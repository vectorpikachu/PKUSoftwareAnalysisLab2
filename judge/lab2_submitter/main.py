import os
import shutil
import json
import time
from shlex import quote
import random
import subprocess
import psutil
import traceback
from pathlib import Path

TIMEOUT_STUDENT = 180
TIMEOUT_JUDGE = 60
RANDOM_SEED = '1337'

uid, serial = os.environ['TOKEN'].split(':')

global_path = Path('/mnt/global_space')
driver_path = Path('/mnt/user_space') / serial
student_path = Path('/home/student')

if not driver_path.is_dir():
    print('\n== 提交不存在')
    exit(0)

if (driver_path / 'result.json').is_file():
    print('\n== 已经评测过了')
    exit(0)

load_avg = psutil.getloadavg()[0]

print(f'\n== 当前评测机负载: {psutil.getloadavg()[0]:.1f} / {psutil.cpu_count()}')
if load_avg / psutil.cpu_count() > .33:
    assert input(' - 当前负载较高，要继续吗？[y/N]').lower()=='y'

try:
    def check_perm(p):
        stat = p.stat()
        assert stat.st_uid==0, f'{p} creator error: {stat.st_uid}'
        assert (stat.st_mode&0o777)==0o700, f'{p} permission error: {oct(stat.st_mode)}'

    check_perm(Path('/mnt'))

    print('\n== 评测环境：')
    for cmd in ['uname -a', 'z3 --version', 'python3 -VV', 'pypy3 -VV', 'java -version', 'node -v']:
        print(f'\n$ {cmd}')
        subprocess.run(cmd, shell=True)

    submission_path = student_path / 'submission'

    assert (driver_path / 'submission.zip').is_file()
    print('\n== 解压提交的 .zip 文件')

    shutil.copy(driver_path / 'submission.zip', student_path / 'submission.zip')
    (student_path / 'submission.zip').chmod(0o644)
    subprocess.check_call(f'su student -c "cd {quote(str(student_path))} && unzip -o -d submission submission.zip"', shell=True)

    if not (submission_path / 'run.sh').is_file(): # maybe in a directory
        for p in submission_path.iterdir():
            if (p / 'run.sh').is_file():
                submission_path = p
                break
        else:
            raise AssertionError('找不到 run.sh')

    for dir in ['input.sl', 'result.txt']:
        if (submission_path / dir).is_dir():
            print(f' - 删除了提交中的 {dir} 目录')
            shutil.rmtree(submission_path / dir)
        elif (submission_path / dir).is_file():
            print(f' - 删除了提交中的 {dir} 文件')
            (submission_path / dir).unlink()

    def parse_benchmark(txt):
        ret = {}

        for line in txt.splitlines():
            line = line.strip()
            if line:
                cat, filename = line.split(',')
                ret.setdefault(cat, []).append(filename)

        return ret

    benchmark = parse_benchmark((global_path / 'benchmark.txt').read_text())

    global_testcase_path = global_path / 'tests'
    student_testcase_path = submission_path / 'input.sl'
    student_output_path = submission_path / 'result.txt'

    def kill_tree(pid):
        try:
            p = psutil.Process(pid)
            for c in p.children(recursive=True):
                c.kill()
            p.kill()
        except psutil.NoSuchProcess:
            pass

    # https://github.com/SyGuS-Org/logs/blob/master/2019/validation-scripts/process_result
    judge_tmp_path = Path('/root/judge_tmp')
    def judge_score(student_output_path, testcase_path):
        if judge_tmp_path.is_dir():
            shutil.rmtree(judge_tmp_path)
        judge_tmp_path.mkdir()

        # judge syntax

        res_syntax = subprocess.run(
            f'/root/SynthLib2Tester {quote(str(student_output_path))} {quote(str(testcase_path))}',
            shell=True, cwd=judge_tmp_path,
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding='utf-8',
            timeout=TIMEOUT_JUDGE,
        ).stdout.strip()
        
        print(res_syntax)
        if not res_syntax.startswith('adheres=true'):
            return ('wrong', 'result_syntax_error'), 0
        
        expr_size_ln = res_syntax.splitlines()[1]
        assert expr_size_ln.startswith('exprs-total-size=')
        expr_size = int(expr_size_ln.partition('=')[2])

        # judge semantic

        res_semantic = subprocess.run(
            f'z3 {quote(str(judge_tmp_path / "__sygus_grmrchecker_output.smt"))}',
            shell=True, cwd=judge_tmp_path,
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding='utf-8',
            timeout=TIMEOUT_JUDGE,
        ).stdout.strip()

        print(res_semantic)
        if res_semantic!='sat':
            return ('wrong', 'result_semantic_error'), 0

        return ('correct', expr_size), 1

    def copy_to_student(cat, path_in, path_out):
        random.seed(f'{RANDOM_SEED}-{path_in.name}')

        if cat in ['bv', 'hidden_bv']:
            # added a filter to avoid over-fitting the if constraints
            def keep_in_outfile(line):
                key_list = ['(constraint', '(=', '#x']

                for key in key_list:
                    if key not in line:
                        return True # not a constraint, always keep
                
                return random.random()>.1 # is a constraint, 90% chance to keep
        else:
            def keep_in_outfile(line):
                return True

        lines = [l for l in path_in.read_text().splitlines() if keep_in_outfile(l)]

        path_out.write_text('\n'.join(lines))

    def run_case(cat, filename):
        # prepare benchmark

        testcase_path = global_testcase_path / cat / filename
        copy_to_student(cat, testcase_path, student_testcase_path)

        try:
            t1 = time.time()

            # run student process

            stdout_fn = driver_path / f'{cat}-{filename}-stdout.txt'

            p = subprocess.Popen(
                f'su student -c "cd {quote(str(submission_path))} && chmod +x run.sh && PATH=$PATH TIMEOUT={TIMEOUT_STUDENT} ./run.sh input.sl" 2>&1 | tee {quote(str(stdout_fn))}',
                shell=True,
                stdin=subprocess.DEVNULL, stdout=None, stderr=subprocess.STDOUT,
            )
            try:
                retcode = p.wait(timeout=TIMEOUT_STUDENT)
                t2 = time.time()
            except subprocess.TimeoutExpired:
                return ('error', 'run_timeout'), 0, TIMEOUT_STUDENT
            finally:
                # cleanup student process
                kill_tree(p.pid)

            if retcode!=0:
                return ('error', 'retcode', retcode), 0, t2-t1

            if not student_output_path.is_file():
                return ('error', 'result_not_found'), 0, t2-t1
            
            shutil.copyfile(student_output_path, driver_path / f'{cat}-{filename}-result.txt')
            
            # judge score

            print('\n检查答案：')
            try:
                desc, score = judge_score(student_output_path, testcase_path)
                if (judge_tmp_path / '__sygus_grmrchecker_output.smt').is_file():
                    shutil.copyfile(judge_tmp_path / '__sygus_grmrchecker_output.smt', driver_path / f'{cat}-{filename}-judge.smt')
            except Exception:
                traceback.print_exc()
                return ('error', 'judge_error'), 0, t2-t1
            return desc, score, t2-t1
            
        finally:
            # remove previous test case
            student_testcase_path.unlink(missing_ok=True)

            # remove previous output file
            student_output_path.unlink(missing_ok=True)

    result = {
        'tot_score': 0,
        'tot_time': 0,
        'error': None,
        'cases': {},
    }
    
    for cat, filenames in benchmark.items():
        for ind, filename in enumerate(filenames):
            print(f'\n== 运行 {cat} 测试：[{ind+1}/{len(filenames)}] {filename}')
            desc, score, tot_time = run_case(cat, filename)
            print(f'\n得分：{score} {desc}\n时间：{tot_time:.2f}s')

            result['cases'][f'{cat}-{filename}'] = (desc, score, tot_time)
            result['tot_score'] += score
            result['tot_time'] += tot_time

        if cat=='basic' and result['tot_score']<len(filenames):
            print('\n== 由于未完全通过 basic，已跳过其他测试用例')
            break

    print(f'\n== 通过测试用例总数：{result["tot_score"]}')

    with (driver_path / 'result.json').open('w') as f:
        json.dump(result, f, indent=1)

except BaseException:
    with (driver_path / 'result.json').open('w') as f:
        json.dump({
            'tot_score': 0,
            'error': traceback.format_exc(),
        }, f, indent=1)

    print('\n')
    raise

else:
    print('\nDone.')

finally:
    time.sleep(.3)
    shutil.copy('/root/main.stdout', driver_path / 'main.stdout.txt')