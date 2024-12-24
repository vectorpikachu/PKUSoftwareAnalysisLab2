FROM ubuntu:22.04
ENV DEBIAN_FRONTEND=noninteractive
ENV PIP_BREAK_SYSTEM_PACKAGES=1
WORKDIR /root

RUN apt-get update -y

# z3 env for python (incl. judger)
RUN apt-get install -y unzip python3 python3-pip
RUN pip3 install importlib_resources psutil z3-solver numba

# z3 env for native (e.g., c)
RUN apt-get install -y z3 libz3-4

# z3 env for pypy
#RUN apt-get install -y pypy3
#RUN pypy3 -m pip install z3-solver

# z3 env for java
#RUN apt-get install -y openjdk-17-jdk libz3-java

# z3 env for nodejs
#RUN apt-get install -y nodejs npm
#RUN npm install -g z3-solver

RUN useradd -m student
RUN chmod 700 /mnt

# src: https://github.com/xmcp/SyGuS-tools/tree/master/work-in-progress/postprocessor
COPY SynthLib2Tester /root/SynthLib2Tester
RUN chmod +x /root/SynthLib2Tester

COPY main.py /root/main.py

CMD python3 -u /root/main.py 2>&1 | tee -a /root/main.stdout
