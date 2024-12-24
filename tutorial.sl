(set-logic LIA)

(synth-fun max ((x Int) (y Int) (z Int)) Int
	   (
	   (Start Int ( 1
	   				0
		           (+ Start Start)
	   ))))

(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)

(constraint (= (max x1 x2 x3) (300)))

(check-synth)