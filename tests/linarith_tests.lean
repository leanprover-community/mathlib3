import tactic.linarith
 
example (a b c : ℚ)  (h2 : b + 2 > 3 + b) : false :=
by linarith

example (g v V c h : ℚ) (h1 : h = 0) (h2 : v = V) (h3 : V > 0) (h4 : g > 0)
        (h5 : 0 ≤ c) (h6 : c < 1) :
  v ≤ V :=
by linarith

theorem f (x y z : ℚ) (h1 : 2*x + ((-3)*y) < 0) (h2 : (-4)*x + 2*z < 0)
       (h3 : 12*y + (-4)* z < 0) (h4 : nat.prime 7) : false :=
by linarith

example (x y z : ℤ) (h1 : 2*x  < 3*y) (h2 : -4*x + 2*z < 0) 
        (h3 : 12*y - 4* z < 0)  : false :=
by linarith

example (w x y z : ℤ) (h1 : 4*x + (-3)*y + 6*w ≤ 0) (h2 : (-1)*x < 0) 
        (h3 : y < 0) (h4 : w ≥ 0) (h5 : nat.prime x.nat_abs) : false :=
by linarith

example (a b c : ℚ) (h1 : a > 0) (h2 : b > 5) (h3 : c < -10) 
        (h4 : a + b - c < 3)  : false :=
by linarith

example (a b c : ℚ) (h2 : b > 0) (h3 : b < 0) : false :=
by linarith

example (a b c : ℚ) (h2 : (2 : ℚ) > 3)  : a + b - c ≥ 3 :=
by linarith

example (x : ℚ) (hx : x > 0) (h : x.num < 0) : false :=
by linarith using [rat.num_pos_iff_pos.mpr hx]