import tactic.linarith

example (e b c a v0 v1 : ℚ) (h1 : v0 = 5*a) (h2 : v1 = 3*b) (h3 : v0 + v1 + c = 10) :
  v0 + 5 + (v1 - 3) + (c - 2) = 10 :=
by linarith

example (ε : ℚ) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε :=
 by linarith

example (x y z : ℚ) (h1 : 2*x  < 3*y) (h2 : -4*x + z/2 < 0)
        (h3 : 12*y - z < 0)  : false :=
by linarith

example (ε : ℚ) (h1 : ε > 0) : ε / 2 < ε :=
by linarith

example (ε : ℚ) (h1 : ε > 0) : ε / 3 + ε / 3 + ε / 3 = ε :=
by linarith

example (a b c : ℚ)  (h2 : b + 2 > 3 + b) : false :=
by linarith {discharger := `[ring SOP]}

example (a b c : ℚ)  (h2 : b + 2 > 3 + b) : false :=
by linarith

example (a b c : ℚ) (x y : ℤ) (h1 : x ≤ 3*y) (h2 : b + 2 > 3 + b) : false :=
by linarith {restrict_type := ℚ}

example (g v V c h : ℚ) (h1 : h = 0) (h2 : v = V) (h3 : V > 0) (h4 : g > 0)
        (h5 : 0 ≤ c) (h6 : c < 1) :
  v ≤ V :=
by linarith

example (x y z : ℚ) (h1 : 2*x + ((-3)*y) < 0) (h2 : (-4)*x + 2*z < 0)
       (h3 : 12*y + (-4)* z < 0) (h4 : nat.prime 7) : false :=
by linarith

example (x y z : ℚ) (h1 : 2*1*x + (3)*(y*(-1)) < 0) (h2 : (-2)*x*2 < -(z + z))
       (h3 : 12*y + (-4)* z < 0) (h4 : nat.prime 7) : false :=
by linarith

example (x y z : ℤ) (h1 : 2*x  < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0)  : false :=
by linarith

example (x y z : ℤ) (h1 : 2*x  < 3*y) (h2 : -4*x + 2*z < 0) (h3 : x*y < 5)
        (h3 : 12*y - 4* z < 0)  : false :=
by linarith

example (x y z : ℤ) (h1 : 2*x  < 3*y) (h2 : -4*x + 2*z < 0) (h3 : x*y < 5) :
        ¬ 12*y - 4* z < 0 :=
by linarith

example (w x y z : ℤ) (h1 : 4*x + (-3)*y + 6*w ≤ 0) (h2 : (-1)*x < 0)
        (h3 : y < 0) (h4 : w ≥ 0) (h5 : nat.prime x.nat_abs) : false :=
by linarith

example (a b c : ℚ) (h1 : a > 0) (h2 : b > 5) (h3 : c < -10)
        (h4 : a + b - c < 3)  : false :=
by linarith

example (a b c : ℚ) (h2 : b > 0) (h3 : ¬ b ≥ 0) : false :=
by linarith

example (a b c : ℚ) (h2 : (2 : ℚ) > 3)  : a + b - c ≥ 3 :=
by linarith {exfalso := ff}

example (x : ℚ) (hx : x > 0) (h : x.num < 0) : false :=
by linarith using [rat.num_pos_iff_pos.mpr hx]

example (x y z : ℚ) (hx : x ≤ 3*y) (h2 : y ≤ 2*z) (h3 : x ≥ 6*z) : x = 3*y :=
by linarith

example (x y z : ℕ) (hx : x ≤ 3*y) (h2 : y ≤ 2*z) (h3 : x ≥ 6*z) : x = 3*y :=
by linarith

example (x y z : ℚ) (hx : ¬ x > 3*y) (h2 : ¬ y > 2*z) (h3 : x ≥ 6*z) : x = 3*y :=
by linarith

example (h1 : (1 : ℕ) < 1) : false :=
by linarith

example (a b c : ℚ) (h2 : b > 0) (h3 : b < 0) : nat.prime 10 :=
by linarith

example (a b c : ℕ) : a + b ≥ a :=
by linarith

example (a b c : ℕ) : ¬ a + b < a :=
by linarith

example (x y : ℚ) (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3) (h' : (x + 4) * x ≥ 0)
  (h'' : (6 + 3 * y) * y ≥ 0)  : false :=
by linarith

example (x y : ℕ) (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3) : false :=
by linarith