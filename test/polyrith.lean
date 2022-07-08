/-
Copyright (c) 2022 Dhruv Bhatia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Dhruv Bhatia
-/

import tactic.polyrith
import data.real.basic

/-!

Each call to `polyrith` makes a call to the SageCell web API at
<https://sagecell.sagemath.org/>. To avoid making many API calls from CI,
we only test this communication in a few tests.
A full test suite is provided below the `#exit` command.

-/

/-!
## Set up testing infrastructre
-/

section tactic
open polyrith tactic
/--
For testing purposes, this behaves like `tactic.polyrith`, but takes an extra argument
representing the expected output from a call to Sage.
Allows for testing without actually making API calls.
-/
meta def tactic.test_polyrith (only_on : bool) (hyps : list pexpr)
  (sage_out : string) (expected_args : list string) (expected_out : string) :
  tactic unit := do
  (eq_names, m, R, args) ← create_args only_on hyps,
  guard (args = expected_args) <|>
    fail!"expected arguments to Sage: {expected_args}\nbut produced: {args}",
  out ← to_string <$> process_output eq_names m R sage_out,
  guard (out = expected_out) <|>
    fail!"expected final output: {expected_out}\nbut produced: {out}"

meta def format_string_list (input : list string) : string :=
to_string $ input.map (λ s, "\"" ++ s ++ "\"")

setup_tactic_parser

meta def tactic.interactive.test_polyrith (restr : parse (tk "only")?)
  (hyps : parse pexpr_list?)
  (sage_out : string) (expected_args : list string) (expected_out : string) : tactic unit := do
tactic.test_polyrith restr.is_some (hyps.get_or_else []) sage_out expected_args expected_out

meta def tactic.interactive.test_sage_output (restr : parse (tk "only")?)
  (hyps : parse pexpr_list?) (expected_out : string) : tactic unit := do
  sleep 10, -- otherwise can lead to weird errors when actively editing code with polyrith calls
  (eq_names, m, R, args) ← create_args restr.is_some (hyps.get_or_else []),
  sage_out ← sage_output args,
  guard (sage_out.popn_back 2 = expected_out) <|>
    fail!"Expected output from Sage: {expected_out}\nbut produced: {sage_out}"

/--
A convenience function. Given a working test, prints the code for a call to `test_sage_output`.
-/
meta def tactic.interactive.create_sage_output_test (restr : parse (tk "only")?)
  (hyps : parse pexpr_list?) : tactic unit := do
  let hyps := (hyps.get_or_else []),
  sleep 10, -- otherwise can lead to weird errors when actively editing code with polyrith calls
  (eq_names, m, R, args) ← create_args restr.is_some hyps,
  sage_out ← sage_output args,
  let onl := if restr.is_some then "only " else "",
  let hyps := if hyps = [] then "" else to_string hyps,
  trace!"test_sage_output {onl}{hyps} \"{sage_out}\""

/--
A convenience function. Given a working test, prints the code for a call to `test_polyrith`.
-/
meta def tactic.interactive.create_polyrith_test (restr : parse (tk "only")?)
  (hyps : parse pexpr_list?) : tactic unit := do
  let hyps := (hyps.get_or_else []),
  sleep 10, -- otherwise can lead to weird errors when actively editing code with polyrith calls
  (eq_names, m, R, args) ← create_args restr.is_some hyps,
  sage_out ← sage_output args,
  out ← to_string <$> process_output eq_names m R sage_out,
  let argstring := format_string_list args,
  let onl := if restr.is_some then "only " else "",
  let hyps := if hyps = [] then "" else to_string hyps,
  trace!"test_polyrith {onl}{hyps} \"{sage_out}\" {argstring}  \"{out}\""


end tactic

/-!
## SageCell communcation tests
-/

example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
begin
  test_sage_output  "(poly.const 1/1) (poly.sub (poly.const 0/1) (poly.const 2/1))",
  linear_combination h1 - 2 * h2
end

example (w x y z : ℝ) (h1 : x + 2.1*y + 2*z = 2) (h2 : x + 8*z + 5*w = -6.5)
    (h3 : x + y + 5*z + 5*w = 3) :
  x + 2.2*y + 2*z - 5*w = -8.5 :=
begin
  test_sage_output  "(poly.const 2/1) (poly.const 1/1) (poly.sub (poly.const 0/1) (poly.const 2/1))",
  linear_combination 2 * h1 + h2 - 2 * h3
end

/-! ### Standard Cases over ℤ, ℚ, and ℝ -/

example (x y : ℤ) (h1 : 3*x + 2*y = 10):
  3*x + 2*y = 10 :=
by test_polyrith  "(poly.const 1/1)
" ["ff", "int", "[var2, var1]", "[(((3 * var1) + (2 * var2)) - 10)]", "(((3 * var1) + (2 * var2)) - 10)"] "linear_combination h1"


example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
by test_polyrith  "(poly.const 1/1) (poly.sub (poly.const 0/1) (poly.const 2/1))
" ["ff", "rat", "[var2, var1]", "[(((var1 * var2) + (2 * var1)) - 1), (var1 - var2)]", "((var1 * var2) - (((-1 * 2) * var2) + 1))"]  "linear_combination h1 - 2 * h2"

example (x y : ℝ) (h1 : x + 2 = -3) (h2 : y = 10) :
  -y + 2*x + 4 = -16 :=
by test_polyrith  "(poly.const 2/1) (poly.sub (poly.const 0/1) (poly.const 1/1))
" ["ff", "real", "[var2, var1]", "[((var2 + 2) - (-1 * 3)), (var1 - 10)]", "((((-1 * var1) + (2 * var2)) + 4) - (-1 * 16))"]  "linear_combination 2 * h1 - h2"

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
  -3*x - 3*y - 4*z = 2 :=
by test_polyrith  "(poly.const 1/1) (poly.sub (poly.const 0/1) (poly.const 1/1)) (poly.sub (poly.const 0/1) (poly.const 2/1))
" ["ff", "real", "[var3, var2, var1]", "[(((var1 + (2 * var2)) - var3) - 4), ((((2 * var1) + var2) + var3) - (-1 * 2)), (((var1 + (2 * var2)) + var3) - 2)]", "(((((-1 * 3) * var1) - (3 * var2)) - (4 * var3)) - 2)"]  "linear_combination ha - hb - 2 * hc"

example (w x y z : ℝ) (h1 : x + 2.1*y + 2*z = 2) (h2 : x + 8*z + 5*w = -6.5)
    (h3 : x + y + 5*z + 5*w = 3) :
  x + 2.2*y + 2*z - 5*w = -8.5 :=
by test_polyrith  "(poly.const 2/1) (poly.const 1/1) (poly.sub (poly.const 0/1) (poly.const 2/1))
" ["ff", "real", "[var4, var3, var2, var1]", "[(((var1 + (21/10 * var2)) + (2 * var3)) - 2), (((var1 + (8 * var3)) + (5 * var4)) - (-1 * 13/2)), ((((var1 + var2) + (5 * var3)) + (5 * var4)) - 3)]", "((((var1 + (11/5 * var2)) + (2 * var3)) - (5 * var4)) - (-1 * 17/2))"]  "linear_combination 2 * h1 + h2 - 2 * h3"


example (a b c d : ℚ) (h1 : a = 4) (h2 : 3 = b) (h3 : c*3 = d) (h4 : -d = a) :
  2*a - 3 + 9*c + 3*d = 8 - b + 3*d - 3*a :=
by test_polyrith  "(poly.const 2/1) (poly.sub (poly.const 0/1) (poly.const 1/1)) (poly.const 3/1) (poly.sub (poly.const 0/1) (poly.const 3/1))
" ["ff", "rat", "[var4, var3, var2, var1]", "[(var1 - 4), (3 - var4), ((var2 * 3) - var3), ((-1 * var3) - var1)]", "(((((2 * var1) - 3) + (9 * var2)) + (3 * var3)) - (((8 - var4) + (3 * var3)) - (3 * var1)))"]  "linear_combination 2 * h1 - h2 + 3 * h3 - 3 * h4"

/-! ### Case with ambiguous identifiers-/

example («def evil» y : ℤ) (h1 : 3*«def evil» + 2*y = 10):
  3*«def evil» + 2*y = 10 :=
by test_polyrith  "(poly.const 1/1)
" ["ff", "int", "[var2, var1]", "[(((3 * var1) + (2 * var2)) - 10)]", "(((3 * var1) + (2 * var2)) - 10)"]  "linear_combination h1"

example («¥» y : ℤ) (h1 : 3*«¥» + 2*y = 10):
  «¥» * (3*«¥» + 2*y) = 10 * «¥» :=
by test_polyrith  "(poly.var 1)
" ["ff", "int", "[var2, var1]", "[(((3 * var1) + (2 * var2)) - 10)]", "((var1 * ((3 * var1) + (2 * var2))) - (10 * var1))"]  "linear_combination «¥» * h1"

/-! ### Cases with arbitrary coefficients -/

example (a b : ℤ) (h : a = b) :
  a * a = a * b :=
by test_polyrith  "(poly.var 1)
" ["ff", "int", "[var2, var1]", "[(var1 - var2)]", "((var1 * var1) - (var1 * var2))"]  "linear_combination a * h"

example (a b c : ℤ) (h : a = b) :
  a * c = b * c :=
by test_polyrith  "(poly.var 2)
" ["ff", "int", "[var3, var2, var1]", "[(var1 - var3)]", "((var1 * var2) - (var3 * var2))"]  "linear_combination c * h"

example (a b c : ℤ) (h1 : a = b) (h2 : b = 1) :
  c * a + b = c * b + 1 :=
by test_polyrith  "(poly.var 1) (poly.const 1/1)
" ["ff", "int", "[var3, var2, var1]", "[(var2 - var3), (var3 - 1)]", "(((var1 * var2) + var3) - ((var1 * var3) + 1))"]  "linear_combination c * h1 + h2"

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
  x*x*y + y*x*y + 6*x = 3*x*y + 14 :=
by test_polyrith  "(poly.sub (poly.sum (poly.pow (poly.var 1) 2) (poly.mul (poly.const 7/3) (poly.var 2))) (poly.const 49/9)) (poly.sum (poly.sum (poly.sub (poly.sub (poly.mul (poly.const 1/3) (poly.pow (poly.var 2) 2)) (poly.mul (poly.const 1/3) (poly.pow (poly.var 1) 2))) (poly.mul (poly.const 16/9) (poly.var 2))) (poly.mul (poly.const 2/9) (poly.var 1))) (poly.const 13/3))
" ["ff", "rat", "[var2, var1]", "[((var1 + var2) - 3), ((3 * var1) - 7)]", "(((((var1 * var1) * var2) + ((var2 * var1) * var2)) + (6 * var1)) - (((3 * var1) * var2) + 14))"]  "linear_combination (x ^ 2 + 7 / 3 * y - 49 / 9) * h1 + (1 / 3 * y ^ 2 - 1 / 3 * x ^ 2 - 16 / 9 * y + 2 / 9 * x +
    13 / 3) * h2"

example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w :=
by test_polyrith  "(poly.sum (poly.mul (poly.const 2/1) (poly.var 3)) (poly.var 1))
" ["ff", "rat", "[var4, var3, var2, var1]", "[(var2 - var4)]", "(((var1 * var2) + ((2 * var3) * var2)) - ((var1 * var4) + ((2 * var3) * var4)))"]  "linear_combination (2 * y + x) * hzw"


/-! ### Cases with non-hypothesis inputs/input restrictions -/

example (a b : ℝ) (ha : 2*a = 4) (hab : 2*b = a - b) (hignore : 3 = a + b) :
  b = 2 / 3 :=
by test_polyrith only [ha, hab] "(poly.const 1/6) (poly.const 1/3)
" ["ff", "real", "[var2, var1]", "[((2 * var2) - 4), ((2 * var1) - (var2 - var1))]", "(var1 - 2/3)"]  "linear_combination 1 / 6 * ha + 1 / 3 * hab"

constant term : ∀ a b : ℚ, a + b = 0

example (a b c d : ℚ) (h : a + b = 0) (h2: b + c = 0): a + b + c + d = 0 :=
by test_polyrith only [term c d, h] "(poly.const 1/1) (poly.const 1/1)
" ["ff", "rat", "[var4, var3, var2, var1]", "[((var3 + var4) - 0), ((var1 + var2) - 0)]", "((((var1 + var2) + var3) + var4) - 0)"]  "linear_combination term c d + h"

constants (qc : ℚ) (hqc : qc = 2*qc)

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc :=
by test_polyrith [h a b, hqc] "(poly.const 3/1) (poly.const 1/1)
" ["ff", "rat", "[var3, var2, var1]", "[(var1 - var3), (var2 - (2 * var2))]", "(((3 * var1) + var2) - ((3 * var3) + (2 * var2)))"]  "linear_combination 3 * h a b + hqc"

constant bad (q : ℚ) : q = 0

example (a b : ℚ) : a + b^3 = 0 :=
by test_polyrith [bad a, bad (b^2)] "(poly.const 1/1) (poly.var 2)
" ["ff", "rat", "[var2, var1]", "[(var1 - 0), ((var2 ^ 2) - 0)]", "((var1 + (var2 ^ 3)) - 0)"]  "linear_combination bad a + b * bad (b ^ 2)"

/-! ### Case over arbitrary field/ring -/

example {α} [h : comm_ring α] {a b c d e f : α} (h1 : a*d = b*c) (h2 : c*f = e*d) :
  c * (a*f - b*e) = 0 :=
by test_polyrith  "(poly.var 5) (poly.var 2)
" ["ff", "α", "[var6, var5, var4, var3, var2, var1]", "[((var2 * var6) - (var4 * var1)), ((var1 * var3) - (var5 * var6))]", "((var1 * ((var2 * var3) - (var4 * var5))) - 0)"]  "linear_combination e * h1 + a * h2"

example {K : Type*} [field K] [invertible 2] [invertible 3]
  {ω p q r s t x: K} (hp_nonzero : p ≠ 0) (hr : r ^ 2 = q ^ 2 + p ^ 3) (hs3 : s ^ 3 = q + r)
  (ht : t * s = p) (x : K) (H : 1 + ω + ω ^ 2 = 0) :
  x ^ 3 + 3 * p * x - 2 * q =
    (x - (s - t)) * (x - (s * ω - t * ω ^ 2)) * (x - (s * ω ^ 2 - t * ω)) :=
begin
  have hs_nonzero : s ≠ 0,
  { contrapose! hp_nonzero with hs_nonzero,
    test_polyrith  "(poly.const 0/1) (poly.const 0/1) (poly.sub (poly.const 0/1) (poly.const 1/1)) (poly.const 0/1) (poly.var 5)
" ["ff", "K", "[var6, var5, var4, var3, var2, var1]", "[((var2 ^ 2) - ((var3 ^ 2) + (var1 ^ 3))), ((var4 ^ 3) - (var3 + var2)), ((var5 * var4) - var1), (((1 + var6) + (var6 ^ 2)) - 0), (var4 - 0)]", "(var1 - 0)"]  "linear_combination -ht + t * hs_nonzero"
     },
  have H' : 2 * q = s ^ 3 - t ^ 3,
  { rw ← mul_left_inj' (pow_ne_zero 3 hs_nonzero),
    test_polyrith  "(poly.sub (poly.const 0/1) (poly.const 1/1)) (poly.sum (poly.sub (poly.sub (poly.const 0/1) (poly.pow (poly.var 2) 3)) (poly.var 4)) (poly.var 1)) (poly.sum (poly.sum (poly.mul (poly.pow (poly.var 3) 2) (poly.pow (poly.var 2) 2)) (poly.mul (poly.mul (poly.var 5) (poly.var 3)) (poly.var 2))) (poly.pow (poly.var 5) 2)) (poly.const 0/1)
" ["ff", "K", "[var6, var5, var4, var3, var2, var1]", "[((var4 ^ 2) - ((var1 ^ 2) + (var5 ^ 3))), ((var2 ^ 3) - (var1 + var4)), ((var3 * var2) - var5), (((1 + var6) + (var6 ^ 2)) - 0)]", "(((2 * var1) * (var2 ^ 3)) - (((var2 ^ 3) - (var3 ^ 3)) * (var2 ^ 3)))"]  "linear_combination -hr + (-s ^ 3 - r + q) * hs3 + (t ^ 2 * s ^ 2 + p * t * s + p ^ 2) * ht"
  },
test_polyrith  "(poly.const 0/1) (poly.const 0/1) (poly.sum (poly.sum (poly.sub (poly.sum (poly.sub (poly.sum (poly.sum (poly.sub (poly.mul (poly.pow (poly.var 6) 4) (poly.var 5)) (poly.mul (poly.pow (poly.var 6) 4) (poly.var 4))) (poly.mul (poly.pow (poly.var 6) 4) (poly.var 1))) (poly.mul (poly.pow (poly.var 6) 3) (poly.var 5))) (poly.mul (poly.pow (poly.var 6) 3) (poly.var 4))) (poly.mul (poly.pow (poly.var 6) 2) (poly.var 5))) (poly.mul (poly.pow (poly.var 6) 2) (poly.var 4))) (poly.mul (poly.const 3/1) (poly.mul (poly.pow (poly.var 6) 2) (poly.var 1)))) (poly.mul (poly.const 2/1) (poly.mul (poly.var 6) (poly.var 1)))) (poly.sum (poly.sum (poly.sub (poly.sub (poly.sub (poly.sum (poly.sum (poly.sub (poly.sub (poly.sub (poly.sum (poly.sum (poly.sub (poly.const 0/1) (poly.mul (poly.var 6) (poly.pow (poly.var 5) 3))) (poly.mul (poly.var 6) (poly.pow (poly.var 4) 3))) (poly.mul (poly.mul (poly.pow (poly.var 6) 2) (poly.var 5)) (poly.var 2))) (poly.mul (poly.mul (poly.pow (poly.var 6) 2) (poly.var 4)) (poly.var 2))) (poly.mul (poly.mul (poly.var 6) (poly.pow (poly.var 5) 2)) (poly.var 1))) (poly.mul (poly.mul (poly.var 6) (poly.pow (poly.var 4) 2)) (poly.var 1))) (poly.mul (poly.mul (poly.pow (poly.var 6) 2) (poly.var 2)) (poly.var 1))) (poly.pow (poly.var 5) 3)) (poly.pow (poly.var 4) 3)) (poly.mul (poly.mul (poly.var 6) (poly.var 2)) (poly.var 1))) (poly.mul (poly.var 5) (poly.pow (poly.var 1) 2))) (poly.mul (poly.var 4) (poly.pow (poly.var 1) 2))) (poly.mul (poly.const 3/1) (poly.mul (poly.var 2) (poly.var 1)))) (poly.sub (poly.const 0/1) (poly.const 1/1))
" ["ff", "K", "[var7, var6, var5, var4, var3, var2, var1]", "[((var7 ^ 2) - ((var3 ^ 2) + (var2 ^ 3))), ((var4 ^ 3) - (var3 + var7)), ((var5 * var4) - var2), (((1 + var6) + (var6 ^ 2)) - 0), ((2 * var3) - ((var4 ^ 3) - (var5 ^ 3)))]", "((((var1 ^ 3) + ((3 * var2) * var1)) - (2 * var3)) - (((var1 - (var4 - var5)) * (var1 - ((var4 * var6) - (var5 * (var6 ^ 2))))) * (var1 - ((var4 * (var6 ^ 2)) - (var5 * var6)))))"]  "linear_combination (ω ^ 4 * t - ω ^ 4 * s + ω ^ 4 * x + ω ^ 3 * t - ω ^ 3 * s + ω ^ 2 * t - ω ^ 2 * s +
      3 * (ω ^ 2 * x) +
    2 * (ω * x)) * ht + (-(ω * t ^ 3) + ω * s ^ 3 + ω ^ 2 * t * p - ω ^ 2 * s * p - ω * t ^ 2 * x -
                  ω * s ^ 2 * x +
                ω ^ 2 * p * x +
              t ^ 3 -
            s ^ 3 -
          ω * p * x -
        t * x ^ 2 +
      s * x ^ 2 +
    3 * (p * x)) * H - H'",
end





We comment the following tests so that we don't overwhelm the SageCell API.













/-! ### Standard Cases over ℤ, ℚ, and ℝ -/

example (x y : ℤ) (h1 : 3*x + 2*y = 10):
  3*x + 2*y = 10 :=
by polyrith

example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
by polyrith

example (x y : ℝ) (h1 : x + 2 = -3) (h2 : y = 10) :
  -y + 2*x + 4 = -16 :=
by polyrith

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
  -3*x - 3*y - 4*z = 2 :=
by polyrith

example (w x y z : ℝ) (h1 : x + 2.1*y + 2*z = 2) (h2 : x + 8*z + 5*w = -6.5)
    (h3 : x + y + 5*z + 5*w = 3) :
  x + 2.2*y + 2*z - 5*w = -8.5 :=
by polyrith

example (a b c d : ℚ) (h1 : a = 4) (h2 : 3 = b) (h3 : c*3 = d) (h4 : -d = a) :
  2*a - 3 + 9*c + 3*d = 8 - b + 3*d - 3*a :=
by polyrith

/-! ### Case with ambiguous identifiers-/

example («def evil» y : ℤ) (h1 : 3*«def evil» + 2*y = 10):
  3*«def evil» + 2*y = 10 :=
by polyrith

example («¥» y : ℤ) (h1 : 3*«¥» + 2*y = 10):
  «¥» * (3*«¥» + 2*y) = 10 * «¥» :=
by polyrith

/-! ### Cases with arbitrary coefficients -/

example (a b : ℤ) (h : a = b) :
  a * a = a * b :=
by polyrith

example (a b c : ℤ) (h : a = b) :
  a * c = b * c :=
by polyrith

example (a b c : ℤ) (h1 : a = b) (h2 : b = 1) :
  c * a + b = c * b + 1 :=
by polyrith

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
  x*x*y + y*x*y + 6*x = 3*x*y + 14 :=
by polyrith

example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w :=
by polyrith


/-! ### Cases with non-hypothesis inputs/input restrictions -/

example (a b : ℝ) (ha : 2*a = 4) (hab : 2*b = a - b) (hignore : 3 = a + b) :
  b = 2 / 3 :=
by polyrith only [ha, hab]

constant term : ∀ a b : ℚ, a + b = 0

example (a b c d : ℚ) (h : a + b = 0) (h2: b + c = 0): a + b + c + d = 0 :=
by polyrith only [term c d, h]

constants (qc : ℚ) (hqc : qc = 2*qc)

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc :=
by polyrith [h a b, hqc]

constant bad (q : ℚ) : q = 0

example (a b : ℚ) : a + b^3 = 0 :=
by polyrith [bad a, bad (b^2)]

/-! ### Case over arbitrary field/ring -/

example {α} [h : comm_ring α] {a b c d e f : α} (h1 : a*d = b*c) (h2 : c*f = e*d) :
  c * (a*f - b*e) = 0 :=
by polyrith

example {K : Type*} [field K] [invertible 2] [invertible 3]
  {ω p q r s t x: K} (hp_nonzero : p ≠ 0) (hr : r ^ 2 = q ^ 2 + p ^ 3) (hs3 : s ^ 3 = q + r)
  (ht : t * s = p) (x : K) (H : 1 + ω + ω ^ 2 = 0) :
  x ^ 3 + 3 * p * x - 2 * q =
    (x - (s - t)) * (x - (s * ω - t * ω ^ 2)) * (x - (s * ω ^ 2 - t * ω)) :=
begin
  have hs_nonzero : s ≠ 0,
  { contrapose! hp_nonzero with hs_nonzero,
    polyrith,
     },
  have H' : 2 * q = s ^ 3 - t ^ 3,
  { rw ← mul_left_inj' (pow_ne_zero 3 hs_nonzero),
    polyrith,},
  polyrith,
end

/-!
### With trace enabled
Here, the tactic will trace the command that gets sent to sage,
and so the tactic will not prove the goal. `linear_combination`
is called manually to prevent errors.
-/

set_option trace.polyrith true

example (x y : ℝ) (h1 : x + 2 = -3) (h2 : y = 10) :
  -y + 2*x + 4 = -16 :=
begin
  polyrith,
  linear_combination 2 * h1 - h2,
end

example (a b c : ℤ) (h1 : a = b) (h2 : b = 1) :
  c * a + b = c * b + 1 :=
begin
  polyrith,
  linear_combination c * h1 + h2,
end

example (a b c d : ℚ) (h : a + b = 0) (h2: b + c = 0): a + b + c + d = 0 :=
begin
  polyrith only [term c d, h],
  linear_combination term c d + h,
end

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc :=
begin
  polyrith [h a b, hqc],
  linear_combination 3 * h a b + hqc,
end
