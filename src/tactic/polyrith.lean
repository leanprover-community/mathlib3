/-
Copyright (c) 2022 Dhruv Bhatia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Bhatia
-/
import tactic.linear_combination
import data.buffer.parser

/-!

# polyrith Tactic

In this file, the `polyrith` tactic is created.  This tactic, which
works over `field`s, attempts to prove a multivariate polynomial target over said
field by using multivariable polynomial hypotheses/proof terms over the same field.
Used as is, the tactic makes use of those hypotheses in the local context that are
over the same field as the target. However, the user can also specifiy which hypotheses
from the local context to use, along with proof terms that might not already be in the
local context. Note: since this tactic uses SageMath via an API call done in Python,
it can only be used with a working internet connection, and with a local installation of Python.

## Notation
* This file uses the local notation `exmap` for `list (expr × ℕ)`.

## Implementation Notes

The tactic `linear_combination` is often used to prove such goals by allowing the user to
specify a coefficient for each hypothesis. If the target polynomial can be written as a
linear combination of the hypotheses with the chosen coefficients, then the `linear_combination`
tactic succeeds. In other words, `linear_combination` is a certificate checker, and it is left
to the user to find a collection of good coefficients. The `polyrith` tactic automates this
process using the theory of Groebner bases.

Polyrith does this by first parsing the relevant hypotheses into a form that Python can understand.
It then calls a Python file that uses the SageMath API to compute the coefficients. These
coefficients are then sent back to Lean, which parses them into pexprs. The information is then
given to the `linear_combination` tactic, which completes the process by checking the certificate.

## References

* See the book `Ideals, Varieties, and Algorithms` by David Cox, John Little, and Donal O'Shea
for the background theory on Groebner bases
* This code was heavily inspired by the code for the tactic `linarith`, which was written by
Robert Lewis, who advised me on this project as part of a Computer Science independant study
at Brown University.

-/

open tactic native

namespace polyrith

/-! # Poly Datatype-/

/--
A datatype representing the semantics of multivariable polynomials.
Each `poly` can be converted into a string.
-/
inductive poly
| const: ℚ → poly
| var: ℕ → poly
| add: poly → poly → poly
| sub: poly → poly → poly
| mul: poly → poly → poly
| pow : poly → ℕ → poly

/--
This converts a poly object into a string representing it. The string
maintains the semantic structure of the poly object.
-/

meta def poly.mk_string : poly → string
| (poly.const z) := to_string z
| (poly.var n) := "var" ++ to_string n
| (poly.add p q) := "(" ++ poly.mk_string p ++ " + " ++ poly.mk_string q ++ ")"
| (poly.sub p q) := "(" ++ poly.mk_string p ++ " - " ++ poly.mk_string q ++ ")"
| (poly.mul p q) := "(" ++ poly.mk_string p ++ " * " ++ poly.mk_string q ++ ")"
| (poly.pow p n) := to_string $ format!"({poly.mk_string p} ^ {n})"

meta instance : has_add poly := ⟨poly.add⟩
meta instance : has_sub poly := ⟨poly.sub⟩
meta instance : has_mul poly := ⟨poly.mul⟩
meta instance : has_pow poly ℕ := ⟨poly.pow⟩
meta instance : has_repr poly := ⟨poly.mk_string⟩
meta instance : has_to_format poly := ⟨to_fmt ∘ poly.mk_string⟩
meta instance : inhabited poly := ⟨poly.const 0⟩


/-!
# Parsing algorithms

The following section contains code that can convert an `expr` of type `Prop` into a `poly` object
(provided that it is an equality)
-/

local notation `exmap` := list (expr × ℕ)

/--
`poly_form_of_atom red map e` is the atomic case for `poly_form_of_expr`.
If `e` appears with index `k` in `map`, it returns the singleton sum `poly.var k`.
Otherwise it updates `map`, adding `e` with index `n`, and returns the singleton `poly.var n`.
-/
meta def poly_form_of_atom (red : transparency) (m : exmap) (e : expr) : tactic (exmap × poly) :=
(do (_, k) ← m.find_defeq red e, return (m, poly.var k)) <|>
(let n := m.length + 1 in return ((e, n)::m, poly.var n))

/--
`poly_form_of_expr red map e` computes the polynomial form of `e`.

`map` is a lookup map from atomic expressions to variable numbers.
If a new atomic expression is encountered, it is added to the map with a new number.
It matches atomic expressions up to reducibility given by `red`.

Because it matches up to definitional equality, this function must be in the `tactic` monad,
and forces some functions that call it into `tactic` as well.
-/
meta def poly_form_of_expr (red : transparency) : exmap → expr → tactic (exmap × poly)
| m `(%%e1 * %%e2) :=
   do (m', comp1) ← poly_form_of_expr m e1,
      (m', comp2) ← poly_form_of_expr m' e2,
      return (m', comp1 * comp2)
| m `(%%e1 + %%e2) :=
   do (m', comp1) ← poly_form_of_expr m e1,
      (m', comp2) ← poly_form_of_expr m' e2,
      return (m', comp1 + comp2)
| m `(%%e1 - %%e2) :=
   do (m', comp1) ← poly_form_of_expr m e1,
      (m', comp2) ← poly_form_of_expr m' e2,
      return (m',  comp1 - comp2)
| m `(-%%e) :=
  do (m', comp) ← poly_form_of_expr m e,
     return (m', (poly.const (-1)) * comp)
| m p@`(@has_pow.pow _ ℕ _ %%e %%n) :=
  match n.to_nat with
  | some k :=
    do (m', comp) ← poly_form_of_expr m e,
    return (m', comp^k)
  | none := poly_form_of_atom red m p
  end
| m e :=
  match e.to_rat with
  | some z := return ⟨m, poly.const z⟩
  | none := poly_form_of_atom red m e
  end


/-!
# Un-Parsing algorithms

The following section contains code that can convert an a `poly` object into a `pexpr`.
-/

/--
A helper tactic that takes in a `ℕ` and a `(expr × ℕ)`. It succeeds if
the first `ℕ` can be unified with the second one. -/
meta def has_val: ℕ → (expr × ℕ) → tactic unit
| n (_,m) := unify `(n) `(m)

/--
This can convert a `poly` into a `pexpr` that would evaluate to a polynomial.
To do so, it uses an `exmap` that contains information about what atomic expressions
the variables in the `poly` refer to.

`poly` objects only contain coefficients from `ℚ`. However, the `poly` object might
be referring to a polynomial over some other field. As such, the resulting `pexpr` contains
no typing information.
-/
meta def poly.to_pexpr :exmap → poly → tactic pexpr
| _ (poly.const z) := return z.to_pexpr
| m (poly.var n) :=
  do
    (e, num) ← m.mfind (has_val n),
    return ``(%%e)
| m (poly.add p q) :=
  do
    p_pexpr ← poly.to_pexpr m p,
    q_pexpr ← poly.to_pexpr m q,
    return ``(%%p_pexpr + %%q_pexpr)
| m (poly.sub p q) :=
  do
    p_pexpr ← poly.to_pexpr m p,
    q_pexpr ← poly.to_pexpr m q,
    if p_pexpr = ``(0) then return ``(- %%q_pexpr) else
    return ``(%%p_pexpr - %%q_pexpr)
| m (poly.mul p q) :=
  do
    p_pexpr ← poly.to_pexpr m p,
    q_pexpr ← poly.to_pexpr m q,
    return ``(%%p_pexpr * %%q_pexpr)
| m (poly.pow p n) :=
  do
    p_pexpr ← poly.to_pexpr m p,
    return ``(%%p_pexpr ^ %%n)


/-!
# Parsing SageMath output into a poly

The following section contains code that can convert a string of appropriate format into
a `poly` object. This is used later on to convert the coefficients given by Sage into
`poly` objects.
-/

/--
An error message returned from Sage has a kind and a message.
-/
@[derive inhabited]
structure sage_error :=
(kind : string)
(message : string)

open parser

/--
Parse an error message from the output of the polyrith python script.
The script formats errors as "%{kind}%{message}".
-/
meta def error_parser : parser sage_error := do
  ch '%',
  kind ← many_char1 (sat (≠ '%')),
  ch '%',
  msg ← list.as_string <$> many any_char,
  return ⟨kind, msg⟩

/--
A parser object that parses `string`s of the form `"poly.var n"`
to the appropriate `poly` object representing a variable.
Here, `n` is a natural number
-/
meta def var_parser : parser poly := do
  str "poly.var ",
  n ← nat,
  return (poly.var n)

/--
A parser object that parses `string`s of the form `"-n"`
to the appropriate `poly` object representing a negative integer.
Here, `n` is a natural number
-/
meta def neg_nat_parser : parser int := do
  ch '-',
  n ← nat,
  return (- n)

/--
A parser object that parses `string`s of the form `"-n"`
to the appropriate `poly` object representing a positive integer.
Here, `n` is a natural number
-/
meta def nat_as_int_parser : parser int := do
  n ← nat,
  return (n)

/--
A parser object that parses `string`s of the form `"poly.const z"`
to the appropriate `poly` object representing a rational coefficient.
Here, `n` is a rational number
-/
meta def const_fraction_parser : parser poly := do
  str "poly.const ",
  numer ← neg_nat_parser <|> nat_as_int_parser,
  ch '/',
  denom ← nat,
  return (poly.const (numer/denom))

/--
A parser object that parses `string`s of the form `"poly.sum p q"`
to the appropriate `poly` object representing the sum of two `poly`s.
Here, `p` and `q` are themselves string forms of `poly`s.
-/
meta def add_parser (cont : parser poly) : parser poly := do
  str "poly.sum ",
  lhs ← cont,
  ch ' ',
  rhs ← cont,
  return (poly.add lhs rhs)

/--
A parser object that parses `string`s of the form `"poly.sub p q"`
to the appropriate `poly` object representing the subtraction of two `poly`s.
Here, `p` and `q` are themselves string forms of `poly`s.
-/
meta def sub_parser (cont : parser poly) : parser poly := do
  str "poly.sub ",
  lhs ← cont,
  ch ' ',
  rhs ← cont,
  return (poly.sub lhs rhs)

/--
A parser object that parses `string`s of the form `"poly.mul p q"`
to the appropriate `poly` object representing the product of two `poly`s.
Here, `p` and `q` are themselves string forms of `poly`s.
-/
meta def mul_parser (cont : parser poly) : parser poly := do
  str "poly.mul ",
  lhs ← cont,
  ch ' ',
  rhs ← cont,
  return (poly.mul lhs rhs)

/--
A parser object that parses `string`s of the form `"poly.pow p n"`
to the appropriate `poly` object representing a `poly` raised to the
power of a natural number. Here, `p` is the string form of a `poly`
and `n` is a natural number.
-/
meta def pow_parser (cont : parser poly) : parser poly := do
  str "poly.pow ",
  base ← cont,
  ch ' ',
  n ← nat,
  return (poly.pow base n)

/--
A parser object that parses `string`s into `poly` objects.
-/
meta def poly_parser : parser poly := do
  ch '(',
  t ←  var_parser <|> const_fraction_parser <|> add_parser poly_parser
    <|> sub_parser poly_parser <|> mul_parser poly_parser <|> pow_parser poly_parser,
  ch ')',
  return t

/--A parser object that parses a string (which may contain trailing whitespace) into a poly object-/
meta def one_of_many_poly_parser : parser poly := do
  p ← poly_parser,
  optional $ ch ' ',
  return p

/--checks whether a character is a whitespace character-/
@[derive decidable]
meta def _root_.char.is_whitespace' (c : char) : Prop :=
c.is_whitespace ∨ c.to_nat = 13

/--removes trailing whitespace from a `string`-/
meta def remove_trailing_whitespace : string → string
| s := if s.back.is_whitespace' then remove_trailing_whitespace s.pop_back else s

/--
A parser object that converts the output of sage (which should be
formatted as a collection of ``poly`s in `string` form, separated
 by a single space) into a `list poly`
-/
meta def sage_output_parser : parser (sage_error ⊕ list poly) :=
(sum.inl <$> error_parser) <|> sum.inr <$> many (one_of_many_poly_parser)

/--A tactic that checks whether `sage_output_parser` worked-/
meta def parser_output_checker : string ⊕ (sage_error ⊕ list poly) → tactic (list poly)
| (sum.inl s) := fail!"polyrith failed to parse the output from Sage.\n\n{s}"
| (sum.inr (sum.inr poly_list)) := return poly_list
| (sum.inr (sum.inl err))
  := fail!"polyrith failed to retrieve a solution from Sage! {err.kind}: {err.message}"

/--
A tactic that uses the above defined parsers to convert
the sage output `string` to a `list poly`
-/
meta def convert_sage_output : string → tactic (list poly)
| s := (let sage_stuff := sage_output_parser.run_string (remove_trailing_whitespace s)
  in parser_output_checker sage_stuff)


/-!
# Parsing context into poly

The following section contains code that collects hypotheses of the appropriate type
from the context (and from the list of hypotheses and proof terms specified by the user)
and converts them into `poly` objects.
-/

/--
A tactic that takes an `expr`, and, if it is an equality of the
form `lhs = rhs`, returns the expr given by `lhs - rhs`-/
meta def equality_to_left_side : expr → tactic expr
| `(%%lhs = %%rhs) :=
  do
    out_expr ← to_expr ``(%%lhs - %%rhs),
    return out_expr
| e := fail "expression is not an equality"

/--
A tactic that converts the current target (an equality over
some field) into a `poly`. The tactic returns an `exmap` containing
information about the atomic expressions in the target, the `poly`
itself, and an `expr` representing the field.-/
meta def parse_target_to_poly : tactic (exmap × poly × expr) :=
do
  e@`(@eq %%R _ _) ← target,
  left_side ← equality_to_left_side e,
  (m, p) ← poly_form_of_expr transparency.reducible [] left_side,
  return (m, p, R)

/--
A function that takes in an `exmap`, a `list poly`, and
an `expr` to be converted to a `poly`. The function carries
out this conversion, updates the `exmap` with information
about the new `poly`, and adds the new `poly` to the top
of the list.
-/
meta def fold_function: (exmap × list poly) → expr → tactic (exmap × list poly)
| (m, poly_list) new_exp :=
do
  (m', new_poly) ← poly_form_of_expr transparency.reducible m new_exp,
  return (m', poly_list ++ [new_poly])

/--
A tactic that takes in two `expr`s, and returns a `bool`.
The first `expr` represents a type. If the second `expr` is an
equality of this type, it returns true. If not, it returns false.
-/
meta def is_eq_of_type : expr → expr → tactic bool
| expt h_eq := (do `(@eq %%R _ _) ← infer_type h_eq, unify expt R, return tt) <|> return ff

/--
A tactic that takes in an `expr` representing a type,
and a `list expr`. the tactic returns the sublist of those
`expr`s that are equalities of that type.
-/
meta def get_equalities_of_type : expr → list expr → tactic (list expr)
| expt l := l.mfilter (is_eq_of_type expt)

/--
The prupose of this tactic is to collect all the hypotheses
and proof terms (specified by the user) that are equalities
of the same type as the target. It takes in an `expr` representing
the type, an `exmap` (typically this starts as only containing
information about the target), a `bool` representing whether the
user used the key word "only", and a `list pexpr` of all the
hypotheses and proof terms selected by the user.

If the key word "only" is used, it collects together only those
hypotheses/proof terms selected by the user. If not, they are
combined with hypotheses from the local context. We throw out
those hypotheses that are not equalities of the given type,
and then modify each equality such that everything has been
moved to the left of the "=" sign.

The tactic returns the names of these hypotheses (as `expr`s),
an `exmap` updated with information from all these hypotheses,
and a list of these hypotheses converted into `poly` objects.
-/
meta def parse_ctx_to_polys : expr → exmap → bool → list pexpr →
  tactic (list expr × exmap × list poly)
| expt m only_on hyps:=
do
  hyps ← hyps.mmap $ λ e, i_to_expr e,
  hyps ← if only_on then return hyps else (++ hyps) <$> local_context,
  eq_names ← get_equalities_of_type expt hyps,
  eqs ← eq_names.mmap infer_type,
  eqs_to_left ← eqs.mmap equality_to_left_side,
  (m, poly_list) ← mfoldl (fold_function) (m, []) eqs_to_left,
  return (eq_names, m, poly_list)


/-!
# Connecting with Python

The following section contains code that allows lean to communicate with a python script.
-/

/--
This tactic calls python from the command line with the args in `arg_list`.
The output printed to the console is returned as a `string`.
-/
meta def sage_output (arg_list : list string := []) : tactic string :=
let args := ["scripts/polyrith_sage.py"] ++ arg_list in
do
  s ← tactic.unsafe_run_io $ io.cmd { cmd := "python3", args := args},
  return s

/--
Given an updated `exmap`, this function returns a list of strings
of the form `"var n"`, where `n` is a `ℕ` that exists as an index
in the `exmap`. Essentially, this is a list of all the variable indices
contained in the `exmap`.
-/
meta def get_var_names : exmap → list string
| [] := []
| ((e, n) :: tl) := ("var" ++ to_string n) :: (get_var_names tl)

/--
Given a pair of `expr`s, where one represents the hypothesis/proof term,
and the other representes the coefficient attached to it, this tactic
creates a string combining the two in the appropriate format for
`linear_combination`.

The boolean value returned is `tt` if the format needs to be negated
to accurately reflect the input expressions.
The negation is not applied in the format output by this function,
because it may appear as a negation (if this is the first component)
or a subtraction.
-/
meta def component_to_lc_format : expr × expr → tactic (bool × format)
| (ex, `(-@has_one.one _ _)) := prod.mk tt <$> pformat!"{ex}"
| (ex, `(@has_one.one _ _))  := prod.mk ff <$> pformat!"{ex}"
| (ex, `(-%%cf)) := do (neg, fmt) ← component_to_lc_format (ex, cf), return (!neg, fmt)
| (ex, cf@`(_ + _)) := prod.mk ff <$> pformat!"({cf}) * {ex}"
| (ex, cf@`(_ - _)) := prod.mk ff <$> pformat!"({cf}) * {ex}"
| (ex, cf) := prod.mk ff <$> pformat!"{cf} * {ex}"

private meta def intersperse_ops_aux : list (bool × format) → format
| [] := ""
| ((ff, fmt) :: t) := " +" ++ format.soft_break ++ fmt ++ intersperse_ops_aux t
| ((tt, fmt) :: t) := " -" ++ format.soft_break ++ fmt ++ intersperse_ops_aux t

/--
Given a `list (bool × format)`, this function uses `+` and `-` to conjoin the
`format`s in the list. A `format` is negated if its corresponding `bool` is `tt`.
-/
meta def intersperse_ops : list (bool × format) → format
| [] := ""
| ((ff, fmt)::t) := fmt ++ intersperse_ops_aux t
| ((tt, fmt)::t) := "-" ++ fmt ++ intersperse_ops_aux t

/-- This tactic repeats the process above for a `list` of pairs of `expr`s.-/
meta def components_to_lc_format (components : list (expr × expr)) : tactic format :=
intersperse_ops <$> components.mmap component_to_lc_format

/-!
# Connecting with Python

The following section contains code that allows lean to communicate with a python script.
-/

declare_trace polyrith

/--
This is the main body of the `polyrith` tactic. It takes in the following inputs:
* `(only_on : bool)` - This represents whether the user used the key word "only"
* `(hyps : list pexpr)` - the hypotheses/proof terms selecteed by the user

First, the tactic converts the target into a `poly`, and finds out what type it
is an equality of. (It also fills up an `exmap` with its information). Then, it
collects all the relevant hypotheses/proof terms from the context, and from those
selected by the user, taking into account whether `only_on` is true. (The `exmap` is
updated accordingly as well).

This information is used to create a list of args that get used in a call to
the appropriate python file that executes a grobner basis computation. The
output of this computation is a `string` representing the certificate. This
string is parsed into a list of `poly` objects that are then converted into
`pexpr`s (using the updated `exmap`).

the names of the hypotheses, along with the corresponding coefficients are
given to `linear_combination`. If that tactic succeeds, the user is prompted
to replace the call to `polyrith` with the appropriate call to
`linear_combination`.
-/
meta def tactic.polyrith (only_on : bool) (hyps : list pexpr): tactic unit :=
do
  sleep 10, -- otherwise can lead to weird errors when actively editing code with polyrith calls
  (m, p, R) ← parse_target_to_poly,
  (eq_names, m, polys) ← parse_ctx_to_polys R m only_on hyps,
  let args := [to_string R, (get_var_names m).to_string,
    (polys.map poly.mk_string).to_string, p.mk_string],
  let args := to_string (is_trace_enabled_for `polyrith) :: args,
  sage_out ← sage_output args,
  if is_trace_enabled_for `polyrith then
    trace sage_out
  else do
  coeffs_as_poly ← convert_sage_output sage_out,
  coeffs_as_pexpr ← coeffs_as_poly.mmap (poly.to_pexpr m),
  let eq_names_pexpr := eq_names.map to_pexpr,
  coeffs_as_expr ← coeffs_as_pexpr.mmap $ λ e, to_expr ``(%%e : %%R),
  linear_combo.linear_combination eq_names_pexpr coeffs_as_pexpr,
  let components := (eq_names.zip coeffs_as_expr).filter
    $ λ pr, bnot $ pr.2.is_app_of `has_zero.zero,
  expr_string ← components_to_lc_format components,
  let cmd : format := "linear_combination " ++ format.nest 2 (format.group expr_string),
  trace!"Try this: {cmd}"


/-! # Interactivity -/
setup_tactic_parser

/--
Attempts to prove polynomial equality goals through polynomial arithmetic
on the hypotheses (and additional proof terms if the user specifies them).
It proves the goal by generating an appropriate call to the tactic
`linear_combination`. If this call succeeds, the call to `linear_combination`
is suggested to the user.

* `polyrith` will use all relevant hypotheses in the local context.
* `polyrith [t1, t2, t3]` will add proof terms t1, t2, t3 to the local context.
* `polyrith only [h1, h2, h3, t1, t2, t3]` will use only local hypotheses
  `h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

Note: This tactic only works with a working internet connection.

Examples:

```
example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
by polyrith
-- Try this: linear_combination h1 - 2 * h2

example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w :=
by polyrith
-- Try this: linear_combination (2 * y + x) * hzw

constant scary : ∀ a b : ℚ, a + b = 0

example (a b c d : ℚ) (h : a + b = 0) (h2: b + c = 0) : a + b + c + d = 0 :=
by polyrith only [scary c d, h]
-- Try this: linear_combination scary c d + h
```
-/
meta def _root_.tactic.interactive.polyrith (restr : parse (tk "only")?)
  (hyps : parse pexpr_list?) : tactic unit :=
  tactic.polyrith restr.is_some (hyps.get_or_else [])

add_tactic_doc
{ name := "polyrith",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.polyrith],
  tags := ["arithmetic", "automation", "polynomial", "grobner", "groebner"] }

end polyrith
