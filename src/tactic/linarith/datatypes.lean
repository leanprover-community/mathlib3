/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import meta.rb_map
import tactic.ring
import tactic.linarith.lemmas

/-!
# Datatypes for `linarith`

Some of the data structures here are used in multiple parts of the tactic.
We split them into their own file.

This file also contains a few convenient auxiliary functions.
-/


declare_trace linarith

/-- A shorthand for tracing when the `trace.linarith` option is set to true. -/
meta def linarith.linarith_trace {α} [has_to_tactic_format α] (s : α) :=
tactic.when_tracing `linarith (tactic.trace s)

/--
A shorthand for tracing the types of a list of proof terms
when the `trace.linarith` option is set to true.
-/
meta def linarith.linarith_trace_proofs (s : string := "") (l : list expr) : tactic unit :=
tactic.when_tracing `linarith $ do
  tactic.trace s, l.mmap tactic.infer_type >>= tactic.trace

open native

/-! ### Linear expressions -/

/--
A linear expression is a list of pairs of variable indices and coefficients,
representing the sum of the products of each coefficient with its corresponding variable.

Some functions on `linexp` assume that `n : ℕ` occurs at most once as the first element of a pair,
and that the list is sorted in decreasing order of the first argument.
This is not enforced by the type but the operations here preserve it.
-/
@[reducible]
def linarith.linexp : Type := list (ℕ × ℤ)

/--
A map `ℕ → ℤ` is converted to `list (ℕ × ℤ)` in the obvious way.
This list is sorted in decreasing order of the first argument.
-/
meta def native.rb_map.to_linexp (m : rb_map ℕ ℤ) : linarith.linexp :=
m.to_list

namespace linarith

namespace linexp

/--
Add two `linexp`s together componentwise.
Preserves sorting and uniqueness of the first argument.
-/
meta def add : linexp → linexp → linexp
| [] a := a
| a [] := a
| (a@(n1,z1)::t1) (b@(n2,z2)::t2) :=
  if n1 < n2 then b::add (a::t1) t2
  else if n2 < n1 then a::add t1 (b::t2)
  else let sum := z1 + z2 in if sum = 0 then add t1 t2 else (n1, sum)::add t1 t2

/-- `l.scale c` scales the values in `l` by `c` without modifying the order or keys. -/
def scale (c : ℤ) (l : linexp) : linexp :=
if c = 0 then []
else if c = 1 then l
else l.map $ λ ⟨n, z⟩, (n, z*c)

/--
`l.get n` returns the value in `l` associated with key `n`, if it exists, and `none` otherwise.
This function assumes that `l` is sorted in decreasing order of the first argument,
that is, it will return `none` as soon as it finds a key smaller than `n`.
-/
def get (n : ℕ) : linexp → option ℤ
| [] := none
| ((a, b)::t) :=
  if a < n then none
  else if a = n then some b
  else get t

/--
`l.contains n` is true iff `n` is the first element of a pair in `l`.
-/
def contains (n : ℕ) : linexp → bool := option.is_some ∘ get n

/--
`l.zfind n` returns the value associated with key `n` if there is one, and 0 otherwise.
-/
def zfind (n : ℕ) (l : linexp) : ℤ :=
match l.get n with
| none := 0
| some v := v
end

/--
Defines a lex ordering on `linexp`. This function is performance critical.
-/
def cmp : linexp → linexp → ordering
| [] [] := ordering.eq
| [] _ := ordering.lt
| _ [] := ordering.gt
| ((n1,z1)::t1) ((n2,z2)::t2) :=
  if n1 < n2 then ordering.lt
  else if n2 < n1 then ordering.gt
  else if z1 < z2 then ordering.lt
  else if z2 < z1 then ordering.gt
  else cmp t1 t2

end linexp

/-! ### Inequalities -/

/-- The three-element type `ineq` is used to represent the strength of a comparison between terms. -/
@[derive decidable_eq, derive inhabited]
inductive ineq
| eq | le | lt

namespace ineq

/--
`max R1 R2` computes the strength of the sum of two inequalities. If `t1 R1 0` and `t2 R2 0`,
then `t1 + t2 (max R1 R2) 0`.
-/
def max : ineq → ineq → ineq
| lt a := lt
| a lt := lt
| le a := le
| a le := le
| eq eq := eq

/-- `ineq` is ordered `eq < le < lt`. -/
def cmp : ineq → ineq → ordering
| eq eq := ordering.eq
| eq _ := ordering.lt
| le le := ordering.eq
| le lt := ordering.lt
| lt lt := ordering.eq
| _ _ := ordering.gt

/-- Prints an `ineq` as the corresponding infix symbol. -/
def to_string : ineq → string
| eq := "="
| le := "≤"
| lt := "<"

/-- Finds the name of a multiplicative lemma corresponding to an inequality strength. -/
meta def to_const_mul_nm : ineq → name
| lt := ``mul_neg
| le := ``mul_nonpos
| eq := ``mul_eq


instance : has_to_string ineq := ⟨ineq.to_string⟩

meta instance : has_to_format ineq := ⟨λ i, ineq.to_string i⟩

end ineq

/-! ### Comparisons with 0 -/

/--
The main datatype for FM elimination.
Variables are represented by natural numbers, each of which has an integer coefficient.
Index 0 is reserved for constants, i.e. `coeffs.find 0` is the coefficient of 1.
The represented term is `coeffs.sum (λ ⟨k, v⟩, v * Var[k])`.
str determines the direction of the comparison -- is it < 0, ≤ 0, or = 0?
-/
@[derive inhabited]
meta structure comp : Type :=
(str : ineq)
(coeffs : linexp)

/-- `comp.coeff_of c a` projects the coefficient of variable `a` out of `c`. -/
meta def comp.coeff_of (c : comp) (a : ℕ) : ℤ :=
c.coeffs.zfind a

/-- `comp.scale c n` scales the coefficients of `c` by `n`. -/
meta def comp.scale (c : comp) (n : ℕ) : comp :=
{ c with coeffs := c.coeffs.scale n }

/--
`comp.add c1 c2` adds the expressions represented by `c1` and `c2`.
The coefficient of variable `a` in `c1.add c2`
is the sum of the coefficients of `a` in `c1` and `c2`.
 -/
meta def comp.add (c1 c2 : comp) : comp :=
⟨c1.str.max c2.str, c1.coeffs.add c2.coeffs⟩

/-- `comp` has a lex order. First the `ineq`s are compared, then the `coeff`s. -/
meta def comp.cmp : comp → comp → ordering
| ⟨str1, coeffs1⟩ ⟨str2, coeffs2⟩ :=
  match str1.cmp str2 with
  | ordering.lt := ordering.lt
  | ordering.gt := ordering.gt
  | ordering.eq := coeffs1.cmp coeffs2
  end

/--
A `comp` represents a contradiction if its expression has no coefficients and its strength is <,
that is, it represents the fact `0 < 0`.
 -/
meta def comp.is_contr (c : comp) : bool := c.coeffs.empty ∧ c.str = ineq.lt

/--
`comp_source` tracks the source of a comparison.
The atomic source of a comparison is an assumption, indexed by a natural number.
Two comparisons can be added to produce a new comparison,
and one comparison can be scaled by a natural number to produce a new comparison.
 -/
meta inductive comp_source : Type
| assump : ℕ → comp_source
| add : comp_source → comp_source → comp_source
| scale : ℕ → comp_source → comp_source

/--
Given a `comp_source` `cs`, `cs.flatten` maps an assumption index
to the number of copies of that assumption that appear in the history of `cs`.

For example, suppose `cs` is produced by scaling assumption 2 by 5,
and adding to that the sum of assumptions 1 and 2.
`cs.flatten` maps `1 ↦ 1, 2 ↦ 6`.
 -/
meta def comp_source.flatten : comp_source → rb_map ℕ ℕ
| (comp_source.assump n) := mk_rb_map.insert n 1
| (comp_source.add c1 c2) := (comp_source.flatten c1).add (comp_source.flatten c2)
| (comp_source.scale n c) := (comp_source.flatten c).map (λ v, v * n)

/-- Formats a `comp_source` for printing. -/
meta def comp_source.to_string : comp_source → string
| (comp_source.assump e) := to_string e
| (comp_source.add c1 c2) := comp_source.to_string c1 ++ " + " ++ comp_source.to_string c2
| (comp_source.scale n c) := to_string n ++ " * " ++ comp_source.to_string c

meta instance comp_source.has_to_format : has_to_format comp_source :=
⟨λ a, comp_source.to_string a⟩

/-- `pcomp` pairs a zero comparison with its history. -/
meta structure pcomp :=
(c : comp)
(src : comp_source)

/--
The `comp_source` field is ignored when comparing `pcomp`s. Two `pcomp`s proving the same
comparison, with different sources, are considered equivalent.
-/
meta def pcomp.cmp (p1 p2 : pcomp) : ordering :=
p1.c.cmp p2.c

/-- `pcomp.scale c n` scales the coefficients of `c` by `n` and notes this in the `comp_source`. -/
meta def pcomp.scale (c : pcomp) (n : ℕ) : pcomp :=
⟨c.c.scale n, comp_source.scale n c.src⟩

/-- `pcomp.add c1 c2` adds the coefficients of `c1` to `c2`, and notes this in the `comp_source`. -/
meta def pcomp.add (c1 c2 : pcomp) : pcomp :=
⟨c1.c.add c2.c, comp_source.add c1.src c2.src⟩

meta instance pcomp.to_format : has_to_format pcomp :=
⟨λ p, to_fmt p.c.coeffs ++ to_string p.c.str ++ "0"⟩

meta instance comp.to_format : has_to_format comp :=
⟨λ p, to_fmt p.coeffs ++ to_string p.str ++ "0"⟩

/-- Creates an empty set of `pcomp`s, sorted using `pcomp.cmp`. This should always be used instead
of `mk_rb_map` for performance reasons. -/
meta def mk_pcomp_set : rb_set pcomp :=
rb_map.mk_core unit pcomp.cmp

/-! ### Control -/

/--
A preprocessor transforms a proof of a proposition into a proof of a different propositon.
The return type is `list expr`, since some preprocessing steps may create multiple new hypotheses,
and some may remove a hypothesis from the list.
A "no-op" preprocessor should return its input as a singleton list.
-/
meta structure preprocessor : Type :=
(name : string)
(transform : expr → tactic (list expr))

/--
Some preprocessors need to examine the full list of hypotheses instead of working item by item.
As with `preprocessor`, the input to a `global_preprocessor` is replaced by, not added to, its output.
-/
meta structure global_preprocessor : Type :=
(name : string)
(transform : list expr → tactic (list expr))

/--
A `preprocessor` lifts to a `global_preprocessor` by folding it over the input list.
-/
meta def preprocessor.globalize (pp : preprocessor) : global_preprocessor :=
{ name := pp.name,
  transform := list.mfoldl (λ ret e, do l' ← pp.transform e, return (l' ++ ret)) [] }

meta def global_preprocessor.process (pp : global_preprocessor) (l : list expr) :
  tactic (list expr) :=
do l ← pp.transform l,
   linarith_trace_proofs (to_string format!"Preprocessing: {pp.name}") l,
   return l

meta instance : has_coe preprocessor global_preprocessor :=
⟨preprocessor.globalize⟩

/-- A configuration object for `linarith`. -/
meta structure linarith_config :=
(discharger : tactic unit := `[ring])
(restrict_type : option Type := none)
(restrict_type_reflect : reflected restrict_type . tactic.apply_instance)
(exfalso : bool := tt)
(transparency : tactic.transparency := reducible)
(split_hypotheses : bool := tt)
(preprocessors : option (list global_preprocessor) := none)

/--
`cfg.update_reducibility reduce_semi` will change the transparency setting of `cfg` to
`semireducible` if `reduce_semi` is true. In this case, it also sets the discharger to `ring!`,
since this is typically needed when using stronger unification.
-/
meta def linarith_config.update_reducibility (cfg : linarith_config) (reduce_semi : bool) :
  linarith_config :=
if reduce_semi then { cfg with transparency := semireducible, discharger := `[ring!] }
else cfg

/-!
### Auxiliary functions

These functions are used by multiple modules, so we put them here for accessibility.
-/

open tactic

/--
`get_rel_sides e` returns the left and right hand sides of `e` if `e` is a comparison,
and fails otherwise.
This function is more naturally in the `option` monad, but it is convenient to put in `tactic`
for compositionality.
 -/
meta def get_rel_sides : expr → tactic (expr × expr)
| `(%%a < %%b) := return (a, b)
| `(%%a ≤ %%b) := return (a, b)
| `(%%a = %%b) := return (a, b)
| `(%%a ≥ %%b) := return (a, b)
| `(%%a > %%b) := return (a, b)
| _ := tactic.failed


/--
`parse_into_comp_and_expr e` checks if `e` is of the form `t < 0`, `t ≤ 0`, or `t = 0`.
If it is, it returns the comparison along with `t`.
 -/
meta def parse_into_comp_and_expr : expr → option (ineq × expr)
| `(%%e < 0) := (ineq.lt, e)
| `(%%e ≤ 0) := (ineq.le, e)
| `(%%e = 0) := (ineq.eq, e)
| _ := none

/--
`mk_single_comp_zero_pf c h` assumes that `h` is a proof of `t R 0`.
It produces a pair `(R', h')`, where `h'` is a proof of `c*t R' 0`.
Typically `R` and `R'` will be the same, except when `c = 0`, in which case `R'` is `=`.
If `c = 1`, `h'` is the same as `h` -- specifically, it does *not* change the type to `1*t R 0`.
-/
meta def mk_single_comp_zero_pf (c : ℕ) (h : expr) : tactic (ineq × expr) :=
do tp ← infer_type h,
  some (iq, e) ← return $ parse_into_comp_and_expr tp,
  if c = 0 then
    do e' ← mk_app ``zero_mul [e], return (ineq.eq, e')
  else if c = 1 then return (iq, h)
  else
    do nm ← resolve_name iq.to_const_mul_nm,
       tp ← (prod.snd <$> (infer_type h >>= get_rel_sides)) >>= infer_type,
       cpos ← to_expr ``((%%c.to_pexpr : %%tp) > 0),
       (_, ex) ← solve_aux cpos `[norm_num, done],
       e' ← to_expr ``(%%nm %%h %%ex) ff,
       return (iq, e')


end linarith
