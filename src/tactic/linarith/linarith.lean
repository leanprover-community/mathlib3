/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import tactic.ring
import tactic.linarith.lemmas
import tactic.cancel_denoms
import tactic.zify

/-!
# Linear arithmetic

`linarith` is a tactic for discharging linear arithmetic goals using Fourier-Motzkin elimination.

`linarith` is (in principle) complete for ℚ and ℝ. It is not complete for non-dense orders, i.e. ℤ.

- @TODO: investigate storing comparisons in a list instead of a set, for possible efficiency gains
- @TODO: delay proofs of denominator normalization and nat casting until after contradiction is
  found
-/

open native
namespace linarith

declare_trace linarith

/-- A shorthand for tracing when the `trace.linarith` option is set to true. -/
meta def linarith_trace {α} [has_to_tactic_format α] (s : α) :=
tactic.when_tracing `linarith (tactic.trace s)

/--
A shorthand for tracing the types of a list of proof terms
when the `trace.linarith` option is set to true.
-/
meta def linarith_trace_proofs (s : string := "") (l : list expr) : tactic unit :=
tactic.when_tracing `linarith $ do
  tactic.trace s, l.mmap tactic.infer_type >>= tactic.trace

/-!
### Datatypes

#### Linear expressions
-/

/--
A linear expression is a list of pairs of variable indices and coefficients,
representing the sum of the products of each coefficient with its corresponding variable.

Some functions on `linexp` assume that `n : ℕ` occurs at most once as the first element of a pair,
and that the list is sorted in decreasing order of the first argument.
This is not enforced by the type but the operations here preserve it.
-/
@[reducible]
def linexp : Type := list (ℕ × ℤ)

end linarith

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

/-! #### Inequalities -/

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

instance : has_to_string ineq := ⟨ineq.to_string⟩

meta instance : has_to_format ineq := ⟨λ i, ineq.to_string i⟩

end ineq

/-! #### Control -/

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

/-! #### Comparisons with 0 -/

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


/-!
### The Fourier-Motzkin elimination procedure

The Fourier-Motzkin procedure is a variable elimination method for linear inequalities.
<https://en.wikipedia.org/wiki/Fourier%E2%80%93Motzkin_elimination>

Given a set of linear inequalities `comps = {tᵢ Rᵢ 0}`,
we aim to eliminate a single variable `a` from the set.
We partition `comps` into `comps_pos`, `comps_neg`, and `comps_zero`,
where `comps_pos` contains the comparisons `tᵢ Rᵢ 0` in which
the coefficient of `a` in `tᵢ` is positive, and similar.

For each pair of comparisons `tᵢ Rᵢ 0 ∈ comps_pos`, `tⱼ Rⱼ 0 ∈ comps_neg`,
we compute coefficients `vᵢ, vⱼ ∈ ℕ` such that `vᵢ*tᵢ + vⱼ*tⱼ` cancels out `a`.
We collect these sums `vᵢ*tᵢ + vⱼ*tⱼ R' 0` in a set `S` and set `comps' = S ∪ comps_zero`,
a new set of comparisons in which `a` has been eliminated.

Theorem: `comps` and `comps'` are equisatisfiable.

We recursively eliminate all variables from the system. If we derive an empty clause `0 < 0`,
we conclude that the original system was unsatisfiable.
-/

/-- If `c1` and `c2` both contain variable `a` with opposite coefficients,
produces `v1` and `v2`, such that `a` has been cancelled in `v1*c1 + v2*c2`. -/
meta def elim_var (c1 c2 : comp) (a : ℕ) : option (ℕ × ℕ × comp) :=
let v1 := c1.coeff_of a,
    v2 := c2.coeff_of a in
if v1 * v2 < 0 then
  let vlcm :=  nat.lcm v1.nat_abs v2.nat_abs,
      v1' := vlcm / v1.nat_abs,
      v2' := vlcm / v2.nat_abs in
  some ⟨v1', v2', comp.add (c1.scale v1') (c2.scale v2')⟩
else none

/--
`pelim_var p1 p2` calls `elim_var` on the `comp` components of `p1` and `p2`.
If this returns `v1` and `v2`, it creates a new `pcomp` equal to `v1*p1 + v2*p2`,
and tracks this in the `comp_source`.
-/
meta def pelim_var (p1 p2 : pcomp) (a : ℕ) : option pcomp :=
do (n1, n2, c) ← elim_var p1.c p2.c a,
   return ⟨c, comp_source.add (p1.src.scale n1) (p2.src.scale n2)⟩

/--
A `pcomp` represents a contradiction if its `comp` field represents a contradiction.
-/
meta def pcomp.is_contr (p : pcomp) : bool := p.c.is_contr

/--
`elim_var_with_set a p comps` collects the result of calling `pelim_var p p' a`
for every `p' ∈ comps`.
-/
meta def elim_with_set (a : ℕ) (p : pcomp) (comps : rb_set pcomp) : rb_set pcomp :=
comps.fold mk_pcomp_set $ λ pc s,
match pelim_var p pc a with
| some pc := s.insert pc
| none := s
end

/--
The state for the elimination monad.
* `vars`: the set of variables that have not been officially eliminated
* `comps`: a set of comparisons

The elimination procedure proceeds by eliminating variable `v` from `comps` progressively
for each `v ∈ vars`.

Note: variables are eliminated in decreasing order. Instead of storing `vars` as an `rb_set`,
we could store the largest `n : N` that has not yet been eliminated.
This is not done yet for historical reasons, and is a negligible performance gain.
-/
meta structure linarith_structure :=
(vars : rb_set ℕ)
(comps : rb_set pcomp)

/--
The linarith monad extends an exceptional monad with a `linarith_structure` state.
An exception produces a contradictory `pcomp`.
-/
@[reducible, derive [monad, monad_except pcomp]] meta def linarith_monad :=
state_t linarith_structure (except_t pcomp id)

/-- Return the set of active variables. -/
meta def get_vars : linarith_monad (rb_set ℕ) :=
linarith_structure.vars <$> get

/-- Return the list of active variables. -/
meta def get_var_list : linarith_monad (list ℕ) :=
rb_set.to_list <$> get_vars

/-- Return the current comparison set. -/
meta def get_comps : linarith_monad (rb_set pcomp) :=
linarith_structure.comps <$> get

/-- Throws an exception if a contradictory `pcomp` is contained in the current state. -/
meta def validate : linarith_monad unit :=
do ⟨_, comps⟩ ← get,
match comps.to_list.find (λ p : pcomp, p.is_contr) with
| none := return ()
| some c := throw c
end

/--
Updates the current state with a new set of variables and comparisons,
and calls `validate` to check for a contradiction.
-/
meta def update (vars : rb_set ℕ) (comps : rb_set pcomp) : linarith_monad unit :=
state_t.put ⟨vars, comps⟩ >> validate

/--
`split_set_by_var_sign a comps` partitions the set `comps` into three parts.
* `pos` contains the elements of `comps` in which `a` has a positive coefficient.
* `neg` contains the elements of `comps` in which `a` has a negative coefficient.
* `not_present` contains the elements of `comps` in which `a` has coefficient 0.

Returns `(pos, neg, not_present)`.
-/
meta def split_set_by_var_sign (a : ℕ) (comps : rb_set pcomp) :
  rb_set pcomp × rb_set pcomp × rb_set pcomp :=
comps.fold ⟨mk_pcomp_set, mk_pcomp_set, mk_pcomp_set⟩ $ λ pc ⟨pos, neg, not_present⟩,
  let n := pc.c.coeff_of a in
  if n > 0 then ⟨pos.insert pc, neg, not_present⟩
  else if n < 0 then ⟨pos, neg.insert pc, not_present⟩
  else ⟨pos, neg, not_present.insert pc⟩

/--
`monad.elim_var a` performs one round of Fourier-Motzkin elimination, eliminating the variable `a`
from the `linarith` state.
-/
meta def monad.elim_var (a : ℕ) : linarith_monad unit :=
do vs ← get_vars,
   when (vs.contains a) $
do ⟨pos, neg, not_present⟩ ← split_set_by_var_sign a <$> get_comps,
   let cs' := pos.fold not_present (λ p s, s.union (elim_with_set a p neg)),
   update (vs.erase a) $ cs'

/--
`elim_all_vars` eliminates all variables from the linarith state, leaving it with a set of
ground comparisons. If this succeeds without exception, the original `linarith` state is consistent.
-/
meta def elim_all_vars : linarith_monad unit :=
get_var_list >>= list.mmap' monad.elim_var


/-!
### Parsing input expressions into linear form

`linarith` computes the linear form of its input expressions,
assuming (without justification) that the type of these expressions
is a commutative semiring.

It identifies atoms up to ring-equivalence: that is, `(y*3)*x` will be identified `3*(x*y)`,
where the monomial `x*y` is the linear atom.

* Variables are represented by natural numbers.
* Monomials are represented by `monom := rb_map ℕ ℕ`. The monomial `1` is represented by the empty map.
* Linear combinations of monomials are represented by `sum := rb_map monom ℤ`.

All input expressions are converted to `sum`s, preserving the map from expressions to variables.
We then discard the monomial information, mapping each distinct monomial to a natural number.
The resulting `rb_map ℕ ℤ` represents the ring-normalized linear form of the expression.

This is ultimately converted into a `linexp` in the obvious way.

#### Parsing datatypes
-/

/-- Variables (represented by natural numbers) map to their power. -/
@[reducible] meta def monom : Type := rb_map ℕ ℕ

/-- Compare monomials by first comparing their keys and then their powers. -/
@[reducible] meta def monom.lt : monom → monom → Prop :=
λ a b, (a.keys < b.keys) || ((a.keys = b.keys) && (a.values < b.values))

/-- The `has_lt` instance for `monom` is only needed locally. -/
local attribute [instance]
meta def monom_has_lt : has_lt monom := ⟨monom.lt⟩

/-- Linear combinations of monomials are represented by mapping monomials to coefficients. -/
@[reducible] meta def sum : Type := rb_map monom ℤ

/-- `sum.scale_by_monom s m` multiplies every monomial in `s` by `m`. -/
meta def sum.scale_by_monom (s : sum) (m : monom) : sum :=
s.fold mk_rb_map $ λ m' coeff sm, sm.insert (m.add m') coeff

/-- `sum.mul s1 s2` distributes the multiplication of two sums.` -/
meta def sum.mul (s1 s2 : sum) : sum :=
s1.fold mk_rb_map $ λ mn coeff sm, sm.add $ (s2.scale_by_monom mn).scale coeff

/-- `sum_of_monom m` lifts `m` to a sum with coefficient `1`. -/
meta def sum_of_monom (m : monom) : sum :=
mk_rb_map.insert m 1

/-- The unit monomial `one` is represented by the empty rb map. -/
meta def one : monom := mk_rb_map

/-- A scalar `z` is represented by a `sum` with coefficient `z` and monomial `one` -/
meta def scalar (z : ℤ) : sum :=
mk_rb_map.insert one z

/-- A single variable `n` is represented by a sum with coefficient `1` and monomial `n`. -/
meta def var (n : ℕ) : sum :=
mk_rb_map.insert (mk_rb_map.insert n 1) 1

section parse

open ineq tactic

/-! #### Parsing algorithms -/

/--
`map_of_expr red map e` computes the linear form of `e`.

`map` is a lookup map from atomic expressions to variable numbers.
If a new atomic expression is encountered, it is added to the map with a new number.
It matches atomic expressions up to reducibility given by `red`.

Because it matches up to definitional equality, this function must be in the `tactic` monad,
and forces some functions that call it into `tactic` as well.
-/
meta def map_of_expr (red : transparency) : expr_map ℕ → expr → tactic (expr_map ℕ × sum)
| m e@`(%%e1 * %%e2) :=
   do (m', comp1) ← map_of_expr m e1,
      (m', comp2) ← map_of_expr m' e2,
      return (m', comp1.mul comp2)
| m `(%%e1 + %%e2) :=
   do (m', comp1) ← map_of_expr m e1,
      (m', comp2) ← map_of_expr m' e2,
      return (m', comp1.add comp2)
| m `(%%e1 - %%e2) :=
   do (m', comp1) ← map_of_expr m e1,
      (m', comp2) ← map_of_expr m' e2,
      return (m', comp1.add (comp2.scale (-1)))
| m `(-%%e) := do (m', comp) ← map_of_expr m e, return (m', comp.scale (-1))
| m e :=
  match e.to_int with
  | some 0 := return ⟨m, mk_rb_map⟩
  | some z := return ⟨m, scalar z⟩
  | none :=
    (do k ← m.find_defeq red e, return (m, var k)) <|>
    (let n := m.size + 1 in return (m.insert e n, var n))
  end

/--
`sum_to_lf s map` eliminates the monomial level of the `sum` `s`.

`map` is a lookup map from monomials to variable numbers.
The output `rb_map ℕ ℤ` has the same structure as `sum`,
but each monomial key is replaced with its index according to `map`.
If any new monomials are encountered, they are assigned variable numbers and `map` is updated.
 -/
meta def sum_to_lf (s : sum) (m : rb_map monom ℕ) : rb_map monom ℕ × rb_map ℕ ℤ :=
s.fold (m, mk_rb_map) $ λ mn coeff ⟨map, out⟩,
  match map.find mn with
  | some n := ⟨map, out.insert n coeff⟩
  | none := let n := map.size in ⟨map.insert mn n, out.insert n coeff⟩
  end

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
`to_comp red e e_map monom_map` converts an expression of the form `t < 0`, `t ≤ 0`, or `t = 0`
into a `comp` object.

`e_map` maps atomic expressions to indices; `monom_map` maps monomials to indices.
Both of these are updated during processing and returned.
-/
meta def to_comp (red : transparency) (e : expr) (e_map : expr_map ℕ) (monom_map : rb_map monom ℕ) :
  tactic (comp × expr_map ℕ × rb_map monom ℕ) :=
do (iq, e) ← parse_into_comp_and_expr e,
   (m', comp') ← map_of_expr red e_map e,
   let ⟨nm, mm'⟩ := sum_to_lf comp' monom_map,
   return ⟨⟨iq, mm'.to_linexp⟩,m',nm⟩

/--
`to_comp_fold red e_map exprs monom_map` folds `to_comp` over `exprs`,
updating `e_map` and `monom_map` as it goes.
 -/
meta def to_comp_fold (red : transparency) : expr_map ℕ → list expr → rb_map monom ℕ →
      tactic (list comp × expr_map ℕ × rb_map monom ℕ)
| m [] mm := return ([], m, mm)
| m (h::t) mm :=
  do (c, m', mm') ← to_comp red h m mm,
      (l, mp, mm') ← to_comp_fold m' t mm',
      return (c::l, mp, mm')

/-! ### Control functions -/

/--
`mk_linarith_structure red l` takes a list of proofs of props of the form `t {<, ≤, =} 0`,
and creates a `linarith_structure`. The transparency setting `red` is used to unify atoms.

Along with a `linarith_structure`, it produces a map `ℕ → (expr × expr)`.
This map assigns indices to the hypotheses in `l`. It maps a natural number `n` to a pair
`(prf, tp)`, where `prf` is the `n`th element of `l` and is a proof of the comparison `tp`.
-/
meta def mk_linarith_structure (red : transparency) (l : list expr) :
  tactic (linarith_structure × rb_map ℕ (expr × expr)) :=
do pftps ← l.mmap infer_type,
  (l', _, map) ← to_comp_fold red mk_rb_map pftps mk_rb_map,
  let lz := list.enum $ (l.zip pftps).zip l',
  let prmap := rb_map.of_list $ lz.map (λ ⟨n, x⟩, (n, x.1)),
  let vars : rb_set ℕ := rb_map.set_of_list $ list.range map.size,
  let pc : rb_set pcomp :=
    rb_set.of_list_core mk_pcomp_set $ lz.map (λ ⟨n, x⟩, ⟨x.2, comp_source.assump n⟩),
  return (⟨vars, pc⟩, prmap)

/--
`linarith_monad.run red tac l` runs the `linarith` process `tac` on input `l`.
It returns the value produced by `tac` if `tac` does not find a contradiction.
Otherwise it returns a `pcomp` representing a proof of `0 < 0`.

It also produces a map `ℕ → (expr × expr)`.
This map assigns indices to the hypotheses in `l`. It maps a natural number `n` to a pair
`(prf, tp)`, where `prf` is the `n`th element of `l` and is a proof of the comparison `tp`.
This map is needed to reconstruct the proof of the discovered contradiction.
 -/
meta def linarith_monad.run (red : transparency) {α} (tac : linarith_monad α) (l : list expr) :
  tactic ((pcomp ⊕ α) × rb_map ℕ (expr × expr)) :=
do (struct, inputs) ← mk_linarith_structure red l,
match (state_t.run (validate >> tac) struct).run with
| (except.ok (a, _)) := return (sum.inr a, inputs)
| (except.error contr) := return (sum.inl contr, inputs)
end

end parse

/-!
### Verification

`linarith_monad.run` is used to search for a way to derive `false` from a set of hypotheses.
This search is unverified, but it returns a certificate:
a map `m` from hypothesis indices to natural number coefficients.
If our set of hypotheses has the form  `{tᵢ Rᵢ 0}`,
then the elimination process should have guaranteed that
1.\ `∑ (m i)*tᵢ = 0`,
with at least one `i` such that `m i > 0` and `Rᵢ` is `<`.

We have also that
2.\ `∑ (m i)*tᵢ < 0`,
since for each `i`, `(m i)*tᵢ ≤ 0` and at least one is strictly negative.
So we conclude a contradiction `0 < 0`.

It remains to produce proofs of (1) and (2). (1) is verified by calling the `discharger` tactic
of the `linarith_config` object, which is typically `ring`. We prove (2) by folding over the
set of hypotheses.

#### Auxiliary functions for assembling proofs
-/

section prove
open ineq tactic

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
| _ := failed

/--
`mul_expr n e` creates a `pexpr` representing `n*e`.
When elaborated, the coefficient will be a native numeral of the same type as `e`.
-/
meta def mul_expr (n : ℕ) (e : expr) : pexpr :=
if n = 1 then ``(%%e) else
``(%%(nat.to_pexpr n) * %%e)

private meta def add_exprs_aux : pexpr → list pexpr → pexpr
| p [] := p
| p [a] := ``(%%p + %%a)
| p (h::t) := add_exprs_aux ``(%%p + %%h) t

/--
`add_exprs l` creates a `pexpr` representing the sum of the elements of `l`, associated left.
If `l` is empty, it will be the `pexpr` 0. Otherwise, it does not include 0 in the sum.
-/
meta def add_exprs : list pexpr → pexpr
| [] := ``(0)
| (h::t) := add_exprs_aux h t

/-- Finds the name of a multiplicative lemma corresponding to an inequality strength. -/
meta def ineq.to_const_mul_nm : ineq → name
| lt := ``mul_neg
| le := ``mul_nonpos
| eq := ``mul_eq

/--
If our goal is to add together two inequalities `t1 R1 0` and `t2 R2 0`,
`ineq_const_nm R1 R2` produces the strength of the inequality in the sum `R`,
along with the name of a lemma to apply in order to conclude `t1 + t2 R 0`.
-/
meta def ineq_const_nm : ineq → ineq → (name × ineq)
| eq eq := (``eq_of_eq_of_eq, eq)
| eq le := (``le_of_eq_of_le, le)
| eq lt := (``lt_of_eq_of_lt, lt)
| le eq := (``le_of_le_of_eq, le)
| le le := (`add_nonpos, le)
| le lt := (`add_neg_of_nonpos_of_neg, lt)
| lt eq := (``lt_of_lt_of_eq, lt)
| lt le := (`add_neg_of_neg_of_nonpos, lt)
| lt lt := (`add_neg, lt)

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
    do e' ← mk_app ``zero_mul [e], return (eq, e')
  else if c = 1 then return (iq, h)
  else
    do nm ← resolve_name iq.to_const_mul_nm,
       tp ← (prod.snd <$> (infer_type h >>= get_rel_sides)) >>= infer_type,
       cpos ← to_expr ``((%%c.to_pexpr : %%tp) > 0),
       (_, ex) ← solve_aux cpos `[norm_num, done],
       e' ← to_expr ``(%%nm %%h %%ex) ff,
       return (iq, e')

/--
`mk_lt_zero_pf_aux c pf npf coeff` assumes that `pf` is a proof of `t1 R1 0` and `npf` is a proof
of `t2 R2 0`. It uses `mk_single_comp_zero_pf` to prove `t1 + coeff*t2 R 0`, and returns `R`
along with this proof.
-/
meta def mk_lt_zero_pf_aux (c : ineq) (pf npf : expr) (coeff : ℕ) : tactic (ineq × expr) :=
do (iq, h') ← mk_single_comp_zero_pf coeff npf,
   let (nm, niq) := ineq_const_nm c iq,
   n ← resolve_name nm,
   e' ← to_expr ``(%%n %%pf %%h'),
   return (niq, e')

/--
`mk_lt_zero_pf coeffs pfs` takes a list of coefficients and a list of proofs of the form `tᵢ Rᵢ 0`,
of equal length. It produces a proof that `∑tᵢ R 0`, where `R` is as strong as possible.
-/
meta def mk_lt_zero_pf : list ℕ → list expr → tactic expr
| _ [] := fail "no linear hypotheses found"
| [c] [h] := prod.snd <$> mk_single_comp_zero_pf c h
| (c::ct) (h::t) :=
  do (iq, h') ← mk_single_comp_zero_pf c h,
     prod.snd <$> (ct.zip t).mfoldl (λ pr ce, mk_lt_zero_pf_aux pr.1 pr.2 ce.2 ce.1) (iq, h')
| _ _ := fail "not enough args to mk_lt_zero_pf"

/-- If `prf` is a proof of `t R s`, `term_of_ineq_prf prf` returns `t`. -/
meta def term_of_ineq_prf (prf : expr) : tactic expr :=
prod.fst <$> (infer_type prf >>= get_rel_sides)

/-- If `prf` is a proof of `t R s`, `ineq_prf_tp prf` returns the type of `t`. -/
meta def ineq_prf_tp (prf : expr) : tactic expr :=
term_of_ineq_prf prf >>= infer_type

/--
`mk_neg_one_lt_zero_pf tp` returns a proof of `-1 < 0`,
where the numerals are natively of type `tp`.
-/
meta def mk_neg_one_lt_zero_pf (tp : expr) : tactic expr :=
to_expr ``((neg_neg_of_pos zero_lt_one : -1 < (0 : %%tp)))

/--
If `e` is a proof that `t = 0`, `mk_neg_eq_zero_pf e` returns a proof that `-t = 0`.
-/
meta def mk_neg_eq_zero_pf (e : expr) : tactic expr :=
to_expr ``(neg_eq_zero.mpr %%e)

/--
`add_neg_eq_pfs l` inspects the list of proofs `l` for proofs of the form `t = 0`. For each such
proof, it adds a proof of `-t = 0` to the list.
-/
meta def add_neg_eq_pfs : list expr → tactic (list expr)
| [] := return []
| (h::t) :=
  do some (iq, tp) ← parse_into_comp_and_expr <$> infer_type h,
  match iq with
  | ineq.eq := do nep ← mk_neg_eq_zero_pf h, tl ← add_neg_eq_pfs t, return $ h::nep::tl
  | _ := list.cons h <$> add_neg_eq_pfs t
  end

/--
`prove_false_by_linarith` is the main workhorse of `linarith`.
Given a list `l` of proofs of `tᵢ Rᵢ 0` and a proof state with target `false`,
it tries to derive a contradiction from `l` and use this to close the goal.
-/
meta def prove_false_by_linarith (cfg : linarith_config) : list expr → tactic unit
| [] := fail "no args to linarith"
| l@(h::t) := do
    -- for the elimination to work properly, we must add a proof of `-1 < 0` to the list,
    -- along with negated equality proofs.
    l' ← add_neg_eq_pfs l,
    hz ← ineq_prf_tp h >>= mk_neg_one_lt_zero_pf,
    -- perform the elimination and fail if no contradiction is found.
    (sum.inl contr, inputs) ← elim_all_vars.run cfg.transparency (hz::l')
      | fail "linarith failed to find a contradiction",
    -- we construct two lists `coeffs` and `pfs` of equal length,
    -- filtering out the comparisons that were not used in deriving the contradiction.
    linarith_trace "linarith has found a contradiction",
    let coeff_map := contr.src.flatten,
    let coeffs := inputs.keys.map coeff_map.ifind,
    let pfs : list expr := inputs.keys.map (λ k, (inputs.ifind k).1),
    let zip := (coeffs.zip pfs).filter (λ pr, pr.1 ≠ 0),
    let (coeffs, pfs) := zip.unzip,
    mls ← zip.mmap (λ pr, do e ← term_of_ineq_prf pr.2, return (mul_expr pr.1 e)),
    -- `sm` is the sum of input terms, scaled to cancel out all variables.
    sm ← to_expr $ add_exprs mls,
    pformat! "The expression\n  {sm}\nshould be both 0 and negative" >>= linarith_trace,
    tgt ← to_expr ``(%%sm = 0),
    -- we prove that `sm = 0`, typically with `ring`.
    (_, sm_eq_zero) ← solve_aux tgt (cfg.discharger >> done),
    linarith_trace "We have proved that it is zero",
    -- we also prove that `sm < 0`.
    sm_lt_zero ← mk_lt_zero_pf coeffs pfs,
    linarith_trace "We have proved that it is negative",
    -- this is a contradiction.
    pftp ← infer_type sm_lt_zero,
    (_, nep, _) ← rewrite_core sm_eq_zero pftp,
    pf' ← mk_eq_mp nep sm_lt_zero,
    mk_app `lt_irrefl [pf'] >>= exact

end prove

section preprocessing

/-! ### Preprocessing -/

open tactic

set_option eqn_compiler.max_steps 50000

meta def rem_neg (prf : expr) : expr → tactic expr
| `(_ ≤ _) := to_expr ``(lt_of_not_ge %%prf)
| `(_ < _) := to_expr ``(le_of_not_gt %%prf)
| `(_ > _) := to_expr ``(le_of_not_gt %%prf)
| `(_ ≥ _) := to_expr ``(lt_of_not_ge %%prf)
| e := failed

private meta def rearr_comp_aux : expr → expr → tactic expr
| prf `(%%a ≤ 0) := return prf
| prf  `(%%a < 0) := return prf
| prf  `(%%a = 0) := return prf
| prf  `(%%a ≥ 0) := to_expr ``(neg_nonpos.mpr %%prf)
| prf  `(%%a > 0) := to_expr ``(neg_neg_of_pos %%prf)
| prf  `(0 ≥ %%a) := to_expr ``(show %%a ≤ 0, from %%prf)
| prf  `(0 > %%a) := to_expr ``(show %%a < 0, from %%prf)
| prf  `(0 = %%a) := to_expr ``(eq.symm %%prf)
| prf  `(0 ≤ %%a) := to_expr ``(neg_nonpos.mpr %%prf)
| prf  `(0 < %%a) := to_expr ``(neg_neg_of_pos %%prf)
| prf  `(%%a ≤ %%b) := to_expr ``(sub_nonpos.mpr %%prf)
| prf  `(%%a < %%b) := to_expr ``(sub_neg_of_lt %%prf)
| prf  `(%%a = %%b) := to_expr ``(sub_eq_zero.mpr %%prf)
| prf  `(%%a > %%b) := to_expr ``(sub_neg_of_lt %%prf)
| prf  `(%%a ≥ %%b) := to_expr ``(sub_nonpos.mpr %%prf)
| prf  `(¬ %%t) := do nprf ← rem_neg prf t, tp ← infer_type nprf, rearr_comp_aux nprf tp
| prf  a := trace a >> fail "couldn't rearrange comp"

/--
`rearr_comp e` takes a proof `e` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <}`.
 -/
meta def rearr_comp (e : expr) : tactic expr :=
infer_type e >>= rearr_comp_aux e

meta def get_contr_lemma_name_and_type : expr → option (name × expr)
| `(@has_lt.lt %%tp %%_ _ _) := return (`lt_of_not_ge, tp)
| `(@has_le.le %%tp %%_ _ _) := return (`le_of_not_gt, tp)
| `(@eq %%tp _ _) := return (``eq_of_not_lt_of_not_gt, tp)
| `(@ne %%tp _ _) := return (`not.intro, tp)
| `(@ge %%tp %%_ _ _) := return (`le_of_not_gt, tp)
| `(@gt %%tp %%_ _ _) := return (`lt_of_not_ge, tp)
| `(¬ @has_lt.lt %%tp %%_ _ _) := return (`not.intro, tp)
| `(¬ @has_le.le %%tp %%_ _ _) := return (`not.intro, tp)
| `(¬ @eq %%tp _ _) := return (``not.intro, tp)
| `(¬ @ge %%tp %%_ _ _) := return (`not.intro, tp)
| `(¬ @gt %%tp %%_ _ _) := return (`not.intro, tp)
| _ := none

meta def is_nat_int_coe : expr → option expr
| `((↑(%%n : ℕ) : ℤ)) := some n
| _ := none

meta def mk_coe_nat_nonneg_prf (e : expr) : tactic expr :=
mk_app `int.coe_nat_nonneg [e]

meta def get_nat_comps : expr → list expr
| `(%%a + %%b) := (get_nat_comps a).append (get_nat_comps b)
| `(%%a * %%b) := (get_nat_comps a).append (get_nat_comps b)
| e := match is_nat_int_coe e with
  | some e' := [e']
  | none := []
  end

meta def mk_coe_nat_nonneg_prfs (e : expr) : tactic (list expr) :=
(get_nat_comps e).mmap mk_coe_nat_nonneg_prf

meta def mk_int_pfs_of_nat_pf (pf : expr) : tactic (list expr) :=
do pf' ← zify_proof pf,
   (a, b) ← infer_type pf' >>= get_rel_sides,
   list.cons pf' <$> ((++) <$> mk_coe_nat_nonneg_prfs a <*> mk_coe_nat_nonneg_prfs b)

meta def mk_non_strict_int_pf_of_strict_int_pf (pf : expr) : tactic expr :=
do tp ← infer_type pf,
match tp with
| `(%%a < %%b) := to_expr ``(@cast (%%a < %%b) (%%a + 1 ≤ %%b) (by refl) %%pf)
| `(%%a > %%b) := to_expr ``(@cast (%%a > %%b) (%%a ≥ %%b + 1) (by refl) %%pf)
| `(¬ %%a ≤ %%b) := to_expr ``(@cast (%%a > %%b) (%%a ≥ %%b + 1) (by refl) (lt_of_not_ge %%pf))
| `(¬ %%a ≥ %%b) := to_expr ``(@cast (%%a < %%b) (%%a + 1 ≤ %%b) (by refl) (lt_of_not_ge %%pf))
| _ := fail "mk_non_strict_int_pf_of_strict_int_pf failed: proof is not an inequality"
end

/--
`is_nat_prop tp` is true iff `tp` is an inequality or equality between natural numbers
or the negation thereof.
-/
meta def is_nat_prop : expr → bool
| `(@eq ℕ %%_ _) := tt
| `(@has_le.le ℕ %%_ _ _) := tt
| `(@has_lt.lt ℕ %%_ _ _) := tt
| `(@ge ℕ %%_ _ _) := tt
| `(@gt ℕ %%_ _ _) := tt
| `(¬ %%p) := is_nat_prop p
| _ := ff

/--
`is_strict_int_prop tp` is true iff `tp` is a strict inequality between integers
or the negation of a weak inequality between integers.
-/
meta def is_strict_int_prop : expr → bool
| `(@has_lt.lt ℤ %%_ _ _) := tt
| `(@gt ℤ %%_ _ _) := tt
| `(¬ @has_le.le ℤ %%_ _ _) := tt
| `(¬ @ge ℤ %%_ _ _) := tt
| _ := ff

private meta def filter_comparisons_aux : expr → bool
| `(¬ %%p) := p.app_symbol_in [`has_lt.lt, `has_le.le, `gt, `ge]
| tp := tp.app_symbol_in [`has_lt.lt, `has_le.le, `gt, `ge, `eq]

/--
Removes any expressions that are not proofs of inequalities, equalities, or negations thereof.
-/
meta def filter_comparisons : preprocessor :=
{ name := "filter terms that are not proofs of comparisons",
  transform := λ h,
(do tp ← infer_type h,
   is_prop tp >>= guardb,
   guardb (filter_comparisons_aux tp),
   return [h])
<|> return [] }

meta def remove_negations : preprocessor :=
{ name := "replace negations of comparisons",
  transform := λ h,
do tp ← infer_type h,
match tp with
| `(¬ %%p) := singleton <$> rem_neg h p
| _ := return [h]
end }

/--
If `h` is an equality or inequality between natural numbers,
`nat_to_int h` lifts this inequality to the integers,
adding the facts that the integers involved are nonnegative.
 -/
meta def nat_to_int : preprocessor :=
{ name := "move nats to ints",
  transform := λ h,
do tp ← infer_type h,
   guardb (is_nat_prop tp) >> mk_int_pfs_of_nat_pf h <|> return [h] }

/-- `strengthen_strict_int h` turns a proof `h` of a strict integer inequality `t1 < t2`
into a proof of `t1 ≤ t2 + 1`. -/
meta def strengthen_strict_int : preprocessor :=
{ name := "strengthen strict inequalities over int",
  transform := λ h,
do tp ← infer_type h,
   guardb (is_strict_int_prop tp) >> singleton <$> mk_non_strict_int_pf_of_strict_int_pf h
     <|> return [h] }

/--
`mk_comp_with_zero h` takes a proof `h` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <}`.
 -/
meta def make_comp_with_zero : preprocessor :=
{ name := "make comparisons with zero",
  transform := λ e, singleton <$> rearr_comp e <|> return [] }

/--
`normalize_denominators_in_lhs h lhs` assumes that `h` is a proof of `lhs R 0`.
It creates a proof of `lhs' R 0`, where all numeric division in `lhs` has been cancelled.
-/
meta def normalize_denominators_in_lhs (h lhs : expr) : tactic expr :=
do (v, lhs') ← cancel_factors.kill_factors lhs,
   if v = 1 then return h else do
   (ih, h'') ← mk_single_comp_zero_pf v h,
   (_, nep, _) ← infer_type h'' >>= rewrite_core lhs',
   mk_eq_mp nep h''

/--
`cancel_denoms pf` assumes `pf` is a proof of `t R 0`. If `t` contains the division symbol `/`,
it tries to scale `t` to cancel out division by numerals.
-/
meta def cancel_denoms : preprocessor :=
{ name := "cancel denominators",
  transform := λ pf,
(do some (_, lhs) ← parse_into_comp_and_expr <$> infer_type pf,
   guardb $ lhs.contains_constant (= `has_div.div),
   singleton <$> normalize_denominators_in_lhs pf lhs)
<|> return [pf] }

/--
`find_squares m e` collects all terms of the form `a ^ 2` and `a * a` that appear in `e`
and adds them to the set `m`.
A pair `(a, tt)` is added to `m` when `a^2` appears in `e`, and `(a, ff)` is added to `m`
when `a*a` appears in `e`.  -/
meta def find_squares : rb_set (expr × bool) → expr → tactic (rb_set (expr × bool))
| s `(%%a ^ 2) := do s ← find_squares s a, return (s.insert (a, tt))
| s e@`(%%e1 * %%e2) := if e1 = e2 then do s ← find_squares s e1, return (s.insert (e1, ff)) else e.mfoldl find_squares s
| s e := e.mfoldl find_squares s

meta def nlinarith_extras : global_preprocessor :=
{ name := "nonlinear arithmetic extras",
  transform := λ ls,
do s ← ls.mfoldr (λ h s', infer_type h >>= find_squares s') mk_rb_set,
   new_es ← s.mfold ([] : list expr) $ λ ⟨e, is_sq⟩ new_es,
     (do p ← mk_app (if is_sq then ``pow_two_nonneg else ``mul_self_nonneg) [e],
      return $ p::new_es),
   new_es ← make_comp_with_zero.globalize.transform new_es,
   linarith_trace "nlinarith preprocessing found squares",
   linarith_trace s,
   linarith_trace_proofs "so we added proofs" new_es,
   with_comps ← (new_es ++ ls).mmap (λ e, do
     tp ← infer_type e,
     return $ (parse_into_comp_and_expr tp).elim (ineq.lt, e) (λ ⟨ine, _⟩, (ine, e))),
   products ← with_comps.mmap_diag $ λ ⟨posa, a⟩ ⟨posb, b⟩,
    match posa, posb with
      | ineq.eq, _ := mk_app ``zero_mul_eq [a, b]
      | _, ineq.eq := mk_app ``mul_zero_eq [a, b]
      | ineq.lt, ineq.lt := mk_app ``mul_pos_of_neg_of_neg [a, b]
      | ineq.lt, ineq.le := do a ← mk_app ``le_of_lt [a], mk_app ``mul_nonneg_of_nonpos_of_nonpos [a, b]
      | ineq.le, ineq.lt := do b ← mk_app ``le_of_lt [b], mk_app ``mul_nonneg_of_nonpos_of_nonpos [a, b]
      | ineq.le, ineq.le := mk_app ``mul_nonneg_of_nonpos_of_nonpos [a, b]
      end,
    products ← make_comp_with_zero.globalize.transform products,
    return $ new_es ++ ls ++ products }

/--
The default list of preprocessors, in the order they should typically run.
-/
meta def default_preprocessors : list global_preprocessor :=
[filter_comparisons, remove_negations, nat_to_int, strengthen_strict_int,
  make_comp_with_zero, cancel_denoms]

/--
`preprocess pps l` takes a list `l` of proofs of propositions.
It maps each preprocessor `pp ∈ pps` over this list.
The preprocessors are run sequentially: each recieves the output of the previous one.
Note that a preprocessor produces a `list expr` for each input `expr`,
so the size of the list may change.
-/
meta def preprocess (pps : list global_preprocessor) (l : list expr) : tactic (list expr) :=
pps.mfoldl (λ l' pp, pp.process l') l


end preprocessing

section
open tactic linarith

/-! ### Control -/

-- return : the type it compares over
meta def apply_contr_lemma : tactic (option (expr × expr)) :=
do t ← target,
   match get_contr_lemma_name_and_type t with
   | some (nm, tp) := do applyc nm, v ← intro1, return $ some (tp, v)
   | none := return none
   end

meta def partition_by_type_aux : rb_lmap expr expr → list expr → tactic (rb_lmap expr expr)
| m [] := return m
| m (h::t) := do tp ← ineq_prf_tp h, partition_by_type_aux (m.insert tp h) t

meta def partition_by_type (l : list expr) : tactic (rb_lmap expr expr) :=
partition_by_type_aux mk_rb_map l



meta def try_linarith_on_lists (cfg : linarith_config) (ls : list (list expr)) : tactic unit :=
(first $ ls.map $ prove_false_by_linarith cfg) <|> fail "linarith failed to find a contradiction"

meta def run_linarith_on_pfs (cfg : linarith_config) (hyps : list expr) (pref_type : option expr) :
  tactic unit :=
do hyps ← preprocess (cfg.preprocessors.get_or_else default_preprocessors) hyps,
   linarith_trace_proofs
     ("after preprocessing, linarith has " ++ to_string hyps.length ++ " facts:") hyps,
   hyp_set ← partition_by_type hyps,
   linarith_trace format!"hypotheses appear in {hyp_set.size} different types",
   match pref_type with
   | some t := prove_false_by_linarith cfg (hyp_set.ifind t) <|>
               try_linarith_on_lists cfg (rb_map.values (hyp_set.erase t))
   | none := try_linarith_on_lists cfg (rb_map.values hyp_set)
   end

meta def filter_hyps_to_type (restr_type : expr) : list expr → tactic (list expr)
| [] := return []
| (h::t) := do ht ← infer_type h,
  match get_contr_lemma_name_and_type ht with
  | some (_, h_type) :=
    do t ← (filter_hyps_to_type t), unify h_type restr_type >> return (h::t) <|> return t
  | none := filter_hyps_to_type t
  end

meta def get_restrict_type (e : expr) : tactic expr :=
do m ← mk_mvar,
   unify `(some %%m : option Type) e,
   instantiate_mvars m

end
end linarith

open linarith tactic
meta def tactic.linarith (reduce_semi : bool) (only_on : bool) (hyps : list pexpr)
  (cfg : linarith_config := {}) : tactic unit :=
do t ← target,
-- if the target is an equality, we run `linarith` twice, to prove ≤ and ≥.
if t.is_eq.is_some then
  linarith_trace "target is an equality: splitting" >>
    seq' (applyc ``eq_of_not_lt_of_not_gt) tactic.linarith else
do when cfg.split_hypotheses (linarith_trace "trying to split hypotheses" >> try auto.split_hyps),
/- If we are proving a comparison goal (and not just `false`), we consider the type of the
   elements in the comparison to be the "preferred" type. That is, if we find comparison
   hypotheses in multiple types, we will run `linarith` on the goal type first.
   In this case we also recieve a new variable from moving the goal to a hypothesis.
   Otherwise, there is no preferred type and no new variable; we simply change the goal to `false`. -/
   pref_type_and_new_var_from_tgt ← apply_contr_lemma,
   when pref_type_and_new_var_from_tgt.is_none $
     if cfg.exfalso then linarith_trace "using exfalso" >> exfalso
     else fail "linarith failed: target is not a valid comparison",
   let cfg := cfg.update_reducibility reduce_semi,
   let (pref_type, new_var) := pref_type_and_new_var_from_tgt.elim (none, none) (λ ⟨a, b⟩, (some a, some b)),
   -- set up the list of hypotheses, considering the `only_on` and `restrict_type` options
   hyps ← hyps.mmap i_to_expr,
   hyps ← if only_on then return (new_var.elim [] singleton ++ hyps) else (++ hyps) <$> local_context,
   hyps ← (do t ← get_restrict_type cfg.restrict_type_reflect, filter_hyps_to_type t hyps) <|> return hyps,
   linarith_trace_proofs "linarith is running on the following hypotheses:" hyps,
   run_linarith_on_pfs cfg hyps pref_type
