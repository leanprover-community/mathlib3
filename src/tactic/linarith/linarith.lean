/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/
import tactic.ring
import tactic.linarith.lemmas
import data.tree

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

meta def linarith_trace {α} [has_to_tactic_format α] (s : α) :=
tactic.when_tracing `linarith (tactic.trace s)

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

-- TODO: this isn't symmetric??
def max : ineq → ineq → ineq
| eq a := a
| le a := a
| lt a := lt

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

meta def to_comp_fold (red : transparency) : expr_map ℕ → list expr → rb_map monom ℕ →
      tactic (list (option comp) × expr_map ℕ × rb_map monom ℕ )
| m [] mm := return ([], m, mm)
| m (h::t) mm :=
  (do (c, m', mm') ← to_comp red h m mm,
      (l, mp, mm') ← to_comp_fold m' t mm',
      return (c::l, mp, mm')) <|>
  (do (l, mp, mm') ← to_comp_fold m t mm,
      return (none::l, mp, mm'))

/--
Takes a list of proofs of props of the form `t {<, ≤, =} 0`, and creates a
`linarith_structure`.
-/
meta def mk_linarith_structure (red : transparency) (l : list expr) :
  tactic (linarith_structure × rb_map ℕ (expr × expr)) :=
do pftps ← l.mmap infer_type,
  (l', _, map) ← to_comp_fold red mk_rb_map pftps mk_rb_map,
  let lz := list.enum $ ((l.zip pftps).zip l').filter_map (λ ⟨a, b⟩, prod.mk a <$> b),
  let prmap := rb_map.of_list $ lz.map (λ ⟨n, x⟩, (n, x.1)),
  let vars : rb_set ℕ := rb_map.set_of_list $ list.range map.size,
  let pc : rb_set pcomp :=
    rb_set.of_list_core mk_pcomp_set $ lz.map (λ ⟨n, x⟩, ⟨x.2, comp_source.assump n⟩),
  return (⟨vars, pc⟩, prmap)

meta def linarith_monad.run (red : transparency) {α} (tac : linarith_monad α) (l : list expr) :
  tactic ((pcomp ⊕ α) × rb_map ℕ (expr × expr)) :=
do (struct, inputs) ← mk_linarith_structure red l,
match (state_t.run (validate >> tac) struct).run with
| (except.ok (a, _)) := return (sum.inr a, inputs)
| (except.error contr) := return (sum.inl contr, inputs)
end

end parse

section prove
open ineq tactic

meta def get_rel_sides : expr → tactic (expr × expr)
| `(%%a < %%b) := return (a, b)
| `(%%a ≤ %%b) := return (a, b)
| `(%%a = %%b) := return (a, b)
| `(%%a ≥ %%b) := return (a, b)
| `(%%a > %%b) := return (a, b)
| _ := failed

meta def mul_expr (n : ℕ) (e : expr) : pexpr :=
if n = 1 then ``(%%e) else
``(%%(nat.to_pexpr n) * %%e)

meta def add_exprs_aux : pexpr → list pexpr → pexpr
| p [] := p
| p [a] := ``(%%p + %%a)
| p (h::t) := add_exprs_aux ``(%%p + %%h) t

meta def add_exprs : list pexpr → pexpr
| [] := ``(0)
| (h::t) := add_exprs_aux h t

meta def find_contr (m : rb_set pcomp) : option pcomp :=
m.keys.find (λ p, p.c.is_contr)

meta def ineq_const_mul_nm : ineq → name
| lt := ``mul_neg
| le := ``mul_nonpos
| eq := ``mul_eq

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

meta def mk_single_comp_zero_pf (c : ℕ) (h : expr) : tactic (ineq × expr) :=
do tp ← infer_type h,
  some (iq, e) ← return $ parse_into_comp_and_expr tp,
  if c = 0 then
    do e' ← mk_app ``zero_mul [e], return (eq, e')
  else if c = 1 then return (iq, h)
  else
    do nm ← resolve_name (ineq_const_mul_nm iq),
       tp ← (prod.snd <$> (infer_type h >>= get_rel_sides)) >>= infer_type,
       cpos ← to_expr ``((%%c.to_pexpr : %%tp) > 0),
       (_, ex) ← solve_aux cpos `[norm_num, done],
--       e' ← mk_app (ineq_const_mul_nm iq) [h, ex], -- this takes many seconds longer in some examples! why?
       e' ← to_expr ``(%%nm %%h %%ex) ff,
       return (iq, e')

meta def mk_lt_zero_pf_aux (c : ineq) (pf npf : expr) (coeff : ℕ) : tactic (ineq × expr) :=
do (iq, h') ← mk_single_comp_zero_pf coeff npf,
   let (nm, niq) := ineq_const_nm c iq,
   n ← resolve_name nm,
   e' ← to_expr ``(%%n %%pf %%h'),
   return (niq, e')

/--
Takes a list of coefficients `[c]` and list of expressions, of equal length.
Each expression is a proof of a prop of the form `t {<, ≤, =} 0`.
Produces a proof that the sum of `(c*t) {<, ≤, =} 0`,
where the `comp` is as strong as possible.
-/
meta def mk_lt_zero_pf : list ℕ → list expr → tactic expr
| _ [] := fail "no linear hypotheses found"
| [c] [h] := prod.snd <$> mk_single_comp_zero_pf c h
| (c::ct) (h::t) :=
  do (iq, h') ← mk_single_comp_zero_pf c h,
     prod.snd <$> (ct.zip t).mfoldl (λ pr ce, mk_lt_zero_pf_aux pr.1 pr.2 ce.2 ce.1) (iq, h')
| _ _ := fail "not enough args to mk_lt_zero_pf"

meta def term_of_ineq_prf (prf : expr) : tactic expr :=
do (lhs, _) ← infer_type prf >>= get_rel_sides,
   return lhs

meta structure linarith_config :=
(discharger : tactic unit := `[ring])
(restrict_type : option Type := none)
(restrict_type_reflect : reflected restrict_type . apply_instance)
(exfalso : bool := tt)
(transparency : transparency := reducible)
(split_hypotheses : bool := tt)
(nonlinear_preprocessing : bool := ff)

meta def linarith_config.update_reducibility (cfg : linarith_config) (reduce_semi : bool) :
  linarith_config :=
if reduce_semi then { cfg with transparency := semireducible, discharger := `[ring!] }
else cfg

meta def ineq_pf_tp (pf : expr) : tactic expr :=
do (_, z) ← infer_type pf >>= get_rel_sides,
   infer_type z

meta def mk_neg_one_lt_zero_pf (tp : expr) : tactic expr :=
to_expr ``((neg_neg_of_pos zero_lt_one : -1 < (0 : %%tp)))

/--
Assumes `e` is a proof that `t = 0`. Creates a proof that `-t = 0`.
-/
meta def mk_neg_eq_zero_pf (e : expr) : tactic expr :=
to_expr ``(neg_eq_zero.mpr %%e)

meta def add_neg_eq_pfs : list expr → tactic (list expr)
| [] := return []
| (h::t) :=
  do some (iq, tp) ← parse_into_comp_and_expr <$> infer_type h,
  match iq with
  | ineq.eq := do nep ← mk_neg_eq_zero_pf h, tl ← add_neg_eq_pfs t, return $ h::nep::tl
  | _ := list.cons h <$> add_neg_eq_pfs t
  end

/--
Takes a list of proofs of propositions of the form `t {<, ≤, =} 0`,
and tries to prove the goal `false`.
-/
meta def prove_false_by_linarith1 (cfg : linarith_config) : list expr → tactic unit
| [] := fail "no args to linarith"
| l@(h::t) :=
  do l' ← add_neg_eq_pfs l,
     hz ← ineq_pf_tp h >>= mk_neg_one_lt_zero_pf,
     (sum.inl contr, inputs) ← elim_all_vars.run cfg.transparency (hz::l')
       | fail "linarith failed to find a contradiction",
     let coeffs := inputs.keys.map (λ k, (contr.src.flatten.ifind k)),
     let pfs : list expr := inputs.keys.map (λ k, (inputs.ifind k).1),
     let zip := (coeffs.zip pfs).filter (λ pr, pr.1 ≠ 0),
     let (coeffs, pfs) := zip.unzip,
     mls ← zip.mmap (λ pr, do e ← term_of_ineq_prf pr.2, return (mul_expr pr.1 e)),
     sm ← to_expr $ add_exprs mls,
     tgt ← to_expr ``(%%sm = 0),
     (a, b) ← solve_aux tgt (cfg.discharger >> done),
     pf ← mk_lt_zero_pf coeffs pfs,
     pftp ← infer_type pf,
     (_, nep, _) ← rewrite_core b pftp,
     pf' ← mk_eq_mp nep pf,
     mk_app `lt_irrefl [pf'] >>= exact

end prove

section normalize
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

meta def is_numeric : expr → option ℚ
| `(%%e1 + %%e2) := (+) <$> is_numeric e1 <*> is_numeric e2
| `(%%e1 - %%e2) := has_sub.sub <$> is_numeric e1 <*> is_numeric e2
| `(%%e1 * %%e2) := (*) <$> is_numeric e1 <*> is_numeric e2
| `(%%e1 / %%e2) := (/) <$> is_numeric e1 <*> is_numeric e2
| `(-%%e) := rat.neg <$> is_numeric e
| e := e.to_rat

meta def find_cancel_factor : expr → ℕ × tree ℕ
| `(%%e1 + %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, lcm := v1.lcm v2 in
  (lcm, tree.node lcm t1 t2)
| `(%%e1 - %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, lcm := v1.lcm v2 in
  (lcm, tree.node lcm t1 t2)
| `(%%e1 * %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, pd := v1*v2 in
  (pd, tree.node pd t1 t2)
| `(%%e1 / %%e2) :=
  match is_numeric e2 with
  | some q := let (v1, t1) := find_cancel_factor e1, n := v1.lcm q.num.nat_abs in
    (n, tree.node n t1 (tree.node q.num.nat_abs tree.nil tree.nil))
  | none := (1, tree.node 1 tree.nil tree.nil)
  end
| `(-%%e) := find_cancel_factor e
| _ := (1, tree.node 1 tree.nil tree.nil)

open tree

meta def mk_prod_prf : ℕ → tree ℕ → expr → tactic expr
| v (node _ lhs rhs) `(%%e1 + %%e2) :=
  do v1 ← mk_prod_prf v lhs e1, v2 ← mk_prod_prf v rhs e2, mk_app ``add_subst [v1, v2]
| v (node _ lhs rhs) `(%%e1 - %%e2) :=
  do v1 ← mk_prod_prf v lhs e1, v2 ← mk_prod_prf v rhs e2, mk_app ``sub_subst [v1, v2]
| v (node n lhs@(node ln _ _) rhs) `(%%e1 * %%e2) :=
  do tp ← infer_type e1, v1 ← mk_prod_prf ln lhs e1, v2 ← mk_prod_prf (v/ln) rhs e2,
     ln' ← tp.of_nat ln, vln' ← tp.of_nat (v/ln), v' ← tp.of_nat v,
     ntp ← to_expr ``(%%ln' * %%vln' = %%v'),
     (_, npf) ← solve_aux ntp `[norm_num, done],
     mk_app ``mul_subst [v1, v2, npf]
| v (node n lhs rhs@(node rn _ _)) `(%%e1 / %%e2) :=
  do tp ← infer_type e1, v1 ← mk_prod_prf (v/rn) lhs e1,
     rn' ← tp.of_nat rn, vrn' ← tp.of_nat (v/rn), n' ← tp.of_nat n, v' ← tp.of_nat v,
     ntp ← to_expr ``(%%rn' / %%e2 = 1),
     (_, npf) ← solve_aux ntp `[norm_num, done],
     ntp2 ← to_expr ``(%%vrn' * %%n' = %%v'),
     (_, npf2) ← solve_aux ntp2 `[norm_num, done],
     mk_app ``div_subst [v1, npf, npf2]
| v t `(-%%e) := do v' ← mk_prod_prf v t e, mk_app ``neg_subst [v']
| v _ e :=
  do tp ← infer_type e,
     v' ← tp.of_nat v,
     e' ← to_expr ``(%%v' * %%e),
     mk_app `eq.refl [e']

/--
Given `e`, a term with rational division, produces a natural number `n` and a proof of `n*e = e'`,
where `e'` has no division.
-/
meta def kill_factors (e : expr) : tactic (ℕ × expr) :=
let (n, t) := find_cancel_factor e in
do e' ← mk_prod_prf n t e, return (n, e')

/--
`normalize_denominators_in_lhs h lhs` assumes that `h` is a proof of `lhs R 0`.
It creates a proof of `lhs' R 0`, where all numeric division in `lhs` has been cancelled.
-/
meta def normalize_denominators_in_lhs (h lhs : expr) : tactic expr :=
do (v, lhs') ← kill_factors lhs,
   if v = 1 then return h else do
   (ih, h'') ← mk_single_comp_zero_pf v h,
   (_, nep, _) ← infer_type h'' >>= rewrite_core lhs',
   mk_eq_mp nep h''

meta def get_contr_lemma_name : expr → option name
| `(%%a < %%b) := return `lt_of_not_ge
| `(%%a ≤ %%b) := return `le_of_not_gt
| `(%%a = %%b) := return ``eq_of_not_lt_of_not_gt
| `(%%a ≠ %%b) := return `not.intro
| `(%%a ≥ %%b) := return `le_of_not_gt
| `(%%a > %%b) := return `lt_of_not_ge
| `(¬ %%a < %%b) := return `not.intro
| `(¬ %%a ≤ %%b) := return `not.intro
| `(¬ %%a = %%b) := return `not.intro
| `(¬ %%a ≥ %%b) := return `not.intro
| `(¬ %%a > %%b) := return `not.intro
| _ := none

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

/-- Assumes the input `t` is of type `ℕ`. Produces `t'` of type `ℤ` such that `↑t = t'` and
a proof of equality. -/
meta def cast_expr (e : expr) : tactic (expr × expr) :=
do s ← [`int.coe_nat_add, `int.coe_nat_zero, `int.coe_nat_one,
        ``int.coe_nat_bit0_mul, ``int.coe_nat_bit1_mul, ``int.coe_nat_zero_mul, ``int.coe_nat_one_mul,
        ``int.coe_nat_mul_bit0, ``int.coe_nat_mul_bit1, ``int.coe_nat_mul_zero, ``int.coe_nat_mul_one,
        ``int.coe_nat_bit0, ``int.coe_nat_bit1].mfoldl simp_lemmas.add_simp simp_lemmas.mk,
   ce ← to_expr ``(↑%%e : ℤ),
   simplify s [] ce {fail_if_unchanged := ff}

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

meta def mk_cast_eq_and_nonneg_prfs (pf a b : expr) (ln : name) : tactic (list expr) :=
do (a', prfa) ← cast_expr a,
   (b', prfb) ← cast_expr b,
   la ← mk_coe_nat_nonneg_prfs a',
   lb ← mk_coe_nat_nonneg_prfs b',
   pf' ← mk_app ln [pf, prfa, prfb],
   return $ pf'::(la.append lb)

meta def mk_int_pfs_of_nat_pf (pf : expr) : tactic (list expr) :=
do tp ← infer_type pf,
match tp with
| `(%%a = %%b) := mk_cast_eq_and_nonneg_prfs pf a b ``nat_eq_subst
| `(%%a ≤ %%b) := mk_cast_eq_and_nonneg_prfs pf a b ``nat_le_subst
| `(%%a < %%b) := mk_cast_eq_and_nonneg_prfs pf a b ``nat_lt_subst
| `(%%a ≥ %%b) := mk_cast_eq_and_nonneg_prfs pf b a ``nat_le_subst
| `(%%a > %%b) := mk_cast_eq_and_nonneg_prfs pf b a ``nat_lt_subst
| `(¬ %%a ≤ %%b) := do pf' ← mk_app ``lt_of_not_ge [pf], mk_cast_eq_and_nonneg_prfs pf' b a ``nat_lt_subst
| `(¬ %%a < %%b) := do pf' ← mk_app ``le_of_not_gt [pf], mk_cast_eq_and_nonneg_prfs pf' b a ``nat_le_subst
| `(¬ %%a ≥ %%b) := do pf' ← mk_app ``lt_of_not_ge [pf], mk_cast_eq_and_nonneg_prfs pf' a b ``nat_lt_subst
| `(¬ %%a > %%b) := do pf' ← mk_app ``le_of_not_gt [pf], mk_cast_eq_and_nonneg_prfs pf' a b ``nat_le_subst
| _ := fail "mk_int_pfs_of_nat_pf failed: proof is not an inequality"
end

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

meta def partition_by_type_aux : rb_lmap expr expr → list expr → tactic (rb_lmap expr expr)
| m [] := return m
| m (h::t) := do tp ← ineq_pf_tp h, partition_by_type_aux (m.insert tp h) t

meta def partition_by_type (l : list expr) : tactic (rb_lmap expr expr) :=
partition_by_type_aux mk_rb_map l

meta def try_linarith_on_lists (cfg : linarith_config) (ls : list (list expr)) : tactic unit :=
(first $ ls.map $ prove_false_by_linarith1 cfg) <|> fail "linarith failed"

/--
A preprocessor transforms a proof of a proposition into a proof of a different propositon.
The return type is `list expr`, since some preprocessing steps may create multiple new hypotheses,
and some may remove a hypothesis from the list.
A "no-op" preprocessor should return its input as a singleton list.
-/
meta def preprocessor : Type := expr → tactic (list expr)

private meta def filter_comparisons_aux : expr → bool
| `(¬ %%p) := p.app_symbol_in [`has_lt.lt, `has_le.le, `gt, `ge]
| tp := tp.app_symbol_in [`has_lt.lt, `has_le.le, `gt, `ge, `eq]

/--
Removes any expressions that are not proofs of inequalities, equalities, or negations thereof.
-/
meta def filter_comparisons : preprocessor := λ h,
(do tp ← infer_type h,
   is_prop tp >>= guardb,
   guardb (filter_comparisons_aux tp),
   return [h])
<|> return []

/--
If `h` is an equality or inequality between natural numbers,
`nat_to_int h` lifts this inequality to the integers,
adding the facts that the integers involved are nonnegative.
 -/
meta def nat_to_int : preprocessor := λ h,
do tp ← infer_type h,
   guardb (is_nat_prop tp) >> mk_int_pfs_of_nat_pf h <|> return [h]

/-- `strengthen_strict_int h` turns a proof `h` of a strict integer inequality `t1 < t2`
into a proof of `t1 ≤ t2 + 1`. -/
meta def strengthen_strict_int : preprocessor := λ h,
do tp ← infer_type h,
   guardb (is_strict_int_prop tp) >> singleton <$> mk_non_strict_int_pf_of_strict_int_pf h
     <|> return [h]

/--
`mk_comp_with_zero h` takes a proof `h` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <}`.
 -/
meta def make_comp_with_zero : preprocessor :=
λ e, singleton <$> rearr_comp e <|> return []

/--
`cancel_denoms pf` assumes `pf` is a proof of `t R 0`. If `t` contains the division symbol `/`,
it tries to scale `t` to cancel out division by numerals.
-/
meta def cancel_denoms : preprocessor := λ pf,
(do some (_, lhs) ← parse_into_comp_and_expr <$> infer_type pf,
   guardb $ lhs.contains_constant (= `has_div.div),
   singleton <$> normalize_denominators_in_lhs pf lhs)
<|> return [pf]


meta def global_preprocessor : Type := list expr → tactic (list expr)

meta def preprocessor.globalize (pp : preprocessor) : global_preprocessor := λ l,
do l' ← list.mfoldl (λ ret e, do l' ← pp e, return (l' ++ ret)) [] l,
   linarith_trace_proofs "preprocessing produced" l',
   return l'

/--
`find_squares m e` collects all terms of the form `a ^ 2` and `a * a` that appear in `e`
and adds them to the set `m`.
A pair `(a, tt)` is added to `m` when `a^2` appears in `e`, and `(a, ff)` is added to `m`
when `a*a` appears in `e`.  -/
meta def find_squares : rb_set (expr × bool) → expr → tactic (rb_set (expr × bool))
| s `(%%a ^ 2) := do s ← find_squares s a, return (s.insert (a, tt))
| s e@`(%%e1 * %%e2) := if e1 = e2 then do s ← find_squares s e1, return (s.insert (e1, ff)) else e.mfoldl find_squares s
| s e := e.mfoldl find_squares s

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unused_arguments]
lemma mul_zero_eq {α} {R : α → α → Prop} [semiring α] {a b : α} (_ : R a 0) (h : b = 0) : a * b = 0 :=
by simp [h]

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unused_arguments]
lemma zero_mul_eq {α} {R : α → α → Prop} [semiring α] {a b : α} (h : a = 0) (_ : R b 0) : a * b = 0 :=
by simp [h]

meta def nlinarith_extras : global_preprocessor := λ ls,
do s ← ls.mfoldr (λ h s', infer_type h >>= find_squares s') mk_rb_set,
   new_es ← s.mfold ([] : list expr) $ λ ⟨e, is_sq⟩ new_es,
     (do p ← mk_app (if is_sq then ``pow_two_nonneg else ``mul_self_nonneg) [e],
      return $ p::new_es),
   new_es ← make_comp_with_zero.globalize new_es,
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
    products ← make_comp_with_zero.globalize products,
    return $ new_es ++ ls ++ products
/--
`preprocess pps l` takes a list `l` of proofs of propositions.
It maps each preprocessor `pp ∈ pps` over this list.
The preprocessors are run sequentially: each recieves the output of the previous one.
Note that a preprocessor produces a `list expr` for each input `expr`,
so the size of the list may change.
-/
meta def preprocess (pps : list global_preprocessor) (l : list expr) : tactic (list expr) :=
pps.mfoldl (λ l' pp, pp l') l

-- return : the type it compares over
meta def apply_contr_lemma : tactic (option (expr × expr)) :=
do t ← target,
   match get_contr_lemma_name_and_type t with
   | some (nm, tp) := do applyc nm, v ← intro1, return $ some (tp, v)
   | none := return none
   end

meta def run_linarith_on_pfs (cfg : linarith_config) (hyps : list expr) (pref_type : option expr) :
  tactic unit :=
let preprocessors :=
  [filter_comparisons, nat_to_int, strengthen_strict_int, make_comp_with_zero, cancel_denoms],
    preprocessors := preprocessors.map preprocessor.globalize,
    preprocessors := preprocessors ++ if cfg.nonlinear_preprocessing then [nlinarith_extras] else [] in
do hyps ← preprocess preprocessors hyps,
   linarith_trace_proofs ("after preprocessing, linarith has " ++ to_string hyps.length ++ " facts:") hyps,
   hyp_set ← partition_by_type hyps,
   linarith_trace "hypotheses appear in the following types:",
   linarith_trace hyp_set.keys,
   match pref_type with
   | some t := prove_false_by_linarith1 cfg (hyp_set.ifind t) <|>
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
end normalize
end linarith

section
open linarith tactic
meta def tactic.linarith (reduce_semi : bool) (only_on : bool) (hyps : list pexpr)
  (cfg : linarith_config := {}) : tactic unit :=
do t ← target,
if t.is_eq.is_some then
  linarith_trace "target is an equality: splitting" >>
    seq' (applyc ``eq_of_not_lt_of_not_gt) tactic.linarith else
do when cfg.split_hypotheses (linarith_trace "trying to split hypotheses" >> try auto.split_hyps),
   pref_type_from_tgt ← apply_contr_lemma,
   when pref_type_from_tgt.is_none $
     if cfg.exfalso then linarith_trace "using exfalso" >> exfalso
     else fail "linarith failed: target is not a valid comparison",
   let cfg := (cfg.update_reducibility reduce_semi),
   let (pref_type, new_var) := pref_type_from_tgt.elim (none, none) (λ ⟨a, b⟩, (some a, some b)),
   hyps ← hyps.mmap i_to_expr,
   hyps ← if only_on then return (new_var.elim [] (λ e, [e]) ++ hyps) else (++ hyps) <$> local_context,
   hyps ← (do t ← get_restrict_type cfg.restrict_type_reflect, filter_hyps_to_type t hyps) <|> return hyps,
   linarith_trace_proofs "linarith is running on the following hypotheses:" hyps,
   run_linarith_on_pfs cfg hyps pref_type

open lean lean.parser interactive tactic interactive.types
local postfix `?`:9001 := optional
local postfix *:9001 := many

/--
Tries to prove a goal of `false` by linear arithmetic on hypotheses.
If the goal is a linear (in)equality, tries to prove it by contradiction.
If the goal is not `false` or an inequality, applies `exfalso` and tries linarith on the
hypotheses.

* `linarith` will use all relevant hypotheses in the local context.
* `linarith [t1, t2, t3]` will add proof terms t1, t2, t3 to the local context.
* `linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
  `h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.
* `linarith!` will use a stronger reducibility setting to identify atoms.

Config options:
* `linarith {exfalso := ff}` will fail on a goal that is neither an inequality nor `false`
* `linarith {restrict_type := T}` will run only on hypotheses that are inequalities over `T`
* `linarith {discharger := tac}` will use `tac` instead of `ring` for normalization.
  Options: `ring2`, `ring SOP`, `simp`
* `linarith {split_hypotheses := ff}` will not destruct conjunctions in the context.
-/
meta def tactic.interactive.linarith (red : parse ((tk "!")?))
  (restr : parse ((tk "only")?)) (hyps : parse pexpr_list?)
  (cfg : linarith_config := {}) : tactic unit :=
tactic.linarith red.is_some restr.is_some (hyps.get_or_else []) cfg

add_hint_tactic "linarith"

/--
`linarith` attempts to find a contradiction between hypotheses that are linear (in)equalities.
Equivalently, it can prove a linear inequality by assuming its negation and proving `false`.

In theory, `linarith` should prove any goal that is true in the theory of linear arithmetic over
the rationals. While there is some special handling for non-dense orders like `nat` and `int`,
this tactic is not complete for these theories and will not prove every true goal.

An example:
```lean
example (x y z : ℚ) (h1 : 2*x  < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0)  : false :=
by linarith
```

`linarith` will use all appropriate hypotheses and the negation of the goal, if applicable.

`linarith [t1, t2, t3]` will additionally use proof terms `t1, t2, t3`.

`linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
`h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

`linarith!` will use a stronger reducibility setting to try to identify atoms. For example,
```lean
example (x : ℚ) : id x ≥ x :=
by linarith
```
will fail, because `linarith` will not identify `x` and `id x`. `linarith!` will.
This can sometimes be expensive.

`linarith {discharger := tac, restrict_type := tp, exfalso := ff}` takes a config object with five
optional arguments:
* `discharger` specifies a tactic to be used for reducing an algebraic equation in the
  proof stage. The default is `ring`. Other options currently include `ring SOP` or `simp` for basic
  problems.
* `restrict_type` will only use hypotheses that are inequalities over `tp`. This is useful
  if you have e.g. both integer and rational valued inequalities in the local context, which can
  sometimes confuse the tactic.
* `transparency` controls how hard `linarith` will try to match atoms to each other. By default
  it will only unfold `reducible` definitions.
* If `split_hypotheses` is true, `linarith` will split conjunctions in the context into separate
  hypotheses.
* If `exfalso` is false, `linarith` will fail when the goal is neither an inequality nor `false`.
  (True by default.)

A variant, `nlinarith`, does some basic preprocessing to handle some nonlinear goals.
-/
add_tactic_doc
{ name       := "linarith",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.linarith],
  tags       := ["arithmetic", "decision procedure", "finishing"] }

/--
An extension of `linarith` with some preprocessing to allow it to solve some nonlinear arithmetic
problems. (Based on Coq's `nra` tactic.) See `linarith` for the available syntax of options,
which are inherited by `nlinarith`; that is, `nlinarith!` and `nlinarith only [h1, h2]` all work as
in `linarith`. The preprocessing is as follows:

* For every subterm `a ^ 2` or `a * a` in a hypothesis or the goal,
  the assumption `0 ≤ a ^ 2` or `0 ≤ a * a` is added to the context.
* For every pair of hypotheses `a1 R1 b1`, `a2 R2 b2` in the context, `R1, R2 ∈ {<, ≤, =}`,
  the assumption `0 R' (b1 - a1) * (b2 - a2)` is added to the context (non-recursively),
  where `R ∈ {<, ≤, =}` is the appropriate comparison derived from `R1, R2`.
-/
meta def tactic.interactive.nlinarith (red : parse ((tk "!")?))
  (restr : parse ((tk "only")?)) (hyps : parse pexpr_list?)
  (cfg : linarith_config := {}) : tactic unit :=
tactic.linarith red.is_some restr.is_some (hyps.get_or_else []) {cfg with nonlinear_preprocessing := tt}

add_hint_tactic "nlinarith"

add_tactic_doc
{ name       := "nlinarith",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.nlinarith],
  tags       := ["arithmetic", "decision procedure", "finishing"] }

end
