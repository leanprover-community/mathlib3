/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.finsupp.lex

/-!
# Addition on `α →₀ N` need not be monotone, when it is monotone on `N`

This example addresses a comment in `data.finsupp.lex` to the effect that the proof that addition
is monotone on `α →₀ N` uses that it is *strictly* monotone on `N`.

The specific statement is about `finsupp.lex.covariant_class_le_left` and its analogue
`finsupp.lex.covariant_class_le_right`.  We do not need two separate counterexamples, since the
operation is commutative.

The example is very simple.  Let `F = {0, 1}` with order determined by `0 < 1` and absorbing
addition (which is the same as `max` in this case).  We denote a function `f : F → F` (which is
automatically finitely supported!) by `[f 0, f 1]`, listing its values.  Recall that the order on
finitely supported function is lexicographic, matching the list notation.  The inequality
`[0, 1] ≤ [1, 0]` holds.  However, adding `[1, 0]` to both sides yields the *reversed* inequality
`[1, 1] > [1, 0]`.
-/
open finsupp
/--  `F` is the type with two elements `zero` and `one`.  We define the "obvious" linear order and
absorbing addition on it to generate our counterexample. -/
@[derive [decidable_eq, inhabited]] inductive F | zero | one

/--  The same as `list.get_rest`, except that we take the "rest" from the first match, rather than
from the beginning, returning `[]` if there is no match.  For instance,
```lean
#eval [1,2].drop_until [3,1,2,4,1,2]  -- [4, 1, 2]
```
-/
def list.drop_until {α} [decidable_eq α] : list α → list α → list α
| l [] := []
| l (a::as) := ((a::as).get_rest l).get_or_else (l.drop_until as)

/-- `guard_decl_in_file na loc` makes sure that the declaration with name `na` is in the file with
relative path `"src/" ++ "/".intercalate loc ++ ".lean"`.
```lean
#eval guard_decl_in_file `nat.nontrivial ["data", "nat", "basic"]  -- does nothing

#eval guard_decl_in_file `nat.nontrivial ["not", "in", "here"]
-- fails giving the location 'data/nat/basic.lean'
```

This test makes sure that the comment referring to this example is in the file claimed in the
doc-module to this counterexample. -/
meta def guard_decl_in_file (na : name) (loc : list string) : tactic unit :=
do env ← tactic.get_env,
  some fil ← pure $ env.decl_olean na | fail!"the instance `{na}` is not imported!",
  let path : string := ⟨list.drop_until "/src/".to_list fil.to_list⟩,
  let locdot : string := ".".intercalate loc,
  guard (fil.ends_with ("src/" ++ "/".intercalate loc ++ ".lean")) <|>
    fail!("instance `{na}` is no longer in `{locdot}`.\n\n" ++
      "Please, update the doc-module and this check with the correct location:\n\n'{path}'\n")

#eval guard_decl_in_file `finsupp.lex.covariant_class_le_left ["data", "finsupp", "lex"]
#eval guard_decl_in_file `finsupp.lex.covariant_class_le_right ["data", "finsupp", "lex"]

namespace F

instance : has_zero F := ⟨F.zero⟩

/--  `1` is not really needed, but it is nice to use the notation. -/
instance : has_one F := ⟨F.one⟩

/--  A tactic to prove trivial goals by enumeration. -/
meta def boom : tactic unit :=
`[ repeat { rintro ⟨⟩ }; dec_trivial ]

/--  `aux` maps `0 1 : F` to their counterparts in `ℕ`.
We use it to lift the linear order on `N`. -/
def aux : ∀ a : F, ℕ
| 0 := 0
| 1 := 1

instance : linear_order F := linear_order.lift' aux (by boom)

@[simp] lemma z01  : (0 : F) < 1 := by boom

/--  `F` would be a `comm_semiring`, using `min` as multiplication.  Again, we do not need this. -/
instance : add_comm_monoid F :=
{ add       := max,
  add_assoc := by boom,
  zero      := 0,
  zero_add  := by boom,
  add_zero  := by boom,
  add_comm  := by boom }

instance covariant_class_add_le : covariant_class F F (+) (≤) := ⟨by boom⟩

/--  The following examples show that `F` has all the typeclasses used by
`finsupp.lex.covariant_class_le_left`... -/
example : linear_order F := by apply_instance
example : add_monoid F   := by apply_instance
example : covariant_class F F (function.swap (+)) (≤) := by apply_instance

/-- ... except for the strict monotonicity of addition, the crux of the matter. -/
example : ¬ covariant_class F F (+) (<) := λ h, lt_irrefl 1 $ (h.elim : covariant F F (+) (<)) 1 z01

/--  A few `simp`-lemmas to take care of trivialities in the proof of the example below. -/
@[simp] lemma f1   : ∀ (a : F), 1 + a = 1 := by boom
@[simp] lemma f011 : of_lex (single (0 : F) (1 : F)) 1 = 0 := single_apply_eq_zero.mpr (λ h, h)
@[simp] lemma f010 : of_lex (single (0 : F) (1 : F)) 0 = 1 := single_eq_same
@[simp] lemma f111 : of_lex (single (1 : F) (1 : F)) 1 = 1 := single_eq_same
@[simp] lemma f110 : of_lex (single (1 : F) (1 : F)) 0 = 0 := single_apply_eq_zero.mpr (λ h, h.symm)

/--  Here we see that (not-necessarily strict) monotonicity of addition on `lex (F →₀ F)` is not
a consequence of monotonicity of addition on `F`.  Strict monotonicity of addition on `F` is
enough and is the content of `finsupp.lex.covariant_class_le_left`. -/
example : ¬ covariant_class (lex (F →₀ F)) (lex (F →₀ F)) (+) (≤) :=
begin
  rintro ⟨h⟩,
  refine not_lt.mpr (h (single (0 : F) (1 : F)) (_ : single 1 1 ≤ single 0 1)) ⟨1, _⟩,
  { exact or.inr ⟨0, by simp [(by boom : ∀ j : F, j < 0 ↔ false)]⟩ },
  { simp only [(by boom : ∀ j : F, j < 1 ↔ j = 0), of_lex_add, coe_add, pi.to_lex_apply,
      pi.add_apply, forall_eq, f010, f1, eq_self_iff_true, f011, f111, zero_add, and_self] },
end

end F
