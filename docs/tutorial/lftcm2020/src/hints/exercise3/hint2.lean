import ...for_mathlib.category_theory -- This imports some simp lemmas that I realised belong in mathlib while writing this exercise.

open category_theory

variables {C : Type*} [category C]
variables {D : Type*} [category D]

lemma equiv_reflects_mono {X Y : C} (f : X ⟶ Y) (e : C ≌ D)
  (hef : mono (e.functor.map f)) : mono f :=
begin
  split,
  intros Z g h w,
  -- Let's think about the maths here.
  -- We're trying to prove an equation between morphisms in `C`,
  -- but the only thing we know, namely `hef`, lives over in `D`.
  -- So lets use the injectivity of an equivalence at the level of morphisms:
  apply e.functor.map_injective,
  sorry
end
