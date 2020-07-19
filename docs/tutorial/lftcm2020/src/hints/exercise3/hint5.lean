import ...for_mathlib.category_theory -- This imports some simp lemmas that I realised belong in mathlib while writing this exercise.

open category_theory

variables {C : Type*} [category C]
variables {D : Type*} [category D]

lemma equiv_reflects_mono {X Y : C} (f : X ⟶ Y) (e : C ≌ D)
  (hef : mono (e.functor.map f)) : mono f :=
begin
  split,
  intros Z g h w,
  apply e.functor.map_injective,
  rw ← cancel_mono (e.functor.map f),
  apply e.inverse.map_injective,
  -- That's ugly! In fact, so ugly that surely `simp` can clean things up from here.
  sorry
end
