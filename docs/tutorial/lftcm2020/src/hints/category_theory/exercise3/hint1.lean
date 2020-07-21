import ...for_mathlib.category_theory -- This imports some simp lemmas that I realised belong in mathlib while writing this exercise.

open category_theory

variables {C : Type*} [category C]
variables {D : Type*} [category D]

lemma equiv_reflects_mono {X Y : C} (f : X ⟶ Y) (e : C ≌ D)
  (hef : mono (e.functor.map f)) : mono f :=
begin
  -- My first instinct is always to call `tidy`, to see how far it gets:
  tidy,

  -- It seems it unfolded the definition of `mono` in the goal for us,
  -- and introduced some new hypotheses. That seems pretty reasonable for this problem!

  -- If you like, you can ask `tidy` what it did by calling `tidy?`.
  -- Often some human intervention is required to clean up the output,
  -- but on this occasion it's pretty good.
  sorry
end
