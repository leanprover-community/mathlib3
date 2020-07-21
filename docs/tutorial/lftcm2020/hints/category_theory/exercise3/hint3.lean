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
  -- That looks pretty good, we're in a position where we can apply `hef`.
  -- The relevant lemma is `cancel_mono`, which says
  --   `g ≫ f = h ≫ f ↔ g = h ` whenever `f` is a mono
  -- This is an iff, so we can either using `rw ←cancel_mono ...` or `apply (cancel_mono ...).1`.
  sorry,
end
