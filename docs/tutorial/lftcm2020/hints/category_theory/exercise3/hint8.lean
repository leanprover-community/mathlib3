import category_theory.equivalence

open category_theory

variables {C : Type*} [category C]
variables {D : Type*} [category D]

lemma equiv_preserves_mono {X Y : C} (f : X ⟶ Y) [mono f] (e : C ≌ D) :
  mono (e.functor.map f) :=
begin
  tidy,
  replace w := congr_arg (λ k, e.inverse.map k) w,
  simp at w,
  rw [←category.assoc, ←category.assoc, cancel_mono f] at w,
  -- Should be easy from here? See if `simp` can help.
  sorry
end
