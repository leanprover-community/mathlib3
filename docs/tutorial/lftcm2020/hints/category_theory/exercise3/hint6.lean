import category_theory.equivalence

open category_theory

variables {C : Type*} [category C]
variables {D : Type*} [category D]

/-!
Let's get started on the second half of the exercise.
-/

lemma equiv_preserves_mono {X Y : C} (f : X ⟶ Y) [mono f] (e : C ≌ D) :
  mono (e.functor.map f) :=
begin
  -- Again I've started with:
  tidy,
  -- Now we want to map the equation in `w` over to `C`.
  -- This is actually a bit of a hassle, and probably deserves custom tactic support. Want to help?
  replace w := congr_arg (λ k, e.inverse.map k) w,
  simp at w,
  sorry

end
