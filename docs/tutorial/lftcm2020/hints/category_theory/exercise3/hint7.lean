import ...for_mathlib.category_theory -- This imports some simp lemmas that I realised belong in mathlib while writing this exercise.

open category_theory

variables {C : Type*} [category C]
variables {D : Type*} [category D]


lemma equiv_preserves_mono {X Y : C} (f : X ⟶ Y) [mono f] (e : C ≌ D) :
  mono (e.functor.map f) :=
begin
  tidy,
  replace w := congr_arg (λ k, e.inverse.map k) w,
  simp at w,
  -- We can see that `w` is now in a position that we can use the hyothesis `mono f`.
  -- However there's a problem, which is that `A ≫ B ≫ C` is implicitly right-associated,
  -- so we can't directly use `rw cancel_mono f at w`.
  -- We first need to shuffle the parentheses around using associativity:
  rw [←category.assoc] at w, -- and maybe a second time?
  sorry
end
