import category_theory.limits.limits

universes v w u

namespace category_theory

class has_site (C : Type u) [category.{v} C] : Type (max u v) :=
(cov : Π U : C, set (set (Σ V, V ⟶ U)))
(iso_mem : ∀ {U V : C} (e : V ≅ U), { sigma.mk V e.1 } ∈ cov U)
(comp_mem : ∀ {U : C} (S : set (Σ V, V ⟶ U)) (HS : S ∈ cov U)
  (F : Π m : Σ V, V ⟶ U, m ∈ S → set (Σ V, V ⟶ m.1)),
  (∀ m hm, F m hm ∈ cov m.1) →
  { m | ∃ t ∈ S, ∃ u ∈ F t H, (⟨u.1, u.2 ≫ t.2⟩ : Σ V, V ⟶ U) = m } ∈ cov U)
(pullback_mem : ∀ {U} (S ∈ cov U) (V) (f : V ⟶ U),
  { m | ∃ t ∈ S, (⟨_, pullback.fst f t.2⟩ : Σ W, W ⟶ V) = m } ∈ cov V)

end category_theory
