import category_theory.functor
import category_theory.eq_to_hom
import category_theory.over

namespace category_theory

universes v v₁ v₂ v₃ u u₁ u₂ u₃

variables {E : Type u₁} [category.{v₁} E] {B : Type u₂} [category.{v₂} B] (p : E ⥤ B)

namespace functor

def fiber (b : B) := { e : E // p.obj e = b }

instance (b : B) : category (p.fiber b) :=
{ hom := λ e₁ e₂, { ψ : e₁.1 ⟶ e₂.1 // p.map ψ = eq_to_hom (by rw [e₁.2, e₂.2]) },
  id := λ e, ⟨𝟙 _, by simp⟩,
  comp := λ _ _ _ ψ₁ ψ₂, ⟨ψ₁.1 ≫ ψ₂.1, by { rw [map_comp, ψ₁.2, ψ₂.2], simp }⟩ }

-- wrong: def fiber_equivalence (b : B) : { f : structured_arrow b p // is_iso f.hom } ≌ p.fiber b :=
def fiber_equivalence (e : E) :
  { f : structured_arrow (p.obj e) p // is_iso f.hom } ≌ p.fiber (p.obj e) :=
{ functor :=
  { obj := λ f, ⟨e, rfl⟩,
    map := , },
  inverse := _,
  unit_iso := _,
  counit_iso := _
}

def fiber_inclusion (b : B) : p.fiber b ⥤ E :=
{ obj := λ e, e.1,
  map := λ _ _ ψ, ψ.1 }

end
