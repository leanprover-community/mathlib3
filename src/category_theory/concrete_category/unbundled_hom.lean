import category_theory.concrete_category.bundled_hom

universes v u

namespace category_theory

class unbundled_hom {c : Type u → Type v} (hom : Π {α β}, c α → c β → (α → β) → Prop) :=
(hom_id : ∀ {α} (ia : c α), hom ia ia id)
(hom_comp : ∀ {α β γ} {Iα : c α} {Iβ : c β} {Iγ : c γ} {g : β → γ} {f : α → β}
  (hg : hom Iβ Iγ g) (hf : hom Iα Iβ f), hom Iα Iγ (g ∘ f))

namespace unbundled_hom

variables (c : Type u → Type v) (hom : Π ⦃α β⦄, c α → c β → (α → β) → Prop) [𝒞 : unbundled_hom hom]
include 𝒞

instance bundled_hom : bundled_hom (λ α β (Iα : c α) (Iβ : c β), subtype (hom Iα Iβ)) :=
{ to_fun := λ _ _ _ _, subtype.val,
  id := λ α Iα, ⟨id, hom_id hom Iα⟩,
  id_to_fun := by intros; refl,
  comp := λ _ _ _ _ _ _ g f, ⟨g.1 ∘ f.1, hom_comp c g.2 f.2⟩,
  comp_to_fun := by intros; refl,
  hom_ext := by intros; apply subtype.eq }

end unbundled_hom

end category_theory
