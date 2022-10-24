import algebra.category.Ring.internal

namespace category_theory

namespace concrete_category

namespace internal

open operations

variables {C : Type*} [category C] (R : internal Ring C) (M : internal Ab C)

class module :=
(smul [] : Ab.yoneda_bilinear R.Ab M M)
(one_smul [] : operations.lift₂ (to_functor_const_punit ≫ Ring_one.to_internal_yoneda_operation₀ R)
   (𝟙 _) ≫ smul.φ = 𝟙 _)
(mul_smul [] : lift₂ (pr₁₂_₃ ≫ Ring_mul.to_internal_yoneda_operation₂ R) pr₃_₃ ≫ smul.φ =
  lift₂ pr₁_₃ (pr₂₃_₃ ≫ smul.φ) ≫ smul.φ)

instance : module R R.Ab :=
{ smul :=
  { φ := Ring_mul.to_internal_yoneda_operation₂ R,
    right_distrib := operation₂.to_internal_yoneda_operation₂_right_distrib _ _ R Ring_right_distrib,
    left_distrib := operation₂.to_internal_yoneda_operation₂_left_distrib _ _ R Ring_left_distrib, },
  one_smul := operation₂.to_internal_yoneda_operation₂_zero_add  _ R _ Ring_one_mul,
  mul_smul := operation₂.to_internal_yoneda_operation₂_assoc Ring_mul R Ring_mul_assoc, }

@[simp]
def is_linear_map {M₁ M₂ : internal Ab C} [module R M₁] [module R M₂] (f : M₁ ⟶ M₂) : Prop :=
(module.smul R M₁).φ ≫ hom.to_internal_yoneda_operation₁ f =
  lift₂ pr₁ (pr₂ ≫ hom.to_internal_yoneda_operation₁ f) ≫ (module.smul R M₂).φ

class linear_map {M₁ M₂ : internal Ab C} [module R M₁] [module R M₂] (f : M₁ ⟶ M₂) :=
(is_linear_map [] : is_linear_map R f)

instance {M : internal Ab C} [module R M] : linear_map R (𝟙 M) :=
⟨begin
  dsimp only [is_linear_map],
  simp only [hom.to_internal_yoneda_operation₁_id, category.comp_id],
  convert (category.id_comp _).symm,
  tidy,
end⟩

instance {M₁ M₂ M₃ : internal Ab C} [module R M₁] [module R M₂] [module R M₃]
  (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) [linear_map R f] [linear_map R g] : linear_map R (f ≫ g) :=
⟨begin
  dsimp only [is_linear_map],
  simp only [hom.to_internal_yoneda_operation₁_comp],
  have hf := linear_map.is_linear_map R f,
  have hg := linear_map.is_linear_map R g,
  dsimp only [is_linear_map] at hf hg,
  rw [reassoc_of hf, hg],
  refl,
end⟩

structure Module :=
(α : internal Ab C)
[hα : module R α]

namespace Module

variable {R}

instance (M : Module R) : module R M.α := M.hα

def hom (M₁ M₂ : Module R) := { f : M₁.α ⟶ M₂.α // is_linear_map R f }

instance (M₁ M₂ : Module R) (f : hom M₁ M₂) : linear_map R f.1 := ⟨f.2⟩

instance (M₁ M₂ : Module R) (f₁ f₂ : M₁.α ⟶ M₂.α) [linear_map R f₁]
  [linear_map R f₂] : linear_map R (f₁ + f₂) :=
⟨begin
  dsimp only [is_linear_map],
  ext Y x : 3,
  rcases x with ⟨a, m⟩,
  simp only [nat_trans.comp_app, types_comp_apply, lift₂_app, pr₁_app, pr₂_app],
  -- (module.smul R M₂.α).right_distrib,
  sorry,
end⟩

instance zero_linear (M₁ M₂ : Module R) : linear_map R (0 : M₁.α ⟶ M₂.α) := sorry

instance (M₁ M₂ : Module R) (f : M₁.α ⟶ M₂.α) [linear_map R f] : linear_map R (-f) := sorry

@[simps]
def hom.mk {M₁ M₂ : Module R} (f : M₁.α ⟶ M₂.α) [h : linear_map R f] : hom M₁ M₂ :=
⟨f, h.is_linear_map⟩

@[simps]
def id (M : Module R) : hom M M := hom.mk (𝟙 M.α)

@[simps]
def comp {M₁ M₂ M₃ : Module R} (f : hom M₁ M₂) (g : hom M₂ M₃) : hom M₁ M₃ := hom.mk (f.1 ≫ g.1)

instance : category (Module R) :=
{ hom := hom,
  id := id,
  comp := λ M₁ M₂ M₃, comp, }

instance : preadditive (Module R) :=
{ hom_group := λ M₁ M₂,
  { add := λ f₁ f₂, hom.mk (f₁.1 + f₂.1),
    zero := hom.mk 0,
    neg := λ f, hom.mk (-f.1),
    add_assoc := λ f₁ f₂ f₃, by { ext1, apply add_assoc, },
    zero_add := λ f, by { ext1, apply zero_add, },
    add_zero := λ f, by { ext1, apply add_zero, },
    add_left_neg := λ f, by { ext1, apply add_left_neg, },
    add_comm := λ f₁ f₂, by { ext1, apply add_comm, }, },
  add_comp' := λ M₁ M₂ M₃ f₁ f₂ g, by { ext1, apply preadditive.add_comp, },
  comp_add' := λ M₁ M₂ M₃ f g₁ g₂, by { ext1, apply preadditive.comp_add, }, }

end Module

end internal

end concrete_category

end category_theory
