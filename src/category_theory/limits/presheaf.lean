import category_theory.adjunction
import category_theory.elements
import category_theory.limits.functor_category
import category_theory.limits.shapes
import category_theory.limits.types

namespace category_theory

noncomputable theory

open category limits
universes v₁ v₂ u₁ u₂

variables {C : Type u₁} [small_category C]
variables {ℰ : Type u₂} [category.{u₁} ℰ]
variables [has_colimits ℰ]
variable (A : C ⥤ ℰ)

namespace colimit_adj

@[simps]
def R : ℰ ⥤ (Cᵒᵖ ⥤ Type u₁) :=
{ obj := λ E,
  { obj := λ c, A.obj c.unop ⟶ E,
    map := λ c c' f k, A.map f.unop ≫ k },
  map := λ E E' k, { app := λ c f, f ≫ k } }.

def Le' (P : Cᵒᵖ ⥤ Type u₁) (E : ℰ) {c : cocone ((category_of_elements.π P).left_op ⋙ A)}
  (t : is_colimit c) : (c.X ⟶ E) ≃ (P ⟶ (R A).obj E) :=
(t.hom_iso' E).to_equiv.trans
{ to_fun := λ k,
  { app := λ c p, k.1 (opposite.op ⟨_, p⟩),
    naturality' := λ c c' f,
    begin
      ext p,
      apply (k.2 (has_hom.hom.op ⟨f, rfl⟩ : (opposite.op ⟨c', P.map f p⟩ : P.elementsᵒᵖ) ⟶ opposite.op ⟨c, p⟩)).symm,
    end },
  inv_fun := λ τ,
  { val := λ p, τ.app p.unop.1 p.unop.2,
    property := λ p p' f,
    begin
      simp_rw [← f.unop.2],
      apply (congr_fun (τ.naturality f.unop.1) p'.unop.2).symm,
    end },
  left_inv :=
  begin
    rintro ⟨k₁, k₂⟩,
    ext,
    dsimp,
    congr' 1,
    simp,
  end,
  right_inv :=
  begin
    rintro ⟨_, _⟩,
    refl,
  end }

lemma Le'_natural (P : Cᵒᵖ ⥤ Type u₁) (E₁ E₂ : ℰ) (g : E₁ ⟶ E₂)
  {c : cocone _} (t : is_colimit c) (k : c.X ⟶ E₁) :
Le' A P E₂ t (k ≫ g) = Le' A P E₁ t k ≫ (R A).map g :=
begin
  ext _ X p,
  apply (assoc _ _ _).symm,
end

def L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ :=
adjunction.left_adjoint_of_equiv
  (λ P E, Le' A P E (colimit.is_colimit _))
  (λ P E E' g, Le'_natural A P E E' g _)

def L_adjunction : L A ⊣ R A := adjunction.adjunction_of_equiv_left _ _

def term_element (A : C) : (yoneda.obj A).elementsᵒᵖ :=
opposite.op ⟨opposite.op A, 𝟙 _⟩

def is_term (A : C) : is_terminal (term_element A) :=
{ lift := λ s,
  begin
    refine (has_hom.hom.op (_ : _ ⟶ opposite.unop s.X) : s.X ⟶ opposite.op ⟨opposite.op A, 𝟙 A⟩),
    refine ⟨s.X.unop.2.op, comp_id _⟩,
  end,
  uniq' := λ s m w, has_hom.hom.unop_inj
  begin
    simp_rw ← m.unop.2,
    dsimp [as_empty_cone, term_element],
    simp,
  end }

def extend : (yoneda : C ⥤ _) ⋙ L A ≅ A :=
nat_iso.of_components
(λ X, (colimit.is_colimit _).cocone_point_unique_up_to_iso (colimit_of_diagram_terminal (is_term X) _))
begin
  intros X Y f,
  change (colimit.desc _ ⟨_, _⟩ ≫ colimit.desc _ _) = colimit.desc _ _ ≫ _,
  apply colimit.hom_ext,
  intro j,
  rw [colimit.ι_desc_assoc, colimit.ι_desc_assoc],
  change (colimit.ι _ _ ≫ 𝟙 _) ≫ colimit.desc _ _ = _,
  rw [comp_id, colimit.ι_desc],
  dsimp,
  rw ← A.map_comp,
  congr' 1,
end

end colimit_adj

open colimit_adj

def right_is_id : R (yoneda : C ⥤ _) ≅ 𝟭 _ :=
nat_iso.of_components
(λ P, nat_iso.of_components (λ X, yoneda_sections_small X.unop _)
  (λ X Y f, funext $ λ x,
  begin
    apply eq.trans _ (congr_fun (x.naturality f) (𝟙 _)),
    dsimp [ulift_trivial, yoneda_lemma],
    simp only [id_comp, comp_id],
  end))
(λ _ _ _, rfl)

def left_is_id : L (yoneda : C ⥤ _) ≅ 𝟭 _ :=
adjunction.left_adjoint_uniq (L_adjunction _) (adjunction.id.of_nat_iso_right right_is_id.symm)

-- This is a cocone with point `P`, for which the diagram consists solely of representables.
def the_cocone (P : Cᵒᵖ ⥤ Type u₁) :
  cocone ((category_of_elements.π P).left_op ⋙ yoneda) :=
cocone.extend (colimit.cocone _) (left_is_id.hom.app P)

def is_a_limit (P : Cᵒᵖ ⥤ Type u₁) : is_colimit (the_cocone P) :=
begin
  apply is_colimit.of_point_iso (colimit.is_colimit ((category_of_elements.π P).left_op ⋙ yoneda)),
  change is_iso (colimit.desc _ (cocone.extend _ _)),
  rw [colimit.desc_extend, colimit.desc_cocone],
  apply_instance,
end

-- Probably needs preserves branch for simp to be nice
-- def unique_extension (L' : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ) (hL : (yoneda : C ⥤ _) ⋙ L' ≅ A)
--   [preserves_colimits L'] :
--   L' ≅ L A :=
-- begin
--   apply nat_iso.of_components _ _,
--   intro P,
--   apply (preserves_colimit.preserves (is_a_limit P)).cocone_points_iso_of_nat_iso (colimit.is_colimit ((category_of_elements.π P).left_op ⋙ A)),
--   apply functor.associator _ _ _ ≪≫ iso_whisker_left _ hL,
--   apply_instance,
--   intros X Y f,
--   simp,
-- end

end category_theory
