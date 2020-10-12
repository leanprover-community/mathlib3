/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.adjunction
import category_theory.elements
import category_theory.limits.functor_category
import category_theory.limits.shapes
import category_theory.limits.types

namespace category_theory

noncomputable theory

open category limits
universes u₁ u₂

variables {C : Type u₁} [small_category C]
variables {ℰ : Type u₂} [category.{u₁} ℰ]
variable (A : C ⥤ ℰ)

namespace colimit_adj

/--
The functor taking `(E : ℰ) (c : Cᵒᵖ)` to the homset `(A.obj C ⟶ E)`. It is shown in `L_adjunction`
that this functor has a left adjoint (provided `E` has colimits) given by taking colimits over
categories of elements.
-/
@[simps {rhs_md := semireducible}]
def R : ℰ ⥤ (Cᵒᵖ ⥤ Type u₁) :=
yoneda ⋙ (whiskering_left _ _ (Type u₁)).obj (functor.op A)

/--
(Implementation). The equivalence of homsets which helps construct the left adjoint to
`colimit_adj.R`.
It is shown in `Le'_natural` that this is a natural bijection.
-/
def Le' (P : Cᵒᵖ ⥤ Type u₁) (E : ℰ) {c : cocone ((category_of_elements.π P).left_op ⋙ A)}
  (t : is_colimit c) : (c.X ⟶ E) ≃ (P ⟶ (R A).obj E) :=
(t.hom_iso' E).to_equiv.trans
{ to_fun := λ k,
  { app := λ c p, k.1 (opposite.op ⟨_, p⟩),
    naturality' := λ c c' f, funext $ λ p,
      (k.2 (has_hom.hom.op ⟨f, rfl⟩ :
              (opposite.op ⟨c', P.map f p⟩ : P.elementsᵒᵖ) ⟶ opposite.op ⟨c, p⟩)).symm },
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

/-- (Implementation). Show that the bijection in `Le'` is natural (on the right). -/
lemma Le'_natural (P : Cᵒᵖ ⥤ Type u₁) (E₁ E₂ : ℰ) (g : E₁ ⟶ E₂)
  {c : cocone _} (t : is_colimit c) (k : c.X ⟶ E₁) :
Le' A P E₂ t (k ≫ g) = Le' A P E₁ t k ≫ (R A).map g :=
begin
  ext _ X p,
  apply (assoc _ _ _).symm,
end

variables [has_colimits ℰ]

/-- The left adjoint to the functor `R` which sends `R(E,C)`  -/
def L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ :=
adjunction.left_adjoint_of_equiv
  (λ P E, Le' A P E (colimit.is_colimit _))
  (λ P E E' g, Le'_natural A P E E' g _)

@[simp]
lemma L_obj (P : Cᵒᵖ ⥤ Type u₁) : (L A).obj P =
colimit ((category_of_elements.π P).left_op ⋙ A) := rfl

/-- Show `L` is left adjoint to `R`. -/
def L_adjunction : L A ⊣ R A := adjunction.adjunction_of_equiv_left _ _

/--
The terminal object in the category of elements for a representable functor.
In `is_term` it is shown that this is terminal.
-/
def term_element (A : C) : (yoneda.obj A).elementsᵒᵖ :=
opposite.op ⟨opposite.op A, 𝟙 _⟩

/--
Show that `term_element A` is terminal in the category of elements for the `yoneda` functor.
-/
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

/--
On the full subcategory of representables, `L A` is an extension of `A`.
TODO: Among functors preserving colimits, `L` is unique with this property up to isomorphism.
-/
def extend : (yoneda : C ⥤ Cᵒᵖ ⥤ Type u₁) ⋙ L A ≅ A :=
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

/-- The functor `R` is isomorphic to the identity functor if evaluated at the yoneda embedding. -/
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

/--
Since `L A` is adjoint to `R A`, if we use `A = yoneda` then `R A` is isomorphic to the
identity, and so `L A` is as well.
-/
def left_is_id : L (yoneda : C ⥤ _) ≅ 𝟭 _ :=
adjunction.left_adjoint_uniq (L_adjunction _) (adjunction.id.of_nat_iso_right right_is_id.symm)

/--
This is a cocone with point `P`, for which the diagram consists solely of representables.
It is shown in `is_a_limit P` that this cocone is a colimit: that is, we have exhibited an
arbitrary presheaf `P` as a colimit of representables.
-/
def the_cocone (P : Cᵒᵖ ⥤ Type u₁) :
  cocone ((category_of_elements.π P).left_op ⋙ yoneda) :=
cocone.extend (colimit.cocone _) (left_is_id.hom.app P)

@[simp]
lemma the_cocone_X (P : Cᵒᵖ ⥤ Type u₁) : (the_cocone P).X = P := rfl

/--
The cocone with point `P` given by `the_cocone` is a colimit: that is, we have exhibited an
arbitrary presheaf `P` as a colimit of representables.
-/
def is_a_limit (P : Cᵒᵖ ⥤ Type u₁) : is_colimit (the_cocone P) :=
begin
  apply is_colimit.of_point_iso (colimit.is_colimit ((category_of_elements.π P).left_op ⋙ yoneda)),
  change is_iso (colimit.desc _ (cocone.extend _ _)),
  rw [colimit.desc_extend, colimit.desc_cocone],
  apply_instance,
end

end category_theory
