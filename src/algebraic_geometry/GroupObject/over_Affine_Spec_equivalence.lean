import algebraic_geometry.AffineScheme
import algebraic_geometry.GroupObject.CommAlg
import algebra.category.Algebra.limits
open algebraic_geometry category_theory
universes v u

variables (R : Type u) [comm_ring R]

instance (x : under (CommRing.of R)) : algebra R x.right :=
ring_hom.to_algebra x.hom

variables {R}

def alg_hom_of_under_hom {x y : under (CommRing.of R)} (f : x ⟶ y) :
  x.right →ₐ[R] y.right :=
{ commutes' := λ r, (ring_hom.ext_iff.1 f.3 r).symm, ..f.2 }

def CommRing.of_self_iso (R : CommRing) : CommRing.of R ≅ R :=
{ hom := 𝟙 R, inv := 𝟙 R }

def fucksake (A : CommAlg R) : A ≃ₐ[R] CommAlg.of R A := alg_equiv.refl
namespace CommAlg
def to_under_CommRing (x : CommAlg R) : under (CommRing.of R) :=
under.mk (CommRing.of_hom (algebra_map R x.1))

-- ?? :|
def to_under_CommRing_right_iso (x : CommAlg R) :
  x.to_under_CommRing.right ≃ₐ[R] x :=
{ commutes' := λ r, rfl, ..ring_equiv.refl _ }

def hom_to_under_hom {x y : CommAlg R} (f : x ⟶ y) :
  x.to_under_CommRing ⟶ y.to_under_CommRing :=
under.hom_mk f.to_ring_hom (by ext r; exact f.commutes r)

def under_CommRing_CommAlg_equivalence : under (CommRing.of R) ≌ CommAlg R :=
{ functor :=
  { obj := λ A, CommAlg.of R A.right,
    map := λ A B f, CommAlg.of_hom (alg_hom_of_under_hom f) },
  inverse :=
  { obj := λ A, CommAlg.to_under_CommRing A,
    map := λ A B f, CommAlg.hom_to_under_hom f },
  unit_iso := nat_iso.of_components (λ X, under.iso_mk (CommRing.of_self_iso _).symm $
    by ext; refl) (λ X Y f, by ext; refl),
  counit_iso := nat_iso.of_components (λ X, (to_under_CommRing_right_iso X).to_CommAlg_iso
    ≪≫ CommAlg.of_self_iso R X) (λ X Y f, by ext; refl) }

variables {C : Type*} [category C] (X : C) (Y Z : over (opposite.op X))
  (f : Y ⟶ Z)

def op_over_op_equivalence {C : Type*} [category C] (X : C) : (over (opposite.op X))ᵒᵖ ≌ under X :=
{ functor :=
  { obj := λ Y, under.mk (opposite.unop Y).hom.unop,
    map := λ Y Z f, under.hom_mk f.unop.1.unop (by {have := f.unop.3, dsimp * at *,
      rw [←unop_comp, this, category.comp_id]}) },
  inverse :=
  { obj := λ Y, opposite.op (over.mk Y.hom.op),
    map := λ Y Z f, quiver.hom.op (over.hom_mk f.2.op (by {have := f.3, dsimp * at *,
      rw [←op_comp, ←this, category.id_comp] })) },
  unit_iso := nat_iso.of_components (λ Y,
  show opposite.op (opposite.unop Y) ≅ opposite.op (over.mk Y.unop.hom),
  by exact iso.op (over.iso_mk (iso.refl _) (category.id_comp _)))
    (λ Y Z f, quiver.hom.unop_inj (by ext; dsimp; rw [category.id_comp, category.comp_id])),
  counit_iso := nat_iso.of_components (λ Y, under.iso_mk (iso.refl _) (category.comp_id _))
    (λ Y Z f, by ext; dsimp; rw [category.id_comp, category.comp_id]) }

def over_op_op_equivalence {C : Type*} [category C] (X : C) :
  over (opposite.op X) ≌ (under X)ᵒᵖ :=
(op_op_equivalence _).symm.trans (op_over_op_equivalence X).op

def op_under_op_equivalence {C : Type*} [category C] (X : C) :
  (under (opposite.op X))ᵒᵖ ≌ over X :=
{ functor :=
  { obj := λ Y, over.mk (opposite.unop Y).hom.unop,
    map := λ Y Z f, over.hom_mk f.unop.2.unop (by {have := f.unop.3, dsimp * at *,
      rw [←unop_comp, ←this, category.id_comp]}) },
  inverse :=
  { obj := λ Y, opposite.op (under.mk Y.hom.op),
    map := λ Y Z f, quiver.hom.op (under.hom_mk f.1.op (by {have := f.3, dsimp * at *,
      rw [←op_comp, this, category.comp_id] })) },
  unit_iso := nat_iso.of_components (λ Y,
  show opposite.op (opposite.unop Y) ≅ opposite.op (under.mk Y.unop.hom),
    by exact iso.op (under.iso_mk (iso.refl _) (category.comp_id _)))
      (λ Y Z f, quiver.hom.unop_inj (by ext; dsimp; rw [category.id_comp, category.comp_id])),
  counit_iso := nat_iso.of_components (λ Y, over.iso_mk (iso.refl _) (category.id_comp _))
    (λ Y Z f, by ext; dsimp; rw [category.id_comp, category.comp_id]) }

def under_op_op_equivalence {C : Type*} [category C] (X : C) :
  under (opposite.op X) ≌ (over X)ᵒᵖ :=
(op_op_equivalence _).symm.trans (op_under_op_equivalence X).op

def over_equivalence {C D : Type*} [category C] [category D]
  (e : C ≌ D) (X : C) : over X ≌ over (e.1.obj X) :=
{ functor := over.post e.1,
  inverse :=
  ({ obj := λ Y, over.mk ((e.symm.to_adjunction.hom_equiv Y.left X).symm Y.hom),
     map := λ Y Z f, over.hom_mk (e.2.map f.1) (by {have := f.3; dsimp at *;
      simp only [adjunction.hom_equiv_counit, ←functor.map_comp_assoc, this, category.comp_id]}),
     map_id' := λ Y, by ext; exact e.inverse.map_id _,
     map_comp' := by intros; ext; exact e.inverse.map_comp _ _ }),
  unit_iso := sorry,
  counit_iso := sorry,
  functor_unit_iso_comp' := sorry }

noncomputable def over_Affine_Spec_equivalence :
  over (AffineScheme.Spec.obj (opposite.op $ CommRing.of R)) ≌ (CommAlg R)ᵒᵖ :=
(over_equivalence AffineScheme.equiv_CommRing.symm (opposite.op (CommRing.of R))).symm.trans
  ((over_op_op_equivalence _).trans (under_CommRing_CommAlg_equivalence).op)


end CommAlg
