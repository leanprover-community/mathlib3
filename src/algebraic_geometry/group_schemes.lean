import algebra.category.Group.internal
import algebraic_geometry.Gamma_Spec_adjunction
import algebra.category.Ring.instances
import algebra.free_algebra

noncomputable theory

universe u

namespace category_theory

namespace adjunction

def yoneda_nat_iso {C D : Type*} [category C] [category D]
  {G : C ⥤ D} {F : D ⥤ C} (adj : G ⊣ F) (Y : D) :
  G.op ⋙ yoneda.obj Y ≅ yoneda.obj (F.obj Y) :=
nat_iso.of_components
(λ X, equiv_equiv_iso (adj.hom_equiv X.unop Y)) (by tidy)

end adjunction

namespace functor

open opposite

def comp_yoneda_obj {C D : Type*} [category C] [category D]
  (F : Cᵒᵖ ⥤ D) (X : D) : F ⋙ coyoneda.obj (op X) ≅
  F.right_op.op ⋙ yoneda.obj (op X) :=
nat_iso.of_components (λ Y, equiv_equiv_iso (equiv.symm
  (by apply op_equiv))) (by tidy)

end functor

end category_theory

open category_theory category_theory.concrete_category opposite

lemma ring_hom_from_ulift_ℤ (R : Type u) [ring R] :
  ulift.{u} ℤ →+* R :=
{ to_fun := λ x, ↑(ulift.down x),
  map_one' := by tidy,
  map_mul' := by tidy,
  map_zero' := by tidy,
  map_add' := by tidy, }

instance inhabited_ring_hom_from_ulift_ℤ (R : Type u) [ring R] :
  inhabited (ulift.{u} ℤ →+* R) :=
⟨ring_hom_from_ulift_ℤ R⟩

instance (R : Type u) [ring R] : subsingleton (ulift.{u} ℤ →+* R) :=
⟨λ f₁ f₂, begin
  ext,
  suffices : ∀ (n : ℕ), f₁ (ulift.up n) = f₂ (ulift.up n),
  { cases x,
    cases x,
    { apply this, },
    { rw int.neg_succ_of_nat_eq,
      let y : ulift.{u} ℤ := ulift.up (((x+1) : ℤ)),
      change f₁ (-y) = f₂ (-y),
      simpa only [map_neg, neg_inj] using this _, }, },
  intro n,
  induction n with n hn,
  { change f₁ 0 = f₂ 0,
    simp only [map_zero], },
  { let x : ulift.{u} ℤ := ulift.up (n : ℤ),
    change f₁ x = f₂ x at hn,
    change f₁ (x+1) = f₂ (x+1),
    simp only [map_add, hn, map_one] },
end⟩

instance (R : Type u) [ring R] : unique (ulift.{u} ℤ →+* R) := unique.mk' _

def polynomial_coyoneda_iso :
  coyoneda.obj (op (CommRing.of (polynomial (ulift.{u} ℤ)))) ≅
    (concrete_category.forget CommRing.{u}) :=
nat_iso.of_components (λ R, equiv_equiv_iso begin
  exact
  { to_fun := λ f, f.1 polynomial.X,
    inv_fun := λ a, polynomial.eval₂_ring_hom (ring_hom_from_ulift_ℤ R) a,
    left_inv := by tidy,
    right_inv := by tidy, }
end) (by tidy)

namespace algebraic_geometry

open Scheme

def Gₐ' : internal CommRing Scheme.{u} :=
{ obj := Spec.obj (op (CommRing.of (polynomial (ulift.{u} ℤ)))),
  presheaf := Γ,
  iso := (Γ_Spec.adjunction.yoneda_nat_iso _).symm ≪≫
    (Γ.comp_yoneda_obj _).symm ≪≫ iso_whisker_left Γ polynomial_coyoneda_iso, }

def Gₐ : internal Ab Scheme.{u} := (internal.forget₂ CommRing Ring Scheme.{u} ⋙
  internal.forget₂ Ring Ab.{u} Scheme.{u}).obj Gₐ'

end algebraic_geometry
