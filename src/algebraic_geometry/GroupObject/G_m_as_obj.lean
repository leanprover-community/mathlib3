import ring_theory.tensor_product
import algebraic_geometry.GroupObject.GroupScheme
import data.polynomial.laurent
import algebra.category.Ring.constructions
universes v u
noncomputable theory
open laurent_polynomial category_theory algebraic_geometry
open_locale tensor_product
local notation R`[T;T⁻¹]`:9000 := laurent_polynomial R

def is_localization.alg_hom_lift {R S P : Type*} [comm_semiring R] [comm_semiring S]
  [comm_semiring P] (U : submonoid R) [algebra R S] [_root_.is_localization U S] [algebra R P]
  (H : ∀ y : U, is_unit (algebra_map R P y)) :
  S →ₐ[R] P :=
{ commutes' := λ r, is_localization.lift_eq _ _, ..is_localization.lift H }

def Eval₂_ring_hom {R S : Type*}
  [comm_semiring R] [comm_semiring S] (f : R →+* S) (x : Sˣ) :
  R[T;T⁻¹] →+* S :=
@is_localization.lift (polynomial R) _ _ _ _ _ _ _ laurent_polynomial.is_localization
(polynomial.eval₂_ring_hom f x) $
begin
  suffices : submonoid.closure {@polynomial.X R _} ≤ (is_unit.submonoid S).comap
    (polynomial.eval₂_ring_hom f x).to_monoid_hom,
  { intro y, exact this y.2},
  rw submonoid.closure_le,
  simpa only [ring_hom.to_monoid_hom_eq_coe, submonoid.coe_comap, ring_hom.coe_monoid_hom,
    polynomial.coe_eval₂_ring_hom, set.singleton_subset_iff, set.mem_preimage,
    polynomial.eval₂_X] using units.is_unit x,
end

/-variables {R S : Type*} [comm_semiring R] [comm_semiring S] [algebra R S] (x : Sˣ)

#check @is_localization.alg_hom_lift (polynomial R) (R[T;T⁻¹]) S _ _ _ _ _
laurent_polynomial.is_localization (polynomial.eval₂_ring_hom
  (algebra_map R S) (x : S)).to_algebra
  (begin
  suffices : submonoid.closure {@polynomial.X R _} ≤ (is_unit.submonoid S).comap
    (polynomial.eval₂_ring_hom (algebra_map R S) (x : S)).to_monoid_hom,
  { intro y, exact this y.2},
  rw submonoid.closure_le,
  simpa only [ring_hom.to_monoid_hom_eq_coe, submonoid.coe_comap, ring_hom.coe_monoid_hom,
    polynomial.coe_eval₂_ring_hom, set.singleton_subset_iff, set.mem_preimage,
    polynomial.eval₂_X] using units.is_unit x,
end)-/

def eval₂_alg_hom {R S : Type*} [comm_semiring R] [comm_semiring S] [algebra R S] (x : Sˣ) :
  R[T;T⁻¹] →ₐ[R] S :=
{ commutes' := sorry, ..Eval₂_ring_hom (algebra_map R S) x }

variables (R : Type*) [comm_ring R]

def comultiplication : R[T;T⁻¹] →+* R[T;T⁻¹] ⊗[R] R[T;T⁻¹] :=
@Eval₂_ring_hom R (R[T;T⁻¹] ⊗[R] R[T;T⁻¹]) _ _ (algebra_map R _) (units.mk_of_mul_eq_one
  (T 1 ⊗ₜ T 1) (T (-1 : ℤ) ⊗ₜ T (-1 : ℤ))
  (by { rw [algebra.tensor_product.tmul_mul_tmul, ←T_add, add_neg_self], refl }))

abbreviation Over := over (Scheme.Spec.obj (opposite.op $ CommRing.of R))

def Over.mk_of_hom {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S) :
  Over R := over.mk (Scheme.Spec_map $ CommRing.of_hom f)

def Over.mk_of_alg (R S : Type*) [comm_ring R] [comm_ring S] [algebra R S] :=
Over.mk_of_hom (algebra_map R S)

def Over.mk_hom_of_alg {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T] (f : T →ₐ[R] S) :
  Over.mk_of_alg R S ⟶ Over.mk_of_alg R T :=
over.hom_mk (Scheme.Spec_map $ CommRing.of_hom f.to_ring_hom) $
begin
  dsimp [Over.mk_of_alg, Over.mk_of_hom],
  rw ←Scheme.Spec_map_comp,
  congr,
  ext,
  simp only [comp_apply, CommRing.of_hom_apply, alg_hom.coe_to_ring_hom, alg_hom.commutes],
end

def Over.mk_hom_of_hom {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
  (f : R →+* S) (g : R →+* T) (F : @alg_hom R T S _ _ _ g.to_algebra f.to_algebra) :
  Over.mk_of_hom f ⟶ Over.mk_of_hom g :=
@Over.mk_hom_of_alg R S T _ _ _ f.to_algebra g.to_algebra F

def Over.mk_hom_of_hom' {R S T : Type u} [comm_ring R] [comm_ring S] [comm_ring T]
  (f : R →+* S) (g : R →+* T) (F : T →+* S) (hF : ∀ (r : R), F (g r) = f r) :
  Over.mk_of_hom f ⟶ Over.mk_of_hom g :=
over.hom_mk (Scheme.Spec_map $ CommRing.of_hom F) $
begin
  dsimp [Over.mk_of_hom],
  rw ←Scheme.Spec_map_comp,
  congr,
  ext,
  simp only [hF, comp_apply, CommRing.of_hom_apply],
end

def 𝔾ₘ_obj : Over R := Over.mk_of_hom (algebra_map R R[T;T⁻¹])

local attribute [instance] over.construct_products.over_binary_product_of_pullback
  over.over_has_terminal
section
open category_theory.limits category_theory.over.construct_products
variables {C : Type*} [category C] [has_pullbacks C]

def iso_cospan {B : C} (X Y : over B) :
  wide_pullback_diagram_of_diagram_over B (pair X Y) ≅ cospan X.hom Y.hom :=
nat_iso.of_components (λ j, option.rec_on j (iso.refl _) (λ j, walking_pair.rec_on j
  (iso.refl _) (iso.refl _))) sorry

def aux {B : C} (X Y : over B) :
  limits.limit_cone (cospan X.hom Y.hom) :=
{ cone := (limits.cones.postcompose (iso_cospan X Y).hom).obj ((cones_equiv B _).inverse.obj
   (limits.limit.cone _)),
  is_limit := sorry }

def prod_left_iso_pullback {B : C} (X Y : over B) :
  (X ⨯ Y).left ≅ limits.pullback X.hom Y.hom :=
(aux X Y).2.cone_point_unique_up_to_iso (limits.limit.is_limit _)

def prod_iso_mk_pullback {B : C} (X Y : over B) :
  X ⨯ Y ≅ over.mk ((limits.limit.cone (cospan X.hom Y.hom)).π.app none) :=
over.iso_mk (prod_left_iso_pullback X Y) $
begin
  dsimp,
  dunfold prod_left_iso_pullback,
  dsimp,
  erw limits.is_limit.cone_point_unique_up_to_iso_hom_comp,
  dunfold aux,
  dsimp,
  exact category.comp_id _,
end

def proj {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : limits.pullback f g ⟶ Z :=
(limits.limit.cone (cospan f g)).π.app none

end

def pullback_of_affine {R S T : CommRing}
  (f : R ⟶ S) (g : R ⟶ T) :
  Scheme.Spec.obj (limits.pullback f.op g.op) ≅ limits.pullback
    (Scheme.Spec_map f) (Scheme.Spec_map g) :=
limits.preserves_pullback.iso _ _ _

def over_pullback_of_affine {R S T : CommRing}
  (f : R ⟶ S) (g : R ⟶ T) :
  over.mk (Scheme.Spec_map (proj f.op g.op).unop)
  ≅ over.mk (proj (Scheme.Spec_map f) (Scheme.Spec_map g)) :=
over.iso_mk (pullback_of_affine f g) $
begin
  dsimp,
  dunfold proj pullback_of_affine,
  simp only [limits.preserves_pullback.iso_hom, limits.pullback_cone.condition_one,
    limits.pullback_cone.fst_colimit_cocone, limits.pullback_comparison_comp_fst_assoc,
    Scheme.Spec_map_2, unop_comp, quiver.hom.unop_op, Scheme.Spec_map_comp],
end

def pushout_iso {R S T : CommRing} (f : R ⟶ S) (g : R ⟶ T) :
  limits.pushout f g ≅ CommRing.of (@tensor_product R _ S T _ _
    (by letI := ring_hom.to_algebra f; apply_instance)
    (by letI := ring_hom.to_algebra g; apply_instance)) :=
limits.is_colimit.cocone_point_unique_up_to_iso (limits.colimit.is_colimit _)
(CommRing.pushout_cocone_is_colimit _ _)

def pushout_iso' {R S T : CommRing} [algebra R S] [algebra R T] :
  limits.pushout (CommRing.of_hom $ algebra_map R S) (CommRing.of_hom $ algebra_map R T)
  ≅ CommRing.of (S ⊗[R] T) :=
pushout_iso _ _ ≪≫ sorry -- christ knows


#check Over.mk_hom_of_hom' (algebra_map R (R[T;T⁻¹] ⊗[R] R[T;T⁻¹])) (algebra_map R R[T;T⁻¹])
 (comultiplication R)
def fml : Over.mk_of_hom (algebra_map R $ R[T;T⁻¹] ⊗[R] R[T;T⁻¹]) ⟶ 𝔾ₘ_obj R :=
Over.mk_hom_of_hom' (algebra_map R (R[T;T⁻¹] ⊗[R] R[T;T⁻¹])) (algebra_map R _) (comultiplication R) _
#exit
def 𝔾ₘ_mul : 𝔾ₘ_obj R ⨯ 𝔾ₘ_obj R ⟶ 𝔾ₘ_obj R :=
(prod_iso_mk_pullback _ _).hom ≫
begin
  refine (over_pullback_of_affine _ _).inv ≫ _,
  refine over.hom_mk _ _,
  dsimp [𝔾ₘ_obj, Over.mk_of_alg, Over.mk_of_hom],
  refine Scheme.Spec_map _,
  refine _ ≫ (limits.pushout_iso_unop_pullback _ _).hom,
  refine CommRing.of_hom (comultiplication R) ≫ (pushout_iso _ _).inv,
end

--over.iso_mk (pullback_of_affine _ _).symm _ ≫ _
#exit
def comul (R : Type*) [comm_semiring R] : R[T;T⁻¹] →+* (R[T;T⁻¹] ⊗[R] R[T;T⁻¹]) :=
@laurent_polynomial.eval₂_ring_hom R (R[T;T⁻¹] ⊗[R] R[T;T⁻¹]) _ _
  (algebra_map R (R[T;T⁻¹] ⊗[R] R[T;T⁻¹]))
  (units.mk_of_mul_eq_one (T 1 ⊗ₜ T 1) (T (-1 : ℤ) ⊗ₜ T (-1 : ℤ))
  (by {rw [algebra.tensor_product.tmul_mul_tmul, ←T_add, add_neg_self], refl}))
/-lemma comul (R : Type*) [comm_ring R] :=
@is_localization.lift R[X] _ _ R[T;T⁻¹] _ _ (R[T;T⁻¹] ⊗[R] R[T;T⁻¹]) _
  laurent_polynomial.is_localization
  (polynomial.eval₂_ring_hom (algebra_map _ _) (T 0 ⊗ₜ T 0))
  (begin
    suffices : submonoid.closure {@polynomial.X R _} ≤ (is_unit.submonoid S).comap
      (polynomial.eval₂_ring_hom f x).to_monoid_hom,
    { intro y, exact this y.2},
    rw submonoid.closure_le,
    simpa only [ring_hom.to_monoid_hom_eq_coe, submonoid.coe_comap, ring_hom.coe_monoid_hom,
    polynomial.coe_eval₂_ring_hom, set.singleton_subset_iff, set.mem_preimage,
    polynomial.eval₂_X] using units.is_unit x,
  end)-/

local attribute [instance] over.construct_products.over_binary_product_of_pullback
  over.over_has_terminal

abbreviation Over := over (Scheme.Spec.obj (opposite.op $ CommRing.of k))
#check laurent_polynomial.C
def 𝔾_m_obj : Over k := over.mk
