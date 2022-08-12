/-
Copyright (c) 2021 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import representation_theory.cohomology.std_resn
import representation_theory.cohomology.cochain_succ
import category_theory.abelian.ext
import algebra.category.Module.projective
import representation_theory.cohomology.op_complex
/-!

# Ext

Defines an isomorphism of `Ext_ℤ[G](ℤ, M)` with the cohomology groups of a cochain
complex of explicit homogeneous cochains.

-/
open group_cohomology
universes v u
variables (k : Type u) [comm_ring k] [nontrivial k] (G : Type u) [group G] (M : Type u) [add_comm_group M]
  [module k M] (ρ : representation k G M) (n : ℕ)

noncomputable theory

open category_theory category_theory.limits
open_locale zero_object

def cochain_succ.complex : cochain_complex (Module k) ℕ :=
cochain_complex.of (λ n, Module.of k $ homog_cochain ρ (n + 1))
 (λ i, homog_cochain.d ρ rfl)
 (λ i, linear_map.ext $ homog_cochain.d_squared_eq_zero ρ rfl rfl)

variables {C : Type*} [category C] [abelian C] (X : cochain_complex C ℕ)
#exit
/-- The group of homogeneous cochains `Gⁿ → M` is isomorphic to the group of
`ℤ[G]`-linear homs `ℤ[Gⁿ] → M`. -/
def cochain_succ_equiv : homog_cochain ρ n ≃ₗ[k] (group_ring (fin n → G) →ₗ[group_ring G] M) :=
{ to_fun := λ f,
  { map_smul' := λ g x, by { refine group_ring.map_smul_of_map_smul_of
        (finsupp.lift_add_hom (λ v, zmultiples_hom M (f v))) _ _ _,
      intros g x,
      simp only [finsupp.lift_add_hom_apply_single, finsupp.lift_add_hom_apply, one_zsmul,
        add_monoid_hom.to_fun_eq_coe, zmultiples_hom_apply, group_ring.of_apply],
      erw [group_ring.of_smul_of, finsupp.sum_single_index],
      { rw finsupp.sum_single_index,
        { show _ = finsupp.total _ _ _ _ _, by simpa },
        { exact add_monoid_hom.map_zero _}},
      { exact add_monoid_hom.map_zero _}},
    ..finsupp.lift_add_hom (λ v, zmultiples_hom M (f v)) },
  inv_fun := λ f,
  { to_fun := f ∘ group_ring.of (fin n → G),
    smul_apply' := λ s g, by
    { dsimp,
      have := f.map_smul (finsupp.single s 1) (finsupp.single g 1),
      erw group_ring.of_smul_of at this,
      erw this,
      show _ = finsupp.total _ _ _ _ _,
      rw [finsupp.total_single, one_smul] }},
  left_inv := λ x, by
  { ext w,
    show finsupp.lift_add_hom (λ v, zmultiples_hom M (x v)) (finsupp.single w 1) = x w,
    rw [finsupp.lift_add_hom_apply_single, zmultiples_hom_apply, one_smul] },
  right_inv := λ f, by
  { ext x,
    refine x.induction_on _ (λ v w hv hw, _) (λ r v hv, _),
    { intro x,
      show finsupp.lift_add_hom (λ v, zmultiples_hom M (f _)) _ = _,
      rw [group_ring.of_apply, finsupp.lift_add_hom_apply_single,
        zmultiples_hom_apply, one_smul],
      refl },
    { erw add_monoid_hom.map_add,
      rw [linear_map.map_add, ←hv, ←hw],
      refl },
    { erw add_monoid_hom.map_zsmul,
      rw [linear_map.map_smul_of_tower, ←hv],
      refl }},
  map_add' := λ x y, by
  { ext v,
    show finsupp.lift_add_hom _ _ = finsupp.lift_add_hom _ _ + finsupp.lift_add_hom _ _,
    rw [←add_monoid_hom.add_apply, ←add_equiv.map_add],
    congr,
    ext,
    dsimp,
    simp only [one_smul] } }

@[simp] lemma cochain_succ_add_equiv_apply {f : homog_cochain ρ n} {x} :
  cochain_succ_add_equiv G M n f x = finsupp.lift_add_hom (λ v, zmultiples_hom M (f v)) x := rfl

@[simp] lemma cochain_succ_add_equiv_symm_apply {f : group_ring (fin n → G) →ₗ[group_ring G] M} {x} :
  (cochain_succ_add_equiv G M n).symm f x = f (group_ring.of (fin n → G) x) :=
rfl

/-- A bundled `ℤ[G]`-module with structure induced by a `distib_mul_action` on `G.` -/
def group_ring.Module_of  (N : Type v) [add_comm_group N] [distrib_mul_action G N] :
  Module (group_ring G) :=
{ carrier := N,
  is_add_comm_group := by apply_instance,
  is_module := group_ring.to_module }

/-- The chain complex of elements of `(Module ℤ)ᵒᵖ` given by
`Hom(ℤ[G], M) → Hom(ℤ[G²], M) → ...` -/
def map_std_resn : chain_complex.{u} (Module.{u} ℤ)ᵒᵖ ℕ := ((functor.map_homological_complex
  ((linear_yoneda ℤ (Module.{u} (group_ring G))).obj
  (group_ring.Module_of G M)).right_op (complex_shape.down ℕ)).obj
  (group_ring.std_resn G).complex)

/-- A tautological isomorphism to help Lean out, I think -/
def yoneda_equiv_hom (R : Type u) [ring R] (M N : Module R) :
  @opposite.unop (Module ℤ) (((linear_yoneda ℤ (Module R)).obj M).right_op.obj N) ≃+ (N →ₗ[R] M) :=
add_equiv.refl _

/-- Ummm.... another slightly different tautological isomorphism -/
def hom_equiv_yoneda (R : Type*) [ring R] (M : Type*) [add_comm_group M] [module R M]
  (N : Type*) [add_comm_group N] [module R N] :
  (N →ₗ[R] M) ≃+ @opposite.unop (Module ℤ) (((linear_yoneda ℤ (Module R)).obj $
    Module.of R M).right_op.obj $ Module.of R N) :=
add_equiv.refl _

/-- The differential in `map_std_resn G M` is precomposition with `d: ℤ[Gⁿ⁺¹] → ℤ[Gⁿ]`. -/
lemma map_std_resn_d_apply {f : group_ring (fin (n + 1) → G) →ₗ[group_ring G] M} :
  ((map_std_resn G M).d (n + 1) _).unop (hom_equiv_yoneda (group_ring G) _ _ f) =
  hom_equiv_yoneda _ _ _ (f.comp (group_ring.d G rfl)) :=
begin
  show _ ≫ _ = _,
  ext,
  dsimp,
  erw chain_complex.of_d,
  refl,
end

lemma cochain_succ_comm_aux (x : homog_cochain ρ (n + 1)) :
  cochain_succ_add_equiv _ _ _ (homog_cochain.d rfl x)
    = (cochain_succ_add_equiv _ _ _ x).comp (group_ring.d G rfl) :=
begin
  ext g,
  simp only [linear_map.comp_apply, cochain_succ_add_equiv_apply],
  refine g.induction_on _ _ _,
  { intro v,
    rw [finsupp.lift_add_hom_apply, group_ring.of_apply, finsupp.sum_single_index],
    { simp only [←cochain_succ.total_d_eq_d, finsupp.total_apply, zmultiples_hom_apply,
      one_smul, finsupp.lift_add_hom_apply],
      refl },
    { rw add_monoid_hom.map_zero }},
  { intros f g hf hg,
    simp only [add_monoid_hom.map_add, linear_map.map_add, hf, hg] },
  { intros r f hf,
    simp only [add_monoid_hom.map_zsmul, linear_map.map_smul_of_tower, hf]}
end

lemma cochain_succ_comm (x : homog_cochain ρ (n + 1)) :
  cochain_succ_add_equiv _ _ _ (homog_cochain.d rfl x) = ((map_std_resn G M).d _ _).unop
    (hom_equiv_yoneda _ _ _ (cochain_succ_add_equiv G M _ x)) :=
begin
  rw [map_std_resn_d_apply, cochain_succ_comm_aux],
  refl,
end

lemma cochain_succ_symm_comm (x : group_ring (fin (n + 1) → G) →ₗ[group_ring G] M) :
  (cochain_succ_add_equiv G M _).symm (((map_std_resn G M).d _ _).unop (hom_equiv_yoneda _ _ _ x))
    = homog_cochain.d rfl ((cochain_succ_add_equiv G M _).symm x) :=
begin
  rw [add_equiv.symm_apply_eq, cochain_succ_comm, add_equiv.apply_symm_apply],
end

/-- The cochain map from our complex of homogeneous cochains to `Hom(-, M)` of our
  projective resolution of the trivial `ℤ[G]`-module `ℤ`. -/
def cochain_succ_to_map_std_resn :
  cochain_succ.complex G M ⟶ (map_std_resn G M).unop_obj :=
{ f := λ i, (cochain_succ_add_equiv G M (i + 1)).to_add_monoid_hom.to_int_linear_map,
  comm' := λ i j hij,
  begin
    cases hij,
    ext1,
    simp only [category_theory.comp_apply],
    erw [cochain_complex.of_d, cochain_succ_comm],
    refl,
  end }

/-- The cochain map from `Hom(-, M)` of our projective resolution of the trivial `ℤ[G]`-module `ℤ`
  to our complex of homogeneous cochains. -/
def map_std_resn_to_cochain_succ :
  (map_std_resn G M).unop_obj ⟶ cochain_succ.complex G M :=
{ f := λ i, ((cochain_succ_add_equiv G M (i + 1)).trans
    (hom_equiv_yoneda _ _ _)).symm.to_add_monoid_hom.to_int_linear_map,
  comm' := λ i j hij,
  begin
    cases hij,
    ext1,
    simp only [category_theory.comp_apply],
    erw [cochain_complex.of_d, cochain_succ_symm_comm],
    refl,
  end }

/-- Homotopy equivalence between complex of homogeneous cochains and `Hom(-, M)`
  of our projective resolution of trivial `ℤ[G]`-module `ℤ`. -/
def homotopy_equiv_cochain_succ :
  homotopy_equiv (cochain_succ.complex G M) (map_std_resn G M).unop_obj :=
{ hom := cochain_succ_to_map_std_resn G M,
  inv := map_std_resn_to_homog_cochain ρ,
  homotopy_hom_inv_id := homotopy.of_eq $
  begin
    ext n x i,
    congr' 1,
    exact add_equiv.apply_symm_apply _ _,
  end,
  homotopy_inv_hom_id := homotopy.of_eq $
  begin
    ext n x i,
    congr' 1,
    exact add_equiv.apply_symm_apply _ _,
  end }

/-- Isomorphism of cohomology of our complex of homogeneous cochains and `Hom(-, M)` of
  our proj res of `ℤ`. -/
def cochain_succ_homology_iso :
  (cochain_succ.complex G M).homology n ≅ (map_std_resn G M).unop_obj.homology n :=
homology_obj_iso_of_homotopy_equiv (homotopy_equiv_homog_cochain ρ) n
#check chain_complex.homology_unop (map_std_resn G M) n
/-- This has type
  `opposite.op ((map_std_resn G M).unop_obj.homology n) ≅ (map_std_resn G M).homology n`,
  saying homology 'commutes' with viewing `Hom(P., M)` as a cochain complex (instead of a chain
  complex of AddCommGroupᵒᵖs). But Lean times out when I give a type ascription :) -/

def map_std_resn_homology_iso := chain_complex.homology_unop (map_std_resn G M) n

noncomputable def force_noncomputable {α : Sort*} (a : α) : α :=
  function.const _ a (classical.choice ⟨a⟩)

def tautological (R : Type*) [ring R] (C : Type*) [category C] [abelian C] [linear R C]
  [enough_projectives C] (n : ℕ) (X Y : C) :
  (((linear_yoneda R C).obj Y).right_op.left_derived n).left_op.obj (opposite.op X)
    ≅ ((Ext R C n).obj (opposite.op X)).obj Y := force_noncomputable sorry

instance gg : has_projective_resolutions (Module.{u} (group_ring G)) :=
sorry

def huhh (R : Type*) [ring R] (C : Type*) [category C] [abelian C] [linear R C]
  [enough_projectives C] (n : ℕ) (X Y : C) :
  (((linear_yoneda R C).obj Y).right_op.left_derived n).left_op.obj (opposite.op X)
    ≅ ((Ext R C n).obj (opposite.op X)).obj Y := force_noncomputable sorry
open group_ring


section
variables {C' : Type u} [category C'] [abelian C'] {D : Type u} [category D]
  [abelian D] [has_projective_resolutions C']
  /-[has_zero_object C'] [has_equalizers C'] [has_images C'] [has_projective_resolutions.{u} C']
  [preadditive D] [has_zero_object D] [has_equalizers D] [has_cokernels D] [has_images D]
  [has_image_maps D]
  [has_zero_object Dᵒᵖ] [has_equalizers Dᵒᵖ] [has_cokernels Dᵒᵖ] [has_images Dᵒᵖ]
  [has_image_maps Dᵒᵖ]
  -/(F : C' ⥤ Dᵒᵖ) [h : F.additive] {x : C'} (P : ProjectiveResolution x)
  --(F.left_derived n).obj X ≅ (homology_functor D (complex_shape.down ℕ) n).obj
--  ((F.map_homological_complex (complex_shape.down ℕ)).obj P.complex)

variables {A : D} {B : Dᵒᵖ} (H : opposite.op A ≅ B)

def huh [h : F.additive] : (F.left_derived n).left_op.obj (opposite.op x)
  ≅ ((homology_functor _ _ n).obj ((F.map_homological_complex _ ).obj P.complex).unop_obj) :=
(functor.left_derived_obj_iso F n P).symm.unop.trans
  (chain_complex.homology_unop ((F.map_homological_complex _).obj P.complex) n).unop


end
#exit

instance : enough_projectives (Module.{u} (group_ring G)) := sorry

#check huh n (((linear_yoneda ℤ (Module.{u} (group_ring G))).obj (Module_of G M)).right_op)
  (std_resn G)

-- so this would be it:
/- (huh n (((linear_yoneda ℤ (Module.{u} (group_ring G))).obj (Module_of G M)).right_op)
  (std_resn G)).trans (cochain_succ_homology_iso stuff).symm
  if there werent two fucking zero objects. -/
#check ((homology_functor _ _ n).obj (map_std_resn G M).unop_obj)
def hmmm : ((Ext ℤ (Module.{u} (group_ring G)) n).obj (opposite.op $ group_ring.trivial G)).obj
  (Module_of G M) ≅ ((homology_functor _ _ n).obj (map_std_resn G M).unop_obj)
  := force_noncomputable sorry

  #exit
(functor.left_derived_obj_iso _ n _).symm.unop.trans
  (chain_complex.homology_unop ((functor.map_homological_complex _ _).obj (std_resn G).complex) n).unop

--set_option pp.universes true
#check functor.left_derived
#check @functor.left_derived_obj_iso (Module.{u} (group_ring G)) _
  (Module ℤ)ᵒᵖ _ _ _ _ _ _ _ _ _ _ _ _
(((linear_yoneda ℤ (Module.{u} (group_ring G))).obj (group_ring.Module_of.{u} G M)).right_op)
_ n (group_ring.trivial.{u} G) (group_ring.std_resn.{u} G)
--  (group_ring.Module_of G M)).right_op n (group_ring.std_resn G)
lemma Extish_obj_iso : ((Ext ℤ (Module.{u} (group_ring G)) n).obj (opposite.op $ group_ring.trivial G)).obj (group_ring.Module_of G M)
   ≅ (map_std_resn G M).unop_obj.homology n :=
sorry --functor.left_derived_obj_iso ((linear_yoneda ℤ (Module.{u} (group_ring G))).obj
--  (group_ring.Module_of G M)).right_op n (group_ring.std_resn G)

#check ((Ext ℤ (Module.{u} (group_ring G)) n).obj (opposite.op $ group_ring.trivial G)).obj (group_ring.Module_of G M)
#check functor.flip
#check (@functor.left_derived (Module.{u} (group_ring G)) _ (Module.{u} ℤ)ᵒᵖ _ _
  abelian.has_zero_object _ _ _ _ _ _ _ _ _ ((linear_yoneda ℤ (Module (group_ring G))).obj
  (group_ring.Module_of G M)).right_op _ n).left_op
#check ((linear_yoneda ℤ (Module (group_ring G))).obj
  (group_ring.Module_of G M)).right_op
abbreviation Extish := (((linear_yoneda ℤ (Module (group_ring G))).obj
  (group_ring.Module_of G M)).right_op.left_derived n).obj (group_ring.trivial G)

#check functor.left_op
#check (@Ext ℤ _ (Module.{u} (group_ring G)) _ _ _ Module.Module_enough_projectives.{u} (n + 1)).obj
  (opposite.op $ group_ring.trivial G)
#exit

#check (quiver.hom.op 0 : ((linear_yoneda ℤ (Module.{u u} (group_ring G))).obj
  (group_ring.Module_of G M)).right_op.obj ((std_resn G).complex.X 0) ⟶ opposite.op 0) _
--≅ opposite.unop ((homology_functor (Module ℤ)ᵒᵖ (complex_shape.down ℕ) 0).obj (map_std_resn G M))
#check (@Ext ℤ _ (Module (group_ring G)) _ _ _ Module.Module_enough_projectives (n + 1)).obj
  (opposite.op $ group_ring.trivial G)
instance why : enough_projectives (Module (group_ring G)) :=
Module.Module_enough_projectives
#check @functor.left_derived (Module (group_ring G)) _ (Module ℤ) _ _ _ _ _ (@ProjectiveResolution.category_theory.has_projective_resolutions)
--instance : has_projective_resolutions (Module (group_ring G)) :=
--@ProjectiveResolution.category_theory.has_projective_resolutions (Module (group_ring G)) _ _ (why G)
/- Ext without some 'left_op', so it takes values in `(Module ℤ)ᵒᵖ` -/
abbreviation Extish := (((linear_yoneda ℤ (Module (group_ring G))).obj
  (group_ring.Module_of G M)).right_op.left_derived n).obj (group_ring.trivial G)

/- `Extⁿ(ℤ, M)ᵒᵖ ≅` the homology of the complex with elements in `AddCommGroupᵒᵖ` given by
  `Hom(ℤ[G], M) → Hom(ℤ[G²], M) → ...` -/
def Extish_obj_iso : Extish G M n ≅ (homology_functor _ _ n).obj (map_std_resn G M) :=
functor.left_derived_obj_iso ((linear_yoneda ℤ (Module.{u} (group_ring G))).obj
  (group_ring.Module_of G M)).right_op n (group_ring.std_resn G)

/- LHS is Ext. but I get timeouts when I use Ext. -/
def Ext_Extish :
  (((linear_yoneda ℤ (Module (group_ring G))).obj
    (group_ring.Module_of G M)).right_op.left_derived n).left_op.obj
    (opposite.op (group_ring.trivial G))
  ≅ opposite.unop (Extish G M n) :=
iso.refl _

/-- Composition of the above to give `Ext(ℤ, M) ≅` the cohomology of the complex of
homogeneous cochains. But we use `homology_op`, which is sorried. -/
def Ext_iso_homogeneous : (homology_functor _ _ n).obj (cochain_succ.complex G M) ≅
  (((linear_yoneda ℤ (Module (group_ring G))).obj
    (group_ring.Module_of G M)).right_op.left_derived n).left_op.obj
    (opposite.op (group_ring.trivial G)) :=
(((cohomology_iso G M n).trans (homology_op G M n)).trans (Extish_obj_iso G M n).unop).trans
  (Ext_Extish G M n).symm
