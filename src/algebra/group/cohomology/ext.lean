/-
Copyright (c) 2021 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import algebra.group.cohomology.std_resn
import algebra.group.cohomology.cochain_succ
import category_theory.abelian.ext
import algebra.category.Module.projective
/-!

# Ext

Defines an isomorphism of `Ext_ℤ[G](ℤ, M)` with the cohomology groups of a cochain
complex of explicit homogeneous cochains.

-/
open group_cohomology
universes u v
variables (G : Type u) [group G] (M : Type u) [add_comm_group M]
  [distrib_mul_action G M] (n : ℕ)

noncomputable theory

def cochain_succ.complex : cochain_complex (Module ℤ) ℕ :=
cochain_complex.of (λ n, Module.of ℤ $ cochain_succ G M (n + 1))
 (λ i, (cochain_succ.d rfl).to_int_linear_map)
 (λ i, linear_map.ext $ cochain_succ.d_squared_eq_zero rfl rfl)

local attribute [instance] group_ring.to_module

/-- The group of homogeneous cochains `Gⁿ → M` is isomorphic to the group of
`ℤ[G]`-linear homs `ℤ[Gⁿ] → M`. -/
def cochain_succ_add_equiv : cochain_succ G M n ≃+ (group_ring (fin n → G) →ₗ[group_ring G] M) :=
{ to_fun := λ f,
  { map_smul' := λ g x,
    by {
    refine g.induction_on _ _ _,
    { intro g,
      refine x.induction_on _ _ _,
      { intro x,
        simp only [finsupp.lift_add_hom_apply_single, finsupp.lift_add_hom_apply, one_zsmul,
          add_monoid_hom.to_fun_eq_coe, zmultiples_hom_apply, group_ring.of_apply],
        erw [group_ring.of_smul_of, finsupp.sum_single_index],
        { rw finsupp.sum_single_index,
          { show _ = finsupp.total _ _ _ _ _,
            simp only [zmultiples_hom_apply, one_smul, f.smul_apply,
              finsupp.total_single, ring_hom.id_apply],
            refl,},
          { exact add_monoid_hom.map_zero _}},
        { exact add_monoid_hom.map_zero _}},
      { intros f g hf hg,
        simp only [smul_add, add_monoid_hom.to_fun_eq_coe, add_monoid_hom.map_add] at hf hg ⊢,
        rw [hf, hg] },
      { intros r f hf,
        rw smul_comm,
        simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.map_zsmul] at hf ⊢,
        rw [hf, smul_comm] }},
    { intros f g hf hg,
      simp only [add_smul, add_monoid_hom.to_fun_eq_coe, map_add] at hf hg ⊢,
      rw [hf, hg] },
    { intros r f hf,
      rw smul_assoc,
      simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.map_zsmul] at hf ⊢,
      rw [hf, ←smul_assoc],
      refl }
    }, ..finsupp.lift_add_hom (λ v, zmultiples_hom M (f v)) },
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
    rw [finsupp.lift_add_hom_apply_single, zmultiples_hom_apply, one_smul]
   },
  right_inv := λ f, by
  { ext x,
    refine x.induction_on _ _ _,
    { intro x,
      show finsupp.lift_add_hom (λ v, zmultiples_hom M (f _)) _ = _,
      rw [group_ring.of_apply, finsupp.lift_add_hom_apply_single,
        zmultiples_hom_apply, one_smul],
      refl },
    { intros v w hv hw,
      erw add_monoid_hom.map_add,
      rw [linear_map.map_add, ←hv, ←hw],
      refl },
    { intros r v hv,
      erw add_monoid_hom.map_zsmul,
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

@[simp] lemma cochain_succ_add_equiv_apply {f : cochain_succ G M n} {x} :
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

open category_theory
/-- Expresses a cochain complex as a chain complex in the opposite category. -/
def cochain_to_chain_op {V : Type*} [category V] [preadditive V]
  (C : cochain_complex V ℕ) : chain_complex Vᵒᵖ ℕ :=
{ X := λ n, opposite.op (C.X n),
  d := λ i j, (C.d j i).op,
  shape' := λ i j hij, by rw [C.shape' _ _ hij, op_zero],
  d_comp_d' := λ i j k hij hjk, by rw [←op_comp, C.d_comp_d, op_zero] }

/-- Expresses a chain complex in the opposite category as a cochain complex. -/
def chain_op_to_cochain {V : Type*} [category V] [preadditive V]
  (C : chain_complex Vᵒᵖ ℕ) : cochain_complex V ℕ :=
{ X := λ n, opposite.unop (C.X n),
  d := λ i j, (C.d j i).unop,
  shape' := λ i j hij, by rw [C.shape' _ _ hij, unop_zero],
  d_comp_d' := λ i j k hij hjk, by rw [←unop_comp, C.d_comp_d, unop_zero] }

/-- The chain complex of elements of `(Module ℤ)ᵒᵖ` given by
`Hom(ℤ[G], M) → Hom(ℤ[G²], M) → ...` -/
def map_std_resn := (functor.map_homological_complex ((linear_yoneda ℤ (Module (group_ring G))).obj
  (group_ring.Module_of G M)).right_op (complex_shape.down ℕ)).obj
  (group_ring.std_resn G).complex

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

section
variables {A B C A' B' C' : AddCommGroup.{u}}
  (FA : A ≅ A') (FB : B ≅ B') (FC : C ≅ C') {j : A ⟶ B} {k : B ⟶ C} (w : j ≫ k = 0)
  {j' : A' ⟶ B'} {k' : B' ⟶ C'} (w' : j' ≫ k' = 0) (hj : FA.hom ≫ j' = j ≫ FB.hom)
  (hk : FB.hom ≫ k' = k ≫ FC.hom)

def homology_iso_of_iso : homology j k w ≅ homology j' k' w' :=
{ hom := homology.map _ _ { left := FA.hom, right := FB.hom, w' := hj }
    { left := FB.hom, right := FC.hom, w' := hk } rfl,
  inv := homology.map _ _ { left := FA.inv, right := FB.inv, w' :=
    by { dsimp, rw [iso.inv_comp_eq, ←category.assoc, hj], simp }}
    { left := FB.inv, right := FC.inv, w' :=
    by { dsimp, rw [iso.inv_comp_eq, ←category.assoc, hk], simp }} rfl,
  hom_inv_id' :=
  begin
    ext,
    sorry,
    /- simp_rw [category.comp_id, homology.π_map_assoc, homology.π_map,
      ←category.assoc, ←limits.kernel_subobject_map_comp],
    convert category.id_comp _,
    convert limits.kernel_subobject_map_id,
    ext; simp, -/
  end,
  inv_hom_id' :=
  begin
    ext,
    sorry,
    /- simp_rw [category.comp_id, homology.π_map_assoc, homology.π_map,
      ←category.assoc, ←limits.kernel_subobject_map_comp],
    sorry, -/
  end }

end

lemma cochain_succ_comm_aux (x : cochain_succ G M (n + 1)) :
  cochain_succ_add_equiv _ _ _ (cochain_succ.d rfl x)
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

lemma cochain_succ_comm (x : cochain_succ G M (n + 1)) :
  cochain_succ_add_equiv _ _ _ (cochain_succ.d rfl x) = ((map_std_resn G M).d _ _).unop
    (hom_equiv_yoneda _ _ _ (cochain_succ_add_equiv G M _ x)) :=
begin
  rw [map_std_resn_d_apply, cochain_succ_comm_aux],
  refl,
end

lemma cochain_succ_symm_comm (x : group_ring (fin (n + 1) → G) →ₗ[group_ring G] M) :
  (cochain_succ_add_equiv G M _).symm (((map_std_resn G M).d _ _).unop (hom_equiv_yoneda _ _ _ x))
    = cochain_succ.d rfl ((cochain_succ_add_equiv G M _).symm x) :=
begin
  rw [add_equiv.symm_apply_eq, cochain_succ_comm, add_equiv.apply_symm_apply],
end

/-- The cochain complex of `AddCommGroup`s `Hom(ℤ[G], M) → Hom(ℤ[G²], M) → ...` -/
abbreviation map_std_resn_cochain : cochain_complex.{u} (Module.{u} ℤ) ℕ :=
(chain_op_to_cochain (map_std_resn G M))

/-- The cochain map from our complex of homogeneous cochains to `Hom(-, M)` of our
  projective resolution of the trivial `ℤ[G]`-module `ℤ`. -/
def cochain_succ_to_map_std_resn :
  cochain_succ.complex G M ⟶ map_std_resn_cochain G M :=
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
  map_std_resn_cochain G M ⟶ cochain_succ.complex G M :=
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
  homotopy_equiv (cochain_succ.complex G M) (map_std_resn_cochain G M) :=
{ hom := cochain_succ_to_map_std_resn G M,
  inv := map_std_resn_to_cochain_succ G M,
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
def cohomology_iso :
  (homology_functor _ _ n).obj (cochain_succ.complex G M) ≅
  (homology_functor _ _ n).obj (map_std_resn_cochain G M) :=
homology_obj_iso_of_homotopy_equiv (homotopy_equiv_cochain_succ G M) _

/-- taking homology "commutes with op" -/
def homology_op :
  (homology_functor _ _ n).obj (map_std_resn_cochain G M) ≅
  (opposite.unop $ (homology_functor _ _ n).obj (map_std_resn G M)) :=
sorry

instance : has_projective_resolutions (Module (group_ring G)) := sorry

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
