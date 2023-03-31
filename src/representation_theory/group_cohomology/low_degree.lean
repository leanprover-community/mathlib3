import algebra.category.Module.images
import algebra.category.Module.subobject
import representation_theory.group_cohomology.basic
import representation_theory.invariants
universes v u
noncomputable theory

variables {k G : Type u} [comm_ring k] [group G] (A : Rep k G)

@[simp] lemma fin.mul_nth_zero_one {α : Type*} [has_mul α] (f : fin 1 → α) :
  fin.mul_nth 0 f = default :=
by ext x; exact fin.elim0 x

@[simp] lemma fin.mul_nth_zero_two {α : Type*} [has_mul α] (f : fin 2 → α) :
  fin.mul_nth 0 f = λ i, f 0 * f 1 :=
by ext x; simpa only [subsingleton.elim x 0, fin.mul_nth_eq_apply f (fin.coe_zero _),
    fin.add_nat_one, fin.succ_zero_eq_one']

namespace group_cohomology
open category_theory category_theory.limits
section zeroth

def zero_cochains_iso : (inhomogeneous_cochains A).X 0 ≅ Module.of k A :=
(linear_equiv.fun_unique (fin 0 → G) k A).to_Module_iso

def one_cochains_iso : (inhomogeneous_cochains A).X 1 ≅ Module.of k (G → A) :=
(linear_equiv.fun_congr_left k A (equiv.fun_unique (fin 1) G).symm).to_Module_iso

@[simps] def d_zero : A →ₗ[k] (G → A) :=
{ to_fun := λ m g, A.ρ g m - m,
  map_add' := λ x y, funext $ λ g, by simpa only [map_add, add_sub_add_comm],
  map_smul' := λ r x, funext $ λ g, by dsimp; rw [map_smul, smul_sub] }

-- what's the best statement here? one composition on each side of the = instead of 2 on the LHS?
lemma d_zero_eq : (zero_cochains_iso A).hom ≫ Module.of_hom (d_zero A)
  ≫ (one_cochains_iso A).inv = (inhomogeneous_cochains A).d 0 1 :=
begin
  ext x y,
  simp only [Module.coe_comp, function.comp_app, inhomogeneous_cochains.d_def,
    inhomogeneous_cochains.d_apply, fin.add_nat_one, finset.range_one, finset.sum_singleton,
    pow_one, fin.mul_nth_zero_one, neg_smul, one_smul, zero_cochains_iso, one_cochains_iso,
    linear_equiv.to_Module_iso_inv, linear_equiv.fun_congr_left_symm, equiv.symm_symm,
    linear_equiv.to_Module_iso_hom, linear_equiv.coe_coe, linear_equiv.fun_unique_apply,
    function.eval_apply, linear_equiv.fun_congr_left_apply, equiv.fun_unique_apply,
    linear_map.fun_left_apply, fin.default_eq_zero, Module.of_hom, id.def, d_zero_apply,
    sub_eq_add_neg],
  congr,
end

open representation

def zeroth : Module k := Module.of k (invariants A.ρ)

lemma d_zero_ker_eq_invariants : (d_zero A).ker = invariants A.ρ :=
begin
  ext,
  simp only [linear_map.mem_ker, mem_invariants, ←@sub_eq_zero _ _ _ x],
  exact function.funext_iff,
end

open category_theory category_theory.limits

def zeroth_iso : group_cohomology A 0 ≅ zeroth A :=
(inhomogeneous_cochains A).homology_zero_iso ≪≫ kernel.map_iso _ _
  (zero_cochains_iso A) (one_cochains_iso A)
  (by rw [←iso.eq_comp_inv, category.assoc]; exact (d_zero_eq A).symm)
  ≪≫ Module.kernel_iso_ker (Module.of_hom (d_zero A))
  ≪≫ (linear_equiv.of_eq _ _ (d_zero_ker_eq_invariants A)).to_Module_iso

end zeroth
section first

def two_cochains_iso : (inhomogeneous_cochains A).X 2 ≅ Module.of k (G × G → A) :=
(linear_equiv.fun_congr_left k A $ (pi_fin_two_equiv (λ i, G)).symm).to_Module_iso

@[simps] def d_one : (G → A) →ₗ[k] (G × G → A) :=
{ to_fun := λ f g, A.ρ g.1 (f g.2) - f (g.1 * g.2) + f g.1,
  map_add' := λ x y, funext $ λ g, by dsimp; rw [map_add, add_add_add_comm, add_sub_add_comm],
  map_smul' := λ r x, funext $ λ g, by dsimp; rw [map_smul, smul_add, smul_sub], }

lemma d_one_eq : (one_cochains_iso A).hom ≫ Module.of_hom (d_one A)
  ≫ (two_cochains_iso A).inv = (inhomogeneous_cochains A).d 1 2 :=
begin
  ext x y,
  simp only [Module.coe_comp, function.comp_app, inhomogeneous_cochains.d_def,
    inhomogeneous_cochains.d_apply, fin.add_nat_one, finset.range_one, finset.sum_singleton,
    pow_one, fin.mul_nth_zero_one, neg_smul, one_smul, two_cochains_iso, one_cochains_iso,
    linear_equiv.to_Module_iso_inv, linear_equiv.fun_congr_left_symm, equiv.symm_symm,
    linear_equiv.to_Module_iso_hom, linear_equiv.coe_coe, linear_equiv.fun_unique_apply,
    function.eval_apply, linear_equiv.fun_congr_left_apply, equiv.fun_unique_apply,
    linear_map.fun_left_apply, fin.default_eq_zero, Module.of_hom, id.def, d_one_apply,
    sub_eq_add_neg, pi_fin_two_equiv_apply, equiv.fun_unique_symm_apply, add_assoc],
  rw [finset.range_succ, finset.sum_insert finset.not_mem_range_self],
  simp only [finset.range_one, finset.sum_singleton, neg_one_sq, one_smul, pow_one,
    fin.mul_nth_zero_two, neg_smul, add_comm (x (fin.mul_nth 1 y))],
  congr,
  { ext x y, simpa only [subsingleton.elim x 0], },
  { ext i,
    simpa only [subsingleton.elim i 0, fin.mul_nth_lt_apply y
      (show ((0 : fin 1) : ℕ) < 1, from zero_lt_one)] },
end

-- could prove this using d_zero_eq and d_one_eq but directly is easier...
lemma d_zero_range_le_d_one_ker : (d_zero A).range ≤ (d_one A).ker :=
begin
  rintros x ⟨y, rfl⟩,
  rw linear_map.mem_ker,
  ext,
  simp only [d_one_apply, d_zero_apply, map_sub, map_mul, linear_map.mul_apply],
  abel,
end

def first : Module k :=
Module.of k ((d_one A).ker ⧸ ((d_zero A).cod_restrict (d_one A).ker $
λ c, d_zero_range_le_d_one_ker A ⟨c, rfl⟩).range)

variables {R : Type u} [comm_ring R] {M N P : Module.{u} R} (f : M ⟶ N) (g : N ⟶ P)

@[reassoc] lemma Module.factor_thru_image_comp_image_iso_range_hom :
  factor_thru_image f ≫ (Module.image_iso_range f).hom
  = Module.of_hom (linear_map.range_restrict f) :=
begin
  simp only [←iso.eq_comp_inv, ←cancel_mono (limits.image.ι f), category.assoc,
    Module.image_iso_range_inv_image_ι, image.fac],
  ext,
  refl,
end

lemma Module.image_to_kernel_eq : image_to_kernel f g sorry =
  (image_subobject_iso f ≪≫ Module.image_iso_range f).hom ≫ Module.of_hom
  (linear_map.cod_restrict (linear_map.ker g) (linear_map.range f).subtype sorry) ≫
  (kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).inv :=
begin
  simp only [←cancel_mono (kernel_subobject g).arrow, ←cancel_epi (factor_thru_image_subobject f),
    image_to_kernel_arrow, image_subobject_arrow_comp, iso.trans_hom, iso.trans_inv, category.assoc,
    kernel_subobject_arrow', Module.kernel_iso_ker_inv_kernel_ι, factor_thru_image_subobject,
    iso.inv_hom_id_assoc, image_subobject_arrow', image.fac],
  simp only [←category.assoc, Module.factor_thru_image_comp_image_iso_range_hom],
  ext,
  refl,
end

/-def Module.homology_iso {R : Type u} [comm_ring R] {M N P : Module.{u} R} (f : M ⟶ N) (g : N ⟶ P)
  (H : f ≫ g = 0) :
  homology f g H ≅ cokernel (Module.of_hom ((linear_map.range f).subtype.cod_restrict
    (linear_map.ker g) sorry)) :=
cokernel.map_iso (image_to_kernel f g sorry) _ (image_subobject_iso f ≪≫ Module.image_iso_range f)
  (kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g)
  (by { simp only [Module.image_to_kernel_eq, category.assoc, cancel_epi, iso.inv_hom_id],
    ext, refl })-/
set_option profiler true --11.4s
def Module.homology_iso :
  homology f g sorry ≅ Module.of R (g.ker ⧸ (f.cod_restrict g.ker sorry).range) :=
cokernel.map_iso (image_to_kernel f g sorry) (Module.of_hom ((linear_map.range f).subtype.cod_restrict
  (linear_map.ker g) sorry)) (image_subobject_iso f ≪≫ Module.image_iso_range f)
  (kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g)
  (by { simp only [Module.image_to_kernel_eq, category.assoc, cancel_epi, iso.inv_hom_id],
    ext, refl })
  ≪≫ Module.cokernel_iso_range_quotient _
  ≪≫ (submodule.quotient.equiv _ _ (linear_equiv.refl _ _)
(begin
  show submodule.map _ (linear_map.cod_restrict _ _ _).range = _,
  simp only [linear_map.range_eq_map, linear_map.map_cod_restrict,
    submodule.map_subtype_top, eq_self_iff_true],
  exact submodule.map_id _,
end)).to_Module_iso
#check homology
#exit
lemma Module.homology_iso_hom :
  (Module.homology_iso f g).hom = homology.desc _ _ _
    ((kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).hom ≫ submodule.mkq _) sorry :=
begin
  dunfold Module.homology_iso,
  simp only [iso.trans_hom, category.assoc, submodule.quotient.equiv_refl, cokernel.map_iso_hom,
    linear_equiv.to_Module_iso_hom],
  sorry
end

section


-- want map from kernel_subobject g -> g.ker/
/-- The cokernel cocone induced by the projection onto the quotient. -/
def cokernel_cocone (H : f ≫ g = 0) : cokernel_cofork (image_to_kernel f g H) :=
cokernel_cofork.of_π ((kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).hom ≫
  Module.of_hom (submodule.mkq (linear_map.cod_restrict (linear_map.ker g) f sorry).range)) $
begin
  rw Module.image_to_kernel_eq,
  simp only [iso.trans_hom, iso.trans_inv, category.assoc, iso.inv_hom_id_assoc,
    preadditive.is_iso.comp_left_eq_zero],

end

/-- The projection onto the quotient is a cokernel in the categorical sense. -/
def cokernel_is_colimit (H : f ≫ g = 0) : is_colimit (cokernel_cocone f g H) :=
cofork.is_colimit.mk _
  (λ s, ((linear_map.cod_restrict (linear_map.ker g) f sorry).range).liftq
    ((kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).inv ≫ cofork.π s) $
    begin
      have := cokernel_cofork.condition s,
      dsimp * at *,
      rw linear_map.range_le_ker_iff,
      ext,
      simp only [linear_map.coe_comp, Module.coe_comp, function.comp_app, linear_map.zero_apply],

    end) sorry _
#exit
  (λ s, f.range.liftq (cofork.π s) $ linear_map.range_le_ker_iff.2 $ cokernel_cofork.condition s)
  (λ s, f.range.liftq_mkq (cofork.π s) _)
  (λ s m h,
  begin
    haveI : epi (as_hom f.range.mkq) := (epi_iff_range_eq_top _).mpr (submodule.range_mkq _),
    apply (cancel_epi (as_hom f.range.mkq)).1,
    convert h,
    exact submodule.liftq_mkq _ _ _

  end)
end

/-- The category of R-modules has kernels, given by the inclusion of the kernel submodule. -/
lemma has_kernels_Module : has_kernels (Module R) :=
⟨λ X Y f, has_limit.mk ⟨_, kernel_is_limit f⟩⟩

/-- The category or R-modules has cokernels, given by the projection onto the quotient. -/
lemma has_cokernels_Module : has_cokernels (Module R) :=
⟨λ X Y f, has_colimit.mk ⟨_, cokernel_is_colimit f⟩⟩

open_locale Module

local attribute [instance] has_kernels_Module
local attribute [instance] has_cokernels_Module

variables {G H : Module.{v} R} (f : G ⟶ H)
/--
The categorical cokernel of a morphism in `Module`
agrees with the usual module-theoretical quotient.
-/
noncomputable def cokernel_iso_range_quotient {G H : Module.{v} R} (f : G ⟶ H) :
  cokernel f ≅ Module.of R (H ⧸ f.range) :=
colimit.iso_colimit_cocone ⟨_, cokernel_is_colimit f⟩


end
def fml {R M N : Type*} [ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]
  (f : M →ₗ[R] N) :
  cokernel (Module.of_hom f) ≅ Module.of R (N ⧸ f.range) :=
Module.cokernel_iso_range_quotient _

def FUCKSAKE {R : Type*} [ring R] (M N P : Module R) (f : M ⟶ N) (g : N ⟶ P) (H : f ≫ g = 0) :
  cokernel (Module.of_hom ((linear_map.range f).subtype.cod_restrict
    (linear_map.ker g) sorry).range.mkq) ≅ homology f g H :=
begin
  refine cokernel.map_iso _ _ _ _ _,
end
--cokernel ((linear_map.range f).subtype.cod_restrict (linear_map.ker g) sorry).range.mkq ≅
    --homology f g H


    #exit
noncomputable! def fucksake2 {R : Type*} [ring R] (M N P : Module R)
  (f : M ⟶ N) (g : N ⟶ P) (H : f ≫ g = 0) :
Module.of R
      (linear_map.ker g ⧸ ((linear_map.range f).subtype.cod_restrict (linear_map.ker g) sorry).range) ≅
    homology f g H :=
begin
  refine (Module.cokernel_iso_range_quotient (Module.of_hom $
    ((linear_map.range f).subtype.cod_restrict (linear_map.ker g) sorry))).symm ≪≫ _,



end

#exit
noncomputable! def fucksake2 {R M N P : Type*} [ring R] [add_comm_group M] [add_comm_group N] [add_comm_group P]
  [module R M] [module R N] [module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (H : g.comp f = 0) :
  Module.of R (g.ker ⧸ (f.cod_restrict g.ker sorry).range)
  ≅ homology (Module.of_hom f) (Module.of_hom g) H :=
(submodule.quotient.equiv (f.cod_restrict g.ker sorry).range
  (f.range.subtype.cod_restrict g.ker sorry).range (linear_equiv.refl _ _) sorry).to_Module_iso
  ≪≫ _


#check cokernel.map_iso
def fucksake2 : first A ≅ homology (Module.of_hom (d_zero A)) (Module.of_hom (d_one A)) sorry :=
(submodule.quotient.equiv ((d_zero A).cod_restrict (d_one A).ker $
λ c, d_zero_range_le_d_one_ker A ⟨c, rfl⟩).range ((d_zero A).range.subtype.cod_restrict
(d_one A).ker sorry).range (linear_equiv.refl _ _) sorry).to_Module_iso ≪≫
(Module.cokernel_iso_range_quotient (Module.of_hom $ (d_zero A).range.subtype.cod_restrict
(d_one A).ker sorry).range (linear_equiv.refl _ _)).symm ≪≫ _

#exit
(Module.cokernel_iso_range_quotient (Module.of_hom $ (d_zero A).cod_restrict (d_one A).ker $
λ c, d_zero_range_le_d_one_ker A ⟨c, rfl⟩)).symm ≪≫
cokernel.map_iso _ _ _ _ _

#exit
(submodule.quotient.equiv _ _ (kernel_subobject_iso _ ≪≫ Module.kernel_iso_ker _).symm.to_linear_equiv _).to_Module_iso
 ≪≫ _ --(Module.cokernel_iso_range_quotient _).symm


def first_iso : group_cohomology A 1 ≅ first A :=
(inhomogeneous_cochains A).homology_succ_iso 0 ≪≫
_

#exit
cokernel.map_iso _ _ (image_subobject_iso _ ≪≫ Module.image_iso_range _ ≪≫ _) _ _
≪≫ (Module.cokernel_iso_range_quotient (Module.of_hom _))
≪≫ (submodule.quotient.equiv ((d_zero A).cod_restrict (d_one A).ker $
λ c, d_zero_range_le_d_one_ker A ⟨c, rfl⟩).range ((d_zero A).range.subtype.cod_restrict (d_one A).ker
sorry).range (linear_equiv.refl _ _)
(begin
  rw fucksake,
  exact submodule.map_id _,
  sorry,
end)).symm.to_Module_iso

end first
end group_cohomology
