/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Group.epi_mono
import algebra.category.Group.Z_Module_equivalence
import algebra.category.Module.epi_mono
import algebra.module.injective
import category_theory.preadditive.injective
import group_theory.divisible
import group_theory.order_of_element
import ring_theory.principal_ideal_domain

/-!
# Injective objects in the category of abelian groups

In this file we prove that divisible groups are injective object in category of (additive) abelian
groups.

-/


open category_theory
open_locale pointwise

universe u

variables (A : Type u) [add_comm_group A]

namespace AddCommGroup

lemma injective_of_injective_as_module [injective (⟨A⟩ : Module ℤ)] :
  category_theory.injective (⟨A⟩ : AddCommGroup) :=
{ factors := λ X Y g f m,
  begin
    resetI,
    let G : (⟨X⟩ : Module ℤ) ⟶ ⟨A⟩ :=
      { map_smul' := by { intros, rw [ring_hom.id_apply, g.to_fun_eq_coe, map_zsmul], }, ..g },
    let F : (⟨X⟩ : Module ℤ) ⟶ ⟨Y⟩ :=
      { map_smul' := by { intros, rw [ring_hom.id_apply, f.to_fun_eq_coe, map_zsmul], }, ..f },
    haveI : mono F,
    { refine ⟨λ Z α β eq1, _⟩,
      let α' : AddCommGroup.of Z ⟶ X := α.to_add_monoid_hom,
      let β' : AddCommGroup.of Z ⟶ X := β.to_add_monoid_hom,
      have eq2 : α' ≫ f = β' ≫ f,
      { ext,
        simp only [category_theory.comp_apply, linear_map.to_add_monoid_hom_coe],
        simpa only [Module.coe_comp, linear_map.coe_mk,
          function.comp_app] using fun_like.congr_fun eq1 x },
      rw cancel_mono at eq2,
      ext, simpa only using fun_like.congr_fun eq2 x, },
    refine ⟨(injective.factor_thru G F).to_add_monoid_hom, _⟩,
    ext, convert fun_like.congr_fun (injective.comp_factor_thru G F) x,
  end }

lemma injective_as_module_of_injective_as_Ab [injective (⟨A⟩ : AddCommGroup)] :
  injective (⟨A⟩ : Module ℤ) :=
{ factors := λ X Y g f m,
  begin
    resetI,
    let G : (⟨X⟩ : AddCommGroup) ⟶ ⟨A⟩ := g.to_add_monoid_hom,
    let F : (⟨X⟩ : AddCommGroup) ⟶ ⟨Y⟩ := f.to_add_monoid_hom,
    haveI : mono F,
    { rw mono_iff_injective, intros _ _ h, exact ((Module.mono_iff_injective f).mp m) h, },
    refine ⟨{map_smul' := _, ..injective.factor_thru G F}, _⟩,
    { intros m x, rw [add_monoid_hom.to_fun_eq_coe, ring_hom.id_apply],
      induction m using int.induction_on with n hn n hn,
      { rw [zero_smul],
        convert map_zero _,
        convert zero_smul _ x, },
      { simp only [add_smul, map_add, hn, one_smul], },
      { simp only [sub_smul, map_sub, hn, one_smul] }, },
    ext, convert fun_like.congr_fun (injective.comp_factor_thru G F) x,
  end }

instance injective_of_divisible [divisible_by A ℤ] :
  category_theory.injective (⟨A⟩ : AddCommGroup) :=
@@injective_of_injective_as_module A _ $
@@module.injective_object_of_injective_module ℤ _ A _ _ $
module.Baer.injective $
λ I g, begin
  rcases is_principal_ideal_ring.principal I with ⟨m, rfl⟩,
  by_cases m_eq_zero : m = 0,
  { subst m_eq_zero,
    refine ⟨{ to_fun := _, map_add' := _, map_smul' := _ }, λ n hn, _⟩,
    { intros n, exact g 0, },
    { intros n1 n2,
      simp only [map_zero, add_zero] },
    { intros n1 n2,
      simp only [map_zero, smul_zero], },
    { rw [submodule.span_singleton_eq_bot.mpr rfl, submodule.mem_bot] at hn,
      simp only [hn, map_zero],
      symmetry,
      convert map_zero _, }, },
  { set gₘ := g ⟨m, submodule.subset_span (set.mem_singleton _)⟩ with gm_eq,
    refine ⟨{ to_fun := _, map_add' := _, map_smul' := _ }, λ n hn, _⟩,
    { intros n,
      exact n • divisible_by.div gₘ m, },
    { intros n1 n2, simp only [add_smul], },
    { intros n1 n2,
      rw [ring_hom.id_apply, smul_eq_mul, mul_smul], },
    { rw submodule.mem_span_singleton at hn,
      rcases hn with ⟨n, rfl⟩,
      simp only [gm_eq, algebra.id.smul_eq_mul, linear_map.coe_mk],
      rw [mul_smul, divisible_by.div_cancel (g ⟨m, _⟩) m_eq_zero, ←linear_map.map_smul],
      congr, }, },
end

namespace divisible_emb

-- In this section we prove that any additive abelian group A can be embed into a divisible group,
-- namely `∏ᵢ (ℚ⧸ℤ)` where `i` indexing over all morphism `A →+ ℚ⧸ℤ`

local notation `Z` := (algebra_map ℤ ℚ).to_add_monoid_hom.range

noncomputable instance divisible_ℚ_quotient_ℤ : divisible_by (ℚ ⧸ Z) ℤ :=
@@add_group.divisible_by_int_of_divisible_by_nat _ _ $ @@quotient_add_group.divisible_by _ _ $
@@add_group.divisible_by_nat_of_divisible_by_int _ _ _

local notation `ℚ⧸ℤ` := (ulift.{u} (ℚ ⧸ Z))
instance : add_comm_group (ℚ⧸ℤ) := infer_instance -- this is for typechecking of `divisible_by_Div`
local notation `I` := AddCommGroup.of A ⟶ AddCommGroup.of (ℚ⧸ℤ)
local notation `Div` := AddCommGroup.of (Π (i : I), ℚ⧸ℤ)

noncomputable instance divisible_by_Div : divisible_by Div ℤ :=
pi.divisible_by _

-- We need to show this function is injective
/--
For every abelian group `A`, there is a group homomorphism `A ⟶ ∏ (i : A ⟶ ℚ/ℤ), ℚ/ℤ)`
by evaluating: `a ↦ (f ↦ f a)`.
-/
@[simps] def to_Div : AddCommGroup.of A ⟶ Div :=
{ to_fun := λ a i, i a,
  map_zero' := by simpa only [map_zero],
  map_add' := λ x y, by simpa only [map_add] }

lemma to_Div_inj_of_exists
  (h : ∀ (a : A), a ≠ 0 → ∃ (f : (⟨submodule.span ℤ {a}⟩ : Module ℤ) ⟶ ⟨ℚ⧸ℤ⟩),
    f ⟨a, submodule.subset_span $ set.mem_singleton _⟩ ≠ 0) :
  function.injective $ to_Div A :=
begin
  contrapose! h,
  simp only [function.injective, not_forall] at h,
  obtain ⟨a, b, h1, h2⟩ := h,
  refine ⟨a-b, λ r, h2 (sub_eq_zero.mp r), λ f, _⟩,
  haveI injQZ : category_theory.injective (⟨ℚ⧸ℤ⟩ : Module ℤ) :=
    injective_as_module_of_injective_as_Ab _,
  let g : (⟨(submodule.span ℤ {a - b} : submodule ℤ A)⟩ : Module ℤ) ⟶ ⟨A⟩ :=
    submodule.subtype (submodule.span ℤ {a - b}),
  haveI : mono g,
  { rw Module.mono_iff_injective, apply submodule.injective_subtype, },
  have f_eq := injective.comp_factor_thru f g,
  rw [←fun_like.congr_fun f_eq ⟨a - b, submodule.subset_span (set.mem_singleton _)⟩,
    comp_apply],
  have := congr_fun h1 (injective.factor_thru f g).to_add_monoid_hom,
  rw [to_Div_apply, to_Div_apply, ←sub_eq_zero, ←map_sub] at this,
  convert this,
end

section
variable {A}

/--
`rep x` is defined to be an integer such that `rep x • a = x` for any `x ∈ ⟨a⟩ ⊆ A`.
-/
noncomputable def rep {a : A} (x : submodule.span ℤ {a}) : ℤ :=
(submodule.mem_span_singleton.mp x.2).some

lemma rep_spec {a : A} (x : submodule.span ℤ {a}) : rep x • a = x :=
(submodule.mem_span_singleton.mp x.2).some_spec

end

namespace infinite_order

variables {A} {a : A}

/--
There is a morphism `⟨a⟩ ⟶ ℚ/ℤ` by `r • a ↦ a/2`.
-/
@[reducible] noncomputable def to_fun : submodule.span ℤ {a} → ℚ⧸ℤ :=
λ x, ulift.up $ quotient.mk' (rat.mk (rep x) 2)

variable (infinite_order : ∀ (a : A), add_order_of a = 0)
include infinite_order

lemma infinite_order' (m : ℤ) : m • a = 0 → m = 0 :=
match m with
| int.of_nat 0 := λ _, rfl
| int.of_nat (nat.succ n) := λ h, begin
  erw of_nat_zsmul at h,
  exact false.elim (add_order_of_eq_zero_iff'.mp (infinite_order a) n.succ (nat.zero_lt_succ _) h),
end
| -[1+n] := λ h, begin
  rw [zsmul_neg_succ_of_nat, neg_eq_zero] at h,
  exact false.elim (add_order_of_eq_zero_iff'.mp (infinite_order a) n.succ (nat.zero_lt_succ _) h),
end
end

lemma to_fun_spec.aux {m n : ℤ} (eq1 : m • a = n • a) : m = n :=
begin
  rw [←sub_eq_zero, ←sub_smul] at eq1,
  refine sub_eq_zero.mp (infinite_order' infinite_order _ eq1),
end

lemma rep_add (x y : submodule.span ℤ {a}) : rep (x + y) = rep x + rep y :=
to_fun_spec.aux infinite_order $ (by simp [rep_spec, add_smul] : _ • a = _ • a)

lemma rep_smul (m : ℤ) (x : submodule.span ℤ {a}) : rep (m • x) = m * rep x :=
to_fun_spec.aux infinite_order $ by rw [mul_smul, rep_spec x, rep_spec (m • x), submodule.coe_smul]

lemma to_fun_spec (x : submodule.span ℤ {a}) {m : ℤ} (hm : m • a = (↑x : A)) :
  to_fun x = ⟨quotient.mk' (rat.mk m 2)⟩ :=
by rw show m = rep x, by { apply to_fun_spec.aux infinite_order, rw [hm, rep_spec x] }

lemma map_add' (x y : submodule.span ℤ {a}) :
  to_fun (x + y) = to_fun x + to_fun y :=
begin
  rw [to_fun_spec infinite_order (x + y) (rep_spec _), to_fun_spec infinite_order x (rep_spec _),
    to_fun_spec infinite_order y (rep_spec _)],
  ext1,
  erw [quotient_add_group.eq', rat.neg_def, rat.add_def, rat.add_def,
    rep_add infinite_order, ←add_mul, mul_assoc, neg_mul, neg_add_self, rat.zero_mk],
  exact add_subgroup.zero_mem _, all_goals { norm_num },
end

lemma map_smul' (m : ℤ) (x : submodule.span ℤ {a}) : to_fun (m • x) = m • to_fun x :=
begin
  ext1, erw [quotient_add_group.eq', rep_smul infinite_order, zsmul_eq_mul, rat.coe_int_eq_mk m,
    rat.mul_def, show (1 : ℤ) * 2 = 2, from rfl, neg_add_self],
  exact add_subgroup.zero_mem _, all_goals { norm_num },
end

/--
There is a morphism `⟨a⟩ ⟶ ℚ/ℤ` by `r • a ↦ a/2`.
-/
@[simps] noncomputable def to_quotient : (⟨submodule.span ℤ {a}⟩ : Module ℤ) ⟶ ⟨ℚ⧸ℤ⟩ :=
{ to_fun := to_fun,
  map_add' := map_add' infinite_order,
  map_smul' := map_smul' infinite_order }

lemma to_quotient.apply_ne_zero :
  to_quotient infinite_order ⟨a, submodule.mem_span_singleton_self _⟩ ≠ 0 :=
have H : ∀ (m : ℤ), - m * 2 ≠ 1, from λ m,
by { rw [mul_comm, ←bit0_eq_two_mul], exact int.bit0_ne_bit1 (-m) 0 },
begin
  intros r, rw [to_quotient_apply, ulift.ext_iff] at r,
  change quotient.mk' _ = (quotient.mk' 0 : ℚ ⧸ Z) at r,
  rw [quotient_add_group.eq', add_zero, rat.neg_def] at r,
  rcases r with ⟨m, eq1⟩,
  rw [show (algebra_map ℤ ℚ).to_add_monoid_hom m = (m : ℚ), from rfl, rat.coe_int_eq_mk _,
    rat.mk_eq, mul_one, eq_neg_iff_eq_neg, ←neg_mul] at eq1,
  refine H m (sub_eq_zero.mp (infinite_order' infinite_order _ (_ : _ • a = _))),
  rw [sub_smul, one_smul, sub_eq_zero, ←eq1, rep_spec, subtype.coe_mk],
  all_goals { norm_num },
end

end infinite_order

end divisible_emb

end AddCommGroup
