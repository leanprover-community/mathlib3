/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Group.epi_mono
import algebra.group.ulift
import algebra.category.Group.Z_Module_equivalence
import algebra.category.Module.epi_mono
import algebra.module.injective
import category_theory.preadditive.injective
import group_theory.divisible
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

private def ℤ_as_ℚ_subgroup : add_subgroup ℚ :=
{ carrier := set.range (coe : ℤ → ℚ),
  add_mem' := by { rintros _ _ ⟨a, rfl⟩ ⟨b, rfl⟩, refine ⟨a + b, by norm_cast⟩, },
  zero_mem' := ⟨0, rfl⟩,
  neg_mem' := by { rintros _ ⟨a, rfl⟩, refine ⟨-a, by norm_cast⟩ } }

local notation `Z` := ℤ_as_ℚ_subgroup

noncomputable instance divisible_ℚ_quotient_ℤ : divisible_by (ℚ ⧸ Z) ℤ :=
add_comm_group.divisible_by_int_of_smul_top_eq_top _ $ λ n hn, set_like.ext $ λ x,
{ mp := λ _, trivial,
  mpr := λ _, begin
    induction x using quotient.induction_on',
    refine ⟨quotient.mk' (x/n), trivial, _⟩,
    change quotient.mk' (n • _) = _,
    congr,
    rw [div_eq_mul_inv, mul_comm],
    norm_num,
    rw [←mul_assoc, mul_inv_cancel, one_mul],
    exact_mod_cast hn,
  end }

local notation `ℚ⧸ℤ` := (ulift.{u} (ℚ ⧸ Z))
instance : add_comm_group (ℚ⧸ℤ) := infer_instance
local notation `I` := AddCommGroup.of A ⟶ AddCommGroup.of (ℚ⧸ℤ)
local notation `Div` := AddCommGroup.of (Π (i : I), ℚ⧸ℤ)

noncomputable instance divisible_by_Div : divisible_by Div ℤ :=
pi.divisible_by _

-- We need to show this function is injective
@[simps]
def embed_into_divisible : AddCommGroup.of A ⟶ Div :=
{ to_fun := λ a i, i a,
  map_zero' := by simpa only [map_zero],
  map_add' := λ x y, by simpa only [map_add] }

section
variable {A}

noncomputable def rep {a : A} (x : (submodule.span ℤ {a} : submodule ℤ A)) : ℤ :=
(submodule.mem_span_singleton.mp x.2).some

lemma rep_eq {a : A} (x : (submodule.span ℤ {a} : submodule ℤ A)) :
  (rep x) • a = x :=
(submodule.mem_span_singleton.mp x.2).some_spec

end

namespace infinite_order

variable {A}

variables {a : A}


noncomputable def to_fun : (submodule.span ℤ {a} : submodule ℤ A) → ℚ⧸ℤ :=
λ x, ⟨quotient.mk' (rat.mk (rep x) 2)⟩

lemma to_fun_wd.aux (infinite_order : ∀ (n : ℕ), n ≠ 0 → n • a ≠ 0)
  {m n : ℤ} (eq1 : m • a = n • a) :
  m = n :=
begin
  rw [←sub_eq_zero, ←sub_smul] at eq1,
  have eq2 : (m - n).nat_abs • a = 0,
  { suffices : ((m - n).nat_abs : ℤ) • a = 0,
    { rw ←this,
      simp only [coe_nat_zsmul], },
    rw [←int.abs_eq_nat_abs],
    refine abs_by_cases (λ (m : ℤ), m • a = 0) eq1 _,
    rw [neg_smul, eq1, neg_zero], },
  specialize infinite_order (int.nat_abs (m - n)),
  suffices : (m - n).nat_abs = 0,
  { rwa [int.nat_abs_eq_zero, sub_eq_zero] at this, },
  contrapose! infinite_order,
  refine ⟨infinite_order, eq2⟩,
end

lemma to_fun_wd
  (infinite_order : ∀ (n : ℕ), n ≠ 0 → n • a ≠ 0)
  (x : (submodule.span ℤ {a} : submodule ℤ A))
  {m : ℤ} (hm : m • a = x) :
  to_fun x = ⟨quotient.mk' (rat.mk m 2)⟩ :=
begin
  dunfold to_fun,
  have eq1 : m = rep x,
  { have := rep_eq x,
    rw ←hm at this,
    rw to_fun_wd.aux infinite_order this, },
  subst eq1,
end

lemma map_add'
  (infinite_order : ∀ (n : ℕ), n ≠ 0 → n • a ≠ 0)
  (x y : (submodule.span ℤ {a} : submodule ℤ A)) :
  to_fun (x + y) = to_fun x + to_fun y :=
begin
  have : (rep x + rep y) • a = rep (x + y) • a,
  { rw [add_smul, rep_eq, rep_eq, rep_eq, submodule.coe_add], },
  have := to_fun_wd.aux infinite_order this,
  dunfold to_fun,
  ext1,
  change _ = _ + _,
  dsimp only,
  change _ = quotient.mk' (_ + _),
  rw [quotient_add_group.eq', rat.neg_def, rat.add_def, rat.add_def];
  norm_num,
  simp only [add_mul, mul_assoc],
  norm_num,
  rw [←add_mul, ←neg_mul, ←add_mul, this, ←sub_eq_neg_add, sub_self, zero_mul],
  norm_num,
  exact add_subgroup.zero_mem _,
end

lemma map_smul'
  (infinite_order : ∀ (n : ℕ), n ≠ 0 → n • a ≠ 0)
  (m : ℤ) (x : (submodule.span ℤ {a} : submodule ℤ A)) :
  to_fun (m • x) = m • to_fun x :=
begin
  have : (m * rep x) • a = rep (m • x) • a,
  { rw [mul_smul, rep_eq x, rep_eq (m • x), submodule.coe_smul], },
  have := to_fun_wd.aux infinite_order this,
  dunfold to_fun,
  ext1,
  change _ = _ • _,
  change _ = quotient.mk' _,
  dsimp only,
  rw [quotient_add_group.eq', ←this, rat.neg_def],
  norm_num,
  rw [show (m : ℚ) = rat.mk m 1, from rat.coe_int_eq_mk _, rat.mul_def, rat.add_def];
  norm_num,
  refine ⟨0, by norm_num⟩,
end

noncomputable def to_quotient
  (infinite_order : ∀ (n : ℕ), n ≠ 0 → n • a ≠ 0) : (⟨(submodule.span ℤ {a} : submodule ℤ A)⟩ : Module ℤ) ⟶ ⟨ℚ⧸ℤ⟩ :=
{ to_fun := to_fun,
  map_add' := map_add' infinite_order,
  map_smul' := map_smul' infinite_order }

lemma to_quotient.apply_ne_zero
  (infinite_order : ∀ (n : ℕ), n ≠ 0 → n • a ≠ 0) :
  to_quotient infinite_order ⟨a, submodule.mem_span_singleton_self _⟩ ≠ 0 :=
have H : ∀ (m : ℤ), - m * 2 ≠ 1,
begin
  intros m r,
  have : (2 : ℤ) ∣ -m * 2,
  { exact dvd_mul_left 2 (-m), },
  rw r at this,
  have not_dvd : ¬ (2 : ℤ) ∣ 1,
  { rw ←int.exists_lt_and_lt_iff_not_dvd,
    refine ⟨0, by linarith, by linarith⟩,
    linarith, },
  exact not_dvd this,
end,
begin
  dunfold to_quotient,
  change to_fun _ ≠ 0,
  dunfold to_fun,
  suffices : (quotient.mk' (rat.mk (rep ⟨a, _⟩) 2) : ℚ ⧸ ℤ_as_ℚ_subgroup) ≠ 0,
  { contrapose! this,
    rw ulift.ext_iff at this,
    exact this, },
  intro r,
  rw show (0 : ℚ ⧸ ℤ_as_ℚ_subgroup) = quotient.mk' 0, from rfl at r,
  rw [quotient_add_group.eq', add_zero, rat.neg_def] at r,
  rcases r with ⟨m, eq1⟩,
  rw show (m : ℚ) = rat.mk m 1, from rat.coe_int_eq_mk _ at eq1,
  rw [rat.mk_eq, mul_one] at eq1,
  replace eq1 : - m * 2 = rep ⟨a, _⟩,
  { rw [neg_mul, eq1, neg_neg], },
  have eq2 : (- m * 2) • a = rep ⟨a, _⟩ • a,
  { rw [eq1], },
  rw rep_eq at eq2,
  rw ←subtype.val_eq_coe at eq2,
  dsimp only at eq2,
  have eq3 : (-m * 2 - 1) • a = 0,
  { rw [sub_smul, one_smul, sub_eq_zero, eq2], },
  have eq4 : (-m * 2 - 1).nat_abs • a = 0,
  { suffices : ((-m * 2 - 1).nat_abs : ℤ) • a = 0,
    { rw ←this,
      simp only [coe_nat_zsmul], },
    rw [←int.abs_eq_nat_abs],
    refine abs_by_cases (λ (m : ℤ), m • a = 0) eq3 _,
    rw [neg_smul, eq3, neg_zero], },
  have eq5 : (-m * 2 - 1).nat_abs = 0,
  { contrapose! infinite_order,
    exact ⟨_, infinite_order, eq4⟩, },
  rw int.nat_abs_eq_zero at eq5,
  rw [sub_eq_zero] at eq5,
  exact H _ eq5,
  norm_num,
  norm_num,
end

end infinite_order

namespace finite_order

variables {A} {a : A}

noncomputable def order
  (fo : ∃ (n : ℕ), n ≠ 0 ∧ n • a = 0) : ℕ :=
@nat.find _ (classical.dec_pred _) fo

lemma order_ne_zero
  (fo : ∃ (n : ℕ), n ≠ 0 ∧ n • a = 0) :
  (order fo) ≠ 0 :=
(@nat.find_spec _ (classical.dec_pred _) fo).1

lemma order_smul (fo : ∃ (n : ℕ), n ≠ 0 ∧ n • a = 0) :
  (order fo) • a = 0 :=
(@nat.find_spec _ (classical.dec_pred _) fo).2

lemma order_is_min
  (fo : ∃ (n : ℕ), n ≠ 0 ∧ n • a = 0)
  {m : ℕ} (m_ne_zero : m ≠ 0) (hm : m • a = 0) :
  order fo ≤ m :=
@nat.find_min' _ (classical.dec_pred _) fo _ ⟨m_ne_zero, hm⟩

lemma dvd_of_smul_eq_zero
  (fo : ∃ (n : ℕ), n ≠ 0 ∧ n • a = 0)
  {m : ℕ} (m_ne_zero : m ≠ 0) (hm : m • a = 0) :
  order fo ∣ m :=
begin
  have eq1 := order_smul fo,
  have ineq1 := order_is_min fo m_ne_zero hm,
  set r := m % order fo with r_eq,
  set m' := m / order fo with m'_eq,
  have eq2 : m = order fo * m' + r,
  { rw [r_eq, m'_eq, nat.div_add_mod m (order fo)] },
  have eq3 : r • a = 0,
  { rwa [eq2, add_smul, mul_comm, mul_smul, order_smul, smul_zero, zero_add] at hm, },
  by_cases ineq2 : r = 0,
  { rw ineq2 at eq2 eq3,
    rw [add_zero] at eq2,
    exact ⟨_, eq2⟩ },
  { have ineq3 : r < order fo,
    { rw [r_eq],
      apply nat.mod_lt,
      exact nat.pos_of_ne_zero (order_ne_zero fo), },
    have ineq4 : order fo ≤ r := order_is_min fo ineq2 eq3,
    linarith },
end

noncomputable def to_fun (fo : ∃ (n : ℕ), n ≠ 0 ∧ n • a = 0) : (submodule.span ℤ {a} : submodule ℤ A) → ℚ⧸ℤ :=
λ x, ⟨quotient.mk' $ rat.mk (rep x) (order fo)⟩

lemma to_fun_wd (fo : ∃ (n : ℕ), n ≠ 0 ∧ n • a = 0) (x : (submodule.span ℤ {a} : submodule ℤ A))
  {m : ℤ} (hm : m • a = x) :
  to_fun fo x = ⟨quotient.mk' $ rat.mk m (order fo)⟩ :=
begin
  have INEQ : ((order fo) : ℤ) ≠ 0,
  { norm_cast, apply order_ne_zero, },
  dunfold to_fun,
  ext,
  dsimp only,
  rw [quotient_add_group.eq', rat.neg_def, rat.add_def, ←add_mul, ←sub_eq_neg_add,
    show rat.mk ((m - rep x) * (order fo)) ((order fo) * (order fo)) = rat.mk (m - rep x) (order fo),
    { rw [rat.mk_eq],
      ring,
      rw mul_ne_zero_iff,
      exact ⟨INEQ, INEQ⟩,
      exact INEQ }],
  all_goals { try { exact INEQ } },
  have eq1 := congr_arg2 has_sub.sub hm (rep_eq x),
  rw [sub_self, ←sub_smul] at eq1,
  have eq2 : (m - rep x).nat_abs • a = 0,
  { suffices : ((m - rep x).nat_abs : ℤ) • a = 0,
    { rwa coe_nat_zsmul at this, },
    rw ←int.abs_eq_nat_abs,
    refine abs_by_cases (λ (m : ℤ), m • a = 0) eq1 _,
    rw [neg_smul, eq1, neg_zero], },
  by_cases ineq1 : (m - rep x).nat_abs = 0,
  { rw int.nat_abs_eq_zero at ineq1,
    rw ineq1,
    exact ⟨0, by norm_num⟩, },
  have dvd1 := dvd_of_smul_eq_zero fo ineq1 eq2,
  have dvd2 : (order fo : ℤ) ∣ (m - rep x).nat_abs,
  { rcases dvd1 with ⟨k, hk⟩,
    refine ⟨k, _⟩,
    exact_mod_cast hk, },
  rw int.dvd_nat_abs at dvd2,
  rcases dvd2 with ⟨k, hk⟩,
  refine ⟨k, _⟩,
  rw [hk, show (k : ℚ) = rat.mk k 1, from rat.coe_int_eq_mk _,
    rat.mk_eq, mul_one, mul_comm],
  linarith,
  exact INEQ,
end

lemma map_add' (fo : ∃ (n : ℕ), n ≠ 0 ∧ n • a = 0)
  (x y : (submodule.span ℤ {a} : submodule ℤ A)) :
  to_fun fo (x + y) = to_fun fo x + to_fun fo y :=
begin
  have INEQ : ((order fo) : ℤ) ≠ 0,
  { norm_cast, apply order_ne_zero, },

  have eq1 : rep (x + y) • a = (rep x + rep y) • a,
  { rw [rep_eq, add_smul, rep_eq, rep_eq],
    refl },
  have eq2 : ↑(x + y) = (rep x + rep y) • a := by rwa [rep_eq] at eq1,
  rw to_fun_wd fo (x + y) eq2.symm,
  ext,
  dunfold to_fun,
  change quotient.mk' _ = quotient.mk' (_ + _),
  rw [quotient_add_group.eq', rat.neg_def, rat.add_def,
    rat.add_def, ←add_mul, mul_assoc, ←add_mul, ←sub_eq_neg_add,
    sub_self, zero_mul],
  suffices : (0 : ℚ) ∈ ℤ_as_ℚ_subgroup,
  { convert this,
    norm_num, },
  exact ⟨0, rfl⟩,
  exact INEQ,
  rw mul_ne_zero_iff,
  exact ⟨INEQ, INEQ⟩,
  exact INEQ,
  exact INEQ,
end

lemma map_smul' (fo : ∃ (n : ℕ), n ≠ 0 ∧ n • a = 0) (m : ℤ)
  (x : (submodule.span ℤ {a} : submodule ℤ A)) :
  to_fun fo (m • x) = m • to_fun fo x :=
begin
  have INEQ : ((order fo) : ℤ) ≠ 0,
  { norm_cast, apply order_ne_zero, },
  have eq1 : (m * rep x) • a = rep (m • x) • a,
  { rw [mul_smul, rep_eq x, rep_eq (m • x)],
    refl, },
  have eq2 : (m * rep x) • a = (m • x),
  { rw rep_eq at eq1,
    exact eq1 },
  rw to_fun_wd fo (m • x) eq2,
  dunfold to_fun,
  ext,
  change quotient.mk' _ = quotient.mk' (_ • _),
  rw [quotient_add_group.eq', rat.neg_def],
  norm_num,
  rw [show (m : ℚ) = rat.mk m 1, from rat.coe_int_eq_mk _,
    rat.mul_def, rat.add_def, one_mul, ←add_mul, ←sub_eq_neg_add,
    sub_self, zero_mul],
  suffices : (0 : ℚ) ∈ ℤ_as_ℚ_subgroup,
  { convert this,
    norm_num },
  exact ⟨0, rfl⟩,
  exact INEQ,
  rw one_mul,
  exact INEQ,
  linarith,
  exact INEQ,
end

noncomputable def to_quotient (fo : ∃ (n : ℕ), n ≠ 0 ∧ n • a = 0) :
  (⟨(submodule.span ℤ {a} : submodule ℤ A)⟩ : Module ℤ) ⟶ ⟨ℚ⧸ℤ⟩ :=
{ to_fun := to_fun fo,
  map_add' := map_add' fo,
  map_smul' := map_smul' fo }

lemma to_quotient.apply_ne_zero (fo : ∃ (n : ℕ), n ≠ 0 ∧ n • a = 0)
  (ha : a ≠ 0) :
  to_quotient fo ⟨a, submodule.mem_span_singleton_self _⟩ ≠ 0 :=
begin
  have INEQ : ((order fo) : ℤ) ≠ 0,
  { norm_cast, apply order_ne_zero, },

  change to_fun fo _ ≠ 0,
  rw to_fun_wd fo ⟨a, _⟩ (rep_eq ⟨a, _⟩),
  intro r,
  rw ulift.ext_iff at r,
  change quotient.mk' _ = 0 at r,
  have r2 : quotient.mk' (rat.mk (rep ⟨a, _⟩) (order fo)) = quotient.mk' 0,
  { rw r, refl, },
  rw [quotient_add_group.eq', add_zero, rat.neg_def] at r2,
  rcases r2 with ⟨m, hm⟩,
  rw [show (m : ℚ) = rat.mk m 1, from rat.coe_int_eq_mk _, rat.mk_eq,
    mul_one] at hm,
  have eq1 : (m * order fo) • a =
    (- rep ⟨a, _⟩) • a,
  { rw hm, },
  rw [neg_smul, rep_eq ⟨a, submodule.mem_span_singleton_self _⟩, ←subtype.val_eq_coe] at eq1,
  dsimp only at eq1,
  have eq2 : (m * order fo + 1) • a = 0,
  { rw [add_smul, one_smul, eq1, ←sub_eq_neg_add, sub_self], },
  have eq3 : (m * order fo) • a = 0,
  { rw [mul_smul, coe_nat_zsmul, order_smul fo, smul_zero], },
  have eq4 := congr_arg2 has_sub.sub eq2 eq3,
  rw [←sub_smul, add_sub_cancel', one_smul, sub_self] at eq4,
  exact ha eq4,
  linarith,
  exact INEQ,
end

end finite_order

lemma embed_into_injective_injective :
  function.injective (embed_into_divisible A) :=
suffices h : ∀ (a : A) (ha : a ≠ 0), ∃ (f : (AddCommGroup.of A) ⟶ (AddCommGroup.of ℚ⧸ℤ)), (f : A ⟶ ℚ⧸ℤ) a ≠ 0,
begin
  contrapose! h,
  simp only [function.injective, not_forall] at h,
  rcases h with ⟨a, b, h, ineq1⟩,
  refine ⟨a-b, _, _⟩,
  { intro r,
    rw sub_eq_zero at r,
    exact ineq1 r, },
  { intros f,
    have eq2 : f a = f b,
    { unfold embed_into_divisible at h,
      simp only [id.def, add_monoid_hom.coe_mk] at h,
      convert congr_fun h f, },
    rwa [map_sub, sub_eq_zero], },
end,
λ a ha,
suffices ∃ (f : (⟨submodule.span ℤ {a}⟩ : Module ℤ) ⟶ ⟨ℚ⧸ℤ⟩), f ⟨a, submodule.subset_span (set.mem_singleton _)⟩ ≠ 0,
begin
  rcases this with ⟨f, eq1⟩,
  haveI injQZ : category_theory.injective (⟨ℚ⧸ℤ⟩ : Module ℤ),
  { apply injective_as_module_of_injective_as_Ab, },
  replace injQZ := injQZ.factors,
  replace injQZ := @injQZ ⟨submodule.span ℤ {a}⟩ ⟨A⟩ f
  { to_fun := λ x, x.1,
    map_add' := λ x y, rfl,
    map_smul' := λ x y, rfl } begin
    rw Module.mono_iff_injective,
    intros x y eq1,
    rw subtype.ext_iff_val,
    exact eq1,
  end,
  rcases injQZ with ⟨h, eq2⟩,
  refine ⟨h.to_add_monoid_hom, _⟩,
  replace eq2 := fun_like.congr_fun eq2 ⟨a, submodule.mem_span_singleton_self _⟩,
  erw ←eq2 at eq1,
  convert eq1,
end,
begin
  by_cases finite_order_or_not :
    ∀ (n : ℕ), n ≠ 0 → n • a ≠ 0,
  { rename finite_order_or_not io,
    exact ⟨infinite_order.to_quotient io, infinite_order.to_quotient.apply_ne_zero io⟩ },
  { rename finite_order_or_not fo,
    simp only [ne.def, not_forall, not_not, exists_prop] at fo,
    exact ⟨finite_order.to_quotient fo, finite_order.to_quotient.apply_ne_zero fo ha⟩, }
end

def has_injective_presentation : category_theory.injective_presentation (AddCommGroup.of.{u} A) :=
{ J := Div,
  injective := AddCommGroup.injective_of_divisible _,
  f := embed_into_divisible A,
  mono := (AddCommGroup.mono_iff_injective _).mpr $ embed_into_injective_injective _ }

end divisible_emb


instance : category_theory.enough_injectives (AddCommGroup.{u}) :=
{ presentation := λ ⟨A, α⟩, nonempty.intro $
    by { resetI, exact divisible_emb.has_injective_presentation A } }


end AddCommGroup
