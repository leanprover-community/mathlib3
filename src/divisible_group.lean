import algebra.category.Group
import algebra.category.Module.epi_mono
import ring_theory.principal_ideal_domain
import category_theory.preadditive.injective
import algebra.module.injective
import group_theory.subgroup.pointwise
import group_theory.quotient_group
import linear_algebra.basis
import additional_lemma1
import additional_lemma2

namespace add_comm_group

open quotient_group

open_locale pointwise

universe u

variables (A : Type u) [add_comm_group A]

class divisible : Prop :=
(div : ∀ (n : ℤ), n ≠ 0 → n • (⊤ : add_subgroup A) = ⊤)

instance : divisible ℚ :=
{ div := λ n hn, add_subgroup.ext $ λ q,
  { mp := λ _, trivial,
    mpr := λ _, ⟨q/n, trivial, by norm_num; rw [div_eq_mul_inv, mul_comm q, ←mul_assoc, mul_inv_cancel (by norm_cast; exact hn : (n : ℚ) ≠ 0), one_mul]⟩ } }

section product

variables {ι : Type*} (B : ι → Type*) [Π i, add_comm_group (B i)] [Π i, divisible (B i)]

lemma divisible_of_product_divisible : divisible (Π i, B i) :=
{ div := λ n hn, set_like.ext $ λ x,
  { mp := λ _, trivial,
    mpr := λ _, begin
      suffices : ∀ i, ∃ a, x i = n • a,
      { choose rep h_rep using this,
        refine ⟨rep, trivial, _⟩,
        ext i,
        rw h_rep,
        refl, },
      { intros i,
        have mem1 : x i ∈ n • ⊤,
        { rw divisible.div n hn,
          exact add_subgroup.mem_top _,
          apply_instance, },
        rcases mem1 with ⟨a, -, eq1⟩,
        exact ⟨a, eq1 ▸ rfl⟩, },
    end } }

end product

lemma injective_of_injective_as_module (h : category_theory.injective (⟨A⟩ : Module ℤ)) :
  category_theory.injective (AddCommGroup.of A) :=
{ factors := λ X Y g f m, begin
    have factors := h.factors,
    replace factors := @factors ⟨X⟩ ⟨Y⟩ _ _ _,
    work_on_goal 2
    { refine { to_fun := g, map_add' := _, map_smul' := _ },
      { intros x y, rw map_add },
      { intros z x,
        rw [ring_hom.id_apply],
        induction z using int.induction_on with n hn n hn,
        { rw [zero_smul, map_zero, zero_smul] },
        { rw [add_smul, one_smul, map_add, hn, add_smul, one_smul] },
        { rw [sub_smul, one_smul, map_sub, hn, sub_smul, one_smul] }, }, },
    work_on_goal 2
    { refine { to_fun := f, map_add' := _, map_smul' := _ },
      { intros x y, rw map_add },
      { intros z x,
        rw [ring_hom.id_apply],
        induction z using int.induction_on with n hn n hn,
        { rw [zero_smul, map_zero, zero_smul] },
        { rw [add_smul, one_smul, map_add, hn, add_smul, one_smul] },
        { rw [sub_smul, one_smul, map_sub, hn, sub_smul, one_smul] } } },
    work_on_goal 2
    { split,
      intros Z α β eq1,
      set α' : AddCommGroup.of Z ⟶ X := α.to_add_monoid_hom with α'_eq,
      set β' : AddCommGroup.of Z ⟶ X := β.to_add_monoid_hom with β'_eq,
      have eq2 : α' ≫ f = β' ≫ f,
      { ext,
        simp only [category_theory.comp_apply, linear_map.to_add_monoid_hom_coe, α'_eq, β'_eq],
        have := fun_like.congr_fun eq1 x,
        simpa only [Module.coe_comp, linear_map.coe_mk, function.comp_app] using this },
      resetI,
      rw category_theory.cancel_mono at eq2,
      ext,
      { have := fun_like.congr_fun eq2 x,
        simpa only using this }, },
    rcases factors with ⟨h, eq1⟩,
    refine ⟨h.to_add_monoid_hom, _⟩,
    ext,
    replace eq1 := fun_like.congr_fun eq1 x,
    simpa only using eq1,
  end }

lemma injective_as_module_of_injective_as_Ab (h : category_theory.injective (AddCommGroup.of A)) :
  category_theory.injective (⟨A⟩ : Module ℤ) :=
{ factors := λ X Y g f m, begin
    replace h := h.factors,
    replace h := @h ⟨X⟩ ⟨Y⟩ g.to_add_monoid_hom f.to_add_monoid_hom begin
      rw AddCommGroup.mono_iff_injective,
      rw Module.mono_iff_injective at m,
      intros x y eq1,
      change f x = f y at eq1,
      exact m eq1,
    end,
    rcases h with ⟨h, eq1⟩,
    refine ⟨{ to_fun := h, map_add' := λ x y, by rw [map_add], map_smul' := _ }, _⟩,
    { intros m x,
      rw [ring_hom.id_apply],
      induction m using int.induction_on with n hn n hn,
      { rw [zero_smul],
        convert map_zero _,
        convert zero_smul _ x, },
      { simp only [add_smul, map_add, hn, one_smul], },
      { simp only [sub_smul, map_sub, hn, one_smul] }, },
    { ext,
      replace eq1 := fun_like.congr_fun eq1 x,
      convert eq1, },
  end }

lemma injective_of_divisible (d : divisible A) :
  category_theory.injective (AddCommGroup.of A) :=
injective_of_injective_as_module _ $
@@module.injective_object_of_injective_module ℤ _ A _ _ $
module.Baer.injective $ λ I g, begin
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
  { have d : m • (⊤ : add_subgroup A) = _ := divisible.div m m_eq_zero,
    replace d : ∀ (a : A), ∃ (a' : A), a = m • a',
    { intros a,
      have mem1 : a ∈ m • ⊤,
      { rw d, trivial },
      { rcases mem1 with ⟨a', -, eq1⟩,
        refine ⟨a', _⟩,
        rw [←eq1],
        refl, }, },
    choose rep h_rep using d,
    set gₘ := g ⟨m, submodule.subset_span (set.mem_singleton _)⟩ with gm_eq,
    refine ⟨{ to_fun := _, map_add' := _, map_smul' := _ }, λ n hn, _⟩,
    { intros n,
      exact n • rep gₘ, },
    { intros n1 n2, simp only [add_smul], },
    { intros n1 n2,
      rw [ring_hom.id_apply, smul_eq_mul, mul_smul], },
    { rw submodule.mem_span_singleton at hn,
      rcases hn with ⟨n, rfl⟩,
      simp only [gm_eq, algebra.id.smul_eq_mul, linear_map.coe_mk],
      rw [mul_smul, ←h_rep (g ⟨m, _⟩), ←linear_map.map_smul],
      congr, }, },
end

def ℤ_as_ℚ_subgroup : add_subgroup ℚ :=
{ carrier := set.range (coe : ℤ → ℚ),
  add_mem' := begin
    rintros _ _ ⟨a, rfl⟩ ⟨b, rfl⟩,
    refine ⟨a + b, _⟩,
    norm_cast,
  end,
  zero_mem' := ⟨0, rfl⟩,
  neg_mem' := begin
    rintros _ ⟨a, rfl⟩,
    refine ⟨-a, _⟩,
    norm_cast,
  end }

instance divisible_ℚ_quotient_ℤ : divisible (ℚ ⧸ ℤ_as_ℚ_subgroup) :=
{ div := λ n hn, set_like.ext $ λ x,
  { mp := λ _, trivial,
    mpr := λ _, begin
      induction x using quotient.induction_on',
      refine ⟨quotient.mk' (x/n), trivial, _⟩,
      simp only [distrib_mul_action.to_add_monoid_End_apply, distrib_mul_action.to_add_monoid_hom_apply],
      change quotient.mk' (n • _) = _,
      congr,
      rw [div_eq_mul_inv, mul_comm],
      norm_num,
      rw [←mul_assoc, mul_inv_cancel, one_mul],
      norm_cast,
      exact hn,
    end } }

instance [divisible A] : divisible (ulift A) :=
{ div := λ n hn, set_like.ext $ λ x,
  { mp := λ _, trivial,
    mpr := λ _, begin
      rcases x with ⟨a⟩,
      have mem1 : a ∈ n • ⊤,
      { rw divisible.div n hn,
        exact add_subgroup.mem_top _,
        apply_instance },
      rcases mem1 with ⟨a, -, rfl⟩,
      refine ⟨⟨a⟩, trivial, _⟩,
      simp only [distrib_mul_action.to_add_monoid_End_apply, distrib_mul_action.to_add_monoid_hom_apply],
      refl,
    end } }

local notation `ℚ⧸ℤ` := (ulift.{u} (ℚ ⧸ ℤ_as_ℚ_subgroup))
local notation `I` := AddCommGroup.of A ⟶ AddCommGroup.of (ℚ⧸ℤ)

@[reducible] def dummy_function : I → Type u := λ i, ℚ⧸ℤ
instance : add_comm_group (Π (i : I), ℚ⧸ℤ) := @pi.add_comm_group I (dummy_function A) (λ _ , infer_instance)

local notation `D` := AddCommGroup.of (Π (i : I), ℚ⧸ℤ)

instance : category_theory.injective (⟨ℚ⧸ℤ⟩ : Module ℤ) :=
injective_as_module_of_injective_as_Ab _ $ injective_of_divisible _ infer_instance

lemma ℚ_quotient_ℤ.Baer : module.Baer ℤ ℚ⧸ℤ :=
criterion' $ (module.injective_iff_injective_object _ _).mpr infer_instance

@[simps]
def embed_into_injective : AddCommGroup.of A ⟶ D :=
{ to_fun := λ a, begin
    intros i,
    exact i a,
  end,
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
  function.injective (embed_into_injective A) :=
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
    { unfold embed_into_injective at h,
      simp only [id.def, add_monoid_hom.coe_mk] at h,
      convert congr_fun h f, },
    rwa [map_sub, sub_eq_zero], },
end,
λ a ha,
suffices ∃ (f : (⟨submodule.span ℤ {a}⟩ : Module ℤ) ⟶ ⟨ℚ⧸ℤ⟩), f ⟨a, submodule.subset_span (set.mem_singleton _)⟩ ≠ 0,
begin
  rcases this with ⟨f, eq1⟩,
  haveI injQZ : category_theory.injective (⟨ℚ⧸ℤ⟩ : Module ℤ) := infer_instance,
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
{ J := D,
  injective := injective_of_divisible _ (by apply divisible_of_product_divisible),
  f := embed_into_injective A,
  mono := (AddCommGroup.mono_iff_injective _).mpr $ embed_into_injective_injective _ }

instance : category_theory.enough_injectives (Ab.{u}) :=
{ presentation := λ A, nonempty.intro $ begin
    rcases A with ⟨A, α⟩,
    resetI,
    convert has_injective_presentation A,
  end }

end add_comm_group
