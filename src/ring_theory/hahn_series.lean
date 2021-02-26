/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import order.well_founded_set
import algebra.big_operators

/-!
# Hahn Series

## Main Definitions
  * If `Γ` is linearly ordered and `R` has zero, then `hahn_series Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded.
  * If `R` is a (commutative) additive monoid or group, then so is `hahn_series Γ R`.
  * If `R` is a (comm_)(semi)ring, then so is `hahn_series Γ R`.

## TODO
  * Given `[linear_ordered_add_comm_group Γ]` and `[field R]`, define `field (hahn_series Γ R)`.
  * Build an API for the constant map `C` and the variable `X`
  * Define Laurent series

-/

open_locale big_operators

/-- If `Γ` is linearly ordered and `R` has zero, then `hahn_series Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded. -/
@[ext]
structure hahn_series (Γ : Type*) (R : Type*) [linear_order Γ] [has_zero R] :=
(coeff : Γ → R)
(is_wf_support : {a | coeff a ≠ 0}.is_wf)

variables {Γ : Type*} {R : Type*}

namespace hahn_series

section zero
variables [linear_order Γ] [has_zero R]

instance : has_zero (hahn_series Γ R) :=
⟨{ coeff := 0,
   is_wf_support := by simp }⟩

instance : inhabited (hahn_series Γ R) := ⟨0⟩

@[simp]
lemma zero_coeff {a : Γ} : (0 : hahn_series Γ R).coeff a = 0 := rfl

/-- `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise. -/
def single (a : Γ) (r : R) : hahn_series Γ R := {
  coeff := λ b, if a = b then r else 0,
  is_wf_support := (set.is_wf_singleton a).mono (λ b, begin
    simp only [and_imp, exists_prop, set.mem_singleton_iff, ite_eq_right_iff,
      ne.def, set.mem_set_of_eq, not_forall],
    exact λ h1 _, h1.symm,
  end) }

variables {a b : Γ} {r : R}

theorem single_coeff : (single a r).coeff b = if a = b then r else 0 := rfl

@[simp]
theorem single_coeff_same : (single a r).coeff a = r := if_pos rfl

@[simp]
theorem single_coeff_of_ne (h : a ≠ b) : (single a r).coeff b = 0 := if_neg h

@[simp]
lemma single_support_of_ne (h : r ≠ 0) : {b | (single a r).coeff b ≠ 0} = {a} :=
begin
  ext b,
  simp only [set.mem_singleton_iff, ne.def, set.mem_set_of_eq],
  split,
  { contrapose!,
    exact λ h', single_coeff_of_ne (ne.symm h') },
  { rintro rfl,
    simp [h] }
end

@[simp]
lemma single_eq_zero : (single a (0 : R)) = 0 := by { ext, simp [single_coeff] }

end zero
section addition

variable [linear_order Γ]

instance [add_monoid R] : has_add (hahn_series Γ R) :=
{ add := λ x y, { coeff := x.coeff + y.coeff,
                  is_wf_support := (x.is_wf_support.union y.is_wf_support).mono (λ a ha, begin
                    contrapose! ha,
                    simp only [not_or_distrib, not_not, set.mem_union_eq, set.mem_set_of_eq] at ha,
                    simp only [pi.add_apply, not_not, set.mem_set_of_eq],
                    rw [ha.1, ha.2, add_zero],
                  end) } }

instance [add_monoid R] : add_monoid (hahn_series Γ R) :=
{ zero := 0,
  add := (+),
  add_assoc := λ x y z, by { ext, apply add_assoc },
  zero_add := λ x, by { ext, apply zero_add },
  add_zero := λ x, by { ext, apply add_zero } }

@[simp]
lemma add_coeff [add_monoid R] {x y : hahn_series Γ R} {a : Γ} :
  (x + y).coeff a = x.coeff a + y.coeff a := rfl

instance [add_comm_monoid R] : add_comm_monoid (hahn_series Γ R) :=
{ add_comm := λ x y, by { ext, apply add_comm }
  .. hahn_series.add_monoid }

instance [add_group R] : add_group (hahn_series Γ R) :=
{ neg := λ x, { coeff := λ a, - x.coeff a,
                is_wf_support := by { convert x.is_wf_support,
                  ext a,
                  simp }, },
  add_left_neg := λ x, by { ext, apply add_left_neg },
  .. hahn_series.add_monoid }

@[simp]
lemma neg_coeff [add_group R] {x : hahn_series Γ R} {a : Γ} : (- x).coeff a = - x.coeff a := rfl

instance [add_comm_group R] : add_comm_group (hahn_series Γ R) :=
{ .. hahn_series.add_comm_monoid,
  .. hahn_series.add_group }

end addition
section smul

variables [linear_order Γ] {V : Type*}

section distrib_mul_action
variables [monoid R] [add_monoid V] [distrib_mul_action R V]

instance : has_scalar R (hahn_series Γ V) :=
⟨λ r x, { coeff := λ a, r • x.coeff a,
          is_wf_support := x.is_wf_support.mono (λ a ha con, ha (by { rw [con, smul_zero] })) }⟩

@[simp]
lemma smul_coeff [monoid R] [add_monoid V] [distrib_mul_action R V]
  {r : R} {x : hahn_series Γ V} {a : Γ} : (r • x).coeff a = r • (x.coeff a) := rfl

instance : distrib_mul_action R (hahn_series Γ V) :=
{ smul := (•),
  one_smul := λ _, by { ext, simp },
  smul_zero := λ _, by { ext, simp },
  smul_add := λ _ _ _, by { ext, simp [smul_add] },
  mul_smul := λ _ _ _, by { ext, simp [mul_smul] } }

end distrib_mul_action

variables [semiring R] [add_comm_monoid V] [semimodule R V]

instance : semimodule R (hahn_series Γ V) :=
{ zero_smul := λ _, by { ext, simp },
  add_smul := λ _ _ _, by { ext, simp [add_smul] },
  .. hahn_series.distrib_mul_action }

end smul
section multiplication

variable [linear_ordered_cancel_add_comm_monoid Γ]

instance [has_zero R] [has_one R] : has_one (hahn_series Γ R) :=
⟨single 0 1⟩

@[simp]
lemma one_coeff [has_zero R] [has_one R] {a : Γ} :
  (1 : hahn_series Γ R).coeff a = if 0 = a then 1 else 0 := rfl

@[simp]
lemma single_zero_one [has_zero R] [has_one R] : (single 0 (1 : R)) = 1 := rfl

noncomputable instance [semiring R] : has_mul (hahn_series Γ R) :=
{ mul := λ x y, { coeff := λ a,
    ∑ ij in (finset.add_antidiagonal x.is_wf_support y.is_wf_support a),
    x.coeff ij.fst * y.coeff ij.snd,
    is_wf_support := begin
      have h : {a : Γ | ∑ (ij : Γ × Γ) in finset.add_antidiagonal x.is_wf_support
        y.is_wf_support a, x.coeff ij.fst * y.coeff ij.snd ≠ 0} ⊆
        {a : Γ | (finset.add_antidiagonal x.is_wf_support y.is_wf_support a).nonempty},
      { intros a ha,
        contrapose! ha,
        simp [finset.not_nonempty_iff_eq_empty.1 ha] },
      exact finset.is_wf_support_add_antidiagonal.mono h,
    end, }, }

@[simp]
lemma mul_coeff [semiring R] {x y : hahn_series Γ R} {a : Γ} :
  (x * y).coeff a = ∑ ij in (finset.add_antidiagonal x.is_wf_support y.is_wf_support a),
    x.coeff ij.fst * y.coeff ij.snd := rfl

lemma mul_coeff_right' [semiring R] {x y : hahn_series Γ R} {a : Γ} {s : set Γ} (hs : s.is_wf)
  (hys : {b | y.coeff b ≠ 0} ⊆ s) :
  (x * y).coeff a = ∑ ij in (finset.add_antidiagonal x.is_wf_support hs a),
    x.coeff ij.fst * y.coeff ij.snd :=
begin
  rw mul_coeff,
  apply finset.sum_subset_zero_on_sdiff (finset.add_antidiagonal_mono_right hys) _ (λ _ _, rfl),
  intros b hb,
  simp only [not_and, not_not, finset.mem_sdiff, finset.mem_add_antidiagonal,
      ne.def, set.mem_set_of_eq] at hb,
  rw [(hb.2 hb.1.1 hb.1.2.1), mul_zero]
end

lemma mul_coeff_left' [semiring R] {x y : hahn_series Γ R} {a : Γ} {s : set Γ} (hs : s.is_wf)
  (hxs : {b | x.coeff b ≠ 0} ⊆ s) :
  (x * y).coeff a = ∑ ij in (finset.add_antidiagonal hs y.is_wf_support a),
    x.coeff ij.fst * y.coeff ij.snd :=
begin
  rw mul_coeff,
  apply finset.sum_subset_zero_on_sdiff (finset.add_antidiagonal_mono_left hxs) _ (λ _ _, rfl),
  intros b hb,
  simp only [not_and, not_not, finset.mem_sdiff, finset.mem_add_antidiagonal,
      ne.def, set.mem_set_of_eq] at hb,
  rw [not_not.1 (λ con, hb.1.2.2 (hb.2 hb.1.1 con)), zero_mul],
end

noncomputable instance [semiring R] : distrib (hahn_series Γ R) :=
{ left_distrib := λ x y z, begin
    ext a,
    have hwf := (y.is_wf_support.union z.is_wf_support),
    rw [mul_coeff_right' hwf, add_coeff, mul_coeff_right' hwf (set.subset_union_right _ _),
      mul_coeff_right' hwf (set.subset_union_left _ _)],
    { simp only [add_coeff, mul_add, finset.sum_add_distrib] },
    { intro b,
      simp only [add_coeff, ne.def, set.mem_union_eq, set.mem_set_of_eq],
      contrapose!,
      intro h,
      rw [h.1, h.2, add_zero], }
  end,
  right_distrib := λ x y z, begin
    ext a,
    have hwf := (x.is_wf_support.union y.is_wf_support),
    rw [mul_coeff_left' hwf, add_coeff, mul_coeff_left' hwf (set.subset_union_right _ _),
      mul_coeff_left' hwf (set.subset_union_left _ _)],
    { simp only [add_coeff, add_mul, finset.sum_add_distrib] },
    { intro b,
      simp only [add_coeff, ne.def, set.mem_union_eq, set.mem_set_of_eq],
      contrapose!,
      intro h,
      rw [h.1, h.2, add_zero], },
  end,
  .. hahn_series.has_mul,
  .. hahn_series.has_add }

@[simp]
lemma single_zero_mul_eq_smul [semiring R] {r : R} {x : hahn_series Γ R} :
  (single 0 r) * x = r • x :=
begin
  ext a,
  by_cases hr : r = 0,
  { simp [hr] },
  simp only [hr, smul_coeff, mul_coeff, single_support_of_ne, ne.def, not_false_iff, smul_eq_mul],
  by_cases hx : x.coeff a = 0,
  { simp only [hx, mul_zero],
    rw [finset.sum_congr _ (λ _ _, rfl), finset.sum_empty],
    ext ⟨a1, a2⟩,
    simp only [finset.not_mem_empty, not_and, set.mem_singleton_iff, not_not,
      finset.mem_add_antidiagonal, set.mem_set_of_eq, iff_false],
    rintro rfl rfl,
    rw [← hx, zero_add] },
  transitivity ∑ (ij : Γ × Γ) in {((0 : Γ),a)}, (single 0 r).coeff ij.fst * x.coeff ij.snd,
  { apply finset.sum_congr _ (λ _ _, rfl),
    ext ⟨a1, a2⟩,
    simp only [set.mem_singleton_iff, prod.mk.inj_iff, finset.mem_add_antidiagonal,
      finset.mem_singleton, set.mem_set_of_eq],
    split,
    { rintro ⟨rfl, rfl, h2⟩,
      refine ⟨rfl, (zero_add _).symm⟩ },
    { rintro ⟨rfl, rfl⟩,
      simp [hx] } },
  { simp }
end

lemma mul_single_zero_coeff [semiring R] {r : R} {x : hahn_series Γ R} {a : Γ} :
  (x * (single 0 r)).coeff a = x.coeff a * r :=
begin
  by_cases hr : r = 0,
  { simp [hr] },
  simp only [hr, smul_coeff, mul_coeff, single_support_of_ne, ne.def, not_false_iff, smul_eq_mul],
  by_cases hx : x.coeff a = 0,
  { simp only [hx, zero_mul],
    rw [finset.sum_congr _ (λ _ _, rfl), finset.sum_empty],
    ext ⟨a1, a2⟩,
    simp only [finset.not_mem_empty, not_and, set.mem_singleton_iff, not_not,
      finset.mem_add_antidiagonal, set.mem_set_of_eq, iff_false],
    rintro rfl h rfl,
    rw add_zero at hx,
    exact h hx, },
  transitivity ∑ (ij : Γ × Γ) in {(a,(0 : Γ))}, x.coeff ij.fst * (single 0 r).coeff ij.snd,
  { apply finset.sum_congr _ (λ _ _, rfl),
    ext ⟨a1, a2⟩,
    simp only [set.mem_singleton_iff, prod.mk.inj_iff, finset.mem_add_antidiagonal,
      finset.mem_singleton, set.mem_set_of_eq],
    split,
    { rintro ⟨rfl, h, rfl⟩,
      refine ⟨(add_zero _).symm, rfl⟩ },
    { rintro ⟨rfl, rfl⟩,
      simp [hx] } },
  { simp }
end

theorem support_mul_subset_mul_support [semiring R] {x y : hahn_series Γ R} :
  {b : Γ | (x * y).coeff b ≠ 0} ⊆ {a : Γ | x.coeff a ≠ 0} + {a : Γ | y.coeff a ≠ 0} :=
begin
  apply set.subset.trans (λ x hx, _) finset.support_add_antidiagonal_subset_add,
  { exact x.is_wf_support },
  { exact y.is_wf_support },
  contrapose! hx,
  simp only [finset.not_nonempty_iff_eq_empty, ne.def, set.mem_set_of_eq] at hx,
  simp [hx],
end

private lemma mul_assoc' [semiring R] (x y z : hahn_series Γ R) :
  x * y * z = x * (y * z) :=
begin
  ext b,
  rw [mul_coeff_left' (x.is_wf_support.add y.is_wf_support) support_mul_subset_mul_support,
      mul_coeff_right' (y.is_wf_support.add z.is_wf_support) support_mul_subset_mul_support],
  simp only [mul_coeff, add_coeff, finset.sum_mul, finset.mul_sum, finset.sum_sigma'],
  refine finset.sum_bij_ne_zero (λ a has ha0, ⟨⟨a.2.1, a.2.2 + a.1.2⟩, ⟨a.2.2, a.1.2⟩⟩) _ _ _ _,
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H1 H2,
    simp only [true_and, set.image2_add, eq_self_iff_true, finset.mem_add_antidiagonal, ne.def,
      set.image_prod, finset.mem_sigma, set.mem_set_of_eq] at H1 H2 ⊢,
    obtain ⟨⟨rfl, ⟨H3, nz⟩⟩, ⟨rfl, nx, ny⟩⟩ := H1,
    refine ⟨⟨(add_assoc _ _ _).symm, nx, set.add_mem_add ny nz⟩, ny, nz⟩ },
  { rintros ⟨⟨i1,j1⟩, ⟨k1,l1⟩⟩ ⟨⟨i2,j2⟩, ⟨k2,l2⟩⟩ H1 H2 H3 H4 H5,
    simp only [set.image2_add, prod.mk.inj_iff, finset.mem_add_antidiagonal, ne.def,
      set.image_prod, finset.mem_sigma, set.mem_set_of_eq, heq_iff_eq] at H1 H3 H5,
    obtain ⟨⟨rfl, H⟩, rfl, rfl⟩ := H5,
    simp only [and_true, prod.mk.inj_iff, eq_self_iff_true, heq_iff_eq],
    exact add_right_cancel (H1.1.1.trans H3.1.1.symm) },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H1 H2,
    simp only [exists_prop, set.image2_add, prod.mk.inj_iff, finset.mem_add_antidiagonal,
      sigma.exists, ne.def, set.image_prod, finset.mem_sigma, set.mem_set_of_eq, heq_iff_eq,
      prod.exists] at H1 H2 ⊢,
    obtain ⟨⟨rfl, nx, H⟩, rfl, ny, nz⟩ := H1,
    exact ⟨i + k, l, i, k, ⟨⟨add_assoc _ _ _, set.add_mem_add nx ny, nz⟩, rfl, nx, ny⟩,
      λ con, H2 ((mul_assoc _ _ _).symm.trans con), ⟨rfl, rfl⟩, rfl, rfl⟩ },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H1 H2,
    simp [mul_assoc], }
end

noncomputable instance [semiring R] : semiring (hahn_series Γ R) :=
{ zero := 0,
  one := 1,
  add := (+),
  mul := (*),
  zero_mul := λ _, by { ext, simp },
  mul_zero := λ _, by { ext, simp },
  one_mul := λ x, single_zero_mul_eq_smul.trans (one_smul _ _),
  mul_one := λ x, by { ext, exact mul_single_zero_coeff.trans (mul_one _) },
  mul_assoc := mul_assoc',
  .. hahn_series.add_comm_monoid,
  .. hahn_series.distrib }

noncomputable instance [comm_semiring R] : comm_semiring (hahn_series Γ R) :=
{ mul_comm := λ x y, begin
    ext,
    simp_rw [mul_coeff, mul_comm],
    refine finset.sum_bij (λ a ha, ⟨a.2, a.1⟩) _ (λ a ha, by simp) _ _,
    { intros a ha,
      simp only [finset.mem_add_antidiagonal, ne.def, set.mem_set_of_eq] at ha ⊢,
      obtain ⟨h1, h2, h3⟩ := ha,
      refine ⟨_, h3, h2⟩,
      rw [add_comm, h1], },
    { rintros ⟨a1, a2⟩ ⟨b1, b2⟩ ha hb hab,
      rw prod.ext_iff at *,
      refine ⟨hab.2, hab.1⟩, },
    { intros a ha,
      refine ⟨a.swap, _, by simp⟩,
      simp only [prod.fst_swap, finset.mem_add_antidiagonal, prod.snd_swap,
        ne.def, set.mem_set_of_eq] at ha ⊢,
      exact ⟨(add_comm _ _).trans ha.1, ha.2.2, ha.2.1⟩ }
  end,
  .. hahn_series.semiring }

noncomputable instance [ring R] : ring (hahn_series Γ R) :=
{ .. hahn_series.semiring,
  .. hahn_series.add_comm_group }

noncomputable instance [comm_ring R] : comm_ring (hahn_series Γ R) :=
{ .. hahn_series.comm_semiring,
  .. hahn_series.ring }

end multiplication

end hahn_series
