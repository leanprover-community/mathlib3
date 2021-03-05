/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import order.well_founded_set
import algebra.big_operators
import algebra.module.pi
import ring_theory.power_series.basic

/-!
# Hahn Series

## Main Definitions
  * If `Γ` is linearly ordered and `R` has zero, then `hahn_series Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded.
  * If `R` is a (commutative) additive monoid or group, then so is `hahn_series Γ R`.
  * If `R` is a (comm_)(semi)ring, then so is `hahn_series Γ R`.

## TODO
  * Given `[linear_ordered_add_comm_group Γ]` and `[field R]`, define `field (hahn_series Γ R)`.
  * Build an API for the variable `X`
  * Define Laurent series

-/

open_locale big_operators classical
noncomputable theory

/-- If `Γ` is linearly ordered and `R` has zero, then `hahn_series Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded. -/
@[ext]
structure hahn_series (Γ : Type*) (R : Type*) [linear_order Γ] [has_zero R] :=
(coeff : Γ → R)
(is_wf_support' : (function.support coeff).is_wf)

variables {Γ : Type*} {R : Type*}

namespace hahn_series

section zero
variables [linear_order Γ] [has_zero R]

/-- The support of a Hahn series is just the set of indices whose coefficients are nonzero.
  Notably, it is well-founded. -/
def support (x : hahn_series Γ R) : set Γ := function.support x.coeff

@[simp]
lemma is_wf_support (x : hahn_series Γ R) : x.support.is_wf := x.is_wf_support'

@[simp]
lemma mem_support (x : hahn_series Γ R) (a : Γ) : a ∈ x.support ↔ x.coeff a ≠ 0 := iff.refl _

instance : has_zero (hahn_series Γ R) :=
⟨{ coeff := 0,
   is_wf_support' := by simp }⟩

instance : inhabited (hahn_series Γ R) := ⟨0⟩

@[simp]
lemma zero_coeff {a : Γ} : (0 : hahn_series Γ R).coeff a = 0 := rfl

@[simp]
lemma support_zero : support (0 : hahn_series Γ R) = ∅ := function.support_zero

/-- `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise. -/
def single (a : Γ) (r : R) : hahn_series Γ R := {
  coeff := pi.single a r,
  is_wf_support' := (set.is_wf_singleton a).mono pi.support_single_subset }

variables {a b : Γ} {r : R}

@[simp]
theorem single_coeff_same : (single a r).coeff a = r := pi.single_eq_same a r

@[simp]
theorem single_coeff_of_ne (h : b ≠ a) : (single a r).coeff b = 0 := pi.single_eq_of_ne h r

theorem single_coeff : (single a r).coeff b = if (b = a) then r else 0 :=
by { split_ifs with h; simp [h] }

@[simp]
lemma support_single_of_ne (h : r ≠ 0) : support (single a r) = {a} :=
pi.support_single_of_ne h

lemma support_single_subset : support (single a r) ⊆ {a} :=
pi.support_single_subset

lemma eq_of_mem_support_single {b : Γ} (h : b ∈ support (single a r)) : b = a :=
support_single_subset h

@[simp]
lemma single_eq_zero : (single a (0 : R)) = 0 := ext _ _ (pi.single_zero _)

end zero

section addition

variable [linear_order Γ]

instance [add_monoid R] : has_add (hahn_series Γ R) :=
{ add := λ x y, { coeff := x.coeff + y.coeff,
                  is_wf_support' := (x.is_wf_support.union y.is_wf_support).mono
                    (function.support_add _ _) } }

instance [add_monoid R] : add_monoid (hahn_series Γ R) :=
{ zero := 0,
  add := (+),
  add_assoc := λ x y z, by { ext, apply add_assoc },
  zero_add := λ x, by { ext, apply zero_add },
  add_zero := λ x, by { ext, apply add_zero } }

@[simp]
lemma add_coeff' [add_monoid R] {x y : hahn_series Γ R} :
  (x + y).coeff = x.coeff + y.coeff := rfl

lemma add_coeff [add_monoid R] {x y : hahn_series Γ R} {a : Γ} :
  (x + y).coeff a = x.coeff a + y.coeff a := rfl

instance [add_comm_monoid R] : add_comm_monoid (hahn_series Γ R) :=
{ add_comm := λ x y, by { ext, apply add_comm }
  .. hahn_series.add_monoid }

instance [add_group R] : add_group (hahn_series Γ R) :=
{ neg := λ x, { coeff := λ a, - x.coeff a,
                is_wf_support' := by { rw function.support_neg,
                  exact x.is_wf_support }, },
  add_left_neg := λ x, by { ext, apply add_left_neg },
  .. hahn_series.add_monoid }

@[simp]
lemma neg_coeff' [add_group R] {x : hahn_series Γ R} : (- x).coeff = - x.coeff := rfl

lemma neg_coeff [add_group R] {x : hahn_series Γ R} {a : Γ} : (- x).coeff a = - x.coeff a := rfl

@[simp]
lemma sub_coeff' [add_group R] {x y : hahn_series Γ R} :
  (x - y).coeff = x.coeff - y.coeff := by { ext, simp [sub_eq_add_neg] }

lemma sub_coeff [add_group R] {x y : hahn_series Γ R} {a : Γ} :
  (x - y).coeff a = x.coeff a - y.coeff a := by simp

instance [add_comm_group R] : add_comm_group (hahn_series Γ R) :=
{ .. hahn_series.add_comm_monoid,
  .. hahn_series.add_group }

end addition

section distrib_mul_action
variables [linear_order Γ] {V : Type*} [monoid R] [add_monoid V] [distrib_mul_action R V]

instance : has_scalar R (hahn_series Γ V) :=
⟨λ r x, { coeff := r • x.coeff,
          is_wf_support' := x.is_wf_support.mono (function.support_smul_subset r x.coeff) }⟩

@[simp]
lemma smul_coeff {r : R} {x : hahn_series Γ V} {a : Γ} : (r • x).coeff a = r • (x.coeff a) := rfl

instance : distrib_mul_action R (hahn_series Γ V) :=
{ smul := (•),
  one_smul := λ _, by { ext, simp },
  smul_zero := λ _, by { ext, simp },
  smul_add := λ _ _ _, by { ext, simp [smul_add] },
  mul_smul := λ _ _ _, by { ext, simp [mul_smul] } }

end distrib_mul_action

section scalar

variables [linear_order Γ] [semiring R] {V : Type*} [add_comm_monoid V] [semimodule R V]

instance :
  semimodule R (hahn_series Γ V) :=
{ zero_smul := λ _, by { ext, simp },
  add_smul := λ _ _ _, by { ext, simp [add_smul] },
  .. hahn_series.distrib_mul_action }

variables {S : Type*} [semiring S] [semimodule S V]

instance [semimodule R S] [is_scalar_tower R S V] :
  is_scalar_tower R S (hahn_series Γ V) :=
⟨λ r s a, by { ext, simp }⟩

instance [semimodule R V] [smul_comm_class R S V] :
  smul_comm_class R S (hahn_series Γ V) :=
⟨λ r s a, by { ext, simp [smul_comm] }⟩

end scalar

section multiplication

variable [linear_ordered_cancel_add_comm_monoid Γ]

instance [has_zero R] [has_one R] : has_one (hahn_series Γ R) :=
⟨single 0 1⟩

@[simp]
lemma one_coeff [has_zero R] [has_one R] {a : Γ} :
  (1 : hahn_series Γ R).coeff a = if a = 0 then 1 else 0 := single_coeff

@[simp]
lemma single_zero_one [has_zero R] [has_one R] : (single 0 (1 : R)) = 1 := rfl

instance [semiring R] : has_mul (hahn_series Γ R) :=
{ mul := λ x y, { coeff := λ a,
    ∑ ij in (finset.add_antidiagonal x.is_wf_support y.is_wf_support a),
    x.coeff ij.fst * y.coeff ij.snd,
    is_wf_support' := begin
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
  (hys : y.support ⊆ s) :
  (x * y).coeff a = ∑ ij in (finset.add_antidiagonal x.is_wf_support hs a),
    x.coeff ij.fst * y.coeff ij.snd :=
begin
  rw mul_coeff,
  apply finset.sum_subset_zero_on_sdiff (finset.add_antidiagonal_mono_right hys) _ (λ _ _, rfl),
  intros b hb,
  simp only [not_and, not_not, finset.mem_sdiff, finset.mem_add_antidiagonal,
      ne.def, set.mem_set_of_eq, mem_support] at hb,
  rw [(hb.2 hb.1.1 hb.1.2.1), mul_zero]
end

lemma mul_coeff_left' [semiring R] {x y : hahn_series Γ R} {a : Γ} {s : set Γ} (hs : s.is_wf)
  (hxs : x.support ⊆ s) :
  (x * y).coeff a = ∑ ij in (finset.add_antidiagonal hs y.is_wf_support a),
    x.coeff ij.fst * y.coeff ij.snd :=
begin
  rw mul_coeff,
  apply finset.sum_subset_zero_on_sdiff (finset.add_antidiagonal_mono_left hxs) _ (λ _ _, rfl),
  intros b hb,
  simp only [not_and, not_not, finset.mem_sdiff, finset.mem_add_antidiagonal,
      ne.def, set.mem_set_of_eq, mem_support] at hb,
  rw [not_not.1 (λ con, hb.1.2.2 (hb.2 hb.1.1 con)), zero_mul],
end

instance [semiring R] : distrib (hahn_series Γ R) :=
{ left_distrib := λ x y z, begin
    ext a,
    have hwf := (y.is_wf_support.union z.is_wf_support),
    rw [mul_coeff_right' hwf, add_coeff, mul_coeff_right' hwf (set.subset_union_right _ _),
      mul_coeff_right' hwf (set.subset_union_left _ _)],
    { simp only [add_coeff, mul_add, finset.sum_add_distrib] },
    { intro b,
      simp only [add_coeff, ne.def, set.mem_union_eq, set.mem_set_of_eq, mem_support],
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
      simp only [add_coeff, ne.def, set.mem_union_eq, set.mem_set_of_eq, mem_support],
      contrapose!,
      intro h,
      rw [h.1, h.2, add_zero], },
  end,
  .. hahn_series.has_mul,
  .. hahn_series.has_add }

lemma single_mul_coeff_add [semiring R] {r : R} {x : hahn_series Γ R} {a : Γ} {b : Γ} :
  ((single b r) * x).coeff (a + b) = r * x.coeff a :=
begin
  by_cases hr : r = 0,
  { simp [hr] },
  simp only [hr, smul_coeff, mul_coeff, support_single_of_ne, ne.def, not_false_iff, smul_eq_mul],
  by_cases hx : x.coeff a = 0,
  { simp only [hx, mul_zero],
    rw [finset.sum_congr _ (λ _ _, rfl), finset.sum_empty],
    ext ⟨a1, a2⟩,
    simp only [finset.not_mem_empty, not_and, set.mem_singleton_iff, not_not,
      finset.mem_add_antidiagonal, set.mem_set_of_eq, iff_false],
    rintro h1 rfl h2,
    rw add_comm at h1,
    rw ← add_right_cancel h1 at hx,
    exact h2 hx, },
  transitivity ∑ (ij : Γ × Γ) in {(b, a)}, (single b r).coeff ij.fst * x.coeff ij.snd,
  { apply finset.sum_congr _ (λ _ _, rfl),
    ext ⟨a1, a2⟩,
    simp only [set.mem_singleton_iff, prod.mk.inj_iff, finset.mem_add_antidiagonal,
      finset.mem_singleton, set.mem_set_of_eq],
    split,
    { rintro ⟨h1, rfl, h2⟩,
      rw add_comm at h1,
      refine ⟨rfl, add_right_cancel h1⟩ },
    { rintro ⟨rfl, rfl⟩,
      refine ⟨add_comm _ _, _⟩,
      simp [hx] } },
  { simp }
end

lemma mul_single_coeff_add [semiring R] {r : R} {x : hahn_series Γ R} {a : Γ} {b : Γ} :
  (x * (single b r)).coeff (a + b) = x.coeff a * r :=
begin
  by_cases hr : r = 0,
  { simp [hr] },
  simp only [hr, smul_coeff, mul_coeff, support_single_of_ne, ne.def, not_false_iff, smul_eq_mul],
  by_cases hx : x.coeff a = 0,
  { simp only [hx, zero_mul],
    rw [finset.sum_congr _ (λ _ _, rfl), finset.sum_empty],
    ext ⟨a1, a2⟩,
    simp only [finset.not_mem_empty, not_and, set.mem_singleton_iff, not_not,
      finset.mem_add_antidiagonal, set.mem_set_of_eq, iff_false],
    rintro h1 h2 rfl,
    rw ← add_right_cancel h1 at hx,
    exact h2 hx, },
  transitivity ∑ (ij : Γ × Γ) in {(a,b)}, x.coeff ij.fst * (single b r).coeff ij.snd,
  { apply finset.sum_congr _ (λ _ _, rfl),
    ext ⟨a1, a2⟩,
    simp only [set.mem_singleton_iff, prod.mk.inj_iff, finset.mem_add_antidiagonal,
      finset.mem_singleton, set.mem_set_of_eq],
    split,
    { rintro ⟨h1, h2, rfl⟩,
      refine ⟨add_right_cancel h1, rfl⟩ },
    { rintro ⟨rfl, rfl⟩,
      simp [hx] } },
  { simp }
end

@[simp]
lemma mul_single_zero_coeff [semiring R] {r : R} {x : hahn_series Γ R} {a : Γ} :
  (x * (single 0 r)).coeff a = x.coeff a * r  :=
by rw [← add_zero a, mul_single_coeff_add, add_zero]

lemma single_zero_mul_coeff [semiring R] {r : R} {x : hahn_series Γ R} {a : Γ} :
  ((single 0 r) * x).coeff a = r * x.coeff a :=
by rw [← add_zero a, single_mul_coeff_add, add_zero]

@[simp]
lemma single_zero_mul_eq_smul [semiring R] {r : R} {x : hahn_series Γ R} :
  (single 0 r) * x = r • x :=
by { ext, exact single_zero_mul_coeff }

theorem support_mul_subset_add_support [semiring R] {x y : hahn_series Γ R} :
  support (x * y) ⊆ support x + support y :=
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
  rw [mul_coeff_left' (x.is_wf_support.add y.is_wf_support) support_mul_subset_add_support,
      mul_coeff_right' (y.is_wf_support.add z.is_wf_support) support_mul_subset_add_support],
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

instance [semiring R] : semiring (hahn_series Γ R) :=
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

instance [comm_semiring R] : comm_semiring (hahn_series Γ R) :=
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

instance [ring R] : ring (hahn_series Γ R) :=
{ .. hahn_series.semiring,
  .. hahn_series.add_comm_group }

instance [comm_ring R] : comm_ring (hahn_series Γ R) :=
{ .. hahn_series.comm_semiring,
  .. hahn_series.ring }

section semiring
variables [semiring R]

@[simp]
lemma single_mul_single {a b : Γ} {r s : R} :
  single a r * single b s = single (a + b) (r * s) :=
begin
  ext x,
  by_cases h : x = a + b,
  { rw [h, mul_single_coeff_add],
    simp },
  { rw [single_coeff_of_ne h, mul_coeff, finset.sum_eq_zero],
    rintros ⟨y1, y2⟩ hy,
    obtain ⟨rfl, hy1, hy2⟩ := finset.mem_add_antidiagonal.1 hy,
    rw [eq_of_mem_support_single hy1, eq_of_mem_support_single hy2] at h,
    exact (h rfl).elim }
end

/-- -/
def C : R →+* (hahn_series Γ R) :=
{ to_fun := single 0,
  map_zero' := single_eq_zero,
  map_one' := rfl,
  map_add' := λ x y, by { ext a, by_cases h : a = 0; simp [h] },
  map_mul' := λ x y, by rw [single_mul_single, zero_add] }

@[simp]
lemma C_apply (r : R) : C r = single (0 : Γ) r := rfl

@[simp]
lemma C_zero : C (0 : R) = (0 : hahn_series Γ R) := C.map_zero

@[simp]
lemma C_one : C (1 : R) = (1 : hahn_series Γ R) := C.map_one

lemma C_mul_eq_smul {r : R} {x : hahn_series Γ R} : C r * x = r • x :=
single_zero_mul_eq_smul

end semiring

section algebra
variables [comm_semiring R] {A : Type*} [semiring A] [algebra R A]

instance : algebra R (hahn_series Γ A) :=
{ to_ring_hom := C.comp (algebra_map R A),
  smul_def' := λ r x, by { ext, simp },
  commutes' := λ r x, by { ext, simp only [smul_coeff, single_zero_mul_eq_smul, ring_hom.coe_comp,
    ring_hom.to_fun_eq_coe, C_apply, function.comp_app, algebra_map_smul, mul_single_zero_coeff],
    rw [← algebra.commutes, algebra.smul_def], }, }

theorem C_eq_algebra_map : C = (algebra_map R (hahn_series Γ R)) := rfl

theorem algebra_map_apply {r : R} :
  algebra_map R (hahn_series Γ A) r = C (algebra_map R A r) := rfl

end algebra

end multiplication

section semiring
variables [semiring R]

/-- The ring `hahn_series ℕ R` is isomorphic to `power_series R`. -/
def to_power_series : (hahn_series ℕ R) ≃+* power_series R :=
{ to_fun := λ f, power_series.mk f.coeff,
  inv_fun := λ f, ⟨λ n, power_series.coeff R n f, nat.lt_wf.is_wf _⟩,
  left_inv := λ f, by { ext, simp },
  right_inv := λ f, by { ext, simp },
  map_add' := λ f g, by { ext, simp },
  map_mul' := λ f g, begin
    ext n,
    simp only [power_series.coeff_mul, power_series.coeff_mk, mul_coeff, is_wf_support],
    classical,
    refine finset.sum_filter_ne_zero.symm.trans
      ((finset.sum_congr _ (λ _ _, rfl)).trans finset.sum_filter_ne_zero),
    ext m,
    simp only [finset.nat.mem_antidiagonal, and.congr_left_iff, finset.mem_add_antidiagonal, ne.def,
      and_iff_left_iff_imp, finset.mem_filter, mem_support],
    intros h1 h2,
    contrapose h1,
    rw ← decidable.or_iff_not_and_not at h1,
    cases h1; simp [h1]
  end }

@[simp]
lemma coeff_to_power_series {f : hahn_series ℕ R} {n : ℕ} :
  power_series.coeff R n f.to_power_series = f.coeff n :=
power_series.coeff_mk _ _

@[simp]
lemma coeff_to_power_series_symm {f : power_series R} {n : ℕ} :
  (hahn_series.to_power_series.symm f).coeff n = power_series.coeff R n f :=
rfl

end semiring

section algebra
variables (R) [comm_semiring R] {A : Type*} [semiring A] [algebra R A]

/-- The `R`-algebra `hahn_series ℕ A` is isomorphic to `power_series A`. -/
def to_power_series_alg : (hahn_series ℕ A) ≃ₐ[R] power_series A :=
{ commutes' := λ r, begin
    ext n,
    simp only [algebra_map_apply, power_series.algebra_map_apply, ring_equiv.to_fun_eq_coe, C_apply,
      coeff_to_power_series],
    cases n,
    { simp only [power_series.coeff_zero_eq_constant_coeff, single_coeff_same],
      refl },
    { simp only [n.succ_ne_zero, ne.def, not_false_iff, single_coeff_of_ne],
      rw [power_series.coeff_C, if_neg n.succ_ne_zero] }
  end,
  .. to_power_series }

@[simp]
lemma to_power_series_alg_apply {f : hahn_series ℕ A} :
  hahn_series.to_power_series_alg R f = f.to_power_series := rfl

@[simp]
lemma to_power_series_alg_symm_apply {f : power_series A} :
  (hahn_series.to_power_series_alg R).symm f = hahn_series.to_power_series.symm f := rfl

end algebra

end hahn_series
