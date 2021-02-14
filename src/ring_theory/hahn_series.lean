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
  * If `α` is linearly ordered and `R` has zero, then `hahn_series α R` consists of
  formal series over `α` with coefficients in `R`, whose supports are well-founded.
  * If `R` is a (commutative) additive monoid or group, then so is `hahn_series α R`.
  * If `R` is a `semiring`, then `hahn_series α R` has multiplication.begin

## TODO
  * Given `[semiring R]`, provide the proofs for `semiring [hahn_series α R]`

-/

open_locale big_operators

@[ext]
structure hahn_series (α : Type*) (R : Type*) [linear_order α] [has_zero R] :=
(coeff : α → R)
(is_wf_support : {a | coeff a ≠ 0}.is_wf)

variables {α : Type*} {R : Type*}

namespace hahn_series

section zero
variables [linear_order α] [has_zero R]

instance : has_zero (hahn_series α R) :=
⟨{ coeff := 0,
   is_wf_support := by simp }⟩

instance : inhabited (hahn_series α R) := ⟨0⟩

@[simp]
lemma zero_coeff {a : α} : (0 : hahn_series α R).coeff a = 0 := rfl

end zero
section addition

variable [linear_order α]

instance [add_monoid R] : has_add (hahn_series α R) :=
{ add := λ x y, { coeff := λ a, x.coeff a + y.coeff a,
                  is_wf_support := (x.is_wf_support.union y.is_wf_support).mono (λ a ha, begin
                    contrapose! ha,
                    simp only [not_or_distrib, not_not, set.mem_union_eq, set.mem_set_of_eq] at ha,
                    simp only [not_not, set.mem_set_of_eq],
                    rw [ha.1, ha.2, add_zero],
                  end) } }

instance [add_monoid R] : add_monoid (hahn_series α R) :=
{ add_assoc := λ x y z, by { ext, apply add_assoc },
  zero_add := λ x, by { ext, apply zero_add },
  add_zero := λ x, by { ext, apply add_zero },
  .. hahn_series.has_add,
  .. hahn_series.has_zero }

@[simp]
lemma add_coeff [add_monoid R] {x y : hahn_series α R} {a : α} :
  (x + y).coeff a = x.coeff a + y.coeff a := rfl

instance [add_comm_monoid R] : add_comm_monoid (hahn_series α R) :=
{ add_comm := λ x y, by { ext, apply add_comm }
  .. hahn_series.add_monoid }

instance [add_group R] : add_group (hahn_series α R) :=
{ neg := λ x, { coeff := λ a, - x.coeff a,
                is_wf_support := by { convert x.is_wf_support,
                  ext a,
                  simp }, },
  add_left_neg := λ x, by { ext, apply add_left_neg },
  .. hahn_series.add_monoid }

@[simp]
lemma neg_coeff [add_group R] {x : hahn_series α R} {a : α} : (- x).coeff a = - x.coeff a := rfl

instance [add_comm_group R] : add_comm_group (hahn_series α R) :=
{ .. hahn_series.add_comm_monoid,
  .. hahn_series.add_group }

end addition
section multiplication

variable [linear_ordered_cancel_add_comm_monoid α]

instance [has_zero R] [has_one R] : has_one (hahn_series α R) :=
⟨{ coeff := λ a, if a = 0 then (1 : R) else (0 : R),
           is_wf_support := (set.is_wf_singleton (0 : α)).mono (by simp) }⟩

noncomputable instance [semiring R] : has_mul (hahn_series α R) :=
{ mul := λ x y, { coeff := λ a,
    ∑ ij in (finset.add_antidiagonal x.is_wf_support y.is_wf_support a),
    x.coeff ij.fst * y.coeff ij.snd,
    is_wf_support := begin
      have h : {a : α | ∑ (ij : α × α) in finset.add_antidiagonal x.is_wf_support
        y.is_wf_support a, x.coeff ij.fst * y.coeff ij.snd ≠ 0} ⊆
        {a : α | (finset.add_antidiagonal x.is_wf_support y.is_wf_support a).nonempty},
      { intros a ha,
        contrapose! ha,
        simp [finset.not_nonempty_iff_eq_empty.1 ha] },
      exact finset.is_wf_support_add_antidiagonal.mono h,
    end, }, }

@[simp]
lemma mul_coeff [semiring R] {x y : hahn_series α R} {a : α} :
  (x * y).coeff a = ∑ ij in (finset.add_antidiagonal x.is_wf_support y.is_wf_support a),
    x.coeff ij.fst * y.coeff ij.snd := rfl

lemma mul_coeff_right' [semiring R] {x y : hahn_series α R} {a : α} {s : set α} (hs : s.is_wf)
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

lemma mul_coeff_left' [semiring R] {x y : hahn_series α R} {a : α} {s : set α} (hs : s.is_wf)
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

noncomputable instance [comm_semiring R] : distrib (hahn_series α R) :=
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

end multiplication

end hahn_series
