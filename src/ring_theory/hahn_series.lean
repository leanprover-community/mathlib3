/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import order.well_founded_set
import algebra.big_operators

/-!
# Hahn Series


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

instance [add_monoid R] : add_monoid (hahn_series α R) :=
{ add := λ x y, { coeff := λ a, x.coeff a + y.coeff a,
                  is_wf_support := (x.is_wf_support.union y.is_wf_support).mono (λ a ha, begin
                    contrapose! ha,
                    simp only [not_or_distrib, not_not, set.mem_union_eq, set.mem_set_of_eq] at ha,
                    simp only [not_not, set.mem_set_of_eq],
                    rw [ha.1, ha.2, add_zero],
                  end) },
  add_assoc := λ x y z, by { ext, apply add_assoc },
  zero_add := λ x, by { ext, apply zero_add },
  add_zero := λ x, by { ext, apply add_zero },
 .. hahn_series.has_zero }

@[simp]
lemma add_apply [add_monoid R] {x y : hahn_series α R} {a : α} :
  (x + y).coeff a = x.coeff a + y.coeff a := rfl

instance [add_comm_monoid R] : add_comm_monoid (hahn_series α R) :=
{ add_comm := λ x y, by { ext, apply add_comm }
  .. hahn_series.add_monoid }

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
lemma mul_apply [semiring R] {x y : hahn_series α R} {a : α} :
  (x * y).coeff a = ∑ ij in (finset.add_antidiagonal x.is_wf_support y.is_wf_support a),
    x.coeff ij.fst * y.coeff ij.snd := rfl

end multiplication

end hahn_series
