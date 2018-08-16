/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Nonnegative real numbers.
-/
import data.real.basic order.lattice

noncomputable theory
open lattice

def nnreal := {r : ℝ // 0 ≤ r}
local notation ` ℝ≥0 ` := nnreal

namespace nnreal

instance : has_coe ℝ≥0 ℝ := ⟨subtype.val⟩

protected lemma eq {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) → n = m := subtype.eq
protected lemma eq_iff {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) ↔ n = m :=
iff.intro nnreal.eq (congr_arg coe)

protected def of_real (r : ℝ) : ℝ≥0 := ⟨max r 0, le_max_right _ _⟩

instance : has_zero ℝ≥0  := ⟨⟨0, le_refl 0⟩⟩
instance : has_one ℝ≥0   := ⟨⟨1, zero_le_one⟩⟩
instance : has_add ℝ≥0   := ⟨λa b, ⟨a + b, add_nonneg a.2 b.2⟩⟩
instance : has_sub ℝ≥0   := ⟨λa b, nnreal.of_real (a - b)⟩
instance : has_mul ℝ≥0   := ⟨λa b, ⟨a * b, mul_nonneg a.2 b.2⟩⟩
instance : has_div ℝ≥0   := ⟨λa b, ⟨a.1 / b.1, div_nonneg' a.2 b.2⟩⟩
instance : has_le ℝ≥0    := ⟨λ r s, (r:ℝ) ≤ s⟩
instance : has_bot ℝ≥0   := ⟨0⟩
instance : inhabited ℝ≥0 := ⟨0⟩

@[simp] protected lemma coe_zero : ((0 : ℝ≥0) : ℝ) = 0 := rfl
@[simp] protected lemma coe_one  : ((1 : ℝ≥0) : ℝ) = 1 := rfl
@[simp] protected lemma coe_add (r₁ r₂ : ℝ≥0) : ((r₁ + r₂ : ℝ≥0) : ℝ) = r₁ + r₂ := rfl
@[simp] protected lemma coe_mul (r₁ r₂ : ℝ≥0) : ((r₁ * r₂ : ℝ≥0) : ℝ) = r₁ * r₂ := rfl
@[simp] protected lemma coe_div (r₁ r₂ : ℝ≥0) : ((r₁ / r₂ : ℝ≥0) : ℝ) = r₁ / r₂ := rfl

@[simp] protected lemma coe_sub (r₁ r₂ : ℝ≥0) (h : r₂ ≤ r₁) : ((r₁ - r₂ : ℝ≥0) : ℝ) = r₁ - r₂ :=
max_eq_left $ le_sub.2 $ by simp [show (r₂ : ℝ) ≤ r₁, from h]

-- TODO: setup semifield!
@[simp] protected lemma zero_div (r : nnreal) : 0 / r = 0 :=
nnreal.eq (zero_div _)

@[simp] protected lemma coe_eq_zero (r : nnreal) : ↑r = (0 : ℝ) ↔ r = 0 :=
@nnreal.eq_iff r 0

instance : comm_semiring ℝ≥0 :=
begin
  refine { zero := 0, add := (+), one := 1, mul := (*), ..};
  { intros;
    apply nnreal.eq;
    simp [mul_comm, mul_assoc, add_comm_monoid.add, left_distrib, right_distrib,
          add_comm_monoid.zero] }
end

@[simp] protected lemma coe_nat_cast : ∀(n : ℕ), (↑(↑n : ℝ≥0) : ℝ) = n
| 0       := rfl
| (n + 1) := by simp [coe_nat_cast n]

instance : decidable_linear_order ℝ≥0 :=
{ le               := (≤),
  lt               := λa b, (a : ℝ) < b,
  lt_iff_le_not_le := assume a b, @lt_iff_le_not_le ℝ _ a b,
  le_refl          := assume a, le_refl (a : ℝ),
  le_trans         := assume a b c, @le_trans ℝ _ a b c,
  le_antisymm      := assume a b hab hba, nnreal.eq $ le_antisymm hab hba,
  le_total         := assume a b, le_total (a : ℝ) b,
  decidable_le     := λa b, by apply_instance }

instance : canonically_ordered_monoid ℝ≥0 :=
{ add_le_add_left       := assume a b h c, @add_le_add_left ℝ _ a b h c,
  lt_of_add_lt_add_left := assume a b c, @lt_of_add_lt_add_left ℝ _ a b c,
  le_iff_exists_add     := assume ⟨a, ha⟩ ⟨b, hb⟩,
    iff.intro
      (assume h : a ≤ b,
        ⟨⟨b - a, le_sub_iff_add_le.2 $ by simp [h]⟩,
          nnreal.eq $ show b = a + (b - a), by rw [add_sub_cancel'_right]⟩)
      (assume ⟨⟨c, hc⟩, eq⟩, eq.symm ▸ show a ≤ a + c, from (le_add_iff_nonneg_right a).2 hc),
  ..nnreal.comm_semiring,
  ..nnreal.decidable_linear_order}

instance : order_bot ℝ≥0 :=
{ bot := ⊥, bot_le := zero_le, .. nnreal.decidable_linear_order }

instance : distrib_lattice ℝ≥0 := by apply_instance

instance : semilattice_inf_bot ℝ≥0 :=
{ .. nnreal.lattice.order_bot, .. nnreal.lattice.distrib_lattice }

instance : semilattice_sup_bot ℝ≥0 :=
{ .. nnreal.lattice.order_bot, .. nnreal.lattice.distrib_lattice }

instance : linear_ordered_semiring ℝ≥0 :=
{ add_left_cancel            := assume a b c h, nnreal.eq $ @add_left_cancel ℝ _ a b c (nnreal.eq_iff.2 h),
  add_right_cancel           := assume a b c h, nnreal.eq $ @add_right_cancel ℝ _ a b c (nnreal.eq_iff.2 h),
  le_of_add_le_add_left      := assume a b c, @le_of_add_le_add_left ℝ _ a b c,
  mul_le_mul_of_nonneg_left  := assume a b c, @mul_le_mul_of_nonneg_left ℝ _ a b c,
  mul_le_mul_of_nonneg_right := assume a b c, @mul_le_mul_of_nonneg_right ℝ _ a b c,
  mul_lt_mul_of_pos_left     := assume a b c, @mul_lt_mul_of_pos_left ℝ _ a b c,
  mul_lt_mul_of_pos_right    := assume a b c, @mul_lt_mul_of_pos_right ℝ _ a b c,
  zero_lt_one                := @zero_lt_one ℝ _,
  .. nnreal.decidable_linear_order,
  .. nnreal.canonically_ordered_monoid,
  .. nnreal.comm_semiring }

instance : canonically_ordered_comm_semiring ℝ≥0 :=
{ zero_ne_one     := assume h, @zero_ne_one ℝ _ $ congr_arg subtype.val $ h,
  mul_eq_zero_iff := assume a b, nnreal.eq_iff.symm.trans $ mul_eq_zero.trans $ by simp,
  .. nnreal.linear_ordered_semiring,
  .. nnreal.canonically_ordered_monoid,
  .. nnreal.comm_semiring }

lemma sum_coe {α} {s : finset α} {f : α → nnreal} :
  s.sum (λa, (f a : ℝ)) = (s.sum f : nnreal)  :=
finset.sum_hom _ rfl (assume a b, rfl)

end nnreal
