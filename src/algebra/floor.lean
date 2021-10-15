/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
import tactic.abel
import tactic.linarith

/-!
# Floor and ceil

## Summary

We define the natural- and integer-valued floor and ceil functions on linearly ordered rings.

## Main Definitions

- `floor_ring`: Linear ordered ring with a floor function.
- `int.floor a`: Greatest integer `z` such that `z ≤ a`.
- `int.ceil a`: Least integer `z` such that `a ≤ z`.
- `int.fract a`: Fractional part of `a`, defined as `a - floor a`.
- `nat.floor a`: Greatest natural `n` such that `n ≤ a`. Defined as `0` if `a < 0`.
- `nat.ceil a`: Least natural `n` such that `a ≤ n`.

## Notations

- `⌊a⌋` is `int.floor a`.
- `⌈a⌉` is `int.ceil a`.
- `⌊a⌋₊` is `nat.floor a`.
- `⌈a⌉₊` is `nat.ceil a`.

The index `₊` in the notations for `nat.floor` and `nat.ceil` is used in analogy to the notation
for `nnnorm`.

## Tags

rounding, floor, ceil
-/

variables {α : Type*}

open_locale classical

/-! ### Floor rings -/

/--
A `floor_ring` is a linear ordered ring over `α` with a function
`floor : α → ℤ` satisfying `∀ (z : ℤ) (a : α), z ≤ floor a ↔ (z : α) ≤ a)`.
-/
class floor_ring (α) [linear_ordered_ring α] :=
(floor : α → ℤ)
(le_floor : ∀ (z : ℤ) (a : α), z ≤ floor a ↔ (z : α) ≤ a)

instance : floor_ring ℤ := { floor := id, le_floor := λ _ _, by { rw int.cast_id, refl }}

namespace int
variables [linear_ordered_ring α] [floor_ring α] {z : ℤ} {a : α}

/-- `int.floor a` is the greatest integer `z` such that `z ≤ a`. It is denoted with `⌊a⌋`. -/
def floor : α → ℤ := floor_ring.floor

/-- `int.ceil a` is the smallest integer `z` such that `a ≤ z`. It is denoted with `⌈a⌉`. -/
def ceil (a : α) : ℤ := -floor (-a)

/-- `int.fract a`, the fractional part of `a`, is `a` minus its floor. -/
def fract (a : α) : α := a - floor a

notation `⌊` a `⌋` := int.floor a
notation `⌈` a `⌉` := int.ceil a
-- Mathematical notation for `fract a` is usually `{a}`. Let's not even go there.

/-! #### Floor -/

lemma le_floor : ∀ {z : ℤ} {a : α}, z ≤ ⌊a⌋ ↔ (z : α) ≤ a := floor_ring.le_floor

lemma floor_lt {a : α} {z : ℤ} : ⌊a⌋ < z ↔ a < z := lt_iff_lt_of_le_iff_le le_floor

lemma floor_le (a : α) : (⌊a⌋ : α) ≤ a := le_floor.1 le_rfl

lemma floor_nonneg {a : α} : 0 ≤ ⌊a⌋ ↔ 0 ≤ a := le_floor

lemma lt_succ_floor (a : α) : a < ⌊a⌋.succ := floor_lt.1 $ int.lt_succ_self _

lemma lt_floor_add_one (a : α) : a < ⌊a⌋ + 1 :=
by simpa only [int.succ, int.cast_add, int.cast_one] using lt_succ_floor a

lemma sub_one_lt_floor (a : α) : a - 1 < ⌊a⌋ := sub_lt_iff_lt_add.2 (lt_floor_add_one a)

@[simp] lemma floor_coe (z : ℤ) : ⌊(z : α)⌋ = z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor, int.cast_le]

@[simp] lemma floor_zero : ⌊(0 : α)⌋ = 0 := floor_coe 0

@[simp] lemma floor_one : ⌊(1 : α)⌋ = 1 := by rw [← int.cast_one, floor_coe]

@[mono] lemma floor_mono {a b : α} (h : a ≤ b) : ⌊a⌋ ≤ ⌊b⌋ := le_floor.2 ((floor_le _).trans h)

lemma floor_pos : 0 < ⌊a⌋ ↔ 1 ≤ a :=
⟨λ h, le_trans (by rwa [←int.cast_one, int.cast_le, ←zero_add (1 : ℤ), int.add_one_le_iff])
  (floor_le _), λ h, zero_lt_one.trans_le (le_floor.2 $ by rwa int.cast_one)⟩

@[simp] lemma floor_add_int (a : α) (z : ℤ) : ⌊a + z⌋ = ⌊a⌋ + z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor,
  ← sub_le_iff_le_add, ← sub_le_iff_le_add, le_floor, int.cast_sub]

lemma floor_add_one (a : α) : ⌊a + 1⌋ = ⌊a⌋ + 1 :=
by { convert floor_add_int a 1, exact cast_one.symm }

@[simp] lemma floor_int_add (z : ℤ) (a : α) : ⌊↑z + a⌋ = z + ⌊a⌋ :=
by simpa only [add_comm] using floor_add_int a z

@[simp] lemma floor_add_nat (a : α) (n : ℕ) : ⌊a + n⌋ = ⌊a⌋ + n := floor_add_int a n

@[simp] lemma floor_nat_add (n : ℕ) (a : α) : ⌊↑n + a⌋ = n + ⌊a⌋ := floor_int_add n a

@[simp] lemma floor_sub_int (a : α) (z : ℤ) : ⌊a - z⌋ = ⌊a⌋ - z :=
eq.trans (by rw [int.cast_neg, sub_eq_add_neg]) (floor_add_int _ _)

@[simp] lemma floor_sub_nat (a : α) (n : ℕ) : ⌊a - n⌋ = ⌊a⌋ - n := floor_sub_int a n

lemma abs_sub_lt_one_of_floor_eq_floor {α : Type*} [linear_ordered_comm_ring α] [floor_ring α]
  {a b : α} (h : ⌊a⌋ = ⌊b⌋) : |a - b| < 1 :=
begin
  have : a < ⌊a⌋ + 1         := lt_floor_add_one a,
  have : b < ⌊b⌋ + 1         :=  lt_floor_add_one b,
  have : (⌊a⌋ : α) = ⌊b⌋ := int.cast_inj.2 h,
  have : (⌊a⌋: α) ≤ a        := floor_le a,
  have : (⌊b⌋ : α) ≤ b       := floor_le b,
  exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
end

lemma floor_eq_iff {a : α} {z : ℤ} : ⌊a⌋ = z ↔ ↑z ≤ a ∧ a < z + 1 :=
by rw [le_antisymm_iff, le_floor, ←int.lt_add_one_iff, floor_lt, int.cast_add, int.cast_one,
  and.comm]

lemma floor_eq_on_Ico (n : ℤ) : ∀ a ∈ set.Ico (n : α) (n + 1), ⌊a⌋ = n :=
λ a ⟨h₀, h₁⟩, floor_eq_iff.mpr ⟨h₀, h₁⟩

lemma floor_eq_on_Ico' (n : ℤ) : ∀ a ∈ set.Ico (n : α) (n + 1), (⌊a⌋ : α) = n :=
λ a ha, congr_arg _ $ floor_eq_on_Ico n a ha

/-! #### Fractional part -/

@[simp] lemma floor_add_fract (a : α) : (⌊a⌋ : α) + fract a = a := add_sub_cancel'_right _ _

@[simp] lemma fract_add_floor (a : α) : fract a + ⌊a⌋ = a := sub_add_cancel _ _

lemma fract_nonneg (a : α) : 0 ≤ fract a := sub_nonneg.2 $ floor_le _

lemma fract_lt_one (a : α) : fract a < 1 := sub_lt.1 $ sub_one_lt_floor _

@[simp] lemma fract_zero : fract (0 : α) = 0 := by rw [fract, floor_zero, cast_zero, sub_self]

@[simp] lemma fract_coe (z : ℤ) : fract (z : α) = 0 :=
by { unfold fract, rw floor_coe, exact sub_self _ }

@[simp] lemma fract_floor (a : α) : fract (⌊a⌋ : α) = 0 := fract_coe _

@[simp] lemma floor_fract (a : α) : ⌊fract a⌋ = 0 :=
floor_eq_iff.2 ⟨fract_nonneg _, by { rw [int.cast_zero, zero_add], exact fract_lt_one a }⟩

lemma fract_eq_iff {a b : α} : fract a = b ↔ 0 ≤ b ∧ b < 1 ∧ ∃ z : ℤ, a - b = z :=
⟨λ h, by { rw ←h, exact ⟨fract_nonneg _, fract_lt_one _, ⟨⌊a⌋, sub_sub_cancel _ _⟩⟩},
  begin
    rintro ⟨h₀, h₁, z, hz⟩,
    show a - ⌊a⌋ = b, apply eq.symm,
    rw [eq_sub_iff_add_eq, add_comm, ←eq_sub_iff_add_eq],
    rw [hz, int.cast_inj, floor_eq_iff, ←hz],
    clear hz, split; simpa [sub_eq_add_neg, add_assoc]
  end⟩

lemma fract_eq_fract {a b : α} : fract a = fract b ↔ ∃ z : ℤ, a - b = z :=
⟨λ h, ⟨⌊a⌋ - ⌊b⌋, begin
  unfold fract at h, rw [int.cast_sub, sub_eq_sub_iff_sub_eq_sub.1 h],
 end⟩, begin
  rintro ⟨z, hz⟩,
  refine fract_eq_iff.2 ⟨fract_nonneg _, fract_lt_one _, z + ⌊b⌋, _⟩,
  rw [eq_add_of_sub_eq hz, add_comm, int.cast_add],
  exact add_sub_sub_cancel _ _ _,
end⟩

@[simp] lemma fract_fract (a : α) : fract (fract a) = fract a :=
fract_eq_fract.2 ⟨-⌊a⌋, (cast_neg ⌊a⌋).symm.subst (sub_sub_cancel_left a ⌊a⌋)⟩

lemma fract_add (a b : α) : ∃ z : ℤ, fract (a + b) - fract a - fract b = z :=
⟨⌊a⌋ + ⌊b⌋ - ⌊a + b⌋, by { unfold fract, simp [sub_eq_add_neg], abel }⟩

lemma fract_mul_nat (a : α) (b : ℕ) : ∃ z : ℤ, fract a * b - fract (a * b) = z :=
begin
  induction b with c hc,
    use 0, simp,
  rcases hc with ⟨z, hz⟩,
  rw [nat.succ_eq_add_one, nat.cast_add, mul_add, mul_add, nat.cast_one, mul_one, mul_one],
  rcases fract_add (a * c) a with ⟨y, hy⟩,
  use z - y,
  rw [int.cast_sub, ←hz, ←hy],
  abel
end

/-! #### Ceil -/

lemma ceil_le {z : ℤ} {a : α} : ⌈a⌉ ≤ z ↔ a ≤ z :=
by rw [ceil, neg_le, le_floor, int.cast_neg, neg_le_neg_iff]

lemma floor_neg {a : α} : ⌊-a⌋ = -⌈a⌉ :=
eq_of_forall_le_iff (λ z, by rw [le_neg, ceil_le, le_floor, int.cast_neg, le_neg])

lemma ceil_neg {a : α} : ⌈-a⌉ = -⌊a⌋ :=
eq_of_forall_ge_iff (λ z, by rw [neg_le, ceil_le, le_floor, int.cast_neg, neg_le])

lemma lt_ceil {a : α} {z : ℤ} : z < ⌈a⌉ ↔ (z : α) < a := lt_iff_lt_of_le_iff_le ceil_le

lemma ceil_le_floor_add_one (a : α) : ⌈a⌉ ≤ ⌊a⌋ + 1 :=
by { rw [ceil_le, int.cast_add, int.cast_one], exact (lt_floor_add_one a).le }

lemma le_ceil (a : α) : a ≤ ⌈a⌉ := ceil_le.1 le_rfl

@[simp] lemma ceil_coe (z : ℤ) : ⌈(z : α)⌉ = z :=
eq_of_forall_ge_iff $ λ a, by rw [ceil_le, int.cast_le]

lemma ceil_mono {a b : α} (h : a ≤ b) : ⌈a⌉ ≤ ⌈b⌉ := ceil_le.2 (h.trans (le_ceil _))

@[simp] lemma ceil_add_int (a : α) (z : ℤ) : ⌈a + z⌉ = ⌈a⌉ + z :=
by rw [←neg_inj, neg_add', ←floor_neg, ←floor_neg, neg_add', floor_sub_int]

lemma ceil_add_one (a : α) : ⌈a + 1⌉ = ⌈a⌉ + 1 :=
by { convert ceil_add_int a (1 : ℤ), exact cast_one.symm }

lemma ceil_sub_int (a : α) (z : ℤ) : ⌈a - z⌉ = ⌈a⌉ - z :=
eq.trans (by rw [int.cast_neg, sub_eq_add_neg]) (ceil_add_int _ _)

lemma ceil_lt_add_one (a : α) : (⌈a⌉ : α) < a + 1 :=
by { rw [← lt_ceil, ← int.cast_one, ceil_add_int], apply lt_add_one }

lemma ceil_pos {a : α} : 0 < ⌈a⌉ ↔ 0 < a := lt_ceil

@[simp] lemma ceil_zero : ⌈(0 : α)⌉ = 0 := ceil_coe 0

lemma ceil_nonneg {a : α} (ha : 0 ≤ a) : 0 ≤ ⌈a⌉ :=
by exact_mod_cast ha.trans (le_ceil a)

lemma ceil_eq_iff {a : α} {z : ℤ} : ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a ≤ z :=
by rw [←ceil_le, ←int.cast_one, ←int.cast_sub, ←lt_ceil, int.sub_one_lt_iff, le_antisymm_iff,
  and.comm]

lemma ceil_eq_on_Ioc (z : ℤ) : ∀ a ∈ set.Ioc (z - 1 : α) z, ⌈a⌉ = z :=
λ a ⟨h₀, h₁⟩, ceil_eq_iff.mpr ⟨h₀, h₁⟩

lemma ceil_eq_on_Ioc' (z : ℤ) : ∀ a ∈ set.Ioc (z - 1 : α) z, (⌈a⌉ : α) = z :=
λ a ha, by exact_mod_cast ceil_eq_on_Ioc z a ha

lemma floor_lt_ceil_of_lt {a b : α} (h : a < b) : ⌊a⌋ < ⌈b⌉ :=
cast_lt.1 $ (floor_le a).trans_lt $ h.trans_le $ le_ceil b

/-! #### Intervals -/

@[simp] lemma preimage_Ioo {a b : α} : ((coe : ℤ → α) ⁻¹' (set.Ioo a b)) = set.Ioo ⌊a⌋ ⌈b⌉ :=
by { ext, simp [floor_lt, lt_ceil] }

@[simp] lemma preimage_Ico {a b : α} : ((coe : ℤ → α) ⁻¹' (set.Ico a b)) = set.Ico ⌈a⌉ ⌈b⌉ :=
by { ext, simp [ceil_le, lt_ceil] }

@[simp] lemma preimage_Ioc {a b : α} : ((coe : ℤ → α) ⁻¹' (set.Ioc a b)) = set.Ioc ⌊a⌋ ⌊b⌋ :=
by { ext, simp [floor_lt, le_floor] }

@[simp] lemma preimage_Icc {a b : α} : ((coe : ℤ → α) ⁻¹' (set.Icc a b)) = set.Icc ⌈a⌉ ⌊b⌋ :=
by { ext, simp [ceil_le, le_floor] }

@[simp] lemma preimage_Ioi {a : α} : ((coe : ℤ → α) ⁻¹' (set.Ioi a)) = set.Ioi ⌊a⌋ :=
by { ext, simp [floor_lt] }

@[simp] lemma preimage_Ici {a : α} : ((coe : ℤ → α) ⁻¹' (set.Ici a)) = set.Ici ⌈a⌉ :=
by { ext, simp [ceil_le] }

@[simp] lemma preimage_Iio {a : α} : ((coe : ℤ → α) ⁻¹' (set.Iio a)) = set.Iio ⌈a⌉ :=
by { ext, simp [lt_ceil] }

@[simp] lemma preimage_Iic {a : α} : ((coe : ℤ → α) ⁻¹' (set.Iic a)) = set.Iic ⌊a⌋ :=
by { ext, simp [le_floor] }

end int

lemma floor_ring_unique {α} [linear_ordered_ring α] (inst1 inst2 : floor_ring α) :
  @int.floor _ _ inst1 = @int.floor _ _ inst2 :=
begin
  ext v,
  suffices : (⌊v⌋ : α) ≤ v ∧ v < ⌊v⌋ + 1, by rwa [int.floor_eq_iff],
  exact ⟨int.floor_le v, int.lt_floor_add_one v⟩
end

/-! ### `nat.floor` and `nat.ceil` -/

namespace nat
variables [linear_ordered_ring α] [floor_ring α] {a : α} {n : ℕ}

/-- `nat.floor a` is the greatest natural `n` that is less than `a`.
It is equal to `⌊a⌋` when `a ≥ 0`, and is `0` otherwise. It is denoted with `⌊a⌋₊`.-/
def floor (a : α) : ℕ := int.to_nat ⌊a⌋

/-- `nat.ceil a` is the least natural `n` that is greater than `a`.
It is equal to `⌈a⌉` when `a ≥ 0`, and is `0` otherwise. It is denoted with `⌈a⌉₊`. -/
def ceil (a : α) : ℕ := int.to_nat ⌈a⌉

notation `⌊` a `⌋₊` := nat.floor a
notation `⌈` a `⌉₊` := nat.ceil a

lemma floor_of_nonpos (ha : a ≤ 0) : ⌊a⌋₊ = 0 :=
begin
  apply int.to_nat_of_nonpos,
  exact_mod_cast (int.floor_le a).trans ha,
end

lemma floor_le (ha : 0 ≤ a) : ↑⌊a⌋₊ ≤ a :=
begin
  refine le_trans _ (int.floor_le _),
  norm_cast,
  exact (int.to_nat_of_nonneg (int.floor_nonneg.2 ha)).le,
end

lemma le_floor_of_le (h : ↑n ≤ a) : n ≤ ⌊a⌋₊ :=
begin
  have hn := int.le_to_nat n,
  norm_cast at hn,
  exact hn.trans (int.to_nat_le_to_nat (int.le_floor.2 h)),
end

lemma le_floor_iff (ha : 0 ≤ a) : n ≤ ⌊a⌋₊ ↔ ↑n ≤ a :=
⟨λ h, (nat.cast_le.2 h).trans (floor_le ha), le_floor_of_le⟩

lemma floor_pos : 0 < ⌊a⌋₊ ↔ 1 ≤ a :=
begin
  cases le_total a 0,
  { rw floor_of_nonpos h,
    exact iff_of_false (lt_irrefl 0) (λ ha, zero_lt_one.not_le $ ha.trans h) },
  { rw ←nat.cast_one,
    exact le_floor_iff h }
end

lemma pos_of_floor_pos (h : 0 < ⌊a⌋₊) : 0 < a :=
(le_or_lt a 0).resolve_left (λ ha, lt_irrefl 0 $ by rwa floor_of_nonpos ha at h)

lemma lt_of_lt_floor (h : n < ⌊a⌋₊) : ↑n < a :=
(nat.cast_lt.2 h).trans_le (floor_le (pos_of_floor_pos ((nat.zero_le n).trans_lt h)).le)

lemma floor_lt_iff (ha : 0 ≤ a) : ⌊a⌋₊ < n ↔ a < ↑n :=
le_iff_le_iff_lt_iff_lt.1 (le_floor_iff ha)

lemma floor_mono {a₁ a₂ : α} (h : a₁ ≤ a₂) : ⌊a₁⌋₊ ≤ ⌊a₂⌋₊ :=
begin
  obtain ha | ha := le_total a₁ 0,
  { rw floor_of_nonpos ha,
    exact nat.zero_le _ },
  exact le_floor_of_le ((floor_le ha).trans h),
end

@[simp] lemma floor_coe (n : ℕ) : ⌊(n : α)⌋₊ = n :=
begin
  rw floor,
  convert int.to_nat_coe_nat n,
  exact int.floor_coe n,
end

@[simp] lemma floor_zero : ⌊(0 : α)⌋₊ = 0 := floor_coe 0

lemma floor_add_nat (ha : 0 ≤ a) (n : ℕ) : ⌊a + n⌋₊ = ⌊a⌋₊ + n :=
begin
  change int.to_nat ⌊a + (n : ℤ)⌋ = int.to_nat ⌊a⌋ + n,
  rw [int.floor_add_int, int.to_nat_add_nat (int.le_floor.2 ha)],
end

lemma floor_add_one {a : α} (ha : 0 ≤ a) : ⌊a + 1⌋₊ = ⌊a⌋₊ + 1 :=
by { convert floor_add_nat ha 1, exact cast_one.symm }

lemma lt_floor_add_one (a : α) : a < ⌊a⌋₊ + 1 :=
begin
  refine (int.lt_floor_add_one a).trans_le (add_le_add_right _ 1),
  norm_cast,
  exact int.le_to_nat _,
end

lemma sub_one_lt_floor (a : α) : a - 1 < ⌊a⌋₊ := sub_lt_iff_lt_add.2 (lt_floor_add_one a)

lemma floor_eq_zero_iff : ⌊a⌋₊ = 0 ↔ a < 1 :=
begin
  obtain ha | ha := le_total a 0,
  { exact iff_of_true (floor_of_nonpos ha) (ha.trans_lt zero_lt_one) },
  rw [←nat.cast_one, ←floor_lt_iff ha, nat.lt_add_one_iff, nat.le_zero_iff],
end

/-! #### Ceil -/

@[simp] lemma ceil_le : ⌈a⌉₊ ≤ n ↔ a ≤ n := by { rw [ceil, int.to_nat_le, int.ceil_le], refl }

lemma lt_ceil : n < ⌈a⌉₊ ↔ (n : α) < a :=
not_iff_not.1 $ by rw [not_lt, not_lt, ceil_le]

lemma le_ceil (a : α) : a ≤ ⌈a⌉₊ := ceil_le.1 le_rfl

lemma ceil_mono {a₁ a₂ : α} (h : a₁ ≤ a₂) : ⌈a₁⌉₊ ≤ ⌈a₂⌉₊ := ceil_le.2 (h.trans (le_ceil _))

@[simp] lemma ceil_coe (n : ℕ) : ⌈(n : α)⌉₊ = n :=
show (⌈((n : ℤ) : α)⌉).to_nat = n, by { rw int.ceil_coe, refl }

@[simp] lemma ceil_zero : ⌈(0 : α)⌉₊ = 0 := ceil_coe 0

@[simp] lemma ceil_eq_zero : ⌈a⌉₊ = 0 ↔ a ≤ 0 := by simp [← nonpos_iff_eq_zero]

lemma ceil_add_nat {a : α} (ha : 0 ≤ a) (n : ℕ) : ⌈a + n⌉₊ = ⌈a⌉₊ + n :=
begin
  change int.to_nat (⌈a + (n:ℤ)⌉) = int.to_nat ⌈a⌉ + n,
  rw [int.ceil_add_int],
  have : 0 ≤ ⌈a⌉, by simpa using (int.ceil_mono ha),
  obtain ⟨_, ceil_a_eq⟩ : ∃ (n : ℕ), ⌈a⌉ = n, from int.eq_coe_of_zero_le this,
  rw ceil_a_eq,
  refl
end

lemma ceil_add_one {a : α} (ha : 0 ≤ a) : ⌈a + 1⌉₊ = ⌈a⌉₊ + 1 :=
by { convert ceil_add_nat ha 1, exact cast_one.symm }

lemma ceil_lt_add_one {a : α} (ha : 0 ≤ a) : (⌈a⌉₊ : α) < a + 1 :=
lt_ceil.1 $ (nat.lt_succ_self _).trans_le (ceil_add_one ha).ge

lemma lt_of_ceil_lt {a : α} {n : ℕ} (h : ⌈a⌉₊ < n) : a < n := (le_ceil a).trans_lt (nat.cast_lt.2 h)

lemma le_of_ceil_le {a : α} {n : ℕ} (h : ⌈a⌉₊ ≤ n) : a ≤ n := (le_ceil a).trans (nat.cast_le.2 h)

lemma floor_lt_ceil_of_lt_of_pos {a b : α} (h : a < b) (h' : 0 < b) : ⌊a⌋₊ < ⌈b⌉₊ :=
begin
  rcases le_or_lt 0 a with ha|ha,
  { rw floor_lt_iff ha, exact h.trans_le (le_ceil _) },
  { rwa [floor_of_nonpos ha.le, lt_ceil] }
end

end nat
