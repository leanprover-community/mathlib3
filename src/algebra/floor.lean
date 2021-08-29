/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
import tactic.linarith
import tactic.abel
import algebra.ordered_group
import data.set.intervals.basic

/-!
# Floor and ceil

## Summary

We define `floor`, `ceil`, `nat_floor`and `nat_ceil` functions on linear ordered rings.

## Main Definitions

- `floor_ring`: Linear ordered ring with a floor function.
- `floor x`: Greatest integer `z` such that `z ≤ x`.
- `ceil x`: Least integer `z` such that `x ≤ z`.
- `fract x`: Fractional part of `x`, defined as `x - floor x`.
- `nat_floor x`: Greatest natural `n` such that `n ≤ x`. Defined as `0` if `x < 0`.
- `nat_ceil x`: Least natural `n` such that `x ≤ n`.

## Notations

- `⌊x⌋` is `floor x`.
- `⌈x⌉` is `ceil x`.
- `⌊x⌋₊` is `nat_floor x`.
- `⌈x⌉₊` is `nat_ceil x`.

The index `₊` in the notations for `nat_floor` and `nat_ceil` is used in analogy to the notation
for `nnnorm`.

## Tags

rounding, floor, ceil
-/

variables {α : Type*}

open_locale classical

/-! ### Floor rings -/

/--
A `floor_ring` is a linear ordered ring over `α` with a function
`floor : α → ℤ` satisfying `∀ (z : ℤ) (x : α), z ≤ floor x ↔ (z : α) ≤ x)`.
-/
class floor_ring (α) [linear_ordered_ring α] :=
(floor : α → ℤ)
(le_floor : ∀ (z : ℤ) (x : α), z ≤ floor x ↔ (z : α) ≤ x)

instance : floor_ring ℤ := { floor := id, le_floor := λ _ _, by rw int.cast_id; refl }

variables [linear_ordered_ring α] [floor_ring α]

/-- `floor x` is the greatest integer `z` such that `z ≤ x`. It is denoted with `⌊x⌋`. -/
def floor : α → ℤ := floor_ring.floor

notation `⌊` x `⌋` := floor x

theorem le_floor : ∀ {z : ℤ} {x : α}, z ≤ ⌊x⌋ ↔ (z : α) ≤ x :=
floor_ring.le_floor

theorem floor_lt {x : α} {z : ℤ} : ⌊x⌋ < z ↔ x < z :=
lt_iff_lt_of_le_iff_le le_floor

theorem floor_le (x : α) : (⌊x⌋ : α) ≤ x :=
le_floor.1 (le_refl _)

theorem floor_nonneg {x : α} : 0 ≤ ⌊x⌋ ↔ 0 ≤ x :=
by rw [le_floor]; refl

theorem lt_succ_floor (x : α) : x < ⌊x⌋.succ :=
floor_lt.1 $ int.lt_succ_self _

theorem lt_floor_add_one (x : α) : x < ⌊x⌋ + 1 :=
by simpa only [int.succ, int.cast_add, int.cast_one] using lt_succ_floor x

theorem sub_one_lt_floor (x : α) : x - 1 < ⌊x⌋ :=
sub_lt_iff_lt_add.2 (lt_floor_add_one x)

@[simp] theorem floor_coe (z : ℤ) : ⌊(z:α)⌋ = z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor, int.cast_le]

@[simp] theorem floor_zero : ⌊(0:α)⌋ = 0 := floor_coe 0

@[simp] theorem floor_one : ⌊(1:α)⌋ = 1 :=
by rw [← int.cast_one, floor_coe]

@[mono] theorem floor_mono {a b : α} (h : a ≤ b) : ⌊a⌋ ≤ ⌊b⌋ :=
le_floor.2 (le_trans (floor_le _) h)

@[simp] theorem floor_add_int (x : α) (z : ℤ) : ⌊x + z⌋ = ⌊x⌋ + z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor,
  ← sub_le_iff_le_add, ← sub_le_iff_le_add, le_floor, int.cast_sub]

@[simp] theorem floor_int_add (z : ℤ) (x : α) : ⌊↑z + x⌋ = z + ⌊x⌋ :=
by simpa only [add_comm] using floor_add_int x z

@[simp] theorem floor_add_nat (x : α) (n : ℕ) : ⌊x + n⌋ = ⌊x⌋ + n :=
floor_add_int x n

@[simp] theorem floor_nat_add (n : ℕ) (x : α) : ⌊↑n + x⌋ = n + ⌊x⌋ :=
floor_int_add n x

@[simp] theorem floor_sub_int (x : α) (z : ℤ) : ⌊x - z⌋ = ⌊x⌋ - z :=
eq.trans (by rw [int.cast_neg, sub_eq_add_neg]) (floor_add_int _ _)

@[simp] theorem floor_sub_nat (x : α) (n : ℕ) : ⌊x - n⌋ = ⌊x⌋ - n :=
floor_sub_int x n

lemma abs_sub_lt_one_of_floor_eq_floor {α : Type*} [linear_ordered_comm_ring α]
  [floor_ring α] {x y : α} (h : ⌊x⌋ = ⌊y⌋) : abs (x - y) < 1 :=
begin
  have : x < ⌊x⌋ + 1         := lt_floor_add_one x,
  have : y < ⌊y⌋ + 1         :=  lt_floor_add_one y,
  have : (⌊x⌋ : α) = ⌊y⌋ := int.cast_inj.2 h,
  have : (⌊x⌋: α) ≤ x        := floor_le x,
  have : (⌊y⌋ : α) ≤ y       := floor_le y,
  exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
end

lemma floor_eq_iff {r : α} {z : ℤ} :
  ⌊r⌋ = z ↔ ↑z ≤ r ∧ r < (z + 1) :=
by rw [←le_floor, ←int.cast_one, ←int.cast_add, ←floor_lt,
int.lt_add_one_iff, le_antisymm_iff, and.comm]

lemma floor_ring_unique {α} [linear_ordered_ring α] (inst1 inst2 : floor_ring α) :
  @floor _ _ inst1 = @floor _ _ inst2 :=
begin
  ext v,
  suffices : (⌊v⌋ : α) ≤ v ∧ v < ⌊v⌋ + 1, by rwa [floor_eq_iff],
  exact ⟨floor_le v, lt_floor_add_one v⟩
end

lemma floor_eq_on_Ico (n : ℤ) : ∀ x ∈ (set.Ico n (n+1) : set α), ⌊x⌋ = n :=
λ x ⟨h₀, h₁⟩, floor_eq_iff.mpr ⟨h₀, h₁⟩

lemma floor_eq_on_Ico' (n : ℤ) : ∀ x ∈ (set.Ico n (n+1) : set α), (⌊x⌋ : α) = n :=
λ x hx, by exact_mod_cast floor_eq_on_Ico n x hx

/-- The fractional part fract r of r is just r - ⌊r⌋ -/
def fract (r : α) : α := r - ⌊r⌋

-- Mathematical notation is usually {r}. Let's not even go there.

@[simp] lemma floor_add_fract (r : α) : (⌊r⌋ : α) + fract r = r := by unfold fract; simp

@[simp] lemma fract_add_floor (r : α) : fract r + ⌊r⌋ = r := sub_add_cancel _ _

theorem fract_nonneg (r : α) : 0 ≤ fract r :=
sub_nonneg.2 $ floor_le _

theorem fract_lt_one (r : α) : fract r < 1 :=
sub_lt.1 $ sub_one_lt_floor _

@[simp] lemma fract_zero : fract (0 : α) = 0 := by unfold fract; simp

@[simp] lemma fract_coe (z : ℤ) : fract (z : α) = 0 :=
by unfold fract; rw floor_coe; exact sub_self _

@[simp] lemma fract_floor (r : α) : fract (⌊r⌋ : α) = 0 := fract_coe _

@[simp] lemma floor_fract (r : α) : ⌊fract r⌋ = 0 :=
by rw floor_eq_iff; exact ⟨fract_nonneg _,
  by rw [int.cast_zero, zero_add]; exact fract_lt_one r⟩

theorem fract_eq_iff {r s : α} : fract r = s ↔ 0 ≤ s ∧ s < 1 ∧ ∃ z : ℤ, r - s = z :=
⟨λ h, by rw ←h; exact ⟨fract_nonneg _, fract_lt_one _,
  ⟨⌊r⌋, sub_sub_cancel _ _⟩⟩, begin
    intro h,
    show r - ⌊r⌋ = s, apply eq.symm,
    rw [eq_sub_iff_add_eq, add_comm, ←eq_sub_iff_add_eq],
    rcases h with ⟨hge, hlt, ⟨z, hz⟩⟩,
    rw [hz, int.cast_inj, floor_eq_iff, ←hz],
    clear hz, split; simpa [sub_eq_add_neg, add_assoc]
  end⟩

theorem fract_eq_fract {r s : α} : fract r = fract s ↔ ∃ z : ℤ, r - s = z :=
⟨λ h, ⟨⌊r⌋ - ⌊s⌋, begin
  unfold fract at h, rw [int.cast_sub, sub_eq_sub_iff_sub_eq_sub.1 h],
 end⟩,
λ h, begin
  rcases h with ⟨z, hz⟩,
  rw fract_eq_iff,
  split, exact fract_nonneg _,
  split, exact fract_lt_one _,
  use z + ⌊s⌋,
  rw [eq_add_of_sub_eq hz, int.cast_add],
  unfold fract, simp [sub_eq_add_neg, add_assoc]
end⟩

@[simp] lemma fract_fract (r : α) : fract (fract r) = fract r :=
by rw fract_eq_fract; exact ⟨-⌊r⌋, by simp [sub_eq_add_neg, add_assoc, fract]⟩

theorem fract_add (r s : α) : ∃ z : ℤ, fract (r + s) - fract r - fract s = z :=
⟨⌊r⌋ + ⌊s⌋ - ⌊r + s⌋, by unfold fract; simp [sub_eq_add_neg]; abel⟩

theorem fract_mul_nat (r : α) (b : ℕ) : ∃ z : ℤ, fract r * b - fract (r * b) = z :=
begin
  induction b with c hc,
    use 0, simp,
  rcases hc with ⟨z, hz⟩,
  rw [nat.succ_eq_add_one, nat.cast_add, mul_add, mul_add, nat.cast_one, mul_one, mul_one],
  rcases fract_add (r * c) r with ⟨y, hy⟩,
  use z - y,
  rw [int.cast_sub, ←hz, ←hy],
  abel
end

/-- `ceil x` is the smallest integer `z` such that `x ≤ z`. It is denoted with `⌈x⌉`. -/
def ceil (x : α) : ℤ := -⌊-x⌋

notation `⌈` x `⌉` := ceil x

theorem ceil_le {z : ℤ} {x : α} : ⌈x⌉ ≤ z ↔ x ≤ z :=
by rw [ceil, neg_le, le_floor, int.cast_neg, neg_le_neg_iff]

theorem lt_ceil {x : α} {z : ℤ} : z < ⌈x⌉ ↔ (z:α) < x :=
lt_iff_lt_of_le_iff_le ceil_le

theorem ceil_le_floor_add_one (x : α) : ⌈x⌉ ≤ ⌊x⌋ + 1 :=
by rw [ceil_le, int.cast_add, int.cast_one]; exact le_of_lt (lt_floor_add_one x)

theorem le_ceil (x : α) : x ≤ ⌈x⌉ :=
ceil_le.1 (le_refl _)

@[simp] theorem ceil_coe (z : ℤ) : ⌈(z:α)⌉ = z :=
by rw [ceil, ← int.cast_neg, floor_coe, neg_neg]

theorem ceil_mono {a b : α} (h : a ≤ b) : ⌈a⌉ ≤ ⌈b⌉ :=
ceil_le.2 (le_trans h (le_ceil _))

@[simp] theorem ceil_add_int (x : α) (z : ℤ) : ⌈x + z⌉ = ⌈x⌉ + z :=
by rw [ceil, neg_add', floor_sub_int, neg_sub, sub_eq_neg_add]; refl

theorem ceil_sub_int (x : α) (z : ℤ) : ⌈x - z⌉ = ⌈x⌉ - z :=
eq.trans (by rw [int.cast_neg, sub_eq_add_neg]) (ceil_add_int _ _)

theorem ceil_lt_add_one (x : α) : (⌈x⌉ : α) < x + 1 :=
by rw [← lt_ceil, ← int.cast_one, ceil_add_int]; apply lt_add_one

lemma ceil_pos {a : α} : 0 < ⌈a⌉ ↔ 0 < a :=
⟨ λ h, have ⌊-a⌋ < 0, from neg_of_neg_pos h,
  pos_of_neg_neg $ lt_of_not_ge $ (not_iff_not_of_iff floor_nonneg).1 $ not_le_of_gt this,
 λ h, have -a < 0, from neg_neg_of_pos h,
  neg_pos_of_neg $ lt_of_not_ge $ (not_iff_not_of_iff floor_nonneg).2 $ not_le_of_gt this ⟩

@[simp] theorem ceil_zero : ⌈(0 : α)⌉ = 0 := by simp [ceil]

lemma ceil_nonneg {q : α} (hq : 0 ≤ q) : 0 ≤ ⌈q⌉ :=
if h : q > 0 then le_of_lt $ ceil_pos.2 h
else by rw [le_antisymm (le_of_not_lt h) hq, ceil_zero]; trivial

lemma ceil_eq_iff {r : α} {z : ℤ} :
  ⌈r⌉ = z ↔ ↑z-1 < r ∧ r ≤ z :=
by rw [←ceil_le, ←int.cast_one, ←int.cast_sub, ←lt_ceil,
int.sub_one_lt_iff, le_antisymm_iff, and.comm]

lemma ceil_eq_on_Ioc (n : ℤ) : ∀ x ∈ (set.Ioc (n-1) n : set α), ⌈x⌉ = n :=
λ x ⟨h₀, h₁⟩, ceil_eq_iff.mpr ⟨h₀, h₁⟩

lemma ceil_eq_on_Ioc' (n : ℤ) : ∀ x ∈ (set.Ioc (n-1) n : set α), (⌈x⌉ : α) = n :=
λ x hx, by exact_mod_cast ceil_eq_on_Ioc n x hx

lemma floor_lt_ceil_of_lt {x y : α} (h : x < y) : ⌊x⌋ < ⌈y⌉ :=
by { rw floor_lt, exact h.trans_le (le_ceil _) }

/-! ### `nat_floor` and `nat_ceil` -/

section nat
variables {a : α} {n : ℕ}

/-- `nat_floor x` is the greatest natural `n` that is less than `x`.
It is equal to `⌊x⌋` when `x ≥ 0`, and is `0` otherwise. It is denoted with `⌊x⌋₊`.-/
def nat_floor (a : α) : ℕ := int.to_nat ⌊a⌋

notation `⌊` x `⌋₊` := nat_floor x

lemma nat_floor_of_nonpos (ha : a ≤ 0) : ⌊a⌋₊ = 0 :=
begin
  apply int.to_nat_of_nonpos,
  exact_mod_cast (floor_le a).trans ha,
end

lemma pos_of_nat_floor_pos (h : 0 < ⌊a⌋₊) : 0 < a :=
begin
  refine (le_or_lt a 0).resolve_left (λ ha, lt_irrefl 0 _),
  rwa nat_floor_of_nonpos ha at h,
end

lemma nat_floor_le (ha : 0 ≤ a) : ↑⌊a⌋₊ ≤ a :=
begin
  refine le_trans _ (floor_le _),
  norm_cast,
  exact (int.to_nat_of_nonneg (floor_nonneg.2 ha)).le,
end

lemma le_nat_floor_of_le (h : ↑n ≤ a) : n ≤ ⌊a⌋₊ :=
begin
  have hn := int.le_to_nat n,
  norm_cast at hn,
  exact hn.trans (int.to_nat_le_to_nat (le_floor.2 h)),
end

theorem le_nat_floor_iff (ha : 0 ≤ a) : n ≤ ⌊a⌋₊ ↔ ↑n ≤ a :=
⟨λ h, (nat.cast_le.2 h).trans (nat_floor_le ha), le_nat_floor_of_le⟩

lemma lt_of_lt_nat_floor (h : n < ⌊a⌋₊) : ↑n < a :=
(nat.cast_lt.2 h).trans_le (nat_floor_le (pos_of_nat_floor_pos ((nat.zero_le n).trans_lt h)).le)

theorem nat_floor_lt_iff (ha : 0 ≤ a) : ⌊a⌋₊ < n ↔ a < ↑n :=
le_iff_le_iff_lt_iff_lt.1 (le_nat_floor_iff ha)

theorem nat_floor_mono {a₁ a₂ : α} (h : a₁ ≤ a₂) : ⌊a₁⌋₊ ≤ ⌊a₂⌋₊ :=
begin
  obtain ha | ha := le_total a₁ 0,
  { rw nat_floor_of_nonpos ha,
    exact nat.zero_le _ },
  exact le_nat_floor_of_le ((nat_floor_le ha).trans h),
end

@[simp] theorem nat_floor_coe (n : ℕ) : ⌊(n : α)⌋₊ = n :=
begin
  rw nat_floor,
  convert int.to_nat_coe_nat n,
  exact floor_coe n,
end

@[simp] theorem nat_floor_zero : ⌊(0 : α)⌋₊ = 0 := nat_floor_coe 0

theorem nat_floor_add_nat (ha : 0 ≤ a) (n : ℕ) : ⌊a + n⌋₊ = ⌊a⌋₊ + n :=
begin
  change int.to_nat ⌊a + (n : ℤ)⌋ = int.to_nat ⌊a⌋ + n,
  rw [floor_add_int, int.to_nat_add_nat (le_floor.2 ha)],
end

lemma lt_nat_floor_add_one (a : α) : a < ⌊a⌋₊ + 1 :=
begin
  refine (lt_floor_add_one a).trans_le (add_le_add_right _ 1),
  norm_cast,
  exact int.le_to_nat _,
end

lemma nat_floor_eq_zero_iff : ⌊a⌋₊ = 0 ↔ a < 1 :=
begin
  obtain ha | ha := le_total a 0,
  { exact iff_of_true (nat_floor_of_nonpos ha) (ha.trans_lt zero_lt_one) },
  rw [←nat.cast_one, ←nat_floor_lt_iff ha, nat.lt_add_one_iff, nat.le_zero_iff],
end

/-- `nat_ceil x` is the least natural `n` that is greater than `x`.
It is equal to `⌈x⌉` when `x ≥ 0`, and is `0` otherwise. It is denoted with `⌈x⌉₊`. -/
def nat_ceil (a : α) : ℕ := int.to_nat ⌈a⌉

notation `⌈` x `⌉₊` := nat_ceil x

theorem nat_ceil_le : ⌈a⌉₊ ≤ n ↔ a ≤ n :=
by rw [nat_ceil, int.to_nat_le, ceil_le]; refl

theorem lt_nat_ceil : n < ⌈a⌉₊ ↔ (n : α) < a :=
not_iff_not.1 $ by rw [not_lt, not_lt, nat_ceil_le]

theorem le_nat_ceil (a : α) : a ≤ ⌈a⌉₊ := nat_ceil_le.1 (le_refl _)

theorem nat_ceil_mono {a₁ a₂ : α} (h : a₁ ≤ a₂) : ⌈a₁⌉₊ ≤ ⌈a₂⌉₊ :=
nat_ceil_le.2 (le_trans h (le_nat_ceil _))

@[simp] theorem nat_ceil_coe (n : ℕ) : ⌈(n : α)⌉₊ = n :=
show (⌈((n : ℤ) : α)⌉).to_nat = n, by rw [ceil_coe]; refl

@[simp] theorem nat_ceil_zero : ⌈(0 : α)⌉₊ = 0 := nat_ceil_coe 0

theorem nat_ceil_add_nat {a : α} (a_nonneg : 0 ≤ a) (n : ℕ) : ⌈a + n⌉₊ = ⌈a⌉₊ + n :=
begin
  change int.to_nat (⌈a + (n:ℤ)⌉) = int.to_nat ⌈a⌉ + n,
  rw [ceil_add_int],
  have : 0 ≤ ⌈a⌉, by simpa using (ceil_mono a_nonneg),
  obtain ⟨_, ceil_a_eq⟩ : ∃ (n : ℕ), ⌈a⌉ = n, from int.eq_coe_of_zero_le this,
  rw ceil_a_eq,
  refl
end

theorem nat_ceil_lt_add_one {a : α} (a_nonneg : 0 ≤ a) : (⌈a⌉₊ : α) < a + 1 :=
lt_nat_ceil.1 $ by rw (
  show ⌈a + 1⌉₊ = ⌈a⌉₊ + 1, by exact_mod_cast (nat_ceil_add_nat a_nonneg 1));
  apply nat.lt_succ_self

lemma lt_of_nat_ceil_lt {x : α} {n : ℕ} (h : ⌈x⌉₊ < n) : x < n :=
lt_of_le_of_lt (le_nat_ceil x) (by exact_mod_cast h)

lemma le_of_nat_ceil_le {x : α} {n : ℕ} (h : ⌈x⌉₊ ≤ n) : x ≤ n :=
le_trans (le_nat_ceil x) (by exact_mod_cast h)

lemma nat_floor_lt_nat_ceil_of_lt_of_pos {x y : α} (h : x < y) (h' : 0 < y) :
  ⌊x⌋₊ < ⌈y⌉₊ :=
begin
  rcases le_or_lt 0 x with hx|hx,
  { rw nat_floor_lt_iff hx, exact h.trans_le (le_nat_ceil _) },
  { rwa [nat_floor_of_nonpos hx.le, lt_nat_ceil] }
end

end nat

namespace int

@[simp] lemma preimage_Ioo {x y : α} :
  ((coe : ℤ → α) ⁻¹' (set.Ioo x y)) = set.Ioo ⌊x⌋ ⌈y⌉ :=
by { ext, simp [floor_lt, lt_ceil] }

@[simp] lemma preimage_Ico {x y : α} :
  ((coe : ℤ → α) ⁻¹' (set.Ico x y)) = set.Ico ⌈x⌉ ⌈y⌉ :=
by { ext, simp [ceil_le, lt_ceil] }

@[simp] lemma preimage_Ioc {x y : α} :
  ((coe : ℤ → α) ⁻¹' (set.Ioc x y)) = set.Ioc ⌊x⌋ ⌊y⌋ :=
by { ext, simp [floor_lt, le_floor] }

@[simp] lemma preimage_Icc {x y : α} :
  ((coe : ℤ → α) ⁻¹' (set.Icc x y)) = set.Icc ⌈x⌉ ⌊y⌋ :=
by { ext, simp [ceil_le, le_floor] }

@[simp] lemma preimage_Ioi {x : α} : ((coe : ℤ → α) ⁻¹' (set.Ioi x)) = set.Ioi ⌊x⌋ :=
by { ext, simp [floor_lt] }

@[simp] lemma preimage_Ici {x : α} : ((coe : ℤ → α) ⁻¹' (set.Ici x)) = set.Ici ⌈x⌉ :=
by { ext, simp [ceil_le] }

@[simp] lemma preimage_Iio {x : α} : ((coe : ℤ → α) ⁻¹' (set.Iio x)) = set.Iio ⌈x⌉ :=
by { ext, simp [lt_ceil] }

@[simp] lemma preimage_Iic {x : α} : ((coe : ℤ → α) ⁻¹' (set.Iic x)) = set.Iic ⌊x⌋ :=
by { ext, simp [le_floor] }

end int
