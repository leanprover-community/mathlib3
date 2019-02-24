/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Archimedean groups and fields.
-/
import algebra.group_power data.rat tactic.linarith tactic.abel

local infix ` • ` := add_monoid.smul

variables {α : Type*}

class floor_ring (α) [linear_ordered_ring α] :=
(floor : α → ℤ)
(le_floor : ∀ (z : ℤ) (x : α), z ≤ floor x ↔ (z : α) ≤ x)

instance : floor_ring ℤ :=
{ floor := id, le_floor := λ _ _, by rw int.cast_id; refl }

instance : floor_ring ℚ :=
{ floor := rat.floor, le_floor := @rat.le_floor }

section
variables [linear_ordered_ring α] [floor_ring α]

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

theorem floor_mono {a b : α} (h : a ≤ b) : ⌊a⌋ ≤ ⌊b⌋ :=
le_floor.2 (le_trans (floor_le _) h)

@[simp] theorem floor_add_int (x : α) (z : ℤ) : ⌊x + z⌋ = ⌊x⌋ + z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor,
  ← sub_le_iff_le_add, ← sub_le_iff_le_add, le_floor, int.cast_sub]

theorem floor_sub_int (x : α) (z : ℤ) : ⌊x - z⌋ = ⌊x⌋ - z :=
eq.trans (by rw [int.cast_neg]; refl) (floor_add_int _ _)

lemma abs_sub_lt_one_of_floor_eq_floor {α : Type*} [decidable_linear_ordered_comm_ring α] [floor_ring α]
  {x y : α} (h : floor x = floor y) : abs (x - y) < 1 :=
begin
  have : x < (floor x) + 1         := lt_floor_add_one x,
  have : y < (floor y) + 1         :=  lt_floor_add_one y,
  have : ((floor x) : α) = floor y := int.cast_inj.2 h,
  have : ((floor x) : α) ≤ x       := floor_le x,
  have : ((floor y) : α) ≤ y       := floor_le y,
  exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
end

lemma floor_eq_iff {r : α} {z : ℤ} :
  ⌊r⌋ = z ↔ ↑z ≤ r ∧ r < (z + 1) :=
by rw [←le_floor, ←int.cast_one, ←int.cast_add, ←floor_lt,
int.lt_add_one_iff, le_antisymm_iff, and.comm]

/-- The fractional part fract r of r is just r - ⌊r⌋ -/
def fract (r : α) : α := r - ⌊r⌋

-- Mathematical notation is usually {r}. Let's not even go there.

@[simp] lemma fract_add_floor (r : α) : (⌊r⌋ : α) + fract r = r := by unfold fract; simp

@[simp] lemma floor_add_fract (r : α) : fract r + ⌊r⌋ = r := sub_add_cancel _ _

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
    clear hz, split; linarith {discharger := `[simp]}
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
  unfold fract, simp
end⟩

@[simp] lemma fract_fract (r : α) : fract (fract r) = fract r :=
by rw fract_eq_fract; exact ⟨-⌊r⌋, by unfold fract;simp⟩

theorem fract_add (r s : α) : ∃ z : ℤ, fract (r + s) - fract r - fract s = z :=
⟨⌊r⌋ + ⌊s⌋ - ⌊r + s⌋, by unfold fract; simp⟩

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

/-- `ceil x` is the smallest integer `z` such that `x ≤ z` -/
def ceil (x : α) : ℤ := -⌊-x⌋

notation `⌈` x `⌉` := ceil x

theorem ceil_le {z : ℤ} {x : α} : ⌈x⌉ ≤ z ↔ x ≤ z :=
by rw [ceil, neg_le, le_floor, int.cast_neg, neg_le_neg_iff]

theorem lt_ceil {x : α} {z : ℤ} : z < ⌈x⌉ ↔ (z:α) < x :=
lt_iff_lt_of_le_iff_le ceil_le

theorem le_ceil (x : α) : x ≤ ⌈x⌉ :=
ceil_le.1 (le_refl _)

@[simp] theorem ceil_coe (z : ℤ) : ⌈(z:α)⌉ = z :=
by rw [ceil, ← int.cast_neg, floor_coe, neg_neg]

theorem ceil_mono {a b : α} (h : a ≤ b) : ⌈a⌉ ≤ ⌈b⌉ :=
ceil_le.2 (le_trans h (le_ceil _))

@[simp] theorem ceil_add_int (x : α) (z : ℤ) : ⌈x + z⌉ = ⌈x⌉ + z :=
by rw [ceil, neg_add', floor_sub_int, neg_sub, sub_eq_neg_add]; refl

theorem ceil_sub_int (x : α) (z : ℤ) : ⌈x - z⌉ = ⌈x⌉ - z :=
eq.trans (by rw [int.cast_neg]; refl) (ceil_add_int _ _)

theorem ceil_lt_add_one (x : α) : (⌈x⌉ : α) < x + 1 :=
by rw [← lt_ceil, ← int.cast_one, ceil_add_int]; apply lt_add_one

lemma ceil_pos {a : α} : 0 < ⌈a⌉ ↔ 0 < a :=
⟨ λ h, have ⌊-a⌋ < 0, from neg_of_neg_pos h,
  pos_of_neg_neg $ lt_of_not_ge $ (not_iff_not_of_iff floor_nonneg).1 $ not_le_of_gt this,
 λ h, have -a < 0, from neg_neg_of_pos h,
  neg_pos_of_neg $ lt_of_not_ge $ (not_iff_not_of_iff floor_nonneg).2 $ not_le_of_gt this ⟩

@[simp] theorem ceil_zero : ⌈(0 : α)⌉ = 0 := by simp [ceil]

lemma ceil_nonneg [decidable_rel ((<) : α → α → Prop)] {q : α} (hq : q ≥ 0) : ⌈q⌉ ≥ 0 :=
if h : q > 0 then le_of_lt $ ceil_pos.2 h
else by rw [le_antisymm (le_of_not_lt h) hq, ceil_zero]; trivial

end

class archimedean (α) [ordered_comm_monoid α] : Prop :=
(arch : ∀ (x : α) {y}, 0 < y → ∃ n : ℕ, x ≤ n • y)

theorem exists_nat_gt [linear_ordered_semiring α] [archimedean α]
  (x : α) : ∃ n : ℕ, x < n :=
let ⟨n, h⟩ := archimedean.arch x zero_lt_one in
⟨n+1, lt_of_le_of_lt (by rwa ← add_monoid.smul_one)
  (nat.cast_lt.2 (nat.lt_succ_self _))⟩

section linear_ordered_ring
variables [linear_ordered_ring α] [archimedean α]

lemma pow_unbounded_of_gt_one (x : α) {y : α}
    (hy1 : 1 < y) : ∃ n : ℕ, x < y ^ n :=
have hy0 : 0 <  y - 1 := sub_pos_of_lt hy1,
let ⟨n, h⟩ := archimedean.arch x hy0 in
⟨n, calc x ≤ n • (y - 1)     : h
       ... < 1 + n • (y - 1) : by rw add_comm; exact lt_add_one _
       ... ≤ y ^ n           : pow_ge_one_add_sub_mul (le_of_lt hy1) _⟩

theorem exists_int_gt (x : α) : ∃ n : ℤ, x < n :=
let ⟨n, h⟩ := exists_nat_gt x in ⟨n, by rwa ← coe_coe⟩

theorem exists_int_lt (x : α) : ∃ n : ℤ, (n : α) < x :=
let ⟨n, h⟩ := exists_int_gt (-x) in ⟨-n, by rw int.cast_neg; exact neg_lt.1 h⟩

theorem exists_floor (x : α) :
  ∃ (fl : ℤ), ∀ (z : ℤ), z ≤ fl ↔ (z : α) ≤ x :=
begin
  haveI := classical.prop_decidable,
  have : ∃ (ub : ℤ), (ub:α) ≤ x ∧ ∀ (z : ℤ), (z:α) ≤ x → z ≤ ub :=
  int.exists_greatest_of_bdd
    (let ⟨n, hn⟩ := exists_int_gt x in ⟨n, λ z h',
      int.cast_le.1 $ le_trans h' $ le_of_lt hn⟩)
    (let ⟨n, hn⟩ := exists_int_lt x in ⟨n, le_of_lt hn⟩),
  refine this.imp (λ fl h z, _),
  cases h with h₁ h₂,
  exact ⟨λ h, le_trans (int.cast_le.2 h) h₁, h₂ z⟩,
end

end linear_ordered_ring

section linear_ordered_field

variables [linear_ordered_field α] [floor_ring α]

lemma sub_floor_div_mul_nonneg (x : α) {y : α} (hy : 0 < y) :
  0 ≤ x - ⌊x / y⌋ * y :=
begin
  conv in x {rw ← div_mul_cancel x (ne_of_lt hy).symm},
  rw ← sub_mul,
  exact mul_nonneg (sub_nonneg.2 (floor_le _)) (le_of_lt hy)
end

lemma sub_floor_div_mul_lt (x : α) {y : α} (hy : 0 < y) :
  x - ⌊x / y⌋ * y < y :=
sub_lt_iff_lt_add.2 begin
  conv in y {rw ← one_mul y},
  conv in x {rw ← div_mul_cancel x (ne_of_lt hy).symm},
  rw ← add_mul,
  exact (mul_lt_mul_right hy).2 (by rw add_comm; exact lt_floor_add_one _),
end

end linear_ordered_field

instance : archimedean ℕ :=
⟨λ n m m0, ⟨n, by simpa only [mul_one, nat.smul_eq_mul] using nat.mul_le_mul_left n m0⟩⟩

instance : archimedean ℤ :=
⟨λ n m m0, ⟨n.to_nat, le_trans (int.le_to_nat _) $
by simpa only [add_monoid.smul_eq_mul, int.nat_cast_eq_coe_nat, zero_add, mul_one] using mul_le_mul_of_nonneg_left
    (int.add_one_le_iff.2 m0) (int.coe_zero_le n.to_nat)⟩⟩

noncomputable def archimedean.floor_ring (α)
  [linear_ordered_ring α] [archimedean α] : floor_ring α :=
{ floor := λ x, classical.some (exists_floor x),
  le_floor := λ z x, classical.some_spec (exists_floor x) z }

section linear_ordered_field
variables [linear_ordered_field α]

theorem archimedean_iff_nat_lt :
  archimedean α ↔ ∀ x : α, ∃ n : ℕ, x < n :=
⟨@exists_nat_gt α _, λ H, ⟨λ x y y0,
  (H (x / y)).imp $ λ n h, le_of_lt $
  by rwa [div_lt_iff y0, ← add_monoid.smul_eq_mul] at h⟩⟩

theorem archimedean_iff_nat_le :
  archimedean α ↔ ∀ x : α, ∃ n : ℕ, x ≤ n :=
archimedean_iff_nat_lt.trans
⟨λ H x, (H x).imp $ λ _, le_of_lt,
 λ H x, let ⟨n, h⟩ := H x in ⟨n+1,
   lt_of_le_of_lt h (nat.cast_lt.2 (lt_add_one _))⟩⟩

theorem exists_rat_gt [archimedean α] (x : α) : ∃ q : ℚ, x < q :=
let ⟨n, h⟩ := exists_nat_gt x in ⟨n, by rwa rat.cast_coe_nat⟩

theorem archimedean_iff_rat_lt :
  archimedean α ↔ ∀ x : α, ∃ q : ℚ, x < q :=
⟨@exists_rat_gt α _,
  λ H, archimedean_iff_nat_lt.2 $ λ x,
  let ⟨q, h⟩ := H x in
  ⟨rat.nat_ceil q, lt_of_lt_of_le h $
    by simpa only [rat.cast_coe_nat] using (@rat.cast_le α _ _ _).2 (rat.le_nat_ceil _)⟩⟩

theorem archimedean_iff_rat_le :
  archimedean α ↔ ∀ x : α, ∃ q : ℚ, x ≤ q :=
archimedean_iff_rat_lt.trans
⟨λ H x, (H x).imp $ λ _, le_of_lt,
 λ H x, let ⟨n, h⟩ := H x in ⟨n+1,
   lt_of_le_of_lt h (rat.cast_lt.2 (lt_add_one _))⟩⟩

variable [archimedean α]

theorem exists_rat_lt (x : α) : ∃ q : ℚ, (q : α) < x :=
let ⟨n, h⟩ := exists_int_lt x in ⟨n, by rwa rat.cast_coe_int⟩

theorem exists_rat_btwn {x y : α} (h : x < y) : ∃ q : ℚ, x < q ∧ (q:α) < y :=
begin
  cases exists_nat_gt (y - x)⁻¹ with n nh,
  cases exists_floor (x * n) with z zh,
  refine ⟨(z + 1 : ℤ) / n, _⟩,
  have n0 := nat.cast_pos.1 (lt_trans (inv_pos (sub_pos.2 h)) nh),
  have n0' := (@nat.cast_pos α _ _).2 n0,
  rw [rat.cast_div_of_ne_zero, rat.cast_coe_nat, rat.cast_coe_int, div_lt_iff n0'],
  refine ⟨(lt_div_iff n0').2 $
    (lt_iff_lt_of_le_iff_le (zh _)).1 (lt_add_one _), _⟩,
  rw [int.cast_add, int.cast_one],
  refine lt_of_le_of_lt (add_le_add_right ((zh _).1 (le_refl _)) _) _,
  rwa [← lt_sub_iff_add_lt', ← sub_mul,
       ← div_lt_iff' (sub_pos.2 h), one_div_eq_inv],
  { rw [rat.coe_int_denom, nat.cast_one], exact one_ne_zero },
  { intro H, rw [rat.coe_nat_num, ← coe_coe, nat.cast_eq_zero] at H, subst H, cases n0 },
  { rw [rat.coe_nat_denom, nat.cast_one], exact one_ne_zero }
end

theorem exists_nat_one_div_lt {ε : α} (hε : ε > 0) : ∃ n : ℕ, 1 / (n + 1: α) < ε :=
begin
  cases archimedean_iff_nat_lt.1 (by apply_instance) (1/ε) with n hn,
  existsi n,
  apply div_lt_of_mul_lt_of_pos,
  { simp, apply add_pos_of_pos_of_nonneg zero_lt_one, apply nat.cast_nonneg },
  { apply (div_lt_iff' hε).1,
    transitivity,
    { exact hn },
    { simp [zero_lt_one] }}
end

theorem exists_pos_rat_lt {x : α} (x0 : 0 < x) : ∃ q : ℚ, 0 < q ∧ (q : α) < x :=
by simpa only [rat.cast_pos] using exists_rat_btwn x0

include α
@[simp] theorem rat.cast_floor (x : ℚ) :
  by haveI := archimedean.floor_ring α; exact ⌊(x:α)⌋ = ⌊x⌋ :=
begin
  haveI := archimedean.floor_ring α,
  apply le_antisymm,
  { rw [le_floor, ← @rat.cast_le α, rat.cast_coe_int],
    apply floor_le },
  { rw [le_floor, ← rat.cast_coe_int, rat.cast_le],
    apply floor_le }
end

end linear_ordered_field

section
variables [discrete_linear_ordered_field α] [archimedean α]

theorem exists_rat_near (x : α) {ε : α} (ε0 : ε > 0) :
  ∃ q : ℚ, abs (x - q) < ε :=
let ⟨q, h₁, h₂⟩ := exists_rat_btwn $
  lt_trans ((sub_lt_self_iff x).2 ε0) ((lt_add_iff_pos_left x).2 ε0) in
⟨q, abs_sub_lt_iff.2 ⟨sub_lt.1 h₁, sub_lt_iff_lt_add.2 h₂⟩⟩

end

instance : archimedean ℚ :=
archimedean_iff_rat_le.2 $ λ q, ⟨q, by rw rat.cast_id⟩
