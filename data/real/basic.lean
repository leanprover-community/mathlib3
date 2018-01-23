/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

The (classical) real numbers ℝ. This is a direct construction
from Cauchy sequences.
-/
import data.real.cau_seq algebra.big_operators data.nat.prime

def real := quotient (@cau_seq.equiv ℚ _ _ _ abs _)
notation `ℝ` := real

namespace real
open rat cau_seq

def mk : cau_seq ℚ abs → ℝ := quotient.mk

@[simp] theorem mk_eq_mk (f) : @eq ℝ ⟦f⟧ (mk f) := rfl

theorem mk_eq {f g} : mk f = mk g ↔ f ≈ g := quotient.eq

def of_rat (x : ℚ) : ℝ := mk (const abs x)

instance : has_zero ℝ := ⟨of_rat 0⟩
instance : has_one ℝ := ⟨of_rat 1⟩
instance : inhabited ℝ := ⟨0⟩

theorem of_rat_zero : of_rat 0 = 0 := rfl
theorem of_rat_one : of_rat 1 = 1 := rfl

@[simp] theorem mk_eq_zero {f} : mk f = 0 ↔ lim_zero f :=
by have : mk f = 0 ↔ lim_zero (f - 0) := quotient.eq;
   rwa sub_zero at this

instance : has_add ℝ :=
⟨λ x y, quotient.lift_on₂ x y (λ f g, mk (f + g)) $
  λ f₁ g₁ f₂ g₂ hf hg, quotient.sound $
  by simpa [(≈), setoid.r] using add_lim_zero hf hg⟩

@[simp] theorem mk_add (f g : cau_seq ℚ abs) : mk f + mk g = mk (f + g) := rfl 

instance : has_neg ℝ :=
⟨λ x, quotient.lift_on x (λ f, mk (-f)) $
  λ f₁ f₂ hf, quotient.sound $
  by simpa [(≈), setoid.r] using neg_lim_zero hf⟩

@[simp] theorem mk_neg (f : cau_seq ℚ abs) : -mk f = mk (-f) := rfl 

instance : has_mul ℝ :=
⟨λ x y, quotient.lift_on₂ x y (λ f g, mk (f * g)) $
  λ f₁ g₁ f₂ g₂ hf hg, quotient.sound $
  by simpa [(≈), setoid.r, mul_add, mul_comm] using
    add_lim_zero (mul_lim_zero g₁ hf) (mul_lim_zero f₂ hg)⟩

@[simp] theorem mk_mul (f g : cau_seq ℚ abs) : mk f * mk g = mk (f * g) := rfl 

theorem of_rat_add (x y : ℚ) : of_rat (x + y) = of_rat x + of_rat y :=
congr_arg mk (const_add _ _)

theorem of_rat_neg (x : ℚ) : of_rat (-x) = -of_rat x :=
congr_arg mk (const_neg _)

theorem of_rat_mul (x y : ℚ) : of_rat (x * y) = of_rat x * of_rat y :=
congr_arg mk (const_mul _ _)

instance : comm_ring ℝ :=
by refine { neg := has_neg.neg,
    add := (+), zero := 0, mul := (*), one := 1, .. };
  { repeat {refine λ a, quotient.induction_on a (λ _, _)},
    simp [show 0 = mk 0, from rfl, show 1 = mk 1, from rfl,
          mul_left_comm, mul_comm, mul_add] }

instance : semigroup ℝ      := by apply_instance
instance : monoid ℝ         := by apply_instance
instance : comm_semigroup ℝ := by apply_instance
instance : comm_monoid ℝ    := by apply_instance
instance : add_monoid ℝ     := by apply_instance
instance : add_group ℝ      := by apply_instance
instance : add_comm_group ℝ := by apply_instance
instance : ring ℝ           := by apply_instance

theorem of_rat_sub (x y : ℚ) : of_rat (x - y) = of_rat x - of_rat y :=
congr_arg mk (const_sub _ _)

instance : has_lt ℝ :=
⟨λ x y, quotient.lift_on₂ x y (<) $
  λ f₁ g₁ f₂ g₂ hf hg, propext $
  ⟨λ h, lt_of_eq_of_lt (setoid.symm hf) (lt_of_lt_of_eq h hg),
   λ h, lt_of_eq_of_lt hf (lt_of_lt_of_eq h (setoid.symm hg))⟩⟩

@[simp] theorem mk_lt {f g : cau_seq ℚ abs} : mk f < mk g ↔ f < g := iff.rfl

@[simp] theorem mk_pos {f : cau_seq ℚ abs} : 0 < mk f ↔ pos f :=
iff_of_eq (congr_arg pos (sub_zero f))

instance : has_le ℝ := ⟨λ x y, x < y ∨ x = y⟩

@[simp] theorem mk_le {f g : cau_seq ℚ abs} : mk f ≤ mk g ↔ f ≤ g :=
or_congr iff.rfl quotient.eq

theorem add_lt_add_iff_left {a b : ℝ} (c : ℝ) : c + a < c + b ↔ a < b :=
quotient.induction_on₃ a b c (λ f g h,
  iff_of_eq (congr_arg pos $ by rw add_sub_add_left_eq_sub))

instance : linear_order ℝ :=
{ le := (≤), lt := (<),
  le_refl := λ a, or.inr rfl,
  le_trans := λ a b c, quotient.induction_on₃ a b c $
    λ f g h, by simpa using le_trans,
  lt_iff_le_not_le := λ a b, quotient.induction_on₂ a b $
    λ f g, by simpa using lt_iff_le_not_le,
  le_antisymm := λ a b, quotient.induction_on₂ a b $
    λ f g, by simpa [mk_eq] using @cau_seq.le_antisymm _ _ f g,
  le_total := λ a b, quotient.induction_on₂ a b $
    λ f g, by simpa using le_total f g }

instance : partial_order ℝ := by apply_instance
instance : preorder ℝ      := by apply_instance

theorem of_rat_lt {x y : ℚ} : of_rat x < of_rat y ↔ x < y := const_lt

protected theorem zero_lt_one : (0 : ℝ) < 1 := of_rat_lt.2 zero_lt_one

protected theorem mul_pos {a b : ℝ} : 0 < a → 0 < b → 0 < a * b :=
quotient.induction_on₂ a b $ λ f g, by simpa using cau_seq.mul_pos

instance : linear_ordered_comm_ring ℝ :=
{ add_le_add_left := λ a b h c,
    (le_iff_le_iff_lt_iff_lt.2 $ real.add_lt_add_iff_left c).2 h,
  zero_ne_one := ne_of_lt real.zero_lt_one,
  mul_nonneg := λ a b a0 b0,
    match a0, b0 with
    | or.inl a0, or.inl b0 := le_of_lt (real.mul_pos a0 b0)
    | or.inr a0, _ := by simp [a0.symm]
    | _, or.inr b0 := by simp [b0.symm]
    end,
  mul_pos := @real.mul_pos,
  zero_lt_one := real.zero_lt_one,
  add_lt_add_left := λ a b h c, (real.add_lt_add_iff_left c).2 h,
  ..real.comm_ring, ..real.linear_order }

instance : linear_ordered_ring ℝ        := by apply_instance
instance : ordered_ring ℝ               := by apply_instance
instance : ordered_comm_group ℝ         := by apply_instance
instance : ordered_cancel_comm_monoid ℝ := by apply_instance
instance : integral_domain ℝ            := by apply_instance
instance : domain ℝ                     := by apply_instance

local attribute [instance] classical.prop_decidable

noncomputable instance : has_inv ℝ :=
⟨λ x, quotient.lift_on x
  (λ f, mk $ if h : lim_zero f then 0 else inv f h) $
λ f g fg, begin
  have := lim_zero_congr fg,
  by_cases hf : lim_zero f,
  { simp [hf, this.1 hf, setoid.refl] },
  { have hg := mt this.2 hf, simp [hf, hg],
    have If : mk (inv f hf) * mk f = 1 := mk_eq.2 (inv_mul_cancel hf),
    have Ig : mk (inv g hg) * mk g = 1 := mk_eq.2 (inv_mul_cancel hg),
    rw [mk_eq.2 fg, ← Ig] at If,
    rw mul_comm at Ig,
    rw [← mul_one (mk (inv f hf)), ← Ig, ← mul_assoc, If,
        mul_assoc, Ig, mul_one] }
end⟩

@[simp] theorem inv_zero : (0 : ℝ)⁻¹ = 0 :=
congr_arg mk $ by rw dif_pos; [refl, exact zero_lim_zero]

@[simp] theorem inv_mk {f} (hf) : (mk f)⁻¹ = mk (inv f hf) :=
congr_arg mk $ by rw dif_neg

protected theorem inv_mul_cancel {x : ℝ} : x ≠ 0 → x⁻¹ * x = 1 :=
quotient.induction_on x $ λ f hf, begin
  simp at hf, simp [hf],
  exact quotient.sound (cau_seq.inv_mul_cancel hf)
end

noncomputable instance : discrete_linear_ordered_field ℝ :=
{ inv            := has_inv.inv,
  inv_mul_cancel := @real.inv_mul_cancel,
  mul_inv_cancel := λ x x0, by rw [mul_comm, real.inv_mul_cancel x0],
  inv_zero       := inv_zero,
  decidable_le   := by apply_instance,
  ..real.linear_ordered_comm_ring }

noncomputable instance : linear_ordered_field ℝ   := by apply_instance
noncomputable instance : decidable_linear_ordered_comm_ring ℝ  := by apply_instance
noncomputable instance : decidable_linear_ordered_comm_group ℝ := by apply_instance
noncomputable instance : decidable_linear_order ℝ := by apply_instance
noncomputable instance : discrete_field ℝ         := by apply_instance
noncomputable instance : field ℝ                  := by apply_instance
noncomputable instance : division_ring ℝ          := by apply_instance

@[simp] theorem of_rat_eq_cast : ∀ x : ℚ, of_rat x = x :=
eq_cast of_rat rfl of_rat_add of_rat_mul

theorem le_mk_of_forall_le (x : ℝ) (f : cau_seq ℚ abs) :
  (∃ i, ∀ j ≥ i, x ≤ f j) → x ≤ mk f :=
quotient.induction_on x $ λ g h, le_of_not_lt $
λ ⟨K, K0, hK⟩,
let ⟨i, H⟩ := exists_forall_ge_and h $
  exists_forall_ge_and hK (f.cauchy₃ $ half_pos K0) in
begin
  apply not_lt_of_le (H _ (le_refl _)).1,
  rw ← of_rat_eq_cast,
  refine ⟨_, half_pos K0, i, λ j ij, _⟩,
  have := add_le_add (H _ ij).2.1
    (le_of_lt (abs_lt.1 $ (H _ (le_refl _)).2.2 _ ij).1),
  rwa [← sub_eq_add_neg, sub_self_div_two, sub_apply, sub_add_sub_cancel] at this
end

theorem mk_le_of_forall_le (f : cau_seq ℚ abs) (x : ℝ) :
  (∃ i, ∀ j ≥ i, (f j : ℝ) ≤ x) → mk f ≤ x
| ⟨i, H⟩ := by rw [← neg_le_neg_iff, mk_neg]; exact
  le_mk_of_forall_le _ _ ⟨i, λ j ij, by simp [H _ ij]⟩

theorem mk_near_of_forall_near (f : cau_seq ℚ abs) (x : ℝ) {ε : ℝ}
  (H : ∃ i, ∀ j ≥ i, abs ((f j : ℝ) - x) ≤ ε) : abs (mk f - x) ≤ ε :=
abs_sub_le_iff.2
  ⟨sub_le_iff_le_add'.2 $ mk_le_of_forall_le _ _ $
    H.imp $ λ i h j ij, sub_le_iff_le_add'.1 (abs_sub_le_iff.1 $ h j ij).1,
  sub_le.1 $ le_mk_of_forall_le _ _ $
    H.imp $ λ i h j ij, sub_le.1 (abs_sub_le_iff.1 $ h j ij).2⟩

theorem exists_rat_gt (x : ℝ) : ∃ n : ℚ, x < n :=
quotient.induction_on x $ λ f,
let ⟨M, M0, H⟩ := f.bounded' 0 in
⟨M + 1, by rw ← of_rat_eq_cast; exact
  ⟨1, zero_lt_one, 0, λ i _, le_sub_iff_add_le'.2 $
    (add_le_add_iff_right _).2 $ le_of_lt (abs_lt.1 (H i)).2⟩⟩

theorem exists_nat_gt (x : ℝ) : ∃ n : ℕ, x < n :=
let ⟨q, h⟩ := exists_rat_gt x in
⟨nat_ceil q, lt_of_lt_of_le h $ 
   by simpa using (@rat.cast_le ℝ _ _ _).2 (le_nat_ceil _)⟩

theorem exists_int_gt (x : ℝ) : ∃ n : ℤ, x < n :=
let ⟨n, h⟩ := exists_nat_gt x in ⟨n, by simp [h]⟩

theorem exists_int_lt (x : ℝ) : ∃ n : ℤ, (n:ℝ) < x :=
let ⟨n, h⟩ := exists_int_gt (-x) in ⟨-n, by simp [neg_lt.1 h]⟩

theorem exists_rat_lt (x : ℝ) : ∃ n : ℚ, (n:ℝ) < x :=
let ⟨n, h⟩ := exists_int_gt (-x) in ⟨-n, by simp [neg_lt.1 h]⟩

theorem exists_pos_rat_lt {x : ℝ} (x0 : 0 < x) : ∃ q : ℚ, 0 < q ∧ (q:ℝ) < x :=
let ⟨n, h⟩ := exists_nat_gt x⁻¹ in
⟨n.succ⁻¹, inv_pos (nat.cast_pos.2 (nat.succ_pos n)), begin
  rw [rat.cast_inv, inv_eq_one_div,
      div_lt_iff, mul_comm, ← div_lt_iff x0, one_div_eq_inv],
  { apply lt_trans h, simp [zero_lt_one] },
  { simp [-nat.cast_succ, nat.succ_pos] }
end⟩

theorem exists_rat_near' (x : ℝ) {ε : ℚ} (ε0 : ε > 0) :
  ∃ q : ℚ, abs (x - q) < ε :=
quotient.induction_on x $ λ f,
let ⟨i, hi⟩ := f.cauchy (half_pos ε0) in ⟨f i, begin
  rw [← of_rat_eq_cast, ← of_rat_eq_cast],
  refine abs_lt.2 ⟨_, _⟩;
    refine mk_lt.2 ⟨_, half_pos ε0, i, λ j ij, _⟩; simp;
    rw [← sub_le_iff_le_add', ← neg_sub, sub_self_div_two],
  { exact le_of_lt (abs_lt.1 (hi _ ij)).1 },
  { have := le_of_lt (abs_lt.1 (hi _ ij)).2,
    rwa [← neg_sub, neg_le] at this }
end⟩

theorem exists_rat_near (x : ℝ) {ε : ℝ} (ε0 : ε > 0) :
  ∃ q : ℚ, abs (x - q) < ε :=
let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0,
    ⟨q, h⟩ := exists_rat_near' x δ0 in ⟨q, lt_trans h δε⟩

theorem exists_rat_btwn {x y : ℝ} (h : x < y) : ∃ q : ℚ, x < q ∧ (q:ℝ) < y :=
let ⟨q, h⟩ := exists_rat_near (x + (y - x) / 2) (half_pos (sub_pos.2 h)),
    ⟨h₁, h₂⟩ := abs_lt.1 h in begin
  refine ⟨q, _, _⟩,
  { rwa [sub_lt_iff_lt_add', add_lt_add_iff_right] at h₂ },
  { rwa [neg_lt_sub_iff_lt_add, add_assoc, add_halves, add_sub_cancel'_right] at h₁ }
end

theorem is_cau_seq_iff_lift {f : ℕ → ℚ} : is_cau_seq abs f ↔ is_cau_seq abs (λ i, (f i : ℝ)) :=
⟨λ H ε ε0,
  let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0 in
  (H _ δ0).imp $ λ i hi j ij, lt_trans
    (by simpa using (@rat.cast_lt ℝ _ _ _).2 (hi _ ij)) δε,
 λ H ε ε0, (H _ (rat.cast_pos.2 ε0)).imp $
   λ i hi j ij, (@rat.cast_lt ℝ _ _ _).1 $ by simpa using hi _ ij⟩

theorem of_near (f : ℕ → ℚ) (x : ℝ)
  (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, abs ((f j : ℝ) - x) < ε) :
  ∃ h', mk ⟨f, h'⟩ = x :=
⟨is_cau_seq_iff_lift.2 (of_near _ (const abs x) h),
 sub_eq_zero.1 $ abs_eq_zero.1 $
  eq_of_le_of_forall_le_of_dense (abs_nonneg _) $ λ ε ε0,
    mk_near_of_forall_near _ _ $
    (h _ ε0).imp (λ i h j ij, le_of_lt (h j ij))⟩

theorem exists_floor (x : ℝ) : ∃ (ub : ℤ), (ub:ℝ) ≤ x ∧ 
   ∀ (z : ℤ), (z:ℝ) ≤ x → z ≤ ub :=
int.exists_greatest_of_bdd
  (let ⟨n, hn⟩ := exists_int_gt x in ⟨n, λ z h',
    int.cast_le.1 $ le_trans h' $ le_of_lt hn⟩)
  (let ⟨n, hn⟩ := exists_int_lt x in ⟨n, le_of_lt hn⟩)

/-- `floor x` is the largest integer `z` such that `z ≤ x` -/
noncomputable def floor (x : ℝ) : ℤ := classical.some (exists_floor x)

notation `⌊` x `⌋` := floor x

theorem le_floor {z : ℤ} {x : ℝ} : z ≤ ⌊x⌋ ↔ (z : ℝ) ≤ x :=
let ⟨h₁, h₂⟩ := classical.some_spec (exists_floor x) in
⟨λ h, le_trans (int.cast_le.2 h) h₁, h₂ z⟩

theorem floor_lt {x : ℝ} {z : ℤ} : ⌊x⌋ < z ↔ x < z :=
le_iff_le_iff_lt_iff_lt.1 le_floor

theorem floor_le (x : ℝ) : (⌊x⌋ : ℝ) ≤ x :=
le_floor.1 (le_refl _)

theorem floor_nonneg {x : ℝ} : 0 ≤ ⌊x⌋ ↔ 0 ≤ x :=
by simpa using @le_floor 0 x

theorem lt_succ_floor (x : ℝ) : x < ⌊x⌋.succ :=
floor_lt.1 $ int.lt_succ_self _

theorem lt_floor_add_one (x : ℝ) : x < ⌊x⌋ + 1 :=
by simpa [int.succ] using lt_succ_floor x

theorem sub_one_lt_floor (x : ℝ) : x - 1 < ⌊x⌋ :=
sub_lt_iff_lt_add.2 (lt_floor_add_one x)

@[simp] theorem floor_coe (z : ℤ) : ⌊z⌋ = z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor, int.cast_le]

theorem floor_mono {a b : ℝ} (h : a ≤ b) : ⌊a⌋ ≤ ⌊b⌋ :=
le_floor.2 (le_trans (floor_le _) h)

@[simp] theorem floor_add_int (x : ℝ) (z : ℤ) : ⌊x + z⌋ = ⌊x⌋ + z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor,
  ← sub_le_iff_le_add, ← sub_le_iff_le_add, le_floor, int.cast_sub]

theorem floor_sub_int (x : ℝ) (z : ℤ) : ⌊x - z⌋ = ⌊x⌋ - z :=
eq.trans (by rw [int.cast_neg]; refl) (floor_add_int _ _)

/-- `ceil x` is the smallest integer `z` such that `x ≤ z` -/
noncomputable def ceil (x : ℝ) : ℤ := -⌊-x⌋

notation `⌈` x `⌉` := ceil x

theorem ceil_le {z : ℤ} {x : ℝ} : ⌈x⌉ ≤ z ↔ x ≤ z :=
by rw [ceil, neg_le, le_floor, int.cast_neg, neg_le_neg_iff]

theorem lt_ceil {x : ℝ} {z : ℤ} : z < ⌈x⌉ ↔ (z:ℝ) < x :=
le_iff_le_iff_lt_iff_lt.1 ceil_le

theorem le_ceil (x : ℝ) : x ≤ ⌈x⌉ :=
ceil_le.1 (le_refl _)

@[simp] theorem ceil_coe (z : ℤ) : ⌈z⌉ = z :=
by rw [ceil, ← int.cast_neg, floor_coe, neg_neg]

theorem ceil_mono {a b : ℝ} (h : a ≤ b) : ⌈a⌉ ≤ ⌈b⌉ :=
ceil_le.2 (le_trans h (le_ceil _))

@[simp] theorem ceil_add_int (x : ℝ) (z : ℤ) : ⌈x + z⌉ = ⌈x⌉ + z :=
by rw [ceil, neg_add', floor_sub_int, neg_sub, sub_eq_neg_add]; refl

theorem ceil_sub_int (x : ℝ) (z : ℤ) : ⌈x - z⌉ = ⌈x⌉ - z :=
eq.trans (by rw [int.cast_neg]; refl) (ceil_add_int _ _)

theorem ceil_lt_add_one (x : ℝ) : (⌈x⌉ : ℝ) < x + 1 :=
by rw [← lt_ceil, ← int.cast_one, ceil_add_int]; apply lt_add_one

theorem exists_sup (S : set ℝ) : (∃ x, x ∈ S) → (∃ x, ∀ y ∈ S, y ≤ x) →
  ∃ x, ∀ y, x ≤ y ↔ ∀ z ∈ S, z ≤ y
| ⟨L, hL⟩ ⟨U, hU⟩ := begin
  have,
  { refine λ d : ℕ, @int.exists_greatest_of_bdd
      (λ n, ∃ y ∈ S, (n:ℝ) ≤ y * d) _ _ _,
    { cases exists_int_gt U with k hk,
      refine ⟨k * d, λ z h, _⟩,
      rcases h with ⟨y, yS, hy⟩,
      refine int.cast_le.1 (le_trans hy _),
      simp,
      exact mul_le_mul_of_nonneg_right
        (le_trans (hU _ yS) (le_of_lt hk)) (nat.cast_nonneg _) },
    { exact ⟨⌊L * d⌋, L, hL, floor_le _⟩ } },
  cases classical.axiom_of_choice this with f hf,
  dsimp at f hf,
  have hf₁ : ∀ n > 0, ∃ y ∈ S, ((f n / n:ℚ):ℝ) ≤ y := λ n n0,
    let ⟨y, yS, hy⟩ := (hf n).1 in
    ⟨y, yS, by simpa using (div_le_iff (nat.cast_pos.2 n0)).2 hy⟩,
  have hf₂ : ∀ (n > 0) (y ∈ S), (y - (n:ℕ)⁻¹ : ℝ) < (f n / n:ℚ),
  { intros n n0 y yS,
    have := lt_of_lt_of_le (sub_one_lt_floor _)
      (int.cast_le.2 $ (hf n).2 _ ⟨y, yS, floor_le _⟩),
    simp [-sub_eq_add_neg],
    rwa [lt_div_iff (nat.cast_pos.2 n0), sub_mul, _root_.inv_mul_cancel],
    exact ne_of_gt (nat.cast_pos.2 n0) },
  suffices hg, let g : cau_seq ℚ abs := ⟨λ n, f n / n, hg⟩,
  refine ⟨mk g, λ y, ⟨λ h x xS, le_trans _ h, λ h, _⟩⟩,
  { refine le_of_forall_ge_of_dense (λ z xz, _),
    cases exists_nat_gt (x - z)⁻¹ with K hK,
    refine le_mk_of_forall_le _ _ ⟨K, λ n nK, _⟩,
    replace xz := sub_pos.2 xz,
    replace hK := le_trans (le_of_lt hK) (nat.cast_le.2 nK),
    have n0 : 0 < n := nat.cast_pos.1 (lt_of_lt_of_le (inv_pos xz) hK),
    refine le_trans _ (le_of_lt $ hf₂ _ n0 _ xS),
    rwa [le_sub, inv_le (nat.cast_pos.2 n0) xz] },
  { exact mk_le_of_forall_le _ _ ⟨1, λ n n1,
      let ⟨x, xS, hx⟩ := hf₁ _ n1 in le_trans hx (h _ xS)⟩ },
  intros ε ε0,
  suffices : ∀ j k ≥ nat_ceil ε⁻¹, (f j / j - f k / k : ℚ) < ε,
  { refine ⟨_, λ j ij, abs_lt.2 ⟨_, this _ _ ij (le_refl _)⟩⟩,
    rw [neg_lt, neg_sub], exact this _ _ (le_refl _) ij },
  intros j k ij ik,
  replace ij := le_trans (le_nat_ceil _) (nat.cast_le.2 ij),
  replace ik := le_trans (le_nat_ceil _) (nat.cast_le.2 ik),
  have j0 := nat.cast_pos.1 (lt_of_lt_of_le (inv_pos ε0) ij),
  have k0 := nat.cast_pos.1 (lt_of_lt_of_le (inv_pos ε0) ik),
  rcases hf₁ _ j0 with ⟨y, yS, hy⟩,
  refine lt_of_lt_of_le ((@rat.cast_lt ℝ _ _ _).1 _)
    ((inv_le ε0 (nat.cast_pos.2 k0)).1 ik),
  simpa using sub_lt_iff_lt_add'.2
    (lt_of_le_of_lt hy $ sub_lt_iff_lt_add.1 $ hf₂ _ k0 _ yS)
end

noncomputable def Sup (S : set ℝ) : ℝ :=
if h : (∃ x, x ∈ S) ∧ (∃ x, ∀ y ∈ S, y ≤ x)
then classical.some (exists_sup S h.1 h.2) else 0

theorem Sup_le (S : set ℝ) (h₁ : ∃ x, x ∈ S) (h₂ : ∃ x, ∀ y ∈ S, y ≤ x)
  {y} : Sup S ≤ y ↔ ∀ z ∈ S, z ≤ y :=
by simp [Sup, h₁, h₂]; exact
classical.some_spec (exists_sup S h₁ h₂) y

theorem lt_Sup (S : set ℝ) (h₁ : ∃ x, x ∈ S) (h₂ : ∃ x, ∀ y ∈ S, y ≤ x)
  {y} : y < Sup S ↔ ∃ z ∈ S, y < z :=
by simpa [not_forall] using not_congr (@Sup_le S h₁ h₂ y)

theorem le_Sup (S : set ℝ) (h₂ : ∃ x, ∀ y ∈ S, y ≤ x) {x} (xS : x ∈ S) : x ≤ Sup S :=
(Sup_le S ⟨_, xS⟩ h₂).1 (le_refl _) _ xS

theorem Sup_le_ub (S : set ℝ) (h₁ : ∃ x, x ∈ S) {ub} (h₂ : ∀ y ∈ S, y ≤ ub) : Sup S ≤ ub :=
(Sup_le S h₁ ⟨_, h₂⟩).2 h₂

noncomputable def Inf (S : set ℝ) : ℝ := -Sup {x | -x ∈ S}

theorem le_Inf (S : set ℝ) (h₁ : ∃ x, x ∈ S) (h₂ : ∃ x, ∀ y ∈ S, x ≤ y)
  {y} : y ≤ Inf S ↔ ∀ z ∈ S, y ≤ z :=
begin
  refine le_neg.trans ((Sup_le _ _ _).trans _),
  { cases h₁ with x xS, exact ⟨-x, by simp [xS]⟩ },
  { cases h₂ with ub h, exact ⟨-ub, λ y hy, le_neg.1 $ h _ hy⟩ },
  split; intros H z hz,
  { exact neg_le_neg_iff.1 (H _ $ by simp [hz]) },
  { exact le_neg.2 (H _ hz) }
end

theorem Inf_lt (S : set ℝ) (h₁ : ∃ x, x ∈ S) (h₂ : ∃ x, ∀ y ∈ S, x ≤ y)
  {y} : Inf S < y ↔ ∃ z ∈ S, z < y :=
by simpa [not_forall] using not_congr (@le_Inf S h₁ h₂ y)

theorem Inf_le (S : set ℝ) (h₂ : ∃ x, ∀ y ∈ S, x ≤ y) {x} (xS : x ∈ S) : Inf S ≤ x :=
(le_Inf S ⟨_, xS⟩ h₂).1 (le_refl _) _ xS

theorem lb_le_Inf (S : set ℝ) (h₁ : ∃ x, x ∈ S) {lb} (h₂ : ∀ y ∈ S, lb ≤ y) : lb ≤ Inf S :=
(le_Inf S h₁ ⟨_, h₂⟩).2 h₂

theorem cau_seq_converges (f : cau_seq ℝ abs) : ∃ x, f ≈ const abs x :=
begin
  let S := {x : ℝ | const abs x < f},
  have lb : ∃ x, x ∈ S := exists_lt f,
  have ub' : ∀ x, f < const abs x → ∀ y ∈ S, y ≤ x :=
    λ x h y yS, le_of_lt $ const_lt.1 $ cau_seq.lt_trans yS h,
  have ub : ∃ x, ∀ y ∈ S, y ≤ x := (exists_gt f).imp ub',
  refine ⟨Sup S,
    ((lt_total _ _).resolve_left (λ h, _)).resolve_right (λ h, _)⟩,
  { rcases h with ⟨ε, ε0, i, ih⟩,
    refine not_lt_of_le (Sup_le_ub S lb (ub' _ _))
      ((sub_lt_self_iff _).2 (half_pos ε0)),
    refine ⟨_, half_pos ε0, i, λ j ij, _⟩,
    rw [sub_apply, const_apply, sub_right_comm,
      le_sub_iff_add_le, add_halves],
    exact ih _ ij },
  { rcases h with ⟨ε, ε0, i, ih⟩,
    refine not_lt_of_le (le_Sup S ub _)
      ((lt_add_iff_pos_left _).2 (half_pos ε0)),
    refine ⟨_, half_pos ε0, i, λ j ij, _⟩,
    rw [sub_apply, const_apply, add_comm, ← sub_sub,
      le_sub_iff_add_le, add_halves],
    exact ih _ ij }
end

noncomputable def lim (f : cau_seq ℝ abs) : ℝ :=
classical.some (cau_seq_converges f)

theorem equiv_lim (f : cau_seq ℝ abs) : f ≈ const abs (lim f) :=
classical.some_spec (cau_seq_converges f)

theorem sqrt_exists : ∀ {x : ℝ}, 0 ≤ x → ∃ y, 0 ≤ y ∧ y * y = x :=
suffices H : ∀ {x : ℝ}, 0 < x → x ≤ 1 → ∃ y, 0 < y ∧ y * y = x, begin
  intros x x0, cases x0,
  cases le_total x 1 with x1 x1,
  { rcases H x0 x1 with ⟨y, y0, hy⟩,
    exact ⟨y, le_of_lt y0, hy⟩ },
  { have := (inv_le_inv x0 zero_lt_one).2 x1,
    rw inv_one at this,
    rcases H (inv_pos x0) this with ⟨y, y0, hy⟩,
    refine ⟨y⁻¹, le_of_lt (inv_pos y0), _⟩, rw [← mul_inv', hy, inv_inv'] },
  { exact ⟨0, by simp [x0.symm]⟩ }
end,
λ x x0 x1, begin
  let S := {y | 0 < y ∧ y * y ≤ x},
  have lb : x ∈ S := ⟨x0, by simpa using (mul_le_mul_right x0).2 x1⟩,
  have ub : ∀ y ∈ S, (y:ℝ) ≤ 1,
  { intros y yS, cases yS with y0 yx,
    refine (mul_self_le_mul_self_iff (le_of_lt y0) zero_le_one).2 _,
    simpa using le_trans yx x1 },
  have S0 : 0 < Sup S := lt_of_lt_of_le x0 (le_Sup _ ⟨_, ub⟩ lb),
  refine ⟨Sup S, S0, le_antisymm (not_lt.1 $ λ h, _) (not_lt.1 $ λ h, _)⟩,
  { rw [← div_lt_iff S0, lt_Sup S ⟨_, lb⟩ ⟨_, ub⟩] at h,
    rcases h with ⟨y, yS, hy⟩, rcases yS with ⟨y0, yx⟩,
    rw [div_lt_iff S0, ← div_lt_iff' y0, lt_Sup S ⟨_, lb⟩ ⟨_, ub⟩] at hy,
    rcases hy with ⟨z, zS, hz⟩, rcases zS with ⟨z0, zx⟩,
    rw [div_lt_iff y0] at hz,
    exact not_lt_of_lt
      ((mul_lt_mul_right y0).1 (lt_of_le_of_lt yx hz))
      ((mul_lt_mul_left z0).1 (lt_of_le_of_lt zx hz)) },
  { let s := Sup S, let y := s + (x - s * s) / 3,
    replace h : 0 < x - s * s := sub_pos.2 h,
    have _30 := bit1_pos zero_le_one,
    have : s < y := (lt_add_iff_pos_right _).2 (div_pos h _30),
    refine not_le_of_lt this (le_Sup S ⟨_, ub⟩ ⟨lt_trans S0 this, _⟩),
    rw [add_mul_self_eq, add_assoc, ← le_sub_iff_add_le', ← add_mul,
      ← le_div_iff (div_pos h _30), div_div_cancel (ne_of_gt h)],
    apply add_le_add,
    { simpa using (mul_le_mul_left (@two_pos ℝ _)).2 (Sup_le_ub _ ⟨_, lb⟩ ub) },
    { rw [div_le_one_iff_le _30],
      refine le_trans (sub_le_self _ (mul_self_nonneg _)) (le_trans x1 _),
      exact (le_add_iff_nonneg_left _).2 (le_of_lt two_pos) } }
end

def sqrt_aux (f : cau_seq ℚ abs) : ℕ → ℚ
| 0       := rat.mk_nat (f 0).num.to_nat.sqrt (f 0).denom.sqrt 
| (n + 1) := let s := sqrt_aux n in max 0 $ (s + f (n+1) / s) / 2

theorem sqrt_aux_nonneg (f : cau_seq ℚ abs) : ∀ i : ℕ, 0 ≤ sqrt_aux f i
| 0       := by rw [sqrt_aux, mk_nat_eq, mk_eq_div];
  apply div_nonneg'; exact int.cast_nonneg.2 (int.of_nat_nonneg _)
| (n + 1) := le_max_left _ _

/- TODO(Mario): finish the proof
theorem sqrt_aux_converges (f : cau_seq ℚ abs) : ∃ h x, 0 ≤ x ∧ x * x = max 0 (mk f) ∧
  mk ⟨sqrt_aux f, h⟩ = x :=
begin
  rcases sqrt_exists (le_max_left 0 (mk f)) with ⟨x, x0, hx⟩,
  suffices : ∃ h, mk ⟨sqrt_aux f, h⟩ = x,
  { exact this.imp (λ h e, ⟨x, x0, hx, e⟩) },
  apply of_near,

  suffices : ∃ δ > 0, ∀ i, abs (↑(sqrt_aux f i) - x) < δ / 2 ^ i,
  { rcases this with ⟨δ, δ0, hδ⟩,
    intros,
     }
end -/

noncomputable def sqrt (x : ℝ) : ℝ :=
classical.some (sqrt_exists (le_max_left 0 x))
/-quotient.lift_on x
  (λ f, mk ⟨sqrt_aux f, (sqrt_aux_converges f).fst⟩)
  (λ f g e, begin
    rcases sqrt_aux_converges f with ⟨hf, x, x0, xf, xs⟩,
    rcases sqrt_aux_converges g with ⟨hg, y, y0, yg, ys⟩,
    refine xs.trans (eq.trans _ ys.symm),
    rw [← @mul_self_inj_of_nonneg ℝ _ x y x0 y0, xf, yg],
    congr_n 1, exact quotient.sound e
  end)-/

theorem sqrt_prop (x : ℝ) : 0 ≤ sqrt x ∧ sqrt x * sqrt x = max 0 x :=
classical.some_spec (sqrt_exists (le_max_left 0 x))
/-quotient.induction_on x $ λ f,
by rcases sqrt_aux_converges f with ⟨hf, _, x0, xf, rfl⟩; exact ⟨x0, xf⟩-/

theorem sqrt_eq_zero_of_nonpos {x : ℝ} (h : x ≤ 0) : sqrt x = 0 :=
eq_zero_of_mul_self_eq_zero $ (sqrt_prop x).2.trans $ max_eq_left h

theorem sqrt_nonneg (x : ℝ) : 0 ≤ sqrt x := (sqrt_prop x).1

@[simp] theorem mul_self_sqrt {x : ℝ} (h : 0 ≤ x) : sqrt x * sqrt x = x :=
(sqrt_prop x).2.trans (max_eq_right h)

@[simp] theorem sqrt_mul_self {x : ℝ} (h : 0 ≤ x) : sqrt (x * x) = x :=
(mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))

theorem sqrt_eq_iff_mul_self_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  sqrt x = y ↔ y * y = x :=
⟨λ h, by rw [← h, mul_self_sqrt hx],
 λ h, by rw [← h, sqrt_mul_self hy]⟩

local infix ` ^ ` := monoid.pow

@[simp] theorem sqr_sqrt {x : ℝ} (h : 0 ≤ x) : sqrt x ^ 2 = x :=
by rw [pow_two, mul_self_sqrt h]

@[simp] theorem sqrt_sqr {x : ℝ} (h : 0 ≤ x) : sqrt (x ^ 2) = x :=
by rw [pow_two, sqrt_mul_self h]

theorem sqrt_eq_iff_sqr_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  sqrt x = y ↔ y ^ 2 = x :=
by rw [pow_two, sqrt_eq_iff_mul_self_eq hx hy]

theorem sqrt_mul_self_eq_abs (x : ℝ) : sqrt (x * x) = abs x :=
(le_total 0 x).elim
  (λ h, (sqrt_mul_self h).trans (abs_of_nonneg h).symm)
  (λ h, by rw [← neg_mul_neg,
    sqrt_mul_self (neg_nonneg.2 h), abs_of_nonpos h])

theorem sqrt_sqr_eq_abs (x : ℝ) : sqrt (x ^ 2) = abs x :=
by rw [pow_two, sqrt_mul_self_eq_abs]

@[simp] theorem sqrt_zero : sqrt 0 = 0 :=
by simpa using sqrt_mul_self (le_refl _)

@[simp] theorem sqrt_one : sqrt 1 = 1 :=
by simpa using sqrt_mul_self zero_le_one

@[simp] theorem sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x ≤ sqrt y ↔ x ≤ y :=
by rw [mul_self_le_mul_self_iff (sqrt_nonneg _) (sqrt_nonneg _),
       mul_self_sqrt hx, mul_self_sqrt hy]

@[simp] theorem sqrt_lt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x < sqrt y ↔ x < y :=
le_iff_le_iff_lt_iff_lt.1 (sqrt_le hy hx)

@[simp] theorem sqrt_inj {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x = sqrt y ↔ x = y :=
by simp [le_antisymm_iff, hx, hy]

@[simp] theorem sqrt_eq_zero {x : ℝ} (h : 0 ≤ x) : sqrt x = 0 ↔ x = 0 :=
by simpa using sqrt_inj h (le_refl _)

theorem sqrt_eq_zero' {x : ℝ} : sqrt x = 0 ↔ x ≤ 0 :=
(le_total x 0).elim
  (λ h, by simp [h, sqrt_eq_zero_of_nonpos])
  (λ h, by simp [h]; simp [le_antisymm_iff, h])

@[simp] theorem sqrt_pos {x : ℝ} : 0 < sqrt x ↔ 0 < x :=
le_iff_le_iff_lt_iff_lt.1 (iff.trans
  (by simp [le_antisymm_iff, sqrt_nonneg]) sqrt_eq_zero')

@[simp] theorem sqrt_mul' (x) {y : ℝ} (hy : 0 ≤ y) : sqrt (x * y) = sqrt x * sqrt y :=
begin
  cases le_total 0 x with hx hx,
  { refine (mul_self_inj_of_nonneg _ (mul_nonneg _ _)).1 _; try {apply sqrt_nonneg},
    rw [mul_self_sqrt (mul_nonneg hx hy), mul_assoc,
        mul_left_comm (sqrt y), mul_self_sqrt hy, ← mul_assoc, mul_self_sqrt hx] },
  { rw [sqrt_eq_zero'.2 (mul_nonpos_of_nonpos_of_nonneg hx hy),
        sqrt_eq_zero'.2 hx, zero_mul] }
end

@[simp] theorem sqrt_mul {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : sqrt (x * y) = sqrt x * sqrt y :=
by rw [mul_comm, sqrt_mul' _ hx, mul_comm]

@[simp] theorem sqrt_inv (x : ℝ) : sqrt x⁻¹ = (sqrt x)⁻¹ :=
(le_or_lt x 0).elim
  (λ h, by simp [sqrt_eq_zero'.2, inv_nonpos, h])
  (λ h, by rw [
    ← mul_self_inj_of_nonneg (sqrt_nonneg _) (le_of_lt $ inv_pos $ sqrt_pos.2 h),
    mul_self_sqrt (le_of_lt $ inv_pos h), ← mul_inv', mul_self_sqrt (le_of_lt h)])

@[simp] theorem sqrt_div {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : sqrt (x / y) = sqrt x / sqrt y :=
by rw [division_def, sqrt_mul hx, sqrt_inv]; refl

end real
