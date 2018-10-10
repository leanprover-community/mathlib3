/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

The (classical) real numbers ℝ. This is a direct construction
from Cauchy sequences.
-/
import order.conditionally_complete_lattice data.real.cau_seq_completion
  algebra.big_operators algebra.archimedean order.bounds

def real := @cau_seq.completion.Cauchy ℚ _ _ _ abs _
notation `ℝ` := real
local attribute [reducible] real

namespace real
open cau_seq cau_seq.completion

def of_rat (x : ℚ) : ℝ := of_rat x

instance : comm_ring ℝ := cau_seq.completion.comm_ring

/- Extra instances to short-circuit type class resolution -/
instance : ring ℝ               := by apply_instance
instance : comm_semiring ℝ      := by apply_instance
instance : semiring ℝ           := by apply_instance
instance : add_comm_group ℝ     := by apply_instance
instance : add_group ℝ          := by apply_instance
instance : add_comm_monoid ℝ    := by apply_instance
instance : add_monoid ℝ         := by apply_instance
instance : add_left_cancel_semigroup ℝ := by apply_instance
instance : add_right_cancel_semigroup ℝ := by apply_instance
instance : add_comm_semigroup ℝ := by apply_instance
instance : add_semigroup ℝ      := by apply_instance
instance : comm_monoid ℝ        := by apply_instance
instance : monoid ℝ             := by apply_instance
instance : comm_semigroup ℝ     := by apply_instance
instance : semigroup ℝ          := by apply_instance
instance : inhabited ℝ := ⟨0⟩

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

/- Extra instances to short-circuit type class resolution -/
instance : linear_ordered_ring ℝ        := by apply_instance
instance : ordered_ring ℝ               := by apply_instance
instance : linear_ordered_semiring ℝ    := by apply_instance
instance : ordered_semiring ℝ           := by apply_instance
instance : ordered_comm_group ℝ         := by apply_instance
instance : ordered_cancel_comm_monoid ℝ := by apply_instance
instance : ordered_comm_monoid ℝ        := by apply_instance
instance : domain ℝ                     := by apply_instance

local attribute [instance] classical.prop_decidable

noncomputable instance : discrete_linear_ordered_field ℝ :=
{ inv            := has_inv.inv,
  inv_mul_cancel := @cau_seq.completion.inv_mul_cancel _ _ _ _ _ _,
  mul_inv_cancel := λ x x0, by rw [mul_comm, cau_seq.completion.inv_mul_cancel x0],
  inv_zero       := inv_zero,
  decidable_le   := by apply_instance,
  ..real.linear_ordered_comm_ring }

/- Extra instances to short-circuit type class resolution -/
noncomputable instance : linear_ordered_field ℝ    := by apply_instance
noncomputable instance : decidable_linear_ordered_comm_ring ℝ := by apply_instance
noncomputable instance : decidable_linear_ordered_semiring ℝ := by apply_instance
noncomputable instance : decidable_linear_ordered_comm_group ℝ := by apply_instance
noncomputable instance real.discrete_field : discrete_field ℝ          := by apply_instance
noncomputable instance : field ℝ                   := by apply_instance
noncomputable instance : division_ring ℝ           := by apply_instance
noncomputable instance : integral_domain ℝ         := by apply_instance
noncomputable instance : nonzero_comm_ring ℝ       := by apply_instance
noncomputable instance : decidable_linear_order ℝ  := by apply_instance
noncomputable instance : lattice.distrib_lattice ℝ := by apply_instance
noncomputable instance : lattice.lattice ℝ         := by apply_instance
noncomputable instance : lattice.semilattice_inf ℝ := by apply_instance
noncomputable instance : lattice.semilattice_sup ℝ := by apply_instance
noncomputable instance : lattice.has_inf ℝ         := by apply_instance
noncomputable instance : lattice.has_sup ℝ         := by apply_instance

open rat

@[simp] theorem of_rat_eq_cast : ∀ x : ℚ, of_rat x = x :=
eq_cast of_rat rfl of_rat_add of_rat_mul

theorem le_mk_of_forall_le {x : ℝ} {f : cau_seq ℚ abs} :
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

theorem mk_le_of_forall_le {f : cau_seq ℚ abs} {x : ℝ} :
  (∃ i, ∀ j ≥ i, (f j : ℝ) ≤ x) → mk f ≤ x
| ⟨i, H⟩ := by rw [← neg_le_neg_iff, mk_neg]; exact
  le_mk_of_forall_le ⟨i, λ j ij, by simp [H _ ij]⟩

theorem mk_near_of_forall_near {f : cau_seq ℚ abs} {x : ℝ} {ε : ℝ}
  (H : ∃ i, ∀ j ≥ i, abs ((f j : ℝ) - x) ≤ ε) : abs (mk f - x) ≤ ε :=
abs_sub_le_iff.2
  ⟨sub_le_iff_le_add'.2 $ mk_le_of_forall_le $
    H.imp $ λ i h j ij, sub_le_iff_le_add'.1 (abs_sub_le_iff.1 $ h j ij).1,
  sub_le.1 $ le_mk_of_forall_le $
    H.imp $ λ i h j ij, sub_le.1 (abs_sub_le_iff.1 $ h j ij).2⟩

instance : archimedean ℝ :=
archimedean_iff_rat_le.2 $ λ x, quotient.induction_on x $ λ f,
let ⟨M, M0, H⟩ := f.bounded' 0 in
⟨M, mk_le_of_forall_le ⟨0, λ i _,
  rat.cast_le.2 $ le_of_lt (abs_lt.1 (H i)).2⟩⟩

noncomputable instance : floor_ring ℝ := archimedean.floor_ring _

theorem is_cau_seq_iff_lift {f : ℕ → ℚ} : is_cau_seq abs f ↔ is_cau_seq abs (λ i, (f i : ℝ)) :=
⟨λ H ε ε0,
  let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0 in
  (H _ δ0).imp $ λ i hi j ij, lt_trans
    (by simpa using (@rat.cast_lt ℝ _ _ _).2 (hi _ ij)) δε,
 λ H ε ε0, (H _ (rat.cast_pos.2 ε0)).imp $
   λ i hi j ij, (@rat.cast_lt ℝ _ _ _).1 $ by simpa using hi _ ij⟩

theorem of_near (f : ℕ → ℚ) (x : ℝ)
  (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, abs ((f j : ℝ) - x) < ε) :
  ∃ h', cau_seq.completion.mk ⟨f, h'⟩ = x :=
⟨is_cau_seq_iff_lift.2 (of_near _ (const abs x) h),
 sub_eq_zero.1 $ abs_eq_zero.1 $
  eq_of_le_of_forall_le_of_dense (abs_nonneg _) $ λ ε ε0,
    mk_near_of_forall_near $
    (h _ ε0).imp (λ i h j ij, le_of_lt (h j ij))⟩

theorem exists_floor (x : ℝ) : ∃ (ub : ℤ), (ub:ℝ) ≤ x ∧
   ∀ (z : ℤ), (z:ℝ) ≤ x → z ≤ ub :=
int.exists_greatest_of_bdd
  (let ⟨n, hn⟩ := exists_int_gt x in ⟨n, λ z h',
    int.cast_le.1 $ le_trans h' $ le_of_lt hn⟩)
  (let ⟨n, hn⟩ := exists_int_lt x in ⟨n, le_of_lt hn⟩)

theorem exists_sup (S : set ℝ) : (∃ x, x ∈ S) → (∃ x, ∀ y ∈ S, y ≤ x) →
  ∃ x, ∀ y, x ≤ y ↔ ∀ z ∈ S, z ≤ y
| ⟨L, hL⟩ ⟨U, hU⟩ := begin
  choose f hf using begin
    refine λ d : ℕ, @int.exists_greatest_of_bdd
      (λ n, ∃ y ∈ S, (n:ℝ) ≤ y * d) _ _ _,
    { cases exists_int_gt U with k hk,
      refine ⟨k * d, λ z h, _⟩,
      rcases h with ⟨y, yS, hy⟩,
      refine int.cast_le.1 (le_trans hy _),
      simp,
      exact mul_le_mul_of_nonneg_right
        (le_trans (hU _ yS) (le_of_lt hk)) (nat.cast_nonneg _) },
    { exact ⟨⌊L * d⌋, L, hL, floor_le _⟩ }
  end,
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
    refine le_mk_of_forall_le ⟨K, λ n nK, _⟩,
    replace xz := sub_pos.2 xz,
    replace hK := le_trans (le_of_lt hK) (nat.cast_le.2 nK),
    have n0 : 0 < n := nat.cast_pos.1 (lt_of_lt_of_le (inv_pos xz) hK),
    refine le_trans _ (le_of_lt $ hf₂ _ n0 _ xS),
    rwa [le_sub, inv_le (nat.cast_pos.2 n0) xz] },
  { exact mk_le_of_forall_le ⟨1, λ n n1,
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

protected lemma is_lub_Sup {s : set ℝ} {a b : ℝ} (ha : a ∈ s) (hb : b ∈ upper_bounds s) :
  is_lub s (Sup s) :=
⟨λ x xs, real.le_Sup s ⟨_, hb⟩ xs,
 λ u h, real.Sup_le_ub _ ⟨_, ha⟩ h⟩

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

open lattice
noncomputable instance lattice : lattice ℝ := by apply_instance

noncomputable instance : conditionally_complete_linear_order ℝ :=
{ Sup := real.Sup,
  Inf := real.Inf,
  le_cSup :=
    assume (s : set ℝ) (a : ℝ) (_ : bdd_above s) (_ : a ∈ s),
    show a ≤ Sup s,
      from le_Sup s ‹bdd_above s› ‹a ∈ s›,
  cSup_le :=
    assume (s : set ℝ) (a : ℝ) (_ : s ≠ ∅) (H : ∀b∈s, b ≤ a),
    show Sup s ≤ a,
      from Sup_le_ub s (set.exists_mem_of_ne_empty ‹s ≠ ∅›) H,
  cInf_le :=
    assume (s : set ℝ) (a : ℝ) (_ : bdd_below s) (_ : a ∈ s),
    show Inf s ≤ a,
      from Inf_le s ‹bdd_below s› ‹a ∈ s›,
  le_cInf :=
    assume (s : set ℝ) (a : ℝ) (_ : s ≠ ∅) (H : ∀b∈s, a ≤ b),
    show a ≤ Inf s,
      from lb_le_Inf s (set.exists_mem_of_ne_empty ‹s ≠ ∅›) H,
 ..real.linear_order, ..real.lattice}

theorem Sup_empty : lattice.Sup (∅ : set ℝ) = 0 := dif_neg $ by simp

theorem Sup_of_not_bdd_above {s : set ℝ} (hs : ¬ bdd_above s) : lattice.Sup s = 0 :=
dif_neg $ assume h, hs h.2

theorem Inf_empty : lattice.Inf (∅ : set ℝ) = 0 :=
show Inf ∅ = 0, by simp [Inf]; exact Sup_empty

theorem Inf_of_not_bdd_below {s : set ℝ} (hs : ¬ bdd_below s) : lattice.Inf s = 0 :=
have bdd_above {x | -x ∈ s} → bdd_below s, from
  assume ⟨b, hb⟩, ⟨-b, assume x hxs, neg_le.2 $ hb _ $ by simp [hxs]⟩,
have ¬ bdd_above {x | -x ∈ s}, from mt this hs,
neg_eq_zero.2 $ Sup_of_not_bdd_above $ this

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

noncomputable instance : cau_seq.is_complete ℝ abs :=
⟨ λ f, let ⟨x, hx⟩ := cau_seq_converges f in
  have lim_zero (const abs x - f), from lim_zero_sub_rev hx,
  ⟨x, this⟩ ⟩

section lim

open cau_seq

noncomputable def lim (f : ℕ → ℝ) : ℝ :=
if hf : is_cau_seq abs f then
  classical.some (cau_seq_converges ⟨f, hf⟩)
else 0

theorem equiv_lim (f : cau_seq ℝ abs) : f ≈ const abs (lim f) :=
by simp [lim, f.is_cau]; cases f with f hf;
   exact classical.some_spec (cau_seq_converges ⟨f, hf⟩)

lemma eq_lim_of_const_equiv {f : cau_seq ℝ abs} {x : ℝ} (h : cau_seq.const abs x ≈ f) : x = lim f :=
const_equiv.mp $ setoid.trans h $ equiv_lim f

lemma lim_eq_of_equiv_const {f : cau_seq ℝ abs} {x : ℝ} (h : f ≈ cau_seq.const abs x) : lim f = x :=
(eq_lim_of_const_equiv $ setoid.symm h).symm

lemma lim_eq_lim_of_equiv {f g : cau_seq ℝ abs} (h : f ≈ g) : lim f = lim g :=
lim_eq_of_equiv_const $ setoid.trans h $ equiv_lim g

@[simp] lemma lim_const (x : ℝ) : lim (const abs x) = x :=
lim_eq_of_equiv_const $ setoid.refl _

lemma lim_add (f g : cau_seq ℝ abs) : lim f + lim g = lim ⇑(f + g) :=
eq_lim_of_const_equiv $ show lim_zero (const abs (lim ⇑f + lim ⇑g) - (f + g)),
  by rw [const_add, add_sub_comm];
  exact add_lim_zero (setoid.symm (equiv_lim f)) (setoid.symm (equiv_lim g))

lemma lim_mul_lim (f g : cau_seq ℝ abs) : lim f * lim g = lim ⇑(f * g) :=
eq_lim_of_const_equiv $ show lim_zero (const abs (lim ⇑f * lim ⇑g) - f * g),
  from have h : const abs (lim ⇑f * lim ⇑g) - f * g = g * (const abs (lim f) - f)
      + const abs (lim f) * (const abs (lim g) - g) :=
    by simp [mul_sub, mul_comm, const_mul, mul_add],
  by rw h; exact add_lim_zero (mul_lim_zero _ (setoid.symm (equiv_lim f)))
      (mul_lim_zero _ (setoid.symm (equiv_lim g)))

lemma lim_mul (f : cau_seq ℝ abs) (x : ℝ) : lim f * x = lim ⇑(f * const abs x) :=
by rw [← lim_mul_lim, lim_const]

lemma lim_neg (f : cau_seq ℝ abs) : lim ⇑(-f) = -lim f :=
lim_eq_of_equiv_const (show lim_zero (-f - const abs (-lim ⇑f)),
  by rw [const_neg, sub_neg_eq_add, add_comm];
  exact setoid.symm (equiv_lim f))

lemma lim_eq_zero_iff (f : cau_seq ℝ abs) : lim f = 0 ↔ lim_zero f :=
⟨assume h,
  by have hf := equiv_lim f;
  rw h at hf;
  exact (lim_zero_congr hf).mpr (const_lim_zero.mpr rfl),
assume h,
  have h₁ : f = (f - const abs 0) := ext (λ n, by simp [sub_apply, const_apply]),
  by rw h₁ at h; exact lim_eq_of_equiv_const h ⟩

lemma lim_inv {f : cau_seq ℝ abs} (hf : ¬ lim_zero f) : lim ⇑(inv f hf) = (lim f)⁻¹ :=
have hl : lim f ≠ 0 := by rwa ← lim_eq_zero_iff at hf,
lim_eq_of_equiv_const $ show lim_zero (inv f hf - const abs (lim ⇑f)⁻¹),
  from have h₁ : ∀ (g f : cau_seq ℝ abs) (hf : ¬ lim_zero f), lim_zero (g - f * inv f hf * g) :=
    λ g f hf, by rw [← one_mul g, ← mul_assoc, ← sub_mul, mul_one, mul_comm, mul_comm f];
    exact mul_lim_zero _ (setoid.symm (cau_seq.inv_mul_cancel _)),
  have h₂ : lim_zero ((inv f hf - const abs (lim ⇑f)⁻¹) - (const abs (lim f) - f) *
      (inv f hf * const abs (lim ⇑f)⁻¹)) :=
    by rw [sub_mul, ← sub_add, sub_sub, sub_add_eq_sub_sub, sub_right_comm, sub_add];
    exact show lim_zero (inv f hf - const abs (lim ⇑f) * (inv f hf * const abs (lim ⇑f)⁻¹)
      - (const abs (lim ⇑f)⁻¹ - f * (inv f hf * const abs (lim ⇑f)⁻¹))),
    from sub_lim_zero
      (by rw [← mul_assoc, mul_right_comm, const_inv hl]; exact h₁ _ _ _)
      (by rw [← mul_assoc]; exact h₁ _ _ _),
  (lim_zero_congr h₂).mpr $ by rw mul_comm; exact mul_lim_zero _ (setoid.symm (equiv_lim f))

lemma lim_le {f : cau_seq ℝ abs} {x : ℝ}
  (h : f ≤ cau_seq.const abs x) : real.lim f ≤ x :=
cau_seq.const_le.1 $ cau_seq.le_of_eq_of_le (setoid.symm (real.equiv_lim f)) h

lemma le_lim {f : cau_seq ℝ abs} {x : ℝ}
  (h : cau_seq.const abs x ≤ f) : x ≤ real.lim f :=
cau_seq.const_le.1 $ cau_seq.le_of_le_of_eq h (real.equiv_lim f)

lemma lt_lim {f : cau_seq ℝ abs} {x : ℝ}
  (h : cau_seq.const abs x < f) : x < real.lim f :=
cau_seq.const_lt.1 $ cau_seq.lt_of_lt_of_eq h (real.equiv_lim f)

lemma lim_lt {f : cau_seq ℝ abs} {x : ℝ}
  (h : f < cau_seq.const abs x) : real.lim f < x :=
cau_seq.const_lt.1 $ cau_seq.lt_of_eq_of_lt (setoid.symm (real.equiv_lim f)) h

end lim

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
    rcases h with ⟨y, ⟨y0, yx⟩, hy⟩,
    rw [div_lt_iff S0, ← div_lt_iff' y0, lt_Sup S ⟨_, lb⟩ ⟨_, ub⟩] at hy,
    rcases hy with ⟨z, ⟨z0, zx⟩, hz⟩,
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
    congr' 1, exact quotient.sound e
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
lt_iff_lt_of_le_iff_le (sqrt_le hy hx)

@[simp] theorem sqrt_inj {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x = sqrt y ↔ x = y :=
by simp [le_antisymm_iff, hx, hy]

@[simp] theorem sqrt_eq_zero {x : ℝ} (h : 0 ≤ x) : sqrt x = 0 ↔ x = 0 :=
by simpa using sqrt_inj h (le_refl _)

theorem sqrt_eq_zero' {x : ℝ} : sqrt x = 0 ↔ x ≤ 0 :=
(le_total x 0).elim
  (λ h, by simp [h, sqrt_eq_zero_of_nonpos])
  (λ h, by simp [h]; simp [le_antisymm_iff, h])

@[simp] theorem sqrt_pos {x : ℝ} : 0 < sqrt x ↔ 0 < x :=
lt_iff_lt_of_le_iff_le (iff.trans
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
