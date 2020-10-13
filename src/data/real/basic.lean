/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn

The (classical) real numbers ℝ. This is a direct construction
from Cauchy sequences.
-/
import order.conditionally_complete_lattice
import data.real.cau_seq_completion
import algebra.archimedean

/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
def real := @cau_seq.completion.Cauchy ℚ _ _ _ abs _
notation `ℝ` := real

namespace real
open cau_seq cau_seq.completion

variables {x y : ℝ}

def comm_ring_aux : comm_ring ℝ := cau_seq.completion.comm_ring

instance : comm_ring ℝ := { ..comm_ring_aux }

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

/-- Coercion `ℚ` → `ℝ` as a `ring_hom`. Note that this
is `cau_seq.completion.of_rat`, not `rat.cast`. -/
def of_rat : ℚ →+* ℝ := ⟨of_rat, rfl, of_rat_mul, rfl, of_rat_add⟩

/-- Make a real number from a Cauchy sequence of rationals (by taking the equivalence class). -/
def mk (x : cau_seq ℚ abs) : ℝ := cau_seq.completion.mk x

theorem of_rat_sub (x y : ℚ) : of_rat (x - y) = of_rat x - of_rat y :=
congr_arg mk (const_sub _ _)

instance : has_lt ℝ :=
⟨λ x y, quotient.lift_on₂ x y (<) $
  λ f₁ g₁ f₂ g₂ hf hg, propext $
  ⟨λ h, lt_of_eq_of_lt (setoid.symm hf) (lt_of_lt_of_eq h hg),
   λ h, lt_of_eq_of_lt hf (lt_of_lt_of_eq h (setoid.symm hg))⟩⟩

@[simp] theorem mk_lt {f g : cau_seq ℚ abs} : mk f < mk g ↔ f < g := iff.rfl

theorem mk_eq {f g : cau_seq ℚ abs} : mk f = mk g ↔ f ≈ g := mk_eq

theorem quotient_mk_eq_mk (f : cau_seq ℚ abs) : ⟦f⟧ = mk f := rfl

theorem mk_eq_mk {f : cau_seq ℚ abs} : cau_seq.completion.mk f = mk f := rfl

@[simp] theorem mk_pos {f : cau_seq ℚ abs} : 0 < mk f ↔ pos f :=
iff_of_eq (congr_arg pos (sub_zero f))

protected def le (x y : ℝ) : Prop := x < y ∨ x = y
instance : has_le ℝ := ⟨real.le⟩

@[simp] theorem mk_le {f g : cau_seq ℚ abs} : mk f ≤ mk g ↔ f ≤ g :=
or_congr iff.rfl quotient.eq

theorem add_lt_add_iff_left {a b : ℝ} (c : ℝ) : c + a < c + b ↔ a < b :=
quotient.induction_on₃ a b c (λ f g h,
  iff_of_eq (congr_arg pos $ by rw add_sub_add_left_eq_sub))

instance : linear_order ℝ :=
{ le := (≤), lt := (<),
  le_refl := λ a, or.inr rfl,
  le_trans := λ a b c, quotient.induction_on₃ a b c $
    λ f g h, by simpa [quotient_mk_eq_mk] using le_trans,
  lt_iff_le_not_le := λ a b, quotient.induction_on₂ a b $
    λ f g, by simpa [quotient_mk_eq_mk] using lt_iff_le_not_le,
  le_antisymm := λ a b, quotient.induction_on₂ a b $
    λ f g, by simpa [mk_eq, quotient_mk_eq_mk] using @cau_seq.le_antisymm _ _ f g,
  le_total := λ a b, quotient.induction_on₂ a b $
    λ f g, by simpa [quotient_mk_eq_mk] using le_total f g }

instance : partial_order ℝ := by apply_instance
instance : preorder ℝ      := by apply_instance

theorem of_rat_lt {x y : ℚ} : of_rat x < of_rat y ↔ x < y := const_lt

protected theorem zero_lt_one : (0 : ℝ) < 1 := of_rat_lt.2 zero_lt_one

protected theorem mul_pos {a b : ℝ} : 0 < a → 0 < b → 0 < a * b :=
quotient.induction_on₂ a b $ λ f g,
  show pos (f - 0) → pos (g - 0) → pos (f * g - 0),
  by simpa using cau_seq.mul_pos

instance : linear_ordered_comm_ring ℝ :=
{ add_le_add_left := λ a b h c,
    (le_iff_le_iff_lt_iff_lt.2 $ real.add_lt_add_iff_left c).2 h,
  exists_pair_ne  := ⟨0, 1, ne_of_lt real.zero_lt_one⟩,
  mul_pos     := @real.mul_pos,
  zero_lt_one := real.zero_lt_one,
  .. real.comm_ring, .. real.linear_order, .. real.semiring }

/- Extra instances to short-circuit type class resolution -/
instance : linear_ordered_ring ℝ        := by apply_instance
instance : ordered_ring ℝ               := by apply_instance
instance : linear_ordered_semiring ℝ    := by apply_instance
instance : ordered_semiring ℝ           := by apply_instance
instance : ordered_add_comm_group ℝ     := by apply_instance
instance : ordered_cancel_add_comm_monoid ℝ := by apply_instance
instance : ordered_add_comm_monoid ℝ    := by apply_instance
instance : domain ℝ                     := by apply_instance
instance : has_one ℝ                    := by apply_instance
instance : has_zero ℝ                   := by apply_instance
instance : has_mul ℝ                    := by apply_instance
instance : has_add ℝ                    := by apply_instance
instance : has_sub ℝ                    := by apply_instance

open_locale classical

noncomputable instance : discrete_linear_ordered_field ℝ :=
{ decidable_le := by apply_instance,
  ..real.linear_ordered_comm_ring,
  ..real.domain,
  ..cau_seq.completion.field }

/- Extra instances to short-circuit type class resolution -/

noncomputable instance : linear_ordered_field ℝ    := by apply_instance
noncomputable instance : decidable_linear_ordered_comm_ring ℝ := by apply_instance
noncomputable instance : decidable_linear_ordered_semiring ℝ := by apply_instance
noncomputable instance : decidable_linear_ordered_add_comm_group ℝ := by apply_instance
noncomputable instance field : field ℝ := by apply_instance
noncomputable instance : division_ring ℝ           := by apply_instance
noncomputable instance : integral_domain ℝ         := by apply_instance
instance : nontrivial ℝ                            := by apply_instance
noncomputable instance : decidable_linear_order ℝ  := by apply_instance
noncomputable instance : distrib_lattice ℝ := by apply_instance
noncomputable instance : lattice ℝ         := by apply_instance
noncomputable instance : semilattice_inf ℝ := by apply_instance
noncomputable instance : semilattice_sup ℝ := by apply_instance
noncomputable instance : has_inf ℝ         := by apply_instance
noncomputable instance : has_sup ℝ         := by apply_instance
noncomputable instance decidable_lt (a b : ℝ) : decidable (a < b) := by apply_instance
noncomputable instance decidable_le (a b : ℝ) : decidable (a ≤ b) := by apply_instance
noncomputable instance decidable_eq (a b : ℝ) : decidable (a = b) := by apply_instance

lemma le_of_forall_epsilon_le {a b : real} (h : ∀ε, 0 < ε → a ≤ b + ε) : a ≤ b :=
le_of_forall_le_of_dense $ assume x hxb,
calc  a ≤ b + (x - b) : h (x-b) $ sub_pos.2 hxb
    ... = x : by rw [add_comm]; simp

open rat

@[simp] theorem of_rat_eq_cast : ∀ x : ℚ, of_rat x = x :=
of_rat.eq_rat_cast

theorem le_mk_of_forall_le {f : cau_seq ℚ abs} :
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
| ⟨i, H⟩ := by rw [← neg_le_neg_iff, ← mk_eq_mk, mk_neg]; exact
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

/- mark `real` irreducible in order to prevent `auto_cases` unfolding reals,
since users rarely want to consider real numbers as Cauchy sequences.
Marking `comm_ring_aux` `irreducible` is done to ensure that there are no problems
with non definitionally equal instances, caused by making `real` irreducible-/
attribute [irreducible] real comm_ring_aux

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
  ∃ h', real.mk ⟨f, h'⟩ = x :=
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
      (λ n, ∃ y ∈ S, (n:ℝ) ≤ y * d) _ _,
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
    ⟨y, yS, by simpa using (div_le_iff ((nat.cast_pos.2 n0):((_:ℝ) < _))).2 hy⟩,
  have hf₂ : ∀ (n > 0) (y ∈ S), (y - (n:ℕ)⁻¹ : ℝ) < (f n / n:ℚ),
  { intros n n0 y yS,
    have := lt_of_lt_of_le (sub_one_lt_floor _)
      (int.cast_le.2 $ (hf n).2 _ ⟨y, yS, floor_le _⟩),
    simp [-sub_eq_add_neg],
    rwa [lt_div_iff ((nat.cast_pos.2 n0):((_:ℝ) < _)), sub_mul, _root_.inv_mul_cancel],
    exact ne_of_gt (nat.cast_pos.2 n0) },
  suffices hg, let g : cau_seq ℚ abs := ⟨λ n, f n / n, hg⟩,
  refine ⟨mk g, λ y, ⟨λ h x xS, le_trans _ h, λ h, _⟩⟩,
  { refine le_of_forall_ge_of_dense (λ z xz, _),
    cases exists_nat_gt (x - z)⁻¹ with K hK,
    refine le_mk_of_forall_le ⟨K, λ n nK, _⟩,
    replace xz := sub_pos.2 xz,
    replace hK := le_trans (le_of_lt hK) (nat.cast_le.2 nK),
    have n0 : 0 < n := nat.cast_pos.1 (lt_of_lt_of_le (inv_pos.2 xz) hK),
    refine le_trans _ (le_of_lt $ hf₂ _ n0 _ xS),
    rwa [le_sub, inv_le ((nat.cast_pos.2 n0):((_:ℝ) < _)) xz] },
  { exact mk_le_of_forall_le ⟨1, λ n n1,
      let ⟨x, xS, hx⟩ := hf₁ _ n1 in le_trans hx (h _ xS)⟩ },
  intros ε ε0,
  suffices : ∀ j k ≥ nat_ceil ε⁻¹, (f j / j - f k / k : ℚ) < ε,
  { refine ⟨_, λ j ij, abs_lt.2 ⟨_, this _ _ ij (le_refl _)⟩⟩,
    rw [neg_lt, neg_sub], exact this _ _ (le_refl _) ij },
  intros j k ij ik,
  replace ij := le_trans (le_nat_ceil _) (nat.cast_le.2 ij),
  replace ik := le_trans (le_nat_ceil _) (nat.cast_le.2 ik),
  have j0 := nat.cast_pos.1 (lt_of_lt_of_le (inv_pos.2 ε0) ij),
  have k0 := nat.cast_pos.1 (lt_of_lt_of_le (inv_pos.2 ε0) ik),
  rcases hf₁ _ j0 with ⟨y, yS, hy⟩,
  refine lt_of_lt_of_le ((@rat.cast_lt ℝ _ _ _).1 _)
    ((inv_le ε0 (nat.cast_pos.2 k0)).1 ik),
  simpa using sub_lt_iff_lt_add'.2
    (lt_of_le_of_lt hy $ sub_lt_iff_lt_add.1 $ hf₂ _ k0 _ yS)
end

noncomputable instance : has_Sup ℝ :=
⟨λ S, if h : (∃ x, x ∈ S) ∧ (∃ x, ∀ y ∈ S, y ≤ x)
  then classical.some (exists_sup S h.1 h.2) else 0⟩

lemma Sup_def (S : set ℝ) :
  Sup S = if h : (∃ x, x ∈ S) ∧ (∃ x, ∀ y ∈ S, y ≤ x)
    then classical.some (exists_sup S h.1 h.2) else 0 := rfl

theorem Sup_le (S : set ℝ) (h₁ : ∃ x, x ∈ S) (h₂ : ∃ x, ∀ y ∈ S, y ≤ x)
  {y} : Sup S ≤ y ↔ ∀ z ∈ S, z ≤ y :=
by simp [Sup_def, h₁, h₂]; exact
classical.some_spec (exists_sup S h₁ h₂) y

section
-- this proof times out without this
local attribute [instance, priority 1000] classical.prop_decidable
theorem lt_Sup (S : set ℝ) (h₁ : ∃ x, x ∈ S) (h₂ : ∃ x, ∀ y ∈ S, y ≤ x)
  {y} : y < Sup S ↔ ∃ z ∈ S, y < z :=
by simpa [not_forall] using not_congr (@Sup_le S h₁ h₂ y)
end

theorem le_Sup (S : set ℝ) (h₂ : ∃ x, ∀ y ∈ S, y ≤ x) {x} (xS : x ∈ S) : x ≤ Sup S :=
(Sup_le S ⟨_, xS⟩ h₂).1 (le_refl _) _ xS

theorem Sup_le_ub (S : set ℝ) (h₁ : ∃ x, x ∈ S) {ub} (h₂ : ∀ y ∈ S, y ≤ ub) : Sup S ≤ ub :=
(Sup_le S h₁ ⟨_, h₂⟩).2 h₂

protected lemma is_lub_Sup {s : set ℝ} {a b : ℝ} (ha : a ∈ s) (hb : b ∈ upper_bounds s) :
  is_lub s (Sup s) :=
⟨λ x xs, real.le_Sup s ⟨_, hb⟩ xs,
 λ u h, real.Sup_le_ub _ ⟨_, ha⟩ h⟩

noncomputable instance : has_Inf ℝ := ⟨λ S, -Sup {x | -x ∈ S}⟩

lemma Inf_def (S : set ℝ) : Inf S = -Sup {x | -x ∈ S} := rfl

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

section
-- this proof times out without this
local attribute [instance, priority 1000] classical.prop_decidable
theorem Inf_lt (S : set ℝ) (h₁ : ∃ x, x ∈ S) (h₂ : ∃ x, ∀ y ∈ S, x ≤ y)
  {y} : Inf S < y ↔ ∃ z ∈ S, z < y :=
by simpa [not_forall] using not_congr (@le_Inf S h₁ h₂ y)
end

theorem Inf_le (S : set ℝ) (h₂ : ∃ x, ∀ y ∈ S, x ≤ y) {x} (xS : x ∈ S) : Inf S ≤ x :=
(le_Inf S ⟨_, xS⟩ h₂).1 (le_refl _) _ xS

theorem lb_le_Inf (S : set ℝ) (h₁ : ∃ x, x ∈ S) {lb} (h₂ : ∀ y ∈ S, lb ≤ y) : lb ≤ Inf S :=
(le_Inf S h₁ ⟨_, h₂⟩).2 h₂

noncomputable instance : conditionally_complete_linear_order ℝ :=
{ Sup := has_Sup.Sup,
  Inf := has_Inf.Inf,
  le_cSup :=
    assume (s : set ℝ) (a : ℝ) (_ : bdd_above s) (_ : a ∈ s),
    show a ≤ Sup s,
      from le_Sup s ‹bdd_above s› ‹a ∈ s›,
  cSup_le :=
    assume (s : set ℝ) (a : ℝ) (_ : s.nonempty) (H : ∀b∈s, b ≤ a),
    show Sup s ≤ a,
      from Sup_le_ub s ‹s.nonempty› H,
  cInf_le :=
    assume (s : set ℝ) (a : ℝ) (_ : bdd_below s) (_ : a ∈ s),
    show Inf s ≤ a,
      from Inf_le s ‹bdd_below s› ‹a ∈ s›,
  le_cInf :=
    assume (s : set ℝ) (a : ℝ) (_ : s.nonempty) (H : ∀b∈s, a ≤ b),
    show a ≤ Inf s,
      from lb_le_Inf s ‹s.nonempty› H,
  decidable_le := classical.dec_rel _,
 ..real.linear_order, ..real.lattice}

theorem Sup_empty : Sup (∅ : set ℝ) = 0 := dif_neg $ by simp

theorem Sup_of_not_bdd_above {s : set ℝ} (hs : ¬ bdd_above s) : Sup s = 0 :=
dif_neg $ assume h, hs h.2

theorem Sup_univ : Sup (@set.univ ℝ) = 0 :=
real.Sup_of_not_bdd_above $ λ ⟨x, h⟩, not_le_of_lt (lt_add_one _) $ h (set.mem_univ _)

theorem Inf_empty : Inf (∅ : set ℝ) = 0 :=
by simp [Inf_def, Sup_empty]

theorem Inf_of_not_bdd_below {s : set ℝ} (hs : ¬ bdd_below s) : Inf s = 0 :=
have bdd_above {x | -x ∈ s} → bdd_below s, from
  assume ⟨b, hb⟩, ⟨-b, assume x hxs, neg_le.2 $ hb $ by simp [hxs]⟩,
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

noncomputable instance : cau_seq.is_complete ℝ abs := ⟨cau_seq_converges⟩

theorem sqrt_exists : ∀ {x : ℝ}, 0 ≤ x → ∃ y, 0 ≤ y ∧ y * y = x :=
suffices H : ∀ {x : ℝ}, 0 < x → x ≤ 1 → ∃ y, 0 < y ∧ y * y = x, begin
  intros x x0, cases x0,
  cases le_total x 1 with x1 x1,
  { rcases H x0 x1 with ⟨y, y0, hy⟩,
    exact ⟨y, le_of_lt y0, hy⟩ },
  { have := (inv_le_inv x0 zero_lt_one).2 x1,
    rw inv_one at this,
    rcases H (inv_pos.2 x0) this with ⟨y, y0, hy⟩,
    refine ⟨y⁻¹, le_of_lt (inv_pos.2 y0), _⟩, rw [← mul_inv', hy, inv_inv'] },
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
      ← le_div_iff (div_pos h _30), div_div_cancel' (ne_of_gt h)],
    apply add_le_add,
    { simpa using (mul_le_mul_left (@zero_lt_two ℝ _)).2 (Sup_le_ub _ ⟨_, lb⟩ ub) },
    { rw [div_le_one _30],
      refine le_trans (sub_le_self _ (mul_self_nonneg _)) (le_trans x1 _),
      exact (le_add_iff_nonneg_left _).2 (le_of_lt zero_lt_two) } }
end

def sqrt_aux (f : cau_seq ℚ abs) : ℕ → ℚ
| 0       := rat.mk_nat (f 0).num.to_nat.sqrt (f 0).denom.sqrt
| (n + 1) := let s := sqrt_aux n in max 0 $ (s + f (n+1) / s) / 2

theorem sqrt_aux_nonneg (f : cau_seq ℚ abs) : ∀ i : ℕ, 0 ≤ sqrt_aux f i
| 0       := by rw [sqrt_aux, mk_nat_eq, mk_eq_div];
  apply div_nonneg; exact int.cast_nonneg.2 (int.of_nat_nonneg _)
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

/-- The square root of a real number. This returns 0 for negative inputs. -/
@[pp_nodot] noncomputable def sqrt (x : ℝ) : ℝ :=
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

theorem sqrt_eq_zero_of_nonpos (h : x ≤ 0) : sqrt x = 0 :=
eq_zero_of_mul_self_eq_zero $ (sqrt_prop x).2.trans $ max_eq_left h

theorem sqrt_nonneg (x : ℝ) : 0 ≤ sqrt x := (sqrt_prop x).1

@[simp] theorem mul_self_sqrt (h : 0 ≤ x) : sqrt x * sqrt x = x :=
(sqrt_prop x).2.trans (max_eq_right h)

@[simp] theorem sqrt_mul_self (h : 0 ≤ x) : sqrt (x * x) = x :=
(mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))

theorem sqrt_eq_iff_mul_self_eq (hx : 0 ≤ x) (hy : 0 ≤ y) :
  sqrt x = y ↔ y * y = x :=
⟨λ h, by rw [← h, mul_self_sqrt hx],
 λ h, by rw [← h, sqrt_mul_self hy]⟩

@[simp] theorem sqr_sqrt (h : 0 ≤ x) : sqrt x ^ 2 = x :=
by rw [pow_two, mul_self_sqrt h]

@[simp] theorem sqrt_sqr (h : 0 ≤ x) : sqrt (x ^ 2) = x :=
by rw [pow_two, sqrt_mul_self h]

theorem sqrt_eq_iff_sqr_eq (hx : 0 ≤ x) (hy : 0 ≤ y) :
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

@[simp] theorem sqrt_le (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x ≤ sqrt y ↔ x ≤ y :=
by rw [mul_self_le_mul_self_iff (sqrt_nonneg _) (sqrt_nonneg _),
       mul_self_sqrt hx, mul_self_sqrt hy]

@[simp] theorem sqrt_lt (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x < sqrt y ↔ x < y :=
lt_iff_lt_of_le_iff_le (sqrt_le hy hx)

lemma sqrt_le_sqrt (h : x ≤ y) : sqrt x ≤ sqrt y :=
begin
  rw [mul_self_le_mul_self_iff (sqrt_nonneg _) (sqrt_nonneg _), (sqrt_prop _).2, (sqrt_prop _).2],
  exact max_le_max (le_refl _) h
end

lemma sqrt_le_left (hy : 0 ≤ y) : sqrt x ≤ y ↔ x ≤ y ^ 2 :=
begin
  rw [mul_self_le_mul_self_iff (sqrt_nonneg _) hy, pow_two],
  cases le_total 0 x with hx hx,
  { rw [mul_self_sqrt hx] },
  { have h1 : 0 ≤ y * y := mul_nonneg hy hy,
    have h2 : x ≤ y * y := le_trans hx h1,
    simp [sqrt_eq_zero_of_nonpos, hx, h1, h2] }
end

/- note: if you want to conclude `x ≤ sqrt y`, then use `le_sqrt_of_sqr_le`.
   if you have `x > 0`, consider using `le_sqrt'` -/
lemma le_sqrt (hx : 0 ≤ x) (hy : 0 ≤ y) : x ≤ sqrt y ↔ x ^ 2 ≤ y :=
by rw [mul_self_le_mul_self_iff hx (sqrt_nonneg _), pow_two, mul_self_sqrt hy]

lemma le_sqrt' (hx : 0 < x) : x ≤ sqrt y ↔ x ^ 2 ≤ y :=
begin
  rw [mul_self_le_mul_self_iff (le_of_lt hx) (sqrt_nonneg _), pow_two],
  cases le_total 0 y with hy hy,
  { rw [mul_self_sqrt hy] },
  { have h1 : 0 < x * x := mul_pos hx hx,
    have h2 : ¬x * x ≤ y := not_le_of_lt (lt_of_le_of_lt hy h1),
    simp [sqrt_eq_zero_of_nonpos, hy, h1, h2] }
end

lemma le_sqrt_of_sqr_le (h : x ^ 2 ≤ y) : x ≤ sqrt y :=
begin
  cases lt_or_ge 0 x with hx hx,
  { rwa [le_sqrt' hx] },
  { exact le_trans hx (sqrt_nonneg y) }
end

@[simp] theorem sqrt_inj (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x = sqrt y ↔ x = y :=
by simp [le_antisymm_iff, hx, hy]

@[simp] theorem sqrt_eq_zero (h : 0 ≤ x) : sqrt x = 0 ↔ x = 0 :=
by simpa using sqrt_inj h (le_refl _)

theorem sqrt_eq_zero' : sqrt x = 0 ↔ x ≤ 0 :=
(le_total x 0).elim
  (λ h, by simp [h, sqrt_eq_zero_of_nonpos])
  (λ h, by simp [h]; simp [le_antisymm_iff, h])

@[simp] theorem sqrt_pos : 0 < sqrt x ↔ 0 < x :=
lt_iff_lt_of_le_iff_le (iff.trans
  (by simp [le_antisymm_iff, sqrt_nonneg]) sqrt_eq_zero')

@[simp] theorem sqrt_mul' (x) {y : ℝ} (hy : 0 ≤ y) : sqrt (x * y) = sqrt x * sqrt y :=
begin
  cases le_total 0 x with hx hx,
  { refine iff.mp (mul_self_inj_of_nonneg _ (mul_nonneg _ _)) _; try {apply sqrt_nonneg},
    rw [mul_self_sqrt (mul_nonneg hx hy), mul_assoc,
        mul_left_comm (sqrt y), mul_self_sqrt hy, ← mul_assoc, mul_self_sqrt hx] },
  { rw [sqrt_eq_zero'.2 (mul_nonpos_of_nonpos_of_nonneg hx hy),
        sqrt_eq_zero'.2 hx, zero_mul] }
end

@[simp] theorem sqrt_mul (hx : 0 ≤ x) (y : ℝ) : sqrt (x * y) = sqrt x * sqrt y :=
by rw [mul_comm, sqrt_mul' _ hx, mul_comm]

@[simp] theorem sqrt_inv (x : ℝ) : sqrt x⁻¹ = (sqrt x)⁻¹ :=
(le_or_lt x 0).elim
  (λ h, by simp [sqrt_eq_zero'.2, inv_nonpos, h])
  (λ h, by rw [
    ← mul_self_inj_of_nonneg (sqrt_nonneg _) (le_of_lt $ inv_pos.2 $ sqrt_pos.2 h),
    mul_self_sqrt (le_of_lt $ inv_pos.2 h), ← mul_inv', mul_self_sqrt (le_of_lt h)])

@[simp] theorem sqrt_div (hx : 0 ≤ x) (y : ℝ) : sqrt (x / y) = sqrt x / sqrt y :=
by rw [division_def, sqrt_mul hx, sqrt_inv]; refl

attribute [irreducible] real.le

end real
