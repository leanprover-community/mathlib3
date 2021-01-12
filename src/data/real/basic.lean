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
import algebra.star.basic

/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
def real := @cau_seq.completion.Cauchy ℚ _ _ _ abs _
notation `ℝ` := real

namespace real
open cau_seq cau_seq.completion

variables {x y : ℝ}

def comm_ring_aux : comm_ring ℝ := Cauchy.comm_ring

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

/-- The real numbers are a *-ring, with the trivial *-structure. -/
instance : star_ring ℝ          := star_ring_of_comm

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

instance : partial_order ℝ :=
{ le := (≤), lt := (<),
  le_refl := λ a, or.inr rfl,
  le_trans := λ a b c, quotient.induction_on₃ a b c $
    λ f g h, by simpa [quotient_mk_eq_mk] using le_trans,
  lt_iff_le_not_le := λ a b, quotient.induction_on₂ a b $
    λ f g, by simpa [quotient_mk_eq_mk] using lt_iff_le_not_le,
  le_antisymm := λ a b, quotient.induction_on₂ a b $
    λ f g, by simpa [mk_eq, quotient_mk_eq_mk] using @cau_seq.le_antisymm _ _ f g }

instance : preorder ℝ := by apply_instance

theorem of_rat_lt {x y : ℚ} : of_rat x < of_rat y ↔ x < y := const_lt

protected theorem zero_lt_one : (0 : ℝ) < 1 := of_rat_lt.2 zero_lt_one

protected theorem mul_pos {a b : ℝ} : 0 < a → 0 < b → 0 < a * b :=
quotient.induction_on₂ a b $ λ f g,
  show pos (f - 0) → pos (g - 0) → pos (f * g - 0),
  by simpa using cau_seq.mul_pos

instance : ordered_ring ℝ :=
{ add_le_add_left := λ a b h c, h.imp (real.add_lt_add_iff_left c).2 (λ h, h ▸ rfl),
  zero_le_one := le_of_lt real.zero_lt_one,
  mul_pos     := @real.mul_pos,
  .. real.comm_ring, .. real.partial_order, .. real.semiring }

instance : ordered_semiring ℝ           := by apply_instance
instance : ordered_add_comm_group ℝ     := by apply_instance
instance : ordered_cancel_add_comm_monoid ℝ := by apply_instance
instance : ordered_add_comm_monoid ℝ    := by apply_instance
instance : has_one ℝ                    := by apply_instance
instance : has_zero ℝ                   := by apply_instance
instance : has_mul ℝ                    := by apply_instance
instance : has_add ℝ                    := by apply_instance
instance : has_sub ℝ                    := by apply_instance
instance : nontrivial ℝ := ⟨⟨0, 1, ne_of_lt real.zero_lt_one⟩⟩

open_locale classical

noncomputable instance : linear_order ℝ :=
{ le_total := λ a b, quotient.induction_on₂ a b $
    λ f g, by simpa [quotient_mk_eq_mk] using le_total f g,
  decidable_le := by apply_instance,
  .. real.partial_order }

noncomputable instance : linear_ordered_comm_ring ℝ :=
{ .. real.nontrivial, .. real.ordered_ring, .. real.comm_ring, .. real.linear_order }

/- Extra instances to short-circuit type class resolution -/
noncomputable instance : linear_ordered_ring ℝ        := by apply_instance
noncomputable instance : linear_ordered_semiring ℝ    := by apply_instance
instance : domain ℝ                     :=
{ .. real.nontrivial, .. real.comm_ring, .. linear_ordered_ring.to_domain }

noncomputable instance : linear_ordered_field ℝ :=
{ ..real.linear_ordered_comm_ring,
  ..real.domain,
  ..cau_seq.completion.field }

/- Extra instances to short-circuit type class resolution -/

noncomputable instance : linear_ordered_add_comm_group ℝ := by apply_instance
noncomputable instance field : field ℝ := by apply_instance
noncomputable instance : division_ring ℝ           := by apply_instance
noncomputable instance : integral_domain ℝ         := by apply_instance
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
      (sub_lt_self _ (half_pos ε0)),
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

attribute [irreducible] real.le

end real
