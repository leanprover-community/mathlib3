/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import order.conditionally_complete_lattice
import data.real.cau_seq_completion
import algebra.archimedean
import algebra.star.basic
import algebra.bounds

/-!
# Real numbers from Cauchy sequences

This file defines `ℝ` as the type of equivalence classes of Cauchy sequences of rational numbers.
This choice is motivated by how easy it is to prove that `ℝ` is a commutative ring, by simply
lifting everything to `ℚ`.
-/

open_locale pointwise

/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
structure real := of_cauchy ::
(cauchy : @cau_seq.completion.Cauchy ℚ _ _ _ abs _)
notation `ℝ` := real

attribute [pp_using_anonymous_constructor] real

namespace real
open cau_seq cau_seq.completion

variables {x y : ℝ}

lemma ext_cauchy_iff : ∀ {x y : real}, x = y ↔ x.cauchy = y.cauchy
| ⟨a⟩ ⟨b⟩ := by split; cc

lemma ext_cauchy {x y : real} : x.cauchy = y.cauchy → x = y :=
ext_cauchy_iff.2

/-- The real numbers are isomorphic to the quotient of Cauchy sequences on the rationals. -/
def equiv_Cauchy : ℝ ≃ cau_seq.completion.Cauchy :=
⟨real.cauchy, real.of_cauchy, λ ⟨_⟩, rfl, λ _, rfl⟩

-- irreducible doesn't work for instances: https://github.com/leanprover-community/lean/issues/511
@[irreducible] private def zero : ℝ := ⟨0⟩
@[irreducible] private def one : ℝ := ⟨1⟩
@[irreducible] private def add : ℝ → ℝ → ℝ | ⟨a⟩ ⟨b⟩ := ⟨a + b⟩
@[irreducible] private def neg : ℝ → ℝ | ⟨a⟩ := ⟨-a⟩
@[irreducible] private def mul : ℝ → ℝ → ℝ | ⟨a⟩ ⟨b⟩ := ⟨a * b⟩

instance : has_zero ℝ := ⟨zero⟩
instance : has_one ℝ := ⟨one⟩
instance : has_add ℝ := ⟨add⟩
instance : has_neg ℝ := ⟨neg⟩
instance : has_mul ℝ := ⟨mul⟩

lemma zero_cauchy : (⟨0⟩ : ℝ) = 0 := show _ = zero, by rw zero
lemma one_cauchy : (⟨1⟩ : ℝ) = 1 := show _ = one, by rw one
lemma add_cauchy {a b} : (⟨a⟩ + ⟨b⟩ : ℝ) = ⟨a + b⟩ := show add _ _ = _, by rw add
lemma neg_cauchy {a} : (-⟨a⟩ : ℝ) = ⟨-a⟩ := show neg _ = _, by rw neg
lemma mul_cauchy {a b} : (⟨a⟩ * ⟨b⟩ : ℝ) = ⟨a * b⟩ := show mul _ _ = _, by rw mul

instance : comm_ring ℝ :=
begin
  refine_struct { zero  := 0,
                  one   := 1,
                  mul   := (*),
                  add   := (+),
                  neg   := @has_neg.neg ℝ _,
                  sub   := λ a b, a + (-b),
                  npow  := @npow_rec _ ⟨1⟩ ⟨(*)⟩,
                  nsmul := @nsmul_rec _ ⟨0⟩ ⟨(+)⟩,
                  gsmul := @gsmul_rec _ ⟨0⟩ ⟨(+)⟩ ⟨@has_neg.neg ℝ _⟩ };
  repeat { rintro ⟨_⟩, };
  try { refl };
  simp [← zero_cauchy, ← one_cauchy, add_cauchy, neg_cauchy, mul_cauchy];
  apply add_assoc <|> apply add_comm <|> apply mul_assoc <|> apply mul_comm <|>
    apply left_distrib <|> apply right_distrib <|> apply sub_eq_add_neg <|> skip
end

/-! Extra instances to short-circuit type class resolution.

 These short-circuits have an additional property of ensuring that a computable path is found; if
 `field ℝ` is found first, then decaying it to these typeclasses would result in a `noncomputable`
 version of them. -/
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
instance : has_sub ℝ            := by apply_instance
instance : module ℝ ℝ           := by apply_instance
instance : inhabited ℝ          := ⟨0⟩

/-- The real numbers are a `*`-ring, with the trivial `*`-structure. -/
instance : star_ring ℝ          := star_ring_of_comm

/-- Coercion `ℚ` → `ℝ` as a `ring_hom`. Note that this
is `cau_seq.completion.of_rat`, not `rat.cast`. -/
def of_rat : ℚ →+* ℝ :=
by refine_struct { to_fun := of_cauchy ∘ of_rat };
  simp [of_rat_one, of_rat_zero, of_rat_mul, of_rat_add,
    one_cauchy, zero_cauchy, ← mul_cauchy, ← add_cauchy]

lemma of_rat_apply (x : ℚ) : of_rat x = of_cauchy (cau_seq.completion.of_rat x) := rfl

/-- Make a real number from a Cauchy sequence of rationals (by taking the equivalence class). -/
def mk (x : cau_seq ℚ abs) : ℝ := ⟨cau_seq.completion.mk x⟩

theorem mk_eq {f g : cau_seq ℚ abs} : mk f = mk g ↔ f ≈ g :=
ext_cauchy_iff.trans mk_eq

@[irreducible]
private def lt : ℝ → ℝ → Prop | ⟨x⟩ ⟨y⟩ :=
quotient.lift_on₂ x y (<) $
  λ f₁ g₁ f₂ g₂ hf hg, propext $
  ⟨λ h, lt_of_eq_of_lt (setoid.symm hf) (lt_of_lt_of_eq h hg),
   λ h, lt_of_eq_of_lt hf (lt_of_lt_of_eq h (setoid.symm hg))⟩

instance : has_lt ℝ := ⟨lt⟩

lemma lt_cauchy {f g} : (⟨⟦f⟧⟩ : ℝ) < ⟨⟦g⟧⟩ ↔ f < g := show lt _ _ ↔ _, by rw lt; refl

@[simp] theorem mk_lt {f g : cau_seq ℚ abs} : mk f < mk g ↔ f < g :=
lt_cauchy

lemma mk_zero : mk 0 = 0 := by rw ← zero_cauchy; refl
lemma mk_one : mk 1 = 1 := by rw ← one_cauchy; refl
lemma mk_add {f g : cau_seq ℚ abs} : mk (f + g) = mk f + mk g := by simp [mk, add_cauchy]
lemma mk_mul {f g : cau_seq ℚ abs} : mk (f * g) = mk f * mk g := by simp [mk, mul_cauchy]
lemma mk_neg {f : cau_seq ℚ abs} : mk (-f) = -mk f := by simp [mk, neg_cauchy]

@[simp] theorem mk_pos {f : cau_seq ℚ abs} : 0 < mk f ↔ pos f :=
by rw [← mk_zero, mk_lt]; exact iff_of_eq (congr_arg pos (sub_zero f))

@[irreducible] private def le (x y : ℝ) : Prop := x < y ∨ x = y
instance : has_le ℝ := ⟨le⟩
private lemma le_def {x y : ℝ} : x ≤ y ↔ x < y ∨ x = y := show le _ _ ↔ _, by rw le

@[simp] theorem mk_le {f g : cau_seq ℚ abs} : mk f ≤ mk g ↔ f ≤ g :=
by simp [le_def, mk_eq]; refl

@[elab_as_eliminator]
protected lemma ind_mk {C : real → Prop} (x : real) (h : ∀ y, C (mk y)) : C x :=
begin
  cases x with x,
  induction x using quot.induction_on with x,
  exact h x
end

theorem add_lt_add_iff_left {a b : ℝ} (c : ℝ) : c + a < c + b ↔ a < b :=
begin
  induction a using real.ind_mk,
  induction b using real.ind_mk,
  induction c using real.ind_mk,
  simp only [mk_lt, ← mk_add],
  show pos _ ↔ pos _, rw add_sub_add_left_eq_sub
end

instance : partial_order ℝ :=
{ le := (≤), lt := (<),
  lt_iff_le_not_le := λ a b, real.ind_mk a $ λ a, real.ind_mk b $ λ b,
    by simpa using lt_iff_le_not_le,
  le_refl := λ a, a.ind_mk (by intro a; rw mk_le),
  le_trans := λ a b c, real.ind_mk a $ λ a, real.ind_mk b $ λ b, real.ind_mk c $ λ c,
    by simpa using le_trans,
  lt_iff_le_not_le := λ a b, real.ind_mk a $ λ a, real.ind_mk b $ λ b,
    by simpa using lt_iff_le_not_le,
  le_antisymm := λ a b, real.ind_mk a $ λ a, real.ind_mk b $ λ b,
    by simpa [mk_eq] using @cau_seq.le_antisymm _ _ a b }

instance : preorder ℝ := by apply_instance

theorem of_rat_lt {x y : ℚ} : of_rat x < of_rat y ↔ x < y :=
begin
  rw [mk_lt] {md := tactic.transparency.semireducible},
  exact const_lt
end

protected theorem zero_lt_one : (0 : ℝ) < 1 :=
by convert of_rat_lt.2 zero_lt_one; simp

protected theorem mul_pos {a b : ℝ} : 0 < a → 0 < b → 0 < a * b :=
begin
  induction a using real.ind_mk with a,
  induction b using real.ind_mk with b,
  simpa only [mk_lt, mk_pos, ← mk_mul] using cau_seq.mul_pos
end

instance : ordered_ring ℝ :=
{ add_le_add_left :=
  begin
    simp only [le_iff_eq_or_lt],
    rintros a b ⟨rfl, h⟩,
    { simp },
    { exact λ c, or.inr ((add_lt_add_iff_left c).2 ‹_›) }
  end,
  zero_le_one := le_of_lt real.zero_lt_one,
  mul_pos     := @real.mul_pos,
  .. real.comm_ring, .. real.partial_order, .. real.semiring }

instance : ordered_semiring ℝ           := by apply_instance
instance : ordered_add_comm_group ℝ     := by apply_instance
instance : ordered_cancel_add_comm_monoid ℝ := by apply_instance
instance : ordered_add_comm_monoid ℝ    := by apply_instance
instance : nontrivial ℝ := ⟨⟨0, 1, ne_of_lt real.zero_lt_one⟩⟩

open_locale classical

noncomputable instance : linear_order ℝ :=
{ le_total := begin
    intros a b,
    induction a using real.ind_mk with a,
    induction b using real.ind_mk with b,
    simpa using le_total a b,
  end,
  decidable_le := by apply_instance,
  .. real.partial_order }

noncomputable instance : linear_ordered_comm_ring ℝ :=
{ .. real.nontrivial, .. real.ordered_ring, .. real.comm_ring, .. real.linear_order }

/- Extra instances to short-circuit type class resolution -/
noncomputable instance : linear_ordered_ring ℝ        := by apply_instance
noncomputable instance : linear_ordered_semiring ℝ    := by apply_instance
instance : domain ℝ                     :=
{ .. real.nontrivial, .. real.comm_ring, .. linear_ordered_ring.to_domain }

/-- The real numbers are an ordered `*`-ring, with the trivial `*`-structure. -/
instance : star_ordered_ring ℝ :=
{ star_mul_self_nonneg := λ r, mul_self_nonneg r, }

@[irreducible] private noncomputable def inv' : ℝ → ℝ | ⟨a⟩ := ⟨a⁻¹⟩
noncomputable instance : has_inv ℝ := ⟨inv'⟩
lemma inv_cauchy {f} : (⟨f⟩ : ℝ)⁻¹ = ⟨f⁻¹⟩ := show inv' _ = _, by rw inv'

noncomputable instance : linear_ordered_field ℝ :=
{ inv := has_inv.inv,
  mul_inv_cancel := begin
    rintros ⟨a⟩ h,
    rw mul_comm,
    simp only [inv_cauchy, mul_cauchy, ← one_cauchy, ← zero_cauchy, ne.def] at *,
    exact cau_seq.completion.inv_mul_cancel h,
  end,
  inv_zero := by simp [← zero_cauchy, inv_cauchy],
  ..real.linear_ordered_comm_ring,
  ..real.domain }

/- Extra instances to short-circuit type class resolution -/

noncomputable instance : linear_ordered_add_comm_group ℝ          := by apply_instance
noncomputable instance field : field ℝ                            := by apply_instance
noncomputable instance : division_ring ℝ                          := by apply_instance
noncomputable instance : integral_domain ℝ                        := by apply_instance
noncomputable instance : distrib_lattice ℝ                        := by apply_instance
noncomputable instance : lattice ℝ                                := by apply_instance
noncomputable instance : semilattice_inf ℝ                        := by apply_instance
noncomputable instance : semilattice_sup ℝ                        := by apply_instance
noncomputable instance : has_inf ℝ                                := by apply_instance
noncomputable instance : has_sup ℝ                                := by apply_instance
noncomputable instance decidable_lt (a b : ℝ) : decidable (a < b) := by apply_instance
noncomputable instance decidable_le (a b : ℝ) : decidable (a ≤ b) := by apply_instance
noncomputable instance decidable_eq (a b : ℝ) : decidable (a = b) := by apply_instance

open rat

@[simp] theorem of_rat_eq_cast : ∀ x : ℚ, of_rat x = x :=
of_rat.eq_rat_cast

theorem le_mk_of_forall_le {f : cau_seq ℚ abs} :
  (∃ i, ∀ j ≥ i, x ≤ f j) → x ≤ mk f :=
begin
  intro h,
  induction x using real.ind_mk with x,
  apply le_of_not_lt,
  rw mk_lt,
  rintro ⟨K, K0, hK⟩,
  obtain ⟨i, H⟩ := exists_forall_ge_and h
    (exists_forall_ge_and hK (f.cauchy₃ $ half_pos K0)),
  apply not_lt_of_le (H _ (le_refl _)).1,
  rw ← of_rat_eq_cast,
  rw [mk_lt] {md := tactic.transparency.semireducible},
  refine ⟨_, half_pos K0, i, λ j ij, _⟩,
  have := add_le_add (H _ ij).2.1
    (le_of_lt (abs_lt.1 $ (H _ (le_refl _)).2.2 _ ij).1),
  rwa [← sub_eq_add_neg, sub_self_div_two, sub_apply, sub_add_sub_cancel] at this
end

theorem mk_le_of_forall_le {f : cau_seq ℚ abs} {x : ℝ}
  (h : ∃ i, ∀ j ≥ i, (f j : ℝ) ≤ x) : mk f ≤ x :=
begin
  cases h with i H,
  rw [← neg_le_neg_iff, ← mk_neg],
  exact le_mk_of_forall_le ⟨i, λ j ij, by simp [H _ ij]⟩
end

theorem mk_near_of_forall_near {f : cau_seq ℚ abs} {x : ℝ} {ε : ℝ}
  (H : ∃ i, ∀ j ≥ i, abs ((f j : ℝ) - x) ≤ ε) : abs (mk f - x) ≤ ε :=
abs_sub_le_iff.2
  ⟨sub_le_iff_le_add'.2 $ mk_le_of_forall_le $
    H.imp $ λ i h j ij, sub_le_iff_le_add'.1 (abs_sub_le_iff.1 $ h j ij).1,
  sub_le.1 $ le_mk_of_forall_le $
    H.imp $ λ i h j ij, sub_le.1 (abs_sub_le_iff.1 $ h j ij).2⟩

instance : archimedean ℝ :=
archimedean_iff_rat_le.2 $ λ x, real.ind_mk x $ λ f,
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

/-- Every nonempty bounded below set of real numbers has the greatest lower bound. This is an
auxiliary lemma for the definition of a `conditionally_complete_linear_order` structure on `ℝ`.
Use `Inf s` and lemmas with `cInf` in their names instead of this lemma.  -/
theorem exists_is_glb (S : set ℝ) (hne : S.nonempty) (hbdd : bdd_below S) :
  ∃ x, is_glb S x :=
begin
  rcases ⟨hne, hbdd⟩ with ⟨⟨x, hxS⟩, ⟨L, hL⟩⟩,
  set s : ℕ → set ℤ := λ n, {m | (m / (n + 1) : ℝ) ∈ lower_bounds S},
  have hdiv : ∀ {n : ℕ} {x y : ℝ}, x / (n + 1) ≤ y ↔ x ≤ y * (n + 1) :=
    λ d x y, div_le_iff d.cast_add_one_pos,
  have : ∀ n, ∃ m : ℤ, is_greatest (s n) m,
  { refine λ n, int.exists_greatest_of_bdd ⟨⌊x * (n + 1)⌋, λ z hz, _⟩ ⟨⌊L * (n + 1)⌋, λ y hy, _⟩,
    { have := hz hxS, rwa [hdiv, ← le_floor] at this },
    { exact hdiv.2 ((floor_le _).trans (mul_le_mul_of_nonneg_right (hL hy)
        n.cast_add_one_pos.le)) } },
  choose f hf,
  set g : ℕ → ℚ := λ n, f n / (n + 1),
  have g_le : ∀ n (y ∈ S), (g n : ℝ) ≤ y,
  { intros n y hy, rw [rat.cast_div], exact_mod_cast (hf n).1 hy },
  have lt_g : ∀ n, ∃ y ∈ S, (y : ℝ) < g n + (n + 1)⁻¹,
  { intro n,
    have : f n + 1 ∉ s n, from λ hn, ((hf n).2 hn).not_lt (lt_add_one _),
    simpa [s, mem_lower_bounds, add_div] using this },
  have sub_le : ∀ k n, g k - g n ≤ (n + 1)⁻¹,
  { intros k n, rcases lt_g n with ⟨y, hyS, hy⟩,
    rw [← @rat.cast_le ℝ, rat.cast_sub, rat.cast_inv, rat.cast_add, rat.cast_one, rat.cast_coe_nat],
    exact sub_le_iff_le_add'.2 ((g_le _ _ hyS).trans hy.le) },
  have abs_sub_le : ∀ k n, n ≤ k → abs (g k - g n) ≤ (n + 1)⁻¹,
    from λ k n hle, abs_sub_le_iff.2 ⟨sub_le _ _, (sub_le _ _).trans $
      inv_le_inv_of_le n.cast_add_one_pos (add_le_add_right (nat.cast_le.2 hle) _)⟩,
  have hg_cau : is_cau_seq abs g,
  { refine λ ε (ε0 : 0 < ε), ⟨⌊ε⁻¹⌋₊, λ j hj, (abs_sub_le _ _ hj).trans_lt _⟩,
    exact inv_lt_of_inv_lt ε0 (lt_nat_floor_add_one _) },
  refine ⟨mk ⟨g, hg_cau⟩, ⟨λ x xS, mk_le_of_forall_le ⟨0, λ n _, g_le n x xS⟩, λ y h, _⟩⟩,
  refine le_of_forall_pos_sub_le (λ ε ε0, le_mk_of_forall_le ⟨⌈ε⁻¹⌉₊, λ n hn, _⟩),
  rcases lt_g n with ⟨y', hy'S, hy'⟩,
  replace hn : ((n + 1)⁻¹ : ℝ) ≤ ε :=
    inv_le_of_inv_le ε0 ((nat_ceil_le.1 hn).trans (lt_add_one _).le),
  calc y - ε ≤ g n + (n + 1)⁻¹ - ε : sub_le_sub_right ((h hy'S).trans hy'.le) _
         ... ≤ g n                 : by simp [add_sub_assoc, hn],
end

noncomputable instance : conditionally_complete_linear_order ℝ :=
{ ..real.linear_order, .. lattice_of_linear_order,
  .. conditionally_complete_lattice_of_exists_is_glb exists_is_glb 0 }

lemma lt_Inf_add_pos {s : set ℝ} (h : s.nonempty) {ε : ℝ} (hε : 0 < ε) :
  ∃ a ∈ s, a < Inf s + ε :=
exists_lt_of_cInf_lt h $ lt_add_of_pos_right _ hε

lemma add_neg_lt_Sup {s : set ℝ} (h : s.nonempty) {ε : ℝ} (hε : ε < 0) :
  ∃ a ∈ s, Sup s + ε < a :=
exists_lt_of_lt_cSup h $ add_lt_iff_neg_left.2 hε

@[simp] theorem Sup_empty : Sup (∅ : set ℝ) = 0 := dif_neg $ by simp

theorem Sup_of_not_bdd_above {s : set ℝ} (hs : ¬ bdd_above s) : Sup s = 0 :=
cSup_of_not_bdd_above hs

@[simp] theorem Sup_univ : Sup (@set.univ ℝ) = 0 :=
real.Sup_of_not_bdd_above not_bdd_above_univ

@[simp] theorem Inf_empty : Inf (∅ : set ℝ) = 0 := cInf_empty

theorem Inf_of_not_bdd_below {s : set ℝ} (hs : ¬ bdd_below s) : Inf s = 0 :=
cInf_of_not_bdd_below hs

@[simp] theorem Inf_univ : Inf (@set.univ ℝ) = 0 :=
real.Inf_of_not_bdd_below not_bdd_below_univ

/--
As `0` is the default value for `real.Sup` of the empty set or sets which are not bounded above, it
suffices to show that `S` is bounded below by `0` to show that `0 ≤ Inf S`.
-/
lemma Sup_nonneg (S : set ℝ) (hS : ∀ x ∈ S, (0:ℝ) ≤ x) : 0 ≤ Sup S :=
begin
  rcases S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩,
  { exact Sup_empty.ge },
  { apply dite _ (λ h, le_cSup_of_le h hy $ hS y hy) (λ h, (Sup_of_not_bdd_above h).ge) }
end

/--
As `0` is the default value for `real.Sup` of the empty set, it suffices to show that `S` is
bounded above by `0` to show that `Sup S ≤ 0`.
-/
lemma Sup_nonpos (S : set ℝ) (hS : ∀ x ∈ S, x ≤ (0:ℝ)) : Sup S ≤ 0 :=
begin
  rcases S.eq_empty_or_nonempty with rfl | hS₂,
  exacts [Sup_empty.le, cSup_le hS₂ hS],
end

/--
As `0` is the default value for `real.Inf` of the empty set, it suffices to show that `S` is
bounded below by `0` to show that `0 ≤ Inf S`.
-/
lemma Inf_nonneg (S : set ℝ) (hS : ∀ x ∈ S, (0:ℝ) ≤ x) : 0 ≤ Inf S :=
begin
  rcases S.eq_empty_or_nonempty with rfl | hS₂,
  exacts [Inf_empty.ge, le_cInf hS₂ hS]
end

/--
As `0` is the default value for `real.Inf` of the empty set or sets which are not bounded below, it
suffices to show that `S` is bounded above by `0` to show that `Inf S ≤ 0`.
-/
lemma Inf_nonpos (S : set ℝ) (hS : ∀ x ∈ S, x ≤ (0:ℝ)) : Inf S ≤ 0 :=
begin
  rcases S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩,
  { exact Inf_empty.le },
  { apply dite _ (λ h, cInf_le_of_le h hy $ hS y hy) (λ h, (Inf_of_not_bdd_below h).le) }
end

lemma Inf_le_Sup (s : set ℝ) (h₁ : bdd_below s) (h₂ : bdd_above s) : Inf s ≤ Sup s :=
begin
  rcases s.eq_empty_or_nonempty with rfl | hne,
  { rw [Inf_empty, Sup_empty] },
  { exact cInf_le_cSup h₁ h₂ hne }
end

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
    refine (cSup_le lb (ub' _ _)).not_lt (sub_lt_self _ (half_pos ε0)),
    refine ⟨_, half_pos ε0, i, λ j ij, _⟩,
    rw [sub_apply, const_apply, sub_right_comm,
      le_sub_iff_add_le, add_halves],
    exact ih _ ij },
  { rcases h with ⟨ε, ε0, i, ih⟩,
    refine (le_cSup ub _).not_lt ((lt_add_iff_pos_left _).2 (half_pos ε0)),
    refine ⟨_, half_pos ε0, i, λ j ij, _⟩,
    rw [sub_apply, const_apply, add_comm, ← sub_sub,
      le_sub_iff_add_le, add_halves],
    exact ih _ ij }
end

noncomputable instance : cau_seq.is_complete ℝ abs := ⟨cau_seq_converges⟩

end real
