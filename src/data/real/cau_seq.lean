/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.group_power.lemmas
import algebra.order.absolute_value
import algebra.order.group.min_max
import algebra.order.field.basic
import algebra.ring.pi
import group_theory.group_action.pi

/-!
# Cauchy sequences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A basic theory of Cauchy sequences, used in the construction of the reals and p-adic numbers. Where
applicable, lemmas that will be reused in other contexts have been stated in extra generality.

There are other "versions" of Cauchyness in the library, in particular Cauchy filters in topology.
This is a concrete implementation that is useful for simplicity and computability reasons.

## Important definitions

* `is_cau_seq`: a predicate that says `f : ℕ → β` is Cauchy.
* `cau_seq`: the type of Cauchy sequences valued in type `β` with respect to an absolute value
  function `abv`.

## Tags

sequence, cauchy, abs val, absolute value
-/

open is_absolute_value

variables {G α β : Type*}

theorem exists_forall_ge_and {α} [linear_order α] {P Q : α → Prop} :
  (∃ i, ∀ j ≥ i, P j) → (∃ i, ∀ j ≥ i, Q j) →
  ∃ i, ∀ j ≥ i, P j ∧ Q j
| ⟨a, h₁⟩ ⟨b, h₂⟩ := let ⟨c, ac, bc⟩ := exists_ge_of_linear a b in
  ⟨c, λ j hj, ⟨h₁ _ (le_trans ac hj), h₂ _ (le_trans bc hj)⟩⟩

section
variables [linear_ordered_field α] [ring β] (abv : β → α) [is_absolute_value abv]

theorem rat_add_continuous_lemma
  {ε : α} (ε0 : 0 < ε) : ∃ δ > 0, ∀ {a₁ a₂ b₁ b₂ : β},
  abv (a₁ - b₁) < δ → abv (a₂ - b₂) < δ → abv (a₁ + a₂ - (b₁ + b₂)) < ε :=
⟨ε / 2, half_pos ε0, λ a₁ a₂ b₁ b₂ h₁ h₂,
  by simpa [add_halves, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using lt_of_le_of_lt (abv_add abv _ _) (add_lt_add h₁ h₂)⟩

theorem rat_mul_continuous_lemma
  {ε K₁ K₂ : α} (ε0 : 0 < ε) :
  ∃ δ > 0, ∀ {a₁ a₂ b₁ b₂ : β}, abv a₁ < K₁ → abv b₂ < K₂ →
  abv (a₁ - b₁) < δ → abv (a₂ - b₂) < δ → abv (a₁ * a₂ - b₁ * b₂) < ε :=
begin
  have K0 : (0 : α) < max 1 (max K₁ K₂) := lt_of_lt_of_le zero_lt_one (le_max_left _ _),
  have εK := div_pos (half_pos ε0) K0,
  refine ⟨_, εK, λ a₁ a₂ b₁ b₂ ha₁ hb₂ h₁ h₂, _⟩,
  replace ha₁ := lt_of_lt_of_le ha₁ (le_trans (le_max_left _ K₂) (le_max_right 1 _)),
  replace hb₂ := lt_of_lt_of_le hb₂ (le_trans (le_max_right K₁ _) (le_max_right 1 _)),
  have := add_lt_add
    (mul_lt_mul' (le_of_lt h₁) hb₂ (abv_nonneg abv _) εK)
    (mul_lt_mul' (le_of_lt h₂) ha₁ (abv_nonneg abv _) εK),
  rw [← abv_mul abv, mul_comm, div_mul_cancel _ (ne_of_gt K0), ← abv_mul abv, add_halves] at this,
  simpa [mul_add, add_mul, sub_eq_add_neg, add_comm, add_left_comm]
    using lt_of_le_of_lt (abv_add abv _ _) this
end

theorem rat_inv_continuous_lemma
  {β : Type*} [division_ring β] (abv : β → α) [is_absolute_value abv]
  {ε K : α} (ε0 : 0 < ε) (K0 : 0 < K) :
  ∃ δ > 0, ∀ {a b : β}, K ≤ abv a → K ≤ abv b →
  abv (a - b) < δ → abv (a⁻¹ - b⁻¹) < ε :=
begin
  refine ⟨K * ε * K, mul_pos (mul_pos K0 ε0) K0, λ a b ha hb h, _⟩,
  have a0 := K0.trans_le ha,
  have b0 := K0.trans_le hb,
  rw [inv_sub_inv' ((abv_pos abv).1 a0) ((abv_pos abv).1 b0), abv_mul abv, abv_mul abv,
    abv_inv abv, abv_inv abv,  abv_sub abv],
  refine lt_of_mul_lt_mul_left (lt_of_mul_lt_mul_right _ b0.le) a0.le,
  rw [mul_assoc, inv_mul_cancel_right₀ b0.ne', ←mul_assoc, mul_inv_cancel a0.ne', one_mul],
  refine h.trans_le _,
  exact mul_le_mul (mul_le_mul ha le_rfl ε0.le a0.le) hb K0.le (mul_nonneg a0.le ε0.le),
end
end

/-- A sequence is Cauchy if the distance between its entries tends to zero. -/
def is_cau_seq {α : Type*} [linear_ordered_field α]
  {β : Type*} [ring β] (abv : β → α) (f : ℕ → β) : Prop :=
∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j - f i) < ε

namespace is_cau_seq
variables [linear_ordered_field α] [ring β] {abv : β → α} [is_absolute_value abv] {f g : ℕ → β}

@[nolint ge_or_gt] -- see Note [nolint_ge]
theorem cauchy₂ (hf : is_cau_seq abv f) {ε : α} (ε0 : 0 < ε) :
  ∃ i, ∀ j k ≥ i, abv (f j - f k) < ε :=
begin
  refine (hf _ (half_pos ε0)).imp (λ i hi j ij k ik, _),
  rw ← add_halves ε,
  refine lt_of_le_of_lt (abv_sub_le abv _ _ _) (add_lt_add (hi _ ij) _),
  rw abv_sub abv, exact hi _ ik
end

theorem cauchy₃ (hf : is_cau_seq abv f) {ε : α} (ε0 : 0 < ε) :
  ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - f j) < ε :=
let ⟨i, H⟩ := hf.cauchy₂ ε0 in ⟨i, λ j ij k jk, H _ (le_trans ij jk) _ ij⟩

lemma add (hf : is_cau_seq abv f) (hg : is_cau_seq abv g) : is_cau_seq abv (f + g) :=
λ ε ε0,
  let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abv ε0,
      ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0) in
  ⟨i, λ j ij, let ⟨H₁, H₂⟩ := H _ le_rfl in Hδ (H₁ _ ij) (H₂ _ ij)⟩

end is_cau_seq

/-- `cau_seq β abv` is the type of `β`-valued Cauchy sequences, with respect to the absolute value
function `abv`. -/
def cau_seq {α : Type*} [linear_ordered_field α]
  (β : Type*) [ring β] (abv : β → α) : Type* :=
{f : ℕ → β // is_cau_seq abv f}

namespace cau_seq
variables [linear_ordered_field α]

section ring
variables [ring β] {abv : β → α}

instance : has_coe_to_fun (cau_seq β abv) (λ _, ℕ → β) := ⟨subtype.val⟩

@[simp] theorem mk_to_fun (f) (hf : is_cau_seq abv f) :
  @coe_fn (cau_seq β abv) _ _ ⟨f, hf⟩ = f := rfl

theorem ext {f g : cau_seq β abv} (h : ∀ i, f i = g i) : f = g :=
subtype.eq (funext h)

theorem is_cau (f : cau_seq β abv) : is_cau_seq abv f := f.2

theorem cauchy (f : cau_seq β abv) :
  ∀ {ε}, 0 < ε → ∃ i, ∀ j ≥ i, abv (f j - f i) < ε := f.2

/-- Given a Cauchy sequence `f`, create a Cauchy sequence from a sequence `g` with
the same values as `f`. -/
def of_eq (f : cau_seq β abv) (g : ℕ → β) (e : ∀ i, f i = g i) : cau_seq β abv :=
⟨g, λ ε, by rw [show g = f, from (funext e).symm]; exact f.cauchy⟩

variable [is_absolute_value abv]

@[nolint ge_or_gt] -- see Note [nolint_ge]
theorem cauchy₂ (f : cau_seq β abv) {ε} : 0 < ε →
  ∃ i, ∀ j k ≥ i, abv (f j - f k) < ε := f.2.cauchy₂

theorem cauchy₃ (f : cau_seq β abv) {ε} : 0 < ε →
  ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - f j) < ε := f.2.cauchy₃

theorem bounded (f : cau_seq β abv) : ∃ r, ∀ i, abv (f i) < r :=
begin
  cases f.cauchy zero_lt_one with i h,
  set R : ℕ → α := @nat.rec (λ n, α) (abv (f 0)) (λ i c, max c (abv (f i.succ))) with hR,
  have : ∀ i, ∀ j ≤ i, abv (f j) ≤ R i,
  { refine nat.rec (by simp [hR]) _,
    rintros i hi j (rfl | hj),
    { simp },
    exact (hi j hj).trans (le_max_left _ _) },
  refine ⟨R i + 1, λ j, _⟩,
  cases lt_or_le j i with ij ij,
  { exact lt_of_le_of_lt (this i _ (le_of_lt ij)) (lt_add_one _) },
  { have := lt_of_le_of_lt (abv_add abv _ _)
      (add_lt_add_of_le_of_lt (this i _ le_rfl) (h _ ij)),
    rw [add_sub, add_comm] at this, simpa }
end

theorem bounded' (f : cau_seq β abv) (x : α) : ∃ r > x, ∀ i, abv (f i) < r :=
let ⟨r, h⟩ := f.bounded in
⟨max r (x+1), lt_of_lt_of_le (lt_add_one _) (le_max_right _ _),
  λ i, lt_of_lt_of_le (h i) (le_max_left _ _)⟩

instance : has_add (cau_seq β abv) := ⟨λ f g, ⟨f + g, f.2.add g.2⟩⟩

@[simp, norm_cast] lemma coe_add (f g : cau_seq β abv) : ⇑(f + g) = f + g := rfl
@[simp, norm_cast] theorem add_apply (f g : cau_seq β abv) (i : ℕ) : (f + g) i = f i + g i := rfl

variable (abv)

/-- The constant Cauchy sequence. -/
def const (x : β) : cau_seq β abv :=
⟨λ i, x, λ ε ε0, ⟨0, λ j ij, by simpa [abv_zero abv] using ε0⟩⟩

variable {abv}

local notation `const` := const abv

@[simp, norm_cast] lemma coe_const (x : β) : ⇑(const x) = function.const _ x := rfl
@[simp, norm_cast] theorem const_apply (x : β) (i : ℕ) : (const x : ℕ → β) i = x := rfl

theorem const_inj {x y : β} : (const x : cau_seq β abv) = const y ↔ x = y :=
⟨λ h, congr_arg (λ f:cau_seq β abv, (f:ℕ→β) 0) h, congr_arg _⟩

instance : has_zero (cau_seq β abv) := ⟨const 0⟩
instance : has_one (cau_seq β abv) := ⟨const 1⟩
instance : inhabited (cau_seq β abv) := ⟨0⟩

@[simp, norm_cast] lemma coe_zero : ⇑(0 : cau_seq β abv) = 0 := rfl
@[simp, norm_cast] lemma coe_one : ⇑(1 : cau_seq β abv) = 1 := rfl
@[simp, norm_cast] lemma zero_apply (i) : (0 : cau_seq β abv) i = 0 := rfl
@[simp, norm_cast] lemma one_apply (i) : (1 : cau_seq β abv) i = 1 := rfl
@[simp] lemma const_zero : const 0 = 0 := rfl
@[simp] lemma const_one : const 1 = 1 := rfl

theorem const_add (x y : β) : const (x + y) = const x + const y :=
rfl

instance : has_mul (cau_seq β abv) :=
⟨λ f g, ⟨f * g, λ ε ε0,
  let ⟨F, F0, hF⟩ := f.bounded' 0, ⟨G, G0, hG⟩ := g.bounded' 0,
      ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abv ε0,
      ⟨i, H⟩ := exists_forall_ge_and (f.cauchy₃ δ0) (g.cauchy₃ δ0) in
  ⟨i, λ j ij, let ⟨H₁, H₂⟩ := H _ le_rfl in
    Hδ (hF j) (hG i) (H₁ _ ij) (H₂ _ ij)⟩⟩⟩

@[simp, norm_cast] lemma coe_mul (f g : cau_seq β abv) : ⇑(f * g) = f * g := rfl
@[simp, norm_cast] theorem mul_apply (f g : cau_seq β abv) (i : ℕ) : (f * g) i = f i * g i := rfl

theorem const_mul (x y : β) : const (x * y) = const x * const y := rfl

instance : has_neg (cau_seq β abv) :=
⟨λ f, of_eq (const (-1) * f) (λ x, -f x) (λ i, by simp)⟩

@[simp, norm_cast] lemma coe_neg (f : cau_seq β abv) : ⇑(-f) = -f := rfl
@[simp, norm_cast] theorem neg_apply (f : cau_seq β abv) (i) : (-f) i = -f i := rfl

theorem const_neg (x : β) : const (-x) = -const x := rfl

instance : has_sub (cau_seq β abv) :=
⟨λ f g, of_eq (f + -g) (λ x, f x - g x) (λ i, by simp [sub_eq_add_neg])⟩

@[simp, norm_cast] lemma coe_sub (f g : cau_seq β abv) : ⇑(f - g) = f - g := rfl
@[simp, norm_cast] theorem sub_apply (f g : cau_seq β abv) (i : ℕ) : (f - g) i = f i - g i := rfl

theorem const_sub (x y : β) : const (x - y) = const x - const y := rfl

section has_smul
variables [has_smul G β] [is_scalar_tower G β β]

instance : has_smul G (cau_seq β abv) :=
⟨λ a f, of_eq (const (a • 1) * f) (a • f) $ λ i, smul_one_mul _ _⟩

@[simp, norm_cast] lemma coe_smul (a : G) (f : cau_seq β abv) : ⇑(a • f) = a • f := rfl
@[simp, norm_cast] lemma smul_apply (a : G) (f : cau_seq β abv) (i : ℕ) : (a • f) i = a • f i := rfl
lemma const_smul (a : G) (x : β) : const (a • x) = a • const x := rfl

instance : is_scalar_tower G (cau_seq β abv) (cau_seq β abv) :=
⟨λ a f g, subtype.ext $ smul_assoc a ⇑f ⇑g⟩

end has_smul

instance : add_group (cau_seq β abv) :=
function.injective.add_group _ subtype.coe_injective
  rfl coe_add coe_neg coe_sub (λ _ _, coe_smul _ _) (λ _ _, coe_smul _ _)

instance : add_group_with_one (cau_seq β abv) :=
{ one := 1,
  nat_cast := λ n, const n,
  nat_cast_zero := congr_arg const nat.cast_zero,
  nat_cast_succ := λ n, congr_arg const (nat.cast_succ n),
  int_cast := λ n, const n,
  int_cast_of_nat := λ n, congr_arg const (int.cast_of_nat n),
  int_cast_neg_succ_of_nat := λ n, congr_arg const (int.cast_neg_succ_of_nat n),
  .. cau_seq.add_group }

instance : has_pow (cau_seq β abv) ℕ :=
⟨λ f n, of_eq (npow_rec n f) (λ i, f i ^ n) $ by induction n; simp [*, npow_rec, pow_succ]⟩

@[simp, norm_cast] lemma coe_pow (f : cau_seq β abv) (n : ℕ) : ⇑(f ^ n) = f ^ n := rfl
@[simp, norm_cast] lemma pow_apply (f : cau_seq β abv) (n i : ℕ) : (f ^ n) i = f i ^ n := rfl
lemma const_pow (x : β) (n : ℕ) : const (x ^ n) = const x ^ n := rfl

instance : ring (cau_seq β abv) :=
function.injective.ring _ subtype.coe_injective
  rfl rfl coe_add coe_mul coe_neg coe_sub (λ _ _, coe_smul _ _) (λ _ _, coe_smul _ _) coe_pow
  (λ _, rfl) (λ _, rfl)

instance {β : Type*} [comm_ring β] {abv : β → α} [is_absolute_value abv] :
  comm_ring (cau_seq β abv) :=
{ mul_comm := by intros; apply ext; simp [mul_left_comm, mul_comm],
  ..cau_seq.ring }

/-- `lim_zero f` holds when `f` approaches 0. -/
def lim_zero {abv : β → α} (f : cau_seq β abv) : Prop := ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j) < ε

theorem add_lim_zero {f g : cau_seq β abv}
  (hf : lim_zero f) (hg : lim_zero g) : lim_zero (f + g)
| ε ε0 := (exists_forall_ge_and
    (hf _ $ half_pos ε0) (hg _ $ half_pos ε0)).imp $
  λ i H j ij, let ⟨H₁, H₂⟩ := H _ ij in
    by simpa [add_halves ε] using lt_of_le_of_lt (abv_add abv _ _) (add_lt_add H₁ H₂)

theorem mul_lim_zero_right (f : cau_seq β abv) {g}
  (hg : lim_zero g) : lim_zero (f * g)
| ε ε0 := let ⟨F, F0, hF⟩ := f.bounded' 0 in
  (hg _ $ div_pos ε0 F0).imp $ λ i H j ij,
  by have := mul_lt_mul' (le_of_lt $ hF j) (H _ ij) (abv_nonneg abv _) F0;
     rwa [mul_comm F, div_mul_cancel _ (ne_of_gt F0), ← abv_mul abv] at this

theorem mul_lim_zero_left {f} (g : cau_seq β abv)
  (hg : lim_zero f) : lim_zero (f * g)
| ε ε0 := let ⟨G, G0, hG⟩ := g.bounded' 0 in
  (hg _ $ div_pos ε0 G0).imp $ λ i H j ij,
  by have := mul_lt_mul'' (H _ ij) (hG j) (abv_nonneg abv _) (abv_nonneg abv _);
     rwa [div_mul_cancel _ (ne_of_gt G0), ← abv_mul abv] at this

theorem neg_lim_zero {f : cau_seq β abv} (hf : lim_zero f) : lim_zero (-f) :=
by rw ← neg_one_mul; exact mul_lim_zero_right _ hf

theorem sub_lim_zero {f g : cau_seq β abv}
  (hf : lim_zero f) (hg : lim_zero g) : lim_zero (f - g) :=
by simpa only [sub_eq_add_neg] using add_lim_zero hf (neg_lim_zero hg)

theorem lim_zero_sub_rev {f g : cau_seq β abv} (hfg : lim_zero (f - g)) : lim_zero (g - f) :=
by simpa using neg_lim_zero hfg

theorem zero_lim_zero : lim_zero (0 : cau_seq β abv)
| ε ε0 := ⟨0, λ j ij, by simpa [abv_zero abv] using ε0⟩

theorem const_lim_zero {x : β} : lim_zero (const x) ↔ x = 0 :=
⟨λ H, (abv_eq_zero abv).1 $
  eq_of_le_of_forall_le_of_dense (abv_nonneg abv _) $
  λ ε ε0, let ⟨i, hi⟩ := H _ ε0 in le_of_lt $ hi _ le_rfl,
λ e, e.symm ▸ zero_lim_zero⟩

instance equiv : setoid (cau_seq β abv) :=
⟨λ f g, lim_zero (f - g),
⟨λ f, by simp [zero_lim_zero],
 λ f g h, by simpa using neg_lim_zero h,
 λ f g h fg gh, by simpa [sub_eq_add_neg, add_assoc] using add_lim_zero fg gh⟩⟩

lemma add_equiv_add {f1 f2 g1 g2 : cau_seq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
  f1 + g1 ≈ f2 + g2 :=
by simpa only [←add_sub_add_comm] using add_lim_zero hf hg

lemma neg_equiv_neg {f g : cau_seq β abv} (hf : f ≈ g) : -f ≈ -g :=
by simpa only [neg_sub'] using neg_lim_zero hf

lemma sub_equiv_sub {f1 f2 g1 g2 : cau_seq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
  f1 - g1 ≈ f2 - g2 :=
by simpa only [sub_eq_add_neg] using add_equiv_add hf (neg_equiv_neg hg)

theorem equiv_def₃ {f g : cau_seq β abv} (h : f ≈ g) {ε : α} (ε0 : 0 < ε) :
  ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - g j) < ε :=
(exists_forall_ge_and (h _ $ half_pos ε0) (f.cauchy₃ $ half_pos ε0)).imp $
λ i H j ij k jk, let ⟨h₁, h₂⟩ := H _ ij in
by have := lt_of_le_of_lt (abv_add abv (f j - g j) _) (add_lt_add h₁ (h₂ _ jk));
   rwa [sub_add_sub_cancel', add_halves] at this

theorem lim_zero_congr {f g : cau_seq β abv} (h : f ≈ g) : lim_zero f ↔ lim_zero g :=
⟨λ l, by simpa using add_lim_zero (setoid.symm h) l,
 λ l, by simpa using add_lim_zero h l⟩

theorem abv_pos_of_not_lim_zero {f : cau_seq β abv} (hf : ¬ lim_zero f) :
  ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ abv (f j) :=
begin
  haveI := classical.prop_decidable,
  by_contra nk,
  refine hf (λ ε ε0, _),
  simp [not_forall] at nk,
  cases f.cauchy₃ (half_pos ε0) with i hi,
  rcases nk _ (half_pos ε0) i with ⟨j, ij, hj⟩,
  refine ⟨j, λ k jk, _⟩,
  have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi j ij k jk) hj),
  rwa [sub_add_cancel, add_halves] at this
end

theorem of_near (f : ℕ → β) (g : cau_seq β abv)
  (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j - g j) < ε) : is_cau_seq abv f
| ε ε0 :=
  let ⟨i, hi⟩ := exists_forall_ge_and
    (h _ (half_pos $ half_pos ε0)) (g.cauchy₃ $ half_pos ε0) in
  ⟨i, λ j ij, begin
    cases hi _ le_rfl with h₁ h₂, rw abv_sub abv at h₁,
    have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi _ ij).1 h₁),
    have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add this (h₂ _ ij)),
    rwa [add_halves, add_halves, add_right_comm,
         sub_add_sub_cancel, sub_add_sub_cancel] at this
  end⟩

lemma not_lim_zero_of_not_congr_zero {f : cau_seq _ abv} (hf : ¬ f ≈ 0) : ¬ lim_zero f :=
assume : lim_zero f,
have lim_zero (f - 0), by simpa,
hf this

lemma mul_equiv_zero  (g : cau_seq _ abv) {f : cau_seq _ abv} (hf : f ≈ 0) : g * f ≈ 0 :=
have lim_zero (f - 0), from hf,
have lim_zero (g*f), from mul_lim_zero_right _ $ by simpa,
show lim_zero (g*f - 0), by simpa

lemma mul_equiv_zero' (g : cau_seq _ abv) {f : cau_seq _ abv} (hf : f ≈ 0) : f * g ≈ 0 :=
have lim_zero (f - 0), from hf,
have lim_zero (f*g), from mul_lim_zero_left _ $ by simpa,
show lim_zero (f*g - 0), by simpa

lemma mul_not_equiv_zero {f g : cau_seq _ abv} (hf : ¬ f ≈ 0) (hg : ¬ g ≈ 0) : ¬ (f * g) ≈ 0 :=
assume : lim_zero (f*g - 0),
have hlz : lim_zero (f*g), by simpa,
have hf' : ¬ lim_zero f, by simpa using (show ¬ lim_zero (f - 0), from hf),
have hg' : ¬ lim_zero g, by simpa using (show ¬ lim_zero (g - 0), from hg),
begin
  rcases abv_pos_of_not_lim_zero hf' with ⟨a1, ha1, N1, hN1⟩,
  rcases abv_pos_of_not_lim_zero hg' with ⟨a2, ha2, N2, hN2⟩,
  have : 0 < a1 * a2, from mul_pos ha1 ha2,
  cases hlz _ this with N hN,
  let i := max N (max N1 N2),
  have hN' := hN i (le_max_left _ _),
  have hN1' := hN1 i (le_trans (le_max_left _ _) (le_max_right _ _)),
  have hN1' := hN2 i (le_trans (le_max_right _ _) (le_max_right _ _)),
  apply not_le_of_lt hN',
  change _ ≤ abv (_ * _),
  rw is_absolute_value.abv_mul abv,
  apply mul_le_mul; try { assumption },
  { apply le_of_lt ha2 },
  { apply is_absolute_value.abv_nonneg abv }
end

theorem const_equiv {x y : β} : const x ≈ const y ↔ x = y :=
show lim_zero _ ↔ _, by rw [← const_sub, const_lim_zero, sub_eq_zero]

lemma mul_equiv_mul {f1 f2 g1 g2 : cau_seq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
  f1 * g1 ≈ f2 * g2 :=
by simpa only [mul_sub, sub_mul, sub_add_sub_cancel]
  using add_lim_zero (mul_lim_zero_left g1 hf) (mul_lim_zero_right f2 hg)

lemma smul_equiv_smul [has_smul G β] [is_scalar_tower G β β] {f1 f2 : cau_seq β abv}
  (c : G) (hf : f1 ≈ f2) :
  c • f1 ≈ c • f2 :=
by simpa [const_smul, smul_one_mul _ _]
  using mul_equiv_mul (const_equiv.mpr $ eq.refl $ c • 1) hf

lemma pow_equiv_pow {f1 f2 : cau_seq β abv} (hf : f1 ≈ f2) (n : ℕ) :
  f1 ^ n ≈ f2 ^ n :=
begin
  induction n with n ih,
  { simp only [pow_zero, setoid.refl] },
  { simpa only [pow_succ] using mul_equiv_mul hf ih, },
end

end ring

section is_domain
variables [ring β] [is_domain β] (abv : β → α) [is_absolute_value abv]

lemma one_not_equiv_zero : ¬ (const abv 1) ≈ (const abv 0) :=
assume h,
have ∀ ε > 0, ∃ i, ∀ k, i ≤ k → abv (1 - 0) < ε, from h,
have h1 : abv 1 ≤ 0, from le_of_not_gt $
  assume h2 : 0 < abv 1,
  exists.elim (this _ h2) $ λ i hi,
    lt_irrefl (abv 1) $ by simpa using hi _ le_rfl,
have h2 : 0 ≤ abv 1, from is_absolute_value.abv_nonneg _ _,
have abv 1 = 0, from le_antisymm h1 h2,
have (1 : β) = 0, from (is_absolute_value.abv_eq_zero abv).1 this,
absurd this one_ne_zero

end is_domain

section division_ring
variables [division_ring β] {abv : β → α} [is_absolute_value abv]

theorem inv_aux {f : cau_seq β abv} (hf : ¬ lim_zero f) :
  ∀ ε > 0, ∃ i, ∀ j ≥ i, abv ((f j)⁻¹ - (f i)⁻¹) < ε | ε ε0 :=
let ⟨K, K0, HK⟩ := abv_pos_of_not_lim_zero hf,
    ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abv ε0 K0,
    ⟨i, H⟩ := exists_forall_ge_and HK (f.cauchy₃ δ0) in
⟨i, λ j ij, let ⟨iK, H'⟩ := H _ le_rfl in Hδ (H _ ij).1 iK (H' _ ij)⟩

/-- Given a Cauchy sequence `f` with nonzero limit, create a Cauchy sequence with values equal to
the inverses of the values of `f`. -/
def inv (f : cau_seq β abv) (hf : ¬ lim_zero f) : cau_seq β abv := ⟨_, inv_aux hf⟩

@[simp, norm_cast] lemma coe_inv {f : cau_seq β abv} (hf) : ⇑(inv f hf) = f⁻¹ := rfl
@[simp, norm_cast] theorem inv_apply {f : cau_seq β abv} (hf i) : inv f hf i = (f i)⁻¹ := rfl

theorem inv_mul_cancel {f : cau_seq β abv} (hf) : inv f hf * f ≈ 1 :=
λ ε ε0, let ⟨K, K0, i, H⟩ := abv_pos_of_not_lim_zero hf in
⟨i, λ j ij,
  by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)),
    abv_zero abv] using ε0⟩

theorem mul_inv_cancel {f : cau_seq β abv} (hf) : f * inv f hf ≈ 1 :=
λ ε ε0, let ⟨K, K0, i, H⟩ := abv_pos_of_not_lim_zero hf in
⟨i, λ j ij,
  by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)),
    abv_zero abv] using ε0⟩

theorem const_inv {x : β} (hx : x ≠ 0) :
  const abv (x⁻¹) = inv (const abv x) (by rwa const_lim_zero) := rfl

end division_ring

section abs
local notation `const` := const abs

/-- The entries of a positive Cauchy sequence eventually have a positive lower bound. -/
def pos (f : cau_seq α abs) : Prop := ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ f j

theorem not_lim_zero_of_pos {f : cau_seq α abs} : pos f → ¬ lim_zero f
| ⟨F, F0, hF⟩ H :=
  let ⟨i, h⟩ := exists_forall_ge_and hF (H _ F0),
      ⟨h₁, h₂⟩ := h _ le_rfl in
  not_lt_of_le h₁ (abs_lt.1 h₂).2

theorem const_pos {x : α} : pos (const x) ↔ 0 < x :=
⟨λ ⟨K, K0, i, h⟩, lt_of_lt_of_le K0 (h _ le_rfl),
 λ h, ⟨x, h, 0, λ j _, le_rfl⟩⟩

theorem add_pos {f g : cau_seq α abs} : pos f → pos g → pos (f + g)
| ⟨F, F0, hF⟩ ⟨G, G0, hG⟩ :=
  let ⟨i, h⟩ := exists_forall_ge_and hF hG in
  ⟨_, _root_.add_pos F0 G0, i,
    λ j ij, let ⟨h₁, h₂⟩ := h _ ij in add_le_add h₁ h₂⟩

theorem pos_add_lim_zero {f g : cau_seq α abs} : pos f → lim_zero g → pos (f + g)
| ⟨F, F0, hF⟩ H :=
  let ⟨i, h⟩ := exists_forall_ge_and hF (H _ (half_pos F0)) in
  ⟨_, half_pos F0, i, λ j ij, begin
    cases h j ij with h₁ h₂,
    have := add_le_add h₁ (le_of_lt (abs_lt.1 h₂).1),
    rwa [← sub_eq_add_neg, sub_self_div_two] at this
  end⟩

protected theorem mul_pos {f g : cau_seq α abs} : pos f → pos g → pos (f * g)
| ⟨F, F0, hF⟩ ⟨G, G0, hG⟩ :=
  let ⟨i, h⟩ := exists_forall_ge_and hF hG in
  ⟨_, _root_.mul_pos F0 G0, i,
    λ j ij, let ⟨h₁, h₂⟩ := h _ ij in
    mul_le_mul h₁ h₂ (le_of_lt G0) (le_trans (le_of_lt F0) h₁)⟩

theorem trichotomy (f : cau_seq α abs) : pos f ∨ lim_zero f ∨ pos (-f) :=
begin
  cases classical.em (lim_zero f); simp *,
  rcases abv_pos_of_not_lim_zero h with ⟨K, K0, hK⟩,
  rcases exists_forall_ge_and hK (f.cauchy₃ K0) with ⟨i, hi⟩,
  refine (le_total 0 (f i)).imp _ _;
    refine (λ h, ⟨K, K0, i, λ j ij, _⟩);
    have := (hi _ ij).1;
    cases hi _ le_rfl with h₁ h₂,
  { rwa abs_of_nonneg at this,
    rw abs_of_nonneg h at h₁,
    exact (le_add_iff_nonneg_right _).1
      (le_trans h₁ $ neg_le_sub_iff_le_add'.1 $
        le_of_lt (abs_lt.1 $ h₂ _ ij).1) },
  { rwa abs_of_nonpos at this,
    rw abs_of_nonpos h at h₁,
    rw [← sub_le_sub_iff_right, zero_sub],
    exact le_trans (le_of_lt (abs_lt.1 $ h₂ _ ij).2) h₁ }
end

instance : has_lt (cau_seq α abs) := ⟨λ f g, pos (g - f)⟩
instance : has_le (cau_seq α abs) := ⟨λ f g, f < g ∨ f ≈ g⟩

theorem lt_of_lt_of_eq {f g h : cau_seq α abs}
  (fg : f < g) (gh : g ≈ h) : f < h :=
show pos (h - f),
by simpa [sub_eq_add_neg, add_comm, add_left_comm] using pos_add_lim_zero fg (neg_lim_zero gh)

theorem lt_of_eq_of_lt {f g h : cau_seq α abs}
  (fg : f ≈ g) (gh : g < h) : f < h :=
by have := pos_add_lim_zero gh (neg_lim_zero fg);
   rwa [← sub_eq_add_neg, sub_sub_sub_cancel_right] at this

theorem lt_trans {f g h : cau_seq α abs} (fg : f < g) (gh : g < h) : f < h :=
show pos (h - f),
by simpa [sub_eq_add_neg, add_comm, add_left_comm] using add_pos fg gh

theorem lt_irrefl {f : cau_seq α abs} : ¬ f < f
| h := not_lim_zero_of_pos h (by simp [zero_lim_zero])

lemma le_of_eq_of_le {f g h : cau_seq α abs}
  (hfg : f ≈ g) (hgh : g ≤ h) : f ≤ h :=
hgh.elim (or.inl ∘ cau_seq.lt_of_eq_of_lt hfg)
  (or.inr ∘ setoid.trans hfg)

lemma le_of_le_of_eq {f g h : cau_seq α abs}
  (hfg : f ≤ g) (hgh : g ≈ h) : f ≤ h :=
hfg.elim (λ h, or.inl (cau_seq.lt_of_lt_of_eq h hgh))
  (λ h, or.inr (setoid.trans h hgh))

instance : preorder (cau_seq α abs) :=
{ lt := (<),
  le := λ f g, f < g ∨ f ≈ g,
  le_refl := λ f, or.inr (setoid.refl _),
  le_trans := λ f g h fg, match fg with
    | or.inl fg, or.inl gh := or.inl $ lt_trans fg gh
    | or.inl fg, or.inr gh := or.inl $ lt_of_lt_of_eq fg gh
    | or.inr fg, or.inl gh := or.inl $ lt_of_eq_of_lt fg gh
    | or.inr fg, or.inr gh := or.inr $ setoid.trans fg gh
    end,
  lt_iff_le_not_le := λ f g,
    ⟨λ h, ⟨or.inl h,
      not_or (mt (lt_trans h) lt_irrefl) (not_lim_zero_of_pos h)⟩,
    λ ⟨h₁, h₂⟩, h₁.resolve_right
      (mt (λ h, or.inr (setoid.symm h)) h₂)⟩ }

theorem le_antisymm {f g : cau_seq α abs} (fg : f ≤ g) (gf : g ≤ f) : f ≈ g :=
fg.resolve_left (not_lt_of_le gf)

theorem lt_total (f g : cau_seq α abs) : f < g ∨ f ≈ g ∨ g < f :=
(trichotomy (g - f)).imp_right
  (λ h, h.imp (λ h, setoid.symm h) (λ h, by rwa neg_sub at h))

theorem le_total (f g : cau_seq α abs) : f ≤ g ∨ g ≤ f :=
(or.assoc.2 (lt_total f g)).imp_right or.inl

theorem const_lt {x y : α} : const x < const y ↔ x < y :=
show pos _ ↔ _, by rw [← const_sub, const_pos, sub_pos]

theorem const_le {x y : α} : const x ≤ const y ↔ x ≤ y :=
by rw le_iff_lt_or_eq; exact or_congr const_lt const_equiv

lemma le_of_exists {f g : cau_seq α abs}
  (h : ∃ i, ∀ j ≥ i, f j ≤ g j) : f ≤ g :=
let ⟨i, hi⟩ := h in
(or.assoc.2 (cau_seq.lt_total f g)).elim
  id
  (λ hgf, false.elim (let ⟨K, hK0, j, hKj⟩ := hgf in
    not_lt_of_ge (hi (max i j) (le_max_left _ _))
      (sub_pos.1 (lt_of_lt_of_le hK0 (hKj _ (le_max_right _ _))))))

theorem exists_gt (f : cau_seq α abs) : ∃ a : α, f < const a :=
let ⟨K, H⟩ := f.bounded in
⟨K + 1, 1, zero_lt_one, 0, λ i _, begin
  rw [sub_apply, const_apply, le_sub_iff_add_le', add_le_add_iff_right],
  exact le_of_lt (abs_lt.1 (H _)).2
end⟩

theorem exists_lt (f : cau_seq α abs) : ∃ a : α, const a < f :=
let ⟨a, h⟩ := (-f).exists_gt in ⟨-a, show pos _,
  by rwa [const_neg, sub_neg_eq_add, add_comm, ← sub_neg_eq_add]⟩

-- so named to match `rat_add_continuous_lemma`
theorem _root_.rat_sup_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} :
  abs (a₁ - b₁) < ε → abs (a₂ - b₂) < ε → abs (a₁ ⊔ a₂ - (b₁ ⊔ b₂)) < ε :=
λ h₁ h₂, (abs_max_sub_max_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)

-- so named to match `rat_add_continuous_lemma`
theorem _root_.rat_inf_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} :
  abs (a₁ - b₁) < ε → abs (a₂ - b₂) < ε → abs (a₁ ⊓ a₂ - (b₁ ⊓ b₂)) < ε :=
λ h₁ h₂, (abs_min_sub_min_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)

instance : has_sup (cau_seq α abs) :=
⟨λ f g, ⟨f ⊔ g, λ ε ε0,
  (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp $ λ i H j ij,
    let ⟨H₁, H₂⟩ := H _ le_rfl in rat_sup_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

instance : has_inf (cau_seq α abs) :=
⟨λ f g, ⟨f ⊓ g, λ ε ε0,
  (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp $ λ i H j ij,
    let ⟨H₁, H₂⟩ := H _ le_rfl in rat_inf_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

@[simp, norm_cast] lemma coe_sup (f g : cau_seq α abs) : ⇑(f ⊔ g) = f ⊔ g := rfl

@[simp, norm_cast] lemma coe_inf (f g : cau_seq α abs) : ⇑(f ⊓ g) = f ⊓ g := rfl

theorem sup_lim_zero {f g : cau_seq α abs}
  (hf : lim_zero f) (hg : lim_zero g) : lim_zero (f ⊔ g)
| ε ε0 := (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp $
  λ i H j ij, let ⟨H₁, H₂⟩ := H _ ij in begin
    rw abs_lt at H₁ H₂ ⊢,
    exact ⟨lt_sup_iff.mpr (or.inl H₁.1), sup_lt_iff.mpr ⟨H₁.2, H₂.2⟩⟩
  end

theorem inf_lim_zero {f g : cau_seq α abs}
  (hf : lim_zero f) (hg : lim_zero g) : lim_zero (f ⊓ g)
| ε ε0 := (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp $
  λ i H j ij, let ⟨H₁, H₂⟩ := H _ ij in begin
    rw abs_lt at H₁ H₂ ⊢,
    exact ⟨lt_inf_iff.mpr ⟨H₁.1, H₂.1⟩, inf_lt_iff.mpr (or.inl H₁.2), ⟩
  end

lemma sup_equiv_sup {a₁ b₁ a₂ b₂ : cau_seq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
  a₁ ⊔ b₁ ≈ a₂ ⊔ b₂ :=
begin
  intros ε ε0,
  obtain ⟨ai, hai⟩ := ha ε ε0,
  obtain ⟨bi, hbi⟩ := hb ε ε0,
  exact ⟨ai ⊔ bi, λ i hi,
    (abs_max_sub_max_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
    (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩,
end

lemma inf_equiv_inf {a₁ b₁ a₂ b₂ : cau_seq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
  a₁ ⊓ b₁ ≈ a₂ ⊓ b₂ :=
begin
  intros ε ε0,
  obtain ⟨ai, hai⟩ := ha ε ε0,
  obtain ⟨bi, hbi⟩ := hb ε ε0,
  exact ⟨ai ⊔ bi, λ i hi,
    (abs_min_sub_min_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
    (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩,
end

protected lemma sup_lt {a b c : cau_seq α abs} (ha : a < c) (hb : b < c) : a ⊔ b < c :=
begin
  obtain ⟨⟨εa, εa0, ia, ha⟩, ⟨εb, εb0, ib, hb⟩⟩ := ⟨ha, hb⟩,
  refine ⟨εa ⊓ εb, lt_inf_iff.mpr ⟨εa0, εb0⟩, ia ⊔ ib, λ i hi, _⟩,
  have := min_le_min (ha _ (sup_le_iff.mp hi).1) (hb _ (sup_le_iff.mp hi).2),
  exact this.trans_eq (min_sub_sub_left _ _ _)
end

protected lemma lt_inf {a b c : cau_seq α abs} (hb : a < b) (hc : a < c) : a < b ⊓ c :=
begin
  obtain ⟨⟨εb, εb0, ib, hb⟩, ⟨εc, εc0, ic, hc⟩⟩ := ⟨hb, hc⟩,
  refine ⟨εb ⊓ εc, lt_inf_iff.mpr ⟨εb0, εc0⟩, ib ⊔ ic, λ i hi, _⟩,
  have := min_le_min (hb _ (sup_le_iff.mp hi).1) (hc _ (sup_le_iff.mp hi).2),
  exact this.trans_eq (min_sub_sub_right _ _ _),
end

@[simp] protected lemma sup_idem (a : cau_seq α abs) : a ⊔ a = a := subtype.ext sup_idem

@[simp] protected lemma inf_idem (a : cau_seq α abs) : a ⊓ a = a := subtype.ext inf_idem

protected lemma sup_comm (a b : cau_seq α abs) : a ⊔ b = b ⊔ a := subtype.ext sup_comm

protected lemma inf_comm (a b : cau_seq α abs) : a ⊓ b = b ⊓ a := subtype.ext inf_comm

protected lemma sup_eq_right {a b : cau_seq α abs} (h : a ≤ b) :
  a ⊔ b ≈ b :=
begin
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h,
  { intros _ _,
    refine ⟨i, λ j hj, _⟩,
    dsimp,
    erw ←max_sub_sub_right,
    rwa [sub_self, max_eq_right, abs_zero],
    rw [sub_nonpos, ←sub_nonneg],
    exact ε0.le.trans (h _ hj) },
  { refine setoid.trans (sup_equiv_sup h (setoid.refl _)) _,
    rw cau_seq.sup_idem,
    exact setoid.refl _ },
end

protected lemma inf_eq_right {a b : cau_seq α abs} (h : b ≤ a) :
  a ⊓ b ≈ b :=
begin
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h,
  { intros _ _,
    refine ⟨i, λ j hj, _⟩,
    dsimp,
    erw ←min_sub_sub_right,
    rwa [sub_self, min_eq_right, abs_zero],
    exact ε0.le.trans (h _ hj) },
  { refine setoid.trans (inf_equiv_inf (setoid.symm h) (setoid.refl _)) _,
    rw cau_seq.inf_idem,
    exact setoid.refl _ },
end

protected lemma sup_eq_left {a b : cau_seq α abs} (h : b ≤ a) :
  a ⊔ b ≈ a :=
by simpa only [cau_seq.sup_comm] using cau_seq.sup_eq_right h

protected lemma inf_eq_left {a b : cau_seq α abs} (h : a ≤ b) :
  a ⊓ b ≈ a :=
by simpa only [cau_seq.inf_comm] using cau_seq.inf_eq_right h

protected lemma le_sup_left {a b : cau_seq α abs} : a ≤ a ⊔ b :=
le_of_exists ⟨0, λ j hj, le_sup_left⟩

protected lemma inf_le_left {a b : cau_seq α abs} : a ⊓ b ≤ a :=
le_of_exists ⟨0, λ j hj, inf_le_left⟩

protected lemma le_sup_right {a b : cau_seq α abs} : b ≤ a ⊔ b :=
le_of_exists ⟨0, λ j hj, le_sup_right⟩

protected lemma inf_le_right {a b : cau_seq α abs} : a ⊓ b ≤ b :=
le_of_exists ⟨0, λ j hj, inf_le_right⟩

protected lemma sup_le {a b c : cau_seq α abs} (ha : a ≤ c) (hb : b ≤ c) : a ⊔ b ≤ c :=
begin
  cases ha with ha ha,
  { cases hb with hb hb,
    { exact or.inl (cau_seq.sup_lt ha hb) },
    { replace ha := le_of_le_of_eq ha.le (setoid.symm hb),
      refine le_of_le_of_eq (or.inr _) hb,
      exact cau_seq.sup_eq_right ha }, },
  { replace hb := le_of_le_of_eq hb (setoid.symm ha),
    refine le_of_le_of_eq (or.inr _) ha,
    exact cau_seq.sup_eq_left hb }
end

protected lemma le_inf {a b c : cau_seq α abs} (hb : a ≤ b) (hc : a ≤ c) : a ≤ b ⊓ c :=
begin
  cases hb with hb hb,
  { cases hc with hc hc,
    { exact or.inl (cau_seq.lt_inf hb hc) },
    { replace hb := le_of_eq_of_le (setoid.symm hc) hb.le,
      refine le_of_eq_of_le hc (or.inr _),
      exact setoid.symm (cau_seq.inf_eq_right hb) }, },
  { replace hc := le_of_eq_of_le (setoid.symm hb) hc,
    refine le_of_eq_of_le hb (or.inr _),
    exact setoid.symm (cau_seq.inf_eq_left hc) }
end

/-! Note that `distrib_lattice (cau_seq α abs)` is not true because there is no `partial_order`. -/

protected lemma sup_inf_distrib_left (a b c : cau_seq α abs) : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) :=
subtype.ext $ funext $ λ i, max_min_distrib_left

protected lemma sup_inf_distrib_right (a b c : cau_seq α abs) : (a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
subtype.ext $ funext $ λ i, max_min_distrib_right

end abs

end cau_seq
