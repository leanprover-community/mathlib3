/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.order.absolute_value
import algebra.big_operators.order

/-!
# Cauchy sequences

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

open_locale big_operators

open is_absolute_value

theorem exists_forall_ge_and {α} [linear_order α] {P Q : α → Prop} :
  (∃ i, ∀ j ≥ i, P j) → (∃ i, ∀ j ≥ i, Q j) →
  ∃ i, ∀ j ≥ i, P j ∧ Q j
| ⟨a, h₁⟩ ⟨b, h₂⟩ := let ⟨c, ac, bc⟩ := exists_ge_of_linear a b in
  ⟨c, λ j hj, ⟨h₁ _ (le_trans ac hj), h₂ _ (le_trans bc hj)⟩⟩

section
variables {α : Type*} [linear_ordered_field α]
  {β : Type*} [ring β] (abv : β → α) [is_absolute_value abv]

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
  {β : Type*} [field β] (abv : β → α) [is_absolute_value abv]
  {ε K : α} (ε0 : 0 < ε) (K0 : 0 < K) :
  ∃ δ > 0, ∀ {a b : β}, K ≤ abv a → K ≤ abv b →
  abv (a - b) < δ → abv (a⁻¹ - b⁻¹) < ε :=
begin
  have KK := mul_pos K0 K0,
  have εK := mul_pos ε0 KK,
  refine ⟨_, εK, λ a b ha hb h, _⟩,
  have a0 := lt_of_lt_of_le K0 ha,
  have b0 := lt_of_lt_of_le K0 hb,
  rw [inv_sub_inv ((abv_pos abv).1 a0) ((abv_pos abv).1 b0),
      abv_div abv, abv_mul abv, mul_comm, abv_sub abv,
      ← mul_div_cancel ε (ne_of_gt KK)],
  exact div_lt_div h
    (mul_le_mul hb ha (le_of_lt K0) (abv_nonneg abv _))
    (le_of_lt $ mul_pos ε0 KK) KK
end
end

/-- A sequence is Cauchy if the distance between its entries tends to zero. -/
def is_cau_seq {α : Type*} [linear_ordered_field α]
  {β : Type*} [ring β] (abv : β → α) (f : ℕ → β) : Prop :=
∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j - f i) < ε

namespace is_cau_seq
variables {α : Type*} [linear_ordered_field α]
  {β : Type*} [ring β] {abv : β → α} [is_absolute_value abv] {f : ℕ → β}

@[nolint ge_or_gt] -- see Note [nolint_ge]
theorem cauchy₂ (hf : is_cau_seq abv f) {ε : α} (ε0 : 0 < ε) :
  ∃ i, ∀ j k ≥ i, abv (f j - f k) < ε :=
begin
  refine (hf _ (half_pos ε0)).imp (λ i hi j k ij ik, _),
  rw ← add_halves ε,
  refine lt_of_le_of_lt (abv_sub_le abv _ _ _) (add_lt_add (hi _ ij) _),
  rw abv_sub abv, exact hi _ ik
end

theorem cauchy₃ (hf : is_cau_seq abv f) {ε : α} (ε0 : 0 < ε) :
  ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - f j) < ε :=
let ⟨i, H⟩ := hf.cauchy₂ ε0 in ⟨i, λ j ij k jk, H _ _ (le_trans ij jk) ij⟩

end is_cau_seq

/-- `cau_seq β abv` is the type of `β`-valued Cauchy sequences, with respect to the absolute value
function `abv`. -/
def cau_seq {α : Type*} [linear_ordered_field α]
  (β : Type*) [ring β] (abv : β → α) : Type* :=
{f : ℕ → β // is_cau_seq abv f}

namespace cau_seq
variables {α : Type*} [linear_ordered_field α]

section ring
variables {β : Type*} [ring β] {abv : β → α}

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
  let R := ∑ j in finset.range (i+1), abv (f j),
  have : ∀ j ≤ i, abv (f j) ≤ R,
  { intros j ij, change (λ j, abv (f j)) j ≤ R,
    apply finset.single_le_sum,
    { intros, apply abv_nonneg abv },
    { rwa [finset.mem_range, nat.lt_succ_iff] } },
  refine ⟨R + 1, λ j, _⟩,
  cases lt_or_le j i with ij ij,
  { exact lt_of_le_of_lt (this _ (le_of_lt ij)) (lt_add_one _) },
  { have := lt_of_le_of_lt (abv_add abv _ _)
      (add_lt_add_of_le_of_lt (this _ (le_refl _)) (h _ ij)),
    rw [add_sub, add_comm] at this, simpa }
end

theorem bounded' (f : cau_seq β abv) (x : α) : ∃ r > x, ∀ i, abv (f i) < r :=
let ⟨r, h⟩ := f.bounded in
⟨max r (x+1), lt_of_lt_of_le (lt_add_one _) (le_max_right _ _),
  λ i, lt_of_lt_of_le (h i) (le_max_left _ _)⟩

instance : has_add (cau_seq β abv) :=
⟨λ f g, ⟨λ i, (f i + g i : β), λ ε ε0,
  let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abv ε0,
      ⟨i, H⟩ := exists_forall_ge_and (f.cauchy₃ δ0) (g.cauchy₃ δ0) in
  ⟨i, λ j ij, let ⟨H₁, H₂⟩ := H _ (le_refl _) in Hδ (H₁ _ ij) (H₂ _ ij)⟩⟩⟩

@[simp] theorem add_apply (f g : cau_seq β abv) (i : ℕ) : (f + g) i = f i + g i := rfl

variable (abv)

/-- The constant Cauchy sequence. -/
def const (x : β) : cau_seq β abv :=
⟨λ i, x, λ ε ε0, ⟨0, λ j ij, by simpa [abv_zero abv] using ε0⟩⟩

variable {abv}

local notation `const` := const abv

@[simp] theorem const_apply (x : β) (i : ℕ) : (const x : ℕ → β) i = x := rfl

theorem const_inj {x y : β} : (const x : cau_seq β abv) = const y ↔ x = y :=
⟨λ h, congr_arg (λ f:cau_seq β abv, (f:ℕ→β) 0) h, congr_arg _⟩

instance : has_zero (cau_seq β abv) := ⟨const 0⟩
instance : has_one (cau_seq β abv) := ⟨const 1⟩
instance : inhabited (cau_seq β abv) := ⟨0⟩

@[simp] theorem zero_apply (i) : (0 : cau_seq β abv) i = 0 := rfl
@[simp] theorem one_apply (i) : (1 : cau_seq β abv) i = 1 := rfl
@[simp] theorem const_zero : const 0 = 0 := rfl

theorem const_add (x y : β) : const (x + y) = const x + const y :=
ext $ λ i, rfl

instance : has_mul (cau_seq β abv) :=
⟨λ f g, ⟨λ i, (f i * g i : β), λ ε ε0,
  let ⟨F, F0, hF⟩ := f.bounded' 0, ⟨G, G0, hG⟩ := g.bounded' 0,
      ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abv ε0,
      ⟨i, H⟩ := exists_forall_ge_and (f.cauchy₃ δ0) (g.cauchy₃ δ0) in
  ⟨i, λ j ij, let ⟨H₁, H₂⟩ := H _ (le_refl _) in
    Hδ (hF j) (hG i) (H₁ _ ij) (H₂ _ ij)⟩⟩⟩

@[simp] theorem mul_apply (f g : cau_seq β abv) (i : ℕ) : (f * g) i = f i * g i := rfl

theorem const_mul (x y : β) : const (x * y) = const x * const y :=
ext $ λ i, rfl

instance : has_neg (cau_seq β abv) :=
⟨λ f, of_eq (const (-1) * f) (λ x, -f x) (λ i, by simp)⟩

@[simp] theorem neg_apply (f : cau_seq β abv) (i) : (-f) i = -f i := rfl

theorem const_neg (x : β) : const (-x) = -const x :=
ext $ λ i, rfl

instance : has_sub (cau_seq β abv) :=
⟨λ f g, of_eq (f + -g) (λ x, f x - g x) (λ i, by simp [sub_eq_add_neg])⟩

@[simp] theorem sub_apply (f g : cau_seq β abv) (i : ℕ) : (f - g) i = f i - g i := rfl

theorem const_sub (x y : β) : const (x - y) = const x - const y :=
ext $ λ i, rfl

instance : ring (cau_seq β abv) :=
by refine_struct
     { neg := has_neg.neg,
       add := (+),
       zero := (0 : cau_seq β abv),
       mul := (*),
       one := 1,
       sub := has_sub.sub,
       npow := @npow_rec (cau_seq β abv) ⟨1⟩ ⟨(*)⟩,
       nsmul := @nsmul_rec (cau_seq β abv) ⟨0⟩ ⟨(+)⟩,
       gsmul := @gsmul_rec (cau_seq β abv) ⟨0⟩ ⟨(+)⟩ ⟨has_neg.neg⟩ };
intros; try { refl }; apply ext;
simp [mul_add, mul_assoc, add_mul, add_comm, add_left_comm, sub_eq_add_neg]

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
  λ ε ε0, let ⟨i, hi⟩ := H _ ε0 in le_of_lt $ hi _ (le_refl _),
λ e, e.symm ▸ zero_lim_zero⟩

instance equiv : setoid (cau_seq β abv) :=
⟨λ f g, lim_zero (f - g),
⟨λ f, by simp [zero_lim_zero],
 λ f g h, by simpa using neg_lim_zero h,
 λ f g h fg gh, by simpa [sub_eq_add_neg, add_assoc] using add_lim_zero fg gh⟩⟩

lemma add_equiv_add {f1 f2 g1 g2 : cau_seq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
  f1 + g1 ≈ f2 + g2 :=
begin
  change lim_zero ((f1 + g1) - _),
  convert add_lim_zero hf hg using 1,
  simp only [sub_eq_add_neg, add_assoc],
  rw add_comm (-f2), simp only [add_assoc],
  congr' 2, simp
end

lemma neg_equiv_neg {f g : cau_seq β abv} (hf : f ≈ g) : -f ≈ -g :=
begin
  have hf : lim_zero _ := neg_lim_zero hf,
  show lim_zero (-f - -g),
  convert hf using 1, simp
end

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
    cases hi _ (le_refl _) with h₁ h₂, rw abv_sub abv at h₁,
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

end ring

section comm_ring
variables {β : Type*} [comm_ring β] {abv : β → α} [is_absolute_value abv]

lemma mul_equiv_zero' (g : cau_seq _ abv) {f : cau_seq _ abv} (hf : f ≈ 0) : f * g ≈ 0 :=
by rw mul_comm; apply mul_equiv_zero _ hf

end comm_ring

section is_domain
variables {β : Type*} [ring β] [is_domain β] (abv : β → α) [is_absolute_value abv]

lemma one_not_equiv_zero : ¬ (const abv 1) ≈ (const abv 0) :=
assume h,
have ∀ ε > 0, ∃ i, ∀ k, i ≤ k → abv (1 - 0) < ε, from h,
have h1 : abv 1 ≤ 0, from le_of_not_gt $
  assume h2 : 0 < abv 1,
  exists.elim (this _ h2) $ λ i hi,
    lt_irrefl (abv 1) $ by simpa using hi _ (le_refl _),
have h2 : 0 ≤ abv 1, from is_absolute_value.abv_nonneg _ _,
have abv 1 = 0, from le_antisymm h1 h2,
have (1 : β) = 0, from (is_absolute_value.abv_eq_zero abv).1 this,
absurd this one_ne_zero

end is_domain

section field
variables {β : Type*} [field β] {abv : β → α} [is_absolute_value abv]

theorem inv_aux {f : cau_seq β abv} (hf : ¬ lim_zero f) :
  ∀ ε > 0, ∃ i, ∀ j ≥ i, abv ((f j)⁻¹ - (f i)⁻¹) < ε | ε ε0 :=
let ⟨K, K0, HK⟩ := abv_pos_of_not_lim_zero hf,
    ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abv ε0 K0,
    ⟨i, H⟩ := exists_forall_ge_and HK (f.cauchy₃ δ0) in
⟨i, λ j ij, let ⟨iK, H'⟩ := H _ (le_refl _) in Hδ (H _ ij).1 iK (H' _ ij)⟩

/-- Given a Cauchy sequence `f` with nonzero limit, create a Cauchy sequence with values equal to
the inverses of the values of `f`. -/
def inv (f : cau_seq β abv) (hf : ¬ lim_zero f) : cau_seq β abv := ⟨_, inv_aux hf⟩

@[simp] theorem inv_apply {f : cau_seq β abv} (hf i) : inv f hf i = (f i)⁻¹ := rfl

theorem inv_mul_cancel {f : cau_seq β abv} (hf) : inv f hf * f ≈ 1 :=
λ ε ε0, let ⟨K, K0, i, H⟩ := abv_pos_of_not_lim_zero hf in
⟨i, λ j ij,
  by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)),
    abv_zero abv] using ε0⟩

theorem const_inv {x : β} (hx : x ≠ 0) :
  const abv (x⁻¹) = inv (const abv x) (by rwa const_lim_zero) :=
ext (assume n, by simp[inv_apply, const_apply])

end field

section abs
local notation `const` := const abs

/-- The entries of a positive Cauchy sequence eventually have a positive lower bound. -/
def pos (f : cau_seq α abs) : Prop := ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ f j

theorem not_lim_zero_of_pos {f : cau_seq α abs} : pos f → ¬ lim_zero f
| ⟨F, F0, hF⟩ H :=
  let ⟨i, h⟩ := exists_forall_ge_and hF (H _ F0),
      ⟨h₁, h₂⟩ := h _ (le_refl _) in
  not_lt_of_le h₁ (abs_lt.1 h₂).2

theorem const_pos {x : α} : pos (const x) ↔ 0 < x :=
⟨λ ⟨K, K0, i, h⟩, lt_of_lt_of_le K0 (h _ (le_refl _)),
 λ h, ⟨x, h, 0, λ j _, le_refl _⟩⟩

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
    cases hi _ (le_refl _) with h₁ h₂,
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

end abs

end cau_seq
