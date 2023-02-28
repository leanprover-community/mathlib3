/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import algebra.hom.ring
import algebra.order.monoid.with_top
import algebra.order.ring.canonical

/-! # Structures involving `*` and `0` on `with_top` and `with_bot`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The main results of this section are `with_top.canonically_ordered_comm_semiring` and
`with_bot.ordered_comm_semiring`.
-/

variables {α : Type*}

namespace with_top

instance [nonempty α] : nontrivial (with_top α) := option.nontrivial

variable [decidable_eq α]

section has_mul

variables [has_zero α] [has_mul α]

instance : mul_zero_class (with_top α) :=
{ zero := 0,
  mul := λ m n, if m = 0 ∨ n = 0 then 0 else option.map₂ (*) m n,
  zero_mul := assume a, if_pos $ or.inl rfl,
  mul_zero := assume a, if_pos $ or.inr rfl }

lemma mul_def {a b : with_top α} : a * b = if a = 0 ∨ b = 0 then 0 else option.map₂ (*) a b := rfl

lemma mul_top' {a : with_top α} : a * ⊤ = if a = 0 then 0 else ⊤ :=
by induction a using with_top.rec_top_coe; simp [mul_def]; refl

@[simp] lemma mul_top {a : with_top α} (h : a ≠ 0) : a * ⊤ = ⊤ := by rw [mul_top', if_neg h]

lemma top_mul' {a : with_top α} : ⊤ * a = if a = 0 then 0 else ⊤ :=
by induction a using with_top.rec_top_coe; simp [mul_def]; refl

@[simp] lemma top_mul {a : with_top α} (h : a ≠ 0) : ⊤ * a = ⊤ := by rw [top_mul', if_neg h]

@[simp] lemma top_mul_top : (⊤ * ⊤ : with_top α) = ⊤ :=
top_mul top_ne_zero

theorem mul_eq_top_iff {a b : with_top α} : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 :=
begin
  rw [mul_def, ite_eq_iff, ← none_eq_top, option.map₂_eq_none_iff],
  have ha : a = 0 → a ≠ none := λ h, h.symm ▸ zero_ne_top,
  have hb : b = 0 → b ≠ none := λ h, h.symm ▸ zero_ne_top,
  tauto
end

theorem mul_lt_top' [has_lt α] {a b : with_top α} (ha : a < ⊤) (hb : b < ⊤) : a * b < ⊤ :=
begin
  rw [with_top.lt_top_iff_ne_top] at *,
  simp only [ne.def, mul_eq_top_iff, *, and_false, false_and, false_or, not_false_iff]
end

theorem mul_lt_top [has_lt α] {a b : with_top α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b < ⊤ :=
  mul_lt_top' (with_top.lt_top_iff_ne_top.2 ha) (with_top.lt_top_iff_ne_top.2 hb)

instance [no_zero_divisors α] : no_zero_divisors (with_top α) :=
begin
  refine ⟨λ a b h₁, decidable.by_contradiction $ λ h₂, _⟩,
  rw [mul_def, if_neg h₂] at h₁,
  rcases option.mem_map₂_iff.1 h₁ with ⟨a, b, (rfl : _ = _), (rfl : _ = _), hab⟩,
  exact h₂ ((eq_zero_or_eq_zero_of_mul_eq_zero hab).imp (congr_arg some) (congr_arg some))
end

end has_mul

section mul_zero_class

variables [mul_zero_class α]

@[simp, norm_cast] lemma coe_mul {a b : α} : (↑(a * b) : with_top α) = a * b :=
decidable.by_cases (assume : a = 0, by simp [this]) $ assume ha,
decidable.by_cases (assume : b = 0, by simp [this]) $ assume hb,
by { simp [*, mul_def] }

lemma mul_coe {b : α} (hb : b ≠ 0) : ∀{a : with_top α}, a * b = a.bind (λa:α, ↑(a * b))
| none     := show (if (⊤:with_top α) = 0 ∨ (b:with_top α) = 0 then 0 else ⊤ : with_top α) = ⊤,
    by simp [hb]
| (some a) := show ↑a * ↑b = ↑(a * b), from coe_mul.symm

@[simp] lemma untop'_zero_mul (a b : with_top α) : (a * b).untop' 0 = a.untop' 0 * b.untop' 0 :=
begin
  by_cases ha : a = 0, { rw [ha, zero_mul, ← coe_zero, untop'_coe, zero_mul] },
  by_cases hb : b = 0, { rw [hb, mul_zero, ← coe_zero, untop'_coe, mul_zero] },
  induction a using with_top.rec_top_coe, { rw [top_mul hb, untop'_top, zero_mul] },
  induction b using with_top.rec_top_coe, { rw [mul_top ha, untop'_top, mul_zero] },
  rw [← coe_mul, untop'_coe, untop'_coe, untop'_coe]
end

end mul_zero_class

/-- `nontrivial α` is needed here as otherwise we have `1 * ⊤ = ⊤` but also `0 * ⊤ = 0`. -/
instance [mul_zero_one_class α] [nontrivial α] : mul_zero_one_class (with_top α) :=
{ mul := (*),
  one := 1,
  zero := 0,
  one_mul := λ a, match a with
  | ⊤       := mul_top (mt coe_eq_coe.1 one_ne_zero)
  | (a : α) := by rw [← coe_one, ← coe_mul, one_mul]
  end,
  mul_one := λ a, match a with
  | ⊤       := top_mul (mt coe_eq_coe.1 one_ne_zero)
  | (a : α) := by rw [← coe_one, ← coe_mul, mul_one]
  end,
  .. with_top.mul_zero_class }

/-- A version of `with_top.map` for `monoid_with_zero_hom`s. -/
@[simps { fully_applied := ff }] protected def _root_.monoid_with_zero_hom.with_top_map
  {R S : Type*} [mul_zero_one_class R] [decidable_eq R] [nontrivial R]
  [mul_zero_one_class S] [decidable_eq S] [nontrivial S] (f : R →*₀ S) (hf : function.injective f) :
  with_top R →*₀ with_top S :=
{ to_fun := with_top.map f,
  map_mul' := λ x y,
    begin
      have : ∀ z, map f z = 0 ↔ z = 0,
        from λ z, (option.map_injective hf).eq_iff' f.to_zero_hom.with_top_map.map_zero,
      rcases decidable.eq_or_ne x 0 with rfl|hx, { simp },
      rcases decidable.eq_or_ne y 0 with rfl|hy, { simp },
      induction x using with_top.rec_top_coe, { simp [hy, this] },
      induction y using with_top.rec_top_coe,
      { have : (f x : with_top S) ≠ 0, by simpa [hf.eq_iff' (map_zero f)] using hx,
        simp [hx, this] },
      simp only [← coe_mul, map_coe, map_mul]
    end,
  .. f.to_zero_hom.with_top_map, .. f.to_monoid_hom.to_one_hom.with_top_map }

instance [semigroup_with_zero α] [no_zero_divisors α] : semigroup_with_zero (with_top α) :=
{ mul := (*),
  zero := 0,
  mul_assoc := λ a b c, begin
    rcases eq_or_ne a 0 with rfl|ha, { simp only [zero_mul] },
    rcases eq_or_ne b 0 with rfl|hb, { simp only [zero_mul, mul_zero] },
    rcases eq_or_ne c 0 with rfl|hc, { simp only [mul_zero] },
    induction a using with_top.rec_top_coe, { simp [hb, hc] },
    induction b using with_top.rec_top_coe, { simp [ha, hc] },
    induction c using with_top.rec_top_coe, { simp [ha, hb] },
    simp only [← coe_mul, mul_assoc]
  end,
  .. with_top.mul_zero_class }

instance [monoid_with_zero α] [no_zero_divisors α] [nontrivial α] : monoid_with_zero (with_top α) :=
{ .. with_top.mul_zero_one_class, .. with_top.semigroup_with_zero }

instance [comm_monoid_with_zero α] [no_zero_divisors α] [nontrivial α] :
  comm_monoid_with_zero (with_top α) :=
{ mul := (*),
  zero := 0,
  mul_comm := λ a b,
    by simp only [or_comm, mul_def, mul_comm, @option.map₂_comm _ _ _ _ a b _ mul_comm],
  .. with_top.monoid_with_zero }

variables [canonically_ordered_comm_semiring α]

private lemma distrib' (a b c : with_top α) : (a + b) * c = a * c + b * c :=
begin
  induction c using with_top.rec_top_coe,
  { by_cases ha : a = 0; simp [ha] },
  { by_cases hc : c = 0, { simp [hc] },
    simp only [mul_coe hc], cases a; cases b,
    repeat { refl <|> exact congr_arg some (add_mul _ _ _) } }
end

/-- This instance requires `canonically_ordered_comm_semiring` as it is the smallest class
that derives from both `non_assoc_non_unital_semiring` and `canonically_ordered_add_monoid`, both
of which are required for distributivity. -/
instance [nontrivial α] : comm_semiring (with_top α) :=
{ right_distrib   := distrib',
  left_distrib    := λ a b c, by { rw [mul_comm, distrib', mul_comm b, mul_comm c], refl },
  .. with_top.add_comm_monoid_with_one, .. with_top.comm_monoid_with_zero }

instance [nontrivial α] : canonically_ordered_comm_semiring (with_top α) :=
{ .. with_top.comm_semiring,
  .. with_top.canonically_ordered_add_monoid,
  .. with_top.no_zero_divisors, }

/-- A version of `with_top.map` for `ring_hom`s. -/
@[simps { fully_applied := ff }] protected def _root_.ring_hom.with_top_map
  {R S : Type*} [canonically_ordered_comm_semiring R] [decidable_eq R] [nontrivial R]
  [canonically_ordered_comm_semiring S] [decidable_eq S] [nontrivial S]
  (f : R →+* S) (hf : function.injective f) :
  with_top R →+* with_top S :=
{ to_fun := with_top.map f,
  .. f.to_monoid_with_zero_hom.with_top_map hf, .. f.to_add_monoid_hom.with_top_map }

end with_top

namespace with_bot

instance [nonempty α] : nontrivial (with_bot α) := option.nontrivial

variable [decidable_eq α]

section has_mul

variables [has_zero α] [has_mul α]

instance : mul_zero_class (with_bot α) :=
with_top.mul_zero_class

lemma mul_def {a b : with_bot α} :
  a * b = if a = 0 ∨ b = 0 then 0 else option.map₂ (*) a b := rfl

@[simp] lemma mul_bot {a : with_bot α} (h : a ≠ 0) : a * ⊥ = ⊥ :=
with_top.mul_top h

@[simp] lemma bot_mul {a : with_bot α} (h : a ≠ 0) : ⊥ * a = ⊥ :=
with_top.top_mul h

@[simp] lemma bot_mul_bot : (⊥ * ⊥ : with_bot α) = ⊥ :=
with_top.top_mul_top

theorem mul_eq_bot_iff {a b : with_bot α} : a * b = ⊥ ↔ a ≠ 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b ≠ 0 :=
with_top.mul_eq_top_iff

theorem bot_lt_mul' [has_lt α] {a b : with_bot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b :=
@with_top.mul_lt_top' αᵒᵈ _ _ _ _ _ _ ha hb

theorem bot_lt_mul [has_lt α] {a b : with_bot α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : ⊥ < a * b :=
@with_top.mul_lt_top αᵒᵈ _ _ _ _ _ _ ha hb

end has_mul

section mul_zero_class

variables [mul_zero_class α]

@[norm_cast] lemma coe_mul {a b : α} : (↑(a * b) : with_bot α) = a * b :=
with_top.coe_mul

lemma mul_coe {b : α} (hb : b ≠ 0) {a : with_bot α} : a * b = a.bind (λa:α, ↑(a * b)) :=
with_top.mul_coe hb

end mul_zero_class

/-- `nontrivial α` is needed here as otherwise we have `1 * ⊥ = ⊥` but also `= 0 * ⊥ = 0`. -/
instance [mul_zero_one_class α] [nontrivial α] : mul_zero_one_class (with_bot α) :=
with_top.mul_zero_one_class

instance [mul_zero_class α] [no_zero_divisors α] : no_zero_divisors (with_bot α) :=
with_top.no_zero_divisors

instance [semigroup_with_zero α] [no_zero_divisors α] : semigroup_with_zero (with_bot α) :=
with_top.semigroup_with_zero

instance [monoid_with_zero α] [no_zero_divisors α] [nontrivial α] : monoid_with_zero (with_bot α) :=
with_top.monoid_with_zero

instance [comm_monoid_with_zero α] [no_zero_divisors α] [nontrivial α] :
  comm_monoid_with_zero (with_bot α) :=
with_top.comm_monoid_with_zero

instance [canonically_ordered_comm_semiring α] [nontrivial α] : comm_semiring (with_bot α) :=
with_top.comm_semiring

instance [mul_zero_class α] [preorder α] [pos_mul_mono α] :
  pos_mul_mono (with_bot α) :=
⟨begin
  rintros ⟨x, x0⟩ a b h, simp only [subtype.coe_mk],
  rcases eq_or_ne x 0 with rfl | x0', { simp, },
  lift x to α, { rintro ⟨rfl⟩, exact (with_bot.bot_lt_coe (0 : α)).not_le x0, },
  induction a using with_bot.rec_bot_coe, { simp_rw [mul_bot x0', bot_le] },
  induction b using with_bot.rec_bot_coe, { exact absurd h (bot_lt_coe a).not_le },
  simp only [← coe_mul, coe_le_coe] at *,
  norm_cast at x0,
  exact mul_le_mul_of_nonneg_left h x0,
end ⟩

instance [mul_zero_class α] [preorder α] [mul_pos_mono α] :
  mul_pos_mono (with_bot α) :=
⟨begin
  rintros ⟨x, x0⟩ a b h, simp only [subtype.coe_mk],
  rcases eq_or_ne x 0 with rfl | x0', { simp, },
  lift x to α, { rintro ⟨rfl⟩, exact (with_bot.bot_lt_coe (0 : α)).not_le x0, },
  induction a using with_bot.rec_bot_coe, { simp_rw [bot_mul x0', bot_le] },
  induction b using with_bot.rec_bot_coe, { exact absurd h (bot_lt_coe a).not_le },
  simp only [← coe_mul, coe_le_coe] at *,
  norm_cast at x0,
  exact mul_le_mul_of_nonneg_right h x0,
end ⟩

instance [mul_zero_class α] [preorder α] [pos_mul_strict_mono α] :
  pos_mul_strict_mono (with_bot α) :=
⟨begin
  rintros ⟨x, x0⟩ a b h, simp only [subtype.coe_mk],
  lift x to α using x0.ne_bot,
  induction b using with_bot.rec_bot_coe, { exact absurd h not_lt_bot, },
  induction a using with_bot.rec_bot_coe, { simp_rw [mul_bot x0.ne.symm, ← coe_mul, bot_lt_coe], },
  simp only [← coe_mul, coe_lt_coe] at *,
  norm_cast at x0,
  exact mul_lt_mul_of_pos_left h x0,
end ⟩

instance [mul_zero_class α] [preorder α] [mul_pos_strict_mono α] :
  mul_pos_strict_mono (with_bot α) :=
⟨begin
  rintros ⟨x, x0⟩ a b h, simp only [subtype.coe_mk],
  lift x to α using x0.ne_bot,
  induction b using with_bot.rec_bot_coe, { exact absurd h not_lt_bot, },
  induction a using with_bot.rec_bot_coe, { simp_rw [bot_mul x0.ne.symm, ← coe_mul, bot_lt_coe], },
  simp only [← coe_mul, coe_lt_coe] at *,
  norm_cast at x0,
  exact mul_lt_mul_of_pos_right h x0,
end ⟩

instance [mul_zero_class α] [preorder α] [pos_mul_reflect_lt α] :
  pos_mul_reflect_lt (with_bot α) :=
⟨begin
  rintros ⟨x, x0⟩ a b h, simp only [subtype.coe_mk] at h,
  rcases eq_or_ne x 0 with rfl | x0', { simpa using h, },
  lift x to α, { rintro ⟨rfl⟩, exact (with_bot.bot_lt_coe (0 : α)).not_le x0, },
  induction b using with_bot.rec_bot_coe, { rw [mul_bot x0'] at h, exact absurd h bot_le.not_lt, },
  induction a using with_bot.rec_bot_coe, { exact with_bot.bot_lt_coe _, },
  simp only [← coe_mul, coe_lt_coe] at *,
  norm_cast at x0,
  exact lt_of_mul_lt_mul_left h x0,
end ⟩

instance [mul_zero_class α] [preorder α] [mul_pos_reflect_lt α] :
  mul_pos_reflect_lt (with_bot α) :=
⟨begin
  rintros ⟨x, x0⟩ a b h, simp only [subtype.coe_mk] at h,
  rcases eq_or_ne x 0 with rfl | x0', { simpa using h, },
  lift x to α, { rintro ⟨rfl⟩, exact (with_bot.bot_lt_coe (0 : α)).not_le x0, },
  induction b using with_bot.rec_bot_coe, { rw [bot_mul x0'] at h, exact absurd h bot_le.not_lt, },
  induction a using with_bot.rec_bot_coe, { exact with_bot.bot_lt_coe _, },
  simp only [← coe_mul, coe_lt_coe] at *,
  norm_cast at x0,
  exact lt_of_mul_lt_mul_right h x0,
end ⟩

instance [mul_zero_class α] [preorder α] [pos_mul_mono_rev α] :
  pos_mul_mono_rev (with_bot α) :=
⟨begin
  rintros ⟨x, x0⟩ a b h, simp only [subtype.coe_mk] at h,
  lift x to α using x0.ne_bot,
  induction a using with_bot.rec_bot_coe, { exact bot_le, },
  induction b using with_bot.rec_bot_coe,
  { rw [mul_bot x0.ne.symm, ← coe_mul] at h, exact absurd h (bot_lt_coe (x * a)).not_le, },
  simp only [← coe_mul, coe_le_coe] at *,
  norm_cast at x0,
  exact le_of_mul_le_mul_left h x0,
end ⟩

instance [mul_zero_class α] [preorder α] [mul_pos_mono_rev α] :
  mul_pos_mono_rev (with_bot α) :=
⟨begin
  rintros ⟨x, x0⟩ a b h, simp only [subtype.coe_mk] at h,
  lift x to α using x0.ne_bot,
  induction a using with_bot.rec_bot_coe, { exact bot_le, },
  induction b using with_bot.rec_bot_coe,
  { rw [bot_mul x0.ne.symm, ← coe_mul] at h, exact absurd h (bot_lt_coe (a * x)).not_le, },
  simp only [← coe_mul, coe_le_coe] at *,
  norm_cast at x0,
  exact le_of_mul_le_mul_right h x0,
end ⟩

instance [canonically_ordered_comm_semiring α] [nontrivial α] :
  ordered_comm_semiring (with_bot α) :=
{ mul_le_mul_of_nonneg_left  := λ _ _ _, mul_le_mul_of_nonneg_left,
  mul_le_mul_of_nonneg_right := λ _ _ _, mul_le_mul_of_nonneg_right,
  .. with_bot.zero_le_one_class,
  .. with_bot.ordered_add_comm_monoid,
  .. with_bot.comm_semiring, }

end with_bot
