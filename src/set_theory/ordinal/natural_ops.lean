/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.ordinal.arithmetic
import tactic.abel

/-!
# Natural operations on ordinals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The goal of this file is to define natural addition and multiplication on ordinals, also known as
the Hessenberg sum and product, and provide a basic API. The natural addition of two ordinals
`a ♯ b` is recursively defined as the least ordinal greater than `a' ♯ b` and `a ♯ b'` for `a' < a`
and `b' < b`. The natural multiplication `a ⨳ b` is likewise recursively defined as the least
ordinal such that `a ⨳ b ♯ a' ⨳ b'` is greater than `a' ⨳ b ♯ a ⨳ b'` for any `a' < a` and
`b' < b`.

These operations form a rich algebraic structure: they're commutative, associative, preserve order,
have the usual `0` and `1` from ordinals, and distribute over one another.

Moreover, these operations are the addition and multiplication of ordinals when viewed as
combinatorial `game`s. This makes them particularly useful for game theory.

Finally, both operations admit simple, intuitive descriptions in terms of the Cantor normal form.
The natural addition of two ordinals corresponds to adding their Cantor normal forms as if they were
polynomials in `ω`. Likewise, their natural multiplication corresponds to multiplying the Cantor
normal forms as polynomials.

# Implementation notes

Given the rich algebraic structure of these two operations, we choose to create a type synonym
`nat_ordinal`, where we provide the appropriate instances. However, to avoid casting back and forth
between both types, we attempt to prove and state most results on `ordinal`.

# Todo

- Prove the characterizations of natural addition and multiplication in terms of the Cantor normal
  form.
-/

universes u v

open function order

noncomputable theory

/-! ### Basic casts between `ordinal` and `nat_ordinal` -/

/-- A type synonym for ordinals with natural addition and multiplication. -/
@[derive [has_zero, inhabited, has_one, linear_order, succ_order, has_well_founded]]
def nat_ordinal : Type* := ordinal

/-- The identity function between `ordinal` and `nat_ordinal`. -/
@[pattern] def ordinal.to_nat_ordinal : ordinal ≃o nat_ordinal := order_iso.refl _

/-- The identity function between `nat_ordinal` and `ordinal`. -/
@[pattern] def nat_ordinal.to_ordinal : nat_ordinal ≃o ordinal := order_iso.refl _

namespace nat_ordinal

open ordinal

variables {a b c : nat_ordinal.{u}}

@[simp] theorem to_ordinal_symm_eq : nat_ordinal.to_ordinal.symm = ordinal.to_nat_ordinal := rfl
@[simp] theorem to_ordinal_to_nat_ordinal (a : nat_ordinal) : a.to_ordinal.to_nat_ordinal = a := rfl

theorem lt_wf : @well_founded nat_ordinal (<) := ordinal.lt_wf
instance : well_founded_lt nat_ordinal := ordinal.well_founded_lt
instance : is_well_order nat_ordinal (<) := ordinal.has_lt.lt.is_well_order

@[simp] theorem to_ordinal_zero : to_ordinal 0 = 0 := rfl
@[simp] theorem to_ordinal_one : to_ordinal 1 = 1 := rfl

@[simp] theorem to_ordinal_eq_zero (a) : to_ordinal a = 0 ↔ a = 0 := iff.rfl
@[simp] theorem to_ordinal_eq_one (a) : to_ordinal a = 1 ↔ a = 1 := iff.rfl

@[simp] theorem to_ordinal_max : (max a b).to_ordinal = max a.to_ordinal b.to_ordinal := rfl
@[simp] theorem to_ordinal_min : (min a b).to_ordinal = min a.to_ordinal b.to_ordinal := rfl

theorem succ_def (a : nat_ordinal) : succ a = (a.to_ordinal + 1).to_nat_ordinal := rfl

/-- A recursor for `nat_ordinal`. Use as `induction x using nat_ordinal.rec`. -/
protected def rec {β : nat_ordinal → Sort*} (h : Π a, β (to_nat_ordinal a)) : Π a, β a :=
λ a, h a.to_ordinal

/-- `ordinal.induction` but for `nat_ordinal`. -/
theorem induction {p : nat_ordinal → Prop} : ∀ i (h : ∀ j, (∀ k, k < j → p k) → p j), p i :=
ordinal.induction

end nat_ordinal

namespace ordinal

@[simp] theorem to_nat_ordinal_symm_eq : to_nat_ordinal.symm = nat_ordinal.to_ordinal := rfl
@[simp] theorem to_nat_ordinal_to_ordinal (a : ordinal) : a.to_nat_ordinal.to_ordinal = a := rfl

@[simp] theorem to_nat_ordinal_zero : to_nat_ordinal 0 = 0 := rfl
@[simp] theorem to_nat_ordinal_one : to_nat_ordinal 1 = 1 := rfl

@[simp] theorem to_nat_ordinal_eq_zero (a) : to_nat_ordinal a = 0 ↔ a = 0 := iff.rfl
@[simp] theorem to_nat_ordinal_eq_one (a) : to_nat_ordinal a = 1 ↔ a = 1 := iff.rfl

@[simp] theorem to_nat_ordinal_max (a b : ordinal) :
  to_nat_ordinal (max a b) = max a.to_nat_ordinal b.to_nat_ordinal := rfl
@[simp] theorem to_nat_ordinal_min (a b : ordinal) :
  (linear_order.min a b).to_nat_ordinal = linear_order.min a.to_nat_ordinal b.to_nat_ordinal := rfl

/-! We place the definitions of `nadd` and `nmul` before actually developing their API, as this
guarantees we only need to open the `natural_ops` locale once. -/

/-- Natural addition on ordinals `a ♯ b`, also known as the Hessenberg sum, is recursively defined
as the least ordinal greater than `a' ♯ b` and `a ♯ b'` for all `a' < a` and `b' < b`. In contrast
to normal ordinal addition, it is commutative.

Natural addition can equivalently be characterized as the ordinal resulting from adding up
corresponding coefficients in the Cantor normal forms of `a` and `b`. -/
noncomputable def nadd : ordinal → ordinal → ordinal
| a b := max
  (blsub.{u u} a $ λ a' h, nadd a' b)
  (blsub.{u u} b $ λ b' h, nadd a b')
using_well_founded { dec_tac := `[solve_by_elim [psigma.lex.left, psigma.lex.right]] }

localized "infix (name := ordinal.nadd) ` ♯ `:65 := ordinal.nadd" in natural_ops

/-- Natural multiplication on ordinals `a ⨳ b`, also known as the Hessenberg product, is recursively
defined as the least ordinal such that `a ⨳ b + a' ⨳ b'` is greater than `a' ⨳ b + a ⨳ b'` for all
`a' < a` and `b < b'`. In contrast to normal ordinal multiplication, it is commutative and
distributive (over natural addition).

Natural multiplication can equivalently be characterized as the ordinal resulting from multiplying
the Cantor normal forms of `a` and `b` as if they were polynomials in `ω`. Addition of exponents is
done via natural addition. -/
noncomputable def nmul : ordinal.{u} → ordinal.{u} → ordinal.{u}
| a b := Inf {c | ∀ (a' < a) (b' < b), nmul a' b ♯ nmul a b' < c ♯ nmul a' b'}
using_well_founded { dec_tac := `[solve_by_elim [psigma.lex.left, psigma.lex.right]] }

localized "infix ` ⨳ `:70 := ordinal.nmul" in natural_ops

end ordinal

open_locale natural_ops

/-! ### Natural addition -/

namespace ordinal

variables {a b c : ordinal.{u}}

theorem nadd_def (a b : ordinal) : a ♯ b = max
  (blsub.{u u} a $ λ a' h, a' ♯ b)
  (blsub.{u u} b $ λ b' h, a ♯ b') :=
by rw nadd

theorem lt_nadd_iff : a < b ♯ c ↔ (∃ b' < b, a ≤ b' ♯ c) ∨ ∃ c' < c, a ≤ b ♯ c' :=
by { rw nadd_def, simp [lt_blsub_iff] }

theorem nadd_le_iff : b ♯ c ≤ a ↔ (∀ b' < b, b' ♯ c < a) ∧ ∀ c' < c, b ♯ c' < a :=
by { rw nadd_def, simp [blsub_le_iff] }

theorem nadd_lt_nadd_left (h : b < c) (a) : a ♯ b < a ♯ c :=
lt_nadd_iff.2 (or.inr ⟨b, h, le_rfl⟩)

theorem nadd_lt_nadd_right (h : b < c) (a) : b ♯ a < c ♯ a :=
lt_nadd_iff.2 (or.inl ⟨b, h, le_rfl⟩)

theorem nadd_le_nadd_left (h : b ≤ c) (a) : a ♯ b ≤ a ♯ c :=
begin
  rcases lt_or_eq_of_le h with h | rfl,
  { exact (nadd_lt_nadd_left h a).le },
  { exact le_rfl }
end

theorem nadd_le_nadd_right (h : b ≤ c) (a) : b ♯ a ≤ c ♯ a :=
begin
  rcases lt_or_eq_of_le h with h | rfl,
  { exact (nadd_lt_nadd_right h a).le },
  { exact le_rfl }
end

variables (a b)

theorem nadd_comm : ∀ a b, a ♯ b = b ♯ a
| a b := begin
  rw [nadd_def, nadd_def, max_comm],
  congr; ext c hc;
  apply nadd_comm
end
using_well_founded { dec_tac := `[solve_by_elim [psigma.lex.left, psigma.lex.right]] }

theorem blsub_nadd_of_mono {f : Π c < a ♯ b, ordinal.{max u v}}
  (hf : ∀ {i j} hi hj, i ≤ j → f i hi ≤ f j hj) : blsub _ f = max
  (blsub.{u v} a (λ a' ha', f (a' ♯ b) $ nadd_lt_nadd_right ha' b))
  (blsub.{u v} b (λ b' hb', f (a ♯ b') $ nadd_lt_nadd_left hb' a)) :=
begin
  apply (blsub_le_iff.2 (λ i h, _)).antisymm (max_le _ _),
  { rcases lt_nadd_iff.1 h with ⟨a', ha', hi⟩ | ⟨b', hb', hi⟩,
    { exact lt_max_of_lt_left ((hf h (nadd_lt_nadd_right ha' b) hi).trans_lt (lt_blsub _ _ _)) },
    { exact lt_max_of_lt_right ((hf h (nadd_lt_nadd_left hb' a) hi).trans_lt (lt_blsub _ _ _)) } },
  all_goals
  { apply blsub_le_of_brange_subset.{u u v},
    rintro c ⟨d, hd, rfl⟩,
    apply mem_brange_self }
end

theorem nadd_assoc : ∀ a b c, a ♯ b ♯ c = a ♯ (b ♯ c)
| a b c := begin
  rw [nadd_def a (b ♯ c), nadd_def, blsub_nadd_of_mono, blsub_nadd_of_mono, max_assoc],
  { congr; ext d hd;
    apply nadd_assoc },
  { exact λ i j _ _ h, nadd_le_nadd_left h a },
  { exact λ i j _ _ h, nadd_le_nadd_right h c }
end
using_well_founded { dec_tac := `[solve_by_elim [psigma.lex.left, psigma.lex.right]] }

@[simp] theorem nadd_zero : a ♯ 0 = a :=
begin
  induction a using ordinal.induction with a IH,
  rw [nadd_def, blsub_zero, max_zero_right],
  convert blsub_id a,
  ext b hb,
  exact IH _ hb
end

@[simp] theorem zero_nadd : 0 ♯ a = a :=
by rw [nadd_comm, nadd_zero]

@[simp] theorem nadd_one : a ♯ 1 = succ a :=
begin
  induction a using ordinal.induction with a IH,
  rw [nadd_def, blsub_one, nadd_zero, max_eq_right_iff, blsub_le_iff],
  intros i hi,
  rwa [IH i hi, succ_lt_succ_iff]
end

@[simp] theorem one_nadd : 1 ♯ a = succ a :=
by rw [nadd_comm, nadd_one]

theorem nadd_succ : a ♯ succ b = succ (a ♯ b) :=
by rw [←nadd_one (a ♯ b), nadd_assoc, nadd_one]

theorem succ_nadd : succ a ♯ b = succ (a ♯ b) :=
by rw [←one_nadd (a ♯ b), ←nadd_assoc, one_nadd]

@[simp] theorem nadd_nat (n : ℕ) : a ♯ n = a + n :=
begin
  induction n with n hn,
  { simp },
  { rw [nat.cast_succ, add_one_eq_succ, nadd_succ, add_succ, hn] }
end

@[simp] theorem nat_nadd (n : ℕ) : ↑n ♯ a = a + n :=
by rw [nadd_comm, nadd_nat]

theorem add_le_nadd : a + b ≤ a ♯ b :=
begin
  apply b.limit_rec_on,
  { simp },
  { intros c h,
    rwa [add_succ, nadd_succ, succ_le_succ_iff] },
  { intros c hc H,
    rw [←is_normal.blsub_eq.{u u} (add_is_normal a) hc, blsub_le_iff],
    exact λ i hi, (H i hi).trans_lt (nadd_lt_nadd_left hi a) }
end

end ordinal

namespace nat_ordinal

open ordinal

instance : has_add nat_ordinal := ⟨nadd⟩

instance add_covariant_class_lt :
  covariant_class nat_ordinal.{u} nat_ordinal.{u} (+) (<) :=
⟨λ a b c h, nadd_lt_nadd_left h a⟩

instance add_covariant_class_le :
  covariant_class nat_ordinal.{u} nat_ordinal.{u} (+) (≤) :=
⟨λ a b c h, nadd_le_nadd_left h a⟩

instance add_contravariant_class_le :
  contravariant_class nat_ordinal.{u} nat_ordinal.{u} (+) (≤) :=
⟨λ a b c h, by { by_contra' h', exact h.not_lt (add_lt_add_left h' a) }⟩

instance : ordered_cancel_add_comm_monoid nat_ordinal :=
{ add := (+),
  add_assoc := nadd_assoc,
  add_le_add_left := λ a b, add_le_add_left,
  le_of_add_le_add_left := λ a b c, le_of_add_le_add_left,
  zero := 0,
  zero_add := zero_nadd,
  add_zero := nadd_zero,
  add_comm := nadd_comm,
  ..nat_ordinal.linear_order }

instance : add_monoid_with_one nat_ordinal := add_monoid_with_one.unary

@[simp] theorem add_one_eq_succ : ∀ a : nat_ordinal, a + 1 = succ a := nadd_one

@[simp] theorem to_ordinal_cast_nat (n : ℕ) : to_ordinal n = n :=
begin
  induction n with n hn,
  { refl },
  { change to_ordinal n ♯ 1 = n + 1,
    rw hn, exact nadd_one n }
end

end nat_ordinal

namespace ordinal

theorem nadd_eq_add (a b : ordinal) : a ♯ b = (a.to_nat_ordinal + b.to_nat_ordinal).to_ordinal :=
rfl

@[simp] theorem to_nat_ordinal_cast_nat (n : ℕ) : to_nat_ordinal n = n :=
by { rw ←nat_ordinal.to_ordinal_cast_nat n, refl }

theorem lt_of_nadd_lt_nadd_left : ∀ {a b c}, a ♯ b < a ♯ c → b < c :=
@lt_of_add_lt_add_left nat_ordinal _ _ _
theorem lt_of_nadd_lt_nadd_right : ∀ {a b c}, b ♯ a < c ♯ a → b < c :=
@_root_.lt_of_add_lt_add_right nat_ordinal _ _ _
theorem le_of_nadd_le_nadd_left : ∀ {a b c}, a ♯ b ≤ a ♯ c → b ≤ c :=
@le_of_add_le_add_left nat_ordinal _ _ _
theorem le_of_nadd_le_nadd_right : ∀ {a b c}, b ♯ a ≤ c ♯ a → b ≤ c :=
@le_of_add_le_add_right nat_ordinal _ _ _

theorem nadd_lt_nadd_iff_left : ∀ a {b c}, a ♯ b < a ♯ c ↔ b < c :=
@add_lt_add_iff_left nat_ordinal _ _ _ _
theorem nadd_lt_nadd_iff_right : ∀ a {b c}, b ♯ a < c ♯ a ↔ b < c :=
@add_lt_add_iff_right nat_ordinal _ _ _ _
theorem nadd_le_nadd_iff_left : ∀ a {b c}, a ♯ b ≤ a ♯ c ↔ b ≤ c :=
@add_le_add_iff_left nat_ordinal _ _ _ _
theorem nadd_le_nadd_iff_right : ∀ a {b c}, b ♯ a ≤ c ♯ a ↔ b ≤ c :=
@_root_.add_le_add_iff_right nat_ordinal _ _ _ _

theorem nadd_le_nadd : ∀ {a b c d}, a ≤ b → c ≤ d → a ♯ c ≤ b ♯ d :=
@add_le_add nat_ordinal _ _ _ _
theorem nadd_lt_nadd : ∀ {a b c d}, a < b → c < d → a ♯ c < b ♯ d :=
@add_lt_add nat_ordinal _ _ _ _

theorem nadd_lt_nadd_of_lt_of_le : ∀ {a b c d}, a < b → c ≤ d → a ♯ c < b ♯ d :=
@add_lt_add_of_lt_of_le nat_ordinal _ _ _ _
theorem nadd_lt_nadd_of_le_of_lt : ∀ {a b c d}, a ≤ b → c < d → a ♯ c < b ♯ d :=
@add_lt_add_of_le_of_lt nat_ordinal _ _ _ _

theorem nadd_left_cancel : ∀ {a b c}, a ♯ b = a ♯ c → b = c :=
@_root_.add_left_cancel nat_ordinal _ _
theorem nadd_right_cancel : ∀ {a b c}, a ♯ b = c ♯ b → a = c :=
@_root_.add_right_cancel nat_ordinal _ _
theorem nadd_left_cancel_iff : ∀ {a b c}, a ♯ b = a ♯ c ↔ b = c :=
@add_left_cancel_iff nat_ordinal _ _
theorem nadd_right_cancel_iff : ∀ {a b c}, b ♯ a = c ♯ a ↔ b = c :=
@add_right_cancel_iff nat_ordinal _ _

theorem le_nadd_self {a b} : a ≤ b ♯ a :=
by simpa using nadd_le_nadd_right (ordinal.zero_le b) a
theorem le_nadd_left {a b c} (h : a ≤ c) : a ≤ b ♯ c :=
le_nadd_self.trans (nadd_le_nadd_left h b)
theorem le_self_nadd {a b} : a ≤ a ♯ b :=
by simpa using nadd_le_nadd_left (ordinal.zero_le b) a
theorem le_nadd_right {a b c} (h : a ≤ b) : a ≤ b ♯ c :=
le_self_nadd.trans (nadd_le_nadd_right h c)

theorem nadd_left_comm : ∀ a b c, a ♯ (b ♯ c) = b ♯ (a ♯ c) :=
@add_left_comm nat_ordinal _
theorem nadd_right_comm : ∀ a b c, a ♯ b ♯ c = a ♯ c ♯ b :=
@add_right_comm nat_ordinal _

/-! ### Natural multiplication -/

variables {a b c d : ordinal.{u}}

theorem nmul_def (a b : ordinal) :
  a ⨳ b = Inf {c | ∀ (a' < a) (b' < b), a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b'} :=
by rw nmul

/-- The set in the definition of `nmul` is nonempty. -/
theorem nmul_nonempty (a b : ordinal.{u}) :
  {c : ordinal.{u} | ∀ (a' < a) (b' < b), a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b'}.nonempty :=
⟨_, λ a' ha b' hb, (lt_blsub₂.{u u u} _ ha hb).trans_le le_self_nadd⟩

theorem nmul_nadd_lt {a' b' : ordinal} (ha : a' < a) (hb : b' < b) :
  a' ⨳ b ♯ a ⨳ b' < a ⨳ b ♯ a' ⨳ b' :=
by { rw nmul_def a b, exact Inf_mem (nmul_nonempty a b) a' ha b' hb }

theorem nmul_nadd_le {a' b' : ordinal} (ha : a' ≤ a) (hb : b' ≤ b) :
  a' ⨳ b ♯ a ⨳ b' ≤ a ⨳ b ♯ a' ⨳ b' :=
begin
  rcases lt_or_eq_of_le ha with ha | rfl,
  { rcases lt_or_eq_of_le hb with hb | rfl,
    { exact (nmul_nadd_lt ha hb).le },
    { rw nadd_comm } },
  { exact le_rfl }
end

theorem lt_nmul_iff : c < a ⨳ b ↔ ∃ (a' < a) (b' < b), c ♯ a' ⨳ b' ≤ a' ⨳ b ♯ a ⨳ b' :=
begin
  refine ⟨λ h, _, _⟩,
  { rw nmul at h,
    simpa using not_mem_of_lt_cInf h ⟨0, λ _ _, bot_le⟩ },
  { rintros ⟨a', ha, b', hb, h⟩,
    have := h.trans_lt (nmul_nadd_lt ha hb),
    rwa nadd_lt_nadd_iff_right at this }
end

theorem nmul_le_iff : a ⨳ b ≤ c ↔ ∀ (a' < a) (b' < b), a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b' :=
by { rw ←not_iff_not, simp [lt_nmul_iff] }

theorem nmul_comm : ∀ (a b), a ⨳ b = b ⨳ a
| a b := begin
  rw [nmul, nmul],
  congr, ext x, split;
  intros H c hc d hd,
  { rw [nadd_comm, ←nmul_comm, ←nmul_comm a, ←nmul_comm d],
    exact H _ hd _ hc },
  { rw [nadd_comm, nmul_comm, nmul_comm c, nmul_comm c],
    exact H _ hd _ hc }
end
using_well_founded { dec_tac := `[solve_by_elim [psigma.lex.left, psigma.lex.right]] }

@[simp] theorem nmul_zero (a) : a ⨳ 0 = 0 :=
by { rw [←ordinal.le_zero, nmul_le_iff], exact λ  _ _ a ha, (ordinal.not_lt_zero a ha).elim }

@[simp] theorem zero_nmul (a) : 0 ⨳ a = 0 :=
by rw [nmul_comm, nmul_zero]

@[simp] theorem nmul_one : ∀ a, a ⨳ 1 = a
| a := begin
  rw nmul,
  simp only [lt_one_iff_zero, forall_eq, nmul_zero, nadd_zero],
  convert cInf_Ici,
  ext b,
  refine ⟨λ H, le_of_forall_lt (λ c hc, _), λ ha c hc, _⟩,
  { simpa only [nmul_one] using H c hc },
  { simpa only [nmul_one] using hc.trans_le ha }
end
using_well_founded { dec_tac := `[assumption] }

@[simp] theorem one_nmul (a) : 1 ⨳ a = a :=
by rw [nmul_comm, nmul_one]

theorem nmul_lt_nmul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c ⨳ a < c ⨳ b :=
lt_nmul_iff.2 ⟨0, h₂, a, h₁, by simp⟩

theorem nmul_lt_nmul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a ⨳ c < b ⨳ c :=
lt_nmul_iff.2 ⟨a, h₁, 0, h₂, by simp⟩

theorem nmul_le_nmul_of_nonneg_left (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c ⨳ a ≤ c ⨳ b :=
begin
  rcases lt_or_eq_of_le h₁ with h₁|rfl;
  rcases lt_or_eq_of_le h₂ with h₂|rfl,
  { exact (nmul_lt_nmul_of_pos_left h₁ h₂).le },
  all_goals { simp }
end

theorem nmul_le_nmul_of_nonneg_right (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a ⨳ c ≤ b ⨳ c :=
begin
  rw [nmul_comm, nmul_comm b],
  exact nmul_le_nmul_of_nonneg_left h₁ h₂
end

theorem nmul_nadd : ∀ (a b c), a ⨳ (b ♯ c) = a ⨳ b ♯ a ⨳ c
| a b c := begin
  apply le_antisymm (nmul_le_iff.2 $ λ a' ha d hd, _) (nadd_le_iff.2 ⟨λ d hd, _, λ d hd, _⟩),
  { rw nmul_nadd,
    rcases lt_nadd_iff.1 hd with ⟨b', hb, hd⟩ | ⟨c', hc, hd⟩,
    { have := nadd_lt_nadd_of_lt_of_le (nmul_nadd_lt ha hb) (nmul_nadd_le ha.le hd),
      rw [nmul_nadd, nmul_nadd] at this,
      simp only [nadd_assoc] at this,
      rwa [nadd_left_comm, nadd_left_comm _ (a ⨳ b'), nadd_left_comm (a ⨳ b), nadd_lt_nadd_iff_left,
        nadd_left_comm (a' ⨳ b), nadd_left_comm (a ⨳ b), nadd_lt_nadd_iff_left, ←nadd_assoc,
        ←nadd_assoc] at this },
    { have := nadd_lt_nadd_of_le_of_lt (nmul_nadd_le ha.le hd) (nmul_nadd_lt ha hc),
      rw [nmul_nadd, nmul_nadd] at this,
      simp only [nadd_assoc] at this,
      rwa [nadd_left_comm, nadd_comm (a ⨳ c), nadd_left_comm (a' ⨳ d), nadd_left_comm (a ⨳ c'),
        nadd_left_comm (a ⨳ b), nadd_lt_nadd_iff_left, nadd_comm (a' ⨳ c), nadd_left_comm (a ⨳ d),
        nadd_left_comm (a' ⨳ b), nadd_left_comm (a ⨳ b), nadd_lt_nadd_iff_left, nadd_comm (a ⨳ d),
        nadd_comm (a' ⨳ d), ←nadd_assoc, ←nadd_assoc] at this } },
  { rcases lt_nmul_iff.1 hd with ⟨a', ha, b', hb, hd⟩,
    have := nadd_lt_nadd_of_le_of_lt hd (nmul_nadd_lt ha (nadd_lt_nadd_right hb c)),
    rw [nmul_nadd, nmul_nadd, nmul_nadd a'] at this,
    simp only [nadd_assoc] at this,
    rwa [nadd_left_comm (a' ⨳ b'), nadd_left_comm, nadd_lt_nadd_iff_left, nadd_left_comm,
      nadd_left_comm _ (a' ⨳ b'), nadd_left_comm (a ⨳ b'), nadd_lt_nadd_iff_left,
      nadd_left_comm (a' ⨳ c), nadd_left_comm, nadd_lt_nadd_iff_left, nadd_left_comm,
      nadd_comm _ (a' ⨳ c), nadd_lt_nadd_iff_left] at this },
  { rcases lt_nmul_iff.1 hd with ⟨a', ha, c', hc, hd⟩,
    have := nadd_lt_nadd_of_lt_of_le (nmul_nadd_lt ha (nadd_lt_nadd_left hc b)) hd,
    rw [nmul_nadd, nmul_nadd, nmul_nadd a'] at this,
    simp only [nadd_assoc] at this,
    rwa [nadd_left_comm _ (a' ⨳ b), nadd_lt_nadd_iff_left, nadd_left_comm (a' ⨳ c'),
      nadd_left_comm _ (a' ⨳ c), nadd_lt_nadd_iff_left, nadd_left_comm,
      nadd_comm (a' ⨳ c'), nadd_left_comm _ (a ⨳ c'), nadd_lt_nadd_iff_left,
      nadd_comm _ (a' ⨳ c'), nadd_comm _ (a' ⨳ c'), nadd_left_comm,
      nadd_lt_nadd_iff_left] at this }
end
using_well_founded { dec_tac := `[solve_by_elim [psigma.lex.left, psigma.lex.right]] }

theorem nadd_nmul (a b c) : (a ♯ b) ⨳ c = a ⨳ c ♯ b ⨳ c :=
by rw [nmul_comm, nmul_nadd, nmul_comm, nmul_comm c]

theorem nmul_nadd_lt₃ {a' b' c' : ordinal} (ha : a' < a) (hb : b' < b) (hc : c' < c) :
  a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' <
  a ⨳ b ⨳ c ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' :=
by simpa only [nadd_nmul, ←nadd_assoc] using nmul_nadd_lt (nmul_nadd_lt ha hb) hc

theorem nmul_nadd_le₃ {a' b' c' : ordinal} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
  a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' ≤
  a ⨳ b ⨳ c ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' :=
by simpa only [nadd_nmul, ←nadd_assoc] using nmul_nadd_le (nmul_nadd_le ha hb) hc

theorem nmul_nadd_lt₃' {a' b' c' : ordinal} (ha : a' < a) (hb : b' < b) (hc : c' < c) :
  a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') <
  a ⨳ (b ⨳ c) ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') :=
begin
  simp only [nmul_comm _ (_ ⨳ _)],
  convert nmul_nadd_lt₃ hb hc ha using 1;
  { simp only [nadd_eq_add, nat_ordinal.to_ordinal_to_nat_ordinal], abel }
end

theorem nmul_nadd_le₃' {a' b' c' : ordinal} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
  a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') ≤
  a ⨳ (b ⨳ c) ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') :=
begin
  simp only [nmul_comm _ (_ ⨳ _)],
  convert nmul_nadd_le₃ hb hc ha using 1;
  { simp only [nadd_eq_add, nat_ordinal.to_ordinal_to_nat_ordinal], abel }
end

theorem lt_nmul_iff₃ : d < a ⨳ b ⨳ c ↔ ∃ (a' < a) (b' < b) (c' < c),
  d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' ≤
  a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' :=
begin
  refine ⟨λ h, _, _⟩,
  { rcases lt_nmul_iff.1 h with ⟨e, he, c', hc, H₁⟩,
    rcases lt_nmul_iff.1 he with ⟨a', ha, b', hb, H₂⟩,
    refine ⟨a', ha, b', hb, c', hc, _⟩,
    have := nadd_le_nadd H₁ (nmul_nadd_le H₂ hc.le),
    simp only [nadd_nmul, nadd_assoc] at this,
    rw [nadd_left_comm, nadd_left_comm d, nadd_left_comm, nadd_le_nadd_iff_left,
      nadd_left_comm (a ⨳ b' ⨳ c), nadd_left_comm (a' ⨳ b ⨳ c), nadd_left_comm (a ⨳ b ⨳ c'),
      nadd_le_nadd_iff_left, nadd_left_comm (a ⨳ b ⨳ c'), nadd_left_comm (a ⨳ b ⨳ c')] at this,
    simpa only [nadd_assoc] },
  { rintro ⟨a', ha, b', hb, c', hc, h⟩,
    have := h.trans_lt (nmul_nadd_lt₃ ha hb hc),
    repeat { rwa nadd_lt_nadd_iff_right at this } }
end

theorem nmul_le_iff₃ : a ⨳ b ⨳ c ≤ d ↔ ∀ (a' < a) (b' < b) (c' < c),
  a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' <
  d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' :=
by { rw ←not_iff_not, simp [lt_nmul_iff₃] }

theorem lt_nmul_iff₃' : d < a ⨳ (b ⨳ c) ↔ ∃ (a' < a) (b' < b) (c' < c),
  d ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') ≤
  a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') :=
begin
  simp only [nmul_comm _ (_ ⨳ _), lt_nmul_iff₃, nadd_eq_add, nat_ordinal.to_ordinal_to_nat_ordinal],
  split; rintro ⟨b', hb, c', hc, a', ha, h⟩,
  { use [a', ha, b', hb, c', hc], convert h using 1; abel },
  { use [c', hc, a', ha, b', hb], convert h using 1; abel }
end

theorem nmul_le_iff₃' : a ⨳ (b ⨳ c) ≤ d ↔ ∀ (a' < a) (b' < b) (c' < c),
  a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') <
  d ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') :=
by { rw ←not_iff_not, simp [lt_nmul_iff₃'] }

theorem nmul_assoc : ∀ a b c, a ⨳ b ⨳ c = a ⨳ (b ⨳ c)
| a b c := begin
  apply le_antisymm,
  { rw nmul_le_iff₃,
    intros a' ha b' hb c' hc,
    repeat { rw nmul_assoc },
    exact nmul_nadd_lt₃' ha hb hc },
  { rw nmul_le_iff₃',
    intros a' ha b' hb c' hc,
    repeat { rw ←nmul_assoc },
    exact nmul_nadd_lt₃ ha hb hc },
end
using_well_founded { dec_tac := `[solve_by_elim [psigma.lex.left, psigma.lex.right]] }

end ordinal

open ordinal

instance : has_mul nat_ordinal := ⟨nmul⟩

instance : ordered_comm_semiring nat_ordinal :=
{ mul := (*),
  left_distrib := nmul_nadd,
  right_distrib := nadd_nmul,
  zero_mul := zero_nmul,
  mul_zero := nmul_zero,
  mul_assoc := nmul_assoc,
  one := 1,
  one_mul := one_nmul,
  mul_one := nmul_one,
  mul_comm := nmul_comm,
  zero_le_one := @zero_le_one ordinal _ _ _ _,
  mul_le_mul_of_nonneg_left := λ a b c, nmul_le_nmul_of_nonneg_left,
  mul_le_mul_of_nonneg_right := λ a b c, nmul_le_nmul_of_nonneg_right,
  ..nat_ordinal.ordered_cancel_add_comm_monoid,
  ..nat_ordinal.linear_order }

namespace ordinal

theorem nmul_eq_mul (a b) : a ⨳ b = (a.to_nat_ordinal * b.to_nat_ordinal).to_ordinal := rfl

theorem nmul_nadd_one : ∀ a b, a ⨳ (b ♯ 1) = a ⨳ b ♯ a := @mul_add_one nat_ordinal _ _ _
theorem nadd_one_nmul : ∀ a b, (a ♯ 1) ⨳ b = a ⨳ b ♯ b := @add_one_mul nat_ordinal _ _ _
theorem nmul_succ (a b) : a ⨳ succ b = a ⨳ b ♯ a := by rw [←nadd_one, nmul_nadd_one]
theorem succ_nmul (a b) : succ a ⨳ b = a ⨳ b ♯ b := by rw [←nadd_one, nadd_one_nmul]
theorem nmul_add_one : ∀ a b, a ⨳ (b + 1) = a ⨳ b ♯ a := nmul_succ
theorem add_one_nmul : ∀ a b, (a + 1) ⨳ b = a ⨳ b ♯ b := succ_nmul

end ordinal

namespace nat_ordinal

open ordinal

theorem mul_le_nmul (a b : ordinal.{u}) : a * b ≤ a ⨳ b :=
begin
  apply b.limit_rec_on,
  { simp },
  { intros c h,
    rw [mul_succ, nmul_succ],
    exact (add_le_nadd _ a).trans (nadd_le_nadd_right h a) },
  { intros c hc H,
    rcases eq_zero_or_pos a with rfl | ha,
    { simp },
    { rw [←is_normal.blsub_eq.{u u} (mul_is_normal ha) hc, blsub_le_iff],
      exact λ i hi, (H i hi).trans_lt (nmul_lt_nmul_of_pos_left hi ha) } }
end

end nat_ordinal
