/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.ordinal.arithmetic

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

- Define natural multiplication and provide a basic API.
- Prove the characterizations of natural addition and multiplication in terms of the Cantor normal
  form.
-/

universes u v

open function order

noncomputable theory

/-- A type synonym for ordinals with natural addition and multiplication. -/
@[derive [has_zero, inhabited, has_one, linear_order, succ_order, has_well_founded]]
def nat_ordinal : Type* := ordinal

/-- The identity function between `ordinal` and `nat_ordinal`. -/
@[pattern] def ordinal.to_nat_ordinal : ordinal ≃o nat_ordinal := order_iso.refl _

/-- The identity function between `nat_ordinal` and `ordinal`. -/
@[pattern] def nat_ordinal.to_ordinal : nat_ordinal ≃o ordinal := order_iso.refl _

open ordinal

namespace nat_ordinal

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

variables {a b c : ordinal.{u}}

@[simp] theorem to_nat_ordinal_symm_eq : to_nat_ordinal.symm = nat_ordinal.to_ordinal := rfl
@[simp] theorem to_nat_ordinal_to_ordinal (a : ordinal) : a.to_nat_ordinal.to_ordinal = a := rfl

@[simp] theorem to_nat_ordinal_zero : to_nat_ordinal 0 = 0 := rfl
@[simp] theorem to_nat_ordinal_one : to_nat_ordinal 1 = 1 := rfl

@[simp] theorem to_nat_ordinal_eq_zero (a) : to_nat_ordinal a = 0 ↔ a = 0 := iff.rfl
@[simp] theorem to_nat_ordinal_eq_one (a) : to_nat_ordinal a = 1 ↔ a = 1 := iff.rfl

@[simp] theorem to_nat_ordinal_max :
  to_nat_ordinal (max a b) = max a.to_nat_ordinal b.to_nat_ordinal := rfl
@[simp] theorem to_nat_ordinal_min :
  (linear_order.min a b).to_nat_ordinal = linear_order.min a.to_nat_ordinal b.to_nat_ordinal := rfl

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

open ordinal

namespace nat_ordinal

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
  { change nadd (to_ordinal n) 1 = n + 1,
    rw hn,
    apply nadd_one }
end

end nat_ordinal

open nat_ordinal

open_locale natural_ops

namespace ordinal

@[simp] theorem to_nat_ordinal_cast_nat (n : ℕ) : to_nat_ordinal n = n :=
by { rw ←to_ordinal_cast_nat n, refl }

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

theorem nadd_left_cancel : ∀ {a b c}, a ♯ b = a ♯ c → b = c :=
@_root_.add_left_cancel nat_ordinal _ _
theorem nadd_right_cancel : ∀ {a b c}, a ♯ b = c ♯ b → a = c :=
@_root_.add_right_cancel nat_ordinal _ _
theorem nadd_left_cancel_iff : ∀ {a b c}, a ♯ b = a ♯ c ↔ b = c :=
@add_left_cancel_iff nat_ordinal _ _
theorem nadd_right_cancel_iff : ∀ {a b c}, b ♯ a = c ♯ a ↔ b = c :=
@add_right_cancel_iff nat_ordinal _ _

end ordinal
