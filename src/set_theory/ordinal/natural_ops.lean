/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.ordinal.arithmetic

/-!
# Natural operations on ordinals

The goal of this file is to define natural addition and multiplication on ordinals, and provide a
basic API. The natural addition of two ordinals `a + b` is recursively defined as the least ordinal
greater than `a' + b` and `a + b'` for `a' < a` and `b' < b`. The natural multiplication `a * b` is
likewise recursively defined as the least ordinal such that `a * b + a' * b'` is greater than
`a' * b + a * b'` for any `a' < a` and `b' < b`.

These operations form a rich algebraic structure: they're commutative, associative, have the usual
`0` and `1` from ordinals, and distribute over one another.

Moreover, these operations are the addition and multiplication of ordinals when viewed as `surreal`
numbers. This makes them particularly useful for game theory.

Finally, both operations admit simple, intuitive descriptions in terms of the Cantor normal form.
The natural addition of two ordinals corresponds to adding the Cantor normal forms as if they were
polynomials in `ω`. Likewise, their natural multiplication corresponds to multiplying the Cantor
normal forms as polynomials.

# Implementation notes

Given the rich algebraic structure of these two operations, we choose to implement them via a type
synonym `nat_ordinal`. We provide many auxiliary theorems to make the transition between `ordinal`
and `nat_ordinal` as seamless as possible.

# Todo

- Define natural multiplication and provide a basic API.
- Prove the characterizations of natural addition and multiplication in terms of the Cantor normal
  form.
-/

universes u v

open function ordinal

noncomputable theory

/-- A type synonym for ordinals with natural addition and multiplication. -/
def nat_ordinal : Type* := ordinal

namespace nat_ordinal

/-- The identity function between `ordinal` and `nat_ordinal`. -/
@[pattern] def to_nat_ordinal : ordinal ≃ nat_ordinal := equiv.refl _

/-- The identity function between `nat_ordinal` and `ordinal`. -/
@[pattern] def of_nat_ordinal : nat_ordinal ≃ ordinal := equiv.refl _

@[simp] theorem to_nat_ordinal_symm_eq : to_nat_ordinal.symm = of_nat_ordinal := rfl
@[simp] theorem of_nat_ordinal_symm_eq : of_nat_ordinal.symm = to_nat_ordinal := rfl
@[simp] theorem to_nat_ordinal_of_nat_ordinal (a) : to_nat_ordinal (of_nat_ordinal a) = a := rfl
@[simp] theorem of_nat_ordinal_to_nat_ordinal (a) : of_nat_ordinal (to_nat_ordinal a) = a := rfl

instance : has_zero nat_ordinal := ⟨to_nat_ordinal 0⟩
instance : has_one nat_ordinal := ⟨to_nat_ordinal 1⟩
instance : has_well_founded nat_ordinal := ordinal.has_well_founded
instance : linear_order nat_ordinal := ordinal.linear_order

@[simp] theorem to_nat_ordinal_zero : to_nat_ordinal 0 = 0 := rfl
@[simp] theorem of_nat_ordinal_zero : of_nat_ordinal 0 = 0 := rfl
@[simp] theorem to_nat_ordinal_one : to_nat_ordinal 1 = 1 := rfl
@[simp] theorem of_nat_ordinal_one : of_nat_ordinal 1 = 1 := rfl

@[simp] theorem to_nat_ordinal_eq_zero (a) : to_nat_ordinal a = 0 ↔ a = 0 := iff.rfl
@[simp] theorem of_nat_ordinal_eq_zero (a) : of_nat_ordinal a = 0 ↔ a = 0 := iff.rfl
@[simp] theorem to_nat_ordinal_eq_one (a) : to_nat_ordinal a = 1 ↔ a = 1 := iff.rfl
@[simp] theorem of_nat_ordinal_eq_one (a) : of_nat_ordinal a = 1 ↔ a = 1 := iff.rfl

@[simp] theorem to_nat_ordinal_lt_iff {a b} : to_nat_ordinal a < to_nat_ordinal b ↔ a < b := iff.rfl
@[simp] theorem to_nat_ordinal_le_iff {a b} : to_nat_ordinal a ≤ to_nat_ordinal b ↔ a ≤ b := iff.rfl
@[simp] theorem of_nat_ordinal_lt_iff {a b} : of_nat_ordinal a < of_nat_ordinal b ↔ a < b := iff.rfl
@[simp] theorem of_nat_ordinal_le_iff {a b} : of_nat_ordinal a ≤ of_nat_ordinal b ↔ a ≤ b := iff.rfl
@[simp] theorem to_nat_ordinal_inj {a b} : to_nat_ordinal a = to_nat_ordinal b ↔ a = b := iff.rfl
@[simp] theorem of_nat_ordinal_inj {a b} : of_nat_ordinal a = of_nat_ordinal b ↔ a = b := iff.rfl

theorem lt_to_nat_ordinal_iff {a b} : a < to_nat_ordinal b ↔ of_nat_ordinal a < b := iff.rfl
theorem le_to_nat_ordinal_iff {a b} : a ≤ to_nat_ordinal b ↔ of_nat_ordinal a ≤ b := iff.rfl
theorem eq_to_nat_ordinal_iff {a b} : a = to_nat_ordinal b ↔ of_nat_ordinal a = b := iff.rfl
theorem lt_of_nat_ordinal_iff {a b} : a < of_nat_ordinal b ↔ to_nat_ordinal a < b := iff.rfl
theorem le_of_nat_ordinal_iff {a b} : a ≤ of_nat_ordinal b ↔ to_nat_ordinal a ≤ b := iff.rfl
theorem eq_of_nat_ordinal_iff {a b} : a = of_nat_ordinal b ↔ to_nat_ordinal a = b := iff.rfl

@[simp] theorem to_nat_ordinal_max {a b} :
  to_nat_ordinal (max a b) = max (to_nat_ordinal a) (to_nat_ordinal b) := rfl
@[simp] theorem of_nat_ordinal_max {a b} :
  of_nat_ordinal (max a b) = max (of_nat_ordinal a) (of_nat_ordinal b) := rfl
@[simp] theorem to_nat_ordinal_min {a b} :
  to_nat_ordinal (linear_order.min a b) = min (to_nat_ordinal a) (to_nat_ordinal b) := rfl
@[simp] theorem of_nat_ordinal_min {a b} :
  of_nat_ordinal (linear_order.min a b) = min (of_nat_ordinal a) (of_nat_ordinal b) := rfl

/-- A recursor for `nat_ordinal`. Use as `induction x using nat_ordinal.rec`. -/
protected def rec {β : nat_ordinal → Sort*} (h : Π a, β (to_nat_ordinal a)) : Π a, β a :=
λ a, h (of_nat_ordinal a)

/-- `ordinal.induction` but for `nat_ordinal`. -/
theorem induction {p : nat_ordinal → Prop} :
  ∀ i (h : ∀ j, (∀ k, k < j → p k) → p j), p i := ordinal.induction

/-- `ordinal.blsub` but for `nat_ordinal`. -/
def blsub (o : nat_ordinal.{u}) (f : Π a < o, nat_ordinal.{max u v}) : nat_ordinal :=
to_nat_ordinal (blsub.{u v} (of_nat_ordinal o) (λ a ha, of_nat_ordinal (f (to_nat_ordinal a) ha)))

/-- Natural addition on ordinals `a + b` is recursively defined as the least ordinal greater than
`a' + b` and `a + b'` for all `a' < a` and `b < b'`. In contrast to normal ordinal addition, it is
commutative.

Natural addition can equivalently be characterized as the ordinal resulting from adding up
corresponding coefficients in the Cantor normal forms of `a` and `b`. -/
noncomputable def add : nat_ordinal → nat_ordinal → nat_ordinal
| a b := max
  (blsub.{u u} a $ λ a' h, add a' b)
  (blsub.{u u} b $ λ b' h, add a b')
using_well_founded { dec_tac := `[solve_by_elim [psigma.lex.left, psigma.lex.right]] }

instance : has_add nat_ordinal := ⟨add⟩

theorem add_def (a b : nat_ordinal) : a + b = max
  (blsub.{u u} a $ λ a' h, a' + b)
  (blsub.{u u} b $ λ b' h, a + b') :=
by { unfold has_add.add, rw add }

instance add_covariant_class_lt :
  covariant_class nat_ordinal.{u} nat_ordinal.{u} (+) (<) :=
⟨λ a b c h, begin
  nth_rewrite 1 add_def,
  exact lt_max_of_lt_right (lt_blsub.{u u} _ (of_nat_ordinal b) h)
end⟩

instance swap_add_covariant_class_lt :
  covariant_class nat_ordinal.{u} nat_ordinal.{u} (swap (+)) (<) :=
⟨λ a b c h, begin
  change _ < c + a,
  rw add_def,
  exact lt_max_of_lt_left (lt_blsub.{u u} _ (of_nat_ordinal b) h)
end⟩

instance add_covariant_class_le :
  covariant_class nat_ordinal.{u} nat_ordinal.{u} (+) (≤) :=
⟨λ a b c h, begin
  rcases lt_or_eq_of_le h with h | rfl,
  { exact (add_lt_add_left h a).le },
  { exact le_rfl }
end⟩

instance swap_add_covariant_class_le :
  covariant_class nat_ordinal.{u} nat_ordinal.{u} (swap (+)) (≤) :=
⟨λ a b c h, begin
  rcases lt_or_eq_of_le h with h | rfl,
  { exact (add_lt_add_right h a).le },
  { exact le_rfl }
end⟩

instance add_contravariant_class_lt :
  contravariant_class nat_ordinal.{u} nat_ordinal.{u} (+) (<) :=
⟨λ a b c h, by { by_contra' h', exact h.not_le (add_le_add_left h' a) }⟩

instance swap_add_contravariant_class_lt :
  contravariant_class nat_ordinal.{u} nat_ordinal.{u} (swap (+)) (<) :=
⟨λ a b c h, by { by_contra' h', exact h.not_le (add_le_add_right h' a) }⟩

instance add_contravariant_class_le :
  contravariant_class nat_ordinal.{u} nat_ordinal.{u} (+) (≤) :=
⟨λ a b c h, by { by_contra' h', exact h.not_lt (add_lt_add_left h' a) }⟩

instance swap_add_contravariant_class_le :
  contravariant_class nat_ordinal.{u} nat_ordinal.{u} (swap (+)) (≤) :=
⟨λ a b c h, by { by_contra' h', exact h.not_lt (add_lt_add_right h' a) }⟩

theorem lt_add_iff {a b c : nat_ordinal} :
  a < b + c ↔ (∃ b' < b, a ≤ b' + c) ∨ ∃ c' < c, a ≤ b + c' :=
by { rw add_def, simpa [blsub, lt_blsub_iff, lt_to_nat_ordinal_iff] }

theorem blsub_add_of_mono {a b : nat_ordinal.{u}} {f : Π c < (a + b), nat_ordinal.{max u v}}
  (hf : ∀ {i j} hi hj, i ≤ j → f i hi ≤ f j hj) : blsub _ f = max
  (blsub.{u v} a (λ a' ha', f (a' + b) $ add_lt_add_right ha' b))
  (blsub.{u v} b (λ b' hb', f (a + b') $ add_lt_add_left hb' a)) :=
begin
  apply le_antisymm (blsub_le_iff.2 (λ i hi, _)) (max_le _ _),
  { rcases lt_add_iff.1 hi with ⟨a', ha', hi'⟩ | ⟨b', hb', hi'⟩,
    { exact lt_max_of_lt_left ((hf hi (add_lt_add_right ha' b) hi').trans_lt (lt_blsub _ a' _)) },
    { exact lt_max_of_lt_right ((hf hi (add_lt_add_left hb' a) hi').trans_lt (lt_blsub _ b' _)) } },
  all_goals
  { apply blsub_le_of_brange_subset.{u u v},
    rintro c ⟨d, hd, rfl⟩,
    apply mem_brange_self }
end

private theorem add_assoc' : ∀ a b c : nat_ordinal, a + b + c = a + (b + c)
| a b c := begin
  nth_rewrite 2 add_def,
  rw [add_def, blsub_add_of_mono, blsub_add_of_mono, max_assoc],
  { congr;
    ext d hd;
    apply add_assoc' },
  { exact λ i j _ _ h, add_le_add_left h a },
  { exact λ i j _ _ h, add_le_add_right h c }
end
using_well_founded { dec_tac := `[solve_by_elim [psigma.lex.left, psigma.lex.right]] }

instance : add_semigroup nat_ordinal :=
{ add := (+),
  add_assoc := add_assoc' }

private theorem add_comm' : ∀ a b : nat_ordinal, a + b = b + a
| a b := begin
  rw [add_def, add_def, max_comm],
  congr;
  ext a' ha';
  apply add_comm'
end
using_well_founded { dec_tac := `[solve_by_elim [psigma.lex.left, psigma.lex.right]] }

instance : add_comm_semigroup nat_ordinal :=
{ add_comm := add_comm',
  ..nat_ordinal.add_semigroup }

private theorem add_zero' : ∀ a : nat_ordinal, a + 0 = a
| a := begin
  rw add_def,
  simp only [blsub, of_nat_ordinal_zero, blsub_zero, to_nat_ordinal_zero, max_zero_right],
  rw ←eq_of_nat_ordinal_iff,
  convert blsub_id (of_nat_ordinal a),
  ext b hb,
  apply add_zero'
end
using_well_founded { dec_tac := `[assumption] }

instance : add_cancel_comm_monoid nat_ordinal :=
{ zero := 0,
  add_zero := add_zero',
  zero_add := λ a, by rw [add_comm, add_zero'],
  add_left_cancel := λ a b c, add_left_cancel'',
  ..nat_ordinal.add_comm_semigroup }

theorem add_one : ∀ a : nat_ordinal.{u}, a + 1 = to_nat_ordinal (succ (of_nat_ordinal a))
| a := begin
  rw add_def,
  simp only [blsub, of_nat_ordinal_one, blsub_one, to_nat_ordinal_zero, add_zero, max_eq_right_iff,
    to_nat_ordinal_le_iff, blsub_le_iff],
  intros i hi,
  rw add_one (to_nat_ordinal i),
  exact succ_lt_succ.2 hi
end
using_well_founded { dec_tac := `[assumption] }

theorem add_nat (a : nat_ordinal) (n : ℕ) :
  a + n = to_nat_ordinal ((of_nat_ordinal a) + (n : ordinal)) :=
begin
  induction n with n hn,
  { simp },
  { rw [nat.cast_succ, nat.cast_succ, ←add_assoc, ←add_assoc, hn, add_one],
    refl }
end

@[simp] theorem of_nat_ordinal_cast (n : ℕ) : of_nat_ordinal (↑n) = ↑n :=
begin
  induction n with n hn,
  { refl },
  { simpa [add_one, hn] }
end

@[simp] theorem to_nat_ordinal_cast (n : ℕ) : to_nat_ordinal (↑n) = ↑n :=
by { rw ←of_nat_ordinal_cast n, refl }

theorem ordinal_add_le_add (a b : nat_ordinal.{u}) :
  of_nat_ordinal a + of_nat_ordinal b ≤ of_nat_ordinal (a + b) :=
begin
  induction b using ordinal.induction with b IH,
  rw [add_def, of_nat_ordinal_max],
  rcases zero_or_succ_or_limit (of_nat_ordinal b) with hb | ⟨c, hb⟩ | hb,
  { apply le_max_of_le_left,
    rw of_nat_ordinal_eq_zero at hb,
    rw hb,
    simp [blsub] },
  { apply le_max_of_le_right,
    rw [blsub, of_nat_ordinal_to_nat_ordinal, hb, blsub_succ_of_mono, add_succ, succ_le_succ],
    { apply IH (to_nat_ordinal c),
      rw [←lt_of_nat_ordinal_iff, hb],
      exact lt_succ_self c },
    { exact λ i j _ _ h, of_nat_ordinal_le_iff.2 (add_le_add_left h a) } },
  { apply le_max_of_le_right,
    rw [←is_normal.blsub_eq.{u u} (add_is_normal (of_nat_ordinal a)) hb, blsub_le_iff],
    exact λ i hi, (IH (to_nat_ordinal i) hi).trans_lt (lt_blsub.{u u} _ i hi) }
end

end nat_ordinal
