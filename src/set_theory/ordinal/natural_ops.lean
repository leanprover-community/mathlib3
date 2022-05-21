/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.ordinal.arithmetic

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
@[simp] theorem to_nat_ordinal_inj {a b} : to_nat_ordinal a = to_nat_ordinal b ↔ a = b := iff.rfl
@[simp] theorem of_nat_ordinal_inj {a b} : of_nat_ordinal a = of_nat_ordinal b ↔ a = b := iff.rfl

instance : has_zero nat_ordinal := ⟨to_nat_ordinal 0⟩
instance : has_one nat_ordinal := ⟨to_nat_ordinal 1⟩
instance : has_well_founded nat_ordinal := ordinal.has_well_founded
instance : linear_order nat_ordinal := ordinal.linear_order

@[simp] theorem to_nat_ordinal_zero : to_nat_ordinal 0 = 0 := rfl
@[simp] theorem of_nat_ordinal_zero : of_nat_ordinal 0 = 0 := rfl
@[simp] theorem to_nat_ordinal_one : to_nat_ordinal 1 = 1 := rfl
@[simp] theorem of_nat_ordinal_one : of_nat_ordinal 1 = 1 := rfl

@[simp] theorem to_nat_ordinal_lt_iff {a b} : to_nat_ordinal a < to_nat_ordinal b ↔ a < b := iff.rfl
@[simp] theorem to_nat_ordinal_le_iff {a b} : to_nat_ordinal a ≤ to_nat_ordinal b ↔ a ≤ b := iff.rfl
@[simp] theorem of_nat_ordinal_lt_iff {a b} : of_nat_ordinal a < of_nat_ordinal b ↔ a < b := iff.rfl
@[simp] theorem of_nat_ordinal_le_iff {a b} : of_nat_ordinal a ≤ of_nat_ordinal b ↔ a ≤ b := iff.rfl

/-- A recursor for `nat_ordinal`. Use as `induction x using nat_ordinal.rec`. -/
protected def rec {β : nat_ordinal → Sort*} (h : Π a, β (to_nat_ordinal a)) : Π a, β a :=
λ a, h (of_nat_ordinal a)

/-- Natural addition on ordinals `a + b` is recursively defined as the least ordinal greater than
`a' + b` and `a + b'` for all `a' < a` and `b < b'`. In contrast to normal ordinal addition, it is
commutative.

Natural addition can equivalently be characterized as the ordinal resulting from adding up
corresponding coefficients in the Cantor normal forms of `a` and `b`. -/
noncomputable def add : nat_ordinal → nat_ordinal → nat_ordinal
| a b := max
  (blsub.{u u} (of_nat_ordinal a) (λ a' h, of_nat_ordinal (add (to_nat_ordinal a') b)))
  (blsub.{u u} (of_nat_ordinal b) (λ b' h, of_nat_ordinal (add a (to_nat_ordinal b'))))
using_well_founded { dec_tac := `[solve_by_elim [psigma.lex.left, psigma.lex.right]] }

instance : has_add nat_ordinal := ⟨add⟩

theorem add_def (a b : nat_ordinal) : a + b = max
  (blsub.{u u} (of_nat_ordinal a) (λ a' h, of_nat_ordinal (to_nat_ordinal a' + b)))
  (blsub.{u u} (of_nat_ordinal b) (λ b' h, of_nat_ordinal (a + to_nat_ordinal b'))) :=
by { unfold has_add.add, rw add }

instance add_covariant_class_lt :
  covariant_class nat_ordinal.{u} nat_ordinal.{u} (+) (<) :=
⟨λ a b c h, begin
  nth_rewrite 1 add_def,
  exact lt_max_of_lt_right (lt_blsub _ (of_nat_ordinal b) h)
end⟩

instance swap_add_covariant_class_lt :
  covariant_class nat_ordinal.{u} nat_ordinal.{u} (swap (+)) (<) :=
⟨λ a b c h, begin
  change _ < c + a,
  rw add_def,
  exact lt_max_of_lt_left (lt_blsub _ (of_nat_ordinal b) h)
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

theorem lt_add_iff {a b c : nat_ordinal} :
  a < b + c ↔ (∃ b' < b, a ≤ b' + c) ∨ ∃ c' < c, a ≤ b + c' :=
by { rw add_def, simpa [lt_blsub_iff] }

theorem blsub_add {a b : nat_ordinal.{u}} {f : Π c < of_nat_ordinal (a + b), ordinal.{max u v}}
  (hf : ∀ {i j} hi hj, i ≤ j → f i hi ≤ f j hj) : blsub _ f = max
  (blsub.{u v} (of_nat_ordinal a) (λ a' ha', f (of_nat_ordinal (to_nat_ordinal a' + b))
    $ @add_lt_add_right nat_ordinal _ _ _ _ _ ha' (to_nat_ordinal b)))
  (blsub.{u v} (of_nat_ordinal b) (λ b' hb', f (of_nat_ordinal (a + to_nat_ordinal b'))
    $ @add_lt_add_left nat_ordinal _ _ _ _ _ hb' (to_nat_ordinal a))) :=
begin
  apply le_antisymm (blsub_le_iff.2 (λ i hi, _)) (max_le _ _),
  { rcases lt_add_iff.1 hi with ⟨a', ha', hi'⟩ | ⟨b', hb', hi'⟩,
    { exact lt_max_of_lt_left ((hf hi (
        @add_lt_add_right nat_ordinal _ _ _ _ _ ha' (to_nat_ordinal b)) hi').trans_lt
        (lt_blsub _ a' _)) },
    { exact lt_max_of_lt_right ((hf hi (
        @add_lt_add_left nat_ordinal _ _ _ _ _ hb' (to_nat_ordinal a)) hi').trans_lt
        (lt_blsub _ b' _)) } },
  all_goals
  { apply blsub_le_of_brange_subset.{u u v},
    rintro c ⟨d, hd, rfl⟩,
    apply mem_brange_self }
end

private theorem add_assoc' : ∀ a b c : nat_ordinal, a + b + c = a + (b + c)
| a b c := begin
  nth_rewrite 2 add_def,
  rw [add_def, blsub_add, blsub_add, max_assoc],
  { congr;
    ext d hd;
    apply add_assoc' },
  { exact λ i j _ _ h, @add_le_add_left nat_ordinal _ _ _ _ _ h a },
  { exact λ i j _ _ h, @add_le_add_right nat_ordinal _ _ _ _ _ h c }
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
  simp only [of_nat_ordinal_zero, blsub_zero, max_zero_right],
  convert blsub_id (of_nat_ordinal a),
  ext b hb,
  apply add_zero'
end
using_well_founded { dec_tac := `[assumption] }

instance : add_comm_monoid nat_ordinal :=
{ zero := 0,
  add_zero := add_zero',
  zero_add := λ a, by rw [add_comm, add_zero'],
  ..nat_ordinal.add_comm_semigroup }

@[simp] theorem add_nat : ∀ (a : nat_ordinal) (n : ℕ),
  a + n = to_nat_ordinal ((of_nat_ordinal a) + (n : ordinal))
| a n := begin
  rw add_def,
  apply le_antisymm (max_le _ _),
  { cases n with n hn,
    { simpa using le_refl a },
    apply le_max_of_le_right,
 -- convert is_normal.blsub_eq (add_is_normal (of_nat_ordinal a))

  }

end
using_well_founded { dec_tac := `[solve_by_elim [psigma.lex.left, psigma.lex.right]] }

theorem ordinal_add_le_add (a b : nat_ordinal) : of_nat_ordinal a + of_nat_ordinal b ≤ a + b :=
sorry

end nat_ordinal
