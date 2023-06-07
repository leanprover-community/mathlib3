/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.jordan.basic
import algebra.module.basic

/-!
# Symmetrized algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A commutative multiplication on a real or complex space can be constructed from any multiplication
by "symmetrization" i.e
$$
a \circ b = \frac{1}{2}(ab + ba)
$$

We provide the symmetrized version of a type `α` as `sym_alg α`, with notation `αˢʸᵐ`.

## Implementation notes

The approach taken here is inspired by algebra.opposites. We use Oxford Spellings
(IETF en-GB-oxendict).

## References

* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
-/

open function

/--
The symmetrized algebra has the same underlying space as the original algebra.
-/
def sym_alg (α : Type*) : Type* := α

postfix `ˢʸᵐ`:std.prec.max_plus := sym_alg

namespace sym_alg

variables {α : Type*}

/-- The element of `sym_alg α` that represents `a : α`. -/
@[pattern,pp_nodot]
def sym : α ≃ αˢʸᵐ := equiv.refl _

/-- The element of `α` represented by `x : αˢʸᵐ`. -/
@[pp_nodot]
def unsym : αˢʸᵐ ≃ α := equiv.refl _

@[simp] lemma unsym_sym (a : α) : unsym (sym a) = a := rfl
@[simp] lemma sym_unsym (a : α) : sym (unsym a) = a := rfl
@[simp] lemma sym_comp_unsym : (sym : α → αˢʸᵐ) ∘ unsym = id := rfl
@[simp] lemma unsym_comp_sym : (unsym : αˢʸᵐ → α) ∘ sym = id := rfl
@[simp] lemma sym_symm : (@sym α).symm = unsym := rfl
@[simp] lemma unsym_symm : (@unsym α).symm = sym := rfl

lemma sym_bijective : bijective (sym : α → αˢʸᵐ) := sym.bijective
lemma unsym_bijective : bijective (unsym : αˢʸᵐ → α) := unsym.symm.bijective
lemma sym_injective : injective (sym : α → αˢʸᵐ) := sym.injective
lemma sym_surjective : surjective (sym : α → αˢʸᵐ) := sym.surjective
lemma unsym_injective : injective (unsym : αˢʸᵐ → α) := unsym.injective
lemma unsym_surjective : surjective (unsym : αˢʸᵐ → α) := unsym.surjective

@[simp] lemma sym_inj {a b : α} : sym a = sym b ↔ a = b := sym_injective.eq_iff
@[simp] lemma unsym_inj {a b : αˢʸᵐ} : unsym a = unsym b ↔ a = b := unsym_injective.eq_iff

instance [nontrivial α] : nontrivial αˢʸᵐ := sym_injective.nontrivial
instance [inhabited α] : inhabited αˢʸᵐ := ⟨sym default⟩
instance [subsingleton α] : subsingleton αˢʸᵐ := unsym_injective.subsingleton
instance [unique α] : unique αˢʸᵐ := unique.mk' _
instance [is_empty α] : is_empty αˢʸᵐ := function.is_empty unsym

@[to_additive]
instance [has_one α] : has_one αˢʸᵐ := { one := sym 1 }

instance [has_add α] : has_add αˢʸᵐ :=
{ add := λ a b, sym (unsym a + unsym b) }

instance [has_sub α] : has_sub αˢʸᵐ := { sub := λ a b, sym (unsym a - unsym b) }

instance [has_neg α] : has_neg αˢʸᵐ :=
{ neg := λ a, sym (-unsym a) }

/- Introduce the symmetrized multiplication-/
instance [has_add α] [has_mul α] [has_one α] [invertible (2 : α)] : has_mul (αˢʸᵐ) :=
{ mul := λ a b, sym (⅟2 * (unsym a * unsym b + unsym b * unsym a)) }

@[to_additive] instance [has_inv α] : has_inv αˢʸᵐ :=
{ inv := λ a, sym $ (unsym a)⁻¹ }

instance (R : Type*) [has_smul R α] : has_smul R αˢʸᵐ :=
{ smul := λ r a, sym (r • unsym a) }

@[simp, to_additive] lemma sym_one [has_one α] : sym (1 : α) = 1 := rfl
@[simp, to_additive] lemma unsym_one [has_one α] : unsym (1 : αˢʸᵐ) = 1 := rfl

@[simp] lemma sym_add [has_add α] (a b : α) : sym (a + b) = sym a + sym b := rfl
@[simp] lemma unsym_add [has_add α] (a b : αˢʸᵐ) : unsym (a + b) = unsym a + unsym b := rfl

@[simp] lemma sym_sub [has_sub α] (a b : α) : sym (a - b) = sym a - sym b := rfl
@[simp] lemma unsym_sub [has_sub α] (a b : αˢʸᵐ) : unsym (a - b) = unsym a - unsym b := rfl

@[simp] lemma sym_neg [has_neg α] (a : α) : sym (-a) = -sym a := rfl
@[simp] lemma unsym_neg [has_neg α] (a : αˢʸᵐ) : unsym (-a) = -unsym a := rfl

lemma mul_def [has_add α] [has_mul α] [has_one α] [invertible (2 : α)] (a b : αˢʸᵐ) :
  a * b = sym (⅟2*(unsym a * unsym b + unsym b * unsym a)) := by refl

lemma unsym_mul [has_mul α] [has_add α] [has_one α] [invertible (2 : α)] (a b : αˢʸᵐ) :
  unsym (a * b) = ⅟2*(unsym a * unsym b + unsym b * unsym a) := by refl

lemma sym_mul_sym [has_mul α] [has_add α] [has_one α] [invertible (2 : α)] (a b : α) :
  sym a * sym b = sym (⅟2*(a * b + b * a)) :=
rfl

@[simp, to_additive] lemma sym_inv [has_inv α] (a : α) : sym (a⁻¹) = (sym a)⁻¹ := rfl
@[simp, to_additive] lemma unsym_inv [has_inv α] (a : αˢʸᵐ) : unsym (a⁻¹) = (unsym a)⁻¹ := rfl

@[simp] lemma sym_smul {R : Type*} [has_smul R α] (c : R) (a : α) : sym (c • a) = c • sym a := rfl
@[simp] lemma unsym_smul {R : Type*} [has_smul R α] (c : R) (a : αˢʸᵐ) :
  unsym (c • a) = c • unsym a := rfl

@[simp, to_additive] lemma unsym_eq_one_iff [has_one α] (a : αˢʸᵐ) : a.unsym = 1 ↔ a = 1 :=
unsym_injective.eq_iff' rfl

@[simp, to_additive] lemma sym_eq_one_iff [has_one α] (a : α) : sym a = 1 ↔ a = 1 :=
sym_injective.eq_iff' rfl

@[to_additive] lemma unsym_ne_one_iff [has_one α] (a : αˢʸᵐ) : a.unsym ≠ (1 : α) ↔ a ≠ (1 : αˢʸᵐ) :=
not_congr $ unsym_eq_one_iff a

@[to_additive] lemma sym_ne_one_iff [has_one α] (a : α) : sym a ≠ (1 : αˢʸᵐ) ↔ a ≠ (1 : α) :=
not_congr $ sym_eq_one_iff a

instance [add_comm_semigroup α] : add_comm_semigroup (αˢʸᵐ) :=
unsym_injective.add_comm_semigroup _ unsym_add

instance [add_monoid α] : add_monoid (αˢʸᵐ) :=
unsym_injective.add_monoid _ unsym_zero unsym_add (λ _ _, rfl)

instance [add_group α] : add_group (αˢʸᵐ) :=
unsym_injective.add_group _ unsym_zero
  unsym_add unsym_neg unsym_sub (λ _ _, rfl) (λ _ _, rfl)

instance [add_comm_monoid α] : add_comm_monoid (αˢʸᵐ) :=
{ ..sym_alg.add_comm_semigroup, ..sym_alg.add_monoid }

instance [add_comm_group α] : add_comm_group (αˢʸᵐ) :=
{ ..sym_alg.add_comm_monoid, ..sym_alg.add_group }

instance {R : Type*} [semiring R] [add_comm_monoid α] [module R α] : module R αˢʸᵐ :=
function.injective.module R ⟨unsym, unsym_zero, unsym_add⟩ unsym_injective unsym_smul

instance [has_mul α] [has_add α] [has_one α] [invertible (2 : α)] (a : α) [invertible a] :
  invertible (sym a) :=
{ inv_of := sym (⅟a),
  inv_of_mul_self := begin
    rw [sym_mul_sym, mul_inv_of_self, inv_of_mul_self, ←bit0, inv_of_mul_self, sym_one],
  end,
  mul_inv_of_self := begin
    rw [sym_mul_sym, mul_inv_of_self, inv_of_mul_self, ←bit0, inv_of_mul_self, sym_one],
  end }

@[simp] lemma inv_of_sym [has_mul α] [has_add α] [has_one α] [invertible (2 : α)] (a : α)
  [invertible a] : ⅟(sym a) = sym (⅟a) := rfl

instance [semiring α] [invertible (2 : α)] : non_assoc_semiring (αˢʸᵐ) :=
{ one := 1,
  mul := (*),
  zero := (0),
  zero_mul := λ _, by rw [mul_def, unsym_zero, zero_mul, mul_zero, add_zero, mul_zero, sym_zero],
  mul_zero := λ _, by rw [mul_def, unsym_zero, zero_mul, mul_zero, add_zero, mul_zero, sym_zero],
  mul_one := λ _, by rw [mul_def, unsym_one, mul_one, one_mul, ←two_mul, inv_of_mul_self_assoc,
                         sym_unsym],
  one_mul := λ _, by rw [mul_def, unsym_one, mul_one, one_mul, ←two_mul, inv_of_mul_self_assoc,
                         sym_unsym],
  left_distrib := λ a b c, match a, b, c with
    | sym a, sym b, sym c := begin
      rw [sym_mul_sym, sym_mul_sym, ←sym_add, sym_mul_sym, ←sym_add, mul_add a, add_mul _ _ a,
        add_add_add_comm, mul_add],
    end
  end,
  right_distrib := λ a b c, match a, b, c with
    | sym a, sym b, sym c := begin
      rw [sym_mul_sym, sym_mul_sym, ←sym_add, sym_mul_sym, ←sym_add, mul_add c, add_mul _ _ c,
        add_add_add_comm, mul_add],
    end
  end,
  ..sym_alg.add_comm_monoid, }

/-- The symmetrization of a real (unital, associative) algebra is a non-associative ring. -/
instance [ring α] [invertible (2 : α)] : non_assoc_ring (αˢʸᵐ) :=
{ ..sym_alg.non_assoc_semiring,
  ..sym_alg.add_comm_group, }

/-! The squaring operation coincides for both multiplications -/

lemma unsym_mul_self [semiring α] [invertible (2 : α)] (a : αˢʸᵐ) :
  unsym (a*a) = unsym a * unsym a :=
by rw [mul_def, unsym_sym, ←two_mul, inv_of_mul_self_assoc]

lemma sym_mul_self [semiring α] [invertible (2 : α)] (a : α) : sym (a*a) = sym a * sym a :=
by rw [sym_mul_sym, ←two_mul, inv_of_mul_self_assoc]

lemma mul_comm [has_mul α] [add_comm_semigroup α] [has_one α] [invertible (2 : α)] (a b : αˢʸᵐ) :
  a * b = b * a :=
by rw [mul_def, mul_def, add_comm]


instance [ring α] [invertible (2 : α)] : is_comm_jordan αˢʸᵐ :=
{ mul_comm := sym_alg.mul_comm,
  lmul_comm_rmul_rmul := λ a b, begin
    -- Rearrange LHS
    have commute_half_left := λ a : α, (commute.one_left a).bit0_left.inv_of_left.eq,
    rw [mul_def, mul_def a b, unsym_sym, ← mul_assoc, ← commute_half_left (unsym (a*a)), mul_assoc,
      mul_assoc, ← mul_add, ← mul_assoc, add_mul, mul_add (unsym (a * a)), ← add_assoc, ← mul_assoc,
      ← mul_assoc],

    -- Rearrange RHS
    nth_rewrite_rhs 0 [mul_def],
    nth_rewrite_rhs 0 [mul_def],
    nth_rewrite_rhs 2 [mul_def],

    rw [unsym_sym, sym_inj, ← mul_assoc, ← commute_half_left (unsym a), mul_assoc (⅟2) (unsym a),
      mul_assoc (⅟2) _ (unsym a), ← mul_add, ← mul_assoc],

    nth_rewrite_rhs 0 mul_add (unsym a),
    rw [add_mul, ← add_assoc, ← mul_assoc, ← mul_assoc],

    rw unsym_mul_self,
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← sub_eq_zero, ← mul_sub],

    convert mul_zero (⅟(2:α) * ⅟(2:α)),
    rw [add_sub_add_right_eq_sub, add_assoc, add_assoc, add_sub_add_left_eq_sub, add_comm,
      add_sub_add_right_eq_sub, sub_eq_zero],
  end }

end sym_alg
