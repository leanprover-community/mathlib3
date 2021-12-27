/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.jordan.basic

/-!
# Special Jordan algebras

A commutative multiplication on a real or complex space can be constructed from any multiplicaion by
"symmetrisation" i.e
```
a∘b = 1/2(ab+ba).
```
When the original multiplication is associative, the symmetrised algebra is a commutative Jordan
algebra. A commutative Jordan algebra which can be constructed in this way from an associative
multiplication is said to be a special Jordan algebra.

## Main results

- comm_jordan : The symmeterised algebra arising from an associative algebra is a commutative Jordan
  algebra.

## Implementation notes

The approach taken here is inspired by algebra.opposites.

## References

* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
-/

/--
The symmetrised algebra has the same underlying space as the original algebra.
-/
def sym_alg (α : Type*) : Type* := α

postfix `ˢʸᵐ`:std.prec.max_plus := sym_alg

namespace sym_alg

variables {α : Type*}

/-- The element of `sym_alg α` that represents `a : α`. -/
@[pp_nodot]
def sym : α → αˢʸᵐ := id

/-- The element of `α` represented by `x : αˢʸᵐ`. -/
@[pp_nodot]
def unsym : αˢʸᵐ → α := id

instance [inhabited α] : inhabited αˢʸᵐ := ⟨sym (default α)⟩

@[simp] lemma unsym_sym (x : α) : unsym (sym x) = x := rfl
@[simp] lemma sym_unsym (x : α) : sym (unsym x) = x := rfl

instance [has_zero α] : has_zero (αˢʸᵐ) := { zero := sym 0 }
instance [has_sub α] : has_sub αˢʸᵐ := { sub := λ a b, sym (unsym a - unsym b) }

instance [has_add α] : has_add αˢʸᵐ :=
{ add := λ a b, sym (unsym a + unsym b) }

@[simp] lemma sym_add [has_add α] (a b : α) : sym (a + b) = sym a + sym b := rfl
@[simp] lemma unsym_add [has_add α] (x y : αˢʸᵐ) : unsym (x + y) = unsym x + unsym y := rfl


instance [has_neg α] : has_neg αˢʸᵐ :=
{ neg := λ a, sym ( -(unsym a)) }

instance {R : Type*} [has_scalar R α] : has_scalar R αˢʸᵐ :=
{ smul := λ r a, sym (r•(unsym a)) }

@[simp] lemma sym_smul {R : Type*} [has_scalar R α] (c : R) (a : α) : sym (c • a) = c • sym a := rfl

lemma unsym_injective : function.injective (@unsym α) := λ _ _, id

instance [add_comm_semigroup α] : add_comm_semigroup (αˢʸᵐ) :=
unsym_injective.add_comm_semigroup _ (λ _ _, rfl)

instance [add_monoid α] : add_monoid (αˢʸᵐ) :=
unsym_injective.add_monoid_smul _ rfl (λ _ _, rfl) (λ _ _, rfl)

instance [add_group α] : add_group (αˢʸᵐ) :=
unsym_injective.add_group_smul _ rfl
  (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [add_comm_monoid α] : add_comm_monoid (αˢʸᵐ) :=
{ ..sym_alg.add_comm_semigroup, ..sym_alg.add_monoid }

instance [add_comm_group α] : add_comm_group (αˢʸᵐ) :=
{ ..sym_alg.add_comm_monoid, ..sym_alg.add_group }

@[simp] lemma sym_zero [has_zero α] : sym (0 : α) = 0 := rfl
@[simp] lemma unsym_zero [has_zero α] : unsym (0 : αˢʸᵐ) = 0 := rfl

@[simp] lemma unsym_eq_zero_iff {α} [has_zero α] (a : αˢʸᵐ) : a.unsym = (0 : α) ↔ a = (0 : αˢʸᵐ) :=
unsym_injective.eq_iff' rfl

lemma zero_zero [ring α] [algebra ℝ α] : unsym add_comm_group.zero = (0:α) := rfl

instance {R : Type*} [semiring R] [add_comm_monoid α] [module R α] : module R αˢʸᵐ :=
function.injective.module R ⟨unsym, rfl, λ _ _, rfl⟩ (λ _ _, id) (λ _ _, rfl)

noncomputable instance [ring α] [algebra ℝ α] : has_mul(αˢʸᵐ) :=
{ mul := λ a b, (sym ((1/2:ℝ)•(unsym(a)*unsym(b)+unsym(b)*unsym(a)))), }

lemma mul_def [ring α] [algebra ℝ α] (a b: αˢʸᵐ) :
  a*b = sym ((1/2:ℝ)•(unsym(a)*unsym(b)+unsym(b)*unsym(a))) := by refl

noncomputable instance [ring α] [algebra ℝ α] : non_unital_non_assoc_ring (αˢʸᵐ) :=
{ zero_mul := λ _,
  begin
    simp only [mul_def,zero_zero, add_zero, sym_zero, zero_mul, mul_zero, smul_zero],
    exact rfl,
  end,
  mul_zero :=  λ _,
  begin
    simp only [mul_def,zero_zero, add_zero, sym_zero, zero_mul, mul_zero, smul_zero],
    exact rfl,
  end,
  left_distrib := λ a b c, begin
    change (1/2:ℝ)•(unsym(a)*(unsym(b)+unsym(c))+(unsym(b)+unsym(c))*unsym(a)) =
      (1/2:ℝ)•(unsym(a)*unsym(b)+unsym(b)*unsym(a))+(1/2:ℝ)•(unsym(a)*unsym(c)+unsym(c)*unsym(a)),
    rw [mul_add, add_mul, smul_add, smul_add, smul_add, smul_add, smul_add],
    abel,
  end,
  right_distrib := λ a b c, begin
    change (1/2:ℝ)•((unsym(a)+unsym(b))*unsym(c)+unsym(c)*(unsym(a)+unsym(b))) =
      (1/2:ℝ)•(unsym(a)*unsym(c)+unsym(c)*unsym(a))+(1/2:ℝ)•(unsym(b)*unsym(c)+unsym(c)*unsym(b)),
    rw [mul_add, add_mul, smul_add, smul_add, smul_add, smul_add, smul_add],
    abel,
  end,
  ..sym_alg.has_mul,
  ..sym_alg.add_comm_group, }


theorem two_rmul [ring α] [algebra ℝ α]  (x:α) : (2 : ℝ) • x = x + x :=
begin
   rw [bit0, add_smul, one_smul],
end

lemma sym_squares [ring α] [algebra ℝ α] (a: αˢʸᵐ) : unsym(a*a) = unsym a * unsym a :=
begin
  rw [mul_def, unsym_sym, ← two_rmul, ← smul_assoc],
  simp,
end

noncomputable instance (α : Type*) [ring α] [algebra ℝ α] : comm_jordan (αˢʸᵐ) :=
{ comm := λ a,
  begin
    ext b,
    change (1/2:ℝ)•(unsym(b)*unsym(a)+unsym(a)*unsym(b)) =
     (1/2:ℝ)•(unsym(a)*unsym(b)+unsym(b)*unsym(a)),
    rw add_comm,
  end,
  jordan := λ a,
  begin
    ext b,
    simp,
    change (1/2:ℝ)•(unsym(a)*(1/2:ℝ)•(unsym(a*a)*unsym(b)+unsym(b)*unsym(a*a))
      +(1/2:ℝ)•(unsym(a*a)*unsym(b)+unsym(b)*unsym(a*a))*unsym(a))
      - (1/2:ℝ)•(unsym(a*a)*(1/2:ℝ)•(unsym(a)*unsym(b)+unsym(b)*unsym(a))
      +(1/2:ℝ)•(unsym(a)*unsym(b)+unsym(b)*unsym(a))*unsym(a*a)) = 0,
    rw [← smul_sub, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
      ← smul_add, ← smul_add, ← smul_sub, smul_smul],
    convert (smul_zero ((1 / 2:ℝ) * (1 / 2:ℝ))),
    rw [mul_add, add_mul, mul_add, add_mul, ← add_assoc, ← add_assoc, sym_squares,
      ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc,
      ← mul_assoc (unsym(a) * unsym(a)) (unsym(a)) (unsym(b)),
      ← mul_assoc (unsym(a) * unsym(a)) (unsym(b)) (unsym(a)),
      ← mul_assoc (unsym(b) * unsym(a)) (unsym(a)) (unsym(a))],
    abel,
    rw ← add_assoc,
    abel,
  end }

end sym_alg
