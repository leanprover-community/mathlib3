/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.ordered_group
import algebra.module.basic -- Needed for scalar multiplication
import tactic.ring

/-!
# Lattice ordered groups

Lattice ordered groups were introduced by [Birkhoff][birkhoff1942].
They form the algebraic underpinnings of vector lattices, Banach lattices, AL-space, AM-space etc.

This file develops the basic theory, concentrating on the commutative case written additively.

## Main definitions

* `lattice_ordered_group` - a (non-commutative) partially ordered (multiplicative) group which forms
  a lattice with respect to the partial order.
* `lattice_ordered_add_group` - the additive form of a `lattice_ordered_group`
* `lattice_ordered_comm_group` - a lattice ordered (multiplicative) group with commutative group
  operation
* `lattice_ordered_add_comm_group` - the additice form of a `lattice_ordered_comm_group`

## Main statements

- `pos_sub_neg`: Every element `a` of a `lattice_ordered_add_comm_group` has a decomposition `a⁺-a⁻`
   into the difference of the positive and negative component.
- `pos_meet_neg_eq_zero`: The positive and negative components are coprime.
- `abs_triangle`: The absolute value operation satisfies the triangle inequality.

It is shown that the meet and join operations are related to the absolute value operation by a
number of equations and inequalities.

## Notations

- `a⁺ = a ⊔ 0`: The *positive component* of an element `a` of a `lattice_ordered_add_comm_group`
- `a⁻ = (-a) ⊔ 0`: The *negative component* of an element `a` of a `lattice_ordered_add_comm_group`
* `|a| = a⊔(-a)`: The *absolute value* of an element `a` of a `lattice_ordered_add_comm_group`

## Implementation notes

We define `lattice_ordered_group` as extending `group` and `lattice` and
`lattice_ordered_comm_group` as extending `comm_group` and `lattice`. Equivalent additive classes
are defined. We then show that a `lattice_ordered_comm_group` is a `lattice_ordered_group` and an
`ordered_comm_group`.

The remainder of the file establishes basic properties of `lattice_ordered_add_comm_group`. A number
of these results also hold in the non-commutative case ([Birkhoff][birkhoff1942],
[Fuchs][fuchs1963]) but we have not developed that here. We have concentrated on groups written
additively, since we are primarily interested in vector lattices.

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

lattice, ordered, group
-/

universe u

/--
A group `(α,*)`, equipped with a partial order `≤`, making `α` into a lattice, such that, given
elements `a` and `b` of type `α` satisfying `a ≤ b`, for all elements `c` and `d` of `type α`,
$$c * a * d ≤ c * b * d,$$
is said to be a *lattice ordered group*.
-/
class lattice_ordered_group (α : Type u)
  extends group α, lattice α :=
(mul_le_mul : ∀ a b : α, a ≤ b → ∀ c d : α, c * a * d ≤ c * b * d)

/--
A lattice ordered group with Abelian group multiplication is said to be a *lattice ordered
commutative group*.
-/
class lattice_ordered_comm_group (α : Type u)
  extends comm_group α, lattice α :=
(mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)

/--
A group `(α,+)`, equipped with a partial order `≤`, making `α` into a lattice, such that, given
elements `a` and `b` of type `α` satisfying `a ≤ b`, for all elements `c` and `d` of type `α`,
$$c + a + d ≤ c + b + d,$$
is said to be a *lattice ordered (additive) group*.
-/
class lattice_ordered_add_group (α : Type u)
  extends add_group α, lattice α :=
(add_le_add : ∀ a b : α, a ≤ b → ∀ c d : α, c + a + d ≤ c + b + d)

/--
A lattice ordered additive group with Abelian group addition is said to be a *lattice ordered
(additative) commutative group*.
-/
class lattice_ordered_add_comm_group (α : Type u)
  extends add_comm_group α, lattice α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)

-- Tells to_additive that lattice_ordered_add_group is the additive form of lattice_ordered_group
-- and lattice_ordered_add_comm_group is the additive form of lattice_ordered_comm_group
attribute [to_additive] lattice_ordered_group
attribute [to_additive] lattice_ordered_comm_group

-- Every lattice ordered commutative group is also an ordered additive commutative group
@[priority 100, to_additive] -- see Note [lower instance priority]
instance lattice_ordered_comm_group.to_ordered_comm_group (α : Type u)
  [s : lattice_ordered_comm_group α] : ordered_comm_group α :=
{ mul := s.mul, ..s }

-- A lattice ordered commutative group is a lattice ordered group
@[priority 100, to_additive] -- see Note [lower instance priority]
instance lattice_ordered_comm_group.to_lattice_ordered_group (α : Type u)
  [s : lattice_ordered_comm_group α] : lattice_ordered_group α :=
{ mul_le_mul := λ a b hab c d, mul_le_mul' (mul_le_mul' le_rfl hab) le_rfl }


-- A linearly ordered additive commutative group is a lattice ordered commutative group
@[priority 100, to_additive] -- see Note [lower instance priority]
instance linear_ordered_comm_group.to_lattice_ordered_comm_group (α : Type u)
 [s : linear_ordered_comm_group α] : lattice_ordered_comm_group α :=
{ mul_le_mul_left := s.mul_le_mul_left, }

variables {α : Type u} [lattice_ordered_add_comm_group α]

-- Special case of Bourbaki A.VI.9 (1)
/--
Let `α` be a lattice ordered commutative group. For all elements `a`, `b` and `c` in `α`,
$$c + (a⊔b) = (c+a)⊔(c+b).$$
-/
lemma add_join_eq_add_join_add (a b c : α) : c + (a⊔b) = (c+a)⊔(c+b) :=
begin
  refine le_antisymm _ (by simp),
  rw [← add_le_add_iff_left (-c), ← add_assoc, neg_add_self, zero_add],
  apply sup_le,
  { simp },
  { simp },
end

-- Special case of Bourbaki A.VI.9 (2)
/--
Let `α` be a lattice ordered commutative group. For all elements `a` and `b` in `α`,
$$-(a⊔b)=(-a)⊓(-b).$$
-/
lemma neg_join_eq_neg_meet_neg (a b : α) : -(a⊔b)=(-a)⊓(-b) :=
begin
  rw le_antisymm_iff,
  split,
  { rw le_inf_iff,
    split,
    { rw neg_le_neg_iff, apply le_sup_left, },
    { rw neg_le_neg_iff, apply le_sup_right, } },
  { rw ← neg_le_neg_iff, simp,
    split,
    { rw ← neg_le_neg_iff, simp, },
    { rw ← neg_le_neg_iff, simp, } }
end

/--
Let `α` be a lattice ordered commutative group. For all elements `a` and `b` in `α`,
$$-a⊔-b = -(a⊓b).$$
-/
@[simp] lemma join_neg_eq_neg_meet (a b : α) : -a⊔-b = -(a⊓b) :=
begin
  rw [← neg_neg (-a⊔-b), neg_join_eq_neg_meet_neg (-a) (-b), neg_neg, neg_neg],
end

-- Bourbaki A.VI.10 Prop 7
/--
Let `α` be a lattice ordered commutative group. For all elements `a` and `b` in `α`,
$$a⊓b + (a⊔b) = a + b.$$
-/
lemma add_eq_meet_add_join (a b : α) : a⊓b + (a⊔b) = a + b :=
calc a⊓b + (a⊔b) = a⊓b + ((a + b) + ((-b)⊔(-a))) :
  by {  rw add_join_eq_add_join_add (-b) (-a) (a+b), simp,  }
... = a⊓b + ((a + b) + -(a⊓b)) : by { rw [← join_neg_eq_neg_meet, sup_comm], }
... = a + b                    : by { simp, }

-- Bourbaki A.VI.12 Definition 4
/--
Let `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type `α`,
the element `a ⊔ 0` is said to be the *positive component* of `a`, denoted `a⁺`.
-/
def lattice_ordered_add_comm_group.pos (a : α) : α :=  a ⊔ 0
postfix `⁺`:1000 := lattice_ordered_add_comm_group.pos

/--
Let `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type `α`,
the element `(-a) ⊔ 0` is said to be the *negative component* of `a`, denoted `a⁻`.
-/
def lattice_ordered_add_comm_group.neg (a : α) : α :=  (-a) ⊔ 0
postfix `⁻`:1000 := lattice_ordered_add_comm_group.neg

/--
Absolute value is a unary operator with properties similar to the absolute value of a real number.
-/
class has_abs (α : Type u) := (abs : α → α)
local notation `|`a`|` := has_abs.abs a
@[priority 100] -- see Note [lower instance priority]
instance lattice_ordered_add_comm_group_has_abs : has_abs (α)  := ⟨λa, a⊔-a⟩

namespace lattice_ordered_add_comm_group

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with absolute value
`|a|`. Then,
$$a ≤ |a|.$$
-/
lemma le_abs (a : α) : a ≤ |a| := le_sup_left

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with absolute value
`|a|`. Then,
$$-a ≤ |a|.$$
-/
lemma neg_le_abs (a : α) : -a ≤ |a| := le_sup_right

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with positive
 component `a⁺`. Then `a⁺` is positive.
-/
lemma pos_pos (a : α) : 0 ≤ a⁺ := le_sup_right

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` withnegative
component `a⁻`. Then `a⁻` is positive.
-/
lemma neg_pos (a : α) : 0 ≤ a⁻ := le_sup_right

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with positive
component `a⁺`. Then `a⁺` dominates `a`.
-/
lemma le_pos (a : α) : a ≤ a⁺ := le_sup_left

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with negative
component `a⁻`. Then `a⁻` dominates `-a`.
-/
lemma le_neg (a : α) : -a ≤ a⁻ := le_sup_left

end lattice_ordered_add_comm_group

-- Bourbaki A.VI.12
/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α`. Then the negative
component `a⁻` of `a` is equal to the positive component `(-a)⁺` of `-a`.
-/
lemma neg_eq_pos_neg (a : α) : a⁻ =(-a)⁺ :=
begin
  unfold lattice_ordered_add_comm_group.neg,
  unfold lattice_ordered_add_comm_group.pos,
end

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α`. Then the positive
component `a⁺` of `a` is equal to the negative component `(-a)⁻` of `-a`.
-/
lemma pos_eq_neg_neg (a : α) : a⁺ =(-a)⁻ :=
begin
  rw neg_eq_pos_neg,
  simp,
end

-- We use this in Bourbaki A.VI.12  Prop 9 a)
/--
Let `α` be a lattice ordered commutative group. For all elements `a`, `b` and `c` in `α`,
$$c + (a⊓b) = (c+a)⊓(c+b).$$
-/
lemma add_meet_eq_add_meet_add (a b c : α) : c + (a⊓b) = (c+a)⊓(c+b) :=
begin
  rw le_antisymm_iff,
  split,
  { simp, },
  { rw ← add_le_add_iff_left (-c), abel, rw le_inf_iff, simp, }
end

-- We use this in Bourbaki A.VI.12  Prop 9 a)
/--
Let `α` be a lattice ordered commutative group with identity `0` and let `a` be an element in `α`
with negative component `a⁻`. Then
$$a⁻ = -(a⊓0).$$
-/
lemma neg_eq_neg_inf_zero (a : α) : a⁻ = -(a⊓0) :=
begin
  unfold lattice_ordered_add_comm_group.neg,
  rw ← neg_inj,
  rw neg_join_eq_neg_meet_neg,
  simp,
end

-- Bourbaki A.VI.12  Prop 9 a)
/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with positive
component `a⁺` and negative component `a⁻`. Then `a` can be decomposed as the difference of `a⁺` and
`a⁻`.
-/
lemma pos_sub_neg (a : α) : a = a⁺ - a⁻ :=
begin
  unfold lattice_ordered_add_comm_group.neg,
  rw [eq_sub_iff_add_eq, add_join_eq_add_join_add, add_zero, add_right_neg, sup_comm],
  unfold lattice_ordered_add_comm_group.pos,
end

-- Hack to work around rewrite not working if lhs is a variable
@[nolint doc_blame_thm] lemma pos_sub_neg' (a : α) :  a⁺ - a⁻ = a := (pos_sub_neg _).symm

-- Bourbaki A.VI.12  Prop 9 a)
/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with positive
component `a⁺` and negative component `a⁻`. Then `a⁺` and `a⁻` are co-prime (and, since they are
positive, disjoint).
-/
lemma pos_meet_neg_eq_zero (a : α) : a⁺⊓a⁻=0 :=
begin
  rw ←add_right_inj (-a⁻),
  rw add_meet_eq_add_meet_add,
  rw neg_add_eq_sub,
  simp only [add_zero, add_left_neg],
  rw pos_sub_neg',
  rw neg_eq_neg_inf_zero,
  simp,
end

-- Bourbaki A.VI.12 (with a and b swapped)
/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α`, and let
`(a - b)⁺` be the positive componet of `a-b`. Then
$$a⊔b = b + (a - b)⁺.$$
-/
lemma join_eq_add_pos_sub (a b : α) : a⊔b = b + (a - b)⁺ :=
  calc  a⊔b = (b+(a-b))⊔(b+0) : by {rw add_zero b, rw add_sub_cancel'_right, }
  ... = b + ((a-b)⊔0) : by { rw ← add_join_eq_add_join_add (a-b) 0 b}

-- Bourbaki A.VI.12 (with a and b swapped)
/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α`, and let
`(a - b)⁺` be the positive componet of `a-b`. Then
$$a⊓b = a - (a - b)⁺.$$
-/
lemma meet_eq_sub_pos_sub (a b : α) : a⊓b = a - (a - b)⁺ :=
  calc a⊓b = (a+0)⊓(a+(b-a)) : by { rw add_zero a, rw add_sub_cancel'_right, }
  ... = a + (0⊓(b-a))        : by {rw ← add_meet_eq_add_meet_add 0 (b-a) a}
  ... = a + ((b-a)⊓0)        : by { rw inf_comm }
  ... = a + (-(a-b)⊓-0 )     : by { rw neg_zero, rw neg_sub }
  ... = a - ((a-b)⊔0)        : by  { rw ← neg_join_eq_neg_meet_neg, rw ← sub_eq_add_neg, }

-- Bourbaki A.VI.12 Prop 9 c)
-- Can we rewrite `lattice_ordered_add_comm_group.le_pos b` as `b.le_pos`?
/--
Let `α` be a lattice ordered commutative group and let `a` and `b` be elements in `α` with positive
components `a⁺` and `b⁺` and negative components `a⁻` and `b⁻` respectively. Then `b` dominates `a`
if and only if `b⁺` dominates `a⁺` and `a⁻` dominates `b⁻`.
-/
lemma le_iff_pos_le_neg_ge (a b : α) : a ≤ b ↔ a⁺ ≤ b⁺ ∧ b⁻ ≤ a⁻ :=
begin
  split,
  { intro h,
    split,
    { apply sup_le
      (le_trans h (lattice_ordered_add_comm_group.le_pos b))
      (lattice_ordered_add_comm_group.pos_pos b), },
    { rw ← neg_le_neg_iff at h,
      apply sup_le
      (le_trans h (lattice_ordered_add_comm_group.le_neg a))
      (lattice_ordered_add_comm_group.neg_pos a), }
  },
  { intro h,
    rw [← pos_sub_neg' a, ← pos_sub_neg' b ],
    apply sub_le_sub h.1 h.2, }
end

-- The proof from Bourbaki A.VI.12 Prop 9 d)
/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with absolute value
`|a|`, positive component `a⁺` and negative component `a⁻`. Then `|a|` decomposes as the sum of `a⁺`
and `a⁻`.
-/
lemma pos_add_neg (a : α) : |a| = a⁺ + a⁻ :=
begin
  rw le_antisymm_iff,
  split,
  { unfold has_abs.abs,
    rw sup_le_iff,
    split,
    { nth_rewrite 0 ← add_zero a,
      apply add_le_add
        (lattice_ordered_add_comm_group.le_pos a)
        (lattice_ordered_add_comm_group.neg_pos a) },
    { nth_rewrite 0 ← zero_add (-a),
      apply add_le_add
        (lattice_ordered_add_comm_group.pos_pos a)
        (lattice_ordered_add_comm_group.le_neg a) }
  },
  { have mod_eq_pos: |a|⁺ = |a| :=
    begin
      nth_rewrite 1 ← pos_sub_neg' (|a|),
      rw sub_eq_add_neg,
      symmetry,
      rw [add_right_eq_self, neg_eq_zero, le_antisymm_iff ],
      split,
      { rw ← pos_meet_neg_eq_zero a,
        apply le_inf,
        { rw pos_eq_neg_neg,
          apply and.right
            (iff.elim_left (le_iff_pos_le_neg_ge _ _)
            (lattice_ordered_add_comm_group.neg_le_abs a)), },
        { apply and.right
            (iff.elim_left (le_iff_pos_le_neg_ge _ _)
            (lattice_ordered_add_comm_group.le_abs a)), } },
      { apply lattice_ordered_add_comm_group.neg_pos, }
    end,
    rw [← add_eq_meet_add_join, pos_meet_neg_eq_zero, zero_add, ← mod_eq_pos ],
    apply sup_le,
    apply and.left
      (iff.elim_left (le_iff_pos_le_neg_ge _ _)
      (lattice_ordered_add_comm_group.le_abs a)),
    rw neg_eq_pos_neg,
    apply and.left
      (iff.elim_left (le_iff_pos_le_neg_ge _ _)
      (lattice_ordered_add_comm_group.neg_le_abs a)), }
end

/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α` and let `|b-a|`
be the absolute value of `b-a`. Then,
$$a⊔b - (a⊓b) = |b-a|.$$
-/
lemma join_sub_meet_eq_abs_sub (a b : α) : a⊔b - (a⊓b) = |b-a| :=
begin
  rw [join_eq_add_pos_sub, inf_comm, meet_eq_sub_pos_sub],
  simp only [add_sub_sub_cancel],
  rw [pos_eq_neg_neg, add_comm, neg_sub, pos_add_neg],
end

/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α` and let `|b-a|`
be the absolute value of `b-a`. Then,
$$2•(a⊔b) = a + b + |b - a|.$$
-/
lemma two_join_eq_add_add_abs_sub (a b : α) : 2•(a⊔b) = a + b + |b - a| :=
begin
  rw [← add_eq_meet_add_join a b, ← join_sub_meet_eq_abs_sub],
  abel,
  simp only [← gsmul_coe_nat],
  norm_cast,
end

/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α` and let `|b-a|`
be the absolute value of `b-a`. Then,
$$2•(a⊓b) = a + b - |b - a|.$$
-/
lemma two_meet_eq_add_sub_abs_sub (a b : α) : 2•(a⊓b) = a + b - |b - a| :=
begin
  rw [← add_eq_meet_add_join a b, ← join_sub_meet_eq_abs_sub],
  abel,
  simp only [← gsmul_coe_nat],
  norm_cast,
end

/--
Every lattice ordered commutative group is a distributive lattice
-/
@[priority 100] -- see Note [lower instance priority]
instance lattice_ordered_add_comm_group.to_distrib_lattice (α : Type u)
  [s : lattice_ordered_add_comm_group α] : distrib_lattice α :=
{ le_sup_inf :=
  begin
    intros,
    rw [← add_le_add_iff_left (x⊓y⊓z), inf_assoc, add_eq_meet_add_join x (y⊓z),
      ← neg_add_le_iff_le_add, le_inf_iff ],
    split,
    { rw [neg_add_le_iff_le_add, ← add_eq_meet_add_join x y ],
      apply add_le_add,
      { apply inf_le_inf_left, apply inf_le_left, },
      { apply inf_le_left, } },
    { rw [neg_add_le_iff_le_add, ← add_eq_meet_add_join x z ],
      apply add_le_add,
      { apply inf_le_inf_left, apply inf_le_right, },
      { apply inf_le_right, }, }
  end,
  ..s
}

-- See, e.g. Zaanen, Lectures on Riesz Spaces
-- 3rd lecture
/--
Let `α` be a lattice ordered commutative group and let `a`, `b` and `c` be elements in `α`. Let
`|a⊔c-(b⊔c)|`, `|a⊓c-b⊓c|` and `|a-b|` denote the absolute values of `a⊔c-(b⊔c)`, `a⊓c-b⊓c` and
`a-b` respectively. Then,
$$|a⊔c-(b⊔c)| + |a⊓c-b⊓c| = |a-b|.$$
-/
theorem abs_diff_sup_add_abs_diff_inf (a b c : α) :
|a⊔c-(b⊔c)| + |a⊓c-b⊓c| = |a-b| :=
  calc |a⊔c-(b⊔c)| + |a⊓c-b⊓c| =
    (b⊔c)⊔(a⊔c) - (b⊔c)⊓(a⊔c) + |a⊓c-b⊓c|       : by {rw ← join_sub_meet_eq_abs_sub, }
    ... = (b⊔c)⊔(a⊔c) - (b⊔c)⊓(a⊔c) + (b⊓c⊔a⊓c - b⊓c⊓(a⊓c)) : by {rw ←join_sub_meet_eq_abs_sub, }
    ... = b⊔a⊔c - ((b⊓a)⊔c) + ((b⊔a)⊓c - b⊓a⊓c) : by {
      rw [← sup_inf_right, ← inf_sup_right, sup_assoc ],
      nth_rewrite 1 sup_comm,
      rw [sup_right_idem, sup_assoc, inf_assoc ],
      nth_rewrite 3 inf_comm,
      rw [inf_right_idem, inf_assoc], }
    ... = b⊔a⊔c + (b⊔a)⊓c -(((b⊓a)⊔c)+b⊓a⊓c)    : by {abel,}
    ... = b⊔a + c -(b⊓a+c)                      :
      by {rw [add_comm, add_eq_meet_add_join, add_comm (b ⊓ a ⊔ c), add_eq_meet_add_join] }
    ... = b⊔a - b⊓a                             : by { simp, }
    ... = |a-b|                                 : by { rw join_sub_meet_eq_abs_sub, }

/--
Let `α` be a lattice ordered commutative group and let `a` be a positive element in `α`. Then `a` is
equal to its positive component `a⁺`.
-/
lemma pos_pos_id (a : α) (h : 0≤ a): a⁺ = a :=
begin
  unfold lattice_ordered_add_comm_group.pos,
  apply sup_of_le_left h,
end

/--
Let `α` be a lattice ordered commutative group and let `a` be a positive element in `α`. Then `a` is
equal to its absolute value `|a|`.
-/
lemma abs_pos_eq (a : α) (h: 0≤a) : |a| = a :=
begin
  unfold has_abs.abs,
  rw [join_eq_add_pos_sub, sub_neg_eq_add, neg_add_eq_sub, ←add_left_inj a, sub_add_cancel,
    ← two_smul ℕ, pos_pos_id ],
  exact nsmul_nonneg h 2,
end

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α`. Then the absolute
value `|a|` of `a` is positive.
-/
lemma lattice_ordered_add_comm_group.abs_pos (a : α) : 0 ≤ |a| :=
begin
  rw [pos_add_neg, ← add_zero (0:α)],
  apply add_le_add
    (lattice_ordered_add_comm_group.pos_pos a)
    (lattice_ordered_add_comm_group.neg_pos a),
end

/--
Let `α` be a lattice ordered commutative group. The unary operation of taking the absolute value is
idempotent.
-/
lemma abs_idempotent (a : α) : |a| = | |a| | :=
begin
  rw abs_pos_eq (|a|),
  apply lattice_ordered_add_comm_group.abs_pos,
end

-- Commutative case, Zaanen, 3rd lecture
-- For the non-commutative case, see Birkhoff Theorem 19 (27)
/--
Let `α` be a lattice ordered commutative group and let `a`, `b` and `c` be elements in `α`. Let
`|a⊔c-(b⊔c)|`, `|a⊓c-b⊓c|` and `|a-b|` denote the absolute values of `a⊔c-(b⊔c)`, `a⊓c-b⊓c` and
`a-b` respectively. Then `|a-b|` dominates `|a⊔c-(b⊔c)|` and `|a⊓c-b⊓c|`.
-/
theorem Birkhoff_inequalities (a b c : α) :
|a⊔c-(b⊔c)| ⊔ |a⊓c-b⊓c| ≤ |a-b| :=
begin
  rw sup_le_iff,
  split,
  { apply le_of_add_le_of_nonneg_left,
    rw abs_diff_sup_add_abs_diff_inf,
    apply lattice_ordered_add_comm_group.abs_pos, },
  { apply le_of_add_le_of_nonneg_right,
    rw abs_diff_sup_add_abs_diff_inf,
    apply lattice_ordered_add_comm_group.abs_pos, }
end

-- Banasiak Proposition 2.12, Zaanen 2nd lecture
/--
Let `α` be a lattice ordered commutative group. Then the absolute value satisfies the triangle
inequality.
-/
lemma abs_triangle  (a b : α) : |a+b| ≤ |a|+|b| :=
begin
  apply sup_le,
  { apply add_le_add,
    apply lattice_ordered_add_comm_group.le_abs,
    apply lattice_ordered_add_comm_group.le_abs, },
  { rw neg_add,
    apply add_le_add,
    apply lattice_ordered_add_comm_group.neg_le_abs,
    apply lattice_ordered_add_comm_group.neg_le_abs, }
end
