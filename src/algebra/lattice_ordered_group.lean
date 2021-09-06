/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.ordered_group
import algebra.group_power.basic -- Needed for squares
import tactic.nth_rewrite

/-!
# Lattice ordered groups

Lattice ordered groups were introduced by [Birkhoff][birkhoff1942].
They form the algebraic underpinnings of vector lattices, Banach lattices, AL-space, AM-space etc.

This file develops the basic theory, concentrating on the commutative case.

## Main statements

- `pos_div_neg`: Every element `a` of a lattice ordered commutative group has a decomposition
  `a⁺-a⁻` into the difference of the positive and negative component.
- `pos_inf_neg_eq_one`: The positive and negative components are coprime.
- `abs_triangle`: The absolute value operation satisfies the triangle inequality.

It is shown that the inf and sup operations are related to the absolute value operation by a
number of equations and inequalities.

## Notations

- `a⁺ = a ⊔ 0`: The *positive component* of an element `a` of a lattice ordered commutative group
- `a⁻ = (-a) ⊔ 0`: The *negative component* of an element `a` of a lattice ordered commutative group
* `|a| = a⊔(-a)`: The *absolute value* of an element `a` of a lattice ordered commutative group

## Implementation notes

A lattice ordered commutative group is a type `α` satisfying:

* `[lattice α]`
* `[comm_group α]`
* `[covariant_class α α (*) (≤)]`

The remainder of the file establishes basic properties of lattice ordered commutative groups. A
number of these results also hold in the non-commutative case ([Birkhoff][birkhoff1942],
[Fuchs][fuchs1963]) but we have not developed that here, since we are primarily interested in vector
lattices.

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

-- A linearly ordered additive commutative group is a lattice ordered commutative group
@[priority 100, to_additive] -- see Note [lower instance priority]
instance linear_ordered_comm_group.to_covariant_class (α : Type u)
  [linear_ordered_comm_group α] :  covariant_class α α (*) (≤) :=
{ elim := λ a b c bc, linear_ordered_comm_group.mul_le_mul_left _ _ bc a }

variables {α : Type u} [lattice α] [comm_group α]

-- Special case of Bourbaki A.VI.9 (1)
/--
Let `α` be a lattice ordered commutative group. For all elements `a`, `b` and `c` in `α`,
$$c + (a ⊔ b) = (c + a) ⊔ (c + b).$$
-/
@[to_additive]
lemma mul_sup_eq_mul_sup_mul [covariant_class α α (*) (≤)]
  (a b c : α) : c * (a ⊔ b) = (c * a) ⊔ (c * b) :=
begin
  refine le_antisymm _ (by simp),
  rw [← mul_le_mul_iff_left (c⁻¹), ← mul_assoc, inv_mul_self, one_mul],
  apply sup_le,
  { simp },
  { simp },
end

-- Special case of Bourbaki A.VI.9 (2)
/--
Let `α` be a lattice ordered commutative group. For all elements `a` and `b` in `α`,
$$-(a ⊔ b)=(-a) ⊓ (-b).$$
-/
@[to_additive]
lemma inv_sup_eq_inv_inf_inv [covariant_class α α (*) (≤)] (a b : α) : (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹ :=
begin
  rw le_antisymm_iff,
  split,
  { rw le_inf_iff,
    split,
    { rw inv_le_inv_iff, apply le_sup_left, },
    { rw inv_le_inv_iff, apply le_sup_right, } },
  { rw ← inv_le_inv_iff, simp,
    split,
    { rw ← inv_le_inv_iff, simp, },
    { rw ← inv_le_inv_iff, simp, } }
end

/--
Let `α` be a lattice ordered commutative group. For all elements `a` and `b` in `α`,
$$ -(a ⊓ b) = -a ⊔ -b.$$
-/
@[to_additive]
lemma inv_inf_eq_sup_inv [covariant_class α α (*) (≤)] (a b : α) : (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹ :=
by rw [← inv_inv (a⁻¹ ⊔ b⁻¹), inv_sup_eq_inv_inf_inv a⁻¹ b⁻¹, inv_inv, inv_inv]

-- Bourbaki A.VI.10 Prop 7
/--
Let `α` be a lattice ordered commutative group. For all elements `a` and `b` in `α`,
$$a ⊓ b + (a ⊔ b) = a + b.$$
-/
@[to_additive]
lemma inf_mul_sup [covariant_class α α (*) (≤)] (a b : α) : a ⊓ b * (a ⊔ b) = a * b :=
calc a⊓b * (a ⊔ b) = a ⊓ b * ((a * b) * (b⁻¹ ⊔ a⁻¹)) :
  by {  rw mul_sup_eq_mul_sup_mul b⁻¹ a⁻¹ (a * b), simp,  }
... = a⊓b * ((a * b) * (a ⊓ b)⁻¹) : by rw [inv_inf_eq_sup_inv, sup_comm]
... = a * b                       : by rw [mul_comm, inv_mul_cancel_right]

/--
Absolute value is a unary operator with properties similar to the absolute value of a real number.
-/
local notation `|`a`|` := mabs a

namespace lattice_ordered_comm_group

-- Bourbaki A.VI.12 Definition 4
/--
Let `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type `α`,
the element `a ⊔ 0` is said to be the *positive component* of `a`, denoted `a⁺`.
-/
@[to_additive pos
  "Let `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type `α`,
  the element `a ⊔ 0` is said to be the *positive component* of `a`, denoted `a⁺`."]
def mpos (a : α) : α :=  a ⊔ 1
postfix `⁺`:1000 := mpos

/--
Let `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type `α`,
the element `(-a) ⊔ 0` is said to be the *negative component* of `a`, denoted `a⁻`.
-/
@[to_additive neg
  "Let `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type `α`,
  the element `(-a) ⊔ 0` is said to be the *negative component* of `a`, denoted `a⁻`."]
def mneg (a : α) : α := a⁻¹ ⊔ 1
postfix `⁻`:1000 := mneg

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with absolute value
`|a|`. Then,
$$a ≤ |a|.$$
-/
@[to_additive le_abs]
lemma le_mabs (a : α) : a ≤ |a| := le_sup_left

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with absolute value
`|a|`. Then,
$$-a ≤ |a|.$$
-/
@[to_additive]
lemma inv_le_abs (a : α) : a⁻¹ ≤ |a| := le_sup_right

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with positive
 component `a⁺`. Then `a⁺` is positive.
-/
@[to_additive pos_pos]
lemma m_pos_pos (a : α) : 1 ≤ a⁺ := le_sup_right

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` withnegative
component `a⁻`. Then `a⁻` is positive.
-/
@[to_additive neg_pos]
lemma m_neg_pos (a : α) : 1 ≤ a⁻ := le_sup_right

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with positive
component `a⁺`. Then `a⁺` dominates `a`.
-/
@[to_additive le_pos]
lemma m_le_pos (a : α) : a ≤ a⁺ := le_sup_left

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with negative
component `a⁻`. Then `a⁻` dominates `-a`.
-/
@[to_additive le_neg]
lemma m_le_neg (a : α) : a⁻¹ ≤ a⁻ := le_sup_left

-- Bourbaki A.VI.12
/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α`. Then the negative
component `a⁻` of `a` is equal to the positive component `(-a)⁺` of `-a`.
-/
@[to_additive]
lemma neg_eq_pos_inv (a : α) : a⁻ = (a⁻¹)⁺ := by { unfold mneg, unfold mpos}

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α`. Then the positive
component `a⁺` of `a` is equal to the negative component `(-a)⁻` of `-a`.
-/
@[to_additive]
lemma pos_eq_neg_inv (a : α) : a⁺ = (a⁻¹)⁻ := by simp [neg_eq_pos_inv]

-- We use this in Bourbaki A.VI.12  Prop 9 a)
/--
Let `α` be a lattice ordered commutative group. For all elements `a`, `b` and `c` in `α`,
$$c + (a ⊓ b) = (c + a) ⊓ (c + b).$$
-/
@[to_additive]
lemma mul_inf_eq_mul_inf_mul [covariant_class α α (*) (≤)]
  (a b c : α) : c * (a ⊓ b) = (c * a) ⊓ (c * b) :=
begin
  rw le_antisymm_iff,
  split,
  { simp, },
  { rw [← mul_le_mul_iff_left c⁻¹, ← mul_assoc, inv_mul_self, one_mul, le_inf_iff], simp, }
end

-- We use this in Bourbaki A.VI.12  Prop 9 a)
/--
Let `α` be a lattice ordered commutative group with identity `0` and let `a` be an element in `α`
with negative component `a⁻`. Then
$$a⁻ = -(a ⊓ 0).$$
-/
@[to_additive]
lemma neg_eq_inv_inf_one [covariant_class α α (*) (≤)] (a : α) : a⁻ = (a ⊓ 1)⁻¹ :=
begin
  unfold lattice_ordered_comm_group.mneg,
  rw [← inv_inj, inv_sup_eq_inv_inf_inv, inv_inv, inv_inv, one_inv],
end

-- Bourbaki A.VI.12  Prop 9 a)
/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with positive
component `a⁺` and negative component `a⁻`. Then `a` can be decomposed as the difference of `a⁺` and
`a⁻`.
-/
@[to_additive]
lemma pos_inv_neg [covariant_class α α (*) (≤)] (a : α) : a = a⁺ / a⁻ :=
begin
  rw div_eq_mul_inv,
  apply eq_mul_inv_of_mul_eq,
  unfold lattice_ordered_comm_group.mneg,
  rw [mul_sup_eq_mul_sup_mul, mul_one, mul_right_inv, sup_comm],
  unfold lattice_ordered_comm_group.mpos,
end

-- Hack to work around rewrite not working if lhs is a variable
@[to_additive, nolint doc_blame_thm]
lemma pos_div_neg' [covariant_class α α (*) (≤)] (a : α) :  a⁺ / a⁻ = a := (pos_inv_neg _).symm

-- Bourbaki A.VI.12  Prop 9 a)
/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with positive
component `a⁺` and negative component `a⁻`. Then `a⁺` and `a⁻` are co-prime (and, since they are
positive, disjoint).
-/
@[to_additive]
lemma pos_inf_neg_eq_one [covariant_class α α (*) (≤)] (a : α) : a⁺ ⊓ a⁻=1 :=
by rw [←mul_right_inj (a⁻)⁻¹, mul_inf_eq_mul_inf_mul, mul_one, mul_left_inv, mul_comm,
  ←div_eq_mul_inv, pos_div_neg', neg_eq_inv_inf_one, inv_inv]

-- Bourbaki A.VI.12 (with a and b swapped)
/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α`, and let
`(a - b)⁺` be the positive componet of `a - b`. Then
$$a⊔b = b + (a - b)⁺.$$
-/
@[to_additive]
lemma sup_eq_mul_pos_div [covariant_class α α (*) (≤)] (a b : α) : a ⊔ b = b * (a / b)⁺ :=
calc  a ⊔ b = (b * (a / b)) ⊔ (b * 1) : by {rw [mul_one b, div_eq_mul_inv, mul_comm a,
  mul_inv_cancel_left], }
... = b * ((a / b) ⊔ 1) : by { rw ← mul_sup_eq_mul_sup_mul (a / b) 1 b}

-- Bourbaki A.VI.12 (with a and b swapped)
/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α`, and let
`(a - b)⁺` be the positive componet of `a - b`. Then
$$a⊓b = a - (a - b)⁺.$$
-/
@[to_additive]
lemma inf_eq_div_pos_div [covariant_class α α (*) (≤)] (a b : α) : a ⊓ b = a / (a / b)⁺ :=
calc a ⊓ b = (a * 1) ⊓ (a * (b / a)) : by { rw [mul_one a, div_eq_mul_inv, mul_comm b,
  mul_inv_cancel_left], }
... = a * (1 ⊓ (b / a))     : by rw ← mul_inf_eq_mul_inf_mul 1 (b / a) a
... = a * ((b / a) ⊓ 1)     : by rw inf_comm
... = a * ((a / b)⁻¹ ⊓ 1)   : by { rw div_eq_mul_inv,  nth_rewrite 0 ← inv_inv b,
  rw [← mul_inv, mul_comm b⁻¹, ← div_eq_mul_inv], }
... = a * ((a / b)⁻¹ ⊓ 1⁻¹) : by rw one_inv
... = a / ((a / b) ⊔ 1)     : by rw [← inv_sup_eq_inv_inf_inv, ← div_eq_mul_inv]

-- Bourbaki A.VI.12 Prop 9 c)
/--
Let `α` be a lattice ordered commutative group and let `a` and `b` be elements in `α` with positive
components `a⁺` and `b⁺` and negative components `a⁻` and `b⁻` respectively. Then `b` dominates `a`
if and only if `b⁺` dominates `a⁺` and `a⁻` dominates `b⁻`.
-/
@[to_additive le_iff_pos_le_neg_ge]
lemma m_le_iff_pos_le_neg_ge [covariant_class α α (*) (≤)] (a b : α) : a ≤ b ↔ a⁺ ≤ b⁺ ∧ b⁻ ≤ a⁻ :=
begin
  split,
  { intro h,
    split,
    { apply sup_le
      (le_trans h (lattice_ordered_comm_group.m_le_pos b))
      (lattice_ordered_comm_group.m_pos_pos b), },
    { rw ← inv_le_inv_iff at h,
      apply sup_le
      (le_trans h (lattice_ordered_comm_group.m_le_neg a))
      (lattice_ordered_comm_group.m_neg_pos a), }
  },
  { intro h,
    rw [← pos_div_neg' a, ← pos_div_neg' b ],
    apply div_le_div'' h.1 h.2, }
end

-- The proof from Bourbaki A.VI.12 Prop 9 d)
/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with absolute value
`|a|`, positive component `a⁺` and negative component `a⁻`. Then `|a|` decomposes as the sum of `a⁺`
and `a⁻`.
-/
@[to_additive]
lemma pos_mul_neg [covariant_class α α (*) (≤)] (a : α) : |a| = a⁺ * a⁻ :=
begin
  rw le_antisymm_iff,
  split,
  { unfold mabs,
    rw sup_le_iff,
    split,
    { nth_rewrite 0 ← mul_one a,
      apply mul_le_mul'
        (lattice_ordered_comm_group.m_le_pos a)
        (lattice_ordered_comm_group.m_neg_pos a) },
    { nth_rewrite 0 ← one_mul (a⁻¹),
      apply mul_le_mul'
        (lattice_ordered_comm_group.m_pos_pos a)
        (lattice_ordered_comm_group.m_le_neg a) } },
  { have mod_eq_pos: |a|⁺ = |a|,
    { nth_rewrite 1 ← pos_div_neg' (|a|),
      rw div_eq_mul_inv,
      symmetry,
      rw [mul_right_eq_self], symmetry, rw [one_eq_inv, le_antisymm_iff],
      split,
      { rw ← pos_inf_neg_eq_one a,
        apply le_inf,
        { rw pos_eq_neg_inv,
          apply and.right
            (iff.elim_left (m_le_iff_pos_le_neg_ge _ _)
            (lattice_ordered_comm_group.inv_le_abs a)), },
        { apply and.right
            (iff.elim_left (m_le_iff_pos_le_neg_ge _ _)
            (lattice_ordered_comm_group.le_mabs a)), } },
      { apply lattice_ordered_comm_group.m_neg_pos, } },
    rw [← inf_mul_sup, pos_inf_neg_eq_one, one_mul, ← mod_eq_pos ],
    apply sup_le,
    apply and.left
      (iff.elim_left (m_le_iff_pos_le_neg_ge _ _)
      (lattice_ordered_comm_group.le_mabs a)),
    rw neg_eq_pos_inv,
    apply and.left
      (iff.elim_left (m_le_iff_pos_le_neg_ge _ _)
      (lattice_ordered_comm_group.inv_le_abs a)), }
end

/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α` and let `|b - a|`
be the absolute value of `b - a`. Then,
$$a ⊔ b - (a ⊓ b) = |b - a|.$$
-/
@[to_additive]
lemma sup_div_inf_eq_abs_div [covariant_class α α (*) (≤)] (a b : α) :
  (a ⊔ b) / (a ⊓ b) = |b / a| :=
begin
  rw [sup_eq_mul_pos_div, inf_comm, inf_eq_div_pos_div, div_eq_mul_inv],
  nth_rewrite 1 div_eq_mul_inv,
  rw [mul_inv_rev, inv_inv, mul_comm, ← mul_assoc, inv_mul_cancel_right, pos_eq_neg_inv (a / b)],
  nth_rewrite 1 div_eq_mul_inv,
  rw [mul_inv_rev, ← div_eq_mul_inv, inv_inv, ← pos_mul_neg],
end

/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α` and let `|b - a|`
be the absolute value of `b - a`. Then,
$$2•(a ⊔ b) = a + b + |b - a|.$$
-/
@[to_additive]
lemma sup_sq_eq_mul_mul_abs_div [covariant_class α α (*) (≤)] (a b : α) :
  (a ⊔ b)^2 = a * b * |b / a| :=
by rw [← inf_mul_sup a b, ← sup_div_inf_eq_abs_div, div_eq_mul_inv, ← mul_assoc, mul_comm,
    mul_assoc, ← pow_two, inv_mul_cancel_left]

/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α` and let `|b-a|`
be the absolute value of `b-a`. Then,
$$2•(a ⊓ b) = a + b - |b - a|.$$
-/
@[to_additive]
lemma two_inf_eq_mul_div_abs_div [covariant_class α α (*) (≤)] (a b : α) :
  (a ⊓ b)^2 = a * b / |b / a| :=
by rw [← inf_mul_sup a b, ← sup_div_inf_eq_abs_div, div_eq_mul_inv, div_eq_mul_inv,
    mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_comm_assoc, ← pow_two]

/--
Every lattice ordered commutative group is a distributive lattice
-/
@[to_additive
  "Every lattice ordered commutative additive group is a distributive lattice"
]
def lattice_ordered_comm_group_to_distrib_lattice (α : Type u)
  [s: lattice α] [comm_group α] [covariant_class α α (*) (≤)] : distrib_lattice α :=
{ le_sup_inf :=
  begin
    intros,
    rw [← mul_le_mul_iff_left (x ⊓ (y ⊓ z)),  inf_mul_sup x (y ⊓ z),
      ← inv_mul_le_iff_le_mul, le_inf_iff ],
    split,
    { rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x y ],
      apply mul_le_mul',
      { apply inf_le_inf_left, apply inf_le_left, },
      { apply inf_le_left, } },
    { rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x z ],
      apply mul_le_mul',
      { apply inf_le_inf_left, apply inf_le_right, },
      { apply inf_le_right, }, }
  end,
  ..s }

-- See, e.g. Zaanen, Lectures on Riesz Spaces
-- 3rd lecture
/--
Let `α` be a lattice ordered commutative group and let `a`, `b` and `c` be elements in `α`. Let
`|a ⊔ c - (b ⊔ c)|`, `|a ⊓ c - b ⊓ c|` and `|a - b|` denote the absolute values of
`a ⊔ c - (b ⊔ c)`, `a ⊓ c - b ⊓ c` and `a - b` respectively. Then,
$$|a ⊔ c - (b ⊔ c)| + |a ⊓ c-b ⊓ c| = |a - b|.$$
-/
@[to_additive]
theorem abs_div_sup_mul_abs_div_inf [covariant_class α α (*) (≤)] (a b c : α) :
  |(a ⊔ c)/(b ⊔ c)| * |(a ⊓ c)/(b ⊓ c)| = |a / b| :=
begin
  letI : distrib_lattice α := lattice_ordered_comm_group_to_distrib_lattice α,
  calc |(a ⊔ c) / (b ⊔ c)| * |a ⊓ c / (b ⊓ c)| =
    ((b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c))) * |a ⊓ c / (b ⊓ c)| : by rw sup_div_inf_eq_abs_div
  ... = (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * (((b ⊓ c) ⊔ (a ⊓ c)) / ((b ⊓ c) ⊓ (a ⊓ c))) :
    by rw sup_div_inf_eq_abs_div (b ⊓ c) (a ⊓ c)
  ... = (b ⊔ a ⊔ c) / ((b ⊓ a) ⊔ c) * (((b ⊔ a) ⊓ c) / (b ⊓ a ⊓ c)) : by {
    rw [← sup_inf_right, ← inf_sup_right, sup_assoc ],
    nth_rewrite 1 sup_comm,
    rw [sup_right_idem, sup_assoc, inf_assoc ],
    nth_rewrite 3 inf_comm,
    rw [inf_right_idem, inf_assoc], }
  ... = (b ⊔ a ⊔ c) * ((b ⊔ a) ⊓ c) /(((b ⊓ a) ⊔ c) * (b ⊓ a ⊓ c)) : by rw div_mul_comm
  ... = (b ⊔ a) * c / (b ⊓ a * c) :
    by rw [mul_comm, inf_mul_sup, mul_comm (b ⊓ a ⊔ c), inf_mul_sup]
  ... = (b ⊔ a) / (b ⊓ a) : by rw [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_inv_cancel_left,
      ← div_eq_mul_inv]
  ... = |a / b|           : by rw sup_div_inf_eq_abs_div
end

/--
Let `α` be a lattice ordered commutative group and let `a` be a positive element in `α`. Then `a` is
equal to its positive component `a⁺`.
-/
@[to_additive pos_pos_id]
lemma m_pos_pos_id (a : α) (h : 1 ≤ a): a⁺ = a :=
begin
  unfold lattice_ordered_comm_group.mpos,
  apply sup_of_le_left h,
end

/--
Let `α` be a lattice ordered commutative group and let `a` be a positive element in `α`. Then `a` is
equal to its absolute value `|a|`.
-/
@[to_additive abs_pos_eq]
lemma mabs_pos_eq [covariant_class α α (*) (≤)] (a : α) (h: 1 ≤ a) : |a| = a :=
begin
  unfold mabs,
  rw [sup_eq_mul_pos_div, div_eq_mul_inv, inv_inv, ← pow_two, inv_mul_eq_iff_eq_mul,
    ← pow_two, m_pos_pos_id ],
  rw pow_two,
  apply one_le_mul h h,
end

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α`. Then the absolute
value `|a|` of `a` is positive.
-/
@[to_additive abs_pos]
lemma mabs_pos [covariant_class α α (*) (≤)] (a : α) : 1 ≤ |a| :=
begin
  rw pos_mul_neg,
  apply one_le_mul
    (lattice_ordered_comm_group.m_pos_pos a)
    (lattice_ordered_comm_group.m_neg_pos a),
end

/--
Let `α` be a lattice ordered commutative group. The unary operation of taking the absolute value is
idempotent.
-/
@[to_additive abs_idempotent]
lemma mabs_idempotent [covariant_class α α (*) (≤)] (a : α) : |a| = | |a| | :=
begin
  rw mabs_pos_eq (|a|),
  apply lattice_ordered_comm_group.mabs_pos,
end

-- Commutative case, Zaanen, 3rd lecture
-- For the non-commutative case, see Birkhoff Theorem 19 (27)
/--
Let `α` be a lattice ordered commutative group and let `a`, `b` and `c` be elements in `α`. Let
`|a ⊔ c - (b ⊔ c)|`, `|a ⊓ c - b ⊓ c|` and `|a - b|` denote the absolute values of
`a ⊔ c - (b ⊔ c)`, `a ⊓ c - b ⊓ c` and`a - b` respectively. Then `|a - b|` dominates
`|a ⊔ c - (b ⊔ c)|` and `|a ⊓ c - b ⊓ c|`.
-/
@[to_additive Birkhoff_inequalities]
theorem m_Birkhoff_inequalities [covariant_class α α (*) (≤)] (a b c : α) :
|(a ⊔ c) / (b ⊔ c)| ⊔ |(a ⊓ c) / (b ⊓ c)| ≤ |a / b| :=
begin
  rw sup_le_iff,
  split,
  { apply le_of_mul_le_of_one_le_left,
    rw abs_div_sup_mul_abs_div_inf,
    apply lattice_ordered_comm_group.mabs_pos, },
  { apply le_of_mul_le_of_one_le_right,
    rw abs_div_sup_mul_abs_div_inf,
    apply lattice_ordered_comm_group.mabs_pos, }
end

-- Banasiak Proposition 2.12, Zaanen 2nd lecture
/--
Let `α` be a lattice ordered commutative group. Then the absolute value satisfies the triangle
inequality.
-/
@[to_additive abs_triangle]
lemma mabs_triangle [covariant_class α α (*) (≤)] (a b : α) : |a * b| ≤ |a| * |b| :=
begin
  apply sup_le,
  { apply mul_le_mul'
    (lattice_ordered_comm_group.le_mabs a)
    (lattice_ordered_comm_group.le_mabs b), },
  { rw mul_inv,
    apply mul_le_mul',
    apply lattice_ordered_comm_group.inv_le_abs,
    apply lattice_ordered_comm_group.inv_le_abs, }
end

end lattice_ordered_comm_group
