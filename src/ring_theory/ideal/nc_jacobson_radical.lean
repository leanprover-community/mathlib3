/-
Copyright (c) 2022 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
import ring_theory.ideal.basic
import tactic.noncomm_ring
/-!
# Noncommutative Jacobson radical

In this file, we define the Jacobson radical of a ring and prove its basic properties.

Let `R` be a (possibly noncommutative) ring. The *Jacobson radical* of `R` is defined
to be the intersection of all maximal *left* ideals of `R`, which coincides with that of
all maximal *right* ideals, so it is a two-sided ideal.

## Main definitions

* `nc_jacobson R : ideal R`: the Jacobson radical of a ring `R`, that is,
  the intersection of all maximal *left* ideals.

## Main statements

* `mem_nc_jacobson_tfae`: some equivalent conditions for an element in a ring
  to be contained in the Jacobson radical.

* `nc_jacobson_symm`: the definition of the Jacobson radical is left-right symmetric, that is,
  the intersection of all maximal left ideals coincides with that of all maximal right ideals.
-/

universe u
open mul_opposite

section monoid
variables {M : Type u} {a : M} {b : M} [monoid M]
/-! ### Some lemmas on inverses in monoids -/

lemma is_unit.op (h : is_unit a) : is_unit (op a) :=
let ⟨a, _⟩ := h in ⟨units.op_equiv.symm (op a), by simpa⟩

lemma is_unit.unop {x : Mᵐᵒᵖ} (h : is_unit x) : is_unit (unop x) :=
let ⟨a, _⟩ := h in ⟨unop a.op_equiv, by simpa⟩

lemma is_unit_op_iff_is_unit {a : M} : is_unit (op a) ↔ is_unit a :=
⟨λ h, unop_op a ▸ h.unop, is_unit.op⟩

lemma is_unit_unop_iff_is_unit {x : Mᵐᵒᵖ} : is_unit (unop x) ↔ is_unit x :=
⟨λ h, op_unop x ▸ h.op, is_unit.unop⟩

lemma is_unit_iff_has_two_sided_inv :
  is_unit a ↔ ∃ x : M, a * x = 1 ∧ x * a = 1 :=
⟨λ ⟨⟨a, x, hax, hxa⟩, rfl⟩, ⟨x, hax, hxa⟩, λ ⟨x, hax, hxa⟩, ⟨⟨a, x, hax, hxa⟩, rfl⟩⟩

/-- An element `a : M` of a monoid has a left inverse
if there is some `x : M` satisfying `x * a = 1`. -/
def has_left_inv (a : M) : Prop := ∃ x : M, x * a = 1

/-- An element `a : M` of a monoid has a right inverse
if there is some `x : M` satisfying `a * x = 1`. -/
def has_right_inv (a : M) : Prop := ∃ x : M, a * x = 1

/-- An element of a monoid is a unit
if and only if it has both a left inverse and a right inverse. -/
theorem is_unit_iff_has_left_inv_right_inv :
  is_unit a ↔ has_left_inv a ∧ has_right_inv a :=
⟨λ h, ⟨h.exists_left_inv, h.exists_right_inv⟩,
  λ ⟨⟨x, hxa⟩, ⟨y, hay⟩⟩, ⟨⟨a, x, by { convert hay,
  rw [←mul_one x, ←hay, ←mul_assoc, hxa, one_mul] }, hxa⟩, rfl⟩⟩

/-- An element of a monoid is a unit
if it has a left inverse which also has a left inverse. -/
theorem is_unit_of_has_left_inv_of_has_left_inv
  (h₁ : b * a = 1) (h₂ : has_left_inv b) : is_unit a :=
let ⟨c, hcb⟩ := h₂ in ⟨⟨a, b, by { convert hcb,
  rw [←one_mul a, ←hcb, mul_assoc, h₁, mul_one] }, h₁⟩, rfl⟩

end monoid

section ring
variables {R : Type u} {a : R} {b : R} [ring R]
/-! ### Some lemmas on inverses in rings -/

lemma has_left_inv.one_add_mul_swap
  (h : has_left_inv (1 + a * b)) : has_left_inv (1 + b * a) :=
begin
  obtain ⟨u, hu⟩ := h,
  existsi 1 - b * u * a,
  calc (1 - b * u * a) * (1 + b * a)
        = 1 + b * a - b * (u * (1 + a * b)) * a : by noncomm_ring
    ... = 1 : by rw [hu, mul_one, add_sub_cancel],
end

lemma has_right_inv.one_add_mul_swap
  (h : has_right_inv (1 + a * b)) : has_right_inv (1 + b * a) :=
begin
  obtain ⟨u, hu⟩ := h,
  existsi 1 - b * u * a,
  calc (1 + b * a) * (1 - b * u * a)
        = 1 + b * a - b * ((1 + a * b ) * u) * a : by noncomm_ring
    ... = 1 : by rw [hu, mul_one, add_sub_cancel],
end

lemma is_unit.one_add_mul_swap
  (h : is_unit (1 + a * b)) : is_unit (1 + b * a) :=
begin
  rw is_unit_iff_has_left_inv_right_inv at *,
  obtain ⟨h₁, h₂⟩ := h,
  exact ⟨h₁.one_add_mul_swap, h₂.one_add_mul_swap⟩,
end

end ring

namespace ideal
section nc_jacobson_radical
variables {R : Type u} [ring R]
/-! ### Jacobson radical of a ring -/

/--
For a semiring `R`, `nc_jacobson R` is the Jacobson radical of `R`, that is,
the intersection of all maximal left ideals of of `R`. Note that we use left ideals.
-/
def nc_jacobson (R : Type u) [semiring R] : ideal R :=
Inf {I : ideal R | I.is_maximal }

lemma has_left_inv_iff_span_top {x : R} :
  has_left_inv x ↔ span ({x} : set R) = ⊤ :=
begin
  split,
  { rintro ⟨a, hax⟩,
    apply eq_top_of_unit_mem _ x a _ hax,
    apply submodule.mem_span_singleton_self },
  { intro h,
    have : (1 : R) ∈ span ({x} : set R) := by { rw h, exact submodule.mem_top },
    exact (mem_span_singleton').mp this },
end

lemma not_has_left_inv_iff_mem_maximal {x : R} :
  ¬has_left_inv x ↔ ∃ I : ideal R, I.is_maximal ∧ x ∈ I :=
begin
  rw has_left_inv_iff_span_top,
  split,
  { intro hx,
    obtain ⟨I, hImax, hxI⟩ := exists_le_maximal _ hx,
    exact ⟨I, hImax, by {apply hxI, apply submodule.mem_span_singleton_self}⟩ },
  { rintro ⟨I, hImax, hxI⟩ hcontra,
    refine hImax.ne_top _,
    rwa [eq_top_iff, ←hcontra, span_le, set.singleton_subset_iff] },
end

lemma has_left_inv_one_add_of_mem_jacobson {x : R} :
  x ∈ nc_jacobson R → has_left_inv (1 + x):=
begin
  contrapose,
  rw not_has_left_inv_iff_mem_maximal,
  rintro ⟨I, hImax, hxxI⟩ hx,
  refine hImax.ne_top _,
  rw eq_top_iff_one,
  have hxI : x ∈ I := by { rw [nc_jacobson, mem_Inf] at hx, apply hx hImax },
  exact (add_mem_cancel_right hxI).mp hxxI,
end

lemma one_add_mul_self_mem_maximal_of_not_mem_maximal {x : R} {I : ideal R}
  (h₁ : I.is_maximal) (h₂ : x ∉ I) : ∃ a : R, 1 + a * x ∈ I :=
begin
  have : (1 : R) ∈ I ⊔ span {x},
  { rw is_maximal_iff at h₁,
    apply h₁.2 _ _ le_sup_left h₂,
    apply mem_sup_right,
    apply submodule.mem_span_singleton_self },
  rw submodule.mem_sup at this,
  obtain ⟨m, hmI, y, hy, hmy⟩ := this,
  rw mem_span_singleton' at hy,
  obtain ⟨a, rfl⟩ := hy,
  existsi -a,
  rwa [←hmy, neg_mul, add_neg_cancel_right],
end

/-- Characterizations of the Jacobson radical of a ring.

The following are equivalent for an element `x` in a ring `R`.
* 0: `x` is in the Jacobson radical of `R`, that is, contained in every mximal left ideal.
* 1: `1 + a * x` has a left inverse for any `a : R`.
* 2: `1 + a * x` is a unit for any `a : R`.
* 3: `1 + x * b` is a unit for any `b : R`.
* 4: `1 + a * x * b` is a unit for any `a b : R`.
-/
theorem mem_nc_jacobson_tfae {R : Type u} [ring R] (x : R) : tfae [
  x ∈ nc_jacobson R,
  ∀ a : R, has_left_inv (1 + a * x),
  ∀ a : R, is_unit (1 + a * x),
  ∀ b : R, is_unit (1 + x * b),
  ∀ a b : R, is_unit (1 + a * x * b)] :=
begin
  tfae_have : 1 → 2,
  { exact λ hx a, has_left_inv_one_add_of_mem_jacobson $
    (nc_jacobson R).smul_mem' a hx },
  tfae_have : 2 → 3,
  { intros hx a,
    obtain ⟨c, hc⟩ := hx a,
    apply is_unit_of_has_left_inv_of_has_left_inv hc,
    suffices : c = 1 + ( -c * a * x),
    { rw this, apply hx },
    { calc c = c * (1 + a * x) + ( -c * a * x) : by noncomm_ring
        ...  = 1 + ( -c * a * x) : by rw hc } },
  tfae_have : 3 → 5,
  { intros hx _ _,
    apply is_unit.one_add_mul_swap,
    rw ←mul_assoc,
    apply hx },
  tfae_have : 5 → 1,
  { intro h,
    by_contra hx,
    rw [nc_jacobson, submodule.mem_Inf] at hx,
    simp only [not_forall] at hx,
    rcases hx with ⟨I, hImax, hxI⟩,
    refine hImax.ne_top _,
    obtain ⟨a, ha⟩ := one_add_mul_self_mem_maximal_of_not_mem_maximal hImax hxI,
    apply eq_top_of_is_unit_mem _ ha,
    specialize h a 1,
    rwa [mul_assoc, mul_one] at h },
  tfae_have : 3 ↔ 4,
  { split; exact λ h b, (h b).one_add_mul_swap },
  tfae_finish,
end

/--
The definition of the Jacobson radical of a ring is left-right symmetric, that is,
the intersection of all maximal left ideals coincides with that of all maximal right ideals.
We express this by using the opposite ring `Rᵐᵒᵖ`, that is,
the Jacobson radical of `R` coincides with that of `Rᵐᵒᵖ`,
-/
theorem nc_jacobson_symm {x : R} :
  x ∈ nc_jacobson R ↔ op x ∈ nc_jacobson Rᵐᵒᵖ :=
begin
  split,
  { intro hx,
    rw (mem_nc_jacobson_tfae $ op x).out 0 3,
    intro a,
    rw [←is_unit_unop_iff_is_unit, unop_add, unop_one, unop_mul, unop_op],
    apply ((mem_nc_jacobson_tfae x).out 0 2).mp hx },
  { intro hx,
    rw (mem_nc_jacobson_tfae x).out 0 3,
    intro a,
    rw [←is_unit_op_iff_is_unit, op_add, op_one, op_mul],
    apply ((mem_nc_jacobson_tfae $ op x).out 0 2).mp hx },
end

end nc_jacobson_radical
end ideal
