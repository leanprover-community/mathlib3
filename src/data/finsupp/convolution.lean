/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.finsupp

/-!
# The convolution product on `finsupp`.

When the domain of a `finsupp` has an additive structure, we can define
the convolution product.

TODO per issue #1864: we intend to introduce a new type tag for
this product, probably `add_monoid_algebra`, and instead provide
pointwise multiplication as the default multiplication on `finsupp`.
-/

noncomputable theory
open_locale classical

open finset finsupp

universes u₁ u₂
variables (α : Type u₁) (β : Type u₂)

section
variables [monoid α] [semiring β]

def monoid_algebra := α →₀ β

variables {α β}

instance : add_comm_monoid (monoid_algebra α β) :=
by { dsimp [monoid_algebra], apply_instance }
end

namespace monoid_algebra

variables {α β}
local attribute [reducible] monoid_algebra

section
variables [monoid α] [semiring β]

/-! ### Declarations about the convolution product on `finsupp`s -/

/-- The product of `f g : α →₀ β` is the finitely supported function
  whose value at `a` is the sum of `f x * g y` over all pairs `x, y`
  such that `x + y = a`. (Think of the product of multivariate
  polynomials where `α` is the monoid of monomial exponents.) -/
instance : has_mul (monoid_algebra α β) :=
⟨λf g, f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ * a₂) (b₁ * b₂)⟩

lemma mul_def {f g : monoid_algebra α β} :
  f * g = (f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ * a₂) (b₁ * b₂)) :=
rfl

lemma support_mul (a b : monoid_algebra α β) :
  (a * b).support ⊆ a.support.bind (λa₁, b.support.bind $ λa₂, {a₁ * a₂}) :=
subset.trans support_sum $ bind_mono $ assume a₁ _,
  subset.trans support_sum $ bind_mono $ assume a₂ _, support_single_subset

/-- The unit of the multiplication is `single 1 1`, i.e. the function
  that is `1` at `1` and zero elsewhere. -/
instance : has_one (monoid_algebra α β) :=
⟨single 1 1⟩

lemma one_def : (1 : monoid_algebra α β) = single 1 1 :=
rfl

-- TODO: the simplifier unfolds 0 in the instance proof!
private lemma zero_mul (f : monoid_algebra α β) : 0 * f = 0 :=
by simp only [mul_def, sum_zero_index]

private lemma mul_zero (f : monoid_algebra α β) : f * 0 = 0 :=
by simp only [mul_def, sum_zero_index, sum_zero]

private lemma left_distrib (a b c : monoid_algebra α β) : a * (b + c) = a * b + a * c :=
by simp only [mul_def, sum_add_index, mul_add, _root_.mul_zero, single_zero, single_add,
  eq_self_iff_true, forall_true_iff, forall_3_true_iff, sum_add]

private lemma right_distrib (a b c : monoid_algebra α β) : (a + b) * c = a * c + b * c :=
by simp only [mul_def, sum_add_index, add_mul, _root_.mul_zero, _root_.zero_mul, single_zero,
  single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff, sum_zero, sum_add]

instance : semiring (monoid_algebra α β) :=
{ one       := 1,
  mul       := (*),
  one_mul   := assume f, by simp only [mul_def, one_def, sum_single_index, _root_.zero_mul,
    single_zero, sum_zero, zero_add, one_mul, sum_single],
  mul_one   := assume f, by simp only [mul_def, one_def, sum_single_index, _root_.mul_zero,
    single_zero, sum_zero, add_zero, mul_one, sum_single],
  zero_mul  := zero_mul,
  mul_zero  := mul_zero,
  mul_assoc := assume f g h, by simp only [mul_def, sum_sum_index, sum_zero_index, sum_add_index,
    sum_single_index, single_zero, single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff,
    add_mul, mul_add, add_assoc, mul_assoc, _root_.zero_mul, _root_.mul_zero, sum_zero, sum_add],
  left_distrib  := left_distrib,
  right_distrib := right_distrib,
  .. finsupp.add_comm_monoid }

end

instance [comm_monoid α] [comm_semiring β] : comm_semiring (monoid_algebra α β) :=
{ mul_comm := assume f g,
  begin
    simp only [mul_def, finsupp.sum, mul_comm],
    rw [finset.sum_comm],
    simp only [mul_comm]
  end,
  .. monoid_algebra.semiring }

instance [monoid α] [ring β] : has_neg (monoid_algebra α β) :=
by apply_instance

instance [monoid α] [ring β] : ring (monoid_algebra α β) :=
{ neg := has_neg.neg,
  add_left_neg := add_left_neg,
  .. monoid_algebra.semiring }

instance [comm_monoid α] [comm_ring β] : comm_ring (monoid_algebra α β) :=
{ mul_comm := mul_comm, .. monoid_algebra.ring}

lemma single_mul_single [monoid α] [semiring β] {a₁ a₂ : α} {b₁ b₂ : β}:
  (single a₁ b₁ : monoid_algebra α β) * single a₂ b₂ = single (a₁ * a₂) (b₁ * b₂) :=
(sum_single_index (by simp only [_root_.zero_mul, single_zero, sum_zero])).trans
  (sum_single_index (by rw [_root_.mul_zero, single_zero]))

universe ui
variable {ι : Type ui}

lemma prod_single [comm_monoid α] [comm_semiring β]
  {s : finset ι} {a : ι → α} {b : ι → β} :
  s.prod (λi, single (a i) (b i)) = single (s.prod a) (s.prod b) :=
finset.induction_on s rfl $ λ a s has ih, by rw [prod_insert has, ih,
  single_mul_single, prod_insert has, prod_insert has]

end monoid_algebra

section
variables [add_monoid α] [semiring β]

def add_monoid_algebra := α →₀ β

variables {α β}

instance : add_comm_monoid (add_monoid_algebra α β) :=
by { dsimp [add_monoid_algebra], apply_instance }
end

namespace add_monoid_algebra

variables {α β}
local attribute [reducible] add_monoid_algebra

section
variables [add_monoid α] [semiring β]

/-! ### Declarations about the convolution product on `finsupp`s -/

/-- The product of `f g : α →₀ β` is the finitely supported function
  whose value at `a` is the sum of `f x * g y` over all pairs `x, y`
  such that `x + y = a`. (Think of the product of multivariate
  polynomials where `α` is the monoid of monomial exponents.) -/
instance : has_mul (add_monoid_algebra α β) :=
⟨λf g, f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ + a₂) (b₁ * b₂)⟩

lemma mul_def {f g : add_monoid_algebra α β} :
  f * g = (f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ + a₂) (b₁ * b₂)) :=
rfl

lemma support_mul (a b : add_monoid_algebra α β) :
  (a * b).support ⊆ a.support.bind (λa₁, b.support.bind $ λa₂, {a₁ + a₂}) :=
subset.trans support_sum $ bind_mono $ assume a₁ _,
  subset.trans support_sum $ bind_mono $ assume a₂ _, support_single_subset

/-- The unit of the multiplication is `single 1 1`, i.e. the function
  that is `1` at `0` and zero elsewhere. -/
instance : has_one (add_monoid_algebra α β) :=
⟨single 0 1⟩

lemma one_def : (1 : add_monoid_algebra α β) = single 0 1 :=
rfl

-- TODO: the simplifier unfolds 0 in the instance proof!
private lemma zero_mul (f : add_monoid_algebra α β) : 0 * f = 0 :=
by simp only [mul_def, sum_zero_index]

private lemma mul_zero (f : add_monoid_algebra α β) : f * 0 = 0 :=
by simp only [mul_def, sum_zero_index, sum_zero]

private lemma left_distrib (a b c : add_monoid_algebra α β) : a * (b + c) = a * b + a * c :=
by simp only [mul_def, sum_add_index, mul_add, _root_.mul_zero, single_zero, single_add,
  eq_self_iff_true, forall_true_iff, forall_3_true_iff, sum_add]

private lemma right_distrib (a b c : add_monoid_algebra α β) : (a + b) * c = a * c + b * c :=
by simp only [mul_def, sum_add_index, add_mul, _root_.mul_zero, _root_.zero_mul, single_zero,
  single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff, sum_zero, sum_add]

instance : semiring (add_monoid_algebra α β) :=
{ one       := 1,
  mul       := (*),
  one_mul   := assume f, by simp only [mul_def, one_def, sum_single_index, _root_.zero_mul,
    single_zero, sum_zero, zero_add, one_mul, sum_single],
  mul_one   := assume f, by simp only [mul_def, one_def, sum_single_index, _root_.mul_zero,
    single_zero, sum_zero, add_zero, mul_one, sum_single],
  zero_mul  := zero_mul,
  mul_zero  := mul_zero,
  mul_assoc := assume f g h, by simp only [mul_def, sum_sum_index, sum_zero_index, sum_add_index,
    sum_single_index, single_zero, single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff,
    add_mul, mul_add, add_assoc, mul_assoc, _root_.zero_mul, _root_.mul_zero, sum_zero, sum_add],
  left_distrib  := left_distrib,
  right_distrib := right_distrib,
  .. finsupp.add_comm_monoid }

end

instance [add_comm_monoid α] [comm_semiring β] : comm_semiring (add_monoid_algebra α β) :=
{ mul_comm := assume f g,
  begin
    simp only [mul_def, finsupp.sum, mul_comm],
    rw [finset.sum_comm],
    simp only [add_comm]
  end,
  .. add_monoid_algebra.semiring }

instance [add_monoid α] [ring β] : has_neg (add_monoid_algebra α β) :=
by apply_instance

instance [add_monoid α] [ring β] : ring (add_monoid_algebra α β) :=
{ neg := has_neg.neg,
  add_left_neg := add_left_neg,
  .. add_monoid_algebra.semiring }

instance [add_comm_monoid α] [comm_ring β] : comm_ring (add_monoid_algebra α β) :=
{ mul_comm := mul_comm, .. add_monoid_algebra.ring}

lemma single_mul_single [add_monoid α] [semiring β] {a₁ a₂ : α} {b₁ b₂ : β}:
  (single a₁ b₁ : add_monoid_algebra α β) * single a₂ b₂ = single (a₁ + a₂) (b₁ * b₂) :=
(sum_single_index (by simp only [_root_.zero_mul, single_zero, sum_zero])).trans
  (sum_single_index (by rw [_root_.mul_zero, single_zero]))

universe ui
variable {ι : Type ui}

lemma prod_single [add_comm_monoid α] [comm_semiring β]
  {s : finset ι} {a : ι → α} {b : ι → β} :
  s.prod (λi, single (a i) (b i)) = single (s.sum a) (s.prod b) :=
finset.induction_on s rfl $ λ a s has ih, by rw [prod_insert has, ih,
  single_mul_single, sum_insert has, prod_insert has]

end add_monoid_algebra
