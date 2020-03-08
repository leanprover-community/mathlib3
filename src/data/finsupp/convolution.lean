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

open finset

universes u₁ u₂ u₃ u₄ u₅
variables {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄} {ι : Type u₅}

namespace finsupp

/-! ### Declarations about the convolution product on `finsupp`s -/

/-- The product of `f g : α →₀ β` is the finitely supported function
  whose value at `a` is the sum of `f x * g y` over all pairs `x, y`
  such that `x + y = a`. (Think of the product of multivariate
  polynomials where `α` is the monoid of monomial exponents.) -/
instance [has_add α] [semiring β] : has_mul (α →₀ β) :=
⟨λf g, f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ + a₂) (b₁ * b₂)⟩

lemma mul_def [has_add α] [semiring β] {f g : α →₀ β} :
  f * g = (f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ + a₂) (b₁ * b₂)) :=
rfl

lemma support_mul [has_add α] [semiring β] (a b : α →₀ β) :
  (a * b).support ⊆ a.support.bind (λa₁, b.support.bind $ λa₂, {a₁ + a₂}) :=
subset.trans support_sum $ bind_mono $ assume a₁ _,
  subset.trans support_sum $ bind_mono $ assume a₂ _, support_single_subset

/-- The unit of the multiplication is `single 0 1`, i.e. the function
  that is `1` at `0` and zero elsewhere. -/
instance [has_zero α] [has_zero β] [has_one β] : has_one (α →₀ β) :=
⟨single 0 1⟩

lemma one_def [has_zero α] [has_zero β] [has_one β] : 1 = (single 0 1 : α →₀ β) :=
rfl

/-!
### Declarations related to semirings

When `α` is an `add_monoid` and `β` is a `semiring`, there is a `semiring` instance on
`α →₀ β`.
-/

section
variables [add_monoid α] [semiring β]

-- TODO: the simplifier unfolds 0 in the instance proof!
private lemma zero_mul (f : α →₀ β) : 0 * f = 0 :=
by simp only [mul_def, sum_zero_index]

private lemma mul_zero (f : α →₀ β) : f * 0 = 0 :=
by simp only [mul_def, sum_zero_index, sum_zero]

private lemma left_distrib (a b c : α →₀ β) : a * (b + c) = a * b + a * c :=
by simp only [mul_def, sum_add_index, mul_add, _root_.mul_zero, single_zero, single_add,
  eq_self_iff_true, forall_true_iff, forall_3_true_iff, sum_add]

private lemma right_distrib (a b c : α →₀ β) : (a + b) * c = a * c + b * c :=
by simp only [mul_def, sum_add_index, add_mul, _root_.mul_zero, _root_.zero_mul, single_zero,
  single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff, sum_zero, sum_add]

instance : semiring (α →₀ β) :=
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

instance [add_comm_monoid α] [comm_semiring β] : comm_semiring (α →₀ β) :=
{ mul_comm := assume f g,
  begin
    simp only [mul_def, finsupp.sum, mul_comm],
    rw [finset.sum_comm],
    simp only [add_comm]
  end,
  .. finsupp.semiring }

instance [add_monoid α] [ring β] : ring (α →₀ β) :=
{ neg := has_neg.neg,
  add_left_neg := add_left_neg,
  .. finsupp.semiring }

instance [add_comm_monoid α] [comm_ring β] : comm_ring (α →₀ β) :=
{ mul_comm := mul_comm, .. finsupp.ring}

lemma single_mul_single [has_add α] [semiring β] {a₁ a₂ : α} {b₁ b₂ : β}:
  single a₁ b₁ * single a₂ b₂ = single (a₁ + a₂) (b₁ * b₂) :=
(sum_single_index (by simp only [_root_.zero_mul, single_zero, sum_zero])).trans
  (sum_single_index (by rw [_root_.mul_zero, single_zero]))

lemma prod_single [add_comm_monoid α] [comm_semiring β]
  {s : finset ι} {a : ι → α} {b : ι → β} :
  s.prod (λi, single (a i) (b i)) = single (s.sum a) (s.prod b) :=
finset.induction_on s rfl $ λ a s has ih, by rw [prod_insert has, ih,
  single_mul_single, sum_insert has, prod_insert has]

section

instance [semiring γ] [add_comm_monoid β] [semimodule γ β] : has_scalar γ (α →₀ β) :=
⟨λa v, v.map_range ((•) a) (smul_zero _)⟩

variables (α β)

@[simp] lemma smul_apply' {R:semiring γ} [add_comm_monoid β] [semimodule γ β]
  {a : α} {b : γ} {v : α →₀ β} : (b • v) a = b • (v a) :=
rfl

instance [semiring γ] [add_comm_monoid β] [semimodule γ β] : semimodule γ (α →₀ β) :=
{ smul      := (•),
  smul_add  := λ a x y, ext $ λ _, smul_add _ _ _,
  add_smul  := λ a x y, ext $ λ _, add_smul _ _ _,
  one_smul  := λ x, ext $ λ _, one_smul _ _,
  mul_smul  := λ r s x, ext $ λ _, mul_smul _ _ _,
  zero_smul := λ x, ext $ λ _, zero_smul _ _,
  smul_zero := λ x, ext $ λ _, smul_zero _ }

instance [ring γ] [add_comm_group β] [module γ β] : module γ (α →₀ β) :=
{ ..finsupp.semimodule α β }

instance [field γ] [add_comm_group β] [vector_space γ β] : vector_space γ (α →₀ β) :=
{ ..finsupp.module α β }

variables {α β}
lemma support_smul {R:semiring γ} [add_comm_monoid β] [semimodule γ β] {b : γ} {g : α →₀ β} :
  (b • g).support ⊆ g.support :=
λ a, by simp only [smul_apply', mem_support_iff, ne.def]; exact mt (λ h, h.symm ▸ smul_zero _)

section
variables {α' : Type*} [has_zero δ] {p : α → Prop}

@[simp] lemma filter_smul {R : semiring γ} [add_comm_monoid β] [semimodule γ β]
  {b : γ} {v : α →₀ β} : (b • v).filter p = b • v.filter p :=
ext $ λ a, begin
  by_cases p a,
  { simp only [h, smul_apply', filter_apply_pos] },
  { simp only [h, smul_apply', not_false_iff, filter_apply_neg, smul_zero] }
end

end

lemma map_domain_smul {α'} {R : semiring γ} [add_comm_monoid β] [semimodule γ β]
   {f : α → α'} (b : γ) (v : α →₀ β) : map_domain f (b • v) = b • map_domain f v :=
begin
  change map_domain f (map_range _ _ _) = map_range _ _ _,
  apply finsupp.induction v, { simp only [map_domain_zero, map_range_zero] },
  intros a b v' hv₁ hv₂ IH,
  rw [map_range_add, map_domain_add, IH, map_domain_add, map_range_add,
    map_range_single, map_domain_single, map_domain_single, map_range_single];
  apply smul_add
end

@[simp] lemma smul_single {R : semiring γ} [add_comm_monoid β] [semimodule γ β]
  (c : γ) (a : α) (b : β) : c • finsupp.single a b = finsupp.single a (c • b) :=
ext $ λ a', by by_cases a = a';
  [{ subst h, simp only [smul_apply', single_eq_same] },
   simp only [h, smul_apply', ne.def, not_false_iff, single_eq_of_ne, smul_zero]]

end

@[simp] lemma smul_apply [ring β] {a : α} {b : β} {v : α →₀ β} :
  (b • v) a = b • (v a) :=
rfl

lemma sum_smul_index [ring β] [add_comm_monoid γ] {g : α →₀ β} {b : β} {h : α → β → γ}
  (h0 : ∀i, h i 0 = 0) : (b • g).sum h = g.sum (λi a, h i (b * a)) :=
finsupp.sum_map_range_index h0

section
variables [semiring β] [semiring γ]

lemma sum_mul (b : γ) (s : α →₀ β) {f : α → β → γ} :
  (s.sum f) * b = s.sum (λ a c, (f a (s a)) * b) :=
by simp only [finsupp.sum, finset.sum_mul]

lemma mul_sum (b : γ) (s : α →₀ β) {f : α → β → γ} :
  b * (s.sum f) = s.sum (λ a c, b * (f a (s a))) :=
by simp only [finsupp.sum, finset.mul_sum]

protected lemma eq_zero_of_zero_eq_one
  (zero_eq_one : (0 : β) = 1) (l : α →₀ β) : l = 0 :=
by ext i; simp only [eq_zero_of_zero_eq_one β zero_eq_one (l i), finsupp.zero_apply]

end

end finsupp
