/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import data.finsupp.indicator
import algebra.big_operators.pi
import algebra.big_operators.ring
import algebra.big_operators.order
import group_theory.submonoid.membership

/-!
# Big operators for finsupps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains theorems relevant to big operators in finitely supported functions.
-/

noncomputable theory

open finset function
open_locale big_operators

variables {α ι γ A B C : Type*} [add_comm_monoid A] [add_comm_monoid B] [add_comm_monoid C]
variables {t : ι → A → C} (h0 : ∀ i, t i 0 = 0) (h1 : ∀ i x y, t i (x + y) = t i x + t i y)
variables {s : finset α} {f : α → (ι →₀ A)} (i : ι)
variables (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variables {β M M' N P G H R S : Type*}

namespace finsupp

/-!
### Declarations about `sum` and `prod`

In most of this section, the domain `β` is assumed to be an `add_monoid`.
-/

section sum_prod

/-- `prod f g` is the product of `g a (f a)` over the support of `f`. -/
@[to_additive "`sum f g` is the sum of `g a (f a)` over the support of `f`. "]
def prod [has_zero M] [comm_monoid N] (f : α →₀ M) (g : α → M → N) : N :=
∏ a in f.support, g a (f a)

variables [has_zero M] [has_zero M'] [comm_monoid N]

@[to_additive]
lemma prod_of_support_subset (f : α →₀ M) {s : finset α}
  (hs : f.support ⊆ s) (g : α → M → N) (h : ∀ i ∈ s, g i 0 = 1) :
  f.prod g = ∏ x in s, g x (f x) :=
finset.prod_subset hs $ λ x hxs hx, h x hxs ▸ congr_arg (g x) $ not_mem_support_iff.1 hx

@[to_additive]
lemma prod_fintype [fintype α] (f : α →₀ M) (g : α → M → N) (h : ∀ i, g i 0 = 1) :
  f.prod g = ∏ i, g i (f i) :=
f.prod_of_support_subset (subset_univ _) g (λ x _, h x)

@[simp, to_additive]
lemma prod_single_index {a : α} {b : M} {h : α → M → N} (h_zero : h a 0 = 1) :
  (single a b).prod h = h a b :=
calc (single a b).prod h = ∏ x in {a}, h x (single a b x) :
  prod_of_support_subset _ support_single_subset h $
    λ x hx, (mem_singleton.1 hx).symm ▸ h_zero
... = h a b : by simp

@[to_additive]
lemma prod_map_range_index {f : M → M'} {hf : f 0 = 0} {g : α →₀ M} {h : α → M' → N}
  (h0 : ∀a, h a 0 = 1) : (map_range f hf g).prod h = g.prod (λa b, h a (f b)) :=
finset.prod_subset support_map_range $ λ _ _ H,
  by rw [not_mem_support_iff.1 H, h0]

@[simp, to_additive]
lemma prod_zero_index {h : α → M → N} : (0 : α →₀ M).prod h = 1 := rfl

@[to_additive]
lemma prod_comm (f : α →₀ M) (g : β →₀ M') (h : α → M → β → M' → N) :
  f.prod (λ x v, g.prod (λ x' v', h x v x' v')) = g.prod (λ x' v', f.prod (λ x v, h x v x' v')) :=
finset.prod_comm

@[simp, to_additive]
lemma prod_ite_eq [decidable_eq α] (f : α →₀ M) (a : α) (b : α → M → N) :
  f.prod (λ x v, ite (a = x) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 :=
by { dsimp [finsupp.prod], rw f.support.prod_ite_eq, }

@[simp] lemma sum_ite_self_eq
  [decidable_eq α] {N : Type*} [add_comm_monoid N] (f : α →₀ N) (a : α) :
  f.sum (λ x v, ite (a = x) v 0) = f a :=
begin
  classical,
  convert f.sum_ite_eq a (λ x, id),
  simp [ite_eq_right_iff.2 eq.symm]
end

/-- A restatement of `prod_ite_eq` with the equality test reversed. -/
@[simp, to_additive "A restatement of `sum_ite_eq` with the equality test reversed."]
lemma prod_ite_eq' [decidable_eq α] (f : α →₀ M) (a : α) (b : α → M → N) :
  f.prod (λ x v, ite (x = a) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 :=
by { dsimp [finsupp.prod], rw f.support.prod_ite_eq', }

@[simp] lemma sum_ite_self_eq'
  [decidable_eq α] {N : Type*} [add_comm_monoid N] (f : α →₀ N) (a : α) :
  f.sum (λ x v, ite (x = a) v 0) = f a :=
begin
  classical,
  convert f.sum_ite_eq' a (λ x, id),
  simp [ite_eq_right_iff.2 eq.symm]
end

@[simp] lemma prod_pow [fintype α] (f : α →₀ ℕ) (g : α → N) :
  f.prod (λ a b, g a ^ b) = ∏ a, g a ^ (f a) :=
f.prod_fintype _ $ λ a, pow_zero _

/-- If `g` maps a second argument of 0 to 1, then multiplying it over the
result of `on_finset` is the same as multiplying it over the original
`finset`. -/
@[to_additive "If `g` maps a second argument of 0 to 0, summing it over the
result of `on_finset` is the same as summing it over the original
`finset`."]
lemma on_finset_prod {s : finset α} {f : α → M} {g : α → M → N}
    (hf : ∀a, f a ≠ 0 → a ∈ s) (hg : ∀ a, g a 0 = 1) :
  (on_finset s f hf).prod g = ∏ a in s, g a (f a) :=
finset.prod_subset support_on_finset_subset $ by simp [*] { contextual := tt }

/-- Taking a product over `f : α →₀ M` is the same as multiplying the value on a single element
`y ∈ f.support` by the product over `erase y f`. -/
@[to_additive /-" Taking a sum over over `f : α →₀ M` is the same as adding the value on a
single element `y ∈ f.support` to the sum over `erase y f`. "-/]
lemma mul_prod_erase (f : α →₀ M) (y : α) (g : α → M → N) (hyf : y ∈ f.support) :
  g y (f y) * (erase y f).prod g = f.prod g :=
begin
  classical,
  rw [finsupp.prod, finsupp.prod, ←finset.mul_prod_erase _ _ hyf, finsupp.support_erase,
    finset.prod_congr rfl],
  intros h hx,
  rw finsupp.erase_ne (ne_of_mem_erase hx),
end

/-- Generalization of `finsupp.mul_prod_erase`: if `g` maps a second argument of 0 to 1,
then its product over `f : α →₀ M` is the same as multiplying the value on any element
`y : α` by the product over `erase y f`. -/
@[to_additive /-" Generalization of `finsupp.add_sum_erase`: if `g` maps a second argument of 0
to 0, then its sum over `f : α →₀ M` is the same as adding the value on any element
`y : α` to the sum over `erase y f`. "-/]
lemma mul_prod_erase' (f : α →₀ M) (y : α) (g : α → M → N) (hg : ∀ (i : α), g i 0 = 1) :
  g y (f y) * (erase y f).prod g = f.prod g :=
begin
  classical,
  by_cases hyf : y ∈ f.support,
  { exact finsupp.mul_prod_erase f y g hyf },
  { rw [not_mem_support_iff.mp hyf, hg y, erase_of_not_mem_support hyf, one_mul] },
end

@[to_additive]
lemma _root_.submonoid_class.finsupp_prod_mem {S : Type*} [set_like S N] [submonoid_class S N]
  (s : S) (f : α →₀ M) (g : α → M → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : f.prod g ∈ s :=
prod_mem $ λ i hi, h _ (finsupp.mem_support_iff.mp hi)

@[to_additive]
lemma prod_congr {f : α →₀ M} {g1 g2 : α → M → N}
  (h : ∀ x ∈ f.support, g1 x (f x) = g2 x (f x)) : f.prod g1 = f.prod g2 :=
finset.prod_congr rfl h

end sum_prod

end finsupp


@[to_additive]
lemma map_finsupp_prod [has_zero M] [comm_monoid N] [comm_monoid P] {H : Type*}
  [monoid_hom_class H N P] (h : H) (f : α →₀ M) (g : α → M → N) :
  h (f.prod g) = f.prod (λ a b, h (g a b)) :=
map_prod h _ _

/-- Deprecated, use `_root_.map_finsupp_prod` instead. -/
@[to_additive "Deprecated, use `_root_.map_finsupp_sum` instead."]
protected lemma mul_equiv.map_finsupp_prod [has_zero M] [comm_monoid N] [comm_monoid P]
  (h : N ≃* P) (f : α →₀ M) (g : α → M → N) : h (f.prod g) = f.prod (λ a b, h (g a b)) :=
map_finsupp_prod h f g

/-- Deprecated, use `_root_.map_finsupp_prod` instead. -/
@[to_additive "Deprecated, use `_root_.map_finsupp_sum` instead."]
protected lemma monoid_hom.map_finsupp_prod [has_zero M] [comm_monoid N] [comm_monoid P]
  (h : N →* P) (f : α →₀ M) (g : α → M → N) : h (f.prod g) = f.prod (λ a b, h (g a b)) :=
map_finsupp_prod h f g

/-- Deprecated, use `_root_.map_finsupp_sum` instead. -/
protected lemma ring_hom.map_finsupp_sum [has_zero M] [semiring R] [semiring S]
  (h : R →+* S) (f : α →₀ M) (g : α → M → R) : h (f.sum g) = f.sum (λ a b, h (g a b)) :=
map_finsupp_sum h f g

/-- Deprecated, use `_root_.map_finsupp_prod` instead. -/
protected lemma ring_hom.map_finsupp_prod [has_zero M] [comm_semiring R] [comm_semiring S]
  (h : R →+* S) (f : α →₀ M) (g : α → M → R) : h (f.prod g) = f.prod (λ a b, h (g a b)) :=
map_finsupp_prod h f g

@[to_additive]
lemma monoid_hom.coe_finsupp_prod [has_zero β] [monoid N] [comm_monoid P]
  (f : α →₀ β) (g : α → β → N →* P) :
  ⇑(f.prod g) = f.prod (λ i fi, g i fi) :=
monoid_hom.coe_finset_prod _ _

@[simp, to_additive]
lemma monoid_hom.finsupp_prod_apply [has_zero β] [monoid N] [comm_monoid P]
  (f : α →₀ β) (g : α → β → N →* P) (x : N) :
  f.prod g x = f.prod (λ i fi, g i fi x) :=
monoid_hom.finset_prod_apply _ _ _

namespace finsupp

lemma single_multiset_sum [add_comm_monoid M] (s : multiset M) (a : α) :
  single a s.sum = (s.map (single a)).sum :=
multiset.induction_on s (single_zero _) $ λ a s ih,
by rw [multiset.sum_cons, single_add, ih, multiset.map_cons, multiset.sum_cons]

lemma single_finset_sum [add_comm_monoid M] (s : finset ι) (f : ι → M) (a : α) :
  single a (∑ b in s, f b) = ∑ b in s, single a (f b) :=
begin
  transitivity,
  apply single_multiset_sum,
  rw [multiset.map_map],
  refl
end

lemma single_sum [has_zero M] [add_comm_monoid N] (s : ι →₀ M) (f : ι → M → N) (a : α) :
  single a (s.sum f) = s.sum (λd c, single a (f d c)) :=
single_finset_sum _ _ _

@[to_additive]
lemma prod_neg_index [add_group G] [comm_monoid M] {g : α →₀ G} {h : α → G → M}
  (h0 : ∀a, h a 0 = 1) :
  (-g).prod h = g.prod (λa b, h a (- b)) :=
prod_map_range_index h0

end finsupp

namespace finsupp

lemma finset_sum_apply [add_comm_monoid N] (S : finset ι) (f : ι → α →₀ N) (a : α) :
  (∑ i in S, f i) a = ∑ i in S, f i a :=
(apply_add_hom a : (α →₀ N) →+ _).map_sum _ _

@[simp] lemma sum_apply [has_zero M] [add_comm_monoid N]
  {f : α →₀ M} {g : α → M → β →₀ N} {a₂ : β} :
  (f.sum g) a₂ = f.sum (λa₁ b, g a₁ b a₂) :=
finset_sum_apply _ _ _

lemma coe_finset_sum [add_comm_monoid N] (S : finset ι) (f : ι → α →₀ N) :
  ⇑(∑ i in S, f i) = ∑ i in S, f i :=
(coe_fn_add_hom : (α →₀ N) →+ _).map_sum _ _

lemma coe_sum [has_zero M] [add_comm_monoid N] (f : α →₀ M) (g : α → M → β →₀ N) :
  ⇑(f.sum g) = f.sum (λ a₁ b, g a₁ b) :=
coe_finset_sum _ _

lemma support_sum [decidable_eq β] [has_zero M] [add_comm_monoid N]
  {f : α →₀ M} {g : α → M → (β →₀ N)} :
  (f.sum g).support ⊆ f.support.bUnion (λa, (g a (f a)).support) :=
have ∀ c, f.sum (λ a b, g a b c) ≠ 0 → (∃ a, f a ≠ 0 ∧ ¬ (g a (f a)) c = 0),
  from assume a₁ h,
  let ⟨a, ha, ne⟩ := finset.exists_ne_zero_of_sum_ne_zero h in
  ⟨a, mem_support_iff.mp ha, ne⟩,
by simpa only [finset.subset_iff, mem_support_iff, finset.mem_bUnion, sum_apply, exists_prop]

lemma support_finset_sum [decidable_eq β] [add_comm_monoid M] {s : finset α} {f : α → (β →₀ M)} :
  (finset.sum s f).support ⊆ s.bUnion (λ x, (f x).support) :=
begin
  rw ←finset.sup_eq_bUnion,
  induction s using finset.cons_induction_on with a s ha ih,
  { refl },
  { rw [finset.sum_cons, finset.sup_cons],
    exact support_add.trans (finset.union_subset_union (finset.subset.refl _) ih), },
end

@[simp] lemma sum_zero [has_zero M] [add_comm_monoid N] {f : α →₀ M} :
  f.sum (λa b, (0 : N)) = 0 :=
finset.sum_const_zero

@[simp, to_additive]
lemma prod_mul  [has_zero M] [comm_monoid N] {f : α →₀ M} {h₁ h₂ : α → M → N} :
  f.prod (λa b, h₁ a b * h₂ a b) = f.prod h₁ * f.prod h₂ :=
finset.prod_mul_distrib

@[simp, to_additive]
lemma prod_inv [has_zero M] [comm_group G] {f : α →₀ M}
  {h : α → M → G} : f.prod (λa b, (h a b)⁻¹) = (f.prod h)⁻¹ :=
(map_prod ((monoid_hom.id G)⁻¹) _ _).symm

@[simp] lemma sum_sub [has_zero M] [add_comm_group G] {f : α →₀ M}
  {h₁ h₂ : α → M → G} :
  f.sum (λa b, h₁ a b - h₂ a b) = f.sum h₁ - f.sum h₂ :=
finset.sum_sub_distrib

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism on the support.
This is a more general version of `finsupp.prod_add_index'`; the latter has simpler hypotheses. -/
@[to_additive "Taking the product under `h` is an additive homomorphism of finsupps,
if `h` is an additive homomorphism on the support.
This is a more general version of `finsupp.sum_add_index'`; the latter has simpler hypotheses."]
lemma prod_add_index [decidable_eq α] [add_zero_class M] [comm_monoid N] {f g : α →₀ M}
  {h : α → M → N} (h_zero : ∀ a ∈ f.support ∪ g.support, h a 0 = 1)
  (h_add : ∀ (a ∈ f.support ∪ g.support) b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
  (f + g).prod h = f.prod h * g.prod h :=
begin
  rw [finsupp.prod_of_support_subset f (subset_union_left _ g.support) h h_zero,
      finsupp.prod_of_support_subset g (subset_union_right f.support _) h h_zero,
      ←finset.prod_mul_distrib,
      finsupp.prod_of_support_subset (f + g) finsupp.support_add h h_zero],
  exact finset.prod_congr rfl (λ x hx, (by apply h_add x hx)),
end

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism.
This is a more specialized version of `finsupp.prod_add_index` with simpler hypotheses. -/
@[to_additive "Taking the sum under `h` is an additive homomorphism of finsupps,
if `h` is an additive homomorphism.
This is a more specific version of `finsupp.sum_add_index` with simpler hypotheses."]
lemma prod_add_index' [add_zero_class M] [comm_monoid N] {f g : α →₀ M}
  {h : α → M → N} (h_zero : ∀a, h a 0 = 1) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
  (f + g).prod h = f.prod h * g.prod h :=
by classical; exact prod_add_index (λ a ha, h_zero a) (λ a ha, h_add a)

@[simp]
lemma sum_hom_add_index [add_zero_class M] [add_comm_monoid N] {f g : α →₀ M} (h : α → M →+ N) :
  (f + g).sum (λ x, h x) = f.sum (λ x, h x) + g.sum (λ x, h x) :=
sum_add_index' (λ a, (h a).map_zero) (λ a, (h a).map_add)

@[simp]
lemma prod_hom_add_index [add_zero_class M] [comm_monoid N] {f g : α →₀ M}
  (h : α → multiplicative M →* N) :
  (f + g).prod (λ a b, h a (multiplicative.of_add b)) =
    f.prod (λ a b, h a (multiplicative.of_add b)) * g.prod (λ a b, h a (multiplicative.of_add b)) :=
prod_add_index' (λ a, (h a).map_one) (λ a, (h a).map_mul)


/-- The canonical isomorphism between families of additive monoid homomorphisms `α → (M →+ N)`
and monoid homomorphisms `(α →₀ M) →+ N`. -/
def lift_add_hom [add_zero_class M] [add_comm_monoid N] : (α → M →+ N) ≃+ ((α →₀ M) →+ N) :=
{ to_fun := λ F,
  { to_fun := λ f, f.sum (λ x, F x),
    map_zero' := finset.sum_empty,
    map_add' := λ _ _, sum_add_index' (λ x, (F x).map_zero) (λ x, (F x).map_add) },
  inv_fun := λ F x, F.comp $ single_add_hom x,
  left_inv := λ F, by { ext, simp },
  right_inv := λ F, by { ext, simp },
  map_add' := λ F G, by { ext, simp } }

@[simp] lemma lift_add_hom_apply [add_comm_monoid M] [add_comm_monoid N]
  (F : α → M →+ N) (f : α →₀ M) :
  lift_add_hom F f = f.sum (λ x, F x) :=
rfl

@[simp] lemma lift_add_hom_symm_apply [add_comm_monoid M] [add_comm_monoid N]
  (F : (α →₀ M) →+ N) (x : α) :
  lift_add_hom.symm F x = F.comp (single_add_hom x) :=
rfl

lemma lift_add_hom_symm_apply_apply [add_comm_monoid M] [add_comm_monoid N]
  (F : (α →₀ M) →+ N) (x : α) (y : M) :
  lift_add_hom.symm F x y = F (single x y) :=
rfl

@[simp] lemma lift_add_hom_single_add_hom [add_comm_monoid M] :
  lift_add_hom (single_add_hom : α → M →+ α →₀ M) = add_monoid_hom.id _ :=
lift_add_hom.to_equiv.apply_eq_iff_eq_symm_apply.2 rfl

@[simp] lemma sum_single [add_comm_monoid M] (f : α →₀ M) :
  f.sum single = f :=
add_monoid_hom.congr_fun lift_add_hom_single_add_hom f

@[simp] lemma sum_univ_single [add_comm_monoid M] [fintype α] (i : α) (m : M) :
  ∑ (j : α), (single i m) j = m :=
by simp [single]

@[simp] lemma sum_univ_single' [add_comm_monoid M] [fintype α] (i : α) (m : M) :
  ∑ (j : α), (single j m) i = m :=
by simp [single]

@[simp] lemma lift_add_hom_apply_single [add_comm_monoid M] [add_comm_monoid N]
  (f : α → M →+ N) (a : α) (b : M) :
  lift_add_hom f (single a b) = f a b :=
sum_single_index (f a).map_zero

@[simp] lemma lift_add_hom_comp_single [add_comm_monoid M] [add_comm_monoid N] (f : α → M →+ N)
  (a : α) :
  (lift_add_hom f).comp (single_add_hom a) = f a :=
add_monoid_hom.ext $ λ b, lift_add_hom_apply_single f a b

lemma comp_lift_add_hom [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P]
  (g : N →+ P) (f : α → M →+ N) :
  g.comp (lift_add_hom f) = lift_add_hom (λ a, g.comp (f a)) :=
lift_add_hom.symm_apply_eq.1 $ funext $ λ a,
  by rw [lift_add_hom_symm_apply, add_monoid_hom.comp_assoc, lift_add_hom_comp_single]

lemma sum_sub_index [add_comm_group β] [add_comm_group γ] {f g : α →₀ β}
  {h : α → β → γ} (h_sub : ∀a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) :
  (f - g).sum h = f.sum h - g.sum h :=
(lift_add_hom (λ a, add_monoid_hom.of_map_sub (h a) (h_sub a))).map_sub f g

@[to_additive]
lemma prod_emb_domain [has_zero M] [comm_monoid N] {v : α →₀ M} {f : α ↪ β} {g : β → M → N} :
  (v.emb_domain f).prod g = v.prod (λ a b, g (f a) b) :=
begin
  rw [prod, prod, support_emb_domain, finset.prod_map],
  simp_rw emb_domain_apply,
end

@[to_additive]
lemma prod_finset_sum_index [add_comm_monoid M] [comm_monoid N]
  {s : finset ι} {g : ι → α →₀ M}
  {h : α → M → N} (h_zero : ∀a, h a 0 = 1) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
  ∏ i in s, (g i).prod h = (∑ i in s, g i).prod h :=
finset.cons_induction_on s rfl $ λ a s has ih,
by rw [prod_cons, ih, sum_cons, prod_add_index' h_zero h_add]

@[to_additive]
lemma prod_sum_index
  [add_comm_monoid M] [add_comm_monoid N] [comm_monoid P]
  {f : α →₀ M} {g : α → M → β →₀ N}
  {h : β → N → P} (h_zero : ∀a, h a 0 = 1) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
  (f.sum g).prod h = f.prod (λa b, (g a b).prod h) :=
(prod_finset_sum_index h_zero h_add).symm

lemma multiset_sum_sum_index
  [add_comm_monoid M] [add_comm_monoid N]
  (f : multiset (α →₀ M)) (h : α → M → N)
  (h₀ : ∀a, h a 0 = 0) (h₁ : ∀ (a : α) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂) :
  (f.sum.sum h) = (f.map $ λg:α →₀ M, g.sum h).sum :=
multiset.induction_on f rfl $ assume a s ih,
by rw [multiset.sum_cons, multiset.map_cons, multiset.sum_cons, sum_add_index' h₀ h₁, ih]

lemma support_sum_eq_bUnion {α : Type*} {ι : Type*} {M : Type*} [decidable_eq α]
  [add_comm_monoid M]
  {g : ι → α →₀ M} (s : finset ι) (h : ∀ i₁ i₂, i₁ ≠ i₂ → disjoint (g i₁).support (g i₂).support) :
  (∑ i in s, g i).support = s.bUnion (λ i, (g i).support) :=
begin
  classical,
  apply finset.induction_on s,
  { simp },
  { intros i s hi,
    simp only [hi, sum_insert, not_false_iff, bUnion_insert],
    intro hs,
    rw [finsupp.support_add_eq, hs],
    rw [hs, finset.disjoint_bUnion_right],
    intros j hj,
    refine h _ _ (ne_of_mem_of_not_mem hj hi).symm }
end

lemma multiset_map_sum [has_zero M] {f : α →₀ M} {m : β → γ} {h : α → M → multiset β} :
  multiset.map m (f.sum h) = f.sum (λa b, (h a b).map m) :=
(multiset.map_add_monoid_hom m).map_sum _ f.support

lemma multiset_sum_sum [has_zero M] [add_comm_monoid N] {f : α →₀ M} {h : α → M → multiset N} :
  multiset.sum (f.sum h) = f.sum (λa b, multiset.sum (h a b)) :=
(multiset.sum_add_monoid_hom : multiset N →+ N).map_sum _ f.support


/-- For disjoint `f1` and `f2`, and function `g`, the product of the products of `g`
over `f1` and `f2` equals the product of `g` over `f1 + f2` -/
@[to_additive "For disjoint `f1` and `f2`, and function `g`, the sum of the sums of `g`
over `f1` and `f2` equals the sum of `g` over `f1 + f2`"]
lemma prod_add_index_of_disjoint [add_comm_monoid M] {f1 f2 : α →₀ M}
  (hd : disjoint f1.support f2.support) {β : Type*} [comm_monoid β] (g : α → M → β) :
  (f1 + f2).prod g = f1.prod g * f2.prod g :=
have ∀ {f1 f2 : α →₀ M}, disjoint f1.support f2.support →
  ∏ x in f1.support, g x (f1 x + f2 x) = f1.prod g :=
  λ f1 f2 hd, finset.prod_congr rfl (λ x hx,
    by simp only [not_mem_support_iff.mp (disjoint_left.mp hd hx), add_zero]),
begin
  classical,
  simp_rw [← this hd, ← this hd.symm,
    add_comm (f2 _), finsupp.prod, support_add_eq hd, prod_union hd, add_apply]
end

lemma prod_dvd_prod_of_subset_of_dvd [add_comm_monoid M] [comm_monoid N]
  {f1 f2 : α →₀ M} {g1 g2 : α → M → N} (h1 : f1.support ⊆ f2.support)
  (h2 : ∀ (a : α), a ∈ f1.support → g1 a (f1 a) ∣ g2 a (f2 a)) :
  f1.prod g1 ∣ f2.prod g2 :=
begin
  classical,
  simp only [finsupp.prod, finsupp.prod_mul],
  rw [←sdiff_union_of_subset h1, prod_union sdiff_disjoint],
  apply dvd_mul_of_dvd_right,
  apply prod_dvd_prod_of_dvd,
  exact h2,
end

lemma indicator_eq_sum_single [add_comm_monoid M] (s : finset α) (f : Π a ∈ s, M) :
  indicator s f = ∑ x in s.attach, single x (f x x.2) :=
begin
  rw [← sum_single (indicator s f), sum, sum_subset (support_indicator_subset _ _), ← sum_attach],
  { refine finset.sum_congr rfl (λ x hx, _),
    rw [indicator_of_mem], },
  intros i _ hi,
  rw [not_mem_support_iff.mp hi, single_zero],
end

@[simp, to_additive]
lemma prod_indicator_index [has_zero M] [comm_monoid N]
  {s : finset α} (f : Π a ∈ s, M) {h : α → M → N} (h_zero : ∀ a ∈ s, h a 0 = 1) :
  (indicator s f).prod h = ∏ x in s.attach, h x (f x x.2) :=
begin
  rw [prod_of_support_subset _ (support_indicator_subset _ _) h h_zero, ← prod_attach],
  refine finset.prod_congr rfl (λ x hx, _),
  rw [indicator_of_mem],
end

end finsupp


theorem finset.sum_apply' : (∑ k in s, f k) i = ∑ k in s, f k i :=
(finsupp.apply_add_hom i : (ι →₀ A) →+ A).map_sum f s

theorem finsupp.sum_apply' : g.sum k x = g.sum (λ i b, k i b x) :=
finset.sum_apply _ _ _

section
include h0 h1

open_locale classical

theorem finsupp.sum_sum_index' : (∑ x in s, f x).sum t = ∑ x in s, (f x).sum t :=
finset.induction_on s rfl $ λ a s has ih,
by simp_rw [finset.sum_insert has, finsupp.sum_add_index' h0 h1, ih]

end

section
variables [non_unital_non_assoc_semiring R] [non_unital_non_assoc_semiring S]

lemma finsupp.sum_mul (b : S) (s : α →₀ R) {f : α → R → S} :
  (s.sum f) * b = s.sum (λ a c, (f a c) * b) :=
by simp only [finsupp.sum, finset.sum_mul]

lemma finsupp.mul_sum (b : S) (s : α →₀ R) {f : α → R → S} :
  b * (s.sum f) = s.sum (λ a c, b * (f a c)) :=
by simp only [finsupp.sum, finset.mul_sum]

end

namespace nat

/-- If `0 : ℕ` is not in the support of `f : ℕ →₀ ℕ` then `0 < ∏ x in f.support, x ^ (f x)`. -/
lemma prod_pow_pos_of_zero_not_mem_support {f : ℕ →₀ ℕ} (hf : 0 ∉ f.support) : 0 < f.prod pow :=
finset.prod_pos (λ a ha, pos_iff_ne_zero.mpr (pow_ne_zero _ (λ H, by {subst H, exact hf ha})))

end nat
