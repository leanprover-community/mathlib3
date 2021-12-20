/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.big_operators.basic
import algebra.group.pi
import algebra.group.prod
import algebra.module.pi
import order.conditionally_complete_lattice

/-!
# Support of a function

In this file we define `function.support f = {x | f x ≠ 0}` and prove its basic properties.
We also define `function.mul_support f = {x | f x ≠ 1}`.
-/

open set
open_locale big_operators
namespace function

variables {α β A B R S M₀ : Type*} {M N P G G₀ : α → Type*} {ι : Sort*}

section has_one

/-- `support` of a function is the set of points `x` such that `f x ≠ 0`. -/
def support [Π a, has_zero (M a)] (f : Π a, M a) : set α := {x | f x ≠ 0}

variables [has_one A] [has_one B] [Π a, has_one (M a)] [Π a, has_one (N a)] [Π a, has_one (P a)]

/-- `mul_support` of a function is the set of points `x` such that `f x ≠ 1`. -/
@[to_additive] def mul_support (f : Π a, M a) : set α := {x | f x ≠ 1}

@[to_additive] lemma mul_support_eq_preimage (f : α → A) : mul_support f = f ⁻¹' {1}ᶜ := rfl

@[to_additive] lemma nmem_mul_support {f : Π a, M a} {x : α} : x ∉ mul_support f ↔ f x = 1 :=
not_not

@[to_additive] lemma compl_mul_support {f : Π a, M a} : (mul_support f)ᶜ = {x | f x = 1} :=
ext $ λ x, nmem_mul_support

@[simp, to_additive] lemma mem_mul_support {f : Π a, M a} {x : α} :
  x ∈ mul_support f ↔ f x ≠ 1 :=
iff.rfl

@[simp, to_additive] lemma mul_support_subset_iff {f : Π a, M a} {s : set α} :
  mul_support f ⊆ s ↔ ∀ x, f x ≠ 1 → x ∈ s :=
iff.rfl

@[to_additive] lemma mul_support_subset_iff' {f : Π a, M a} {s : set α} :
  mul_support f ⊆ s ↔ ∀ x ∉ s, f x = 1 :=
forall_congr $ λ x, not_imp_comm

@[simp, to_additive] lemma mul_support_eq_empty_iff {f : Π a, M a} :
  mul_support f = ∅ ↔ f = 1 :=
by { simp_rw [← subset_empty_iff, mul_support_subset_iff', funext_iff], simp }

@[simp, to_additive] lemma mul_support_one' : mul_support (1 : Π a, M a) = ∅ :=
mul_support_eq_empty_iff.2 rfl

@[simp, to_additive] lemma mul_support_one : mul_support (λ x : α, (1 : M x)) = ∅ :=
mul_support_one'

@[to_additive] lemma mul_support_const {c : A} (hc : c ≠ 1) : mul_support (λ x : α, c) = set.univ :=
by { ext x, simp [hc] }

@[to_additive] lemma mul_support_binop_subset (op : Π a, M a → N a → P a) (op1 : ∀ a, op a 1 1 = 1)
  (f : Π a, M a) (g : Π a, N a) :
  mul_support (λ x, op x (f x) (g x)) ⊆ mul_support f ∪ mul_support g :=
λ x hx, classical.by_cases
  (λ hf : f x = 1, or.inr $ λ hg, hx $ by simp only [hf, hg, op1])
  or.inl

@[to_additive] lemma mul_support_sup [Π a, semilattice_sup (M a)] (f g : Π a, M a) :
  mul_support (λ x, f x ⊔ g x) ⊆ mul_support f ∪ mul_support g :=
mul_support_binop_subset (λ a, (⊔) : Π a, M a → M a → M a) (λ _, sup_idem) f g

@[to_additive] lemma mul_support_inf [Π a, semilattice_inf (M a)] (f g : Π a, M a) :
  mul_support (λ x, f x ⊓ g x) ⊆ mul_support f ∪ mul_support g :=
mul_support_binop_subset (λ a, (⊓) : Π a, M a → M a → M a) (λ _, inf_idem) f g

@[to_additive] lemma mul_support_max [Π a, linear_order (M a)] (f g : Π a, M a) :
  mul_support (λ x, max (f x) (g x)) ⊆ mul_support f ∪ mul_support g :=
mul_support_sup f g

@[to_additive] lemma mul_support_min [Π a, linear_order (M a)] (f g : Π a, M a) :
  mul_support (λ x, min (f x) (g x)) ⊆ mul_support f ∪ mul_support g :=
mul_support_inf f g

@[to_additive] lemma mul_support_supr [Π a, conditionally_complete_lattice (M a)] [nonempty ι]
  (f : ι → Π a, M a) :
  mul_support (λ x, ⨆ i, f i x) ⊆ ⋃ i, mul_support (f i) :=
begin
  rw mul_support_subset_iff',
  simp only [mem_Union, not_exists, nmem_mul_support],
  intros x hx,
  simp only [hx, csupr_const]
end

@[to_additive] lemma mul_support_infi [Π a, conditionally_complete_lattice (M a)] [nonempty ι]
  (f : ι → Π a, M a) :
  mul_support (λ x, ⨅ i, f i x) ⊆ ⋃ i, mul_support (f i) :=
@mul_support_supr _ (λ a, order_dual (M a)) ι _ _ _ f

@[to_additive] lemma mul_support_comp_subset {g : A → B} (hg : g 1 = 1) (f : α → A) :
  mul_support (g ∘ f) ⊆ mul_support f :=
λ x, mt $ λ h, by simp only [(∘), *]

@[to_additive] lemma mul_support_subset_comp {g : A → B} (hg : ∀ {x}, g x = 1 → x = 1)
  (f : α → A) :
  mul_support f ⊆ mul_support (g ∘ f) :=
λ x, mt hg

@[to_additive] lemma mul_support_comp_eq (g : A → B) (hg : ∀ {x}, g x = 1 ↔ x = 1)
  (f : α → A) :
  mul_support (g ∘ f) = mul_support f :=
set.ext $ λ x, not_congr hg

@[to_additive] lemma mul_support_comp_eq_preimage (g : β → A) (f : α → β) :
  mul_support (g ∘ f) = f ⁻¹' mul_support g :=
rfl

@[to_additive support_prod_mk] lemma mul_support_prod_mk (f : Π a, M a) (g : Π a, N a) :
  mul_support (λ x, (f x, g x) : Π a, M a × N a) = mul_support f ∪ mul_support g :=
set.ext $ λ x, by simp only [mul_support, not_and_distrib, mem_union_eq, mem_set_of_eq,
  prod.mk_eq_one, ne.def]

@[to_additive support_prod_mk'] lemma mul_support_prod_mk' (f : Π a, M a × N a) :
  mul_support f = mul_support (λ x, (f x).1) ∪ mul_support (λ x, (f x).2) :=
by simp only [← mul_support_prod_mk, prod.mk.eta]

@[to_additive] lemma mul_support_along_fiber_subset {M : α × β → Type*} [Π a, has_one (M a)]
  (f : Π a, M a) (a : α) :
  mul_support (λ b, f (a, b)) ⊆ (mul_support f).image prod.snd :=
by tidy

@[simp, to_additive] lemma mul_support_along_fiber_finite_of_finite {M : α × β → Type*}
  [Π a, has_one (M a)] (f : Π a, M a) (a : α) (h : (mul_support f).finite) :
  (mul_support (λ b, f (a, b))).finite :=
(h.image prod.snd).subset (mul_support_along_fiber_subset f a)

end has_one

@[to_additive] lemma mul_support_mul [Π a, monoid (M a)] (f g : Π a, M a) :
  mul_support (λ x, f x * g x) ⊆ mul_support f ∪ mul_support g :=
mul_support_binop_subset (λ a, (*) : Π a, M a → M a → M a) (λ _, one_mul _) f g

@[simp, to_additive] lemma mul_support_inv [Π a, group (G a)] (f : Π a, G a) :
  mul_support (λ x, (f x)⁻¹) = mul_support f :=
set.ext $ λ x, not_congr inv_eq_one

@[simp, to_additive] lemma mul_support_inv' [Π a, group (G a)] (f : Π a, G a) :
  mul_support (f⁻¹) = mul_support f :=
mul_support_inv f

@[simp] lemma mul_support_inv₀ [Π a, group_with_zero (G₀ a)] (f : Π a, G₀ a) :
  mul_support (λ x, (f x)⁻¹) = mul_support f :=
set.ext $ λ x, not_congr inv_eq_one₀

@[to_additive] lemma mul_support_mul_inv [Π a, group (G a)] (f g : Π a, G a) :
  mul_support (λ x, f x * (g x)⁻¹) ⊆ mul_support f ∪ mul_support g :=
mul_support_binop_subset (λ _ a b, a * b⁻¹) (by simp) f g

@[to_additive support_sub] lemma mul_support_group_div [Π a, group (G a)] (f g : Π a, G a) :
  mul_support (λ x, f x / g x) ⊆ mul_support f ∪ mul_support g :=
mul_support_binop_subset (λ _, (/) : Π a, G a → G a → G a) (λ _, div_one' _) f g

lemma mul_support_div [Π a, group_with_zero (G₀ a)] (f g : Π a, G₀ a) :
  mul_support (λ x, f x / g x) ⊆ mul_support f ∪ mul_support g :=
mul_support_binop_subset (λ _, (/) : Π a, G₀ a → G₀ a → G₀ a) (λ _, div_one _) f g

@[simp] lemma support_mul [Π a, mul_zero_class (M a)] [Π a, no_zero_divisors (M a)]
  (f g : Π a, M a) :
  support (λ x, f x * g x) = support f ∩ support g :=
set.ext $ λ x, by simp only [mem_support, mul_ne_zero_iff, mem_inter_eq, not_or_distrib]

lemma support_smul_subset_right [Π a, add_monoid (M a)] [monoid A] [Π a, distrib_mul_action A (M a)]
  (b : A) (f : Π a, M a) :
  support (b • f) ⊆ support f :=
λ x hbf hf, hbf $ by rw [pi.smul_apply, hf, smul_zero]

lemma support_smul_subset_left [semiring R] [Π a, add_comm_monoid (M a)] [Π a, module R (M a)]
  (f : α → R) (g : Π a, M a) :
  support (f • g) ⊆ support f :=
λ x hfg hf, hfg $ by rw [pi.smul_apply', hf, zero_smul]

lemma support_smul [semiring R] [Π a, add_comm_monoid (M a)] [Π a, module R (M a)]
  [Π a, no_zero_smul_divisors R (M a)] (f : α → R) (g : Π a, M a) :
  support (f • g) = support f ∩ support g :=
ext $ λ x, smul_ne_zero

@[simp] lemma support_inv [Π a, group_with_zero (G₀ a)] (f : Π a, G₀ a) :
  support (λ x, (f x)⁻¹) = support f :=
set.ext $ λ x, not_congr inv_eq_zero

@[simp] lemma support_div [Π a, group_with_zero (G₀ a)] (f g : Π a, G₀ a) :
  support (λ x, f x / g x) = support f ∩ support g :=
by { ext, simp [not_or_distrib, div_eq_mul_inv] }

@[to_additive] lemma mul_support_prod [comm_monoid A] (s : finset α) (f : α → β → A) :
  mul_support (λ x, ∏ i in s, f i x) ⊆ ⋃ i ∈ s, mul_support (f i) :=
begin
  rw mul_support_subset_iff',
  simp only [mem_Union, not_exists, nmem_mul_support],
  exact λ x, finset.prod_eq_one
end

lemma support_prod_subset [comm_monoid_with_zero A] (s : finset α) (f : α → β → A) :
  support (λ x, ∏ i in s, f i x) ⊆ ⋂ i ∈ s, support (f i) :=
λ x hx, mem_bInter_iff.2 $ λ i hi H, hx $ finset.prod_eq_zero hi H

lemma support_prod [comm_monoid_with_zero A] [no_zero_divisors A] [nontrivial A]
  (s : finset α) (f : α → β → A) :
  support (λ x, ∏ i in s, f i x) = ⋂ i ∈ s, support (f i) :=
set.ext $ λ x, by
  simp only [support, ne.def, finset.prod_eq_zero_iff, mem_set_of_eq, set.mem_Inter, not_exists]

lemma mul_support_one_add [has_one R] [add_left_cancel_monoid R] (f : α → R) :
  mul_support (λ x, 1 + f x) = support f :=
set.ext $ λ x, not_congr add_right_eq_self

lemma mul_support_one_add' [has_one R] [add_left_cancel_monoid R] (f : α → R) :
  mul_support (1 + f) = support f :=
mul_support_one_add f

lemma mul_support_add_one [has_one R] [add_right_cancel_monoid R] (f : α → R) :
  mul_support (λ x, f x + 1) = support f :=
set.ext $ λ x, not_congr add_left_eq_self

lemma mul_support_add_one' [has_one R] [add_right_cancel_monoid R] (f : α → R) :
  mul_support (f + 1) = support f :=
mul_support_add_one f

lemma mul_support_one_sub' [has_one R] [add_group R] (f : α → R) :
  mul_support (1 - f) = support f :=
by rw [sub_eq_add_neg, mul_support_one_add', support_neg']

lemma mul_support_one_sub [has_one R] [add_group R] (f : α → R) :
  mul_support (λ x, 1 - f x) = support f :=
mul_support_one_sub' f

end function

namespace set

open function

variables {α β M : Type*} [has_one M] {f : α → M}

@[to_additive] lemma image_inter_mul_support_eq {s : set β} {g : β → α} :
  (g '' s ∩ mul_support f) = g '' (s ∩ mul_support (f ∘ g)) :=
by rw [mul_support_comp_eq_preimage f g, image_inter_preimage]

end set

namespace pi
variables {A : Type*} {B : A → Type*} [decidable_eq A] [Π a, has_zero (B a)] {a : A} {b : B a}

lemma support_single_zero : function.support (pi.single a (0 : B a)) = ∅ := by simp

@[simp] lemma support_single_of_ne (h : b ≠ 0) :
  function.support (pi.single a b) = {a} :=
begin
  ext,
  simp only [mem_singleton_iff, ne.def, function.mem_support],
  split,
  { contrapose!,
    exact λ h', single_eq_of_ne h' b },
  { rintro rfl,
    rw single_eq_same,
    exact h }
end

lemma support_single [Π a, decidable_eq (B a)] :
  function.support (pi.single a b) = if b = 0 then ∅ else {a} := by { split_ifs with h; simp [h] }

lemma support_single_subset : function.support (pi.single a b) ⊆ {a} :=
begin
  classical,
  rw support_single,
  split_ifs; simp
end

lemma support_single_disjoint {i j : A} {b : B i} {b' : B j} (hb : b ≠ 0) (hb' : b' ≠ 0) :
  disjoint (function.support (single i b)) (function.support (single j b')) ↔ i ≠ j :=
by rw [support_single_of_ne hb, support_single_of_ne hb', disjoint_singleton]

end pi
