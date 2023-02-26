/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import order.conditionally_complete_lattice.basic
import data.set.finite
import algebra.big_operators.basic
import algebra.group.prod
import algebra.group.pi
import algebra.module.basic
import group_theory.group_action.pi

/-!
# Support of a function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `function.support f = {x | f x ≠ 0}` and prove its basic properties.
We also define `function.mul_support f = {x | f x ≠ 1}`.
-/

open set
open_locale big_operators
namespace function

variables {α β A B M N P R S G M₀ G₀ : Type*} {ι : Sort*}

section has_one

variables [has_one M] [has_one N] [has_one P]

/-- `support` of a function is the set of points `x` such that `f x ≠ 0`. -/
def support [has_zero A] (f : α → A) : set α := {x | f x ≠ 0}

/-- `mul_support` of a function is the set of points `x` such that `f x ≠ 1`. -/
@[to_additive] def mul_support (f : α → M) : set α := {x | f x ≠ 1}

@[to_additive] lemma mul_support_eq_preimage (f : α → M) : mul_support f = f ⁻¹' {1}ᶜ := rfl

@[to_additive] lemma nmem_mul_support {f : α → M} {x : α} :
  x ∉ mul_support f ↔ f x = 1 :=
not_not

@[to_additive] lemma compl_mul_support {f : α → M} :
  (mul_support f)ᶜ = {x | f x = 1} :=
ext $ λ x, nmem_mul_support

@[simp, to_additive] lemma mem_mul_support {f : α → M} {x : α} :
  x ∈ mul_support f ↔ f x ≠ 1 :=
iff.rfl

@[simp, to_additive] lemma mul_support_subset_iff {f : α → M} {s : set α} :
  mul_support f ⊆ s ↔ ∀ x, f x ≠ 1 → x ∈ s :=
iff.rfl

@[to_additive] lemma mul_support_subset_iff' {f : α → M} {s : set α} :
  mul_support f ⊆ s ↔ ∀ x ∉ s, f x = 1 :=
forall_congr $ λ x, not_imp_comm

@[to_additive] lemma mul_support_eq_iff {f : α → M} {s : set α} :
  mul_support f = s ↔ ((∀ x, x ∈ s → f x ≠ 1) ∧ (∀ x, x ∉ s → f x = 1)) :=
by simp only [set.ext_iff, mem_mul_support, ne.def, imp_not_comm, ← forall_and_distrib,
  ← iff_def, ← xor_iff_not_iff', ← xor_iff_iff_not]

@[to_additive] lemma mul_support_disjoint_iff {f : α → M} {s : set α} :
  disjoint (mul_support f) s ↔ eq_on f 1 s :=
by simp_rw [←subset_compl_iff_disjoint_right, mul_support_subset_iff', not_mem_compl_iff, eq_on,
  pi.one_apply]

@[to_additive] lemma disjoint_mul_support_iff {f : α → M} {s : set α} :
  disjoint s (mul_support f) ↔ eq_on f 1 s :=
by rw [disjoint.comm, mul_support_disjoint_iff]

@[simp, to_additive] lemma mul_support_eq_empty_iff {f : α → M} :
  mul_support f = ∅ ↔ f = 1 :=
by { simp_rw [← subset_empty_iff, mul_support_subset_iff', funext_iff], simp }

@[simp, to_additive] lemma mul_support_nonempty_iff {f : α → M} :
  (mul_support f).nonempty ↔ f ≠ 1 :=
by rw [nonempty_iff_ne_empty, ne.def, mul_support_eq_empty_iff]

@[to_additive]
lemma range_subset_insert_image_mul_support (f : α → M) :
  range f ⊆ insert 1 (f '' mul_support f) :=
by simpa only [range_subset_iff, mem_insert_iff, or_iff_not_imp_left]
  using λ x (hx : x ∈ mul_support f), mem_image_of_mem f hx

@[simp, to_additive] lemma mul_support_one' : mul_support (1 : α → M) = ∅ :=
mul_support_eq_empty_iff.2 rfl

@[simp, to_additive] lemma mul_support_one : mul_support (λ x : α, (1 : M)) = ∅ :=
mul_support_one'

@[to_additive] lemma mul_support_const {c : M} (hc : c ≠ 1) :
  mul_support (λ x : α, c) = set.univ :=
by { ext x, simp [hc] }

@[to_additive] lemma mul_support_binop_subset (op : M → N → P) (op1 : op 1 1 = 1)
  (f : α → M) (g : α → N) :
  mul_support (λ x, op (f x) (g x)) ⊆ mul_support f ∪ mul_support g :=
λ x hx, not_or_of_imp (λ hf hg, hx $ by simp only [hf, hg, op1])

@[to_additive] lemma mul_support_sup [semilattice_sup M] (f g : α → M) :
  mul_support (λ x, f x ⊔ g x) ⊆ mul_support f ∪ mul_support g :=
mul_support_binop_subset (⊔) sup_idem f g

@[to_additive] lemma mul_support_inf [semilattice_inf M] (f g : α → M) :
  mul_support (λ x, f x ⊓ g x) ⊆ mul_support f ∪ mul_support g :=
mul_support_binop_subset (⊓) inf_idem f g

@[to_additive] lemma mul_support_max [linear_order M] (f g : α → M) :
  mul_support (λ x, max (f x) (g x)) ⊆ mul_support f ∪ mul_support g :=
mul_support_sup f g

@[to_additive] lemma mul_support_min [linear_order M] (f g : α → M) :
  mul_support (λ x, min (f x) (g x)) ⊆ mul_support f ∪ mul_support g :=
mul_support_inf f g

@[to_additive] lemma mul_support_supr [conditionally_complete_lattice M] [nonempty ι]
  (f : ι → α → M) :
  mul_support (λ x, ⨆ i, f i x) ⊆ ⋃ i, mul_support (f i) :=
begin
  rw mul_support_subset_iff',
  simp only [mem_Union, not_exists, nmem_mul_support],
  intros x hx,
  simp only [hx, csupr_const]
end

@[to_additive] lemma mul_support_infi [conditionally_complete_lattice M] [nonempty ι]
  (f : ι → α → M) :
  mul_support (λ x, ⨅ i, f i x) ⊆ ⋃ i, mul_support (f i) :=
@mul_support_supr _ Mᵒᵈ ι ⟨(1:M)⟩ _ _ f

@[to_additive] lemma mul_support_comp_subset {g : M → N} (hg : g 1 = 1) (f : α → M) :
  mul_support (g ∘ f) ⊆ mul_support f :=
λ x, mt $ λ h, by simp only [(∘), *]

@[to_additive] lemma mul_support_subset_comp {g : M → N} (hg : ∀ {x}, g x = 1 → x = 1)
  (f : α → M) :
  mul_support f ⊆ mul_support (g ∘ f) :=
λ x, mt hg

@[to_additive] lemma mul_support_comp_eq (g : M → N) (hg : ∀ {x}, g x = 1 ↔ x = 1)
  (f : α → M) :
  mul_support (g ∘ f) = mul_support f :=
set.ext $ λ x, not_congr hg

@[to_additive] lemma mul_support_comp_eq_preimage (g : β → M) (f : α → β) :
  mul_support (g ∘ f) = f ⁻¹' mul_support g :=
rfl

@[to_additive support_prod_mk] lemma mul_support_prod_mk (f : α → M) (g : α → N) :
  mul_support (λ x, (f x, g x)) = mul_support f ∪ mul_support g :=
set.ext $ λ x, by simp only [mul_support, not_and_distrib, mem_union, mem_set_of_eq,
  prod.mk_eq_one, ne.def]

@[to_additive support_prod_mk'] lemma mul_support_prod_mk' (f : α → M × N) :
  mul_support f = mul_support (λ x, (f x).1) ∪ mul_support (λ x, (f x).2) :=
by simp only [← mul_support_prod_mk, prod.mk.eta]

@[to_additive] lemma mul_support_along_fiber_subset (f : α × β → M) (a : α) :
  mul_support (λ b, f (a, b)) ⊆ (mul_support f).image prod.snd :=
by tidy

@[simp, to_additive] lemma mul_support_along_fiber_finite_of_finite
  (f : α × β → M) (a : α) (h : (mul_support f).finite) :
  (mul_support (λ b, f (a, b))).finite :=
(h.image prod.snd).subset (mul_support_along_fiber_subset f a)

end has_one

@[to_additive] lemma mul_support_mul [mul_one_class M] (f g : α → M) :
  mul_support (λ x, f x * g x) ⊆ mul_support f ∪ mul_support g :=
mul_support_binop_subset (*) (one_mul _) f g

@[to_additive] lemma mul_support_pow [monoid M] (f : α → M) (n : ℕ) :
  mul_support (λ x, f x ^ n) ⊆ mul_support f :=
begin
  induction n with n hfn,
  { simpa only [pow_zero, mul_support_one] using empty_subset _ },
  { simpa only [pow_succ] using (mul_support_mul f _).trans (union_subset subset.rfl hfn) }
end

section division_monoid
variables [division_monoid G] (f g : α → G)

@[simp, to_additive]
lemma mul_support_inv : mul_support (λ x, (f x)⁻¹) = mul_support f := ext $ λ _, inv_ne_one

@[simp, to_additive] lemma mul_support_inv' : mul_support f⁻¹ = mul_support f := mul_support_inv f

@[to_additive] lemma mul_support_mul_inv :
  mul_support (λ x, f x * (g x)⁻¹) ⊆ mul_support f ∪ mul_support g :=
mul_support_binop_subset (λ a b, a * b⁻¹) (by simp) f g

@[to_additive] lemma mul_support_div :
  mul_support (λ x, f x / g x) ⊆ mul_support f ∪ mul_support g :=
mul_support_binop_subset (/) one_div_one f g

end division_monoid

lemma support_smul [has_zero R] [has_zero M] [smul_with_zero R M] [no_zero_smul_divisors R M]
  (f : α → R) (g : α → M) :
  support (f • g) = support f ∩ support g :=
ext $ λ x, smul_ne_zero_iff

@[simp] lemma support_mul [mul_zero_class R] [no_zero_divisors R] (f g : α → R) :
  support (λ x, f x * g x) = support f ∩ support g :=
support_smul f g

@[simp] lemma support_mul_subset_left [mul_zero_class R] (f g : α → R) :
  support (λ x, f x * g x) ⊆ support f :=
λ x hfg hf, hfg $ by simp only [hf, zero_mul]

@[simp] lemma support_mul_subset_right [mul_zero_class R] (f g : α → R) :
  support (λ x, f x * g x) ⊆ support g :=
λ x hfg hg, hfg $ by simp only [hg, mul_zero]

lemma support_smul_subset_right [add_monoid A] [monoid B] [distrib_mul_action B A]
  (b : B) (f : α → A) :
  support (b • f) ⊆ support f :=
λ x hbf hf, hbf $ by rw [pi.smul_apply, hf, smul_zero]

lemma support_smul_subset_left [has_zero M] [has_zero β] [smul_with_zero M β]
  (f : α → M) (g : α → β) :
  support (f • g) ⊆ support f :=
λ x hfg hf, hfg $ by rw [pi.smul_apply', hf, zero_smul]

lemma support_const_smul_of_ne_zero [semiring R] [add_comm_monoid M] [module R M]
  [no_zero_smul_divisors R M] (c : R) (g : α → M) (hc : c ≠ 0) :
  support (c • g) = support g :=
ext $ λ x, by simp only [hc, mem_support, pi.smul_apply, ne.def, smul_eq_zero, false_or]

@[simp] lemma support_inv [group_with_zero G₀] (f : α → G₀) :
  support (λ x, (f x)⁻¹) = support f :=
set.ext $ λ x, not_congr inv_eq_zero

@[simp] lemma support_div [group_with_zero G₀] (f g : α → G₀) :
  support (λ x, f x / g x) = support f ∩ support g :=
by simp [div_eq_mul_inv]

@[to_additive] lemma mul_support_prod [comm_monoid M] (s : finset α) (f : α → β → M) :
  mul_support (λ x, ∏ i in s, f i x) ⊆ ⋃ i ∈ s, mul_support (f i) :=
begin
  rw mul_support_subset_iff',
  simp only [mem_Union, not_exists, nmem_mul_support],
  exact λ x, finset.prod_eq_one
end

lemma support_prod_subset [comm_monoid_with_zero A] (s : finset α) (f : α → β → A) :
  support (λ x, ∏ i in s, f i x) ⊆ ⋂ i ∈ s, support (f i) :=
λ x hx, mem_Inter₂.2 $ λ i hi H, hx $ finset.prod_eq_zero hi H

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
variables {A : Type*} {B : Type*} [decidable_eq A] [has_one B] {a : A} {b : B}

open function

@[to_additive] lemma mul_support_mul_single_subset : mul_support (mul_single a b) ⊆ {a} :=
λ x hx, by_contra $ λ hx', hx $ mul_single_eq_of_ne hx' _

@[to_additive] lemma mul_support_mul_single_one : mul_support (mul_single a (1 : B)) = ∅ :=
by simp

@[simp, to_additive] lemma mul_support_mul_single_of_ne (h : b ≠ 1) :
  mul_support (mul_single a b) = {a} :=
mul_support_mul_single_subset.antisymm $
  λ x (hx : x = a), by rwa [mem_mul_support, hx, mul_single_eq_same]

@[to_additive] lemma mul_support_mul_single [decidable_eq B] :
  mul_support (mul_single a b) = if b = 1 then ∅ else {a} := by { split_ifs with h; simp [h] }

@[to_additive]
lemma mul_support_mul_single_disjoint {b' : B} (hb : b ≠ 1) (hb' : b' ≠ 1) {i j : A} :
  disjoint (mul_support (mul_single i b)) (mul_support (mul_single j b')) ↔ i ≠ j :=
by rw [mul_support_mul_single_of_ne hb, mul_support_mul_single_of_ne hb', disjoint_singleton]

end pi
