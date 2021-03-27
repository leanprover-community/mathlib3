/-
Copyright (c) 2020 Kexing Ying and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Kevin Buzzard, Yury Kudryashov
-/

import data.set.finite
import data.set.disjointed
import algebra.big_operators
import data.indicator_function

/-!
# Finite products and sums over types and sets

We define products sums over types and subsets of types, with no finiteness hypotheses. All infinite
product and sums are defined to be junk values (i.e. one or zero). This approach is sometimes easier
to use than `finset.sum` when issues arise with `finset` and `fintype` being data.

## Main definitions

We use the following variables:

* `α`, `β` - types with no structure;
* `s`, `t` - sets
* `M`, `N` - additive or multiplicative commutative monoids
* `f`, `g` - functions

Definitions in this file:

* `finsum f : M` : the sum of `f x` as `x` ranges over the support of `f`, if it's finite.
   Zero otherwise.

* `finprod f : M` : the product of `f x` as `x` ranges over the multiplicative support of `f`, if
   it's finite. One otherwise.

## Notation

* `∑ᶠ i, f i` and `∑ᶠ i : α, f i` for `finsum f`

* `∑ᶠ i in s, f i` for `finsum_in s f`

* `∏ᶠ i, f i` and `∑ᶠ i : α, f i` for `finprod f`

* `∏ᶠ i in s, f i` for `finprod_in s f`

## Implementation notes

`finsum` and `finprod` is "yet another way of doing finite sums and products in Lean". However
experiments in the wild (e.g. with matroids) indicate that it is a helpful approach in settings
where the user is not interested in computability and wants to do reasoning without running into
typeclass diamonds caused by the constructive finiteness used in definitions such as `finset` and
`fintype`. By sticking solely to `set.finite` we avoid these problems. We are aware that there are
other solutions but for beginner mathematicians this approach is easier in practice.

Another application is the construction of a partition of unity from a collection of “bump”
function. In this case the finite set depends on the point and it's convenient to have a definition
that does not mention the set explicitly.

## Todo

We did not add `is_finite (X : Type) : Prop`, because it is simply `nonempty (fintype X)`.
There is work on `fincard` in the pipeline, which returns the cardinality of `X` if it
is finite, and 0 otherwise.

## Tags

finsum, finsum_in, finprod, finprod_in, finite sum, finite product
-/

open_locale classical
open function set

/-!
### Definition and relation to `finset.sum` and `finset.prod`
-/

section sort
variables {α β ι : Sort*} {M N : Type*} [comm_monoid M] [comm_monoid N]

open_locale big_operators

/-- Sum of `f x` as `x` ranges over the elements of the support of `f`, if it's finite. Zero
otherwise. -/
@[irreducible] noncomputable def finsum {M} [add_comm_monoid M] (f : α → M) : M :=
if h : finite (support (f ∘ plift.down)) then ∑ i in h.to_finset, f i.down else 0

/-- Product of `f x` as `x` ranges over the elements of the multiplicative support of `f`, if it's
finite. One otherwise. -/
@[irreducible, to_additive]
noncomputable def finprod (f : α → M) : M :=
if h : finite (mul_support (f ∘ plift.down)) then ∏ i in h.to_finset, f i.down else 1

localized "notation `∑ᶠ` binders `, ` r:(scoped:67 f, finsum f) := r" in big_operators

localized "notation `∏ᶠ` binders `, ` r:(scoped:67 f, finprod f) := r" in big_operators

@[to_additive] lemma finprod_eq_prod_plift_of_mul_support_to_finset_subset
  {f : α → M} (hf : finite (mul_support (f ∘ plift.down))) {s : finset (plift α)}
  (hs : hf.to_finset ⊆ s) :
  ∏ᶠ i, f i = ∏ i in s, f i.down :=
begin
  rw [finprod, dif_pos hf],
  refine finset.prod_subset hs (λ x hx hxf, _),
  rwa [hf.mem_to_finset, nmem_mul_support] at hxf
end

@[to_additive] lemma finprod_eq_prod_plift_of_mul_support_subset
  {f : α → M} {s : finset (plift α)} (hs : mul_support (f ∘ plift.down) ⊆ s) :
  ∏ᶠ i, f i = ∏ i in s, f i.down :=
finprod_eq_prod_plift_of_mul_support_to_finset_subset
  (s.finite_to_set.subset hs) $ λ x hx, by { rw finite.mem_to_finset at hx, exact hs hx }

@[simp, to_additive] lemma finprod_one : ∏ᶠ i : α, (1 : M) = 1 :=
begin
  have : mul_support (λ x : plift α, (λ _, 1 : α → M) x.down) ⊆ (∅ : finset (plift α)),
    from λ x h, h rfl,
  rw [finprod_eq_prod_plift_of_mul_support_subset this, finset.prod_empty]
end

@[to_additive] lemma finprod_of_empty (ha : α → false) (f : α → M) : ∏ᶠ i, f i = 1 :=
by { rw ← finprod_one, congr' with x, exact (ha x).elim }

@[simp, to_additive] lemma finprod_false (f : false → M) : ∏ᶠ i, f i = 1 :=
finprod_of_empty id _

@[to_additive] lemma finprod_unique [unique α] (f : α → M) : ∏ᶠ i, f i = f (default α) :=
begin
  have : mul_support (f ∘ plift.down) ⊆ (finset.univ : finset (plift α)),
    from λ x _, finset.mem_univ x,
  rw [finprod_eq_prod_plift_of_mul_support_subset this, univ_unique,
    finset.prod_singleton],
  exact congr_arg f (plift.down_up _)
end

@[to_additive] lemma finprod_true (f : true → M) : ∏ᶠ i, f i = f trivial :=
@finprod_unique true M _ ⟨⟨trivial⟩, λ _, rfl⟩ f

@[to_additive] lemma finprod_eq_dif {p : Prop} (f : p → M) :
  ∏ᶠ i, f i = if h : p then f h else 1 :=
begin
  split_ifs,
  { haveI : unique p := ⟨⟨h⟩, λ _, rfl⟩,
    exact finprod_unique f },
  { exact finprod_of_empty h f }
end

@[to_additive] lemma finprod_eq_if {p : Prop} {x : M} : ∏ᶠ i : p, x = if p then x else 1 :=
finprod_eq_dif (λ _, x)

@[to_additive] lemma finprod_congr {f g : α → M} (h : ∀ x, f x = g x) :
  finprod f = finprod g :=
congr_arg _ $ funext h

@[congr, to_additive] lemma finprod_congr_Prop {p q : Prop} {f : p → M} {g : q → M} (hpq : p = q)
  (hfg : ∀ h : q, f (hpq.mpr h) = g h) :
  finprod f = finprod g :=
by { subst q, exact finprod_congr hfg }

attribute [congr] finsum_congr_Prop

end sort

section type

variables {α β ι M N : Type*} [comm_monoid M] [comm_monoid N]

open_locale big_operators

@[to_additive] lemma finprod_eq_mul_indicator_apply (s : set α) (f : α → M) (a : α) :
  ∏ᶠ (h : a ∈ s), f a = mul_indicator s f a :=
finprod_eq_if

@[to_additive] lemma finprod_in_def (s : set α) (f : α → M) :
  ∏ᶠ a ∈ s, f a = ∏ᶠ a, mul_indicator s f a :=
finprod_congr $ finprod_eq_mul_indicator_apply s f

@[to_additive] lemma finprod_eq_prod_of_mul_support_subset (f : α → M) {s : finset α}
  (h : mul_support f ⊆ s) :
  ∏ᶠ i, f i = ∏ i in s, f i :=
begin
  have A : mul_support (f ∘ plift.down) = equiv.plift.symm '' mul_support f,
  { rw mul_support_comp_eq_preimage,
    exact (equiv.plift.symm.image_eq_preimage _).symm },
  have : mul_support (f ∘ plift.down) ⊆ s.map equiv.plift.symm.to_embedding,
  { rw [A, finset.coe_map], exact image_subset _ h },
  rw [finprod_eq_prod_plift_of_mul_support_subset this],
  simp
end

@[to_additive] lemma finprod_eq_prod_of_mul_support_to_finset_subset (f : α → M)
  (hf : finite (mul_support f)) {s : finset α} (h : hf.to_finset ⊆ s) :
  ∏ᶠ i, f i = ∏ i in s, f i :=
finprod_eq_prod_of_mul_support_subset _ $ λ x hx, h $ hf.mem_to_finset.2 hx

@[to_additive] lemma finprod_def (f : α → M) :
  ∏ᶠ i : α, f i = if h : (mul_support f).finite then ∏ i in h.to_finset, f i else 1 :=
begin
  split_ifs,
  { exact finprod_eq_prod_of_mul_support_to_finset_subset _ h (finset.subset.refl _) },
  { rw [finprod, dif_neg],
    rw [mul_support_comp_eq_preimage],
    exact mt (λ hf, hf.of_preimage equiv.plift.surjective) h}
end

@[to_additive] lemma finprod_of_infinite_mul_support {f : α → M} (hf : (mul_support f).infinite) :
  ∏ᶠ i, f i = 1 :=
by rw [finprod_def, dif_neg hf]

@[to_additive] lemma finprod_eq_prod (f : α → M) (hf : (mul_support f).finite) :
  ∏ᶠ i : α, f i = ∏ i in hf.to_finset, f i :=
by rw [finprod_def, dif_pos hf]

@[to_additive] lemma finprod_eq_prod_of_fintype [fintype α] (f : α → M) :
  ∏ᶠ i : α, f i = ∏ i, f i :=
finprod_eq_prod_of_mul_support_to_finset_subset _ (finite.of_fintype _) $ finset.subset_univ _

@[to_additive] lemma finprod_in_eq_prod_of_mem_iff (f : α → M) {s : set α} {t : finset α}
  (h : ∀ {x}, f x ≠ 1 → (x ∈ s ↔ x ∈ t)) :
  ∏ᶠ i ∈ s, f i = ∏ i in t, f i :=
begin
  have : mul_support (s.mul_indicator f) ⊆ t,
  { rw [set.mul_support_mul_indicator], intros x hx, exact (h hx.2).1 hx.1 },
  rw [finprod_in_def, finprod_eq_prod_of_mul_support_subset _ this],
  refine finset.prod_congr rfl (λ x hx, mul_indicator_apply_eq_self.2 $ λ hxs, _),
  contrapose! hxs,
  exact (h hxs).2 hx
end

@[to_additive] lemma finprod_in_eq_prod_of_inter_mul_support_eq (f : α → M) {s : set α}
  {t : finset α} (h : s ∩ mul_support f = t ∩ mul_support f) :
  ∏ᶠ i ∈ s, f i = ∏ i in t, f i :=
finprod_in_eq_prod_of_mem_iff _ $ by simpa [set.ext_iff] using h

@[to_additive] lemma finprod_in_eq_prod_of_subset (f : α → M) {s : set α} {t : finset α}
  (h₁ : s ∩ mul_support f ⊆ t) (h₂ : ↑t ⊆ s) :
  ∏ᶠ i ∈ s, f i = ∏ i in t, f i :=
finprod_in_eq_prod_of_mem_iff _ $ λ x hx, ⟨λ h, h₁ ⟨h, hx⟩, λ h, h₂ h⟩

@[to_additive] lemma finprod_in_eq_prod (f : α → M) {s : set α}
  (hf : (s ∩ mul_support f).finite) :
  ∏ᶠ i ∈ s, f i = ∏ i in hf.to_finset, f i :=
finprod_in_eq_prod_of_inter_mul_support_eq _ $ by simp [inter_assoc]

@[to_additive] lemma finprod_in_eq_prod_filter (f : α → M) (s : set α)
  (hf : (mul_support f).finite) :
  ∏ᶠ i ∈ s, f i = ∏ i in finset.filter (∈ s) hf.to_finset, f i :=
finprod_in_eq_prod_of_inter_mul_support_eq _ $ by simp [inter_comm, inter_left_comm]

@[to_additive] lemma finprod_in_eq_to_finset_prod (f : α → M) (s : set α) [fintype s] :
  ∏ᶠ i ∈ s, f i = ∏ i in s.to_finset, f i :=
finprod_in_eq_prod_of_inter_mul_support_eq _ $ by rw [coe_to_finset]

@[to_additive] lemma finprod_in_eq_finite_to_finset_prod (f : α → M) {s : set α} (hs : s.finite) :
  ∏ᶠ i ∈ s, f i = ∏ i in hs.to_finset, f i :=
finprod_in_eq_prod_of_inter_mul_support_eq _ $ by rw [hs.coe_to_finset]

@[to_additive] lemma finprod_in_finset_eq_prod (f : α → M) (s : finset α) :
  ∏ᶠ i ∈ s, f i = ∏ i in s, f i :=
finprod_in_eq_prod_of_inter_mul_support_eq _ rfl

@[to_additive] lemma finprod_in_coe_eq_prod (f : α → M) (s : finset α) :
  ∏ᶠ i ∈ (s : set α), f i = ∏ i in s, f i :=
finprod_in_eq_prod_of_inter_mul_support_eq _ rfl

@[to_additive] lemma finprod_in_eq_one_of_infinite {f : α → M} {s : set α}
  (hs : (s ∩ mul_support f).infinite) : ∏ᶠ i ∈ s, f i = 1 :=
begin
  rw finprod_in_def,
  apply finprod_of_infinite_mul_support,
  rwa [← mul_support_mul_indicator] at hs
end

@[to_additive] lemma finprod_in_inter_mul_support (f : α → M) (s : set α) :
  ∏ᶠ i ∈ (s ∩ mul_support f), f i = ∏ᶠ i ∈ s, f i :=
by rw [finprod_in_def, finprod_in_def, mul_indicator_inter_mul_support]

@[to_additive] lemma finprod_in_inter_mul_support_eq (f : α → M) (s t : set α)
  (h : s ∩ mul_support f = t ∩ mul_support f) :
  ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, f i :=
by rw [← finprod_in_inter_mul_support, h, finprod_in_inter_mul_support]

@[to_additive] lemma finprod_in_inter_mul_support_eq' (f : α → M) (s t : set α)
  (h : ∀ x ∈ mul_support f, x ∈ s ↔ x ∈ t) :
  ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, f i :=
begin
  apply finprod_in_inter_mul_support_eq,
  ext x,
  exact and_congr_left (h x)
end

@[to_additive] lemma finprod_in_univ (f : α → M) : ∏ᶠ i ∈ @set.univ α, f i = ∏ᶠ i : α, f i :=
finprod_congr $ λ i, finprod_true _

variables {f g : α → M} {a b : α} {s t : set α}

@[to_additive] lemma finprod_in_congr (h₀ : s = t) (h₁ : ∀ x ∈ t, f x = g x) :
  ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, g i :=
h₀.symm ▸ (finprod_congr $ λ i, finprod_congr_Prop rfl (h₁ i))

/-!
### Distributivity w.r.t. addition, subtraction, and (scalar) multiplication
-/

/-- If the multiplicative supports of `f` and `g` are finite, then the product of `f i * g i` equals
the product of `f i` multiplied by the product over `g i`. -/
@[to_additive] lemma finprod_mul_distrib (hf : (mul_support f).finite)
  (hg : (mul_support g).finite) :
  ∏ᶠ i, (f i * g i) = (∏ᶠ i, f i) * ∏ᶠ i, g i :=
begin
  rw [finprod_eq_prod_of_mul_support_to_finset_subset _ hf (finset.subset_union_left _ _),
    finprod_eq_prod_of_mul_support_to_finset_subset _ hg (finset.subset_union_right _ _),
    ← finset.prod_mul_distrib],
  refine finprod_eq_prod_of_mul_support_subset _ _,
  simp [mul_support_mul]
end

/-- A more general version of `finprod_in_mul_distrib` that requires `s ∩ mul_support f` and
`s ∩ mul_support g` instead of `s` to be finite. -/
@[to_additive] lemma finprod_in_mul_distrib' (hf : (s ∩ mul_support f).finite)
  (hg : (s ∩ mul_support g).finite) :
  ∏ᶠ i ∈ s, (f i * g i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ s, g i :=
begin
  rw [← mul_support_mul_indicator] at hf hg,
  simp only [finprod_in_def, mul_indicator_mul, finprod_mul_distrib hf hg]
end

/-- The product of constant one over any set equals one. -/
@[to_additive] lemma finprod_in_one (s : set α) : ∏ᶠ i ∈ s, (1 : M) = 1 := by simp

/-- If a function `f` equals one on a set `s`, then the product of `f i` over `i ∈ s` equals one. -/
@[to_additive] lemma finprod_in_of_eq_on_one (hf : eq_on f 1 s) : ∏ᶠ i ∈ s, f i = 1 :=
by { rw ← finprod_in_one s, exact finprod_in_congr rfl hf }

/-- If the product of `f i` over `i ∈ s` is not equal to one, then there is some `x ∈ s`
such that `f x ≠ 1`. -/
@[to_additive] lemma exists_ne_one_of_finprod_in_ne_one (h : ∏ᶠ i ∈ s, f i ≠ 1) :
  ∃ x ∈ s, f x ≠ 1 :=
begin
  by_contra h', push_neg at h',
  exact h (finprod_in_of_eq_on_one h')
end

/-- Given a finite set `s`, the product of `f i * g i` over `i ∈ s` equals the product of `f i`
over `i ∈ s` times the product of `g i` over `i ∈ s`. -/
@[to_additive] lemma finprod_in_mul_distrib (hs : s.finite) :
  ∏ᶠ i ∈ s, (f i * g i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ s, g i :=
finprod_in_mul_distrib' (hs.inter_of_left _) (hs.inter_of_left _)

@[to_additive] lemma finprod_hom {f : α → M} (g : M →* N) (hf : (mul_support f).finite) :
  ∏ᶠ i, g (f i) = g (∏ᶠ i, f i) :=
begin
  rw [finprod_eq_prod _ hf, g.map_prod],
  refine finprod_eq_prod_of_mul_support_subset _ _,
  simp [mul_support_comp_subset g.map_one]
end

/-- A more general version of `finprod_in_hom` that requires `s ∩ mul_support f` and instead of
  `s` to be finite. -/
@[to_additive] lemma finprod_in_hom' {f : α → M} (g : M →* N) (h₀ : (s ∩ mul_support f).finite) :
  ∏ᶠ i ∈ s, (g (f i)) = g (∏ᶠ j ∈ s, f j) :=
begin
  rw [finprod_in_def, mul_indicator_comp_of_one g.map_one, finprod_hom, finprod_in_def],
  rwa mul_support_mul_indicator
end

/-- Given a monoid homomorphism `g : M →* N`, and a function `f : α → M`, the product of `(g ∘ f) i`
over `s` equals the value of `g` at the product of `f i` over `i ∈ s`. -/
@[to_additive] lemma finprod_in_hom (f : α → M) (g : M →* N) (hs : s.finite) :
  ∏ᶠ i ∈ s, (g ∘ f) i = g (∏ᶠ j ∈ s, f j) :=
finprod_in_hom' g (hs.inter_of_left _)

@[to_additive] lemma finprod_in_hom'' (f : α → M) (g : M →* N) (hs : s.finite) :
  ∏ᶠ i ∈ s, g (f i) = g (∏ᶠ j ∈ s, f j) :=
finprod_in_hom f g hs

/-!
### `finprod_in` and set operations
-/

/-- The product of any function over an empty set is one. -/
@[to_additive] lemma finprod_in_empty : ∏ᶠ i ∈ (∅ : set α), f i = 1 := by simp

/-- A set `s` is not empty if the product of some function over `s` is not equal to one. -/
@[to_additive] lemma nonempty_of_finprod_in_ne_one (h : ∏ᶠ i ∈ s, f i ≠ 1) : s.nonempty :=
ne_empty_iff_nonempty.1 $ λ h', h $ h'.symm ▸ finprod_in_empty

/-- Given finite sets `s` and `t`, the product of `f i` over `i ∈ s ∪ t` times the product of
`f i` over `i ∈ s ∩ t` equals the product of `f i` over `i ∈ s` times the product of `f i`
over `i ∈ t`. -/
@[to_additive] lemma finprod_in_union_inter (hs : s.finite) (ht : t.finite) :
  (∏ᶠ i ∈ s ∪ t, f i) * ∏ᶠ i ∈ s ∩ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
begin
  unfreezingI { lift s to finset α using hs, lift t to finset α using ht },
  rw [← finset.coe_union, ← finset.coe_inter],
  simp only [finprod_in_coe_eq_prod, finset.prod_union_inter]
end

/-- A more general version of `finprod_in_union_inter` that requires `s ∩ mul_support f` and
`t ∩ mul_support f` instead of `s` and `t` to be finite. -/
@[to_additive] lemma finprod_in_union_inter'
  (hs : (s ∩ mul_support f).finite) (ht : (t ∩ mul_support f).finite) :
  (∏ᶠ i ∈ s ∪ t, f i) * ∏ᶠ i ∈ s ∩ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
begin
  rw [← finprod_in_inter_mul_support f s, ← finprod_in_inter_mul_support f t,
    ← finprod_in_union_inter hs ht, ← union_inter_distrib_right, finprod_in_inter_mul_support,
    ← finprod_in_inter_mul_support f (s ∩ t)],
  congr' 2,
  rw [inter_left_comm, inter_assoc, inter_assoc, inter_self, inter_left_comm]
end

/-- A more general version of `finprod_in_union` that requires `s ∩ mul_support f` and
`t ∩ mul_support f` instead of `s` and `t` to be finite. -/
@[to_additive] lemma finprod_in_union' (hs : (s ∩ mul_support f).finite)
  (ht : (t ∩ mul_support f).finite) (hst : disjoint s t) :
  ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
by rw [← finprod_in_union_inter' hs ht, disjoint_iff_inter_eq_empty.1 hst, finprod_in_empty,
  mul_one]

/-- Given two finite disjoint sets `s` and `t`, the product of `f i` over `i ∈ s ∪ t` equals the
product of `f i` over `i ∈ s` times the product of `f i` over `i ∈ t`. -/
@[to_additive] lemma finprod_in_union (hs : s.finite) (ht : t.finite) (hst : disjoint s t) :
  ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
finprod_in_union' (hs.inter_of_left _) (ht.inter_of_left _) hst

/-- A more general version of `finprod_in_union'` that requires `s ∩ mul_support f` and
`t ∩ mul_support f` instead of `s` and `t` to be disjoint -/
@[to_additive] lemma finprod_in_union'' (hs : (s ∩ mul_support f).finite)
  (ht : (t ∩ mul_support f).finite) (hst : disjoint (s ∩ mul_support f) (t ∩ mul_support f)) :
  ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
by rw [← finprod_in_inter_mul_support f s, ← finprod_in_inter_mul_support f t,
  ← finprod_in_union hs ht hst, ← union_inter_distrib_right, finprod_in_inter_mul_support]

/-- The product of `f i` over `i ∈ {a}` equals `f a`. -/
@[to_additive] lemma finprod_in_singleton : ∏ᶠ i ∈ ({a} : set α), f i = f a :=
by rw [← finset.coe_singleton, finprod_in_coe_eq_prod, finset.prod_singleton]

@[simp, to_additive] lemma finprod_in_eq_left : ∏ᶠ i = a, f i = f a :=
finprod_in_singleton

@[simp, to_additive] lemma finprod_in_eq_right : ∏ᶠ i (hi : a = i), f i = f a :=
by simpa [@eq_comm _ a] using finprod_in_eq_left

/-- A more general version of `finprod_in_insert` that requires `s ∩ mul_support f` instead of
`s` to be finite. -/
@[to_additive] lemma finprod_in_insert' (f : α → M) (h : a ∉ s)
  (hs : (s ∩ mul_support f).finite) :
  ∏ᶠ i ∈ insert a s, f i = f a * ∏ᶠ i ∈ s, f i :=
begin
  rw [insert_eq, finprod_in_union' _ hs, finprod_in_singleton],
  { rwa disjoint_singleton_left },
  { exact (finite_singleton a).inter_of_left _ }
end

/-- Given a finite set `s` and an element `a ∉ s`, the product of `f i` over `i ∈ insert a s` equals
`f a` times the product of `f i` over `i ∈ s`. -/
@[to_additive] lemma finprod_in_insert (f : α → M) (h : a ∉ s) (hs : s.finite) :
  ∏ᶠ i ∈ insert a s, f i = f a * ∏ᶠ i ∈ s, f i :=
finprod_in_insert' f h $ hs.inter_of_left _

/-- If `f a = 1` for all `a ∉ s`, then the product of `f i` over `i ∈ insert a s` equals the
product of `f i` over `i ∈ s`. -/
@[to_additive] lemma finprod_in_insert_of_eq_one_if_not_mem (h : a ∉ s → f a = 1) :
  ∏ᶠ i ∈ (insert a s), f i = ∏ᶠ i ∈ s, f i :=
begin
  refine finprod_in_inter_mul_support_eq' _ _ _ (λ x hx, ⟨_, or.inr⟩),
  rintro (rfl|hxs),
  exacts [not_imp_comm.1 h hx, hxs]
end

/-- If `f a = 1`, then the product of `f i` over `i ∈ insert a s` equals the product of `f i` over
`i ∈ s`. -/
@[to_additive] lemma finprod_insert_one (h : f a = 1) :
  ∏ᶠ i ∈ (insert a s), f i = ∏ᶠ i ∈ s, f i :=
finprod_in_insert_of_eq_one_if_not_mem (λ _, h)

/-- The product of `f i` over `i ∈ {a, b}`, `a ≠ b`, is equal to `f a * f b`. -/
@[to_additive] lemma finprod_pair (h : a ≠ b) : ∏ᶠ i ∈ ({a, b} : set α), f i = f a * f b :=
by { rw [finprod_in_insert, finprod_in_singleton], exacts [h, finite_singleton b] }

/-- The product of `f y` over `y ∈ g '' s` equals the product of `f (g i)` over `s`
provided that `g` is injective on `s ∩ mul_support (f ∘ g)`. -/
@[to_additive] lemma finprod_in_image' {s : set β} {g : β → α}
  (hg : set.inj_on g (s ∩ mul_support (f ∘ g))) :
  ∏ᶠ i ∈ (g '' s), f i = ∏ᶠ j ∈ s, f (g j) :=
begin
  by_cases hs : finite (s ∩ mul_support (f ∘ g)),
  { have hg : ∀ (x ∈ hs.to_finset) (y ∈ hs.to_finset), g x = g y → x = y,
      by simpa only [hs.mem_to_finset],
    rw [finprod_in_eq_prod _ hs, ← finset.prod_image hg],
    refine finprod_in_eq_prod_of_inter_mul_support_eq f _,
    rw [finset.coe_image, hs.coe_to_finset, ← image_inter_mul_support_eq, inter_assoc,
      inter_self] },
  { rw [finprod_in_eq_one_of_infinite hs, finprod_in_eq_one_of_infinite],
    rwa [image_inter_mul_support_eq, infinite_image_iff hg] }
end

/-- The product of `f y` over `y ∈ g '' s` equals the product of `f (g i)` over `s`
provided that `g` is injective on `s`. -/
@[to_additive] lemma finprod_in_image {β} {s : set β} {g : β → α} (hg : set.inj_on g s) :
  ∏ᶠ i ∈ (g '' s), f i = ∏ᶠ j ∈ s, f (g j) :=
finprod_in_image' $ hg.mono $ inter_subset_left _ _

/-- The product of `f y` over `y ∈ set.range g` equals the product of `f (g i)` over all `i`
provided that `g` is injective on `mul_support (f ∘ g)`. -/
@[to_additive] lemma finprod_in_range' {g : β → α} (hg : set.inj_on g (mul_support (f ∘ g))) :
  ∏ᶠ i ∈ range g, f i = ∏ᶠ j, f (g j) :=
begin
  rw [← image_univ, finprod_in_image', finprod_in_univ],
  rwa univ_inter
end

/-- The product of `f y` over `y ∈ set.range g` equals the product of `f (g i)` over all `i`
provided that `g` is injective. -/
@[to_additive] lemma finprod_in_range {g : β → α} (hg : injective g) :
  ∏ᶠ i ∈ range g, f i = ∏ᶠ j, f (g j) :=
finprod_in_range' (hg.inj_on _)

/-- The product of `f i` over `s : set α` is equal to the product of `g j` over `t : set β`
if there exists a function `e : α → β` such that `e` is bijective from `s` to `t` and for all
`x` in `s` we have `f x = g (e x)`. -/
@[to_additive] lemma finprod_in_eq_of_bij_on {s : set α} {t : set β} {f : α → M} {g : β → M}
  (e : α → β) (he₀ : set.bij_on e s t) (he₁ : ∀ x ∈ s, f x = g (e x)) :
  ∏ᶠ i ∈ s, f i = ∏ᶠ j ∈ t, g j :=
begin
  rw [← set.bij_on.image_eq he₀, finprod_in_image he₀.2.1],
  exact finprod_in_congr rfl he₁
end

@[to_additive] lemma finprod_subtype_eq_finprod_in (s : set α) : ∏ᶠ j : s, f j = ∏ᶠ i ∈ s, f i :=
begin
  rw [← finprod_in_range, subtype.range_coe],
  exact subtype.coe_injective
end

@[to_additive] lemma finprod_in_inter_mul_diff' (h : (s ∩ mul_support f).finite) :
  (∏ᶠ i ∈ s ∩ t, f i) * ∏ᶠ i ∈ s \ t, f i = ∏ᶠ i ∈ s, f i :=
begin
  rw [← finprod_in_union', inter_union_diff],
  exacts [h.subset (λ x hx, ⟨hx.1.1, hx.2⟩), h.subset (λ x hx, ⟨hx.1.1, hx.2⟩),
    λ x hx, hx.2.2 hx.1.2]
end

@[to_additive] lemma finprod_in_inter_mul_diff (h : s.finite) :
  (∏ᶠ i ∈ s ∩ t, f i) * ∏ᶠ i ∈ s \ t, f i = ∏ᶠ i ∈ s, f i :=
finprod_in_inter_mul_diff' $ h.inter_of_left _

/-- A more general version of `finprod_in_mul_diff` that requires `t ∩ mul_support f` instead of
  `t` to be finite. -/
@[to_additive] lemma finprod_in_mul_diff' (ht : (t ∩ mul_support f).finite) (hst : s ⊆ t) :
  (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t \ s, f i = ∏ᶠ i ∈ t, f i :=
by rw [← finprod_in_inter_mul_diff' ht, inter_eq_self_of_subset_right hst]

/-- Given a finite set `t` and a subset `s` of `t`, the product of `f i` over `i ∈ s`
times the product of `f i` over `t \ s` equals the product of `f i` over `i ∈ t`. -/
@[to_additive] lemma finprod_in_mul_diff (ht : t.finite) (hst : s ⊆ t) :
  (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t \ s, f i = ∏ᶠ i ∈ t, f i :=
finprod_in_mul_diff' (ht.inter_of_left _) hst

/-- Given a family of pairwise disjoint finite sets `t i` indexed by a finite type,
the product of `f a` over the union `⋃ i, t i` is equal to the product over all indexes `i`
of the products of `f a` over `a ∈ t i`. -/
@[to_additive] lemma finprod_in_Union [fintype ι] {t : ι → set α}
  (ht : ∀ i, (t i).finite) (h : pairwise (disjoint on t)) :
  ∏ᶠ a ∈ (⋃ i : ι, t i), f a = ∏ᶠ i, (∏ᶠ a ∈ t i, f a) :=
begin
  unfreezingI { lift t to ι → finset α using ht },
  rw [← bUnion_univ, ← finset.coe_univ, ← finset.coe_bUnion,
    finprod_in_coe_eq_prod, finset.prod_bUnion],
  { simp only [finprod_in_coe_eq_prod, finprod_eq_prod_of_fintype] },
  { exact λ x _ y _ hxy, finset.disjoint_iff_disjoint_coe.2 (h x y hxy) }
end

/-- Given a family of sets `t : ι → set α`, a finite set `I` in the index type such that all
sets `t i`, `i ∈ I`, are finite, if all `t i`, `i ∈ I`, are pairwise disjoint, then
the product of `f a` over `a ∈ ⋃ i ∈ I, t i` is equal to the product over `i ∈ I`
of the products of `f a` over `a ∈ t i`. -/
@[to_additive] lemma finprod_in_bUnion {I : set ι} {t : ι → set α} (hI : I.finite)
  (ht : ∀ i ∈ I, (t i).finite) (h : pairwise_on I (disjoint on t)) :
  ∏ᶠ a ∈ ⋃ x ∈ I, t x, f a = ∏ᶠ i ∈ I, ∏ᶠ j ∈ t i, f j :=
begin
  haveI := hI.fintype,
  rw [← Union_subtype, finprod_in_Union, ← finprod_subtype_eq_finprod_in],
  exacts [λ b, ht b b.2, λ x y hxy, h x x.2 y y.2 (subtype.coe_injective.ne hxy)]
end

/-- If `t` is a finite set of pairwise disjoint finite sets, then the product of `f a`
over `a ∈ ⋃₀ t` is the product over `s ∈ t` of the products of `f a` over `a ∈ s`. -/
@[to_additive] lemma finprod_in_sUnion {t : set (set α)} (ht₀ : t.finite)
  (ht₁ : ∀ x ∈ t, set.finite x) (h : pairwise_on t disjoint):
  ∏ᶠ a ∈ ⋃₀ t, f a = ∏ᶠ s ∈ t, ∏ᶠ a ∈ s, f a :=
by rw [set.sUnion_eq_bUnion, finprod_in_bUnion ht₀ ht₁ h]

/-- If `s : set α` and `t : set β` are finite sets, then the product over `s` commutes
with the product over `t`. -/
@[to_additive] lemma finprod_in_comm {s : set α} {t : set β}
  (f : α → β → M) (hs : s.finite) (ht : t.finite) :
  ∏ᶠ i ∈ s, ∏ᶠ j ∈ t, f i j = ∏ᶠ j ∈ t, ∏ᶠ i ∈ s, f i j :=
begin
  unfreezingI { lift s to finset α using hs, lift t to finset β using ht },
  simp only [finprod_in_coe_eq_prod],
  exact finset.prod_comm
end

/-- To prove a property of a finite product, it suffices to prove that the property is
multiplicative and holds on multipliers. -/
@[to_additive] lemma finprod_in_induction (p : M → Prop) (hp₀ : p 1)
  (hp₁ : ∀ x y, p x → p y → p (x * y)) (hp₂ : ∀ x ∈ s, p $ f x) :
  p (∏ᶠ i ∈ s, f i) :=
begin
  by_cases hs : (s ∩ mul_support f).finite,
  { rw [finprod_in_eq_prod _ hs],
    refine finset.prod_induction _ p hp₁ hp₀ (λ x hx, hp₂ x _),
    rw hs.mem_to_finset at hx, exact hx.1 },
  { exact (finprod_in_eq_one_of_infinite hs).symm ▸ hp₀ }
end

end type
