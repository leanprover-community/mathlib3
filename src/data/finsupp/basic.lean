/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Scott Morrison
-/
import algebra.hom.group_action
import algebra.indicator_function
import data.finset.preimage

/-!
# Type of functions with finite support

For any type `α` and a type `M` with zero, we define the type `finsupp α M` (notation: `α →₀ M`)
of finitely supported functions from `α` to `M`, i.e. the functions which are zero everywhere
on `α` except on a finite set.

Functions with finite support are used (at least) in the following parts of the library:

* `monoid_algebra R M` and `add_monoid_algebra R M` are defined as `M →₀ R`;

* polynomials and multivariate polynomials are defined as `add_monoid_algebra`s, hence they use
  `finsupp` under the hood;

* the linear combination of a family of vectors `v i` with coefficients `f i` (as used, e.g., to
  define linearly independent family `linear_independent`) is defined as a map
  `finsupp.total : (ι → M) → (ι →₀ R) →ₗ[R] M`.

Some other constructions are naturally equivalent to `α →₀ M` with some `α` and `M` but are defined
in a different way in the library:

* `multiset α ≃+ α →₀ ℕ`;
* `free_abelian_group α ≃+ α →₀ ℤ`.

Most of the theory assumes that the range is a commutative additive monoid. This gives us the big
sum operator as a powerful way to construct `finsupp` elements.

Many constructions based on `α →₀ M` use `semireducible` type tags to avoid reusing unwanted type
instances. E.g., `monoid_algebra`, `add_monoid_algebra`, and types based on these two have
non-pointwise multiplication.

## Main declarations

* `finsupp`: The type of finitely supported functions from `α` to `β`.
* `finsupp.single`: The `finsupp` which is nonzero in exactly one point.
* `finsupp.update`: Changes one value of a `finsupp`.
* `finsupp.erase`: Replaces one value of a `finsupp` by `0`.
* `finsupp.on_finset`: The restriction of a function to a `finset` as a `finsupp`.
* `finsupp.map_range`: Composition of a `zero_hom` with a `finsupp`.
* `finsupp.emb_domain`: Maps the domain of a `finsupp` by an embedding.
* `finsupp.map_domain`: Maps the domain of a `finsupp` by a function and by summing.
* `finsupp.comap_domain`: Postcomposition of a `finsupp` with a function injective on the preimage
  of its support.
* `finsupp.zip_with`: Postcomposition of two `finsupp`s with a function `f` such that `f 0 0 = 0`.
* `finsupp.sum`: Sum of the values of a `finsupp`.
* `finsupp.prod`: Product of the nonzero values of a `finsupp`.

## Notations

This file adds `α →₀ M` as a global notation for `finsupp α M`.

We also use the following convention for `Type*` variables in this file

* `α`, `β`, `γ`: types with no additional structure that appear as the first argument to `finsupp`
  somewhere in the statement;

* `ι` : an auxiliary index type;

* `M`, `M'`, `N`, `P`: types with `has_zero` or `(add_)(comm_)monoid` structure; `M` is also used
  for a (semi)module over a (semi)ring.

* `G`, `H`: groups (commutative or not, multiplicative or additive);

* `R`, `S`: (semi)rings.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## TODO

* This file is currently ~2.7K lines long, so it should be splitted into smaller chunks.
  One option would be to move all the sum and product stuff to `algebra.big_operators.finsupp` and
  move the definitions that depend on it to new files under `data.finsupp.`.

* Expand the list of definitions and important lemmas to the module docstring.

-/

noncomputable theory

open finset function
open_locale classical big_operators

variables {α β γ ι M M' N P G H R S : Type*}

/-- `finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that
  `f x = 0` for all but finitely many `x`. -/
structure finsupp (α : Type*) (M : Type*) [has_zero M] :=
(support            : finset α)
(to_fun             : α → M)
(mem_support_to_fun : ∀a, a ∈ support ↔ to_fun a ≠ 0)

infixr ` →₀ `:25 := finsupp

namespace finsupp

/-! ### Basic declarations about `finsupp` -/

section basic
variable [has_zero M]

instance fun_like : fun_like (α →₀ M) α (λ _, M) := ⟨to_fun, begin
  rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g),
  congr',
  ext a,
  exact (hf _).trans (hg _).symm,
end⟩

/-- Helper instance for when there are too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (α →₀ M) (λ _, α → M) := fun_like.has_coe_to_fun

@[ext] lemma ext {f g : α →₀ M} (h : ∀ a, f a = g a) : f = g := fun_like.ext _ _ h
/-- Deprecated. Use `fun_like.ext_iff` instead. -/
lemma ext_iff {f g : α →₀ M} : f = g ↔ ∀ a, f a = g a := fun_like.ext_iff
/-- Deprecated. Use `fun_like.coe_fn_eq` instead. -/
lemma coe_fn_inj {f g : α →₀ M} : (f : α → M) = g ↔ f = g := fun_like.coe_fn_eq
/-- Deprecated. Use `fun_like.coe_injective` instead. -/
lemma coe_fn_injective : @function.injective (α →₀ M) (α → M) coe_fn := fun_like.coe_injective
/-- Deprecated. Use `fun_like.congr_fun` instead. -/
lemma congr_fun {f g : α →₀ M} (h : f = g) (a : α) : f a = g a := fun_like.congr_fun h _

@[simp] lemma coe_mk (f : α → M) (s : finset α) (h : ∀ a, a ∈ s ↔ f a ≠ 0) :
  ⇑(⟨s, f, h⟩ : α →₀ M) = f := rfl

instance : has_zero (α →₀ M) := ⟨⟨∅, 0, λ _, ⟨false.elim, λ H, H rfl⟩⟩⟩

@[simp] lemma coe_zero : ⇑(0 : α →₀ M) = 0 := rfl
lemma zero_apply {a : α} : (0 : α →₀ M) a = 0 := rfl
@[simp] lemma support_zero : (0 : α →₀ M).support = ∅ := rfl

instance : inhabited (α →₀ M) := ⟨0⟩

@[simp] lemma mem_support_iff {f : α →₀ M} : ∀{a:α}, a ∈ f.support ↔ f a ≠ 0 :=
f.mem_support_to_fun

@[simp, norm_cast] lemma fun_support_eq (f : α →₀ M) : function.support f = f.support :=
set.ext $ λ x, mem_support_iff.symm

lemma not_mem_support_iff {f : α →₀ M} {a} : a ∉ f.support ↔ f a = 0 :=
not_iff_comm.1 mem_support_iff.symm

@[simp, norm_cast] lemma coe_eq_zero {f : α →₀ M} : (f : α → M) = 0 ↔ f = 0 :=
by rw [← coe_zero, coe_fn_inj]

lemma ext_iff' {f g : α →₀ M} : f = g ↔ f.support = g.support ∧ ∀ x ∈ f.support, f x = g x :=
⟨λ h, h ▸ ⟨rfl, λ _ _, rfl⟩, λ ⟨h₁, h₂⟩, ext $ λ a,
  if h : a ∈ f.support then h₂ a h else
    have hf : f a = 0, from not_mem_support_iff.1 h,
    have hg : g a = 0, by rwa [h₁, not_mem_support_iff] at h,
    by rw [hf, hg]⟩

@[simp] lemma support_eq_empty {f : α →₀ M} : f.support = ∅ ↔ f = 0 :=
by exact_mod_cast @function.support_eq_empty_iff _ _ _ f

lemma support_nonempty_iff {f : α →₀ M} : f.support.nonempty ↔ f ≠ 0 :=
by simp only [finsupp.support_eq_empty, finset.nonempty_iff_ne_empty, ne.def]

lemma nonzero_iff_exists {f : α →₀ M} : f ≠ 0 ↔ ∃ a : α, f a ≠ 0 :=
by simp [← finsupp.support_eq_empty, finset.eq_empty_iff_forall_not_mem]

lemma card_support_eq_zero {f : α →₀ M} : card f.support = 0 ↔ f = 0 :=
by simp

instance [decidable_eq α] [decidable_eq M] : decidable_eq (α →₀ M) :=
assume f g, decidable_of_iff (f.support = g.support ∧ (∀a∈f.support, f a = g a)) ext_iff'.symm

lemma finite_support (f : α →₀ M) : set.finite (function.support f) :=
f.fun_support_eq.symm ▸ f.support.finite_to_set

lemma support_subset_iff {s : set α} {f : α →₀ M} :
  ↑f.support ⊆ s ↔ (∀a∉s, f a = 0) :=
by simp only [set.subset_def, mem_coe, mem_support_iff];
   exact forall_congr (assume a, not_imp_comm)

/-- Given `fintype α`, `equiv_fun_on_fintype` is the `equiv` between `α →₀ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps] def equiv_fun_on_fintype [fintype α] : (α →₀ M) ≃ (α → M) :=
⟨λf a, f a, λf, mk (finset.univ.filter $ λa, f a ≠ 0) f (by simp only [true_and, finset.mem_univ,
  iff_self, finset.mem_filter, finset.filter_congr_decidable, forall_true_iff]),
  begin intro f, ext a, refl end,
  begin intro f, ext a, refl end⟩

@[simp] lemma equiv_fun_on_fintype_symm_coe {α} [fintype α] (f : α →₀ M) :
  equiv_fun_on_fintype.symm f = f :=
by { ext, simp [equiv_fun_on_fintype], }

/-- If `α` has a unique term,
then the type of finitely supported functions `α →₀ β` is equivalent to `β`. -/
@[simps] noncomputable
def _root_.equiv.finsupp_unique {ι : Type*} [unique ι] : (ι →₀ M) ≃ M :=
finsupp.equiv_fun_on_fintype.trans (equiv.fun_unique ι M)

end basic

/-! ### Declarations about `single` -/

section single
variables [has_zero M] {a a' : α} {b : M}

/-- `single a b` is the finitely supported function which has
  value `b` at `a` and zero otherwise. -/
def single (a : α) (b : M) : α →₀ M :=
⟨if b = 0 then ∅ else {a}, λ a', if a = a' then b else 0, λ a', begin
  by_cases hb : b = 0; by_cases a = a';
    simp only [hb, h, if_pos, if_false, mem_singleton],
  { exact ⟨false.elim, λ H, H rfl⟩ },
  { exact ⟨false.elim, λ H, H rfl⟩ },
  { exact ⟨λ _, hb, λ _, rfl⟩ },
  { exact ⟨λ H _, h H.symm, λ H, (H rfl).elim⟩ }
end⟩

lemma single_apply [decidable (a = a')] : single a b a' = if a = a' then b else 0 :=
by convert rfl

lemma single_eq_indicator : ⇑(single a b) = set.indicator {a} (λ _, b) :=
by { ext, simp [single_apply, set.indicator, @eq_comm _ a] }

@[simp] lemma single_eq_same : (single a b : α →₀ M) a = b :=
if_pos rfl

@[simp] lemma single_eq_of_ne (h : a ≠ a') : (single a b : α →₀ M) a' = 0 :=
if_neg h

lemma single_eq_update [decidable_eq α] (a : α) (b : M) : ⇑(single a b) = function.update 0 a b :=
by rw [single_eq_indicator, ← set.piecewise_eq_indicator, set.piecewise_singleton]

lemma single_eq_pi_single [decidable_eq α] (a : α) (b : M) : ⇑(single a b) = pi.single a b :=
single_eq_update a b

@[simp] lemma single_zero (a : α) : (single a 0 : α →₀ M) = 0 :=
coe_fn_injective $ by simpa only [single_eq_update, coe_zero]
  using function.update_eq_self a (0 : α → M)

lemma single_of_single_apply (a a' : α) (b : M) :
  single a ((single a' b) a) = single a' (single a' b) a :=
begin
  rw [single_apply, single_apply],
  ext,
  split_ifs,
  { rw h, },
  { rw [zero_apply, single_apply, if_t_t], },
end

lemma support_single_ne_zero (a : α) (hb : b ≠ 0) : (single a b).support = {a} :=
if_neg hb

lemma support_single_subset : (single a b).support ⊆ {a} :=
show ite _ _ _ ⊆ _, by split_ifs; [exact empty_subset _, exact subset.refl _]

lemma single_apply_mem (x) : single a b x ∈ ({0, b} : set M) :=
by rcases em (a = x) with (rfl|hx); [simp, simp [single_eq_of_ne hx]]

lemma range_single_subset : set.range (single a b) ⊆ {0, b} :=
set.range_subset_iff.2 single_apply_mem

/-- `finsupp.single a b` is injective in `b`. For the statement that it is injective in `a`, see
`finsupp.single_left_injective` -/
lemma single_injective (a : α) : function.injective (single a : M → α →₀ M) :=
assume b₁ b₂ eq,
have (single a b₁ : α →₀ M) a = (single a b₂ : α →₀ M) a, by rw eq,
by rwa [single_eq_same, single_eq_same] at this

lemma single_apply_eq_zero {a x : α} {b : M} : single a b x = 0 ↔ (x = a → b = 0) :=
by simp [single_eq_indicator]

lemma single_apply_ne_zero {a x : α} {b : M} : single a b x ≠ 0 ↔ (x = a ∧ b ≠ 0) :=
by simp [single_apply_eq_zero]

lemma mem_support_single (a a' : α) (b : M) :
  a ∈ (single a' b).support ↔ a = a' ∧ b ≠ 0 :=
by simp [single_apply_eq_zero, not_or_distrib]

lemma eq_single_iff {f : α →₀ M} {a b} : f = single a b ↔ f.support ⊆ {a} ∧ f a = b :=
begin
  refine ⟨λ h, h.symm ▸ ⟨support_single_subset, single_eq_same⟩, _⟩,
  rintro ⟨h, rfl⟩,
  ext x,
  by_cases hx : a = x; simp only [hx, single_eq_same, single_eq_of_ne, ne.def, not_false_iff],
  exact not_mem_support_iff.1 (mt (λ hx, (mem_singleton.1 (h hx)).symm) hx)
end

lemma single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : M) :
  single a₁ b₁ = single a₂ b₂ ↔ ((a₁ = a₂ ∧ b₁ = b₂) ∨ (b₁ = 0 ∧ b₂ = 0)) :=
begin
  split,
  { assume eq,
    by_cases a₁ = a₂,
    { refine or.inl ⟨h, _⟩,
      rwa [h, (single_injective a₂).eq_iff] at eq },
    { rw [ext_iff] at eq,
      have h₁ := eq a₁,
      have h₂ := eq a₂,
      simp only [single_eq_same, single_eq_of_ne h, single_eq_of_ne (ne.symm h)] at h₁ h₂,
      exact or.inr ⟨h₁, h₂.symm⟩ } },
  { rintros (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩),
    { refl },
    { rw [single_zero, single_zero] } }
end

/-- `finsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`finsupp.single_injective` -/
lemma single_left_injective (h : b ≠ 0) : function.injective (λ a : α, single a b) :=
λ a a' H, (((single_eq_single_iff _ _ _ _).mp H).resolve_right $ λ hb, h hb.1).left

lemma single_left_inj (h : b ≠ 0) : single a b = single a' b ↔ a = a' :=
(single_left_injective h).eq_iff

lemma support_single_ne_bot (i : α) (h : b ≠ 0) :
  (single i b).support ≠ ⊥ :=
by simpa only [support_single_ne_zero _ h] using singleton_ne_empty _

lemma support_single_disjoint [decidable_eq α] {b' : M} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : α} :
  disjoint (single i b).support (single j b').support ↔ i ≠ j :=
by rw [support_single_ne_zero _ hb, support_single_ne_zero _ hb', disjoint_singleton]

@[simp] lemma single_eq_zero : single a b = 0 ↔ b = 0 :=
by simp [ext_iff, single_eq_indicator]

lemma single_swap (a₁ a₂ : α) (b : M) : single a₁ b a₂ = single a₂ b a₁ :=
by simp only [single_apply]; ac_refl

instance [nonempty α] [nontrivial M] : nontrivial (α →₀ M) :=
begin
  inhabit α,
  rcases exists_ne (0 : M) with ⟨x, hx⟩,
  exact nontrivial_of_ne (single default x) 0 (mt single_eq_zero.1 hx)
end

lemma unique_single [unique α] (x : α →₀ M) : x = single default (x default) :=
ext $ unique.forall_iff.2 single_eq_same.symm

@[ext]
lemma unique_ext [unique α] {f g : α →₀ M} (h : f default = g default) : f = g :=
ext $ λ a, by rwa [unique.eq_default a]

lemma unique_ext_iff [unique α] {f g : α →₀ M} : f = g ↔ f default = g default :=
⟨λ h, h ▸ rfl, unique_ext⟩

@[simp] lemma unique_single_eq_iff [unique α] {b' : M} :
  single a b = single a' b' ↔ b = b' :=
by rw [unique_ext_iff, unique.eq_default a, unique.eq_default a', single_eq_same, single_eq_same]

lemma support_eq_singleton {f : α →₀ M} {a : α} :
  f.support = {a} ↔ f a ≠ 0 ∧ f = single a (f a) :=
⟨λ h, ⟨mem_support_iff.1 $ h.symm ▸ finset.mem_singleton_self a,
  eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩, λ h, h.2.symm ▸ support_single_ne_zero _ h.1⟩

lemma support_eq_singleton' {f : α →₀ M} {a : α} :
  f.support = {a} ↔ ∃ b ≠ 0, f = single a b :=
⟨λ h, let h := support_eq_singleton.1 h in ⟨_, h.1, h.2⟩,
  λ ⟨b, hb, hf⟩, hf.symm ▸ support_single_ne_zero _ hb⟩

lemma card_support_eq_one {f : α →₀ M} : card f.support = 1 ↔ ∃ a, f a ≠ 0 ∧ f = single a (f a) :=
by simp only [card_eq_one, support_eq_singleton]

lemma card_support_eq_one' {f : α →₀ M} : card f.support = 1 ↔ ∃ a (b ≠ 0), f = single a b :=
by simp only [card_eq_one, support_eq_singleton']

lemma support_subset_singleton {f : α →₀ M} {a : α} :
  f.support ⊆ {a} ↔ f = single a (f a) :=
⟨λ h, eq_single_iff.mpr ⟨h, rfl⟩, λ h, (eq_single_iff.mp h).left⟩

lemma support_subset_singleton' {f : α →₀ M} {a : α} :
  f.support ⊆ {a} ↔ ∃ b, f = single a b :=
⟨λ h, ⟨f a, support_subset_singleton.mp h⟩,
  λ ⟨b, hb⟩, by rw [hb, support_subset_singleton, single_eq_same]⟩

lemma card_support_le_one [nonempty α] {f : α →₀ M} :
  card f.support ≤ 1 ↔ ∃ a, f = single a (f a) :=
by simp only [card_le_one_iff_subset_singleton, support_subset_singleton]

lemma card_support_le_one' [nonempty α] {f : α →₀ M} :
  card f.support ≤ 1 ↔ ∃ a b, f = single a b :=
by simp only [card_le_one_iff_subset_singleton, support_subset_singleton']

@[simp] lemma equiv_fun_on_fintype_single [decidable_eq α] [fintype α] (x : α) (m : M) :
  (@finsupp.equiv_fun_on_fintype α M _ _) (finsupp.single x m) = pi.single x m :=
by { ext, simp [finsupp.single_eq_pi_single, finsupp.equiv_fun_on_fintype], }

@[simp] lemma equiv_fun_on_fintype_symm_single [decidable_eq α] [fintype α] (x : α) (m : M) :
  (@finsupp.equiv_fun_on_fintype α M _ _).symm (pi.single x m) = finsupp.single x m :=
by { ext, simp [finsupp.single_eq_pi_single, finsupp.equiv_fun_on_fintype], }

end single

/-! ### Declarations about `update` -/

section update

variables [has_zero M] (f : α →₀ M) (a : α) (b : M) (i : α)

/-- Replace the value of a `α →₀ M` at a given point `a : α` by a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the `finsupp.support`.
Otherwise, if `a` was not in the `finsupp.support`, it is added to it.

This is the finitely-supported version of `function.update`. -/
def update : α →₀ M :=
⟨if b = 0 then f.support.erase a else insert a f.support,
  function.update f a b,
  λ i, begin
    simp only [function.update_apply, ne.def],
    split_ifs with hb ha ha hb;
    simp [ha, hb]
  end⟩

@[simp] lemma coe_update [decidable_eq α] : (f.update a b : α → M) = function.update f a b :=
by convert rfl
@[simp] lemma update_self : f.update a (f a) = f :=
by { ext, simp }

lemma support_update [decidable_eq α] : support (f.update a b) =
  if b = 0 then f.support.erase a else insert a f.support := by convert rfl

@[simp] lemma support_update_zero [decidable_eq α] :
  support (f.update a 0) = f.support.erase a := by convert if_pos rfl

variables {b}

lemma support_update_ne_zero [decidable_eq α] (h : b ≠ 0) :
  support (f.update a b) = insert a f.support := by convert if_neg h

end update

/-! ### Declarations about `on_finset` -/

section on_finset
variables [has_zero M]

/-- `on_finset s f hf` is the finsupp function representing `f` restricted to the finset `s`.
  The function needs to be `0` outside of `s`. Use this when the set needs to be filtered anyways,
  otherwise a better set representation is often available. -/
def on_finset (s : finset α) (f : α → M) (hf : ∀a, f a ≠ 0 → a ∈ s) : α →₀ M :=
⟨s.filter (λa, f a ≠ 0), f, by simpa⟩

@[simp] lemma on_finset_apply {s : finset α} {f : α → M} {hf a} :
  (on_finset s f hf : α →₀ M) a = f a :=
rfl

@[simp] lemma support_on_finset_subset {s : finset α} {f : α → M} {hf} :
  (on_finset s f hf).support ⊆ s :=
filter_subset _ _

@[simp] lemma mem_support_on_finset
  {s : finset α} {f : α → M} (hf : ∀ (a : α), f a ≠ 0 → a ∈ s) {a : α} :
  a ∈ (finsupp.on_finset s f hf).support ↔ f a ≠ 0 :=
by rw [finsupp.mem_support_iff, finsupp.on_finset_apply]

lemma support_on_finset
  {s : finset α} {f : α → M} (hf : ∀ (a : α), f a ≠ 0 → a ∈ s) :
  (finsupp.on_finset s f hf).support = s.filter (λ a, f a ≠ 0) :=
rfl

end on_finset

section of_support_finite

variables [has_zero M]

/-- The natural `finsupp` induced by the function `f` given that it has finite support. -/
noncomputable def of_support_finite
  (f : α → M) (hf : (function.support f).finite) : α →₀ M :=
{ support := hf.to_finset,
  to_fun := f,
  mem_support_to_fun := λ _, hf.mem_to_finset }

lemma of_support_finite_coe {f : α → M} {hf : (function.support f).finite} :
  (of_support_finite f hf : α → M) = f := rfl

instance : can_lift (α → M) (α →₀ M) :=
{ coe := coe_fn,
  cond := λ f, (function.support f).finite,
  prf := λ f hf, ⟨of_support_finite f hf, rfl⟩ }

end of_support_finite

/-! ### Declarations about `map_range` -/

section map_range
variables [has_zero M] [has_zero N] [has_zero P]

/-- The composition of `f : M → N` and `g : α →₀ M` is
`map_range f hf g : α →₀ N`, well-defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled:

* `finsupp.map_range.equiv`
* `finsupp.map_range.zero_hom`
* `finsupp.map_range.add_monoid_hom`
* `finsupp.map_range.add_equiv`
* `finsupp.map_range.linear_map`
* `finsupp.map_range.linear_equiv`
-/
def map_range (f : M → N) (hf : f 0 = 0) (g : α →₀ M) : α →₀ N :=
on_finset g.support (f ∘ g) $
  assume a, by rw [mem_support_iff, not_imp_not]; exact λ H, (congr_arg f H).trans hf

@[simp] lemma map_range_apply {f : M → N} {hf : f 0 = 0} {g : α →₀ M} {a : α} :
  map_range f hf g a = f (g a) :=
rfl

@[simp] lemma map_range_zero {f : M → N} {hf : f 0 = 0} : map_range f hf (0 : α →₀ M) = 0 :=
ext $ λ a, by simp only [hf, zero_apply, map_range_apply]

@[simp] lemma map_range_id (g : α →₀ M) : map_range id rfl g = g :=
ext $ λ _, rfl

lemma map_range_comp
  (f : N → P) (hf : f 0 = 0) (f₂ : M → N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0) (g : α →₀ M) :
  map_range (f ∘ f₂) h g = map_range f hf (map_range f₂ hf₂ g) :=
ext $ λ _, rfl

lemma support_map_range {f : M → N} {hf : f 0 = 0} {g : α →₀ M} :
  (map_range f hf g).support ⊆ g.support :=
support_on_finset_subset

@[simp] lemma map_range_single {f : M → N} {hf : f 0 = 0} {a : α} {b : M} :
  map_range f hf (single a b) = single a (f b) :=
ext $ λ a', show f (ite _ _ _) = ite _ _ _, by split_ifs; [refl, exact hf]

lemma support_map_range_of_injective
  {e : M → N} (he0 : e 0 = 0) (f : ι →₀ M) (he : function.injective e) :
  (finsupp.map_range e he0 f).support = f.support :=
begin
  ext,
  simp only [finsupp.mem_support_iff, ne.def, finsupp.map_range_apply],
  exact he.ne_iff' he0,
end

end map_range

/-! ### Declarations about `emb_domain` -/

section emb_domain
variables [has_zero M] [has_zero N]

/-- Given `f : α ↪ β` and `v : α →₀ M`, `emb_domain f v : β →₀ M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is zero. -/
def emb_domain (f : α ↪ β) (v : α →₀ M) : β →₀ M :=
begin
  refine ⟨v.support.map f, λa₂,
    if h : a₂ ∈ v.support.map f then v (v.support.choose (λa₁, f a₁ = a₂) _) else 0, _⟩,
  { rcases finset.mem_map.1 h with ⟨a, ha, rfl⟩,
    exact exists_unique.intro a ⟨ha, rfl⟩ (assume b ⟨_, hb⟩, f.injective hb) },
  { assume a₂,
    split_ifs,
    { simp only [h, true_iff, ne.def],
      rw [← not_mem_support_iff, not_not],
      apply finset.choose_mem },
    { simp only [h, ne.def, ne_self_iff_false] } }
end

@[simp] lemma support_emb_domain (f : α ↪ β) (v : α →₀ M) :
  (emb_domain f v).support = v.support.map f :=
rfl

@[simp] lemma emb_domain_zero (f : α ↪ β) : (emb_domain f 0 : β →₀ M) = 0 :=
rfl

@[simp] lemma emb_domain_apply (f : α ↪ β) (v : α →₀ M) (a : α) :
  emb_domain f v (f a) = v a :=
begin
  change dite _ _ _ = _,
  split_ifs; rw [finset.mem_map' f] at h,
  { refine congr_arg (v : α → M) (f.inj' _),
    exact finset.choose_property (λa₁, f a₁ = f a) _ _ },
  { exact (not_mem_support_iff.1 h).symm }
end

lemma emb_domain_notin_range (f : α ↪ β) (v : α →₀ M) (a : β) (h : a ∉ set.range f) :
  emb_domain f v a = 0 :=
begin
  refine dif_neg (mt (assume h, _) h),
  rcases finset.mem_map.1 h with ⟨a, h, rfl⟩,
  exact set.mem_range_self a
end

lemma emb_domain_injective (f : α ↪ β) :
  function.injective (emb_domain f : (α →₀ M) → (β →₀ M)) :=
λ l₁ l₂ h, ext $ λ a, by simpa only [emb_domain_apply] using ext_iff.1 h (f a)

@[simp] lemma emb_domain_inj {f : α ↪ β} {l₁ l₂ : α →₀ M} :
  emb_domain f l₁ = emb_domain f l₂ ↔ l₁ = l₂ :=
(emb_domain_injective f).eq_iff

@[simp] lemma emb_domain_eq_zero {f : α ↪ β} {l : α →₀ M} :
  emb_domain f l = 0 ↔ l = 0 :=
(emb_domain_injective f).eq_iff' $ emb_domain_zero f

lemma emb_domain_map_range
  (f : α ↪ β) (g : M → N) (p : α →₀ M) (hg : g 0 = 0) :
  emb_domain f (map_range g hg p) = map_range g hg (emb_domain f p) :=
begin
  ext a,
  by_cases a ∈ set.range f,
  { rcases h with ⟨a', rfl⟩,
    rw [map_range_apply, emb_domain_apply, emb_domain_apply, map_range_apply] },
  { rw [map_range_apply, emb_domain_notin_range, emb_domain_notin_range, ← hg]; assumption }
end

lemma single_of_emb_domain_single
  (l : α →₀ M) (f : α ↪ β) (a : β) (b : M) (hb : b ≠ 0)
  (h : l.emb_domain f = single a b) :
  ∃ x, l = single x b ∧ f x = a :=
begin
  have h_map_support : finset.map f (l.support) = {a},
    by rw [←support_emb_domain, h, support_single_ne_zero _ hb]; refl,
  have ha : a ∈ finset.map f (l.support),
    by simp only [h_map_support, finset.mem_singleton],
  rcases finset.mem_map.1 ha with ⟨c, hc₁, hc₂⟩,
  use c,
  split,
  { ext d,
    rw [← emb_domain_apply f l, h],
    by_cases h_cases : c = d,
    { simp only [eq.symm h_cases, hc₂, single_eq_same] },
    { rw [single_apply, single_apply, if_neg, if_neg h_cases],
      by_contra hfd,
      exact h_cases (f.injective (hc₂.trans hfd)) } },
  { exact hc₂ }
end

@[simp] lemma emb_domain_single (f : α ↪ β) (a : α) (m : M) :
  emb_domain f (single a m) = single (f a) m :=
begin
  ext b,
  by_cases h : b ∈ set.range f,
  { rcases h with ⟨a', rfl⟩,
    simp [single_apply], },
  { simp only [emb_domain_notin_range, h, single_apply, not_false_iff],
    rw if_neg,
    rintro rfl,
    simpa using h, },
end

end emb_domain

/-! ### Declarations about `zip_with` -/

section zip_with
variables [has_zero M] [has_zero N] [has_zero P]

/-- `zip_with f hf g₁ g₂` is the finitely supported function satisfying
  `zip_with f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, and it is well-defined when `f 0 0 = 0`. -/
def zip_with (f : M → N → P) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : α →₀ P :=
on_finset (g₁.support ∪ g₂.support) (λa, f (g₁ a) (g₂ a)) $ λ a H,
begin
  simp only [mem_union, mem_support_iff, ne], rw [← not_and_distrib],
  rintro ⟨h₁, h₂⟩, rw [h₁, h₂] at H, exact H hf
end

@[simp] lemma zip_with_apply
  {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} {a : α} :
  zip_with f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
rfl

lemma support_zip_with [D : decidable_eq α] {f : M → N → P} {hf : f 0 0 = 0}
  {g₁ : α →₀ M} {g₂ : α →₀ N} : (zip_with f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support :=
by rw subsingleton.elim D; exact support_on_finset_subset

end zip_with

/-! ### Declarations about `erase` -/

section erase

variables [has_zero M]

/-- `erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to
  `0`. -/
def erase (a : α) (f : α →₀ M) : α →₀ M :=
⟨f.support.erase a, (λa', if a' = a then 0 else f a'),
  assume a', by rw [mem_erase, mem_support_iff]; split_ifs;
    [exact ⟨λ H _, H.1 h, λ H, (H rfl).elim⟩,
    exact and_iff_right h]⟩

@[simp] lemma support_erase [decidable_eq α] {a : α} {f : α →₀ M} :
  (f.erase a).support = f.support.erase a :=
by convert rfl

@[simp] lemma erase_same {a : α} {f : α →₀ M} : (f.erase a) a = 0 :=
if_pos rfl

@[simp] lemma erase_ne {a a' : α} {f : α →₀ M} (h : a' ≠ a) : (f.erase a) a' = f a' :=
if_neg h

@[simp] lemma erase_single {a : α} {b : M} : (erase a (single a b)) = 0 :=
begin
  ext s, by_cases hs : s = a,
  { rw [hs, erase_same], refl },
  { rw [erase_ne hs], exact single_eq_of_ne (ne.symm hs) }
end

lemma erase_single_ne {a a' : α} {b : M} (h : a ≠ a') : (erase a (single a' b)) = single a' b :=
begin
  ext s, by_cases hs : s = a,
  { rw [hs, erase_same, single_eq_of_ne (h.symm)] },
  { rw [erase_ne hs] }
end

@[simp] lemma erase_of_not_mem_support {f : α →₀ M} {a} (haf : a ∉ f.support) : erase a f = f :=
begin
  ext b, by_cases hab : b = a,
  { rwa [hab, erase_same, eq_comm, ←not_mem_support_iff] },
  { rw erase_ne hab }
end

@[simp] lemma erase_zero (a : α) : erase a (0 : α →₀ M) = 0 :=
by rw [← support_eq_empty, support_erase, support_zero, erase_empty]

end erase



--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- section add_zero_class   vvvvv
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

/-!
### Additive monoid structure on `α →₀ M`
-/

section add_zero_class

variables [add_zero_class M]

instance : has_add (α →₀ M) := ⟨zip_with (+) (add_zero 0)⟩

@[simp] lemma coe_add (f g : α →₀ M) : ⇑(f + g) = f + g := rfl
lemma add_apply (g₁ g₂ : α →₀ M) (a : α) : (g₁ + g₂) a = g₁ a + g₂ a := rfl

lemma support_add [decidable_eq α] {g₁ g₂ : α →₀ M} :
  (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support :=
support_zip_with

lemma support_add_eq [decidable_eq α] {g₁ g₂ : α →₀ M} (h : disjoint g₁.support g₂.support) :
  (g₁ + g₂).support = g₁.support ∪ g₂.support :=
le_antisymm support_zip_with $ assume a ha,
(finset.mem_union.1 ha).elim
  (assume ha, have a ∉ g₂.support, from disjoint_left.1 h ha,
    by simp only [mem_support_iff, not_not] at *;
    simpa only [add_apply, this, add_zero])
  (assume ha, have a ∉ g₁.support, from disjoint_right.1 h ha,
    by simp only [mem_support_iff, not_not] at *;
    simpa only [add_apply, this, zero_add])

@[simp] lemma single_add (a : α) (b₁ b₂ : M) : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
ext $ assume a',
begin
  by_cases h : a = a',
  { rw [h, add_apply, single_eq_same, single_eq_same, single_eq_same] },
  { rw [add_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, zero_add] }
end

instance : add_zero_class (α →₀ M) :=
fun_like.coe_injective.add_zero_class _ coe_zero coe_add

/-- `finsupp.single` as an `add_monoid_hom`.

See `finsupp.lsingle` for the stronger version as a linear map.
-/
@[simps] def single_add_hom (a : α) : M →+ α →₀ M :=
⟨single a, single_zero a, single_add a⟩

/-- Evaluation of a function `f : α →₀ M` at a point as an additive monoid homomorphism.

See `finsupp.lapply` for the stronger version as a linear map. -/
@[simps apply]
def apply_add_hom (a : α) : (α →₀ M) →+ M := ⟨λ g, g a, zero_apply, λ _ _, add_apply _ _ _⟩

/-- Coercion from a `finsupp` to a function type is an `add_monoid_hom`. -/
@[simps]
noncomputable def coe_fn_add_hom : (α →₀ M) →+ (α → M) :=
{ to_fun := coe_fn,
  map_zero' := coe_zero,
  map_add' := coe_add }

lemma update_eq_single_add_erase (f : α →₀ M) (a : α) (b : M) :
  f.update a b = single a b + f.erase a :=
begin
  ext j,
  rcases eq_or_ne a j with rfl|h,
  { simp },
  { simp [function.update_noteq h.symm, single_apply, h, erase_ne, h.symm] }
end

lemma update_eq_erase_add_single (f : α →₀ M) (a : α) (b : M) :
  f.update a b = f.erase a + single a b :=
begin
  ext j,
  rcases eq_or_ne a j with rfl|h,
  { simp },
  { simp [function.update_noteq h.symm, single_apply, h, erase_ne, h.symm] }
end

lemma single_add_erase (a : α) (f : α →₀ M) : single a (f a) + f.erase a = f :=
by rw [←update_eq_single_add_erase, update_self]

lemma erase_add_single (a : α) (f : α →₀ M) : f.erase a + single a (f a) = f :=
by rw [←update_eq_erase_add_single, update_self]

@[simp] lemma erase_add (a : α) (f f' : α →₀ M) : erase a (f + f') = erase a f + erase a f' :=
begin
  ext s, by_cases hs : s = a,
  { rw [hs, add_apply, erase_same, erase_same, erase_same, add_zero] },
  rw [add_apply, erase_ne hs, erase_ne hs, erase_ne hs, add_apply],
end

/-- `finsupp.erase` as an `add_monoid_hom`. -/
@[simps]
def erase_add_hom (a : α) : (α →₀ M) →+ (α →₀ M) :=
{ to_fun := erase a, map_zero' := erase_zero a, map_add' := erase_add a }

@[elab_as_eliminator]
protected theorem induction {p : (α →₀ M) → Prop} (f : α →₀ M)
  (h0 : p 0) (ha : ∀a b (f : α →₀ M), a ∉ f.support → b ≠ 0 → p f → p (single a b + f)) :
  p f :=
suffices ∀s (f : α →₀ M), f.support = s → p f, from this _ _ rfl,
assume s, finset.induction_on s (λ f hf, by rwa [support_eq_empty.1 hf]) $
assume a s has ih f hf,
suffices p (single a (f a) + f.erase a), by rwa [single_add_erase] at this,
begin
  apply ha,
  { rw [support_erase, mem_erase], exact λ H, H.1 rfl },
  { rw [← mem_support_iff, hf], exact mem_insert_self _ _ },
  { apply ih _ _,
    rw [support_erase, hf, finset.erase_insert has] }
end

lemma induction₂ {p : (α →₀ M) → Prop} (f : α →₀ M)
  (h0 : p 0) (ha : ∀a b (f : α →₀ M), a ∉ f.support → b ≠ 0 → p f → p (f + single a b)) :
  p f :=
suffices ∀s (f : α →₀ M), f.support = s → p f, from this _ _ rfl,
assume s, finset.induction_on s (λ f hf, by rwa [support_eq_empty.1 hf]) $
assume a s has ih f hf,
suffices p (f.erase a + single a (f a)), by rwa [erase_add_single] at this,
begin
  apply ha,
  { rw [support_erase, mem_erase], exact λ H, H.1 rfl },
  { rw [← mem_support_iff, hf], exact mem_insert_self _ _ },
  { apply ih _ _,
    rw [support_erase, hf, finset.erase_insert has] }
end

lemma induction_linear {p : (α →₀ M) → Prop} (f : α →₀ M)
  (h0 : p 0) (hadd : ∀ f g : α →₀ M, p f → p g → p (f + g)) (hsingle : ∀ a b, p (single a b)) :
  p f :=
induction₂ f h0 (λ a b f _ _ w, hadd _ _ w (hsingle _ _))

@[simp] lemma add_closure_set_of_eq_single :
  add_submonoid.closure {f : α →₀ M | ∃ a b, f = single a b} = ⊤ :=
top_unique $ λ x hx, finsupp.induction x (add_submonoid.zero_mem _) $
  λ a b f ha hb hf, add_submonoid.add_mem _
    (add_submonoid.subset_closure $ ⟨a, b, rfl⟩) hf

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`, then
they are equal. -/
lemma add_hom_ext [add_zero_class N] ⦃f g : (α →₀ M) →+ N⦄
  (H : ∀ x y, f (single x y) = g (single x y)) :
  f = g :=
begin
  refine add_monoid_hom.eq_of_eq_on_mdense add_closure_set_of_eq_single _,
  rintro _ ⟨x, y, rfl⟩,
  apply H
end

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`, then
they are equal.

We formulate this using equality of `add_monoid_hom`s so that `ext` tactic can apply a type-specific
extensionality lemma after this one.  E.g., if the fiber `M` is `ℕ` or `ℤ`, then it suffices to
verify `f (single a 1) = g (single a 1)`. -/
@[ext] lemma add_hom_ext' [add_zero_class N] ⦃f g : (α →₀ M) →+ N⦄
  (H : ∀ x, f.comp (single_add_hom x) = g.comp (single_add_hom x)) :
  f = g :=
add_hom_ext $ λ x, add_monoid_hom.congr_fun (H x)

lemma mul_hom_ext [mul_one_class N] ⦃f g : multiplicative (α →₀ M) →* N⦄
  (H : ∀ x y, f (multiplicative.of_add $ single x y) = g (multiplicative.of_add $ single x y)) :
  f = g :=
monoid_hom.ext $ add_monoid_hom.congr_fun $
  @add_hom_ext α M (additive N) _ _ f.to_additive'' g.to_additive'' H

@[ext] lemma mul_hom_ext' [mul_one_class N] {f g : multiplicative (α →₀ M) →* N}
  (H : ∀ x, f.comp (single_add_hom x).to_multiplicative =
    g.comp (single_add_hom x).to_multiplicative) :
  f = g :=
mul_hom_ext $ λ x, monoid_hom.congr_fun (H x)

lemma map_range_add [add_zero_class N]
  {f : M → N} {hf : f 0 = 0} (hf' : ∀ x y, f (x + y) = f x + f y) (v₁ v₂ : α →₀ M) :
  map_range f hf (v₁ + v₂) = map_range f hf v₁ + map_range f hf v₂ :=
ext $ λ a, by simp only [hf', add_apply, map_range_apply]

/-- Bundle `emb_domain f` as an additive map from `α →₀ M` to `β →₀ M`. -/
@[simps] def emb_domain.add_monoid_hom (f : α ↪ β) : (α →₀ M) →+ β →₀ M :=
{ to_fun := λ v, emb_domain f v,
  map_zero' := by simp,
  map_add' := λ v w,
  begin
    ext b,
    by_cases h : b ∈ set.range f,
    { rcases h with ⟨a, rfl⟩,
      simp, },
    { simp [emb_domain_notin_range, h], },
  end, }

@[simp] lemma emb_domain_add (f : α ↪ β) (v w : α →₀ M) :
  emb_domain f (v + w) = emb_domain f v + emb_domain f w :=
(emb_domain.add_monoid_hom f).map_add v w

end add_zero_class

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- section add_zero_class  ^^^^^
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------



section add_monoid

variables [add_monoid M]

/-- Note the general `finsupp.has_smul` instance doesn't apply as `ℕ` is not distributive
unless `β i`'s addition is commutative. -/
instance has_nat_scalar : has_smul ℕ (α →₀ M) :=
⟨λ n v, v.map_range ((•) n) (nsmul_zero _)⟩

instance : add_monoid (α →₀ M) :=
fun_like.coe_injective.add_monoid _ coe_zero coe_add (λ _ _, rfl)

end add_monoid

instance [add_comm_monoid M] : add_comm_monoid (α →₀ M) :=
fun_like.coe_injective.add_comm_monoid _ coe_zero coe_add (λ _ _, rfl)

instance [add_group G] : has_neg (α →₀ G) := ⟨map_range (has_neg.neg) neg_zero⟩

@[simp] lemma coe_neg [add_group G] (g : α →₀ G) : ⇑(-g) = -g := rfl
lemma neg_apply [add_group G] (g : α →₀ G) (a : α) : (- g) a = - g a := rfl

instance [add_group G] : has_sub (α →₀ G) := ⟨zip_with has_sub.sub (sub_zero _)⟩

@[simp] lemma coe_sub [add_group G] (g₁ g₂ : α →₀ G) : ⇑(g₁ - g₂) = g₁ - g₂ := rfl
lemma sub_apply [add_group G] (g₁ g₂ : α →₀ G) (a : α) : (g₁ - g₂) a = g₁ a - g₂ a := rfl

/-- Note the general `finsupp.has_smul` instance doesn't apply as `ℤ` is not distributive
unless `β i`'s addition is commutative. -/
instance has_int_scalar [add_group G] : has_smul ℤ (α →₀ G) :=
⟨λ n v, v.map_range ((•) n) (zsmul_zero _)⟩

instance [add_group G] : add_group (α →₀ G) :=
fun_like.coe_injective.add_group _ coe_zero coe_add coe_neg coe_sub (λ _ _, rfl) (λ _ _, rfl)

instance [add_comm_group G] : add_comm_group (α →₀ G) :=
fun_like.coe_injective.add_comm_group _ coe_zero coe_add coe_neg coe_sub (λ _ _, rfl) (λ _ _, rfl)

lemma single_add_single_eq_single_add_single [add_comm_monoid M]
  {k l m n : α} {u v : M} (hu : u ≠ 0) (hv : v ≠ 0) :
  single k u + single l v = single m u + single n v ↔
  (k = m ∧ l = n) ∨ (u = v ∧ k = n ∧ l = m) ∨ (u + v = 0 ∧ k = l ∧ m = n) :=
begin
  simp_rw [fun_like.ext_iff, coe_add, single_eq_pi_single, ←funext_iff],
  exact pi.single_add_single_eq_single_add_single hu hv,
end

@[simp] lemma support_neg [add_group G] (f : α →₀ G) : support (-f) = support f :=
finset.subset.antisymm
  support_map_range
  (calc support f = support (- (- f)) : congr_arg support (neg_neg _).symm
     ... ⊆ support (- f) : support_map_range)

lemma support_sub [decidable_eq α] [add_group G] {f g : α →₀ G} :
  support (f - g) ⊆ support f ∪ support g :=
begin
  rw [sub_eq_add_neg, ←support_neg g],
  exact support_add,
end

lemma erase_eq_sub_single [add_group G] (f : α →₀ G) (a : α) :
  f.erase a = f - single a (f a) :=
begin
  ext a',
  rcases eq_or_ne a a' with rfl|h,
  { simp },
  { simp [erase_ne h.symm, single_eq_of_ne h] }
end

lemma update_eq_sub_add_single [add_group G] (f : α →₀ G) (a : α) (b : G) :
  f.update a b = f - single a (f a) + single a b :=
by rw [update_eq_erase_add_single, erase_eq_sub_single]




--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Start of main `sum` and `prod` definitions
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

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
by { convert f.sum_ite_eq a (λ x, id), simp [ite_eq_right_iff.2 eq.symm] }

/-- A restatement of `prod_ite_eq` with the equality test reversed. -/
@[simp, to_additive "A restatement of `sum_ite_eq` with the equality test reversed."]
lemma prod_ite_eq' [decidable_eq α] (f : α →₀ M) (a : α) (b : α → M → N) :
  f.prod (λ x v, ite (x = a) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 :=
by { dsimp [finsupp.prod], rw f.support.prod_ite_eq', }

@[simp] lemma sum_ite_self_eq'
  [decidable_eq α] {N : Type*} [add_comm_monoid N] (f : α →₀ N) (a : α) :
  f.sum (λ x v, ite (x = a) v 0) = f a :=
by { convert f.sum_ite_eq' a (λ x, id), simp [ite_eq_right_iff.2 eq.symm] }

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
lemma prod_add_index [add_zero_class M] [comm_monoid N] {f g : α →₀ M}
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
prod_add_index (λ a ha, h_zero a) (λ a ha, h_add a)

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
finset.induction_on s rfl $ λ a s has ih,
by rw [prod_insert has, ih, sum_insert has, prod_add_index' h_zero h_add]

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

lemma support_sum_eq_bUnion {α : Type*} {ι : Type*} {M : Type*} [add_comm_monoid M]
  {g : ι → α →₀ M} (s : finset ι) (h : ∀ i₁ i₂, i₁ ≠ i₂ → disjoint (g i₁).support (g i₂).support) :
  (∑ i in s, g i).support = s.bUnion (λ i, (g i).support) :=
begin
  apply finset.induction_on s,
  { simp },
  { intros i s hi,
    simp only [hi, sum_insert, not_false_iff, bUnion_insert],
    intro hs,
    rw [finsupp.support_add_eq, hs],
    rw [hs],
    intros x hx,
    simp only [mem_bUnion, exists_prop, inf_eq_inter, ne.def, mem_inter] at hx,
    obtain ⟨hxi, j, hj, hxj⟩ := hx,
    have hn : i ≠ j := λ H, hi (H.symm ▸ hj),
    apply h _ _ hn,
    simp [hxi, hxj] }
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
by simp_rw [← this hd, ← this hd.symm,
  add_comm (f2 _), finsupp.prod, support_add_eq hd, prod_union hd, add_apply]


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- End of main `sum` and `prod` definitions
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

end finsupp
