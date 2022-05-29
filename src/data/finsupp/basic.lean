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
* `finsupp.map_range`: Composition of a `zero_hom` with a`finsupp`.
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

lemma single_eq_update [decidable_eq α] : ⇑(single a b) = function.update 0 a b :=
by rw [single_eq_indicator, ← set.piecewise_eq_indicator, set.piecewise_singleton]

lemma single_eq_pi_single [decidable_eq α] : ⇑(single a b) = pi.single a b :=
single_eq_update

@[simp] lemma single_zero : (single a 0 : α →₀ M) = 0 :=
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

lemma support_single_ne_zero (hb : b ≠ 0) : (single a b).support = {a} :=
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
by simpa only [support_single_ne_zero h] using singleton_ne_empty _

lemma support_single_disjoint [decidable_eq α] {b' : M} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : α} :
  disjoint (single i b).support (single j b').support ↔ i ≠ j :=
by rw [support_single_ne_zero hb, support_single_ne_zero hb', disjoint_singleton]

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
  eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩, λ h, h.2.symm ▸ support_single_ne_zero h.1⟩

lemma support_eq_singleton' {f : α →₀ M} {a : α} :
  f.support = {a} ↔ ∃ b ≠ 0, f = single a b :=
⟨λ h, let h := support_eq_singleton.1 h in ⟨_, h.1, h.2⟩,
  λ ⟨b, hb, hf⟩, hf.symm ▸ support_single_ne_zero hb⟩

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
    by rw [←support_emb_domain, h, support_single_ne_zero hb]; refl,
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
  prod_of_support_subset _ support_single_subset h $ λ x hx, (mem_singleton.1 hx).symm ▸ h_zero
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

@[simp] lemma single_add {a : α} {b₁ b₂ : M} : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
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
⟨single a, single_zero, λ _ _, single_add⟩

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

section add_monoid

variables [add_monoid M]

/-- Note the general `finsupp.has_scalar` instance doesn't apply as `ℕ` is not distributive
unless `β i`'s addition is commutative. -/
instance has_nat_scalar : has_scalar ℕ (α →₀ M) :=
⟨λ n v, v.map_range ((•) n) (nsmul_zero _)⟩

instance : add_monoid (α →₀ M) :=
fun_like.coe_injective.add_monoid _ coe_zero coe_add (λ _ _, rfl)

end add_monoid

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

instance [add_comm_monoid M] : add_comm_monoid (α →₀ M) :=
fun_like.coe_injective.add_comm_monoid _ coe_zero coe_add (λ _ _, rfl)

instance [add_group G] : has_neg (α →₀ G) := ⟨map_range (has_neg.neg) neg_zero⟩

@[simp] lemma coe_neg [add_group G] (g : α →₀ G) : ⇑(-g) = -g := rfl
lemma neg_apply [add_group G] (g : α →₀ G) (a : α) : (- g) a = - g a := rfl

instance [add_group G] : has_sub (α →₀ G) := ⟨zip_with has_sub.sub (sub_zero _)⟩

@[simp] lemma coe_sub [add_group G] (g₁ g₂ : α →₀ G) : ⇑(g₁ - g₂) = g₁ - g₂ := rfl
lemma sub_apply [add_group G] (g₁ g₂ : α →₀ G) (a : α) : (g₁ - g₂) a = g₁ a - g₂ a := rfl

/-- Note the general `finsupp.has_scalar` instance doesn't apply as `ℤ` is not distributive
unless `β i`'s addition is commutative. -/
instance has_int_scalar [add_group G] : has_scalar ℤ (α →₀ G) :=
⟨λ n v, v.map_range ((•) n) (zsmul_zero _)⟩

instance [add_group G] : add_group (α →₀ G) :=
fun_like.coe_injective.add_group _ coe_zero coe_add coe_neg coe_sub (λ _ _, rfl) (λ _ _, rfl)

instance [add_comm_group G] : add_comm_group (α →₀ G) :=
fun_like.coe_injective.add_comm_group _ coe_zero coe_add coe_neg coe_sub (λ _ _, rfl) (λ _ _, rfl)

lemma single_multiset_sum [add_comm_monoid M] (s : multiset M) (a : α) :
  single a s.sum = (s.map (single a)).sum :=
multiset.induction_on s single_zero $ λ a s ih,
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
lemma prod_add_index_of_disjoint [add_comm_monoid M] {f1 f2 : α →₀ M}
  (hd : disjoint f1.support f2.support) {β : Type*} [comm_monoid β] (g : α → M → β) :
  (f1 + f2).prod g = f1.prod g * f2.prod g :=
have ∀ {f1 f2 : α →₀ M}, disjoint f1.support f2.support →
  ∏ x in f1.support, g x (f1 x + f2 x) = f1.prod g :=
  λ f1 f2 hd, finset.prod_congr rfl (λ x hx,
    by simp only [not_mem_support_iff.mp (disjoint_left.mp hd hx), add_zero]),
by simp_rw [← this hd, ← this hd.symm,
  add_comm (f2 _), finsupp.prod, support_add_eq hd, prod_union hd, add_apply]

section map_range

section equiv
variables [has_zero M] [has_zero N] [has_zero P]

/-- `finsupp.map_range` as an equiv. -/
@[simps apply]
def map_range.equiv (f : M ≃ N) (hf : f 0 = 0) (hf' : f.symm 0 = 0) : (α →₀ M) ≃ (α →₀ N) :=
{ to_fun := (map_range f hf : (α →₀ M) → (α →₀ N)),
  inv_fun := (map_range f.symm hf' : (α →₀ N) → (α →₀ M)),
  left_inv := λ x, begin
    rw ←map_range_comp _ _ _ _; simp_rw equiv.symm_comp_self,
    { exact map_range_id _ },
    { refl },
  end,
  right_inv := λ x, begin
    rw ←map_range_comp _ _ _ _; simp_rw equiv.self_comp_symm,
    { exact map_range_id _ },
    { refl },
  end }

@[simp]
lemma map_range.equiv_refl :
  map_range.equiv (equiv.refl M) rfl rfl = equiv.refl (α →₀ M) :=
equiv.ext map_range_id

lemma map_range.equiv_trans
  (f : M ≃ N) (hf : f 0 = 0) (hf') (f₂ : N ≃ P) (hf₂ : f₂ 0 = 0) (hf₂') :
  (map_range.equiv (f.trans f₂) (by rw [equiv.trans_apply, hf, hf₂])
    (by rw [equiv.symm_trans_apply, hf₂', hf']) : (α →₀ _) ≃ _) =
    (map_range.equiv f hf hf').trans (map_range.equiv f₂ hf₂ hf₂') :=
equiv.ext $ map_range_comp _ _ _ _ _

@[simp] lemma map_range.equiv_symm (f : M ≃ N) (hf hf') :
  ((map_range.equiv f hf hf').symm : (α →₀ _) ≃ _) = map_range.equiv f.symm hf' hf :=
equiv.ext $ λ x, rfl

end equiv

section zero_hom
variables [has_zero M] [has_zero N] [has_zero P]

/-- Composition with a fixed zero-preserving homomorphism is itself an zero-preserving homomorphism
on functions. -/
@[simps]
def map_range.zero_hom (f : zero_hom M N) : zero_hom (α →₀ M) (α →₀ N) :=
{ to_fun := (map_range f f.map_zero : (α →₀ M) → (α →₀ N)),
  map_zero' := map_range_zero }

@[simp]
lemma map_range.zero_hom_id :
  map_range.zero_hom (zero_hom.id M) = zero_hom.id (α →₀ M) := zero_hom.ext map_range_id

lemma map_range.zero_hom_comp (f : zero_hom N P) (f₂ : zero_hom M N) :
  (map_range.zero_hom (f.comp f₂) : zero_hom (α →₀ _) _) =
    (map_range.zero_hom f).comp (map_range.zero_hom f₂) :=
zero_hom.ext $ map_range_comp _ _ _ _ _

end zero_hom

section add_monoid_hom
variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P]

/--
Composition with a fixed additive homomorphism is itself an additive homomorphism on functions.
-/
@[simps]
def map_range.add_monoid_hom (f : M →+ N) : (α →₀ M) →+ (α →₀ N) :=
{ to_fun := (map_range f f.map_zero : (α →₀ M) → (α →₀ N)),
  map_zero' := map_range_zero,
  map_add' := λ a b, map_range_add f.map_add _ _ }

@[simp]
lemma map_range.add_monoid_hom_id :
  map_range.add_monoid_hom (add_monoid_hom.id M) = add_monoid_hom.id (α →₀ M) :=
add_monoid_hom.ext map_range_id

lemma map_range.add_monoid_hom_comp (f : N →+ P) (f₂ : M →+ N) :
  (map_range.add_monoid_hom (f.comp f₂) : (α →₀ _) →+ _) =
    (map_range.add_monoid_hom f).comp (map_range.add_monoid_hom f₂) :=
add_monoid_hom.ext $ map_range_comp _ _ _ _ _

@[simp]
lemma map_range.add_monoid_hom_to_zero_hom (f : M →+ N) :
  (map_range.add_monoid_hom f).to_zero_hom =
    (map_range.zero_hom f.to_zero_hom : zero_hom (α →₀ _) _) :=
zero_hom.ext $ λ _, rfl

lemma map_range_multiset_sum (f : M →+ N) (m : multiset (α →₀ M)) :
  map_range f f.map_zero m.sum = (m.map $ λx, map_range f f.map_zero x).sum :=
(map_range.add_monoid_hom f : (α →₀ _) →+ _).map_multiset_sum _

lemma map_range_finset_sum (f : M →+ N) (s : finset ι) (g : ι → (α →₀ M))  :
  map_range f f.map_zero (∑ x in s, g x) = ∑ x in s, map_range f f.map_zero (g x) :=
(map_range.add_monoid_hom f : (α →₀ _) →+ _).map_sum _ _


/-- `finsupp.map_range.add_monoid_hom` as an equiv. -/
@[simps apply]
def map_range.add_equiv (f : M ≃+ N) : (α →₀ M) ≃+ (α →₀ N) :=
{ to_fun := (map_range f f.map_zero : (α →₀ M) → (α →₀ N)),
  inv_fun := (map_range f.symm f.symm.map_zero : (α →₀ N) → (α →₀ M)),
  left_inv := λ x, begin
    rw ←map_range_comp _ _ _ _; simp_rw add_equiv.symm_comp_self,
    { exact map_range_id _ },
    { refl },
  end,
  right_inv := λ x, begin
    rw ←map_range_comp _ _ _ _; simp_rw add_equiv.self_comp_symm,
    { exact map_range_id _ },
    { refl },
  end,
  ..(map_range.add_monoid_hom f.to_add_monoid_hom) }

@[simp]
lemma map_range.add_equiv_refl :
  map_range.add_equiv (add_equiv.refl M) = add_equiv.refl (α →₀ M) :=
add_equiv.ext map_range_id

lemma map_range.add_equiv_trans (f : M ≃+ N) (f₂ : N ≃+ P) :
  (map_range.add_equiv (f.trans f₂) : (α →₀ _) ≃+ _) =
    (map_range.add_equiv f).trans (map_range.add_equiv f₂) :=
add_equiv.ext $ map_range_comp _ _ _ _ _

@[simp] lemma map_range.add_equiv_symm (f : M ≃+ N) :
  ((map_range.add_equiv f).symm : (α →₀ _) ≃+ _) = map_range.add_equiv f.symm :=
add_equiv.ext $ λ x, rfl

@[simp]
lemma map_range.add_equiv_to_add_monoid_hom (f : M ≃+ N) :
  (map_range.add_equiv f : (α →₀ _) ≃+ _).to_add_monoid_hom =
    (map_range.add_monoid_hom f.to_add_monoid_hom : (α →₀ _) →+ _) :=
add_monoid_hom.ext $ λ _, rfl

@[simp]
lemma map_range.add_equiv_to_equiv (f : M ≃+ N) :
  (map_range.add_equiv f).to_equiv =
    (map_range.equiv f.to_equiv f.map_zero f.symm.map_zero : (α →₀ _) ≃ _) :=
equiv.ext $ λ _, rfl

end add_monoid_hom

end map_range

/-! ### Declarations about `map_domain` -/

section map_domain
variables [add_comm_monoid M] {v v₁ v₂ : α →₀ M}

/-- Given `f : α → β` and `v : α →₀ M`, `map_domain f v : β →₀ M`
  is the finitely supported function whose value at `a : β` is the sum
  of `v x` over all `x` such that `f x = a`. -/
def map_domain (f : α → β) (v : α →₀ M) : β →₀ M :=
v.sum $ λa, single (f a)

lemma map_domain_apply {f : α → β} (hf : function.injective f) (x : α →₀ M) (a : α) :
  map_domain f x (f a) = x a :=
begin
  rw [map_domain, sum_apply, sum, finset.sum_eq_single a, single_eq_same],
  { assume b _ hba, exact single_eq_of_ne (hf.ne hba) },
  { assume h, rw [not_mem_support_iff.1 h, single_zero, zero_apply] }
end

lemma map_domain_notin_range {f : α → β} (x : α →₀ M) (a : β) (h : a ∉ set.range f) :
  map_domain f x a = 0 :=
begin
  rw [map_domain, sum_apply, sum],
  exact finset.sum_eq_zero
    (assume a' h', single_eq_of_ne $ assume eq, h $ eq ▸ set.mem_range_self _)
end

@[simp]
lemma map_domain_id : map_domain id v = v :=
sum_single _

lemma map_domain_comp {f : α → β} {g : β → γ} :
  map_domain (g ∘ f) v = map_domain g (map_domain f v) :=
begin
  refine ((sum_sum_index _ _).trans _).symm,
  { intros, exact single_zero },
  { intros, exact single_add },
  refine sum_congr (λ _ _, sum_single_index _),
  { exact single_zero }
end

@[simp]
lemma map_domain_single {f : α → β} {a : α} {b : M} : map_domain f (single a b) = single (f a) b :=
sum_single_index single_zero

@[simp] lemma map_domain_zero {f : α → β} : map_domain f (0 : α →₀ M) = (0 : β →₀ M) :=
sum_zero_index

lemma map_domain_congr {f g : α → β} (h : ∀x∈v.support, f x = g x) :
  v.map_domain f = v.map_domain g :=
finset.sum_congr rfl $ λ _ H, by simp only [h _ H]

lemma map_domain_add {f : α → β} : map_domain f (v₁ + v₂) = map_domain f v₁ + map_domain f v₂ :=
sum_add_index' (λ _, single_zero) (λ _ _ _, single_add)

@[simp] lemma map_domain_equiv_apply {f : α ≃ β} (x : α →₀ M) (a : β) :
  map_domain f x a = x (f.symm a) :=
begin
  conv_lhs { rw ←f.apply_symm_apply a },
  exact map_domain_apply f.injective _ _,
end

/-- `finsupp.map_domain` is an `add_monoid_hom`. -/
@[simps]
def map_domain.add_monoid_hom (f : α → β) : (α →₀ M) →+ (β →₀ M) :=
{ to_fun := map_domain f,
  map_zero' := map_domain_zero,
  map_add' := λ _ _, map_domain_add}

@[simp]
lemma map_domain.add_monoid_hom_id : map_domain.add_monoid_hom id = add_monoid_hom.id (α →₀ M) :=
add_monoid_hom.ext $ λ _, map_domain_id

lemma map_domain.add_monoid_hom_comp (f : β → γ) (g : α → β) :
  (map_domain.add_monoid_hom (f ∘ g) : (α →₀ M) →+ (γ →₀ M)) =
    (map_domain.add_monoid_hom f).comp (map_domain.add_monoid_hom g) :=
add_monoid_hom.ext $ λ _, map_domain_comp

lemma map_domain_finset_sum {f : α → β} {s : finset ι} {v : ι → α →₀ M} :
  map_domain f (∑ i in s, v i) = ∑ i in s, map_domain f (v i) :=
(map_domain.add_monoid_hom f : (α →₀ M) →+ β →₀ M).map_sum _ _

lemma map_domain_sum [has_zero N] {f : α → β} {s : α →₀ N} {v : α → N → α →₀ M} :
  map_domain f (s.sum v) = s.sum (λa b, map_domain f (v a b)) :=
(map_domain.add_monoid_hom f : (α →₀ M) →+ β →₀ M).map_finsupp_sum _ _

lemma map_domain_support [decidable_eq β] {f : α → β} {s : α →₀ M} :
  (s.map_domain f).support ⊆ s.support.image f :=
finset.subset.trans support_sum $
  finset.subset.trans (finset.bUnion_mono $ assume a ha, support_single_subset) $
  by rw [finset.bUnion_singleton]; exact subset.refl _

lemma map_domain_apply' (S : set α) {f : α → β} (x : α →₀ M)
  (hS : (x.support : set α) ⊆ S) (hf : set.inj_on f S) {a : α} (ha : a ∈ S) :
  map_domain f x (f a) = x a :=
begin
  rw [map_domain, sum_apply, sum],
  simp_rw single_apply,
  have : ∀ (b : α) (ha1 : b ∈ x.support),
    (if f b = f a then x b else 0) = if f b = f a then x a else 0,
  { intros b hb,
    refine if_ctx_congr iff.rfl (λ hh, _) (λ _, rfl),
    rw hf (hS hb) ha hh, },
  conv in (ite _ _ _)
  { rw [this _ H], },
  by_cases ha : a ∈ x.support,
  { rw [← finset.add_sum_erase _ _ ha, if_pos rfl],
    convert add_zero _,
    have : ∀ i ∈ x.support.erase a, f i ≠ f a,
    { intros i hi,
      exact (finset.ne_of_mem_erase hi) ∘ (hf (hS $ finset.mem_of_mem_erase hi) (hS ha)), },
    conv in (ite _ _ _)
    { rw if_neg (this x H), },
    exact finset.sum_const_zero, },
  { rw [mem_support_iff, not_not] at ha,
    simp [ha], }
end

lemma map_domain_support_of_inj_on [decidable_eq β] {f : α → β} (s : α →₀ M)
  (hf : set.inj_on f s.support) : (map_domain f s).support = finset.image f s.support :=
finset.subset.antisymm map_domain_support $ begin
  intros x hx,
  simp only [mem_image, exists_prop, mem_support_iff, ne.def] at hx,
  rcases hx with ⟨hx_w, hx_h_left, rfl⟩,
  simp only [mem_support_iff, ne.def],
  rw map_domain_apply' (↑s.support : set _) _ _ hf,
  { exact hx_h_left, },
  { simp only [mem_coe, mem_support_iff, ne.def],
    exact hx_h_left, },
  { exact subset.refl _, },
end

lemma map_domain_support_of_injective [decidable_eq β] {f : α → β} (hf : function.injective f)
  (s : α →₀ M) : (map_domain f s).support = finset.image f s.support :=
map_domain_support_of_inj_on s (hf.inj_on _)

@[to_additive]
lemma prod_map_domain_index [comm_monoid N] {f : α → β} {s : α →₀ M}
  {h : β → M → N} (h_zero : ∀b, h b 0 = 1) (h_add : ∀b m₁ m₂, h b (m₁ + m₂) = h b m₁ * h b m₂) :
  (map_domain f s).prod h = s.prod (λa m, h (f a) m) :=
(prod_sum_index h_zero h_add).trans $ prod_congr $ λ _ _, prod_single_index (h_zero _)

/--
A version of `sum_map_domain_index` that takes a bundled `add_monoid_hom`,
rather than separate linearity hypotheses.
-/
-- Note that in `prod_map_domain_index`, `M` is still an additive monoid,
-- so there is no analogous version in terms of `monoid_hom`.
@[simp]
lemma sum_map_domain_index_add_monoid_hom [add_comm_monoid N] {f : α → β}
  {s : α →₀ M} (h : β → M →+ N) :
  (map_domain f s).sum (λ b m, h b m) = s.sum (λ a m, h (f a) m) :=
@sum_map_domain_index _ _ _ _ _ _ _ _
  (λ b m, h b m)
  (λ b, (h b).map_zero)
  (λ b m₁ m₂, (h b).map_add _ _)

lemma emb_domain_eq_map_domain (f : α ↪ β) (v : α →₀ M) :
  emb_domain f v = map_domain f v :=
begin
  ext a,
  by_cases a ∈ set.range f,
  { rcases h with ⟨a, rfl⟩,
    rw [map_domain_apply f.injective, emb_domain_apply] },
  { rw [map_domain_notin_range, emb_domain_notin_range]; assumption }
end

@[to_additive]
lemma prod_map_domain_index_inj [comm_monoid N] {f : α → β} {s : α →₀ M}
  {h : β → M → N} (hf : function.injective f) :
  (s.map_domain f).prod h = s.prod (λa b, h (f a) b) :=
by rw [←function.embedding.coe_fn_mk f hf, ←emb_domain_eq_map_domain, prod_emb_domain]

lemma map_domain_injective {f : α → β} (hf : function.injective f) :
  function.injective (map_domain f : (α →₀ M) → (β →₀ M)) :=
begin
  assume v₁ v₂ eq, ext a,
  have : map_domain f v₁ (f a) = map_domain f v₂ (f a), { rw eq },
  rwa [map_domain_apply hf, map_domain_apply hf] at this,
end

/-- When `f` is an embedding we have an embedding `(α →₀ ℕ)  ↪ (β →₀ ℕ)` given by `map_domain`. -/
@[simps] def map_domain_embedding {α β : Type*} (f : α ↪ β) : (α →₀ ℕ) ↪ β →₀ ℕ :=
⟨finsupp.map_domain f, finsupp.map_domain_injective f.injective⟩

lemma map_domain.add_monoid_hom_comp_map_range [add_comm_monoid N] (f : α → β) (g : M →+ N) :
  (map_domain.add_monoid_hom f).comp (map_range.add_monoid_hom g) =
    (map_range.add_monoid_hom g).comp (map_domain.add_monoid_hom f) :=
by { ext, simp }

/-- When `g` preserves addition, `map_range` and `map_domain` commute. -/
lemma map_domain_map_range [add_comm_monoid N] (f : α → β) (v : α →₀ M) (g : M → N)
  (h0 : g 0 = 0) (hadd : ∀ x y, g (x + y) = g x + g y) :
  map_domain f (map_range g h0 v) = map_range g h0 (map_domain f v) :=
let g' : M →+ N := { to_fun := g, map_zero' := h0, map_add' := hadd} in
add_monoid_hom.congr_fun (map_domain.add_monoid_hom_comp_map_range f g') v

lemma sum_update_add [add_comm_monoid α] [add_comm_monoid β]
  (f : ι →₀ α) (i : ι) (a : α) (g : ι → α → β) (hg : ∀ i, g i 0 = 0)
  (hgg : ∀ (j : ι) (a₁ a₂ : α), g j (a₁ + a₂) = g j a₁ + g j a₂) :
  (f.update i a).sum g + g i (f i) = f.sum g + g i a :=
begin
  rw [update_eq_erase_add_single, sum_add_index' hg hgg],
  conv_rhs { rw ← finsupp.update_self f i },
  rw [update_eq_erase_add_single, sum_add_index' hg hgg, add_assoc, add_assoc],
  congr' 1,
  rw [add_comm, sum_single_index (hg _), sum_single_index (hg _)],
end

lemma map_domain_inj_on (S : set α) {f : α → β}
  (hf : set.inj_on f S) :
  set.inj_on (map_domain f : (α →₀ M) → (β →₀ M)) {w | (w.support : set α) ⊆ S} :=
begin
  intros v₁ hv₁ v₂ hv₂ eq,
  ext a,
  by_cases h : a ∈ v₁.support ∪ v₂.support,
  { rw [← map_domain_apply' S _ hv₁ hf _, ← map_domain_apply' S _ hv₂ hf _, eq];
    { apply set.union_subset hv₁ hv₂,
      exact_mod_cast h, }, },
  { simp only [decidable.not_or_iff_and_not, mem_union, not_not, mem_support_iff] at h,
    simp [h], },
end


end map_domain

/-! ### Declarations about `comap_domain` -/

section comap_domain

/-- Given `f : α → β`, `l : β →₀ M` and a proof `hf` that `f` is injective on
the preimage of `l.support`, `comap_domain f l hf` is the finitely supported function
from `α` to `M` given by composing `l` with `f`. -/
@[simps support]
def comap_domain [has_zero M] (f : α → β) (l : β →₀ M) (hf : set.inj_on f (f ⁻¹' ↑l.support)) :
  α →₀ M :=
{ support := l.support.preimage f hf,
  to_fun := (λ a, l (f a)),
  mem_support_to_fun :=
    begin
      intros a,
      simp only [finset.mem_def.symm, finset.mem_preimage],
      exact l.mem_support_to_fun (f a),
    end }

@[simp]
lemma comap_domain_apply [has_zero M] (f : α → β) (l : β →₀ M)
  (hf : set.inj_on f (f ⁻¹' ↑l.support)) (a : α) :
  comap_domain f l hf a = l (f a) :=
rfl

lemma sum_comap_domain [has_zero M] [add_comm_monoid N]
  (f : α → β) (l : β →₀ M) (g : β → M → N)
  (hf : set.bij_on f (f ⁻¹' ↑l.support) ↑l.support) :
  (comap_domain f l hf.inj_on).sum (g ∘ f) = l.sum g :=
begin
  simp only [sum, comap_domain_apply, (∘)],
  simp [comap_domain, finset.sum_preimage_of_bij f _ _ (λ x, g x (l x))],
end

lemma eq_zero_of_comap_domain_eq_zero [add_comm_monoid M]
  (f : α → β) (l : β →₀ M) (hf : set.bij_on f (f ⁻¹' ↑l.support) ↑l.support) :
   comap_domain f l hf.inj_on = 0 → l = 0 :=
begin
  rw [← support_eq_empty, ← support_eq_empty, comap_domain],
  simp only [finset.ext_iff, finset.not_mem_empty, iff_false, mem_preimage],
  assume h a ha,
  cases hf.2.2 ha with b hb,
  exact h b (hb.2.symm ▸ ha)
end

section f_injective

section has_zero
variables [has_zero M]

/-- Note the `hif` argument is needed for this to work in `rw`. -/
@[simp] lemma comap_domain_zero (f : α → β)
  (hif : set.inj_on f (f ⁻¹' ↑((0 : β →₀ M).support)) := set.inj_on_empty _) :
  comap_domain f (0 : β →₀ M) hif = (0 : α →₀ M) :=
by { ext, refl }

@[simp] lemma comap_domain_single (f : α → β) (a : α) (m : M)
  (hif : set.inj_on f (f ⁻¹' (single (f a) m).support)) :
  comap_domain f (finsupp.single (f a) m) hif = finsupp.single a m :=
begin
  rcases eq_or_ne m 0 with rfl | hm,
  { simp only [single_zero, comap_domain_zero] },
  { rw [eq_single_iff, comap_domain_apply, comap_domain_support, ← finset.coe_subset, coe_preimage,
      support_single_ne_zero hm, coe_singleton, coe_singleton, single_eq_same],
    rw [support_single_ne_zero hm, coe_singleton] at hif,
    exact ⟨λ x hx, hif hx rfl hx, rfl⟩ }
end

end has_zero

section add_zero_class
variables [add_zero_class M] {f : α → β}

lemma comap_domain_add (v₁ v₂ : β →₀ M)
  (hv₁ : set.inj_on f (f ⁻¹' ↑(v₁.support))) (hv₂ : set.inj_on f (f ⁻¹' ↑(v₂.support)))
  (hv₁₂ : set.inj_on f (f ⁻¹' ↑((v₁ + v₂).support))) :
  comap_domain f (v₁ + v₂) hv₁₂ = comap_domain f v₁ hv₁ + comap_domain f v₂ hv₂ :=
by { ext, simp only [comap_domain_apply, coe_add, pi.add_apply] }

/-- A version of `finsupp.comap_domain_add` that's easier to use. -/
lemma comap_domain_add_of_injective (hf : function.injective f) (v₁ v₂ : β →₀ M) :
  comap_domain f (v₁ + v₂) (hf.inj_on _)
    = comap_domain f v₁ (hf.inj_on _) + comap_domain f v₂ (hf.inj_on _) :=
comap_domain_add _ _ _ _ _

/-- `finsupp.comap_domain` is an `add_monoid_hom`. -/
@[simps]
def comap_domain.add_monoid_hom (hf : function.injective f) : (β →₀ M) →+ (α →₀ M) :=
{ to_fun := λ x, comap_domain f x (hf.inj_on _),
  map_zero' := comap_domain_zero f,
  map_add' := comap_domain_add_of_injective hf }

end add_zero_class

variables [add_comm_monoid M] (f : α → β)

lemma map_domain_comap_domain
  (hf : function.injective f) (l : β →₀ M) (hl : ↑l.support ⊆ set.range f) :
  map_domain f (comap_domain f l (hf.inj_on _)) = l :=
begin
  ext a,
  by_cases h_cases: a ∈ set.range f,
  { rcases set.mem_range.1 h_cases with ⟨b, hb⟩,
    rw [hb.symm, map_domain_apply hf, comap_domain_apply] },
  { rw map_domain_notin_range _ _ h_cases,
    by_contra h_contr,
    apply h_cases (hl $ finset.mem_coe.2 $ mem_support_iff.2 $ λ h, h_contr h.symm) }
end

end f_injective

end comap_domain

section option

/-- Restrict a finitely supported function on `option α` to a finitely supported function on `α`. -/
def some [has_zero M] (f : option α →₀ M) : α →₀ M :=
f.comap_domain option.some (λ _, by simp)

@[simp] lemma some_apply [has_zero M] (f : option α →₀ M) (a : α) :
  f.some a = f (option.some a) := rfl

@[simp] lemma some_zero [has_zero M] : (0 : option α →₀ M).some = 0 :=
by { ext, simp, }

@[simp] lemma some_add [add_comm_monoid M] (f g : option α →₀ M) : (f + g).some = f.some + g.some :=
by { ext, simp, }

@[simp] lemma some_single_none [has_zero M] (m : M) : (single none m : option α →₀ M).some = 0 :=
by { ext, simp, }

@[simp] lemma some_single_some [has_zero M] (a : α) (m : M) :
  (single (option.some a) m : option α →₀ M).some = single a m :=
by { ext b, simp [single_apply], }

@[to_additive]
lemma prod_option_index [add_comm_monoid M] [comm_monoid N]
  (f : option α →₀ M) (b : option α → M → N) (h_zero : ∀ o, b o 0 = 1)
  (h_add : ∀ o m₁ m₂, b o (m₁ + m₂) = b o m₁ * b o m₂) :
  f.prod b = b none (f none) * f.some.prod (λ a, b (option.some a)) :=
begin
  apply induction_linear f,
  { simp [h_zero], },
  { intros f₁ f₂ h₁ h₂,
    rw [finsupp.prod_add_index, h₁, h₂, some_add, finsupp.prod_add_index],
    simp only [h_add, pi.add_apply, finsupp.coe_add],
    rw mul_mul_mul_comm,
    all_goals { simp [h_zero, h_add], }, },
  { rintros (_|a) m; simp [h_zero, h_add], }
end

lemma sum_option_index_smul [semiring R] [add_comm_monoid M] [module R M]
  (f : option α →₀ R) (b : option α → M) :
  f.sum (λ o r, r • b o) =
    f none • b none + f.some.sum (λ a r, r • b (option.some a)) :=
f.sum_option_index _ (λ _, zero_smul _ _) (λ _ _ _, add_smul _ _ _)

end option

/-! ### Declarations about `equiv_congr_left` -/

section equiv_congr_left

variable [has_zero M]

/-- Given `f : α ≃ β`, we can map `l : α →₀ M` to  `equiv_map_domain f l : β →₀ M` (computably)
by mapping the support forwards and the function backwards. -/
def equiv_map_domain (f : α ≃ β) (l : α →₀ M) : β →₀ M :=
{ support := l.support.map f.to_embedding,
  to_fun := λ a, l (f.symm a),
  mem_support_to_fun := λ a, by simp only [finset.mem_map_equiv, mem_support_to_fun]; refl }

@[simp] lemma equiv_map_domain_apply (f : α ≃ β) (l : α →₀ M) (b : β) :
  equiv_map_domain f l b = l (f.symm b) := rfl

lemma equiv_map_domain_symm_apply (f : α ≃ β) (l : β →₀ M) (a : α) :
  equiv_map_domain f.symm l a = l (f a) := rfl

@[simp] lemma equiv_map_domain_refl (l : α →₀ M) : equiv_map_domain (equiv.refl _) l = l :=
by ext x; refl

lemma equiv_map_domain_refl' : equiv_map_domain (equiv.refl _) = @id (α →₀ M) :=
by ext x; refl

lemma equiv_map_domain_trans (f : α ≃ β) (g : β ≃ γ) (l : α →₀ M) :
  equiv_map_domain (f.trans g) l = equiv_map_domain g (equiv_map_domain f l) := by ext x; refl

lemma equiv_map_domain_trans' (f : α ≃ β) (g : β ≃ γ) :
  @equiv_map_domain _ _ M _ (f.trans g) = equiv_map_domain g ∘ equiv_map_domain f := by ext x; refl

@[simp] lemma equiv_map_domain_single (f : α ≃ β) (a : α) (b : M) :
  equiv_map_domain f (single a b) = single (f a) b :=
by ext x; simp only [single_apply, equiv.apply_eq_iff_eq_symm_apply, equiv_map_domain_apply]; congr

@[simp] lemma equiv_map_domain_zero {f : α ≃ β} : equiv_map_domain f (0 : α →₀ M) = (0 : β →₀ M) :=
by ext x; simp only [equiv_map_domain_apply, coe_zero, pi.zero_apply]

lemma equiv_map_domain_eq_map_domain {M} [add_comm_monoid M] (f : α ≃ β) (l : α →₀ M) :
  equiv_map_domain f l = map_domain f l := by ext x; simp [map_domain_equiv_apply]

/-- Given `f : α ≃ β`, the finitely supported function spaces are also in bijection:
`(α →₀ M) ≃ (β →₀ M)`.

This is the finitely-supported version of `equiv.Pi_congr_left`. -/
def equiv_congr_left (f : α ≃ β) : (α →₀ M) ≃ (β →₀ M) :=
by refine ⟨equiv_map_domain f, equiv_map_domain f.symm, λ f, _, λ f, _⟩;
  ext x; simp only [equiv_map_domain_apply, equiv.symm_symm,
    equiv.symm_apply_apply, equiv.apply_symm_apply]

@[simp] lemma equiv_congr_left_apply (f : α ≃ β) (l : α →₀ M) :
  equiv_congr_left f l = equiv_map_domain f l := rfl

@[simp] lemma equiv_congr_left_symm (f : α ≃ β) :
  (@equiv_congr_left _ _ M _ f).symm = equiv_congr_left f.symm := rfl

end equiv_congr_left

/-! ### Declarations about `filter` -/

section filter
section has_zero
variables [has_zero M] (p : α → Prop) (f : α →₀ M)

/-- `filter p f` is the function which is `f a` if `p a` is true and 0 otherwise. -/
def filter (p : α → Prop) (f : α →₀ M) : α →₀ M :=
{ to_fun := λ a, if p a then f a else 0,
  support := f.support.filter (λ a, p a),
  mem_support_to_fun := λ a, by split_ifs; { simp only [h, mem_filter, mem_support_iff], tauto } }

lemma filter_apply (a : α) [D : decidable (p a)] : f.filter p a = if p a then f a else 0 :=
by rw subsingleton.elim D; refl

lemma filter_eq_indicator : ⇑(f.filter p) = set.indicator {x | p x} f := rfl

lemma filter_eq_zero_iff : f.filter p = 0 ↔ ∀ x, p x → f x = 0 :=
by simp only [fun_like.ext_iff, filter_eq_indicator, zero_apply, set.indicator_apply_eq_zero,
  set.mem_set_of_eq]

lemma filter_eq_self_iff : f.filter p = f ↔ ∀ x, f x ≠ 0 → p x :=
by simp only [fun_like.ext_iff, filter_eq_indicator, set.indicator_apply_eq_self, set.mem_set_of_eq,
  not_imp_comm]

@[simp] lemma filter_apply_pos {a : α} (h : p a) : f.filter p a = f a :=
if_pos h

@[simp] lemma filter_apply_neg {a : α} (h : ¬ p a) : f.filter p a = 0 :=
if_neg h

@[simp] lemma support_filter [D : decidable_pred p] : (f.filter p).support = f.support.filter p :=
by rw subsingleton.elim D; refl

lemma filter_zero : (0 : α →₀ M).filter p = 0 :=
by rw [← support_eq_empty, support_filter, support_zero, finset.filter_empty]

@[simp] lemma filter_single_of_pos {a : α} {b : M} (h : p a) :
  (single a b).filter p = single a b :=
(filter_eq_self_iff _ _).2 $ λ x hx, (single_apply_ne_zero.1 hx).1.symm ▸ h

@[simp] lemma filter_single_of_neg {a : α} {b : M} (h : ¬ p a) : (single a b).filter p = 0 :=
(filter_eq_zero_iff _ _).2 $ λ x hpx, single_apply_eq_zero.2 $ λ hxa, absurd hpx (hxa.symm ▸ h)

@[to_additive] lemma prod_filter_index [comm_monoid N] (g : α → M → N) :
  (f.filter p).prod g = ∏ x in (f.filter p).support, g x (f x) :=
begin
  refine finset.prod_congr rfl (λ x hx, _),
  rw [support_filter, finset.mem_filter] at hx,
  rw [filter_apply_pos _ _ hx.2]
end

@[simp, to_additive] lemma prod_filter_mul_prod_filter_not [comm_monoid N] (g : α → M → N) :
  (f.filter p).prod g * (f.filter (λ a, ¬ p a)).prod g = f.prod g :=
by simp_rw [prod_filter_index, support_filter, prod_filter_mul_prod_filter_not, finsupp.prod]

@[simp, to_additive] lemma prod_div_prod_filter [comm_group G] (g : α → M → G) :
  f.prod g / (f.filter p).prod g = (f.filter (λ a, ¬p a)).prod g :=
div_eq_of_eq_mul' (prod_filter_mul_prod_filter_not _ _ _).symm

end has_zero

lemma filter_pos_add_filter_neg [add_zero_class M] (f : α →₀ M) (p : α → Prop) :
  f.filter p + f.filter (λa, ¬ p a) = f :=
coe_fn_injective $ set.indicator_self_add_compl {x | p x} f

end filter

/-! ### Declarations about `frange` -/

section frange
variables [has_zero M]

/-- `frange f` is the image of `f` on the support of `f`. -/
def frange (f : α →₀ M) : finset M := finset.image f f.support

theorem mem_frange {f : α →₀ M} {y : M} :
  y ∈ f.frange ↔ y ≠ 0 ∧ ∃ x, f x = y :=
finset.mem_image.trans
⟨λ ⟨x, hx1, hx2⟩, ⟨hx2 ▸ mem_support_iff.1 hx1, x, hx2⟩,
λ ⟨hy, x, hx⟩, ⟨x, mem_support_iff.2 (hx.symm ▸ hy), hx⟩⟩

theorem zero_not_mem_frange {f : α →₀ M} : (0:M) ∉ f.frange :=
λ H, (mem_frange.1 H).1 rfl

theorem frange_single {x : α} {y : M} : frange (single x y) ⊆ {y} :=
λ r hr, let ⟨t, ht1, ht2⟩ := mem_frange.1 hr in ht2 ▸
  (by rw single_apply at ht2 ⊢; split_ifs at ht2 ⊢; [exact finset.mem_singleton_self _, cc])

end frange

/-! ### Declarations about `subtype_domain` -/

section subtype_domain


section zero

variables [has_zero M] {p : α → Prop}

/-- `subtype_domain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
def subtype_domain (p : α → Prop) (f : α →₀ M) : (subtype p →₀ M) :=
⟨f.support.subtype p, f ∘ coe, λ a, by simp only [mem_subtype, mem_support_iff]⟩

@[simp] lemma support_subtype_domain [D : decidable_pred p] {f : α →₀ M} :
  (subtype_domain p f).support = f.support.subtype p :=
by rw subsingleton.elim D; refl

@[simp] lemma subtype_domain_apply {a : subtype p} {v : α →₀ M} :
  (subtype_domain p v) a = v (a.val) :=
rfl

@[simp] lemma subtype_domain_zero : subtype_domain p (0 : α →₀ M) = 0 :=
rfl

lemma subtype_domain_eq_zero_iff' {f : α →₀ M} :
  f.subtype_domain p = 0 ↔ ∀ x, p x → f x = 0 :=
by simp_rw [← support_eq_empty, support_subtype_domain, subtype_eq_empty, not_mem_support_iff]

lemma subtype_domain_eq_zero_iff {f : α →₀ M} (hf : ∀ x ∈ f.support , p x) :
  f.subtype_domain p = 0 ↔ f = 0 :=
subtype_domain_eq_zero_iff'.trans ⟨λ H, ext $ λ x,
  if hx : p x then H x hx else not_mem_support_iff.1 $ mt (hf x) hx, λ H x _, by simp [H]⟩

@[to_additive]
lemma prod_subtype_domain_index [comm_monoid N] {v : α →₀ M}
  {h : α → M → N} (hp : ∀x∈v.support, p x) :
  (v.subtype_domain p).prod (λa b, h a b) = v.prod h :=
prod_bij (λp _, p.val)
  (λ _, mem_subtype.1)
  (λ _ _, rfl)
  (λ _ _ _ _, subtype.eq)
  (λ b hb, ⟨⟨b, hp b hb⟩, mem_subtype.2 hb, rfl⟩)

end zero

section add_zero_class
variables [add_zero_class M] {p : α → Prop} {v v' : α →₀ M}

@[simp] lemma subtype_domain_add {v v' : α →₀ M} :
  (v + v').subtype_domain p = v.subtype_domain p + v'.subtype_domain p :=
ext $ λ _, rfl

/-- `subtype_domain` but as an `add_monoid_hom`. -/
def subtype_domain_add_monoid_hom : (α →₀ M) →+ subtype p →₀ M :=
{ to_fun := subtype_domain p,
  map_zero' := subtype_domain_zero,
  map_add' := λ _ _, subtype_domain_add }

/-- `finsupp.filter` as an `add_monoid_hom`. -/
def filter_add_hom (p : α → Prop) : (α →₀ M) →+ (α →₀ M) :=
{ to_fun := filter p,
  map_zero' := filter_zero p,
  map_add' := λ f g, coe_fn_injective $ set.indicator_add {x | p x} f g }

@[simp] lemma filter_add {v v' : α →₀ M} : (v + v').filter p = v.filter p + v'.filter p :=
(filter_add_hom p).map_add v v'

end add_zero_class

section comm_monoid
variables [add_comm_monoid M] {p : α → Prop}

lemma subtype_domain_sum {s : finset ι} {h : ι → α →₀ M} :
  (∑ c in s, h c).subtype_domain p = ∑ c in s, (h c).subtype_domain p :=
(subtype_domain_add_monoid_hom : _ →+ subtype p →₀ M).map_sum _ s

lemma subtype_domain_finsupp_sum [has_zero N] {s : β →₀ N} {h : β → N → α →₀ M} :
  (s.sum h).subtype_domain p = s.sum (λc d, (h c d).subtype_domain p) :=
subtype_domain_sum

lemma filter_sum (s : finset ι) (f : ι → α →₀ M) :
  (∑ a in s, f a).filter p = ∑ a in s, filter p (f a) :=
(filter_add_hom p : (α →₀ M) →+ _).map_sum f s

lemma filter_eq_sum (p : α → Prop) [D : decidable_pred p] (f : α →₀ M) :
  f.filter p = ∑ i in f.support.filter p, single i (f i) :=
(f.filter p).sum_single.symm.trans $ finset.sum_congr (by rw subsingleton.elim D; refl) $
  λ x hx, by rw [filter_apply_pos _ _ (mem_filter.1 hx).2]

end comm_monoid

section group
variables [add_group G] {p : α → Prop} {v v' : α →₀ G}

@[simp] lemma subtype_domain_neg : (- v).subtype_domain p = - v.subtype_domain p :=
ext $ λ _, rfl

@[simp] lemma subtype_domain_sub :
  (v - v').subtype_domain p = v.subtype_domain p - v'.subtype_domain p :=
ext $ λ _, rfl

@[simp] lemma single_neg {a : α} {b : G} : single a (-b) = -single a b :=
(single_add_hom a : G →+ _).map_neg b

@[simp] lemma single_sub {a : α} {b₁ b₂ : G} : single a (b₁ - b₂) = single a b₁ - single a b₂ :=
(single_add_hom a : G →+ _).map_sub b₁ b₂

@[simp] lemma erase_neg (a : α) (f : α →₀ G) : erase a (-f) = -erase a f :=
(erase_add_hom a : (_ →₀ G) →+ _).map_neg f

@[simp] lemma erase_sub (a : α) (f₁ f₂ : α →₀ G) : erase a (f₁ - f₂) = erase a f₁ - erase a f₂ :=
(erase_add_hom a : (_ →₀ G) →+ _).map_sub f₁ f₂

@[simp] lemma filter_neg (p : α → Prop) (f : α →₀ G) : filter p (-f) = -filter p f :=
(filter_add_hom p : (_ →₀ G) →+ _).map_neg f

@[simp] lemma filter_sub (p : α → Prop) (f₁ f₂ : α →₀ G) :
  filter p (f₁ - f₂) = filter p f₁ - filter p f₂ :=
(filter_add_hom p : (_ →₀ G) →+ _).map_sub f₁ f₂

end group

end subtype_domain

lemma mem_support_multiset_sum [add_comm_monoid M]
  {s : multiset (α →₀ M)} (a : α) :
  a ∈ s.sum.support → ∃f∈s, a ∈ (f : α →₀ M).support :=
multiset.induction_on s false.elim
  begin
    assume f s ih ha,
    by_cases a ∈ f.support,
    { exact ⟨f, multiset.mem_cons_self _ _, h⟩ },
    { simp only [multiset.sum_cons, mem_support_iff, add_apply,
        not_mem_support_iff.1 h, zero_add] at ha,
      rcases ih (mem_support_iff.2 ha) with ⟨f', h₀, h₁⟩,
      exact ⟨f', multiset.mem_cons_of_mem h₀, h₁⟩ }
  end

lemma mem_support_finset_sum [add_comm_monoid M]
  {s : finset ι} {h : ι → α →₀ M} (a : α) (ha : a ∈ (∑ c in s, h c).support) :
  ∃ c ∈ s, a ∈ (h c).support :=
let ⟨f, hf, hfa⟩ := mem_support_multiset_sum a ha in
let ⟨c, hc, eq⟩ := multiset.mem_map.1 hf in
⟨c, hc, eq.symm ▸ hfa⟩

/-! ### Declarations about `curry` and `uncurry` -/

section curry_uncurry

variables [add_comm_monoid M] [add_comm_monoid N]

/-- Given a finitely supported function `f` from a product type `α × β` to `γ`,
`curry f` is the "curried" finitely supported function from `α` to the type of
finitely supported functions from `β` to `γ`. -/
protected def curry (f : (α × β) →₀ M) : α →₀ (β →₀ M) :=
f.sum $ λp c, single p.1 (single p.2 c)

@[simp] lemma curry_apply (f : (α × β) →₀ M) (x : α) (y : β) :
  f.curry x y = f (x, y) :=
begin
  have : ∀ (b : α × β), single b.fst (single b.snd (f b)) x y = if b = (x, y) then f b else 0,
  { rintros ⟨b₁, b₂⟩,
    simp [single_apply, ite_apply, prod.ext_iff, ite_and],
    split_ifs; simp [single_apply, *] },
  rw [finsupp.curry, sum_apply, sum_apply, finsupp.sum, finset.sum_eq_single, this, if_pos rfl],
  { intros b hb b_ne, rw [this b, if_neg b_ne] },
  { intros hxy, rw [this (x, y), if_pos rfl, not_mem_support_iff.mp hxy] }
end

lemma sum_curry_index (f : (α × β) →₀ M) (g : α → β → M → N)
  (hg₀ : ∀ a b, g a b 0 = 0) (hg₁ : ∀a b c₀ c₁, g a b (c₀ + c₁) = g a b c₀ + g a b c₁) :
  f.curry.sum (λa f, f.sum (g a)) = f.sum (λp c, g p.1 p.2 c) :=
begin
  rw [finsupp.curry],
  transitivity,
  { exact sum_sum_index (assume a, sum_zero_index)
      (assume a b₀ b₁, sum_add_index' (assume a, hg₀ _ _) (assume c d₀ d₁, hg₁ _ _ _ _)) },
  congr, funext p c,
  transitivity,
  { exact sum_single_index sum_zero_index },
  exact sum_single_index (hg₀ _ _)
end

/-- Given a finitely supported function `f` from `α` to the type of
finitely supported functions from `β` to `M`,
`uncurry f` is the "uncurried" finitely supported function from `α × β` to `M`. -/
protected def uncurry (f : α →₀ (β →₀ M)) : (α × β) →₀ M :=
f.sum $ λa g, g.sum $ λb c, single (a, b) c

/-- `finsupp_prod_equiv` defines the `equiv` between `((α × β) →₀ M)` and `(α →₀ (β →₀ M))` given by
currying and uncurrying. -/
def finsupp_prod_equiv : ((α × β) →₀ M) ≃ (α →₀ (β →₀ M)) :=
by refine ⟨finsupp.curry, finsupp.uncurry, λ f, _, λ f, _⟩; simp only [
  finsupp.curry, finsupp.uncurry, sum_sum_index, sum_zero_index, sum_add_index,
  sum_single_index, single_zero, single_add, eq_self_iff_true, forall_true_iff,
  forall_3_true_iff, prod.mk.eta, (single_sum _ _ _).symm, sum_single]

lemma filter_curry (f : α × β →₀ M) (p : α → Prop) :
  (f.filter (λa:α×β, p a.1)).curry = f.curry.filter p :=
begin
  rw [finsupp.curry, finsupp.curry, finsupp.sum, finsupp.sum, filter_sum, support_filter,
    sum_filter],
  refine finset.sum_congr rfl _,
  rintros ⟨a₁, a₂⟩ ha,
  dsimp only,
  split_ifs,
  { rw [filter_apply_pos, filter_single_of_pos]; exact h },
  { rwa [filter_single_of_neg] }
end

lemma support_curry [decidable_eq α] (f : α × β →₀ M) :
  f.curry.support ⊆ f.support.image prod.fst :=
begin
  rw ← finset.bUnion_singleton,
  refine finset.subset.trans support_sum _,
  refine finset.bUnion_mono (assume a _, support_single_subset)
end

end curry_uncurry

section sum

/-- `finsupp.sum_elim f g` maps `inl x` to `f x` and `inr y` to `g y`. -/
def sum_elim {α β γ : Type*} [has_zero γ]
  (f : α →₀ γ) (g : β →₀ γ) : α ⊕ β →₀ γ :=
on_finset
  ((f.support.map ⟨_, sum.inl_injective⟩) ∪ g.support.map ⟨_, sum.inr_injective⟩)
  (sum.elim f g)
  (λ ab h, by { cases ab with a b; simp only [sum.elim_inl, sum.elim_inr] at h; simpa })

@[simp] lemma coe_sum_elim {α β γ : Type*} [has_zero γ]
  (f : α →₀ γ) (g : β →₀ γ) : ⇑(sum_elim f g) = sum.elim f g := rfl

lemma sum_elim_apply {α β γ : Type*} [has_zero γ]
  (f : α →₀ γ) (g : β →₀ γ) (x : α ⊕ β) : sum_elim f g x = sum.elim f g x := rfl

lemma sum_elim_inl {α β γ : Type*} [has_zero γ]
  (f : α →₀ γ) (g : β →₀ γ) (x : α) : sum_elim f g (sum.inl x) = f x := rfl

lemma sum_elim_inr {α β γ : Type*} [has_zero γ]
  (f : α →₀ γ) (g : β →₀ γ) (x : β) : sum_elim f g (sum.inr x) = g x := rfl

/-- The equivalence between `(α ⊕ β) →₀ γ` and `(α →₀ γ) × (β →₀ γ)`.

This is the `finsupp` version of `equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps apply symm_apply]
def sum_finsupp_equiv_prod_finsupp {α β γ : Type*} [has_zero γ] :
  ((α ⊕ β) →₀ γ) ≃ (α →₀ γ) × (β →₀ γ) :=
{ to_fun := λ f,
    ⟨f.comap_domain sum.inl (sum.inl_injective.inj_on _),
     f.comap_domain sum.inr (sum.inr_injective.inj_on _)⟩,
  inv_fun := λ fg, sum_elim fg.1 fg.2,
  left_inv := λ f, by { ext ab, cases ab with a b; simp },
  right_inv := λ fg, by { ext; simp } }

lemma fst_sum_finsupp_equiv_prod_finsupp {α β γ : Type*} [has_zero γ]
  (f : (α ⊕ β) →₀ γ) (x : α) :
  (sum_finsupp_equiv_prod_finsupp f).1 x = f (sum.inl x) :=
rfl

lemma snd_sum_finsupp_equiv_prod_finsupp {α β γ : Type*} [has_zero γ]
  (f : (α ⊕ β) →₀ γ) (y : β) :
  (sum_finsupp_equiv_prod_finsupp f).2 y = f (sum.inr y) :=
rfl

lemma sum_finsupp_equiv_prod_finsupp_symm_inl {α β γ : Type*} [has_zero γ]
  (fg : (α →₀ γ) × (β →₀ γ)) (x : α) :
  (sum_finsupp_equiv_prod_finsupp.symm fg) (sum.inl x) = fg.1 x :=
rfl

lemma sum_finsupp_equiv_prod_finsupp_symm_inr {α β γ : Type*} [has_zero γ]
  (fg : (α →₀ γ) × (β →₀ γ)) (y : β) :
  (sum_finsupp_equiv_prod_finsupp.symm fg) (sum.inr y) = fg.2 y :=
rfl

variables [add_monoid M]

/-- The additive equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `finsupp` version of `equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps apply symm_apply] def sum_finsupp_add_equiv_prod_finsupp {α β : Type*} :
  ((α ⊕ β) →₀ M) ≃+ (α →₀ M) × (β →₀ M) :=
{ map_add' :=
    by { intros, ext;
          simp only [equiv.to_fun_as_coe, prod.fst_add, prod.snd_add, add_apply,
              snd_sum_finsupp_equiv_prod_finsupp, fst_sum_finsupp_equiv_prod_finsupp] },
  .. sum_finsupp_equiv_prod_finsupp }

lemma fst_sum_finsupp_add_equiv_prod_finsupp {α β : Type*}
  (f : (α ⊕ β) →₀ M) (x : α) :
  (sum_finsupp_add_equiv_prod_finsupp f).1 x = f (sum.inl x) :=
rfl

lemma snd_sum_finsupp_add_equiv_prod_finsupp {α β : Type*}
  (f : (α ⊕ β) →₀ M) (y : β) :
  (sum_finsupp_add_equiv_prod_finsupp f).2 y = f (sum.inr y) :=
rfl

lemma sum_finsupp_add_equiv_prod_finsupp_symm_inl {α β : Type*}
  (fg : (α →₀ M) × (β →₀ M)) (x : α) :
  (sum_finsupp_add_equiv_prod_finsupp.symm fg) (sum.inl x) = fg.1 x :=
rfl

lemma sum_finsupp_add_equiv_prod_finsupp_symm_inr {α β : Type*}
  (fg : (α →₀ M) × (β →₀ M)) (y : β) :
  (sum_finsupp_add_equiv_prod_finsupp.symm fg) (sum.inr y) = fg.2 y :=
rfl

end sum

section
variables [has_zero M] [monoid_with_zero R] [mul_action_with_zero R M]

@[simp] lemma single_smul (a b : α) (f : α → M) (r : R) :
  (single a r b) • (f a) = single a (r • f b) b :=
by by_cases a = b; simp [h]

end

section
variables [monoid G] [mul_action G α] [add_comm_monoid M]

/-- Scalar multiplication acting on the domain.

This is not an instance as it would conflict with the action on the range.
See the `instance_diamonds` test for examples of such conflicts. -/
def comap_has_scalar : has_scalar G (α →₀ M) :=
{ smul := λ g, map_domain ((•) g) }

local attribute [instance] comap_has_scalar

lemma comap_smul_def (g : G) (f : α →₀ M) : g • f = map_domain ((•) g) f := rfl

@[simp] lemma comap_smul_single (g : G) (a : α) (b : M) :
  g • single a b = single (g • a) b :=
map_domain_single

/-- `finsupp.comap_has_scalar` is multiplicative -/
def comap_mul_action : mul_action G (α →₀ M) :=
{ one_smul := λ f, by  rw [comap_smul_def, one_smul_eq_id, map_domain_id],
  mul_smul := λ g g' f, by rw [comap_smul_def, comap_smul_def, comap_smul_def, ←comp_smul_left,
    map_domain_comp], }

local attribute [instance] comap_mul_action

/-- `finsupp.comap_has_scalar` is distributive -/
def comap_distrib_mul_action :
  distrib_mul_action G (α →₀ M) :=
{ smul_zero := λ g, by { ext, dsimp [(•)], simp, },
  smul_add := λ g f f', by { ext, dsimp [(•)], simp [map_domain_add], }, }

end

section
variables [group G] [mul_action G α] [add_comm_monoid M]

local attribute [instance] comap_has_scalar comap_mul_action comap_distrib_mul_action

/-- When `G` is a group, `finsupp.comap_has_scalar` acts by precomposition with the action of `g⁻¹`.
-/
@[simp] lemma comap_smul_apply (g : G) (f : α →₀ M) (a : α) :
  (g • f) a = f (g⁻¹ • a) :=
begin
  conv_lhs { rw ←smul_inv_smul g a },
  exact map_domain_apply (mul_action.injective g) _ (g⁻¹ • a),
end

end

section
instance [monoid R] [add_monoid M] [distrib_mul_action R M] : has_scalar R (α →₀ M) :=
⟨λa v, v.map_range ((•) a) (smul_zero _)⟩

/-!
Throughout this section, some `monoid` and `semiring` arguments are specified with `{}` instead of
`[]`. See note [implicit instance arguments].
-/

@[simp] lemma coe_smul {_ : monoid R} [add_monoid M] [distrib_mul_action R M]
  (b : R) (v : α →₀ M) : ⇑(b • v) = b • v := rfl
lemma smul_apply {_ : monoid R} [add_monoid M] [distrib_mul_action R M]
  (b : R) (v : α →₀ M) (a : α) : (b • v) a = b • (v a) := rfl

lemma _root_.is_smul_regular.finsupp {_ : monoid R} [add_monoid M] [distrib_mul_action R M] {k : R}
  (hk : is_smul_regular M k) : is_smul_regular (α →₀ M) k :=
λ _ _ h, ext $ λ i, hk (congr_fun h i)

instance [monoid R] [nonempty α] [add_monoid M] [distrib_mul_action R M] [has_faithful_scalar R M] :
  has_faithful_scalar R (α →₀ M) :=
{ eq_of_smul_eq_smul := λ r₁ r₂ h, let ⟨a⟩ := ‹nonempty α› in eq_of_smul_eq_smul $ λ m : M,
    by simpa using congr_fun (h (single a m)) a }

variables (α M)

instance [monoid R] [add_monoid M] [distrib_mul_action R M] : distrib_mul_action R (α →₀ M) :=
{ smul      := (•),
  smul_add  := λ a x y, ext $ λ _, smul_add _ _ _,
  one_smul  := λ x, ext $ λ _, one_smul _ _,
  mul_smul  := λ r s x, ext $ λ _, mul_smul _ _ _,
  smul_zero := λ x, ext $ λ _, smul_zero _ }

instance [monoid R] [monoid S] [add_monoid M] [distrib_mul_action R M] [distrib_mul_action S M]
  [has_scalar R S] [is_scalar_tower R S M] :
  is_scalar_tower R S (α →₀ M) :=
{ smul_assoc := λ r s a, ext $ λ _, smul_assoc _ _ _ }

instance [monoid R] [monoid S] [add_monoid M] [distrib_mul_action R M] [distrib_mul_action S M]
  [smul_comm_class R S M] :
  smul_comm_class R S (α →₀ M) :=
{ smul_comm := λ r s a, ext $ λ _, smul_comm _ _ _ }

instance [monoid R] [add_monoid M] [distrib_mul_action R M] [distrib_mul_action Rᵐᵒᵖ M]
  [is_central_scalar R M] : is_central_scalar R (α →₀ M) :=
{ op_smul_eq_smul := λ r a, ext $ λ _, op_smul_eq_smul _ _ }

instance [semiring R] [add_comm_monoid M] [module R M] : module R (α →₀ M) :=
{ smul      := (•),
  zero_smul := λ x, ext $ λ _, zero_smul _ _,
  add_smul  := λ a x y, ext $ λ _, add_smul _ _ _,
  .. finsupp.distrib_mul_action α M }

variables {α M} {R}

lemma support_smul {_ : monoid R} [add_monoid M] [distrib_mul_action R M] {b : R} {g : α →₀ M} :
  (b • g).support ⊆ g.support :=
λ a, by { simp only [smul_apply, mem_support_iff, ne.def], exact mt (λ h, h.symm ▸ smul_zero _) }

@[simp]
lemma support_smul_eq [semiring R] [add_comm_monoid M] [module R M]
  [no_zero_smul_divisors R M] {b : R} (hb : b ≠ 0) {g : α →₀ M} :
  (b • g).support = g.support :=
finset.ext (λ a, by simp [finsupp.smul_apply, hb])

section

variables {p : α → Prop}

@[simp] lemma filter_smul {_ : monoid R} [add_monoid M] [distrib_mul_action R M]
  {b : R} {v : α →₀ M} : (b • v).filter p = b • v.filter p :=
coe_fn_injective $ set.indicator_const_smul {x | p x} b v

end

lemma map_domain_smul {_ : monoid R} [add_comm_monoid M] [distrib_mul_action R M]
   {f : α → β} (b : R) (v : α →₀ M) : map_domain f (b • v) = b • map_domain f v :=
map_domain_map_range _ _ _ _ (smul_add b)

@[simp] lemma smul_single {_ : monoid R} [add_monoid M] [distrib_mul_action R M]
  (c : R) (a : α) (b : M) : c • finsupp.single a b = finsupp.single a (c • b) :=
map_range_single

@[simp] lemma smul_single' {_ : semiring R}
  (c : R) (a : α) (b : R) : c • finsupp.single a b = finsupp.single a (c * b) :=
smul_single _ _ _

lemma map_range_smul {_ : monoid R} [add_monoid M] [distrib_mul_action R M]
  [add_monoid N] [distrib_mul_action R N]
  {f : M → N} {hf : f 0 = 0} (c : R) (v : α →₀ M) (hsmul : ∀ x, f (c • x) = c • f x) :
  map_range f hf (c • v) = c • map_range f hf v :=
begin
  erw ←map_range_comp,
  have : (f ∘ (•) c) = ((•) c ∘ f) := funext hsmul,
  simp_rw this,
  apply map_range_comp,
  rw [function.comp_apply, smul_zero, hf],
end

lemma smul_single_one [semiring R] (a : α) (b : R) : b • single a 1 = single a b :=
by rw [smul_single, smul_eq_mul, mul_one]

lemma comap_domain_smul [add_monoid M] [monoid R] [distrib_mul_action R M]
  {f : α → β} (r : R) (v : β →₀ M)
  (hfv : set.inj_on f (f ⁻¹' ↑(v.support)))
  (hfrv : set.inj_on f (f ⁻¹' ↑((r • v).support)) :=
    hfv.mono $ set.preimage_mono $ finset.coe_subset.mpr support_smul):
  comap_domain f (r • v) hfrv = r • comap_domain f v hfv :=
by { ext, refl }

/-- A version of `finsupp.comap_domain_smul` that's easier to use. -/
lemma comap_domain_smul_of_injective [add_monoid M] [monoid R] [distrib_mul_action R M]
  {f : α → β} (hf : function.injective f) (r : R) (v : β →₀ M) :
  comap_domain f (r • v) (hf.inj_on _) = r • comap_domain f v (hf.inj_on _) :=
comap_domain_smul _ _ _ _

end

lemma sum_smul_index [semiring R] [add_comm_monoid M] {g : α →₀ R} {b : R} {h : α → R → M}
  (h0 : ∀i, h i 0 = 0) : (b • g).sum h = g.sum (λi a, h i (b * a)) :=
finsupp.sum_map_range_index h0

lemma sum_smul_index' [monoid R] [add_monoid M] [distrib_mul_action R M] [add_comm_monoid N]
  {g : α →₀ M} {b : R} {h : α → M → N} (h0 : ∀i, h i 0 = 0) :
  (b • g).sum h = g.sum (λi c, h i (b • c)) :=
finsupp.sum_map_range_index h0

/-- A version of `finsupp.sum_smul_index'` for bundled additive maps. -/
lemma sum_smul_index_add_monoid_hom
  [monoid R] [add_monoid M] [add_comm_monoid N] [distrib_mul_action R M]
  {g : α →₀ M} {b : R} {h : α → M →+ N} :
  (b • g).sum (λ a, h a) = g.sum (λ i c, h i (b • c)) :=
sum_map_range_index (λ i, (h i).map_zero)

instance [semiring R] [add_comm_monoid M] [module R M] {ι : Type*}
  [no_zero_smul_divisors R M] : no_zero_smul_divisors R (ι →₀ M) :=
⟨λ c f h, or_iff_not_imp_left.mpr (λ hc, finsupp.ext
  (λ i, (smul_eq_zero.mp (finsupp.ext_iff.mp h i)).resolve_left hc))⟩

section distrib_mul_action_hom

variables [semiring R]
variables [add_comm_monoid M] [add_comm_monoid N] [distrib_mul_action R M] [distrib_mul_action R N]

/-- `finsupp.single` as a `distrib_mul_action_hom`.

See also `finsupp.lsingle` for the version as a linear map. -/
def distrib_mul_action_hom.single (a : α) : M →+[R] (α →₀ M) :=
{ map_smul' :=
    λ k m, by simp only [add_monoid_hom.to_fun_eq_coe, single_add_hom_apply, smul_single],
  .. single_add_hom a }

lemma distrib_mul_action_hom_ext {f g : (α →₀ M) →+[R] N}
  (h : ∀ (a : α) (m : M), f (single a m) = g (single a m)) :
  f = g :=
distrib_mul_action_hom.to_add_monoid_hom_injective $ add_hom_ext h

/-- See note [partially-applied ext lemmas]. -/
@[ext] lemma distrib_mul_action_hom_ext' {f g : (α →₀ M) →+[R] N}
  (h : ∀ (a : α), f.comp (distrib_mul_action_hom.single a) =
                  g.comp (distrib_mul_action_hom.single a)) :
  f = g :=
distrib_mul_action_hom_ext $ λ a, distrib_mul_action_hom.congr_fun (h a)

end distrib_mul_action_hom

section
variables [has_zero R]

/-- The `finsupp` version of `pi.unique`. -/
instance unique_of_right [subsingleton R] : unique (α →₀ R) :=
{ uniq := λ l, ext $ λ i, subsingleton.elim _ _,
  .. finsupp.inhabited }

/-- The `finsupp` version of `pi.unique_of_is_empty`. -/
instance unique_of_left [is_empty α] : unique (α →₀ R) :=
{ uniq := λ l, ext is_empty_elim,
  .. finsupp.inhabited }

end

/-- Given an `add_comm_monoid M` and `s : set α`, `restrict_support_equiv s M` is the `equiv`
between the subtype of finitely supported functions with support contained in `s` and
the type of finitely supported functions from `s`. -/
def restrict_support_equiv (s : set α) (M : Type*) [add_comm_monoid M] :
  {f : α →₀ M // ↑f.support ⊆ s } ≃ (s →₀ M) :=
begin
  refine ⟨λf, subtype_domain (λx, x ∈ s) f.1, λ f, ⟨f.map_domain subtype.val, _⟩, _, _⟩,
  { refine set.subset.trans (finset.coe_subset.2 map_domain_support) _,
    rw [finset.coe_image, set.image_subset_iff],
    exact assume x hx, x.2 },
  { rintros ⟨f, hf⟩,
    apply subtype.eq,
    ext a,
    dsimp only,
    refine classical.by_cases (assume h : a ∈ set.range (subtype.val : s → α), _) (assume h, _),
    { rcases h with ⟨x, rfl⟩,
      rw [map_domain_apply subtype.val_injective, subtype_domain_apply] },
    { convert map_domain_notin_range _ _ h,
      rw [← not_mem_support_iff],
      refine mt _ h,
      exact assume ha, ⟨⟨a, hf ha⟩, rfl⟩ } },
  { assume f,
    ext ⟨a, ha⟩,
    dsimp only,
    rw [subtype_domain_apply, map_domain_apply subtype.val_injective] }
end

/-- Given `add_comm_monoid M` and `e : α ≃ β`, `dom_congr e` is the corresponding `equiv` between
`α →₀ M` and `β →₀ M`.

This is `finsupp.equiv_congr_left` as an `add_equiv`. -/
@[simps apply]
protected def dom_congr [add_comm_monoid M] (e : α ≃ β) : (α →₀ M) ≃+ (β →₀ M) :=
{ to_fun := equiv_map_domain e,
  inv_fun := equiv_map_domain e.symm,
  left_inv := λ v, begin
    simp only [← equiv_map_domain_trans, equiv.self_trans_symm],
    exact equiv_map_domain_refl _
  end,
  right_inv := begin
    assume v,
    simp only [← equiv_map_domain_trans, equiv.symm_trans_self],
    exact equiv_map_domain_refl _
  end,
  map_add' := λ a b, by simp only [equiv_map_domain_eq_map_domain]; exact map_domain_add }

@[simp] lemma dom_congr_refl [add_comm_monoid M] :
  finsupp.dom_congr (equiv.refl α) = add_equiv.refl (α →₀ M) :=
add_equiv.ext $ λ _, equiv_map_domain_refl _

@[simp] lemma dom_congr_symm [add_comm_monoid M] (e : α ≃ β) :
  (finsupp.dom_congr e).symm = (finsupp.dom_congr e.symm : (β →₀ M) ≃+ (α →₀ M)):=
add_equiv.ext $ λ _, rfl

@[simp] lemma dom_congr_trans [add_comm_monoid M] (e : α ≃ β) (f : β ≃ γ) :
  (finsupp.dom_congr e).trans (finsupp.dom_congr f) =
    (finsupp.dom_congr (e.trans f) : (α →₀ M) ≃+ _) :=
add_equiv.ext $ λ _, (equiv_map_domain_trans _ _ _).symm

end finsupp

namespace finsupp

/-! ### Declarations about sigma types -/

section sigma

variables {αs : ι → Type*} [has_zero M] (l : (Σ i, αs i) →₀ M)

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `M` and
an index element `i : ι`, `split l i` is the `i`th component of `l`,
a finitely supported function from `as i` to `M`.

This is the `finsupp` version of `sigma.curry`.
-/
def split (i : ι) : αs i →₀ M :=
l.comap_domain (sigma.mk i) (λ x1 x2 _ _ hx, heq_iff_eq.1 (sigma.mk.inj hx).2)

lemma split_apply (i : ι) (x : αs i) : split l i x = l ⟨i, x⟩ :=
begin
  dunfold split,
  rw comap_domain_apply
end

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `β`,
`split_support l` is the finset of indices in `ι` that appear in the support of `l`. -/
def split_support : finset ι := l.support.image sigma.fst

lemma mem_split_support_iff_nonzero (i : ι) :
  i ∈ split_support l ↔ split l i ≠ 0 :=
begin
  rw [split_support, mem_image, ne.def, ← support_eq_empty, ← ne.def,
    ← finset.nonempty_iff_ne_empty, split, comap_domain, finset.nonempty],
  simp only [exists_prop, finset.mem_preimage, exists_and_distrib_right, exists_eq_right,
    mem_support_iff, sigma.exists, ne.def]
end

/-- Given `l`, a finitely supported function from the sigma type `Σ i, αs i` to `β` and
an `ι`-indexed family `g` of functions from `(αs i →₀ β)` to `γ`, `split_comp` defines a
finitely supported function from the index type `ι` to `γ` given by composing `g i` with
`split l i`. -/
def split_comp [has_zero N] (g : Π i, (αs i →₀ M) → N)
  (hg : ∀ i x, x = 0 ↔ g i x = 0) : ι →₀ N :=
{ support := split_support l,
  to_fun := λ i, g i (split l i),
  mem_support_to_fun :=
  begin
    intros i,
    rw [mem_split_support_iff_nonzero, not_iff_not, hg],
  end }

lemma sigma_support : l.support = l.split_support.sigma (λ i, (l.split i).support) :=
by simp only [finset.ext_iff, split_support, split, comap_domain, mem_image,
  mem_preimage, sigma.forall, mem_sigma]; tauto

lemma sigma_sum [add_comm_monoid N] (f : (Σ (i : ι), αs i) → M → N) :
  l.sum f = ∑ i in split_support l, (split l i).sum (λ (a : αs i) b, f ⟨i, a⟩ b) :=
by simp only [sum, sigma_support, sum_sigma, split_apply]

variables {η : Type*} [fintype η] {ιs : η → Type*} [has_zero α]

/-- On a `fintype η`, `finsupp.split` is an equivalence between `(Σ (j : η), ιs j) →₀ α`
and `Π j, (ιs j →₀ α)`.

This is the `finsupp` version of `equiv.Pi_curry`. -/
noncomputable def sigma_finsupp_equiv_pi_finsupp :
  ((Σ j, ιs j) →₀ α) ≃ Π j, (ιs j →₀ α) :=
{ to_fun := split,
  inv_fun := λ f, on_finset
    (finset.univ.sigma (λ j, (f j).support))
    (λ ji, f ji.1 ji.2)
    (λ g hg, finset.mem_sigma.mpr ⟨finset.mem_univ _, mem_support_iff.mpr hg⟩),
  left_inv := λ f, by { ext, simp [split] },
  right_inv := λ f, by { ext, simp [split] } }

@[simp] lemma sigma_finsupp_equiv_pi_finsupp_apply
  (f : (Σ j, ιs j) →₀ α) (j i) :
sigma_finsupp_equiv_pi_finsupp f j i = f ⟨j, i⟩ := rfl

/-- On a `fintype η`, `finsupp.split` is an additive equivalence between
`(Σ (j : η), ιs j) →₀ α` and `Π j, (ιs j →₀ α)`.

This is the `add_equiv` version of `finsupp.sigma_finsupp_equiv_pi_finsupp`.
-/
noncomputable def sigma_finsupp_add_equiv_pi_finsupp
  {α : Type*} {ιs : η → Type*} [add_monoid α] :
  ((Σ j, ιs j) →₀ α) ≃+ Π j, (ιs j →₀ α) :=
{ map_add' := λ f g, by { ext, simp },
  .. sigma_finsupp_equiv_pi_finsupp }

@[simp] lemma sigma_finsupp_add_equiv_pi_finsupp_apply
  {α : Type*} {ιs : η → Type*} [add_monoid α] (f : (Σ j, ιs j) →₀ α) (j i) :
sigma_finsupp_add_equiv_pi_finsupp f j i = f ⟨j, i⟩ := rfl

end sigma

end finsupp

section cast_finsupp
variables [has_zero M] (f : α →₀ M)

namespace nat

@[simp, norm_cast] lemma cast_finsupp_prod [comm_semiring R] (g : α → M → ℕ) :
  (↑(f.prod g) : R) = f.prod (λ a b, ↑(g a b)) :=
nat.cast_prod _ _

@[simp, norm_cast] lemma cast_finsupp_sum [comm_semiring R] (g : α → M → ℕ) :
  (↑(f.sum g) : R) = f.sum (λ a b, ↑(g a b)) :=
nat.cast_sum _ _

end nat

namespace int

@[simp, norm_cast] lemma cast_finsupp_prod [comm_ring R] (g : α → M → ℤ) :
  (↑(f.prod g) : R) = f.prod (λ a b, ↑(g a b)) :=
int.cast_prod _ _

@[simp, norm_cast] lemma cast_finsupp_sum [comm_ring R] (g : α → M → ℤ) :
  (↑(f.sum g) : R) = f.sum (λ a b, ↑(g a b)) :=
int.cast_sum _ _

end int
end cast_finsupp
