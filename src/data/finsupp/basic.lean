/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Scott Morrison
-/
import data.finset.preimage
import algebra.indicator_function
import algebra.group_action_hom

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

## Notations

This file adds `α →₀ M` as a global notation for `finsupp α M`. We also use the following convention
for `Type*` variables in this file

* `α`, `β`, `γ`: types with no additional structure that appear as the first argument to `finsupp`
  somewhere in the statement;

* `ι` : an auxiliary index type;

* `M`, `M'`, `N`, `P`: types with `has_zero` or `(add_)(comm_)monoid` structure; `M` is also used
  for a (semi)module over a (semi)ring.

* `G`, `H`: groups (commutative or not, multiplicative or additive);

* `R`, `S`: (semi)rings.

## TODO

* This file is currently ~2K lines long, so possibly it should be splitted into smaller chunks;

* Add the list of definitions and important lemmas to the module docstring.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## Notation

This file defines `α →₀ β` as notation for `finsupp α β`.

-/

noncomputable theory
open_locale classical big_operators

open finset

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

instance : has_coe_to_fun (α →₀ M) (λ _, α → M) := ⟨to_fun⟩

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

lemma coe_fn_injective : @function.injective (α →₀ M) (α → M) coe_fn
| ⟨s, f, hf⟩ ⟨t, g, hg⟩ h :=
  begin
    change f = g at h, subst h,
    have : s = t, { ext a, exact (hf a).trans (hg a).symm },
    subst this
  end

@[simp, norm_cast] lemma coe_fn_inj {f g : α →₀ M} : (f : α → M) = g ↔ f = g :=
coe_fn_injective.eq_iff

@[simp, norm_cast] lemma coe_eq_zero {f : α →₀ M} : (f : α → M) = 0 ↔ f = 0 :=
by rw [← coe_zero, coe_fn_inj]

@[ext] lemma ext {f g : α →₀ M} (h : ∀a, f a = g a) : f = g := coe_fn_injective (funext h)

lemma ext_iff {f g : α →₀ M} : f = g ↔ (∀a:α, f a = g a) :=
⟨by rintros rfl a; refl, ext⟩

lemma ext_iff' {f g : α →₀ M} : f = g ↔ f.support = g.support ∧ ∀ x ∈ f.support, f x = g x :=
⟨λ h, h ▸ ⟨rfl, λ _ _, rfl⟩, λ ⟨h₁, h₂⟩, ext $ λ a,
  if h : a ∈ f.support then h₂ a h else
    have hf : f a = 0, from not_mem_support_iff.1 h,
    have hg : g a = 0, by rwa [h₁, not_mem_support_iff] at h,
    by rw [hf, hg]⟩

lemma congr_fun {f g : α →₀ M} (h : f = g) (a : α) : f a = g a :=
congr_fun (congr_arg finsupp.to_fun h) a

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
begin
  have : i ∈ (single i b).support := by simpa using h,
  intro H,
  simpa [H]
end

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

lemma unique_ext [unique α] {f g : α →₀ M} (h : f default = g default) : f = g :=
ext $ λ a, by rwa [unique.eq_default a]

lemma unique_ext_iff [unique α] {f g : α →₀ M} : f = g ↔  f default = g default :=
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
def zip_with (f : M → N → P) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : (α →₀ P) :=
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
lemma _root_.submonoid.finsupp_prod_mem (S : submonoid N) (f : α →₀ M) (g : α → M → N)
  (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) : f.prod g ∈ S :=
S.prod_mem $ λ i hi, h _ (finsupp.mem_support_iff.mp hi)

@[to_additive]
lemma prod_congr {f : α →₀ M} {g1 g2 : α → M → N}
  (h : ∀ x ∈ f.support, g1 x (f x) = g2 x (f x)) : f.prod g1 = f.prod g2 :=
finset.prod_congr rfl h

end sum_prod

/-! ### Declarations about `comap_domain` -/

section comap_domain

/-- Given `f : α → β`, `l : β →₀ M` and a proof `hf` that `f` is injective on
the preimage of `l.support`, `comap_domain f l hf` is the finitely supported function
from `α` to `M` given by composing `l` with `f`. -/
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

end comap_domain

section option

/-- Restrict a finitely supported function on `option α` to a finitely supported function on `α`. -/
def some [has_zero M] (f : option α →₀ M) : α →₀ M :=
f.comap_domain option.some (λ _, by simp)

@[simp] lemma some_apply [has_zero M] (f : option α →₀ M) (a : α) :
  f.some a = f (option.some a) := rfl

@[simp] lemma some_zero [has_zero M] : (0 : option α →₀ M).some = 0 :=
by { ext, simp, }

@[simp] lemma some_single_none [has_zero M] (m : M) : (single none m : option α →₀ M).some = 0 :=
by { ext, simp, }

@[simp] lemma some_single_some [has_zero M] (a : α) (m : M) :
  (single (option.some a) m : option α →₀ M).some = single a m :=
by { ext b, simp [single_apply], }

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

@[simp] lemma filter_apply_pos {a : α} (h : p a) : f.filter p a = f a :=
if_pos h

@[simp] lemma filter_apply_neg {a : α} (h : ¬ p a) : f.filter p a = 0 :=
if_neg h

@[simp] lemma support_filter [D : decidable_pred p] : (f.filter p).support = f.support.filter p :=
by rw subsingleton.elim D; refl

lemma filter_zero : (0 : α →₀ M).filter p = 0 :=
by rw [← support_eq_empty, support_filter, support_zero, finset.filter_empty]

@[simp] lemma filter_single_of_pos
  {a : α} {b : M} (h : p a) : (single a b).filter p = single a b :=
coe_fn_injective $ by simp [filter_eq_indicator, set.subset_def, mem_support_single, h]

@[simp] lemma filter_single_of_neg
  {a : α} {b : M} (h : ¬ p a) : (single a b).filter p = 0 :=
ext $ by simp [filter_eq_indicator, single_apply_eq_zero, @imp.swap (p _), h]

end has_zero
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
      (assume a b₀ b₁, sum_add_index (assume a, hg₀ _ _) (assume c d₀ d₁, hg₁ _ _ _ _)) },
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
variables [group G] [mul_action G α] [add_comm_monoid M]

/--
Scalar multiplication by a group element g,
given by precomposition with the action of g⁻¹ on the domain.
-/
def comap_has_scalar : has_scalar G (α →₀ M) :=
{ smul := λ g f, f.comap_domain (λ a, g⁻¹ • a)
  (λ a a' m m' h, by simpa [←mul_smul] using (congr_arg (λ a, g • a) h)) }

local attribute [instance] comap_has_scalar

/--
Scalar multiplication by a group element,
given by precomposition with the action of g⁻¹ on the domain,
is multiplicative in g.
-/
def comap_mul_action : mul_action G (α →₀ M) :=
{ one_smul := λ f, by { ext, dsimp [(•)], simp, },
  mul_smul := λ g g' f, by { ext, dsimp [(•)], simp [mul_smul], }, }

local attribute [instance] comap_mul_action

/--
Scalar multiplication by a group element,
given by precomposition with the action of g⁻¹ on the domain,
is additive in the second argument.
-/
def comap_distrib_mul_action :
  distrib_mul_action G (α →₀ M) :=
{ smul_zero := λ g, by { ext, dsimp [(•)], simp, },
  smul_add := λ g f f', by { ext, dsimp [(•)], simp, }, }

/--
Scalar multiplication by a group element on finitely supported functions on a group,
given by precomposition with the action of g⁻¹. -/
def comap_distrib_mul_action_self :
  distrib_mul_action G (G →₀ M) :=
@finsupp.comap_distrib_mul_action G M G _ (monoid.to_mul_action G) _

@[simp]
lemma comap_smul_single (g : G) (a : α) (b : M) :
  g • single a b = single (g • a) b :=
begin
  ext a',
  dsimp [(•)],
  by_cases h : g • a = a',
  { subst h, simp [←mul_smul], },
  { simp [single_eq_of_ne h], rw [single_eq_of_ne],
    rintro rfl, simpa [←mul_smul] using h, }
end

@[simp]
lemma comap_smul_apply (g : G) (f : α →₀ M) (a : α) :
  (g • f) a = f (g⁻¹ • a) := rfl

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
coe_fn_injective $ set.indicator_smul {x | p x} b v

end

lemma map_domain_smul {_ : monoid R} [add_comm_monoid M] [distrib_mul_action R M]
   {f : α → β} (b : R) (v : α →₀ M) : map_domain f (b • v) = b • map_domain f v :=
begin
  change map_domain f (map_range _ _ _) = map_range _ _ _,
  apply finsupp.induction v, { simp only [map_domain_zero, map_range_zero] },
  intros a b v' hv₁ hv₂ IH,
  rw [map_range_add, map_domain_add, IH, map_domain_add, map_range_add,
    map_range_single, map_domain_single, map_domain_single, map_range_single];
  apply smul_add
end

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
