/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/

-- import topology.separation
import topology.homeomorph

/-!
# The topological support of a function

In this file we define the topological support of a function `f`, `function.tsupport f`,
as the closure of the support of `f`.

Furthermore, we say that `f` has compact support if the topological support of `f` is compact.

## Main definitions

* `function.mul_support`
* `function.has_compact_mul_support`

-/

open function set filter
open_locale topological_space

variables {X α α' β γ δ M E : Type*}

namespace function

section one
variables [has_one α]
variables [topological_space X]

-- todo: add mul_tsupport -> tsupport to to_additive dictionary

/-- The topological support of a function is the closure of its support, i.e. the closure of the
  set of all elements where the function is not equal to 1. -/
@[to_additive tsupport
/-" The topological support of a function is the closure of its support. i.e. the closure of the
  set of all elements where the function is nonzero. "-/]
def mul_tsupport (f : X → α) : set X := closure (mul_support f)

@[to_additive]
lemma subset_mul_tsupport (f : X → α) : mul_support f ⊆ mul_tsupport f :=
subset_closure

@[to_additive]
lemma is_closed_mul_tsupport (f : X → α) : is_closed (mul_tsupport f) :=
is_closed_closure

@[to_additive]
lemma mul_tsupport_eq_empty_iff {f : X → α} : mul_tsupport f = ∅ ↔ f = 1 :=
by rw [mul_tsupport, closure_empty_iff, mul_support_eq_empty_iff]

@[to_additive]
lemma image_eq_zero_of_nmem_mul_tsupport {f : X → α} {x : X} (hx : x ∉ mul_tsupport f) : f x = 1 :=
mul_support_subset_iff'.mp (subset_mul_tsupport f) x hx

end one

section

variables [topological_space α] [topological_space α']
variables [has_one β] [has_one γ] [has_one δ]
variables {g : β → γ} {f : α → β} {f₂ : α → γ} {m : β → γ → δ} {x : α}

@[to_additive]
lemma not_mem_closure_mul_support_iff_eventually_eq : x ∉ mul_tsupport f ↔ f =ᶠ[𝓝 x] 1 :=
by simp_rw [mul_tsupport, mem_closure_iff_nhds, not_forall, not_nonempty_iff_eq_empty,
    ← disjoint_iff_inter_eq_empty, disjoint_mul_support_iff, eventually_eq_iff_exists_mem]

/-- A function `f` *has compact multiplicative support* or is *compactly supported* if the closure
of the multiplicative support of `f` is compact. In other words: `f` is equal to `1` outside a
compact set. -/
@[to_additive
/-" A function `f` *has compact support* or is *compactly supported* if the closure of the support
of `f` is compact. In other words: `f` is equal to `0` outside a compact set. "-/]
def has_compact_mul_support (f : α → β) : Prop :=
is_compact (mul_tsupport f)

@[to_additive]
lemma has_compact_mul_support_def :
  has_compact_mul_support f ↔ is_compact (closure (mul_support f)) :=
by refl

@[to_additive]
lemma exists_compact_iff_has_compact_mul_support [t2_space α] :
  (∃ K : set α, is_compact K ∧ ∀ x ∉ K, f x = 1) ↔ has_compact_mul_support f :=
by simp_rw [← nmem_mul_support, ← mem_compl_iff, ← subset_def, compl_subset_compl,
    has_compact_mul_support_def, exists_compact_superset_iff]

@[to_additive]
lemma has_compact_mul_support.intro [t2_space α] {K : set α}
  (hK : is_compact K) (hfK : ∀ x ∉ K, f x = 1) : has_compact_mul_support f :=
exists_compact_iff_has_compact_mul_support.mp ⟨K, hK, hfK⟩

@[to_additive]
lemma has_compact_mul_support.is_compact (hf : has_compact_mul_support f) :
  is_compact (mul_tsupport f) :=
hf

@[to_additive]
lemma has_compact_mul_support.mono' {f' : α → γ} (hf : has_compact_mul_support f)
  (hff' : mul_support f' ⊆ mul_tsupport f) : has_compact_mul_support f' :=
compact_of_is_closed_subset hf is_closed_closure $ closure_minimal hff' is_closed_closure

@[to_additive]
lemma has_compact_mul_support.mono {f' : α → γ} (hf : has_compact_mul_support f)
  (hff' : mul_support f' ⊆ mul_support f) : has_compact_mul_support f' :=
hf.mono' $ hff'.trans subset_closure

@[to_additive]
lemma has_compact_mul_support.comp_left (hf : has_compact_mul_support f) (hg : g 1 = 1) :
  has_compact_mul_support (g ∘ f) :=
hf.mono $ mul_support_comp_subset hg f

@[to_additive]
lemma has_compact_mul_support_comp_left (hg : ∀ {x}, g x = 1 ↔ x = 1) :
  has_compact_mul_support (g ∘ f) ↔ has_compact_mul_support f :=
by simp_rw [has_compact_mul_support_def, mul_support_comp_eq g @hg f]

@[to_additive]
lemma has_compact_mul_support.comp₂_left (hf : has_compact_mul_support f)
  (hf₂ : has_compact_mul_support f₂) (hm : m 1 1 = 1) :
  has_compact_mul_support (λ x, m (f x) (f₂ x)) :=
begin
  refine compact_of_is_closed_subset (hf.union hf₂) is_closed_closure _,
  refine closure_minimal (λ x h2x, _) (is_closed_closure.union is_closed_closure) ,
  refine union_subset_union subset_closure subset_closure _,
  by_contra hx,
  simp_rw [mem_union, not_or_distrib, nmem_mul_support] at hx,
  apply h2x,
  simp_rw [hx.1, hx.2, hm]
end

@[to_additive]
lemma has_compact_mul_support.comp_homeomorph (hf : has_compact_mul_support f) (φ : α' ≃ₜ α) :
  has_compact_mul_support (f ∘ φ) :=
begin
  rw [has_compact_mul_support_def, mul_support_comp_eq_preimage, ← φ.preimage_closure],
  exact φ.compact_preimage.mpr hf
end

end

section monoid

variables [topological_space α] [monoid β]
variables {f f' : α → β} {x : α}


@[to_additive]
lemma has_compact_mul_support.mul (hf : has_compact_mul_support f)
  (hf' : has_compact_mul_support f') : has_compact_mul_support (f * f') :=
by apply hf.comp₂_left hf' (mul_one 1) -- `by apply` speeds up elaboration

end monoid

section monoid

variables [topological_space α] [monoid_with_zero β] [add_monoid γ] [distrib_mul_action β γ]
variables {f : α → β} {f' : α → γ} {x : α}


lemma has_compact_support.smul (hf : has_compact_support f)
  (hf' : has_compact_support f') : has_compact_support (f • f') :=
by apply hf.comp₂_left hf' (smul_zero 0) -- `by apply` speeds up elaboration

end monoid

section monoid_with_zero

variables [topological_space α] [mul_zero_class β]
variables {f f' : α → β} {x : α}

@[to_additive]
lemma has_compact_support.mul (hf : has_compact_support f)
  (hf' : has_compact_support f') : has_compact_support (f * f') :=
by apply hf.comp₂_left hf' (mul_zero 0) -- `by apply` speeds up elaboration

end monoid_with_zero


-- move
section

variables [topological_space α] [normed_group β]
variables {f : α → β} {x : α}

lemma has_compact_support_norm_iff : has_compact_support (λ x, ∥ f x ∥) ↔ has_compact_support f :=
has_compact_support_comp_left $ λ x, norm_eq_zero

alias has_compact_support_norm_iff ↔ _ has_compact_support.norm

end


section order

variables [conditionally_complete_linear_order α] [topological_space α]
  [order_topology α] [topological_space β]

-- topology.algebra.ordered.compact
/-- The **extreme value theorem**: if a continuous function `f` is larger than a value in its range
away from compact sets, then it has a global minimum. -/
lemma _root_.continuous.exists_forall_le' {f : β → α} (hf : continuous f) (x₀ : β)
  (h : ∀ᶠ x in cocompact β, f x₀ ≤ f x) : ∃ (x : β), ∀ (y : β), f x ≤ f y :=
begin
  obtain ⟨K : set β, hK : is_compact K, hKf : ∀ x ∉ K, f x₀ ≤ f x⟩ :=
  (has_basis_cocompact.eventually_iff).mp h,
  obtain ⟨x, -, hx⟩ : ∃ x ∈ insert x₀ K, ∀ y ∈ insert x₀ K, f x ≤ f y :=
  (hK.insert x₀).exists_forall_le (nonempty_insert _ _) hf.continuous_on,
  refine ⟨x, λ y, _⟩,
  by_cases hy : y ∈ K,
  exacts [hx y (or.inr hy), (hx _ (or.inl rfl)).trans (hKf y hy)]
end

-- better proof
lemma _root_.continuous.exists_forall_le'' [nonempty β] {f : β → α}
  (hf : continuous f) (hlim : tendsto f (cocompact β) at_top) :
  ∃ x, ∀ y, f x ≤ f y :=
by { inhabit β, exact hf.exists_forall_le' default (hlim.eventually $ eventually_ge_at_top _) }

@[to_additive]
lemma _root_.continuous.exists_forall_le_of_has_compact_mul_support [nonempty β] [has_one α]
  {f : β → α} (hf : continuous f) (h : has_compact_mul_support f) :
  ∃ (x : β), ∀ (y : β), f x ≤ f y :=
begin
  -- we use `continuous.exists_forall_le'` with as `x₀` any element outside the support of `f`,
  -- if such an element exists (and otherwise an arbitrary element).
  refine hf.exists_forall_le' (classical.epsilon $ λ x, f x = 1)
    (eventually_of_mem h.compl_mem_cocompact $ λ x hx, _),
  have : f x = 1 := nmem_mul_support.mp (mt (λ h2x, subset_closure h2x) hx),
  exact ((classical.epsilon_spec ⟨x, this⟩).trans this.symm).le
end

@[to_additive]
lemma continuous.exists_forall_ge_of_has_compact_mul_support [nonempty β] [has_one α]
  {f : β → α} (hf : continuous f) (h : has_compact_mul_support f) :
  ∃ (x : β), ∀ (y : β), f y ≤ f x :=
@continuous.exists_forall_le_of_has_compact_mul_support (order_dual α) _ _ _ _ _ _ _ _ hf h

@[to_additive]
lemma continuous.bdd_below_range_of_has_compact_mul_support [has_one α]
  {f : β → α} (hf : continuous f) (h : has_compact_mul_support f) :
  bdd_below (range f) :=
begin
  casesI is_empty_or_nonempty β with hβ hβ,
  { rw range_eq_empty_iff.mpr, exact bdd_below_empty, exact hβ },
  obtain ⟨x, hx⟩ := hf.exists_forall_le_of_has_compact_mul_support h,
  refine ⟨f x, _⟩, rintro _ ⟨x', rfl⟩, exact hx x'
end

@[to_additive]
lemma continuous.bdd_above_range_of_has_compact_mul_support [has_one α]
  {f : β → α} (hf : continuous f) (h : has_compact_mul_support f) :
  bdd_above (range f) :=
@continuous.bdd_below_range_of_has_compact_mul_support (order_dual α) _ _ _ _ _ _ _ hf h

lemma is_compact.bdd_below_image {f : β → α} {K : set β}
  (hK : is_compact K) (hf : continuous_on f K) : bdd_below (f '' K) :=
begin
  rcases eq_empty_or_nonempty K with rfl|h, { rw [image_empty], exact bdd_below_empty },
  obtain ⟨c, -, hc⟩ := hK.exists_forall_le h hf,
  refine ⟨f c, _⟩, rintro _ ⟨x, hx, rfl⟩, exact hc x hx
end

lemma is_compact.bdd_above_image {f : β → α} {K : set β}
  (hK : is_compact K) (hf : continuous_on f K) : bdd_above (f '' K) :=
@is_compact.bdd_below_image (order_dual α) _ _ _ _ _ _ _ hK hf


variables [topological_space X] [normed_group E]

lemma continuous.bounded_above_of_compact_support {f : X → E} (hf : continuous f)
  (hsupp : has_compact_support f) : ∃ C, ∀ x, ∥f x∥ ≤ C :=
by simpa [bdd_above_def] using hf.norm.bdd_above_range_of_has_compact_support hsupp.norm

end order

end function
