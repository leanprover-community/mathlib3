/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/

import topology.separation

/-!
# The topological support of a function

In this file we define the topological support of a function `f`, `tsupport f`,
as the closure of the support of `f`.

Furthermore, we say that `f` has compact support if the topological support of `f` is compact.

## Main definitions

* `function.mul_support`
* `function.has_compact_mul_support`

## Implementation Notes

* We write all lemmas for multiplicative functions, and use `@[to_additive]` to get the more common
  additive versions.
* We do not put the definitions in the `function` namespace, following many other topological
  definitions that are in the root namespace (compare `embedding` vs `function.embedding`).
-/

open function set filter
open_locale topological_space

variables {X α α' β γ δ M E : Type*}

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
of the multiplicative support of `f` is compact. In a T₂ space this is equivalent to `f` being equal
to `1` outside a compact set. -/
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
