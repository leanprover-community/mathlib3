/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/

import topology.separation

/-!
# The topological support of a function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the topological support of a function `f`, `tsupport f`,
as the closure of the support of `f`.

Furthermore, we say that `f` has compact support if the topological support of `f` is compact.

## Main definitions

* `function.mul_tsupport` & `function.tsupport`
* `function.has_compact_mul_support` & `function.has_compact_support`

## Implementation Notes

* We write all lemmas for multiplicative functions, and use `@[to_additive]` to get the more common
  additive versions.
* We do not put the definitions in the `function` namespace, following many other topological
  definitions that are in the root namespace (compare `embedding` vs `function.embedding`).
-/

open function set filter
open_locale topology

variables {X α α' β γ δ M E R : Type*}

section one
variables [has_one α]
variables [topological_space X]

/-- The topological support of a function is the closure of its support, i.e. the closure of the
  set of all elements where the function is not equal to 1. -/
@[to_additive
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
lemma image_eq_one_of_nmem_mul_tsupport {f : X → α} {x : X} (hx : x ∉ mul_tsupport f) : f x = 1 :=
mul_support_subset_iff'.mp (subset_mul_tsupport f) x hx

@[to_additive]
lemma range_subset_insert_image_mul_tsupport (f : X → α) :
  range f ⊆ insert 1 (f '' mul_tsupport f) :=
(range_subset_insert_image_mul_support f).trans $
  insert_subset_insert $ image_subset _ subset_closure

@[to_additive]
lemma range_eq_image_mul_tsupport_or (f : X → α) :
  range f = f '' mul_tsupport f ∨ range f = insert 1 (f '' mul_tsupport f) :=
(wcovby_insert _ _).eq_or_eq (image_subset_range _ _) (range_subset_insert_image_mul_tsupport f)

lemma tsupport_mul_subset_left {α : Type*} [mul_zero_class α] {f g : X → α} :
  tsupport (λ x, f x * g x) ⊆ tsupport f :=
closure_mono (support_mul_subset_left _ _)

lemma tsupport_mul_subset_right {α : Type*} [mul_zero_class α] {f g : X → α} :
  tsupport (λ x, f x * g x) ⊆ tsupport g :=
closure_mono (support_mul_subset_right _ _)

end one

lemma tsupport_smul_subset_left {M α} [topological_space X] [has_zero M] [has_zero α]
  [smul_with_zero M α] (f : X → M) (g : X → α) :
  tsupport (λ x, f x • g x) ⊆ tsupport f :=
closure_mono $ support_smul_subset_left f g

section

variables [topological_space α] [topological_space α']
variables [has_one β] [has_one γ] [has_one δ]
variables {g : β → γ} {f : α → β} {f₂ : α → γ} {m : β → γ → δ} {x : α}

@[to_additive]
lemma not_mem_mul_tsupport_iff_eventually_eq : x ∉ mul_tsupport f ↔ f =ᶠ[𝓝 x] 1 :=
by simp_rw [mul_tsupport, mem_closure_iff_nhds, not_forall, not_nonempty_iff_eq_empty,
    ← disjoint_iff_inter_eq_empty, disjoint_mul_support_iff, eventually_eq_iff_exists_mem]

@[to_additive] lemma continuous_of_mul_tsupport [topological_space β] {f : α → β}
  (hf : ∀ x ∈ mul_tsupport f, continuous_at f x) : continuous f :=
continuous_iff_continuous_at.2 $ λ x, (em _).elim (hf x) $ λ hx,
  (@continuous_at_const _ _ _ _ _ 1).congr (not_mem_mul_tsupport_iff_eventually_eq.mp hx).symm

/-- A function `f` *has compact multiplicative support* or is *compactly supported* if the closure
of the multiplicative support of `f` is compact. In a T₂ space this is equivalent to `f` being equal
to `1` outside a compact set. -/
@[to_additive
/-" A function `f` *has compact support* or is *compactly supported* if the closure of the support
of `f` is compact. In a T₂ space this is equivalent to `f` being equal to `0` outside a compact
set. "-/]
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
lemma has_compact_mul_support_iff_eventually_eq :
  has_compact_mul_support f ↔ f =ᶠ[coclosed_compact α] 1 :=
⟨ λ h, mem_coclosed_compact.mpr ⟨mul_tsupport f, is_closed_mul_tsupport _, h,
    λ x, not_imp_comm.mpr $ λ hx, subset_mul_tsupport f hx⟩,
  λ h, let ⟨C, hC⟩ := mem_coclosed_compact'.mp h in
    is_compact_of_is_closed_subset hC.2.1 (is_closed_mul_tsupport _) (closure_minimal hC.2.2 hC.1)⟩

@[to_additive]
lemma has_compact_mul_support.is_compact_range [topological_space β]
  (h : has_compact_mul_support f) (hf : continuous f) : is_compact (range f) :=
begin
  cases range_eq_image_mul_tsupport_or f with h2 h2; rw [h2],
  exacts [h.image hf, (h.image hf).insert 1]
end

@[to_additive]
lemma has_compact_mul_support.mono' {f' : α → γ} (hf : has_compact_mul_support f)
  (hff' : mul_support f' ⊆ mul_tsupport f) : has_compact_mul_support f' :=
is_compact_of_is_closed_subset hf is_closed_closure $ closure_minimal hff' is_closed_closure

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
lemma has_compact_mul_support.comp_closed_embedding (hf : has_compact_mul_support f)
  {g : α' → α} (hg : closed_embedding g) : has_compact_mul_support (f ∘ g) :=
begin
  rw [has_compact_mul_support_def, function.mul_support_comp_eq_preimage],
  refine is_compact_of_is_closed_subset (hg.is_compact_preimage hf) is_closed_closure _,
  rw [hg.to_embedding.closure_eq_preimage_closure_image],
  exact preimage_mono (closure_mono $ image_preimage_subset _ _)
end

@[to_additive]
lemma has_compact_mul_support.comp₂_left (hf : has_compact_mul_support f)
  (hf₂ : has_compact_mul_support f₂) (hm : m 1 1 = 1) :
  has_compact_mul_support (λ x, m (f x) (f₂ x)) :=
begin
  rw [has_compact_mul_support_iff_eventually_eq] at hf hf₂ ⊢,
  filter_upwards [hf, hf₂] using λ x hx hx₂, by simp_rw [hx, hx₂, pi.one_apply, hm]
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

section distrib_mul_action

variables [topological_space α] [monoid_with_zero R] [add_monoid M] [distrib_mul_action R M]
variables {f : α → R} {f' : α → M} {x : α}

lemma has_compact_support.smul_left (hf : has_compact_support f') : has_compact_support (f • f') :=
begin
  rw [has_compact_support_iff_eventually_eq] at hf ⊢,
  refine hf.mono (λ x hx, by simp_rw [pi.smul_apply', hx, pi.zero_apply, smul_zero])
end

end distrib_mul_action

section smul_with_zero

variables [topological_space α] [has_zero R] [has_zero M] [smul_with_zero R M]
variables {f : α → R} {f' : α → M} {x : α}

lemma has_compact_support.smul_right (hf : has_compact_support f) : has_compact_support (f • f') :=
begin
  rw [has_compact_support_iff_eventually_eq] at hf ⊢,
  refine hf.mono (λ x hx, by simp_rw [pi.smul_apply', hx, pi.zero_apply, zero_smul])
end

lemma has_compact_support.smul_left' (hf : has_compact_support f') : has_compact_support (f • f') :=
begin
  rw [has_compact_support_iff_eventually_eq] at hf ⊢,
  refine hf.mono (λ x hx, by simp_rw [pi.smul_apply', hx, pi.zero_apply, smul_zero])
end

end smul_with_zero

section mul_zero_class

variables [topological_space α] [mul_zero_class β]
variables {f f' : α → β} {x : α}

lemma has_compact_support.mul_right (hf : has_compact_support f) : has_compact_support (f * f') :=
begin
  rw [has_compact_support_iff_eventually_eq] at hf ⊢,
  refine hf.mono (λ x hx, by simp_rw [pi.mul_apply, hx, pi.zero_apply, zero_mul])
end

lemma has_compact_support.mul_left (hf : has_compact_support f') : has_compact_support (f * f') :=
begin
  rw [has_compact_support_iff_eventually_eq] at hf ⊢,
  refine hf.mono (λ x hx, by simp_rw [pi.mul_apply, hx, pi.zero_apply, mul_zero])
end

end mul_zero_class

namespace locally_finite

variables {ι : Type*} {U : ι → set X} [topological_space X] [has_one R]

/-- If a family of functions `f` has locally-finite multiplicative support, subordinate to a family
of open sets, then for any point we can find a neighbourhood on which only finitely-many members of
`f` are not equal to 1. -/
@[to_additive
/-" If a family of functions `f` has locally-finite support, subordinate to a family of open sets,
then for any point we can find a neighbourhood on which only finitely-many members of `f` are
non-zero. "-/]
lemma exists_finset_nhd_mul_support_subset
  {f : ι → X → R} (hlf : locally_finite (λ i, mul_support (f i)))
  (hso : ∀ i, mul_tsupport (f i) ⊆ U i) (ho : ∀ i, is_open (U i)) (x : X) :
  ∃ (is : finset ι) {n : set X} (hn₁ : n ∈ 𝓝 x) (hn₂ : n ⊆ ⋂ i ∈ is, U i), ∀ (z ∈ n),
    mul_support (λ i, f i z) ⊆ is :=
begin
  obtain ⟨n, hn, hnf⟩ := hlf x,
  classical,
  let is := hnf.to_finset.filter (λ i, x ∈ U i),
  let js := hnf.to_finset.filter (λ j, x ∉ U j),
  refine ⟨is, n ∩ (⋂ j ∈ js, (mul_tsupport (f j))ᶜ) ∩ (⋂ i ∈ is, U i),
    inter_mem (inter_mem hn _) _, inter_subset_right _ _, λ z hz, _⟩,
  { exact (bInter_finset_mem js).mpr (λ j hj, is_closed.compl_mem_nhds
      (is_closed_mul_tsupport _) (set.not_mem_subset (hso j) (finset.mem_filter.mp hj).2)), },
  { exact (bInter_finset_mem is).mpr (λ i hi, (ho i).mem_nhds (finset.mem_filter.mp hi).2) },
  { have hzn : z ∈ n,
    { rw inter_assoc at hz,
      exact mem_of_mem_inter_left hz, },
    replace hz := mem_of_mem_inter_right (mem_of_mem_inter_left hz),
    simp only [finset.mem_filter, finite.mem_to_finset, mem_set_of_eq, mem_Inter, and_imp] at hz,
    suffices : mul_support (λ i, f i z) ⊆ hnf.to_finset,
    { refine hnf.to_finset.subset_coe_filter_of_subset_forall _ this (λ i hi, _),
      specialize hz i ⟨z, ⟨hi, hzn⟩⟩,
      contrapose hz,
      simp [hz, subset_mul_tsupport (f i) hi], },
    intros i hi,
    simp only [finite.coe_to_finset, mem_set_of_eq],
    exact ⟨z, ⟨hi, hzn⟩⟩, },
end

end locally_finite
