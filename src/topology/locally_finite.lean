/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.basic
import order.filter.small_sets

/-!
### Locally finite families of sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that a family of sets in a topological space is *locally finite* if at every point `x : X`,
there is a neighborhood of `x` which meets only finitely many sets in the family.

In this file we give the definition and prove basic properties of locally finite families of sets.
-/

/- locally finite family [General Topology (Bourbaki, 1995)] -/

open set function filter
open_locale topology filter

universe u
variables {ι : Type u} {ι' α X Y : Type*} [topological_space X] [topological_space Y]
  {f g : ι → set X}

/-- A family of sets in `set X` is locally finite if at every point `x : X`,
there is a neighborhood of `x` which meets only finitely many sets in the family. -/
def locally_finite (f : ι → set X) :=
∀ x : X, ∃t ∈ 𝓝 x, {i | (f i ∩ t).nonempty}.finite

lemma locally_finite_of_finite [finite ι] (f : ι → set X) : locally_finite f :=
assume x, ⟨univ, univ_mem, to_finite _⟩

namespace locally_finite

lemma point_finite (hf : locally_finite f) (x : X) : {b | x ∈ f b}.finite :=
let ⟨t, hxt, ht⟩ := hf x in ht.subset $ λ b hb, ⟨x, hb, mem_of_mem_nhds hxt⟩

protected lemma subset (hf : locally_finite f) (hg : ∀ i, g i ⊆ f i) : locally_finite g :=
assume a,
let ⟨t, ht₁, ht₂⟩ := hf a in
⟨t, ht₁, ht₂.subset $ assume i hi, hi.mono $ inter_subset_inter (hg i) subset.rfl⟩

lemma comp_inj_on {g : ι' → ι} (hf : locally_finite f)
  (hg : inj_on g {i | (f (g i)).nonempty}) : locally_finite (f ∘ g) :=
λ x, let ⟨t, htx, htf⟩ := hf x in ⟨t, htx, htf.preimage $ hg.mono $ λ i hi,
  hi.out.mono $ inter_subset_left _ _⟩

lemma comp_injective {g : ι' → ι} (hf : locally_finite f) (hg : injective g) :
  locally_finite (f ∘ g) :=
hf.comp_inj_on (hg.inj_on _)

lemma _root_.locally_finite_iff_small_sets :
  locally_finite f ↔ ∀ x, ∀ᶠ s in (𝓝 x).small_sets, {i | (f i ∩ s).nonempty}.finite :=
forall_congr $ λ x, iff.symm $ eventually_small_sets' $ λ s t hst ht, ht.subset $
  λ i hi, hi.mono $ inter_subset_inter_right _ hst

protected lemma eventually_small_sets (hf : locally_finite f) (x : X) :
  ∀ᶠ s in (𝓝 x).small_sets, {i | (f i ∩ s).nonempty}.finite :=
locally_finite_iff_small_sets.mp hf x

lemma exists_mem_basis {ι' : Sort*} (hf : locally_finite f) {p : ι' → Prop}
  {s : ι' → set X} {x : X} (hb : (𝓝 x).has_basis p s) :
  ∃ i (hi : p i), {j | (f j ∩ s i).nonempty}.finite :=
let ⟨i, hpi, hi⟩ := hb.small_sets.eventually_iff.mp (hf.eventually_small_sets x)
in ⟨i, hpi, hi subset.rfl⟩

protected lemma closure (hf : locally_finite f) : locally_finite (λ i, closure (f i)) :=
begin
  intro x,
  rcases hf x with ⟨s, hsx, hsf⟩,
  refine ⟨interior s, interior_mem_nhds.2 hsx, hsf.subset $ λ i hi, _⟩,
  exact (hi.mono is_open_interior.closure_inter).of_closure.mono
    (inter_subset_inter_right _ interior_subset)
end

lemma is_closed_Union (hf : locally_finite f) (hc : ∀i, is_closed (f i)) :
  is_closed (⋃i, f i) :=
begin
  simp only [← is_open_compl_iff, compl_Union, is_open_iff_mem_nhds, mem_Inter],
  intros a ha,
  replace ha : ∀ i, (f i)ᶜ ∈ 𝓝 a := λ i, (hc i).is_open_compl.mem_nhds (ha i),
  rcases hf a with ⟨t, h_nhds, h_fin⟩,
  have : t ∩ (⋂ i ∈ {i | (f i ∩ t).nonempty}, (f i)ᶜ) ∈ 𝓝 a,
    from inter_mem h_nhds ((bInter_mem h_fin).2 (λ i _, ha i)),
  filter_upwards [this],
  simp only [mem_inter_iff, mem_Inter],
  rintros b ⟨hbt, hn⟩ i hfb,
  exact hn i ⟨b, hfb, hbt⟩ hfb,
end

lemma closure_Union (h : locally_finite f) : closure (⋃ i, f i) = ⋃ i, closure (f i) :=
subset.antisymm
  (closure_minimal (Union_mono $ λ _, subset_closure) $
    h.closure.is_closed_Union $ λ _, is_closed_closure)
  (Union_subset $ λ i, closure_mono $ subset_Union _ _)

/-- If `f : β → set α` is a locally finite family of closed sets, then for any `x : α`, the
intersection of the complements to `f i`, `x ∉ f i`, is a neighbourhood of `x`. -/
lemma Inter_compl_mem_nhds (hf : locally_finite f) (hc : ∀ i, is_closed (f i)) (x : X) :
  (⋂ i (hi : x ∉ f i), (f i)ᶜ) ∈ 𝓝 x :=
begin
  refine is_open.mem_nhds _ (mem_Inter₂.2 $ λ i, id),
  suffices : is_closed (⋃ i : {i // x ∉ f i}, f i),
    by rwa [← is_open_compl_iff, compl_Union, Inter_subtype] at this,
  exact (hf.comp_injective subtype.coe_injective).is_closed_Union (λ i, hc _)
end

/-- Let `f : ℕ → Π a, β a` be a sequence of (dependent) functions on a topological space. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. Then there exists a
function `F : Π a, β a` such that for any `x`, we have `f n x = F x` on the product of an infinite
interval `[N, +∞)` and a neighbourhood of `x`.

We formulate the conclusion in terms of the product of filter `filter.at_top` and `𝓝 x`. -/
lemma exists_forall_eventually_eq_prod {π : X → Sort*} {f : ℕ → Π x : X, π x}
  (hf : locally_finite (λ n, {x | f (n + 1) x ≠ f n x})) :
  ∃ F : Π x : X, π x, ∀ x, ∀ᶠ p : ℕ × X in at_top ×ᶠ 𝓝 x, f p.1 p.2 = F p.2 :=
begin
  choose U hUx hU using hf,
  choose N hN using λ x, (hU x).bdd_above,
  replace hN : ∀ x (n > N x) (y ∈ U x), f (n + 1) y = f n y,
    from λ x n hn y hy, by_contra (λ hne, hn.lt.not_le $ hN x ⟨y, hne, hy⟩),
  replace hN : ∀ x (n ≥ N x + 1) (y ∈ U x), f n y = f (N x + 1) y,
    from λ x n hn y hy, nat.le_induction rfl (λ k hle, (hN x _ hle _ hy).trans) n hn,
  refine ⟨λ x, f (N x + 1) x, λ x, _⟩,
  filter_upwards [filter.prod_mem_prod (eventually_gt_at_top (N x)) (hUx x)],
  rintro ⟨n, y⟩ ⟨hn : N x < n, hy : y ∈ U x⟩,
  calc f n y = f (N x + 1) y : hN _ _ hn _ hy
  ... = f (max (N x + 1) (N y + 1)) y : (hN _ _ (le_max_left _ _) _ hy).symm
  ... = f (N y + 1) y : hN _ _ (le_max_right _ _) _ (mem_of_mem_nhds $ hUx y)
end

/-- Let `f : ℕ → Π a, β a` be a sequence of (dependent) functions on a topological space. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. Then there exists a
function `F : Π a, β a` such that for any `x`, for sufficiently large values of `n`, we have
`f n y = F y` in a neighbourhood of `x`. -/
lemma exists_forall_eventually_at_top_eventually_eq' {π : X → Sort*}
  {f : ℕ → Π x : X, π x} (hf : locally_finite (λ n, {x | f (n + 1) x ≠ f n x})) :
  ∃ F : Π x : X, π x, ∀ x, ∀ᶠ n : ℕ in at_top, ∀ᶠ y : X in 𝓝 x, f n y = F y :=
hf.exists_forall_eventually_eq_prod.imp $ λ F hF x, (hF x).curry

/-- Let `f : ℕ → α → β` be a sequence of functions on a topological space. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. Then there exists a
function `F :  α → β` such that for any `x`, for sufficiently large values of `n`, we have
`f n =ᶠ[𝓝 x] F`. -/
lemma exists_forall_eventually_at_top_eventually_eq {f : ℕ → X → α}
  (hf : locally_finite (λ n, {x | f (n + 1) x ≠ f n x})) :
  ∃ F : X → α, ∀ x, ∀ᶠ n : ℕ in at_top, f n =ᶠ[𝓝 x] F :=
hf.exists_forall_eventually_at_top_eventually_eq'

lemma preimage_continuous {g : Y → X} (hf : locally_finite f) (hg : continuous g) :
  locally_finite (λ i, g ⁻¹' (f i)) :=
λ x, let ⟨s, hsx, hs⟩ := hf (g x)
  in ⟨g ⁻¹' s, hg.continuous_at hsx, hs.subset $ λ i ⟨y, hy⟩, ⟨g y, hy⟩⟩

end locally_finite

@[simp] lemma equiv.locally_finite_comp_iff (e : ι' ≃ ι) :
  locally_finite (f ∘ e) ↔ locally_finite f :=
⟨λ h, by simpa only [(∘), e.apply_symm_apply] using h.comp_injective e.symm.injective,
  λ h, h.comp_injective e.injective⟩

lemma locally_finite_sum {f : ι ⊕ ι' → set X} :
  locally_finite f ↔ locally_finite (f ∘ sum.inl) ∧ locally_finite (f ∘ sum.inr) :=
by simp only [locally_finite_iff_small_sets, ← forall_and_distrib, ← finite_preimage_inl_and_inr,
  preimage_set_of_eq, (∘), eventually_and]

lemma locally_finite.sum_elim {g : ι' → set X} (hf : locally_finite f) (hg : locally_finite g) :
  locally_finite (sum.elim f g) :=
locally_finite_sum.mpr ⟨hf, hg⟩

lemma locally_finite_option {f : option ι → set X} :
  locally_finite f ↔ locally_finite (f ∘ some) :=
begin
  simp only [← (equiv.option_equiv_sum_punit.{u} ι).symm.locally_finite_comp_iff,
    locally_finite_sum, locally_finite_of_finite, and_true],
  refl
end

lemma locally_finite.option_elim (hf : locally_finite f) (s : set X) :
  locally_finite (option.elim s f) :=
locally_finite_option.2 hf
