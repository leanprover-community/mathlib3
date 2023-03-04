/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
import order.filter.at_top_bot
import order.filter.pi

/-!
# The cofinite filter

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define

`cofinite`: the filter of sets with finite complement

and prove its basic properties. In particular, we prove that for `ℕ` it is equal to `at_top`.

## TODO

Define filters for other cardinalities of the complement.
-/

open set function
open_locale classical

variables {ι α β : Type*} {l : filter α}

namespace filter

/-- The cofinite filter is the filter of subsets whose complements are finite. -/
def cofinite : filter α :=
{ sets             := {s | sᶜ.finite},
  univ_sets        := by simp only [compl_univ, finite_empty, mem_set_of_eq],
  sets_of_superset := assume s t (hs : sᶜ.finite) (st: s ⊆ t),
    hs.subset $ compl_subset_compl.2 st,
  inter_sets       := assume s t (hs : sᶜ.finite) (ht : tᶜ.finite),
    by simp only [compl_inter, finite.union, ht, hs, mem_set_of_eq] }

@[simp] lemma mem_cofinite {s : set α} : s ∈ (@cofinite α) ↔ sᶜ.finite := iff.rfl

@[simp] lemma eventually_cofinite {p : α → Prop} :
  (∀ᶠ x in cofinite, p x) ↔ {x | ¬p x}.finite := iff.rfl

lemma has_basis_cofinite : has_basis cofinite (λ s : set α, s.finite) compl :=
⟨λ s, ⟨λ h, ⟨sᶜ, h, (compl_compl s).subset⟩, λ ⟨t, htf, hts⟩, htf.subset $ compl_subset_comm.2 hts⟩⟩

instance cofinite_ne_bot [infinite α] : ne_bot (@cofinite α) :=
has_basis_cofinite.ne_bot_iff.2 $ λ s hs, hs.infinite_compl.nonempty

lemma frequently_cofinite_iff_infinite {p : α → Prop} :
  (∃ᶠ x in cofinite, p x) ↔ set.infinite {x | p x} :=
by simp only [filter.frequently, filter.eventually, mem_cofinite, compl_set_of, not_not,
  set.infinite]

lemma _root_.set.finite.compl_mem_cofinite {s : set α} (hs : s.finite) : sᶜ ∈ (@cofinite α) :=
mem_cofinite.2 $ (compl_compl s).symm ▸ hs

lemma _root_.set.finite.eventually_cofinite_nmem {s : set α} (hs : s.finite) :
  ∀ᶠ x in cofinite, x ∉ s :=
hs.compl_mem_cofinite

lemma _root_.finset.eventually_cofinite_nmem (s : finset α) : ∀ᶠ x in cofinite, x ∉ s :=
s.finite_to_set.eventually_cofinite_nmem

lemma _root_.set.infinite_iff_frequently_cofinite {s : set α} :
  set.infinite s ↔ (∃ᶠ x in cofinite, x ∈ s) :=
frequently_cofinite_iff_infinite.symm

lemma eventually_cofinite_ne (x : α) : ∀ᶠ a in cofinite, a ≠ x :=
(set.finite_singleton x).eventually_cofinite_nmem

lemma le_cofinite_iff_compl_singleton_mem : l ≤ cofinite ↔ ∀ x, {x}ᶜ ∈ l :=
begin
  refine ⟨λ h x, h (finite_singleton x).compl_mem_cofinite, λ h s (hs : sᶜ.finite), _⟩,
  rw [← compl_compl s, ← bUnion_of_singleton sᶜ, compl_Union₂,filter.bInter_mem hs],
  exact λ x _, h x
end

lemma le_cofinite_iff_eventually_ne : l ≤ cofinite ↔ ∀ x, ∀ᶠ y in l, y ≠ x :=
le_cofinite_iff_compl_singleton_mem

/-- If `α` is a preorder with no maximal element, then `at_top ≤ cofinite`. -/
lemma at_top_le_cofinite [preorder α] [no_max_order α] : (at_top : filter α) ≤ cofinite :=
le_cofinite_iff_eventually_ne.mpr eventually_ne_at_top

lemma comap_cofinite_le (f : α → β) : comap f cofinite ≤ cofinite :=
le_cofinite_iff_eventually_ne.mpr $ λ x,
  mem_comap.2 ⟨{f x}ᶜ, (finite_singleton _).compl_mem_cofinite, λ y, ne_of_apply_ne f⟩

/-- The coproduct of the cofinite filters on two types is the cofinite filter on their product. -/
lemma coprod_cofinite : (cofinite : filter α).coprod (cofinite : filter β) = cofinite :=
filter.coext $ λ s, by simp only [compl_mem_coprod, mem_cofinite, compl_compl,
  finite_image_fst_and_snd_iff]

/-- Finite product of finite sets is finite -/
lemma Coprod_cofinite {α : ι → Type*} [finite ι] :
  filter.Coprod (λ i, (cofinite : filter (α i))) = cofinite :=
filter.coext $ λ s, by simp only [compl_mem_Coprod, mem_cofinite, compl_compl,
  forall_finite_image_eval_iff]

@[simp] lemma disjoint_cofinite_left : disjoint cofinite l ↔ ∃ s ∈ l, set.finite s :=
begin
  simp only [has_basis_cofinite.disjoint_iff l.basis_sets, id, disjoint_compl_left_iff_subset],
  exact ⟨λ ⟨s, hs, t, ht, hts⟩, ⟨t, ht, hs.subset hts⟩, λ ⟨s, hs, hsf⟩, ⟨s, hsf, s, hs, subset.rfl⟩⟩
end

@[simp] lemma disjoint_cofinite_right : disjoint l cofinite ↔ ∃ s ∈ l, set.finite s :=
disjoint.comm.trans disjoint_cofinite_left

end filter

open filter

/-- For natural numbers the filters `cofinite` and `at_top` coincide. -/
lemma nat.cofinite_eq_at_top : @cofinite ℕ = at_top :=
begin
  refine le_antisymm _ at_top_le_cofinite,
  refine at_top_basis.ge_iff.2 (λ N hN, _),
  simpa only [mem_cofinite, compl_Ici] using finite_lt_nat N
end

lemma nat.frequently_at_top_iff_infinite {p : ℕ → Prop} :
  (∃ᶠ n in at_top, p n) ↔ set.infinite {n | p n} :=
by rw [← nat.cofinite_eq_at_top, frequently_cofinite_iff_infinite]

lemma filter.tendsto.exists_within_forall_le {α β : Type*} [linear_order β] {s : set α}
  (hs : s.nonempty)
  {f : α → β} (hf : filter.tendsto f filter.cofinite filter.at_top) :
  ∃ a₀ ∈ s, ∀ a ∈ s, f a₀ ≤ f a :=
begin
  rcases em (∃ y ∈ s, ∃ x, f y < x) with ⟨y, hys, x, hx⟩|not_all_top,
  { -- the set of points `{y | f y < x}` is nonempty and finite, so we take `min` over this set
    have : {y | ¬x ≤ f y}.finite := (filter.eventually_cofinite.mp (tendsto_at_top.1 hf x)),
    simp only [not_le] at this,
    obtain ⟨a₀, ⟨ha₀ : f a₀ < x, ha₀s⟩, others_bigger⟩ :=
      exists_min_image _ f (this.inter_of_left s) ⟨y, hx, hys⟩,
    refine ⟨a₀, ha₀s, λ a has, (lt_or_le (f a) x).elim _ (le_trans ha₀.le)⟩,
    exact λ h, others_bigger a ⟨h, has⟩ },
  { -- in this case, f is constant because all values are at top
    push_neg at not_all_top,
    obtain ⟨a₀, ha₀s⟩ := hs,
    exact ⟨a₀, ha₀s, λ a ha, not_all_top a ha (f a₀)⟩ }
end

lemma filter.tendsto.exists_forall_le [nonempty α] [linear_order β] {f : α → β}
  (hf : tendsto f cofinite at_top) :
  ∃ a₀, ∀ a, f a₀ ≤ f a :=
let ⟨a₀, _, ha₀⟩ := hf.exists_within_forall_le univ_nonempty in ⟨a₀, λ a, ha₀ a (mem_univ _)⟩

lemma filter.tendsto.exists_within_forall_ge [linear_order β] {s : set α} (hs : s.nonempty)
  {f : α → β} (hf : filter.tendsto f filter.cofinite filter.at_bot) :
  ∃ a₀ ∈ s, ∀ a ∈ s, f a ≤ f a₀ :=
@filter.tendsto.exists_within_forall_le _ βᵒᵈ _ _ hs _ hf

lemma filter.tendsto.exists_forall_ge [nonempty α] [linear_order β] {f : α → β}
  (hf : tendsto f cofinite at_bot) :
  ∃ a₀, ∀ a, f a ≤ f a₀ :=
@filter.tendsto.exists_forall_le _ βᵒᵈ _ _ _ hf

/-- For an injective function `f`, inverse images of finite sets are finite. See also
`filter.comap_cofinite_le` and `function.injective.comap_cofinite_eq`. -/
lemma function.injective.tendsto_cofinite {f : α → β} (hf : injective f) :
  tendsto f cofinite cofinite :=
λ s h, h.preimage (hf.inj_on _)

/-- The pullback of the `filter.cofinite` under an injective function is equal to `filter.cofinite`.
See also `filter.comap_cofinite_le` and `function.injective.tendsto_cofinite`. -/
lemma function.injective.comap_cofinite_eq {f : α → β} (hf : injective f) :
  comap f cofinite = cofinite :=
(comap_cofinite_le f).antisymm hf.tendsto_cofinite.le_comap

/-- An injective sequence `f : ℕ → ℕ` tends to infinity at infinity. -/
lemma function.injective.nat_tendsto_at_top {f : ℕ → ℕ} (hf : injective f) :
  tendsto f at_top at_top :=
nat.cofinite_eq_at_top ▸ hf.tendsto_cofinite
