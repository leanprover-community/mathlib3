/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn, Yury Kudryashov
-/
import order.filter.lift
import order.filter.at_top_bot

/-!
# The filter of small sets

This file defines the filter of small sets w.r.t. a filter `f`, which is the largest filter
containing all powersets of members of `f`.

`g` converges to `f.small_sets` if for all `s ∈ f`, eventually we have `g x ⊆ s`.

An example usage is that if `f : ι → E → ℝ` is a family of nonnegative functions with integral 1,
then saying that `λ i, support (f i)` tendsto `(𝓝 0).small_sets` is a way of saying that 
`f` tends to the Dirac delta distribution.
-/

open_locale filter
open filter set

variables {α β : Type*} {ι : Sort*}

namespace filter

variables {l l' la : filter α} {lb : filter β}

/-- The filter `l.small_sets` is the largest filter containing all powersets of members of `l`. -/
def small_sets (l : filter α) : filter (set α) := l.lift' powerset

lemma small_sets_eq_generate {f : filter α} : f.small_sets = generate (powerset '' f.sets) :=
by { simp_rw [generate_eq_binfi, small_sets, infi_image], refl }

lemma has_basis.small_sets {p : ι → Prop} {s : ι → set α}
  (h : has_basis l p s) : has_basis l.small_sets p (λ i, 𝒫 (s i)) :=
h.lift' monotone_powerset

lemma has_basis_small_sets (l : filter α) :
  has_basis l.small_sets (λ t : set α, t ∈ l) powerset :=
l.basis_sets.small_sets

/-- `g` converges to `f.small_sets` if for all `s ∈ f`, eventually we have `g x ⊆ s`. -/
lemma tendsto_small_sets_iff {f : α → set β} :
  tendsto f la lb.small_sets ↔ ∀ t ∈ lb, ∀ᶠ x in la, f x ⊆ t :=
(has_basis_small_sets lb).tendsto_right_iff

lemma eventually_small_sets {p : set α → Prop} :
  (∀ᶠ s in l.small_sets, p s) ↔ ∃ s ∈ l, ∀ t ⊆ s, p t :=
eventually_lift'_iff monotone_powerset

lemma eventually_small_sets' {p : set α → Prop} (hp : ∀ ⦃s t⦄, s ⊆ t → p t → p s) :
  (∀ᶠ s in l.small_sets, p s) ↔ ∃ s ∈ l, p s :=
eventually_small_sets.trans $ exists₂_congr $ λ s hsf,
  ⟨λ H, H s (subset.refl s), λ hs t ht, hp ht hs⟩

lemma has_antitone_basis.tendsto_small_sets {ι} [preorder ι] {s : ι → set α}
  (hl : l.has_antitone_basis s) : tendsto s at_top l.small_sets :=
tendsto_small_sets_iff.2 $ λ t ht, hl.eventually_subset ht

@[mono] lemma monotone_small_sets : monotone (@small_sets α) :=
monotone_lift' monotone_id monotone_const

@[simp] lemma small_sets_bot : (⊥ : filter α).small_sets = pure ∅ :=
by rw [small_sets, lift'_bot monotone_powerset, powerset_empty, principal_singleton]

@[simp] lemma small_sets_top : (⊤ : filter α).small_sets = ⊤ :=
by rw [small_sets, lift'_top, powerset_univ, principal_univ]

@[simp] lemma small_sets_principal (s : set α) : (𝓟 s).small_sets = 𝓟(𝒫 s) :=
lift'_principal monotone_powerset

lemma small_sets_comap (l : filter β) (f : α → β) :
  (comap f l).small_sets = l.lift' (powerset ∘ preimage f) :=
comap_lift'_eq2 monotone_powerset

lemma comap_small_sets (l : filter β) (f : α → set β) :
  comap f l.small_sets = l.lift' (preimage f ∘ powerset) :=
comap_lift'_eq

lemma small_sets_infi {f : ι → filter α} :
  (infi f).small_sets = (⨅ i, (f i).small_sets) :=
begin
  casesI is_empty_or_nonempty ι,
  { rw [infi_of_empty f, infi_of_empty, small_sets_top] },
  { exact (lift'_infi $ λ _ _, (powerset_inter _ _).symm) },
end

lemma small_sets_inf (l₁ l₂ : filter α) :
  (l₁ ⊓ l₂).small_sets = l₁.small_sets ⊓ l₂.small_sets :=
lift'_inf _ _ $ λ _ _, (powerset_inter _ _).symm

instance small_sets_ne_bot (l : filter α) : ne_bot l.small_sets :=
(lift'_ne_bot_iff monotone_powerset).2 $ λ _ _, powerset_nonempty

lemma tendsto.small_sets_mono {s t : α → set β}
  (ht : tendsto t la lb.small_sets) (hst : ∀ᶠ x in la, s x ⊆ t x) :
  tendsto s la lb.small_sets :=
begin
  rw [tendsto_small_sets_iff] at ht ⊢,
  exact λ u hu, (ht u hu).mp (hst.mono $ λ a hst ht, subset.trans hst ht)
end

@[simp] lemma eventually_small_sets_eventually {p : α → Prop} :
  (∀ᶠ s in l.small_sets, ∀ᶠ x in l', x ∈ s → p x) ↔ ∀ᶠ x in l ⊓ l', p x :=
calc _ ↔ ∃ s ∈ l, ∀ᶠ x in l', x ∈ s → p x :
  eventually_small_sets' $ λ s t hst ht, ht.mono $ λ x hx hs, hx (hst hs)
... ↔ ∃ (s ∈ l) (t ∈ l'), ∀ x, x ∈ t → x ∈ s → p x :
  by simp only [eventually_iff_exists_mem]
... ↔ ∀ᶠ x in l ⊓ l', p x : by simp only [eventually_inf, and_comm, mem_inter_iff, ← and_imp]

@[simp] lemma eventually_small_sets_forall {p : α → Prop} :
  (∀ᶠ s in l.small_sets, ∀ x ∈ s, p x) ↔ ∀ᶠ x in l, p x :=
by simpa only [inf_top_eq, eventually_top] using @eventually_small_sets_eventually α l ⊤ p

alias eventually_small_sets_forall ↔ filter.eventually.of_small_sets filter.eventually.small_sets

@[simp] lemma eventually_small_sets_subset {s : set α} :
  (∀ᶠ t in l.small_sets, t ⊆ s) ↔ s ∈ l :=
eventually_small_sets_forall

end filter
