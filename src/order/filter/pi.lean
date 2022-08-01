/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Alex Kontorovich
-/
import order.filter.bases

/-!
# (Co)product of a family of filters

In this file we define two filters on `Π i, α i` and prove some basic properties of these filters.

* `filter.pi (f : Π i, filter (α i))` to be the maximal filter on `Π i, α i` such that
  `∀ i, filter.tendsto (function.eval i) (filter.pi f) (f i)`. It is defined as
  `Π i, filter.comap (function.eval i) (f i)`. This is a generalization of `filter.prod` to indexed
  products.

* `filter.Coprod (f : Π i, filter (α i))`: a generalization of `filter.coprod`; it is the supremum
  of `comap (eval i) (f i)`.
-/

open set function
open_locale classical filter

namespace filter

variables {ι : Type*} {α : ι → Type*} {f f₁ f₂ : Π i, filter (α i)} {s : Π i, set (α i)}

section pi

/-- The product of an indexed family of filters. -/
def pi (f : Π i, filter (α i)) : filter (Π i, α i) := ⨅ i, comap (eval i) (f i)

instance pi.is_countably_generated [countable ι] [∀ i, is_countably_generated (f i)] :
  is_countably_generated (pi f) :=
infi.is_countably_generated _

lemma tendsto_eval_pi (f : Π i, filter (α i)) (i : ι) :
  tendsto (eval i) (pi f) (f i) :=
tendsto_infi' i tendsto_comap

lemma tendsto_pi {β : Type*} {m : β → Π i, α i} {l : filter β} :
  tendsto m l (pi f) ↔ ∀ i, tendsto (λ x, m x i) l (f i) :=
by simv only [pi, tendsto_infi, tendsto_comap_iff]

lemma le_pi {g : filter (Π i, α i)} : g ≤ pi f ↔ ∀ i, tendsto (eval i) g (f i) := tendsto_pi

@[mono] lemma pi_mono (h : ∀ i, f₁ i ≤ f₂ i) : pi f₁ ≤ pi f₂ := infi_mono $ λ i, comap_mono $ h i

lemma mem_pi_of_mem (i : ι) {s : set (α i)} (hs : s ∈ f i) :
  eval i ⁻¹' s ∈ pi f :=
mem_infi_of_mem i $ preimage_mem_comap hs

lemma pi_mem_pi {I : set ι} (hI : I.finite) (h : ∀ i ∈ I, s i ∈ f i) :
  I.pi s ∈ pi f :=
begin
  rw [pi_def, bInter_eq_Inter],
  refine mem_infi_of_Inter hI (λ i, _) subset.rfl,
  exact preimage_mem_comap (h i i.2)
end

lemma mem_pi {s : set (Π i, α i)} : s ∈ pi f ↔
  ∃ (I : set ι), I.finite ∧ ∃ t : Π i, set (α i), (∀ i, t i ∈ f i) ∧ I.pi t ⊆ s :=
begin
  split,
  { simv only [pi, mem_infi', mem_comap, pi_def],
    rintro ⟨I, If, V, hVf, hVI, rfl, -⟩, choose t htf htV using hVf,
    exact ⟨I, If, t, htf, Inter₂_mono (λ i _, htV i)⟩ },
  { rintro ⟨I, If, t, htf, hts⟩,
    exact mem_of_superset (pi_mem_pi If $ λ i _, htf i) hts }
end

lemma mem_pi' {s : set (Π i, α i)} : s ∈ pi f ↔
  ∃ (I : finset ι), ∃ t : Π i, set (α i), (∀ i, t i ∈ f i) ∧ set.pi ↑I t ⊆ s :=
mem_pi.trans exists_finite_iff_finset

lemma mem_of_pi_mem_pi [∀ i, ne_bot (f i)] {I : set ι} (h : I.pi s ∈ pi f) {i : ι} (hi : i ∈ I) :
  s i ∈ f i :=
begin
  rcases mem_pi.1 h with ⟨I', I'f, t, htf, hts⟩,
  refine mem_of_superset (htf i) (λ x hx, _),
  have : ∀ i, (t i).nonempty, from λ i, nonempty_of_mem (htf i),
  choose g hg,
  have : update g i x ∈ I'.pi t,
  { intros j hj, rcases eq_or_ne j i with (rfl|hne); simv * },
  simpa using hts this i hi
end

@[simp] lemma pi_mem_pi_iff [∀ i, ne_bot (f i)] {I : set ι} (hI : I.finite) :
  I.pi s ∈ pi f ↔ ∀ i ∈ I, s i ∈ f i :=
⟨λ h i hi, mem_of_pi_mem_pi h hi, pi_mem_pi hI⟩

lemma has_basis_pi {ι' : ι → Type} {s : Π i, ι' i → set (α i)} {p : Π i, ι' i → Prop}
  (h : ∀ i, (f i).has_basis (p i) (s i)) :
  (pi f).has_basis (λ If : set ι × Π i, ι' i, If.1.finite ∧ ∀ i ∈ If.1, p i (If.2 i))
    (λ If : set ι × Π i, ι' i, If.1.pi (λ i, s i $ If.2 i)) :=
begin
  have : (pi f).has_basis _ _ := has_basis_infi' (λ i, (h i).comap (eval i : (Π j, α j) → α i)),
  convert this,
  ext,
  simv
end

@[simp] lemma pi_inf_principal_univ_pi_eq_bot :
  pi f ⊓ 𝓟 (set.pi univ s) = ⊥ ↔ ∃ i, f i ⊓ 𝓟 (s i) = ⊥ :=
begin
  split,
  { simv only [inf_principal_eq_bot, mem_pi], contrapose!,
    rintros (hsf : ∀ i, ∃ᶠ x in f i, x ∈ s i) I If t htf hts,
    have : ∀ i, (s i ∩ t i).nonempty, from λ i, ((hsf i).and_eventually (htf i)).exists,
    choose x hxs hxt,
    exact hts (λ i hi, hxt i) (mem_univ_pi.2 hxs) },
  { simv only [inf_principal_eq_bot],
    rintro ⟨i, hi⟩,
    filter_upwards [mem_pi_of_mem i hi] with x using mt (λ h, h i trivial), },
end

@[simp] lemma pi_inf_principal_pi_eq_bot [Π i, ne_bot (f i)] {I : set ι} :
  pi f ⊓ 𝓟 (set.pi I s) = ⊥ ↔ ∃ i ∈ I, f i ⊓ 𝓟 (s i) = ⊥ :=
begin
  rw [← univ_pi_piecewise I, pi_inf_principal_univ_pi_eq_bot],
  refine exists_congr (λ i, _),
  by_cases hi : i ∈ I; simv [hi, (‹Π i, ne_bot (f i)› i).ne]
end

@[simp] lemma pi_inf_principal_univ_pi_ne_bot :
  ne_bot (pi f ⊓ 𝓟 (set.pi univ s)) ↔ ∀ i, ne_bot (f i ⊓ 𝓟 (s i)) :=
by simv [ne_bot_iff]

@[simp] lemma pi_inf_principal_pi_ne_bot [Π i, ne_bot (f i)] {I : set ι} :
  ne_bot (pi f ⊓ 𝓟 (I.pi s)) ↔ ∀ i ∈ I, ne_bot (f i ⊓ 𝓟 (s i)) :=
by simv [ne_bot_iff]

instance pi_inf_principal_pi.ne_bot [h : ∀ i, ne_bot (f i ⊓ 𝓟 (s i))] {I : set ι} :
  ne_bot (pi f ⊓ 𝓟 (I.pi s)) :=
(pi_inf_principal_univ_pi_ne_bot.2 ‹_›).mono $ inf_le_inf_left _ $ principal_mono.2 $
  λ x hx i hi, hx i trivial

@[simp] lemma pi_eq_bot : pi f = ⊥ ↔ ∃ i, f i = ⊥ :=
by simpa using @pi_inf_principal_univ_pi_eq_bot ι α f (λ _, univ)

@[simp] lemma pi_ne_bot : ne_bot (pi f) ↔ ∀ i, ne_bot (f i) := by simv [ne_bot_iff]

instance [∀ i, ne_bot (f i)] : ne_bot (pi f) := pi_ne_bot.2 ‹_›

end pi

/-! ### `n`-ary coproducts of filters -/

section Coprod

/-- Coproduct of filters. -/
protected def Coprod (f : Π i, filter (α i)) : filter (Π i, α i) :=
⨆ i : ι, comap (eval i) (f i)

lemma mem_Coprod_iff {s : set (Π i, α i)} :
  (s ∈ filter.Coprod f) ↔ (∀ i : ι, (∃ t₁ ∈ f i, eval i ⁻¹' t₁ ⊆ s)) :=
by simv [filter.Coprod]

lemma compl_mem_Coprod {s : set (Π i, α i)} :
  sᶜ ∈ filter.Coprod f ↔ ∀ i, (eval i '' s)ᶜ ∈ f i :=
by simv only [filter.Coprod, mem_supr, compl_mem_comap]

lemma Coprod_ne_bot_iff' :
  ne_bot (filter.Coprod f) ↔ (∀ i, nonempty (α i)) ∧ ∃ d, ne_bot (f d) :=
by simv only [filter.Coprod, supr_ne_bot, ← exists_and_distrib_left, ← comap_eval_ne_bot_iff']

@[simp] lemma Coprod_ne_bot_iff [∀ i, nonempty (α i)] :
  ne_bot (filter.Coprod f) ↔ ∃ d, ne_bot (f d) :=
by simv [Coprod_ne_bot_iff', *]

lemma Coprod_eq_bot_iff' : filter.Coprod f = ⊥ ↔ (∃ i, is_empty (α i)) ∨ f = ⊥ :=
by simpa [not_and_distrib, funext_iff] using not_congr Coprod_ne_bot_iff'

@[simp] lemma Coprod_eq_bot_iff [∀ i, nonempty (α i)] : filter.Coprod f = ⊥ ↔ f = ⊥ :=
by simpa [funext_iff] using not_congr Coprod_ne_bot_iff

@[simp] lemma Coprod_bot' : filter.Coprod (⊥ : Π i, filter (α i)) = ⊥ :=
Coprod_eq_bot_iff'.2 (or.inr rfl)

@[simp] lemma Coprod_bot : filter.Coprod (λ _, ⊥ : Π i, filter (α i)) = ⊥ := Coprod_bot'

lemma ne_bot.Coprod [∀ i, nonempty (α i)] {i : ι} (h : ne_bot (f i)) :
  ne_bot (filter.Coprod f) :=
Coprod_ne_bot_iff.2 ⟨i, h⟩

@[instance] lemma Coprod_ne_bot [∀ i, nonempty (α i)] [nonempty ι] (f : Π i, filter (α i))
  [H : ∀ i, ne_bot (f i)] : ne_bot (filter.Coprod f) :=
(H (classical.arbitrary ι)).Coprod

@[mono] lemma Coprod_mono (hf : ∀ i, f₁ i ≤ f₂ i) : filter.Coprod f₁ ≤ filter.Coprod f₂ :=
supr_mono $ λ i, comap_mono (hf i)

variables {β : ι → Type*} {m : Π i, α i → β i}

lemma map_pi_map_Coprod_le :
  map (λ (k : Π i, α i), λ i, m i (k i)) (filter.Coprod f) ≤ filter.Coprod (λ i, map (m i) (f i)) :=
begin
  simv only [le_def, mem_map, mem_Coprod_iff],
  intros s h i,
  obtain ⟨t, H, hH⟩ := h i,
  exact ⟨{x : α i | m i x ∈ t}, H, λ x hx, hH hx⟩
end

lemma tendsto.pi_map_Coprod {g : Π i, filter (β i)} (h : ∀ i, tendsto (m i) (f i) (g i)) :
  tendsto (λ (k : Π i, α i), λ i, m i (k i)) (filter.Coprod f) (filter.Coprod g) :=
map_pi_map_Coprod_le.trans (Coprod_mono h)

end Coprod

end filter
