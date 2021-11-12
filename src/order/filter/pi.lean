import order.filter.basic

open set function
open_locale classical filter

namespace filter

variables {ι : Type*} {α : ι → Type*} {f : Π i, filter (α i)} {s : Π i, set (α i)}

def pi (f : Π i, filter (α i)) : filter (Π i, α i) := ⨅ i, comap (function.eval i) (f i)

lemma tendsto_eval_pi (f : Π i, filter (α i)) (i : ι) :
  tendsto (eval i) (pi f) (f i) :=
tendsto_infi' i tendsto_comap

lemma tendsto_pi {β : Type*} {m : β → Π i, α i} {l : filter β} :
  tendsto m l (pi f) ↔ ∀ i, tendsto (λ x, m x i) l (f i) :=
by simp only [pi, tendsto_infi, tendsto_comap_iff]

lemma le_pi {g : filter (Π i, α i)} : g ≤ pi f ↔ ∀ i, tendsto (eval i) g (f i) := tendsto_pi

lemma mem_pi_of_mem (i : ι) {s : set (α i)} (hs : s ∈ f i) :
  eval i ⁻¹' s ∈ pi f :=
mem_infi_of_mem i $ preimage_mem_comap hs

lemma pi_mem_pi {I : set ι} (hI : finite I) (h : ∀ i ∈ I, s i ∈ f i) :
  I.pi s ∈ pi f :=
begin
  rw [pi_def, bInter_eq_Inter],
  refine mem_infi_of_Inter hI (λ i, _) subset.rfl,
  exact preimage_mem_comap (h i i.2)
end

lemma mem_pi {s : set (Π i, α i)} : s ∈ pi f ↔
  ∃ (I : set ι), finite I ∧ ∃ t : Π i, set (α i), (∀ i, t i ∈ f i) ∧ I.pi t ⊆ s :=
begin
  split,
  { simp only [pi, mem_infi', mem_comap, pi_def],
    rintro ⟨I, If, V, hVf, hVI, rfl, -⟩, choose t htf htV using hVf,
    exact ⟨I, If, t, htf, bInter_mono (λ i _, htV i)⟩ },
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
  { intros j hj, rcases eq_or_ne j i with (rfl|hne); simp * },
  simpa using hts this i hi
end

@[simp] lemma pi_mem_pi_iff [∀ i, ne_bot (f i)] {I : set ι} (hI : finite I) :
  I.pi s ∈ pi f ↔ ∀ i ∈ I, s i ∈ f i :=
⟨λ h i hi, mem_of_pi_mem_pi h hi, pi_mem_pi hI⟩

@[simp] lemma pi_inf_principal_univ_pi_eq_bot :
  pi f ⊓ 𝓟 (set.pi univ s) = ⊥ ↔ ∃ i, f i ⊓ 𝓟 (s i) = ⊥ :=
begin
  split,
  { simp only [inf_principal_eq_bot, mem_pi], contrapose!,
    rintros (hsf : ∀ i, ∃ᶠ x in f i, x ∈ s i) I If t htf hts,
    have : ∀ i, (s i ∩ t i).nonempty, from λ i, ((hsf i).and_eventually (htf i)).exists,
    choose x hxs hxt,
    exact hts (λ i hi, hxt i) (mem_univ_pi.2 hxs) },
  { simp only [inf_principal_eq_bot],
    rintro ⟨i, hi⟩,
    filter_upwards [mem_pi_of_mem i hi],
    exact λ x, mt (λ h, h i trivial) }
end

@[simp] lemma pi_inf_principal_pi_eq_bot [Π i, ne_bot (f i)] {I : set ι} :
  pi f ⊓ 𝓟 (set.pi I s) = ⊥ ↔ ∃ i ∈ I, f i ⊓ 𝓟 (s i) = ⊥ :=
begin
  rw [← univ_pi_piecewise I, pi_inf_principal_univ_pi_eq_bot],
  refine exists_congr (λ i, _),
  by_cases hi : i ∈ I; simp [hi, (‹Π i, ne_bot (f i)› i).ne]
end

@[simp] lemma pi_inf_principal_univ_pi_ne_bot :
  ne_bot (pi f ⊓ 𝓟 (set.pi univ s)) ↔ ∀ i, ne_bot (f i ⊓ 𝓟 (s i)) :=
by simp [ne_bot_iff]

@[simp] lemma pi_inf_principal_pi_ne_bot [Π i, ne_bot (f i)] {I : set ι} :
  ne_bot (pi f ⊓ 𝓟 (I.pi s)) ↔ ∀ i ∈ I, ne_bot (f i ⊓ 𝓟 (s i)) :=
by simp [ne_bot_iff]

instance pi_inf_principal_pi.ne_bot [h : ∀ i, ne_bot (f i ⊓ 𝓟 (s i))] {I : set ι} :
  ne_bot (pi f ⊓ 𝓟 (I.pi s)) :=
(pi_inf_principal_univ_pi_ne_bot.2 ‹_›).mono $ inf_le_inf_left _ $ principal_mono.2 $
  λ x hx i hi, hx i trivial

@[simp] lemma pi_eq_bot : pi f = ⊥ ↔ ∃ i, f i = ⊥ :=
by simpa using @pi_inf_principal_univ_pi_eq_bot ι α f (λ _, univ)

@[simp] lemma pi_ne_bot : ne_bot (pi f) ↔ ∀ i, ne_bot (f i) := by simp [ne_bot_iff]

instance [∀ i, ne_bot (f i)] : ne_bot (pi f) := pi_ne_bot.2 ‹_›

end filter
