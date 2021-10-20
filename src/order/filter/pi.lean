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

lemma mem_pi_of_mem (i : ι) {s : set (α i)} (hs : s ∈ f i) :
  eval i ⁻¹' s ∈ pi f :=
mem_infi_of_mem i $ preimage_mem_comap hs

lemma mem_pi {s : set (Π i, α i)} : s ∈ pi f ↔
  ∃ (I : set ι), finite I ∧ ∃ t : Π i, set (α i), (∀ i, t i ∈ f i) ∧
    (⋂ i ∈ I, (eval i : (Π j, α j) → α i) ⁻¹' t i) ⊆ s :=
begin
  split,
  { simp only [pi, mem_infi', mem_comap],
    rintro ⟨I, If, V, hVf, hVI, rfl, -⟩, choose t htf htV using hVf,
    exact ⟨I, If, t, htf, bInter_mono (λ i _, htV i)⟩ },
  { rintro ⟨I, If, t, htf, hts⟩,
    rw bInter_eq_Inter at hts,
    refine mem_infi_of_Inter If (λ i, _) hts,
    exact preimage_mem_comap (htf i) }
end

@[simp] lemma pi_inf_principal_pi_eq_bot :
  pi f ⊓ 𝓟 (set.pi univ s) = ⊥ ↔ ∃ i, f i ⊓ 𝓟 (s i) = ⊥ :=
begin
  split,
  { simp only [inf_principal_eq_bot, mem_pi], contrapose!,
    rintros (hsf : ∀ i, ∃ᶠ x in f i, x ∈ s i) I If t htf hts,
    have : ∀ i, (s i ∩ t i).nonempty, from λ i, ((hsf i).and_eventually (htf i)).exists,
    choose x hxs hxt,
    exact hts (mem_bInter (λ i hi, hxt i)) (mem_univ_pi.2 hxs) },
  { simp only [inf_principal_eq_bot],
    rintro ⟨i, hi⟩,
    filter_upwards [mem_pi_of_mem i hi],
    exact λ x, mt (λ h, h i trivial) }
end

@[simp] lemma pi_inf_principal_pi_ne_bot :
  ne_bot (pi f ⊓ 𝓟 (set.pi univ s)) ↔ ∀ i, ne_bot (f i ⊓ 𝓟 (s i)) :=
by simp [ne_bot_iff]

instance pi_inf_principal_pi.ne_bot [∀ i, ne_bot (f i ⊓ 𝓟 (s i))] :
  ne_bot (pi f ⊓ 𝓟 (set.pi univ s)) :=
pi_inf_principal_pi_ne_bot.2 ‹_›

@[simp] lemma pi_eq_bot : pi f = ⊥ ↔ ∃ i, f i = ⊥ :=
by simpa using @pi_inf_principal_pi_eq_bot ι α f (λ _, univ)

@[simp] lemma pi_ne_bot : ne_bot (pi f) ↔ ∀ i, ne_bot (f i) := by simp [ne_bot_iff]

instance [∀ i, ne_bot (f i)] : ne_bot (pi f) := pi_ne_bot.2 ‹_›

end filter
