/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.filter.bases

/-!
# Lift filters along filter and set functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open set

open_locale classical filter

namespace filter
variables {α : Type*} {β : Type*} {γ : Type*} {ι : Sort*}

section lift

/-- A variant on `bind` using a function `g` taking a set instead of a member of `α`.
This is essentially a push-forward along a function mapping each set to a filter. -/
protected def lift (f : filter α) (g : set α → filter β) :=
⨅s ∈ f, g s

variables {f f₁ f₂ : filter α} {g g₁ g₂ : set α → filter β}

@[simp] lemma lift_top (g : set α → filter β) : (⊤ : filter α).lift g = g univ :=
by simp [filter.lift]

/-- If `(p : ι → Prop, s : ι → set α)` is a basis of a filter `f`, `g` is a monotone function
`set α → filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → set α)` is a basis
of the filter `g (s i)`, then `(λ (i : ι) (x : β i), p i ∧ pg i x, λ (i : ι) (x : β i), sg i x)`
is a basis of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate this fact using
`has_basis` one has to use `Σ i, β i` as the index type, see `filter.has_basis.lift`.
This lemma states the corresponding `mem_iff` statement without using a sigma type. -/
lemma has_basis.mem_lift_iff {ι} {p : ι → Prop} {s : ι → set α} {f : filter α}
  (hf : f.has_basis p s) {β : ι → Type*} {pg : Π i, β i → Prop} {sg : Π i, β i → set γ}
  {g : set α → filter γ} (hg : ∀ i, (g $ s i).has_basis (pg i) (sg i)) (gm : monotone g)
  {s : set γ} :
  s ∈ f.lift g ↔ ∃ (i : ι) (hi : p i) (x : β i) (hx : pg i x), sg i x ⊆ s :=
begin
  refine (mem_binfi_of_directed _ ⟨univ, univ_sets _⟩).trans _,
  { intros t₁ ht₁ t₂ ht₂,
    exact ⟨t₁ ∩ t₂, inter_mem ht₁ ht₂, gm $ inter_subset_left _ _,
      gm $ inter_subset_right _ _⟩ },
  { simp only [← (hg _).mem_iff],
    exact hf.exists_iff (λ t₁ t₂ ht H, gm ht H) }
end

/-- If `(p : ι → Prop, s : ι → set α)` is a basis of a filter `f`, `g` is a monotone function
`set α → filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → set α)` is a basis
of the filter `g (s i)`, then `(λ (i : ι) (x : β i), p i ∧ pg i x, λ (i : ι) (x : β i), sg i x)`
is a basis of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate this fact using
`has_basis` one has to use `Σ i, β i` as the index type. See also `filter.has_basis.mem_lift_iff`
for the corresponding `mem_iff` statement formulated without using a sigma type. -/
lemma has_basis.lift {ι} {p : ι → Prop} {s : ι → set α} {f : filter α} (hf : f.has_basis p s)
  {β : ι → Type*} {pg : Π i, β i → Prop} {sg : Π i, β i → set γ} {g : set α → filter γ}
  (hg : ∀ i, (g $ s i).has_basis (pg i) (sg i)) (gm : monotone g) :
  (f.lift g).has_basis (λ i : Σ i, β i, p i.1 ∧ pg i.1 i.2) (λ i : Σ i, β i, sg i.1 i.2) :=
begin
  refine ⟨λ t, (hf.mem_lift_iff hg gm).trans _⟩,
  simp [sigma.exists, and_assoc, exists_and_distrib_left]
end

lemma mem_lift_sets (hg : monotone g) {s : set β} :
  s ∈ f.lift g ↔ ∃t∈f, s ∈ g t :=
(f.basis_sets.mem_lift_iff (λ s, (g s).basis_sets) hg).trans $
  by simp only [id, exists_mem_subset_iff]

lemma sInter_lift_sets (hg : monotone g) :
  ⋂₀ {s | s ∈ f.lift g} = ⋂ s ∈ f, ⋂₀ {t | t ∈ g s} :=
by simp only [sInter_eq_bInter, mem_set_of_eq, filter.mem_sets, mem_lift_sets hg,
  Inter_exists, @Inter_comm _ (set β)]

lemma mem_lift {s : set β} {t : set α} (ht : t ∈ f) (hs : s ∈ g t) :
  s ∈ f.lift g :=
le_principal_iff.mp $ show f.lift g ≤ 𝓟 s,
  from infi_le_of_le t $ infi_le_of_le ht $ le_principal_iff.mpr hs

lemma lift_le {f : filter α} {g : set α → filter β} {h : filter β} {s : set α}
  (hs : s ∈ f) (hg : g s ≤ h) : f.lift g ≤ h :=
infi₂_le_of_le s hs hg

lemma le_lift {f : filter α} {g : set α → filter β} {h : filter β} :
  h ≤ f.lift g ↔ ∀ s ∈ f, h ≤ g s :=
le_infi₂_iff

lemma lift_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.lift g₁ ≤ f₂.lift g₂ :=
infi_mono $ λ s, infi_mono' $ λ hs, ⟨hf hs, hg s⟩

lemma lift_mono' (hg : ∀s ∈ f, g₁ s ≤ g₂ s) : f.lift g₁ ≤ f.lift g₂ := infi₂_mono hg

lemma tendsto_lift {m : γ → β} {l : filter γ} :
  tendsto m l (f.lift g) ↔ ∀ s ∈ f, tendsto m l (g s) :=
by simp only [filter.lift, tendsto_infi]

lemma map_lift_eq {m : β → γ} (hg : monotone g) : map m (f.lift g) = f.lift (map m ∘ g) :=
have monotone (map m ∘ g),
  from map_mono.comp hg,
filter.ext $ λ s,
  by simp only [mem_lift_sets hg, mem_lift_sets this, exists_prop, mem_map, function.comp_app]

lemma comap_lift_eq {m : γ → β} : comap m (f.lift g) = f.lift (comap m ∘ g) :=
by simp only [filter.lift, comap_infi]

theorem comap_lift_eq2 {m : β → α} {g : set β → filter γ} (hg : monotone g) :
  (comap m f).lift g = f.lift (g ∘ preimage m) :=
le_antisymm
  (le_infi₂ $ λ s hs, infi₂_le (m ⁻¹' s) ⟨s, hs, subset.rfl⟩)
  (le_infi₂ $ λ s ⟨s', hs', (h_sub : m ⁻¹' s' ⊆ s)⟩, infi₂_le_of_le s' hs' $ hg h_sub)

lemma lift_map_le {g : set β → filter γ} {m : α → β} :
  (map m f).lift g ≤ f.lift (g ∘ image m) :=
le_lift.2 $ λ s hs, lift_le (image_mem_map hs) le_rfl

lemma map_lift_eq2 {g : set β → filter γ} {m : α → β} (hg : monotone g) :
  (map m f).lift g = f.lift (g ∘ image m) :=
lift_map_le.antisymm $ le_lift.2 $ λ s hs, lift_le hs $ hg $ image_preimage_subset _ _

lemma lift_comm {g : filter β} {h : set α → set β → filter γ} :
  f.lift (λs, g.lift (h s)) = g.lift (λt, f.lift (λs, h s t)) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume hi, le_infi $ assume j, le_infi $ assume hj,
    infi_le_of_le j $ infi_le_of_le hj $ infi_le_of_le i $ infi_le _ hi)
  (le_infi $ assume i, le_infi $ assume hi, le_infi $ assume j, le_infi $ assume hj,
    infi_le_of_le j $ infi_le_of_le hj $ infi_le_of_le i $ infi_le _ hi)

lemma lift_assoc {h : set β → filter γ} (hg : monotone g)  :
  (f.lift g).lift h = f.lift (λs, (g s).lift h) :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
    infi_le_of_le t $ infi_le _ $ (mem_lift_sets hg).mpr ⟨_, hs, ht⟩)
  (le_infi $ assume t, le_infi $ assume ht,
    let ⟨s, hs, h'⟩ := (mem_lift_sets hg).mp ht in
    infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le t $ infi_le _ h')

lemma lift_lift_same_le_lift {g : set α → set α → filter β} :
  f.lift (λs, f.lift (g s)) ≤ f.lift (λs, g s s) :=
le_lift.2 $ λ s hs, lift_le hs $ lift_le hs le_rfl

lemma lift_lift_same_eq_lift {g : set α → set α → filter β}
  (hg₁ : ∀s, monotone (λt, g s t)) (hg₂ : ∀t, monotone (λs, g s t)) :
  f.lift (λs, f.lift (g s)) = f.lift (λs, g s s) :=
lift_lift_same_le_lift.antisymm $
  le_lift.2 $ λ s hs, le_lift.2 $ λ t ht, lift_le (inter_mem hs ht) $
    calc g (s ∩ t) (s ∩ t) ≤ g s (s ∩ t) : hg₂ (s ∩ t) (inter_subset_left _ _)
                       ... ≤ g s t       : hg₁ s (inter_subset_right _ _)

lemma lift_principal {s : set α} (hg : monotone g) :
  (𝓟 s).lift g = g s :=
(lift_le (mem_principal_self _) le_rfl).antisymm (le_lift.2 $ λ t ht, hg ht)

theorem monotone_lift [preorder γ] {f : γ → filter α} {g : γ → set α → filter β}
  (hf : monotone f) (hg : monotone g) : monotone (λc, (f c).lift (g c)) :=
assume a b h, lift_mono (hf h) (hg h)

lemma lift_ne_bot_iff (hm : monotone g) : (ne_bot $ f.lift g) ↔ (∀s∈f, ne_bot (g s)) :=
by simp only [ne_bot_iff, ne.def, ← empty_mem_iff_bot, mem_lift_sets hm, not_exists]

@[simp] lemma lift_const {f : filter α} {g : filter β} : f.lift (λx, g) = g :=
infi_subtype'.trans infi_const

@[simp] lemma lift_inf {f : filter α} {g h : set α → filter β} :
  f.lift (λx, g x ⊓ h x) = f.lift g ⊓ f.lift h :=
by simp only [filter.lift, infi_inf_eq]

@[simp] lemma lift_principal2 {f : filter α} : f.lift 𝓟 = f :=
le_antisymm
  (assume s hs, mem_lift hs (mem_principal_self s))
  (le_infi $ assume s, le_infi $ assume hs, by simp only [hs, le_principal_iff])

lemma lift_infi_le {f : ι → filter α} {g : set α → filter β} :
  (infi f).lift g ≤ ⨅ i, (f i).lift g :=
le_infi $ λ i, lift_mono (infi_le _ _) le_rfl

lemma lift_infi [nonempty ι] {f : ι → filter α} {g : set α → filter β}
  (hg : ∀ s t, g (s ∩ t) = g s ⊓ g t) : (infi f).lift g = (⨅i, (f i).lift g) :=
begin
  refine lift_infi_le.antisymm (λ s, _),
  have H : ∀ t ∈ infi f, (⨅ i, (f i).lift g) ≤ g t,
  { intros t ht,
    refine infi_sets_induct ht _ (λ i s t hs ht, _),
    { inhabit ι,
      exact infi₂_le_of_le default univ (infi_le _ univ_mem) },
    { rw hg,
      exact le_inf (infi₂_le_of_le i s $ infi_le _ hs) ht } },
  simp only [mem_lift_sets (monotone.of_map_inf hg), exists_imp_distrib],
  exact λ t ht hs, H t ht hs
end

lemma lift_infi_of_directed [nonempty ι] {f : ι → filter α} {g : set α → filter β}
  (hf : directed (≥) f) (hg : monotone g) : (infi f).lift g = (⨅i, (f i).lift g) :=
lift_infi_le.antisymm $ λ s,
  begin
    simp only [mem_lift_sets hg, exists_imp_distrib, mem_infi_of_directed hf],
    exact assume t i ht hs, mem_infi_of_mem i $ mem_lift ht hs
  end

lemma lift_infi_of_map_univ {f : ι → filter α} {g : set α → filter β}
  (hg : ∀ s t, g (s ∩ t) = g s ⊓ g t) (hg' : g univ = ⊤) :
  (infi f).lift g = (⨅i, (f i).lift g) :=
begin
  casesI is_empty_or_nonempty ι,
  { simp [infi_of_empty, hg'] },
  { exact lift_infi hg }
end

end lift

section lift'
/-- Specialize `lift` to functions `set α → set β`. This can be viewed as a generalization of `map`.
This is essentially a push-forward along a function mapping each set to a set. -/
protected def lift' (f : filter α) (h : set α → set β) :=
f.lift (𝓟 ∘ h)

variables {f f₁ f₂ : filter α} {h h₁ h₂ : set α → set β}

@[simp] lemma lift'_top (h : set α → set β) : (⊤ : filter α).lift' h = 𝓟 (h univ) :=
lift_top _

lemma mem_lift' {t : set α} (ht : t ∈ f) : h t ∈ (f.lift' h) :=
le_principal_iff.mp $ show f.lift' h ≤ 𝓟 (h t),
  from infi_le_of_le t $ infi_le_of_le ht $ le_rfl

lemma tendsto_lift' {m : γ → β} {l : filter γ} :
  tendsto m l (f.lift' h) ↔ ∀ s ∈ f, ∀ᶠ a in l, m a ∈ h s :=
by simp only [filter.lift', tendsto_lift, tendsto_principal]

lemma has_basis.lift' {ι} {p : ι → Prop} {s} (hf : f.has_basis p s) (hh : monotone h) :
  (f.lift' h).has_basis p (h ∘ s) :=
begin
  refine ⟨λ t, (hf.mem_lift_iff _ (monotone_principal.comp hh)).trans _⟩,
  show ∀ i, (𝓟 (h (s i))).has_basis (λ j : unit, true) (λ (j : unit), h (s i)),
    from λ i, has_basis_principal _,
  simp only [exists_const]
end

lemma mem_lift'_sets (hh : monotone h) {s : set β} : s ∈ f.lift' h ↔ ∃ t ∈ f, h t ⊆ s :=
mem_lift_sets $ monotone_principal.comp hh

lemma eventually_lift'_iff (hh : monotone h) {p : β → Prop} :
  (∀ᶠ y in f.lift' h, p y) ↔ (∃ t ∈ f, ∀ y ∈ h t, p y) :=
mem_lift'_sets hh

lemma sInter_lift'_sets (hh : monotone h) :
  ⋂₀ {s | s ∈ f.lift' h} = ⋂ s ∈ f, h s :=
(sInter_lift_sets (monotone_principal.comp hh)).trans $ Inter₂_congr $ λ s hs, cInf_Ici

lemma lift'_le {f : filter α} {g : set α → set β} {h : filter β} {s : set α}
  (hs : s ∈ f) (hg : 𝓟 (g s) ≤ h) : f.lift' g ≤ h :=
lift_le hs hg

lemma lift'_mono (hf : f₁ ≤ f₂) (hh : h₁ ≤ h₂) : f₁.lift' h₁ ≤ f₂.lift' h₂ :=
lift_mono hf $ assume s, principal_mono.mpr $ hh s

lemma lift'_mono' (hh : ∀s∈f, h₁ s ⊆ h₂ s) : f.lift' h₁ ≤ f.lift' h₂ :=
infi₂_mono $ λ s hs, principal_mono.mpr $ hh s hs

lemma lift'_cong (hh : ∀s∈f, h₁ s = h₂ s) : f.lift' h₁ = f.lift' h₂ :=
le_antisymm (lift'_mono' $ assume s hs, le_of_eq $ hh s hs)
  (lift'_mono' $ assume s hs, le_of_eq $ (hh s hs).symm)

lemma map_lift'_eq {m : β → γ} (hh : monotone h) : map m (f.lift' h) = f.lift' (image m ∘ h) :=
calc map m (f.lift' h) = f.lift (map m ∘ 𝓟 ∘ h) :
    map_lift_eq $ monotone_principal.comp hh
  ... = f.lift' (image m ∘ h) : by simp only [(∘), filter.lift', map_principal, eq_self_iff_true]

lemma lift'_map_le {g : set β → set γ} {m : α → β} : (map m f).lift' g ≤ f.lift' (g ∘ image m) :=
lift_map_le

lemma map_lift'_eq2 {g : set β → set γ} {m : α → β} (hg : monotone g) :
  (map m f).lift' g = f.lift' (g ∘ image m) :=
map_lift_eq2 $ monotone_principal.comp hg

theorem comap_lift'_eq {m : γ → β} : comap m (f.lift' h) = f.lift' (preimage m ∘ h) :=
by simp only [filter.lift', comap_lift_eq, (∘), comap_principal]

theorem comap_lift'_eq2 {m : β → α} {g : set β → set γ} (hg : monotone g) :
  (comap m f).lift' g = f.lift' (g ∘ preimage m) :=
comap_lift_eq2 $ monotone_principal.comp hg

lemma lift'_principal {s : set α} (hh : monotone h) :
  (𝓟 s).lift' h = 𝓟 (h s) :=
lift_principal $ monotone_principal.comp hh

lemma lift'_pure {a : α} (hh : monotone h) :
  (pure a : filter α).lift' h = 𝓟 (h {a}) :=
by rw [← principal_singleton, lift'_principal hh]

lemma lift'_bot (hh : monotone h) : (⊥ : filter α).lift' h = 𝓟 (h ∅) :=
by rw [← principal_empty, lift'_principal hh]

lemma le_lift' {f : filter α} {h : set α → set β} {g : filter β} :
  g ≤ f.lift' h ↔ ∀ s ∈ f, h s ∈ g :=
le_lift.trans $ forall₂_congr $ λ s hs, le_principal_iff

lemma principal_le_lift' {t : set β} : 𝓟 t ≤ f.lift' h ↔ ∀ s ∈ f, t ⊆ h s := le_lift'

theorem monotone_lift' [preorder γ] {f : γ → filter α} {g : γ → set α → set β}
  (hf : monotone f) (hg : monotone g) : monotone (λc, (f c).lift' (g c)) :=
assume a b h, lift'_mono (hf h) (hg h)

lemma lift_lift'_assoc {g : set α → set β} {h : set β → filter γ}
  (hg : monotone g) (hh : monotone h) :
  (f.lift' g).lift h = f.lift (λs, h (g s)) :=
calc (f.lift' g).lift h = f.lift (λs, (𝓟 (g s)).lift h) :
    lift_assoc (monotone_principal.comp hg)
  ... = f.lift (λs, h (g s)) : by simp only [lift_principal, hh, eq_self_iff_true]

lemma lift'_lift'_assoc {g : set α → set β} {h : set β → set γ}
  (hg : monotone g) (hh : monotone h) :
  (f.lift' g).lift' h = f.lift' (λs, h (g s)) :=
lift_lift'_assoc hg (monotone_principal.comp hh)

lemma lift'_lift_assoc {g : set α → filter β} {h : set β → set γ}
  (hg : monotone g) : (f.lift g).lift' h = f.lift (λs, (g s).lift' h) :=
lift_assoc hg

lemma lift_lift'_same_le_lift' {g : set α → set α → set β} :
  f.lift (λs, f.lift' (g s)) ≤ f.lift' (λs, g s s) :=
lift_lift_same_le_lift

lemma lift_lift'_same_eq_lift' {g : set α → set α → set β}
  (hg₁ : ∀s, monotone (λt, g s t)) (hg₂ : ∀t, monotone (λs, g s t)) :
  f.lift (λs, f.lift' (g s)) = f.lift' (λs, g s s) :=
lift_lift_same_eq_lift
  (assume s, monotone_principal.comp (hg₁ s))
  (assume t, monotone_principal.comp (hg₂ t))

lemma lift'_inf_principal_eq {h : set α → set β} {s : set β} :
  f.lift' h ⊓ 𝓟 s = f.lift' (λt, h t ∩ s) :=
by simp only [filter.lift', filter.lift, (∘), ← inf_principal, infi_subtype', ← infi_inf]

lemma lift'_ne_bot_iff (hh : monotone h) : (ne_bot (f.lift' h)) ↔ (∀s∈f, (h s).nonempty) :=
calc (ne_bot (f.lift' h)) ↔ (∀s∈f, ne_bot (𝓟 (h s))) :
    lift_ne_bot_iff (monotone_principal.comp hh)
  ... ↔ (∀s∈f, (h s).nonempty) : by simp only [principal_ne_bot_iff]

@[simp] lemma lift'_id {f : filter α} : f.lift' id = f :=
lift_principal2

lemma lift'_infi [nonempty ι] {f : ι → filter α} {g : set α → set β}
  (hg : ∀ s t, g (s ∩ t) = g s ∩ g t) : (infi f).lift' g = (⨅ i, (f i).lift' g) :=
lift_infi $ λ s t, by rw [inf_principal, (∘), ← hg]

lemma lift'_infi_of_map_univ {f : ι → filter α} {g : set α → set β}
  (hg : ∀{s t}, g (s ∩ t) = g s ∩ g t) (hg' : g univ = univ) :
  (infi f).lift' g = (⨅ i, (f i).lift' g) :=
lift_infi_of_map_univ (λ s t, by rw [inf_principal, (∘), ← hg])
  (by rw [function.comp_app, hg', principal_univ])

lemma lift'_inf (f g : filter α) {s : set α → set β} (hs : ∀ t₁ t₂, s (t₁ ∩ t₂) = s t₁ ∩ s t₂) :
  (f ⊓ g).lift' s = f.lift' s ⊓ g.lift' s :=
have (⨅ b : bool, cond b f g).lift' s = ⨅ b : bool, (cond b f g).lift' s :=
  lift'_infi @hs,
by simpa only [infi_bool_eq]

lemma lift'_inf_le (f g : filter α) (s : set α → set β) :
  (f ⊓ g).lift' s ≤ f.lift' s ⊓ g.lift' s :=
le_inf (lift'_mono inf_le_left le_rfl) (lift'_mono inf_le_right le_rfl)

theorem comap_eq_lift' {f : filter β} {m : α → β} :
  comap m f = f.lift' (preimage m) :=
filter.ext $ λ s, (mem_lift'_sets monotone_preimage).symm

end lift'

section prod
variables {f : filter α}

lemma prod_def {f : filter α} {g : filter β} : f ×ᶠ g = (f.lift $ λ s, g.lift' $ λ t, s ×ˢ t) :=
have ∀(s:set α) (t : set β),
    𝓟 (s ×ˢ t) = (𝓟 s).comap prod.fst ⊓ (𝓟 t).comap prod.snd,
  by simp only [principal_eq_iff_eq, comap_principal, inf_principal]; intros; refl,
begin
  simp only [filter.lift', function.comp, this, lift_inf, lift_const, lift_inf],
  rw [← comap_lift_eq, ← comap_lift_eq],
  simp only [filter.prod, lift_principal2]
end

lemma prod_same_eq : f ×ᶠ f = f.lift' (λ t : set α, t ×ˢ t) :=
prod_def.trans $ lift_lift'_same_eq_lift'
  (λ s, monotone_const.set_prod monotone_id)
  (λ t, monotone_id.set_prod monotone_const)

lemma mem_prod_same_iff {s : set (α×α)} :
  s ∈ f ×ᶠ f ↔ (∃t∈f, t ×ˢ t ⊆ s) :=
by { rw [prod_same_eq, mem_lift'_sets], exact monotone_id.set_prod monotone_id }

lemma tendsto_prod_self_iff {f : α × α → β} {x : filter α} {y : filter β} :
  filter.tendsto f (x ×ᶠ x) y ↔
  ∀ W ∈ y, ∃ U ∈ x, ∀ (x x' : α), x ∈ U → x' ∈ U → f (x, x') ∈ W :=
by simp only [tendsto_def, mem_prod_same_iff, prod_sub_preimage_iff, exists_prop, iff_self]

variables {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*}

lemma prod_lift_lift
  {f₁ : filter α₁} {f₂ : filter α₂} {g₁ : set α₁ → filter β₁} {g₂ : set α₂ → filter β₂}
  (hg₁ : monotone g₁) (hg₂ : monotone g₂) :
  (f₁.lift g₁) ×ᶠ (f₂.lift g₂) = f₁.lift (λs, f₂.lift (λt, g₁ s ×ᶠ g₂ t)) :=
begin
  simp only [prod_def, lift_assoc hg₁],
  apply congr_arg, funext x,
  rw [lift_comm],
  apply congr_arg, funext y,
  apply lift'_lift_assoc hg₂
end

lemma prod_lift'_lift'
  {f₁ : filter α₁} {f₂ : filter α₂} {g₁ : set α₁ → set β₁} {g₂ : set α₂ → set β₂}
  (hg₁ : monotone g₁) (hg₂ : monotone g₂) :
  f₁.lift' g₁ ×ᶠ f₂.lift' g₂ = f₁.lift (λ s, f₂.lift' (λ t, g₁ s ×ˢ g₂ t)) :=
calc f₁.lift' g₁ ×ᶠ f₂.lift' g₂ = f₁.lift (λ s, f₂.lift (λ t, 𝓟 (g₁ s) ×ᶠ 𝓟 (g₂ t))) :
  prod_lift_lift (monotone_principal.comp hg₁) (monotone_principal.comp hg₂)
... = f₁.lift (λ s, f₂.lift (λ t, 𝓟 (g₁ s ×ˢ g₂ t))) :
  by simp only [prod_principal_principal]

end prod

end filter
