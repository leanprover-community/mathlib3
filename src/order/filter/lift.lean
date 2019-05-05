/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Lift filters along filter and set functions.
-/
import order.filter.basic

open lattice set

local attribute [instance] classical.prop_decidable

namespace filter
variables {α : Type*} {β : Type*} {γ : Type*} {ι : Sort*}

section lift

/-- A variant on `bind` using a function `g` taking a set instead of a member of `α`.
This is essentially a push-forward along a function mapping each set to a filter. -/
protected def lift (f : filter α) (g : set α → filter β) :=
⨅s ∈ f.sets, g s

variables {f f₁ f₂ : filter α} {g g₁ g₂ : set α → filter β}

lemma lift_sets_eq (hg : monotone g) : (f.lift g).sets = (⋃t∈f.sets, (g t).sets) :=
infi_sets_eq'
  (assume s hs t ht, ⟨s ∩ t, inter_mem_sets hs ht,
    hg $ inter_subset_left s t, hg $ inter_subset_right s t⟩)
  ⟨univ, univ_mem_sets⟩

lemma mem_lift {s : set β} {t : set α} (ht : t ∈ f.sets) (hs : s ∈ (g t).sets) :
  s ∈ (f.lift g).sets :=
le_principal_iff.mp $ show f.lift g ≤ principal s,
  from infi_le_of_le t $ infi_le_of_le ht $ le_principal_iff.mpr hs

lemma mem_lift_sets (hg : monotone g) {s : set β} :
  s ∈ (f.lift g).sets ↔ (∃t∈f.sets, s ∈ (g t).sets) :=
by rw [lift_sets_eq hg]; simp only [mem_Union]

lemma lift_le {f : filter α} {g : set α → filter β} {h : filter β} {s : set α}
  (hs : s ∈ f.sets) (hg : g s ≤ h) : f.lift g ≤ h :=
infi_le_of_le s $ infi_le_of_le hs $ hg

lemma le_lift {f : filter α} {g : set α → filter β} {h : filter β}
  (hh : ∀s∈f.sets, h ≤ g s) : h ≤ f.lift g :=
le_infi $ assume s, le_infi $ assume hs, hh s hs

lemma lift_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.lift g₁ ≤ f₂.lift g₂ :=
infi_le_infi $ assume s, infi_le_infi2 $ assume hs, ⟨hf hs, hg s⟩

lemma lift_mono' (hg : ∀s∈f.sets, g₁ s ≤ g₂ s) : f.lift g₁ ≤ f.lift g₂ :=
infi_le_infi $ assume s, infi_le_infi $ assume hs, hg s hs

lemma map_lift_eq {m : β → γ} (hg : monotone g) : map m (f.lift g) = f.lift (map m ∘ g) :=
have monotone (map m ∘ g),
  from monotone_comp hg monotone_map,
filter_eq $ set.ext $
  by simp only [mem_lift_sets, hg, @mem_lift_sets _ _ f _ this, exists_prop, forall_const, mem_map, iff_self, function.comp_app]

lemma comap_lift_eq {m : γ → β} (hg : monotone g) : comap m (f.lift g) = f.lift (comap m ∘ g) :=
have monotone (comap m ∘ g),
  from monotone_comp hg monotone_comap,
filter_eq $ set.ext begin
  simp only [hg, @mem_lift_sets _ _ f _ this, comap, mem_lift_sets, mem_set_of_eq, exists_prop,
    function.comp_apply],
  exact λ s,
   ⟨λ ⟨b, ⟨a, ha, hb⟩, hs⟩, ⟨a, ha, b, hb, hs⟩,
    λ ⟨a, ha, b, hb, hs⟩, ⟨b, ⟨a, ha, hb⟩, hs⟩⟩
end

theorem comap_lift_eq2 {m : β → α} {g : set β → filter γ} (hg : monotone g) :
  (comap m f).lift g = f.lift (g ∘ preimage m) :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs,
    infi_le_of_le (preimage m s) $ infi_le _ ⟨s, hs, subset.refl _⟩)
  (le_infi $ assume s, le_infi $ assume ⟨s', hs', (h_sub : preimage m s' ⊆ s)⟩,
    infi_le_of_le s' $ infi_le_of_le hs' $ hg h_sub)

lemma map_lift_eq2 {g : set β → filter γ} {m : α → β} (hg : monotone g) :
  (map m f).lift g = f.lift (g ∘ image m) :=
le_antisymm
  (infi_le_infi2 $ assume s, ⟨image m s,
    infi_le_infi2 $ assume hs, ⟨
      f.sets_of_superset hs $ assume a h, mem_image_of_mem _ h,
      le_refl _⟩⟩)
  (infi_le_infi2 $ assume t, ⟨preimage m t,
    infi_le_infi2 $ assume ht, ⟨ht,
      hg $ assume x, assume h : x ∈ m '' preimage m t,
        let ⟨y, hy, h_eq⟩ := h in
        show x ∈ t, from h_eq ▸ hy⟩⟩)

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
le_infi $ assume s, le_infi $ assume hs, infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le s $ infi_le _ hs

lemma lift_lift_same_eq_lift {g : set α → set α → filter β}
  (hg₁ : ∀s, monotone (λt, g s t)) (hg₂ : ∀t, monotone (λs, g s t)):
  f.lift (λs, f.lift (g s)) = f.lift (λs, g s s) :=
le_antisymm
  lift_lift_same_le_lift
  (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
    infi_le_of_le (s ∩ t) $
    infi_le_of_le (inter_mem_sets hs ht) $
    calc g (s ∩ t) (s ∩ t) ≤ g s (s ∩ t) : hg₂ (s ∩ t) (inter_subset_left _ _)
      ... ≤ g s t                        : hg₁ s (inter_subset_right _ _))

lemma lift_principal {s : set α} (hg : monotone g) :
  (principal s).lift g = g s :=
le_antisymm
  (infi_le_of_le s $ infi_le _ $ subset.refl _)
  (le_infi $ assume t, le_infi $ assume hi, hg hi)

theorem monotone_lift [preorder γ] {f : γ → filter α} {g : γ → set α → filter β}
  (hf : monotone f) (hg : monotone g) : monotone (λc, (f c).lift (g c)) :=
assume a b h, lift_mono (hf h) (hg h)

lemma lift_neq_bot_iff (hm : monotone g) : (f.lift g ≠ ⊥) ↔ (∀s∈f.sets, g s ≠ ⊥) :=
classical.by_cases
  (assume hn : nonempty β,
    calc f.lift g ≠ ⊥ ↔ (⨅s : { s // s ∈ f.sets}, g s.val) ≠ ⊥ :
      by simp only [filter.lift, infi_subtype, iff_self, ne.def]
      ... ↔ (∀s:{ s // s ∈ f.sets}, g s.val ≠ ⊥) :
        infi_neq_bot_iff_of_directed hn
          (assume ⟨a, ha⟩ ⟨b, hb⟩, ⟨⟨a ∩ b, inter_mem_sets ha hb⟩,
            hm $ inter_subset_left _ _, hm $ inter_subset_right _ _⟩)
      ... ↔ (∀s∈f.sets, g s ≠ ⊥) : ⟨assume h s hs, h ⟨s, hs⟩, assume h ⟨s, hs⟩, h s hs⟩)
  (assume hn : ¬ nonempty β,
    have h₁ : f.lift g = ⊥, from filter_eq_bot_of_not_nonempty hn,
    have h₂ : ∀s, g s = ⊥, from assume s, filter_eq_bot_of_not_nonempty hn,
    calc (f.lift g ≠ ⊥) ↔ false : by simp only [h₁, iff_self, eq_self_iff_true, not_true, ne.def]
      ... ↔ (∀s∈f.sets, false) : ⟨false.elim, assume h, h univ univ_mem_sets⟩
      ... ↔ (∀s∈f.sets, g s ≠ ⊥) : by simp only [h₂, iff_self, eq_self_iff_true, not_true, ne.def])

@[simp] lemma lift_const {f : filter α} {g : filter β} : f.lift (λx, g) = g :=
le_antisymm (lift_le univ_mem_sets $ le_refl g) (le_lift $ assume s hs, le_refl g)

@[simp] lemma lift_inf {f : filter α} {g h : set α → filter β} :
  f.lift (λx, g x ⊓ h x) = f.lift g ⊓ f.lift h :=
by simp only [filter.lift, infi_inf_eq, eq_self_iff_true]

@[simp] lemma lift_principal2 {f : filter α} : f.lift principal = f :=
le_antisymm
  (assume s hs, mem_lift hs (mem_principal_self s))
  (le_infi $ assume s, le_infi $ assume hs, by simp only [hs, le_principal_iff])

lemma lift_infi {f : ι → filter α} {g : set α → filter β}
  (hι : nonempty ι) (hg : ∀{s t}, g s ⊓ g t = g (s ∩ t)) : (infi f).lift g = (⨅i, (f i).lift g) :=
le_antisymm
  (le_infi $ assume i, lift_mono (infi_le _ _) (le_refl _))
  (assume s,
    have g_mono : monotone g,
      from assume s t h, le_of_inf_eq $ eq.trans hg $ congr_arg g $ inter_eq_self_of_subset_left h,
    have ∀t∈(infi f).sets, (⨅ (i : ι), filter.lift (f i) g) ≤ g t,
      from assume t ht, infi_sets_induct ht
        (let ⟨i⟩ := hι in infi_le_of_le i $ infi_le_of_le univ $ infi_le _ univ_mem_sets)
        (assume i s₁ s₂ hs₁ hs₂,
          @hg s₁ s₂ ▸ le_inf (infi_le_of_le i $ infi_le_of_le s₁ $ infi_le _ hs₁) hs₂)
        (assume s₁ s₂ hs₁ hs₂, le_trans hs₂ $ g_mono hs₁),
    begin
      rw [lift_sets_eq g_mono],
      simp only [mem_Union, exists_imp_distrib],
      exact assume t ht hs, this t ht hs
    end)

end lift

section lift'
/-- Specialize `lift` to functions `set α → set β`. This can be viewed as a generalization of `map`.
This is essentially a push-forward along a function mapping each set to a set. -/
protected def lift' (f : filter α) (h : set α → set β) :=
f.lift (principal ∘ h)

variables {f f₁ f₂ : filter α} {h h₁ h₂ : set α → set β}

lemma mem_lift' {t : set α} (ht : t ∈ f.sets) : h t ∈ (f.lift' h).sets :=
le_principal_iff.mp $ show f.lift' h ≤ principal (h t),
  from infi_le_of_le t $ infi_le_of_le ht $ le_refl _

lemma mem_lift'_sets (hh : monotone h) {s : set β} : s ∈ (f.lift' h).sets ↔ (∃t∈f.sets, h t ⊆ s) :=
have monotone (principal ∘ h),
  from assume a b h, principal_mono.mpr $ hh h,
by simp only [filter.lift', @mem_lift_sets α β f _ this, exists_prop, iff_self, mem_principal_sets, function.comp_app]

lemma lift'_le {f : filter α} {g : set α → set β} {h : filter β} {s : set α}
  (hs : s ∈ f.sets) (hg : principal (g s) ≤ h) : f.lift' g ≤ h :=
lift_le hs hg

lemma lift'_mono (hf : f₁ ≤ f₂) (hh : h₁ ≤ h₂) : f₁.lift' h₁ ≤ f₂.lift' h₂ :=
lift_mono hf $ assume s, principal_mono.mpr $ hh s

lemma lift'_mono' (hh : ∀s∈f.sets, h₁ s ⊆ h₂ s) : f.lift' h₁ ≤ f.lift' h₂ :=
infi_le_infi $ assume s, infi_le_infi $ assume hs, principal_mono.mpr $ hh s hs

lemma lift'_cong (hh : ∀s∈f.sets, h₁ s = h₂ s) : f.lift' h₁ = f.lift' h₂ :=
le_antisymm (lift'_mono' $ assume s hs, le_of_eq $ hh s hs) (lift'_mono' $ assume s hs, le_of_eq $ (hh s hs).symm)

lemma map_lift'_eq {m : β → γ} (hh : monotone h) : map m (f.lift' h) = f.lift' (image m ∘ h) :=
calc map m (f.lift' h) = f.lift (map m ∘ principal ∘ h) :
    map_lift_eq $ monotone_comp hh monotone_principal
  ... = f.lift' (image m ∘ h) : by simp only [(∘), filter.lift', map_principal, eq_self_iff_true]

lemma map_lift'_eq2 {g : set β → set γ} {m : α → β} (hg : monotone g) :
  (map m f).lift' g = f.lift' (g ∘ image m) :=
map_lift_eq2 $ monotone_comp hg monotone_principal

theorem comap_lift'_eq {m : γ → β} (hh : monotone h) :
  comap m (f.lift' h) = f.lift' (preimage m ∘ h) :=
calc comap m (f.lift' h) = f.lift (comap m ∘ principal ∘ h) :
    comap_lift_eq $ monotone_comp hh monotone_principal
  ... = f.lift' (preimage m ∘ h) : by simp only [(∘), filter.lift', comap_principal, eq_self_iff_true]

theorem comap_lift'_eq2 {m : β → α} {g : set β → set γ} (hg : monotone g) :
  (comap m f).lift' g = f.lift' (g ∘ preimage m) :=
comap_lift_eq2 $ monotone_comp hg monotone_principal

lemma lift'_principal {s : set α} (hh : monotone h) :
  (principal s).lift' h = principal (h s) :=
lift_principal $ monotone_comp hh monotone_principal

lemma principal_le_lift' {t : set β} (hh : ∀s∈f.sets, t ⊆ h s) :
  principal t ≤ f.lift' h :=
le_infi $ assume s, le_infi $ assume hs, principal_mono.mpr (hh s hs)

theorem monotone_lift' [preorder γ] {f : γ → filter α} {g : γ → set α → set β}
  (hf : monotone f) (hg : monotone g) : monotone (λc, (f c).lift' (g c)) :=
assume a b h, lift'_mono (hf h) (hg h)

lemma lift_lift'_assoc {g : set α → set β} {h : set β → filter γ}
  (hg : monotone g) (hh : monotone h) :
  (f.lift' g).lift h = f.lift (λs, h (g s)) :=
calc (f.lift' g).lift h = f.lift (λs, (principal (g s)).lift h) :
    lift_assoc (monotone_comp hg monotone_principal)
  ... = f.lift (λs, h (g s)) : by simp only [lift_principal, hh, eq_self_iff_true]

lemma lift'_lift'_assoc {g : set α → set β} {h : set β → set γ}
  (hg : monotone g) (hh : monotone h) :
  (f.lift' g).lift' h = f.lift' (λs, h (g s)) :=
lift_lift'_assoc hg (monotone_comp hh monotone_principal)

lemma lift'_lift_assoc {g : set α → filter β} {h : set β → set γ}
  (hg : monotone g) : (f.lift g).lift' h = f.lift (λs, (g s).lift' h) :=
lift_assoc hg

lemma lift_lift'_same_le_lift' {g : set α → set α → set β} :
  f.lift (λs, f.lift' (g s)) ≤ f.lift' (λs, g s s) :=
lift_lift_same_le_lift

lemma lift_lift'_same_eq_lift' {g : set α → set α → set β}
  (hg₁ : ∀s, monotone (λt, g s t)) (hg₂ : ∀t, monotone (λs, g s t)):
  f.lift (λs, f.lift' (g s)) = f.lift' (λs, g s s) :=
lift_lift_same_eq_lift
  (assume s, monotone_comp monotone_id $ monotone_comp (hg₁ s) monotone_principal)
  (assume t, monotone_comp (hg₂ t) monotone_principal)

lemma lift'_inf_principal_eq {h : set α → set β} {s : set β} :
  f.lift' h ⊓ principal s = f.lift' (λt, h t ∩ s) :=
le_antisymm
  (le_infi $ assume t, le_infi $ assume ht,
    calc filter.lift' f h ⊓ principal s ≤ principal (h t) ⊓ principal s :
        inf_le_inf (infi_le_of_le t $ infi_le _ ht) (le_refl _)
      ... = _ : by simp only [principal_eq_iff_eq, inf_principal, eq_self_iff_true, function.comp_app])
  (le_inf
    (le_infi $ assume t, le_infi $ assume ht,
      infi_le_of_le t $ infi_le_of_le ht $
      by simp only [le_principal_iff, inter_subset_left, mem_principal_sets, function.comp_app]; exact inter_subset_right _ _)
    (infi_le_of_le univ $ infi_le_of_le univ_mem_sets $
    by simp only [le_principal_iff, inter_subset_right, mem_principal_sets, function.comp_app]; exact inter_subset_left _ _))

lemma lift'_neq_bot_iff (hh : monotone h) : (f.lift' h ≠ ⊥) ↔ (∀s∈f.sets, h s ≠ ∅) :=
calc (f.lift' h ≠ ⊥) ↔ (∀s∈f.sets, principal (h s) ≠ ⊥) :
    lift_neq_bot_iff (monotone_comp hh monotone_principal)
  ... ↔ (∀s∈f.sets, h s ≠ ∅) : by simp only [principal_eq_bot_iff, iff_self, ne.def, principal_eq_bot_iff]

@[simp] lemma lift'_id {f : filter α} : f.lift' id = f :=
lift_principal2

lemma le_lift' {f : filter α} {h : set α → set β} {g : filter β}
  (h_le : ∀s∈f.sets, h s ∈ g.sets) : g ≤ f.lift' h :=
le_infi $ assume s, le_infi $ assume hs, by simp only [h_le, le_principal_iff, function.comp_app]; exact h_le s hs

lemma lift_infi' {f : ι → filter α} {g : set α → filter β}
  (hι : nonempty ι) (hf : directed (≥) f) (hg : monotone g) : (infi f).lift g = (⨅i, (f i).lift g) :=
le_antisymm
  (le_infi $ assume i, lift_mono (infi_le _ _) (le_refl _))
  (assume s,
  begin
    rw [lift_sets_eq hg],
    simp only [mem_Union, exists_imp_distrib, infi_sets_eq hf hι],
    exact assume t i ht hs, mem_infi_sets i $ mem_lift ht hs
  end)

lemma lift'_infi {f : ι → filter α} {g : set α → set β}
  (hι : nonempty ι) (hg : ∀{s t}, g s ∩ g t = g (s ∩ t)) : (infi f).lift' g = (⨅i, (f i).lift' g) :=
lift_infi hι $ by simp only [principal_eq_iff_eq, inf_principal, function.comp_app]; apply assume s t, hg

theorem comap_eq_lift' {f : filter β} {m : α → β} :
  comap m f = f.lift' (preimage m) :=
filter_eq $ set.ext $ by simp only [mem_lift'_sets, monotone_preimage, comap, exists_prop, forall_const, iff_self, mem_set_of_eq]

end lift'

section prod
variables {f : filter α}

lemma prod_def {f : filter α} {g : filter β} : f.prod g = (f.lift $ λs, g.lift' $ set.prod s) :=
have ∀(s:set α) (t : set β),
    principal (set.prod s t) = (principal s).comap prod.fst ⊓ (principal t).comap prod.snd,
  by simp only [principal_eq_iff_eq, comap_principal, inf_principal]; intros; refl,
begin
  simp only [filter.lift', function.comp, this, -comap_principal, lift_inf, lift_const, lift_inf],
  rw [← comap_lift_eq monotone_principal, ← comap_lift_eq monotone_principal],
  simp only [filter.prod, lift_principal2, eq_self_iff_true]
end

lemma prod_same_eq : filter.prod f f = f.lift' (λt, set.prod t t) :=
by rw [prod_def];
from lift_lift'_same_eq_lift'
  (assume s, set.monotone_prod monotone_const monotone_id)
  (assume t, set.monotone_prod monotone_id monotone_const)

lemma mem_prod_same_iff {s : set (α×α)} :
  s ∈ (filter.prod f f).sets ↔ (∃t∈f.sets, set.prod t t ⊆ s) :=
by rw [prod_same_eq, mem_lift'_sets]; exact set.monotone_prod monotone_id monotone_id

lemma tendsto_prod_self_iff {f : α × α → β} {x : filter α} {y : filter β} :
  filter.tendsto f (filter.prod x x) y ↔
  ∀ W ∈ y.sets, ∃ U ∈ x.sets, ∀ (x x' : α), x ∈ U → x' ∈ U → f (x, x') ∈ W :=
by simp only [tendsto_def, mem_prod_same_iff, prod_sub_preimage_iff, exists_prop, iff_self]

variables {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*}

lemma prod_lift_lift
  {f₁ : filter α₁} {f₂ : filter α₂} {g₁ : set α₁ → filter β₁} {g₂ : set α₂ → filter β₂}
  (hg₁ : monotone g₁) (hg₂ : monotone g₂) :
  filter.prod (f₁.lift g₁) (f₂.lift g₂) = f₁.lift (λs, f₂.lift (λt, filter.prod (g₁ s) (g₂ t))) :=
begin
  simp only [prod_def],
  rw [lift_assoc],
  apply congr_arg, funext x,
  rw [lift_comm],
  apply congr_arg, funext y,
  rw [lift'_lift_assoc],
  exact hg₂,
  exact hg₁
end

lemma prod_lift'_lift'
  {f₁ : filter α₁} {f₂ : filter α₂} {g₁ : set α₁ → set β₁} {g₂ : set α₂ → set β₂}
  (hg₁ : monotone g₁) (hg₂ : monotone g₂) :
  filter.prod (f₁.lift' g₁) (f₂.lift' g₂) = f₁.lift (λs, f₂.lift' (λt, set.prod (g₁ s) (g₂ t))) :=
begin
  rw [prod_def, lift_lift'_assoc],
  apply congr_arg, funext x,
  rw [lift'_lift'_assoc],
  exact hg₂,
  exact set.monotone_prod monotone_const monotone_id,
  exact hg₁,
  exact (monotone_lift' monotone_const $ monotone_lam $
    assume x, set.monotone_prod monotone_id monotone_const)
end

end prod

end filter
