/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Continuous functions.

Parts of the formalization is based on the books:
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
A major difference is that this formalization is heavily based on the filter library.
-/
import topology.topological_space
noncomputable theory

open set filter lattice classical
local attribute [instance] decidable_inhabited prop_decidable

universes u v w x y
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type y} {ι : Sort x}

lemma image_preimage_eq_inter_rng {f : α → β} {t : set β} :
  f '' preimage f t = t ∩ f '' univ :=
set.ext $ assume x, ⟨assume ⟨x, hx, heq⟩, heq ▸ ⟨hx, mem_image_of_mem f trivial⟩,
  assume ⟨hx, ⟨y, hy, h_eq⟩⟩, h_eq ▸ mem_image_of_mem f $
    show y ∈ preimage f t, by simp [preimage, h_eq, hx]⟩

lemma subtype.val_image {p : α → Prop} {s : set (subtype p)} :
  subtype.val '' s = {x | ∃h : p x, (⟨x, h⟩ : subtype p) ∈ s} :=
set.ext $ assume a,
⟨assume ⟨⟨a', ha'⟩, in_s, h_eq⟩, h_eq ▸ ⟨ha', in_s⟩,
  assume ⟨ha, in_s⟩, ⟨⟨a, ha⟩, in_s, rfl⟩⟩

@[simp] lemma univ_prod_univ : set.prod univ univ = (univ : set (α×β)) :=
set.ext $ assume ⟨a, b⟩, by simp

section
variables [topological_space α] [topological_space β] [topological_space γ]

def continuous (f : α → β) := ∀s, is_open s → is_open (preimage f s)

lemma continuous_id : continuous (id : α → α) :=
assume s h, h

lemma continuous_compose {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g):
  continuous (g ∘ f) :=
assume s h, hf _ (hg s h)

lemma continuous_iff_tendsto {f : α → β} :
  continuous f ↔ (∀x, tendsto f (nhds x) (nhds (f x))) :=
⟨assume hf : continuous f, assume x s,
  show s ∈ (nhds (f x)).sets → s ∈ (map f (nhds x)).sets,
    by simp [nhds_sets];
      exact assume t t_open t_subset fx_in_t,
        ⟨preimage f t, hf t t_open, fx_in_t, preimage_mono t_subset⟩,
  assume hf : ∀x, tendsto f (nhds x) (nhds (f x)),
  assume s, assume hs : is_open s,
  have ∀a, f a ∈ s → s ∈ (nhds (f a)).sets,
    by simp [nhds_sets]; exact assume a ha, ⟨s, hs, subset.refl s, ha⟩,
  show is_open (preimage f s),
    by simp [is_open_iff_nhds]; exact assume a ha, hf a (this a ha)⟩

lemma continuous_const {b : β} : continuous (λa:α, b) :=
continuous_iff_tendsto.mpr $ assume a, tendsto_const_nhds

lemma continuous_iff_is_closed {f : α → β} :
  continuous f ↔ (∀s, is_closed s → is_closed (preimage f s)) :=
⟨assume hf s hs, hf (-s) hs,
  assume hf s, by rw [←is_closed_compl_iff, ←is_closed_compl_iff]; exact hf _⟩

lemma image_closure_subset_closure_image {f : α → β} {s : set α} (h : continuous f) :
  f '' closure s ⊆ closure (f '' s) :=
have ∀ (a : α), nhds a ⊓ principal s ≠ ⊥ → nhds (f a) ⊓ principal (f '' s) ≠ ⊥,
  from assume a ha,
  have h₁ : ¬ map f (nhds a ⊓ principal s) = ⊥,
    by rwa[map_eq_bot_iff],
  have h₂ : map f (nhds a ⊓ principal s) ≤ nhds (f a) ⊓ principal (f '' s),
    from le_inf
      (le_trans (map_mono inf_le_left) $ by rw [continuous_iff_tendsto] at h; exact h a)
      (le_trans (map_mono inf_le_right) $ by simp; exact subset.refl _),
  neq_bot_of_le_neq_bot h₁ h₂,
by simp [image_subset_iff_subset_preimage, closure_eq_nhds]; assumption

lemma compact_image {s : set α} {f : α → β} (hs : compact s) (hf : continuous f) : compact (f '' s) :=
compact_of_finite_subcover $ assume c hco hcs,
  have hdo : ∀t∈c, is_open (preimage f t), from assume t' ht, hf _ $ hco _ ht,
  have hds : s ⊆ ⋃i∈c, preimage f i,
    by simp [subset_def]; simp [subset_def] at hcs; exact assume x hx, hcs _ (mem_image_of_mem f hx),
  let ⟨d', hcd', hfd', hd'⟩ := compact_elim_finite_subcover_image hs hdo hds in
  ⟨d', hcd', hfd', by simp [subset_def] at hd'; simp [image_subset_iff_subset_preimage]; assumption⟩

end

section constructions
local notation `cont` := @continuous _ _
local notation `tspace` := topological_space
open topological_space

variable {f : α → β}

lemma continuous_iff_induced_le {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f ↔ (induced f t₂ ≤ t₁) :=
⟨assume hc s ⟨t, ht, s_eq⟩, s_eq.symm ▸ hc t ht,
  assume hle s h, hle _ ⟨_, h, rfl⟩⟩

lemma continuous_eq_le_coinduced {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f = (t₂ ≤ coinduced f t₁) :=
rfl

theorem continuous_generated_from {t : tspace α} {b : set (set β)}
  (h : ∀s∈b, is_open (preimage f s)) : cont t (generate_from b) f :=
assume s hs, generate_open.rec_on hs h
  is_open_univ
  (assume s t _ _, is_open_inter)
  (assume t _ h, by rw [preimage_sUnion]; exact (is_open_Union $ assume s, is_open_Union $ assume hs, h s hs))

lemma continuous_induced_dom {t : tspace β} : cont (induced f t) t f :=
assume s h, ⟨_, h, rfl⟩

lemma continuous_induced_rng {g : γ → α} {t₂ : tspace β} {t₁ : tspace γ}
  (h : cont t₁ t₂ (f ∘ g)) : cont t₁ (induced f t₂) g :=
assume s ⟨t, ht, s_eq⟩, s_eq.symm ▸ h t ht

lemma continuous_coinduced_rng {t : tspace α} : cont t (coinduced f t) f :=
assume s h, h

lemma continuous_coinduced_dom {g : β → γ} {t₁ : tspace α} {t₂ : tspace γ}
  (h : cont t₁ t₂ (g ∘ f)) : cont (coinduced f t₁) t₂ g :=
assume s hs, h s hs

lemma continuous_inf_dom {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h₁ : cont t₁ t₃ f) (h₂ : cont t₂ t₃ f) : cont (t₁ ⊓ t₂) t₃ f :=
assume s h, ⟨h₁ s h, h₂ s h⟩

lemma continuous_inf_rng_left {t₁ : tspace α} {t₃ t₂ : tspace β}
  (h : cont t₁ t₂ f) : cont t₁ (t₂ ⊓ t₃) f :=
assume s hs, h s hs.left

lemma continuous_inf_rng_right {t₁ : tspace α} {t₃ t₂ : tspace β}
  (h : cont t₁ t₃ f) : cont t₁ (t₂ ⊓ t₃) f :=
assume s hs, h s hs.right

lemma continuous_Inf_dom {t₁ : set (tspace α)} {t₂ : tspace β}
  (h : ∀t∈t₁, cont t t₂ f) : cont (Inf t₁) t₂ f :=
assume s hs t ht, h t ht s hs

lemma continuous_Inf_rng {t₁ : tspace α} {t₂ : set (tspace β)}
  {t : tspace β} (h₁ : t ∈ t₂) (hf : cont t₁ t f) : cont t₁ (Inf t₂) f :=
assume s hs, hf s $ hs t h₁

lemma continuous_infi_dom {t₁ : ι → tspace α} {t₂ : tspace β}
  (h : ∀i, cont (t₁ i) t₂ f) : cont (infi t₁) t₂ f :=
continuous_Inf_dom $ assume t ⟨i, (t_eq : t = t₁ i)⟩, t_eq.symm ▸ h i

lemma continuous_infi_rng {t₁ : tspace α} {t₂ : ι → tspace β}
  {i : ι} (h : cont t₁ (t₂ i) f) : cont t₁ (infi t₂) f :=
continuous_Inf_rng ⟨i, rfl⟩ h

lemma continuous_top {t : tspace β} : cont ⊤ t f :=
assume s h, trivial

lemma continuous_bot {t : tspace α} : cont t ⊥ f :=
continuous_Inf_rng (mem_univ $ coinduced f t) continuous_coinduced_rng

lemma continuous_sup_rng {t₁ : tspace α} {t₂ t₃ : tspace β}
  (h₁ : cont t₁ t₂ f) (h₂ : cont t₁ t₃ f) : cont t₁ (t₂ ⊔ t₃) f :=
continuous_Inf_rng
  (show t₂ ≤ coinduced f t₁ ∧ t₃ ≤ coinduced f t₁, from ⟨h₁, h₂⟩)
  continuous_coinduced_rng

lemma continuous_sup_dom_left {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h : cont t₁ t₃ f) : cont (t₁ ⊔ t₂) t₃ f :=
continuous_Inf_dom $ assume t ⟨h₁, h₂⟩ s hs, h₁ _ $ h s hs

lemma continuous_sup_dom_right {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h : cont t₂ t₃ f) : cont (t₁ ⊔ t₂) t₃ f :=
continuous_Inf_dom $ assume t ⟨h₁, h₂⟩ s hs, h₂ _ $ h s hs

end constructions

section embedding

lemma induced_mono {t₁ t₂ : topological_space α} {f : β → α} (h : t₁ ≤ t₂) :
  t₁.induced f ≤ t₂.induced f :=
continuous_iff_induced_le.mp $
  show @continuous β α (@topological_space.induced β α f t₂) t₁ (id ∘ f),
  begin
    apply continuous_compose,
    exact continuous_induced_dom,
    exact assume s hs, h _ hs
  end

lemma induced_id [t : topological_space α] : t.induced id = t :=
topological_space_eq $ funext $ assume s, propext $
  ⟨assume ⟨s', hs, h⟩, h.symm ▸ hs, assume hs, ⟨s, hs, rfl⟩⟩

lemma induced_compose [tβ : topological_space β] [tγ : topological_space γ]
  {f : α → β} {g : β → γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f) :=
topological_space_eq $ funext $ assume s, propext $
  ⟨assume ⟨s', ⟨s, hs, h₂⟩, h₁⟩, h₁.symm ▸ h₂.symm ▸ ⟨s, hs, rfl⟩,
    assume ⟨s, hs, h⟩, ⟨preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩

lemma induced_sup (t₁ : topological_space β) (t₂ : topological_space β) {f : α → β} :
  (t₁ ⊔ t₂).induced f = t₁.induced f ⊔ t₂.induced f :=
le_antisymm
  (continuous_iff_induced_le.mp $ continuous_sup_rng
    (continuous_sup_dom_left continuous_induced_dom)
    (continuous_sup_dom_right continuous_induced_dom))
  (sup_le (induced_mono le_sup_left) (induced_mono le_sup_right))

def embedding [tα : topological_space α] [tβ : topological_space β] (f : α → β) : Prop :=
(∀a₁ a₂, f a₁ = f a₂ → a₁ = a₂) ∧ tα = tβ.induced f

variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

lemma embedding_id : embedding (@id α) :=
⟨assume a₁ a₂ h, h, induced_id.symm⟩

lemma embedding_compose {f : α → β} {g : β → γ} (hf : embedding f) (hg : embedding g) :
  embedding (g ∘ f) :=
⟨assume a₁ a₂ h, hf.left _ _ $ hg.left _ _ $ h, by rw [hf.right, hg.right, induced_compose]⟩

lemma embedding_prod_mk {f : α → β} {g : γ → δ} (hf : embedding f) (hg : embedding g) :
  embedding (λx:α×γ, (f x.1, g x.2)) :=
⟨assume ⟨x₁, x₂⟩ ⟨y₁, y₂⟩, by simp; exact assume h₁ h₂, ⟨hf.left _ _ h₁, hg.left _ _ h₂⟩,
  by rw [prod.topological_space, prod.topological_space, hf.right, hg.right,
         induced_compose, induced_compose, induced_sup, induced_compose, induced_compose]⟩

lemma embedding_of_embedding_compose {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g)
  (hgf : embedding (g ∘ f)) : embedding f :=
⟨assume a₁ a₂ h, hgf.left a₁ a₂ $ by simp [h, (∘)],
  le_antisymm
    (by rw [hgf.right, ←continuous_iff_induced_le];
        apply continuous_compose continuous_induced_dom hg)
    (by rwa [←continuous_iff_induced_le])⟩

lemma embedding_open {f : α → β} {s : set α}
  (hf : embedding f) (h : is_open (f '' univ)) (hs : is_open s) : is_open (f '' s) :=
let ⟨t, ht, h_eq⟩ := by rw [hf.right] at hs; exact hs in
have is_open (t ∩ f '' univ), from is_open_inter ht h,
h_eq.symm ▸ by rwa [image_preimage_eq_inter_rng]

lemma embedding_is_closed {f : α → β} {s : set α}
  (hf : embedding f) (h : is_closed (f '' univ)) (hs : is_closed s) : is_closed (f '' s) :=
let ⟨t, ht, h_eq⟩ := by rw [hf.right, is_closed_induced_iff] at hs; exact hs in
have is_closed (t ∩ f '' univ), from is_closed_inter ht h,
h_eq.symm ▸ by rwa [image_preimage_eq_inter_rng]

end embedding

section sierpinski
variables [topological_space α]

@[simp] lemma is_open_singleton_true : is_open ({true} : set Prop) :=
topological_space.generate_open.basic _ (by simp)

lemma continuous_Prop {p : α → Prop} : continuous p ↔ is_open {x | p x} :=
⟨assume h : continuous p,
  have is_open (preimage p {true}),
    from h _ is_open_singleton_true,
  by simp [preimage, eq_true] at this; assumption,
  assume h : is_open {x | p x},
  continuous_generated_from $ assume s (hs : s ∈ {{true}}),
    by simp at hs; simp [hs, preimage, eq_true, h]⟩

end sierpinski

section induced
open topological_space
variables [t : topological_space β] {f : α → β}

theorem is_open_induced {s : set β} (h : is_open s) : (induced f t).is_open (preimage f s) :=
⟨s, h, rfl⟩

lemma nhds_induced_eq_vmap {a : α} : @nhds α (induced f t) a = vmap f (nhds (f a)) :=
le_antisymm
  (assume s ⟨s', hs', (h_s : preimage f s' ⊆ s)⟩,
    have ∃t':set β, is_open t' ∧ t' ⊆ s' ∧ f a ∈ t',
      by simp [mem_nhds_sets_iff] at hs'; assumption,
    let ⟨t', ht', hsub, hin⟩ := this in
    (@nhds α (induced f t) a).upwards_sets
      begin
        simp [mem_nhds_sets_iff],
        exact ⟨preimage f t', is_open_induced ht', hin, preimage_mono hsub⟩
      end
      h_s)
  (le_infi $ assume s, le_infi $ assume ⟨as, ⟨s', is_open_s', s_eq⟩⟩,
    begin
      simp [vmap, mem_nhds_sets_iff, s_eq],
      exact ⟨s', subset.refl _, s', is_open_s', subset.refl _, by rw [s_eq] at as; assumption⟩
    end)

lemma map_nhds_induced_eq {a : α} (h : image f univ ∈ (nhds (f a)).sets) :
  map f (@nhds α (induced f t) a) = nhds (f a) :=
le_antisymm
  ((@continuous_iff_tendsto α β (induced f t) _ _).mp continuous_induced_dom a)
  (assume s, assume hs : preimage f s ∈ (@nhds α (induced f t) a).sets,
    let ⟨t', t_subset, is_open_t, a_in_t⟩ := mem_nhds_sets_iff.mp h in
    let ⟨s', s'_subset, ⟨s'', is_open_s'', s'_eq⟩, a_in_s'⟩ := (@mem_nhds_sets_iff _ (induced f t) _ _).mp hs in
    by subst s'_eq; exact (mem_nhds_sets_iff.mpr $
      ⟨t' ∩ s'',
        assume x ⟨h₁, h₂⟩, match x, h₂, t_subset h₁ with
        | x, h₂, ⟨y, _, y_eq⟩ := begin subst y_eq, exact s'_subset h₂ end
        end,
        is_open_inter is_open_t is_open_s'',
        ⟨a_in_t, a_in_s'⟩⟩))

lemma closure_induced [t : topological_space β] {f : α → β} {a : α} {s : set α}
  (hf : ∀x y, f x = f y → x = y) :
  a ∈ @closure α (topological_space.induced f t) s ↔ f a ∈ closure (f '' s) :=
have vmap f (nhds (f a) ⊓ principal (f '' s)) ≠ ⊥ ↔ nhds (f a) ⊓ principal (f '' s) ≠ ⊥,
  from ⟨assume h₁ h₂, h₁ $ h₂.symm ▸ vmap_bot,
    assume h,
    forall_sets_neq_empty_iff_neq_bot.mp $
      assume s₁ ⟨s₂, hs₂, (hs : preimage f s₂ ⊆ s₁)⟩,
      have f '' s ∈ (nhds (f a) ⊓ principal (f '' s)).sets,
        from mem_inf_sets_of_right $ by simp [subset.refl],
      have s₂ ∩ f '' s ∈ (nhds (f a) ⊓ principal (f '' s)).sets,
        from inter_mem_sets hs₂ this,
      let ⟨b, hb₁, ⟨a, ha, ha₂⟩⟩ := inhabited_of_mem_sets h this in
      ne_empty_of_mem $ hs $ by rwa [←ha₂] at hb₁⟩,
calc a ∈ @closure α (topological_space.induced f t) s
    ↔ (@nhds α (topological_space.induced f t) a) ⊓ principal s ≠ ⊥ : by rw [closure_eq_nhds]; refl
  ... ↔ vmap f (nhds (f a)) ⊓ principal (preimage f (f '' s)) ≠ ⊥ : by rw [nhds_induced_eq_vmap, preimage_image_eq hf]
  ... ↔ vmap f (nhds (f a) ⊓ principal (f '' s)) ≠ ⊥ : by rw [vmap_inf, ←vmap_principal]
  ... ↔ _ : by rwa [closure_eq_nhds]

end induced

section prod
open topological_space
variables [topological_space α] [topological_space β] [topological_space γ]

lemma continuous_fst : continuous (@prod.fst α β) :=
continuous_sup_dom_left continuous_induced_dom

lemma continuous_snd : continuous (@prod.snd α β) :=
continuous_sup_dom_right continuous_induced_dom

lemma continuous_prod_mk {f : γ → α} {g : γ → β}
  (hf : continuous f) (hg : continuous g) : continuous (λx, prod.mk (f x) (g x)) :=
continuous_sup_rng (continuous_induced_rng hf) (continuous_induced_rng hg)

lemma is_open_prod {s : set α} {t : set β} (hs : is_open s) (ht: is_open t) :
  is_open (set.prod s t) :=
is_open_inter (continuous_fst s hs) (continuous_snd t ht)

lemma prod_generate_from_generate_from_eq {s : set (set α)} {t : set (set β)}
  (hs : ⋃₀ s = univ) (ht : ⋃₀ t = univ) :
  @prod.topological_space α β (generate_from s) (generate_from t) =
  generate_from {g | ∃u∈s, ∃v∈t, g = set.prod u v} :=
let G := generate_from {g | ∃u∈s, ∃v∈t, g = set.prod u v} in
le_antisymm
  (sup_le
    (induced_le_iff_le_coinduced.mpr $ generate_from_le $ assume u hu,
      have (⋃v∈t, set.prod u v) = prod.fst ⁻¹' u,
        from calc (⋃v∈t, set.prod u v) = set.prod u univ:
            set.ext $ assume ⟨a, b⟩, by rw [←ht]; simp {contextual:=tt}
          ... = prod.fst ⁻¹' u : by simp [set.prod, preimage],
      show G.is_open (prod.fst ⁻¹' u),
        from this ▸ @is_open_Union _ _ G _ $ assume v, @is_open_Union _ _ G _ $ assume hv,
          generate_open.basic _ ⟨_, hu, _, hv, rfl⟩)
    (induced_le_iff_le_coinduced.mpr $ generate_from_le $ assume v hv,
      have (⋃u∈s, set.prod u v) = prod.snd ⁻¹' v,
        from calc (⋃u∈s, set.prod u v) = set.prod univ v:
            set.ext $ assume ⟨a, b⟩, by rw [←hs]; by_cases b ∈ v; simp [h] {contextual:=tt}
          ... = prod.snd ⁻¹' v : by simp [set.prod, preimage],
      show G.is_open (prod.snd ⁻¹' v),
        from this ▸ @is_open_Union _ _ G _ $ assume u, @is_open_Union _ _ G _ $ assume hu,
          generate_open.basic _ ⟨_, hu, _, hv, rfl⟩))
  (generate_from_le $ assume g ⟨u, hu, v, hv, g_eq⟩, g_eq.symm ▸
    @is_open_prod _ _ (generate_from s) (generate_from t) _ _
      (generate_open.basic _ hu) (generate_open.basic _ hv))

lemma prod_eq_generate_from [tα : topological_space α] [tβ : topological_space β] :
  prod.topological_space =
  generate_from {g | ∃(s:set α) (t:set β), is_open s ∧ is_open t ∧ g = set.prod s t} :=
le_antisymm
  (sup_le
    (assume s ⟨t, ht, s_eq⟩,
      have set.prod t univ = s, by simp [s_eq, preimage, set.prod],
      this ▸ (generate_open.basic _ ⟨t, univ, ht, is_open_univ, rfl⟩))
    (assume s ⟨t, ht, s_eq⟩,
      have set.prod univ t = s, by simp [s_eq, preimage, set.prod],
      this ▸ (generate_open.basic _ ⟨univ, t, is_open_univ, ht, rfl⟩)))
  (generate_from_le $ assume g ⟨s, t, hs, ht, g_eq⟩, g_eq.symm ▸ is_open_prod hs ht)

lemma nhds_prod_eq {a : α} {b : β} : nhds (a, b) = filter.prod (nhds a) (nhds b) :=
by rw [prod_eq_generate_from, nhds_generate_from];
  exact le_antisymm
    (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
      begin
        simp [mem_nhds_sets_iff] at hs, simp [mem_nhds_sets_iff] at ht,
        revert hs ht,
        exact (assume ⟨s', hs', hs_sub, as'⟩ ⟨t', ht', ht_sub, at'⟩,
          infi_le_of_le (set.prod s' t') $
          infi_le_of_le ⟨⟨as', at'⟩, s', t', hs', ht', rfl⟩ $
          principal_mono.mpr $ set.prod_mono hs_sub ht_sub)
      end)
    (le_infi $ assume s, le_infi $ assume ⟨hab, s', t', hs', ht', s_eq⟩,
      begin
        revert hab,
        simp [s_eq],
        exact assume ha hb, @prod_mem_prod α β s' t' (nhds a) (nhds b)
          (mem_nhds_sets_iff.mpr ⟨s', subset.refl s', hs', ha⟩)
          (mem_nhds_sets_iff.mpr ⟨t', subset.refl t', ht', hb⟩)
      end)

lemma is_open_prod_iff {s : set (α×β)} : is_open s ↔
  (∀a b, (a, b) ∈ s → ∃u v, is_open u ∧ is_open v ∧ a ∈ u ∧ b ∈ v ∧ set.prod u v ⊆ s) :=
begin
  rw [is_open_iff_nhds],
  simp [nhds_prod_eq, mem_prod_iff],
  simp [mem_nhds_sets_iff],
  exact (forall_congr $ assume a, forall_congr $ assume b, forall_congr $ assume h,
    ⟨assume ⟨u', ⟨u, hu₁, hu₂, hu₃⟩, v', h, ⟨v, hv₁, hv₂, hv₃⟩⟩,
      ⟨u, hu₁, v, hv₁, hu₃, hv₃, subset.trans (set.prod_mono hu₂ hv₂) h⟩,
      assume ⟨u, hu₁, v, hv₁, hu₃, hv₃, h⟩,
      ⟨u, ⟨u, hu₁, subset.refl u, hu₃⟩, v, h, ⟨v, hv₁, subset.refl v, hv₃⟩⟩⟩)
end

lemma closure_prod_eq {s : set α} {t : set β} :
  closure (set.prod s t) = set.prod (closure s) (closure t) :=
set.ext $ assume ⟨a, b⟩,
have filter.prod (nhds a) (nhds b) ⊓ principal (set.prod s t) =
  filter.prod (nhds a ⊓ principal s) (nhds b ⊓ principal t),
  by rw [←prod_inf_prod, prod_principal_principal],
by simp [closure_eq_nhds, nhds_prod_eq, this]; exact prod_neq_bot

lemma is_closed_prod [topological_space α] [topological_space β] {s₁ : set α} {s₂ : set β}
  (h₁ : is_closed s₁) (h₂ : is_closed s₂) : is_closed (set.prod s₁ s₂) :=
closure_eq_iff_is_closed.mp $ by simp [h₁, h₂, closure_prod_eq, closure_eq_of_is_closed]

lemma is_closed_diagonal [topological_space α] [t2_space α] : is_closed {p:α×α | p.1 = p.2} :=
is_closed_iff_nhds.mpr $ assume ⟨a₁, a₂⟩ h, eq_of_nhds_neq_bot $ assume : nhds a₁ ⊓ nhds a₂ = ⊥, h $
  let ⟨t₁, ht₁, t₂, ht₂, (h' : t₁ ∩ t₂ ⊆ ∅)⟩ :=
    by rw [←empty_in_sets_eq_bot, mem_inf_sets] at this; exact this in
  begin
    rw [nhds_prod_eq, ←empty_in_sets_eq_bot],
    apply filter.upwards_sets,
    apply inter_mem_inf_sets (prod_mem_prod ht₁ ht₂) (mem_principal_sets.mpr (subset.refl _)),
    exact assume ⟨x₁, x₂⟩ ⟨⟨hx₁, hx₂⟩, (heq : x₁ = x₂)⟩,
      show false, from @h' x₁ ⟨hx₁, heq.symm ▸ hx₂⟩
  end

lemma is_closed_eq [topological_space α] [t2_space α] [topological_space β] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : is_closed {x:β | f x = g x} :=
continuous_iff_is_closed.mp (continuous_prod_mk hf hg) _ is_closed_diagonal

/- TODO: more fine grained instances for first_countable_topology, separable_space, t2_space, ... -/
instance [second_countable_topology α] [second_countable_topology β] :
  second_countable_topology (α × β) :=
⟨let ⟨a, ha₁, ha₂, ha₃, ha₄, ha₅⟩ := is_open_generated_countable_inter α in
  let ⟨b, hb₁, hb₂, hb₃, hb₄, hb₅⟩ := is_open_generated_countable_inter β in
  ⟨{g | ∃u∈a, ∃v∈b, g = set.prod u v},
    have {g | ∃u∈a, ∃v∈b, g = set.prod u v} = (⋃u∈a, ⋃v∈b, {set.prod u v}),
      by apply set.ext; simp,
    by rw [this]; exact (countable_bUnion ha₁ $ assume u hu, countable_bUnion hb₁ $ by simp),
    by rw [ha₅, hb₅, prod_generate_from_generate_from_eq ha₄ hb₄]⟩⟩

end prod

section sum
variables [topological_space α] [topological_space β] [topological_space γ]

lemma continuous_inl : continuous (@sum.inl α β) :=
continuous_inf_rng_left continuous_coinduced_rng

lemma continuous_inr : continuous (@sum.inr α β) :=
continuous_inf_rng_right continuous_coinduced_rng

lemma continuous_sum_rec {f : α → γ} {g : β → γ}
  (hf : continuous f) (hg : continuous g) : @continuous (α ⊕ β) γ _ _ (@sum.rec α β (λ_, γ) f g) :=
continuous_inf_dom hf hg

end sum

section subtype
variables [topological_space α] [topological_space β] [topological_space γ] {p : α → Prop}

lemma tendsto_nhds_iff_of_embedding {f : α → β} {g : β → γ} {a : filter α} {b : β} (hg : embedding g) :
  tendsto f a (nhds b) ↔ tendsto (g ∘ f) a (nhds (g b)) :=
by rw [tendsto, tendsto, hg.right, nhds_induced_eq_vmap, le_vmap_iff_map_le, map_map]

lemma continuous_iff_of_embedding {f : α → β} {g : β → γ} (hg : embedding g) :
  continuous f ↔ continuous (g ∘ f) :=
by simp [continuous_iff_tendsto, @tendsto_nhds_iff_of_embedding α β γ _ _ _ f g _ _ hg]

lemma embedding_graph {f : α → β} (hf : continuous f) : embedding (λx, (x, f x)) :=
embedding_of_embedding_compose (continuous_prod_mk continuous_id hf) continuous_fst embedding_id

lemma embedding_subtype_val : embedding (@subtype.val α p) :=
⟨assume a₁ a₂, subtype.eq, rfl⟩

lemma continuous_subtype_val : continuous (@subtype.val α p) :=
continuous_induced_dom

lemma continuous_subtype_mk {f : β → α}
  (hp : ∀x, p (f x)) (h : continuous f) : continuous (λx, (⟨f x, hp x⟩ : subtype p)) :=
continuous_induced_rng h

lemma map_nhds_subtype_val_eq {a : α} (ha : p a) (h : {a | p a} ∈ (nhds a).sets) :
  map (@subtype.val α p) (nhds ⟨a, ha⟩) = nhds a :=
map_nhds_induced_eq (by simp [subtype.val_image, h])

lemma nhds_subtype_eq_vmap {a : α} {h : p a} :
  nhds (⟨a, h⟩ : subtype p) = vmap subtype.val (nhds a) :=
nhds_induced_eq_vmap

lemma continuous_subtype_nhds_cover {f : α → β} {c : ι → α → Prop}
  (c_cover : ∀x:α, ∃i, {x | c i x} ∈ (nhds x).sets)
  (f_cont  : ∀i, continuous (λ(x : subtype (c i)), f x.val)) :
  continuous f :=
continuous_iff_tendsto.mpr $ assume x,
  let ⟨i, (c_sets : {x | c i x} ∈ (nhds x).sets)⟩ := c_cover x in
  let x' : subtype (c i) := ⟨x, mem_of_nhds c_sets⟩ in
  calc map f (nhds x) = map f (map subtype.val (nhds x')) :
      congr_arg (map f) (map_nhds_subtype_val_eq _ $ c_sets).symm
    ... = map (λx:subtype (c i), f x.val) (nhds x') : rfl
    ... ≤ nhds (f x) : continuous_iff_tendsto.mp (f_cont i) x'

lemma continuous_subtype_is_closed_cover {f : α → β} (c : γ → α → Prop)
  (h_lf : locally_finite (λi, {x | c i x}))
  (h_is_closed : ∀i, is_closed {x | c i x})
  (h_cover : ∀x, ∃i, c i x)
  (f_cont  : ∀i, continuous (λ(x : subtype (c i)), f x.val)) :
  continuous f :=
continuous_iff_is_closed.mpr $
  assume s hs,
  have ∀i, is_closed (@subtype.val α {x | c i x} '' (preimage (f ∘ subtype.val) s)),
    from assume i,
    embedding_is_closed embedding_subtype_val
      (by simp [subtype.val_image]; exact h_is_closed i)
      (continuous_iff_is_closed.mp (f_cont i) _ hs),
  have is_closed (⋃i, @subtype.val α {x | c i x} '' (preimage (f ∘ subtype.val) s)),
    from is_closed_Union_of_locally_finite
      (locally_finite_subset h_lf $ assume i x ⟨⟨x', hx'⟩, _, heq⟩, heq ▸ hx')
      this,
  have preimage f s = (⋃i, @subtype.val α {x | c i x} '' (preimage (f ∘ subtype.val) s)),
  begin
    apply set.ext,
    simp,
    exact assume x, ⟨assume hx, let ⟨i, hi⟩ := h_cover x in ⟨i, ⟨x, hi⟩, hx, rfl⟩,
      assume ⟨i, ⟨x', hx'⟩, hx₁, hx₂⟩, hx₂ ▸ hx₁⟩
  end,
  by rwa [this]

lemma closure_subtype {p : α → Prop} {x : {a // p a}} {s : set {a // p a}}:
  x ∈ closure s ↔ x.val ∈ closure (subtype.val '' s) :=
closure_induced $ assume x y, subtype.eq

end subtype

section pi

lemma nhds_pi {ι : Type u} {α : ι → Type v} [t : ∀i, topological_space (α i)] {a : Πi, α i} :
  nhds a = (⨅i, vmap (λx, x i) (nhds (a i))) :=
calc nhds a = (⨅i, @nhds _ (@topological_space.induced _ _ (λx:Πi, α i, x i) (t i)) a) : nhds_supr
  ... = (⨅i, vmap (λx, x i) (nhds (a i))) : by simp [nhds_induced_eq_vmap]

/-- Tychonoff's theorem -/
lemma compact_pi_infinite {ι : Type v} {α : ι → Type u} [∀i:ι, topological_space (α i)]
  {s : Πi:ι, set (α i)} : (∀i, compact (s i)) → compact {x : Πi:ι, α i | ∀i, x i ∈ s i} :=
begin
  simp [compact_iff_ultrafilter_le_nhds, nhds_pi],
  exact assume h f hf hfs,
    let p : Πi:ι, filter (α i) := λi, map (λx:Πi:ι, α i, x i) f in
    have ∀i:ι, ∃a, a∈s i ∧ p i ≤ nhds a,
      from assume i, h i (p i) (ultrafilter_map hf) $
      show preimage (λx:Πi:ι, α i, x i) (s i) ∈ f.sets,
        from f.upwards_sets hfs $ assume x (hx : ∀i, x i ∈ s i), hx i,
    let ⟨a, ha⟩ := classical.axiom_of_choice this in
    ⟨a, assume i, (ha i).left, assume i, le_vmap_iff_map_le.mpr $ (ha i).right⟩
end

end pi

-- TODO: use embeddings from above!
structure dense_embedding [topological_space α] [topological_space β] (e : α → β) :=
(dense   : ∀x, x ∈ closure (e '' univ))
(inj     : ∀x y, e x = e y → x = y)
(induced : ∀a, vmap e (nhds (e a)) = nhds a)

namespace dense_embedding
variables [topological_space α] [topological_space β]
variables {e : α → β} (de : dense_embedding e)

protected lemma embedding (de : dense_embedding e) : embedding e :=
⟨de.inj, eq_of_nhds_eq_nhds begin intro a, rw [← de.induced a, nhds_induced_eq_vmap] end⟩

protected lemma tendsto (de : dense_embedding e) {a : α} : tendsto e (nhds a) (nhds (e a)) :=
by rw [←de.induced a]; exact tendsto_vmap

protected lemma continuous (de : dense_embedding e) {a : α} : continuous e :=
by rw [continuous_iff_tendsto]; exact assume a, de.tendsto

lemma inj_iff (de : dense_embedding e) {x y} : e x = e y ↔ x = y :=
⟨de.inj _ _, assume h, h ▸ rfl⟩

lemma closure_image_univ : closure (e '' univ) = univ :=
let h := de.dense in
set.ext $ assume x, ⟨assume _, trivial, assume _, @h x⟩

protected lemma nhds_inf_neq_bot (de : dense_embedding e) {b : β} : nhds b ⊓ principal (e '' univ) ≠ ⊥ :=
begin
  have h := de.dense,
  simp [closure_eq_nhds] at h,
  exact h _
end

lemma vmap_nhds_neq_bot (de : dense_embedding e) {b : β} : vmap e (nhds b) ≠ ⊥ :=
forall_sets_neq_empty_iff_neq_bot.mp $
assume s ⟨t, ht, (hs : preimage e t ⊆ s)⟩,
have t ∩ e '' univ ∈ (nhds b ⊓ principal (e '' univ)).sets,
  from inter_mem_inf_sets ht (subset.refl _),
let ⟨x, ⟨hx₁, y, hy, y_eq⟩⟩ := inhabited_of_mem_sets de.nhds_inf_neq_bot this in
ne_empty_of_mem $ hs $ show e y ∈ t, from y_eq.symm ▸ hx₁

variables [topological_space γ] [inhabited γ] [regular_space γ]
def ext (de : dense_embedding e) (f : α → γ) : β → γ := lim ∘ map f ∘ vmap e ∘ nhds

lemma ext_eq {b : β} {c : γ} {f : α → γ} (hf : map f (vmap e (nhds b)) ≤ nhds c) : de.ext f b = c :=
lim_eq begin simp; exact vmap_nhds_neq_bot de end hf

lemma ext_e_eq {a : α} {f : α → γ} (de : dense_embedding e)
  (hf : map f (nhds a) ≤ nhds (f a)) : de.ext f (e a) = f a :=
de.ext_eq begin rw de.induced; exact hf end

lemma tendsto_ext {b : β} {f : α → γ} (de : dense_embedding e)
  (hf : {b | ∃c, tendsto f (vmap e $ nhds b) (nhds c)} ∈ (nhds b).sets) :
  tendsto (de.ext f) (nhds b) (nhds (de.ext f b)) :=
let φ := {b | tendsto f (vmap e $ nhds b) (nhds $ de.ext f b)} in
have hφ : φ ∈ (nhds b).sets,
  from (nhds b).upwards_sets hf $ assume b ⟨c, hc⟩,
    show tendsto f (vmap e (nhds b)) (nhds (de.ext f b)), from (de.ext_eq hc).symm ▸ hc,
assume s hs,
let ⟨s'', hs''₁, hs''₂, hs''₃⟩ := nhds_is_closed hs in
let ⟨s', hs'₁, (hs'₂ : preimage e s' ⊆ preimage f s'')⟩ := mem_of_nhds hφ hs''₁ in
let ⟨t, (ht₁ : t ⊆ φ ∩ s'), ht₂, ht₃⟩ := mem_nhds_sets_iff.mp $ inter_mem_sets hφ hs'₁ in
have h₁ : closure (f '' preimage e s') ⊆ s'',
  by rw [closure_subset_iff_subset_of_is_closed hs''₃, image_subset_iff_subset_preimage]; exact hs'₂,
have h₂ : t ⊆ preimage (de.ext f) (closure (f '' preimage e t)), from
  assume b' hb',
  have nhds b' ≤ principal t, by simp; exact mem_nhds_sets ht₂ hb',
  have map f (vmap e (nhds b')) ≤ nhds (de.ext f b') ⊓ principal (f '' preimage e t),
    from calc _ ≤ map f (vmap e (nhds b' ⊓ principal t)) : map_mono $ vmap_mono $ le_inf (le_refl _) this
      ... ≤ map f (vmap e (nhds b')) ⊓ map f (vmap e (principal t)) :
        le_inf (map_mono $ vmap_mono $ inf_le_left) (map_mono $ vmap_mono $ inf_le_right)
      ... ≤ map f (vmap e (nhds b')) ⊓ principal (f '' preimage e t) : by simp [le_refl]
      ... ≤ _ : inf_le_inf ((ht₁ hb').left) (le_refl _),
  show de.ext f b' ∈ closure (f '' preimage e t),
  begin
    rw [closure_eq_nhds],
    apply neq_bot_of_le_neq_bot _ this,
    simp,
    exact de.vmap_nhds_neq_bot
  end,
(nhds b).upwards_sets
  (show t ∈ (nhds b).sets, from mem_nhds_sets ht₂ ht₃)
  (calc t ⊆ preimage (de.ext f) (closure (f '' preimage e t)) : h₂
    ... ⊆ preimage (de.ext f) (closure (f '' preimage e s')) :
      preimage_mono $ closure_mono $ image_subset f $ preimage_mono $ subset.trans ht₁ $ inter_subset_right _ _
    ... ⊆ preimage (de.ext f) s'' : preimage_mono h₁
    ... ⊆ preimage (de.ext f) s : preimage_mono hs''₂)

lemma continuous_ext {f : α → γ} (de : dense_embedding e)
  (hf : ∀b, ∃c, tendsto f (vmap e (nhds b)) (nhds c)) : continuous (de.ext f) :=
continuous_iff_tendsto.mpr $ assume b, de.tendsto_ext $ univ_mem_sets' hf

end dense_embedding

namespace dense_embedding
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

protected def prod {e₁ : α → β} {e₂ : γ → δ} (de₁ : dense_embedding e₁) (de₂ : dense_embedding e₂) :
  dense_embedding (λ(p : α × γ), (e₁ p.1, e₂ p.2)) :=
{ dense_embedding .
  dense   :=
    have closure ((λ(p : α × γ), (e₁ p.1, e₂ p.2)) '' univ) =
        set.prod (closure (e₁ '' univ)) (closure (e₂ '' univ)),
      by rw [←closure_prod_eq, prod_image_image_eq, univ_prod_univ],
    assume ⟨b, d⟩, begin rw [this], simp, constructor, apply de₁.dense, apply de₂.dense end,
  inj     := assume ⟨x₁, x₂⟩ ⟨y₁, y₂⟩,
    by simp; exact assume h₁ h₂, ⟨de₁.inj _ _ h₁, de₂.inj _ _ h₂⟩,
  induced := assume ⟨a, b⟩,
    by rw [nhds_prod_eq, nhds_prod_eq, ←prod_vmap_vmap_eq, de₁.induced, de₂.induced] }

def subtype_emb (p : α → Prop) {e : α → β} (de : dense_embedding e) (x : {x // p x}) :
  {x // x ∈ closure (e '' {x | p x})} :=
⟨e x.1, subset_closure $ mem_image_of_mem e x.2⟩

protected def subtype (p : α → Prop) {e : α → β} (de : dense_embedding e) :
  dense_embedding (de.subtype_emb p) :=
{ dense_embedding .
  dense   := assume ⟨x, hx⟩, closure_subtype.mpr $
    have (λ (x : {x // p x}), e (x.val)) = e ∘ subtype.val, from rfl,
    begin
      simp [(image_comp _ _ _).symm, (∘), subtype_emb],
      rw [this, image_comp, subtype.val_image],
      simp,
      assumption
    end,
  inj     := assume ⟨x, hx⟩ ⟨y, hy⟩ h, subtype.eq $ de.inj x y $ @@congr_arg subtype.val h,
  induced := assume ⟨x, hx⟩,
    by simp [subtype_emb, nhds_subtype_eq_vmap, vmap_vmap_comp, (∘), (de.induced x).symm] }

end dense_embedding


lemma is_closed_property [topological_space α] [topological_space β] {e : α → β} {p : β → Prop}
  (he : closure (e '' univ) = univ) (hp : is_closed {x | p x}) (h : ∀a, p (e a)) :
  ∀b, p b :=
have univ ⊆ {b | p b},
  from calc univ = closure (e '' univ) : he.symm
    ... ⊆ closure {b | p b} : closure_mono $ image_subset_iff_subset_preimage.mpr $ assume a _, h a
    ... = _ : closure_eq_of_is_closed hp,
assume b, this trivial

lemma is_closed_property2 [topological_space α] [topological_space β] {e : α → β} {p : β → β → Prop}
  (he : dense_embedding e) (hp : is_closed {q:β×β | p q.1 q.2}) (h : ∀a₁ a₂, p (e a₁) (e a₂)) :
  ∀b₁ b₂, p b₁ b₂ :=
have ∀q:β×β, p q.1 q.2,
  from is_closed_property ((he.prod he).closure_image_univ) hp $ assume ⟨a₁, a₂⟩, h _ _,
assume b₁ b₂, this ⟨b₁, b₂⟩

lemma is_closed_property3 [topological_space α] [topological_space β] {e : α → β} {p : β → β → β → Prop}
  (he : dense_embedding e) (hp : is_closed {q:β×β×β | p q.1 q.2.1 q.2.2}) (h : ∀a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) :
  ∀b₁ b₂ b₃, p b₁ b₂ b₃ :=
have ∀q:β×β×β, p q.1 q.2.1 q.2.2,
  from is_closed_property ((he.prod $ he.prod he).closure_image_univ) hp $ assume ⟨a₁, a₂, a₃⟩, h _ _ _,
assume b₁ b₂ b₃, this ⟨b₁, b₂, b₃⟩

lemma mem_closure_of_continuous [topological_space α] [topological_space β]
  {f : α → β} {a : α} {s : set α} {t : set β}
  (hf : continuous f) (ha : a ∈ closure s) (h : ∀a∈s, f a ∈ closure t) :
  f a ∈ closure t :=
calc f a ∈ f '' closure s : mem_image_of_mem _ ha
  ... ⊆ closure (f '' s) : image_closure_subset_closure_image hf
  ... ⊆ closure (closure t) : closure_mono $ image_subset_iff_subset_preimage.mpr $ h
  ... ⊆ closure t : begin rw [closure_eq_of_is_closed], exact subset.refl _, exact is_closed_closure end

lemma mem_closure_of_continuous2 [topological_space α] [topological_space β] [topological_space γ]
  {f : α → β → γ} {a : α} {b : β} {s : set α} {t : set β} {u : set γ}
  (hf : continuous (λp:α×β, f p.1 p.2)) (ha : a ∈ closure s) (hb : b ∈ closure t)
  (h : ∀a∈s, ∀b∈t, f a b ∈ closure u) :
  f a b ∈ closure u :=
have (a,b) ∈ closure (set.prod s t),
  by simp [closure_prod_eq, ha, hb],
show f (a, b).1 (a, b).2 ∈ closure u,
  from @mem_closure_of_continuous (α×β) _ _ _ (λp:α×β, f p.1 p.2) (a,b) _ u hf this $
    assume ⟨p₁, p₂⟩ ⟨h₁, h₂⟩, h p₁ h₁ p₂ h₂
