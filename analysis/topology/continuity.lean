/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Continuous functions.

Parts of the formalization is based on the books:
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
A major difference is that this formalization is heavily based on the filter library.
-/
import analysis.topology.topological_space
noncomputable theory

open set filter lattice
local attribute [instance] classical.prop_decidable

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section
variables [topological_space α] [topological_space β] [topological_space γ]

/-- A function between topological spaces is continuous if the preimage
  of every open set is open. -/
def continuous (f : α → β) := ∀s, is_open s → is_open (f ⁻¹' s)

lemma continuous_id : continuous (id : α → α) :=
assume s h, h

lemma continuous.comp {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g):
  continuous (g ∘ f) :=
assume s h, hf _ (hg s h)

lemma continuous.tendsto {f : α → β} (hf : continuous f) (x) :
  tendsto f (nhds x) (nhds (f x)) | s :=
show s ∈ (nhds (f x)).sets → s ∈ (map f (nhds x)).sets,
by simp [nhds_sets]; exact
assume t t_subset t_open fx_in_t,
  ⟨f ⁻¹' t, preimage_mono t_subset, hf t t_open, fx_in_t⟩

lemma continuous_iff_tendsto {f : α → β} :
  continuous f ↔ (∀x, tendsto f (nhds x) (nhds (f x))) :=
⟨continuous.tendsto,
  assume hf : ∀x, tendsto f (nhds x) (nhds (f x)),
  assume s, assume hs : is_open s,
  have ∀a, f a ∈ s → s ∈ (nhds (f a)).sets,
    by simp [nhds_sets]; exact assume a ha, ⟨s, subset.refl s, hs, ha⟩,
  show is_open (f ⁻¹' s),
    by simp [is_open_iff_nhds]; exact assume a ha, hf a (this a ha)⟩

lemma continuous_const {b : β} : continuous (λa:α, b) :=
continuous_iff_tendsto.mpr $ assume a, tendsto_const_nhds

lemma continuous_iff_is_closed {f : α → β} :
  continuous f ↔ (∀s, is_closed s → is_closed (f ⁻¹' s)) :=
⟨assume hf s hs, hf (-s) hs,
  assume hf s, by rw [←is_closed_compl_iff, ←is_closed_compl_iff]; exact hf _⟩

lemma continuous_if {p : α → Prop} {f g : α → β} {h : ∀a, decidable (p a)}
  (hp : ∀a∈frontier {a | p a}, f a = g a) (hf : continuous f) (hg : continuous g) :
  continuous (λa, @ite (p a) (h a) β (f a) (g a)) :=
continuous_iff_is_closed.mpr $
assume s hs,
have (λa, ite (p a) (f a) (g a)) ⁻¹' s =
    (closure {a | p a} ∩  f ⁻¹' s) ∪ (closure {a | ¬ p a} ∩ g ⁻¹' s),
  from set.ext $ assume a,
  classical.by_cases
    (assume : a ∈ frontier {a | p a},
      have hac : a ∈ closure {a | p a}, from this.left,
      have hai : a ∈ closure {a | ¬ p a},
        from have a ∈ - interior {a | p a}, from this.right, by rwa [←closure_compl] at this,
      by by_cases p a; simp [h, hp a this, hac, hai, iff_def] {contextual := tt})
    (assume hf : a ∈ - frontier {a | p a},
      classical.by_cases
        (assume : p a,
          have hc : a ∈ closure {a | p a}, from subset_closure this,
          have hnc : a ∉ closure {a | ¬ p a},
            by show a ∉ closure (- {a | p a}); rw [closure_compl]; simpa [frontier, hc] using hf,
          by simp [this, hc, hnc])
        (assume : ¬ p a,
          have hc : a ∈ closure {a | ¬ p a}, from subset_closure this,
          have hnc : a ∉ closure {a | p a},
            begin
              have hc : a ∈ closure (- {a | p a}), from hc,
              simp [closure_compl] at hc,
              simpa [frontier, hc] using hf
            end,
          by simp [this, hc, hnc])),
by rw [this]; exact is_closed_union
  (is_closed_inter is_closed_closure $ continuous_iff_is_closed.mp hf s hs)
  (is_closed_inter is_closed_closure $ continuous_iff_is_closed.mp hg s hs)

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
by simp [image_subset_iff, closure_eq_nhds]; assumption

lemma compact_image {s : set α} {f : α → β} (hs : compact s) (hf : continuous f) : compact (f '' s) :=
compact_of_finite_subcover $ assume c hco hcs,
  have hdo : ∀t∈c, is_open (f ⁻¹' t), from assume t' ht, hf _ $ hco _ ht,
  have hds : s ⊆ ⋃i∈c, f ⁻¹' i,
    by simpa [subset_def, -mem_image] using hcs,
  let ⟨d', hcd', hfd', hd'⟩ := compact_elim_finite_subcover_image hs hdo hds in
  ⟨d', hcd', hfd', by simpa [subset_def, -mem_image, image_subset_iff] using hd'⟩

end

section constructions
local notation `cont` := @continuous _ _
local notation `tspace` := topological_space
open topological_space

variables {f : α → β} {ι : Sort*}

lemma continuous_iff_induced_le {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f ↔ induced f t₂ ≤ t₁ :=
⟨assume hc s ⟨t, ht, s_eq⟩, s_eq.symm ▸ hc t ht,
  assume hle s h, hle _ ⟨_, h, rfl⟩⟩

lemma continuous_iff_le_coinduced {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f ↔ t₂ ≤ coinduced f t₁ := iff.rfl

theorem continuous_generated_from {t : tspace α} {b : set (set β)}
  (h : ∀s∈b, is_open (f ⁻¹' s)) : cont t (generate_from b) f :=
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

lemma continuous_le_dom {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h₁ : t₁ ≤ t₂) (h₂ : cont t₁ t₃ f) : cont t₂ t₃ f :=
assume s h, h₁ _ (h₂ s h)

lemma continuous_le_rng {t₁ : tspace α} {t₂ t₃ : tspace β}
  (h₁ : t₃ ≤ t₂) (h₂ : cont t₁ t₂ f) : cont t₁ t₃ f :=
assume s h, h₂ s (h₁ s h)

lemma continuous_inf_dom {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h₁ : cont t₁ t₃ f) (h₂ : cont t₂ t₃ f) : cont (t₁ ⊓ t₂) t₃ f :=
assume s h, ⟨h₁ s h, h₂ s h⟩

lemma continuous_inf_rng_left {t₁ : tspace α} {t₃ t₂ : tspace β} :
  cont t₁ t₂ f → cont t₁ (t₂ ⊓ t₃) f :=
continuous_le_rng inf_le_left

lemma continuous_inf_rng_right {t₁ : tspace α} {t₃ t₂ : tspace β} :
  cont t₁ t₃ f → cont t₁ (t₂ ⊓ t₃) f :=
continuous_le_rng inf_le_right

lemma continuous_Inf_dom {t₁ : set (tspace α)} {t₂ : tspace β}
  (h : ∀t∈t₁, cont t t₂ f) : cont (Inf t₁) t₂ f :=
assume s hs t ht, h t ht s hs

lemma continuous_Inf_rng {t₁ : tspace α} {t₂ : set (tspace β)} {t : tspace β}
  (h₁ : t ∈ t₂) (hf : cont t₁ t f) : cont t₁ (Inf t₂) f :=
assume s hs, hf s $ hs t h₁

lemma continuous_infi_dom {t₁ : ι → tspace α} {t₂ : tspace β}
  (h : ∀i, cont (t₁ i) t₂ f) : cont (infi t₁) t₂ f :=
continuous_Inf_dom $ assume t ⟨i, (t_eq : t = t₁ i)⟩, t_eq.symm ▸ h i

lemma continuous_infi_rng {t₁ : tspace α} {t₂ : ι → tspace β} {i : ι}
  (h : cont t₁ (t₂ i) f) : cont t₁ (infi t₂) f :=
continuous_Inf_rng ⟨i, rfl⟩ h

lemma continuous_sup_rng {t₁ : tspace α} {t₂ t₃ : tspace β}
  (h₁ : cont t₁ t₂ f) (h₂ : cont t₁ t₃ f) : cont t₁ (t₂ ⊔ t₃) f :=
continuous_iff_le_coinduced.2 $ sup_le
  (continuous_iff_le_coinduced.1 h₁)
  (continuous_iff_le_coinduced.1 h₂)

lemma continuous_sup_dom_left {t₁ t₂ : tspace α} {t₃ : tspace β} :
  cont t₁ t₃ f → cont (t₁ ⊔ t₂) t₃ f :=
continuous_le_dom le_sup_left

lemma continuous_sup_dom_right {t₁ t₂ : tspace α} {t₃ : tspace β} :
  cont t₂ t₃ f → cont (t₁ ⊔ t₂) t₃ f :=
continuous_le_dom le_sup_right

lemma continuous_Sup_dom {t₁ : set (tspace α)} {t₂ : tspace β} {t : tspace α} (h₁ : t ∈ t₁) :
  cont t t₂ f → cont (Sup t₁) t₂ f :=
continuous_le_dom $ le_Sup h₁

lemma continuous_Sup_rng {t₁ : tspace α} {t₂ : set (tspace β)}
  (h : ∀t∈t₂, cont t₁ t f) : cont t₁ (Sup t₂) f :=
continuous_iff_le_coinduced.2 $ Sup_le $ assume b hb, continuous_iff_le_coinduced.1 $ h b hb

lemma continuous_supr_dom {t₁ : ι → tspace α} {t₂ : tspace β} {i : ι} :
  cont (t₁ i) t₂ f → cont (supr t₁) t₂ f :=
continuous_le_dom $ le_supr _ _

lemma continuous_supr_rng {t₁ : tspace α} {t₂ : ι → tspace β}
  (h : ∀i, cont t₁ (t₂ i) f) : cont t₁ (supr t₂) f :=
continuous_iff_le_coinduced.2 $ supr_le $ assume i, continuous_iff_le_coinduced.1 $ h i

lemma continuous_top {t : tspace β} : cont ⊤ t f :=
assume s h, trivial

lemma continuous_bot {t : tspace α} : cont t ⊥ f :=
continuous_Inf_rng (mem_univ $ coinduced f t) continuous_coinduced_rng

end constructions

section embedding

lemma induced_mono {t₁ t₂ : topological_space α} {f : β → α} (h : t₁ ≤ t₂) :
  t₁.induced f ≤ t₂.induced f :=
continuous_iff_induced_le.mp $
  show @continuous β α (@topological_space.induced β α f t₂) t₁ (id ∘ f),
  begin
    apply continuous.comp,
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

/-- A function between topological spaces is an embedding if it is injective,
  and for all `s : set α`, `s` is open iff it is the preimage of an open set. -/
def embedding [tα : topological_space α] [tβ : topological_space β] (f : α → β) : Prop :=
function.injective f ∧ tα = tβ.induced f

variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

lemma embedding_id : embedding (@id α) :=
⟨assume a₁ a₂ h, h, induced_id.symm⟩

lemma embedding_compose {f : α → β} {g : β → γ} (hf : embedding f) (hg : embedding g) :
  embedding (g ∘ f) :=
⟨assume a₁ a₂ h, hf.left $ hg.left h, by rw [hf.right, hg.right, induced_compose]⟩

lemma embedding_prod_mk {f : α → β} {g : γ → δ} (hf : embedding f) (hg : embedding g) :
  embedding (λx:α×γ, (f x.1, g x.2)) :=
⟨assume ⟨x₁, x₂⟩ ⟨y₁, y₂⟩, by simp; exact assume h₁ h₂, ⟨hf.left h₁, hg.left h₂⟩,
  by rw [prod.topological_space, prod.topological_space, hf.right, hg.right,
         induced_compose, induced_compose, induced_sup, induced_compose, induced_compose]⟩

lemma embedding_of_embedding_compose {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g)
  (hgf : embedding (g ∘ f)) : embedding f :=
⟨assume a₁ a₂ h, hgf.left $ by simp [h, (∘)],
  le_antisymm
    (by rw [hgf.right, ← continuous_iff_induced_le];
        apply continuous_induced_dom.comp hg)
    (by rwa ← continuous_iff_induced_le)⟩

lemma embedding_open {f : α → β} {s : set α}
  (hf : embedding f) (h : is_open (range f)) (hs : is_open s) : is_open (f '' s) :=
let ⟨t, ht, h_eq⟩ := by rw [hf.right] at hs; exact hs in
have is_open (t ∩ range f), from is_open_inter ht h,
h_eq.symm ▸ by rwa [image_preimage_eq_inter_range]

lemma embedding_is_closed {f : α → β} {s : set α}
  (hf : embedding f) (h : is_closed (range f)) (hs : is_closed s) : is_closed (f '' s) :=
let ⟨t, ht, h_eq⟩ := by rw [hf.right, is_closed_induced_iff] at hs; exact hs in
have is_closed (t ∩ range f), from is_closed_inter ht h,
h_eq.symm ▸ by rwa [image_preimage_eq_inter_range]

end embedding

section sierpinski
variables [topological_space α]

@[simp] lemma is_open_singleton_true : is_open ({true} : set Prop) :=
topological_space.generate_open.basic _ (by simp)

lemma continuous_Prop {p : α → Prop} : continuous p ↔ is_open {x | p x} :=
⟨assume h : continuous p,
  have is_open (p ⁻¹' {true}),
    from h _ is_open_singleton_true,
  by simp [preimage, eq_true] at this; assumption,
  assume h : is_open {x | p x},
  continuous_generated_from $ assume s (hs : s ∈ {{true}}),
    by simp at hs; simp [hs, preimage, eq_true, h]⟩

end sierpinski

section induced
open topological_space
variables [t : topological_space β] {f : α → β}

theorem is_open_induced {s : set β} (h : is_open s) : (induced f t).is_open (f ⁻¹' s) :=
⟨s, h, rfl⟩

lemma nhds_induced_eq_vmap {a : α} : @nhds α (induced f t) a = vmap f (nhds (f a)) :=
le_antisymm
  (assume s ⟨s', hs', (h_s : f ⁻¹' s' ⊆ s)⟩,
    let ⟨t', hsub, ht', hin⟩ := mem_nhds_sets_iff.1 hs' in
    (@nhds α (induced f t) a).upwards_sets
      begin
        simp [mem_nhds_sets_iff],
        exact ⟨preimage f t', preimage_mono hsub, is_open_induced ht', hin⟩
      end
      h_s)
  (le_infi $ assume s, le_infi $ assume ⟨as, s', is_open_s', s_eq⟩,
    begin
      simp [vmap, mem_nhds_sets_iff, s_eq],
      exact ⟨s', ⟨s', subset.refl _, is_open_s', by rwa [s_eq] at as⟩, subset.refl _⟩
    end)

lemma map_nhds_induced_eq {a : α} (h : image f univ ∈ (nhds (f a)).sets) :
  map f (@nhds α (induced f t) a) = nhds (f a) :=
le_antisymm
  (@continuous.tendsto α β (induced f t) _ _ continuous_induced_dom a)
  (assume s, assume hs : f ⁻¹' s ∈ (@nhds α (induced f t) a).sets,
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
      assume s₁ ⟨s₂, hs₂, (hs : f ⁻¹' s₂ ⊆ s₁)⟩,
      have f '' s ∈ (nhds (f a) ⊓ principal (f '' s)).sets,
        from mem_inf_sets_of_right $ by simp [subset.refl],
      have s₂ ∩ f '' s ∈ (nhds (f a) ⊓ principal (f '' s)).sets,
        from inter_mem_sets hs₂ this,
      let ⟨b, hb₁, ⟨a, ha, ha₂⟩⟩ := inhabited_of_mem_sets h this in
      ne_empty_of_mem $ hs $ by rwa [←ha₂] at hb₁⟩,
calc a ∈ @closure α (topological_space.induced f t) s
    ↔ (@nhds α (topological_space.induced f t) a) ⊓ principal s ≠ ⊥ : by rw [closure_eq_nhds]; refl
  ... ↔ vmap f (nhds (f a)) ⊓ principal (f ⁻¹' (f '' s)) ≠ ⊥ : by rw [nhds_induced_eq_vmap, preimage_image_eq _ hf]
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

lemma continuous.prod_mk {f : γ → α} {g : γ → β}
  (hf : continuous f) (hg : continuous g) : continuous (λx, prod.mk (f x) (g x)) :=
continuous_sup_rng (continuous_induced_rng hf) (continuous_induced_rng hg)

lemma is_open_prod {s : set α} {t : set β} (hs : is_open s) (ht : is_open t) :
  is_open (set.prod s t) :=
is_open_inter (continuous_fst s hs) (continuous_snd t ht)

lemma nhds_prod_eq {a : α} {b : β} : nhds (a, b) = filter.prod (nhds a) (nhds b) :=
by rw [filter.prod, prod.topological_space, nhds_sup, nhds_induced_eq_vmap, nhds_induced_eq_vmap]

lemma prod_generate_from_generate_from_eq {s : set (set α)} {t : set (set β)}
  (hs : ⋃₀ s = univ) (ht : ⋃₀ t = univ) :
  @prod.topological_space α β (generate_from s) (generate_from t) =
  generate_from {g | ∃u∈s, ∃v∈t, g = set.prod u v} :=
let G := generate_from {g | ∃u∈s, ∃v∈t, g = set.prod u v} in
le_antisymm
  (sup_le
    (induced_le_iff_le_coinduced.mpr $ generate_from_le $ assume u hu,
      have (⋃v∈t, set.prod u v) = prod.fst ⁻¹' u,
        from calc (⋃v∈t, set.prod u v) = set.prod u univ :
            set.ext $ assume ⟨a, b⟩, by rw ← ht; simp [and.left_comm] {contextual:=tt}
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

lemma is_open_prod_iff {s : set (α×β)} : is_open s ↔
  (∀a b, (a, b) ∈ s → ∃u v, is_open u ∧ is_open v ∧ a ∈ u ∧ b ∈ v ∧ set.prod u v ⊆ s) :=
begin
  rw [is_open_iff_nhds],
  simp [nhds_prod_eq, mem_prod_iff],
  simp [mem_nhds_sets_iff],
  exact forall_congr (assume a, ball_congr $ assume b h,
    ⟨assume ⟨u', ⟨u, us, uo, au⟩, v', ⟨v, vs, vo, bv⟩, h⟩,
      ⟨u, uo, v, vo, au, bv, subset.trans (set.prod_mono us vs) h⟩,
      assume ⟨u, uo, v, vo, au, bv, h⟩,
      ⟨u, ⟨u, subset.refl u, uo, au⟩, v, ⟨v, subset.refl v, vo, bv⟩, h⟩⟩)
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
continuous_iff_is_closed.mp (hf.prod_mk hg) _ is_closed_diagonal

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

lemma embedding.tendsto_nhds_iff {f : α → β} {g : β → γ} {a : filter α} {b : β} (hg : embedding g) :
  tendsto f a (nhds b) ↔ tendsto (g ∘ f) a (nhds (g b)) :=
by rw [tendsto, tendsto, hg.right, nhds_induced_eq_vmap, ← map_le_iff_le_vmap, map_map]

lemma embedding.continuous_iff {f : α → β} {g : β → γ} (hg : embedding g) :
  continuous f ↔ continuous (g ∘ f) :=
by simp [continuous_iff_tendsto, @embedding.tendsto_nhds_iff α β γ _ _ _ f g _ _ hg]

lemma embedding_graph {f : α → β} (hf : continuous f) : embedding (λx, (x, f x)) :=
embedding_of_embedding_compose (continuous_id.prod_mk hf) continuous_fst embedding_id

lemma embedding_subtype_val : embedding (@subtype.val α p) :=
⟨assume a₁ a₂, subtype.eq, rfl⟩

lemma continuous_subtype_val : continuous (@subtype.val α p) :=
continuous_induced_dom

lemma continuous_subtype_mk {f : β → α}
  (hp : ∀x, p (f x)) (h : continuous f) : continuous (λx, (⟨f x, hp x⟩ : subtype p)) :=
continuous_induced_rng h

lemma map_nhds_subtype_val_eq {a : α} (ha : p a) (h : {a | p a} ∈ (nhds a).sets) :
  map (@subtype.val α p) (nhds ⟨a, ha⟩) = nhds a :=
map_nhds_induced_eq (by simp [subtype_val_image, h])

lemma nhds_subtype_eq_vmap {a : α} {h : p a} :
  nhds (⟨a, h⟩ : subtype p) = vmap subtype.val (nhds a) :=
nhds_induced_eq_vmap

lemma continuous_subtype_nhds_cover {ι : Sort*} {f : α → β} {c : ι → α → Prop}
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
  have ∀i, is_closed (@subtype.val α {x | c i x} '' (f ∘ subtype.val ⁻¹' s)),
    from assume i,
    embedding_is_closed embedding_subtype_val
      (by simp [subtype_val_range]; exact h_is_closed i)
      (continuous_iff_is_closed.mp (f_cont i) _ hs),
  have is_closed (⋃i, @subtype.val α {x | c i x} '' (f ∘ subtype.val ⁻¹' s)),
    from is_closed_Union_of_locally_finite
      (locally_finite_subset h_lf $ assume i x ⟨⟨x', hx'⟩, _, heq⟩, heq ▸ hx')
      this,
  have f ⁻¹' s = (⋃i, @subtype.val α {x | c i x} '' (f ∘ subtype.val ⁻¹' s)),
  begin
    apply set.ext,
    have : ∀ (x : α), f x ∈ s ↔ ∃ (i : γ), c i x ∧ f x ∈ s :=
      λ x, ⟨λ hx, let ⟨i, hi⟩ := h_cover x in ⟨i, hi, hx⟩,
            λ ⟨i, hi, hx⟩, hx⟩,
    simp [and.comm, and.left_comm], simpa [(∘)],
  end,
  by rwa [this]

lemma closure_subtype {p : α → Prop} {x : {a // p a}} {s : set {a // p a}}:
  x ∈ closure s ↔ x.val ∈ closure (subtype.val '' s) :=
closure_induced $ assume x y, subtype.eq

end subtype

section pi
variables {ι : Type*} {π : ι → Type*}

lemma continuous_pi [topological_space α] [∀i, topological_space (π i)] {f : α → Πi:ι, π i}
  (h : ∀i, continuous (λa, f a i)) : continuous f :=
continuous_supr_rng $ assume i, continuous_induced_rng $ h i

lemma continuous_apply [topological_space α] [∀i, topological_space (π i)] (i : ι) :
  continuous (λp:Πi, π i, p i) :=
continuous_supr_dom continuous_induced_dom

lemma nhds_pi [t : ∀i, topological_space (π i)] {a : Πi, π i} :
  nhds a = (⨅i, vmap (λx, x i) (nhds (a i))) :=
calc nhds a = (⨅i, @nhds _ (@topological_space.induced _ _ (λx:Πi, π i, x i) (t i)) a) : nhds_supr
  ... = (⨅i, vmap (λx, x i) (nhds (a i))) : by simp [nhds_induced_eq_vmap]

/-- Tychonoff's theorem -/
lemma compact_pi_infinite [∀i, topological_space (π i)] {s : Πi:ι, set (π i)} :
  (∀i, compact (s i)) → compact {x : Πi:ι, π i | ∀i, x i ∈ s i} :=
begin
  simp [compact_iff_ultrafilter_le_nhds, nhds_pi],
  exact assume h f hf hfs,
    let p : Πi:ι, filter (π i) := λi, map (λx:Πi:ι, π i, x i) f in
    have ∀i:ι, ∃a, a∈s i ∧ p i ≤ nhds a,
      from assume i, h i (p i) (ultrafilter_map hf) $
      show (λx:Πi:ι, π i, x i) ⁻¹' s i ∈ f.sets,
        from f.upwards_sets hfs $ assume x (hx : ∀i, x i ∈ s i), hx i,
    let ⟨a, ha⟩ := classical.axiom_of_choice this in
    ⟨a, assume i, (ha i).left, assume i, map_le_iff_le_vmap.mp $ (ha i).right⟩
end

end pi

-- TODO: use embeddings from above!
structure dense_embedding [topological_space α] [topological_space β] (e : α → β) : Prop :=
(dense   : ∀x, x ∈ closure (range e))
(inj     : function.injective e)
(induced : ∀a, vmap e (nhds (e a)) = nhds a)

theorem dense_embedding.mk'
  [topological_space α] [topological_space β] (e : α → β)
  (c     : continuous e)
  (dense : ∀x, x ∈ closure (range e))
  (inj   : function.injective e)
  (H     : ∀ (a:α) s ∈ (nhds a).sets,
    ∃t ∈ (nhds (e a)).sets, ∀ b, e b ∈ t → b ∈ s) :
  dense_embedding e :=
⟨dense, inj, λ a, le_antisymm
  (by simpa [le_def] using H a)
  (tendsto_iff_vmap.1 $ c.tendsto _)⟩

namespace dense_embedding
variables [topological_space α] [topological_space β]
variables {e : α → β} (de : dense_embedding e)

protected lemma embedding (de : dense_embedding e) : embedding e :=
⟨de.inj, eq_of_nhds_eq_nhds begin intro a, rw [← de.induced a, nhds_induced_eq_vmap] end⟩

protected lemma tendsto (de : dense_embedding e) {a : α} : tendsto e (nhds a) (nhds (e a)) :=
by rw [←de.induced a]; exact tendsto_vmap

protected lemma continuous (de : dense_embedding e) {a : α} : continuous e :=
continuous_iff_tendsto.2 $ λ a, de.tendsto

lemma inj_iff (de : dense_embedding e) {x y} : e x = e y ↔ x = y := de.inj.eq_iff

lemma closure_range : closure (range e) = univ :=
let h := de.dense in
set.ext $ assume x, ⟨assume _, trivial, assume _, @h x⟩

protected lemma nhds_inf_neq_bot (de : dense_embedding e) {b : β} : nhds b ⊓ principal (range e) ≠ ⊥ :=
begin
  have h := de.dense,
  simp [closure_eq_nhds] at h,
  exact h _
end

lemma vmap_nhds_neq_bot (de : dense_embedding e) {b : β} : vmap e (nhds b) ≠ ⊥ :=
forall_sets_neq_empty_iff_neq_bot.mp $
assume s ⟨t, ht, (hs : e ⁻¹' t ⊆ s)⟩,
have t ∩ range e ∈ (nhds b ⊓ principal (range e)).sets,
  from inter_mem_inf_sets ht (subset.refl _),
let ⟨_, ⟨hx₁, y, rfl⟩⟩ := inhabited_of_mem_sets de.nhds_inf_neq_bot this in
subset_ne_empty hs $ ne_empty_of_mem hx₁

variables [topological_space γ] [inhabited γ] [regular_space γ]
/-- If `e : α → β` is a dense embedding, then any function `α → γ` extends to a function `β → γ`. -/
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
let ⟨s', hs'₁, (hs'₂ : e ⁻¹' s' ⊆ f ⁻¹' s'')⟩ := mem_of_nhds hφ hs''₁ in
let ⟨t, (ht₁ : t ⊆ φ ∩ s'), ht₂, ht₃⟩ := mem_nhds_sets_iff.mp $ inter_mem_sets hφ hs'₁ in
have h₁ : closure (f '' (e ⁻¹' s')) ⊆ s'',
  by rw [closure_subset_iff_subset_of_is_closed hs''₃, image_subset_iff]; exact hs'₂,
have h₂ : t ⊆ de.ext f ⁻¹' closure (f '' (e ⁻¹' t)), from
  assume b' hb',
  have nhds b' ≤ principal t, by simp; exact mem_nhds_sets ht₂ hb',
  have map f (vmap e (nhds b')) ≤ nhds (de.ext f b') ⊓ principal (f '' (e ⁻¹' t)),
    from calc _ ≤ map f (vmap e (nhds b' ⊓ principal t)) : map_mono $ vmap_mono $ le_inf (le_refl _) this
      ... ≤ map f (vmap e (nhds b')) ⊓ map f (vmap e (principal t)) :
        le_inf (map_mono $ vmap_mono $ inf_le_left) (map_mono $ vmap_mono $ inf_le_right)
      ... ≤ map f (vmap e (nhds b')) ⊓ principal (f '' (e ⁻¹' t)) : by simp [le_refl]
      ... ≤ _ : inf_le_inf ((ht₁ hb').left) (le_refl _),
  show de.ext f b' ∈ closure (f '' (e ⁻¹' t)),
  begin
    rw [closure_eq_nhds],
    apply neq_bot_of_le_neq_bot _ this,
    simp,
    exact de.vmap_nhds_neq_bot
  end,
(nhds b).upwards_sets
  (show t ∈ (nhds b).sets, from mem_nhds_sets ht₂ ht₃)
  (calc t ⊆ de.ext f ⁻¹' closure (f '' (e ⁻¹' t)) : h₂
    ... ⊆ de.ext f ⁻¹' closure (f '' (e ⁻¹' s')) :
      preimage_mono $ closure_mono $ image_subset f $ preimage_mono $ subset.trans ht₁ $ inter_subset_right _ _
    ... ⊆ de.ext f ⁻¹' s'' : preimage_mono h₁
    ... ⊆ de.ext f ⁻¹' s : preimage_mono hs''₂)

lemma continuous_ext {f : α → γ} (de : dense_embedding e)
  (hf : ∀b, ∃c, tendsto f (vmap e (nhds b)) (nhds c)) : continuous (de.ext f) :=
continuous_iff_tendsto.mpr $ assume b, de.tendsto_ext $ univ_mem_sets' hf

end dense_embedding

namespace dense_embedding
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

/-- The product of two dense embeddings is a dense embedding -/
protected def prod {e₁ : α → β} {e₂ : γ → δ} (de₁ : dense_embedding e₁) (de₂ : dense_embedding e₂) :
  dense_embedding (λ(p : α × γ), (e₁ p.1, e₂ p.2)) :=
{ dense_embedding .
  dense   :=
    have closure (range (λ(p : α × γ), (e₁ p.1, e₂ p.2))) =
        set.prod (closure (range e₁)) (closure (range e₂)),
      by rw [←closure_prod_eq, prod_range_range_eq],
    assume ⟨b, d⟩, begin rw [this], simp, constructor, apply de₁.dense, apply de₂.dense end,
  inj     := assume ⟨x₁, x₂⟩ ⟨y₁, y₂⟩,
    by simp; exact assume h₁ h₂, ⟨de₁.inj h₁, de₂.inj h₂⟩,
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
      rw ← image_univ,
      simp [(image_comp _ _ _).symm, (∘), subtype_emb, -image_univ],
      rw [this, image_comp, subtype_val_image],
      simp,
      assumption
    end,
  inj     := assume ⟨x, hx⟩ ⟨y, hy⟩ h, subtype.eq $ de.inj $ @@congr_arg subtype.val h,
  induced := assume ⟨x, hx⟩,
    by simp [subtype_emb, nhds_subtype_eq_vmap, vmap_vmap_comp, (∘), (de.induced x).symm] }

end dense_embedding


lemma is_closed_property [topological_space α] [topological_space β] {e : α → β} {p : β → Prop}
  (he : closure (range e) = univ) (hp : is_closed {x | p x}) (h : ∀a, p (e a)) :
  ∀b, p b :=
have univ ⊆ {b | p b},
  from calc univ = closure (range e) : he.symm
    ... ⊆ closure {b | p b} : closure_mono $ range_subset_iff.mpr h
    ... = _ : closure_eq_of_is_closed hp,
assume b, this trivial

lemma is_closed_property2 [topological_space α] [topological_space β] {e : α → β} {p : β → β → Prop}
  (he : dense_embedding e) (hp : is_closed {q:β×β | p q.1 q.2}) (h : ∀a₁ a₂, p (e a₁) (e a₂)) :
  ∀b₁ b₂, p b₁ b₂ :=
have ∀q:β×β, p q.1 q.2,
  from is_closed_property (he.prod he).closure_range hp $ assume a, h _ _,
assume b₁ b₂, this ⟨b₁, b₂⟩

lemma is_closed_property3 [topological_space α] [topological_space β] {e : α → β} {p : β → β → β → Prop}
  (he : dense_embedding e) (hp : is_closed {q:β×β×β | p q.1 q.2.1 q.2.2}) (h : ∀a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) :
  ∀b₁ b₂ b₃, p b₁ b₂ b₃ :=
have ∀q:β×β×β, p q.1 q.2.1 q.2.2,
  from is_closed_property (he.prod $ he.prod he).closure_range hp $ assume ⟨a₁, a₂, a₃⟩, h _ _ _,
assume b₁ b₂ b₃, this ⟨b₁, b₂, b₃⟩

lemma mem_closure_of_continuous [topological_space α] [topological_space β]
  {f : α → β} {a : α} {s : set α} {t : set β}
  (hf : continuous f) (ha : a ∈ closure s) (h : ∀a∈s, f a ∈ closure t) :
  f a ∈ closure t :=
calc f a ∈ f '' closure s : mem_image_of_mem _ ha
  ... ⊆ closure (f '' s) : image_closure_subset_closure_image hf
  ... ⊆ closure (closure t) : closure_mono $ image_subset_iff.mpr $ h
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
