/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot

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

lemma continuous_of_discrete_topology [discrete_topology α] {f : α → β} : continuous f :=
λs hs, is_open_discrete _

lemma continuous_iff_is_closed {f : α → β} :
  continuous f ↔ (∀s, is_closed s → is_closed (f ⁻¹' s)) :=
⟨assume hf s hs, hf (-s) hs,
  assume hf s, by rw [←is_closed_compl_iff, ←is_closed_compl_iff]; exact hf _⟩

lemma continuous_at_iff_ultrafilter {f : α → β} (x) : tendsto f (nhds x) (nhds (f x)) ↔
  ∀ g, is_ultrafilter g → g ≤ nhds x → g.map f ≤ nhds (f x) :=
tendsto_iff_ultrafilter f (nhds x) (nhds (f x))

lemma continuous_iff_ultrafilter {f : α → β} :
  continuous f ↔ ∀ x g, is_ultrafilter g → g ≤ nhds x → g.map f ≤ nhds (f x) :=
by simp only [continuous_iff_tendsto, continuous_at_iff_ultrafilter]

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

lemma mem_closure [topological_space α] [topological_space β]
  {s : set α} {t : set β} {f : α → β} {a : α}
  (hf : continuous f) (ha : a ∈ closure s) (ht : ∀a∈s, f a ∈ t) : f a ∈ closure t :=
subset.trans (image_closure_subset_closure_image hf) (closure_mono $ image_subset_iff.2 ht) $
  (mem_image_of_mem f ha)

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

lemma continuous_iff_le_coinduced {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f ↔ t₂ ≤ coinduced f t₁ := iff.rfl

lemma continuous_iff_induced_le {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f ↔ induced f t₂ ≤ t₁ :=
iff.trans continuous_iff_le_coinduced (gc_induced_coinduced f _ _).symm

theorem continuous_generated_from {t : tspace α} {b : set (set β)}
  (h : ∀s∈b, is_open (f ⁻¹' s)) : cont t (generate_from b) f :=
continuous_iff_le_coinduced.2 $ generate_from_le h

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
continuous_iff_induced_le.2 $ le_Inf $ assume t ht, continuous_iff_induced_le.1 $ h t ht

lemma continuous_Inf_rng {t₁ : tspace α} {t₂ : set (tspace β)} {t : tspace β}
  (h₁ : t ∈ t₂) (hf : cont t₁ t f) : cont t₁ (Inf t₂) f :=
continuous_iff_le_coinduced.2 $ Inf_le_of_le h₁ $ continuous_iff_le_coinduced.1 hf

lemma continuous_infi_dom {t₁ : ι → tspace α} {t₂ : tspace β}
  (h : ∀i, cont (t₁ i) t₂ f) : cont (infi t₁) t₂ f :=
continuous_Inf_dom $ assume t ⟨i, (t_eq : t₁ i = t)⟩, t_eq ▸ h i

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
continuous_iff_induced_le.2 $ le_top

lemma continuous_bot {t : tspace α} : cont t ⊥ f :=
continuous_iff_le_coinduced.2 $ bot_le

end constructions

section induced
open topological_space
variables [t : topological_space β] {f : α → β}

theorem is_open_induced {s : set β} (h : is_open s) : (induced f t).is_open (f ⁻¹' s) :=
⟨s, h, rfl⟩

lemma nhds_induced_eq_comap {a : α} : @nhds α (induced f t) a = comap f (nhds (f a)) :=
le_antisymm
  (assume s ⟨s', hs', (h_s : f ⁻¹' s' ⊆ s)⟩,
    let ⟨t', hsub, ht', hin⟩ := mem_nhds_sets_iff.1 hs' in
    (@nhds α (induced f t) a).sets_of_superset
      begin
        simp [mem_nhds_sets_iff],
        exact ⟨preimage f t', preimage_mono hsub, is_open_induced ht', hin⟩
      end
      h_s)
  (le_infi $ assume s, le_infi $ assume ⟨as, s', is_open_s', s_eq⟩,
    begin
      simp [comap, mem_nhds_sets_iff, s_eq],
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
have comap f (nhds (f a) ⊓ principal (f '' s)) ≠ ⊥ ↔ nhds (f a) ⊓ principal (f '' s) ≠ ⊥,
  from ⟨assume h₁ h₂, h₁ $ h₂.symm ▸ comap_bot,
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
  ... ↔ comap f (nhds (f a)) ⊓ principal (f ⁻¹' (f '' s)) ≠ ⊥ : by rw [nhds_induced_eq_comap, preimage_image_eq _ hf]
  ... ↔ comap f (nhds (f a) ⊓ principal (f '' s)) ≠ ⊥ : by rw [comap_inf, ←comap_principal]
  ... ↔ _ : by rwa [closure_eq_nhds]

end induced

section embedding

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

lemma embedding.map_nhds_eq [topological_space α] [topological_space β] {f : α → β} (hf : embedding f) (a : α)
  (h : f '' univ ∈ (nhds (f a)).sets) : (nhds a).map f = nhds (f a) :=
by rw [hf.2]; exact map_nhds_induced_eq h

lemma embedding.tendsto_nhds_iff {ι : Type*}
  {f : ι → β} {g : β → γ} {a : filter ι} {b : β} (hg : embedding g) :
  tendsto f a (nhds b) ↔ tendsto (g ∘ f) a (nhds (g b)) :=
by rw [tendsto, tendsto, hg.right, nhds_induced_eq_comap, ← map_le_iff_le_comap, filter.map_map]

lemma embedding.continuous_iff {f : α → β} {g : β → γ} (hg : embedding g) :
  continuous f ↔ continuous (g ∘ f) :=
by simp [continuous_iff_tendsto, embedding.tendsto_nhds_iff hg]

lemma embedding.continuous {f : α → β} (hf : embedding f) : continuous f :=
hf.continuous_iff.mp continuous_id

lemma compact_iff_compact_image_of_embedding {s : set α} {f : α → β} (hf : embedding f) :
  compact s ↔ compact (f '' s) :=
iff.intro (assume h, compact_image h hf.continuous) $ assume h, begin
  rw compact_iff_ultrafilter_le_nhds at ⊢ h,
  intros u hu us',
  let u' : filter β := map f u,
  have : u' ≤ principal (f '' s), begin
    rw [map_le_iff_le_comap, comap_principal], convert us',
    exact preimage_image_eq _ hf.1
  end,
  rcases h u' (ultrafilter_map hu) this with ⟨_, ⟨a, ha, ⟨⟩⟩, _⟩,
  refine ⟨a, ha, _⟩,
  rwa [hf.2, nhds_induced_eq_comap, ←map_le_iff_le_comap]
end

lemma embedding.closure_eq_preimage_closure_image {e : α → β} (he : embedding e) (s : set α) :
  closure s = e ⁻¹' closure (e '' s) :=
by ext x; rw [set.mem_preimage_eq, ← closure_induced he.1, he.2]

end embedding

/-- A function between topological spaces is a quotient map if it is surjective,
  and for all `s : set β`, `s` is open iff its preimage is an open set. -/
def quotient_map [tα : topological_space α] [tβ : topological_space β] (f : α → β) : Prop :=
function.surjective f ∧ tβ = tα.coinduced f

namespace quotient_map
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

protected lemma id : quotient_map (@id α) :=
⟨assume a, ⟨a, rfl⟩, coinduced_id.symm⟩

protected lemma comp {f : α → β} {g : β → γ} (hf : quotient_map f) (hg : quotient_map g) :
  quotient_map (g ∘ f) :=
⟨function.surjective_comp hg.left hf.left, by rw [hg.right, hf.right, coinduced_compose]⟩

protected lemma of_quotient_map_compose {f : α → β} {g : β → γ}
  (hf : continuous f) (hg : continuous g)
  (hgf : quotient_map (g ∘ f)) : quotient_map g :=
⟨assume b, let ⟨a, h⟩ := hgf.left b in ⟨f a, h⟩,
  le_antisymm
    (by rwa ← continuous_iff_le_coinduced)
    (by rw [hgf.right, ← continuous_iff_le_coinduced];
        apply hf.comp continuous_coinduced_rng)⟩

protected lemma continuous_iff {f : α → β} {g : β → γ} (hf : quotient_map f) :
  continuous g ↔ continuous (g ∘ f) :=
by rw [continuous_iff_le_coinduced, continuous_iff_le_coinduced, hf.right, coinduced_compose]

protected lemma continuous {f : α → β} (hf : quotient_map f) : continuous f :=
hf.continuous_iff.mp continuous_id

end quotient_map

section is_open_map
variables [topological_space α] [topological_space β]

def is_open_map (f : α → β) := ∀ U : set α, is_open U → is_open (f '' U)

lemma is_open_map_iff_nhds_le (f : α → β) : is_open_map f ↔ ∀(a:α), nhds (f a) ≤ (nhds a).map f :=
begin
  split,
  { assume h a s hs,
    rcases mem_nhds_sets_iff.1 hs with ⟨t, hts, ht, hat⟩,
    exact filter.mem_sets_of_superset
      (mem_nhds_sets (h t ht) (mem_image_of_mem _ hat))
      (image_subset_iff.2 hts) },
  { refine assume h s hs, is_open_iff_mem_nhds.2 _,
    rintros b ⟨a, ha, rfl⟩,
    exact h _ (filter.image_mem_map $ mem_nhds_sets hs ha) }
end

end is_open_map

namespace is_open_map
variables [topological_space α] [topological_space β] [topological_space γ]
open function

protected lemma id : is_open_map (@id α) := assume s hs, by rwa [image_id]

protected lemma comp
  {f : α → β} {g : β → γ} (hf : is_open_map f) (hg : is_open_map g) : is_open_map (g ∘ f) :=
by intros s hs; rw [image_comp]; exact hg _ (hf _ hs)

lemma of_inverse {f : α → β} {f' : β → α}
  (h : continuous f') (l_inv : left_inverse f f') (r_inv : right_inverse f f') :
  is_open_map f :=
assume s hs,
have f' ⁻¹' s = f '' s, by ext x; simp [mem_image_iff_of_inverse r_inv l_inv],
this ▸ h s hs

lemma to_quotient_map {f : α → β}
  (open_map : is_open_map f) (cont : continuous f) (surj : function.surjective f) :
  quotient_map f :=
⟨ surj,
  begin
    ext s,
    show is_open s ↔ is_open (f ⁻¹' s),
    split,
    { exact cont s },
    { assume h,
      rw ← @image_preimage_eq _ _ _ s surj,
      exact open_map _ h }
  end⟩

end is_open_map

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

lemma continuous_swap : continuous (prod.swap : α × β → β × α) :=
continuous.prod_mk continuous_snd continuous_fst

lemma is_open_prod {s : set α} {t : set β} (hs : is_open s) (ht : is_open t) :
  is_open (set.prod s t) :=
is_open_inter (continuous_fst s hs) (continuous_snd t ht)

lemma nhds_prod_eq {a : α} {b : β} : nhds (a, b) = filter.prod (nhds a) (nhds b) :=
by rw [filter.prod, prod.topological_space, nhds_sup, nhds_induced_eq_comap, nhds_induced_eq_comap]

instance [topological_space α] [discrete_topology α] [topological_space β] [discrete_topology β] :
  discrete_topology (α × β) :=
⟨eq_of_nhds_eq_nhds $ assume ⟨a, b⟩,
  by rw [nhds_prod_eq, nhds_discrete α, nhds_discrete β, nhds_top, filter.prod_pure_pure]⟩

lemma prod_mem_nhds_sets {s : set α} {t : set β} {a : α} {b : β}
  (ha : s ∈ (nhds a).sets) (hb : t ∈ (nhds b).sets) : set.prod s t ∈ (nhds (a, b)).sets :=
by rw [nhds_prod_eq]; exact prod_mem_prod ha hb

lemma nhds_swap (a : α) (b : β) : nhds (a, b) = (nhds (b, a)).map prod.swap :=
by rw [nhds_prod_eq, filter.prod_comm, nhds_prod_eq]; refl

lemma tendsto_prod_mk_nhds {γ} {a : α} {b : β} {f : filter γ} {ma : γ → α} {mb : γ → β}
  (ha : tendsto ma f (nhds a)) (hb : tendsto mb f (nhds b)) :
  tendsto (λc, (ma c, mb c)) f (nhds (a, b)) :=
by rw [nhds_prod_eq]; exact filter.tendsto.prod_mk ha hb

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

lemma mem_closure2 [topological_space α] [topological_space β] [topological_space γ]
  {s : set α} {t : set β} {u : set γ} {f : α → β → γ} {a : α} {b : β}
  (hf : continuous (λp:α×β, f p.1 p.2)) (ha : a ∈ closure s) (hb : b ∈ closure t)
  (hu : ∀a b, a ∈ s → b ∈ t → f a b ∈ u) :
  f a b ∈ closure u :=
have (a, b) ∈ closure (set.prod s t), by rw [closure_prod_eq]; from ⟨ha, hb⟩,
show (λp:α×β, f p.1 p.2) (a, b) ∈ closure u, from
  mem_closure hf this $ assume ⟨a, b⟩ ⟨ha, hb⟩, hu a b ha hb

lemma is_closed_prod [topological_space α] [topological_space β] {s₁ : set α} {s₂ : set β}
  (h₁ : is_closed s₁) (h₂ : is_closed s₂) : is_closed (set.prod s₁ s₂) :=
closure_eq_iff_is_closed.mp $ by simp [h₁, h₂, closure_prod_eq, closure_eq_of_is_closed]

protected lemma is_open_map.prod
  [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]
  {f : α → β} {g : γ → δ}
  (hf : is_open_map f) (hg : is_open_map g) : is_open_map (λ p : α × γ, (f p.1, g p.2)) :=
begin
  rw [is_open_map_iff_nhds_le],
  rintros ⟨a, b⟩,
  rw [nhds_prod_eq, nhds_prod_eq, ← filter.prod_map_map_eq],
  exact filter.prod_mono ((is_open_map_iff_nhds_le f).1 hf a) ((is_open_map_iff_nhds_le g).1 hg b)
end

section tube_lemma

def nhds_contain_boxes (s : set α) (t : set β) : Prop :=
∀ (n : set (α × β)) (hn : is_open n) (hp : set.prod s t ⊆ n),
∃ (u : set α) (v : set β), is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ set.prod u v ⊆ n

lemma nhds_contain_boxes.symm {s : set α} {t : set β} :
  nhds_contain_boxes s t → nhds_contain_boxes t s :=
assume H n hn hp,
  let ⟨u, v, uo, vo, su, tv, p⟩ :=
    H (prod.swap ⁻¹' n)
      (continuous_swap n hn)
      (by rwa [←image_subset_iff, prod.swap, image_swap_prod]) in
  ⟨v, u, vo, uo, tv, su,
    by rwa [←image_subset_iff, prod.swap, image_swap_prod] at p⟩

lemma nhds_contain_boxes.comm {s : set α} {t : set β} :
  nhds_contain_boxes s t ↔ nhds_contain_boxes t s :=
iff.intro nhds_contain_boxes.symm nhds_contain_boxes.symm

lemma nhds_contain_boxes_of_singleton {x : α} {y : β} :
  nhds_contain_boxes ({x} : set α) ({y} : set β) :=
assume n hn hp,
  let ⟨u, v, uo, vo, xu, yv, hp'⟩ :=
    is_open_prod_iff.mp hn x y (hp $ by simp) in
  ⟨u, v, uo, vo, by simpa, by simpa, hp'⟩

lemma nhds_contain_boxes_of_compact {s : set α} (hs : compact s) (t : set β)
  (H : ∀ x ∈ s, nhds_contain_boxes ({x} : set α) t) : nhds_contain_boxes s t :=
assume n hn hp,
have ∀x : subtype s, ∃uv : set α × set β,
     is_open uv.1 ∧ is_open uv.2 ∧ {↑x} ⊆ uv.1 ∧ t ⊆ uv.2 ∧ set.prod uv.1 uv.2 ⊆ n,
  from assume ⟨x, hx⟩,
    have set.prod {x} t ⊆ n, from
      subset.trans (prod_mono (by simpa) (subset.refl _)) hp,
    let ⟨ux,vx,H1⟩ := H x hx n hn this in ⟨⟨ux,vx⟩,H1⟩,
let ⟨uvs, h⟩ := classical.axiom_of_choice this in
have us_cover : s ⊆ ⋃i, (uvs i).1, from
  assume x hx, set.subset_Union _ ⟨x,hx⟩ (by simpa using (h ⟨x,hx⟩).2.2.1),
let ⟨s0, _, s0_fin, s0_cover⟩ :=
  compact_elim_finite_subcover_image hs (λi _, (h i).1) $
    by rw bUnion_univ; exact us_cover in
let u := ⋃(i ∈ s0), (uvs i).1 in
let v := ⋂(i ∈ s0), (uvs i).2 in
have is_open u, from is_open_bUnion (λi _, (h i).1),
have is_open v, from is_open_bInter s0_fin (λi _, (h i).2.1),
have t ⊆ v, from subset_bInter (λi _, (h i).2.2.2.1),
have set.prod u v ⊆ n, from assume ⟨x',y'⟩ ⟨hx',hy'⟩,
  have ∃i ∈ s0, x' ∈ (uvs i).1, by simpa using hx',
  let ⟨i,is0,hi⟩ := this in
  (h i).2.2.2.2 ⟨hi, (bInter_subset_of_mem is0 : v ⊆ (uvs i).2) hy'⟩,
⟨u, v, ‹is_open u›, ‹is_open v›, s0_cover, ‹t ⊆ v›, ‹set.prod u v ⊆ n›⟩

lemma generalized_tube_lemma {s : set α} (hs : compact s) {t : set β} (ht : compact t)
  {n : set (α × β)} (hn : is_open n) (hp : set.prod s t ⊆ n) :
  ∃ (u : set α) (v : set β), is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ set.prod u v ⊆ n :=
have _, from
  nhds_contain_boxes_of_compact hs t $ assume x _, nhds_contain_boxes.symm $
    nhds_contain_boxes_of_compact ht {x} $ assume y _, nhds_contain_boxes_of_singleton,
this n hn hp

end tube_lemma

lemma is_closed_diagonal [topological_space α] [t2_space α] : is_closed {p:α×α | p.1 = p.2} :=
is_closed_iff_nhds.mpr $ assume ⟨a₁, a₂⟩ h, eq_of_nhds_neq_bot $ assume : nhds a₁ ⊓ nhds a₂ = ⊥, h $
  let ⟨t₁, ht₁, t₂, ht₂, (h' : t₁ ∩ t₂ ⊆ ∅)⟩ :=
    by rw [←empty_in_sets_eq_bot, mem_inf_sets] at this; exact this in
  begin
    rw [nhds_prod_eq, ←empty_in_sets_eq_bot],
    apply filter.sets_of_superset,
    apply inter_mem_inf_sets (prod_mem_prod ht₁ ht₂) (mem_principal_sets.mpr (subset.refl _)),
    exact assume ⟨x₁, x₂⟩ ⟨⟨hx₁, hx₂⟩, (heq : x₁ = x₂)⟩,
      show false, from @h' x₁ ⟨hx₁, heq.symm ▸ hx₂⟩
  end

lemma is_closed_eq [topological_space α] [t2_space α] [topological_space β] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : is_closed {x:β | f x = g x} :=
continuous_iff_is_closed.mp (hf.prod_mk hg) _ is_closed_diagonal

lemma diagonal_eq_range_diagonal_map : {p:α×α | p.1 = p.2} = range (λx, (x,x)) :=
ext $ assume p, iff.intro
  (assume h, ⟨p.1, prod.ext_iff.2 ⟨rfl, h⟩⟩)
  (assume ⟨x, hx⟩, show p.1 = p.2, by rw ←hx)

lemma prod_subset_compl_diagonal_iff_disjoint {s t : set α} :
  set.prod s t ⊆ - {p:α×α | p.1 = p.2} ↔ s ∩ t = ∅ :=
by rw [eq_empty_iff_forall_not_mem, subset_compl_comm,
       diagonal_eq_range_diagonal_map, range_subset_iff]; simp

lemma compact_compact_separated [t2_space α] {s t : set α}
  (hs : compact s) (ht : compact t) (hst : s ∩ t = ∅) :
  ∃u v : set α, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ u ∩ v = ∅ :=
by simp only [prod_subset_compl_diagonal_iff_disjoint.symm] at ⊢ hst;
   exact generalized_tube_lemma hs ht is_closed_diagonal hst

lemma closed_of_compact [t2_space α] (s : set α) (hs : compact s) : is_closed s :=
is_open_compl_iff.mpr $ is_open_iff_forall_mem_open.mpr $ assume x hx,
  let ⟨u, v, uo, vo, su, xv, uv⟩ :=
    compact_compact_separated hs (compact_singleton : compact {x})
      (by rwa [inter_comm, ←subset_compl_iff_disjoint, singleton_subset_iff]) in
  have v ⊆ -s, from
    subset_compl_comm.mp (subset.trans su (subset_compl_iff_disjoint.mpr uv)),
⟨v, this, vo, by simpa using xv⟩

lemma locally_compact_of_compact_nhds [topological_space α] [t2_space α]
  (h : ∀ x : α, ∃ s, s ∈ (nhds x).sets ∧ compact s) :
  locally_compact_space α :=
⟨assume x n hn,
  let ⟨u, un, uo, xu⟩ := mem_nhds_sets_iff.mp hn in
  let ⟨k, kx, kc⟩ := h x in
  -- K is compact but not necessarily contained in N.
  -- K \ U is again compact and doesn't contain x, so
  -- we may find open sets V, W separating x from K \ U.
  -- Then K \ W is a compact neighborhood of x contained in U.
  let ⟨v, w, vo, wo, xv, kuw, vw⟩ :=
    compact_compact_separated compact_singleton (compact_diff kc uo)
      (by rw [singleton_inter_eq_empty]; exact λ h, h.2 xu) in
  have wn : -w ∈ (nhds x).sets, from
   mem_nhds_sets_iff.mpr
     ⟨v, subset_compl_iff_disjoint.mpr vw, vo, singleton_subset_iff.mp xv⟩,
  ⟨k - w,
   filter.inter_mem_sets kx wn,
   subset.trans (diff_subset_comm.mp kuw) un,
   compact_diff kc wo⟩⟩

instance locally_compact_of_compact [topological_space α] [t2_space α] [compact_space α] :
  locally_compact_space α :=
locally_compact_of_compact_nhds (assume x, ⟨univ, mem_nhds_sets is_open_univ trivial, compact_univ⟩)

-- We can't make this an instance because it could cause an instance loop.
lemma normal_of_compact_t2 [topological_space α] [compact_space α] [t2_space α] : normal_space α :=
begin
  refine ⟨assume s t hs ht st, _⟩,
  simp only [disjoint_iff],
  exact compact_compact_separated (compact_of_closed hs) (compact_of_closed ht) st.eq_bot
end

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

lemma compact_prod (s : set α) (t : set β) (ha : compact s) (hb : compact t) : compact (set.prod s t) :=
begin
  rw compact_iff_ultrafilter_le_nhds at ha hb ⊢,
  intros f hf hfs,
  rw le_principal_iff at hfs,
  rcases ha (map prod.fst f) (ultrafilter_map hf)
    (le_principal_iff.2 (mem_map_sets_iff.2
      ⟨_, hfs, image_subset_iff.2 (λ s h, h.1)⟩)) with ⟨a, sa, ha⟩,
  rcases hb (map prod.snd f) (ultrafilter_map hf)
    (le_principal_iff.2 (mem_map_sets_iff.2
      ⟨_, hfs, image_subset_iff.2 (λ s h, h.2)⟩)) with ⟨b, tb, hb⟩,
  rw map_le_iff_le_comap at ha hb,
  refine ⟨⟨a, b⟩, ⟨sa, tb⟩, _⟩,
  rw nhds_prod_eq, exact le_inf ha hb
end

instance [compact_space α] [compact_space β] : compact_space (α × β) :=
⟨begin
  have A : compact (set.prod (univ : set α) (univ : set β)) :=
    compact_prod univ univ compact_univ compact_univ,
  have : set.prod (univ : set α) (univ : set β) = (univ : set (α × β)) := by simp,
  rwa this at A,
end⟩

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

lemma embedding_inl : embedding (@sum.inl α β) :=
⟨λ _ _, sum.inl.inj_iff.mp,
  begin
    unfold sum.topological_space,
    apply le_antisymm,
    { intros u hu, existsi (sum.inl '' u),
      change
        (is_open (sum.inl ⁻¹' (@sum.inl α β '' u)) ∧
         is_open (sum.inr ⁻¹' (@sum.inl α β '' u))) ∧
        u = sum.inl ⁻¹' (sum.inl '' u),
      have : sum.inl ⁻¹' (@sum.inl α β '' u) = u :=
        preimage_image_eq u (λ _ _, sum.inl.inj_iff.mp), rw this,
      have : sum.inr ⁻¹' (@sum.inl α β '' u) = ∅ :=
        eq_empty_iff_forall_not_mem.mpr (assume a ⟨b, _, h⟩, sum.inl_ne_inr h), rw this,
      exact ⟨⟨hu, is_open_empty⟩, rfl⟩ },
    { rw induced_le_iff_le_coinduced, exact lattice.inf_le_left }
  end⟩

lemma embedding_inr : embedding (@sum.inr α β) :=
⟨λ _ _, sum.inr.inj_iff.mp,
  begin
    unfold sum.topological_space,
    apply le_antisymm,
    { intros u hu, existsi (sum.inr '' u),
      change
        (is_open (sum.inl ⁻¹' (@sum.inr α β '' u)) ∧
         is_open (sum.inr ⁻¹' (@sum.inr α β '' u))) ∧
        u = sum.inr ⁻¹' (sum.inr '' u),
      have : sum.inl ⁻¹' (@sum.inr α β '' u) = ∅ :=
        eq_empty_iff_forall_not_mem.mpr (assume b ⟨a, _, h⟩, sum.inr_ne_inl h), rw this,
      have : sum.inr ⁻¹' (@sum.inr α β '' u) = u :=
        preimage_image_eq u (λ _ _, sum.inr.inj_iff.mp), rw this,
      exact ⟨⟨is_open_empty, hu⟩, rfl⟩ },
    { rw induced_le_iff_le_coinduced, exact lattice.inf_le_right }
  end⟩

instance [topological_space α] [topological_space β] [compact_space α] [compact_space β] :
  compact_space (α ⊕ β) :=
⟨begin
  have A : compact (@sum.inl α β '' univ) := compact_image compact_univ continuous_inl,
  have B : compact (@sum.inr α β '' univ) := compact_image compact_univ continuous_inr,
  have C := compact_union_of_compact A B,
  have : (@sum.inl α β '' univ) ∪ (@sum.inr α β '' univ) = univ := by ext; cases x; simp,
  rwa this at C,
end⟩

end sum

section subtype
variables [topological_space α] [topological_space β] [topological_space γ] {p : α → Prop}

lemma embedding_graph {f : α → β} (hf : continuous f) : embedding (λx, (x, f x)) :=
embedding_of_embedding_compose (continuous_id.prod_mk hf) continuous_fst embedding_id

lemma embedding_subtype_val : embedding (@subtype.val α p) :=
⟨subtype.val_injective, rfl⟩

lemma continuous_subtype_val : continuous (@subtype.val α p) :=
continuous_induced_dom

lemma continuous_subtype_mk {f : β → α}
  (hp : ∀x, p (f x)) (h : continuous f) : continuous (λx, (⟨f x, hp x⟩ : subtype p)) :=
continuous_induced_rng h

lemma tendsto_subtype_val [topological_space α] {p : α → Prop} {a : subtype p} :
  tendsto subtype.val (nhds a) (nhds a.val) :=
continuous_iff_tendsto.1 continuous_subtype_val _

lemma map_nhds_subtype_val_eq {a : α} (ha : p a) (h : {a | p a} ∈ (nhds a).sets) :
  map (@subtype.val α p) (nhds ⟨a, ha⟩) = nhds a :=
map_nhds_induced_eq (by simp [subtype_val_image, h])

lemma nhds_subtype_eq_comap {a : α} {h : p a} :
  nhds (⟨a, h⟩ : subtype p) = comap subtype.val (nhds a) :=
nhds_induced_eq_comap

lemma tendsto_subtype_rng [topological_space α] {p : α → Prop} {b : filter β} {f : β → subtype p} :
  ∀{a:subtype p}, tendsto f b (nhds a) ↔ tendsto (λx, subtype.val (f x)) b (nhds a.val)
| ⟨a, ha⟩ := by rw [nhds_subtype_eq_comap, tendsto_comap_iff]

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

lemma continuous_subtype_is_closed_cover {ι : Sort*} {f : α → β} (c : ι → α → Prop)
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
    have : ∀ (x : α), f x ∈ s ↔ ∃ (i : ι), c i x ∧ f x ∈ s :=
      λ x, ⟨λ hx, let ⟨i, hi⟩ := h_cover x in ⟨i, hi, hx⟩,
            λ ⟨i, hi, hx⟩, hx⟩,
    simp [and.comm, and.left_comm], simpa [(∘)],
  end,
  by rwa [this]

lemma closure_subtype {x : {a // p a}} {s : set {a // p a}}:
  x ∈ closure s ↔ x.val ∈ closure (subtype.val '' s) :=
closure_induced $ assume x y, subtype.eq

lemma compact_iff_compact_in_subtype {s : set {a // p a}} :
  compact s ↔ compact (subtype.val '' s) :=
compact_iff_compact_image_of_embedding embedding_subtype_val

lemma compact_iff_compact_univ {s : set α} : compact s ↔ compact (univ : set (subtype s)) :=
by rw [compact_iff_compact_in_subtype, image_univ, subtype_val_range]; refl

lemma compact_iff_compact_space {s : set α} : compact s ↔ compact_space s :=
compact_iff_compact_univ.trans ⟨λ h, ⟨h⟩, @compact_space.compact_univ _ _⟩

end subtype

section quotient
variables [topological_space α] [topological_space β] [topological_space γ]
variables {r : α → α → Prop} {s : setoid α}

lemma quotient_map_quot_mk : quotient_map (@quot.mk α r) :=
⟨quot.exists_rep, rfl⟩

lemma continuous_quot_mk : continuous (@quot.mk α r) :=
continuous_coinduced_rng

lemma continuous_quot_lift {f : α → β} (hr : ∀ a b, r a b → f a = f b)
  (h : continuous f) : continuous (quot.lift f hr : quot r → β) :=
continuous_coinduced_dom h

lemma quotient_map_quotient_mk : quotient_map (@quotient.mk α s) :=
quotient_map_quot_mk

lemma continuous_quotient_mk : continuous (@quotient.mk α s) :=
continuous_coinduced_rng

lemma continuous_quotient_lift {f : α → β} (hs : ∀ a b, a ≈ b → f a = f b)
  (h : continuous f) : continuous (quotient.lift f hs : quotient s → β) :=
continuous_coinduced_dom h

instance quot.compact_space {r : α → α → Prop} [topological_space α] [compact_space α] :
  compact_space (quot r) :=
⟨begin
   have : quot.mk r '' univ = univ,
     by rw [image_univ, range_iff_surjective]; exact quot.exists_rep,
   rw ←this,
   exact compact_image compact_univ continuous_quot_mk
 end⟩

instance quotient.compact_space {s : setoid α} [topological_space α] [compact_space α] :
  compact_space (quotient s) :=
quot.compact_space

end quotient

section pi
variables {ι : Type*} {π : ι → Type*}
open topological_space

lemma continuous_pi [topological_space α] [∀i, topological_space (π i)] {f : α → Πi:ι, π i}
  (h : ∀i, continuous (λa, f a i)) : continuous f :=
continuous_supr_rng $ assume i, continuous_induced_rng $ h i

lemma continuous_apply [∀i, topological_space (π i)] (i : ι) :
  continuous (λp:Πi, π i, p i) :=
continuous_supr_dom continuous_induced_dom

lemma nhds_pi [t : ∀i, topological_space (π i)] {a : Πi, π i} :
  nhds a = (⨅i, comap (λx, x i) (nhds (a i))) :=
calc nhds a = (⨅i, @nhds _ (@topological_space.induced _ _ (λx:Πi, π i, x i) (t i)) a) : nhds_supr
  ... = (⨅i, comap (λx, x i) (nhds (a i))) : by simp [nhds_induced_eq_comap]

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
        from mem_sets_of_superset hfs $ assume x (hx : ∀i, x i ∈ s i), hx i,
    let ⟨a, ha⟩ := classical.axiom_of_choice this in
    ⟨a, assume i, (ha i).left, assume i, map_le_iff_le_comap.mp $ (ha i).right⟩
end

lemma is_open_set_pi [∀a, topological_space (π a)] {i : set ι} {s : Πa, set (π a)}
  (hi : finite i) (hs : ∀a∈i, is_open (s a)) : is_open (pi i s) :=
by rw [pi_def]; exact (is_open_bInter hi $ assume a ha, continuous_apply a _ $ hs a ha)

lemma pi_eq_generate_from [∀a, topological_space (π a)] :
  Pi.topological_space =
  generate_from {g | ∃(s:Πa, set (π a)) (i : finset ι), (∀a∈i, is_open (s a)) ∧ g = pi ↑i s} :=
le_antisymm
  (supr_le $ assume a s ⟨t, ht, s_eq⟩, generate_open.basic _ $
    ⟨function.update (λa, univ) a t, {a}, by simpa using ht, by ext f; simp [s_eq, pi]⟩)
  (generate_from_le $ assume g ⟨s, i, hi, eq⟩, eq.symm ▸ is_open_set_pi (finset.finite_to_set _) hi)

lemma pi_generate_from_eq {g : Πa, set (set (π a))} :
  @Pi.topological_space ι π (λa, generate_from (g a)) =
  generate_from {t | ∃(s:Πa, set (π a)) (i : finset ι), (∀a∈i, s a ∈ g a) ∧ t = pi ↑i s} :=
let G := {t | ∃(s:Πa, set (π a)) (i : finset ι), (∀a∈i, s a ∈ g a) ∧ t = pi ↑i s} in
begin
  rw [pi_eq_generate_from],
  refine le_antisymm (generate_from_le _) (generate_from_mono _),
  { rintros s ⟨t, i, hi, rfl⟩,
    rw [pi_def],
    apply is_open_bInter (finset.finite_to_set _),
    assume a ha, show ((generate_from G).coinduced (λf:Πa, π a, f a)).is_open (t a),
    refine generate_from_le _ _ (hi a ha),
    exact assume s hs, generate_open.basic _ ⟨function.update (λa, univ) a s, {a}, by simp [hs]⟩ },
  exact assume s ⟨t, i, ht, eq⟩, ⟨t, i, assume a ha, generate_open.basic _ (ht a ha), eq⟩
end

lemma pi_generate_from_eq_fintype {g : Πa, set (set (π a))} [fintype ι] (hg : ∀a, ⋃₀ g a = univ) :
  @Pi.topological_space ι π (λa, generate_from (g a)) =
  generate_from {t | ∃(s:Πa, set (π a)), (∀a, s a ∈ g a) ∧ t = pi univ s} :=
let G := {t | ∃(s:Πa, set (π a)), (∀a, s a ∈ g a) ∧ t = pi univ s} in
begin
  rw [pi_generate_from_eq],
  refine le_antisymm (generate_from_le _) (generate_from_mono _),
  { rintros s ⟨t, i, ht, rfl⟩,
    apply is_open_iff_forall_mem_open.2 _,
    assume f hf,
    choose c hc using show ∀a, ∃s, s ∈ g a ∧ f a ∈ s,
    { assume a, have : f a ∈ ⋃₀ g a, { rw [hg], apply mem_univ }, simpa },
    refine ⟨pi univ (λa, if a ∈ i then t a else (c : Πa, set (π a)) a), _, _, _⟩,
    { simp [pi_if] },
    { refine generate_open.basic _ ⟨_, assume a, _, rfl⟩,
      by_cases a ∈ i; simp [*, pi] at * },
    { have : f ∈ pi {a | a ∉ i} c, { simp [*, pi] at * },
      simpa [pi_if, hf] } },
  exact assume s ⟨t, ht, eq⟩, ⟨t, finset.univ, by simp [ht, eq]⟩
end

instance second_countable_topology_fintype
  [fintype ι] [t : ∀a, topological_space (π a)] [sc : ∀a, second_countable_topology (π a)] :
  second_countable_topology (∀a, π a) :=
have ∀i, ∃b : set (set (π i)), countable b ∧ ∅ ∉ b ∧ is_topological_basis b, from
  assume a, @is_open_generated_countable_inter (π a) _ (sc a),
let ⟨g, hg⟩ := classical.axiom_of_choice this in
have t = (λa, generate_from (g a)), from funext $ assume a, (hg a).2.2.2.2,
begin
  constructor,
  refine ⟨pi univ '' pi univ g, countable_image _ _, _⟩,
  { suffices : countable {f : Πa, set (π a) | ∀a, f a ∈ g a}, { simpa [pi] },
    exact countable_pi (assume i, (hg i).1), },
  rw [this, pi_generate_from_eq_fintype],
  { congr' 1, ext f, simp [pi, eq_comm] },
  exact assume a, (hg a).2.2.2.1
end

instance pi.compact [∀i:ι, topological_space (π i)] [∀i:ι, compact_space (π i)] : compact_space (Πi, π i) :=
⟨begin
  have A : compact {x : Πi:ι, π i | ∀i, x i ∈ (univ : set (π i))} :=
    compact_pi_infinite (λi, compact_univ),
  have : {x : Πi:ι, π i | ∀i, x i ∈ (univ : set (π i))} = univ := by ext; simp,
  rwa this at A,
end⟩

end pi

namespace list
variables [topological_space α] [topological_space β]

lemma tendsto_cons' {a : α} {l : list α} :
  tendsto (λp:α×list α, list.cons p.1 p.2) ((nhds a).prod (nhds l)) (nhds (a :: l)) :=
by rw [nhds_cons, tendsto, map_prod]; exact le_refl _

lemma tendsto_cons {f : α → β} {g : α → list β}
  {a : _root_.filter α} {b : β} {l : list β} (hf : tendsto f a (nhds b)) (hg : tendsto g a (nhds l)):
  tendsto (λa, list.cons (f a) (g a)) a (nhds (b :: l)) :=
(tendsto.prod_mk hf hg).comp tendsto_cons'

lemma tendsto_cons_iff [topological_space β]
  {f : list α → β} {b : _root_.filter β} {a : α} {l : list α} :
  tendsto f (nhds (a :: l)) b ↔ tendsto (λp:α×list α, f (p.1 :: p.2)) ((nhds a).prod (nhds l)) b :=
have nhds (a :: l) = ((nhds a).prod (nhds l)).map (λp:α×list α, (p.1 :: p.2)),
begin
  simp only [nhds_cons, prod_eq, (filter.map_def _ _).symm, (filter.seq_eq_filter_seq _ _).symm],
  simp [-filter.seq_eq_filter_seq, -filter.map_def, (∘)] with functor_norm,
end,
by rw [this, filter.tendsto_map'_iff]

lemma tendsto_nhds [topological_space β]
  {f : list α → β} {r : list α → _root_.filter β}
  (h_nil : tendsto f (pure []) (r []))
  (h_cons : ∀l a, tendsto f (nhds l) (r l) → tendsto (λp:α×list α, f (p.1 :: p.2)) ((nhds a).prod (nhds l)) (r (a::l))) :
  ∀l, tendsto f (nhds l) (r l)
| []     := by rwa [nhds_nil]
| (a::l) := by rw [tendsto_cons_iff]; exact h_cons l a (tendsto_nhds l)

lemma tendsto_length [topological_space α] :
  ∀(l : list α), tendsto list.length (nhds l) (nhds l.length) :=
begin
  simp only [nhds_discrete],
  refine tendsto_nhds _ _,
  { exact tendsto_pure_pure _ _ },
  { assume l a ih,
    dsimp only [list.length],
    refine tendsto.comp _ (tendsto_pure_pure (λx, x + 1) _),
    refine tendsto.comp tendsto_snd ih }
end

lemma tendsto_insert_nth' {a : α} : ∀{n : ℕ} {l : list α},
  tendsto (λp:α×list α, insert_nth n p.1 p.2) ((nhds a).prod (nhds l)) (nhds (insert_nth n a l))
| 0     l  := tendsto_cons'
| (n+1) [] :=
  suffices tendsto (λa, []) (nhds a) (nhds ([] : list α)),
    by simpa [nhds_nil, tendsto, map_prod, -filter.pure_def, (∘), insert_nth],
  tendsto_const_nhds
| (n+1) (a'::l) :=
  have (nhds a).prod (nhds (a' :: l)) =
    ((nhds a).prod ((nhds a').prod (nhds l))).map (λp:α×α×list α, (p.1, p.2.1 :: p.2.2)),
  begin
    simp only [nhds_cons, prod_eq, (filter.map_def _ _).symm, (filter.seq_eq_filter_seq _ _).symm],
    simp [-filter.seq_eq_filter_seq, -filter.map_def, (∘)] with functor_norm
  end,
  begin
    rw [this, tendsto_map'_iff],
    exact tendsto_cons
      (tendsto_snd.comp tendsto_fst)
      ((tendsto.prod_mk tendsto_fst (tendsto_snd.comp tendsto_snd)).comp (@tendsto_insert_nth' n l))
  end

lemma tendsto_insert_nth {n : ℕ} {a : α} {l : list α} {f : β → α} {g : β → list α}
  {b : _root_.filter β} (hf : tendsto f b (nhds a)) (hg : tendsto g b (nhds l)) :
  tendsto (λb:β, insert_nth n (f b) (g b)) b (nhds (insert_nth n a l)) :=
(tendsto.prod_mk hf hg).comp tendsto_insert_nth'

lemma continuous_insert_nth {n : ℕ} : continuous (λp:α×list α, insert_nth n p.1 p.2) :=
continuous_iff_tendsto.2 $ assume ⟨a, l⟩, by rw [nhds_prod_eq]; exact tendsto_insert_nth'

lemma tendsto_remove_nth : ∀{n : ℕ} {l : list α},
  tendsto (λl, remove_nth l n) (nhds l) (nhds (remove_nth l n))
| _ []      := by rw [nhds_nil]; exact tendsto_pure_nhds _ _
| 0 (a::l) := by rw [tendsto_cons_iff]; exact tendsto_snd
| (n+1) (a::l) :=
  begin
    rw [tendsto_cons_iff],
    dsimp [remove_nth],
    exact tendsto_cons tendsto_fst (tendsto_snd.comp (@tendsto_remove_nth n l))
  end

lemma continuous_remove_nth {n : ℕ} : continuous (λl : list α, remove_nth l n) :=
continuous_iff_tendsto.2 $ assume a, tendsto_remove_nth

end list

namespace vector
open list filter

instance (n : ℕ) [topological_space α] : topological_space (vector α n) :=
by unfold vector; apply_instance

lemma cons_val {n : ℕ} {a : α} : ∀{v : vector α n}, (a :: v).val = a :: v.val
| ⟨l, hl⟩ := rfl

lemma tendsto_cons [topological_space α] {n : ℕ} {a : α} {l : vector α n}:
  tendsto (λp:α×vector α n, vector.cons p.1 p.2) ((nhds a).prod (nhds l)) (nhds (a :: l)) :=
by
  simp [tendsto_subtype_rng, cons_val];
  exact tendsto_cons tendsto_fst (tendsto.comp tendsto_snd tendsto_subtype_val)

lemma tendsto_insert_nth
  [topological_space α] {n : ℕ} {i : fin (n+1)} {a:α} :
  ∀{l:vector α n}, tendsto (λp:α×vector α n, insert_nth p.1 i p.2)
    ((nhds a).prod (nhds l)) (nhds (insert_nth a i l))
| ⟨l, hl⟩ :=
begin
  rw [insert_nth, tendsto_subtype_rng],
  simp [insert_nth_val],
  exact list.tendsto_insert_nth tendsto_fst (tendsto.comp tendsto_snd tendsto_subtype_val)
end

lemma continuous_insert_nth' [topological_space α] {n : ℕ} {i : fin (n+1)} :
  continuous (λp:α×vector α n, insert_nth p.1 i p.2) :=
continuous_iff_tendsto.2 $ assume ⟨a, l⟩, by rw [nhds_prod_eq]; exact tendsto_insert_nth

lemma continuous_insert_nth [topological_space α] [topological_space β] {n : ℕ} {i : fin (n+1)}
  {f : β → α} {g : β → vector α n} (hf : continuous f) (hg : continuous g) :
  continuous (λb, insert_nth (f b) i (g b)) :=
continuous.comp (continuous.prod_mk hf hg) continuous_insert_nth'

lemma tendsto_remove_nth [topological_space α] {n : ℕ} {i : fin (n+1)} :
  ∀{l:vector α (n+1)}, tendsto (remove_nth i) (nhds l) (nhds (remove_nth i l))
| ⟨l, hl⟩ :=
begin
  rw [remove_nth, tendsto_subtype_rng],
  simp [remove_nth_val],
  exact tendsto_subtype_val.comp list.tendsto_remove_nth
end

lemma continuous_remove_nth [topological_space α] {n : ℕ} {i : fin (n+1)} :
  continuous (remove_nth i : vector α (n+1) → vector α n) :=
continuous_iff_tendsto.2 $ assume ⟨a, l⟩, tendsto_remove_nth

end vector

-- TODO: use embeddings from above!
structure dense_embedding [topological_space α] [topological_space β] (e : α → β) : Prop :=
(dense   : ∀x, x ∈ closure (range e))
(inj     : function.injective e)
(induced : ∀a, comap e (nhds (e a)) = nhds a)

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
  (tendsto_iff_comap.1 $ c.tendsto _)⟩

namespace dense_embedding
variables [topological_space α] [topological_space β]
variables {e : α → β} (de : dense_embedding e)

protected lemma embedding (de : dense_embedding e) : embedding e :=
⟨de.inj, eq_of_nhds_eq_nhds begin intro a, rw [← de.induced a, nhds_induced_eq_comap] end⟩

protected lemma tendsto (de : dense_embedding e) {a : α} : tendsto e (nhds a) (nhds (e a)) :=
by rw [←de.induced a]; exact tendsto_comap

protected lemma continuous (de : dense_embedding e) {a : α} : continuous e :=
continuous_iff_tendsto.2 $ λ a, de.tendsto

lemma inj_iff (de : dense_embedding e) {x y} : e x = e y ↔ x = y := de.inj.eq_iff

lemma closure_range : closure (range e) = univ :=
let h := de.dense in
set.ext $ assume x, ⟨assume _, trivial, assume _, @h x⟩

lemma self_sub_closure_image_preimage_of_open {s : set β} (de : dense_embedding e) :
  is_open s → s ⊆ closure (e '' (e ⁻¹' s)) :=
begin
  intros s_op b b_in_s,
  rw [image_preimage_eq_inter_range, mem_closure_iff],
  intros U U_op b_in,
  rw ←inter_assoc,
  have ne_e : U ∩ s ≠ ∅ := ne_empty_of_mem ⟨b_in, b_in_s⟩,
  exact (dense_iff_inter_open.1 de.closure_range) _ (is_open_inter U_op s_op) ne_e
end

lemma closure_image_nhds_of_nhds {s : set α} {a : α} (de : dense_embedding e) :
  s ∈ (nhds a).sets → closure (e '' s) ∈ (nhds (e a)).sets :=
begin
  rw [← de.induced a, mem_comap_sets],
  intro h,
  rcases h with ⟨t, t_nhd, sub⟩,
  rw mem_nhds_sets_iff at t_nhd,
  rcases t_nhd with ⟨U, U_sub, ⟨U_op, e_a_in_U⟩⟩,
  have := calc e ⁻¹' U ⊆ e⁻¹' t : preimage_mono U_sub
                   ... ⊆ s      : sub,
  have := calc U ⊆ closure (e '' (e ⁻¹' U)) : self_sub_closure_image_preimage_of_open de U_op
             ... ⊆ closure (e '' s)         : closure_mono (image_subset e this),
  have U_nhd : U ∈ (nhds (e a)).sets := mem_nhds_sets U_op e_a_in_U,
  exact (nhds (e a)).sets_of_superset U_nhd this
end

variables [topological_space δ] {f : γ → α} {g : γ → δ} {h : δ → β}
/--
 γ -f→ α
g↓     ↓e
 δ -h→ β
-/
lemma tendsto_comap_nhds_nhds  {d : δ} {a : α} (de : dense_embedding e) (H : tendsto h (nhds d) (nhds (e a)))
  (comm : h ∘ g = e ∘ f) : tendsto f (comap g (nhds d)) (nhds a) :=
begin
  have lim1 : map g (comap g (nhds d)) ≤ nhds d := map_comap_le,
  replace lim1 : map h (map g (comap g (nhds d))) ≤ map h (nhds d) := map_mono lim1,
  rw [filter.map_map, comm, ← filter.map_map, map_le_iff_le_comap] at lim1,
  have lim2 :  comap e (map h (nhds d)) ≤  comap e  (nhds (e a)) := comap_mono H,
  rw de.induced at lim2,
  exact le_trans lim1 lim2,
end

protected lemma nhds_inf_neq_bot (de : dense_embedding e) {b : β} : nhds b ⊓ principal (range e) ≠ ⊥ :=
begin
  have h := de.dense,
  simp [closure_eq_nhds] at h,
  exact h _
end

lemma comap_nhds_neq_bot (de : dense_embedding e) {b : β} : comap e (nhds b) ≠ ⊥ :=
forall_sets_neq_empty_iff_neq_bot.mp $
assume s ⟨t, ht, (hs : e ⁻¹' t ⊆ s)⟩,
have t ∩ range e ∈ (nhds b ⊓ principal (range e)).sets,
  from inter_mem_inf_sets ht (subset.refl _),
let ⟨_, ⟨hx₁, y, rfl⟩⟩ := inhabited_of_mem_sets de.nhds_inf_neq_bot this in
subset_ne_empty hs $ ne_empty_of_mem hx₁

variables [topological_space γ]
/-- If `e : α → β` is a dense embedding, then any function `α → γ` extends to a function `β → γ`.
It only extends the parts of `β` which are not mapped by `e`, everything else equal to `f (e a)`.
This allows us to gain equality even if `γ` is not T2. -/
def extend (de : dense_embedding e) (f : α → γ) (b : β) : γ :=
have nonempty γ, from
  let ⟨_, ⟨_, a, _⟩⟩ := exists_mem_of_ne_empty (mem_closure_iff.1 (de.dense b) _ is_open_univ trivial) in
  ⟨f a⟩,
if hb : b ∈ range e
then f (classical.some hb)
else @lim _ (classical.inhabited_of_nonempty this) _ (map f (comap e (nhds b)))

lemma extend_e_eq {f : α → γ} (a : α) : de.extend f (e a) = f a :=
have e a ∈ range e := ⟨a, rfl⟩,
begin
  simp [extend, this],
  congr,
  refine classical.some_spec2 (λx, x = a) _,
  exact assume a h, de.inj h
end

lemma extend_eq [t2_space γ] {b : β} {c : γ} {f : α → γ} (hf : map f (comap e (nhds b)) ≤ nhds c) :
  de.extend f b = c :=
begin
  by_cases hb : b ∈ range e,
  { rcases hb with ⟨a, rfl⟩,
    rw [extend_e_eq],
    have f_a_c : tendsto f (pure a) (nhds c),
    { rw [de.induced] at hf,
      refine le_trans (map_mono _) hf,
      exact pure_le_nhds a },
    have f_a_fa : tendsto f (pure a) (nhds (f a)),
    { rw [tendsto, filter.map_pure], exact pure_le_nhds _  },
    exact tendsto_nhds_unique pure_neq_bot f_a_fa f_a_c },
  { simp [extend, hb],
    exact @lim_eq _ (id _) _ _ _ _ (by simp; exact comap_nhds_neq_bot de) hf }
end

lemma tendsto_extend [regular_space γ] {b : β} {f : α → γ} (de : dense_embedding e)
  (hf : {b | ∃c, tendsto f (comap e $ nhds b) (nhds c)} ∈ (nhds b).sets) :
  tendsto (de.extend f) (nhds b) (nhds (de.extend f b)) :=
let φ := {b | tendsto f (comap e $ nhds b) (nhds $ de.extend f b)} in
have hφ : φ ∈ (nhds b).sets,
  from (nhds b).sets_of_superset hf $ assume b ⟨c, hc⟩,
    show tendsto f (comap e (nhds b)) (nhds (de.extend f b)), from (de.extend_eq hc).symm ▸ hc,
assume s hs,
let ⟨s'', hs''₁, hs''₂, hs''₃⟩ := nhds_is_closed hs in
let ⟨s', hs'₁, (hs'₂ : e ⁻¹' s' ⊆ f ⁻¹' s'')⟩ := mem_of_nhds hφ hs''₁ in
let ⟨t, (ht₁ : t ⊆ φ ∩ s'), ht₂, ht₃⟩ := mem_nhds_sets_iff.mp $ inter_mem_sets hφ hs'₁ in
have h₁ : closure (f '' (e ⁻¹' s')) ⊆ s'',
  by rw [closure_subset_iff_subset_of_is_closed hs''₃, image_subset_iff]; exact hs'₂,
have h₂ : t ⊆ de.extend f ⁻¹' closure (f '' (e ⁻¹' t)), from
  assume b' hb',
  have nhds b' ≤ principal t, by simp; exact mem_nhds_sets ht₂ hb',
  have map f (comap e (nhds b')) ≤ nhds (de.extend f b') ⊓ principal (f '' (e ⁻¹' t)),
    from calc _ ≤ map f (comap e (nhds b' ⊓ principal t)) : map_mono $ comap_mono $ le_inf (le_refl _) this
      ... ≤ map f (comap e (nhds b')) ⊓ map f (comap e (principal t)) :
        le_inf (map_mono $ comap_mono $ inf_le_left) (map_mono $ comap_mono $ inf_le_right)
      ... ≤ map f (comap e (nhds b')) ⊓ principal (f '' (e ⁻¹' t)) : by simp [le_refl]
      ... ≤ _ : inf_le_inf ((ht₁ hb').left) (le_refl _),
  show de.extend f b' ∈ closure (f '' (e ⁻¹' t)),
  begin
    rw [closure_eq_nhds],
    apply neq_bot_of_le_neq_bot _ this,
    simp,
    exact de.comap_nhds_neq_bot
  end,
(nhds b).sets_of_superset
  (show t ∈ (nhds b).sets, from mem_nhds_sets ht₂ ht₃)
  (calc t ⊆ de.extend f ⁻¹' closure (f '' (e ⁻¹' t)) : h₂
    ... ⊆ de.extend f ⁻¹' closure (f '' (e ⁻¹' s')) :
      preimage_mono $ closure_mono $ image_subset f $ preimage_mono $ subset.trans ht₁ $ inter_subset_right _ _
    ... ⊆ de.extend f ⁻¹' s'' : preimage_mono h₁
    ... ⊆ de.extend f ⁻¹' s : preimage_mono hs''₂)

lemma continuous_extend [regular_space γ] {f : α → γ} (de : dense_embedding e)
  (hf : ∀b, ∃c, tendsto f (comap e (nhds b)) (nhds c)) : continuous (de.extend f) :=
continuous_iff_tendsto.mpr $ assume b, de.tendsto_extend $ univ_mem_sets' hf

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
    by rw [nhds_prod_eq, nhds_prod_eq, ←prod_comap_comap_eq, de₁.induced, de₂.induced] }

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
    by simp [subtype_emb, nhds_subtype_eq_comap, comap_comap_comp, (∘), (de.induced x).symm] }

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

/-- α and β are homeomorph, also called topological isomoph -/
structure homeomorph (α : Type*) (β : Type*) [topological_space α] [topological_space β]
  extends α ≃ β :=
(continuous_to_fun  : continuous to_fun)
(continuous_inv_fun : continuous inv_fun)

infix ` ≃ₜ `:50 := homeomorph

namespace homeomorph
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

instance : has_coe_to_fun (α ≃ₜ β) := ⟨λ_, α → β, λe, e.to_equiv⟩

lemma coe_eq_to_equiv (h : α ≃ₜ β) (a : α) : h a = h.to_equiv a := rfl

protected def refl (α : Type*) [topological_space α] : α ≃ₜ α :=
{ continuous_to_fun := continuous_id, continuous_inv_fun := continuous_id, .. equiv.refl α }

protected def trans (h₁ : α ≃ₜ β) (h₂ : β ≃ₜ γ) : α ≃ₜ γ :=
{ continuous_to_fun  := h₁.continuous_to_fun.comp h₂.continuous_to_fun,
  continuous_inv_fun := h₂.continuous_inv_fun.comp h₁.continuous_inv_fun,
  .. equiv.trans h₁.to_equiv h₂.to_equiv }

protected def symm (h : α ≃ₜ β) : β ≃ₜ α :=
{ continuous_to_fun  := h.continuous_inv_fun,
  continuous_inv_fun := h.continuous_to_fun,
  .. h.to_equiv.symm }

protected def continuous (h : α ≃ₜ β) : continuous h := h.continuous_to_fun

lemma symm_comp_self (h : α ≃ₜ β) : ⇑h.symm ∘ ⇑h = id :=
funext $ assume a, h.to_equiv.left_inv a

lemma self_comp_symm (h : α ≃ₜ β) : ⇑h ∘ ⇑h.symm = id :=
funext $ assume a, h.to_equiv.right_inv a

lemma range_coe (h : α ≃ₜ β) : range h = univ :=
eq_univ_of_forall $ assume b, ⟨h.symm b, congr_fun h.self_comp_symm b⟩

lemma image_symm (h : α ≃ₜ β) : image h.symm = preimage h :=
image_eq_preimage_of_inverse h.symm.to_equiv.left_inv h.symm.to_equiv.right_inv

lemma preimage_symm (h : α ≃ₜ β) : preimage h.symm = image h :=
(image_eq_preimage_of_inverse h.to_equiv.left_inv h.to_equiv.right_inv).symm

lemma induced_eq
  {α : Type*} {β : Type*} [tα : topological_space α] [tβ : topological_space β] (h : α ≃ₜ β) :
  tβ.induced h = tα :=
le_antisymm
  (induced_le_iff_le_coinduced.2 h.continuous)
  (calc tα = (tα.induced h.symm).induced h : by rw [induced_compose, symm_comp_self, induced_id]
    ... ≤ tβ.induced h : induced_mono $ (induced_le_iff_le_coinduced.2 h.symm.continuous))

lemma coinduced_eq
  {α : Type*} {β : Type*} [tα : topological_space α] [tβ : topological_space β] (h : α ≃ₜ β) :
  tα.coinduced h = tβ :=
le_antisymm
  (calc tα.coinduced h ≤ (tβ.coinduced h.symm).coinduced h : coinduced_mono h.symm.continuous
    ... = tβ : by rw [coinduced_compose, self_comp_symm, coinduced_id])
  h.continuous

lemma compact_image {s : set α} (h : α ≃ₜ β) : compact (h '' s) ↔ compact s :=
⟨λ hs, by have := compact_image hs h.symm.continuous;
  rwa [← image_comp, symm_comp_self, image_id] at this,
λ hs, compact_image hs h.continuous⟩

lemma compact_preimage {s : set β} (h : α ≃ₜ β) : compact (h ⁻¹' s) ↔ compact s :=
by rw ← image_symm; exact h.symm.compact_image

protected lemma embedding (h : α ≃ₜ β) : embedding h :=
⟨h.to_equiv.bijective.1, h.induced_eq.symm⟩

protected lemma dense_embedding (h : α ≃ₜ β) : dense_embedding h :=
{ dense   := assume a, by rw [h.range_coe, closure_univ]; trivial,
  inj     := h.to_equiv.bijective.1,
  induced := assume a, by rw [← nhds_induced_eq_comap, h.induced_eq] }

protected lemma is_open_map (h : α ≃ₜ β) : is_open_map h :=
begin
  assume s,
  rw ← h.preimage_symm,
  exact h.symm.continuous s
end

protected lemma quotient_map (h : α ≃ₜ β) : quotient_map h :=
⟨h.to_equiv.bijective.2, h.coinduced_eq.symm⟩

def prod_congr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : (α × γ) ≃ₜ (β × δ) :=
{ continuous_to_fun  :=
    continuous.prod_mk (continuous_fst.comp h₁.continuous) (continuous_snd.comp h₂.continuous),
  continuous_inv_fun :=
    continuous.prod_mk (continuous_fst.comp h₁.symm.continuous) (continuous_snd.comp h₂.symm.continuous),
  .. h₁.to_equiv.prod_congr h₂.to_equiv }

section
variables (α β γ)

def prod_comm : (α × β) ≃ₜ (β × α) :=
{ continuous_to_fun  := continuous.prod_mk continuous_snd continuous_fst,
  continuous_inv_fun := continuous.prod_mk continuous_snd continuous_fst,
  .. equiv.prod_comm α β }

def prod_assoc : ((α × β) × γ) ≃ₜ (α × (β × γ)) :=
{ continuous_to_fun  :=
    continuous.prod_mk (continuous_fst.comp continuous_fst)
      (continuous.prod_mk (continuous_fst.comp continuous_snd) continuous_snd),
  continuous_inv_fun := continuous.prod_mk
      (continuous.prod_mk continuous_fst (continuous_snd.comp continuous_fst))
      (continuous_snd.comp continuous_snd),
  .. equiv.prod_assoc α β γ }

end

end homeomorph
