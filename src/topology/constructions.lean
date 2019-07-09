/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot

Constructions of new topological spaces from old ones: product, sum, subtype, quotient, list, vector
-/
import topology.maps topology.subset_properties topology.separation topology.bases
noncomputable theory

open set filter lattice
local attribute [instance] classical.prop_decidable

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section prod
open topological_space
variables [topological_space α] [topological_space β] [topological_space γ]

lemma continuous_fst : continuous (@prod.fst α β) :=
continuous_inf_dom_left continuous_induced_dom

lemma continuous_snd : continuous (@prod.snd α β) :=
continuous_inf_dom_right continuous_induced_dom

lemma continuous.prod_mk {f : γ → α} {g : γ → β}
  (hf : continuous f) (hg : continuous g) : continuous (λx, prod.mk (f x) (g x)) :=
continuous_inf_rng (continuous_induced_rng hf) (continuous_induced_rng hg)

lemma continuous_swap : continuous (prod.swap : α × β → β × α) :=
continuous.prod_mk continuous_snd continuous_fst

lemma is_open_prod {s : set α} {t : set β} (hs : is_open s) (ht : is_open t) :
  is_open (set.prod s t) :=
is_open_inter (continuous_fst s hs) (continuous_snd t ht)

lemma nhds_prod_eq {a : α} {b : β} : nhds (a, b) = filter.prod (nhds a) (nhds b) :=
by rw [filter.prod, prod.topological_space, nhds_inf, nhds_induced, nhds_induced]

instance [topological_space α] [discrete_topology α] [topological_space β] [discrete_topology β] :
  discrete_topology (α × β) :=
⟨eq_of_nhds_eq_nhds $ assume ⟨a, b⟩,
  by rw [nhds_prod_eq, nhds_discrete α, nhds_discrete β, nhds_bot, filter.prod_pure_pure]⟩

lemma prod_mem_nhds_sets {s : set α} {t : set β} {a : α} {b : β}
  (ha : s ∈ nhds a) (hb : t ∈ nhds b) : set.prod s t ∈ nhds (a, b) :=
by rw [nhds_prod_eq]; exact prod_mem_prod ha hb

lemma nhds_swap (a : α) (b : β) : nhds (a, b) = (nhds (b, a)).map prod.swap :=
by rw [nhds_prod_eq, filter.prod_comm, nhds_prod_eq]; refl

lemma tendsto_prod_mk_nhds {γ} {a : α} {b : β} {f : filter γ} {ma : γ → α} {mb : γ → β}
  (ha : tendsto ma f (nhds a)) (hb : tendsto mb f (nhds b)) :
  tendsto (λc, (ma c, mb c)) f (nhds (a, b)) :=
by rw [nhds_prod_eq]; exact filter.tendsto.prod_mk ha hb

lemma continuous_within_at.prod {f : α → β} {g : α → γ} {s : set α} {x : α}
  (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) :
  continuous_within_at (λx, (f x, g x)) s x :=
tendsto_prod_mk_nhds hf hg

lemma continuous_at.prod {f : α → β} {g : α → γ} {x : α}
  (hf : continuous_at f x) (hg : continuous_at g x) : continuous_at (λx, (f x, g x)) x :=
tendsto_prod_mk_nhds hf hg

lemma continuous_on.prod {f : α → β} {g : α → γ} {s : set α}
  (hf : continuous_on f s) (hg : continuous_on g s) : continuous_on (λx, (f x, g x)) s :=
λx hx, continuous_within_at.prod (hf x hx) (hg x hx)

lemma prod_generate_from_generate_from_eq {s : set (set α)} {t : set (set β)}
  (hs : ⋃₀ s = univ) (ht : ⋃₀ t = univ) :
  @prod.topological_space α β (generate_from s) (generate_from t) =
  generate_from {g | ∃u∈s, ∃v∈t, g = set.prod u v} :=
let G := generate_from {g | ∃u∈s, ∃v∈t, g = set.prod u v} in
le_antisymm
  (le_generate_from $ assume g ⟨u, hu, v, hv, g_eq⟩, g_eq.symm ▸
    @is_open_prod _ _ (generate_from s) (generate_from t) _ _
      (generate_open.basic _ hu) (generate_open.basic _ hv))
  (le_inf
    (coinduced_le_iff_le_induced.mp $ le_generate_from $ assume u hu,
      have (⋃v∈t, set.prod u v) = prod.fst ⁻¹' u,
        from calc (⋃v∈t, set.prod u v) = set.prod u univ :
            set.ext $ assume ⟨a, b⟩, by rw ← ht; simp [and.left_comm] {contextual:=tt}
          ... = prod.fst ⁻¹' u : by simp [set.prod, preimage],
      show G.is_open (prod.fst ⁻¹' u),
        from this ▸ @is_open_Union _ _ G _ $ assume v, @is_open_Union _ _ G _ $ assume hv,
          generate_open.basic _ ⟨_, hu, _, hv, rfl⟩)
    (coinduced_le_iff_le_induced.mp $ le_generate_from $ assume v hv,
      have (⋃u∈s, set.prod u v) = prod.snd ⁻¹' v,
        from calc (⋃u∈s, set.prod u v) = set.prod univ v:
            set.ext $ assume ⟨a, b⟩, by rw [←hs]; by_cases b ∈ v; simp [h] {contextual:=tt}
          ... = prod.snd ⁻¹' v : by simp [set.prod, preimage],
      show G.is_open (prod.snd ⁻¹' v),
        from this ▸ @is_open_Union _ _ G _ $ assume u, @is_open_Union _ _ G _ $ assume hu,
          generate_open.basic _ ⟨_, hu, _, hv, rfl⟩))

lemma prod_eq_generate_from [tα : topological_space α] [tβ : topological_space β] :
  prod.topological_space =
  generate_from {g | ∃(s:set α) (t:set β), is_open s ∧ is_open t ∧ g = set.prod s t} :=
le_antisymm
  (le_generate_from $ assume g ⟨s, t, hs, ht, g_eq⟩, g_eq.symm ▸ is_open_prod hs ht)
  (le_inf
    (ball_image_of_ball $ λt ht, generate_open.basic _ ⟨t, univ, by simpa [set.prod_eq] using ht⟩)
    (ball_image_of_ball $ λt ht, generate_open.basic _ ⟨univ, t, by simpa [set.prod_eq] using ht⟩))

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

lemma dense_range_prod [topological_space δ] {f : α → β} {g : γ → δ} (hf : dense_range f)
  (hg : dense_range g) : dense_range (λ p : α × γ, (f p.1, g p.2)) :=
have closure (range $ λ p : α×γ, (f p.1, g p.2)) = set.prod (closure $ range f) (closure $ range g),
    by rw [←closure_prod_eq, prod_range_range_eq],
assume ⟨b, d⟩, this.symm ▸ mem_prod.2 ⟨hf _, hg _⟩

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
    change t₁ ∈ nhds a₁ at ht₁,
    change t₂ ∈ nhds a₂ at ht₂,
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
  (h : ∀ x : α, ∃ s, s ∈ nhds x ∧ compact s) :
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
  have wn : -w ∈ nhds x, from
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
continuous_sup_rng_left continuous_coinduced_rng

lemma continuous_inr : continuous (@sum.inr α β) :=
continuous_sup_rng_right continuous_coinduced_rng

lemma continuous_sum_rec {f : α → γ} {g : β → γ}
  (hf : continuous f) (hg : continuous g) : @continuous (α ⊕ β) γ _ _ (@sum.rec α β (λ_, γ) f g) :=
continuous_sup_dom hf hg

lemma embedding_inl : embedding (@sum.inl α β) :=
{ induced := begin
    unfold sum.topological_space,
    apply le_antisymm,
    { rw ← coinduced_le_iff_le_induced, exact lattice.le_sup_left },
    { intros u hu, existsi (sum.inl '' u),
      change
        (is_open (sum.inl ⁻¹' (@sum.inl α β '' u)) ∧
         is_open (sum.inr ⁻¹' (@sum.inl α β '' u))) ∧
        sum.inl ⁻¹' (sum.inl '' u) = u,
      have : sum.inl ⁻¹' (@sum.inl α β '' u) = u :=
        preimage_image_eq u (λ _ _, sum.inl.inj_iff.mp), rw this,
      have : sum.inr ⁻¹' (@sum.inl α β '' u) = ∅ :=
        eq_empty_iff_forall_not_mem.mpr (assume a ⟨b, _, h⟩, sum.inl_ne_inr h), rw this,
      exact ⟨⟨hu, is_open_empty⟩, rfl⟩ }
  end,
  inj := λ _ _, sum.inl.inj_iff.mp }

lemma embedding_inr : embedding (@sum.inr α β) :=
{ induced := begin
    unfold sum.topological_space,
    apply le_antisymm,
    { rw ← coinduced_le_iff_le_induced, exact lattice.le_sup_right },
    { intros u hu, existsi (sum.inr '' u),
      change
        (is_open (sum.inl ⁻¹' (@sum.inr α β '' u)) ∧
         is_open (sum.inr ⁻¹' (@sum.inr α β '' u))) ∧
        sum.inr ⁻¹' (sum.inr '' u) = u,
      have : sum.inl ⁻¹' (@sum.inr α β '' u) = ∅ :=
        eq_empty_iff_forall_not_mem.mpr (assume b ⟨a, _, h⟩, sum.inr_ne_inl h), rw this,
      have : sum.inr ⁻¹' (@sum.inr α β '' u) = u :=
        preimage_image_eq u (λ _ _, sum.inr.inj_iff.mp), rw this,
      exact ⟨⟨is_open_empty, hu⟩, rfl⟩ }
  end,
  inj := λ _ _, sum.inr.inj_iff.mp }

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
⟨⟨rfl⟩, subtype.val_injective⟩

lemma continuous_subtype_val : continuous (@subtype.val α p) :=
continuous_induced_dom

lemma continuous_subtype_mk {f : β → α}
  (hp : ∀x, p (f x)) (h : continuous f) : continuous (λx, (⟨f x, hp x⟩ : subtype p)) :=
continuous_induced_rng h

lemma continuous_inclusion {s t : set α} (h : s ⊆ t) : continuous (inclusion h) :=
continuous_subtype_mk _ continuous_subtype_val

lemma continuous_at_subtype_val [topological_space α] {p : α → Prop} {a : subtype p} :
  continuous_at subtype.val a :=
continuous_iff_continuous_at.mp continuous_subtype_val _

lemma map_nhds_subtype_val_eq {a : α} (ha : p a) (h : {a | p a} ∈ nhds a) :
  map (@subtype.val α p) (nhds ⟨a, ha⟩) = nhds a :=
map_nhds_induced_eq (by simp [subtype.val_image, h])

lemma nhds_subtype_eq_comap {a : α} {h : p a} :
  nhds (⟨a, h⟩ : subtype p) = comap subtype.val (nhds a) :=
nhds_induced _ _

lemma tendsto_subtype_rng [topological_space α] {p : α → Prop} {b : filter β} {f : β → subtype p} :
  ∀{a:subtype p}, tendsto f b (nhds a) ↔ tendsto (λx, subtype.val (f x)) b (nhds a.val)
| ⟨a, ha⟩ := by rw [nhds_subtype_eq_comap, tendsto_comap_iff]

lemma continuous_subtype_nhds_cover {ι : Sort*} {f : α → β} {c : ι → α → Prop}
  (c_cover : ∀x:α, ∃i, {x | c i x} ∈ nhds x)
  (f_cont  : ∀i, continuous (λ(x : subtype (c i)), f x.val)) :
  continuous f :=
continuous_iff_continuous_at.mpr $ assume x,
  let ⟨i, (c_sets : {x | c i x} ∈ nhds x)⟩ := c_cover x in
  let x' : subtype (c i) := ⟨x, mem_of_nhds c_sets⟩ in
  calc map f (nhds x) = map f (map subtype.val (nhds x')) :
      congr_arg (map f) (map_nhds_subtype_val_eq _ $ c_sets).symm
    ... = map (λx:subtype (c i), f x.val) (nhds x') : rfl
    ... ≤ nhds (f x) : continuous_iff_continuous_at.mp (f_cont i) x'

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
      (by simp [subtype.val_range]; exact h_is_closed i)
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

lemma compact_iff_compact_image_of_embedding {s : set α} {f : α → β} (hf : embedding f) :
  compact s ↔ compact (f '' s) :=
iff.intro (assume h, compact_image h hf.continuous) $ assume h, begin
  rw compact_iff_ultrafilter_le_nhds at ⊢ h,
  intros u hu us',
  let u' : filter β := map f u,
  have : u' ≤ principal (f '' s), begin
    rw [map_le_iff_le_comap, comap_principal], convert us',
    exact preimage_image_eq _ hf.inj
  end,
  rcases h u' (ultrafilter_map hu) this with ⟨_, ⟨a, ha, ⟨⟩⟩, _⟩,
  refine ⟨a, ha, _⟩,
  rwa [hf.induced, nhds_induced, ←map_le_iff_le_comap]
end

lemma compact_iff_compact_in_subtype {s : set {a // p a}} :
  compact s ↔ compact (subtype.val '' s) :=
compact_iff_compact_image_of_embedding embedding_subtype_val

lemma compact_iff_compact_univ {s : set α} : compact s ↔ compact (univ : set (subtype s)) :=
by rw [compact_iff_compact_in_subtype, image_univ, subtype.val_range]; refl

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
continuous_infi_rng $ assume i, continuous_induced_rng $ h i

lemma continuous_apply [∀i, topological_space (π i)] (i : ι) :
  continuous (λp:Πi, π i, p i) :=
continuous_infi_dom continuous_induced_dom

lemma nhds_pi [t : ∀i, topological_space (π i)] {a : Πi, π i} :
  nhds a = (⨅i, comap (λx, x i) (nhds (a i))) :=
calc nhds a = (⨅i, @nhds _ (@topological_space.induced _ _ (λx:Πi, π i, x i) (t i)) a) : nhds_infi
  ... = (⨅i, comap (λx, x i) (nhds (a i))) : by simp [nhds_induced]

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
  (le_generate_from $ assume g ⟨s, i, hi, eq⟩, eq.symm ▸ is_open_set_pi (finset.finite_to_set _) hi)
  (le_infi $ assume a s ⟨t, ht, s_eq⟩, generate_open.basic _ $
    ⟨function.update (λa, univ) a t, {a}, by simpa using ht, by ext f; simp [s_eq.symm, pi]⟩)

lemma pi_generate_from_eq {g : Πa, set (set (π a))} :
  @Pi.topological_space ι π (λa, generate_from (g a)) =
  generate_from {t | ∃(s:Πa, set (π a)) (i : finset ι), (∀a∈i, s a ∈ g a) ∧ t = pi ↑i s} :=
let G := {t | ∃(s:Πa, set (π a)) (i : finset ι), (∀a∈i, s a ∈ g a) ∧ t = pi ↑i s} in
begin
  rw [pi_eq_generate_from],
  refine le_antisymm (generate_from_mono _) (le_generate_from _),
  exact assume s ⟨t, i, ht, eq⟩, ⟨t, i, assume a ha, generate_open.basic _ (ht a ha), eq⟩,
  { rintros s ⟨t, i, hi, rfl⟩,
    rw [pi_def],
    apply is_open_bInter (finset.finite_to_set _),
    assume a ha, show ((generate_from G).coinduced (λf:Πa, π a, f a)).is_open (t a),
    refine le_generate_from _ _ (hi a ha),
    exact assume s hs, generate_open.basic _ ⟨function.update (λa, univ) a s, {a}, by simp [hs]⟩ }
end

lemma pi_generate_from_eq_fintype {g : Πa, set (set (π a))} [fintype ι] (hg : ∀a, ⋃₀ g a = univ) :
  @Pi.topological_space ι π (λa, generate_from (g a)) =
  generate_from {t | ∃(s:Πa, set (π a)), (∀a, s a ∈ g a) ∧ t = pi univ s} :=
let G := {t | ∃(s:Πa, set (π a)), (∀a, s a ∈ g a) ∧ t = pi univ s} in
begin
  rw [pi_generate_from_eq],
  refine le_antisymm (generate_from_mono _) (le_generate_from _),
  exact assume s ⟨t, ht, eq⟩, ⟨t, finset.univ, by simp [ht, eq]⟩,
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
      simpa [pi_if, hf] } }
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

section sigma
variables {ι : Type*} {σ : ι → Type*} [Π i, topological_space (σ i)]
open lattice

lemma continuous_sigma_mk {i : ι} : continuous (@sigma.mk ι σ i) :=
continuous_supr_rng continuous_coinduced_rng

lemma is_open_sigma_iff {s : set (sigma σ)} : is_open s ↔ ∀ i, is_open (sigma.mk i ⁻¹' s) :=
by simp only [is_open_supr_iff, is_open_coinduced]

lemma is_closed_sigma_iff {s : set (sigma σ)} : is_closed s ↔ ∀ i, is_closed (sigma.mk i ⁻¹' s) :=
is_open_sigma_iff

lemma is_open_map_sigma_mk {i : ι} : is_open_map (@sigma.mk ι σ i) :=
begin
  intros s hs,
  rw is_open_sigma_iff,
  intro j,
  classical,
  by_cases h : i = j,
  { subst j,
    convert hs,
    exact set.preimage_image_eq _ injective_sigma_mk },
  { convert is_open_empty,
    apply set.eq_empty_of_subset_empty,
    rintro x ⟨y, _, hy⟩,
    have : i = j, by cc,
    contradiction }
end

lemma is_open_range_sigma_mk {i : ι} : is_open (set.range (@sigma.mk ι σ i)) :=
by { rw ←set.image_univ, exact is_open_map_sigma_mk _ is_open_univ }

lemma is_closed_map_sigma_mk {i : ι} : is_closed_map (@sigma.mk ι σ i) :=
begin
  intros s hs,
  rw is_closed_sigma_iff,
  intro j,
  classical,
  by_cases h : i = j,
  { subst j,
    convert hs,
    exact set.preimage_image_eq _ injective_sigma_mk },
  { convert is_closed_empty,
    apply set.eq_empty_of_subset_empty,
    rintro x ⟨y, _, hy⟩,
    have : i = j, by cc,
    contradiction }
end

lemma is_closed_sigma_mk {i : ι} : is_closed (set.range (@sigma.mk ι σ i)) :=
by { rw ←set.image_univ, exact is_closed_map_sigma_mk _ is_closed_univ }

lemma closed_embedding_sigma_mk {i : ι} : closed_embedding (@sigma.mk ι σ i) :=
closed_embedding_of_continuous_injective_closed
  continuous_sigma_mk injective_sigma_mk is_closed_map_sigma_mk

lemma embedding_sigma_mk {i : ι} : embedding (@sigma.mk ι σ i) :=
closed_embedding_sigma_mk.1

/-- A map out of a sum type is continuous if its restriction to each summand is. -/
lemma continuous_sigma [topological_space β] {f : sigma σ → β}
  (h : ∀ i, continuous (λ a, f ⟨i, a⟩)) : continuous f :=
continuous_supr_dom (λ i, continuous_coinduced_dom (h i))

lemma continuous_sigma_map {κ : Type*} {τ : κ → Type*} [Π k, topological_space (τ k)]
  {f₁ : ι → κ} {f₂ : Π i, σ i → τ (f₁ i)} (hf : ∀ i, continuous (f₂ i)) :
  continuous (sigma.map f₁ f₂) :=
continuous_sigma $ λ i,
  show continuous (λ a, sigma.mk (f₁ i) (f₂ i a)),
  from continuous_sigma_mk.comp (hf i)

/-- The sum of embeddings is an embedding. -/
lemma embedding_sigma_map {τ : ι → Type*} [Π i, topological_space (τ i)]
  {f : Π i, σ i → τ i} (hf : ∀ i, embedding (f i)) : embedding (sigma.map id f) :=
begin
  refine ⟨⟨_⟩, injective_sigma_map function.injective_id (λ i, (hf i).inj)⟩,
  refine le_antisymm
    (continuous_iff_le_induced.mp (continuous_sigma_map (λ i, (hf i).continuous))) _,
  intros s hs,
  replace hs := is_open_sigma_iff.mp hs,
  have : ∀ i, ∃ t, is_open t ∧ f i ⁻¹' t = sigma.mk i ⁻¹' s,
  { intro i,
    apply is_open_induced_iff.mp,
    convert hs i,
    exact (hf i).induced.symm },
  choose t ht using this,
  apply is_open_induced_iff.mpr,
  refine ⟨⋃ i, sigma.mk i '' t i, is_open_Union (λ i, is_open_map_sigma_mk _ (ht i).1), _⟩,
  ext p,
  rcases p with ⟨i, x⟩,
  change (sigma.mk i (f i x) ∈ ⋃ (i : ι), sigma.mk i '' t i) ↔ x ∈ sigma.mk i ⁻¹' s,
  rw [←(ht i).2, mem_Union],
  split,
  { rintro ⟨j, hj⟩,
    rw mem_image at hj,
    rcases hj with ⟨y, hy₁, hy₂⟩,
    rcases sigma.mk.inj_iff.mp hy₂ with ⟨rfl, hy⟩,
    replace hy := eq_of_heq hy,
    subst y,
    exact hy₁ },
  { intro hx,
    use i,
    rw mem_image,
    exact ⟨f i x, hx, rfl⟩ }
end

end sigma

namespace list
variables [topological_space α] [topological_space β]

lemma tendsto_cons' {a : α} {l : list α} :
  tendsto (λp:α×list α, list.cons p.1 p.2) ((nhds a).prod (nhds l)) (nhds (a :: l)) :=
by rw [nhds_cons, tendsto, map_prod]; exact le_refl _

lemma tendsto_cons {f : α → β} {g : α → list β}
  {a : _root_.filter α} {b : β} {l : list β} (hf : tendsto f a (nhds b)) (hg : tendsto g a (nhds l)) :
  tendsto (λa, list.cons (f a) (g a)) a (nhds (b :: l)) :=
tendsto_cons'.comp (tendsto.prod_mk hf hg)

lemma tendsto_cons_iff [topological_space β]
  {f : list α → β} {b : _root_.filter β} {a : α} {l : list α} :
  tendsto f (nhds (a :: l)) b ↔ tendsto (λp:α×list α, f (p.1 :: p.2)) ((nhds a).prod (nhds l)) b :=
have nhds (a :: l) = ((nhds a).prod (nhds l)).map (λp:α×list α, (p.1 :: p.2)),
begin
  simp only
    [nhds_cons, filter.prod_eq, (filter.map_def _ _).symm, (filter.seq_eq_filter_seq _ _).symm],
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

lemma continuous_at_length [topological_space α] :
  ∀(l : list α), continuous_at list.length l :=
begin
  simp only [continuous_at, nhds_discrete],
  refine tendsto_nhds _ _,
  { exact tendsto_pure_pure _ _ },
  { assume l a ih,
    dsimp only [list.length],
    refine tendsto.comp (tendsto_pure_pure (λx, x + 1) _) _,
    refine tendsto.comp ih tendsto_snd }
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
    simp only
      [nhds_cons, filter.prod_eq, (filter.map_def _ _).symm, (filter.seq_eq_filter_seq _ _).symm],
    simp [-filter.seq_eq_filter_seq, -filter.map_def, (∘)] with functor_norm
  end,
  begin
    rw [this, tendsto_map'_iff],
    exact tendsto_cons
      (tendsto_fst.comp tendsto_snd)
      ((@tendsto_insert_nth' n l).comp (tendsto.prod_mk tendsto_fst (tendsto_snd.comp tendsto_snd)))
  end

lemma tendsto_insert_nth {n : ℕ} {a : α} {l : list α} {f : β → α} {g : β → list α}
  {b : _root_.filter β} (hf : tendsto f b (nhds a)) (hg : tendsto g b (nhds l)) :
  tendsto (λb:β, insert_nth n (f b) (g b)) b (nhds (insert_nth n a l)) :=
tendsto_insert_nth'.comp (tendsto.prod_mk hf hg)

lemma continuous_insert_nth {n : ℕ} : continuous (λp:α×list α, insert_nth n p.1 p.2) :=
continuous_iff_continuous_at.mpr $
  assume ⟨a, l⟩, by rw [continuous_at, nhds_prod_eq]; exact tendsto_insert_nth'

lemma tendsto_remove_nth : ∀{n : ℕ} {l : list α},
  tendsto (λl, remove_nth l n) (nhds l) (nhds (remove_nth l n))
| _ []      := by rw [nhds_nil]; exact tendsto_pure_nhds _ _
| 0 (a::l) := by rw [tendsto_cons_iff]; exact tendsto_snd
| (n+1) (a::l) :=
  begin
    rw [tendsto_cons_iff],
    dsimp [remove_nth],
    exact tendsto_cons tendsto_fst ((@tendsto_remove_nth n l).comp tendsto_snd)
  end

lemma continuous_remove_nth {n : ℕ} : continuous (λl : list α, remove_nth l n) :=
continuous_iff_continuous_at.mpr $ assume a, tendsto_remove_nth

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
  exact tendsto_cons tendsto_fst (tendsto.comp continuous_at_subtype_val tendsto_snd)

lemma tendsto_insert_nth
  [topological_space α] {n : ℕ} {i : fin (n+1)} {a:α} :
  ∀{l:vector α n}, tendsto (λp:α×vector α n, insert_nth p.1 i p.2)
    ((nhds a).prod (nhds l)) (nhds (insert_nth a i l))
| ⟨l, hl⟩ :=
begin
  rw [insert_nth, tendsto_subtype_rng],
  simp [insert_nth_val],
  exact list.tendsto_insert_nth tendsto_fst (tendsto.comp continuous_at_subtype_val tendsto_snd : _)
end

lemma continuous_insert_nth' [topological_space α] {n : ℕ} {i : fin (n+1)} :
  continuous (λp:α×vector α n, insert_nth p.1 i p.2) :=
continuous_iff_continuous_at.mpr $ assume ⟨a, l⟩,
  by rw [continuous_at, nhds_prod_eq]; exact tendsto_insert_nth

lemma continuous_insert_nth [topological_space α] [topological_space β] {n : ℕ} {i : fin (n+1)}
  {f : β → α} {g : β → vector α n} (hf : continuous f) (hg : continuous g) :
  continuous (λb, insert_nth (f b) i (g b)) :=
continuous_insert_nth'.comp (continuous.prod_mk hf hg)

lemma continuous_at_remove_nth [topological_space α] {n : ℕ} {i : fin (n+1)} :
  ∀{l:vector α (n+1)}, continuous_at (remove_nth i) l
| ⟨l, hl⟩ :=
--  ∀{l:vector α (n+1)}, tendsto (remove_nth i) (nhds l) (nhds (remove_nth i l))
--| ⟨l, hl⟩ :=
begin
  rw [continuous_at, remove_nth, tendsto_subtype_rng],
  simp [remove_nth_val],
  exact tendsto.comp list.tendsto_remove_nth continuous_at_subtype_val
end

lemma continuous_remove_nth [topological_space α] {n : ℕ} {i : fin (n+1)} :
  continuous (remove_nth i : vector α (n+1) → vector α n) :=
continuous_iff_continuous_at.mpr $ assume ⟨a, l⟩, continuous_at_remove_nth

end vector

namespace dense_inducing
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

/-- The product of two dense inducings is a dense inducing -/
protected def prod {e₁ : α → β} {e₂ : γ → δ} (de₁ : dense_inducing e₁) (de₂ : dense_inducing e₂) :
  dense_inducing (λ(p : α × γ), (e₁ p.1, e₂ p.2)) :=
{ induced := (inducing_prod_mk de₁.to_inducing de₂.to_inducing).induced,
  dense := dense_range_prod de₁.dense de₂.dense }
end dense_inducing

namespace dense_embedding
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

/-- The product of two dense embeddings is a dense embedding -/
protected def prod {e₁ : α → β} {e₂ : γ → δ} (de₁ : dense_embedding e₁) (de₂ : dense_embedding e₂) :
  dense_embedding (λ(p : α × γ), (e₁ p.1, e₂ p.2)) :=
{ inj := assume ⟨x₁, x₂⟩ ⟨y₁, y₂⟩,
    by simp; exact assume h₁ h₂, ⟨de₁.inj h₁, de₂.inj h₂⟩,
  ..dense_inducing.prod de₁.to_dense_inducing de₂.to_dense_inducing }

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
      rw [this, image_comp, subtype.val_image],
      simp,
      assumption
    end,
  inj     := assume ⟨x, hx⟩ ⟨y, hy⟩ h, subtype.eq $ de.inj $ @@congr_arg subtype.val h,
  induced := (induced_iff_nhds_eq _).2 (assume ⟨x, hx⟩,
    by simp [subtype_emb, nhds_subtype_eq_comap, de.to_inducing.nhds_eq_comap, comap_comap_comp, (∘)]) }

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
  from is_closed_property (he.prod he).to_dense_inducing.closure_range hp $ assume a, h _ _,
assume b₁ b₂, this ⟨b₁, b₂⟩

lemma is_closed_property3 [topological_space α] [topological_space β] {e : α → β} {p : β → β → β → Prop}
  (he : dense_embedding e) (hp : is_closed {q:β×β×β | p q.1 q.2.1 q.2.2}) (h : ∀a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) :
  ∀b₁ b₂ b₃, p b₁ b₂ b₃ :=
have ∀q:β×β×β, p q.1 q.2.1 q.2.2,
  from is_closed_property (he.prod $ he.prod he).to_dense_inducing.closure_range hp $
    assume ⟨a₁, a₂, a₃⟩, h _ _ _,
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
{ continuous_to_fun  := h₂.continuous_to_fun.comp h₁.continuous_to_fun,
  continuous_inv_fun := h₁.continuous_inv_fun.comp h₂.continuous_inv_fun,
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
  (calc topological_space.induced ⇑h tβ ≤ _ : induced_mono (coinduced_le_iff_le_induced.1 h.symm.continuous)
  ... ≤ tα : by rw [induced_compose, symm_comp_self, induced_id] ; exact le_refl _)
  (coinduced_le_iff_le_induced.1 h.continuous)

lemma coinduced_eq
  {α : Type*} {β : Type*} [tα : topological_space α] [tβ : topological_space β] (h : α ≃ₜ β) :
  tα.coinduced h = tβ :=
le_antisymm
  h.continuous
  begin
    have : (tβ.coinduced h.symm).coinduced h ≤ tα.coinduced h := coinduced_mono h.symm.continuous,
    rwa [coinduced_compose, self_comp_symm, coinduced_id] at this,
  end

lemma compact_image {s : set α} (h : α ≃ₜ β) : compact (h '' s) ↔ compact s :=
⟨λ hs, by have := compact_image hs h.symm.continuous;
  rwa [← image_comp, symm_comp_self, image_id] at this,
λ hs, compact_image hs h.continuous⟩

lemma compact_preimage {s : set β} (h : α ≃ₜ β) : compact (h ⁻¹' s) ↔ compact s :=
by rw ← image_symm; exact h.symm.compact_image

protected lemma embedding (h : α ≃ₜ β) : embedding h :=
⟨⟨h.induced_eq.symm⟩, h.to_equiv.injective⟩

protected lemma dense_embedding (h : α ≃ₜ β) : dense_embedding h :=
{ dense   := assume a, by rw [h.range_coe, closure_univ]; trivial,
  inj     := h.to_equiv.injective,
  induced := (induced_iff_nhds_eq _).2 (assume a, by rw [← nhds_induced, h.induced_eq]) }

protected lemma is_open_map (h : α ≃ₜ β) : is_open_map h :=
begin
  assume s,
  rw ← h.preimage_symm,
  exact h.symm.continuous s
end

protected lemma quotient_map (h : α ≃ₜ β) : quotient_map h :=
⟨h.to_equiv.surjective, h.coinduced_eq.symm⟩

def prod_congr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : (α × γ) ≃ₜ (β × δ) :=
{ continuous_to_fun  :=
    continuous.prod_mk (h₁.continuous.comp continuous_fst) (h₂.continuous.comp continuous_snd),
  continuous_inv_fun :=
    continuous.prod_mk (h₁.symm.continuous.comp continuous_fst) (h₂.symm.continuous.comp continuous_snd),
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
      (continuous.prod_mk (continuous_snd.comp continuous_fst) continuous_snd),
  continuous_inv_fun := continuous.prod_mk
      (continuous.prod_mk continuous_fst (continuous_fst.comp continuous_snd))
      (continuous_snd.comp continuous_snd),
  .. equiv.prod_assoc α β γ }

end

end homeomorph
