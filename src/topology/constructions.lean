/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import topology.maps

/-!
# Constructions of new topological spaces from old ones

This file constructs products, sums, subtypes and quotients of topological spaces
and sets up their basic theory, such as criteria for maps into or out of these
constructions to be continuous; descriptions of the open sets, neighborhood filters,
and generators of these constructions; and their behavior with respect to embeddings
and other specific classes of maps.

## Implementation note

The constructed topologies are defined using induced and coinduced topologies
along with the complete lattice structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags

product, sum, disjoint union, subspace, quotient space

-/

noncomputable theory

open topological_space set filter lattice
open_locale classical

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

section constructions

instance {p : α → Prop} [t : topological_space α] : topological_space (subtype p) :=
induced subtype.val t

instance {r : α → α → Prop} [t : topological_space α] : topological_space (quot r) :=
coinduced (quot.mk r) t

instance {s : setoid α} [t : topological_space α] : topological_space (quotient s) :=
coinduced quotient.mk t

instance [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α × β) :=
induced prod.fst t₁ ⊓ induced prod.snd t₂

instance [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α ⊕ β) :=
coinduced sum.inl t₁ ⊔ coinduced sum.inr t₂

instance {β : α → Type v} [t₂ : Πa, topological_space (β a)] : topological_space (sigma β) :=
⨆a, coinduced (sigma.mk a) (t₂ a)

instance Pi.topological_space {β : α → Type v} [t₂ : Πa, topological_space (β a)] :
  topological_space (Πa, β a) :=
⨅a, induced (λf, f a) (t₂ a)

lemma quotient_dense_of_dense [setoid α] [topological_space α] {s : set α} (H : ∀ x, x ∈ closure s) :
  closure (quotient.mk '' s) = univ :=
eq_univ_of_forall $ λ x, begin
  rw mem_closure_iff,
  intros U U_op x_in_U,
  let V := quotient.mk ⁻¹' U,
  cases quotient.exists_rep x with y y_x,
  have y_in_V : y ∈ V, by simp only [mem_preimage, y_x, x_in_U],
  have V_op : is_open V := U_op,
  have : V ∩ s ≠ ∅ := mem_closure_iff.1 (H y) V V_op y_in_V,
  rcases exists_mem_of_ne_empty this with ⟨w, w_in_V, w_in_range⟩,
  exact ne_empty_of_mem ⟨w_in_V, mem_image_of_mem quotient.mk w_in_range⟩
end

instance {p : α → Prop} [topological_space α] [discrete_topology α] :
  discrete_topology (subtype p) :=
⟨bot_unique $ assume s hs,
  ⟨subtype.val '' s, is_open_discrete _, (set.preimage_image_eq _ subtype.val_injective)⟩⟩

instance sum.discrete_topology [topological_space α] [topological_space β]
  [hα : discrete_topology α] [hβ : discrete_topology β] : discrete_topology (α ⊕ β) :=
⟨by unfold sum.topological_space; simp [hα.eq_bot, hβ.eq_bot]⟩

instance sigma.discrete_topology {β : α → Type v} [Πa, topological_space (β a)]
  [h : Πa, discrete_topology (β a)] : discrete_topology (sigma β) :=
⟨by { unfold sigma.topological_space, simp [λ a, (h a).eq_bot] }⟩

section topα

variable [topological_space α]

/-
The nhds filter and the subspace topology.
-/

theorem mem_nhds_subtype (s : set α) (a : {x // x ∈ s}) (t : set {x // x ∈ s}) :
  t ∈ nhds a ↔ ∃ u ∈ nhds a.val, (@subtype.val α s) ⁻¹' u ⊆ t :=
by rw mem_nhds_induced

theorem nhds_subtype (s : set α) (a : {x // x ∈ s}) :
  nhds a = comap subtype.val (nhds a.val) :=
by rw nhds_induced

end topα

end constructions


section prod
open topological_space
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

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

instance [discrete_topology α] [discrete_topology β] : discrete_topology (α × β) :=
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

lemma continuous_at.prod {f : α → β} {g : α → γ} {x : α}
  (hf : continuous_at f x) (hg : continuous_at g x) : continuous_at (λx, (f x, g x)) x :=
tendsto_prod_mk_nhds hf hg

lemma prod_generate_from_generate_from_eq {α : Type*} {β : Type*} {s : set (set α)} {t : set (set β)}
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

lemma prod_eq_generate_from :
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

/-- The first projection in a product of topological spaces sends open sets to open sets. -/
lemma is_open_map_fst : is_open_map (@prod.fst α β) :=
begin
  assume s hs,
  rw is_open_iff_forall_mem_open,
  assume x xs,
  rw mem_image_eq at xs,
  rcases xs with ⟨⟨y₁, y₂⟩, ys, yx⟩,
  rcases is_open_prod_iff.1 hs _ _ ys with ⟨o₁, o₂, o₁_open, o₂_open, yo₁, yo₂, ho⟩,
  simp at yx,
  rw yx at yo₁,
  refine ⟨o₁, _, o₁_open, yo₁⟩,
  assume z zs,
  rw mem_image_eq,
  exact ⟨(z, y₂), ho (by simp [zs, yo₂]), rfl⟩
end

/-- The second projection in a product of topological spaces sends open sets to open sets. -/
lemma is_open_map_snd : is_open_map (@prod.snd α β) :=
begin
  /- This lemma could be proved by composing the fact that the first projection is open, and
  exchanging coordinates is a homeomorphism, hence open. As the `prod_comm` homeomorphism is defined
  later, we rather go for the direct proof, copy-pasting the proof for the first projection. -/
  assume s hs,
  rw is_open_iff_forall_mem_open,
  assume x xs,
  rw mem_image_eq at xs,
  rcases xs with ⟨⟨y₁, y₂⟩, ys, yx⟩,
  rcases is_open_prod_iff.1 hs _ _ ys with ⟨o₁, o₂, o₁_open, o₂_open, yo₁, yo₂, ho⟩,
  simp at yx,
  rw yx at yo₂,
  refine ⟨o₂, _, o₂_open, yo₂⟩,
  assume z zs,
  rw mem_image_eq,
  exact ⟨(y₁, z), ho (by simp [zs, yo₁]), rfl⟩
end

/-- A product set is open in a product space if and only if each factor is open, or one of them is
empty -/
lemma is_open_prod_iff' {s : set α} {t : set β} :
  is_open (set.prod s t) ↔ (is_open s ∧ is_open t) ∨ (s = ∅) ∨ (t = ∅) :=
begin
  by_cases h : set.prod s t = ∅,
  { simp [h, prod_eq_empty_iff.1 h] },
  { have st : s ≠ ∅ ∧ t ≠ ∅, by rwa [← ne.def, prod_neq_empty_iff] at h,
    split,
    { assume H : is_open (set.prod s t),
      refine or.inl ⟨_, _⟩,
      show is_open s,
      { rw ← fst_image_prod s st.2,
        exact is_open_map_fst _ H },
      show is_open t,
      { rw ← snd_image_prod st.1 t,
        exact is_open_map_snd _ H } },
    { assume H,
      simp [st] at H,
      exact is_open_prod H.1 H.2 } }
end

lemma closure_prod_eq {s : set α} {t : set β} :
  closure (set.prod s t) = set.prod (closure s) (closure t) :=
set.ext $ assume ⟨a, b⟩,
have filter.prod (nhds a) (nhds b) ⊓ principal (set.prod s t) =
  filter.prod (nhds a ⊓ principal s) (nhds b ⊓ principal t),
  by rw [←prod_inf_prod, prod_principal_principal],
by simp [closure_eq_nhds, nhds_prod_eq, this]; exact prod_neq_bot

lemma mem_closure2 {s : set α} {t : set β} {u : set γ} {f : α → β → γ} {a : α} {b : β}
  (hf : continuous (λp:α×β, f p.1 p.2)) (ha : a ∈ closure s) (hb : b ∈ closure t)
  (hu : ∀a b, a ∈ s → b ∈ t → f a b ∈ u) :
  f a b ∈ closure u :=
have (a, b) ∈ closure (set.prod s t), by rw [closure_prod_eq]; from ⟨ha, hb⟩,
show (λp:α×β, f p.1 p.2) (a, b) ∈ closure u, from
  mem_closure hf this $ assume ⟨a, b⟩ ⟨ha, hb⟩, hu a b ha hb

lemma is_closed_prod {s₁ : set α} {s₂ : set β} (h₁ : is_closed s₁) (h₂ : is_closed s₂) :
  is_closed (set.prod s₁ s₂) :=
closure_eq_iff_is_closed.mp $ by simp [h₁, h₂, closure_prod_eq, closure_eq_of_is_closed]

lemma inducing.prod_mk {f : α → β} {g : γ → δ} (hf : inducing f) (hg : inducing g) :
  inducing (λx:α×γ, (f x.1, g x.2)) :=
⟨by rw [prod.topological_space, prod.topological_space, hf.induced, hg.induced,
         induced_compose, induced_compose, induced_inf, induced_compose, induced_compose]⟩

lemma embedding.prod_mk {f : α → β} {g : γ → δ} (hf : embedding f) (hg : embedding g) :
  embedding (λx:α×γ, (f x.1, g x.2)) :=
{ inj := assume ⟨x₁, x₂⟩ ⟨y₁, y₂⟩, by simp; exact assume h₁ h₂, ⟨hf.inj h₁, hg.inj h₂⟩,
  ..hf.to_inducing.prod_mk hg.to_inducing }

protected lemma is_open_map.prod {f : α → β} {g : γ → δ} (hf : is_open_map f) (hg : is_open_map g) :
  is_open_map (λ p : α × γ, (f p.1, g p.2)) :=
begin
  rw [is_open_map_iff_nhds_le],
  rintros ⟨a, b⟩,
  rw [nhds_prod_eq, nhds_prod_eq, ← filter.prod_map_map_eq],
  exact filter.prod_mono ((is_open_map_iff_nhds_le f).1 hf a) ((is_open_map_iff_nhds_le g).1 hg b)
end

protected lemma open_embedding.prod {f : α → β} {g : γ → δ}
  (hf : open_embedding f) (hg : open_embedding g) : open_embedding (λx:α×γ, (f x.1, g x.2)) :=
open_embedding_of_embedding_open (hf.1.prod_mk hg.1)
  (hf.is_open_map.prod hg.is_open_map)

lemma embedding_graph {f : α → β} (hf : continuous f) : embedding (λx, (x, f x)) :=
embedding_of_embedding_compose (continuous_id.prod_mk hf) continuous_fst embedding_id

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

end sum

section subtype
variables [topological_space α] [topological_space β] [topological_space γ] {p : α → Prop}

lemma embedding_subtype_val : embedding (@subtype.val α p) :=
⟨⟨rfl⟩, subtype.val_injective⟩

lemma continuous_subtype_val : continuous (@subtype.val α p) :=
continuous_induced_dom

lemma subtype_val.open_embedding {s : set α} (hs : is_open s) :
  open_embedding (subtype.val : {x // x ∈ s} → α) :=
{ induced := rfl,
  inj := subtype.val_injective,
  open_range := (subtype.val_range : range subtype.val = s).symm ▸  hs }

lemma subtype_val.closed_embedding {s : set α} (hs : is_closed s) :
  closed_embedding (subtype.val : {x // x ∈ s} → α) :=
{ induced := rfl,
  inj := subtype.val_injective,
  closed_range := (subtype.val_range : range subtype.val = s).symm ▸ hs }

lemma continuous_subtype_mk {f : β → α}
  (hp : ∀x, p (f x)) (h : continuous f) : continuous (λx, (⟨f x, hp x⟩ : subtype p)) :=
continuous_induced_rng h

lemma continuous_inclusion {s t : set α} (h : s ⊆ t) : continuous (inclusion h) :=
continuous_subtype_mk _ continuous_subtype_val

lemma continuous_at_subtype_val {p : α → Prop} {a : subtype p} :
  continuous_at subtype.val a :=
continuous_iff_continuous_at.mp continuous_subtype_val _

lemma map_nhds_subtype_val_eq {a : α} (ha : p a) (h : {a | p a} ∈ nhds a) :
  map (@subtype.val α p) (nhds ⟨a, ha⟩) = nhds a :=
map_nhds_induced_eq (by simp [subtype.val_image, h])

lemma nhds_subtype_eq_comap {a : α} {h : p a} :
  nhds (⟨a, h⟩ : subtype p) = comap subtype.val (nhds a) :=
nhds_induced _ _

lemma tendsto_subtype_rng {β : Type*} {p : α → Prop} {b : filter β} {f : β → subtype p} :
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

lemma open_embedding_sigma_mk {i : ι} : open_embedding (@sigma.mk ι σ i) :=
open_embedding_of_continuous_injective_open
  continuous_sigma_mk injective_sigma_mk is_open_map_sigma_mk

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

lemma is_open_map_sigma [topological_space β] {f : sigma σ → β}
  (h : ∀ i, is_open_map (λ a, f ⟨i, a⟩)) : is_open_map f :=
begin
  intros s hs,
  rw is_open_sigma_iff at hs,
  have : s = ⋃ i, sigma.mk i '' (sigma.mk i ⁻¹' s),
  { rw Union_image_preimage_sigma_mk_eq_self },
  rw this,
  rw [image_Union],
  apply is_open_Union,
  intro i,
  rw [image_image],
  exact h i _ (hs i)
end

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
