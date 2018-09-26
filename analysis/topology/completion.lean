/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Hausdorff completions of uniform spaces.

The goal is to construct a left-adjoint to the inclusion of complete Hausdorff uniform spaces
into all uniform spaces. Any uniform space `α` gets a completion `completion α` and a morphism
(ie. uniformly continuous map) `completion : α → completion α` which solves the universal
mapping problem of factorizing morphisms from `α` to any complete Hausdorff uniform space `β`.
It means any uniformly continuous `f : α → β` gives rise to a unique morphism
`completion.map f : completion α → β` such that `f = completion.extension f ∘ completion α`.
Actually `completion.extension f` is defined for all maps from `α` to `β` but it has the desired
properties only if `f` is uniformly continuous.

Beware that `completion α` is not injective if `α` is not Hausdorff. But its image is always
dense. The adjoint functor acting on morphisms is then constructed by the usual abstract nonsense.
For every uniform spaces `α` and `β`, it turns `f : α → β` into a morphism
  `completion.map f : completion α → completion β`
such that
  `coe ∘ f = (completion.map f) ∘ coe`
provided `f` is uniformly continuous. This construction is compatible with composition.

In this file we introduce the following concepts:

* `separation_setoid α`: to construct the quotient over all elements which are topologically not
  distinguishable.

* `Cauchy α` the uniform completion of the uniform space `α` (using Cauchy filters). These are not
  minimal filters.

* `completion α := quotient (separation_setoid (Cauchy α))` the Hausdorff completion.
  We also lift topological groups (using `uniform_add_group`) to the complete group structure.

This formalization is mostly based on
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
From a slightly different perspective in order to reuse material in analysis.topology.uniform_space.
-/
import data.set.basic data.set.function
import algebra.pi_instances
import analysis.topology.uniform_space analysis.topology.topological_structures

noncomputable theory
local attribute [instance] classical.prop_decidable
open filter set
universes u v w

namespace filter
variables {α : Type u} {β : Type v} {γ : Type w}

@[simp] lemma prod_pure_pure {a : α} {b : β} :
  filter.prod (pure a) (pure b) = pure (a, b) :=
by simp

end filter

/- separation space -/
namespace uniform_space
variables {α : Type u} {β : Type v} {γ : Type w}
variables [uniform_space α] [uniform_space β] [uniform_space γ]

lemma uniform_continuous_of_const {c : α → β} (h : ∀a b, c a = c b) : uniform_continuous c :=
have (λ (x : α × α), (c (x.fst), c (x.snd))) ⁻¹' id_rel = univ, from
  eq_univ_iff_forall.2 $ assume ⟨a, b⟩, h a b,
le_trans (map_le_iff_le_comap.2 $ by simp [comap_principal, this, univ_mem_sets]) refl_le_uniformity

lemma cauchy_prod {f : filter α} {g : filter β} : cauchy f → cauchy g → cauchy (filter.prod f g)
| ⟨f_proper, hf⟩ ⟨g_proper, hg⟩ := ⟨filter.prod_neq_bot.2 ⟨f_proper, g_proper⟩,
  let p_α := λp:(α×β)×(α×β), (p.1.1, p.2.1), p_β := λp:(α×β)×(α×β), (p.1.2, p.2.2) in
  suffices (f.prod f).comap p_α ⊓ (g.prod g).comap p_β ≤ uniformity.comap p_α ⊓ uniformity.comap p_β,
    by simpa [uniformity_prod, filter.prod, filter.comap_inf, filter.comap_comap_comp, (∘),
        lattice.inf_assoc, lattice.inf_comm, lattice.inf_left_comm],
  lattice.inf_le_inf (filter.comap_mono hf) (filter.comap_mono hg)⟩

def separation_setoid (α : Type u) [uniform_space α] : setoid α :=
⟨λx y, (x, y) ∈ separation_rel α, separated_equiv⟩

local attribute [instance] separation_setoid

instance {α : Type u} [u : uniform_space α] : uniform_space (quotient (separation_setoid α)) :=
{ to_topological_space := u.to_topological_space.coinduced (λx, ⟦x⟧),
  uniformity := map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) uniformity,
  refl := le_trans (by simp [quotient.exists_rep]) (filter.map_mono refl_le_uniformity),
  symm := tendsto_map' $
    by simp [prod.swap, (∘)]; exact tendsto_swap_uniformity.comp tendsto_map,
  comp := calc (map (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) uniformity).lift' (λs, comp_rel s s) =
          uniformity.lift' ((λs, comp_rel s s) ∘ image (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧))) :
      map_lift'_eq2 $ monotone_comp_rel monotone_id monotone_id
    ... ≤ uniformity.lift' (image (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) ∘ (λs:set (α×α), comp_rel s (comp_rel s s))) :
      lift'_mono' $ assume s hs ⟨a, b⟩ ⟨c, ⟨⟨a₁, a₂⟩, ha, a_eq⟩, ⟨⟨b₁, b₂⟩, hb, b_eq⟩⟩,
      begin
        simp at a_eq,
        simp at b_eq,
        have h : ⟦a₂⟧ = ⟦b₁⟧, { rw [a_eq.right, b_eq.left] },
        have h : (a₂, b₁) ∈ separation_rel α := quotient.exact h,
        simp [function.comp, set.image, comp_rel, and.comm, and.left_comm, and.assoc],
        exact ⟨a₁, a_eq.left, b₂, b_eq.right, a₂, ha, b₁, h s hs, hb⟩
      end
    ... = map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) (uniformity.lift' (λs:set (α×α), comp_rel s (comp_rel s s))) :
      by rw [map_lift'_eq];
        exact monotone_comp_rel monotone_id (monotone_comp_rel monotone_id monotone_id)
    ... ≤ map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) uniformity :
      map_mono comp_le_uniformity3,
  is_open_uniformity := assume s,
    have ∀a, ⟦a⟧ ∈ s →
        ({p:α×α | p.1 = a → ⟦p.2⟧ ∈ s} ∈ (@uniformity α _).sets ↔
          {p:α×α | p.1 ≈ a → ⟦p.2⟧ ∈ s} ∈ (@uniformity α _).sets),
      from assume a ha,
      ⟨assume h,
        let ⟨t, ht, hts⟩ := comp_mem_uniformity_sets h in
        have hts : ∀{a₁ a₂}, (a, a₁) ∈ t → (a₁, a₂) ∈ t → ⟦a₂⟧ ∈ s,
          from assume a₁ a₂ ha₁ ha₂, @hts (a, a₂) ⟨a₁, ha₁, ha₂⟩ rfl,
        have ht' : ∀{a₁ a₂}, a₁ ≈ a₂ → (a₁, a₂) ∈ t,
          from assume a₁ a₂ h, sInter_subset_of_mem ht h,
        uniformity.sets_of_superset ht $ assume ⟨a₁, a₂⟩ h₁ h₂, hts (ht' $ setoid.symm h₂) h₁,
        assume h, uniformity.sets_of_superset h $ by simp {contextual := tt}⟩,
    begin
      simp [topological_space.coinduced, u.is_open_uniformity, uniformity, forall_quotient_iff],
      exact ⟨λh a ha, (this a ha).mp $ h a ha, λh a ha, (this a ha).mpr $ h a ha⟩
    end }

lemma uniformity_quotient :
  @uniformity (quotient (separation_setoid α)) _ = uniformity.map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) :=
rfl

lemma uniform_continuous_quotient_mk :
  uniform_continuous (quotient.mk : α → quotient (separation_setoid α)) :=
le_refl _

lemma uniform_continuous_quotient {f : quotient (separation_setoid α) → β}
  (hf : uniform_continuous (λx, f ⟦x⟧)) : uniform_continuous f :=
hf

lemma uniform_continuous_quotient_lift
  {f : α → β} {h : ∀a b, (a, b) ∈ separation_rel α → f a = f b}
  (hf : uniform_continuous f) : uniform_continuous (λa, quotient.lift f h a) :=
uniform_continuous_quotient hf

lemma uniform_continuous_quotient_lift₂ [uniform_space γ]
  {f : α → β → γ} {h : ∀a c b d, (a, b) ∈ separation_rel α → (c, d) ∈ separation_rel β → f a c = f b d}
  (hf : uniform_continuous (λp:α×β, f p.1 p.2)) :
  uniform_continuous (λp:_×_, quotient.lift₂ f h p.1 p.2) :=
begin
  rw [uniform_continuous, uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient,
    filter.prod_map_map_eq, filter.tendsto_map'_iff, filter.tendsto_map'_iff],
  rwa [uniform_continuous, uniformity_prod_eq_prod, filter.tendsto_map'_iff] at hf
end

lemma comap_quotient_le_uniformity :
  uniformity.comap (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) ≤ uniformity :=
assume t' ht',
let ⟨t, ht, tt_t'⟩ := comp_mem_uniformity_sets ht' in
let ⟨s, hs, ss_t⟩ := comp_mem_uniformity_sets ht in
⟨(λp:α×α, (⟦p.1⟧, ⟦p.2⟧)) '' s,
  (@uniformity α _).sets_of_superset hs $ assume x hx, ⟨x, hx, rfl⟩,
  assume ⟨a₁, a₂⟩ ⟨⟨b₁, b₂⟩, hb, ab_eq⟩,
  have ⟦b₁⟧ = ⟦a₁⟧ ∧ ⟦b₂⟧ = ⟦a₂⟧, from prod.mk.inj ab_eq,
  have b₁ ≈ a₁ ∧ b₂ ≈ a₂, from and.imp quotient.exact quotient.exact this,
  have ab₁ : (a₁, b₁) ∈ t, from (setoid.symm this.left) t ht,
  have ba₂ : (b₂, a₂) ∈ s, from this.right s hs,
  tt_t' ⟨b₁, show ((a₁, a₂).1, b₁) ∈ t, from ab₁,
    ss_t ⟨b₂, show ((b₁, a₂).1, b₂) ∈ s, from hb, ba₂⟩⟩⟩

lemma comap_quotient_eq_uniformity :
  uniformity.comap (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) = uniformity :=
le_antisymm comap_quotient_le_uniformity le_comap_map

lemma complete_space_separation [h : complete_space α] :
  complete_space (quotient (separation_setoid α)) :=
⟨assume f, assume hf : cauchy f,
  have cauchy (f.comap (λx, ⟦x⟧)), from
    cauchy_comap comap_quotient_le_uniformity hf $
      comap_neq_bot_of_surj hf.left $ assume b, quotient.exists_rep _,
  let ⟨x, (hx : f.comap (λx, ⟦x⟧) ≤ nhds x)⟩ := complete_space.complete this in
  ⟨⟦x⟧, calc f ≤ map (λx, ⟦x⟧) (f.comap (λx, ⟦x⟧)) : le_map_comap $ assume b, quotient.exists_rep _
    ... ≤ map (λx, ⟦x⟧) (nhds x) : map_mono hx
    ... ≤ _ : continuous_iff_tendsto.mp uniform_continuous_quotient_mk.continuous _⟩⟩

lemma separated_separation [h : complete_space α] : separated (quotient (separation_setoid α)) :=
set.ext $ assume ⟨a, b⟩, quotient.induction_on₂ a b $ assume a b,
  ⟨assume h,
    have a ≈ b, from assume s hs,
      have s ∈ (uniformity.comap (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧))).sets,
        from comap_quotient_le_uniformity hs,
      let ⟨t, ht, hts⟩ := this in
      hts begin dsimp, exact h t ht end,
    show ⟦a⟧ = ⟦b⟧, from quotient.sound this,

  assume heq : ⟦a⟧ = ⟦b⟧, assume h hs,
  heq ▸ refl_mem_uniformity hs⟩

lemma separated_of_uniform_continuous {f : α → β} {x y : α}
  (H : uniform_continuous f) (h : x ≈ y) : f x ≈ f y :=
assume _ h', h _ (H h')

lemma eq_of_separated_of_uniform_continuous [separated β] {f : α → β} {x y : α}
  (H : uniform_continuous f) (h : x ≈ y) : f x = f y :=
separated_def.1 (by apply_instance) _ _ $ separated_of_uniform_continuous H h

lemma separation_prod {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) ≈ (a₂, b₂) ↔ a₁ ≈ a₂ ∧ b₁ ≈ b₂ :=
begin
  split,
  { assume h,
    exact ⟨separated_of_uniform_continuous uniform_continuous_fst h,
           separated_of_uniform_continuous uniform_continuous_snd h⟩ },
  { rintros ⟨eqv_α, eqv_β⟩ r r_in,
    rw uniformity_prod at r_in,
    rcases r_in with ⟨t_α, ⟨r_α, r_α_in, h_α⟩, t_β, ⟨r_β, r_β_in, h_β⟩, H⟩,

    let p_α := λ(p : (α × β) × (α × β)), (p.1.1, p.2.1),
    let p_β := λ(p : (α × β) × (α × β)), (p.1.2, p.2.2),
    have key_α : p_α ((a₁, b₁), (a₂, b₂)) ∈ r_α, { simp [p_α, eqv_α r_α r_α_in] },
    have key_β : p_β ((a₁, b₁), (a₂, b₂)) ∈ r_β, { simp [p_β, eqv_β r_β r_β_in] },
    exact H ⟨h_α key_α, h_β key_β⟩ },
end

instance separated.prod [separated α] [separated β] : separated (α × β) :=
separated_def.2 $ assume x y H, prod.ext
  (eq_of_separated_of_uniform_continuous uniform_continuous_fst H)
  (eq_of_separated_of_uniform_continuous uniform_continuous_snd H)

end uniform_space

/-- Space of Cauchy filters

This is essentially the completion of a uniform space. The embeddings are the neighbourhood filters.
This space is not minimal, the separated uniform space (i.e. quotiented on the intersection of all
entourages) is necessary for this.
-/
def Cauchy (α : Type u) [uniform_space α] : Type u := { f : filter α // cauchy f }

namespace Cauchy

section
parameters {α : Type u} [uniform_space α]
variables {β : Type v} {γ : Type w}
variables [uniform_space β] [uniform_space γ]

def gen (s : set (α × α)) : set (Cauchy α × Cauchy α) :=
{p | s ∈ (filter.prod (p.1.val) (p.2.val)).sets }

lemma monotone_gen : monotone gen :=
monotone_set_of $ assume p, @monotone_mem_sets (α×α) (filter.prod (p.1.val) (p.2.val))

private lemma symm_gen : map prod.swap (uniformity.lift' gen) ≤ uniformity.lift' gen :=
calc map prod.swap (uniformity.lift' gen) =
  uniformity.lift' (λs:set (α×α), {p | s ∈ (filter.prod (p.2.val) (p.1.val)).sets }) :
  begin
    delta gen,
    simp [map_lift'_eq, monotone_set_of, monotone_mem_sets,
          function.comp, image_swap_eq_preimage_swap]
  end
  ... ≤ uniformity.lift' gen :
    uniformity_lift_le_swap
      (monotone_comp (monotone_set_of $ assume p,
        @monotone_mem_sets (α×α) ((filter.prod ((p.2).val) ((p.1).val)))) monotone_principal)
      begin
        have h := λ(p:Cauchy α×Cauchy α), @filter.prod_comm _ _ (p.2.val) (p.1.val),
        simp [function.comp, h],
        exact le_refl _
      end

private lemma comp_rel_gen_gen_subset_gen_comp_rel {s t : set (α×α)} : comp_rel (gen s) (gen t) ⊆
  (gen (comp_rel s t) : set (Cauchy α × Cauchy α)) :=
assume ⟨f, g⟩ ⟨h, h₁, h₂⟩,
let ⟨t₁, (ht₁ : t₁ ∈ f.val.sets), t₂, (ht₂ : t₂ ∈ h.val.sets), (h₁ : set.prod t₁ t₂ ⊆ s)⟩ :=
  mem_prod_iff.mp h₁ in
let ⟨t₃, (ht₃ : t₃ ∈ h.val.sets), t₄, (ht₄ : t₄ ∈ g.val.sets), (h₂ : set.prod t₃ t₄ ⊆ t)⟩ :=
  mem_prod_iff.mp h₂ in
have t₂ ∩ t₃ ∈ h.val.sets,
  from inter_mem_sets ht₂ ht₃,
let ⟨x, xt₂, xt₃⟩ :=
  inhabited_of_mem_sets (h.property.left) this in
(filter.prod f.val g.val).sets_of_superset
  (prod_mem_prod ht₁ ht₄)
  (assume ⟨a, b⟩ ⟨(ha : a ∈ t₁), (hb : b ∈ t₄)⟩,
    ⟨x,
      h₁ (show (a, x) ∈ set.prod t₁ t₂, from ⟨ha, xt₂⟩),
      h₂ (show (x, b) ∈ set.prod t₃ t₄, from ⟨xt₃, hb⟩)⟩)

private lemma comp_gen :
  (uniformity.lift' gen).lift' (λs, comp_rel s s) ≤ uniformity.lift' gen :=
calc (uniformity.lift' gen).lift' (λs, comp_rel s s) =
    uniformity.lift' (λs, comp_rel (gen s) (gen s)) :
  begin
    rw [lift'_lift'_assoc],
    exact monotone_gen,
    exact (monotone_comp_rel monotone_id monotone_id)
  end
  ... ≤ uniformity.lift' (λs, gen $ comp_rel s s) :
    lift'_mono' $ assume s hs, comp_rel_gen_gen_subset_gen_comp_rel
  ... = (uniformity.lift' $ λs:set(α×α), comp_rel s s).lift' gen :
  begin
    rw [lift'_lift'_assoc],
    exact (monotone_comp_rel monotone_id monotone_id),
    exact monotone_gen
  end
  ... ≤ uniformity.lift' gen : lift'_mono comp_le_uniformity (le_refl _)

instance : uniform_space (Cauchy α) :=
uniform_space.of_core
{ uniformity  := uniformity.lift' gen,
  refl        := principal_le_lift' $ assume s hs ⟨a, b⟩ (a_eq_b : a = b),
    a_eq_b ▸ a.property.right hs,
  symm        := symm_gen,
  comp        := comp_gen }

theorem mem_uniformity {s : set (Cauchy α × Cauchy α)} :
  s ∈ (@uniformity (Cauchy α) _).sets ↔ ∃ t ∈ (@uniformity α _).sets, gen t ⊆ s :=
mem_lift'_sets monotone_gen

theorem mem_uniformity' {s : set (Cauchy α × Cauchy α)} :
  s ∈ (@uniformity (Cauchy α) _).sets ↔ ∃ t ∈ (@uniformity α _).sets,
    ∀ f g : Cauchy α, t ∈ (filter.prod f.1 g.1).sets → (f, g) ∈ s :=
mem_uniformity.trans $ bex_congr $ λ t h, prod.forall

/-- Embedding of `α` into its completion -/
def pure_cauchy (a : α) : Cauchy α :=
⟨pure a, cauchy_pure⟩

lemma uniform_embedding_pure_cauchy : uniform_embedding (pure_cauchy : α → Cauchy α) :=
⟨assume a₁ a₂ h,
  have (pure_cauchy a₁).val = (pure_cauchy a₂).val, from congr_arg _ h,
  have {a₁} = ({a₂} : set α),
    from principal_eq_iff_eq.mp this,
  by simp at this; assumption,

  have (preimage (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) ∘ gen) = id,
    from funext $ assume s, set.ext $ assume ⟨a₁, a₂⟩,
      by simp [preimage, gen, pure_cauchy, prod_principal_principal],
  calc comap (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) (uniformity.lift' gen)
        = uniformity.lift' (preimage (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) ∘ gen) :
      comap_lift'_eq monotone_gen
    ... = uniformity : by simp [this]⟩

lemma pure_cauchy_dense : ∀x, x ∈ closure (range pure_cauchy) :=
assume f,
have h_ex : ∀s∈(@uniformity (Cauchy α) _).sets, ∃y:α, (f, pure_cauchy y) ∈ s, from
  assume s hs,
  let ⟨t'', ht''₁, (ht''₂ : gen t'' ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs in
  let ⟨t', ht'₁, ht'₂⟩ := comp_mem_uniformity_sets ht''₁ in
  have t' ∈ (filter.prod (f.val) (f.val)).sets,
    from f.property.right ht'₁,
  let ⟨t, ht, (h : set.prod t t ⊆ t')⟩ := mem_prod_same_iff.mp this in
  let ⟨x, (hx : x ∈ t)⟩ := inhabited_of_mem_sets f.property.left ht in
  have t'' ∈ (filter.prod f.val (pure x)).sets,
    from mem_prod_iff.mpr ⟨t, ht, {y:α | (x, y) ∈ t'},
      assume y, begin simp, intro h, simp [h], exact refl_mem_uniformity ht'₁ end,
      assume ⟨a, b⟩ ⟨(h₁ : a ∈ t), (h₂ : (x, b) ∈ t')⟩,
        ht'₂ $ prod_mk_mem_comp_rel (@h (a, x) ⟨h₁, hx⟩) h₂⟩,
  ⟨x, ht''₂ $ by dsimp [gen]; exact this⟩,
begin
  simp [closure_eq_nhds, nhds_eq_uniformity, lift'_inf_principal_eq, set.inter_comm],
  exact (lift'_neq_bot_iff $ monotone_inter monotone_const monotone_preimage).mpr
    (assume s hs,
      let ⟨y, hy⟩ := h_ex s hs in
      have pure_cauchy y ∈ range pure_cauchy ∩ {y : Cauchy α | (f, y) ∈ s},
        from ⟨mem_range_self y, hy⟩,
      ne_empty_of_mem this)
end

lemma dense_embedding_pure_cauchy : dense_embedding pure_cauchy :=
uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense

lemma nonempty_Cauchy_iff : nonempty (Cauchy α) ↔ nonempty α :=
begin
  split ; rintro ⟨c⟩,
  { have := eq_univ_iff_forall.1 dense_embedding_pure_cauchy.closure_range c,
    have := mem_closure_iff.1 this _ is_open_univ trivial,
    rcases exists_mem_of_ne_empty this with ⟨_, ⟨_, a, _⟩⟩,
    exact ⟨a⟩ },
  { exact ⟨pure_cauchy c⟩ }
end

section
set_option eqn_compiler.zeta true
instance : complete_space (Cauchy α) :=
complete_space_extension
  uniform_embedding_pure_cauchy
  pure_cauchy_dense $
  assume f hf,
  let f' : Cauchy α := ⟨f, hf⟩ in
  have map pure_cauchy f ≤ uniformity.lift' (preimage (prod.mk f')),
    from le_lift' $ assume s hs,
    let ⟨t, ht₁, (ht₂ : gen t ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs in
    let ⟨t', ht', (h : set.prod t' t' ⊆ t)⟩ := mem_prod_same_iff.mp (hf.right ht₁) in
    have t' ⊆ { y : α | (f', pure_cauchy y) ∈ gen t },
      from assume x hx, (filter.prod f (pure x)).sets_of_superset (prod_mem_prod ht' $ mem_pure hx) h,
    f.sets_of_superset ht' $ subset.trans this (preimage_mono ht₂),
  ⟨f', by simp [nhds_eq_uniformity]; assumption⟩
end

instance [inhabited α] : inhabited (Cauchy α) :=
⟨pure_cauchy $ default α⟩

instance [h : nonempty α] : nonempty (Cauchy α) :=
h.rec_on $ assume a, nonempty.intro $ Cauchy.pure_cauchy a

section extend
variables [_root_.complete_space β] [separated β]

def extend (f : α → β) : (Cauchy α → β) :=
if uniform_continuous f then
  dense_embedding_pure_cauchy.extend f
else
  λ x, f (classical.inhabited_of_nonempty $ nonempty_Cauchy_iff.1 ⟨x⟩).default

lemma extend_pure_cauchy {f : α → β} (hf : uniform_continuous f) (a : α) :
  extend f (pure_cauchy a) = f a :=
begin
  rw [extend, if_pos hf],
  exact uniformly_extend_of_emb uniform_embedding_pure_cauchy pure_cauchy_dense _
end

lemma uniform_continuous_extend {f : α → β} : uniform_continuous (extend f) :=
begin
  by_cases hf : uniform_continuous f,
  { rw [extend, if_pos hf],
    exact uniform_continuous_uniformly_extend uniform_embedding_pure_cauchy pure_cauchy_dense hf },
  { rw [extend, if_neg hf],
    exact uniform_space.uniform_continuous_of_const (assume a b, by congr) }
end

end extend

end

theorem Cauchy_eq
  {α : Type*} [inhabited α] [uniform_space α] [complete_space α] [separated α] {f g : Cauchy α} :
  lim f.1 = lim g.1 ↔ (f, g) ∈ separation_rel (Cauchy α) :=
begin
  split,
  { intros e s hs,
    rcases Cauchy.mem_uniformity'.1 hs with ⟨t, tu, ts⟩,
    apply ts,
    rcases comp_mem_uniformity_sets tu with ⟨d, du, dt⟩,
    refine mem_prod_iff.2
      ⟨_, le_nhds_lim_of_cauchy f.2 (mem_nhds_right (lim f.1) du),
       _, le_nhds_lim_of_cauchy g.2 (mem_nhds_left (lim g.1) du), λ x h, _⟩,
    cases x with a b, cases h with h₁ h₂,
    rw ← e at h₂,
    exact dt ⟨_, h₁, h₂⟩ },
  { intros H,
    refine separated_def.1 (by apply_instance) _ _ (λ t tu, _),
    rcases mem_uniformity_is_closed tu with ⟨d, du, dc, dt⟩,
    refine H {p | (lim p.1.1, lim p.2.1) ∈ t}
      (Cauchy.mem_uniformity'.2 ⟨d, du, λ f g h, _⟩),
    rcases mem_prod_iff.1 h with ⟨x, xf, y, yg, h⟩,
    have limc : ∀ (f : Cauchy α) (x ∈ f.1.sets), lim f.1 ∈ closure x,
    { intros f x xf,
      rw closure_eq_nhds,
      exact lattice.neq_bot_of_le_neq_bot f.2.1
        (lattice.le_inf (le_nhds_lim_of_cauchy f.2) (le_principal_iff.2 xf)) },
    have := (closure_subset_iff_subset_of_is_closed dc).2 h,
    rw closure_prod_eq at this,
    refine dt (this ⟨_, _⟩); dsimp; apply limc; assumption }
end

section
local attribute [instance] uniform_space.separation_setoid

lemma injective_separated_pure_cauchy {α : Type*} [uniform_space α] [s : separated α] :
  function.injective (λa:α, ⟦pure_cauchy a⟧) | a b h :=
separated_def.1 s _ _ $ assume s hs,
let ⟨t, ht, hts⟩ :=
  by rw [← (@uniform_embedding_pure_cauchy α _).right, filter.mem_comap_sets] at hs; exact hs in
have (pure_cauchy a, pure_cauchy b) ∈ t, from quotient.exact h t ht,
@hts (a, b) this

end

section prod
variables {α : Type*} {β : Type*} [uniform_space α] [uniform_space β]

def prod : Cauchy α × Cauchy β → Cauchy (α × β) :=
dense_embedding.extend (dense_embedding_pure_cauchy.prod dense_embedding_pure_cauchy) pure_cauchy

lemma prod_pure_cauchy_pure_cauchy (a : α) (b :β) :
  prod (pure_cauchy a, pure_cauchy b) = pure_cauchy (a, b) :=
uniformly_extend_of_emb
  (uniform_embedding_pure_cauchy.prod uniform_embedding_pure_cauchy)
  (dense_embedding_pure_cauchy.prod dense_embedding_pure_cauchy).dense
  (a, b)

lemma uniform_continuous_prod : uniform_continuous (@prod α β _ _) :=
uniform_continuous_uniformly_extend
  (uniform_embedding_pure_cauchy.prod uniform_embedding_pure_cauchy)
  (dense_embedding_pure_cauchy.prod dense_embedding_pure_cauchy).dense
  uniform_embedding_pure_cauchy.uniform_continuous

end prod

end Cauchy

local attribute [instance] uniform_space.separation_setoid

open Cauchy set

namespace uniform_space
variables (α : Type*) [uniform_space α]
variables {β : Type*} [uniform_space β]
variables {γ : Type*} [uniform_space γ]

/-- Hausdorff completion of `α` -/
def completion := quotient (separation_setoid $ Cauchy α)

namespace completion

@[priority 50]
instance : uniform_space (completion α) := by dunfold completion ; apply_instance

instance : complete_space (completion α) := complete_space_separation

instance : separated (completion α) := separated_separation

instance : t2_space (completion α) := separated_t2

instance : regular_space (completion α) := separated_regular

/-- Automatic coercion from `α` to its completion. Not always injective. -/
instance : has_coe α (completion α) := ⟨quotient.mk ∘ pure_cauchy⟩

protected lemma coe_eq : (coe : α → completion α) = quotient.mk ∘ pure_cauchy := rfl

lemma uniform_continuous_coe : uniform_continuous (coe : α → completion α) :=
uniform_continuous.comp uniform_embedding_pure_cauchy.uniform_continuous
  uniform_continuous_quotient_mk

lemma continuous_coe : continuous (coe : α → completion α) :=
uniform_continuous.continuous (uniform_continuous_coe α)

lemma comap_coe_eq_uniformity :
  uniformity.comap (λ(p:α×α), ((p.1 : completion α), (p.2 : completion α))) = uniformity :=
begin
  have : (λx:α×α, ((x.1 : completion α), (x.2 : completion α))) =
    (λx:(Cauchy α)×(Cauchy α), (⟦x.1⟧, ⟦x.2⟧)) ∘ (λx:α×α, (pure_cauchy x.1, pure_cauchy x.2)),
  { ext ⟨a, b⟩; simp; refl },
  rw [this, ← filter.comap_comap_comp, comap_quotient_eq_uniformity, uniform_embedding_pure_cauchy.2]
end

lemma uniform_embedding_coe [separated α] : uniform_embedding  (coe : α → completion α) :=
⟨injective_separated_pure_cauchy, comap_coe_eq_uniformity α⟩

variable {α}

lemma dense : closure (range (coe : α → completion α)) = univ   :=
by rw [completion.coe_eq, range_comp]; exact quotient_dense_of_dense pure_cauchy_dense

lemma dense₂ : closure (range (λx:α × β, ((x.1 : completion α), (x.2 : completion β)))) = univ :=
by rw [← set.prod_range_range_eq, closure_prod_eq, dense, dense, univ_prod_univ]

lemma dense₃ :
  closure (range (λx:α × (β × γ), ((x.1 : completion α), ((x.2.1 : completion β), (x.2.2 : completion γ))))) = univ :=
let a : α → completion α := coe, bc := λp:β × γ, ((p.1 : completion β), (p.2 : completion γ)) in
show closure (range (λx:α × (β × γ), (a x.1, bc x.2))) = univ,
begin
  rw [← set.prod_range_range_eq, @closure_prod_eq _ _ _ _ (range a) (range bc), ← univ_prod_univ],
  congr,
  exact dense,
  exact dense₂
end

@[elab_as_eliminator]
lemma induction_on {p : completion α → Prop}
  (a : completion α) (hp : is_closed {a | p a}) (ih : ∀a:α, p a) : p a :=
is_closed_property dense hp ih a

@[elab_as_eliminator]
lemma induction_on₂ {p : completion α → completion β → Prop}
  (a : completion α) (b : completion β)
  (hp : is_closed {x : completion α × completion β | p x.1 x.2})
  (ih : ∀(a:α) (b:β), p a b) : p a b :=
have ∀x : completion α × completion β, p x.1 x.2, from
  is_closed_property dense₂ hp $ assume ⟨a, b⟩, ih a b,
this (a, b)

@[elab_as_eliminator]
lemma induction_on₃ {p : completion α → completion β → completion γ → Prop}
  (a : completion α) (b : completion β) (c : completion γ)
  (hp : is_closed {x : completion α × completion β × completion γ | p x.1 x.2.1 x.2.2})
  (ih : ∀(a:α) (b:β) (c:γ), p a b c) : p a b c :=
have ∀x : completion α × completion β × completion γ, p x.1 x.2.1 x.2.2, from
  is_closed_property dense₃ hp $ assume ⟨a, b, c⟩, ih a b c,
this (a, b, c)

@[elab_as_eliminator]
lemma induction_on₄ {δ : Type*} [uniform_space δ]
  {p : completion α → completion β → completion γ → completion δ → Prop}
  (a : completion α) (b : completion β) (c : completion γ) (d : completion δ)
  (hp : is_closed {x : (completion α × completion β) × (completion γ × completion δ) | p x.1.1 x.1.2 x.2.1 x.2.2})
  (ih : ∀(a:α) (b:β) (c:γ) (d : δ), p ↑a ↑b ↑c ↑d) : p a b c d :=
let
  ab := λp:α × β, ((p.1 : completion α), (p.2 : completion β)),
  cd := λp:γ × δ, ((p.1 : completion γ), (p.2 : completion δ))
in
have dense₄ : closure (range (λx:(α × β) × (γ × δ), (ab x.1, cd x.2))) = univ,
begin
  rw [← set.prod_range_range_eq, @closure_prod_eq _ _ _ _ (range ab) (range cd), ← univ_prod_univ],
  congr,
  exact dense₂,
  exact dense₂
end,
have ∀x:(completion α × completion β) × (completion γ × completion δ), p x.1.1 x.1.2 x.2.1 x.2.2, from
  is_closed_property dense₄ hp (assume p:(α×β)×(γ×δ), ih p.1.1 p.1.2 p.2.1 p.2.2),
this ((a, b), (c, d))

section extension
variables {f : α → β}
variables [complete_space β] [separated β]

/-- "Extension" to the completion. Based on `Cauchy.extend`, which is defined for any map `f` but
returns an arbitrary constant value if `f` is not uniformly continuous -/
protected def extension (f : α → β) : completion α → β :=
quotient.lift (extend f) $ assume a b,
  eq_of_separated_of_uniform_continuous uniform_continuous_extend

lemma uniform_continuous_extension : uniform_continuous (completion.extension f) :=
uniform_continuous_quotient_lift uniform_continuous_extend

lemma continuous_extension : continuous (completion.extension f) :=
uniform_continuous_extension.continuous

@[simp] lemma extension_coe (hf : uniform_continuous f) (a : α) : (completion.extension f) a = f a :=
extend_pure_cauchy hf a

end extension

section map
variables {f : α → β}

/-- Completion functor acting on morphisms -/
protected def map (f : α → γ) : completion α → completion γ :=
completion.extension (coe ∘ f)

lemma uniform_continuous_map : uniform_continuous (completion.map f) :=
uniform_continuous_quotient_lift uniform_continuous_extend

lemma continuous_map : continuous (completion.map f) :=
uniform_continuous_extension.continuous

@[simp] lemma map_coe (hf : uniform_continuous f) (a : α) : (completion.map f) a = f a :=
begin
  rw [completion.map, extension_coe],
  exact hf.comp (uniform_continuous_coe β)
end

end map

section prod
variables [uniform_space β]
protected def prod {α β} [uniform_space α] [uniform_space β] (p : completion α × completion β) : completion (α × β) :=
quotient.lift_on₂ p.1 p.2 (λa b, ⟦Cauchy.prod (a, b)⟧) $ assume a b c d hab hcd,
  quotient.sound $ separated_of_uniform_continuous uniform_continuous_prod $
  separation_prod.2 ⟨hab, hcd⟩

lemma uniform_continuous_prod : uniform_continuous (@completion.prod α β _ _) :=
uniform_continuous_quotient_lift₂ $
  suffices uniform_continuous (quotient.mk ∘ Cauchy.prod),
  { convert this, ext ⟨a, b⟩, refl },
  Cauchy.uniform_continuous_prod.comp uniform_continuous_quotient_mk

lemma prod_coe_coe (a : α) (b : β) :
  completion.prod ((a : completion α), (b : completion β)) = (a, b) :=
congr_arg quotient.mk $ Cauchy.prod_pure_cauchy_pure_cauchy a b

end prod

section map₂

protected def map₂ (f : α → β → γ) (a : completion α) (b : completion β) : completion γ :=
completion.map (λp:α×β, f p.1 p.2) (completion.prod (a, b))

lemma uniform_continuous_map₂' (f : α → β → γ) :
  uniform_continuous (λp:completion α×completion β, completion.map₂ f p.1 p.2) :=
uniform_continuous.comp uniform_continuous_prod completion.uniform_continuous_map

lemma continuous_map₂ {δ} [topological_space δ] {f : α → β → γ}
  {a : δ → completion α} {b : δ → completion β} (ha : continuous a) (hb : continuous b) :
  continuous (λd:δ, completion.map₂ f (a d) (b d)) :=
(continuous.prod_mk ha hb).comp (uniform_continuous_map₂' f).continuous

lemma map₂_coe_coe (a : α) (b : β) (f : α → β → γ) (hf : uniform_continuous (λp:α×β, f p.1 p.2)) :
  completion.map₂ f (a : completion α) (b : completion β) = f a b :=
by rw [completion.map₂, completion.prod_coe_coe, completion.map_coe hf]

end map₂

section group

instance [has_zero α] : has_zero (completion α) := ⟨(0 : α)⟩
instance [has_neg α] : has_neg (completion α) := ⟨completion.map (λa, -a : α → α)⟩
instance [has_add α] : has_add (completion α) := ⟨completion.map₂ (+)⟩

lemma coe_zero [has_zero α] : ((0 : α) : completion α) = 0 := rfl

section uniform_add_group
variables [add_group α] [uniform_add_group α]

lemma coe_neg (a : α) : ((- a : α) : completion α) = - a :=
(map_coe uniform_continuous_neg' a).symm

lemma coe_add (a b : α) : ((a + b : α) : completion α) = a + b :=
(map₂_coe_coe a b (+) uniform_continuous_add').symm

instance : add_group (completion α) :=
{ zero_add     := assume a, completion.induction_on a
    (is_closed_eq (continuous_map₂ continuous_const continuous_id) continuous_id)
    (assume a, show 0 + (a : completion α) = a, by rw [← coe_zero, ← coe_add, zero_add]),
  add_zero     := assume a, completion.induction_on a
    (is_closed_eq (continuous_map₂ continuous_id continuous_const) continuous_id)
    (assume a, show (a : completion α) + 0 = a, by rw [← coe_zero, ← coe_add, add_zero]),
  add_left_neg := assume a, completion.induction_on a
    (is_closed_eq (continuous_map₂ completion.continuous_map continuous_id) continuous_const)
    (assume a, show - (a : completion α) + a = 0, by rw [← coe_neg, ← coe_add, add_left_neg, coe_zero]),
  add_assoc    := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_map₂
        (continuous_map₂ continuous_fst (continuous_snd.comp continuous_fst)) (continuous_snd.comp continuous_snd))
      (continuous_map₂ continuous_fst
        (continuous_map₂ (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd))))
    (assume a b c, show (a : completion α) + b + c = a + (b + c),
      by repeat { rw [← coe_add] }; rw [add_assoc]),
  .. completion.has_zero, .. completion.has_neg, ..completion.has_add }

instance : uniform_add_group (completion α) :=
⟨ (uniform_continuous.prod_mk uniform_continuous_fst
  (uniform_continuous_snd.comp uniform_continuous_map)).comp (uniform_continuous_map₂' (+))  ⟩

instance is_add_group_hom_coe : is_add_group_hom (coe : α → completion α) :=
⟨ coe_add ⟩

lemma is_add_group_hom_extension [add_group β] [uniform_add_group β] [complete_space β] [separated β]
  {f : α → β} [is_add_group_hom f] (hf : continuous f) : is_add_group_hom (completion.extension f) :=
have hf : uniform_continuous f, from uniform_continuous_of_continuous hf,
⟨assume a b, completion.induction_on₂ a b
  (is_closed_eq
    (continuous_add'.comp continuous_extension)
    (continuous_add (continuous_fst.comp continuous_extension) (continuous_snd.comp continuous_extension)))
  (assume a b, by rw [← coe_add, extension_coe hf, extension_coe hf, extension_coe hf, is_add_group_hom.add f])⟩

lemma is_add_group_hom_map [add_group β] [uniform_add_group β]
  {f : α → β} [is_add_group_hom f] (hf : continuous f) : is_add_group_hom (completion.map f) :=
is_add_group_hom_extension (hf.comp (continuous_coe _))

section instance_max_depth
-- TODO: continuous_add requires some long proofs through
-- uniform_add_group / topological_add_group w.r.t prod / completion etc
set_option class.instance_max_depth 52
-- set_option trace.class_instances true

lemma is_add_group_hom_prod [add_group β] [uniform_add_group β] :
  is_add_group_hom (@completion.prod α β _ _) :=
⟨assume ⟨a₁, a₂⟩ ⟨b₁, b₂⟩,
  begin
    refine completion.induction_on₄ a₁ a₂ b₁ b₂ (is_closed_eq _ _) _,
    { refine continuous.comp _ uniform_continuous_prod.continuous,
      refine continuous_add _ _,
      exact continuous.prod_mk (continuous_fst.comp continuous_fst) (continuous_fst.comp continuous_snd),
      exact continuous.prod_mk (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd) },
    { refine continuous_add _ _,
      refine continuous.comp _ uniform_continuous_prod.continuous,
      exact continuous.prod_mk (continuous_fst.comp continuous_fst) (continuous_fst.comp continuous_snd),
      refine continuous.comp _ uniform_continuous_prod.continuous,
      exact continuous.prod_mk (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd) },
    { assume a b c d,
      show completion.prod (↑a + ↑c, ↑b + ↑d) = completion.prod (↑a, ↑b) + completion.prod (↑c, ↑d),
      rw [← coe_add, ← coe_add, prod_coe_coe, prod_coe_coe, prod_coe_coe, ← coe_add],
      refl }
  end⟩

end instance_max_depth

end uniform_add_group

instance [add_comm_group α] [uniform_add_group α] : add_comm_group (completion α) :=
{ add_comm  := assume a b, completion.induction_on₂ a b
    (is_closed_eq (continuous_map₂ continuous_fst continuous_snd) (continuous_map₂ continuous_snd continuous_fst))
    (assume a b, by rw [← coe_add, ← coe_add, add_comm]),
  .. completion.add_group }

end group

end completion

end uniform_space
