/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Uniform structure on topological groups:

* `topological_add_group.to_uniform_space` and `topological_add_group_is_uniform` can be used to
  construct a canonical uniformity for a topological add group.

* extension of ℤ-bilinear maps to complete groups (useful for ring completions)

* `add_group_with_zero_nhd`: construct the topological structure from a group with a neighbourhood
  around zero. Then with `topological_add_group.to_uniform_space` one can derive a `uniform_space`.
-/
import topology.uniform_space.uniform_embedding topology.uniform_space.separation topology.algebra.group

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

local notation `𝓤` := uniformity

section uniform_add_group
open filter set

variables {α : Type*} {β : Type*}

/-- A uniform (additive) group is a group in which the addition and negation are
  uniformly continuous. -/
class uniform_add_group (α : Type*) [uniform_space α] [add_group α] : Prop :=
(uniform_continuous_sub : uniform_continuous (λp:α×α, p.1 - p.2))

theorem uniform_add_group.mk' {α} [uniform_space α] [add_group α]
  (h₁ : uniform_continuous (λp:α×α, p.1 + p.2))
  (h₂ : uniform_continuous (λp:α, -p)) : uniform_add_group α :=
⟨h₁.comp (uniform_continuous_fst.prod_mk (h₂.comp uniform_continuous_snd))⟩

variables [uniform_space α] [add_group α] [uniform_add_group α]

lemma uniform_continuous_sub' : uniform_continuous (λp:α×α, p.1 - p.2) :=
uniform_add_group.uniform_continuous_sub α

lemma uniform_continuous_sub [uniform_space β] {f : β → α} {g : β → α}
  (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous (λx, f x - g x) :=
uniform_continuous_sub'.comp (hf.prod_mk hg)

lemma uniform_continuous_neg [uniform_space β] {f : β → α}
  (hf : uniform_continuous f) : uniform_continuous (λx, - f x) :=
have uniform_continuous (λx, 0 - f x),
  from uniform_continuous_sub uniform_continuous_const hf,
by simp * at *

lemma uniform_continuous_neg' : uniform_continuous (λx:α, - x) :=
uniform_continuous_neg uniform_continuous_id

lemma uniform_continuous_add [uniform_space β] {f : β → α} {g : β → α}
  (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous (λx, f x + g x) :=
have uniform_continuous (λx, f x - - g x),
  from uniform_continuous_sub hf $ uniform_continuous_neg hg,
by simp * at *

lemma uniform_continuous_add' : uniform_continuous (λp:α×α, p.1 + p.2) :=
uniform_continuous_add uniform_continuous_fst uniform_continuous_snd

instance uniform_add_group.to_topological_add_group : topological_add_group α :=
{ continuous_add := uniform_continuous_add'.continuous,
  continuous_neg := uniform_continuous_neg'.continuous }

instance [uniform_space β] [add_group β] [uniform_add_group β] : uniform_add_group (α × β) :=
⟨uniform_continuous.prod_mk
  (uniform_continuous_sub
    (uniform_continuous_fst.comp uniform_continuous_fst)
    (uniform_continuous_fst.comp uniform_continuous_snd))
  (uniform_continuous_sub
    (uniform_continuous_snd.comp uniform_continuous_fst)
    (uniform_continuous_snd.comp uniform_continuous_snd)) ⟩

lemma uniformity_translate (a : α) : (𝓤 α).map (λx:α×α, (x.1 + a, x.2 + a)) = 𝓤 α :=
le_antisymm
  (uniform_continuous_add uniform_continuous_id uniform_continuous_const)
  (calc 𝓤 α =
    ((𝓤 α).map (λx:α×α, (x.1 + -a, x.2 + -a))).map (λx:α×α, (x.1 + a, x.2 + a)) :
      by simp [filter.map_map, (∘)]; exact filter.map_id.symm
    ... ≤ (𝓤 α).map (λx:α×α, (x.1 + a, x.2 + a)) :
      filter.map_mono (uniform_continuous_add uniform_continuous_id uniform_continuous_const))

lemma uniform_embedding_translate (a : α) : uniform_embedding (λx:α, x + a) :=
begin
  refine ⟨assume x y, eq_of_add_eq_add_right, _⟩,
  rw [← uniformity_translate a, comap_map] {occs := occurrences.pos [1]},
  rintros ⟨p₁, p₂⟩ ⟨q₁, q₂⟩,
  simp [prod.eq_iff_fst_eq_snd_eq] {contextual := tt}
end

section
variables (α)
lemma uniformity_eq_comap_nhds_zero : 𝓤 α = comap (λx:α×α, x.2 - x.1) (nhds (0:α)) :=
begin
  rw [nhds_eq_comap_uniformity, filter.comap_comap_comp],
  refine le_antisymm (filter.map_le_iff_le_comap.1 _) _,
  { assume s hs,
    rcases mem_uniformity_of_uniform_continuous_invarant uniform_continuous_sub' hs with ⟨t, ht, hts⟩,
    refine mem_map.2 (mem_sets_of_superset ht _),
    rintros ⟨a, b⟩,
    simpa [subset_def] using hts a b a },
  { assume s hs,
    rcases mem_uniformity_of_uniform_continuous_invarant uniform_continuous_add' hs with ⟨t, ht, hts⟩,
    refine ⟨_, ht, _⟩,
    rintros ⟨a, b⟩, simpa [subset_def] using hts 0 (b - a) a }
end
end

lemma group_separation_rel (x y : α) : (x, y) ∈ separation_rel α ↔ x - y ∈ closure ({0} : set α) :=
have embedding (λa, a + (y - x)), from (uniform_embedding_translate (y - x)).embedding,
show (x, y) ∈ ⋂₀ (𝓤 α).sets ↔ x - y ∈ closure ({0} : set α),
begin
  rw [this.closure_eq_preimage_closure_image, uniformity_eq_comap_nhds_zero α, sInter_comap_sets],
  simp [mem_closure_iff_nhds, inter_singleton_eq_empty]
end

lemma uniform_continuous_of_tendsto_zero [uniform_space β] [add_group β] [uniform_add_group β]
  {f : α → β} [is_add_group_hom f] (h : tendsto f (nhds 0) (nhds 0)) :
  uniform_continuous f :=
begin
  have : ((λx:β×β, x.2 - x.1) ∘ (λx:α×α, (f x.1, f x.2))) = (λx:α×α, f (x.2 - x.1)),
  { simp only [is_add_group_hom.map_sub f] },
  rw [uniform_continuous, uniformity_eq_comap_nhds_zero α, uniformity_eq_comap_nhds_zero β,
    tendsto_comap_iff, this],
  exact tendsto.comp h tendsto_comap
end

lemma uniform_continuous_of_continuous [uniform_space β] [add_group β] [uniform_add_group β]
  {f : α → β} [is_add_group_hom f] (h : continuous f) :
  uniform_continuous f :=
uniform_continuous_of_tendsto_zero $
  suffices tendsto f (nhds 0) (nhds (f 0)), by rwa [is_add_group_hom.map_zero f] at this,
  h.tendsto 0

end uniform_add_group

section topological_add_comm_group
universes u v w x
open filter

variables {G : Type u} [add_comm_group G] [topological_space G] [topological_add_group G]

variable (G)
def topological_add_group.to_uniform_space : uniform_space G :=
{ uniformity          := comap (λp:G×G, p.2 - p.1) (nhds 0),
  refl                :=
    by refine map_le_iff_le_comap.1 (le_trans _ (pure_le_nhds 0));
      simp [set.subset_def] {contextual := tt},
  symm                :=
  begin
    suffices : tendsto ((λp, -p) ∘ (λp:G×G, p.2 - p.1)) (comap (λp:G×G, p.2 - p.1) (nhds 0)) (nhds (-0)),
    { simpa [(∘), tendsto_comap_iff] },
    exact tendsto.comp (tendsto_neg tendsto_id) tendsto_comap
  end,
  comp                :=
  begin
    intros D H,
    rw mem_lift'_sets,
    { rcases H with ⟨U, U_nhds, U_sub⟩,
      rcases exists_nhds_half U_nhds with ⟨V, ⟨V_nhds, V_sum⟩⟩,
      existsi ((λp:G×G, p.2 - p.1) ⁻¹' V),
      have H : (λp:G×G, p.2 - p.1) ⁻¹' V ∈ comap (λp:G×G, p.2 - p.1) (nhds (0 : G)),
        by existsi [V, V_nhds] ; refl,
      existsi H,
      have comp_rel_sub : comp_rel ((λp:G×G, p.2 - p.1) ⁻¹' V) ((λp:G×G, p.2 - p.1) ⁻¹' V) ⊆ (λp:G×G, p.2 - p.1) ⁻¹' U,
      begin
        intros p p_comp_rel,
        rcases p_comp_rel with ⟨z, ⟨Hz1, Hz2⟩⟩,
        simpa using V_sum _ _ Hz1 Hz2
      end,
      exact set.subset.trans comp_rel_sub U_sub },
    { exact monotone_comp_rel monotone_id monotone_id }
  end,
  is_open_uniformity  :=
  begin
    intro S,
    let S' := λ x, {p : G × G | p.1 = x → p.2 ∈ S},
    show is_open S ↔ ∀ (x : G), x ∈ S → S' x ∈ comap (λp:G×G, p.2 - p.1) (nhds (0 : G)),
    rw [is_open_iff_mem_nhds],
    refine forall_congr (assume a, forall_congr (assume ha, _)),
    rw [← nhds_translation a, mem_comap_sets, mem_comap_sets],
    refine exists_congr (assume t, exists_congr (assume ht, _)),
    show (λ (y : G), y - a) ⁻¹' t ⊆ S ↔ (λ (p : G × G), p.snd - p.fst) ⁻¹' t ⊆ S' a,
    split,
    { rintros h ⟨x, y⟩ hx rfl, exact h hx },
    { rintros h x hx, exact @h (a, x) hx rfl }
  end }

section
local attribute [instance] topological_add_group.to_uniform_space

lemma uniformity_eq_comap_nhds_zero' : 𝓤 G = comap (λp:G×G, p.2 - p.1) (nhds (0 : G)) := rfl

variable {G}
lemma topological_add_group_is_uniform : uniform_add_group G :=
have tendsto
    ((λp:(G×G), p.1 - p.2) ∘ (λp:(G×G)×(G×G), (p.1.2 - p.1.1, p.2.2 - p.2.1)))
    (comap (λp:(G×G)×(G×G), (p.1.2 - p.1.1, p.2.2 - p.2.1)) ((nhds 0).prod (nhds 0)))
    (nhds (0 - 0)) :=
  (tendsto_sub tendsto_fst tendsto_snd).comp tendsto_comap,
begin
  constructor,
  rw [uniform_continuous, uniformity_prod_eq_prod, tendsto_map'_iff,
    uniformity_eq_comap_nhds_zero' G, tendsto_comap_iff, prod_comap_comap_eq],
  simpa [(∘)]
end
end

lemma to_uniform_space_eq {α : Type*} [u : uniform_space α] [add_comm_group α] [uniform_add_group α]:
  topological_add_group.to_uniform_space α = u :=
begin
  ext : 1,
  show @uniformity α (topological_add_group.to_uniform_space α) = 𝓤 α,
  rw [uniformity_eq_comap_nhds_zero' α, uniformity_eq_comap_nhds_zero α]
end

end topological_add_comm_group

namespace add_comm_group
section Z_bilin

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables [add_comm_group α] [add_comm_group β] [add_comm_group γ]

/- TODO: when modules are changed to have more explicit base ring, then change replace `is_Z_bilin`
by using `is_bilinear_map ℤ` from `tensor_product`. -/
class is_Z_bilin (f : α × β → γ) : Prop :=
(add_left  : ∀ a a' b, f (a + a', b) = f (a, b) + f (a', b))
(add_right : ∀ a b b', f (a, b + b') = f (a, b) + f (a, b'))

variables (f : α × β → γ) [is_Z_bilin f]

instance is_Z_bilin.comp_hom {g : γ → δ} [add_comm_group δ] [is_add_group_hom g] :
  is_Z_bilin (g ∘ f) :=
by constructor; simp [(∘), is_Z_bilin.add_left f, is_Z_bilin.add_right f, is_add_group_hom.map_add g]

instance is_Z_bilin.comp_swap : is_Z_bilin (f ∘ prod.swap) :=
⟨λ a a' b, is_Z_bilin.add_right f b a a',
 λ a b b', is_Z_bilin.add_left f b b' a⟩

lemma is_Z_bilin.zero_left : ∀ b, f (0, b) = 0 :=
begin
  intro b,
  apply add_self_iff_eq_zero.1,
  rw ←is_Z_bilin.add_left f,
  simp
end

lemma is_Z_bilin.zero_right : ∀ a, f (a, 0) = 0 :=
is_Z_bilin.zero_left (f ∘ prod.swap)

lemma is_Z_bilin.zero : f (0, 0) = 0 :=
is_Z_bilin.zero_left f 0

lemma is_Z_bilin.neg_left  : ∀ a b, f (-a, b) = -f (a, b) :=
begin
  intros a b,
  apply eq_of_sub_eq_zero,
  rw [sub_eq_add_neg, neg_neg, ←is_Z_bilin.add_left f, neg_add_self, is_Z_bilin.zero_left f]
end

lemma is_Z_bilin.neg_right  : ∀ a b, f (a, -b) = -f (a, b) :=
assume a b, is_Z_bilin.neg_left (f ∘ prod.swap) b a

lemma is_Z_bilin.sub_left : ∀ a a' b, f (a - a', b) = f (a, b) - f (a', b) :=
begin
  intros,
  dsimp [algebra.sub],
  rw [is_Z_bilin.add_left f, is_Z_bilin.neg_left f]
end

lemma is_Z_bilin.sub_right : ∀ a b b', f (a, b - b') = f (a, b) - f (a,b') :=
assume a b b', is_Z_bilin.sub_left (f ∘ prod.swap) b b' a
end Z_bilin
end add_comm_group

open add_comm_group filter set function

section
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

-- α, β and G are abelian topological groups, G is complete Hausdorff
variables [topological_space α] [add_comm_group α] [topological_add_group α]
variables [topological_space β] [add_comm_group β] [topological_add_group β]
variables {G : Type*} [uniform_space G] [add_comm_group G] [uniform_add_group G]
  [complete_space G] [separated G]

variables {ψ : α × β → G} (hψ : continuous ψ) [ψbilin : is_Z_bilin ψ]

include hψ ψbilin

lemma is_Z_bilin.tendsto_zero_left (x₁ : α) : tendsto ψ (nhds (x₁, 0)) (nhds 0) :=
begin
  have := continuous.tendsto hψ (x₁, 0),
  rwa [is_Z_bilin.zero_right ψ] at this
end

lemma is_Z_bilin.tendsto_zero_right (y₁ : β) : tendsto ψ (nhds (0, y₁)) (nhds 0) :=
begin
  have := continuous.tendsto hψ (0, y₁),
  rwa [is_Z_bilin.zero_left ψ] at this
end
end

section
variables {α : Type*} {β : Type*}
variables [topological_space α] [add_comm_group α] [topological_add_group α]

-- β is a dense subgroup of α, inclusion is denoted by e
variables [topological_space β] [add_comm_group β] [topological_add_group β]
variables {e : β → α} [is_add_group_hom e] (de : dense_embedding e)
include de

lemma tendsto_sub_comap_self (x₀ : α) :
  tendsto (λt:β×β, t.2 - t.1) (comap (λp:β×β, (e p.1, e p.2)) $ nhds (x₀, x₀)) (nhds 0) :=
begin
  have comm : (λx:α×α, x.2-x.1) ∘ (λt:β×β, (e t.1, e t.2)) = e ∘ (λt:β×β, t.2 - t.1),
  { ext t,
    change e t.2 - e t.1 = e (t.2 - t.1),
    rwa ← is_add_group_hom.map_sub e t.2 t.1 },
  have lim : tendsto (λ x : α × α, x.2-x.1) (nhds (x₀, x₀)) (nhds (e 0)),
    { have := continuous.tendsto (continuous_sub'.comp continuous_swap) (x₀, x₀),
      simpa [-sub_eq_add_neg, sub_self, eq.symm (is_add_group_hom.map_zero e)] using this },
  have := de.tendsto_comap_nhds_nhds lim comm,
  simp [-sub_eq_add_neg, this]
end
end

namespace dense_embedding
open filter
variables {α : Type*} [topological_space α]
variables {β : Type*} [topological_space β]
variables {γ : Type*} [uniform_space γ] [complete_space γ] [separated γ]

lemma continuous_extend_of_cauchy {e : α → β} {f : α → γ}
  (de : dense_embedding e) (h : ∀ b : β, cauchy (map f (comap e $ nhds b))) :
  continuous (de.extend f) :=
continuous_extend de $ λ b, complete_space.complete (h b)

end dense_embedding

namespace dense_embedding
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables {G : Type*}

-- β is a dense subgroup of α, inclusion is denoted by e
-- δ is a dense subgroup of γ, inclusion is denoted by f
variables [topological_space α] [add_comm_group α] [topological_add_group α]
variables [topological_space β] [add_comm_group β] [topological_add_group β]
variables [topological_space γ] [add_comm_group γ] [topological_add_group γ]
variables [topological_space δ] [add_comm_group δ] [topological_add_group δ]
variables [uniform_space G] [add_comm_group G] [uniform_add_group G] [separated G] [complete_space G]
variables {e : β → α} [is_add_group_hom e] (de : dense_embedding e)
variables {f : δ → γ} [is_add_group_hom f] (df : dense_embedding f)
variables {φ : β × δ → G} (hφ : continuous φ) [bilin : is_Z_bilin φ]

include de df hφ bilin

variables {W' : set G} (W'_nhd : W' ∈ nhds (0 : G))
include W'_nhd

private lemma extend_Z_bilin_aux (x₀ : α) (y₁ : δ) :
  ∃ U₂ ∈ comap e (nhds x₀), ∀ x x' ∈ U₂, φ (x' - x, y₁) ∈ W' :=
begin
  let Nx := nhds x₀,
  let ee := λ u : β × β, (e u.1, e u.2),

  have lim1 : tendsto (λ a : β × β, (a.2 - a.1, y₁)) (filter.prod (comap e Nx) (comap e Nx)) (nhds (0, y₁)),
  { have := tendsto.prod_mk (tendsto_sub_comap_self de x₀) (tendsto_const_nhds : tendsto (λ (p : β × β), y₁) (comap ee $ nhds (x₀, x₀)) (nhds y₁)),
    rw [nhds_prod_eq, prod_comap_comap_eq, ←nhds_prod_eq],
    exact (this : _) },

  have lim := tendsto.comp (is_Z_bilin.tendsto_zero_right hφ y₁) lim1,
  rw tendsto_prod_self_iff at lim,
  exact lim W' W'_nhd,
end

private lemma extend_Z_bilin_key (x₀ : α) (y₀ : γ) :
  ∃ U ∈ comap e (nhds x₀), ∃ V ∈ comap f (nhds y₀),
    ∀ x x' ∈ U, ∀ y y' ∈ V, φ (x', y') - φ (x, y) ∈ W' :=
begin
  let Nx := nhds x₀,
  let Ny := nhds y₀,
  let dp := dense_embedding.prod de df,
  let ee := λ u : β × β, (e u.1, e u.2),
  let ff := λ u : δ × δ, (f u.1, f u.2),

  have lim_φ : filter.tendsto φ (nhds (0, 0)) (nhds 0),
  { have := continuous.tendsto hφ (0, 0),
    rwa [is_Z_bilin.zero φ] at this },

  have lim_φ_sub_sub : tendsto (λ (p : (β × β) × (δ × δ)), φ (p.1.2 - p.1.1, p.2.2 - p.2.1))
    (filter.prod (comap ee $ nhds (x₀, x₀)) (comap ff $ nhds (y₀, y₀))) (nhds 0),
  { have lim_sub_sub :  tendsto (λ (p : (β × β) × δ × δ), (p.1.2 - p.1.1, p.2.2 - p.2.1))
      (filter.prod (comap ee (nhds (x₀, x₀))) (comap ff (nhds (y₀, y₀)))) (filter.prod (nhds 0) (nhds 0)),
    { have := filter.prod_mono (tendsto_sub_comap_self de x₀) (tendsto_sub_comap_self df y₀),
      rwa prod_map_map_eq at this },
    rw ← nhds_prod_eq at lim_sub_sub,
    exact tendsto.comp lim_φ lim_sub_sub },

  rcases exists_nhds_quarter W'_nhd with ⟨W, W_nhd, W4⟩,

  have : ∃ U₁ ∈ comap e (nhds x₀), ∃ V₁ ∈ comap f (nhds y₀),
    ∀ x x' ∈ U₁, ∀ y y' ∈ V₁,  φ (x'-x, y'-y) ∈ W,
  { have := tendsto_prod_iff.1 lim_φ_sub_sub W W_nhd,
    repeat { rw [nhds_prod_eq, ←prod_comap_comap_eq] at this },
    rcases this with ⟨U, U_in, V, V_in, H⟩,
    rw [mem_prod_same_iff] at U_in V_in,
    rcases U_in with ⟨U₁, U₁_in, HU₁⟩,
    rcases V_in with ⟨V₁, V₁_in, HV₁⟩,
    existsi [U₁, U₁_in, V₁, V₁_in],
    intros x x' x_in x'_in y y' y_in y'_in,
    exact H _ _ (HU₁ (mk_mem_prod x_in x'_in)) (HV₁ (mk_mem_prod y_in y'_in)) },
  rcases this with ⟨U₁, U₁_nhd, V₁, V₁_nhd, H⟩,

  have : ∃ x₁, x₁ ∈ U₁ := exists_mem_of_ne_empty
    (forall_sets_neq_empty_iff_neq_bot.2 de.comap_nhds_neq_bot U₁ U₁_nhd),
  rcases this with ⟨x₁, x₁_in⟩,

  have : ∃ y₁, y₁ ∈ V₁ := exists_mem_of_ne_empty
    (forall_sets_neq_empty_iff_neq_bot.2 df.comap_nhds_neq_bot V₁ V₁_nhd),
  rcases this with ⟨y₁, y₁_in⟩,

  rcases (extend_Z_bilin_aux de df hφ W_nhd x₀ y₁) with ⟨U₂, U₂_nhd, HU⟩,
  rcases (extend_Z_bilin_aux df de (hφ.comp continuous_swap) W_nhd y₀ x₁) with ⟨V₂, V₂_nhd, HV⟩,

  existsi [U₁ ∩ U₂, inter_mem_sets U₁_nhd U₂_nhd,
            V₁ ∩ V₂, inter_mem_sets V₁_nhd V₂_nhd],

  rintros x x' ⟨xU₁, xU₂⟩ ⟨x'U₁, x'U₂⟩ y y' ⟨yV₁, yV₂⟩ ⟨y'V₁, y'V₂⟩,
  have key_formula : φ(x', y') - φ(x, y) = φ(x' - x, y₁) + φ(x' - x, y' - y₁) + φ(x₁, y' - y) + φ(x - x₁, y' - y),
  { repeat { rw is_Z_bilin.sub_left φ },
    repeat { rw is_Z_bilin.sub_right φ },
    apply eq_of_sub_eq_zero,
    simp },
  rw key_formula,
  have h₁ := HU x x' xU₂ x'U₂,
  have h₂ := H x x' xU₁ x'U₁ y₁ y' y₁_in y'V₁,
  have h₃ := HV y y' yV₂ y'V₂,
  have h₄ := H x₁ x x₁_in xU₁ y y' yV₁ y'V₁,

  exact W4 h₁ h₂ h₃ h₄
end
omit W'_nhd

/-- Bourbaki GT III.6.5 Theorem I:
ℤ-bilinear continuous maps from dense sub-groups into a complete Hausdorff group extend by continuity.
Note: Bourbaki assumes that α and β are also complete Hausdorff, but this is not necessary. -/
theorem extend_Z_bilin  : continuous (extend (dense_embedding.prod de df) φ) :=
begin
  let dp := dense_embedding.prod de df,
  refine dense_embedding.continuous_extend_of_cauchy (dense_embedding.prod de df) _,
  rintro ⟨x₀, y₀⟩,
  split,
  { apply map_ne_bot,
    apply comap_neq_bot,

    intros U h,
    rcases exists_mem_of_ne_empty (mem_closure_iff_nhds.1 (dp.dense (x₀, y₀)) U h)
      with ⟨x, x_in, ⟨z, z_x⟩⟩,
    existsi z,
    cc },
  { suffices : map (λ (p : (β × δ) × (β × δ)), φ p.2 - φ p.1)
      (comap (λ (p : (β × δ) × β × δ), ((e p.1.1, f p.1.2), (e p.2.1, f p.2.2)))
         (filter.prod (nhds (x₀, y₀)) (nhds (x₀, y₀)))) ≤ nhds 0,
    by rwa [uniformity_eq_comap_nhds_zero G, prod_map_map_eq, ←map_le_iff_le_comap, filter.map_map,
        prod_comap_comap_eq],

    intros W' W'_nhd,

    have key := extend_Z_bilin_key de df hφ W'_nhd x₀ y₀,
    rcases key with ⟨U, U_nhd, V, V_nhd, h⟩,
    rw mem_comap_sets at U_nhd,
    rcases U_nhd with ⟨U', U'_nhd, U'_sub⟩,
    rw mem_comap_sets at V_nhd,
    rcases V_nhd with ⟨V', V'_nhd, V'_sub⟩,

    rw [mem_map, mem_comap_sets, nhds_prod_eq],
    existsi set.prod (set.prod U' V') (set.prod U' V'),
    rw mem_prod_same_iff,

    simp only [exists_prop],
    split,
    { change U' ∈ nhds x₀ at U'_nhd,
      change V' ∈ nhds y₀ at V'_nhd,
      have := prod_mem_prod U'_nhd V'_nhd,
      tauto },
    { intros p h',
      simp only [set.mem_preimage_eq, set.prod_mk_mem_set_prod_eq] at h',
      rcases p with ⟨⟨x, y⟩, ⟨x', y'⟩⟩,
      apply h ; tauto } }
end
end dense_embedding
