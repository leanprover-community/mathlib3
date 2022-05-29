/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import topology.uniform_space.uniform_convergence
import topology.uniform_space.uniform_embedding
import topology.uniform_space.complete_separated
import topology.algebra.group
import tactic.abel

/-!
# Uniform structure on topological groups

This file defines uniform groups and its additive counterpart. These typeclasses should be
preferred over using `[topological_space α] [topological_group α]` since every topological
group naturally induces a uniform structure.

## Main declarations
* `uniform_group` and `uniform_add_group`: Multiplicative and additive uniform groups, that
  i.e., groups with uniformly continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`.

## Main results

* `topological_add_group.to_uniform_space` and `topological_add_group_is_uniform` can be used to
  construct a canonical uniformity for a topological add group.

* extension of ℤ-bilinear maps to complete groups (useful for ring completions)
-/

noncomputable theory
open_locale classical uniformity topological_space filter pointwise

section uniform_group
open filter set

variables {α : Type*} {β : Type*}

/-- A uniform group is a group in which multiplication and inversion are uniformly continuous. -/
class uniform_group (α : Type*) [uniform_space α] [group α] : Prop :=
(uniform_continuous_div : uniform_continuous (λp:α×α, p.1 / p.2))

/-- A uniform additive group is an additive group in which addition
  and negation are uniformly continuous.-/
class uniform_add_group (α : Type*) [uniform_space α] [add_group α] : Prop :=
(uniform_continuous_sub : uniform_continuous (λp:α×α, p.1 - p.2))

attribute [to_additive] uniform_group

@[to_additive] theorem uniform_group.mk' {α} [uniform_space α] [group α]
  (h₁ : uniform_continuous (λp:α×α, p.1 * p.2))
  (h₂ : uniform_continuous (λp:α, p⁻¹)) : uniform_group α :=
⟨by simpa only [div_eq_mul_inv] using
  h₁.comp (uniform_continuous_fst.prod_mk (h₂.comp uniform_continuous_snd))⟩

variables [uniform_space α] [group α] [uniform_group α]

@[to_additive] lemma uniform_continuous_div : uniform_continuous (λp:α×α, p.1 / p.2) :=
uniform_group.uniform_continuous_div

@[to_additive] lemma uniform_continuous.div [uniform_space β] {f : β → α} {g : β → α}
  (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous (λx, f x / g x) :=
uniform_continuous_div.comp (hf.prod_mk hg)

@[to_additive] lemma uniform_continuous.inv [uniform_space β] {f : β → α}
  (hf : uniform_continuous f) : uniform_continuous (λx, (f x)⁻¹) :=
have uniform_continuous (λx, 1 / f x),
  from uniform_continuous_const.div hf,
by simp * at *

@[to_additive] lemma uniform_continuous_inv : uniform_continuous (λx:α, x⁻¹) :=
uniform_continuous_id.inv

@[to_additive] lemma uniform_continuous.mul [uniform_space β] {f : β → α} {g : β → α}
  (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous (λx, f x * g x) :=
have uniform_continuous (λx, f x / (g x)⁻¹), from hf.div hg.inv,
by simp * at *

@[to_additive] lemma uniform_continuous_mul : uniform_continuous (λp:α×α, p.1 * p.2) :=
uniform_continuous_fst.mul uniform_continuous_snd

@[priority 10, to_additive]
instance uniform_group.to_topological_group : topological_group α :=
{ continuous_mul := uniform_continuous_mul.continuous,
  continuous_inv := uniform_continuous_inv.continuous }

@[to_additive] instance [uniform_space β] [group β] [uniform_group β] : uniform_group (α × β) :=
⟨((uniform_continuous_fst.comp uniform_continuous_fst).div
  (uniform_continuous_fst.comp uniform_continuous_snd)).prod_mk
 ((uniform_continuous_snd.comp uniform_continuous_fst).div
  (uniform_continuous_snd.comp uniform_continuous_snd))⟩

@[to_additive] lemma uniformity_translate_mul (a : α) :
  (𝓤 α).map (λx:α×α, (x.1 * a, x.2 * a)) = 𝓤 α :=
le_antisymm
  (uniform_continuous_id.mul uniform_continuous_const)
  (calc 𝓤 α =
    ((𝓤 α).map (λx:α×α, (x.1 * a⁻¹, x.2 * a⁻¹))).map (λx:α×α, (x.1 * a, x.2 * a)) :
      by simp [filter.map_map, (∘)]; exact filter.map_id.symm
    ... ≤ (𝓤 α).map (λx:α×α, (x.1 * a, x.2 * a)) :
      filter.map_mono (uniform_continuous_id.mul uniform_continuous_const))

@[to_additive] lemma uniform_embedding_translate_mul (a : α) : uniform_embedding (λx:α, x * a) :=
{ comap_uniformity := begin
    rw [← uniformity_translate_mul a, comap_map] {occs := occurrences.pos [1]},
    rintros ⟨p₁, p₂⟩ ⟨q₁, q₂⟩,
    simp [prod.eq_iff_fst_eq_snd_eq] {contextual := tt}
  end,
  inj := mul_left_injective a }


namespace mul_opposite

@[to_additive] instance : uniform_group αᵐᵒᵖ :=
⟨uniform_continuous_op.comp ((uniform_continuous_unop.comp uniform_continuous_snd).inv.mul $
  uniform_continuous_unop.comp uniform_continuous_fst)⟩

end mul_opposite

namespace subgroup

@[to_additive] instance (S : subgroup α) : uniform_group S :=
⟨uniform_continuous_comap' (uniform_continuous_div.comp $
  uniform_continuous_subtype_val.prod_map uniform_continuous_subtype_val)⟩

end subgroup

section
variables (α)

@[to_additive] lemma uniformity_eq_comap_nhds_one : 𝓤 α = comap (λx:α×α, x.2 / x.1) (𝓝 (1:α)) :=
begin
  rw [nhds_eq_comap_uniformity, filter.comap_comap],
  refine le_antisymm (filter.map_le_iff_le_comap.1 _) _,
  { assume s hs,
    rcases mem_uniformity_of_uniform_continuous_invariant uniform_continuous_div hs
      with ⟨t, ht, hts⟩,
    refine mem_map.2 (mem_of_superset ht _),
    rintros ⟨a, b⟩,
    simpa [subset_def] using hts a b a },
  { assume s hs,
    rcases mem_uniformity_of_uniform_continuous_invariant uniform_continuous_mul hs
      with ⟨t, ht, hts⟩,
    refine ⟨_, ht, _⟩,
    rintros ⟨a, b⟩, simpa [subset_def] using hts 1 (b / a) a }
end

@[to_additive] lemma uniformity_eq_comap_nhds_one_swapped :
  𝓤 α = comap (λx:α×α, x.1 / x.2) (𝓝 (1:α)) :=
by { rw [← comap_swap_uniformity, uniformity_eq_comap_nhds_one, comap_comap, (∘)], refl }

open mul_opposite

@[to_additive]
lemma uniformity_eq_comap_inv_mul_nhds_one : 𝓤 α = comap (λx:α×α, x.1⁻¹ * x.2) (𝓝 (1:α)) :=
begin
  rw [← comap_uniformity_mul_opposite, uniformity_eq_comap_nhds_one, ← op_one, ← comap_unop_nhds,
    comap_comap, comap_comap],
  simp [(∘)]
end

@[to_additive] lemma uniformity_eq_comap_inv_mul_nhds_one_swapped :
  𝓤 α = comap (λx:α×α, x.2⁻¹ * x.1) (𝓝 (1:α)) :=
by { rw [← comap_swap_uniformity, uniformity_eq_comap_inv_mul_nhds_one, comap_comap, (∘)], refl }

end

@[to_additive] lemma filter.has_basis.uniformity_of_nhds_one {ι} {p : ι → Prop} {U : ι → set α}
  (h : (𝓝 (1 : α)).has_basis p U) :
  (𝓤 α).has_basis p (λ i, {x : α × α | x.2 / x.1 ∈ U i}) :=
by { rw uniformity_eq_comap_nhds_one, exact h.comap _ }

@[to_additive] lemma filter.has_basis.uniformity_of_nhds_one_inv_mul
  {ι} {p : ι → Prop} {U : ι → set α} (h : (𝓝 (1 : α)).has_basis p U) :
  (𝓤 α).has_basis p (λ i, {x : α × α | x.1⁻¹ * x.2 ∈ U i}) :=
by { rw uniformity_eq_comap_inv_mul_nhds_one, exact h.comap _ }

@[to_additive] lemma filter.has_basis.uniformity_of_nhds_one_swapped
  {ι} {p : ι → Prop} {U : ι → set α} (h : (𝓝 (1 : α)).has_basis p U) :
  (𝓤 α).has_basis p (λ i, {x : α × α | x.1 / x.2 ∈ U i}) :=
by { rw uniformity_eq_comap_nhds_one_swapped, exact h.comap _ }

@[to_additive] lemma filter.has_basis.uniformity_of_nhds_one_inv_mul_swapped
  {ι} {p : ι → Prop} {U : ι → set α} (h : (𝓝 (1 : α)).has_basis p U) :
  (𝓤 α).has_basis p (λ i, {x : α × α | x.2⁻¹ * x.1 ∈ U i}) :=
by { rw uniformity_eq_comap_inv_mul_nhds_one_swapped, exact h.comap _ }

@[to_additive] lemma group_separation_rel (x y : α) :
  (x, y) ∈ separation_rel α ↔ x / y ∈ closure ({1} : set α) :=
have embedding (λa, a * (y / x)), from (uniform_embedding_translate_mul (y / x)).embedding,
show (x, y) ∈ ⋂₀ (𝓤 α).sets ↔ x / y ∈ closure ({1} : set α),
begin
  rw [this.closure_eq_preimage_closure_image, uniformity_eq_comap_nhds_one α, sInter_comap_sets],
  simp [mem_closure_iff_nhds, inter_singleton_nonempty, sub_eq_add_neg, add_assoc]
end

@[to_additive] lemma uniform_continuous_of_tendsto_one {hom : Type*} [uniform_space β] [group β]
  [uniform_group β] [monoid_hom_class hom α β] {f : hom} (h : tendsto f (𝓝 1) (𝓝 1)) :
  uniform_continuous f :=
begin
  have : ((λx:β×β, x.2 / x.1) ∘ (λx:α×α, (f x.1, f x.2))) = (λx:α×α, f (x.2 / x.1)),
  { simp only [map_div] },
  rw [uniform_continuous, uniformity_eq_comap_nhds_one α, uniformity_eq_comap_nhds_one β,
    tendsto_comap_iff, this],
  exact tendsto.comp h tendsto_comap
end

@[to_additive] lemma uniform_continuous_of_continuous_at_one {hom : Type*}
  [uniform_space β] [group β] [uniform_group β] [monoid_hom_class hom α β]
  (f : hom) (hf : continuous_at f 1) :
  uniform_continuous f :=
uniform_continuous_of_tendsto_one (by simpa using hf.tendsto)

@[to_additive] lemma monoid_hom.uniform_continuous_of_continuous_at_one
  [uniform_space β] [group β] [uniform_group β]
  (f : α →* β) (hf : continuous_at f 1) :
  uniform_continuous f :=
uniform_continuous_of_continuous_at_one f hf

/-- A homomorphism from a uniform group to a discrete uniform group is continuous if and only if
its kernel is open. -/
@[to_additive "A homomorphism from a uniform additive group to a discrete uniform additive group is
continuous if and only if its kernel is open."]
lemma uniform_group.uniform_continuous_iff_open_ker {hom : Type*} [uniform_space β]
  [discrete_topology β] [group β] [uniform_group β] [monoid_hom_class hom α β] {f : hom} :
  uniform_continuous f ↔ is_open ((f : α →* β).ker : set α) :=
begin
  refine ⟨λ hf, _, λ hf, _⟩,
  { apply (is_open_discrete ({1} : set β)).preimage (uniform_continuous.continuous hf) },
  { apply uniform_continuous_of_continuous_at_one,
    rw [continuous_at, nhds_discrete β, map_one, tendsto_pure],
    exact hf.mem_nhds (map_one f) }
end

@[to_additive] lemma uniform_continuous_monoid_hom_of_continuous {hom : Type*} [uniform_space β]
  [group β] [uniform_group β] [monoid_hom_class hom α β] {f : hom} (h : continuous f) :
  uniform_continuous f :=
uniform_continuous_of_tendsto_one $
  suffices tendsto f (𝓝 1) (𝓝 (f 1)), by rwa map_one at this,
  h.tendsto 1

@[to_additive] lemma cauchy_seq.mul {ι : Type*} [semilattice_sup ι] {u v : ι → α}
  (hu : cauchy_seq u) (hv : cauchy_seq v) : cauchy_seq (u * v) :=
uniform_continuous_mul.comp_cauchy_seq (hu.prod hv)

@[to_additive] lemma cauchy_seq.mul_const {ι : Type*} [semilattice_sup ι]
  {u : ι → α} {x : α} (hu : cauchy_seq u) : cauchy_seq (λ n, u n * x) :=
(uniform_continuous_id.mul uniform_continuous_const).comp_cauchy_seq hu

@[to_additive] lemma cauchy_seq.const_mul {ι : Type*} [semilattice_sup ι]
  {u : ι → α} {x : α} (hu : cauchy_seq u) : cauchy_seq (λ n, x * u n) :=
(uniform_continuous_const.mul uniform_continuous_id).comp_cauchy_seq hu

@[to_additive] lemma cauchy_seq.inv {ι : Type*} [semilattice_sup ι]
  {u : ι → α} (h : cauchy_seq u) : cauchy_seq (u⁻¹) :=
uniform_continuous_inv.comp_cauchy_seq h

@[to_additive] lemma totally_bounded_iff_subset_finite_Union_nhds_one {s : set α} :
  totally_bounded s ↔ ∀ U ∈ 𝓝 (1 : α), ∃ (t : set α), t.finite ∧ s ⊆ ⋃ y ∈ t, y • U :=
(𝓝 (1 : α)).basis_sets.uniformity_of_nhds_one_inv_mul_swapped.totally_bounded_iff.trans $
  by simp [← preimage_smul_inv, preimage]

end uniform_group

section topological_comm_group
open filter
variables (G : Type*) [comm_group G] [topological_space G] [topological_group G]

/-- The right uniformity on a topological group. -/
@[to_additive "The right uniformity on a topological group"]
def topological_group.to_uniform_space : uniform_space G :=
{ uniformity          := comap (λp:G×G, p.2 / p.1) (𝓝 1),
  refl                :=
    by refine map_le_iff_le_comap.1 (le_trans _ (pure_le_nhds 1));
      simp [set.subset_def] {contextual := tt},
  symm                :=
  begin
    suffices : tendsto (λp:G×G, (p.2 / p.1)⁻¹) (comap (λp:G×G, p.2 / p.1) (𝓝 1)) (𝓝 1⁻¹),
    { simpa [tendsto_comap_iff], },
    exact tendsto.comp (tendsto.inv tendsto_id) tendsto_comap
  end,
  comp                :=
  begin
    intros D H,
    rw mem_lift'_sets,
    { rcases H with ⟨U, U_nhds, U_sub⟩,
      rcases exists_nhds_one_split U_nhds with ⟨V, ⟨V_nhds, V_sum⟩⟩,
      existsi ((λp:G×G, p.2 / p.1) ⁻¹' V),
      have H : (λp:G×G, p.2 / p.1) ⁻¹' V ∈ comap (λp:G×G, p.2 / p.1) (𝓝 (1 : G)),
        by existsi [V, V_nhds] ; refl,
      existsi H,
      have comp_rel_sub :
        comp_rel ((λp:G×G, p.2 / p.1) ⁻¹' V) ((λp, p.2 / p.1) ⁻¹' V) ⊆ (λp:G×G, p.2 / p.1) ⁻¹' U,
      begin
        intros p p_comp_rel,
        rcases p_comp_rel with ⟨z, ⟨Hz1, Hz2⟩⟩,
        simpa [sub_eq_add_neg, add_comm, add_left_comm] using V_sum _ Hz1 _ Hz2
      end,
      exact set.subset.trans comp_rel_sub U_sub },
    { exact monotone_comp_rel monotone_id monotone_id }
  end,
  is_open_uniformity  :=
  begin
    intro S,
    let S' := λ x, {p : G × G | p.1 = x → p.2 ∈ S},
    show is_open S ↔ ∀ (x : G), x ∈ S → S' x ∈ comap (λp:G×G, p.2 / p.1) (𝓝 (1 : G)),
    rw [is_open_iff_mem_nhds],
    refine forall₂_congr (λ a ha, _),
    rw [← nhds_translation_div, mem_comap, mem_comap],
    refine exists₂_congr (λ t ht, _),
    show (λ (y : G), y / a) ⁻¹' t ⊆ S ↔ (λ (p : G × G), p.snd / p.fst) ⁻¹' t ⊆ S' a,
    split,
    { rintros h ⟨x, y⟩ hx rfl, exact h hx },
    { rintros h x hx, exact @h (a, x) hx rfl }
  end }

variables {G}

@[to_additive] lemma topological_group.tendsto_uniformly_iff
  {ι α : Type*} (F : ι → α → G) (f : α → G) (p : filter ι) :
  @tendsto_uniformly α G ι (topological_group.to_uniform_space G) F f p
    ↔ ∀ u ∈ 𝓝 (1 : G), ∀ᶠ i in p, ∀ a, F i a / f a ∈ u :=
⟨λ h u hu, h _ ⟨u, hu, λ _, id⟩, λ h v ⟨u, hu, hv⟩,
  mem_of_superset (h u hu) (λ i hi a, hv (by exact hi a))⟩

@[to_additive] lemma topological_group.tendsto_uniformly_on_iff
  {ι α : Type*} (F : ι → α → G) (f : α → G) (p : filter ι) (s : set α) :
  @tendsto_uniformly_on α G ι (topological_group.to_uniform_space G) F f p s
    ↔ ∀ u ∈ 𝓝 (1 : G), ∀ᶠ i in p, ∀ a ∈ s, F i a / f a ∈ u :=
⟨λ h u hu, h _ ⟨u, hu, λ _, id⟩, λ h v ⟨u, hu, hv⟩,
  mem_of_superset (h u hu) (λ i hi a ha, hv (by exact hi a ha))⟩

@[to_additive] lemma topological_group.tendsto_locally_uniformly_iff
  {ι α : Type*} [topological_space α] (F : ι → α → G) (f : α → G) (p : filter ι) :
  @tendsto_locally_uniformly α G ι (topological_group.to_uniform_space G) _ F f p
    ↔ ∀ (u ∈ 𝓝 (1 : G)) (x : α), ∃ (t ∈ 𝓝 x), ∀ᶠ i in p, ∀ a ∈ t, F i a / f a ∈ u :=
⟨λ h u hu, h _ ⟨u, hu, λ _, id⟩, λ h v ⟨u, hu, hv⟩ x, exists_imp_exists (by exact λ a,
  exists_imp_exists (λ ha hp, mem_of_superset hp (λ i hi a ha, hv (by exact hi a ha)))) (h u hu x)⟩

@[to_additive] lemma topological_group.tendsto_locally_uniformly_on_iff
  {ι α : Type*} [topological_space α] (F : ι → α → G) (f : α → G) (p : filter ι) (s : set α) :
  @tendsto_locally_uniformly_on α G ι (topological_group.to_uniform_space G) _ F f p s
    ↔ ∀ (u ∈ 𝓝 (1 : G)) (x ∈ s), ∃ (t ∈ 𝓝[s] x), ∀ᶠ i in p, ∀ a ∈ t, F i a / f a ∈ u :=
⟨λ h u hu, h _ ⟨u, hu, λ _, id⟩, λ h v ⟨u, hu, hv⟩ x, exists_imp_exists (by exact λ a,
  exists_imp_exists (λ ha hp, mem_of_superset hp (λ i hi a ha, hv (by exact hi a ha)))) ∘ h u hu x⟩

end topological_comm_group

section topological_comm_group
universes u v w x
open filter

variables (G : Type*) [comm_group G] [topological_space G] [topological_group G]

section
local attribute [instance] topological_group.to_uniform_space

@[to_additive] lemma uniformity_eq_comap_nhds_one' :
  𝓤 G = comap (λp:G×G, p.2 / p.1) (𝓝 (1 : G)) := rfl

variable {G}
@[to_additive] lemma topological_group_is_uniform : uniform_group G :=
have tendsto
    ((λp:(G×G), p.1 / p.2) ∘ (λp:(G×G)×(G×G), (p.1.2 / p.1.1, p.2.2 / p.2.1)))
    (comap (λp:(G×G)×(G×G), (p.1.2 / p.1.1, p.2.2 / p.2.1)) ((𝓝 1).prod (𝓝 1)))
    (𝓝 (1 / 1)) :=
  (tendsto_fst.div' tendsto_snd).comp tendsto_comap,
begin
  constructor,
  rw [uniform_continuous, uniformity_prod_eq_prod, tendsto_map'_iff,
    uniformity_eq_comap_nhds_one' G, tendsto_comap_iff, prod_comap_comap_eq],
  simpa [(∘), div_eq_mul_inv, mul_comm, mul_left_comm] using this
end

open set

@[to_additive] lemma topological_group.t2_space_iff_one_closed :
  t2_space G ↔ is_closed ({1} : set G) :=
begin
  haveI : uniform_group G := topological_group_is_uniform,
  rw [← separated_iff_t2, separated_space_iff, ← closure_eq_iff_is_closed],
  split; intro h,
  { apply subset.antisymm,
    { intros x x_in,
      have := group_separation_rel x 1,
      rw div_one at this,
      rw [← this, h] at x_in,
      change x = 1 at x_in,
      simp [x_in] },
    { exact subset_closure } },
  { ext p,
    cases p with x y,
    rw [group_separation_rel x, h, mem_singleton_iff, div_eq_one],
    refl }
end

@[to_additive] lemma topological_group.t2_space_of_one_sep
  (H : ∀ x : G, x ≠ 1 → ∃ U ∈ nhds (1 : G), x ∉ U) : t2_space G :=
begin
  rw [topological_group.t2_space_iff_one_closed, ← is_open_compl_iff, is_open_iff_mem_nhds],
  intros x x_not,
  have : x ≠ 1, from mem_compl_singleton_iff.mp x_not,
  rcases H x this with ⟨U, U_in, xU⟩,
  rw ← nhds_one_symm G at U_in,
  rcases U_in with ⟨W, W_in, UW⟩,
  rw ← nhds_translation_mul_inv,
  use [W, W_in],
  rw subset_compl_comm,
  suffices : x⁻¹ ∉ W, by simpa,
  exact λ h, xU (UW h)
end

end

@[to_additive] lemma uniform_group.to_uniform_space_eq {G : Type*} [u : uniform_space G]
  [comm_group G] [uniform_group G] : topological_group.to_uniform_space G = u :=
begin
  ext : 1,
  show @uniformity G (topological_group.to_uniform_space G) = 𝓤 G,
  rw [uniformity_eq_comap_nhds_one' G, uniformity_eq_comap_nhds_one G]
end

end topological_comm_group

open comm_group filter set function

section
variables {α : Type*} {β : Type*} {hom : Type*}
variables [topological_space α] [comm_group α] [topological_group α]

-- β is a dense subgroup of α, inclusion is denoted by e
variables [topological_space β] [comm_group β]
variables [monoid_hom_class hom β α] {e : hom} (de : dense_inducing e)
include de

@[to_additive] lemma tendsto_div_comap_self (x₀ : α) :
  tendsto (λt:β×β, t.2 / t.1) (comap (λp:β×β, (e p.1, e p.2)) $ 𝓝 (x₀, x₀)) (𝓝 1) :=
begin
  have comm : (λx:α×α, x.2/x.1) ∘ (λt:β×β, (e t.1, e t.2)) = e ∘ (λt:β×β, t.2 / t.1),
  { ext t,
    change e t.2 / e t.1 = e (t.2 / t.1),
    rwa ← map_div e t.2 t.1 },
  have lim : tendsto (λ x : α × α, x.2/x.1) (𝓝 (x₀, x₀)) (𝓝 (e 1)),
  { simpa using (continuous_div'.comp (@continuous_swap α α _ _)).tendsto (x₀, x₀) },
  simpa using de.tendsto_comap_nhds_nhds lim comm
end
end

namespace dense_inducing
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables {G : Type*}

-- β is a dense subgroup of α, inclusion is denoted by e
-- δ is a dense subgroup of γ, inclusion is denoted by f
variables [topological_space α] [add_comm_group α] [topological_add_group α]
variables [topological_space β] [add_comm_group β] [topological_add_group β]
variables [topological_space γ] [add_comm_group γ] [topological_add_group γ]
variables [topological_space δ] [add_comm_group δ] [topological_add_group δ]
variables [uniform_space G] [add_comm_group G] [uniform_add_group G] [separated_space G]
  [complete_space G]
variables {e : β →+ α} (de : dense_inducing e)
variables {f : δ →+ γ} (df : dense_inducing f)

variables {φ : β →+ δ →+ G}
local notation `Φ` := λ p : β × δ, φ p.1 p.2

variables  (hφ : continuous Φ)

include de df hφ

variables {W' : set G} (W'_nhd : W' ∈ 𝓝 (0 : G))
include W'_nhd

private lemma extend_Z_bilin_aux (x₀ : α) (y₁ : δ) :
  ∃ U₂ ∈ comap e (𝓝 x₀), ∀ x x' ∈ U₂, Φ (x' - x, y₁) ∈ W' :=
begin
  let Nx := 𝓝 x₀,
  let ee := λ u : β × β, (e u.1, e u.2),

  have lim1 : tendsto (λ a : β × β, (a.2 - a.1, y₁)) (comap e Nx ×ᶠ comap e Nx) (𝓝 (0, y₁)),
  { have := tendsto.prod_mk (tendsto_sub_comap_self de x₀)
      (tendsto_const_nhds : tendsto (λ (p : β × β), y₁) (comap ee $ 𝓝 (x₀, x₀)) (𝓝 y₁)),
    rw [nhds_prod_eq, prod_comap_comap_eq, ←nhds_prod_eq],
    exact (this : _) },
  have lim2 : tendsto Φ (𝓝 (0, y₁)) (𝓝 0), by simpa using hφ.tendsto (0, y₁),
  have lim := lim2.comp lim1,
  rw tendsto_prod_self_iff at lim,
  simp_rw ball_mem_comm,
  exact lim W' W'_nhd
end

private lemma extend_Z_bilin_key (x₀ : α) (y₀ : γ) :
  ∃ U ∈ comap e (𝓝 x₀), ∃ V ∈ comap f (𝓝 y₀),
    ∀ x x' ∈ U, ∀ y y' ∈ V, Φ (x', y') - Φ (x, y) ∈ W' :=
begin
  let Nx := 𝓝 x₀,
  let Ny := 𝓝 y₀,
  let dp := dense_inducing.prod de df,
  let ee := λ u : β × β, (e u.1, e u.2),
  let ff := λ u : δ × δ, (f u.1, f u.2),

  have lim_φ : filter.tendsto Φ (𝓝 (0, 0)) (𝓝 0),
  { simpa using hφ.tendsto (0, 0) },

  have lim_φ_sub_sub : tendsto (λ (p : (β × β) × (δ × δ)), Φ (p.1.2 - p.1.1, p.2.2 - p.2.1))
    ((comap ee $ 𝓝 (x₀, x₀)) ×ᶠ (comap ff $ 𝓝 (y₀, y₀))) (𝓝 0),
  { have lim_sub_sub :  tendsto (λ (p : (β × β) × δ × δ), (p.1.2 - p.1.1, p.2.2 - p.2.1))
      ((comap ee (𝓝 (x₀, x₀))) ×ᶠ (comap ff (𝓝 (y₀, y₀)))) (𝓝 0 ×ᶠ 𝓝 0),
    { have := filter.prod_mono (tendsto_sub_comap_self de x₀) (tendsto_sub_comap_self df y₀),
      rwa prod_map_map_eq at this },
    rw ← nhds_prod_eq at lim_sub_sub,
    exact tendsto.comp lim_φ lim_sub_sub },

  rcases exists_nhds_zero_quarter W'_nhd with ⟨W, W_nhd, W4⟩,

  have : ∃ U₁ ∈ comap e (𝓝 x₀), ∃ V₁ ∈ comap f (𝓝 y₀),
    ∀ x x' ∈ U₁, ∀ y y' ∈ V₁,  Φ (x'-x, y'-y) ∈ W,
  { have := tendsto_prod_iff.1 lim_φ_sub_sub W W_nhd,
    repeat { rw [nhds_prod_eq, ←prod_comap_comap_eq] at this },
    rcases this with ⟨U, U_in, V, V_in, H⟩,
    rw [mem_prod_same_iff] at U_in V_in,
    rcases U_in with ⟨U₁, U₁_in, HU₁⟩,
    rcases V_in with ⟨V₁, V₁_in, HV₁⟩,
    existsi [U₁, U₁_in, V₁, V₁_in],
    intros x x_in x' x'_in y y_in y' y'_in,
    exact H _ _ (HU₁ (mk_mem_prod x_in x'_in)) (HV₁ (mk_mem_prod y_in y'_in)) },
  rcases this with ⟨U₁, U₁_nhd, V₁, V₁_nhd, H⟩,

  obtain ⟨x₁, x₁_in⟩ : U₁.nonempty :=
    ((de.comap_nhds_ne_bot _).nonempty_of_mem U₁_nhd),
  obtain ⟨y₁, y₁_in⟩ : V₁.nonempty :=
    ((df.comap_nhds_ne_bot _).nonempty_of_mem V₁_nhd),

  have cont_flip : continuous (λ p : δ × β, φ.flip p.1 p.2),
  { show continuous (Φ ∘ prod.swap), from hφ.comp continuous_swap },
  rcases (extend_Z_bilin_aux de df hφ W_nhd x₀ y₁) with ⟨U₂, U₂_nhd, HU⟩,
  rcases (extend_Z_bilin_aux df de cont_flip W_nhd y₀ x₁) with ⟨V₂, V₂_nhd, HV⟩,

  existsi [U₁ ∩ U₂, inter_mem U₁_nhd U₂_nhd,
            V₁ ∩ V₂, inter_mem V₁_nhd V₂_nhd],

  rintros x ⟨xU₁, xU₂⟩ x' ⟨x'U₁, x'U₂⟩ y ⟨yV₁, yV₂⟩ y' ⟨y'V₁, y'V₂⟩,
  have key_formula : φ x' y' - φ x y =
    φ(x' - x) y₁ + φ (x' - x) (y' - y₁) + φ x₁ (y' - y) + φ (x - x₁) (y' - y),
  { simp, abel },
  rw key_formula,
  have h₁ := HU x xU₂ x' x'U₂,
  have h₂ := H x xU₁ x' x'U₁ y₁ y₁_in y' y'V₁,
  have h₃ := HV y yV₂ y' y'V₂,
  have h₄ := H x₁ x₁_in x xU₁ y yV₁ y' y'V₁,
  exact W4 h₁ h₂ h₃ h₄
end

omit W'_nhd

open dense_inducing

/-- Bourbaki GT III.6.5 Theorem I:
ℤ-bilinear continuous maps from dense images into a complete Hausdorff group extend by continuity.
Note: Bourbaki assumes that α and β are also complete Hausdorff, but this is not necessary. -/
theorem extend_Z_bilin  : continuous (extend (de.prod df) Φ) :=
begin
  refine continuous_extend_of_cauchy _ _,
  rintro ⟨x₀, y₀⟩,
  split,
  { apply ne_bot.map,
    apply comap_ne_bot,

    intros U h,
    rcases mem_closure_iff_nhds.1 ((de.prod df).dense (x₀, y₀)) U h with ⟨x, x_in, ⟨z, z_x⟩⟩,
    existsi z,
    cc },
  { suffices : map (λ (p : (β × δ) × (β × δ)), Φ p.2 - Φ p.1)
      (comap (λ (p : (β × δ) × β × δ), ((e p.1.1, f p.1.2), (e p.2.1, f p.2.2)))
         (𝓝 (x₀, y₀) ×ᶠ 𝓝 (x₀, y₀))) ≤ 𝓝 0,
    by rwa [uniformity_eq_comap_nhds_zero G, prod_map_map_eq, ←map_le_iff_le_comap, filter.map_map,
        prod_comap_comap_eq],

    intros W' W'_nhd,

    have key := extend_Z_bilin_key de df hφ W'_nhd x₀ y₀,
    rcases key with ⟨U, U_nhd, V, V_nhd, h⟩,
    rw mem_comap at U_nhd,
    rcases U_nhd with ⟨U', U'_nhd, U'_sub⟩,
    rw mem_comap at V_nhd,
    rcases V_nhd with ⟨V', V'_nhd, V'_sub⟩,

    rw [mem_map, mem_comap, nhds_prod_eq],
    existsi (U' ×ˢ V') ×ˢ (U' ×ˢ V'),
    rw mem_prod_same_iff,

    simp only [exists_prop],
    split,
    { change U' ∈ 𝓝 x₀ at U'_nhd,
      change V' ∈ 𝓝 y₀ at V'_nhd,
      have := prod_mem_prod U'_nhd V'_nhd,
      tauto },
    { intros p h',
      simp only [set.mem_preimage, set.prod_mk_mem_set_prod_eq] at h',
      rcases p with ⟨⟨x, y⟩, ⟨x', y'⟩⟩,
      apply h ; tauto } }
end
end dense_inducing
