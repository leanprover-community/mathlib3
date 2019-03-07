/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Theory of topological monoids, groups and rings.

TODO: generalize `topological_monoid` and `topological_add_monoid` to semigroups, or add a type class
`topological_operator α (*)`.
-/
import order.liminf_limsup
import algebra.big_operators algebra.group algebra.pi_instances
import data.set.intervals data.equiv.algebra
import topology.basic topology.continuity topology.uniform_space.basic

open classical set lattice filter topological_space
local attribute [instance] classical.prop_decidable

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section topological_monoid

/-- A topological monoid is a monoid in which the multiplication is continuous as a function
`α × α → α`. -/
class topological_monoid (α : Type u) [topological_space α] [monoid α] : Prop :=
(continuous_mul : continuous (λp:α×α, p.1 * p.2))

/-- A topological (additive) monoid is a monoid in which the addition is
  continuous as a function `α × α → α`. -/
class topological_add_monoid (α : Type u) [topological_space α] [add_monoid α] : Prop :=
(continuous_add : continuous (λp:α×α, p.1 + p.2))

attribute [to_additive topological_add_monoid] topological_monoid
attribute [to_additive topological_add_monoid.mk] topological_monoid.mk
attribute [to_additive topological_add_monoid.continuous_add] topological_monoid.continuous_mul

section
variables [topological_space α] [monoid α] [topological_monoid α]

@[to_additive continuous_add']
lemma continuous_mul' : continuous (λp:α×α, p.1 * p.2) :=
topological_monoid.continuous_mul α

@[to_additive continuous_add]
lemma continuous_mul [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x * g x) :=
(hf.prod_mk hg).comp continuous_mul'

-- @[to_additive continuous_smul]
lemma continuous_pow : ∀ n : ℕ, continuous (λ a : α, a ^ n)
| 0 := by simpa using continuous_const
| (k+1) := show continuous (λ (a : α), a * a ^ k), from continuous_mul continuous_id (continuous_pow _)

@[to_additive tendsto_add']
lemma tendsto_mul' {a b : α} : tendsto (λp:α×α, p.fst * p.snd) (nhds (a, b)) (nhds (a * b)) :=
continuous_iff_continuous_at.mp (topological_monoid.continuous_mul α) (a, b)

@[to_additive tendsto_add]
lemma tendsto_mul {f : β → α} {g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) :
  tendsto (λx, f x * g x) x (nhds (a * b)) :=
(hf.prod_mk hg).comp (by rw [←nhds_prod_eq]; exact tendsto_mul')

@[to_additive tendsto_list_sum]
lemma tendsto_list_prod {f : γ → β → α} {x : filter β} {a : γ → α} :
  ∀l:list γ, (∀c∈l, tendsto (f c) x (nhds (a c))) →
    tendsto (λb, (l.map (λc, f c b)).prod) x (nhds ((l.map a).prod))
| []       _ := by simp [tendsto_const_nhds]
| (f :: l) h :=
  begin
    simp,
    exact tendsto_mul
      (h f (list.mem_cons_self _ _))
      (tendsto_list_prod l (assume c hc, h c (list.mem_cons_of_mem _ hc)))
  end

@[to_additive continuous_list_sum]
lemma continuous_list_prod [topological_space β] {f : γ → β → α} (l : list γ)
  (h : ∀c∈l, continuous (f c)) :
  continuous (λa, (l.map (λc, f c a)).prod) :=
continuous_iff_continuous_at.2 $ assume x, tendsto_list_prod l $ assume c hc,
  continuous_iff_continuous_at.1 (h c hc) x

@[to_additive prod.topological_add_monoid]
instance [topological_space β] [monoid β] [topological_monoid β] : topological_monoid (α × β) :=
⟨continuous.prod_mk
  (continuous_mul (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst))
  (continuous_mul (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)) ⟩

attribute [instance] prod.topological_add_monoid

end

section
variables [topological_space α] [comm_monoid α] [topological_monoid α]

@[to_additive tendsto_multiset_sum]
lemma tendsto_multiset_prod {f : γ → β → α} {x : filter β} {a : γ → α} (s : multiset γ) :
  (∀c∈s, tendsto (f c) x (nhds (a c))) →
    tendsto (λb, (s.map (λc, f c b)).prod) x (nhds ((s.map a).prod)) :=
by { rcases s with ⟨l⟩, simp, exact tendsto_list_prod l }

@[to_additive tendsto_finset_sum]
lemma tendsto_finset_prod {f : γ → β → α} {x : filter β} {a : γ → α} (s : finset γ) :
  (∀c∈s, tendsto (f c) x (nhds (a c))) → tendsto (λb, s.prod (λc, f c b)) x (nhds (s.prod a)) :=
tendsto_multiset_prod _

@[to_additive continuous_multiset_sum]
lemma continuous_multiset_prod [topological_space β] {f : γ → β → α} (s : multiset γ) :
  (∀c∈s, continuous (f c)) → continuous (λa, (s.map (λc, f c a)).prod) :=
by { rcases s with ⟨l⟩, simp, exact continuous_list_prod l }

@[to_additive continuous_finset_sum]
lemma continuous_finset_prod [topological_space β] {f : γ → β → α} (s : finset γ) :
  (∀c∈s, continuous (f c)) → continuous (λa, s.prod (λc, f c a)) :=
continuous_multiset_prod _

end

end topological_monoid

section topological_group

/-- A topological group is a group in which the multiplication and inversion operations are
continuous. -/
class topological_group (α : Type*) [topological_space α] [group α]
  extends topological_monoid α : Prop :=
(continuous_inv : continuous (λa:α, a⁻¹))

/-- A topological (additive) group is a group in which the addition and negation operations are
continuous. -/
class topological_add_group (α : Type u) [topological_space α] [add_group α]
  extends topological_add_monoid α : Prop :=
(continuous_neg : continuous (λa:α, -a))

attribute [to_additive topological_add_group] topological_group
attribute [to_additive topological_add_group.mk] topological_group.mk
attribute [to_additive topological_add_group.continuous_neg] topological_group.continuous_inv
attribute [to_additive topological_add_group.to_topological_add_monoid] topological_group.to_topological_monoid

variables [topological_space α] [group α]

@[to_additive continuous_neg']
lemma continuous_inv' [topological_group α] : continuous (λx:α, x⁻¹) :=
topological_group.continuous_inv α

@[to_additive continuous_neg]
lemma continuous_inv [topological_group α] [topological_space β] {f : β → α}
  (hf : continuous f) : continuous (λx, (f x)⁻¹) :=
hf.comp continuous_inv'

@[to_additive tendsto_neg]
lemma tendsto_inv [topological_group α] {f : β → α} {x : filter β} {a : α}
  (hf : tendsto f x (nhds a)) : tendsto (λx, (f x)⁻¹) x (nhds a⁻¹) :=
hf.comp (continuous_iff_continuous_at.mp (topological_group.continuous_inv α) a)

@[to_additive prod.topological_add_group]
instance [topological_group α] [topological_space β] [group β] [topological_group β] :
  topological_group (α × β) :=
{ continuous_inv := continuous.prod_mk (continuous_inv continuous_fst) (continuous_inv continuous_snd) }

attribute [instance] prod.topological_add_group

protected def homeomorph.mul_left [topological_group α] (a : α) : α ≃ₜ α :=
{ continuous_to_fun  := continuous_mul continuous_const continuous_id,
  continuous_inv_fun := continuous_mul continuous_const continuous_id,
  .. equiv.mul_left a }
attribute [to_additive homeomorph.add_left._proof_1] homeomorph.mul_left._proof_1
attribute [to_additive homeomorph.add_left._proof_2] homeomorph.mul_left._proof_2
attribute [to_additive homeomorph.add_left._proof_3] homeomorph.mul_left._proof_3
attribute [to_additive homeomorph.add_left._proof_4] homeomorph.mul_left._proof_4
attribute [to_additive homeomorph.add_left] homeomorph.mul_left

@[to_additive is_open_map_add_left]
lemma is_open_map_mul_left [topological_group α] (a : α) : is_open_map (λ x, a * x) :=
(homeomorph.mul_left a).is_open_map

protected def homeomorph.mul_right
  {α : Type*} [topological_space α] [group α] [topological_group α] (a : α) :
  α ≃ₜ α :=
{ continuous_to_fun  := continuous_mul continuous_id continuous_const,
  continuous_inv_fun := continuous_mul continuous_id continuous_const,
  .. equiv.mul_right a }
attribute [to_additive homeomorph.add_right._proof_1] homeomorph.mul_right._proof_1
attribute [to_additive homeomorph.add_right._proof_2] homeomorph.mul_right._proof_2
attribute [to_additive homeomorph.add_right._proof_3] homeomorph.mul_right._proof_3
attribute [to_additive homeomorph.add_right._proof_4] homeomorph.mul_right._proof_4
attribute [to_additive homeomorph.add_right] homeomorph.mul_right

@[to_additive is_open_map_add_right]
lemma is_open_map_mul_right [topological_group α] (a : α) : is_open_map (λ x, x * a) :=
(homeomorph.mul_right a).is_open_map

protected def homeomorph.inv (α : Type*) [topological_space α] [group α] [topological_group α] :
  α ≃ₜ α :=
{ continuous_to_fun  := continuous_inv',
  continuous_inv_fun := continuous_inv',
  .. equiv.inv α }
attribute [to_additive homeomorph.inv._proof_1] homeomorph.inv._proof_1
attribute [to_additive homeomorph.inv._proof_2] homeomorph.inv._proof_2
attribute [to_additive homeomorph.inv] homeomorph.inv

@[to_additive exists_nhds_half]
lemma exists_nhds_split [topological_group α] {s : set α} (hs : s ∈ (nhds (1 : α)).sets) :
  ∃ V ∈ (nhds (1 : α)).sets, ∀ v w ∈ V, v * w ∈ s :=
begin
  have : ((λa:α×α, a.1 * a.2) ⁻¹' s) ∈ (nhds ((1, 1) : α × α)).sets :=
    tendsto_mul' (by simpa using hs),
  rw nhds_prod_eq at this,
  rcases mem_prod_iff.1 this with ⟨V₁, H₁, V₂, H₂, H⟩,
  exact ⟨V₁ ∩ V₂, inter_mem_sets H₁ H₂, assume v w ⟨hv, _⟩ ⟨_, hw⟩, @H (v, w) ⟨hv, hw⟩⟩
end

@[to_additive exists_nhds_half_neg]
lemma exists_nhds_split_inv [topological_group α] {s : set α} (hs : s ∈ (nhds (1 : α)).sets) :
  ∃ V ∈ (nhds (1 : α)).sets, ∀ v w ∈ V, v * w⁻¹ ∈ s :=
begin
  have : tendsto (λa:α×α, a.1 * (a.2)⁻¹) ((nhds (1:α)).prod (nhds (1:α))) (nhds 1),
  { simpa using tendsto_mul (@tendsto_fst α α (nhds 1) (nhds 1)) (tendsto_inv tendsto_snd) },
  have : ((λa:α×α, a.1 * (a.2)⁻¹) ⁻¹' s) ∈ ((nhds (1:α)).prod (nhds (1:α))).sets :=
    this (by simpa using hs),
  rcases mem_prod_iff.1 this with ⟨V₁, H₁, V₂, H₂, H⟩,
  exact ⟨V₁ ∩ V₂, inter_mem_sets H₁ H₂, assume v w ⟨hv, _⟩ ⟨_, hw⟩, @H (v, w) ⟨hv, hw⟩⟩
end

@[to_additive exists_nhds_quarter]
lemma exists_nhds_split4 [topological_group α] {u : set α} (hu : u ∈ (nhds (1 : α)).sets) :
  ∃ V ∈ (nhds (1 : α)).sets, ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v * w * s * t ∈ u :=
begin
  rcases exists_nhds_split hu with ⟨W, W_nhd, h⟩,
  rcases exists_nhds_split W_nhd with ⟨V, V_nhd, h'⟩,
  existsi [V, V_nhd],
  intros v w s t v_in w_in s_in t_in,
  simpa [mul_assoc] using h _ _ (h' v w v_in w_in) (h' s t s_in t_in)
end

section
variable (α)
@[to_additive nhds_zero_symm]
lemma nhds_one_symm [topological_group α] : comap (λr:α, r⁻¹) (nhds (1 : α)) = nhds (1 : α) :=
begin
  have lim : tendsto (λr:α, r⁻¹) (nhds 1) (nhds 1),
  { simpa using tendsto_inv (@tendsto_id α (nhds 1)) },
  refine comap_eq_of_inverse _ _ lim lim,
  { funext x, simp },
end
end

@[to_additive nhds_translation_add_neg]
lemma nhds_translation_mul_inv [topological_group α] (x : α) :
  comap (λy:α, y * x⁻¹) (nhds 1) = nhds x :=
begin
  refine comap_eq_of_inverse (λy:α, y * x) _ _ _,
  { funext x; simp },
  { suffices : tendsto (λy:α, y * x⁻¹) (nhds x) (nhds (x * x⁻¹)), { simpa },
    exact tendsto_mul tendsto_id tendsto_const_nhds },
  { suffices : tendsto (λy:α, y * x) (nhds 1) (nhds (1 * x)), { simpa },
    exact tendsto_mul tendsto_id tendsto_const_nhds }
end

end topological_group

section topological_add_group
variables [topological_space α] [add_group α]

lemma continuous_sub [topological_add_group α] [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λx, f x - g x) :=
by simp; exact continuous_add hf (continuous_neg hg)

lemma continuous_sub' [topological_add_group α] : continuous (λp:α×α, p.1 - p.2) :=
continuous_sub continuous_fst continuous_snd

lemma tendsto_sub [topological_add_group α] {f : β → α} {g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) : tendsto (λx, f x - g x) x (nhds (a - b)) :=
by simp; exact tendsto_add hf (tendsto_neg hg)

lemma nhds_translation [topological_add_group α] (x : α) : comap (λy:α, y - x) (nhds 0) = nhds x :=
nhds_translation_add_neg x

end topological_add_group

section uniform_add_group
/-- A uniform (additive) group is a group in which the addition and negation are
  uniformly continuous. -/
class uniform_add_group (α : Type u) [uniform_space α] [add_group α] : Prop :=
(uniform_continuous_sub : uniform_continuous (λp:α×α, p.1 - p.2))

theorem uniform_add_group.mk' {α} [uniform_space α] [add_group α]
  (h₁ : uniform_continuous (λp:α×α, p.1 + p.2))
  (h₂ : uniform_continuous (λp:α, -p)) : uniform_add_group α :=
⟨(uniform_continuous_fst.prod_mk (uniform_continuous_snd.comp h₂)).comp h₁⟩

variables [uniform_space α] [add_group α] [uniform_add_group α]

lemma uniform_continuous_sub' : uniform_continuous (λp:α×α, p.1 - p.2) :=
uniform_add_group.uniform_continuous_sub α

lemma uniform_continuous_sub [uniform_space β] {f : β → α} {g : β → α}
  (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous (λx, f x - g x) :=
(hf.prod_mk hg).comp uniform_continuous_sub'

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
    (uniform_continuous_snd.comp uniform_continuous_fst))
  (uniform_continuous_sub
    (uniform_continuous_fst.comp uniform_continuous_snd)
    (uniform_continuous_snd.comp uniform_continuous_snd)) ⟩

lemma uniformity_translate (a : α) : uniformity.map (λx:α×α, (x.1 + a, x.2 + a)) = uniformity :=
le_antisymm
  (uniform_continuous_add uniform_continuous_id uniform_continuous_const)
  (calc uniformity =
    (uniformity.map (λx:α×α, (x.1 + -a, x.2 + -a))).map (λx:α×α, (x.1 + a, x.2 + a)) :
      by simp [filter.map_map, (∘)]; exact filter.map_id.symm
    ... ≤ uniformity.map (λx:α×α, (x.1 + a, x.2 + a)) :
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
lemma uniformity_eq_comap_nhds_zero : uniformity = comap (λx:α×α, x.2 - x.1) (nhds (0:α)) :=
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
show (x, y) ∈ ⋂₀ uniformity.sets ↔ x - y ∈ closure ({0} : set α),
begin
  rw [this.closure_eq_preimage_closure_image, uniformity_eq_comap_nhds_zero α, sInter_comap_sets],
  simp [mem_closure_iff_nhds, inter_singleton_eq_empty]
end

lemma uniform_continuous_of_tendsto_zero [uniform_space β] [add_group β] [uniform_add_group β]
  {f : α → β} [is_add_group_hom f] (h : tendsto f (nhds 0) (nhds 0)) :
  uniform_continuous f :=
begin
  have : ((λx:β×β, x.2 - x.1) ∘ (λx:α×α, (f x.1, f x.2))) = (λx:α×α, f (x.2 - x.1)),
  { simp only [is_add_group_hom.sub f] },
  rw [uniform_continuous, uniformity_eq_comap_nhds_zero α, uniformity_eq_comap_nhds_zero β,
    tendsto_comap_iff, this],
  exact tendsto.comp tendsto_comap h
end

lemma uniform_continuous_of_continuous [uniform_space β] [add_group β] [uniform_add_group β]
  {f : α → β} [is_add_group_hom f] (h : continuous f) :
  uniform_continuous f :=
uniform_continuous_of_tendsto_zero $
  suffices tendsto f (nhds 0) (nhds (f 0)), by rwa [is_add_group_hom.zero f] at this,
  h.tendsto 0

end uniform_add_group

section topological_ring
universe u'
variables (α) [topological_space α]

/-- A topological semiring is a semiring where addition and multiplication are continuous. -/
class topological_semiring [semiring α]
  extends topological_add_monoid α, topological_monoid α : Prop

variables [ring α]

/-- A topological ring is a ring where the ring operations are continuous. -/
class topological_ring extends topological_add_monoid α, topological_monoid α : Prop :=
(continuous_neg : continuous (λa:α, -a))

variables [t : topological_ring α]
instance topological_ring.to_topological_semiring : topological_semiring α := {..t}

instance topological_ring.to_topological_add_group : topological_add_group α := {..t}
end topological_ring

section topological_comm_ring
universe u'
variables [topological_space α] [comm_ring α] [topological_ring α]

def ideal.closure (S : ideal α) : ideal α :=
{ carrier := closure S,
  zero := subset_closure S.zero_mem,
  add  := assume x y hx hy,
    mem_closure2 continuous_add' hx hy $ assume a b, S.add_mem,
  smul  := assume c x hx,
    have continuous (λx:α, c * x) := continuous_mul continuous_const continuous_id,
    mem_closure this hx $ assume a, S.mul_mem_left }

@[simp] lemma ideal.coe_closure (S : ideal α) :
  (S.closure : set α) = closure S := rfl

end topological_comm_ring

/-- (Partially) ordered topology
Also called: partially ordered spaces (pospaces).

Usually ordered topology is used for a topology on linear ordered spaces, where the open intervals
are open sets. This is a generalization as for each linear order where open interals are open sets,
the order relation is closed. -/
class ordered_topology (α : Type*) [t : topological_space α] [preorder α] : Prop :=
(is_closed_le' : is_closed (λp:α×α, p.1 ≤ p.2))

instance {α : Type*} : Π [topological_space α], topological_space (order_dual α) := id

section ordered_topology

section preorder
variables [topological_space α] [preorder α] [t : ordered_topology α]
include t

lemma is_closed_le [topological_space β] {f g : β → α} (hf : continuous f) (hg : continuous g) :
  is_closed {b | f b ≤ g b} :=
continuous_iff_is_closed.mp (hf.prod_mk hg) _ t.is_closed_le'

lemma is_closed_le' (a : α) : is_closed {b | b ≤ a} :=
is_closed_le continuous_id continuous_const

lemma is_closed_ge' (a : α) : is_closed {b | a ≤ b} :=
is_closed_le continuous_const continuous_id

instance : ordered_topology (order_dual α) :=
⟨continuous_swap _ (@ordered_topology.is_closed_le' α _ _ _)⟩

lemma is_closed_Icc {a b : α} : is_closed (Icc a b) :=
is_closed_inter (is_closed_ge' a) (is_closed_le' b)

lemma le_of_tendsto_of_tendsto {f g : β → α} {b : filter β} {a₁ a₂ : α} (hb : b ≠ ⊥)
  (hf : tendsto f b (nhds a₁)) (hg : tendsto g b (nhds a₂)) (h : {b | f b ≤ g b} ∈ b.sets) :
  a₁ ≤ a₂ :=
have tendsto (λb, (f b, g b)) b (nhds (a₁, a₂)),
  by rw [nhds_prod_eq]; exact hf.prod_mk hg,
show (a₁, a₂) ∈ {p:α×α | p.1 ≤ p.2},
  from mem_of_closed_of_tendsto hb this t.is_closed_le' h

lemma le_of_tendsto {f : β → α} {a b : α} {x : filter β}
  (nt : x ≠ ⊥) (lim : tendsto f x (nhds a)) (h : f ⁻¹' {c | c ≤ b} ∈ x.sets) : a ≤ b :=
le_of_tendsto_of_tendsto nt lim tendsto_const_nhds h

lemma ge_of_tendsto {f : β → α} {a b : α} {x : filter β}
  (nt : x ≠ ⊥) (lim : tendsto f x (nhds a)) (h : f ⁻¹' {c | b ≤ c} ∈ x.sets) : b ≤ a :=
le_of_tendsto_of_tendsto nt tendsto_const_nhds lim h

@[simp] lemma closure_le_eq [topological_space β] {f g : β → α} (hf : continuous f) (hg : continuous g) :
  closure {b | f b ≤ g b} = {b | f b ≤ g b} :=
closure_eq_iff_is_closed.mpr $ is_closed_le hf hg
end preorder

section partial_order
variables [topological_space α] [partial_order α] [t : ordered_topology α]
include t

private lemma is_closed_eq : is_closed {p : α × α | p.1 = p.2} :=
by simp [le_antisymm_iff];
   exact is_closed_inter t.is_closed_le' (is_closed_le continuous_snd continuous_fst)

instance ordered_topology.to_t2_space : t2_space α :=
{ t2 :=
  have is_open {p : α × α | p.1 ≠ p.2}, from is_closed_eq,
  assume a b h,
  let ⟨u, v, hu, hv, ha, hb, h⟩ := is_open_prod_iff.mp this a b h in
  ⟨u, v, hu, hv, ha, hb,
    set.eq_empty_iff_forall_not_mem.2 $ assume a ⟨h₁, h₂⟩,
    have a ≠ a, from @h (a, a) ⟨h₁, h₂⟩,
    this rfl⟩ }

end partial_order

section linear_order
variables [topological_space α] [linear_order α] [t : ordered_topology α]
include t

lemma is_open_lt [topological_space β] {f g : β → α} (hf : continuous f) (hg : continuous g) :
  is_open {b | f b < g b} :=
by simp [lt_iff_not_ge, -not_le]; exact is_closed_le hg hf

lemma is_open_Ioo {a b : α} : is_open (Ioo a b) :=
is_open_and (is_open_lt continuous_const continuous_id) (is_open_lt continuous_id continuous_const)

lemma is_open_Iio {a : α} : is_open (Iio a) :=
is_open_lt continuous_id continuous_const

end linear_order

section decidable_linear_order
variables [topological_space α] [decidable_linear_order α] [t : ordered_topology α]
  [topological_space β] {f g : β → α}
include t

section
variables (hf : continuous f) (hg : continuous g)
include hf hg

lemma frontier_le_subset_eq : frontier {b | f b ≤ g b} ⊆ {b | f b = g b} :=
assume b ⟨hb₁, hb₂⟩,
le_antisymm
  (by simpa [closure_le_eq hf hg] using hb₁)
  (not_lt.1 $ assume hb : f b < g b,
    have {b | f b < g b} ⊆ interior {b | f b ≤ g b},
      from (subset_interior_iff_subset_of_open $ is_open_lt hf hg).mpr $ assume x, le_of_lt,
    have b ∈ interior {b | f b ≤ g b}, from this hb,
    by exact hb₂ this)

lemma frontier_lt_subset_eq : frontier {b | f b < g b} ⊆ {b | f b = g b} :=
by rw ← frontier_compl;
   convert frontier_le_subset_eq hg hf; simp [ext_iff, eq_comm]

lemma continuous_max : continuous (λb, max (f b) (g b)) :=
have ∀b∈frontier {b | f b ≤ g b}, g b = f b, from assume b hb, (frontier_le_subset_eq hf hg hb).symm,
continuous_if this hg hf

lemma continuous_min : continuous (λb, min (f b) (g b)) :=
have ∀b∈frontier {b | f b ≤ g b}, f b = g b, from assume b hb, frontier_le_subset_eq hf hg hb,
continuous_if this hf hg

end

lemma tendsto_max {b : filter β} {a₁ a₂ : α} (hf : tendsto f b (nhds a₁)) (hg : tendsto g b (nhds a₂)) :
  tendsto (λb, max (f b) (g b)) b (nhds (max a₁ a₂)) :=
show tendsto ((λp:α×α, max p.1 p.2) ∘ (λb, (f b, g b))) b (nhds (max a₁ a₂)),
  from (hf.prod_mk hg).comp
    begin
      rw [←nhds_prod_eq],
      from continuous_iff_continuous_at.mp (continuous_max continuous_fst continuous_snd) _
    end

lemma tendsto_min {b : filter β} {a₁ a₂ : α} (hf : tendsto f b (nhds a₁)) (hg : tendsto g b (nhds a₂)) :
  tendsto (λb, min (f b) (g b)) b (nhds (min a₁ a₂)) :=
show tendsto ((λp:α×α, min p.1 p.2) ∘ (λb, (f b, g b))) b (nhds (min a₁ a₂)),
  from (hf.prod_mk hg).comp
    begin
      rw [←nhds_prod_eq],
      from continuous_iff_continuous_at.mp (continuous_min continuous_fst continuous_snd) _
    end

end decidable_linear_order

end ordered_topology

/-- Topologies generated by the open intervals.

  This is restricted to linear orders. Only then it is guaranteed that they are also a ordered
  topology. -/
class orderable_topology (α : Type*) [t : topological_space α] [partial_order α] : Prop :=
(topology_eq_generate_intervals :
  t = generate_from {s | ∃a, s = {b : α | a < b} ∨ s = {b : α | b < a}})

section orderable_topology

instance {α : Type*} [topological_space α] [partial_order α] [orderable_topology α] :
  orderable_topology (order_dual α) :=
⟨by convert @orderable_topology.topology_eq_generate_intervals α _ _ _;
  conv in (_ ∨ _) { rw or.comm }; refl⟩

section partial_order
variables [topological_space α] [partial_order α] [t : orderable_topology α]
include t

lemma is_open_iff_generate_intervals {s : set α} :
  is_open s ↔ generate_open {s | ∃a, s = {b : α | a < b} ∨ s = {b : α | b < a}} s :=
by rw [t.topology_eq_generate_intervals]; refl

lemma is_open_lt' (a : α) : is_open {b:α | a < b} :=
by rw [@is_open_iff_generate_intervals α _ _ t]; exact generate_open.basic _ ⟨a, or.inl rfl⟩

lemma is_open_gt' (a : α) : is_open {b:α | b < a} :=
by rw [@is_open_iff_generate_intervals α _ _ t]; exact generate_open.basic _ ⟨a, or.inr rfl⟩

lemma lt_mem_nhds {a b : α} (h : a < b) : {b | a < b} ∈ (nhds b).sets :=
mem_nhds_sets (is_open_lt' _) h

lemma le_mem_nhds {a b : α} (h : a < b) : {b | a ≤ b} ∈ (nhds b).sets :=
(nhds b).sets_of_superset (lt_mem_nhds h) $ assume b hb, le_of_lt hb

lemma gt_mem_nhds {a b : α} (h : a < b) : {a | a < b} ∈ (nhds a).sets :=
mem_nhds_sets (is_open_gt' _) h

lemma ge_mem_nhds {a b : α} (h : a < b) : {a | a ≤ b} ∈ (nhds a).sets :=
(nhds a).sets_of_superset (gt_mem_nhds h) $ assume b hb, le_of_lt hb

lemma nhds_eq_orderable {a : α} :
  nhds a = (⨅b<a, principal {c | b < c}) ⊓ (⨅b>a, principal {c | c < b}) :=
by rw [t.topology_eq_generate_intervals, nhds_generate_from];
from le_antisymm
  (le_inf
    (le_infi $ assume b, le_infi $ assume hb,
      infi_le_of_le {c : α | b < c} $ infi_le _ ⟨hb, b, or.inl rfl⟩)
    (le_infi $ assume b, le_infi $ assume hb,
      infi_le_of_le {c : α | c < b} $ infi_le _ ⟨hb, b, or.inr rfl⟩))
  (le_infi $ assume s, le_infi $ assume ⟨ha, b, hs⟩,
    match s, ha, hs with
    | _, h, (or.inl rfl) := inf_le_left_of_le $ infi_le_of_le b $ infi_le _ h
    | _, h, (or.inr rfl) := inf_le_right_of_le $ infi_le_of_le b $ infi_le _ h
    end)

lemma tendsto_orderable {f : β → α} {a : α} {x : filter β} :
  tendsto f x (nhds a) ↔ (∀a'<a, {b | a' < f b} ∈ x.sets) ∧ (∀a'>a, {b | a' > f b} ∈ x.sets) :=
by simp [@nhds_eq_orderable α _ _, tendsto_inf, tendsto_infi, tendsto_principal]

/-- Also known as squeeze or sandwich theorem. -/
lemma tendsto_of_tendsto_of_tendsto_of_le_of_le {f g h : β → α} {b : filter β} {a : α}
  (hg : tendsto g b (nhds a)) (hh : tendsto h b (nhds a))
  (hgf : {b | g b ≤ f b} ∈ b.sets) (hfh : {b | f b ≤ h b} ∈ b.sets) :
  tendsto f b (nhds a) :=
tendsto_orderable.2
  ⟨assume a' h',
    have {b : β | a' < g b} ∈ b.sets, from (tendsto_orderable.1 hg).left a' h',
    by filter_upwards [this, hgf] assume a, lt_of_lt_of_le,
    assume a' h',
    have {b : β | h b < a'} ∈ b.sets, from (tendsto_orderable.1 hh).right a' h',
    by filter_upwards [this, hfh] assume a h₁ h₂, lt_of_le_of_lt h₂ h₁⟩

lemma nhds_orderable_unbounded {a : α} (hu : ∃u, a < u) (hl : ∃l, l < a) :
  nhds a = (⨅l (h₂ : l < a) u (h₂ : a < u), principal {x | l < x ∧ x < u }) :=
let ⟨u, hu⟩ := hu, ⟨l, hl⟩ := hl in
calc nhds a = (⨅b<a, principal {c | b < c}) ⊓ (⨅b>a, principal {c | c < b}) : nhds_eq_orderable
  ... = (⨅b<a, principal {c | b < c} ⊓ (⨅b>a, principal {c | c < b})) :
    binfi_inf hl
  ... = (⨅l<a, (⨅u>a, principal {c | c < u} ⊓ principal {c | l < c})) :
    begin
      congr, funext x,
      congr, funext hx,
      rw [inf_comm],
      apply binfi_inf hu
    end
  ... = _ : by simp [inter_comm]; refl

lemma tendsto_orderable_unbounded {f : β → α} {a : α} {x : filter β}
  (hu : ∃u, a < u) (hl : ∃l, l < a) (h : ∀l u, l < a → a < u → {b | l < f b ∧ f b < u } ∈ x.sets) :
  tendsto f x (nhds a) :=
by rw [nhds_orderable_unbounded hu hl];
from (tendsto_infi.2 $ assume l, tendsto_infi.2 $ assume hl,
  tendsto_infi.2 $ assume u, tendsto_infi.2 $ assume hu, tendsto_principal.2 $ h l u hl hu)

end partial_order

theorem induced_orderable_topology' {α : Type u} {β : Type v}
  [partial_order α] [ta : topological_space β] [partial_order β] [orderable_topology β]
  (f : α → β) (hf : ∀ {x y}, f x < f y ↔ x < y)
  (H₁ : ∀ {a x}, x < f a → ∃ b < a, x ≤ f b)
  (H₂ : ∀ {a x}, f a < x → ∃ b > a, f b ≤ x) :
  @orderable_topology _ (induced f ta) _ :=
begin
  letI := induced f ta,
  refine ⟨eq_of_nhds_eq_nhds (λ a, _)⟩,
  rw [nhds_induced_eq_comap, nhds_generate_from, @nhds_eq_orderable β _ _], apply le_antisymm,
  { rw [← map_le_iff_le_comap],
    refine le_inf _ _; refine le_infi (λ x, le_infi $ λ h, le_principal_iff.2 _); simp,
    { rcases H₁ h with ⟨b, ab, xb⟩,
      refine mem_infi_sets _ (mem_infi_sets ⟨ab, b, or.inl rfl⟩ (mem_principal_sets.2 _)),
      exact λ c hc, lt_of_le_of_lt xb (hf.2 hc) },
    { rcases H₂ h with ⟨b, ab, xb⟩,
      refine mem_infi_sets _ (mem_infi_sets ⟨ab, b, or.inr rfl⟩ (mem_principal_sets.2 _)),
      exact λ c hc, lt_of_lt_of_le (hf.2 hc) xb } },
  refine le_infi (λ s, le_infi $ λ hs, le_principal_iff.2 _),
  rcases hs with ⟨ab, b, rfl|rfl⟩,
  { exact mem_comap_sets.2 ⟨{x | f b < x},
      mem_inf_sets_of_left $ mem_infi_sets _ $ mem_infi_sets (hf.2 ab) $ mem_principal_self _,
      λ x, hf.1⟩ },
  { exact mem_comap_sets.2 ⟨{x | x < f b},
      mem_inf_sets_of_right $ mem_infi_sets _ $ mem_infi_sets (hf.2 ab) $ mem_principal_self _,
      λ x, hf.1⟩ }
end

theorem induced_orderable_topology {α : Type u} {β : Type v}
  [partial_order α] [ta : topological_space β] [partial_order β] [orderable_topology β]
  (f : α → β) (hf : ∀ {x y}, f x < f y ↔ x < y)
  (H : ∀ {x y}, x < y → ∃ a, x < f a ∧ f a < y) :
  @orderable_topology _ (induced f ta) _ :=
induced_orderable_topology' f @hf
  (λ a x xa, let ⟨b, xb, ba⟩ := H xa in ⟨b, hf.1 ba, le_of_lt xb⟩)
  (λ a x ax, let ⟨b, ab, bx⟩ := H ax in ⟨b, hf.1 ab, le_of_lt bx⟩)

lemma nhds_top_orderable [topological_space α] [order_top α] [orderable_topology α] :
  nhds (⊤:α) = (⨅l (h₂ : l < ⊤), principal {x | l < x}) :=
by rw [@nhds_eq_orderable α _ _]; simp [(>)]

lemma nhds_bot_orderable [topological_space α] [order_bot α] [orderable_topology α] :
  nhds (⊥:α) = (⨅l (h₂ : ⊥ < l), principal {x | x < l}) :=
by rw [@nhds_eq_orderable α _ _]; simp

section linear_order

variables [topological_space α] [linear_order α] [t : orderable_topology α]
include t

lemma mem_nhds_orderable_dest {a : α} {s : set α} (hs : s ∈ (nhds a).sets) :
  ((∃u, u>a) → ∃u, a < u ∧ ∀b, a ≤ b → b < u → b ∈ s) ∧
  ((∃l, l<a) → ∃l, l < a ∧ ∀b, l < b → b ≤ a → b ∈ s) :=
let ⟨t₁, ht₁, t₂, ht₂, hts⟩ :=
  mem_inf_sets.mp $ by rw [@nhds_eq_orderable α _ _ _] at hs; exact hs in
have ht₁ : ((∃l, l<a) → ∃l, l < a ∧ ∀b, l < b → b ∈ t₁) ∧ (∀b, a ≤ b → b ∈ t₁),
  from infi_sets_induct ht₁
    (by simp {contextual := tt})
    (assume a' s₁ s₂ hs₁ ⟨hs₂, hs₃⟩,
      begin
        by_cases a' < a,
        { simp [h] at hs₁,
          letI := classical.DLO α,
          exact ⟨assume hx, let ⟨u, hu₁, hu₂⟩ := hs₂ hx in
            ⟨max u a', max_lt hu₁ h, assume b hb,
              ⟨hs₁ $ lt_of_le_of_lt (le_max_right _ _) hb,
                hu₂ _ $ lt_of_le_of_lt (le_max_left _ _) hb⟩⟩,
            assume b hb, ⟨hs₁ $ lt_of_lt_of_le h hb, hs₃ _ hb⟩⟩ },
        { simp [h] at hs₁, simp [hs₁],
          exact ⟨by simpa using hs₂, hs₃⟩ }
      end)
    (assume s₁ s₂ h ih, and.intro
      (assume hx, let ⟨u, hu₁, hu₂⟩ := ih.left hx in ⟨u, hu₁, assume b hb, h $ hu₂ _ hb⟩)
      (assume b hb, h $ ih.right _ hb)),
have ht₂ : ((∃u, u>a) → ∃u, a < u ∧ ∀b, b < u → b ∈ t₂) ∧ (∀b, b ≤ a → b ∈ t₂),
  from infi_sets_induct ht₂
    (by simp {contextual := tt})
    (assume a' s₁ s₂ hs₁ ⟨hs₂, hs₃⟩,
      begin
        by_cases a' > a,
        { simp [h] at hs₁,
          letI := classical.DLO α,
          exact ⟨assume hx, let ⟨u, hu₁, hu₂⟩ := hs₂ hx in
            ⟨min u a', lt_min hu₁ h, assume b hb,
              ⟨hs₁ $ lt_of_lt_of_le hb (min_le_right _ _),
                hu₂ _ $ lt_of_lt_of_le hb (min_le_left _ _)⟩⟩,
            assume b hb, ⟨hs₁ $ lt_of_le_of_lt hb h, hs₃ _ hb⟩⟩ },
        { simp [h] at hs₁, simp [hs₁],
          exact ⟨by simpa using hs₂, hs₃⟩ }
      end)
    (assume s₁ s₂ h ih, and.intro
      (assume hx, let ⟨u, hu₁, hu₂⟩ := ih.left hx in ⟨u, hu₁, assume b hb, h $ hu₂ _ hb⟩)
      (assume b hb, h $ ih.right _ hb)),
and.intro
  (assume hx, let ⟨u, hu, h⟩ := ht₂.left hx in ⟨u, hu, assume b hb hbu, hts ⟨ht₁.right b hb, h _ hbu⟩⟩)
  (assume hx, let ⟨l, hl, h⟩ := ht₁.left hx in ⟨l, hl, assume b hbl hb, hts ⟨h _ hbl, ht₂.right b hb⟩⟩)

lemma mem_nhds_unbounded {a : α} {s : set α} (hu : ∃u, a < u) (hl : ∃l, l < a) :
  s ∈ (nhds a).sets ↔ (∃l u, l < a ∧ a < u ∧ ∀b, l < b → b < u → b ∈ s) :=
let ⟨l, hl'⟩ := hl, ⟨u, hu'⟩ := hu in
have nhds a = (⨅p : {l // l < a} × {u // a < u}, principal {x | p.1.val < x ∧ x < p.2.val }),
  by simp [nhds_orderable_unbounded hu hl, infi_subtype, infi_prod],
iff.intro
  (assume hs, by rw [this] at hs; from infi_sets_induct hs
    ⟨l, u, hl', hu', by simp⟩
    begin
      intro p, rcases p with ⟨⟨l, hl⟩, ⟨u, hu⟩⟩,
      simp [set.subset_def],
      intros s₁ s₂ hs₁ l' hl' u' hu' hs₂,
      letI := classical.DLO α,
      refine ⟨max l l', _, min u u', _⟩;
      simp [*, lt_min_iff, max_lt_iff] {contextual := tt}
    end
    (assume s₁ s₂ h ⟨l, u, h₁, h₂, h₃⟩, ⟨l, u, h₁, h₂, assume b hu hl, h $ h₃ _ hu hl⟩))
  (assume ⟨l, u, hl, hu, h⟩,
    by rw [this]; exact mem_infi_sets ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ (assume b ⟨h₁, h₂⟩, h b h₁ h₂))

lemma order_separated {a₁ a₂ : α} (h : a₁ < a₂) :
  ∃u v : set α, is_open u ∧ is_open v ∧ a₁ ∈ u ∧ a₂ ∈ v ∧ (∀b₁∈u, ∀b₂∈v, b₁ < b₂) :=
match dense_or_discrete h with
| or.inl ⟨a, ha₁, ha₂⟩ := ⟨{a' | a' < a}, {a' | a < a'}, is_open_gt' a, is_open_lt' a, ha₁, ha₂,
    assume b₁ h₁ b₂ h₂, lt_trans h₁ h₂⟩
| or.inr ⟨h₁, h₂⟩ := ⟨{a | a < a₂}, {a | a₁ < a}, is_open_gt' a₂, is_open_lt' a₁, h, h,
    assume b₁ hb₁ b₂ hb₂,
    calc b₁ ≤ a₁ : h₂ _ hb₁
      ... < a₂ : h
      ... ≤ b₂ : h₁ _ hb₂⟩
end

instance orderable_topology.to_ordered_topology : ordered_topology α :=
{ is_closed_le' :=
    is_open_prod_iff.mpr $ assume a₁ a₂ (h : ¬ a₁ ≤ a₂),
      have h : a₂ < a₁, from lt_of_not_ge h,
      let ⟨u, v, hu, hv, ha₁, ha₂, h⟩ := order_separated h in
      ⟨v, u, hv, hu, ha₂, ha₁, assume ⟨b₁, b₂⟩ ⟨h₁, h₂⟩, not_le_of_gt $ h b₂ h₂ b₁ h₁⟩ }

instance orderable_topology.t2_space : t2_space α := by apply_instance

instance orderable_topology.regular_space : regular_space α :=
{ regular := assume s a hs ha,
    have -s ∈ (nhds a).sets, from mem_nhds_sets hs ha,
    let ⟨h₁, h₂⟩ := mem_nhds_orderable_dest this in
    have ∃t:set α, is_open t ∧ (∀l∈ s, l < a → l ∈ t) ∧ nhds a ⊓ principal t = ⊥,
      from by_cases
        (assume h : ∃l, l < a,
          let ⟨l, hl, h⟩ := h₂ h in
          match dense_or_discrete hl with
          | or.inl ⟨b, hb₁, hb₂⟩ := ⟨{a | a < b}, is_open_gt' _,
              assume c hcs hca, show c < b,
                from lt_of_not_ge $ assume hbc, h c (lt_of_lt_of_le hb₁ hbc) (le_of_lt hca) hcs,
              inf_principal_eq_bot $ (nhds a).sets_of_superset (mem_nhds_sets (is_open_lt' _) hb₂) $
                assume x (hx : b < x), show ¬ x < b, from not_lt.2 $ le_of_lt hx⟩
          | or.inr ⟨h₁, h₂⟩ := ⟨{a' | a' < a}, is_open_gt' _, assume b hbs hba, hba,
              inf_principal_eq_bot $ (nhds a).sets_of_superset (mem_nhds_sets (is_open_lt' _) hl) $
                assume x (hx : l < x), show ¬ x < a, from not_lt.2 $ h₁ _ hx⟩
          end)
        (assume : ¬ ∃l, l < a, ⟨∅, is_open_empty, assume l _ hl, (this ⟨l, hl⟩).elim,
          by rw [principal_empty, inf_bot_eq]⟩),
    let ⟨t₁, ht₁o, ht₁s, ht₁a⟩ := this in
    have ∃t:set α, is_open t ∧ (∀u∈ s, u>a → u ∈ t) ∧ nhds a ⊓ principal t = ⊥,
      from by_cases
        (assume h : ∃u, u > a,
          let ⟨u, hu, h⟩ := h₁ h in
          match dense_or_discrete hu with
          | or.inl ⟨b, hb₁, hb₂⟩ := ⟨{a | b < a}, is_open_lt' _,
              assume c hcs hca, show c > b,
                from lt_of_not_ge $ assume hbc, h c (le_of_lt hca) (lt_of_le_of_lt hbc hb₂) hcs,
              inf_principal_eq_bot $ (nhds a).sets_of_superset (mem_nhds_sets (is_open_gt' _) hb₁) $
                assume x (hx : b > x), show ¬ x > b, from not_lt.2 $ le_of_lt hx⟩
          | or.inr ⟨h₁, h₂⟩ := ⟨{a' | a' > a}, is_open_lt' _, assume b hbs hba, hba,
              inf_principal_eq_bot $ (nhds a).sets_of_superset (mem_nhds_sets (is_open_gt' _) hu) $
                assume x (hx : u > x), show ¬ x > a, from not_lt.2 $ h₂ _ hx⟩
          end)
        (assume : ¬ ∃u, u > a, ⟨∅, is_open_empty, assume l _ hl, (this ⟨l, hl⟩).elim,
          by rw [principal_empty, inf_bot_eq]⟩),
    let ⟨t₂, ht₂o, ht₂s, ht₂a⟩ := this in
    ⟨t₁ ∪ t₂, is_open_union ht₁o ht₂o,
      assume x hx,
      have x ≠ a, from assume eq, ha $ eq ▸ hx,
      (ne_iff_lt_or_gt.mp this).imp (ht₁s _ hx) (ht₂s _ hx),
      by rw [←sup_principal, inf_sup_left, ht₁a, ht₂a, bot_sup_eq]⟩,
  ..orderable_topology.t2_space }

end linear_order

lemma preimage_neg [add_group α] : preimage (has_neg.neg : α → α) = image (has_neg.neg : α → α) :=
(image_eq_preimage_of_inverse neg_neg neg_neg).symm

lemma filter.map_neg [add_group α] : map (has_neg.neg : α → α) = comap (has_neg.neg : α → α) :=
funext $ assume f, map_eq_comap_of_inverse (funext neg_neg) (funext neg_neg)

section topological_add_group

variables [topological_space α] [ordered_comm_group α] [orderable_topology α] [topological_add_group α]

lemma neg_preimage_closure {s : set α} : (λr:α, -r) ⁻¹' closure s = closure ((λr:α, -r) '' s) :=
have (λr:α, -r) ∘ (λr:α, -r) = id, from funext neg_neg,
by rw [preimage_neg]; exact
  (subset.antisymm (image_closure_subset_closure_image continuous_neg') $
    calc closure ((λ (r : α), -r) '' s) = (λr, -r) '' ((λr, -r) '' closure ((λ (r : α), -r) '' s)) :
        by rw [←image_comp, this, image_id]
      ... ⊆ (λr, -r) '' closure ((λr, -r) '' ((λ (r : α), -r) '' s)) :
        mono_image $ image_closure_subset_closure_image continuous_neg'
      ... = _ : by rw [←image_comp, this, image_id])

end topological_add_group

section order_topology

variables [topological_space α] [topological_space β]
  [linear_order α] [linear_order β] [orderable_topology α] [orderable_topology β]

lemma nhds_principal_ne_bot_of_is_lub {a : α} {s : set α} (ha : is_lub s a) (hs : s ≠ ∅) :
  nhds a ⊓ principal s ≠ ⊥ :=
let ⟨a', ha'⟩ := exists_mem_of_ne_empty hs in
forall_sets_neq_empty_iff_neq_bot.mp $ assume t ht,
  let ⟨t₁, ht₁, t₂, ht₂, ht⟩ := mem_inf_sets.mp ht in
  let ⟨hu, hl⟩ := mem_nhds_orderable_dest ht₁ in
  by_cases
    (assume h : a = a',
      have a ∈ t₁, from mem_of_nhds ht₁,
      have a ∈ t₂, from ht₂ $ by rwa [h],
      ne_empty_iff_exists_mem.mpr ⟨a, ht ⟨‹a ∈ t₁›, ‹a ∈ t₂›⟩⟩)
    (assume : a ≠ a',
      have a' < a, from lt_of_le_of_ne (ha.left _ ‹a' ∈ s›) this.symm,
      let ⟨l, hl, hlt₁⟩ := hl ⟨a', this⟩ in
      have ∃a'∈s, l < a',
        from classical.by_contradiction $ assume : ¬ ∃a'∈s, l < a',
          have ∀a'∈s, a' ≤ l, from assume a ha, not_lt.1 $ assume ha', this ⟨a, ha, ha'⟩,
          have ¬ l < a, from not_lt.2 $ ha.right _ this,
          this ‹l < a›,
      let ⟨a', ha', ha'l⟩ := this in
      have a' ∈ t₁, from hlt₁ _ ‹l < a'›  $ ha.left _ ha',
      ne_empty_iff_exists_mem.mpr ⟨a', ht ⟨‹a' ∈ t₁›, ht₂ ‹a' ∈ s›⟩⟩)

lemma nhds_principal_ne_bot_of_is_glb : ∀ {a : α} {s : set α}, is_glb s a → s ≠ ∅ →
  nhds a ⊓ principal s ≠ ⊥ :=
@nhds_principal_ne_bot_of_is_lub (order_dual α) _ _ _

lemma is_lub_of_mem_nhds {s : set α} {a : α} {f : filter α}
  (hsa : a ∈ upper_bounds s) (hsf : s ∈ f.sets) (hfa : f ⊓ nhds a ≠ ⊥) : is_lub s a :=
⟨hsa, assume b hb,
  not_lt.1 $ assume hba,
  have s ∩ {a | b < a} ∈ (f ⊓ nhds a).sets,
    from inter_mem_inf_sets hsf (mem_nhds_sets (is_open_lt' _) hba),
  let ⟨x, ⟨hxs, hxb⟩⟩ := inhabited_of_mem_sets hfa this in
  have b < b, from lt_of_lt_of_le hxb $ hb _ hxs,
  lt_irrefl b this⟩

lemma is_glb_of_mem_nhds : ∀ {s : set α} {a : α} {f : filter α},
  a ∈ lower_bounds s → s ∈ f.sets → f ⊓ nhds a ≠ ⊥ → is_glb s a :=
@is_lub_of_mem_nhds (order_dual α) _ _ _

lemma is_lub_of_is_lub_of_tendsto {f : α → β} {s : set α} {a : α} {b : β}
  (hf : ∀x∈s, ∀y∈s, x ≤ y → f x ≤ f y) (ha : is_lub s a) (hs : s ≠ ∅)
  (hb : tendsto f (nhds a ⊓ principal s) (nhds b)) : is_lub (f '' s) b :=
have hnbot : (nhds a ⊓ principal s) ≠ ⊥, from nhds_principal_ne_bot_of_is_lub ha hs,
have ∀a'∈s, ¬ b < f a',
  from assume a' ha' h,
  have {x | x < f a'} ∈ (nhds b).sets, from mem_nhds_sets (is_open_gt' _) h,
  let ⟨t₁, ht₁, t₂, ht₂, hs⟩ := mem_inf_sets.mp (hb this) in
  by_cases
    (assume h : a = a',
      have a ∈ t₁ ∩ t₂, from ⟨mem_of_nhds ht₁, ht₂ $ by rwa [h]⟩,
      have f a < f a', from hs this,
      lt_irrefl (f a') $ by rwa [h] at this)
    (assume h : a ≠ a',
      have a' < a, from lt_of_le_of_ne (ha.left _ ha') h.symm,
      have {x | a' < x} ∈ (nhds a).sets, from mem_nhds_sets (is_open_lt' _) this,
      have {x | a' < x} ∩ t₁ ∈ (nhds a).sets, from inter_mem_sets this ht₁,
      have ({x | a' < x} ∩ t₁) ∩ s ∈ (nhds a ⊓ principal s).sets,
        from inter_mem_inf_sets this (subset.refl s),
      let ⟨x, ⟨hx₁, hx₂⟩, hx₃⟩ := inhabited_of_mem_sets hnbot this in
      have hxa' : f x < f a', from hs ⟨hx₂, ht₂ hx₃⟩,
      have ha'x : f a' ≤ f x, from hf _ ha' _ hx₃ $ le_of_lt hx₁,
      lt_irrefl _ (lt_of_le_of_lt ha'x hxa')),
and.intro
  (assume b' ⟨a', ha', h_eq⟩, h_eq ▸ not_lt.1 $ this _ ha')
  (assume b' hb', le_of_tendsto hnbot hb $
      mem_inf_sets_of_right $ assume x hx, hb' _ $ mem_image_of_mem _ hx)

lemma is_glb_of_is_glb_of_tendsto {f : α → β} {s : set α} {a : α} {b : β}
  (hf : ∀x∈s, ∀y∈s, x ≤ y → f x ≤ f y) : is_glb s a → s ≠ ∅ →
  tendsto f (nhds a ⊓ principal s) (nhds b) → is_glb (f '' s) b :=
@is_lub_of_is_lub_of_tendsto (order_dual α) (order_dual β) _ _ _ _ _ _ f s a b
  (λ x hx y hy, hf y hy x hx)

lemma is_glb_of_is_lub_of_tendsto : ∀ {f : α → β} {s : set α} {a : α} {b : β},
  (∀x∈s, ∀y∈s, x ≤ y → f y ≤ f x) → is_lub s a → s ≠ ∅ →
  tendsto f (nhds a ⊓ principal s) (nhds b) → is_glb (f '' s) b :=
@is_lub_of_is_lub_of_tendsto α (order_dual β) _ _ _ _ _ _

lemma is_lub_of_is_glb_of_tendsto : ∀ {f : α → β} {s : set α} {a : α} {b : β},
  (∀x∈s, ∀y∈s, x ≤ y → f y ≤ f x) → is_glb s a → s ≠ ∅ →
  tendsto f (nhds a ⊓ principal s) (nhds b) → is_lub (f '' s) b :=
@is_glb_of_is_glb_of_tendsto α (order_dual β) _ _ _ _ _ _

lemma mem_closure_of_is_lub {a : α} {s : set α} (ha : is_lub s a) (hs : s ≠ ∅) : a ∈ closure s :=
by rw closure_eq_nhds; exact nhds_principal_ne_bot_of_is_lub ha hs

lemma mem_of_is_lub_of_is_closed {a : α} {s : set α} (ha : is_lub s a) (hs : s ≠ ∅) (sc : is_closed s): a ∈ s :=
by rw ←closure_eq_of_is_closed sc; exact mem_closure_of_is_lub ha hs

lemma mem_closure_of_is_glb {a : α} {s : set α} (ha : is_glb s a) (hs : s ≠ ∅) : a ∈ closure s :=
by rw closure_eq_nhds; exact nhds_principal_ne_bot_of_is_glb ha hs

lemma mem_of_is_glb_of_is_closed {a : α} {s : set α} (ha : is_glb s a) (hs : s ≠ ∅) (sc : is_closed s): a ∈ s :=
by rw ←closure_eq_of_is_closed sc; exact mem_closure_of_is_glb ha hs

/-- A compact set is bounded below -/
lemma bdd_below_of_compact {α : Type u} [topological_space α] [linear_order α]
  [ordered_topology α] [nonempty α] {s : set α} (hs : compact s) : bdd_below s :=
begin
  by_contra H,
  letI := classical.DLO α,
  rcases @compact_elim_finite_subcover_image α _ _ _ s (λ x, {b | x < b}) hs
    (λ x _, is_open_lt continuous_const continuous_id) _ with ⟨t, st, ft, ht⟩,
  { refine H ((bdd_below_finite ft).imp $ λ C hC y hy, _),
    rcases mem_bUnion_iff.1 (ht hy) with ⟨x, hx, xy⟩,
    exact le_trans (hC _ hx) (le_of_lt xy) },
  { refine λ x hx, mem_bUnion_iff.2 (not_imp_comm.1 _ H),
    exact λ h, ⟨x, λ y hy, le_of_not_lt (h.imp $ λ ys, ⟨_, hy, ys⟩)⟩ }
end

/-- A compact set is bounded above -/
lemma bdd_above_of_compact {α : Type u} [topological_space α] [linear_order α]
  [orderable_topology α] : Π [nonempty α] {s : set α}, compact s → bdd_above s :=
@bdd_below_of_compact (order_dual α) _ _ _

end order_topology


section complete_linear_order

variables [complete_linear_order α] [topological_space α] [orderable_topology α]
  [complete_linear_order β] [topological_space β] [orderable_topology β] [nonempty γ]

lemma Sup_mem_closure {α : Type u} [topological_space α] [complete_linear_order α] [orderable_topology α]
  {s : set α} (hs : s ≠ ∅) : Sup s ∈ closure s :=
mem_closure_of_is_lub is_lub_Sup hs

lemma Inf_mem_closure {α : Type u} [topological_space α] [complete_linear_order α] [orderable_topology α]
  {s : set α} (hs : s ≠ ∅) : Inf s ∈ closure s :=
mem_closure_of_is_glb is_glb_Inf hs

lemma Sup_mem_of_is_closed {α : Type u} [topological_space α] [complete_linear_order α] [orderable_topology α]
  {s : set α} (hs : s ≠ ∅) (hc : is_closed s) : Sup s ∈ s :=
mem_of_is_lub_of_is_closed  is_lub_Sup hs hc

lemma Inf_mem_of_is_closed {α : Type u} [topological_space α] [complete_linear_order α] [orderable_topology α]
  {s : set α} (hs : s ≠ ∅) (hc : is_closed s) : Inf s ∈ s :=
mem_of_is_glb_of_is_closed  is_glb_Inf hs hc

/-- A continuous monotone function sends supremum to supremum for nonempty sets. -/
lemma Sup_of_continuous' {f : α → β} (Mf : continuous f) (Cf : monotone f)
  {s : set α} (hs : s ≠ ∅) : f (Sup s) = Sup (f '' s) :=
--This is a particular case of the more general is_lub_of_is_lub_of_tendsto
(is_lub_iff_Sup_eq.1
  (is_lub_of_is_lub_of_tendsto (λ x hx y hy xy, Cf xy) is_lub_Sup hs $
    tendsto_le_left inf_le_left (continuous.tendsto Mf _))).symm

/-- A continuous monotone function sending bot to bot sends supremum to supremum. -/
lemma Sup_of_continuous {f : α → β} (Mf : continuous f) (Cf : monotone f)
  (fbot : f ⊥ = ⊥) {s : set α} : f (Sup s) = Sup (f '' s) :=
begin
  by_cases (s = ∅),
  { simpa [h] },
  { exact Sup_of_continuous' Mf Cf h }
end

/-- A continuous monotone function sends indexed supremum to indexed supremum. -/
lemma supr_of_continuous {f : α → β} {g : γ → α}
  (Mf : continuous f) (Cf : monotone f) : f (supr g) = supr (f ∘ g) :=
by rw [supr, Sup_of_continuous' Mf Cf
  (λ h, range_eq_empty.1 h ‹_›), ← range_comp]; refl

/-- A continuous monotone function sends infimum to infimum for nonempty sets. -/
lemma Inf_of_continuous' {f : α → β} (Mf : continuous f) (Cf : monotone f)
  {s : set α} (hs : s ≠ ∅) : f (Inf s) = Inf (f '' s) :=
(is_glb_iff_Inf_eq.1
  (is_glb_of_is_glb_of_tendsto (λ x hx y hy xy, Cf xy) is_glb_Inf hs $
    tendsto_le_left inf_le_left (continuous.tendsto Mf _))).symm

/-- A continuous monotone function sending top to top sends infimum to infimum. -/
lemma Inf_of_continuous {f : α → β} (Mf : continuous f) (Cf : monotone f)
  (ftop : f ⊤ = ⊤) {s : set α} : f (Inf s) = Inf (f '' s) :=
begin
  by_cases (s = ∅),
  { simpa [h] },
  { exact Inf_of_continuous' Mf Cf h }
end

/-- A continuous monotone function sends indexed infimum to indexed infimum. -/
lemma infi_of_continuous {f : α → β} {g : γ → α}
  (Mf : continuous f) (Cf : monotone f) : f (infi g) = infi (f ∘ g) :=
by rw [infi, Inf_of_continuous' Mf Cf
  (λ h, range_eq_empty.1 h ‹_›), ← range_comp]; refl

end complete_linear_order


section conditionally_complete_linear_order

variables [conditionally_complete_linear_order α] [topological_space α] [orderable_topology α]
  [conditionally_complete_linear_order β] [topological_space β] [orderable_topology β] [nonempty γ]

lemma cSup_mem_closure {α : Type u} [topological_space α] [conditionally_complete_linear_order α] [orderable_topology α]
  {s : set α} (hs : s ≠ ∅) (B : bdd_above s) : Sup s ∈ closure s :=
mem_closure_of_is_lub (is_lub_cSup hs B) hs

lemma cInf_mem_closure {α : Type u} [topological_space α] [conditionally_complete_linear_order α] [orderable_topology α]
  {s : set α} (hs : s ≠ ∅) (B : bdd_below s) : Inf s ∈ closure s :=
mem_closure_of_is_glb (is_glb_cInf hs B) hs

lemma cSup_mem_of_is_closed {α : Type u} [topological_space α] [conditionally_complete_linear_order α] [orderable_topology α]
  {s : set α} (hs : s ≠ ∅) (hc : is_closed s) (B : bdd_above s) : Sup s ∈ s :=
mem_of_is_lub_of_is_closed (is_lub_cSup hs B) hs hc

lemma cInf_mem_of_is_closed {α : Type u} [topological_space α] [conditionally_complete_linear_order α] [orderable_topology α]
  {s : set α} (hs : s ≠ ∅) (hc : is_closed s) (B : bdd_below s) : Inf s ∈ s :=
mem_of_is_glb_of_is_closed (is_glb_cInf hs B) hs hc

/-- A continuous monotone function sends supremum to supremum in conditionally complete
lattices, under a boundedness assumption. -/
lemma cSup_of_cSup_of_monotone_of_continuous {f : α → β} (Mf : continuous f) (Cf : monotone f)
  {s : set α} (ne : s ≠ ∅) (H : bdd_above s) : f (Sup s) = Sup (f '' s) :=
begin
  refine (is_lub_iff_eq_of_is_lub _).1
    (is_lub_cSup (mt image_eq_empty.1 ne) (bdd_above_of_bdd_above_of_monotone Cf H)),
  refine is_lub_of_is_lub_of_tendsto (λx hx y hy xy, Cf xy) (is_lub_cSup ne H) ne _,
  exact tendsto_le_left inf_le_left (continuous.tendsto Mf _)
end

/-- A continuous monotone function sends indexed supremum to indexed supremum in conditionally complete
lattices, under a boundedness assumption. -/
lemma csupr_of_csupr_of_monotone_of_continuous {f : α → β} {g : γ → α}
  (Mf : continuous f) (Cf : monotone f) (H : bdd_above (range g)) : f (supr g) = supr (f ∘ g) :=
by rw [supr, cSup_of_cSup_of_monotone_of_continuous Mf Cf
  (λ h, range_eq_empty.1 h ‹_›) H, ← range_comp]; refl

/-- A continuous monotone function sends infimum to infimum in conditionally complete
lattices, under a boundedness assumption. -/
lemma cInf_of_cInf_of_monotone_of_continuous {f : α → β} (Mf : continuous f) (Cf : monotone f)
  {s : set α} (ne : s ≠ ∅) (H : bdd_below s) : f (Inf s) = Inf (f '' s) :=
begin
  refine (is_glb_iff_eq_of_is_glb _).1
    (is_glb_cInf (mt image_eq_empty.1 ne) (bdd_below_of_bdd_below_of_monotone Cf H)),
  refine is_glb_of_is_glb_of_tendsto (λx hx y hy xy, Cf xy) (is_glb_cInf ne H) ne _,
  exact tendsto_le_left inf_le_left (continuous.tendsto Mf _)
end

/-- A continuous monotone function sends indexed infimum to indexed infimum in conditionally complete
lattices, under a boundedness assumption. -/
lemma cinfi_of_cinfi_of_monotone_of_continuous {f : α → β} {g : γ → α}
  (Mf : continuous f) (Cf : monotone f) (H : bdd_below (range g)): f (infi g) = infi (f ∘ g) :=
by rw [infi, cInf_of_cInf_of_monotone_of_continuous Mf Cf
  (λ h, range_eq_empty.1 h ‹_›) H, ← range_comp]; refl

/-- The extreme value theorem: a continuous function realizes its minimum on a compact set -/
lemma exists_forall_le_of_compact_of_continuous {α : Type u} [topological_space α]
  (f : α → β) (hf : continuous f) (s : set α) (hs : compact s) (ne_s : s ≠ ∅) :
  ∃x∈s, ∀y∈s, f x ≤ f y :=
begin
  have C : compact (f '' s) := compact_image hs hf,
  haveI := has_Inf_to_nonempty β,
  have B : bdd_below (f '' s) := bdd_below_of_compact C,
  have : Inf (f '' s) ∈ f '' s :=
    cInf_mem_of_is_closed (mt image_eq_empty.1 ne_s) (closed_of_compact _ C) B,
  rcases (mem_image _ _ _).1 this with ⟨x, xs, hx⟩,
  exact ⟨x, xs, λ y hy, hx.symm ▸ cInf_le B ⟨_, hy, rfl⟩⟩
end

/-- The extreme value theorem: a continuous function realizes its maximum on a compact set -/
lemma exists_forall_ge_of_compact_of_continuous {α : Type u} [topological_space α] :
  ∀ f : α → β, continuous f → ∀ s : set α, compact s → s ≠ ∅ →
  ∃x∈s, ∀y∈s, f y ≤ f x :=
@exists_forall_le_of_compact_of_continuous (order_dual β) _ _ _ _ _

end conditionally_complete_linear_order


section liminf_limsup

section ordered_topology
variables [semilattice_sup α] [topological_space α] [orderable_topology α]

lemma is_bounded_le_nhds (a : α) : (nhds a).is_bounded (≤) :=
match forall_le_or_exists_lt_sup a with
| or.inl h := ⟨a, univ_mem_sets' h⟩
| or.inr ⟨b, hb⟩ := ⟨b, ge_mem_nhds hb⟩
end

lemma is_bounded_under_le_of_tendsto {f : filter β} {u : β → α} {a : α}
  (h : tendsto u f (nhds a)) : f.is_bounded_under (≤) u :=
is_bounded_of_le h (is_bounded_le_nhds a)

lemma is_cobounded_ge_nhds (a : α) : (nhds a).is_cobounded (≥) :=
is_cobounded_of_is_bounded nhds_neq_bot (is_bounded_le_nhds a)

lemma is_cobounded_under_ge_of_tendsto {f : filter β} {u : β → α} {a : α}
  (hf : f ≠ ⊥) (h : tendsto u f (nhds a)) : f.is_cobounded_under (≥) u :=
is_cobounded_of_is_bounded (map_ne_bot hf) (is_bounded_under_le_of_tendsto h)

end ordered_topology

section ordered_topology
variables [semilattice_inf α] [topological_space α] [orderable_topology α]

lemma is_bounded_ge_nhds (a : α) : (nhds a).is_bounded (≥) :=
match forall_le_or_exists_lt_inf a with
| or.inl h := ⟨a, univ_mem_sets' h⟩
| or.inr ⟨b, hb⟩ := ⟨b, le_mem_nhds hb⟩
end

lemma is_bounded_under_ge_of_tendsto {f : filter β} {u : β → α} {a : α}
  (h : tendsto u f (nhds a)) : f.is_bounded_under (≥) u :=
is_bounded_of_le h (is_bounded_ge_nhds a)

lemma is_cobounded_le_nhds (a : α) : (nhds a).is_cobounded (≤) :=
is_cobounded_of_is_bounded nhds_neq_bot (is_bounded_ge_nhds a)

lemma is_cobounded_under_le_of_tendsto {f : filter β} {u : β → α} {a : α}
  (hf : f ≠ ⊥) (h : tendsto u f (nhds a)) : f.is_cobounded_under (≤) u :=
is_cobounded_of_is_bounded (map_ne_bot hf) (is_bounded_under_ge_of_tendsto h)

end ordered_topology

section conditionally_complete_linear_order
variables [conditionally_complete_linear_order α] [topological_space α] [orderable_topology α]

theorem lt_mem_sets_of_Limsup_lt {f : filter α} {b} (h : f.is_bounded (≤)) (l : f.Limsup < b) :
  {a | a < b} ∈ f.sets :=
let ⟨c, (h : {a : α | a ≤ c} ∈ f.sets), hcb⟩ :=
  exists_lt_of_cInf_lt (ne_empty_iff_exists_mem.2 h) l in
mem_sets_of_superset h $ assume a hac, lt_of_le_of_lt hac hcb

theorem gt_mem_sets_of_Liminf_gt : ∀ {f : filter α} {b}, f.is_bounded (≥) → f.Liminf > b →
  {a | a > b} ∈ f.sets :=
@lt_mem_sets_of_Limsup_lt (order_dual α) _ _ _

/-- If the liminf and the limsup of a filter coincide, then this filter converges to
their common value, at least if the filter is eventually bounded above and below. -/
theorem le_nhds_of_Limsup_eq_Liminf {f : filter α} {a : α}
  (hl : f.is_bounded (≤)) (hg : f.is_bounded (≥)) (hs : f.Limsup = a) (hi : f.Liminf = a) :
  f ≤ nhds a :=
tendsto_orderable.2 $ and.intro
  (assume b hb, gt_mem_sets_of_Liminf_gt hg $ hi.symm ▸ hb)
  (assume b hb, lt_mem_sets_of_Limsup_lt hl $ hs.symm ▸ hb)

theorem Limsup_nhds (a : α) : Limsup (nhds a) = a :=
cInf_intro (ne_empty_iff_exists_mem.2 $ is_bounded_le_nhds a)
  (assume a' (h : {n : α | n ≤ a'} ∈ (nhds a).sets), show a ≤ a', from @mem_of_nhds α _ a _ h)
  (assume b (hba : a < b), show ∃c (h : {n : α | n ≤ c} ∈ (nhds a).sets), c < b, from
    match dense_or_discrete hba with
    | or.inl ⟨c, hac, hcb⟩ := ⟨c, ge_mem_nhds hac, hcb⟩
    | or.inr ⟨_, h⟩        := ⟨a, (nhds a).sets_of_superset (gt_mem_nhds hba) h, hba⟩
    end)

theorem Liminf_nhds : ∀ (a : α), Liminf (nhds a) = a :=
@Limsup_nhds (order_dual α) _ _ _

/-- If a filter is converging, its limsup coincides with its limit. -/
theorem Liminf_eq_of_le_nhds {f : filter α} {a : α} (hf : f ≠ ⊥) (h : f ≤ nhds a) : f.Liminf = a :=
have hb_ge : is_bounded (≥) f, from is_bounded_of_le h (is_bounded_ge_nhds a),
have hb_le : is_bounded (≤) f, from is_bounded_of_le h (is_bounded_le_nhds a),
le_antisymm
  (calc f.Liminf ≤ f.Limsup : Liminf_le_Limsup hf hb_le hb_ge
    ... ≤ (nhds a).Limsup :
      Limsup_le_Limsup_of_le h (is_cobounded_of_is_bounded hf hb_ge) (is_bounded_le_nhds a)
    ... = a : Limsup_nhds a)
  (calc a = (nhds a).Liminf : (Liminf_nhds a).symm
    ... ≤ f.Liminf :
      Liminf_le_Liminf_of_le h (is_bounded_ge_nhds a) (is_cobounded_of_is_bounded hf hb_le))

/-- If a filter is converging, its liminf coincides with its limit. -/
theorem Limsup_eq_of_le_nhds : ∀ {f : filter α} {a : α}, f ≠ ⊥ → f ≤ nhds a → f.Limsup = a :=
@Liminf_eq_of_le_nhds (order_dual α) _ _ _

end conditionally_complete_linear_order

end liminf_limsup

end orderable_topology

lemma orderable_topology_of_nhds_abs
  {α : Type*} [decidable_linear_ordered_comm_group α] [topological_space α]
  (h_nhds : ∀a:α, nhds a = (⨅r>0, principal {b | abs (a - b) < r})) : orderable_topology α :=
orderable_topology.mk $ eq_of_nhds_eq_nhds $ assume a:α, le_antisymm_iff.mpr
begin
  simp [infi_and, topological_space.nhds_generate_from,
        h_nhds, le_infi_iff, -le_principal_iff, and_comm],
  refine ⟨λ s ha b hs, _, λ r hr, _⟩,
  { rcases hs with rfl | rfl,
    { refine infi_le_of_le (a - b)
        (infi_le_of_le (lt_sub_left_of_add_lt $ by simpa using ha) $
          principal_mono.mpr $ assume c (hc : abs (a - c) < a - b), _),
      have : a - c < a - b := lt_of_le_of_lt (le_abs_self _) hc,
      exact lt_of_neg_lt_neg (lt_of_add_lt_add_left this) },
    { refine infi_le_of_le (b - a)
        (infi_le_of_le (lt_sub_left_of_add_lt $ by simpa using ha) $
          principal_mono.mpr $ assume c (hc : abs (a - c) < b - a), _),
      have : abs (c - a) < b - a, {rw abs_sub; simpa using hc},
      have : c - a < b - a := lt_of_le_of_lt (le_abs_self _) this,
      exact lt_of_add_lt_add_right this } },
  { have h : {b | abs (a + -b) < r} = {b | a - r < b} ∩ {b | b < a + r},
      from set.ext (assume b,
        by simp [abs_lt, -sub_eq_add_neg, (sub_eq_add_neg _ _).symm,
          sub_lt, lt_sub_iff_add_lt, and_comm, sub_lt_iff_lt_add']),
    rw [h, ← inf_principal],
    apply le_inf _ _,
    { exact infi_le_of_le {b : α | a - r < b} (infi_le_of_le (sub_lt_self a hr) $
        infi_le_of_le (a - r) $ infi_le _ (or.inl rfl)) },
    { exact infi_le_of_le {b : α | b < a + r} (infi_le_of_le (lt_add_of_pos_right _ hr) $
        infi_le_of_le (a + r) $ infi_le _ (or.inr rfl)) } }
end

lemma tendsto_at_top_supr_nat [topological_space α] [complete_linear_order α] [orderable_topology α]
  (f : ℕ → α) (hf : monotone f) : tendsto f at_top (nhds (⨆i, f i)) :=
tendsto_orderable.2 $ and.intro
  (assume a ha, let ⟨n, hn⟩ := lt_supr_iff.1 ha in
    mem_at_top_sets.2 ⟨n, assume i hi, lt_of_lt_of_le hn (hf hi)⟩)
  (assume a ha, univ_mem_sets' (assume n, lt_of_le_of_lt (le_supr _ n) ha))

lemma tendsto_at_top_infi_nat [topological_space α] [complete_linear_order α] [orderable_topology α]
  (f : ℕ → α) (hf : ∀{n m}, n ≤ m → f m ≤ f n) : tendsto f at_top (nhds (⨅i, f i)) :=
@tendsto_at_top_supr_nat (order_dual α) _ _ _ _ @hf

lemma supr_eq_of_tendsto {α} [topological_space α] [complete_linear_order α] [orderable_topology α]
  {f : ℕ → α} {a : α} (hf : monotone f) : tendsto f at_top (nhds a) → supr f = a :=
tendsto_nhds_unique at_top_ne_bot (tendsto_at_top_supr_nat f hf)

lemma infi_eq_of_tendsto {α} [topological_space α] [complete_linear_order α] [orderable_topology α]
  {f : ℕ → α} {a : α} (hf : ∀n m, n ≤ m → f m ≤ f n) : tendsto f at_top (nhds a) → infi f = a :=
tendsto_nhds_unique at_top_ne_bot (tendsto_at_top_infi_nat f hf)
