/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot
-/

import tactic.apply_fun
import topology.uniform_space.basic
import topology.separation

/-!
# Hausdorff properties of uniform spaces. Separation quotient.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file studies uniform spaces whose underlying topological spaces are separated
(also known as Hausdorff or T₂).
This turns out to be equivalent to asking that the intersection of all entourages
is the diagonal only. This condition actually implies the stronger separation property
that the space is T₃, hence those conditions are equivalent for topologies coming from
a uniform structure.

More generally, the intersection `𝓢 X` of all entourages of `X`, which has type `set (X × X)` is an
equivalence relation on `X`. Points which are equivalent under the relation are basically
undistinguishable from the point of view of the uniform structure. For instance any uniformly
continuous function will send equivalent points to the same value.

The quotient `separation_quotient X` of `X` by `𝓢 X` has a natural uniform structure which is
separated, and satisfies a universal property: every uniformly continuous function
from `X` to a separated uniform space uniquely factors through `separation_quotient X`.
As usual, this allows to turn `separation_quotient` into a functor (but we don't use the
category theory library in this file).

These notions admit relative versions, one can ask that `s : set X` is separated, this
is equivalent to asking that the uniform structure induced on `s` is separated.

## Main definitions

* `separation_relation X : set (X × X)`: the separation relation
* `separated_space X`: a predicate class asserting that `X` is separated
* `separation_quotient X`: the maximal separated quotient of `X`.
* `separation_quotient.lift f`: factors a map `f : X → Y` through the separation quotient of `X`.
* `separation_quotient.map f`: turns a map `f : X → Y` into a map between the separation quotients
  of `X` and `Y`.

## Main results

* `separated_iff_t2`: the equivalence between being separated and being Hausdorff for uniform
  spaces.
* `separation_quotient.uniform_continuous_lift`: factoring a uniformly continuous map through the
  separation quotient gives a uniformly continuous map.
* `separation_quotient.uniform_continuous_map`: maps induced between separation quotients are
  uniformly continuous.

## Notations

Localized in `uniformity`, we have the notation `𝓢 X` for the separation relation
on a uniform space `X`,

## Implementation notes

The separation setoid `separation_setoid` is not declared as a global instance.
It is made a local instance while building the theory of `separation_quotient`.
The factored map `separation_quotient.lift f` is defined without imposing any condition on
`f`, but returns junk if `f` is not uniformly continuous (constant junk hence it is always
uniformly continuous).

-/

open filter topological_space set classical function uniform_space
open_locale classical topology uniformity filter
noncomputable theory
set_option eqn_compiler.zeta true

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
variables [uniform_space α] [uniform_space β] [uniform_space γ]


/-!
### Separated uniform spaces
-/

@[priority 100]
instance uniform_space.to_regular_space : regular_space α :=
regular_space.of_basis
  (λ a, by { rw [nhds_eq_comap_uniformity], exact uniformity_has_basis_closed.comap _ })
  (λ a V hV, hV.2.preimage $ continuous_const.prod_mk continuous_id)

/-- The separation relation is the intersection of all entourages.
  Two points which are related by the separation relation are "indistinguishable"
  according to the uniform structure. -/
protected def separation_rel (α : Type u) [u : uniform_space α] :=
⋂₀ (𝓤 α).sets

localized "notation (name := separation_rel) `𝓢` := separation_rel" in uniformity

lemma separated_equiv : equivalence (λx y, (x, y) ∈ 𝓢 α) :=
⟨assume x, assume s, refl_mem_uniformity,
  assume x y, assume h (s : set (α×α)) hs,
    have preimage prod.swap s ∈ 𝓤 α,
      from symm_le_uniformity hs,
    h _ this,
  assume x y z (hxy : (x, y) ∈ 𝓢 α) (hyz : (y, z) ∈ 𝓢 α)
      s (hs : s ∈ 𝓤 α),
    let ⟨t, ht, (h_ts : comp_rel t t ⊆ s)⟩ := comp_mem_uniformity_sets hs in
    h_ts $ show (x, z) ∈ comp_rel t t,
      from ⟨y, hxy t ht, hyz t ht⟩⟩

lemma filter.has_basis.mem_separation_rel {ι : Sort*} {p : ι → Prop} {s : ι → set (α × α)}
  (h : (𝓤 α).has_basis p s) {a : α × α} :
  a ∈ 𝓢 α ↔ ∀ i, p i → a ∈ s i :=
h.forall_mem_mem

theorem separation_rel_iff_specializes {a b : α} : (a, b) ∈ 𝓢 α ↔ a ⤳ b :=
by simp only [(𝓤 α).basis_sets.mem_separation_rel, id, mem_set_of_eq,
  (nhds_basis_uniformity (𝓤 α).basis_sets).specializes_iff]

theorem separation_rel_iff_inseparable {a b : α} : (a, b) ∈ 𝓢 α ↔ inseparable a b :=
  separation_rel_iff_specializes.trans specializes_iff_inseparable

/-- A uniform space is separated if its separation relation is trivial (each point
is related only to itself). -/
class separated_space (α : Type u) [uniform_space α] : Prop := (out : 𝓢 α = id_rel)

theorem separated_space_iff {α : Type u} [uniform_space α] :
  separated_space α ↔ 𝓢 α = id_rel :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

theorem separated_def {α : Type u} [uniform_space α] :
  separated_space α ↔ ∀ x y, (∀ r ∈ 𝓤 α, (x, y) ∈ r) → x = y :=
by simp [separated_space_iff, id_rel_subset.2 separated_equiv.1, subset.antisymm_iff];
   simp [subset_def, separation_rel]

theorem separated_def' {α : Type u} [uniform_space α] :
  separated_space α ↔ ∀ x y, x ≠ y → ∃ r ∈ 𝓤 α, (x, y) ∉ r :=
separated_def.trans $ forall₂_congr $ λ x y, by rw ← not_imp_not; simp [not_forall]

lemma eq_of_uniformity {α : Type*} [uniform_space α] [separated_space α] {x y : α}
  (h : ∀ {V}, V ∈ 𝓤 α → (x, y) ∈ V) : x = y :=
separated_def.mp ‹separated_space α› x y (λ _, h)

lemma eq_of_uniformity_basis {α : Type*} [uniform_space α] [separated_space α] {ι : Type*}
  {p : ι → Prop} {s : ι → set (α × α)} (hs : (𝓤 α).has_basis p s) {x y : α}
  (h : ∀ {i}, p i → (x, y) ∈ s i) : x = y :=
eq_of_uniformity (λ V V_in, let ⟨i, hi, H⟩ := hs.mem_iff.mp V_in in H (h hi))

lemma eq_of_forall_symmetric {α : Type*} [uniform_space α] [separated_space α] {x y : α}
  (h : ∀ {V}, V ∈ 𝓤 α → symmetric_rel V → (x, y) ∈ V) : x = y :=
eq_of_uniformity_basis has_basis_symmetric (by simpa [and_imp] using λ _, h)

lemma eq_of_cluster_pt_uniformity [separated_space α] {x y : α} (h : cluster_pt (x, y) (𝓤 α)) :
  x = y :=
eq_of_uniformity_basis uniformity_has_basis_closed $ λ V ⟨hV, hVc⟩,
  is_closed_iff_cluster_pt.1 hVc _ $ h.mono $ le_principal_iff.2 hV

lemma id_rel_sub_separation_relation (α : Type*) [uniform_space α] : id_rel ⊆ 𝓢 α :=
begin
  unfold separation_rel,
  rw id_rel_subset,
  intros x,
  suffices : ∀ t ∈ 𝓤 α, (x, x) ∈ t, by simpa only [refl_mem_uniformity],
  exact λ t, refl_mem_uniformity,
end

lemma separation_rel_comap  {f : α → β}
  (h : ‹uniform_space α› = uniform_space.comap f ‹uniform_space β›) :
  𝓢 α = (prod.map f f) ⁻¹' 𝓢 β :=
begin
  unfreezingI { subst h },
  dsimp [separation_rel],
  simp_rw [uniformity_comap, (filter.comap_has_basis (prod.map f f) (𝓤 β)).sInter_sets,
      ← preimage_Inter, sInter_eq_bInter],
  refl,
end

protected lemma filter.has_basis.separation_rel {ι : Sort*} {p : ι → Prop} {s : ι → set (α × α)}
  (h : has_basis (𝓤 α) p s) :
  𝓢 α = ⋂ i (hi : p i), s i :=
by { unfold separation_rel, rw h.sInter_sets }

lemma separation_rel_eq_inter_closure : 𝓢 α = ⋂₀ (closure '' (𝓤 α).sets) :=
by simp [uniformity_has_basis_closure.separation_rel]

lemma is_closed_separation_rel : is_closed (𝓢 α) :=
begin
  rw separation_rel_eq_inter_closure,
  apply is_closed_sInter,
  rintros _ ⟨t, t_in, rfl⟩,
  exact is_closed_closure,
end

lemma separated_iff_t2 : separated_space α ↔ t2_space α :=
begin
  classical,
  split ; introI h,
  { rw [t2_iff_is_closed_diagonal, ← show 𝓢 α = diagonal α, from h.1],
    exact is_closed_separation_rel },
  { rw separated_def',
    intros x y hxy,
    rcases t2_separation hxy with ⟨u, v, uo, vo, hx, hy, h⟩,
    rcases is_open_iff_ball_subset.1 uo x hx with ⟨r, hrU, hr⟩,
    exact ⟨r, hrU, λ H, h.le_bot ⟨hr H, hy⟩⟩ }
end

@[priority 100] -- see Note [lower instance priority]
instance separated_t3 [separated_space α] : t3_space α :=
by { haveI := separated_iff_t2.mp ‹_›, exact ⟨⟩ }

instance subtype.separated_space [separated_space α] (s : set α) : separated_space s :=
separated_iff_t2.mpr subtype.t2_space

lemma is_closed_of_spaced_out [separated_space α] {V₀ : set (α × α)} (V₀_in : V₀ ∈ 𝓤 α)
  {s : set α} (hs : s.pairwise (λ x y, (x, y) ∉ V₀)) : is_closed s :=
begin
  rcases comp_symm_mem_uniformity_sets V₀_in with ⟨V₁, V₁_in, V₁_symm, h_comp⟩,
  apply is_closed_of_closure_subset,
  intros x hx,
  rw mem_closure_iff_ball at hx,
  rcases hx V₁_in with ⟨y, hy, hy'⟩,
  suffices : x = y, by rwa this,
  apply eq_of_forall_symmetric,
  intros V V_in V_symm,
  rcases hx (inter_mem V₁_in V_in) with ⟨z, hz, hz'⟩,
  obtain rfl : z = y,
  { by_contra hzy,
    exact hs hz' hy' hzy (h_comp $ mem_comp_of_mem_ball V₁_symm (ball_inter_left x _ _ hz) hy) },
  exact ball_inter_right x _ _ hz
end

lemma is_closed_range_of_spaced_out {ι} [separated_space α] {V₀ : set (α × α)} (V₀_in : V₀ ∈ 𝓤 α)
  {f : ι → α} (hf : pairwise (λ x y, (f x, f y) ∉ V₀)) : is_closed (range f) :=
is_closed_of_spaced_out V₀_in $
  by { rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h, exact hf (ne_of_apply_ne f h) }


/-!
### Separation quotient
-/
namespace uniform_space

/-- The separation relation of a uniform space seen as a setoid. -/
def separation_setoid (α : Type u) [uniform_space α] : setoid α :=
⟨λx y, (x, y) ∈ 𝓢 α, separated_equiv⟩

local attribute [instance] separation_setoid

instance separation_setoid.uniform_space {α : Type u} [u : uniform_space α] :
  uniform_space (quotient (separation_setoid α)) :=
{ to_topological_space := u.to_topological_space.coinduced (λx, ⟦x⟧),
  uniformity := map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) u.uniformity,
  refl := le_trans (by simp [quotient.exists_rep]) (filter.map_mono refl_le_uniformity),
  symm := tendsto_map' $
    by simp [prod.swap, (∘)]; exact tendsto_map.comp tendsto_swap_uniformity,
  comp := calc (map (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) u.uniformity).lift' (λs, comp_rel s s) =
          u.uniformity.lift' ((λs, comp_rel s s) ∘ image (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧))) :
      map_lift'_eq2 $ monotone_id.comp_rel monotone_id
    ... ≤ u.uniformity.lift' (image (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) ∘
            (λs:set (α×α), comp_rel s (comp_rel s s))) :
      lift'_mono' $ assume s hs ⟨a, b⟩ ⟨c, ⟨⟨a₁, a₂⟩, ha, a_eq⟩, ⟨⟨b₁, b₂⟩, hb, b_eq⟩⟩,
      begin
        simp at a_eq,
        simp at b_eq,
        have h : ⟦a₂⟧ = ⟦b₁⟧, { rw [a_eq.right, b_eq.left] },
        have h : (a₂, b₁) ∈ 𝓢 α := quotient.exact h,
        simp [function.comp, set.image, comp_rel, and.comm, and.left_comm, and.assoc],
        exact ⟨a₁, a_eq.left, b₂, b_eq.right, a₂, ha, b₁, h s hs, hb⟩
      end
    ... = map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧))
            (u.uniformity.lift' (λs:set (α×α), comp_rel s (comp_rel s s))) :
      by rw [map_lift'_eq];
        exact monotone_id.comp_rel (monotone_id.comp_rel monotone_id)
    ... ≤ map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) u.uniformity :
      map_mono comp_le_uniformity3,
  is_open_uniformity := assume s,
    have ∀a, ⟦a⟧ ∈ s →
        ({p:α×α | p.1 = a → ⟦p.2⟧ ∈ s} ∈ 𝓤 α ↔
          {p:α×α | p.1 ≈ a → ⟦p.2⟧ ∈ s} ∈ 𝓤 α),
      from assume a ha,
      ⟨assume h,
        let ⟨t, ht, hts⟩ := comp_mem_uniformity_sets h in
        have hts : ∀{a₁ a₂}, (a, a₁) ∈ t → (a₁, a₂) ∈ t → ⟦a₂⟧ ∈ s,
          from assume a₁ a₂ ha₁ ha₂, @hts (a, a₂) ⟨a₁, ha₁, ha₂⟩ rfl,
        have ht' : ∀{a₁ a₂}, a₁ ≈ a₂ → (a₁, a₂) ∈ t,
          from assume a₁ a₂ h, sInter_subset_of_mem ht h,
        u.uniformity.sets_of_superset ht $ assume ⟨a₁, a₂⟩ h₁ h₂, hts (ht' $ setoid.symm h₂) h₁,
        assume h, u.uniformity.sets_of_superset h $ by simp {contextual := tt}⟩,
    begin
      simp only [is_open_coinduced, is_open_uniformity, uniformity, forall_quotient_iff,
        mem_preimage, mem_map, preimage_set_of_eq, quotient.eq],
      exact ⟨λh a ha, (this a ha).mp $ h a ha, λh a ha, (this a ha).mpr $ h a ha⟩
    end }

lemma uniformity_quotient :
  𝓤 (quotient (separation_setoid α)) = (𝓤 α).map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) :=
rfl

lemma uniform_continuous_quotient_mk :
  uniform_continuous (quotient.mk : α → quotient (separation_setoid α)) :=
le_rfl

lemma uniform_continuous_quotient {f : quotient (separation_setoid α) → β}
  (hf : uniform_continuous (λx, f ⟦x⟧)) : uniform_continuous f :=
hf

lemma uniform_continuous_quotient_lift
  {f : α → β} {h : ∀a b, (a, b) ∈ 𝓢 α → f a = f b}
  (hf : uniform_continuous f) : uniform_continuous (λa, quotient.lift f h a) :=
uniform_continuous_quotient hf

lemma uniform_continuous_quotient_lift₂
  {f : α → β → γ} {h : ∀a c b d, (a, b) ∈ 𝓢 α → (c, d) ∈ 𝓢 β → f a c = f b d}
  (hf : uniform_continuous (λp:α×β, f p.1 p.2)) :
  uniform_continuous (λp:_×_, quotient.lift₂ f h p.1 p.2) :=
begin
  rw [uniform_continuous, uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient,
    filter.prod_map_map_eq, filter.tendsto_map'_iff, filter.tendsto_map'_iff],
  rwa [uniform_continuous, uniformity_prod_eq_prod, filter.tendsto_map'_iff] at hf
end

lemma comap_quotient_le_uniformity :
  (𝓤 $ quotient $ separation_setoid α).comap (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) ≤ (𝓤 α) :=
assume t' ht',
let ⟨t, ht, tt_t'⟩ := comp_mem_uniformity_sets ht' in
let ⟨s, hs, ss_t⟩ := comp_mem_uniformity_sets ht in
⟨(λp:α×α, (⟦p.1⟧, ⟦p.2⟧)) '' s,
  (𝓤 α).sets_of_superset hs $ assume x hx, ⟨x, hx, rfl⟩,
  assume ⟨a₁, a₂⟩ ⟨⟨b₁, b₂⟩, hb, ab_eq⟩,
  have ⟦b₁⟧ = ⟦a₁⟧ ∧ ⟦b₂⟧ = ⟦a₂⟧, from prod.mk.inj ab_eq,
  have b₁ ≈ a₁ ∧ b₂ ≈ a₂, from and.imp quotient.exact quotient.exact this,
  have ab₁ : (a₁, b₁) ∈ t, from (setoid.symm this.left) t ht,
  have ba₂ : (b₂, a₂) ∈ s, from this.right s hs,
  tt_t' ⟨b₁, show ((a₁, a₂).1, b₁) ∈ t, from ab₁,
    ss_t ⟨b₂, show ((b₁, a₂).1, b₂) ∈ s, from hb, ba₂⟩⟩⟩

lemma comap_quotient_eq_uniformity :
  (𝓤 $ quotient $ separation_setoid α).comap (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) = 𝓤 α :=
le_antisymm comap_quotient_le_uniformity le_comap_map


instance separated_separation : separated_space (quotient (separation_setoid α)) :=
⟨set.ext $ assume ⟨a, b⟩, quotient.induction_on₂ a b $ assume a b,
  ⟨assume h,
    have a ≈ b, from assume s hs,
      have s ∈ (𝓤 $ quotient $ separation_setoid α).comap (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)),
        from comap_quotient_le_uniformity hs,
      let ⟨t, ht, hts⟩ := this in
      hts begin dsimp [preimage], exact h t ht end,
    show ⟦a⟧ = ⟦b⟧, from quotient.sound this,

  assume heq : ⟦a⟧ = ⟦b⟧, assume h hs,
  heq ▸ refl_mem_uniformity hs⟩⟩

lemma separated_of_uniform_continuous {f : α → β} {x y : α}
  (H : uniform_continuous f) (h : x ≈ y) : f x ≈ f y :=
assume _ h', h _ (H h')

lemma eq_of_separated_of_uniform_continuous [separated_space β] {f : α → β} {x y : α}
  (H : uniform_continuous f) (h : x ≈ y) : f x = f y :=
separated_def.1 (by apply_instance) _ _ $ separated_of_uniform_continuous H h

/-- The maximal separated quotient of a uniform space `α`. -/
def separation_quotient (α : Type*) [uniform_space α] := quotient (separation_setoid α)

namespace separation_quotient
instance : uniform_space (separation_quotient α) := separation_setoid.uniform_space
instance : separated_space (separation_quotient α) := uniform_space.separated_separation
instance [inhabited α] : inhabited (separation_quotient α) :=
quotient.inhabited (separation_setoid α)

lemma mk_eq_mk {x y : α} : (⟦x⟧ : separation_quotient α) = ⟦y⟧ ↔ inseparable x y :=
quotient.eq'.trans separation_rel_iff_inseparable

/-- Factoring functions to a separated space through the separation quotient. -/
def lift [separated_space β] (f : α → β) : (separation_quotient α → β) :=
if h : uniform_continuous f then
  quotient.lift f (λ x y, eq_of_separated_of_uniform_continuous h)
else
  λ x, f (nonempty.some ⟨x.out⟩)

lemma lift_mk [separated_space β] {f : α → β} (h : uniform_continuous f) (a : α) :
  lift f ⟦a⟧ = f a :=
by rw [lift, dif_pos h]; refl

lemma uniform_continuous_lift [separated_space β] (f : α → β) : uniform_continuous (lift f) :=
begin
  by_cases hf : uniform_continuous f,
  { rw [lift, dif_pos hf], exact uniform_continuous_quotient_lift hf },
  { rw [lift, dif_neg hf], exact uniform_continuous_of_const (assume a b, rfl) }
end

/-- The separation quotient functor acting on functions. -/
def map (f : α → β) : separation_quotient α → separation_quotient β :=
lift (quotient.mk ∘ f)

lemma map_mk {f : α → β} (h : uniform_continuous f) (a : α) : map f ⟦a⟧ = ⟦f a⟧ :=
by rw [map, lift_mk (uniform_continuous_quotient_mk.comp h)]

lemma uniform_continuous_map (f : α → β) : uniform_continuous (map f) :=
uniform_continuous_lift (quotient.mk ∘ f)

lemma map_unique {f : α → β} (hf : uniform_continuous f)
  {g : separation_quotient α → separation_quotient β}
  (comm : quotient.mk ∘ f = g ∘ quotient.mk) : map f = g :=
by ext ⟨a⟩;
calc map f ⟦a⟧ = ⟦f a⟧ : map_mk hf a
  ... = g ⟦a⟧ : congr_fun comm a

lemma map_id : map (@id α) = id :=
map_unique uniform_continuous_id rfl

lemma map_comp {f : α → β} {g : β → γ} (hf : uniform_continuous f) (hg : uniform_continuous g) :
  map g ∘ map f = map (g ∘ f) :=
(map_unique (hg.comp hf) $ by simp only [(∘), map_mk, hf, hg]).symm

end separation_quotient

lemma separation_prod {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) ≈ (a₂, b₂) ↔ a₁ ≈ a₂ ∧ b₁ ≈ b₂ :=
begin
  split,
  { assume h,
    exact ⟨separated_of_uniform_continuous uniform_continuous_fst h,
           separated_of_uniform_continuous uniform_continuous_snd h⟩ },
  { rintros ⟨eqv_α, eqv_β⟩ r r_in,
    rw uniformity_prod at r_in,
    rcases r_in with ⟨t_α, ⟨r_α, r_α_in, h_α⟩, t_β, ⟨r_β, r_β_in, h_β⟩, rfl⟩,
    let p_α := λ(p : (α × β) × (α × β)), (p.1.1, p.2.1),
    let p_β := λ(p : (α × β) × (α × β)), (p.1.2, p.2.2),
    have key_α : p_α ((a₁, b₁), (a₂, b₂)) ∈ r_α, { simp [p_α, eqv_α r_α r_α_in] },
    have key_β : p_β ((a₁, b₁), (a₂, b₂)) ∈ r_β, { simp [p_β, eqv_β r_β r_β_in] },
    exact ⟨h_α key_α, h_β key_β⟩ },
end

instance separated.prod [separated_space α] [separated_space β] : separated_space (α × β) :=
separated_def.2 $ assume x y H, prod.ext
  (eq_of_separated_of_uniform_continuous uniform_continuous_fst H)
  (eq_of_separated_of_uniform_continuous uniform_continuous_snd H)

end uniform_space
