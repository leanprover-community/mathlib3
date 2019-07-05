/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot

Theory of topological groups.

-/
import data.equiv.algebra
import algebra.pointwise order.filter.pointwise
import group_theory.quotient_group
import topology.algebra.monoid topology.order

open classical set lattice filter topological_space
local attribute [instance] classical.prop_decidable

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

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
continuous_inv'.comp hf

@[to_additive continuous_on.neg]
lemma continuous_on.inv [topological_group α] [topological_space β] {f : β → α} {s : set β}
  (hf : continuous_on f s) : continuous_on (λx, (f x)⁻¹) s :=
continuous_inv'.comp_continuous_on hf

@[to_additive tendsto_neg]
lemma tendsto_inv [topological_group α] {f : β → α} {x : filter β} {a : α}
  (hf : tendsto f x (nhds a)) : tendsto (λx, (f x)⁻¹) x (nhds a⁻¹) :=
tendsto.comp (continuous_iff_continuous_at.mp (topological_group.continuous_inv α) a) hf

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
attribute [to_additive homeomorph.neg._proof_1] homeomorph.inv._proof_1
attribute [to_additive homeomorph.neg._proof_2] homeomorph.inv._proof_2
attribute [to_additive homeomorph.neg] homeomorph.inv

@[to_additive exists_nhds_half]
lemma exists_nhds_split [topological_group α] {s : set α} (hs : s ∈ nhds (1 : α)) :
  ∃ V ∈ nhds (1 : α), ∀ v w ∈ V, v * w ∈ s :=
begin
  have : ((λa:α×α, a.1 * a.2) ⁻¹' s) ∈ nhds ((1, 1) : α × α) :=
    tendsto_mul' (by simpa using hs),
  rw nhds_prod_eq at this,
  rcases mem_prod_iff.1 this with ⟨V₁, H₁, V₂, H₂, H⟩,
  exact ⟨V₁ ∩ V₂, inter_mem_sets H₁ H₂, assume v w ⟨hv, _⟩ ⟨_, hw⟩, @H (v, w) ⟨hv, hw⟩⟩
end

@[to_additive exists_nhds_half_neg]
lemma exists_nhds_split_inv [topological_group α] {s : set α} (hs : s ∈ nhds (1 : α)) :
  ∃ V ∈ nhds (1 : α), ∀ v w ∈ V, v * w⁻¹ ∈ s :=
begin
  have : tendsto (λa:α×α, a.1 * (a.2)⁻¹) ((nhds (1:α)).prod (nhds (1:α))) (nhds 1),
  { simpa using tendsto_mul (@tendsto_fst α α (nhds 1) (nhds 1)) (tendsto_inv tendsto_snd) },
  have : ((λa:α×α, a.1 * (a.2)⁻¹) ⁻¹' s) ∈ (nhds (1:α)).prod (nhds (1:α)) :=
    this (by simpa using hs),
  rcases mem_prod_iff.1 this with ⟨V₁, H₁, V₂, H₂, H⟩,
  exact ⟨V₁ ∩ V₂, inter_mem_sets H₁ H₂, assume v w ⟨hv, _⟩ ⟨_, hw⟩, @H (v, w) ⟨hv, hw⟩⟩
end

@[to_additive exists_nhds_quarter]
lemma exists_nhds_split4 [topological_group α] {u : set α} (hu : u ∈ nhds (1 : α)) :
  ∃ V ∈ nhds (1 : α), ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v * w * s * t ∈ u :=
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

@[to_additive topological_add_group.ext]
lemma topological_group.ext {G : Type*} [group G] {t t' : topological_space G}
  (tg : @topological_group G t _) (tg' : @topological_group G t' _)
  (h : @nhds G t 1 = @nhds G t' 1) : t = t' :=
eq_of_nhds_eq_nhds $ λ x, by
  rw [← @nhds_translation_mul_inv G t _ _ x , ← @nhds_translation_mul_inv G t' _ _ x , ← h]
end topological_group

section quotient_topological_group
variables [topological_space α] [group α] [topological_group α] (N : set α) [normal_subgroup N]

@[to_additive quotient_add_group.quotient.topological_space]
instance : topological_space (quotient_group.quotient N) :=
by dunfold quotient_group.quotient; apply_instance

attribute [instance] quotient_add_group.quotient.topological_space

open quotient_group
@[to_additive quotient_add_group_saturate]
lemma quotient_group_saturate (s : set α) :
  (coe : α → quotient N) ⁻¹' ((coe : α → quotient N) '' s) = (⋃ x : N, (λ y, y*x.1) '' s) :=
begin
  ext x,
  simp only [mem_preimage_eq, mem_image, mem_Union, quotient_group.eq],
  split,
  { exact assume ⟨a, a_in, h⟩, ⟨⟨_, h⟩, a, a_in, mul_inv_cancel_left _ _⟩ },
  { exact assume ⟨⟨i, hi⟩, a, ha, eq⟩,
      ⟨a, ha, by simp only [eq.symm, (mul_assoc _ _ _).symm, inv_mul_cancel_left, hi]⟩ }
end

@[to_additive quotient_add_group.open_coe]
lemma quotient_group.open_coe : is_open_map (coe : α →  quotient N) :=
begin
  intros s s_op,
  change is_open ((coe : α →  quotient N) ⁻¹' (coe '' s)),
  rw quotient_group_saturate N s,
  apply is_open_Union,
  rintro ⟨n, _⟩,
  exact is_open_map_mul_right n s s_op
end

@[to_additive topological_add_group_quotient]
instance topological_group_quotient : topological_group (quotient N) :=
{ continuous_mul := begin
    have cont : continuous ((coe : α → quotient N) ∘ (λ (p : α × α), p.fst * p.snd)) :=
      continuous_quot_mk.comp continuous_mul',
    have quot : quotient_map (λ p : α × α, ((p.1:quotient N), (p.2:quotient N))),
    { apply is_open_map.to_quotient_map,
      { exact is_open_map.prod (quotient_group.open_coe N) (quotient_group.open_coe N) },
      { apply continuous.prod_mk,
        { exact continuous_quot_mk.comp continuous_fst },
        { exact continuous_quot_mk.comp continuous_snd } },
      { rintro ⟨⟨x⟩, ⟨y⟩⟩,
        exact ⟨(x, y), rfl⟩ } },
    exact (quotient_map.continuous_iff quot).2 cont,
  end,
  continuous_inv := begin
    apply continuous_quotient_lift,
    change continuous ((coe : α → quotient N) ∘ (λ (a : α), a⁻¹)),
    exact continuous_quot_mk.comp continuous_inv'
  end }

attribute [instance] topological_add_group_quotient

end quotient_topological_group


section topological_add_group
variables [topological_space α] [add_group α]

lemma continuous_sub [topological_add_group α] [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λx, f x - g x) :=
by simp; exact continuous_add hf (continuous_neg hg)

lemma continuous_sub' [topological_add_group α] : continuous (λp:α×α, p.1 - p.2) :=
continuous_sub continuous_fst continuous_snd

lemma continuous_on.sub [topological_add_group α] [topological_space β] {f : β → α} {g : β → α} {s : set β}
  (hf : continuous_on f s) (hg : continuous_on g s) : continuous_on (λx, f x - g x) s :=
continuous_sub'.comp_continuous_on (hf.prod hg)

lemma tendsto_sub [topological_add_group α] {f : β → α} {g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) : tendsto (λx, f x - g x) x (nhds (a - b)) :=
by simp; exact tendsto_add hf (tendsto_neg hg)

lemma nhds_translation [topological_add_group α] (x : α) : comap (λy:α, y - x) (nhds 0) = nhds x :=
nhds_translation_add_neg x

end topological_add_group

/-- additive group with a neighbourhood around 0.
Only used to construct a topology and uniform space.

This is currently only available for commutative groups, but it can be extended to
non-commutative groups too.
-/
class add_group_with_zero_nhd (α : Type u) extends add_comm_group α :=
(Z : filter α)
(zero_Z {} : pure 0 ≤ Z)
(sub_Z {} : tendsto (λp:α×α, p.1 - p.2) (Z.prod Z) Z)

namespace add_group_with_zero_nhd
variables (α) [add_group_with_zero_nhd α]

local notation `Z` := add_group_with_zero_nhd.Z

instance : topological_space α :=
topological_space.mk_of_nhds $ λa, map (λx, x + a) (Z α)

variables {α}

lemma neg_Z : tendsto (λa:α, - a) (Z α) (Z α) :=
have tendsto (λa, (0:α)) (Z α) (Z α),
  by refine le_trans (assume h, _) zero_Z; simp [univ_mem_sets'] {contextual := tt},
have tendsto (λa:α, 0 - a) (Z α) (Z α), from
  sub_Z.comp (tendsto.prod_mk this tendsto_id),
by simpa

lemma add_Z : tendsto (λp:α×α, p.1 + p.2) ((Z α).prod (Z α)) (Z α) :=
suffices tendsto (λp:α×α, p.1 - -p.2) ((Z α).prod (Z α)) (Z α),
  by simpa,
sub_Z.comp (tendsto.prod_mk tendsto_fst (neg_Z.comp tendsto_snd))

lemma exists_Z_half {s : set α} (hs : s ∈ Z α) : ∃ V ∈ Z α, ∀ v w ∈ V, v + w ∈ s :=
begin
  have : ((λa:α×α, a.1 + a.2) ⁻¹' s) ∈ (Z α).prod (Z α) := add_Z (by simpa using hs),
  rcases mem_prod_iff.1 this with ⟨V₁, H₁, V₂, H₂, H⟩,
  exact ⟨V₁ ∩ V₂, inter_mem_sets H₁ H₂, assume v w ⟨hv, _⟩ ⟨_, hw⟩, @H (v, w) ⟨hv, hw⟩⟩
end

lemma nhds_eq (a : α) : nhds a = map (λx, x + a) (Z α) :=
topological_space.nhds_mk_of_nhds _ _
  (assume a, calc pure a = map (λx, x + a) (pure 0) : by simp
    ... ≤ _ : map_mono zero_Z)
  (assume b s hs,
    let ⟨t, ht, eqt⟩ := exists_Z_half hs in
    have t0 : (0:α) ∈ t, by simpa using zero_Z ht,
    begin
      refine ⟨(λx:α, x + b) '' t, image_mem_map ht, _, _⟩,
      { refine set.image_subset_iff.2 (assume b hbt, _),
        simpa using eqt 0 b t0 hbt },
      { rintros _ ⟨c, hb, rfl⟩,
        refine (Z α).sets_of_superset ht (assume x hxt, _),
        simpa using eqt _ _ hxt hb }
    end)

lemma nhds_zero_eq_Z : nhds 0 = Z α := by simp [nhds_eq]; exact filter.map_id

instance : topological_add_monoid α :=
⟨ continuous_iff_continuous_at.2 $ assume ⟨a, b⟩,
  begin
    rw [continuous_at, nhds_prod_eq, nhds_eq, nhds_eq, nhds_eq, filter.prod_map_map_eq,
      tendsto_map'_iff],
    suffices :  tendsto ((λx:α, (a + b) + x) ∘ (λp:α×α,p.1 + p.2)) (filter.prod (Z α) (Z α))
      (map (λx:α, (a + b) + x) (Z α)),
    { simpa [(∘)] },
    exact tendsto_map.comp add_Z
  end⟩

instance : topological_add_group α :=
⟨continuous_iff_continuous_at.2 $ assume a,
  begin
    rw [continuous_at, nhds_eq, nhds_eq, tendsto_map'_iff],
    suffices : tendsto ((λx:α, x - a) ∘ (λx:α, -x)) (Z α) (map (λx:α, x - a) (Z α)),
    { simpa [(∘)] },
    exact tendsto_map.comp neg_Z
  end⟩

end add_group_with_zero_nhd

section filter_mul
local attribute [instance]
  set.pointwise_one set.pointwise_mul set.pointwise_add filter.pointwise_mul filter.pointwise_add
  filter.pointwise_one

section
variables [topological_space α] [group α] [topological_group α]

@[to_additive is_open_pointwise_add_left]
lemma is_open_pointwise_mul_left {s t : set α} : is_open t → is_open (s * t) := λ ht,
begin
  have : ∀a, is_open ((λ (x : α), a * x) '' t),
    assume a, apply is_open_map_mul_left, exact ht,
  rw pointwise_mul_eq_Union_mul_left,
  exact is_open_Union (λa, is_open_Union $ λha, this _),
end

@[to_additive is_open_pointwise_add_right]
lemma is_open_pointwise_mul_right {s t : set α} : is_open s → is_open (s * t) := λ hs,
begin
  have : ∀a, is_open ((λ (x : α), x * a) '' s),
    assume a, apply is_open_map_mul_right, exact hs,
  rw pointwise_mul_eq_Union_mul_right,
  exact is_open_Union (λa, is_open_Union $ λha, this _),
end

end

section
variables [topological_space α] [comm_group α] [topological_group α]

@[to_additive nhds_pointwise_add]
lemma nhds_pointwise_mul (x y : α) : nhds (x * y) = nhds x * nhds y :=
filter_eq $ set.ext $ assume s,
begin
  rw [← nhds_translation_mul_inv x, ← nhds_translation_mul_inv y, ← nhds_translation_mul_inv (x*y)],
  split,
  { rintros ⟨t, ht, ts⟩,
    rcases exists_nhds_split ht with ⟨V, V_mem, h⟩,
    refine ⟨(λa, a * x⁻¹) ⁻¹' V, ⟨V, V_mem, subset.refl _⟩,
            (λa, a * y⁻¹) ⁻¹' V, ⟨V, V_mem, subset.refl _⟩, _⟩,
    rintros a ⟨v, v_mem, w, w_mem, rfl⟩,
    apply ts,
    simpa [mul_comm, mul_assoc, mul_left_comm] using h (v * x⁻¹) (w * y⁻¹) v_mem w_mem },
  { rintros ⟨a, ⟨b, hb, ba⟩, c, ⟨d, hd, dc⟩, ac⟩,
    refine ⟨b ∩ d, inter_mem_sets hb hd, assume v, _⟩,
    simp only [preimage_subset_iff, mul_inv_rev, mem_preimage_eq] at *,
    rintros ⟨vb, vd⟩,
    refine ac ⟨v * y⁻¹, _, y, _, _⟩,
    { rw ← mul_assoc _ _ _ at vb, exact ba _ vb },
    { apply dc y, rw mul_right_inv, exact mem_of_nhds hd },
    { simp only [inv_mul_cancel_right] } }
end

@[to_additive nhds_is_add_hom]
def nhds_is_mul_hom : is_mul_hom (λx:α, nhds x) := ⟨λ_ _, nhds_pointwise_mul _ _⟩

end

end filter_mul
