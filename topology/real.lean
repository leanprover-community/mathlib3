/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

The real numbers ℝ.

They are constructed as the topological completion of ℚ. With the following steps:
(1) prove that ℚ forms a uniform space.
(2) subtraction and addition are uniform contiunuous functions in this space
(3) for multiplication and inverse this only holds on bounded subsets
(4) ℝ is defined as separated Cauchy filters over ℚ (the separation requires a quotient construction)
(5) extend the uniform continuous functions along the completion
(6) proof field properties using the principle of extension of identities

TODO

generalizations:
* topological groups & rings
* order topologies
* Archimedean fields

-/

import topology.uniform_space topology.topological_structures data.rat algebra.field
noncomputable theory
open classical set lattice filter
local attribute [instance] decidable_inhabited prop_decidable

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

@[simp] lemma quot_mk_image_univ_eq [setoid α] : (λx : α, ⟦x⟧) '' univ = univ :=
set.ext $ assume x, quotient.induction_on x $ assume a, ⟨by simp, assume _, ⟨a, trivial, rfl⟩⟩

lemma forall_subtype_iff {α : Type u} {p : α → Prop} {q : {a // p a} → Prop} :
  (∀x:{a // p a}, q x) ↔ (∀a (h : p a), q ⟨a, h⟩) :=
⟨assume h a ha, h ⟨_, _⟩, assume h ⟨a, ha⟩, h _ _⟩

/- remove when we hava linear arithmetic tactic -/
lemma one_lt_two : 1 < (2 : ℚ) :=
calc (1:ℚ) < 1 + 1 : lt_add_of_le_of_pos (le_refl 1) zero_lt_one
  ... = _ : by simp [bit0]

lemma zero_lt_two : 0 < (2 : ℚ) :=
calc (0:ℚ) < 1 + 1 : lt_add_of_le_of_pos zero_le_one zero_lt_one
  ... = _ : by simp [bit0]

/- rational numbers form a topological group and hence a uniform space -/
def zero_nhd : filter ℚ := (⨅r > 0, principal {q | abs q < r})

lemma mem_zero_nhd {r : ℚ} (h : 0 < r) : {q | abs q < r} ∈ zero_nhd.sets :=
mem_infi_sets r $ mem_infi_sets h $ subset.refl _

lemma mem_zero_nhd_le {r : ℚ} (h : 0 < r) : {q | abs q ≤ r} ∈ zero_nhd.sets :=
zero_nhd.upwards_sets (mem_zero_nhd h) $ assume x, le_of_lt

lemma mem_zero_nhd_iff {s : set ℚ} : s ∈ zero_nhd.sets ↔ ∃r>0, ∀q:ℚ, abs q < r → q ∈ s :=
have directed_on (λx y:ℚ, principal {q | abs q < x} ≤ principal {q | abs q < y}) {r | r > 0},
  from assume x hx y hy,
  have h₁ : ∀a:ℚ, abs a < min x y → abs a < x, from assume a h, lt_of_lt_of_le h (min_le_left _ _),
  have h₂ : ∀a:ℚ, abs a < min x y → abs a < y, from assume a h, lt_of_lt_of_le h (min_le_right _ _),
  ⟨min x y, lt_min hx hy, by simp; exact ⟨h₁, h₂⟩⟩,
show s ∈ (⨅r∈{r:ℚ | r > 0}, principal {q:ℚ | abs q < r}).sets ↔ ∃r>0, ∀q:ℚ, abs q < r → q ∈ s,
begin
  rw [infi_sets_eq' this],
  simp [subset_def],
  show ∃q:ℚ, 0 < q, from ⟨1, zero_lt_one⟩
end

lemma tendsto_zero_nhds {m : α → ℚ} {f : filter α} (hm : ∀r>0, {a | abs (m a) < r} ∈ f.sets) :
  tendsto m f zero_nhd :=
le_infi $ assume i, le_infi $ assume hi : 0 < i, by simp; exact hm i hi

lemma pure_zero_le_zero_nhd : pure 0 ≤ zero_nhd :=
by simp [zero_nhd, le_infi_iff, abs_zero, (>)] {contextual := tt}

lemma tendsto_neg_rat_zero : tendsto has_neg.neg zero_nhd zero_nhd :=
tendsto_zero_nhds $ assume i hi, by simp [abs_neg, mem_zero_nhd hi]

lemma tendsto_add_rat_zero : tendsto (λp:ℚ×ℚ, p.1 + p.2) (filter.prod zero_nhd zero_nhd) zero_nhd :=
tendsto_zero_nhds $ assume i hi,
have 0 < i / 2, from div_pos_of_pos_of_pos hi zero_lt_two,
show {x : ℚ × ℚ | abs (x.1 + x.2) < i} ∈ (filter.prod zero_nhd zero_nhd).sets,
  from filter.upwards_sets _ (prod_mem_prod (mem_zero_nhd this) (mem_zero_nhd this)) $
    assume ⟨a, b⟩ ⟨ha, hb⟩,
    calc abs (a + b) ≤ abs a + abs b : abs_add_le_abs_add_abs _ _
      ... < i/2 + i/2 : add_lt_add ha hb
      ... = (i + i) / 2 : div_add_div_same _ _ _
      ... = i : add_self_div_two _

lemma tendsto_add_rat_zero' {f g : α → ℚ} {x : filter α}
  (hf : tendsto f x zero_nhd) (hg : tendsto g x zero_nhd) : tendsto (λa, f a + g a) x zero_nhd :=
tendsto_compose (tendsto_prod_mk hf hg) tendsto_add_rat_zero

lemma tendsto_sub_rat' {f g : α → ℚ} {x : filter α}
  (hf : tendsto f x zero_nhd) (hg : tendsto g x zero_nhd) : tendsto (λa, f a - g a) x zero_nhd :=
by simp; exact tendsto_add_rat_zero' hf (tendsto_compose hg tendsto_neg_rat_zero)

lemma tendsto_mul_bnd_rat {f : filter ℚ} {r : ℚ} (hr : 0 < r) (hf : {x : ℚ | abs x ≤ r} ∈ f.sets) :
  tendsto (λp:ℚ×ℚ, p.1 * p.2) (filter.prod zero_nhd f) zero_nhd :=
tendsto_zero_nhds $ assume i hi,
have 0 < i / r, from div_pos_of_pos_of_pos hi hr,
show {x : ℚ × ℚ | abs (x.1 * x.2) < i} ∈ (filter.prod zero_nhd f).sets,
  from filter.upwards_sets _ (prod_mem_prod (mem_zero_nhd this) hf) $
    assume ⟨a, b⟩ ⟨ha, hb⟩,
    calc abs (a * b) = abs a * abs b : by simp [abs_mul]
      ... ≤ abs a * r : mul_le_mul_of_nonneg_left hb (abs_nonneg a)
      ... < (i / r) * r : mul_lt_mul_of_pos_right ha hr
      ... = i : div_mul_cancel _ (ne_of_gt hr)

lemma tendsto_mul_bnd_rat' {r : ℚ} {f g : α → ℚ} {x : filter α}
  (hr : 0 < r) (hy : {x : α | abs (g x) ≤ r} ∈ x.sets) (hf : tendsto f x zero_nhd) :
  tendsto (λa, f a * g a) x zero_nhd :=
tendsto_compose (tendsto_prod_mk hf tendsto_map) (tendsto_mul_bnd_rat hr hy)

lemma tendsto_mul_rat' {f g : α → ℚ} {x : filter α}
  (hf : tendsto f x zero_nhd) (hg : tendsto g x zero_nhd) : tendsto (λa, f a * g a) x zero_nhd :=
tendsto_mul_bnd_rat' zero_lt_one (hg $ mem_zero_nhd_le zero_lt_one) hf

set_option eqn_compiler.zeta true
/-- The rational numbers form a uniform space-/
instance : uniform_space ℚ :=
uniform_space.of_core { uniform_space.core .
  uniformity := zero_nhd.vmap (λp, p.1 - p.2),
  refl :=
    have ((λ (p : ℚ × ℚ), p.1 - p.2) '' id_rel) = {0},
      from set.subset.antisymm
        (by simp [set.image_subset_iff_subset_preimage, id_rel] {contextual := tt})
        (assume x hx, ⟨⟨0, 0⟩, begin revert hx, simp [*, id_rel], cc end⟩),
    by simp [le_vmap_iff_map_le, -sub_eq_add_neg, this]; exact pure_zero_le_zero_nhd,
  symm :=
    have (λ (p : ℚ × ℚ), p.fst - p.snd) ∘ prod.swap = has_neg.neg ∘ (λ (p : ℚ × ℚ), p.fst - p.snd),
      from funext $ by simp [(∘)],
    tendsto_vmap' $ by rw [this]; exact tendsto_compose tendsto_vmap tendsto_neg_rat_zero,
  comp :=
    let f := (image (λp:ℚ×ℚ, p.1 - p.2) ∘ (λs, comp_rel s s) ∘ preimage (λp:ℚ×ℚ, p.1 - p.2)) in
    begin
      rw [le_vmap_iff_map_le, map_lift'_eq, vmap_lift'_eq2],
      exact calc zero_nhd.lift' f ≤
          zero_nhd.lift' (image (λp:ℚ×ℚ, p.1 + p.2) ∘ (λs, set.prod s s)) :
            lift'_mono' $
            assume s hs r ⟨⟨p₁, p₂⟩, ⟨q, h₁, h₂⟩, h⟩,
            ⟨⟨p₁ - q, q - p₂⟩, ⟨h₁, h₂⟩,
              calc (p₁ - q) + (q - p₂) = p₁ - p₂ + (q - q) : by simp [-add_right_neg]
                ... = r : by simp [*] at *⟩
        ... = map (λp:ℚ×ℚ, p.1 + p.2) (filter.prod zero_nhd zero_nhd) :
          by rw [←map_lift'_eq, prod_same_eq]; exact monotone_prod monotone_id monotone_id
        ... ≤ zero_nhd : tendsto_add_rat_zero,
      exact monotone_comp (monotone_comp_rel monotone_id monotone_id) monotone_image,
      exact monotone_comp_rel monotone_id monotone_id
    end }

lemma uniformity_rat : uniformity = zero_nhd.vmap (λp:ℚ×ℚ, p.1 - p.2) := rfl

lemma mem_uniformity_rat {r : ℚ} (h : 0 < r) :
  {x:(ℚ × ℚ) | abs (x.1 - x.2) < r} ∈ (@uniformity ℚ _).sets :=
preimage_mem_vmap $ mem_zero_nhd $ h

lemma uniform_continuous_rat [uniform_space α] {f : α → ℚ}
  (hf : tendsto (λp:α×α, f p.1 - f p.2) uniformity zero_nhd ) : uniform_continuous f :=
le_vmap_iff_map_le.mpr $ by rw [map_map]; exact hf

lemma tendsto_sub_uniformity_zero_nhd : tendsto (λp:(ℚ×ℚ), p.1 - p.2) uniformity zero_nhd :=
le_vmap_iff_map_le.mp $ le_refl uniformity

lemma tendsto_sub_uniformity_zero_nhd' {p : α → ℚ} {q : α → ℚ} {f : filter α}
  (h : tendsto (λx, (p x, q x)) f uniformity) : tendsto (λa, p a - q a) f zero_nhd :=
tendsto_compose h tendsto_sub_uniformity_zero_nhd

lemma uniform_continuous_add_rat : uniform_continuous (λp : ℚ × ℚ, p.1 + p.2) :=
uniform_continuous_rat $
have tendsto (λp:(ℚ×ℚ)×(ℚ×ℚ), (p.1.1 - p.2.1) + (p.1.2 - p.2.2)) uniformity zero_nhd,
  from tendsto_add_rat_zero'
    (tendsto_sub_uniformity_zero_nhd' tendsto_prod_uniformity_fst)
    (tendsto_sub_uniformity_zero_nhd' tendsto_prod_uniformity_snd),
have (λp:(ℚ×ℚ)×(ℚ×ℚ), (p.1.1 + p.1.2) - (p.2.1 + p.2.2)) = (λp, (p.1.1 - p.2.1) + (p.1.2 - p.2.2)),
  from funext $ by simp,
by rwa [this]

lemma uniform_continuous_neg_rat : uniform_continuous (λr:ℚ, -r) :=
have (λ (p : ℚ × ℚ), -p.fst - -p.snd) = (λ (p : ℚ × ℚ), p.fst - p.snd) ∘ prod.swap,
  from funext $ by simp [(∘)],
uniform_continuous_rat $
  by rw [this]; exact tendsto_compose tendsto_swap_uniformity tendsto_sub_uniformity_zero_nhd

instance : topological_add_group ℚ :=
{ continuous_add := continuous_of_uniform uniform_continuous_add_rat,
  continuous_neg := continuous_of_uniform uniform_continuous_neg_rat }

lemma nhds_eq_map_zero_nhd {r : ℚ} : nhds r = map (λx, x + r) zero_nhd :=
begin
  have h : ((λ (s : set (ℚ × ℚ)), {y : ℚ | (r, y) ∈ s}) ∘
         preimage ((λ (p : ℚ × ℚ), p.fst - p.snd) ∘ prod.swap)) = image (λx, x + r) ∘ id,
  { simp [(∘)],
    apply (image_eq_preimage_of_inverse _ _ _ _).symm,
    exact assume x, calc r + x + -r = x + (r + -r) : by cc
       ... = x : by simp,
    exact assume x, calc r + (x + -r) = x + (r + -r) : by cc
       ... = x : by simp },
  rw [nhds_eq_uniformity, uniformity_eq_symm, map_swap_vmap_swap_eq],
  change (vmap (prod.swap : ℚ×ℚ → ℚ×ℚ) (zero_nhd.vmap (λp, p.1 - p.2))).lift'
    (λ (s : set (ℚ × ℚ)), {y : ℚ | (r, y) ∈ s}) = _,
  rw [vmap_vmap_comp, vmap_lift'_eq2, h, ←map_lift'_eq, lift'_id],
  apply monotone_preimage,
  apply monotone_preimage
end

lemma lt_mem_nhds {r q : ℚ} (h : r < q) : {x | r < x} ∈ (nhds q).sets :=
have 0 < q - r, from lt_sub_left_of_add_lt $ by simp [h],
begin
  rw [nhds_eq_map_zero_nhd],
  show {x | r < x + q} ∈ zero_nhd.sets,
  apply zero_nhd.upwards_sets (mem_zero_nhd this),
  exact (assume x (h : abs x < q - r),
    calc  r < q - abs x : lt_sub_left_of_add_lt $ add_lt_of_lt_sub_right h
      ... ≤ q - (- x) : sub_le_sub (le_refl q) (neg_le_abs_self x)
      ... ≤ x + q : by simp)
end

lemma le_mem_nhds {r q : ℚ} (h : r < q) : {x | r ≤ x} ∈ (nhds q).sets :=
(nhds q).upwards_sets (lt_mem_nhds h) $ assume x, le_of_lt

lemma gt_mem_nhds {r q : ℚ} (h : q < r) : {x | x < r} ∈ (nhds q).sets :=
have tendsto (λx:ℚ, -x) (nhds q) (nhds (-q)),
  from tendsto_neg tendsto_id,
have {x | -r < -x} ∈ (nhds q).sets,
  from this $ lt_mem_nhds $ neg_lt_neg $ h,
(nhds q).upwards_sets this $ assume x (h : -r < -x), lt_of_neg_lt_neg h

lemma ge_mem_nhds {r q : ℚ} (h : q < r) : {x | x ≤ r} ∈ (nhds q).sets :=
(nhds q).upwards_sets (gt_mem_nhds h) $ assume x, le_of_lt

instance : linear_ordered_topology ℚ :=
⟨assume r:ℚ, by simp [is_open_iff_nhds]; exact assume a, lt_mem_nhds,
  assume r:ℚ, by simp [is_open_iff_nhds]; exact assume a, gt_mem_nhds⟩

lemma uniform_embedding_add_rat {r : ℚ} : uniform_embedding (λp:ℚ, p + r) :=
⟨assume a b (h : a + r = b + r),
  calc a = (a + r) - r : by rw [add_sub_assoc]; simp
    ... = (b + r) - r : by rw [h]
    ... = b : by rw [add_sub_assoc]; simp,
  have h : ∀{a b}, r + (a + (-r + -b)) = a + -b,
    from assume a b, calc r + (a + (-r + -b)) = r + (-r + (a + -b)) : by simp
      ... = _ : by rw [←add_assoc]; simp,
  by simp [uniformity_rat, vmap_vmap_comp, (∘), h]⟩

lemma uniform_embedding_mul_rat {q : ℚ} (hq : q ≠ 0) : uniform_embedding (λp:ℚ, p * q) :=
⟨assume a b (h : a * q = b * q),
  calc a = (a * q) / q : by rw [mul_div_cancel]; exact hq; simp
    ... = (b * q) / q : by rw [h]
    ... = b : by rw [mul_div_cancel]; exact hq; simp,
  have h₁ : ((λ (p : ℚ × ℚ), p.1 + -p.2) ∘ (λ (x : ℚ × ℚ), (q * x.1, q * x.2))) =
    ((*) q ∘ (λ (p : ℚ × ℚ), p.1 + -p.2)),
    by simp [(∘), mul_add],
  have h₂ : vmap ((*) q) zero_nhd = zero_nhd,
    from le_antisymm
      (le_infi $ assume r, le_infi $ assume hr, le_principal_iff.mpr $
        ⟨{s:ℚ | abs s < abs q * r},
          mem_zero_nhd $ mul_pos (abs_pos_of_ne_zero hq) hr,
          begin
            simp [abs_mul],
            rw [mul_comm],
            exact assume a ha, lt_of_mul_lt_mul_left ha (abs_nonneg q)
          end⟩)
      (le_vmap_iff_map_le.mpr $ le_infi $ assume r, le_infi $ assume hr,
        have ∀x:ℚ, abs (q * x) < r ↔ abs x < r / abs q,
          by simp [abs_mul, lt_div_iff (abs_pos_of_ne_zero hq)],
        by simp [this]; exact (mem_zero_nhd $ div_pos_of_pos_of_pos hr (abs_pos_of_ne_zero hq))),
  by simp [uniformity_rat, vmap_vmap_comp, h₁]; rw [←vmap_vmap_comp, h₂]⟩

lemma nhds_0_eq_zero_nhd : nhds 0 = zero_nhd :=
have (λ (x : ℚ), x + 0) = id, from funext $ by simp,
by rw [nhds_eq_map_zero_nhd, this]; simp

lemma uniform_continuous_inv_pos_rat {r : ℚ} (hr : 0 < r) :
  uniform_continuous (λp:{q:ℚ // r ≤ q}, p.1⁻¹) :=
have h : ∀{v:{q:ℚ // r ≤ q}}, v.val ≠ 0,
  from assume ⟨v, hv⟩, ne_of_gt $ lt_of_lt_of_le hr hv,
have hrr : 0 < 1 / (r * r),
  from div_pos_of_pos_of_pos zero_lt_one $ mul_pos hr hr,
uniform_continuous_rat
  begin
    conv { congr, funext, rw [inv_sub_inv_eq h h, div_eq_mul_one_div] },
    apply tendsto_mul_bnd_rat' hrr _ _,
    exact (univ_mem_sets' $ assume ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩,
      have 0 < a₁, from lt_of_lt_of_le hr ha₁,
      have 0 < a₂, from lt_of_lt_of_le hr ha₂,
      show abs (1 / (a₁ * a₂)) ≤ 1 / (r * r),
      begin
        simp [abs_mul, abs_inv, abs_of_pos ‹0<a₁›, abs_of_pos ‹0<a₂›],
        rw [inv_eq_one_div, inv_eq_one_div],
        exact one_div_le_one_div_of_le (mul_pos hr hr) (mul_le_mul ha₁ ha₂ (le_of_lt hr) (le_of_lt ‹0 < a₁›))
      end),
    apply tendsto_sub_uniformity_zero_nhd'
      (tendsto_compose tendsto_swap_uniformity uniform_continuous_subtype_val)
  end

lemma tendsto_of_uniform_continuous_subtype
  [uniform_space α] [uniform_space β] {f: α → β} {p : α → Prop} {a : α}
  (hf : uniform_continuous (λx:{a // p a}, f x.val)) (ha : {a | p a} ∈ (nhds a).sets) :
  tendsto f (nhds a) (nhds (f a)) :=
by
  rw [(@map_nhds_subtype_val_eq α _ p a (mem_of_nhds ha) ha).symm];
  exact (tendsto_map' $ (continuous_iff_tendsto.mp $ continuous_of_uniform $ hf) _)

lemma uniform_continuous_rat' {f : ℚ → ℚ}
  (h : ∀i>0, ∃j>0, ∀a₁ a₂, abs (a₁ - a₂) < j → abs (f a₁ - f a₂) < i) : uniform_continuous f :=
uniform_continuous_rat $
  le_infi $ assume i, le_infi $ assume hi, le_vmap_iff_map_le.mp $
  let ⟨j, hj, hjf⟩ := h i hi in
  show zero_nhd.vmap (λp:ℚ×ℚ, p.1 - p.2) ≤ _,
  begin
    simp [zero_nhd, vmap_infi, -le_principal_iff],
    exact (infi_le_of_le j $ infi_le_of_le hj $ principal_mono.mpr $ assume ⟨a₁, a₂⟩, hjf a₁ a₂)
  end

lemma uniform_continuous_abs_rat : uniform_continuous (abs : ℚ → ℚ) :=
uniform_continuous_rat' $ assume i (hi : 0 < i),
  ⟨i, hi, assume a₁ a₂ ha, lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _) ha⟩

lemma continuous_abs_rat : continuous (abs : ℚ → ℚ) :=
continuous_of_uniform uniform_continuous_abs_rat

lemma tendsto_inv_pos_rat {r : ℚ} (hr : 0 < r) : tendsto (λq, q⁻¹) (nhds r) (nhds r⁻¹) :=
have r / 2 < r / 1, from div_lt_div_of_pos_of_lt_of_pos zero_lt_one one_lt_two hr,
have r / 2 < r, by simp [div_one] at this; assumption,
have 0 < r / 2,
  from div_pos_of_pos_of_pos hr two_pos,
tendsto_of_uniform_continuous_subtype (uniform_continuous_inv_pos_rat this) (le_mem_nhds ‹r/2<r›)

lemma tendsto_inv_rat {r : ℚ} (hr : r ≠ 0) : tendsto (λq, q⁻¹) (nhds r) (nhds r⁻¹) :=
if h : 0 < r then tendsto_inv_pos_rat h else
have r < 0, from lt_of_le_of_ne (le_of_not_gt h) hr,
have 0 < -r, from lt_neg_of_lt_neg $ by simp * at *,
have tendsto (λq, - (-q)⁻¹) (nhds r) (nhds (- (-r)⁻¹)),
  from tendsto_neg $ tendsto_compose (tendsto_neg tendsto_id) (tendsto_inv_pos_rat this),
by simp [inv_neg] at this; assumption

lemma uniform_continuous_mul_rat {r₁ r₂ : ℚ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
  uniform_continuous (λp:{q:ℚ // abs q ≤ r₁}×{q:ℚ // abs q ≤ r₂}, p.1.1 * p.2.1) :=
have h : ∀a₁ a₂ b₁ b₂ : ℚ, a₁ * a₂ - b₁ * b₂ = (a₁ - b₁) * a₂ + (a₂ - b₂) * a₁ - (a₁ - b₁) * (a₂ - b₂),
  from assume a₁ a₂ b₁ b₂, calc
    a₁ * a₂ - b₁ * b₂ =
          a₁ * a₂ + a₁ * b₂ + a₂ * b₁ + -(a₁ * b₂) + -(a₂ * b₁) + -(b₁ * b₂) : by simp
    ... = a₁ * a₂ + (a₁ * b₂ + (a₂ * b₁ + (-(a₁ * b₂) + (-(a₂ * b₁) + -(b₁ * b₂))))) : by cc
    ... = (a₁ - b₁) * a₂ + (a₂ - b₂) * a₁ - (a₁ - b₁) * (a₂ - b₂) : by simp [mul_add, add_mul],
uniform_continuous_rat
  begin
    conv in (_ *_ - _* _) { rw h },
    apply tendsto_sub_rat' _ _,
    apply tendsto_add_rat_zero' _ _,
    exact tendsto_mul_bnd_rat' hr₂
      (univ_mem_sets' $ assume ⟨⟨_, ⟨a, ha⟩⟩, _⟩, ha)
      (tendsto_sub_uniformity_zero_nhd'
        (tendsto_compose tendsto_prod_uniformity_fst uniform_continuous_subtype_val)),
    exact tendsto_mul_bnd_rat' hr₁
      (univ_mem_sets' $ assume ⟨⟨⟨a, ha⟩, _⟩, _⟩, ha)
      (tendsto_sub_uniformity_zero_nhd'
        (tendsto_compose tendsto_prod_uniformity_snd uniform_continuous_subtype_val)),
    exact tendsto_mul_rat'
      (tendsto_sub_uniformity_zero_nhd'
        (tendsto_compose tendsto_prod_uniformity_fst uniform_continuous_subtype_val))
      (tendsto_sub_uniformity_zero_nhd'
        (tendsto_compose tendsto_prod_uniformity_snd uniform_continuous_subtype_val))
  end

private lemma uniform_continuous_swap [uniform_space α] [uniform_space β] {p : α → Prop} {q : β → Prop} :
  uniform_continuous (λx:{x:α×β // p x.1 ∧ q x.2},
     ((⟨x.val.1, x.property.left⟩ : {x // p x}), (⟨x.val.2, x.property.right⟩ : {x // q x}))) :=
uniform_continuous_prod_mk
  (uniform_continuous_subtype_mk
    (uniform_continuous_compose uniform_continuous_subtype_val uniform_continuous_fst) _)
  (uniform_continuous_subtype_mk
    (uniform_continuous_compose uniform_continuous_subtype_val uniform_continuous_snd) _)

private lemma tendsto_mul_rat {r q : ℚ} : tendsto (λp:ℚ×ℚ, p.1 * p.2) (nhds (r, q)) (nhds (r * q)) :=
have hr : ∀{r:ℚ}, 0 < abs r + 1, from assume r, lt_add_of_le_of_pos (abs_nonneg r) zero_lt_one,
have ∀{r:ℚ}, {q | abs q ≤ abs r + 1} ∈ (nhds r).sets,
  from assume r,
  have -1 + -abs r < r,
    from calc -1 + -abs r < -abs r : add_lt_of_lt_neg_add $ lt_add_of_pos_left _ zero_lt_one
      ... ≤ r : neg_le_of_neg_le $ neg_le_abs_self _,
  have r < 1 + abs r, from lt_of_le_of_lt (le_abs_self r) (lt_add_of_pos_left _ zero_lt_one),
  have {q : ℚ | q ≤ 1 + abs r} ∩ {q:ℚ | -1 + -abs r ≤ q} ∈ (nhds r).sets,
    from inter_mem_sets (ge_mem_nhds ‹r < 1 + abs r›) (le_mem_nhds ‹-1 + -abs r < r›),
  by simp [abs_le_iff]; exact this,
have h : {a : ℚ × ℚ | abs (a.fst) ≤ abs r + 1 ∧ abs (a.snd) ≤ abs q + 1} ∈ (nhds (r, q)).sets,
  by rw [nhds_prod_eq]; exact prod_mem_prod this this,
have uniform_continuous (λp:{p:ℚ×ℚ // abs p.1 ≤ abs r + 1 ∧ abs p.2 ≤ abs q + 1}, p.1.1 * p.1.2),
  from uniform_continuous_compose uniform_continuous_swap
    (uniform_continuous_mul_rat hr hr),
tendsto_of_uniform_continuous_subtype this h

instance : topological_ring ℚ :=
{ rat.topological_add_group with
  continuous_mul := continuous_iff_tendsto.mpr $ assume ⟨r, q⟩, tendsto_mul_rat }

lemma totally_bounded_01_rat : totally_bounded {q:ℚ | 0 ≤ q ∧ q ≤ 1} :=
assume s (hs : s ∈ uniformity.sets),
have s ∈ (zero_nhd.vmap (λp:ℚ×ℚ, p.1 - p.2)).sets, by rw [←uniformity_rat]; exact hs,
let ⟨t, ht, (hst : _ ⊆ _)⟩ := this, ⟨e, he, het⟩ := by rw [mem_zero_nhd_iff] at ht; exact ht in
let n := λq, rat.nat_ceil (q / e) in
let c := (λi, ↑i * e) '' {i:ℕ | i ≤ n 1} in
have ∀q, 0 ≤ q → q ≤ 1 → ∃i∈c, abs (q - i) < e,
  from assume q hq0 hq1,
  have hnn: 0 ≤ ↑(n q) * e - q,
    from le_sub_left_of_add_le $ le_mul_of_div_le he $ by simp; exact rat.nat_ceil_spec,
  have hbnd : ↑(n q) * e - q < e,
    from have ↑(n q) < q / e + 1,
      from rat.nat_ceil_lt_add_one $ div_nonneg_of_nonneg_of_pos hq0 he,
    sub_left_lt_of_lt_add $ calc
      ↑(n q) * e < (q / e + 1) * e : mul_lt_mul_of_pos_right this he
      ... = q + e : begin rw [add_mul, div_mul_cancel], simp, exact ne_of_gt he end,
  ⟨n q * e,
    mem_image_of_mem _ $ rat.nat_ceil_mono $ div_le_div_of_le_of_pos hq1 he,
    by rwa [abs_sub, abs_of_nonneg hnn]⟩,
⟨c, finite_image $ finite_le_nat,
  assume r ⟨hr0, hr1⟩,
  let ⟨i, hi, hie⟩ := this r hr0 hr1 in
  by simp; exact ⟨i, hi, @hst (r,i) $ het _ hie⟩⟩

def real : Type := quotient (separation_setoid (Cauchy ℚ))
notation `ℝ` := real

section
local attribute [instance] separation_setoid
open Cauchy

instance : uniform_space ℝ  := by unfold real; apply_instance
instance : complete_space ℝ := by apply complete_space_separation; apply_instance
instance : separated ℝ      := separated_separation

def of_rat (q : ℚ) : ℝ := ⟦pure_cauchy q⟧

instance : has_zero ℝ := ⟨of_rat 0⟩
instance : has_one ℝ := ⟨of_rat 1⟩
instance inhabited_ℝ : inhabited ℝ := ⟨0⟩

lemma uniform_embedding_of_rat : uniform_embedding of_rat :=
⟨assume a b h,
  have a_rel_b : pure_cauchy a ≈ pure_cauchy b, from quotient.exact h,
  classical.by_contradiction $ assume : a ≠ b,
    have a - b ≠ 0, from assume h, ‹a ≠ b› $ sub_eq_zero_iff_eq.mp h,
    have 0 < abs (a - b), from abs_pos_of_ne_zero this,
    have {p:ℚ×ℚ | abs (p.1 - p.2) < abs (a - b)} ∈ (@uniformity ℚ _).sets,
      from preimage_mem_vmap $ mem_zero_nhd this,
    have {p:ℚ×ℚ | abs (p.1 - p.2) < abs (a - b)} ∈
      (vmap (λp:ℚ×ℚ, (pure_cauchy p.1, pure_cauchy p.2)) uniformity).sets,
      by rwa [uniform_embedding_pure_cauchy.right],
    let ⟨s, hs, (h : preimage _ s ⊆ _)⟩ := this in
    have abs (a - b) < abs (a - b), from @h (a, b) (a_rel_b s hs),
    show false, from lt_irrefl _ this,
  calc vmap (λp:ℚ×ℚ, (of_rat p.1, of_rat p.2)) uniformity =
    vmap (λp:ℚ×ℚ, (pure_cauchy p.1, pure_cauchy p.2))
      (vmap (λp:Cauchy ℚ×Cauchy ℚ, (⟦p.1⟧, ⟦p.2⟧)) uniformity) : by rw [vmap_vmap_comp]; refl
    ... = _ : by rw [vmap_quotient_eq_uniformity, uniform_embedding_pure_cauchy.right] ⟩

lemma dense_embedding_of_rat : dense_embedding of_rat :=
have univ ⊆ closure (of_rat '' univ),
  from calc univ ⊆ (λx:Cauchy ℚ, ⟦x⟧) '' univ : by simp [closure_univ, -univ_subtype]
    ... ⊆ (λx:Cauchy ℚ, ⟦x⟧) '' closure (pure_cauchy '' univ) :
      mono_image $ assume x hx, pure_cauchy_dense x
    ... ⊆ closure ((λx:Cauchy ℚ, ⟦x⟧) '' (pure_cauchy '' univ)) :
      image_closure_subset_closure_image $ continuous_of_uniform $ uniform_continuous_quotient_mk
    ... = _ : by rw [←image_comp]; refl,
dense_embedding_of_uniform_embedding uniform_embedding_of_rat $ assume x, this trivial

lemma dense_embedding_of_rat_of_rat : dense_embedding (λp:ℚ×ℚ, (of_rat p.1, of_rat p.2)) :=
dense_embedding_of_rat.prod dense_embedding_of_rat

def lift_rat_fun (f : ℚ → ℚ) : ℝ → ℝ := dense_embedding_of_rat.ext (of_rat ∘ f)
def lift_rat_op (f : ℚ → ℚ → ℚ) (a : ℝ) (b : ℝ) : ℝ :=
dense_embedding_of_rat_of_rat.ext (of_rat ∘ (λp:ℚ×ℚ, f p.1 p.2)) (a, b)

lemma lift_rat_fun_of_rat {r : ℚ} {f : ℚ → ℚ} (hf : tendsto f (nhds r) (nhds (f r))) :
  lift_rat_fun f (of_rat r) = of_rat (f r) :=
dense_embedding_of_rat.ext_e_eq $ tendsto_compose hf $ dense_embedding_of_rat.tendsto

lemma lift_rat_op_of_rat_of_rat {r₁ r₂: ℚ} {f : ℚ → ℚ → ℚ}
  (hf : tendsto (λp:ℚ×ℚ, f p.1 p.2) (nhds (r₁, r₂)) (nhds (f r₁ r₂))) :
  lift_rat_op f (of_rat r₁) (of_rat r₂) = of_rat (f r₁ r₂) :=
let h := dense_embedding_of_rat_of_rat.ext_e_eq (tendsto_compose hf dense_embedding_of_rat.tendsto)
in h

instance : has_add ℝ := ⟨lift_rat_op (+)⟩
instance : has_neg ℝ := ⟨lift_rat_fun has_neg.neg⟩
instance : has_sub ℝ := ⟨λx y, x + - y⟩
instance : has_mul ℝ := ⟨lift_rat_op (*)⟩
instance : has_inv ℝ := ⟨λa:ℝ, if a = 0 then 0 else lift_rat_fun has_inv.inv a⟩
instance : has_div ℝ := ⟨λx y, x * y⁻¹⟩

lemma of_rat_zero : 0 = of_rat 0 := rfl

lemma of_rat_one : 1 = of_rat 1 := rfl

lemma of_rat_neg {r : ℚ} : - of_rat r = of_rat (- r) :=
lift_rat_fun_of_rat $ continuous_iff_tendsto.mp (continuous_of_uniform uniform_continuous_neg_rat) r

lemma of_rat_add {r₁ r₂ : ℚ} : of_rat r₁ + of_rat r₂ = of_rat (r₁ + r₂) :=
lift_rat_op_of_rat_of_rat $
  continuous_iff_tendsto.mp (continuous_of_uniform uniform_continuous_add_rat) (r₁, r₂)

lemma of_rat_sub {r₁ r₂ : ℚ} : of_rat r₁ - of_rat r₂ = of_rat (r₁ - r₂) :=
by simp [has_sub.sub, of_rat_add, of_rat_neg]

lemma of_rat_mul {r₁ r₂ : ℚ} : of_rat r₁ * of_rat r₂ = of_rat (r₁ * r₂) :=
lift_rat_op_of_rat_of_rat tendsto_mul_rat

lemma of_rat_inv {r : ℚ} : (of_rat r)⁻¹ = of_rat r⁻¹ :=
show (if of_rat r = 0 then 0 else lift_rat_fun has_inv.inv (of_rat r)) = of_rat r⁻¹,
  from if h : r = 0 then by simp [h, inv_zero, of_rat_zero]
    else
      have of_rat r ≠ 0, from h ∘ dense_embedding_of_rat.inj _ _,
      by simp [this]; exact lift_rat_fun_of_rat (tendsto_inv_rat h)

local attribute [simp] of_rat_zero of_rat_one of_rat_neg of_rat_add of_rat_sub of_rat_mul of_rat_inv

lemma uniform_continuous_neg_real : uniform_continuous (λp:ℝ, - p) :=
uniform_continuous_uniformly_extend uniform_embedding_of_rat dense_embedding_of_rat.dense $
  uniform_continuous_compose
    uniform_continuous_neg_rat
    (uniform_continuous_of_embedding uniform_embedding_of_rat)

lemma uniform_continuous_add_real : uniform_continuous (λp:ℝ×ℝ, p.1 + p.2) :=
begin
  rw [real.has_add], simp [lift_rat_op], -- TODO: necessary, otherwise elaborator doesn't terminate
  exact (uniform_continuous_uniformly_extend
    (uniform_embedding_prod uniform_embedding_of_rat uniform_embedding_of_rat)
    dense_embedding_of_rat_of_rat.dense
    (uniform_continuous_compose uniform_continuous_add_rat
      (uniform_continuous_of_embedding uniform_embedding_of_rat)))
end

private lemma continuous_neg_real : continuous (λp:ℝ, - p) :=
continuous_of_uniform uniform_continuous_neg_real

private lemma continuous_add_real' : continuous (λp:ℝ×ℝ, p.1 + p.2) :=
continuous_of_uniform uniform_continuous_add_real

private lemma continuous_add_real [topological_space α] {f g : α → ℝ}
  (hf : continuous f) (hg : continuous g) : continuous (λx, f x + g x) :=
continuous_compose (continuous_prod_mk hf hg) continuous_add_real'

instance : add_comm_group ℝ :=
{ add_comm_group .
  zero         := 0,
  add          := (+),
  neg          := has_neg.neg,
  zero_add     := is_closed_property dense_embedding_of_rat.closure_image_univ
    (is_closed_eq (continuous_add_real continuous_const continuous_id) continuous_id)
    begin intros, show of_rat 0 + of_rat a = of_rat a, rw [of_rat_add], simp end,
  add_zero     := is_closed_property dense_embedding_of_rat.closure_image_univ
    (is_closed_eq (continuous_add_real continuous_id continuous_const) continuous_id)
    begin intros, show of_rat a + of_rat 0 = of_rat a, rw [of_rat_add], simp end,
  add_comm     := is_closed_property2 dense_embedding_of_rat
    (is_closed_eq (continuous_add_real continuous_fst continuous_snd) (continuous_add_real continuous_snd continuous_fst))
    (by simp),
  add_assoc    := is_closed_property3 dense_embedding_of_rat
    (is_closed_eq (continuous_add_real
        (continuous_add_real continuous_fst $ continuous_compose continuous_snd continuous_fst) $
        continuous_compose continuous_snd continuous_snd)
      (continuous_add_real continuous_fst $
        continuous_add_real (continuous_compose continuous_snd continuous_fst) $
        continuous_compose continuous_snd continuous_snd))
    (by intros; simp),
  add_left_neg := is_closed_property dense_embedding_of_rat.closure_image_univ
    (is_closed_eq (continuous_add_real continuous_neg_real continuous_id) continuous_const)
    (by simp) }

instance : topological_add_group ℝ :=
{ continuous_add := continuous_add_real',
  continuous_neg := continuous_neg_real }

def nonneg : set ℝ := closure (of_rat '' {q : ℚ | q ≥ 0})

instance : has_le ℝ := ⟨λa b, b - a ∈ nonneg⟩

lemma of_rat_mem_nonneg {q : ℚ} (h : 0 ≤ q) : of_rat q ∈ nonneg :=
have of_rat q ∈ of_rat '' {q:ℚ | q ≥ 0}, from ⟨q, h, rfl⟩,
subset_closure this

lemma of_rat_mem_nonneg_iff {q : ℚ} : of_rat q ∈ nonneg ↔ 0 ≤ q :=
⟨ begin
    rw [nonneg, ←closure_induced, ←dense_embedding_of_rat.embedding.right, closure_eq_of_is_closed],
    exact id,
    exact is_closed_le continuous_const continuous_id,
    exact dense_embedding_of_rat.inj
  end,
  of_rat_mem_nonneg⟩

lemma of_rat_le_of_rat {q₁ q₂ : ℚ} : of_rat q₁ ≤ of_rat q₂ ↔ q₁ ≤ q₂ :=
show (of_rat q₂ - of_rat q₁) ∈ nonneg ↔ q₁ ≤ q₂,
  by rw [of_rat_sub, of_rat_mem_nonneg_iff, le_sub_iff_add_le]; simp

lemma two_eq_of_rat_two : 2 = of_rat 2 := by simp [bit0, -of_rat_add, of_rat_add.symm]

lemma mem_nonneg_of_continuous2 {f : ℝ → ℝ → ℝ} {a b : ℝ}
  (hf : continuous (λp:ℝ×ℝ, f p.1 p.2)) (ha : a ∈ nonneg) (hb : b ∈ nonneg)
  (h : ∀{a b : ℚ}, 0 ≤ a → 0 ≤ b → f (of_rat a) (of_rat b) ∈ nonneg) :
  (f a b) ∈ nonneg :=
mem_closure_of_continuous2 hf ha hb $ assume a ⟨a', ha, ha'⟩ b ⟨b', hb, hb'⟩, ha' ▸ hb' ▸ h ha hb

lemma zero_le_iff_nonneg {r : ℝ} : 0 ≤ r ↔ r ∈ nonneg :=
show (r - 0) ∈ nonneg ↔ r ∈ nonneg, by simp [-of_rat_zero]

private def abs_real := lift_rat_fun abs

private lemma uniform_continuous_abs_real' : uniform_continuous abs_real :=
uniform_continuous_uniformly_extend uniform_embedding_of_rat dense_embedding_of_rat.dense $
  uniform_continuous_compose
  uniform_continuous_abs_rat (uniform_continuous_of_embedding uniform_embedding_of_rat)

private lemma continuous_abs_real' : continuous abs_real :=
continuous_of_uniform uniform_continuous_abs_real'

private lemma of_rat_abs_real {r} : abs_real (of_rat r) = of_rat (abs r) :=
lift_rat_fun_of_rat $ continuous_iff_tendsto.mp (continuous_of_uniform uniform_continuous_abs_rat) r

private lemma abs_real_neg : ∀{r}, abs_real (- r) = abs_real r :=
is_closed_property dense_embedding_of_rat.closure_image_univ
  (is_closed_eq (continuous_compose continuous_neg' continuous_abs_real') continuous_abs_real')
  (by simp [of_rat_abs_real, abs_neg])

private lemma abs_real_of_nonneg {r:ℝ} : 0 ≤ r → abs_real r = r :=
let de := dense_embedding_of_rat.subtype (λq:ℚ, 0 ≤ q) in
have ∀r:{x // x ∈ nonneg}, abs_real r.val = r.val,
  from is_closed_property de.closure_image_univ
    (is_closed_eq (continuous_compose continuous_subtype_val continuous_abs_real') continuous_subtype_val)
    (by simp [forall_subtype_iff, dense_embedding.subtype_emb, of_rat_abs_real];
      exact (assume a ha, congr_arg of_rat $ abs_of_nonneg ha) ),
by rw [zero_le_iff_nonneg]; intro hr; exact this ⟨r, hr⟩

lemma eq_0_of_nonneg_of_neg_nonneg {r : ℝ} (hp : r ∈ nonneg) (hn : -r ∈ nonneg) : r = 0 :=
let d := lift_rat_fun (λq, q * (1 / 2)) in
have uniform_continuous (λq:ℚ, q * (1 / 2)),
  from uniform_continuous_of_embedding $ uniform_embedding_mul_rat $
        ne_of_gt $ div_pos_of_pos_of_pos zero_lt_one zero_lt_two,
have c_d : continuous d,
  from continuous_of_uniform $
    uniform_continuous_uniformly_extend uniform_embedding_of_rat dense_embedding_of_rat.dense $
    uniform_continuous_compose this (uniform_continuous_of_embedding uniform_embedding_of_rat),
have d_of_rat : ∀q:ℚ, d (of_rat q) = of_rat (q * (1 / 2)),
  from assume q, @lift_rat_fun_of_rat q (λq, q * (1 / 2)) $
    continuous_iff_tendsto.mp (continuous_of_uniform this) q,
let f := λr, abs_real (- r) + (- r) in
have continuous f,
  from continuous_add (continuous_compose continuous_neg' continuous_abs_real') continuous_neg',
have ∀ r∈nonneg, f r ∈ closure ({0} : set ℝ),
  from assume r hr, @mem_closure_of_continuous ℝ ℝ _ _ f r _ _ this hr $
    show ∀ (a : ℝ), a ∈ of_rat '' {q : ℚ | q ≥ 0} → abs_real (- a) + (- a) ∈ closure ({0}:set ℝ),
      from assume a ⟨q, (hq : 0 ≤ q), hrq⟩,
      by simp [hrq.symm, of_rat_abs_real, abs_neg, abs_of_nonneg hq],
have h₁ : ∀{r}, r ∈ nonneg → abs_real (- r) + (- r) = 0,
  from assume r hr, show f r = 0, by simp [closure_singleton] at this; exact this _ hr,
have h₂ : ∀r, r = d (r + r),
  from is_closed_property dense_embedding_of_rat.closure_image_univ
    (is_closed_eq continuous_id $ continuous_compose (continuous_add continuous_id continuous_id) c_d)
    begin
      intro a,
      have h : (a + a) * 2⁻¹ = a,
        from calc (a + a) * 2⁻¹ = (a + a) / 2 : by rw [div_eq_mul_one_div]; simp
          ... = a : add_self_div_two a,
      simp [d_of_rat, add_self_div_two, h]
    end,
have r + r = 0,
  from calc r + r = (abs_real (- - r) + (- - r)) - (abs_real (-r) + - r) : by simp [abs_real_neg, -of_rat_zero]
    ... = 0 : by rw [h₁ hp, h₁ hn]; simp,
calc r = d (r + r) : h₂ r
  ... = 0 : by rw [this]; simp [d_of_rat]

lemma preimage_neg_real : preimage (has_neg.neg : ℝ → ℝ) = image (has_neg.neg : ℝ → ℝ) :=
(image_eq_preimage_of_inverse _ _ neg_neg neg_neg).symm

lemma neg_preimage_closure {s : set ℝ} : (λr:ℝ, -r) ⁻¹' closure s = closure ((λr:ℝ, -r) '' s) :=
have (λr:ℝ, -r) ∘ (λr:ℝ, -r) = id, from funext neg_neg,
by rw [preimage_neg_real]; exact
  (subset.antisymm (image_closure_subset_closure_image continuous_neg_real) $
    calc closure ((λ (r : ℝ), -r) '' s) = (λr, -r) '' ((λr, -r) '' closure ((λ (r : ℝ), -r) '' s)) :
        by rw [←image_comp, this, image_id]
      ... ⊆ (λr, -r) '' closure ((λr, -r) '' ((λ (r : ℝ), -r) '' s)) :
        mono_image $ image_closure_subset_closure_image continuous_neg_real
      ... = _ : by rw [←image_comp, this, image_id])

instance : linear_order ℝ :=
{ le := (≤),
  le_refl := assume a, show (a - a) ∈ nonneg, by simp; exact of_rat_mem_nonneg (le_refl _),
  le_trans := assume a b c (h₁ : b - a ∈ nonneg) (h₂ : c - b ∈ nonneg),
    have (c - b) + (b - a) ∈ nonneg,
      from mem_nonneg_of_continuous2 continuous_add' h₂ h₁ $
        assume a b ha hb, by rw [of_rat_add]; exact of_rat_mem_nonneg (le_add_of_le_of_nonneg ha hb),
    have (c - b) + (b - a) = c - a,
      from calc (c - b) + (b - a) = c + - a + (b + -b) : by simp [-add_right_neg]
        ... = c - a : by simp [-of_rat_zero],
    show (c - a) ∈ nonneg, by simp * at *,
  le_antisymm := assume a b (h₁ : b - a ∈ nonneg)  (h₂ : a - b ∈ nonneg),
    have h₁ : - (a - b) ∈ nonneg, by simp at h₁; simp [*],
    eq_of_sub_eq_zero $ eq_0_of_nonneg_of_neg_nonneg h₂ h₁,
  le_total := assume a b,
    have b - a ∈ nonneg ∪ (λr, -r) ⁻¹' nonneg,
      from calc b - a ∈ closure (of_rat '' univ) : dense_embedding_of_rat.dense _
        ... ⊆ closure (of_rat '' {q | 0 ≤ q} ∪ (λr, -r) '' (of_rat '' {q | 0 ≤ q})) :
          closure_mono $ assume r ⟨q, hq, hrq⟩, hrq ▸ match le_total 0 q with
          | or.inl h := or.inl (mem_image_of_mem of_rat h)
          | or.inr h := or.inr ⟨of_rat (-q),
            mem_image_of_mem _ $ show 0 ≤ - q, from le_of_neg_le_neg $ by simp [h],
            by simp⟩
          end
        ... ⊆ nonneg ∪ closure ((λr, -r) '' (of_rat '' {q | 0 ≤ q})) :
          by rw [closure_union]; exact subset.refl _
        ... ⊆ nonneg ∪ (λr, -r) ⁻¹' nonneg : by rw [←neg_preimage_closure]; exact subset.refl _,
    have b - a ∈ nonneg ∨ - (b - a) ∈ nonneg, from this,
    show b - a ∈ nonneg ∨ a - b ∈ nonneg, by simp [*] at * }

lemma of_rat_lt_of_rat {q₁ q₂ : ℚ} : of_rat q₁ < of_rat q₂ ↔ q₁ < q₂ :=
by simp [lt_iff_le_not_le, of_rat_le_of_rat]

private lemma add_le_add_left_iff {a b c : ℝ} : (c + a ≤ c + b) ↔ a ≤ b :=
have (c + b) - (c + a) = b - a,
  from calc (c + b) - (c + a) = c + - c + (b - a) : by simp [-add_right_neg]
    ... = b - a : by simp [-of_rat_zero],
show (c + b) - (c + a) ∈ nonneg ↔ b - a ∈ nonneg,
  from by rwa [this]

instance : decidable_linear_ordered_comm_group ℝ :=
{ real.add_comm_group with
  le := (≤),
  lt := (<),
  le_refl := le_refl,
  le_trans := assume a b c, le_trans,
  le_antisymm := assume a b, le_antisymm,
  le_total := le_total,
  lt_iff_le_not_le := assume a b, lt_iff_le_not_le,
  add_le_add_left := assume a b h c, by rwa [add_le_add_left_iff],
  add_lt_add_left :=
    assume a b, by simp [lt_iff_not_ge, ge, -add_comm, add_le_add_left_iff] {contextual := tt},
  decidable_eq    := by apply_instance,
  decidable_le    := by apply_instance,
  decidable_lt    := by apply_instance }

lemma preimage_neg_rat : preimage (has_neg.neg : ℚ → ℚ) = image (has_neg.neg : ℚ → ℚ) :=
(image_eq_preimage_of_inverse _ _ neg_neg neg_neg).symm

lemma map_neg_real : map (has_neg.neg : ℝ → ℝ) = vmap (has_neg.neg : ℝ → ℝ) :=
funext $ assume f, map_eq_vmap_of_inverse (funext neg_neg) (funext neg_neg)

lemma map_neg_rat : map (has_neg.neg : ℚ → ℚ) = vmap (has_neg.neg : ℚ → ℚ) :=
funext $ assume f, map_eq_vmap_of_inverse (funext neg_neg) (funext neg_neg)

private lemma is_closed_le_real [topological_space α] {f g : α → ℝ}
  (hf : continuous f) (hg : continuous g) : is_closed {a:α | f a ≤ g a} :=
have h : {a:α | f a ≤ g a} = (λa, g a - f a) ⁻¹' nonneg,
  from set.ext $ by simp [-of_rat_zero, zero_le_iff_nonneg.symm, -sub_eq_add_neg, le_sub_iff_add_le],
have is_closed ((λa, g a - f a) ⁻¹' nonneg),
  from continuous_iff_is_closed.mp (continuous_sub hg hf) _ is_closed_closure,
by rw [h]; exact this

private lemma is_open_lt_real [topological_space α] {f g : α → ℝ}
  (hf : continuous f) (hg : continuous g) : is_open {a | f a < g a} :=
have {a | f a < g a} = - {a | g a ≤ f a}, from set.ext $ assume y, by simp [not_le_iff],
by rw [this]; exact is_open_compl_iff.mpr (is_closed_le_real hg hf)

instance : linear_ordered_topology ℝ :=
{ is_open_lt := assume x, is_open_lt_real continuous_const continuous_id,
  is_open_gt := assume x, is_open_lt_real continuous_id continuous_const }

lemma closure_of_rat_image_le_eq {q : ℚ} : closure (of_rat '' {x | q ≤ x}) = {r | of_rat q ≤ r } :=
have {r : ℝ | of_rat q < r} ⊆ closure (of_rat '' {x : ℚ | q ≤ x}),
  from calc {r : ℝ | of_rat q < r} ⊆ {r : ℝ | of_rat q < r} ∩ closure (of_rat '' univ) :
      by simp [dense_embedding_of_rat.closure_image_univ, inter_univ]; exact subset.refl _
    ... ⊆ closure ({r : ℝ | of_rat q < r} ∩ of_rat '' univ) :
      closure_inter_open (is_open_lt continuous_const continuous_id)
    ... ⊆ closure (of_rat '' {x : ℚ | q ≤ x}) : closure_mono $ assume r ⟨h₁, p, _, h₂⟩,
      by simp [h₂.symm, of_rat_lt_of_rat] at *; apply mem_image_of_mem; simp; apply le_of_lt h₁,
subset.antisymm
  (closure_minimal
    (image_subset_iff_subset_preimage.mpr $ by simp [of_rat_le_of_rat] {contextual:=tt})
    (is_closed_le continuous_const continuous_id)) $
  calc {r:ℝ | of_rat q ≤ r} ⊆ {of_rat q} ∪ {r | of_rat q < r} :
      assume x, by simp [le_iff_lt_or_eq, and_imp_iff, or_imp_iff_and_imp] {contextual := tt}
    ... ⊆ closure (of_rat '' {x | q ≤ x}) :
      union_subset (subset.trans (by simp; exact mem_image_of_mem _ (le_refl q)) subset_closure) this

lemma closure_of_rat_image_le_le_eq {a b : ℚ} (hab : a ≤ b) :
  closure (of_rat '' {q:ℚ | a ≤ q ∧ q ≤ b}) = {r:ℝ | of_rat a ≤ r ∧ r ≤ of_rat b} :=
let ivl := closure (of_rat '' {q:ℚ | a ≤ q ∧ q ≤ b}),
  a_lt := {r | of_rat a < r}, lt_b := {r | r < of_rat b} in
have a_lt ∩ lt_b ⊆ ivl,
  from calc a_lt ∩ lt_b ⊆ (a_lt ∩ lt_b) ∩ closure (of_rat '' univ) :
      by simp [dense_embedding_of_rat.closure_image_univ, inter_univ]; exact subset.refl _
    ... ⊆ closure ((a_lt ∩ lt_b) ∩ of_rat '' univ) :
      closure_inter_open $ is_open_inter
        (is_open_lt continuous_const continuous_id) (is_open_lt continuous_id continuous_const)
    ... ⊆ ivl :
      closure_mono $ assume r ⟨⟨hra, hrb⟩, q, hq, hrq⟩,
        hrq ▸ mem_image_of_mem of_rat
        begin
          simp [hrq.symm, of_rat_lt_of_rat] at *,
          exact ⟨le_of_lt hra, le_of_lt hrb⟩
        end,
have hab : ({of_rat a, of_rat b}:set ℝ) ⊆ ivl,
  from subset.trans subset_closure $ closure_mono $
    by simp [subset_def, or_imp_iff_and_imp, hab, mem_image_of_mem] {contextual := tt},
subset.antisymm
  (closure_minimal (by simp [image_subset_iff_subset_preimage, of_rat_le_of_rat] {contextual := tt}) $
    is_closed_inter (is_closed_le continuous_const continuous_id) (is_closed_le continuous_id continuous_const))
  (calc {r:ℝ | of_rat a ≤ r ∧ r ≤ of_rat b} ⊆ {of_rat a, of_rat b} ∪ (a_lt ∩ lt_b) :
      assume x, by simp [le_iff_lt_or_eq, and_imp_iff, or_imp_iff_and_imp] {contextual := tt}
    ... ⊆ ivl : union_subset hab this)

lemma is_closed_imp [topological_space α] {p q : α → Prop}
  (hp : is_open {x | p x}) (hq : is_closed {x | q x}) : is_closed {x | p x → q x} :=
have {x | p x → q x} = (- {x | p x}) ∪ {x | q x}, from set.ext $ by finish,
by rw [this]; exact is_closed_union (is_closed_compl_iff.mpr hp) hq

lemma abs_real_eq_abs : abs_real = abs :=
funext $ assume r,
match le_total 0 r with
| or.inl h := by simp [abs_of_nonneg h, abs_real_of_nonneg h]
| or.inr h :=
  have 0 ≤ -r, from le_neg_of_le_neg $ by simp [-of_rat_zero, h],
  calc abs_real r = abs_real (- - r) : by simp
    ... = - r : by rw [abs_real_neg, abs_real_of_nonneg this]
    ... = _ : by simp [abs_of_nonpos h]
end

lemma uniform_continuous_abs_real : uniform_continuous (abs : ℝ → ℝ) :=
by rw [←abs_real_eq_abs]; exact uniform_continuous_abs_real'

lemma continuous_abs_real : continuous (abs : ℝ → ℝ) :=
continuous_of_uniform uniform_continuous_abs_real

lemma of_rat_abs {q : ℚ} : of_rat (abs q) = abs (of_rat q) :=
by rw [←abs_real_eq_abs]; exact of_rat_abs_real.symm

lemma mem_uniformity_real_iff {s : set (ℝ × ℝ)} :
  s ∈ (@uniformity ℝ _).sets ↔ (∃e>0, ∀r₁ r₂:ℝ, abs (r₁ - r₂) < of_rat e → (r₁, r₂) ∈ s) :=
⟨ assume : s ∈ uniformity.sets,
  let ⟨s', hs', hcs', hss'⟩ := mem_uniformity_is_closed this in
  have s'_eq : {x : ℝ × ℝ | (x.fst, x.snd) ∈ s'} = s', by simp,
  have (λp:ℚ×ℚ, (of_rat p.1, of_rat p.2)) ⁻¹' s' ∈ (zero_nhd.vmap (λp:ℚ×ℚ, p.1 - p.2)).sets,
    by rw [←uniformity_rat, ←uniform_embedding_of_rat.right]; exact preimage_mem_vmap hs',
  let ⟨t, ht, (hst : _ ⊆ _)⟩ := this, ⟨e, he, het⟩ := by rw [mem_zero_nhd_iff] at ht; exact ht in
  have ∀r:ℝ×ℝ, abs (r.1 - r.2) < of_rat e → (r.1, r.2) ∈ s',
    from is_closed_property dense_embedding_of_rat_of_rat.closure_image_univ
      (is_closed_imp (is_open_lt
        (continuous_compose (continuous_sub continuous_fst continuous_snd) continuous_abs_real)
          continuous_const) $ by simp [s'_eq]; exact hcs') $
      assume ⟨q₁, q₂⟩,
      begin
        simp [-sub_eq_add_neg, of_rat_abs.symm, of_rat_lt_of_rat],
        exact assume hq, @hst (q₁, q₂) (het (q₁ - q₂) hq)
      end,
  ⟨e, he, assume r₁ r₂ hr, hss' $ this (r₁, r₂) hr⟩,
  assume ⟨e, he, (hes : ∀ (r₁ r₂ : ℝ), abs (r₁ - r₂) < of_rat e → (r₁, r₂) ∈ s)⟩,
  have 0 < e/2, from div_pos_of_pos_of_pos he zero_lt_two,
  have {q:ℚ×ℚ | abs (q.1 - q.2) < e/2 } ∈ (uniformity.vmap (λp:ℚ×ℚ, (of_rat p.1, of_rat p.2))).sets,
    by rw [uniform_embedding_of_rat.right]; exact mem_uniformity_rat this,
  let ⟨t, ht, hte⟩ := this in
  have ∀p:ℝ×ℝ, p ∈ interior t → abs (p.1 - p.2) ≤ of_rat (e/2),
    from is_closed_property dense_embedding_of_rat_of_rat.closure_image_univ
      (is_closed_imp is_open_interior $ is_closed_le (continuous_compose
        (continuous_sub continuous_fst continuous_snd) continuous_abs_real)
        continuous_const) $
      assume ⟨q₁, q₂⟩ hq,
        have (of_rat q₁, of_rat q₂) ∈ t, from interior_subset hq,
        have abs (q₁ - q₂) ≤ e / 2, from le_of_lt $ @hte (q₁, q₂) this,
        by simp [-sub_eq_add_neg, of_rat_abs.symm, of_rat_le_of_rat]; assumption,
  uniformity.upwards_sets (interior_mem_uniformity ht) $
    assume p hp,
    have abs (p.1 - p.2) < of_rat e,
      from calc _ ≤ of_rat (e / 2) : this p hp
        ... < of_rat e : of_rat_lt_of_rat.mpr $ div_lt_of_mul_lt_of_pos zero_lt_two $
          lt_mul_of_gt_one_right he two_gt_one,
    have (p.1, p.2) ∈ s,
      from hes _ _ this,
    by simp * at *⟩

lemma exists_lt_of_rat (r : ℝ) : ∃q:ℚ, r < of_rat q :=
have {r':ℝ | r < r'} ∩ of_rat '' univ ∈ (nhds (r + 1) ⊓ principal (of_rat '' univ)).sets,
  from inter_mem_inf_sets (mem_nhds_sets (is_open_lt continuous_const continuous_id) $
    show r < r + 1, from lt_add_of_le_of_pos (le_refl _) (of_rat_lt_of_rat.mpr zero_lt_one))
    (mem_principal_sets.mpr $ subset.refl _),
let ⟨x, hx, ⟨q, hq, hxq⟩⟩ := inhabited_of_mem_sets dense_embedding_of_rat.nhds_inf_neq_bot this in
⟨q, hxq.symm ▸ hx⟩

lemma exists_pos_of_rat {r : ℝ} (hr : 0 < r) : ∃q:ℚ, 0 < q ∧ of_rat q < r :=
let ⟨u, v, hu, hv, hru, h0v, huv⟩ := t2_separation (ne_of_gt hr) in
have r ∈ nonneg, from zero_le_iff_nonneg.mp $ le_of_lt $ hr,
have r ∈ closure (u ∩ of_rat '' {q | 0 ≤ q}),
  from closure_inter_open hu ⟨hru, this⟩,
have ∃i:ℚ, i>0 ∧ ∀q, abs q < i → of_rat q ∈ v,
  from have {q:ℚ | of_rat q ∈ v} ∈ (nhds (0:ℚ)).sets,
    from dense_embedding_of_rat.tendsto (mem_nhds_sets hv h0v),
  by rw [nhds_0_eq_zero_nhd, mem_zero_nhd_iff] at this; simp * at *,
let ⟨i, hi, hiq⟩ := this in
have ∀a ∈ u ∩ of_rat '' {q : ℚ | 0 ≤ q}, a - of_rat i ∈ nonneg,
  from assume a ⟨hau, q, (hq : 0 ≤ q), heq⟩,
  have i ≤ q, from le_of_not_gt $ assume : q < i,
    have of_rat q ∈ v, from hiq q $ by simp [abs_of_nonneg hq, *],
    have of_rat q ∈ u ∩ v, from ⟨heq.symm ▸ hau, this⟩,
    by rwa [huv] at this,
  heq ▸ by simp [of_rat_mem_nonneg_iff, -sub_eq_add_neg, le_sub_iff_add_le, this],
have r - of_rat i ∈ nonneg,
  from @mem_closure_of_continuous _ _ _ _ (λr, r - of_rat i) _ (u ∩ of_rat '' {q | 0 ≤ q}) _
    (continuous_sub continuous_id continuous_const) ‹r ∈ closure (u ∩ of_rat '' {q | 0 ≤ q})› this,
⟨i / 2, div_pos_of_pos_of_pos hi zero_lt_two,
  lt_of_lt_of_le (of_rat_lt_of_rat.mpr $ div_two_lt_of_pos hi) this⟩

lemma continuous_mul_real : continuous (λp:ℝ×ℝ, p.1 * p.2) :=
have ∀r:ℝ, ∃(s:set ℚ) (q:ℚ),
    q > 0 ∧ closure (of_rat '' s) ∈ (nhds r).sets ∧ is_closed s ∧ (∀x∈s, abs x ≤ q),
  from assume r,
  let ⟨q, (hrq : abs r < of_rat q)⟩ := exists_lt_of_rat (abs r) in
  have hq : 0 < q, from of_rat_lt_of_rat.mp $ lt_of_le_of_lt (abs_nonneg _) hrq,
  have h_eq : {r : ℝ | of_rat (-q) ≤ r ∧ r ≤ of_rat q} = {r:ℝ | abs r ≤ of_rat q}, by simp [abs_le_iff],
  have {r:ℝ | abs r < of_rat q} ∈ (nhds r).sets,
    from mem_nhds_sets (is_open_lt continuous_abs_real continuous_const) hrq,
  ⟨{p:ℚ | - q ≤ p ∧ p ≤ q}, q, hq,
    begin
      rw [closure_of_rat_image_le_le_eq, h_eq],
      exact ((nhds r).upwards_sets this $ assume r hr, le_of_lt hr),
      exact (le_trans (neg_le_of_neg_le $ by simp [le_of_lt hq]) (le_of_lt hq))
    end,
    is_closed_inter
      (is_closed_le continuous_const continuous_id)
      (is_closed_le continuous_id continuous_const),
    assume x, abs_le_iff.mpr⟩,
begin
  rw [real.has_mul],
  simp [lift_rat_op],
  apply dense_embedding_of_rat_of_rat.continuous_ext,
  exact (assume ⟨r₁, r₂⟩,
    let ⟨s₁, q₁, hq₁p, hs₁, hs₁c, hsq₁⟩ := this r₁, ⟨s₂, q₂, hq₂p, hs₂, hs₂c, hsq₂⟩ := this r₂ in
    let hu := uniform_continuous_compose uniform_continuous_swap $
      uniform_continuous_compose (uniform_continuous_mul_rat hq₁p hq₂p) $
      uniform_continuous_of_embedding uniform_embedding_of_rat in
    have hs : closure ((λp:ℚ×ℚ, (of_rat p.1, of_rat p.2)) '' set.prod s₁ s₂) ∈ (nhds (r₁, r₂)).sets,
    begin
      rw [←prod_image_image_eq, closure_prod_eq, nhds_prod_eq],
      exact prod_mem_prod hs₁ hs₂
    end,
    have hsc : is_closed (set.prod s₁ s₂), from is_closed_prod hs₁c hs₂c,
    uniform_extend_subtype hu
      (uniform_embedding_prod uniform_embedding_of_rat uniform_embedding_of_rat)
      dense_embedding_of_rat_of_rat.dense
      hs hsc (assume ⟨p₁, p₂⟩ ⟨h₁, h₂⟩, ⟨hsq₁ p₁ h₁, hsq₂ p₂ h₂⟩))
end

lemma continuous_mul_real' [topological_space α] {f g : α → ℝ} (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x * g x) :=
continuous_compose (continuous_prod_mk hf hg) continuous_mul_real

lemma tendsto_inv_real {r : ℝ} (hr : r ≠ 0) : tendsto has_inv.inv (nhds r) (nhds r⁻¹) :=
let inv := dense_embedding.ext dense_embedding_of_rat (of_rat ∘ has_inv.inv) in
suffices tendsto inv (nhds r) (nhds (inv r)),
begin
  rw [real.has_inv],
  simp [lift_rat_fun, hr],
  apply tendsto_cong this,
  apply (nhds r).upwards_sets (compl_singleton_mem_nhds hr),
  intro x; simp {contextual := tt}
end,
have h_ex : ∀q, 0 < q → ∀r, of_rat q < r →
    ∃ (c : ℝ), tendsto (of_rat ∘ has_inv.inv) (vmap of_rat (nhds r)) (nhds c),
  from assume q hq a ha,
  have {r | of_rat q < r} ∈ (nhds a).sets,
    from mem_nhds_sets (is_open_lt continuous_const continuous_id) ha,
  have ha : closure (of_rat '' {x : ℚ | q ≤ x}) ∈ (nhds a).sets,
    from (nhds a).upwards_sets this $ by simp [closure_of_rat_image_le_eq, le_of_lt] {contextual:=tt},
  have uniform_continuous (of_rat ∘ has_inv.inv ∘ subtype.val),
    from uniform_continuous_compose
      (uniform_continuous_inv_pos_rat hq)
      (uniform_continuous_of_embedding uniform_embedding_of_rat),
  uniform_extend_subtype this uniform_embedding_of_rat dense_embedding_of_rat.dense
    ha (is_closed_le continuous_const continuous_id) (assume x, id),
match lt_or_gt_of_ne hr  with
| or.inr h :=
  let ⟨q, hq, hqr⟩ := exists_pos_of_rat h in
  have {r | of_rat q < r} ∈ (nhds r).sets,
    from mem_nhds_sets (is_open_lt continuous_const continuous_id) hqr,
  dense_embedding_of_rat.tendsto_ext $ (nhds r).upwards_sets this $ h_ex q hq
| or.inl h :=
  have 0 < -r, from lt_neg_of_lt_neg $ by simp; assumption,
  let ⟨q, hq, hqr⟩ := exists_pos_of_rat this in
  have {r | r < of_rat (-q)} ∈ (nhds r).sets,
    from mem_nhds_sets (is_open_lt continuous_id continuous_const)
      begin rw [←of_rat_neg]; exact lt_neg_of_lt_neg hqr end,
  dense_embedding_of_rat.tendsto_ext $ (nhds r).upwards_sets this $
    assume a (ha : a < of_rat (-q)),
    have of_rat q < -a, by rw [←of_rat_neg] at ha; exact lt_neg_of_lt_neg ha,
    let ⟨c, (hc : tendsto (of_rat ∘ has_inv.inv) (vmap of_rat (nhds (-a))) (nhds c))⟩ := h_ex q hq _ this in
    have tendsto (has_neg.neg ∘ of_rat ∘ has_inv.inv) (vmap of_rat (nhds (-a))) (nhds (- c)),
      from tendsto_compose hc $ continuous_iff_tendsto.mp continuous_neg' _,
    have h_eq : has_neg.neg ∘ (of_rat ∘ has_inv.inv) = (of_rat ∘ has_inv.inv) ∘ has_neg.neg,
      from funext $ assume r, by simp [(∘), -of_rat_inv, inv_neg],
    have tendsto (of_rat ∘ has_inv.inv) (map has_neg.neg $ vmap of_rat (nhds (-a))) (nhds (- c)),
      from tendsto_map' $ by rw [h_eq] at this; exact this,
    have h_le : vmap of_rat (nhds a) ≤ (map has_neg.neg $ vmap of_rat $ nhds (-a)),
      from have of_rat ∘ has_neg.neg = has_neg.neg ∘ of_rat,
        from funext $ assume x, of_rat_neg.symm,
      begin
        rw [map_neg_rat, vmap_vmap_comp, this],
        conv in (vmap (has_neg.neg ∘ _) (nhds _)) { rw [←vmap_vmap_comp] },
        exact (vmap_mono $ le_vmap_iff_map_le.mpr $ continuous_iff_tendsto.mp continuous_neg' _)
      end,
    ⟨- c, le_trans (map_mono h_le) this⟩
end

lemma continuous_inv_real' : continuous (λa:{r:ℝ // r ≠ 0}, a.val⁻¹) :=
continuous_iff_tendsto.mpr $ assume ⟨r, hr⟩,
  tendsto_compose (continuous_iff_tendsto.mp continuous_subtype_val _) (tendsto_inv_real hr)

lemma continuous_inv_real [topological_space α] {f : α → ℝ} (h : ∀a, f a ≠ 0) (hf : continuous f) :
  continuous (λa, (f a)⁻¹) :=
show continuous ((has_inv.inv ∘ @subtype.val ℝ (λr, r ≠ 0)) ∘ λa, ⟨f a, h a⟩),
  from continuous_compose (continuous_subtype_mk _ hf) continuous_inv_real'

private lemma closure_compl_zero_image_univ :
  closure ((λp:{q:ℚ // q ≠ 0},
    (⟨of_rat p.val, assume h, p.2 $ dense_embedding_of_rat.inj _ _ h⟩ : {r:ℝ // r ≠ 0})) '' univ) = univ :=
top_unique $ assume x _,
have of_rat '' univ - {0} ⊆ of_rat ∘ (@subtype.val ℚ (λq, q ≠ 0)) '' univ,
  from assume r ⟨⟨q, _, hq⟩, hr⟩,
    have hr : of_rat q ≠ of_rat 0, by simp [*] at *,
    ⟨⟨q, assume hq, hr $ by simp [hq]⟩, trivial, by simp [hq, (∘)]⟩,
begin
  rw [closure_subtype, ←image_comp],
  change x.val ∈ closure ((of_rat ∘ subtype.val) '' univ),
  exact calc x.val ∈ closure (of_rat '' univ) - closure {0} :
      ⟨dense_embedding_of_rat.dense _, by simp; exact x.property⟩
    ... ⊆ closure (of_rat '' univ - {0}) : closure_diff
    ... ⊆ _ : closure_mono this
end

private lemma mul_nonneg {a b : ℝ} : 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
begin
  simp [zero_le_iff_nonneg, -of_rat_zero],
  exact assume ha hb, mem_nonneg_of_continuous2 continuous_mul_real ha hb $
    by simp [of_rat_mem_nonneg_iff]; exact (assume a b, mul_nonneg)
end

instance : discrete_field ℝ :=
{ real.add_comm_group with
  one              := 1,
  mul              := (*),
  inv              := has_inv.inv,
  mul_one          := is_closed_property dense_embedding_of_rat.closure_image_univ
    (is_closed_eq (continuous_mul_real' continuous_id continuous_const) continuous_id)
    (by simp),
  one_mul          := is_closed_property dense_embedding_of_rat.closure_image_univ
    (is_closed_eq (continuous_mul_real' continuous_const continuous_id) continuous_id)
    (by simp),
  mul_comm         := is_closed_property2 dense_embedding_of_rat
    (is_closed_eq (continuous_mul_real' continuous_fst continuous_snd) (continuous_mul_real' continuous_snd continuous_fst))
    (by simp),
  mul_assoc        := is_closed_property3 dense_embedding_of_rat
    (is_closed_eq (continuous_mul_real'
        (continuous_mul_real' continuous_fst $ continuous_compose continuous_snd continuous_fst) $
        continuous_compose continuous_snd continuous_snd)
      (continuous_mul_real' continuous_fst $
        continuous_mul_real' (continuous_compose continuous_snd continuous_fst) $
        continuous_compose continuous_snd continuous_snd))
    (by intros; simp),
  left_distrib     :=
    is_closed_property3 dense_embedding_of_rat
    (is_closed_eq (continuous_mul_real' continuous_fst
      (continuous_add (continuous_compose continuous_snd continuous_fst) (continuous_compose continuous_snd continuous_snd)))
      (continuous_add (continuous_mul_real' continuous_fst (continuous_compose continuous_snd continuous_fst))
         (continuous_mul_real' continuous_fst (continuous_compose continuous_snd continuous_snd))))
    begin intros, rw [of_rat_add, of_rat_mul, of_rat_mul, of_rat_mul, of_rat_add], simp [left_distrib] end,
  right_distrib    := is_closed_property3 dense_embedding_of_rat
    (is_closed_eq (continuous_mul_real'
      (continuous_add continuous_fst (continuous_compose continuous_snd continuous_fst))
      (continuous_compose continuous_snd continuous_snd))
      (continuous_add
        (continuous_mul_real' continuous_fst (continuous_compose continuous_snd continuous_snd))
        (continuous_mul_real' (continuous_compose continuous_snd continuous_fst)
          (continuous_compose continuous_snd continuous_snd))))
    begin intros, rw [of_rat_add, of_rat_mul, of_rat_mul, of_rat_mul, of_rat_add], simp [right_distrib] end,
  zero_ne_one      := assume h, zero_ne_one $ dense_embedding_of_rat.inj 0 1 h,
  mul_inv_cancel   :=
    suffices ∀a:{a:ℝ // a ≠ 0}, a.val * a.val⁻¹ = 1,
      from assume a ha, this ⟨a, ha⟩,
    is_closed_property closure_compl_zero_image_univ
      (is_closed_eq (continuous_mul_real' continuous_subtype_val continuous_inv_real') continuous_const)
      (assume ⟨a, (ha : a ≠ 0)⟩,
        by simp [*, mul_inv_cancel ha] at *),
  inv_mul_cancel   :=
      suffices ∀a:{a:ℝ // a ≠ 0}, a.val⁻¹ * a.val = 1,
      from assume a ha, this ⟨a, ha⟩,
    is_closed_property closure_compl_zero_image_univ
      (is_closed_eq (continuous_mul_real' continuous_inv_real' continuous_subtype_val) continuous_const)
      (assume ⟨a, (ha : a ≠ 0)⟩,
        by simp [*, mul_inv_cancel ha] at *),
  inv_zero := show (0:ℝ)⁻¹ = 0, from by simp [has_inv.inv],
  has_decidable_eq := by apply_instance }

instance : discrete_linear_ordered_field ℝ :=
{ real.discrete_field with
  le              := (≤),
  lt              := (<),
  le_refl         := le_refl,
  le_trans        := assume a b c, le_trans,
  le_antisymm     := assume a b, le_antisymm,
  le_total        := le_total,
  lt_iff_le_not_le := assume a b, lt_iff_le_not_le,
  zero_lt_one     := of_rat_lt_of_rat.mpr zero_lt_one,
  add_le_add_left := assume a b h c, by rwa [add_le_add_left_iff],
  add_lt_add_left :=
    assume a b, by simp [lt_iff_not_ge, ge, -add_comm, add_le_add_left_iff] {contextual := tt},
  mul_nonneg      := assume a b, mul_nonneg,
  mul_pos         := assume a b ha hb,
    lt_of_le_of_ne (mul_nonneg (le_of_lt ha) (le_of_lt hb)) $
      ne.symm $ mul_ne_zero (ne_of_gt ha) (ne_of_gt hb),
  decidable_eq    := by apply_instance,
  decidable_le    := by apply_instance,
  decidable_lt    := by apply_instance }

instance : topological_ring ℝ := 
{ real.topological_add_group with continuous_mul := continuous_mul_real }

lemma compact_ivl {a b : ℝ} : compact {r:ℝ | a ≤ r ∧ r ≤ b } :=
have is_closed_ivl : ∀{a b : ℝ}, is_closed {r:ℝ | a ≤ r ∧ r ≤ b },
  from assume a b, is_closed_inter
    (is_closed_le continuous_const continuous_id)
    (is_closed_le continuous_id continuous_const),
have compact_01 : compact {r:ℝ | of_rat 0 ≤ r ∧ r ≤ of_rat 1 },
  by rw [←closure_of_rat_image_le_le_eq zero_le_one];
     exact (compact_of_totally_bounded_is_closed (totally_bounded_closure $ totally_bounded_image
      (uniform_continuous_of_embedding uniform_embedding_of_rat) totally_bounded_01_rat)
      is_closed_closure),
if h : a < b then
  have 0 < b - a, from lt_sub_left_of_add_lt $ by simp [-of_rat_zero, h],
  have {r:ℝ | a ≤ r ∧ r ≤ b } = ((λx, x + a) ∘ (λx, x * (b - a))) '' {r:ℝ | 0 ≤ r ∧ r ≤ 1 },
    by rw [image_comp, ivl_stretch this, ivl_translate]; simp [-of_rat_one, -of_rat_zero],
  by rw [this]; exact compact_image compact_01
    (continuous_compose
      (continuous_mul continuous_id continuous_const)
      (continuous_add continuous_id continuous_const))
else
  have {r:ℝ | a ≤ r ∧ r ≤ b } ⊆ {a},
    from assume r ⟨har, hbr⟩,
    have r = a, from le_antisymm (le_trans hbr $ le_of_not_gt h) har,
    by simp [this],
  compact_of_is_closed_subset compact_singleton is_closed_ivl this

lemma exists_supremum_real {s : set ℝ} {a b : ℝ} (ha : a ∈ s) (hb : ∀a∈s, a ≤ b) :
  ∃x, (∀y∈s, y ≤ x) ∧ (∀y, (∀a∈s, a ≤ y) → x ≤ y) :=
let f := (⨅r:{r : ℝ // r ∈ s}, principal {r' | r' ∈ s ∧ r.val ≤ r'}) in
have hf : f ≠ ⊥,
  from infi_neq_bot_of_directed (by apply_instance)
    (assume ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩, ⟨
      ⟨max r₁ r₂, if h: r₁ ≤ r₂ then by rwa [max_eq_right h] else by rwa [max_eq_left (le_of_not_ge h)]⟩,
      by simp; exact assume a ⟨ha, h⟩, ⟨le_trans (le_max_left _ _) h, ha⟩,
      by simp; exact assume a ⟨ha, h⟩, ⟨le_trans (le_max_right _ _) h, ha⟩⟩)
    (by simp [forall_subtype_iff]; exact assume a ha, ne_empty_of_mem ⟨ha, le_refl a⟩),
have principal {r' : ℝ | r' ∈ s ∧ a ≤ r'} ≤ principal {r : ℝ | a ≤ r ∧ r ≤ b},
  by simp [hb] {contextual := tt},
let ⟨x, ⟨hx₁, hx₂⟩, h⟩ := @compact_ivl a b f hf (infi_le_of_le ⟨a, ha⟩ this) in
⟨x, assume y hy, le_of_not_gt $ assume hxy,
    have {r' | r' ∈ s ∧ y ≤ r'} ∩ {z | z < y} ∈ (f ⊓ nhds x).sets,
      from inter_mem_inf_sets
        (le_principal_iff.mp $ infi_le_of_le ⟨y, hy⟩ $ subset.refl _)
        (mem_nhds_sets (is_open_lt continuous_id continuous_const) hxy),
    let ⟨z, ⟨_, hz₁⟩, hz₂⟩ := inhabited_of_mem_sets h this in
    lt_irrefl y $ lt_of_le_of_lt hz₁ hz₂,
 assume y hy, le_of_not_gt $ assume hxy,
    have {r' | r' ≤ y} ∩ {z | y < z} ∈ (f ⊓ nhds x).sets,
      from inter_mem_inf_sets
        (le_principal_iff.mp $ infi_le_of_le ⟨a, ha⟩ $ by simp [hy] {contextual := tt})
        (mem_nhds_sets (is_open_lt continuous_const continuous_id) hxy),
    let ⟨z, hzy, hyz⟩ := inhabited_of_mem_sets h this in
    lt_irrefl z $ lt_of_le_of_lt hzy hyz⟩

end
