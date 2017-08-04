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

reorder:
* topological group properties
* order properties
* ring & field
* order completeness (maybe before field)?

-/

import topology.uniform_space data.rat
noncomputable theory
open classical set
local attribute [instance] decidable_inhabited prop_decidable

/- rational numbers form a topological group and hence a uniform space -/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

lemma not_le_iff [linear_order  α] {a b : α } : ¬ (a ≤ b) ↔ b < a := (lt_iff_not_ge b a).symm
lemma not_lt_iff [linear_order  α] {a b : α } : ¬ (a < b) ↔ b ≤ a := ⟨le_of_not_gt, not_lt_of_ge⟩

lemma lt_div_iff {α : Type u} [linear_ordered_field α] {a b c : α} (h : 0 < c) :
  a < b / c ↔ a * c < b :=
⟨mul_lt_of_lt_div h, lt_div_of_mul_lt h⟩

lemma forall_subtype_iff {α : Type u} {p : α → Prop} {q : {a // p a} → Prop} :
  (∀x:{a // p a}, q x) ↔ (∀a (h : p a), q ⟨a, h⟩) :=
⟨assume h a ha, h ⟨_, _⟩, assume h ⟨a, ha⟩, h _ _⟩

lemma inv_sub_inv_eq {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
  a⁻¹ - b⁻¹ = (b - a) / (a * b) :=
have a * b ≠ 0, by simp [mul_eq_zero_iff_eq_zero_or_eq_zero, ha, hb],
calc (a⁻¹ - b⁻¹) = ((a⁻¹ - b⁻¹) * (a * b)) / (a * b) : by rwa [mul_div_cancel]
  ... = _ :
  begin
    simp [mul_add, add_mul, hb],
    rw [mul_comm a, mul_assoc, mul_comm a⁻¹, mul_inv_cancel ha],
    simp
  end

lemma abs_inv [discrete_linear_ordered_field α] (a : α) : abs a⁻¹ = (abs a)⁻¹ :=
have h : abs (1 / a) = 1 / abs a,
  begin rw [abs_div, abs_of_nonneg], exact zero_le_one end,
by simp [*] at *

lemma inv_neg [discrete_linear_ordered_field α] (a : α) : (-a)⁻¹ = -(a⁻¹) :=
if h : a = 0
then by simp [h, inv_zero]
else by rwa [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

lemma continuous_const [topological_space α] [topological_space β] {b : β} : continuous (λa:α, b) :=
continuous_iff_towards.mpr $ assume a, towards_const_nhds

open lattice set filter

lemma le_map_vmap' {f : filter β} {m : α → β} {s : set β}
  (hs : s ∈ f.sets) (hm : ∀b∈s, ∃a, m a = b) : f ≤ map m (vmap m f) :=
assume t' ⟨t, ht, (sub : ∀x, m x ∈ t → m x ∈ t')⟩,
f.upwards_sets (inter_mem_sets ht hs) $
  assume x ⟨hxt, hxs⟩,
  let ⟨y, (hy : m y = x)⟩ := hm x hxs in
  hy ▸ sub _ (show m y ∈ t, from hy.symm ▸ hxt)

lemma towards_vmap'' {m : α → β} {f : filter α} {g : filter β} (s : set α)
  {i : γ → α} (hs : s ∈ f.sets) (hi : ∀a∈s, ∃c, i c = a)
  (h : towards (m ∘ i) (vmap i f) g) : towards m f g :=
have towards m (map i $ vmap i $ f) g,
  by rwa [towards, ←map_compose] at h,
le_trans (map_mono $ le_map_vmap' hs hi) this

lemma uniform_embedding_subtype_emb {α : Type u} {β : Type v} [uniform_space α] [uniform_space β]
  (p : α → Prop) {e : α → β} (ue : uniform_embedding e) (de : dense_embedding e) :
  uniform_embedding (de.subtype_emb p) :=
⟨(de.subtype p).inj,
  by simp [vmap_vmap_comp, (∘), dense_embedding.subtype_emb, uniformity_subtype, ue.right.symm]⟩

lemma uniform_extend_subtype {α : Type u} {β : Type v} {γ : Type w}
  [uniform_space α] [uniform_space β] [uniform_space γ] [complete_space γ]
  [inhabited γ] [separated γ]
  {p : α → Prop} {e : α → β} {f : α → γ} {b : β} {s : set α}
  (hf : uniform_continuous (λx:subtype p, f x.val))
  (he : uniform_embedding e) (hd : ∀x, x ∈ closure (e '' univ))
  (hb : closure (e '' s) ∈ (nhds b).sets) (hs : closed s) (hp : ∀x∈s, p x) :
  ∃c, towards f (vmap e (nhds b)) (nhds c) :=
have de : dense_embedding e,
  from dense_embedding_of_uniform_embedding he hd,
have de' : dense_embedding (de.subtype_emb p),
  by exact de.subtype p,
have ue' : uniform_embedding (de.subtype_emb p),
  from uniform_embedding_subtype_emb _ he de,
have b ∈ closure (e '' {x | p x}),
  from (closure_mono $ mono_image $ hp) (mem_of_nhds hb),
let ⟨c, (hc : towards (f ∘ subtype.val) (vmap (de.subtype_emb p) (nhds ⟨b, this⟩)) (nhds c))⟩ :=
  uniformly_extend_exists ue' de'.dense hf in
begin
  rw [nhds_subtype_eq_vmap] at hc,
  simp [vmap_vmap_comp] at hc,
  change (towards (f ∘ @subtype.val α p) (vmap (e ∘ @subtype.val α p) (nhds b)) (nhds c)) at hc,
  rw [←vmap_vmap_comp] at hc,
  existsi c,
  apply towards_vmap'' s _ _ hc,
  exact ⟨_, hb, assume x,
    begin
      change e x ∈ (closure (e '' s)) → x ∈ s,
      rw [←closure_induced, closure_eq_nhds],
      dsimp,
      rw [nhds_induced_eq_vmap, de.induced],
      change x ∈ {x | nhds x ⊓ principal s ≠ ⊥} → x ∈ s,
      rw [←closure_eq_nhds, closure_eq_of_closed hs],
      exact id,
      exact de.inj
    end⟩,
  exact (assume x hx, ⟨⟨x, hp x hx⟩, rfl⟩)
end

/- remove when we hava linear arithmetic tactic -/
lemma one_lt_two : 1 < (2 : ℚ) :=
calc (1:ℚ) < 1 + 1 : lt_add_of_le_of_pos (le_refl 1) zero_lt_one
  ... = _ : by simp [bit0]

lemma zero_lt_two : 0 < (2 : ℚ) :=
calc (0:ℚ) < 1 + 1 : lt_add_of_le_of_pos zero_le_one zero_lt_one
  ... = _ : by simp [bit0]

def zero_nhd : filter ℚ := (⨅r > 0, principal {q | abs q < r})

lemma mem_zero_nhd {r : ℚ} (h : 0 < r) : {q | abs q < r} ∈ zero_nhd.sets :=
mem_infi_sets r $ mem_infi_sets h $ subset.refl _

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

lemma towards_zero_nhds {m : α → ℚ} {f : filter α} (hm : ∀r>0, {a | abs (m a) < r} ∈ f.sets) :
  towards m f zero_nhd :=
le_infi $ assume i, le_infi $ assume hi : 0 < i, by simp; exact hm i hi

lemma pure_zero_le_zero_nhd : pure 0 ≤ zero_nhd :=
by simp [zero_nhd, le_infi_iff, abs_zero, (>)] {contextual := tt}

lemma towards_neg_rat_zero : towards has_neg.neg zero_nhd zero_nhd :=
towards_zero_nhds $ assume i hi, by simp [abs_neg, mem_zero_nhd hi]

lemma towards_add_rat_zero : towards (λp:ℚ×ℚ, p.1 + p.2) (filter.prod zero_nhd zero_nhd) zero_nhd :=
towards_zero_nhds $ assume i hi,
have 0 < i / 2, from div_pos_of_pos_of_pos hi zero_lt_two,
show {x : ℚ × ℚ | abs (x.1 + x.2) < i} ∈ (filter.prod zero_nhd zero_nhd).sets,
  from filter.upwards_sets _ (prod_mem_prod (mem_zero_nhd this) (mem_zero_nhd this)) $
    assume ⟨a, b⟩ ⟨ha, hb⟩,
    calc abs (a + b) ≤ abs a + abs b : abs_add_le_abs_add_abs _ _
      ... < i/2 + i/2 : add_lt_add ha hb
      ... = (i + i) / 2 : div_add_div_same _ _ _
      ... = i : add_self_div_two _

lemma towards_add_rat_zero' {f g : α → ℚ} {x : filter α}
  (hf : towards f x zero_nhd) (hg : towards g x zero_nhd) : towards (λa, f a + g a) x zero_nhd :=
towards_compose (towards_prod_mk hf hg) towards_add_rat_zero

lemma towards_sub_rat' {f g : α → ℚ} {x : filter α}
  (hf : towards f x zero_nhd) (hg : towards g x zero_nhd) : towards (λa, f a - g a) x zero_nhd :=
by simp; exact towards_add_rat_zero' hf (towards_compose hg towards_neg_rat_zero)

lemma towards_mul_bnd_rat {f : filter ℚ} {r : ℚ} (hr : 0 < r) (hf : {x : ℚ | abs x < r} ∈ f.sets) :
  towards (λp:ℚ×ℚ, p.1 * p.2) (filter.prod zero_nhd f) zero_nhd :=
towards_zero_nhds $ assume i hi,
have 0 < i / r, from div_pos_of_pos_of_pos hi hr,
show {x : ℚ × ℚ | abs (x.1 * x.2) < i} ∈ (filter.prod zero_nhd f).sets,
  from filter.upwards_sets _ (prod_mem_prod (mem_zero_nhd this) hf) $
    assume ⟨a, b⟩ ⟨ha, hb⟩,
    calc abs (a * b) = abs a * abs b : by simp [abs_mul]
      ... < (i / r) * r : mul_lt_mul' (le_of_lt ha) hb (abs_nonneg b) this
      ... = i : div_mul_cancel _ (ne_of_gt hr)

lemma towards_mul_bnd_rat' {r : ℚ} {f g : α → ℚ} {x : filter α}
  (hr : 0 < r) (hy : {x : α | abs (g x) < r} ∈ x.sets) (hf : towards f x zero_nhd) :
  towards (λa, f a * g a) x zero_nhd :=
towards_compose (towards_prod_mk hf towards_map) (towards_mul_bnd_rat hr hy)

lemma towards_mul_rat' {f g : α → ℚ} {x : filter α}
  (hf : towards f x zero_nhd) (hg : towards g x zero_nhd) : towards (λa, f a * g a) x zero_nhd :=
towards_mul_bnd_rat' zero_lt_one (hg $ mem_zero_nhd zero_lt_one) hf

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
    towards_vmap' $ by rw [this]; exact towards_compose towards_vmap towards_neg_rat_zero,
  comp :=
    let f := (image (λp:ℚ×ℚ, p.1 - p.2) ∘ (λs, comp_rel s s) ∘ preimage (λp:ℚ×ℚ, p.1 - p.2)) in
    begin
      rw [le_vmap_iff_map_le, map_lift'_eq, vmap_lift'_eq2],
      exact calc zero_nhd.lift' f ≤
          zero_nhd.lift' (image (λp:ℚ×ℚ, p.1 + p.2) ∘ (λs, set.prod s s)) :
            lift'_mono' $
            assume s hs r ⟨⟨p₁, p₂⟩, ⟨q, (h₁ : p₁ - q ∈ s), (h₂ : q - p₂ ∈ s)⟩, (h : p₁ - p₂ = r)⟩,
            ⟨⟨p₁ - q, q - p₂⟩, ⟨h₁, h₂⟩,
              calc (p₁ - q) + (q - p₂) = p₁ - p₂ + (q - q) : by simp [-add_right_neg]
                ... = r : by simp [h]⟩
        ... = map (λp:ℚ×ℚ, p.1 + p.2) (filter.prod zero_nhd zero_nhd) :
          by rw [←map_lift'_eq, prod_same_eq]; exact monotone_prod monotone_id monotone_id
        ... ≤ zero_nhd : towards_add_rat_zero,
      exact monotone_comp (monotone_comp_rel monotone_id monotone_id) monotone_image,
      exact monotone_comp_rel monotone_id monotone_id
    end }

lemma uniformity_rat : uniformity = zero_nhd.vmap (λp:ℚ×ℚ, p.1 - p.2) := rfl

lemma mem_uniformity_rat {r : ℚ} (h : 0 < r) :
  {x:(ℚ × ℚ) | abs (x.1 - x.2) < r} ∈ (@uniformity ℚ _).sets :=
mem_vmap_of_mem $ mem_zero_nhd $ h

lemma uniform_continuous_rat [uniform_space α] {f : α → ℚ}
  (hf : towards (λp:α×α, f p.1 - f p.2) uniformity zero_nhd ) : uniform_continuous f :=
le_vmap_iff_map_le.mpr $ by rw [map_map]; exact hf

lemma towards_sub_uniformity_zero_nhd : towards (λp:(ℚ×ℚ), p.1 - p.2) uniformity zero_nhd :=
le_vmap_iff_map_le.mp $ le_refl uniformity

lemma towards_sub_uniformity_zero_nhd' {p : α → ℚ} {q : α → ℚ} {f : filter α}
  (h : towards (λx, (p x, q x)) f uniformity) : towards (λa, p a - q a) f zero_nhd :=
towards_compose h towards_sub_uniformity_zero_nhd

lemma uniform_continuous_add_rat : uniform_continuous (λp : ℚ × ℚ, p.1 + p.2) :=
uniform_continuous_rat $
have towards (λp:(ℚ×ℚ)×(ℚ×ℚ), (p.1.1 - p.2.1) + (p.1.2 - p.2.2)) uniformity zero_nhd,
  from towards_add_rat_zero'
    (towards_sub_uniformity_zero_nhd' towards_prod_uniformity_fst)
    (towards_sub_uniformity_zero_nhd' towards_prod_uniformity_snd),
have (λp:(ℚ×ℚ)×(ℚ×ℚ), (p.1.1 + p.1.2) - (p.2.1 + p.2.2)) = (λp, (p.1.1 - p.2.1) + (p.1.2 - p.2.2)),
  from funext $ by simp,
by rwa [this]

lemma uniform_continuous_neg_rat : uniform_continuous (λr:ℚ, -r) :=
have (λ (p : ℚ × ℚ), -p.fst - -p.snd) = (λ (p : ℚ × ℚ), p.fst - p.snd) ∘ prod.swap,
  from funext $ by simp [(∘)],
uniform_continuous_rat $
  by rw [this]; exact towards_compose towards_swap_uniformity towards_sub_uniformity_zero_nhd

lemma continuous_add_rat : continuous (λp : ℚ × ℚ, p.1 + p.2) :=
continuous_of_uniform uniform_continuous_add_rat

lemma towards_add_rat {r₁ r₂ : ℚ} {f₁ f₂ : α → ℚ} {x : filter α}
  (h₁ : towards f₁ x (nhds r₁)) (h₂ : towards f₂ x (nhds r₂)) :
  towards (λa, f₁ a + f₂ a) x (nhds (r₁ + r₂)) :=
have towards (λp:ℚ×ℚ, p.1 + p.2) (filter.prod (nhds r₁) (nhds r₂)) (nhds (r₁ + r₂)),
begin
  rw [←nhds_prod_eq],
  exact continuous_iff_towards.mp continuous_add_rat ⟨r₁, r₂⟩
end,
towards_compose (towards_prod_mk h₁ h₂) this

lemma continuous_neg_rat : continuous (λp:ℚ, - p) :=
continuous_of_uniform uniform_continuous_neg_rat

lemma towards_neg_rat {r : ℚ} {f : α → ℚ} {x : filter α}
  (h : towards f x (nhds r)) : towards (λa, - f a) x (nhds (-r)) :=
towards_compose h (continuous_iff_towards.mp continuous_neg_rat r)

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

lemma nhds_0_eq_zero_nhd : nhds 0 = zero_nhd :=
have (λ (x : ℚ), x + 0) = id, from funext $ by simp,
by rw [nhds_eq_map_zero_nhd, this]; simp

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

lemma gt_mem_nhds {r q : ℚ} (h : q < r) : {x | x < r} ∈ (nhds q).sets :=
have towards (λx:ℚ, -x) (nhds q) (nhds (-q)),
  from towards_neg_rat towards_id,
have {x | -r < -x} ∈ (nhds q).sets,
  from this $ lt_mem_nhds $ neg_lt_neg $ h,
(nhds q).upwards_sets this $ assume x (h : -r < -x), lt_of_neg_lt_neg h

lemma open_lt {r : ℚ} : open' {x | r < x} :=
by simp [open_iff_nhds]; exact assume a, lt_mem_nhds

lemma open_gt {r : ℚ} : open' {x | x < r} :=
by simp [open_iff_nhds]; exact assume a, gt_mem_nhds

lemma closed_le {r : ℚ} : closed {x | r ≤ x} :=
show open' {x | ¬ r ≤ x}, by simp [not_le_iff]; exact open_gt

lemma closed_ge {r : ℚ} : closed {x | x ≤ r} :=
show open' {x | ¬ x ≤ r}, by simp [not_le_iff]; exact open_lt

lemma uniform_continuous_inv_pos_rat {r : ℚ} (hr : 0 < r) :
  uniform_continuous (λp:{q:ℚ // r < q}, p.1⁻¹) :=
have h : ∀{v:{q:ℚ // r < q}}, v.val ≠ 0,
  from assume ⟨v, hv⟩, ne_of_gt $ lt_trans hr hv,
have hrr : 0 < 1 / (r * r),
  from div_pos_of_pos_of_pos zero_lt_one $ mul_pos hr hr,
uniform_continuous_rat
  begin
    conv { congr, funext, rw [inv_sub_inv_eq h h, div_eq_mul_one_div] },
    apply towards_mul_bnd_rat' hrr _ _,
    exact (univ_mem_sets' $ assume ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩,
      have 0 < a₁, from lt_trans hr ha₁,
      have 0 < a₂, from lt_trans hr ha₂,
      show abs (1 / (a₁ * a₂)) < 1 / (r * r),
      begin
        simp [abs_mul, abs_inv, abs_of_pos ‹0<a₁›, abs_of_pos ‹0<a₂›],
        rw [inv_eq_one_div, inv_eq_one_div],
        exact one_div_lt_one_div_of_lt (mul_pos hr hr) (mul_lt_mul ha₁ (le_of_lt ha₂) hr (le_of_lt ‹0 < a₁›))
      end),
    apply towards_sub_uniformity_zero_nhd'
      (towards_compose towards_swap_uniformity uniform_continuous_subtype_val)
  end

lemma towards_of_uniform_continuous_subtype
  [uniform_space α] [uniform_space β] {f: α → β} {p : α → Prop} {a : α}
  (hf : uniform_continuous (λx:{a // p a}, f x.val)) (ha : {a | p a} ∈ (nhds a).sets) :
  towards f (nhds a) (nhds (f a)) :=
by
  rw [(@map_nhds_subtype_val_eq α _ p a (mem_of_nhds ha) ha).symm];
  exact (towards_map' $ (continuous_iff_towards.mp $ continuous_of_uniform $ hf) _)

lemma towards_inv_pos_rat {r : ℚ} (hr : 0 < r) : towards (λq, q⁻¹) (nhds r) (nhds r⁻¹) :=
have r / 2 < r / 1, from div_lt_div_of_pos_of_lt_of_pos zero_lt_one one_lt_two hr,
have r / 2 < r, by simp [div_one] at this; assumption,
have 0 < r / 2,
  from div_pos_of_pos_of_pos hr two_pos,
towards_of_uniform_continuous_subtype (uniform_continuous_inv_pos_rat this) (lt_mem_nhds ‹r/2<r›)

lemma towards_inv_rat {r : ℚ} (hr : r ≠ 0) : towards (λq, q⁻¹) (nhds r) (nhds r⁻¹) :=
if h : 0 < r then towards_inv_pos_rat h else
have r < 0, from lt_of_le_of_ne (le_of_not_gt h) hr,
have 0 < -r, from lt_neg_of_lt_neg $ by simp * at *,
have towards (λq, - (-q)⁻¹) (nhds r) (nhds (- (-r)⁻¹)),
  from towards_neg_rat $ towards_compose (towards_neg_rat towards_id) (towards_inv_pos_rat this),
by simp [inv_neg] at this; assumption

lemma uniform_continuous_mul_rat {r₁ r₂ : ℚ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
  uniform_continuous (λp:{q:ℚ // abs q < r₁}×{q:ℚ // abs q < r₂}, p.1.1 * p.2.1) :=
have h : ∀a₁ a₂ b₁ b₂ : ℚ, a₁ * a₂ - b₁ * b₂ = (a₁ - b₁) * a₂ + (a₂ - b₂) * a₁ - (a₁ - b₁) * (a₂ - b₂),
  from assume a₁ a₂ b₁ b₂, calc
    a₁ * a₂ - b₁ * b₂ =
          a₁ * a₂ + a₁ * b₂ + a₂ * b₁ + -(a₁ * b₂) + -(a₂ * b₁) + -(b₁ * b₂) : by simp
    ... = a₁ * a₂ + (a₁ * b₂ + (a₂ * b₁ + (-(a₁ * b₂) + (-(a₂ * b₁) + -(b₁ * b₂))))) : by cc
    ... = (a₁ - b₁) * a₂ + (a₂ - b₂) * a₁ - (a₁ - b₁) * (a₂ - b₂) : by simp [mul_add, add_mul],
uniform_continuous_rat
  begin
    conv in (_ *_ - _* _) { rw h },
    apply towards_sub_rat' _ _,
    apply towards_add_rat_zero' _ _,
    exact towards_mul_bnd_rat' hr₂
      (univ_mem_sets' $ assume ⟨⟨_, ⟨a, ha⟩⟩, _⟩, ha)
      (towards_sub_uniformity_zero_nhd'
        (towards_compose towards_prod_uniformity_fst uniform_continuous_subtype_val)),
    exact towards_mul_bnd_rat' hr₁
      (univ_mem_sets' $ assume ⟨⟨⟨a, ha⟩, _⟩, _⟩, ha)
      (towards_sub_uniformity_zero_nhd'
        (towards_compose towards_prod_uniformity_snd uniform_continuous_subtype_val)),
    exact towards_mul_rat'
      (towards_sub_uniformity_zero_nhd'
        (towards_compose towards_prod_uniformity_fst uniform_continuous_subtype_val))
      (towards_sub_uniformity_zero_nhd'
        (towards_compose towards_prod_uniformity_snd uniform_continuous_subtype_val))
  end

private lemma uniform_continuous_swap [uniform_space α] [uniform_space β] {p : α → Prop} {q : β → Prop} :
  uniform_continuous (λx:{x:α×β // p x.1 ∧ q x.2},
     ((⟨x.val.1, x.property.left⟩ : {x // p x}), (⟨x.val.2, x.property.right⟩ : {x // q x}))) :=
uniform_continuous_prod_mk
  (uniform_continuous_subtype_mk
    (uniform_continuous_compose uniform_continuous_subtype_val uniform_continuous_fst) _)
  (uniform_continuous_subtype_mk
    (uniform_continuous_compose uniform_continuous_subtype_val uniform_continuous_snd) _)

lemma towards_mul_rat {r q : ℚ} : towards (λp:ℚ×ℚ, p.1 * p.2) (nhds (r, q)) (nhds (r * q)) :=
have hp : ∀{r:ℚ}, 0 < abs r + 1, from assume r, lt_add_of_le_of_pos (abs_nonneg r) zero_lt_one,
have ∀{r:ℚ}, {q | abs q < abs r + 1} ∈ (nhds r).sets,
  from assume r,
  have hn : - (abs r + 1) < r,
    from neg_lt_of_neg_lt $ lt_add_of_le_of_pos (neg_le_abs_self _) zero_lt_one,
  have hp : r < (abs r + 1),
    from lt_add_of_le_of_pos (le_abs_self _) zero_lt_one,
  (nhds r).upwards_sets (inter_mem_sets (gt_mem_nhds hp) (lt_mem_nhds hn)) $
    assume q ⟨h₁, h₂⟩, abs_by_cases (λq, q < abs r + 1) h₁ (neg_lt_of_neg_lt h₂),
have h : {a : ℚ × ℚ | abs (a.fst) < abs r + 1 ∧ abs (a.snd) < abs q + 1} ∈ (nhds (r, q)).sets,
  by rw [nhds_prod_eq]; exact prod_mem_prod this this,
have uniform_continuous (λp:{p:ℚ×ℚ // abs p.1 < abs r + 1 ∧ abs p.2 < abs q + 1}, p.1.1 * p.1.2),
  from uniform_continuous_compose uniform_continuous_swap
    (uniform_continuous_mul_rat hp hp),
towards_of_uniform_continuous_subtype this h

lemma vmap_infi {ι : Sort w} {f : ι → filter α} {m : β → α} :
  vmap m (⨅i, f i) = (⨅i, vmap m (f i)) :=
le_antisymm
  (le_infi $ assume i, vmap_mono $ infi_le _ i)
  (le_vmap_iff_map_le.mpr $ le_infi $ assume i, le_vmap_iff_map_le.mp $ infi_le _ _)

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
      from mem_vmap_of_mem $ mem_zero_nhd this,
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

@[simp] lemma quot_mk_image_univ_eq : (λx : Cauchy ℚ, ⟦x⟧) '' univ = univ :=
set.ext $ assume x, quotient.induction_on x $ assume a, ⟨by simp, assume _, ⟨a, trivial, rfl⟩⟩

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

lemma lift_rat_fun_of_rat {r : ℚ} {f : ℚ → ℚ} (hf : towards f (nhds r) (nhds (f r))) :
  of_rat (f r) = lift_rat_fun f (of_rat r) :=
(dense_embedding_of_rat.ext_e_eq $ towards_compose hf $ dense_embedding_of_rat.towards).symm

lemma lift_rat_op_of_rat_of_rat {r₁ r₂: ℚ} {f : ℚ → ℚ → ℚ}
  (hf : towards (λp:ℚ×ℚ, f p.1 p.2) (nhds (r₁, r₂)) (nhds (f r₁ r₂))) :
  of_rat (f r₁ r₂) = lift_rat_op f (of_rat r₁) (of_rat r₂) :=
let h := dense_embedding_of_rat_of_rat.ext_e_eq (towards_compose hf dense_embedding_of_rat.towards)
in h.symm

instance : has_add ℝ := ⟨lift_rat_op (+)⟩
instance : has_neg ℝ := ⟨lift_rat_fun has_neg.neg⟩
instance : has_sub ℝ := ⟨λx y, x + - y⟩
instance : has_mul ℝ := ⟨lift_rat_op (*)⟩
instance : has_inv ℝ := ⟨λa:ℝ, if a = 0 then 0 else lift_rat_fun has_inv.inv a⟩
instance : has_div ℝ := ⟨λx y, x * y⁻¹⟩

@[simp] lemma of_rat_zero : of_rat 0 = 0 := rfl

@[simp] lemma of_rat_one : of_rat 1 = 1 := rfl

@[simp] lemma of_rat_neg {r : ℚ} : of_rat (- r) = - of_rat r :=
lift_rat_fun_of_rat $ continuous_iff_towards.mp (continuous_of_uniform uniform_continuous_neg_rat) r

@[simp] lemma of_rat_add {r₁ r₂ : ℚ} : of_rat (r₁ + r₂) = of_rat r₁ + of_rat r₂ :=
lift_rat_op_of_rat_of_rat $
  continuous_iff_towards.mp (continuous_of_uniform uniform_continuous_add_rat) (r₁, r₂)

@[simp] lemma of_rat_sub {r₁ r₂ : ℚ} : of_rat (r₁ - r₂) = of_rat r₁ - of_rat r₂ :=
by simp; refl

@[simp] lemma of_rat_mul {r₁ r₂ : ℚ} : of_rat (r₁ * r₂) = of_rat r₁ * of_rat r₂ :=
lift_rat_op_of_rat_of_rat towards_mul_rat

@[simp] lemma of_rat_inv {r : ℚ} : of_rat r⁻¹ = (of_rat r)⁻¹ :=
show of_rat r⁻¹ = (if of_rat r = 0 then 0 else lift_rat_fun has_inv.inv (of_rat r)),
  from if h : r = 0 then by simp [h, inv_zero]
    else
      have of_rat r ≠ 0, from h ∘ dense_embedding_of_rat.inj _ _,
      by simp [this]; exact lift_rat_fun_of_rat (towards_inv_rat h)

lemma uniform_continuous_neg_real : uniform_continuous (λp:ℝ, - p) :=
uniform_continuous_uniformly_extend uniform_embedding_of_rat dense_embedding_of_rat.dense $
  uniform_continuous_compose
    uniform_continuous_neg_rat
    (uniform_continuous_of_embedding uniform_embedding_of_rat)

lemma continuous_neg_real : continuous (λp:ℝ, - p) :=
continuous_of_uniform uniform_continuous_neg_real

lemma closed_property [topological_space α] [topological_space β] {e : α → β} {p : β → Prop}
  (he : closure (e '' univ) = univ) (hp : closed {x | p x}) (h : ∀a, p (e a)) :
  ∀b, p b :=
have univ ⊆ {b | p b},
  from calc univ = closure (e '' univ) : he.symm
    ... ⊆ closure {b | p b} : closure_mono $ image_subset_iff_subset_preimage.mpr $ assume a _, h a
    ... = _ : closure_eq_of_closed hp,
assume b, this trivial

lemma closed_property2 [topological_space α] [topological_space β] {e : α → β} {p : β → β → Prop}
  (he : dense_embedding e) (hp : closed {q:β×β | p q.1 q.2}) (h : ∀a₁ a₂, p (e a₁) (e a₂)) :
  ∀b₁ b₂, p b₁ b₂ :=
have ∀q:β×β, p q.1 q.2,
  from closed_property ((he.prod he).closure_image_univ) hp $ assume ⟨a₁, a₂⟩, h _ _,
assume b₁ b₂, this ⟨b₁, b₂⟩

lemma closed_property3 [topological_space α] [topological_space β] {e : α → β} {p : β → β → β → Prop}
  (he : dense_embedding e) (hp : closed {q:β×β×β | p q.1 q.2.1 q.2.2}) (h : ∀a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) :
  ∀b₁ b₂ b₃, p b₁ b₂ b₃ :=
have ∀q:β×β×β, p q.1 q.2.1 q.2.2,
  from closed_property ((he.prod $ he.prod he).closure_image_univ) hp $ assume ⟨a₁, a₂, a₃⟩, h _ _ _,
assume b₁ b₂ b₃, this ⟨b₁, b₂, b₃⟩

lemma neg_neg_real : ∀r:ℝ, - - r = r :=
closed_property dense_embedding_of_rat.closure_image_univ
  (closed_eq (continuous_compose continuous_neg_real continuous_neg_real) continuous_id)
  (assume a, begin rw [←of_rat_neg, ←of_rat_neg]; simp end)

lemma preimage_neg_real : preimage (has_neg.neg : ℝ → ℝ) = image (has_neg.neg : ℝ → ℝ) :=
(image_eq_preimage_of_inverse _ _ neg_neg_real neg_neg_real).symm

lemma preimage_neg_rat : preimage (has_neg.neg : ℚ → ℚ) = image (has_neg.neg : ℚ → ℚ) :=
(image_eq_preimage_of_inverse _ _ neg_neg neg_neg).symm

lemma map_neg_real : map (has_neg.neg : ℝ → ℝ) = vmap (has_neg.neg : ℝ → ℝ) :=
funext $ assume f, map_eq_vmap_of_inverse (funext neg_neg_real) (funext neg_neg_real)

lemma map_neg_rat : map (has_neg.neg : ℚ → ℚ) = vmap (has_neg.neg : ℚ → ℚ) :=
funext $ assume f, map_eq_vmap_of_inverse (funext neg_neg) (funext neg_neg)

lemma uniform_continuous_add_real : uniform_continuous (λp:ℝ×ℝ, p.1 + p.2) :=
begin
  rw [real.has_add], simp [lift_rat_op], -- TODO: necessary, otherwise elaborator doesn't terminate
  exact (uniform_continuous_uniformly_extend
    (uniform_embedding_prod uniform_embedding_of_rat uniform_embedding_of_rat)
    dense_embedding_of_rat_of_rat.dense
    (uniform_continuous_compose uniform_continuous_add_rat
      (uniform_continuous_of_embedding uniform_embedding_of_rat)))
end

lemma continuous_add_real' : continuous (λp:ℝ×ℝ, p.1 + p.2) :=
continuous_of_uniform uniform_continuous_add_real

lemma continuous_add_real [topological_space α] {f g : α → ℝ} (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x + g x) :=
continuous_compose (continuous_prod_mk hf hg) continuous_add_real'

lemma continuous_mul_real : continuous (λp:ℝ×ℝ, p.1 * p.2) :=
have ∀r, ∃(s : set ℚ) (q:ℚ),
    q > 0 ∧ closure (of_rat '' s) ∈ (nhds r).sets ∧ closed s ∧ (∀x∈s, abs x < q),
  from assume r,
  have {p:ℚ×ℚ | abs (p.1 - p.2) < 1} ∈ uniformity.sets,
    from mem_uniformity_rat zero_lt_one,
  let ⟨q, hq⟩ := closure_image_mem_nhds_of_uniform_embedding
      r uniform_embedding_of_rat dense_embedding_of_rat this,
    s := {q' | q' ≤ abs q + 1} ∩ {q' | - (abs q + 1) ≤ q'} in
  have {q' : ℚ | abs (q - q') < 1} ⊆ s,
    from assume q' h,
    have abs q' ≤ abs q + 1,
      from le_of_lt $ lt_add_of_sub_left_lt $
        lt_of_le_of_lt (abs_sub_abs_le_abs_sub _ _) $ abs_sub q q' ▸ h,
    show q' ≤ abs q + 1 ∧ - (abs q + 1) ≤ q',
      from ⟨le_trans (le_abs_self q') this, neg_le_of_neg_le $ le_trans (neg_le_abs_self q') this⟩,
  have closure (of_rat '' s) ∈ (nhds r).sets,
    from (nhds r).upwards_sets hq $ closure_mono $ mono_image $ this,
  have ∀x∈s, abs x < (abs q + 1) + 1,
    from assume x ⟨(hx₁ : x ≤ abs q + 1), (hx₂ : -(abs q + 1) ≤ x)⟩,
    lt_add_of_le_of_pos (abs_by_cases (λx, x ≤ abs q + 1) hx₁ $ neg_le_of_neg_le hx₂) zero_lt_one,
  have closed s,
    from closed_inter closed_ge closed_le,
  ⟨s, abs q + 1 + 1,
    lt_add_of_le_of_pos (le_add_of_le_of_nonneg (abs_nonneg _) zero_le_one) zero_lt_one,
    ‹_›, ‹_›, ‹_›⟩,
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
    have hsc : closed (set.prod s₁ s₂), from closed_prod hs₁c hs₂c,
    uniform_extend_subtype hu
      (uniform_embedding_prod uniform_embedding_of_rat uniform_embedding_of_rat)
      dense_embedding_of_rat_of_rat.dense
      hs hsc (assume ⟨p₁, p₂⟩ ⟨h₁, h₂⟩, ⟨hsq₁ p₁ h₁, hsq₂ p₂ h₂⟩))
end

lemma continuous_mul_real' [topological_space α] {f g : α → ℝ} (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x * g x) :=
continuous_compose (continuous_prod_mk hf hg) continuous_mul_real

lemma neg_preimage_closure {s : set ℝ} : (λr:ℝ, -r) ⁻¹' closure s = closure ((λr:ℝ, -r) '' s) :=
have (λr:ℝ, -r) ∘ (λr:ℝ, -r) = id, from funext neg_neg_real,
by rw [preimage_neg_real]; exact
  (subset.antisymm (image_closure_subset_closure_image continuous_neg_real) $
    calc closure ((λ (r : ℝ), -r) '' s) = (λr, -r) '' ((λr, -r) '' closure ((λ (r : ℝ), -r) '' s)) :
        by rw [←image_comp, this, image_id]
      ... ⊆ (λr, -r) '' closure ((λr, -r) '' ((λ (r : ℝ), -r) '' s)) :
        mono_image $ image_closure_subset_closure_image continuous_neg_real
      ... = _ : by rw [←image_comp, this, image_id])

-- TODO: clean up
lemma towards_inv_real {r : ℝ} (hr : r ≠ 0) : towards has_inv.inv (nhds r) (nhds r⁻¹) :=
let inv := dense_embedding.ext dense_embedding_of_rat (of_rat ∘ has_inv.inv) in
suffices towards inv (nhds r) (nhds (inv r)),
begin
  rw [real.has_inv],
  simp [lift_rat_fun, hr],
  exact (towards_cong this $ (nhds r).upwards_sets (compl_singleton_mem_nhds hr)
    begin intro x, simp {contextual := tt} end)
end,
let ⟨u, v, hu, hv, hru, h0v, huv⟩ := t2_separation hr in
have ∃i:ℚ, i>0 ∧ ∀q, abs q < i → of_rat q ∈ v,
  from have {q:ℚ | of_rat q ∈ v} ∈ (nhds (0:ℚ)).sets,
    from dense_embedding_of_rat.towards (mem_nhds_sets hv h0v),
  by rw [nhds_0_eq_zero_nhd, mem_zero_nhd_iff] at this; simp * at *,
let ⟨i, hi, hvi⟩ := this in
have 0 < i / 2, from div_pos_of_pos_of_pos hi zero_lt_two,
have u ∈ (nhds r).sets, from mem_nhds_sets hu hru,
dense_embedding_of_rat.towards_ext $ (nhds r).upwards_sets this $
  assume r hr,
  let ⟨a, (ha : closure (of_rat '' {a' : ℚ | abs (a - a') < i / 2}) ∈ (nhds r).sets)⟩ :=
    closure_image_mem_nhds_of_uniform_embedding r
      uniform_embedding_of_rat dense_embedding_of_rat $ mem_uniformity_rat ‹0 < i / 2› in
  have hia : i / 2 < abs a,
    from lt_of_not_ge $ assume hia,
    have of_rat '' {a' : ℚ | abs (a - a') < i / 2} ⊆ -u,
      from assume x ⟨y, hy, hy_eq⟩,
      have of_rat y ∈ v, from hvi _ $
        calc abs y = abs (a + - (a - y)) : by rw [←sub_eq_add_neg, sub_sub_self]
          ... ≤ abs a + abs (- (a - y)) : abs_add_le_abs_add_abs _ _
          ... < i / 2 + i / 2 : add_lt_add_of_le_of_lt hia $ by rwa [abs_neg]
          ... = (i + i) / 2 : div_add_div_same _ _ _
          ... = i : add_self_div_two _,
      have of_rat y ∈ - u,
        from assume hy,
        have of_rat y ∈ u ∩ v, from ⟨hy, this⟩,
        by rwa [huv] at this,
      hy_eq ▸ this,
    have u ∩ -u ∈ (nhds r).sets,
      from inter_mem_sets (mem_nhds_sets hu hr) $
         (nhds r).upwards_sets ha $ closure_minimal this $ closed_compl_iff.mpr $ hu,
    have ∅ ∈ (nhds r).sets, by simp at this; exact this,
    show false, from mem_of_nhds this,
  have h_ex: ∀r (a > i / 2), closure (of_rat '' {a' : ℚ | abs (a - a') < i / 2}) ∈ (nhds r).sets →
    ∃c:ℝ, towards (of_rat ∘ has_inv.inv) (vmap of_rat (nhds r)) (nhds c),
    from assume r a (hia : i / 2 < a) ha,
    let j := a - i / 2 in
    have 0 < j, from sub_pos_of_lt hia,
    have 0 < j / 2, from div_pos_of_pos_of_pos this zero_lt_two,
    have hsp : ∀x∈{x:ℚ | j ≤ x}, j / 2 < x,
      from assume x (hx : j ≤ x),
      lt_of_lt_of_le (div_lt_of_mul_lt_of_pos zero_lt_two $ lt_mul_of_gt_one_right ‹_› one_lt_two) hx,
    have hs : ∀a':ℚ, abs (a - a') < i / 2 → a - i / 2 ≤ a',
      from assume a' ha',
      le_of_lt $ sub_lt_of_sub_lt $ lt_of_le_of_lt (le_abs_self _) ha',
    have uniform_continuous (of_rat ∘ (has_inv.inv ∘ @subtype.val ℚ (λx, j / 2 < x))),
      from uniform_continuous_compose
        (uniform_continuous_inv_pos_rat ‹0 < j / 2›)
        (uniform_continuous_of_embedding uniform_embedding_of_rat),
    uniform_extend_subtype this uniform_embedding_of_rat dense_embedding_of_rat.dense
      ((nhds r).upwards_sets ha $ closure_mono $ mono_image $ hs) closed_le hsp,
  match le_total 0 a with
  | (or.inl h) := h_ex r a (by rwa [abs_of_nonneg h] at hia) ha
  | (or.inr h) :=
    have towards (λr, -r) (nhds (-r)) (nhds (- - r)),
      from continuous_iff_towards.mp (continuous_of_uniform uniform_continuous_neg_real) (-r),
    have preimage (λr, -r) (closure (of_rat '' {a' : ℚ | abs (a - a') < i / 2})) ∈ (nhds (-r)).sets,
      by rw [neg_neg_real] at this; exact this ha,
    have (closure (of_rat '' {a' : ℚ | abs (- a - a') < i / 2})) ∈ (nhds (-r)).sets,
      from (nhds (-r)).upwards_sets this $
        calc preimage (λr, -r) (closure (of_rat '' {a' : ℚ | abs (a - a') < i / 2}))
            ⊆ closure ((λr, -r) '' (of_rat '' {a' : ℚ | abs (a - a') < i / 2})) :
            by rw [neg_preimage_closure]; exact subset.refl _
          ... = closure (of_rat '' (has_neg.neg '' {a' : ℚ | abs (a - a') < i / 2})) :
            begin rw [← image_comp, ← image_comp], simp [(∘)] end
          ... = closure (of_rat '' {a' : ℚ | abs (a - - a') < i / 2}) : by rw [←preimage_neg_rat]; refl
          ... = closure (of_rat '' {a' : ℚ | abs (- a - a') < i / 2}) :
            begin conv in (abs _) { rw [←abs_neg] }, simp end,
    have ∃c:ℝ, towards (of_rat ∘ has_inv.inv) (vmap of_rat (nhds (-r))) (nhds c),
      from h_ex (-r) (-a) (by rwa [abs_of_nonpos h] at hia) this,
    let ⟨c, (hc : towards (of_rat ∘ has_inv.inv) (vmap of_rat (nhds (-r))) (nhds c))⟩ := this in
    have towards (has_neg.neg ∘ (of_rat ∘ has_inv.inv)) (vmap of_rat (nhds (-r))) (nhds (- c)),
      from towards_compose hc $ continuous_iff_towards.mp continuous_neg_real _,
    have h_eq : has_neg.neg ∘ (of_rat ∘ has_inv.inv) = (of_rat ∘ has_inv.inv) ∘ has_neg.neg,
      from funext $ assume r, by simp [(∘), -of_rat_inv, inv_neg],
    have towards (of_rat ∘ has_inv.inv) (map has_neg.neg $ vmap of_rat (nhds (-r))) (nhds (- c)),
      from towards_map' $ by rw [h_eq] at this; exact this,
    have h_le : vmap of_rat (nhds r) ≤ (map has_neg.neg $ vmap of_rat $ nhds (-r)),
      from have of_rat ∘ has_neg.neg = has_neg.neg ∘ of_rat,
        from funext $ assume x, of_rat_neg,
      begin
        rw [map_neg_rat, vmap_vmap_comp, this],
        conv in (vmap (has_neg.neg ∘ _) (nhds _)) { rw [←vmap_vmap_comp] },
        exact (vmap_mono $ le_vmap_iff_map_le.mpr $ continuous_iff_towards.mp continuous_neg_real _)
      end,
    ⟨- c, le_trans (map_mono h_le) this⟩
  end

lemma continuous_inv_real' : continuous (λa:{r:ℝ // r ≠ 0}, a.val⁻¹) :=
continuous_iff_towards.mpr $ assume ⟨r, hr⟩,
  towards_compose (continuous_iff_towards.mp continuous_subtype_val _) (towards_inv_real hr)

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

instance : discrete_field ℝ :=
{ zero             := 0,
  add              := (+),
  neg              := has_neg.neg,
  one              := 1,
  mul              := (*),
  inv              := has_inv.inv,
  zero_add         := closed_property dense_embedding_of_rat.closure_image_univ
    (closed_eq (continuous_add_real continuous_const continuous_id) continuous_id)
    begin intros, show of_rat 0 + of_rat a = of_rat a, rw [←of_rat_add], simp [-of_rat_add] end,
  add_zero         := closed_property dense_embedding_of_rat.closure_image_univ
    (closed_eq (continuous_add_real continuous_id continuous_const) continuous_id)
    begin intros, show of_rat a + of_rat 0 = of_rat a, rw [←of_rat_add], simp [-of_rat_add] end,
  add_comm         := closed_property2 dense_embedding_of_rat
    (closed_eq (continuous_add_real continuous_fst continuous_snd) (continuous_add_real continuous_snd continuous_fst))
    begin intros; simp only [of_rat_add.symm, add_comm] end,
  add_assoc        := closed_property3 dense_embedding_of_rat
    (closed_eq (continuous_add_real
        (continuous_add_real continuous_fst $ continuous_compose continuous_snd continuous_fst) $
        continuous_compose continuous_snd continuous_snd)
      (continuous_add_real continuous_fst $
        continuous_add_real (continuous_compose continuous_snd continuous_fst) $
        continuous_compose continuous_snd continuous_snd))
    begin intros; simp only [of_rat_add.symm, add_assoc] end,
  add_left_neg     := closed_property dense_embedding_of_rat.closure_image_univ
    (closed_eq (continuous_add_real continuous_neg_real continuous_id) continuous_const)
    begin intros, simp only [of_rat_add.symm, of_rat_neg.symm, of_rat_zero, add_left_neg] end,
  mul_one          := closed_property dense_embedding_of_rat.closure_image_univ
    (closed_eq (continuous_mul_real' continuous_id continuous_const) continuous_id)
    begin intros, simp only [of_rat_mul.symm, of_rat_one.symm, mul_one] end,
  one_mul          := closed_property dense_embedding_of_rat.closure_image_univ
    (closed_eq (continuous_mul_real' continuous_const continuous_id) continuous_id)
    begin intros, simp only [of_rat_mul.symm, of_rat_one.symm, one_mul] end,
  mul_comm         := closed_property2 dense_embedding_of_rat
    (closed_eq (continuous_mul_real' continuous_fst continuous_snd) (continuous_mul_real' continuous_snd continuous_fst))
    begin intros; simp only [of_rat_mul.symm, mul_comm] end,
  mul_assoc        := closed_property3 dense_embedding_of_rat
    (closed_eq (continuous_mul_real'
        (continuous_mul_real' continuous_fst $ continuous_compose continuous_snd continuous_fst) $
        continuous_compose continuous_snd continuous_snd)
      (continuous_mul_real' continuous_fst $
        continuous_mul_real' (continuous_compose continuous_snd continuous_fst) $
        continuous_compose continuous_snd continuous_snd))
    begin intros; simp only [of_rat_mul.symm, mul_assoc] end,
  left_distrib     := closed_property3 dense_embedding_of_rat
    (closed_eq (continuous_mul_real' continuous_fst
      (continuous_add_real (continuous_compose continuous_snd continuous_fst) (continuous_compose continuous_snd continuous_snd)))
      (continuous_add_real (continuous_mul_real' continuous_fst (continuous_compose continuous_snd continuous_fst))
         (continuous_mul_real' continuous_fst (continuous_compose continuous_snd continuous_snd))))
    begin intros; simp only [of_rat_mul.symm, of_rat_add.symm, left_distrib] end,
  right_distrib    := closed_property3 dense_embedding_of_rat
    (closed_eq (continuous_mul_real'
      (continuous_add_real continuous_fst (continuous_compose continuous_snd continuous_fst))
      (continuous_compose continuous_snd continuous_snd))
      (continuous_add_real
        (continuous_mul_real' continuous_fst (continuous_compose continuous_snd continuous_snd))
        (continuous_mul_real' (continuous_compose continuous_snd continuous_fst)
          (continuous_compose continuous_snd continuous_snd))))
    begin intros; simp only [of_rat_mul.symm, of_rat_add.symm, right_distrib] end,
  zero_ne_one      := assume h, zero_ne_one $ dense_embedding_of_rat.inj 0 1 h,
  mul_inv_cancel   :=
    suffices ∀a:{a:ℝ // a ≠ 0}, a.val * a.val⁻¹ = 1,
      from assume a ha, this ⟨a, ha⟩,
    closed_property closure_compl_zero_image_univ
      (closed_eq (continuous_mul_real' continuous_subtype_val continuous_inv_real') continuous_const)
      (assume ⟨a, (ha : a ≠ 0)⟩,
        by simp [*, -of_rat_mul, -of_rat_inv, of_rat_mul.symm, of_rat_inv.symm, mul_inv_cancel ha] at *),
  inv_mul_cancel   :=
      suffices ∀a:{a:ℝ // a ≠ 0}, a.val⁻¹ * a.val = 1,
      from assume a ha, this ⟨a, ha⟩,
    closed_property closure_compl_zero_image_univ
      (closed_eq (continuous_mul_real' continuous_inv_real' continuous_subtype_val) continuous_const)
      (assume ⟨a, (ha : a ≠ 0)⟩,
        by simp [*, -of_rat_mul, -of_rat_inv, of_rat_mul.symm, of_rat_inv.symm, mul_inv_cancel ha] at *),
  inv_zero := by simp [has_inv.inv],
  has_decidable_eq := by apply_instance }

def nonneg : set ℝ := closure (of_rat '' {q : ℚ | q ≥ 0})

instance : has_le ℝ := ⟨λa b, b - a ∈ nonneg⟩

lemma of_rat_mem_nonneg {q : ℚ} (h : 0 ≤ q) : of_rat q ∈ nonneg :=
have of_rat q ∈ of_rat '' {q:ℚ | q ≥ 0}, from ⟨q, h, rfl⟩,
subset_closure this

lemma of_rat_mem_nonneg_iff {q : ℚ} : of_rat q ∈ nonneg ↔ 0 ≤ q :=
⟨ begin
    rw [nonneg, ←closure_induced, ←dense_embedding_of_rat.embedding.right, closure_eq_of_closed],
    exact id,
    exact closed_le,
    exact dense_embedding_of_rat.inj
  end,
  of_rat_mem_nonneg⟩

lemma le_sub_iff_add_le [ordered_comm_group α] {a b c : α} : a ≤ b - c ↔ a + c ≤ b :=
by rw [add_comm]; exact ⟨add_le_of_le_sub_left, le_sub_left_of_add_le⟩

lemma of_rat_le_of_rat {q₁ q₂ : ℚ} : of_rat q₁ ≤ of_rat q₂ ↔ q₁ ≤ q₂ :=
show (of_rat q₂ - of_rat q₁) ∈ nonneg ↔ q₁ ≤ q₂,
  by rw [←of_rat_sub, of_rat_mem_nonneg_iff, le_sub_iff_add_le]; simp

lemma mem_closure_of_continuous [topological_space α] [topological_space β]
  {f : α → β} {a : α} {s : set α} {t : set β}
  (hf : continuous f) (ha : a ∈ closure s) (h : ∀a∈s, f a ∈ closure t) :
  f a ∈ closure t :=
calc f a ∈ f '' closure s : mem_image_of_mem _ ha
  ... ⊆ closure (f '' s) : image_closure_subset_closure_image hf
  ... ⊆ closure (closure t) : closure_mono $ image_subset_iff_subset_preimage.mpr $ h
  ... ⊆ closure t : begin rw [closure_eq_of_closed], exact subset.refl _, exact closed_closure end

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

lemma mem_nonneg_of_continuous2 {f : ℝ → ℝ → ℝ} {a b : ℝ}
  (hf : continuous (λp:ℝ×ℝ, f p.1 p.2)) (ha : a ∈ nonneg) (hb : b ∈ nonneg)
  (h : ∀{a b : ℚ}, 0 ≤ a → 0 ≤ b → f (of_rat a) (of_rat b) ∈ nonneg) :
  (f a b) ∈ nonneg :=
mem_closure_of_continuous2 hf ha hb $ assume a ⟨a', ha, ha'⟩ b ⟨b', hb, hb'⟩, ha' ▸ hb' ▸ h ha hb

@[trans] lemma mem_of_eq_of_mem {α : Type u} {x y : α} {s : set α} (hx : x = y) (h : y ∈ s) : x ∈ s :=
hx.symm ▸ h

lemma two_eq_of_rat_two : 2 = of_rat 2 := by simp [bit0]

lemma zero_le_iff_nonneg {r : ℝ} : 0 ≤ r ↔ r ∈ nonneg :=
show (r - 0) ∈ nonneg ↔ r ∈ nonneg, by simp

private def abs_real := lift_rat_fun abs

private lemma uniform_continuous_abs_real' : uniform_continuous abs_real :=
uniform_continuous_uniformly_extend uniform_embedding_of_rat dense_embedding_of_rat.dense $
  uniform_continuous_compose
  uniform_continuous_abs_rat (uniform_continuous_of_embedding uniform_embedding_of_rat)

private lemma continuous_abs_real' : continuous abs_real :=
continuous_of_uniform uniform_continuous_abs_real'

private lemma of_rat_abs_real {r} : of_rat (abs r) = abs_real (of_rat r) :=
lift_rat_fun_of_rat $ continuous_iff_towards.mp (continuous_of_uniform uniform_continuous_abs_rat) r

private lemma abs_real_neg : ∀{r}, abs_real (- r) = abs_real r :=
closed_property dense_embedding_of_rat.closure_image_univ
  (closed_eq (continuous_compose continuous_neg_real continuous_abs_real') continuous_abs_real')
  (by simp [of_rat_abs_real.symm, -of_rat_neg, of_rat_neg.symm, abs_neg])

private lemma abs_real_of_nonneg {r:ℝ} : 0 ≤ r → abs_real r = r :=
let de := dense_embedding_of_rat.subtype (λq:ℚ, 0 ≤ q) in
have ∀r:{x // x ∈ nonneg}, abs_real r.val = r.val,
  from closed_property de.closure_image_univ
    (closed_eq (continuous_compose continuous_subtype_val continuous_abs_real') continuous_subtype_val)
    (by simp [forall_subtype_iff, dense_embedding.subtype_emb, of_rat_abs_real.symm];
      exact (assume a ha, congr_arg of_rat $ abs_of_nonneg ha) ),
by rw [zero_le_iff_nonneg]; intro hr; exact this ⟨r, hr⟩

lemma eq_0_of_nonneg_of_neg_nonneg {r : ℝ} (hp : r ∈ nonneg) (hn : -r ∈ nonneg) : r = 0 :=
let f := λr, abs_real (- r) + (- r) in
have continuous f,
  from continuous_add_real (continuous_compose continuous_neg_real continuous_abs_real') continuous_neg_real,
have ∀ r∈nonneg, f r ∈ closure ({0} : set ℝ),
  from assume r hr, @mem_closure_of_continuous ℝ ℝ _ _ f r _ _ this hr $
    show ∀ (a : ℝ), a ∈ of_rat '' {q : ℚ | q ≥ 0} → abs_real (- a) + (- a) ∈ closure ({0}:set ℝ),
      from assume a ⟨q, (hq : 0 ≤ q), hrq⟩,
      by simp [hrq.symm, of_rat_abs_real.symm, -of_rat_add, -of_rat_neg, of_rat_neg.symm,
               of_rat_add.symm, abs_neg, abs_of_nonneg hq],
have h: ∀{r}, r ∈ nonneg → abs_real (- r) + (- r) = 0,
  from assume r hr, show f r = 0, by simp [closure_singleton] at this; exact this _ hr,
have 2 * r = 0,
  from calc 2 * r = (abs_real (- - r) + (- - r)) - (abs_real (-r) + - r) : by simp [abs_real_neg, bit0, mul_add]
    ... = 0 : by rw [h hp, h hn]; simp,
calc r = (2 * r) / 2 :
  begin
    rw [mul_div_cancel_left],
    rw [two_eq_of_rat_two],
    exact assume h : of_rat 2 = of_rat 0,
      have 2 < (2:ℚ), from
        calc (2:ℚ) = 0 : dense_embedding_of_rat.inj _ _ h
          ... < 2 : zero_lt_two,
      lt_irrefl 2 this
  end
  ... = 0 : by simp [this, zero_div]

instance : linear_order ℝ :=
{ le := (≤),
  le_refl := assume a, show (a - a) ∈ nonneg, by simp; exact of_rat_mem_nonneg (le_refl _),
  le_trans := assume a b c (h₁ : b - a ∈ nonneg) (h₂ : c - b ∈ nonneg),
    have (c - b) + (b - a) ∈ nonneg,
      from mem_nonneg_of_continuous2 continuous_add_real' h₂ h₁ $
        assume a b ha hb, by rw [←of_rat_add]; exact of_rat_mem_nonneg (le_add_of_le_of_nonneg ha hb),
    have (c - b) + (b - a) = c - a,
      from calc (c - b) + (b - a) = c + - a + (b + -b) : by simp [-add_right_neg]
        ... = c - a : by simp,
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
    ... = b - a : by simp,
show (c + b) - (c + a) ∈ nonneg ↔ b - a ∈ nonneg,
  from by rwa [this]

private lemma mul_nonneg {a b : ℝ} : 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
begin
  simp [zero_le_iff_nonneg],
  exact assume ha hb, mem_nonneg_of_continuous2 continuous_mul_real ha hb $
    by simp [-of_rat_mul, of_rat_mul.symm, of_rat_mem_nonneg_iff]; exact (assume a b, mul_nonneg)
end

instance : discrete_linear_ordered_field ℝ :=
{ real.discrete_field with
  le              := (≤),
  lt              := (<),
  le_refl         := le_refl,
  le_trans        := assume a b c, le_trans,
  le_antisymm     := assume a b, le_antisymm,
  le_total        := le_total,
  lt_iff_le_not_le := assume a b, lt_iff_le_not_le,
  zero_lt_one     := lt_of_not_ge $ assume : of_rat 0 - of_rat 1 ∈ nonneg,
    begin
      rw [←of_rat_sub, of_rat_mem_nonneg_iff] at this,
      have : (0:ℚ) < 0,
        from calc (0:ℚ) ≤ 0 - 1 : this
          ... < -0 : lt_neg_of_lt_neg $ by simp [zero_lt_one],
      exact lt_irrefl _ this
    end,
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

lemma continuous_sub_real [topological_space α] {f g : α → ℝ} (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x - g x) :=
by simp; exact continuous_add_real hf (continuous_compose hg continuous_neg_real)

lemma closed_le_real [topological_space α] {f g : α → ℝ} (hf : continuous f) (hg : continuous g) :
  closed {a:α | f a ≤ g a} :=
have h : {a:α | f a ≤ g a} = (λa, g a - f a) ⁻¹' nonneg,
  from set.ext $ by simp [zero_le_iff_nonneg.symm, -sub_eq_add_neg, le_sub_iff_add_le],
have closed ((λa, g a - f a) ⁻¹' nonneg),
  from continuous_iff_closed.mp (continuous_sub_real hg hf) _ closed_closure,
by rw [h]; exact this

lemma open_lt_real [topological_space α] {f g : α → ℝ} (hf : continuous f) (hg : continuous g) :
  open' {a | f a < g a} :=
have {a | f a < g a} = - {a | g a ≤ f a}, from set.ext $ assume y, by simp [not_le_iff],
by rw [this]; exact open_compl_iff.mpr (closed_le_real hg hf)

lemma closed_imp [topological_space α] {p q : α → Prop}
  (hp : open' {x | p x}) (hq : closed {x | q x}) : closed {x | p x → q x} :=
have {x | p x → q x} = (- {x | p x}) ∪ {x | q x}, from set.ext $ by finish,
by rw [this]; exact closed_union (closed_compl_iff.mpr hp) hq

lemma abs_real_eq_abs : abs_real = abs :=
funext $ assume r,
match le_total 0 r with
| or.inl h := by simp [abs_of_nonneg h, abs_real_of_nonneg h]
| or.inr h :=
  have 0 ≤ -r, from le_neg_of_le_neg $ by simp [h],
  calc abs_real r = abs_real (- - r) : by simp
    ... = - r : by rw [abs_real_neg, abs_real_of_nonneg this]
    ... = _ : by simp [abs_of_nonpos h]
end

lemma uniform_continuous_abs_real : uniform_continuous (abs : ℝ → ℝ) :=
by rw [←abs_real_eq_abs]; exact uniform_continuous_abs_real'

lemma continuous_abs_real : continuous (abs : ℝ → ℝ) :=
continuous_of_uniform uniform_continuous_abs_real

lemma of_rat_abs {q : ℚ} : of_rat (abs q) = abs (of_rat q) :=
by rw [←abs_real_eq_abs]; exact of_rat_abs_real

lemma mem_uniformity_closed [uniform_space α] {s : set (α×α)} (h : s ∈ (@uniformity α _).sets) :
  ∃t∈(@uniformity α _).sets, closed t ∧ t ⊆ s :=
have s ∈ ((@uniformity α _).lift' closure).sets, by rwa [uniformity_eq_uniformity_closure] at h,
have ∃t∈(@uniformity α _).sets, closure t ⊆ s,
  by rwa [mem_lift'_iff] at this; apply closure_mono,
let ⟨t, ht, hst⟩ := this in
⟨closure t, uniformity.upwards_sets ht subset_closure, closed_closure, hst⟩

lemma mem_uniformity_real {s : set (ℝ × ℝ)} :
  s ∈ (@uniformity ℝ _).sets ↔ (∃e>0, ∀r₁ r₂:ℝ, abs (r₁ - r₂) < of_rat e → (r₁, r₂) ∈ s) :=
⟨ assume : s ∈ uniformity.sets,
  let ⟨s', hs', hcs', hss'⟩ := mem_uniformity_closed this in
  have s'_eq : {x : ℝ × ℝ | (x.fst, x.snd) ∈ s'} = s', by simp,
  have (λp:ℚ×ℚ, (of_rat p.1, of_rat p.2)) ⁻¹' s' ∈ (zero_nhd.vmap (λp:ℚ×ℚ, p.1 - p.2)).sets,
    by rw [←uniformity_rat, ←uniform_embedding_of_rat.right]; exact preimage_mem_vmap hs',
  let ⟨t, ht, (hst : _ ⊆ _)⟩ := this, ⟨e, he, het⟩ := by rw [mem_zero_nhd_iff] at ht; exact ht in
  have ∀r:ℝ×ℝ, abs (r.1 - r.2) < of_rat e → (r.1, r.2) ∈ s',
    from closed_property dense_embedding_of_rat_of_rat.closure_image_univ
      (closed_imp (open_lt_real
        (continuous_compose (continuous_sub_real continuous_fst continuous_snd) continuous_abs_real)
          continuous_const) $ by simp [s'_eq]; exact hcs') $
      assume ⟨q₁, q₂⟩,
      begin
        simp [-sub_eq_add_neg, -of_rat_sub, of_rat_sub.symm, of_rat_abs.symm, of_rat_lt_of_rat];
        exact assume hq, @hst (q₁, q₂) (het (q₁ - q₂) hq)
      end,
  ⟨e, he, assume r₁ r₂ hr, hss' $ this (r₁, r₂) hr⟩,
  assume ⟨e, he, (hes : ∀ (r₁ r₂ : ℝ), abs (r₁ - r₂) < of_rat e → (r₁, r₂) ∈ s)⟩,
  have 0 < e/2, from div_pos_of_pos_of_pos he zero_lt_two,
  have {q:ℚ×ℚ | abs (q.1 - q.2) < e/2 } ∈ (uniformity.vmap (λp:ℚ×ℚ, (of_rat p.1, of_rat p.2))).sets,
    by rw [uniform_embedding_of_rat.right]; exact mem_uniformity_rat this,
  let ⟨t, ht, hte⟩ := this in
  have ∀p:ℝ×ℝ, p ∈ interior t → abs (p.1 - p.2) ≤ of_rat (e/2),
    from closed_property dense_embedding_of_rat_of_rat.closure_image_univ
      (closed_imp open_interior $ closed_le_real (continuous_compose
        (continuous_sub_real continuous_fst continuous_snd) continuous_abs_real)
        continuous_const) $
      assume ⟨q₁, q₂⟩ hq,
        have (of_rat q₁, of_rat q₂) ∈ t, from interior_subset hq,
        have abs (q₁ - q₂) ≤ e / 2, from le_of_lt $ @hte (q₁, q₂) this,
        by simp [-sub_eq_add_neg, -of_rat_sub, of_rat_sub.symm, of_rat_abs.symm, of_rat_le_of_rat];
          assumption,
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
  from inter_mem_inf_sets (mem_nhds_sets (open_lt_real continuous_const continuous_id) $
    show r < r + 1, from lt_add_of_le_of_pos (le_refl _) zero_lt_one)
    (mem_principal_sets.mpr $ subset.refl _),
let ⟨x, hx, ⟨q, hq, hxq⟩⟩ := inhabited_of_mem_sets dense_embedding_of_rat.nhds_inf_neq_bot this in
⟨q, hxq.symm ▸ hx⟩

lemma nat.le_zero_iff {i : ℕ} : i ≤ 0 ↔ i = 0 :=
⟨nat.eq_zero_of_le_zero, assume h, h ▸ le_refl i⟩

lemma set_compr_eq_eq_singleton {a : α} : {b | b = a} = {a} :=
set.ext $ by simp

lemma finite_le_nat : ∀{n:ℕ}, finite {i | i ≤ n}
| 0 := by simp [nat.le_zero_iff, set_compr_eq_eq_singleton]
| (n + 1) :=
  have {i | i ≤ n + 1} = insert (n + 1) {i | i ≤ n},
    from set.ext $ begin simp end,
  _

lemma compact_01 : compact {r:ℝ | 0 ≤ r ∧ r ≤ 1 } :=
@compact_of_totally_bounded_closed ℝ _ _ {r:ℝ | 0 ≤ r ∧ r ≤ 1 }
  (assume t ht,
    let ⟨e, he, het⟩ := mem_uniformity_real.mp ht in
    let n := 0 in
    let c := (of_rat ∘ rat.of_int ∘ int.of_nat) '' {i:ℕ | i ≤ n} in
    have 0 < e⁻¹, from _,
    ⟨c, finite_image finite_le_nat, assume r ⟨hr0, hr1⟩, begin simp end⟩)
  (show closed {r:ℝ | 0 ≤ r ∧ r ≤ 1 }, from _)


def Sup (s : set ℝ) : ℝ := lim (⨅r:{r : ℝ // r ∈ s}, principal {r' | r' ∈ s ∧ r' ≥ r.val})

lemma Sup.ne_bot {s : set ℝ} {m : ℝ} (hne : s ≠ ∅) (hb : ∀r∈s, r ≤ m) :
  (⨅r:{r : ℝ // r ∈ s}, principal {r' | r' ∈ s ∧ r' ≥ r.val}) ≠ ⊥ :=
infi_neq_bot_of_directed (by apply_instance)
  (assume ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩, ⟨
    ⟨max r₁ r₂, if h: r₁ ≤ r₂ then by rwa [max_eq_right h] else by rwa [max_eq_left (le_of_not_ge h)]⟩,
    by simp; exact assume a ⟨ha, h⟩, ⟨le_trans (le_max_left _ _) h, ha⟩,
    by simp; exact assume a ⟨ha, h⟩, ⟨le_trans (le_max_right _ _) h, ha⟩⟩)
  (by simp [forall_subtype_iff]; exact assume a ha, ne_empty_of_mem ⟨ha, le_refl a⟩)

end