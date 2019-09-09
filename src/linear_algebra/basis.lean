/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp

Linear independence and basis sets in a module or vector space.

This file is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define the following concepts:

* `linear_independent α v`: states that the elements of the family `v` are linear independent

* `linear_independent.repr hv x`: choose the linear combination representing `x` on the linear
  independent vectors `v`, given `hv : linear_independent α v`.
  `x` should be in `span α (range v)` (uses classical choice).

* `is_basis α v`: if `v` is a basis, i.e. linear independent and spans the entire space

* `is_basis.repr hv x`: like `linear_independent.repr` but as a `linear_map`

* `is_basis.constr hv g`: constructs a `linear_map` by extending `g` from the basis `v`,
  given `hv : is_basis α v`.

-/
import linear_algebra.basic linear_algebra.finsupp order.zorn
noncomputable theory

open function lattice set submodule

variables {ι : Type*} {ι' : Type*} {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {v : ι → β}
variables [decidable_eq ι] [decidable_eq ι']
          [decidable_eq α] [decidable_eq β] [decidable_eq γ] [decidable_eq δ]

section module
variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
variables {a b : α} {x y : β}
include α

variables (α) (v)
/-- Linearly independent set of vectors -/
def linear_independent : Prop := (finsupp.total ι β α v).ker = ⊥
variables {α} {v}

theorem linear_independent_iff : linear_independent α v ↔
  ∀l, finsupp.total ι β α v l = 0 → l = 0 :=
by simp [linear_independent, linear_map.ker_eq_bot']

lemma linear_independent_empty_type (h : ¬ nonempty ι) : linear_independent α v :=
begin
 rw [linear_independent_iff],
 intros,
 ext i,
 exact false.elim (not_nonempty_iff_imp_false.1 h i)
end

lemma ne_zero_of_linear_independent
  {i : ι} (ne : 0 ≠ (1:α)) (hv : linear_independent α v) : v i ≠ 0 :=
λ h, ne $ eq.symm begin
  suffices : (finsupp.single i 1 : ι →₀ α) i = 0, {simpa},
  rw linear_independent_iff.1 hv (finsupp.single i 1),
  {simp},
  {simp [h]}
end

lemma linear_independent.comp
  (h : linear_independent α v) (f : ι' → ι) (hf : injective f) : linear_independent α (v ∘ f) :=
begin
  rw [linear_independent_iff, finsupp.total_comp],
  intros l hl,
  have h_map_domain : ∀ x, (finsupp.map_domain f l) (f x) = 0,
    by rw linear_independent_iff.1 h (finsupp.map_domain f l) hl; simp,
  ext,
  convert h_map_domain a,
  simp only [finsupp.map_domain_apply hf],
end

lemma linear_independent_of_zero_eq_one (zero_eq_one : (0 : α) = 1) : linear_independent α v :=
linear_independent_iff.2 (λ l hl, finsupp.eq_zero_of_zero_eq_one zero_eq_one _)

lemma linear_independent.unique (hv : linear_independent α v) {l₁ l₂ : ι →₀ α} :
  finsupp.total ι β α v l₁ = finsupp.total ι β α v l₂ → l₁ = l₂ :=
by apply linear_map.ker_eq_bot.1 hv

lemma linear_independent.injective (zero_ne_one : (0 : α) ≠ 1) (hv : linear_independent α v) :
  injective v :=
begin
  intros i j hij,
  let l : ι →₀ α := finsupp.single i (1 : α) - finsupp.single j 1,
  have h_total : finsupp.total ι β α v l = 0,
  { rw finsupp.total_apply,
    rw finsupp.sum_sub_index,
    { simp [finsupp.sum_single_index, hij] },
    { intros, apply sub_smul } },
  have h_single_eq : finsupp.single i (1 : α) = finsupp.single j 1,
  { rw linear_independent_iff at hv,
    simp [eq_add_of_sub_eq' (hv l h_total)] },
  show i = j,
  { apply or.elim ((finsupp.single_eq_single_iff _ _ _ _).1 h_single_eq),
    simp,
    exact λ h, false.elim (zero_ne_one.symm h.1) }
end

lemma linear_independent_span (hs : linear_independent α v) :
  @linear_independent ι α (span α (range v))
      (λ i : ι, ⟨v i, subset_span (mem_range_self i)⟩) _ _ _ _ _ _ :=
begin
  rw linear_independent_iff at *,
  intros l hl,
  apply hs l,
  have := congr_arg (submodule.subtype (span α (range v))) hl,
  convert this,
  rw [finsupp.total_apply, finsupp.total_apply],
  unfold finsupp.sum,
  rw linear_map.map_sum (submodule.subtype (span α (range v))),
  simp
end

section subtype
/- The following lemmas use the subtype defined by a set in β as the index set ι. -/

theorem linear_independent_comp_subtype {s : set ι} :
  linear_independent α (v ∘ subtype.val : s → β) ↔
  ∀ l ∈ (finsupp.supported α α s), (finsupp.total ι β α v) l = 0 → l = 0 :=
begin
  rw [linear_independent_iff, finsupp.total_comp],
  simp only [linear_map.comp_apply],
  split,
  { intros h l hl₁ hl₂,
    have h_bij : bij_on subtype.val (subtype.val ⁻¹' l.support.to_set : set s) l.support.to_set,
    { apply bij_on.mk,
      { unfold maps_to },
      { apply set.inj_on_of_injective _ subtype.val_injective },
      intros i hi,
      rw mem_image,
      use subtype.mk i (((finsupp.mem_supported _ _).1 hl₁ : ↑(l.support) ⊆ s) hi),
      rw mem_preimage,
      exact ⟨hi, rfl⟩ },
    show l = 0,
    { apply finsupp.eq_zero_of_comap_domain_eq_zero (subtype.val : s → ι) _ h_bij,
      apply h,
      convert hl₂,
      rw [finsupp.lmap_domain_apply, finsupp.map_domain_comap_domain],
      apply subtype.val_injective,
      rw subtype.range_val,
      exact (finsupp.mem_supported _ _).1 hl₁ } },
  { intros h l hl,
    have hl' : finsupp.total ι β α v (finsupp.emb_domain ⟨subtype.val, subtype.val_injective⟩ l) = 0,
    { rw finsupp.emb_domain_eq_map_domain ⟨subtype.val, subtype.val_injective⟩ l,
      apply hl },
    apply finsupp.emb_domain_inj.1,
    rw [h (finsupp.emb_domain ⟨subtype.val, subtype.val_injective⟩ l) _ hl',
        finsupp.emb_domain_zero],
    rw [finsupp.mem_supported, finsupp.support_emb_domain],
    intros x hx,
    rw [finset.mem_coe, finset.mem_map] at hx,
    rcases hx with ⟨i, x', hx'⟩,
    rw ←hx',
    simp }
end

theorem linear_independent_subtype {s : set β} :
  linear_independent α (λ x, x : s → β) ↔
  ∀ l ∈ (finsupp.supported α α s), (finsupp.total β β α id) l = 0 → l = 0 :=
by apply @linear_independent_comp_subtype _ _ _ id

theorem linear_independent_comp_subtype_disjoint {s : set ι} :
  linear_independent α (v ∘ subtype.val : s → β) ↔
  disjoint (finsupp.supported α α s) (finsupp.total ι β α v).ker :=
by rw [linear_independent_comp_subtype, linear_map.disjoint_ker]

theorem linear_independent_subtype_disjoint {s : set β} :
  linear_independent α (λ x, x : s → β) ↔
  disjoint (finsupp.supported α α s) (finsupp.total β β α id).ker :=
by apply @linear_independent_comp_subtype_disjoint _ _ _ id

theorem linear_independent_iff_total_on {s : set β} :
  linear_independent α (λ x, x : s → β) ↔ (finsupp.total_on β β α id s).ker = ⊥ :=
by rw [finsupp.total_on, linear_map.ker, linear_map.comap_cod_restrict, map_bot, comap_bot,
  linear_map.ker_comp, linear_independent_subtype_disjoint, disjoint, ← map_comap_subtype,
  map_le_iff_le_comap, comap_bot, ker_subtype, le_bot_iff]

lemma linear_independent.to_subtype_range
  (hv : linear_independent α v) : linear_independent α (λ x, x : range v → β) :=
begin
  by_cases zero_eq_one : (0 : α) = 1,
  { apply linear_independent_of_zero_eq_one zero_eq_one },
  rw linear_independent_subtype,
  intros l hl₁ hl₂,
  have h_bij : bij_on v (v ⁻¹' finset.to_set (l.support)) (finset.to_set (l.support)),
  { apply bij_on.mk,
    { unfold maps_to },
    { apply set.inj_on_of_injective _ (linear_independent.injective zero_eq_one hv) },
    intros x hx,
    rcases mem_range.1 (((finsupp.mem_supported _ _).1 hl₁ : ↑(l.support) ⊆ range v) hx) with ⟨i, hi⟩,
    rw mem_image,
    use i,
    rw [mem_preimage, hi],
    exact ⟨hx, rfl⟩ },
  apply finsupp.eq_zero_of_comap_domain_eq_zero v l,
  apply linear_independent_iff.1 hv,
  rw [finsupp.total_comap_domain, finset.sum_preimage v l.support h_bij (λ (x : β), l x • x)],
  rw [finsupp.total_apply, finsupp.sum] at hl₂,
  apply hl₂
end

lemma linear_independent.of_subtype_range (hv : injective v)
  (h : linear_independent α (λ x, x : range v → β)) : linear_independent α v :=
begin
  rw linear_independent_iff,
  intros l hl,
  apply finsupp.injective_map_domain hv,
  apply linear_independent_subtype.1 h (l.map_domain v),
  { rw finsupp.mem_supported,
    intros x hx,
    have := finset.mem_coe.2 (finsupp.map_domain_support hx),
    rw finset.coe_image at this,
    apply set.image_subset_range _ _ this, },
  { rwa [finsupp.total_map_domain _ _ hv, left_id] }
end

lemma linear_independent.restrict_of_comp_subtype {s : set ι}
  (hs : linear_independent α (v ∘ subtype.val : s → β)) :
  linear_independent α (function.restrict v s) :=
begin
  have h_restrict : restrict v s = v ∘ (λ x, x.val) := rfl,
  rw [linear_independent_iff, h_restrict, finsupp.total_comp],
  intros l hl,
  have h_map_domain_subtype_eq_0 : l.map_domain subtype.val = 0,
  { rw linear_independent_comp_subtype at hs,
    apply hs (finsupp.lmap_domain α α (λ x : subtype s, x.val) l) _ hl,
    rw finsupp.mem_supported,
    simp,
    intros x hx,
    have := finset.mem_coe.2 (finsupp.map_domain_support (finset.mem_coe.1 hx)),
    rw finset.coe_image at this,
    exact subtype.val_image_subset _ _ this },
  apply @finsupp.injective_map_domain _ (subtype s) ι,
  { apply subtype.val_injective },
  { simpa },
end

lemma linear_independent_empty : linear_independent α (λ x, x : (∅ : set β) → β) :=
by simp [linear_independent_subtype_disjoint]

lemma linear_independent.mono {t s : set β} (h : t ⊆ s) :
  linear_independent α (λ x, x : s → β) → linear_independent α (λ x, x : t → β) :=
begin
 simp only [linear_independent_subtype_disjoint],
 exact (disjoint_mono_left (finsupp.supported_mono h))
end

lemma linear_independent_union {s t : set β}
  (hs : linear_independent α (λ x, x : s → β)) (ht : linear_independent α (λ x, x : t → β))
  (hst : disjoint (span α s) (span α t)) :
  linear_independent α (λ x, x : (s ∪ t) → β) :=
begin
  rw [linear_independent_subtype_disjoint, disjoint_def, finsupp.supported_union],
  intros l h₁ h₂, rw mem_sup at h₁,
  rcases h₁ with ⟨ls, hls, lt, hlt, rfl⟩,
  have h_ls_mem_t : finsupp.total β β α id ls ∈ span α t,
  { rw [← image_id t, finsupp.span_eq_map_total],
    apply (add_mem_iff_left (map _ _) (mem_image_of_mem _ hlt)).1,
    rw [← linear_map.map_add, linear_map.mem_ker.1 h₂],
    apply zero_mem },
  have h_lt_mem_s : finsupp.total β β α id lt ∈ span α s,
  { rw [← image_id s, finsupp.span_eq_map_total],
    apply (add_mem_iff_left (map _ _) (mem_image_of_mem _ hls)).1,
    rw [← linear_map.map_add, add_comm, linear_map.mem_ker.1 h₂],
    apply zero_mem },
  have h_ls_mem_s : (finsupp.total β β α id) ls ∈ span α s,
  { rw ← image_id s,
    apply (finsupp.mem_span_iff_total _).2 ⟨ls, hls, rfl⟩ },
  have h_lt_mem_t : (finsupp.total β β α id) lt ∈ span α t,
  { rw ← image_id t,
    apply (finsupp.mem_span_iff_total _).2 ⟨lt, hlt, rfl⟩ },
  have h_ls_0 : ls = 0 :=
    disjoint_def.1 (linear_independent_subtype_disjoint.1 hs) _ hls
    (linear_map.mem_ker.2 $ disjoint_def.1 hst (finsupp.total β β α id ls) h_ls_mem_s h_ls_mem_t),
  have h_lt_0 : lt = 0 :=
    disjoint_def.1 (linear_independent_subtype_disjoint.1 ht) _ hlt
    (linear_map.mem_ker.2 $ disjoint_def.1 hst (finsupp.total β β α id lt) h_lt_mem_s h_lt_mem_t),
  show ls + lt = 0,
    by simp [h_ls_0, h_lt_0],
end

lemma linear_independent_of_finite (s : set β)
  (H : ∀ t ⊆ s, finite t → linear_independent α (λ x, x : t → β)) :
  linear_independent α (λ x, x : s → β) :=
linear_independent_subtype.2 $
  λ l hl, linear_independent_subtype.1 (H _ hl (finset.finite_to_set _)) l (subset.refl _)

lemma linear_independent_Union_of_directed {η : Type*}
  {s : η → set β} (hs : directed (⊆) s)
  (h : ∀ i, linear_independent α (λ x, x : s i → β)) :
  linear_independent α (λ x, x : (⋃ i, s i) → β) :=
begin
  haveI := classical.dec (nonempty η),
  by_cases hη : nonempty η,
  { refine linear_independent_of_finite (⋃ i, s i) (λ t ht ft, _),
    rcases finite_subset_Union ft ht with ⟨I, fi, hI⟩,
    rcases hs.finset_le hη fi.to_finset with ⟨i, hi⟩,
    exact (h i).mono (subset.trans hI $ bUnion_subset $
      λ j hj, hi j (finite.mem_to_finset.2 hj)) },
  { refine linear_independent_empty.mono _,
    rintro _ ⟨_, ⟨i, _⟩, _⟩, exact hη ⟨i⟩ }
end

lemma linear_independent_sUnion_of_directed {s : set (set β)}
  (hs : directed_on (⊆) s)
  (h : ∀ a ∈ s, linear_independent α (λ x, x : (a : set β) → β)) :
  linear_independent α (λ x, x : (⋃₀ s) → β) :=
by rw sUnion_eq_Union; exact
linear_independent_Union_of_directed
  ((directed_on_iff_directed _).1 hs) (by simpa using h)

lemma linear_independent_bUnion_of_directed {η} {s : set η} {t : η → set β}
  (hs : directed_on (t ⁻¹'o (⊆)) s) (h : ∀a∈s, linear_independent α (λ x, x : t a → β)) :
  linear_independent α (λ x, x : (⋃a∈s, t a) → β) :=
by rw bUnion_eq_Union; exact
linear_independent_Union_of_directed
  ((directed_comp _ _ _).2 $ (directed_on_iff_directed _).1 hs)
  (by simpa using h)

lemma linear_independent_Union_finite_subtype {ι : Type*} {f : ι → set β}
  (hl : ∀i, linear_independent α (λ x, x : f i → β))
  (hd : ∀i, ∀t:set ι, finite t → i ∉ t → disjoint (span α (f i)) (⨆i∈t, span α (f i))) :
  linear_independent α (λ x, x : (⋃i, f i) → β) :=
begin
  classical,
  rw [Union_eq_Union_finset f],
  apply linear_independent_Union_of_directed,
  apply directed_of_sup,
  exact (assume t₁ t₂ ht, Union_subset_Union $ assume i, Union_subset_Union_const $ assume h, ht h),
  assume t, rw [set.Union, ← finset.sup_eq_supr],
  refine t.induction_on _ _,
  { rw finset.sup_empty,
    apply linear_independent_empty_type (not_nonempty_iff_imp_false.2 _),
    exact λ x, set.not_mem_empty x (subtype.mem x) },
  { rintros ⟨i⟩ s his ih,
    rw [finset.sup_insert],
    apply linear_independent_union,
    { apply hl },
    { apply ih },
    rw [finset.sup_eq_supr],
    refine disjoint_mono (le_refl _) _ (hd i _ _ his),
    { simp only [(span_Union _).symm],
      refine span_mono (@supr_le_supr2 (set β) _ _ _ _ _ _),
      rintros ⟨i⟩, exact ⟨i, le_refl _⟩ },
    { change finite (plift.up ⁻¹' s.to_set),
      exact finite_preimage (inj_on_of_injective _ (assume i j, plift.up.inj))
        s.finite_to_set } }
end

lemma linear_independent_Union_finite {η : Type*} {ιs : η → Type*}
  [decidable_eq η] [∀ j, decidable_eq (ιs j)]
  {f : Π j : η, ιs j → β}
  (hindep : ∀j, linear_independent α (f j))
  (hd : ∀i, ∀t:set η, finite t → i ∉ t →
      disjoint (span α (range (f i))) (⨆i∈t, span α (range (f i)))) :
  linear_independent α (λ ji : Σ j, ιs j, f ji.1 ji.2) :=
begin
  by_cases zero_eq_one : (0 : α) = 1,
  { apply linear_independent_of_zero_eq_one zero_eq_one },
  apply linear_independent.of_subtype_range,
  { rintros ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy,
    by_cases h_cases : x₁ = y₁,
    subst h_cases,
    { apply sigma.eq,
      rw linear_independent.injective zero_eq_one (hindep _) hxy,
      refl },
    { have h0 : f x₁ x₂ = 0,
      { apply disjoint_def.1 (hd x₁ {y₁} (finite_singleton y₁)
          (λ h, h_cases (eq_of_mem_singleton h))) (f x₁ x₂) (subset_span (mem_range_self _)),
        rw supr_singleton,
        simp only [] at hxy,
        rw hxy,
        exact (subset_span (mem_range_self y₂)) },
      exact false.elim (ne_zero_of_linear_independent zero_eq_one (hindep x₁) h0) } },
  rw range_sigma_eq_Union_range,
  apply linear_independent_Union_finite_subtype (λ j, (hindep j).to_subtype_range) hd,
end

end subtype

section repr
variables (hv : linear_independent α v)

def linear_independent.total_equiv (hv : linear_independent α v) : (ι →₀ α) ≃ₗ[α] span α (range v) :=
begin
apply linear_equiv.of_bijective (linear_map.cod_restrict (span α (range v)) (finsupp.total ι β α v) _),
{ rw linear_map.ker_cod_restrict,
  apply hv },
{ rw [linear_map.range, linear_map.map_cod_restrict, ← linear_map.range_le_iff_comap,
  range_subtype, map_top],
  rw finsupp.range_total,
  apply le_refl (span α (range v)) },
{ intro l,
  rw ← finsupp.range_total,
  rw linear_map.mem_range,
  apply mem_range_self l }
end

def linear_independent.repr (hv : linear_independent α v) :
  span α (range v) →ₗ[α] ι →₀ α := hv.total_equiv.symm

lemma linear_independent.total_repr (x) : finsupp.total ι β α v (hv.repr x) = x :=
subtype.coe_ext.1 (linear_equiv.apply_symm_apply hv.total_equiv x)

lemma linear_independent.total_comp_repr : (finsupp.total ι β α v).comp hv.repr = submodule.subtype _ :=
linear_map.ext $ hv.total_repr

lemma linear_independent.repr_ker : hv.repr.ker = ⊥ :=
by rw [linear_independent.repr, linear_equiv.ker]

lemma linear_independent.repr_range : hv.repr.range = ⊤ :=
by rw [linear_independent.repr, linear_equiv.range]

lemma linear_independent.repr_eq
  {l : ι →₀ α} {x} (eq : finsupp.total ι β α v l = ↑x) :
  hv.repr x = l :=
begin
  have : ↑((linear_independent.total_equiv hv : (ι →₀ α) →ₗ[α] span α (range v)) l)
      = finsupp.total ι β α v l := rfl,
  have : (linear_independent.total_equiv hv : (ι →₀ α) →ₗ[α] span α (range v)) l = x,
  { rw eq at this,
    exact subtype.coe_ext.2 this },
  rw ←linear_equiv.symm_apply_apply hv.total_equiv l,
  rw ←this,
  refl,
end

lemma linear_independent.repr_eq_single (i) (x) (hx : ↑x = v i) :
  hv.repr x = finsupp.single i 1 :=
begin
  apply hv.repr_eq,
  simp [finsupp.total_single, hx]
end

lemma linear_independent_iff_not_smul_mem_span :
  linear_independent α v ↔ (∀ (i : ι) (a : α), a • (v i) ∈ span α (v '' (univ \ {i})) → a = 0) :=
⟨ λ hv i a ha, begin
  rw [finsupp.span_eq_map_total, mem_map] at ha,
  rcases ha with ⟨l, hl, e⟩,
  rw sub_eq_zero.1 (linear_independent_iff.1 hv (l - finsupp.single i a) (by simp [e])) at hl,
  by_contra hn,
  exact (not_mem_of_mem_diff (hl $ by simp [hn])) (mem_singleton _),
end, λ H, linear_independent_iff.2 $ λ l hl, begin
  ext i, simp,
  by_contra hn,
  refine hn (H i _ _),
  refine (finsupp.mem_span_iff_total _).2 ⟨finsupp.single i (l i) - l, _, _⟩,
  { rw finsupp.mem_supported',
    intros j hj,
    have hij : j = i :=
      classical.not_not.1
          (λ hij : j ≠ i, hj ((mem_diff _).2 ⟨mem_univ _, λ h, hij (eq_of_mem_singleton h)⟩)),
    simp [hij] },
  { simp [hl] }
end⟩

end repr

lemma surjective_of_linear_independent_of_span
  (hv : linear_independent α v) (f : ι' ↪ ι)
  (hss : range v ⊆ span α (range (v ∘ f))) (zero_ne_one : 0 ≠ (1 : α)):
  surjective f :=
begin
  intros i,
  let repr : (span α (range (v ∘ f)) : Type*) → ι' →₀ α := (hv.comp f f.inj).repr,
  let l := (repr ⟨v i, hss (mem_range_self i)⟩).map_domain f,
  have h_total_l : finsupp.total ι β α v l = v i,
  { dsimp only [l],
    rw finsupp.total_map_domain,
    rw (hv.comp f f.inj).total_repr,
    { refl },
    { exact f.inj } },
  have h_total_eq : (finsupp.total ι β α v) l = (finsupp.total ι β α v) (finsupp.single i 1),
    by rw [h_total_l, finsupp.total_single, one_smul],
  have l_eq : l = _ := linear_map.ker_eq_bot.1 hv h_total_eq,
  dsimp only [l] at l_eq,
  rw ←finsupp.emb_domain_eq_map_domain at l_eq,
  rcases finsupp.single_of_emb_domain_single (repr ⟨v i, _⟩) f i (1 : α) zero_ne_one.symm l_eq with ⟨i', hi'⟩,
  use i',
  exact hi'.2
end

lemma eq_of_linear_independent_of_span_subtype {s t : set β} (zero_ne_one : (0 : α) ≠ 1)
  (hs : linear_independent α (λ x, x : s → β)) (h : t ⊆ s) (hst : s ⊆ span α t) : s = t :=
begin
  let f : t ↪ s := ⟨λ x, ⟨x.1, h x.2⟩, λ a b hab, subtype.val_injective (subtype.mk.inj hab)⟩,
  have h_surj : surjective f,
  { apply surjective_of_linear_independent_of_span hs f _ zero_ne_one,
    convert hst; simp [f, comp], },
  show s = t,
  { apply subset.antisymm _ h,
    intros x hx,
    rcases h_surj ⟨x, hx⟩ with ⟨y, hy⟩,
    convert y.mem,
    rw ← subtype.mk.inj hy,
    refl }
end

open linear_map

lemma linear_independent.image (hv : linear_independent α v) {f : β →ₗ γ}
  (hf_inj : disjoint (span α (range v)) f.ker) : linear_independent α (f ∘ v) :=
begin
  rw [disjoint, ← set.image_univ, finsupp.span_eq_map_total, map_inf_eq_map_inf_comap,
    map_le_iff_le_comap, comap_bot, finsupp.supported_univ, top_inf_eq] at hf_inj,
  unfold linear_independent at hv,
  rw hv at hf_inj,
  haveI : inhabited β := ⟨0⟩,
  rw [linear_independent, finsupp.total_comp],
  rw [@finsupp.lmap_domain_total _ _ α _ _ _ _ _ _ _ _ _ _ f, ker_comp, eq_bot_iff],
  apply hf_inj,
  exact λ _, rfl,
end

lemma linear_independent.image_subtype {s : set β} {f : β →ₗ γ} (hs : linear_independent α (λ x, x : s → β))
  (hf_inj : disjoint (span α s) f.ker) : linear_independent α (λ x, x : f '' s → γ) :=
begin
  rw [disjoint, ← set.image_id s, finsupp.span_eq_map_total, map_inf_eq_map_inf_comap,
    map_le_iff_le_comap, comap_bot] at hf_inj,
  haveI : inhabited β := ⟨0⟩,
  rw [linear_independent_subtype_disjoint, disjoint, ← finsupp.lmap_domain_supported _ _ f, map_inf_eq_map_inf_comap,
      map_le_iff_le_comap, ← ker_comp],
  rw [@finsupp.lmap_domain_total _ _ α _ _ _, ker_comp],
  { exact le_trans (le_inf inf_le_left hf_inj) (le_trans (linear_independent_subtype_disjoint.1 hs) bot_le) },
  { simp }
end

lemma linear_independent_inl_union_inr {s : set β} {t : set γ}
  (hs : linear_independent α (λ x, x : s → β))
  (ht : linear_independent α (λ x, x : t → γ)) :
  linear_independent α (λ x, x : inl α β γ '' s ∪ inr α β γ '' t → β × γ) :=
begin
  apply linear_independent_union,
  exact (hs.image_subtype $ by simp),
  exact (ht.image_subtype $ by simp),
  rw [span_image, span_image];
    simp [disjoint_iff, prod_inf_prod]
end

lemma linear_independent_inl_union_inr' {v : ι → β} {v' : ι' → γ}
  (hv : linear_independent α v) (hv' : linear_independent α v') :
  linear_independent α (sum.elim (inl α β γ ∘ v) (inr α β γ ∘ v')) :=
begin
  by_cases zero_eq_one : (0 : α) = 1,
  { apply linear_independent_of_zero_eq_one zero_eq_one },
  have inj_v : injective v := (linear_independent.injective zero_eq_one hv),
  have inj_v' : injective v' := (linear_independent.injective zero_eq_one hv'),
  apply linear_independent.of_subtype_range,
  { apply sum.elim_injective,
    { exact injective_comp prod.injective_inl inj_v },
    { exact injective_comp prod.injective_inr inj_v' },
    { intros, simp [ne_zero_of_linear_independent zero_eq_one hv] } },
  { rw sum.elim_range,
    apply linear_independent_union,
    { apply linear_independent.to_subtype_range,
      apply linear_independent.image hv,
      simp [ker_inl] },
    { apply linear_independent.to_subtype_range,
      apply linear_independent.image hv',
      simp [ker_inr] },
    { apply disjoint_mono _ _ disjoint_inl_inr,
      { rw [set.range_comp, span_image],
        apply linear_map.map_le_range },
      { rw [set.range_comp, span_image],
        apply linear_map.map_le_range } } }
end

lemma le_of_span_le_span {s t u: set β} (zero_ne_one : (0 : α) ≠ 1)
  (hl : linear_independent α (subtype.val : u → β )) (hsu : s ⊆ u) (htu : t ⊆ u)
  (hst : span α s ≤ span α t) : s ⊆ t :=
begin
  have := eq_of_linear_independent_of_span_subtype zero_ne_one
    (hl.mono (set.union_subset hsu htu))
    (set.subset_union_right _ _)
    (set.union_subset (set.subset.trans subset_span hst) subset_span),
  rw ← this, apply set.subset_union_left
end

lemma span_le_span_iff {s t u: set β} (zero_ne_one : (0 : α) ≠ 1)
  (hl : linear_independent α (subtype.val : u → β )) (hsu : s ⊆ u) (htu : t ⊆ u) :
  span α s ≤ span α t ↔ s ⊆ t :=
⟨le_of_span_le_span zero_ne_one hl hsu htu, span_mono⟩

variables (α) (v)
/-- A set of vectors is a basis if it is linearly independent and all vectors are in the span α. -/
def is_basis := linear_independent α v ∧ span α (range v) = ⊤
variables {α} {v}

section is_basis
variables {s t : set β} (hv : is_basis α v)

lemma is_basis.mem_span (hv : is_basis α v) : ∀ x, x ∈ span α (range v) := eq_top_iff'.1 hv.2

lemma is_basis.comp (hv : is_basis α v) (f : ι' → ι) (hf : bijective f) :
  is_basis α (v ∘ f) :=
begin
  split,
  { apply hv.1.comp f hf.1 },
  { rw[set.range_comp, range_iff_surjective.2 hf.2, image_univ, hv.2] }
end

lemma is_basis.injective (hv : is_basis α v) (zero_ne_one : (0 : α) ≠ 1) : injective v :=
  λ x y h, linear_independent.injective zero_ne_one hv.1 h

def is_basis.repr : β →ₗ (ι →₀ α) :=
(hv.1.repr).comp (linear_map.id.cod_restrict _ hv.mem_span)

lemma is_basis.total_repr (x) : finsupp.total ι β α v (hv.repr x) = x :=
hv.1.total_repr ⟨x, _⟩

lemma is_basis.total_comp_repr : (finsupp.total ι β α v).comp hv.repr = linear_map.id :=
linear_map.ext hv.total_repr

lemma is_basis.repr_ker : hv.repr.ker = ⊥ :=
linear_map.ker_eq_bot.2 $ injective_of_left_inverse hv.total_repr

lemma is_basis.repr_range : hv.repr.range = finsupp.supported α α univ :=
by rw [is_basis.repr, linear_map.range, submodule.map_comp,
  linear_map.map_cod_restrict, submodule.map_id, comap_top, map_top, hv.1.repr_range,
  finsupp.supported_univ]

lemma is_basis.repr_total (x : ι →₀ α) (hx : x ∈ finsupp.supported α α (univ : set ι)) :
  hv.repr (finsupp.total ι β α v x) = x :=
begin
  rw [← hv.repr_range, linear_map.mem_range] at hx,
  cases hx with w hw,
  rw [← hw, hv.total_repr],
end

lemma is_basis.repr_eq_single {i} : hv.repr (v i) = finsupp.single i 1 :=
by apply hv.1.repr_eq_single; simp

/-- Construct a linear map given the value at the basis. -/
def is_basis.constr (f : ι → γ) : β →ₗ[α] γ :=
(finsupp.total γ γ α id).comp $ (finsupp.lmap_domain α α f).comp hv.repr

theorem is_basis.constr_apply (f : ι → γ) (x : β) :
  (hv.constr f : β → γ) x = (hv.repr x).sum (λb a, a • f b) :=
by dsimp [is_basis.constr];
   rw [finsupp.total_apply, finsupp.sum_map_domain_index]; simp [add_smul]

lemma is_basis.ext {f g : β →ₗ[α] γ} (hv : is_basis α v) (h : ∀i, f (v i) = g (v i)) : f = g :=
begin
  apply linear_map.ext (λ x, linear_eq_on (range v) _ (hv.mem_span x)),
  exact (λ y hy, exists.elim (set.mem_range.1 hy) (λ i hi, by rw ←hi; exact h i))
end

lemma constr_basis {f : ι → γ} {i : ι} (hv : is_basis α v) :
  (hv.constr f : β → γ) (v i) = f i :=
by simp [is_basis.constr_apply, hv.repr_eq_single, finsupp.sum_single_index]

lemma constr_eq {g : ι → γ} {f : β →ₗ[α] γ} (hv : is_basis α v)
  (h : ∀i, g i = f (v i)) : hv.constr g = f :=
hv.ext $ λ i, (constr_basis hv).trans (h i)

lemma constr_self (f : β →ₗ[α] γ) : hv.constr (λ i, f (v i)) = f :=
constr_eq hv $ λ x, rfl

lemma constr_zero (hv : is_basis α v) : hv.constr (λi, (0 : γ)) = 0 :=
constr_eq hv $ λ x, rfl

lemma constr_add {g f : ι → γ} (hv : is_basis α v) :
  hv.constr (λi, f i + g i) = hv.constr f + hv.constr g :=
constr_eq hv $ by simp [constr_basis hv] {contextual := tt}

lemma constr_neg {f : ι → γ} (hv : is_basis α v) : hv.constr (λi, - f i) = - hv.constr f :=
constr_eq hv $ by simp [constr_basis hv] {contextual := tt}

lemma constr_sub {g f : ι → γ} (hs : is_basis α v) :
  hv.constr (λi, f i - g i) = hs.constr f - hs.constr g :=
by simp [constr_add, constr_neg]

-- this only works on functions if `α` is a commutative ring
lemma constr_smul {ι α β γ} [decidable_eq ι] [decidable_eq α] [decidable_eq β] [decidable_eq γ] [comm_ring α]
  [add_comm_group β] [add_comm_group γ] [module α β] [module α γ]
  {v : ι → α} {f : ι → γ} {a : α} (hv : is_basis α v) {b : β} :
  hv.constr (λb, a • f b) = a • hv.constr f :=
constr_eq hv $ by simp [constr_basis hv] {contextual := tt}

lemma constr_range [inhabited ι] (hv : is_basis α v) {f : ι  → γ} :
  (hv.constr f).range = span α (range f) :=
by rw [is_basis.constr, linear_map.range_comp, linear_map.range_comp, is_basis.repr_range,
    finsupp.lmap_domain_supported, ←set.image_univ, ←finsupp.span_eq_map_total, image_id]

def module_equiv_finsupp (hv : is_basis α v) : β ≃ₗ[α] ι →₀ α :=
(hv.1.total_equiv.trans (linear_equiv.of_top _ hv.2)).symm

def equiv_of_is_basis {v : ι → β} {v' : ι' → γ} {f : β → γ} {g : γ → β}
  (hv : is_basis α v) (hv' : is_basis α v') (hf : ∀i, f (v i) ∈ range v') (hg : ∀i, g (v' i) ∈ range v)
  (hgf : ∀i, g (f (v i)) = v i) (hfg : ∀i, f (g (v' i)) = v' i) :
  β ≃ₗ γ :=
{ inv_fun := hv'.constr (g ∘ v'),
  left_inv :=
    have (hv'.constr (g ∘ v')).comp (hv.constr (f ∘ v)) = linear_map.id,
    from hv.ext $ λ i, exists.elim (hf i) (λ i' hi', by simp [constr_basis, hi'.symm]; rw [hi', hgf]),
    λ x, congr_arg (λ h:β →ₗ[α] β, h x) this,
  right_inv :=
    have (hv.constr (f ∘ v)).comp (hv'.constr (g ∘ v')) = linear_map.id,
    from hv'.ext $ λ i', exists.elim (hg i') (λ i hi, by simp [constr_basis, hi.symm]; rw [hi, hfg]),
    λ y, congr_arg (λ h:γ →ₗ[α] γ, h y) this,
  ..hv.constr (f ∘ v) }

lemma is_basis_inl_union_inr {v : ι → β} {v' : ι' → γ}
  (hv : is_basis α v) (hv' : is_basis α v') : is_basis α (sum.elim (inl α β γ ∘ v) (inr α β γ ∘ v')) :=
begin
  split,
  apply linear_independent_inl_union_inr' hv.1 hv'.1,
  rw [sum.elim_range, span_union,
      set.range_comp, span_image (inl α β γ), hv.2,  map_top,
      set.range_comp, span_image (inr α β γ), hv'.2, map_top],
  exact linear_map.sup_range_inl_inr
end

end is_basis

lemma is_basis_singleton_one (α : Type*) [unique ι] [decidable_eq α] [ring α] :
  is_basis α (λ (_ : ι), (1 : α)) :=
begin
  split,
  { refine linear_independent_iff.2 (λ l, _),
    rw [finsupp.unique_single l, finsupp.total_single, smul_eq_mul, mul_one],
    intro hi,
    simp [hi] },
  { refine top_unique (λ _ _, _),
    simp [submodule.mem_span_singleton] }
end

lemma linear_equiv.is_basis (hs : is_basis α v)
  (f : β ≃ₗ[α] γ) : is_basis α (f ∘ v) :=
begin
  split,
  { apply @linear_independent.image _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs.1 (f : β →ₗ[α] γ),
    simp [linear_equiv.ker f] },
  { rw set.range_comp,
    have : span α ((f : β →ₗ[α] γ) '' range v) = ⊤,
    { rw [span_image (f : β →ₗ[α] γ), hs.2],
      simp },
    exact this }
end

lemma is_basis_span (hs : linear_independent α v) :
  @is_basis ι α (span α (range v)) (λ i : ι, ⟨v i, subset_span (mem_range_self _)⟩) _ _ _ _ _ _ :=
begin
split,
{ apply linear_independent_span hs },
{ rw eq_top_iff',
  intro x,
  have h₁ : subtype.val '' set.range (λ i, subtype.mk (v i) _) = range v,
    by rw ←set.range_comp,
  have h₂ : map (submodule.subtype _) (span α (set.range (λ i, subtype.mk (v i) _)))
              = span α (range v),
    by rw [←span_image, submodule.subtype_eq_val, h₁],
  have h₃ : (x : β) ∈ map (submodule.subtype _) (span α (set.range (λ i, subtype.mk (v i) _))),
    by rw h₂; apply subtype.mem x,
  rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩,
  have h_x_eq_y : x = y,
    by rw [subtype.coe_ext, ← hy₂]; simp,
  rw h_x_eq_y,
  exact hy₁ }
end

lemma is_basis_empty (h_empty : ¬ nonempty ι) (h : ∀x:β, x = 0) : is_basis α (λ x : ι, (0 : β)) :=
⟨ linear_independent_empty_type h_empty,
  eq_top_iff'.2 $ assume x, (h x).symm ▸ submodule.zero_mem _ ⟩

lemma is_basis_empty_bot (h_empty : ¬ nonempty ι) : is_basis α (λ _ : ι, (0 : (⊥ : submodule α β))) :=
begin
  apply is_basis_empty h_empty,
  intro x,
  apply subtype.ext.2,
  exact (submodule.mem_bot α).1 (subtype.mem x),
end

open fintype
variables [fintype ι] (h : is_basis α v)

/-- A module over α with a finite basis is linearly equivalent to functions from its basis to α. -/
def equiv_fun_basis  : β ≃ₗ[α] (ι → α) :=
linear_equiv.trans (module_equiv_finsupp h)
  { to_fun := finsupp.to_fun,
    add := λ x y, by ext; exact finsupp.add_apply,
    smul := λ x y, by ext; exact finsupp.smul_apply,
    ..finsupp.equiv_fun_on_fintype }

theorem module.card_fintype [fintype α] [fintype β] :
  card β = (card α) ^ (card ι) :=
calc card β = card (ι → α)    : card_congr (equiv_fun_basis h).to_equiv
        ... = card α ^ card ι : card_fun

end module

section vector_space
variables [discrete_field α] [add_comm_group β] [add_comm_group γ]
  [vector_space α β] [vector_space α γ] {s t : set β} {x y z : β}
include α
open submodule

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
   (instead of a data containing type class) -/

section
set_option class.instance_max_depth 36

lemma mem_span_insert_exchange : x ∈ span α (insert y s) → x ∉ span α s → y ∈ span α (insert x s) :=
begin
  simp [mem_span_insert],
  rintro a z hz rfl h,
  refine ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, _⟩,
  have a0 : a ≠ 0, {rintro rfl, simp * at *},
  simp [a0, smul_add, smul_smul]
end

end

lemma linear_independent_iff_not_mem_span : linear_independent α v ↔ (∀i, v i ∉ span α (v '' (univ \ {i}))) :=
begin
  apply linear_independent_iff_not_smul_mem_span.trans,
  split,
  { intros h i h_in_span,
    apply one_ne_zero (h i 1 (by simp [h_in_span])) },
  { intros h i a ha,
    by_contradiction ha',
    exact false.elim (h _ ((smul_mem_iff _ ha').1 ha)) }
end

lemma linear_independent_unique [unique ι] (h : v (default ι) ≠ 0): linear_independent α v :=
begin
  rw linear_independent_iff,
  intros l hl,
  ext i,
  rw [unique.eq_default i, finsupp.zero_apply],
  by_contra hc,
  have := smul_smul _ (l (default ι))⁻¹ (l (default ι)) (v (default ι)),
  rw [finsupp.unique_single l, finsupp.total_single] at hl,
  rw [hl, inv_mul_cancel hc, smul_zero, one_smul] at this,
  exact h this.symm
end

lemma linear_independent_singleton {x : β} (hx : x ≠ 0) : linear_independent α (λ x, x : ({x} : set β) → β) :=
begin
  apply @linear_independent_unique _ _ _ _ _ _ _ _ _ _ _ _,
  apply set.unique_singleton,
  apply hx,
end

lemma disjoint_span_singleton {p : submodule α β} {x : β} (x0 : x ≠ 0) :
  disjoint p (span α {x}) ↔ x ∉ p :=
⟨λ H xp, x0 (disjoint_def.1 H _ xp (singleton_subset_iff.1 subset_span:_)),
begin
  simp [disjoint_def, mem_span_singleton],
  rintro xp y yp a rfl,
  by_cases a0 : a = 0, {simp [a0]},
  exact xp.elim ((smul_mem_iff p a0).1 yp),
end⟩

lemma linear_independent.insert (hs : linear_independent α (λ b, b : s → β)) (hx : x ∉ span α s) :
  linear_independent α (λ b, b : insert x s → β) :=
begin
  rw ← union_singleton,
  have x0 : x ≠ 0 := mt (by rintro rfl; apply zero_mem _) hx,
  apply linear_independent_union hs (linear_independent_singleton x0),
  rwa [disjoint_span_singleton x0],
  exact classical.dec_eq α
end

lemma exists_linear_independent (hs : linear_independent α (λ x, x : s → β)) (hst : s ⊆ t) :
  ∃b⊆t, s ⊆ b ∧ t ⊆ span α b ∧ linear_independent α (λ x, x : b → β) :=
begin
  rcases zorn.zorn_subset₀ {b | b ⊆ t ∧ linear_independent α (λ x, x : b → β)} _ _
    ⟨hst, hs⟩ with ⟨b, ⟨bt, bi⟩, sb, h⟩,
  { refine ⟨b, bt, sb, λ x xt, _, bi⟩,
    haveI := classical.dec (x ∈ span α b),
    by_contra hn,
    apply hn,
    rw ← h _ ⟨insert_subset.2 ⟨xt, bt⟩, bi.insert hn⟩ (subset_insert _ _),
    exact subset_span (mem_insert _ _) },
  { refine λ c hc cc c0, ⟨⋃₀ c, ⟨_, _⟩, λ x, _⟩,
    { exact sUnion_subset (λ x xc, (hc xc).1) },
    { exact linear_independent_sUnion_of_directed cc.directed_on (λ x xc, (hc xc).2) },
    { exact subset_sUnion_of_mem } }
end

lemma exists_subset_is_basis (hs : linear_independent α (λ x, x : s → β)) :
  ∃b, s ⊆ b ∧ is_basis α (λ i : b, i.val) :=
let ⟨b, hb₀, hx, hb₂, hb₃⟩ := exists_linear_independent hs (@subset_univ _ _) in
⟨ b, hx,
  @linear_independent.restrict_of_comp_subtype _ _ _ id _ _ _ _ _ _ _ hb₃,
  by simp; exact eq_top_iff.2 hb₂⟩

variables (α β)
lemma exists_is_basis : ∃b : set β, is_basis α (λ i : b, i.val) :=
let ⟨b, _, hb⟩ := exists_subset_is_basis linear_independent_empty in ⟨b, hb⟩

variables {α β}

-- TODO(Mario): rewrite?
lemma exists_of_linear_independent_of_finite_span {t : finset β}
  (hs : linear_independent α (λ x, x : s → β)) (hst : s ⊆ (span α ↑t : submodule α β)) :
  ∃t':finset β, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = t.card :=
have ∀t, ∀(s' : finset β), ↑s' ⊆ s → s ∩ ↑t = ∅ → s ⊆ (span α ↑(s' ∪ t) : submodule α β) →
  ∃t':finset β, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = (s' ∪ t).card :=
assume t, finset.induction_on t
  (assume s' hs' _ hss',
    have s = ↑s',
      from eq_of_linear_independent_of_span_subtype (@zero_ne_one α _) hs hs' $
          by simpa using hss',
    ⟨s', by simp [this]⟩)
  (assume b₁ t hb₁t ih s' hs' hst hss',
    have hb₁s : b₁ ∉ s,
      from assume h,
      have b₁ ∈ s ∩ ↑(insert b₁ t), from ⟨h, finset.mem_insert_self _ _⟩,
      by rwa [hst] at this,
    have hb₁s' : b₁ ∉ s', from assume h, hb₁s $ hs' h,
    have hst : s ∩ ↑t = ∅,
      from eq_empty_of_subset_empty $ subset.trans
        (by simp [inter_subset_inter, subset.refl]) (le_of_eq hst),
    classical.by_cases
      (assume : s ⊆ (span α ↑(s' ∪ t) : submodule α β),
        let ⟨u, hust, hsu, eq⟩ := ih _ hs' hst this in
        have hb₁u : b₁ ∉ u, from assume h, (hust h).elim hb₁s hb₁t,
        ⟨insert b₁ u, by simp [insert_subset_insert hust],
          subset.trans hsu (by simp), by simp [eq, hb₁t, hb₁s', hb₁u]⟩)
      (assume : ¬ s ⊆ (span α ↑(s' ∪ t) : submodule α β),
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this in
        have hb₂t' : b₂ ∉ s' ∪ t, from assume h, hb₂t $ subset_span h,
        have s ⊆ (span α ↑(insert b₂ s' ∪ t) : submodule α β), from
          assume b₃ hb₃,
          have ↑(s' ∪ insert b₁ t) ⊆ insert b₁ (insert b₂ ↑(s' ∪ t) : set β),
            by simp [insert_eq, -singleton_union, -union_singleton, union_subset_union, subset.refl, subset_union_right],
          have hb₃ : b₃ ∈ span α (insert b₁ (insert b₂ ↑(s' ∪ t) : set β)),
            from span_mono this (hss' hb₃),
          have s ⊆ (span α (insert b₁ ↑(s' ∪ t)) : submodule α β),
            by simpa [insert_eq, -singleton_union, -union_singleton] using hss',
          have hb₁ : b₁ ∈ span α (insert b₂ ↑(s' ∪ t)),
            from mem_span_insert_exchange (this hb₂s) hb₂t,
          by rw [span_insert_eq_span hb₁] at hb₃; simpa using hb₃,
        let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [insert_subset, hb₂s, hs']) hst this in
        ⟨u, subset.trans hust $ union_subset_union (subset.refl _) (by simp [subset_insert]),
          hsu, by rw [finset.union_comm] at hb₂t'; simp [eq, hb₂t', hb₁t, hb₁s']⟩)),
begin
  letI := classical.dec_pred (λx, x ∈ s),
  have eq : t.filter (λx, x ∈ s) ∪ t.filter (λx, x ∉ s) = t,
  { apply finset.ext.mpr,
    intro x,
    by_cases x ∈ s; simp *, finish },
  apply exists.elim (this (t.filter (λx, x ∉ s)) (t.filter (λx, x ∈ s))
    (by simp [set.subset_def]) (by simp [set.ext_iff] {contextual := tt}) (by rwa [eq])),
  intros u h,
  exact ⟨u, subset.trans h.1 (by simp [subset_def, and_imp, or_imp_distrib] {contextual:=tt}),
    h.2.1, by simp only [h.2.2, eq]⟩
end

lemma exists_finite_card_le_of_finite_of_linear_independent_of_span
  (ht : finite t) (hs : linear_independent α (λ x, x : s → β)) (hst : s ⊆ span α t) :
  ∃h : finite s, h.to_finset.card ≤ ht.to_finset.card :=
have s ⊆ (span α ↑(ht.to_finset) : submodule α β), by simp; assumption,
let ⟨u, hust, hsu, eq⟩ := exists_of_linear_independent_of_finite_span hs this in
have finite s, from finite_subset u.finite_to_set hsu,
⟨this, by rw [←eq]; exact (finset.card_le_of_subset $ finset.coe_subset.mp $ by simp [hsu])⟩

lemma exists_left_inverse_linear_map_of_injective {f : β →ₗ[α] γ}
  (hf_inj : f.ker = ⊥) : ∃g:γ →ₗ β, g.comp f = linear_map.id :=
begin
  rcases exists_is_basis α β with ⟨B, hB⟩,
  have hB₀ : _ := hB.1.to_subtype_range,
  have : linear_independent α (λ x, x : f '' B → γ),
  { have h₁ := hB₀.image_subtype (show disjoint (span α (range (λ i : B, i.val))) (linear_map.ker f), by simp [hf_inj]),
    have h₂ : range (λ (i : B), i.val) = B := subtype.range_val B,
    rwa h₂ at h₁ },
  rcases exists_subset_is_basis this with ⟨C, BC, hC⟩,
  haveI : inhabited β := ⟨0⟩,
  use hC.constr (function.restrict (inv_fun f) C : C → β),
  apply @is_basis.ext _ _ _ _ _ _ _ _ (show decidable_eq β, by assumption) _ _ _ _ _ _ _ hB,
  intros b,
  rw image_subset_iff at BC,
  simp,
  have := BC (subtype.mem b),
  rw mem_preimage at this,
  have : f (b.val) = (subtype.mk (f ↑b) (begin rw ←mem_preimage, exact BC (subtype.mem b) end) : C).val,
    by simp; unfold_coes,
  rw this,
  rw [constr_basis hC],
  exact left_inverse_inv_fun (linear_map.ker_eq_bot.1 hf_inj) _,
end

lemma exists_right_inverse_linear_map_of_surjective {f : β →ₗ[α] γ}
  (hf_surj : f.range = ⊤) : ∃g:γ →ₗ β, f.comp g = linear_map.id :=
begin
  rcases exists_is_basis α γ with ⟨C, hC⟩,
  haveI : inhabited β := ⟨0⟩,
  use hC.constr (function.restrict (inv_fun f) C : C → β),
  apply @is_basis.ext _ _ _ _ _ _ _ _ (show decidable_eq γ, by assumption) _ _ _ _ _ _ _ hC,
  intros c,
  simp [constr_basis hC],
  exact right_inverse_inv_fun (linear_map.range_eq_top.1 hf_surj) _
end

set_option class.instance_max_depth 49
open submodule linear_map
theorem quotient_prod_linear_equiv (p : submodule α β) :
  nonempty ((p.quotient × p) ≃ₗ[α] β) :=
begin
  haveI := classical.dec_eq (quotient p),
  rcases exists_right_inverse_linear_map_of_surjective p.range_mkq with ⟨f, hf⟩,
  have mkf : ∀ x, submodule.quotient.mk (f x) = x := linear_map.ext_iff.1 hf,
  have fp : ∀ x, x - f (p.mkq x) ∈ p :=
    λ x, (submodule.quotient.eq p).1 (mkf (p.mkq x)).symm,
  refine ⟨linear_equiv.of_linear (f.copair p.subtype)
    (p.mkq.pair (cod_restrict p (linear_map.id - f.comp p.mkq) fp))
    (by ext; simp) _⟩,
  ext ⟨⟨x⟩, y, hy⟩; simp,
  { apply (submodule.quotient.eq p).2,
    simpa using sub_mem p hy (fp x) },
  { refine subtype.coe_ext.2 _,
    simp [mkf, (submodule.quotient.mk_eq_zero p).2 hy] }
end

open fintype

theorem vector_space.card_fintype [fintype α] [fintype β] :
  ∃ n : ℕ, card β = (card α) ^ n :=
begin
  apply exists.elim (exists_is_basis α β),
  intros b hb,
  haveI := classical.dec_pred (λ x, x ∈ b),
  use card b,
  exact module.card_fintype hb,
end

end vector_space

namespace pi
open set linear_map

section module
variables {η : Type*} {ιs : η → Type*} {φ : η → Type*}
variables [ring α] [∀i, add_comm_group (φ i)] [∀i, module α (φ i)] [fintype η] [decidable_eq η]

lemma linear_independent_std_basis [∀ j, decidable_eq (ιs j)]  [∀ i, decidable_eq (φ i)]
  (v : Πj, ιs j → (φ j)) (hs : ∀i, linear_independent α (v i)) :
  linear_independent α (λ (ji : Σ j, ιs j), std_basis α φ ji.1 (v ji.1 ji.2)) :=
begin
  have hs' : ∀j : η, linear_independent α (λ i : ιs j, std_basis α φ j (v j i)),
  { intro j,
    apply linear_independent.image (hs j),
    simp [ker_std_basis] },
  apply linear_independent_Union_finite hs',
  { assume j J _ hiJ,
    simp [(set.Union.equations._eqn_1 _).symm, submodule.span_image, submodule.span_Union],
    have h₀ : ∀ j, span α (range (λ (i : ιs j), std_basis α φ j (v j i)))
        ≤ range (std_basis α φ j),
    { intro j,
      rw [span_le, linear_map.range_coe],
      apply range_comp_subset_range },
    have h₁ : span α (range (λ (i : ιs j), std_basis α φ j (v j i)))
        ≤ ⨆ i ∈ {j}, range (std_basis α φ i),
    { rw @supr_singleton _ _ _ (λ i, linear_map.range (std_basis α (λ (j : η), φ j) i)),
      apply h₀ },
    have h₂ : (⨆ j ∈ J, span α (range (λ (i : ιs j), std_basis α φ j (v j i)))) ≤
               ⨆ j ∈ J, range (std_basis α (λ (j : η), φ j) j) :=
      supr_le_supr (λ i, supr_le_supr (λ H, h₀ i)),
    have h₃ : disjoint (λ (i : η), i ∈ {j}) J,
    { convert set.disjoint_singleton_left.2 hiJ,
      rw ←@set_of_mem_eq _ {j},
      refl },
    refine disjoint_mono h₁ h₂
      (disjoint_std_basis_std_basis _ _ _ _ h₃), }
end

lemma is_basis_std_basis [∀ j, decidable_eq (ιs j)] [∀ j, decidable_eq (φ j)]
  (s : Πj, ιs j → (φ j)) (hs : ∀j, is_basis α (s j)) :
  is_basis α (λ (ji : Σ j, ιs j), std_basis α φ ji.1 (s ji.1 ji.2)) :=
begin
  split,
  { apply linear_independent_std_basis _ (assume i, (hs i).1) },
  have h₁ : Union (λ j, set.range (std_basis α φ j ∘ s j))
    ⊆ range (λ (ji : Σ (j : η), ιs j), (std_basis α φ (ji.fst)) (s (ji.fst) (ji.snd))),
  { apply Union_subset, intro i,
    apply range_comp_subset_range (λ x : ιs i, (⟨i, x⟩ : Σ (j : η), ιs j))
        (λ (ji : Σ (j : η), ιs j), std_basis α φ (ji.fst) (s (ji.fst) (ji.snd))) },
  have h₂ : ∀ i, span α (range (std_basis α φ i ∘ s i)) = range (std_basis α φ i),
  { intro i,
    rw [set.range_comp, submodule.span_image, (assume i, (hs i).2), submodule.map_top] },
  apply eq_top_mono,
  apply span_mono h₁,
  rw span_Union,
  simp only [h₂],
  apply supr_range_std_basis
end

section
variables (α ι)

lemma is_basis_fun₀ : is_basis α
    (λ (ji : Σ (j : η), (λ _, unit) j),
       (std_basis α (λ (i : η), α) (ji.fst)) 1) :=
begin
  haveI := classical.dec_eq,
  apply @is_basis_std_basis α _ η (λi:η, unit) (λi:η, α) _ _ _ _ _ _ _ (λ _ _, (1 : α))
      (assume i, @is_basis_singleton_one _ _ _ _ _ _),
end

lemma is_basis_fun : is_basis α (λ i, std_basis α (λi:η, α) i 1) :=
begin
  apply is_basis.comp (is_basis_fun₀ α) (λ i, ⟨i, punit.star⟩),
  { apply bijective_iff_has_inverse.2,
    use (λ x, x.1),
    simp [function.left_inverse, function.right_inverse],
    intros _ b,
    rw [unique.eq_default b, unique.eq_default punit.star] },
end

end

end module

end pi

namespace finsupp

lemma is_basis_finsupp (η : Type*) {ι α β : Type*} [ring α] [add_comm_group β] [module α β]
  [decidable_eq α] [decidable_eq β] [decidable_eq η] [decidable_eq ι]
  {v : ι → β} (hv : is_basis α v) : is_basis α (λ i : η × ι, single i.1 (v i.2)) :=
begin
  have h : ∀ f g, (finsupp.total (η × ι) (η →₀ β) α (λ i, single i.1 (v i.2))) f = g ↔
    ∀ n, (finsupp.total ι β α v) (finsupp.curry f n) = g n,
    { intros f g,
      rw [total_apply],
      conv in (_ • _) { rw [smul_single] },
      rw [←sum_curry_index f (λ (n:η) (i:ι) (a:α), single n (a • v i))],
      { conv_lhs { congr, congr, skip, funext, rw [←single_sum] },
        rw [sum_single_range _ (λ f:ι →₀ α, f.sum (λ (i:ι) (a:α), a • v i)) sum_zero_index, ext_iff],
        split, all_goals { intros h n, replace h := h n, simpa } },
      { intros _ _, dsimp, rw [zero_smul, single_zero] },
      { intros _ _ _ _, dsimp, rw [add_smul, single_add] } },
  split,
  { rw [linear_independent_iff],
    intros f hf,
    ext i,
    rw [h] at hf,
    have : _ = _, from congr_arg (λ g:ι →₀ α, g i.2) (linear_independent_iff.mp hv.1 _ (hf i.1)),
    rwa [curry_apply, prod.mk.eta] at this },
  { rw [submodule.eq_top_iff'],
    intro g,
    rw [←set.image_univ, mem_span_iff_total],
    let f := finsupp.uncurry (map_range hv.repr.to_fun hv.repr.map_zero g),
    have H : f ∈ supported α α set.univ, { rw [supported_univ], exact submodule.mem_top },
    existsi [f, H],
    rw [h],
    intro n,
    rw [show finsupp.curry f = _, from finsupp_prod_equiv.right_inv _, map_range_apply],
    change (linear_map.comp (finsupp.total ι β α v) (is_basis.repr hv)) (g n) = g n,
    rw [hv.total_comp_repr, linear_map.id_apply] },
end

end finsupp
