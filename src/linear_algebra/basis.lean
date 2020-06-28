/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import linear_algebra.finsupp
import linear_algebra.projection
import order.zorn
import data.fintype.card

/-!

# Linear independence and bases

This file defines linear independence and bases in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

## Main definitions

All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `linear_independent R v` states that the elements of the family `v` are linearly independent.

* `linear_independent.repr hv x` returns the linear combination representing `x : span R (range v)`
  on the linearly independent vectors `v`, given `hv : linear_independent R v`
  (using classical choice). `linear_independent.repr hv` is provided as a linear map.

* `is_basis R v` states that the vector family `v` is a basis, i.e. it is linearly independent and
  spans the entire space.

* `is_basis.repr hv x` is the basis version of `linear_independent.repr hv x`. It returns the
  linear combination representing `x : M` on a basis `v` of `M` (using classical choice).
  The argument `hv` must be a proof that `is_basis R v`. `is_basis.repr hv` is given as a linear
  map as well.

* `is_basis.constr hv f` constructs a linear map `M₁ →ₗ[R] M₂` given the values `f : ι → M₂` at the
  basis `v : ι → M₁`, given `hv : is_basis R v`.

## Main statements

* `is_basis.ext` states that two linear maps are equal if they coincide on a basis.

* `exists_is_basis` states that every vector space has a basis.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent. For bases, this is useful as well because we can easily derive ordered bases by using an
ordered index type `ι`.

If you want to use sets, use the family `(λ x, x : s → M)` given a set `s : set M`. The lemmas
`linear_independent.to_subtype_range` and `linear_independent.of_subtype_range` connect those two
worlds.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence, basis

-/

noncomputable theory

open function set submodule
open_locale classical big_operators

universe u

variables {ι : Type*} {ι' : Type*} {R : Type*} {K : Type*}
          {M : Type*} {M' : Type*} {V : Type u} {V' : Type*}

section module
variables {v : ι → M}
variables [ring R] [add_comm_group M] [add_comm_group M']
variables [module R M] [module R M']
variables {a b : R} {x y : M}

variables (R) (v)
/-- Linearly independent family of vectors -/
def linear_independent : Prop := (finsupp.total ι M R v).ker = ⊥
variables {R} {v}

theorem linear_independent_iff : linear_independent R v ↔
  ∀l, finsupp.total ι M R v l = 0 → l = 0 :=
by simp [linear_independent, linear_map.ker_eq_bot']

theorem linear_independent_iff' : linear_independent R v ↔
  ∀ s : finset ι, ∀ g : ι → R, ∑ i in s, g i • v i = 0 → ∀ i ∈ s, g i = 0 :=
linear_independent_iff.trans
⟨λ hf s g hg i his, have h : _ := hf (∑ i in s, finsupp.single i (g i)) $
      by simpa only [linear_map.map_sum, finsupp.total_single] using hg, calc
    g i = (finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (finsupp.single i (g i)) :
      by rw [finsupp.lapply_apply, finsupp.single_eq_same]
    ... = ∑ j in s, (finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (finsupp.single j (g j)) :
      eq.symm $ finset.sum_eq_single i
        (λ j hjs hji, by rw [finsupp.lapply_apply, finsupp.single_eq_of_ne hji])
        (λ hnis, hnis.elim his)
    ... = (∑ j in s, finsupp.single j (g j)) i : (finsupp.lapply i : (ι →₀ R) →ₗ[R] R).map_sum.symm
    ... = 0 : finsupp.ext_iff.1 h i,
λ hf l hl, finsupp.ext $ λ i, classical.by_contradiction $ λ hni, hni $ hf _ _ hl _ $
  finsupp.mem_support_iff.2 hni⟩

theorem linear_dependent_iff : ¬ linear_independent R v ↔
  ∃ s : finset ι, ∃ g : ι → R, s.sum (λ i, g i • v i) = 0 ∧ (∃ i ∈ s, g i ≠ 0) :=
begin
  rw linear_independent_iff',
  simp only [exists_prop, classical.not_forall],
end

lemma linear_independent_empty_type (h : ¬ nonempty ι) : linear_independent R v :=
begin
 rw [linear_independent_iff],
 intros,
 ext i,
 exact false.elim (not_nonempty_iff_imp_false.1 h i)
end

lemma linear_independent.ne_zero
  {i : ι} (ne : 0 ≠ (1:R)) (hv : linear_independent R v) : v i ≠ 0 :=
λ h, ne $ eq.symm begin
  suffices : (finsupp.single i 1 : ι →₀ R) i = 0, {simpa},
  rw linear_independent_iff.1 hv (finsupp.single i 1),
  {simp},
  {simp [h]}
end

lemma linear_independent.comp
  (h : linear_independent R v) (f : ι' → ι) (hf : injective f) : linear_independent R (v ∘ f) :=
begin
  rw [linear_independent_iff, finsupp.total_comp],
  intros l hl,
  have h_map_domain : ∀ x, (finsupp.map_domain f l) (f x) = 0,
    by rw linear_independent_iff.1 h (finsupp.map_domain f l) hl; simp,
  ext,
  convert h_map_domain a,
  simp only [finsupp.map_domain_apply hf],
end

lemma linear_independent_of_zero_eq_one (zero_eq_one : (0 : R) = 1) : linear_independent R v :=
linear_independent_iff.2 (λ l hl, finsupp.eq_zero_of_zero_eq_one zero_eq_one _)

lemma linear_independent.unique (hv : linear_independent R v) {l₁ l₂ : ι →₀ R} :
  finsupp.total ι M R v l₁ = finsupp.total ι M R v l₂ → l₁ = l₂ :=
by apply linear_map.ker_eq_bot.1 hv

lemma linear_independent.injective (zero_ne_one : (0 : R) ≠ 1) (hv : linear_independent R v) :
  injective v :=
begin
  intros i j hij,
  let l : ι →₀ R := finsupp.single i (1 : R) - finsupp.single j 1,
  have h_total : finsupp.total ι M R v l = 0,
  { rw finsupp.total_apply,
    rw finsupp.sum_sub_index,
    { simp [finsupp.sum_single_index, hij] },
    { intros, apply sub_smul } },
  have h_single_eq : finsupp.single i (1 : R) = finsupp.single j 1,
  { rw linear_independent_iff at hv,
    simp [eq_add_of_sub_eq' (hv l h_total)] },
  show i = j,
  { apply or.elim ((finsupp.single_eq_single_iff _ _ _ _).1 h_single_eq),
    simp,
    exact λ h, false.elim (zero_ne_one.symm h.1) }
end

lemma linear_independent_span (hs : linear_independent R v) :
  @linear_independent ι R (span R (range v))
      (λ i : ι, ⟨v i, subset_span (mem_range_self i)⟩) _ _ _ :=
begin
  rw linear_independent_iff at *,
  intros l hl,
  apply hs l,
  have := congr_arg (submodule.subtype (span R (range v))) hl,
  convert this,
  rw [finsupp.total_apply, finsupp.total_apply],
  unfold finsupp.sum,
  rw linear_map.map_sum (submodule.subtype (span R (range v))),
  simp
end

section subtype
/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/

theorem linear_independent_comp_subtype {s : set ι} :
  linear_independent R (v ∘ coe : s → M) ↔
  ∀ l ∈ (finsupp.supported R R s), (finsupp.total ι M R v) l = 0 → l = 0 :=
begin
  rw [linear_independent_iff, finsupp.total_comp],
  simp only [linear_map.comp_apply],
  split,
  { intros h l hl₁ hl₂,
    have h_bij : bij_on coe (coe ⁻¹' ↑l.support : set s) ↑l.support,
    { apply bij_on.mk,
      { apply maps_to_preimage },
      { apply subtype.coe_injective.inj_on },
      intros i hi,
      rw [image_preimage_eq_inter_range, subtype.range_coe],
      exact ⟨hi, (finsupp.mem_supported _ _).1 hl₁ hi⟩ },
    show l = 0,
    { apply finsupp.eq_zero_of_comap_domain_eq_zero (coe : s → ι) _ h_bij,
      apply h,
      convert hl₂,
      rw [finsupp.lmap_domain_apply, finsupp.map_domain_comap_domain],
      exact subtype.coe_injective,
      rw subtype.range_coe,
      exact (finsupp.mem_supported _ _).1 hl₁ } },
  { intros h l hl,
    have hl' : finsupp.total ι M R v (finsupp.emb_domain ⟨coe, subtype.coe_injective⟩ l) = 0,
    { rw finsupp.emb_domain_eq_map_domain ⟨coe, subtype.coe_injective⟩ l,
      apply hl },
    apply finsupp.emb_domain_inj.1,
    rw [h (finsupp.emb_domain ⟨coe, subtype.coe_injective⟩ l) _ hl',
        finsupp.emb_domain_zero],
    rw [finsupp.mem_supported, finsupp.support_emb_domain],
    intros x hx,
    rw [finset.mem_coe, finset.mem_map] at hx,
    rcases hx with ⟨i, x', hx'⟩,
    rw ←hx',
    simp }
end

theorem linear_independent_subtype {s : set M} :
  linear_independent R (λ x, x : s → M) ↔
  ∀ l ∈ (finsupp.supported R R s), (finsupp.total M M R id) l = 0 → l = 0 :=
by apply @linear_independent_comp_subtype _ _ _ id

theorem linear_independent_comp_subtype_disjoint {s : set ι} :
  linear_independent R (v ∘ coe : s → M) ↔
  disjoint (finsupp.supported R R s) (finsupp.total ι M R v).ker :=
by rw [linear_independent_comp_subtype, linear_map.disjoint_ker]

theorem linear_independent_subtype_disjoint {s : set M} :
  linear_independent R (λ x, x : s → M) ↔
  disjoint (finsupp.supported R R s) (finsupp.total M M R id).ker :=
by apply @linear_independent_comp_subtype_disjoint _ _ _ id

theorem linear_independent_iff_total_on {s : set M} :
  linear_independent R (λ x, x : s → M) ↔ (finsupp.total_on M M R id s).ker = ⊥ :=
by rw [finsupp.total_on, linear_map.ker, linear_map.comap_cod_restrict, map_bot, comap_bot,
  linear_map.ker_comp, linear_independent_subtype_disjoint, disjoint, ← map_comap_subtype,
  map_le_iff_le_comap, comap_bot, ker_subtype, le_bot_iff]

lemma linear_independent.to_subtype_range
  (hv : linear_independent R v) : linear_independent R (λ x, x : range v → M) :=
begin
  by_cases zero_eq_one : (0 : R) = 1,
  { apply linear_independent_of_zero_eq_one zero_eq_one },
  rw linear_independent_subtype,
  intros l hl₁ hl₂,
  have h_bij : bij_on v (v ⁻¹' ↑l.support) ↑l.support,
  { apply bij_on.mk,
    { apply maps_to_preimage },
    { apply (linear_independent.injective zero_eq_one hv).inj_on },
    intros x hx,
    rcases mem_range.1 (((finsupp.mem_supported _ _).1 hl₁ : ↑(l.support) ⊆ range v) hx)
      with ⟨i, hi⟩,
    rw mem_image,
    use i,
    rw [mem_preimage, hi],
    exact ⟨hx, rfl⟩ },
  apply finsupp.eq_zero_of_comap_domain_eq_zero v l,
  apply linear_independent_iff.1 hv,
  rw [finsupp.total_comap_domain, finset.sum_preimage v l.support h_bij (λ (x : M), l x • x)],
  rw [finsupp.total_apply, finsupp.sum] at hl₂,
  apply hl₂
end

lemma linear_independent.of_subtype_range (hv : injective v)
  (h : linear_independent R (λ x, x : range v → M)) : linear_independent R v :=
begin
  rw linear_independent_iff,
  intros l hl,
  apply finsupp.map_domain_injective hv,
  apply linear_independent_subtype.1 h (l.map_domain v),
  { rw finsupp.mem_supported,
    intros x hx,
    have := finset.mem_coe.2 (finsupp.map_domain_support hx),
    rw finset.coe_image at this,
    apply set.image_subset_range _ _ this, },
  { rwa [finsupp.total_map_domain _ _ hv, left_id] }
end

lemma linear_independent.restrict_of_comp_subtype {s : set ι}
  (hs : linear_independent R (v ∘ coe : s → M)) :
  linear_independent R (s.restrict v) :=
begin
  have h_restrict : restrict v s = v ∘ coe := rfl,
  rw [linear_independent_iff, h_restrict, finsupp.total_comp],
  intros l hl,
  have h_map_domain_subtype_eq_0 : l.map_domain coe = 0,
  { rw linear_independent_comp_subtype at hs,
    apply hs (finsupp.lmap_domain R R coe l) _ hl,
    rw finsupp.mem_supported,
    simp,
    intros x hx,
    have := finset.mem_coe.2 (finsupp.map_domain_support (finset.mem_coe.1 hx)),
    rw finset.coe_image at this,
    exact subtype.coe_image_subset _ _ this },
  apply @finsupp.map_domain_injective _ (subtype s) ι,
  { apply subtype.coe_injective },
  { simpa },
end

variables (R M)
lemma linear_independent_empty : linear_independent R (λ x, x : (∅ : set M) → M) :=
by simp [linear_independent_subtype_disjoint]
variables {R M}

lemma linear_independent.mono {t s : set M} (h : t ⊆ s) :
  linear_independent R (λ x, x : s → M) → linear_independent R (λ x, x : t → M) :=
begin
 simp only [linear_independent_subtype_disjoint],
 exact (disjoint.mono_left (finsupp.supported_mono h))
end

lemma linear_independent.union {s t : set M}
  (hs : linear_independent R (λ x, x : s → M)) (ht : linear_independent R (λ x, x : t → M))
  (hst : disjoint (span R s) (span R t)) :
  linear_independent R (λ x, x : (s ∪ t) → M) :=
begin
  rw [linear_independent_subtype_disjoint, disjoint_def, finsupp.supported_union],
  intros l h₁ h₂, rw mem_sup at h₁,
  rcases h₁ with ⟨ls, hls, lt, hlt, rfl⟩,
  have h_ls_mem_t : finsupp.total M M R id ls ∈ span R t,
  { rw [← image_id t, finsupp.span_eq_map_total],
    apply (add_mem_iff_left (map _ _) (mem_image_of_mem _ hlt)).1,
    rw [← linear_map.map_add, linear_map.mem_ker.1 h₂],
    apply zero_mem },
  have h_lt_mem_s : finsupp.total M M R id lt ∈ span R s,
  { rw [← image_id s, finsupp.span_eq_map_total],
    apply (add_mem_iff_left (map _ _) (mem_image_of_mem _ hls)).1,
    rw [← linear_map.map_add, add_comm, linear_map.mem_ker.1 h₂],
    apply zero_mem },
  have h_ls_mem_s : (finsupp.total M M R id) ls ∈ span R s,
  { rw ← image_id s,
    apply (finsupp.mem_span_iff_total _).2 ⟨ls, hls, rfl⟩ },
  have h_lt_mem_t : (finsupp.total M M R id) lt ∈ span R t,
  { rw ← image_id t,
    apply (finsupp.mem_span_iff_total _).2 ⟨lt, hlt, rfl⟩ },
  have h_ls_0 : ls = 0 :=
    disjoint_def.1 (linear_independent_subtype_disjoint.1 hs) _ hls
    (linear_map.mem_ker.2 $ disjoint_def.1 hst (finsupp.total M M R id ls) h_ls_mem_s h_ls_mem_t),
  have h_lt_0 : lt = 0 :=
    disjoint_def.1 (linear_independent_subtype_disjoint.1 ht) _ hlt
    (linear_map.mem_ker.2 $ disjoint_def.1 hst (finsupp.total M M R id lt) h_lt_mem_s h_lt_mem_t),
  show ls + lt = 0,
    by simp [h_ls_0, h_lt_0],
end

lemma linear_independent_of_finite (s : set M)
  (H : ∀ t ⊆ s, finite t → linear_independent R (λ x, x : t → M)) :
  linear_independent R (λ x, x : s → M) :=
linear_independent_subtype.2 $
  λ l hl, linear_independent_subtype.1 (H _ hl (finset.finite_to_set _)) l (subset.refl _)

lemma linear_independent_Union_of_directed {η : Type*}
  {s : η → set M} (hs : directed (⊆) s)
  (h : ∀ i, linear_independent R (λ x, x : s i → M)) :
  linear_independent R (λ x, x : (⋃ i, s i) → M) :=
begin
  by_cases hη : nonempty η,
  { refine linear_independent_of_finite (⋃ i, s i) (λ t ht ft, _),
    rcases finite_subset_Union ft ht with ⟨I, fi, hI⟩,
    rcases hs.finset_le hη fi.to_finset with ⟨i, hi⟩,
    exact (h i).mono (subset.trans hI $ bUnion_subset $
      λ j hj, hi j (finite.mem_to_finset.2 hj)) },
  { refine (linear_independent_empty _ _).mono _,
    rintro _ ⟨_, ⟨i, _⟩, _⟩, exact hη ⟨i⟩ }
end

lemma linear_independent_sUnion_of_directed {s : set (set M)}
  (hs : directed_on (⊆) s)
  (h : ∀ a ∈ s, linear_independent R (λ x, x : (a : set M) → M)) :
  linear_independent R (λ x, x : (⋃₀ s) → M) :=
by rw sUnion_eq_Union; exact
linear_independent_Union_of_directed
  ((directed_on_iff_directed _).1 hs) (by simpa using h)

lemma linear_independent_bUnion_of_directed {η} {s : set η} {t : η → set M}
  (hs : directed_on (t ⁻¹'o (⊆)) s) (h : ∀a∈s, linear_independent R (λ x, x : t a → M)) :
  linear_independent R (λ x, x : (⋃a∈s, t a) → M) :=
by rw bUnion_eq_Union; exact
linear_independent_Union_of_directed
  ((directed_comp _ _ _).2 $ (directed_on_iff_directed _).1 hs)
  (by simpa using h)

lemma linear_independent_Union_finite_subtype {ι : Type*} {f : ι → set M}
  (hl : ∀i, linear_independent R (λ x, x : f i → M))
  (hd : ∀i, ∀t:set ι, finite t → i ∉ t → disjoint (span R (f i)) (⨆i∈t, span R (f i))) :
  linear_independent R (λ x, x : (⋃i, f i) → M) :=
begin
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
    refine (hl _).union ih _,
    rw [finset.sup_eq_supr],
    refine (hd i _ _ his).mono_right _,
    { simp only [(span_Union _).symm],
      refine span_mono (@supr_le_supr2 (set M) _ _ _ _ _ _),
      rintros ⟨i⟩, exact ⟨i, le_refl _⟩ },
    { change finite (plift.up ⁻¹' ↑s),
      exact s.finite_to_set.preimage (assume i j _ _, plift.up.inj) } }
end

lemma linear_independent_Union_finite {η : Type*} {ιs : η → Type*}
  {f : Π j : η, ιs j → M}
  (hindep : ∀j, linear_independent R (f j))
  (hd : ∀i, ∀t:set η, finite t → i ∉ t →
      disjoint (span R (range (f i))) (⨆i∈t, span R (range (f i)))) :
  linear_independent R (λ ji : Σ j, ιs j, f ji.1 ji.2) :=
begin
  by_cases zero_eq_one : (0 : R) = 1,
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
        simp only at hxy,
        rw hxy,
        exact (subset_span (mem_range_self y₂)) },
      exact false.elim ((hindep x₁).ne_zero zero_eq_one h0) } },
  rw range_sigma_eq_Union_range,
  apply linear_independent_Union_finite_subtype (λ j, (hindep j).to_subtype_range) hd,
end

end subtype

section repr
variables (hv : linear_independent R v)

/-- Canonical isomorphism between linear combinations and the span of linearly independent vectors.
-/
def linear_independent.total_equiv (hv : linear_independent R v) :
  (ι →₀ R) ≃ₗ[R] span R (range v) :=
begin
apply linear_equiv.of_bijective
  (linear_map.cod_restrict (span R (range v)) (finsupp.total ι M R v) _),
{ rw linear_map.ker_cod_restrict,
  apply hv },
{ rw [linear_map.range, linear_map.map_cod_restrict, ← linear_map.range_le_iff_comap,
  range_subtype, map_top],
  rw finsupp.range_total,
  apply le_refl (span R (range v)) },
{ intro l,
  rw ← finsupp.range_total,
  rw linear_map.mem_range,
  apply mem_range_self l }
end

/-- Linear combination representing a vector in the span of linearly independent vectors.

Given a family of linearly independent vectors, we can represent any vector in their span as
a linear combination of these vectors. These are provided by this linear map.
It is simply one direction of `linear_independent.total_equiv`. -/
def linear_independent.repr (hv : linear_independent R v) :
  span R (range v) →ₗ[R] ι →₀ R := hv.total_equiv.symm

lemma linear_independent.total_repr (x) : finsupp.total ι M R v (hv.repr x) = x :=
subtype.ext_iff.1 (linear_equiv.apply_symm_apply hv.total_equiv x)

lemma linear_independent.total_comp_repr :
  (finsupp.total ι M R v).comp hv.repr = submodule.subtype _ :=
linear_map.ext $ hv.total_repr

lemma linear_independent.repr_ker : hv.repr.ker = ⊥ :=
by rw [linear_independent.repr, linear_equiv.ker]

lemma linear_independent.repr_range : hv.repr.range = ⊤ :=
by rw [linear_independent.repr, linear_equiv.range]

lemma linear_independent.repr_eq
  {l : ι →₀ R} {x} (eq : finsupp.total ι M R v l = ↑x) :
  hv.repr x = l :=
begin
  have : ↑((linear_independent.total_equiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l)
      = finsupp.total ι M R v l := rfl,
  have : (linear_independent.total_equiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l = x,
  { rw eq at this,
    exact subtype.ext_iff.2 this },
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

-- TODO: why is this so slow?
lemma linear_independent_iff_not_smul_mem_span :
  linear_independent R v ↔ (∀ (i : ι) (a : R), a • (v i) ∈ span R (v '' (univ \ {i})) → a = 0) :=
⟨ λ hv i a ha, begin
  rw [finsupp.span_eq_map_total, mem_map] at ha,
  rcases ha with ⟨l, hl, e⟩,
  rw sub_eq_zero.1 (linear_independent_iff.1 hv (l - finsupp.single i a) (by simp [e])) at hl,
  by_contra hn,
  exact (not_mem_of_mem_diff (hl $ by simp [hn])) (mem_singleton _),
end, λ H, linear_independent_iff.2 $ λ l hl, begin
  ext i, simp only [finsupp.zero_apply],
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
  (hv : linear_independent R v) (f : ι' ↪ ι)
  (hss : range v ⊆ span R (range (v ∘ f))) (zero_ne_one : 0 ≠ (1 : R)):
  surjective f :=
begin
  intros i,
  let repr : (span R (range (v ∘ f)) : Type*) → ι' →₀ R := (hv.comp f f.injective).repr,
  let l := (repr ⟨v i, hss (mem_range_self i)⟩).map_domain f,
  have h_total_l : finsupp.total ι M R v l = v i,
  { dsimp only [l],
    rw finsupp.total_map_domain,
    rw (hv.comp f f.injective).total_repr,
    { refl },
    { exact f.injective } },
  have h_total_eq : (finsupp.total ι M R v) l = (finsupp.total ι M R v) (finsupp.single i 1),
    by rw [h_total_l, finsupp.total_single, one_smul],
  have l_eq : l = _ := linear_map.ker_eq_bot.1 hv h_total_eq,
  dsimp only [l] at l_eq,
  rw ←finsupp.emb_domain_eq_map_domain at l_eq,
  rcases finsupp.single_of_emb_domain_single (repr ⟨v i, _⟩) f i (1 : R) zero_ne_one.symm l_eq
    with ⟨i', hi'⟩,
  use i',
  exact hi'.2
end

lemma eq_of_linear_independent_of_span_subtype {s t : set M} (zero_ne_one : (0 : R) ≠ 1)
  (hs : linear_independent R (λ x, x : s → M)) (h : t ⊆ s) (hst : s ⊆ span R t) : s = t :=
begin
  let f : t ↪ s := ⟨λ x, ⟨x.1, h x.2⟩, λ a b hab, subtype.coe_injective (subtype.mk.inj hab)⟩,
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

lemma linear_independent.image (hv : linear_independent R v) {f : M →ₗ M'}
  (hf_inj : disjoint (span R (range v)) f.ker) : linear_independent R (f ∘ v) :=
begin
  rw [disjoint, ← set.image_univ, finsupp.span_eq_map_total, map_inf_eq_map_inf_comap,
    map_le_iff_le_comap, comap_bot, finsupp.supported_univ, top_inf_eq] at hf_inj,
  unfold linear_independent at hv,
  rw hv at hf_inj,
  haveI : inhabited M := ⟨0⟩,
  rw [linear_independent, finsupp.total_comp],
  rw [@finsupp.lmap_domain_total _ _ R _ _ _ _ _ _ _ _ _ _ f, ker_comp, eq_bot_iff],
  apply hf_inj,
  exact λ _, rfl,
end

lemma linear_independent.image_subtype {s : set M} {f : M →ₗ M'}
  (hs : linear_independent R (λ x, x : s → M))
  (hf_inj : disjoint (span R s) f.ker) : linear_independent R (λ x, x : f '' s → M') :=
begin
  rw [disjoint, ← set.image_id s, finsupp.span_eq_map_total, map_inf_eq_map_inf_comap,
    map_le_iff_le_comap, comap_bot] at hf_inj,
  haveI : inhabited M := ⟨0⟩,
  rw [linear_independent_subtype_disjoint, disjoint, ← finsupp.lmap_domain_supported _ _ f, map_inf_eq_map_inf_comap,
      map_le_iff_le_comap, ← ker_comp],
  rw [@finsupp.lmap_domain_total _ _ R _ _ _, ker_comp],
  { exact le_trans (le_inf inf_le_left hf_inj)
    (le_trans (linear_independent_subtype_disjoint.1 hs) bot_le) },
  { simp }
end

lemma linear_independent.inl_union_inr {s : set M} {t : set M'}
  (hs : linear_independent R (λ x, x : s → M))
  (ht : linear_independent R (λ x, x : t → M')) :
  linear_independent R (λ x, x : inl R M M' '' s ∪ inr R M M' '' t → M × M') :=
begin
  refine (hs.image_subtype _).union (ht.image_subtype _) _; [simp, simp, skip],
  simp only [span_image],
  simp [disjoint_iff, prod_inf_prod]
end

lemma linear_independent_inl_union_inr' {v : ι → M} {v' : ι' → M'}
  (hv : linear_independent R v) (hv' : linear_independent R v') :
  linear_independent R (sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) :=
begin
  by_cases zero_eq_one : (0 : R) = 1,
  { apply linear_independent_of_zero_eq_one zero_eq_one },
  have inj_v : injective v := (linear_independent.injective zero_eq_one hv),
  have inj_v' : injective v' := (linear_independent.injective zero_eq_one hv'),
  apply linear_independent.of_subtype_range,
  { apply sum.elim_injective,
    { exact prod.inl_injective.comp inj_v },
    { exact prod.inr_injective.comp inj_v' },
    { intros, simp [hv.ne_zero zero_eq_one] } },
  { rw sum.elim_range,
    refine (hv.image _).to_subtype_range.union (hv'.image _).to_subtype_range _;
      [simp, simp, skip],
    apply disjoint_inl_inr.mono _ _;
      simp only [set.range_comp, span_image, linear_map.map_le_range] }
end

/-- Dedekind's linear independence of characters -/
-- See, for example, Keith Conrad's note <https://kconrad.math.uconn.edu/blurbs/galoistheory/linearchar.pdf>
theorem linear_independent_monoid_hom (G : Type*) [monoid G] (L : Type*) [integral_domain L] :
  @linear_independent _ L (G → L) (λ f, f : (G →* L) → (G → L)) _ _ _ :=
by letI := classical.dec_eq (G →* L);
   letI : mul_action L L := distrib_mul_action.to_mul_action;
-- We prove linear independence by showing that only the trivial linear combination vanishes.
exact linear_independent_iff'.2
-- To do this, we use `finset` induction,
(λ s, finset.induction_on s (λ g hg i, false.elim) $ λ a s has ih g hg,
-- Here
-- * `a` is a new character we will insert into the `finset` of characters `s`,
-- * `ih` is the fact that only the trivial linear combination of characters in `s` is zero
-- * `hg` is the fact that `g` are the coefficients of a linear combination summing to zero
-- and it remains to prove that `g` vanishes on `insert a s`.

-- We now make the key calculation:
-- For any character `i` in the original `finset`, we have `g i • i = g i • a` as functions on the monoid `G`.
have h1 : ∀ i ∈ s, (g i • i : G → L) = g i • a, from λ i his, funext $ λ x : G,
  -- We prove these expressions are equal by showing
  -- the differences of their values on each monoid element `x` is zero
  eq_of_sub_eq_zero $ ih (λ j, g j * j x - g j * a x)
    (funext $ λ y : G, calc
    -- After that, it's just a chase scene.
          (∑ i in s, ((g i * i x - g i * a x) • i : G → L)) y
        = ∑ i in s, (g i * i x - g i * a x) * i y : pi.finset_sum_apply _ _ _
    ... = ∑ i in s, (g i * i x * i y - g i * a x * i y) : finset.sum_congr rfl
      (λ _ _, sub_mul _ _ _)
    ... = ∑ i in s, g i * i x * i y - ∑ i in s, g i * a x * i y : finset.sum_sub_distrib
    ... = (g a * a x * a y + ∑ i in s, g i * i x * i y)
          - (g a * a x * a y + ∑ i in s, g i * a x * i y) : by rw add_sub_add_left_eq_sub
    ... = ∑ i in insert a s, g i * i x * i y - ∑ i in insert a s, g i * a x * i y :
      by rw [finset.sum_insert has, finset.sum_insert has]
    ... = ∑ i in insert a s, g i * i (x * y) - ∑ i in insert a s, a x * (g i * i y) :
      congr (congr_arg has_sub.sub (finset.sum_congr rfl $ λ i _, by rw [i.map_mul, mul_assoc]))
        (finset.sum_congr rfl $ λ _ _, by rw [mul_assoc, mul_left_comm])
    ... = (∑ i in insert a s, (g i • i : G → L)) (x * y)
          - a x * (∑ i in insert a s, (g i • i : G → L)) y :
      by rw [pi.finset_sum_apply, pi.finset_sum_apply, finset.mul_sum]; refl
    ... = 0 - a x * 0 : by rw hg; refl
    ... = 0 : by rw [mul_zero, sub_zero])
    i
    his,
-- On the other hand, since `a` is not already in `s`, for any character `i ∈ s`
-- there is some element of the monoid on which it differs from `a`.
have h2 : ∀ i : G →* L, i ∈ s → ∃ y, i y ≠ a y, from λ i his,
  classical.by_contradiction $ λ h,
  have hia : i = a, from monoid_hom.ext $ λ y, classical.by_contradiction $ λ hy, h ⟨y, hy⟩,
  has $ hia ▸ his,
-- From these two facts we deduce that `g` actually vanishes on `s`,
have h3 : ∀ i ∈ s, g i = 0, from λ i his, let ⟨y, hy⟩ := h2 i his in
  have h : g i • i y = g i • a y, from congr_fun (h1 i his) y,
  or.resolve_right (mul_eq_zero.1 $ by rw [mul_sub, sub_eq_zero]; exact h) (sub_ne_zero_of_ne hy),
-- And so, using the fact that the linear combination over `s` and over `insert a s` both vanish,
-- we deduce that `g a = 0`.
have h4 : g a = 0, from calc
  g a = g a * 1 : (mul_one _).symm
  ... = (g a • a : G → L) 1 : by rw ← a.map_one; refl
  ... = (∑ i in insert a s, (g i • i : G → L)) 1 : begin
      rw finset.sum_eq_single a,
      { intros i his hia, rw finset.mem_insert at his, rw [h3 i (his.resolve_left hia), zero_smul] },
      { intros haas, exfalso, apply haas, exact finset.mem_insert_self a s }
    end
  ... = 0 : by rw hg; refl,
-- Now we're done; the last two facts together imply that `g` vanishes on every element of `insert a s`.
(finset.forall_mem_insert _ _ _).2 ⟨h4, h3⟩)

lemma le_of_span_le_span {s t u: set M} (zero_ne_one : (0 : R) ≠ 1)
  (hl : linear_independent R (coe : u → M )) (hsu : s ⊆ u) (htu : t ⊆ u)
  (hst : span R s ≤ span R t) : s ⊆ t :=
begin
  have := eq_of_linear_independent_of_span_subtype zero_ne_one
    (hl.mono (set.union_subset hsu htu))
    (set.subset_union_right _ _)
    (set.union_subset (set.subset.trans subset_span hst) subset_span),
  rw ← this, apply set.subset_union_left
end

lemma span_le_span_iff {s t u: set M} (zero_ne_one : (0 : R) ≠ 1)
  (hl : linear_independent R (coe : u → M)) (hsu : s ⊆ u) (htu : t ⊆ u) :
  span R s ≤ span R t ↔ s ⊆ t :=
⟨le_of_span_le_span zero_ne_one hl hsu htu, span_mono⟩

variables (R) (v)
/-- A family of vectors is a basis if it is linearly independent and all vectors are in the span. -/
def is_basis := linear_independent R v ∧ span R (range v) = ⊤
variables {R} {v}

section is_basis
variables {s t : set M} (hv : is_basis R v)

lemma is_basis.mem_span (hv : is_basis R v) : ∀ x, x ∈ span R (range v) := eq_top_iff'.1 hv.2

lemma is_basis.comp (hv : is_basis R v) (f : ι' → ι) (hf : bijective f) :
  is_basis R (v ∘ f) :=
begin
  split,
  { apply hv.1.comp f hf.1 },
  { rw[set.range_comp, range_iff_surjective.2 hf.2, image_univ, hv.2] }
end

lemma is_basis.injective (hv : is_basis R v) (zero_ne_one : (0 : R) ≠ 1) : injective v :=
  λ x y h, linear_independent.injective zero_ne_one hv.1 h

lemma is_basis.range (hv : is_basis R v) : is_basis R (λ x, x : range v → M) :=
⟨hv.1.to_subtype_range, by { convert hv.2, ext i, exact ⟨λ ⟨p, hp⟩, hp ▸ p.2, λ hi, ⟨⟨i, hi⟩, rfl⟩⟩ }⟩

/-- Given a basis, any vector can be written as a linear combination of the basis vectors. They are
given by this linear map. This is one direction of `module_equiv_finsupp`. -/
def is_basis.repr : M →ₗ (ι →₀ R) :=
(hv.1.repr).comp (linear_map.id.cod_restrict _ hv.mem_span)

lemma is_basis.total_repr (x) : finsupp.total ι M R v (hv.repr x) = x :=
hv.1.total_repr ⟨x, _⟩

lemma is_basis.total_comp_repr : (finsupp.total ι M R v).comp hv.repr = linear_map.id :=
linear_map.ext hv.total_repr

lemma is_basis.repr_ker : hv.repr.ker = ⊥ :=
linear_map.ker_eq_bot.2 $ left_inverse.injective hv.total_repr

lemma is_basis.repr_range : hv.repr.range = finsupp.supported R R univ :=
by rw [is_basis.repr, linear_map.range, submodule.map_comp,
  linear_map.map_cod_restrict, submodule.map_id, comap_top, map_top, hv.1.repr_range,
  finsupp.supported_univ]

lemma is_basis.repr_total (x : ι →₀ R) (hx : x ∈ finsupp.supported R R (univ : set ι)) :
  hv.repr (finsupp.total ι M R v x) = x :=
begin
  rw [← hv.repr_range, linear_map.mem_range] at hx,
  cases hx with w hw,
  rw [← hw, hv.total_repr],
end

lemma is_basis.repr_eq_single {i} : hv.repr (v i) = finsupp.single i 1 :=
by apply hv.1.repr_eq_single; simp

/-- Construct a linear map given the value at the basis. -/
def is_basis.constr (f : ι → M') : M →ₗ[R] M' :=
(finsupp.total M' M' R id).comp $ (finsupp.lmap_domain R R f).comp hv.repr

theorem is_basis.constr_apply (f : ι → M') (x : M) :
  (hv.constr f : M → M') x = (hv.repr x).sum (λb a, a • f b) :=
by dsimp [is_basis.constr];
   rw [finsupp.total_apply, finsupp.sum_map_domain_index]; simp [add_smul]

lemma is_basis.ext {f g : M →ₗ[R] M'} (hv : is_basis R v) (h : ∀i, f (v i) = g (v i)) : f = g :=
begin
  apply linear_map.ext (λ x, linear_eq_on (range v) _ (hv.mem_span x)),
  exact (λ y hy, exists.elim (set.mem_range.1 hy) (λ i hi, by rw ←hi; exact h i))
end

@[simp] lemma constr_basis {f : ι → M'} {i : ι} (hv : is_basis R v) :
  (hv.constr f : M → M') (v i) = f i :=
by simp [is_basis.constr_apply, hv.repr_eq_single, finsupp.sum_single_index]

lemma constr_eq {g : ι → M'} {f : M →ₗ[R] M'} (hv : is_basis R v)
  (h : ∀i, g i = f (v i)) : hv.constr g = f :=
hv.ext $ λ i, (constr_basis hv).trans (h i)

lemma constr_self (f : M →ₗ[R] M') : hv.constr (λ i, f (v i)) = f :=
constr_eq hv $ λ x, rfl

lemma constr_zero (hv : is_basis R v) : hv.constr (λi, (0 : M')) = 0 :=
constr_eq hv $ λ x, rfl

lemma constr_add {g f : ι → M'} (hv : is_basis R v) :
  hv.constr (λi, f i + g i) = hv.constr f + hv.constr g :=
constr_eq hv $ λ b, by simp

lemma constr_neg {f : ι → M'} (hv : is_basis R v) : hv.constr (λi, - f i) = - hv.constr f :=
constr_eq hv $ λ b, by simp

lemma constr_sub {g f : ι → M'} (hs : is_basis R v) :
  hv.constr (λi, f i - g i) = hs.constr f - hs.constr g :=
by simp [sub_eq_add_neg, constr_add, constr_neg]

-- this only works on functions if `R` is a commutative ring
lemma constr_smul {ι R M} [comm_ring R] [add_comm_group M] [module R M]
  {v : ι → R} {f : ι → M} {a : R} (hv : is_basis R v) :
  hv.constr (λb, a • f b) = a • hv.constr f :=
constr_eq hv $ by simp [constr_basis hv] {contextual := tt}

lemma constr_range [nonempty ι] (hv : is_basis R v) {f : ι  → M'} :
  (hv.constr f).range = span R (range f) :=
by rw [is_basis.constr, linear_map.range_comp, linear_map.range_comp, is_basis.repr_range,
    finsupp.lmap_domain_supported, ←set.image_univ, ←finsupp.span_eq_map_total, image_id]

/-- Canonical equivalence between a module and the linear combinations of basis vectors. -/
def module_equiv_finsupp (hv : is_basis R v) : M ≃ₗ[R] ι →₀ R :=
(hv.1.total_equiv.trans (linear_equiv.of_top _ hv.2)).symm

@[simp] theorem module_equiv_finsupp_apply_basis (hv : is_basis R v) (i : ι) :
  module_equiv_finsupp hv (v i) = finsupp.single i 1 :=
(linear_equiv.symm_apply_eq _).2 $ by simp [linear_independent.total_equiv]

/-- Isomorphism between the two modules, given two modules `M` and `M'` with respective bases
`v` and `v'` and a bijection between the indexing sets of the two bases. -/
def equiv_of_is_basis {v : ι → M} {v' : ι' → M'} (hv : is_basis R v) (hv' : is_basis R v')
  (e : ι ≃ ι') : M ≃ₗ[R] M' :=
{ inv_fun := hv'.constr (v ∘ e.symm),
  left_inv := have (hv'.constr (v ∘ e.symm)).comp (hv.constr (v' ∘ e)) = linear_map.id,
      from hv.ext $ by simp,
    λ x, congr_arg (λ h : M →ₗ[R] M, h x) this,
  right_inv := have (hv.constr (v' ∘ e)).comp (hv'.constr (v ∘ e.symm)) = linear_map.id,
      from hv'.ext $ by simp,
    λ y, congr_arg (λ h : M' →ₗ[R] M', h y) this,
  ..hv.constr (v' ∘ e) }

/-- Isomorphism between the two modules, given two modules `M` and `M'` with respective bases
`v` and `v'` and a bijection between the two bases. -/
def equiv_of_is_basis' {v : ι → M} {v' : ι' → M'} (f : M → M') (g : M' → M)
  (hv : is_basis R v) (hv' : is_basis R v')
  (hf : ∀i, f (v i) ∈ range v') (hg : ∀i, g (v' i) ∈ range v)
  (hgf : ∀i, g (f (v i)) = v i) (hfg : ∀i, f (g (v' i)) = v' i) :
  M ≃ₗ M' :=
{ inv_fun := hv'.constr (g ∘ v'),
  left_inv :=
    have (hv'.constr (g ∘ v')).comp (hv.constr (f ∘ v)) = linear_map.id,
    from hv.ext $ λ i, exists.elim (hf i)
      (λ i' hi', by simp [constr_basis, hi'.symm]; rw [hi', hgf]),
    λ x, congr_arg (λ h:M →ₗ[R] M, h x) this,
  right_inv :=
    have (hv.constr (f ∘ v)).comp (hv'.constr (g ∘ v')) = linear_map.id,
    from hv'.ext $ λ i', exists.elim (hg i')
      (λ i hi, by simp [constr_basis, hi.symm]; rw [hi, hfg]),
    λ y, congr_arg (λ h:M' →ₗ[R] M', h y) this,
  ..hv.constr (f ∘ v) }

lemma is_basis_inl_union_inr {v : ι → M} {v' : ι' → M'}
  (hv : is_basis R v) (hv' : is_basis R v') :
  is_basis R (sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) :=
begin
  split,
  apply linear_independent_inl_union_inr' hv.1 hv'.1,
  rw [sum.elim_range, span_union,
      set.range_comp, span_image (inl R M M'), hv.2,  map_top,
      set.range_comp, span_image (inr R M M'), hv'.2, map_top],
  exact linear_map.sup_range_inl_inr
end

end is_basis

lemma is_basis_singleton_one (R : Type*) [unique ι] [ring R] :
  is_basis R (λ (_ : ι), (1 : R)) :=
begin
  split,
  { refine linear_independent_iff.2 (λ l, _),
    rw [finsupp.unique_single l, finsupp.total_single, smul_eq_mul, mul_one],
    intro hi,
    simp [hi] },
  { refine top_unique (λ _ _, _),
    simp [submodule.mem_span_singleton] }
end

protected lemma linear_equiv.is_basis (hs : is_basis R v)
  (f : M ≃ₗ[R] M') : is_basis R (f ∘ v) :=
begin
  split,
  { apply @linear_independent.image _ _ _ _ _ _ _ _ _ _ hs.1 (f : M →ₗ[R] M'),
    simp [linear_equiv.ker f] },
  { rw set.range_comp,
    have : span R ((f : M →ₗ[R] M') '' range v) = ⊤,
    { rw [span_image (f : M →ₗ[R] M'), hs.2],
      simp },
    exact this }
end

lemma is_basis_span (hs : linear_independent R v) :
  @is_basis ι R (span R (range v)) (λ i : ι, ⟨v i, subset_span (mem_range_self _)⟩) _ _ _ :=
begin
split,
{ apply linear_independent_span hs },
{ rw eq_top_iff',
  intro x,
  have h₁ : subtype.val '' set.range (λ i, subtype.mk (v i) _) = range v,
    by rw ←set.range_comp,
  have h₂ : map (submodule.subtype _) (span R (set.range (λ i, subtype.mk (v i) _)))
              = span R (range v),
    by rw [←span_image, submodule.subtype_eq_val, h₁],
  have h₃ : (x : M) ∈ map (submodule.subtype _) (span R (set.range (λ i, subtype.mk (v i) _))),
    by rw h₂; apply subtype.mem x,
  rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩,
  have h_x_eq_y : x = y,
    by rw [subtype.ext_iff, ← hy₂]; simp,
  rw h_x_eq_y,
  exact hy₁ }
end

lemma is_basis_empty (h_empty : ¬ nonempty ι) (h : ∀x:M, x = 0) : is_basis R (λ x : ι, (0 : M)) :=
⟨ linear_independent_empty_type h_empty,
  eq_top_iff'.2 $ assume x, (h x).symm ▸ submodule.zero_mem _ ⟩

lemma is_basis_empty_bot (h_empty : ¬ nonempty ι) :
  is_basis R (λ _ : ι, (0 : (⊥ : submodule R M))) :=
begin
  apply is_basis_empty h_empty,
  intro x,
  apply subtype.ext_iff_val.2,
  exact (submodule.mem_bot R).1 (subtype.mem x),
end

open fintype
variables [fintype ι] (h : is_basis R v)

/-- A module over `R` with a finite basis is linearly equivalent to functions from its basis to `R`.
-/
def equiv_fun_basis  : M ≃ₗ[R] (ι → R) :=
linear_equiv.trans (module_equiv_finsupp h)
  { to_fun := finsupp.to_fun,
    map_add' := λ x y, by ext; exact finsupp.add_apply,
    map_smul' := λ x y, by ext; exact finsupp.smul_apply,
    ..finsupp.equiv_fun_on_fintype }

/-- A module over a finite ring that admits a finite basis is finite. -/
def module.fintype_of_fintype [fintype R] : fintype M :=
fintype.of_equiv _ (equiv_fun_basis h).to_equiv.symm

theorem module.card_fintype [fintype R] [fintype M] :
  card M = (card R) ^ (card ι) :=
calc card M = card (ι → R)    : card_congr (equiv_fun_basis h).to_equiv
        ... = card R ^ card ι : card_fun

/-- Given a basis `v` indexed by `ι`, the canonical linear equivalence between `ι → R` and `M` maps
a function `x : ι → R` to the linear combination `∑_i x i • v i`. -/
@[simp] lemma equiv_fun_basis_symm_apply (x : ι → R) :
  (equiv_fun_basis h).symm x = ∑ i, x i • v i :=
begin
  change finsupp.sum
      ((finsupp.equiv_fun_on_fintype.symm : (ι → R) ≃ (ι →₀ R)) x) (λ (i : ι) (a : R), a • v i)
    = ∑ i, x i • v i,
  dsimp [finsupp.equiv_fun_on_fintype, finsupp.sum],
  rw finset.sum_filter,
  refine finset.sum_congr rfl (λi hi, _),
  by_cases H : x i = 0,
  { simp [H] },
  { simp [H], refl }
end

end module

section vector_space
variables
  {v : ι → V}
  [field K] [add_comm_group V] [add_comm_group V']
  [vector_space K V] [vector_space K V']
  {s t : set V} {x y z : V}
include K
open submodule

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
   (instead of a data containing type class) -/

section

lemma mem_span_insert_exchange : x ∈ span K (insert y s) → x ∉ span K s → y ∈ span K (insert x s) :=
begin
  simp [mem_span_insert],
  rintro a z hz rfl h,
  refine ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, _⟩,
  have a0 : a ≠ 0, {rintro rfl, simp * at *},
  simp [a0, smul_add, smul_smul]
end

end

lemma linear_independent_iff_not_mem_span :
  linear_independent K v ↔ (∀i, v i ∉ span K (v '' (univ \ {i}))) :=
begin
  apply linear_independent_iff_not_smul_mem_span.trans,
  split,
  { intros h i h_in_span,
    apply one_ne_zero (h i 1 (by simp [h_in_span])) },
  { intros h i a ha,
    by_contradiction ha',
    exact false.elim (h _ ((smul_mem_iff _ ha').1 ha)) }
end

lemma linear_independent_unique [unique ι] (h : v (default ι) ≠ 0): linear_independent K v :=
begin
  rw linear_independent_iff,
  intros l hl,
  ext i,
  rw [unique.eq_default i, finsupp.zero_apply],
  by_contra hc,
  have := smul_smul (l (default ι))⁻¹ (l (default ι)) (v (default ι)),
  rw [finsupp.unique_single l, finsupp.total_single] at hl,
  rw [hl, inv_mul_cancel hc, smul_zero, one_smul] at this,
  exact h this.symm
end

lemma linear_independent_singleton {x : V} (hx : x ≠ 0) :
  linear_independent K (λ x, x : ({x} : set V) → V) :=
begin
  apply @linear_independent_unique _ _ _ _ _ _ _ _ _,
  apply set.unique_singleton,
  apply hx,
end

lemma disjoint_span_singleton {p : submodule K V} {x : V} (x0 : x ≠ 0) :
  disjoint p (span K {x}) ↔ x ∉ p :=
⟨λ H xp, x0 (disjoint_def.1 H _ xp (singleton_subset_iff.1 subset_span:_)),
begin
  simp [disjoint_def, mem_span_singleton],
  rintro xp y yp a rfl,
  by_cases a0 : a = 0, {simp [a0]},
  exact xp.elim ((smul_mem_iff p a0).1 yp),
end⟩

lemma linear_independent.insert (hs : linear_independent K (λ b, b : s → V)) (hx : x ∉ span K s) :
  linear_independent K (λ b, b : insert x s → V) :=
begin
  rw ← union_singleton,
  have x0 : x ≠ 0 := mt (by rintro rfl; apply zero_mem _) hx,
  apply hs.union (linear_independent_singleton x0),
  rwa [disjoint_span_singleton x0]
end

lemma exists_linear_independent (hs : linear_independent K (λ x, x : s → V)) (hst : s ⊆ t) :
  ∃b⊆t, s ⊆ b ∧ t ⊆ span K b ∧ linear_independent K (λ x, x : b → V) :=
begin
  rcases zorn.zorn_subset₀ {b | b ⊆ t ∧ linear_independent K (λ x, x : b → V)} _ _
    ⟨hst, hs⟩ with ⟨b, ⟨bt, bi⟩, sb, h⟩,
  { refine ⟨b, bt, sb, λ x xt, _, bi⟩,
    by_contra hn,
    apply hn,
    rw ← h _ ⟨insert_subset.2 ⟨xt, bt⟩, bi.insert hn⟩ (subset_insert _ _),
    exact subset_span (mem_insert _ _) },
  { refine λ c hc cc c0, ⟨⋃₀ c, ⟨_, _⟩, λ x, _⟩,
    { exact sUnion_subset (λ x xc, (hc xc).1) },
    { exact linear_independent_sUnion_of_directed cc.directed_on (λ x xc, (hc xc).2) },
    { exact subset_sUnion_of_mem } }
end

lemma exists_subset_is_basis (hs : linear_independent K (λ x, x : s → V)) :
  ∃b, s ⊆ b ∧ is_basis K (coe : b → V) :=
let ⟨b, hb₀, hx, hb₂, hb₃⟩ := exists_linear_independent hs (@subset_univ _ _) in
⟨ b, hx,
  @linear_independent.restrict_of_comp_subtype _ _ _ id _ _ _ _ hb₃,
  by simp; exact eq_top_iff.2 hb₂⟩

lemma exists_sum_is_basis (hs : linear_independent K v) :
  ∃ (ι' : Type u) (v' : ι' → V), is_basis K (sum.elim v v') :=
begin
  -- This is a hack: we jump through hoops to reuse `exists_subset_is_basis`.
  let s := set.range v,
  let e : ι ≃ s := equiv.set.range v (hs.injective zero_ne_one),
  have : (λ x, x : s → V) = v ∘ e.symm := by { funext, dsimp, rw [equiv.set.apply_range_symm v], },
  have : linear_independent K (λ x, x : s → V),
  { rw this,
    exact linear_independent.comp hs _ (e.symm.injective), },
  obtain ⟨b, ss, is⟩ := exists_subset_is_basis this,
  let e' : ι ⊕ (b \ s : set V) ≃ b :=
  calc ι ⊕ (b \ s : set V) ≃ s ⊕ (b \ s : set V) : equiv.sum_congr e (equiv.refl _)
                       ... ≃ b                   : equiv.set.sum_diff_subset ss,
  refine ⟨(b \ s : set V), λ x, x.1, _⟩,
  convert is_basis.comp is e' _,
  { funext x,
    cases x; simp; refl, },
  { exact e'.bijective, },
end

variables (K V)
lemma exists_is_basis : ∃b : set V, is_basis K (λ i, i : b → V) :=
let ⟨b, _, hb⟩ := exists_subset_is_basis (linear_independent_empty K V : _) in ⟨b, hb⟩

variables {K V}

-- TODO(Mario): rewrite?
lemma exists_of_linear_independent_of_finite_span {t : finset V}
  (hs : linear_independent K (λ x, x : s → V)) (hst : s ⊆ (span K ↑t : submodule K V)) :
  ∃t':finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = t.card :=
have ∀t, ∀(s' : finset V), ↑s' ⊆ s → s ∩ ↑t = ∅ → s ⊆ (span K ↑(s' ∪ t) : submodule K V) →
  ∃t':finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = (s' ∪ t).card :=
assume t, finset.induction_on t
  (assume s' hs' _ hss',
    have s = ↑s',
      from eq_of_linear_independent_of_span_subtype zero_ne_one hs hs' $
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
      (assume : s ⊆ (span K ↑(s' ∪ t) : submodule K V),
        let ⟨u, hust, hsu, eq⟩ := ih _ hs' hst this in
        have hb₁u : b₁ ∉ u, from assume h, (hust h).elim hb₁s hb₁t,
        ⟨insert b₁ u, by simp [insert_subset_insert hust],
          subset.trans hsu (by simp), by simp [eq, hb₁t, hb₁s', hb₁u]⟩)
      (assume : ¬ s ⊆ (span K ↑(s' ∪ t) : submodule K V),
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this in
        have hb₂t' : b₂ ∉ s' ∪ t, from assume h, hb₂t $ subset_span h,
        have s ⊆ (span K ↑(insert b₂ s' ∪ t) : submodule K V), from
          assume b₃ hb₃,
          have ↑(s' ∪ insert b₁ t) ⊆ insert b₁ (insert b₂ ↑(s' ∪ t) : set V),
            by simp [insert_eq, -singleton_union, -union_singleton, union_subset_union, subset.refl, subset_union_right],
          have hb₃ : b₃ ∈ span K (insert b₁ (insert b₂ ↑(s' ∪ t) : set V)),
            from span_mono this (hss' hb₃),
          have s ⊆ (span K (insert b₁ ↑(s' ∪ t)) : submodule K V),
            by simpa [insert_eq, -singleton_union, -union_singleton] using hss',
          have hb₁ : b₁ ∈ span K (insert b₂ ↑(s' ∪ t)),
            from mem_span_insert_exchange (this hb₂s) hb₂t,
          by rw [span_insert_eq_span hb₁] at hb₃; simpa using hb₃,
        let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [insert_subset, hb₂s, hs']) hst this in
        ⟨u, subset.trans hust $ union_subset_union (subset.refl _) (by simp [subset_insert]),
          hsu, by simp [eq, hb₂t', hb₁t, hb₁s']⟩)),
begin
  have eq : t.filter (λx, x ∈ s) ∪ t.filter (λx, x ∉ s) = t,
  { ext1 x,
    by_cases x ∈ s; simp * },
  apply exists.elim (this (t.filter (λx, x ∉ s)) (t.filter (λx, x ∈ s))
    (by simp [set.subset_def]) (by simp [set.ext_iff] {contextual := tt}) (by rwa [eq])),
  intros u h,
  exact ⟨u, subset.trans h.1 (by simp [subset_def, and_imp, or_imp_distrib] {contextual:=tt}),
    h.2.1, by simp only [h.2.2, eq]⟩
end

lemma exists_finite_card_le_of_finite_of_linear_independent_of_span
  (ht : finite t) (hs : linear_independent K (λ x, x : s → V)) (hst : s ⊆ span K t) :
  ∃h : finite s, h.to_finset.card ≤ ht.to_finset.card :=
have s ⊆ (span K ↑(ht.to_finset) : submodule K V), by simp; assumption,
let ⟨u, hust, hsu, eq⟩ := exists_of_linear_independent_of_finite_span hs this in
have finite s, from u.finite_to_set.subset hsu,
⟨this, by rw [←eq]; exact (finset.card_le_of_subset $ finset.coe_subset.mp $ by simp [hsu])⟩

lemma linear_map.exists_left_inverse_of_injective (f : V →ₗ[K] V')
  (hf_inj : f.ker = ⊥) : ∃g:V' →ₗ V, g.comp f = linear_map.id :=
begin
  rcases exists_is_basis K V with ⟨B, hB⟩,
  have hB₀ : _ := hB.1.to_subtype_range,
  have : linear_independent K (λ x, x : f '' B → V'),
  { have h₁ := hB₀.image_subtype
      (show disjoint (span K (range (λ i : B, i.val))) (linear_map.ker f), by simp [hf_inj]),
    rwa subtype.range_coe at h₁ },
  rcases exists_subset_is_basis this with ⟨C, BC, hC⟩,
  haveI : inhabited V := ⟨0⟩,
  use hC.constr (C.restrict (inv_fun f)),
  refine hB.ext (λ b, _),
  rw image_subset_iff at BC,
  have : f b = (⟨f b, BC b.2⟩ : C) := rfl,
  dsimp,
  rw [this, constr_basis hC],
  exact left_inverse_inv_fun (linear_map.ker_eq_bot.1 hf_inj) _
end

lemma submodule.exists_is_compl (p : submodule K V) : ∃ q : submodule K V, is_compl p q :=
let ⟨f, hf⟩ := p.subtype.exists_left_inverse_of_injective p.ker_subtype in
⟨f.ker, linear_map.is_compl_of_proj $ linear_map.ext_iff.1 hf⟩

lemma linear_map.exists_right_inverse_of_surjective (f : V →ₗ[K] V')
  (hf_surj : f.range = ⊤) : ∃g:V' →ₗ V, f.comp g = linear_map.id :=
begin
  rcases exists_is_basis K V' with ⟨C, hC⟩,
  haveI : inhabited V := ⟨0⟩,
  use hC.constr (C.restrict (inv_fun f)),
  refine hC.ext (λ c, _),
  simp [constr_basis hC, right_inverse_inv_fun (linear_map.range_eq_top.1 hf_surj) c]
end

open submodule linear_map

theorem quotient_prod_linear_equiv (p : submodule K V) :
  nonempty ((p.quotient × p) ≃ₗ[K] V) :=
let ⟨q, hq⟩ := p.exists_is_compl in nonempty.intro $
((quotient_equiv_of_is_compl p q hq).prod (linear_equiv.refl _ _)).trans
  (prod_equiv_of_is_compl q p hq.symm)

open fintype
variables (K) (V)

theorem vector_space.card_fintype [fintype K] [fintype V] :
  ∃ n : ℕ, card V = (card K) ^ n :=
exists.elim (exists_is_basis K V) $ λ b hb, ⟨card b, module.card_fintype hb⟩

end vector_space

namespace pi
open set linear_map

section module
variables {η : Type*} {ιs : η → Type*} {Ms : η → Type*}
variables [ring R] [∀i, add_comm_group (Ms i)] [∀i, module R (Ms i)]

lemma linear_independent_std_basis
  (v : Πj, ιs j → (Ms j)) (hs : ∀i, linear_independent R (v i)) :
  linear_independent R (λ (ji : Σ j, ιs j), std_basis R Ms ji.1 (v ji.1 ji.2)) :=
begin
  have hs' : ∀j : η, linear_independent R (λ i : ιs j, std_basis R Ms j (v j i)),
  { intro j,
    apply linear_independent.image (hs j),
    simp [ker_std_basis] },
  apply linear_independent_Union_finite hs',
  { assume j J _ hiJ,
    simp [(set.Union.equations._eqn_1 _).symm, submodule.span_image, submodule.span_Union],
    have h₀ : ∀ j, span R (range (λ (i : ιs j), std_basis R Ms j (v j i)))
        ≤ range (std_basis R Ms j),
    { intro j,
      rw [span_le, linear_map.range_coe],
      apply range_comp_subset_range },
    have h₁ : span R (range (λ (i : ιs j), std_basis R Ms j (v j i)))
        ≤ ⨆ i ∈ {j}, range (std_basis R Ms i),
    { rw @supr_singleton _ _ _ (λ i, linear_map.range (std_basis R (λ (j : η), Ms j) i)),
      apply h₀ },
    have h₂ : (⨆ j ∈ J, span R (range (λ (i : ιs j), std_basis R Ms j (v j i)))) ≤
               ⨆ j ∈ J, range (std_basis R (λ (j : η), Ms j) j) :=
      supr_le_supr (λ i, supr_le_supr (λ H, h₀ i)),
    have h₃ : disjoint (λ (i : η), i ∈ {j}) J,
    { convert set.disjoint_singleton_left.2 hiJ,
      rw ←@set_of_mem_eq _ {j},
      refl },
    exact (disjoint_std_basis_std_basis _ _ _ _ h₃).mono h₁ h₂ }
end

variable [fintype η]

lemma is_basis_std_basis (s : Πj, ιs j → (Ms j)) (hs : ∀j, is_basis R (s j)) :
  is_basis R (λ (ji : Σ j, ιs j), std_basis R Ms ji.1 (s ji.1 ji.2)) :=
begin
  split,
  { apply linear_independent_std_basis _ (assume i, (hs i).1) },
  have h₁ : Union (λ j, set.range (std_basis R Ms j ∘ s j))
    ⊆ range (λ (ji : Σ (j : η), ιs j), (std_basis R Ms (ji.fst)) (s (ji.fst) (ji.snd))),
  { apply Union_subset, intro i,
    apply range_comp_subset_range (λ x : ιs i, (⟨i, x⟩ : Σ (j : η), ιs j))
        (λ (ji : Σ (j : η), ιs j), std_basis R Ms (ji.fst) (s (ji.fst) (ji.snd))) },
  have h₂ : ∀ i, span R (range (std_basis R Ms i ∘ s i)) = range (std_basis R Ms i),
  { intro i,
    rw [set.range_comp, submodule.span_image, (assume i, (hs i).2), submodule.map_top] },
  apply eq_top_mono,
  apply span_mono h₁,
  rw span_Union,
  simp only [h₂],
  apply supr_range_std_basis
end

section
variables (R η)

lemma is_basis_fun₀ : is_basis R
    (λ (ji : Σ (j : η), unit),
       (std_basis R (λ (i : η), R) (ji.fst)) 1) :=
@is_basis_std_basis R η (λi:η, unit) (λi:η, R) _ _ _ _ (λ _ _, (1 : R))
  (assume i, @is_basis_singleton_one _ _ _ _)

lemma is_basis_fun : is_basis R (λ i, std_basis R (λi:η, R) i 1) :=
begin
  apply (is_basis_fun₀ R η).comp (λ i, ⟨i, punit.star⟩),
  apply bijective_iff_has_inverse.2,
  use sigma.fst,
  suffices : ∀ (a : η) (b : unit), punit.star = b,
  { simpa [function.left_inverse, function.right_inverse] },
  exact λ _, punit_eq _
end

end

end module

end pi
