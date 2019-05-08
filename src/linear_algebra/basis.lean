/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Linear independence and basis sets in a module or vector space.

This file is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define the following concepts:

* `linear_independent α v s`: states that the elements indexed by `s` are linear independent

* `linear_independent.repr s b`: choose the linear combination representing `b` on the linear
  independent vectors `s`. `b` should be in `span α b` (uses classical choice)

* `is_basis α s`: if `s` is a basis, i.e. linear independent and spans the entire space

* `is_basis.repr s b`: like `linear_independent.repr` but as a `linear_map`

* `is_basis.constr s g`: constructs a `linear_map` by extending `g` from the basis `s`

-/
import linear_algebra.basic linear_algebra.finsupp order.zorn
noncomputable theory

open function lattice set submodule

variables {ι : Type*} {ι' : Type*} {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
          {v : ι → β}
variables [decidable_eq ι] [decidable_eq ι'] [decidable_eq α] [decidable_eq β] [decidable_eq γ] [decidable_eq δ]

section module
variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
variables {a b : α} {x y : β}
include α



section indexed
variables {s t : set ι}

variables (α) (v)
/-- Linearly independent set of vectors -/
def linear_independent (s : set ι) : Prop :=
disjoint (finsupp.supported α α s) (finsupp.total ι β α v).ker
variables {α} {v}

theorem linear_independent_iff : linear_independent α v s ↔
  ∀l ∈ finsupp.supported α α s, finsupp.total ι β α v l = 0 → l = 0 :=
by simp [linear_independent, linear_map.disjoint_ker]

theorem linear_independent_iff_total_on : linear_independent α v s ↔ (finsupp.total_on ι β α v s).ker = ⊥ :=
by rw [finsupp.total_on, linear_map.ker, linear_map.comap_cod_restrict, map_bot, comap_bot,
  linear_map.ker_comp, linear_independent, disjoint, ← map_comap_subtype, map_le_iff_le_comap,
  comap_bot, ker_subtype, le_bot_iff]

lemma linear_independent_empty : linear_independent α v (∅ : set ι) :=
by simp [linear_independent]

lemma linear_independent_empty_type (h : ¬ nonempty ι) : linear_independent α v univ :=
begin
 rw [linear_independent_iff],
 intros,
 ext i,
 exact false.elim (not_nonempty_iff_imp_false.1 h i)
end

lemma linear_independent.mono (h : t ⊆ s) : linear_independent α v s → linear_independent α v t :=
disjoint_mono_left (finsupp.supported_mono h)

lemma linear_independent.unique (hs : linear_independent α v s) {l₁ l₂ : ι  →₀ α} :
  l₁ ∈ finsupp.supported α α s → l₂ ∈ finsupp.supported α α s →
  finsupp.total ι β α v l₁ = finsupp.total ι β α v l₂ → l₁ = l₂ :=
linear_map.disjoint_ker'.1 hs _ _

lemma zero_not_mem_of_linear_independent
  {i : ι} (ne : 0 ≠ (1:α)) (hs : linear_independent α v s) (hi : v i = 0) :
    i ∉ s :=
λ h, ne $ eq.symm begin
  suffices : (finsupp.single i 1 : ι →₀ α) i = 0, {simpa},
  rw disjoint_def.1 hs _ (finsupp.single_mem_supported _ 1 h),
  {refl}, {simp [hi]}
end

lemma ne_zero_of_linear_independent
  {i : ι} (ne : 0 ≠ (1:α)) (hs : linear_independent α v univ) : v i ≠ 0 :=
λ h, ne $ eq.symm begin
  suffices : (finsupp.single i 1 : ι →₀ α) i = 0, {simpa},
  rw disjoint_def.1 hs _ (finsupp.single_mem_supported _ 1 (mem_univ _)),
  {refl}, {simp [h]}
end

lemma linear_independent_univ_iff :
  linear_independent α v univ ↔ (finsupp.total ι β α v).ker = ⊥ :=
by simp [linear_independent, disjoint_iff]

theorem linear_independent_univ_iff_inj : linear_independent α v univ ↔
  ∀l, finsupp.total ι β α v l = 0 → l = 0 :=
by simp [linear_independent_iff]

lemma linear_independent.comp_univ (f : ι' → ι) (hf : injective f)
  (h : linear_independent α v univ) : linear_independent α (v ∘ f) univ :=
begin
  rw [linear_independent_univ_iff_inj, finsupp.total_comp],
  intros l hl,
  have h_map_domain : ∀ x, (finsupp.map_domain f l) (f x) = 0,
    by rw linear_independent_univ_iff_inj.1 h (finsupp.map_domain f l) hl; simp,
  ext,
  simp,
  simp only [finsupp.map_domain_apply hf] at h_map_domain,
  apply h_map_domain
end

lemma linear_independent_union
  (hs : linear_independent α v s) (ht : linear_independent α v t)
  (hst : disjoint (span α (v '' s)) (span α (v '' t))) :
  linear_independent α v (s ∪ t) :=
begin
  rw [linear_independent, disjoint_def, finsupp.supported_union],
  intros l h₁ h₂, rw mem_sup at h₁,
  rcases h₁ with ⟨ls, hls, lt, hlt, rfl⟩,
  rw [finsupp.span_eq_map_total, finsupp.span_eq_map_total] at hst,
  have : finsupp.total ι β α v ls ∈ map (finsupp.total ι β α v) (finsupp.supported α α t),
  { apply (add_mem_iff_left (map _ _) (mem_image_of_mem _ hlt)).1,
    rw [← linear_map.map_add, linear_map.mem_ker.1 h₂],
    apply zero_mem },
  have ls0 := disjoint_def.1 hs _ hls (linear_map.mem_ker.2 $
    disjoint_def.1 hst _ (mem_image_of_mem _ hls) this),
  subst ls0, simp [-linear_map.mem_ker] at this h₂ ⊢,
  exact disjoint_def.1 ht _ hlt h₂
end

lemma linear_independent_of_finite
  (H : ∀ t ⊆ s, finite t → linear_independent α v t) :
  linear_independent α v s :=
linear_independent_iff.2 $ λ l hl,
linear_independent_iff.1 (H _ hl (finset.finite_to_set _)) l (subset.refl _)

lemma linear_independent_Union_of_directed {η : Type*}
  {s : η → set ι} (hs : directed (⊆) s)
  (h : ∀ i, linear_independent α v (s i)) : linear_independent α v (⋃ i, s i) :=
begin
  haveI := classical.dec (nonempty η),
  by_cases hη : nonempty η,
  { refine linear_independent_of_finite (λ t ht ft, _),
    rcases finite_subset_Union ft ht with ⟨I, fi, hI⟩,
    rcases hs.finset_le hη fi.to_finset with ⟨i, hi⟩,
    exact (h i).mono (subset.trans hI $ bUnion_subset $
      λ j hj, hi j (finite.mem_to_finset.2 hj)) },
  { refine linear_independent_empty.mono _,
    rintro _ ⟨_, ⟨i, _⟩, _⟩, exact hη ⟨i⟩ }
end

lemma linear_independent_sUnion_of_directed {s : set (set ι)}
  (hs : directed_on (⊆) s)
  (h : ∀ a ∈ s, linear_independent α v a) : linear_independent α v (⋃₀ s) :=
by rw sUnion_eq_Union; exact
linear_independent_Union_of_directed
  ((directed_on_iff_directed _).1 hs) (by simpa using h)

lemma linear_independent_bUnion_of_directed {η} {s : set η} {t : η → set ι}
  (hs : directed_on (t ⁻¹'o (⊆)) s) (h : ∀a∈s, linear_independent α v (t a)) :
  linear_independent α v (⋃a∈s, t a) :=
by rw bUnion_eq_Union; exact
linear_independent_Union_of_directed
  ((directed_comp _ _ _).2 $ (directed_on_iff_directed _).1 hs)
  (by simpa using h)

def restrict' {α β} (f : α → β) (s : set α) : s → β := λ x, f x.val

lemma restrict_apply {α : Type*} (f : α → β) (s : set α) (a : subtype s) : restrict' f s a = f a := rfl

lemma image_restrict {α β : Type*} (f : α → β) (s : set α) (t : set s) :
  restrict' f s '' t = f '' (subtype.val '' t) :=
begin
  ext,
  simp [mem_image],
  unfold restrict',
  split,
  { intros h,
    rcases h with ⟨a,ha₁,ha₂,ha₃⟩,
    use a,
    use ha₁,
    use ha₂,
    exact ha₃ },
  { intros h,
    rcases h with ⟨a,⟨ha₁,ha₂⟩,ha₃⟩,
    use a,
    use ha₁,
    exact ⟨ha₂, ha₃⟩ }
end

lemma subtype.val_image_diff {α : Type*} {p : α → Prop} (s t : set (subtype p)) :
  subtype.val '' (s \ t) = (subtype.val '' s \ subtype.val '' t) :=
begin
  ext x,
  rw mem_diff,
  rw mem_image,
  split,
  { intro h,
    split,
    apply mono_image (diff_subset _ _) h,
    intro h',
    rcases h with ⟨a, ⟨ha₁, ha₂⟩⟩,
    rcases h' with ⟨b, ⟨hb₁, hb₂⟩⟩,
    apply not_mem_of_mem_diff ha₁,
    convert hb₁,
    apply subtype.eq',
    rw [ha₂, hb₂] },
  { intro h,
    simp only [mem_image] at h,
    simp only [not_exists, not_and'] at h,
    rcases h.1 with ⟨a , ha⟩,
    use a,
    exact ⟨(mem_diff _).2 ⟨ha.1, h.2 _ ha.2⟩, ha.2⟩ }
end

-- TODO remove
lemma smul_mem_span {α β : Type*} [ring α] [add_comm_group β] [module α β]
  (a : α) {x : β} {s : set β} (h : x ∈ span α s) :
  a • x ∈ span α s :=
submodule.smul _ _ h --mem_span.2 (λ p hp, smul_mem _ _ (mem_span.1 h _ hp))

lemma finsupp.eq_zero_of_zero_eq_one {ι α : Type*} [ring α] (zero_eq_one : (0 : α) = 1) (l : ι →₀ α) : l = 0 :=
  by ext i; simp [eq_zero_of_zero_eq_one α zero_eq_one (l i)]

lemma linear_independent_of_zero_eq_one (zero_eq_one : (0 : α) = 1) : linear_independent α v s :=
begin
  rw linear_independent_iff,
  intros,
  apply finsupp.eq_zero_of_zero_eq_one zero_eq_one,
end

-- TODO: Strengthen "hd" to what it was before?
lemma linear_independent_Union_finite {η : Type*} {ιs : η → Type*}
  [decidable_eq η] [∀ j, decidable_eq (ιs j)]
  {f : Π j : η, ιs j → β}
  (hindep : ∀j, linear_independent α (f j) univ)
  --(zero_ne_one : (0 : α) ≠ 1)
  --(hd : ∀i, ∀t:set η, finite t → i ∉ t →
  --disjoint (span α (range (f i))) (⨆i∈t, span α (range (f i))))
  (hd : ∀ (s : set η) (g : s → β), (finite s) → (∀ i : s, g i ∈ span α (range (f i))) →
        ∀ l : s →₀ α, finsupp.total s β α g l = 0 → ∀ j : s, l j • g j = 0)
  :
  linear_independent α (λ ji : Σ j, ιs j, f ji.1 ji.2) univ :=
begin
  by_cases zero_eq_one : (0 : α) = 1,
  { apply linear_independent_of_zero_eq_one zero_eq_one },
  have zero_ne_one: (0 : α) ≠ 1,
    from zero_eq_one,
  simp only [linear_independent_univ_iff_inj, finsupp.total_apply, finsupp.lsum_apply, finsupp.sigma_sum],
  intros l hl,
  let subsums := λ i, finsupp.sum (finsupp.split l i) (λ (a : ιs i) (b : α), b • f i a),
  have h_subsums_in_span : ∀ i, subsums i ∈ span α (range (f i)),
  { intros i,
    dsimp [subsums],
    unfold finsupp.sum,
    haveI := classical.dec_eq (ιs i),
    apply sum_mem _ _,
    assumption,
    intros a ha,
    apply smul_mem _ _ _,
    apply subset_span (mem_range_self _) },
  have h_subsums_neq_0: ∀ i ∈ (finsupp.split_support l), subsums i ≠ 0,
  { simp only [linear_independent_univ_iff_inj, finsupp.total_apply, finsupp.lsum_apply] at hindep,
    intros i hi_mem hi0,
    rw finsupp.mem_split_support_iff_nonzero at hi_mem,
    exact hi_mem (hindep i (finsupp.split l i) hi0) },
  have h_image_subsums : ∀ t, subsums '' t ⊆ span α (⋃i∈t, range (f i)),
  { intros t x hx,
    rw mem_image at hx,
    rcases hx with ⟨i, hi₁, hi₂⟩,
    rw ←hi₂,
    apply span_mono _ (h_subsums_in_span i),
    apply subset_bUnion_of_mem hi₁ },
  /-have h_linindep_subsums : linear_independent α (restrict' subsums ↑(finsupp.split_support l)) univ,
  { rw linear_independent_iff_not_smul_mem_span,
    intros i hi a h_subsums_in_span',
    by_contradiction,
    apply h_subsums_neq_0 i (finset.mem_coe.1 (subtype.mem _)),
    have := disjoint_def.1 (hd i (↑(finsupp.split_support l) \ {i})
      (set.finite_subset (finset.finite_to_set _) (set.diff_subset _ _))
      (by simp)) (a • subsums i) (smul_mem_span a (h_subsums_in_span i)),
    rw restrict_apply at h_subsums_in_span',
    rw [image_restrict subsums ↑(finsupp.split_support l), subtype.val_image_diff,
        image_singleton, subtype.val_image_univ] at h_subsums_in_span',
    rw ←span_span,
    apply span_mono (h_image_subsums _),
    have := h_subsums_in_span', },-/
  /-have h_linindep_subsums : linear_independent α (restrict' subsums ↑(finsupp.split_support l)) univ,
  {
    apply hd _ _ (finset.finite_to_set (finsupp.split_support l)),
    intros i,
    rw restrict_apply,
    apply h_subsums_in_span
  },-/
  haveI : has_lift (finset α) (set α) := ⟨finset.to_set⟩,
  let const1 : (↑(finsupp.split_support l) : set η) →₀ α :=
    finsupp.on_finset finset.univ (λ _, (1 : α)) (λ _ _, finset.mem_univ _),
  have h_const_smul_subsums_eq_0 : ∀ j : (finsupp.split_support l).to_set, const1 j • subsums j = 0,
  { intros j,
    apply hd,
    { apply finset.finite_to_set },
    { intro i,
      apply h_subsums_in_span },
    simp [finsupp.total_apply],
    unfold finsupp.sum,
    simp [finsupp.on_finset, restrict_apply],
    rw ←hl,
    convert (finset.sum_image _).symm,
    { dsimp only [const1, finsupp.on_finset],
      simp [zero_ne_one.symm],
      apply finset.coe_inj.1,
      simp,
      refl },
    { assumption },
    { intros _ _ _ _ h,
      apply subtype.eq',
      exact h } },
  have h_const_eq_0 : const1 = 0,
  {
    ext j,
    have := h_const_smul_subsums_eq_0 j,
    simp [const1, finsupp.to_fun, finsupp.on_finset] at this,
    exfalso,
    apply h_subsums_neq_0 j (subtype.mem j) this,
  },
  have h_split_support : finsupp.split_support l = finset.image (λ (x : (finsupp.split_support l).to_set), ↑x) const1.support,
  { dsimp only [const1, finsupp.on_finset],
    simp [zero_ne_one.symm],
    apply finset.coe_inj.1,
    simp,
    refl -- <- TODO: this is repeated above, maybe separate "have"?
    },
  have h_split_support_empty: finsupp.split_support l = ∅,
  { rw [h_split_support, h_const_eq_0],
    simp,
    refl },
  { unfold finsupp.split_support at h_split_support_empty,
    rwa [finset.image_eq_empty, finsupp.support_eq_empty] at h_split_support_empty }
end

section repr
variables (hs : linear_independent α v s)

lemma linear_independent.injective (zero_ne_one : (0 : α) ≠ 1)
  (hs : linear_independent α v s) (i j : ι) (hi : i ∈ s) (hi : j ∈ s)
  (hij: v i = v j) : i = j :=
begin
  let l : ι →₀ α := finsupp.single i (1 : α) - finsupp.single j 1,
  have h_supp : l ∈ finsupp.supported α α s,
  { dsimp only [l],
    rw [finsupp.mem_supported],
    intros k hk,
    apply or.elim (finset.mem_union.1 (finsupp.support_add (finset.mem_coe.1 hk))),
    { intro hk',
      rwa finset.mem_singleton.1 (finsupp.support_single_subset hk') },
    { intro hk',
      rw finsupp.support_neg at hk',
      rwa finset.mem_singleton.1 (finsupp.support_single_subset hk') } },
  have h_total : finsupp.total ι β α v l = 0,
  { rw finsupp.total_apply,
    rw finsupp.sum_sub_index,
    { simp [finsupp.sum_single_index, hij] },
    { intros, apply sub_smul } },
  have h_single_eq : finsupp.single i (1 : α) = finsupp.single j 1,
  { rw linear_independent_iff at hs,
    simp [eq_add_of_sub_eq' (hs l h_supp h_total)] },
  show i = j,
  { apply or.elim ((finsupp.single_eq_single_iff _ _ _ _).1 h_single_eq),
    simp,
    exact λ h, false.elim (zero_ne_one.symm h.1) }
end


lemma linear_independent.injective' (zero_ne_one : (0 : α) ≠ 1)
  (hv : linear_independent α v univ) : injective v :=
begin
  intros x y hxy,
  apply linear_independent.injective zero_ne_one hv,
  simp,
  simp,
  assumption
end


/-
lemma linear_independent.id_of_univ (zero_ne_one : (0 : α) ≠ 1)
  (h : linear_independent α v univ) : linear_independent α (subtype.val : range v → β) univ :=
  sorry
-/

lemma linear_independent.id_of_univ
  (h : linear_independent α v univ) : linear_independent α id (range v) :=
begin
  by_cases zero_eq_one : (0 : α) = 1,
  { apply linear_independent_of_zero_eq_one zero_eq_one },
  rw linear_independent_iff,
  intros l hl₁ hl₂,
  have h_bij : bij_on v (v ⁻¹' finset.to_set (l.support)) (finset.to_set (l.support)),
  {
    apply bij_on.mk,
    { rw maps_to',
      apply image_preimage_subset },
    { unfold inj_on,
      intros i₁ i₂ hi₁ hi₂ hi,
      apply linear_independent.injective zero_eq_one h _ _ (mem_univ _) (mem_univ _) hi,
     },
    { intros x hx,
      apply exists.elim (mem_range.1 ((finsupp.mem_supported α l).2 hl₁ hx)),
      intros x' hx',
      rw mem_image,
      use x',
      split,
      { rwa [mem_preimage_eq, hx'] },
      { exact hx' } },
  },
  rw linear_independent_univ_iff_inj at h,
  rw finsupp.total_apply at hl₂,
  rw finsupp.sum at hl₂,
  have := h (finsupp.comap_domain v l (set.inj_on_of_bij_on h_bij)),
  rw finsupp.total_comap_domain at this,
  apply finsupp.eq_zero_of_comap_domain_eq_zero _ _ h_bij,
  rw finset.sum_preimage v l.support h_bij (λ (x : β), l x • x) at this,
  exact this hl₂,
end

lemma linear_independent.univ_of_id (hv : injective v)
  (h : linear_independent α id (range v)) : linear_independent α v univ :=
begin
  rw linear_independent_iff at *,
  intros l hl₁ hl₂,
  apply finsupp.injective_map_domain hv,
  apply h (l.map_domain v),
  { rw finsupp.mem_supported,
    intros x hx,
    have := finset.mem_coe.2 (finsupp.map_domain_support hx),
    rw finset.coe_image at this,
    apply set.image_subset_range _ _ this },
  { rw finsupp.total_map_domain _ _ hv,
    rw left_id,
    exact hl₂ }
end

lemma linear_independent.univ_of_id' (s : set β)
  (h : linear_independent α id s) : linear_independent α (subtype.val : s → β) univ :=
linear_independent.univ_of_id subtype.val_injective (by rwa [subtype.val_range, set.set_of_mem_eq])

def linear_independent.total_equiv : finsupp.supported α α s ≃ₗ span α (v '' s) :=
linear_equiv.of_bijective (finsupp.total_on ι β α v s)
  (linear_independent_iff_total_on.1 hs) (finsupp.total_on_range _ _)

private def aux_linear_equiv_to_linear_map:
  has_coe (span α (v '' s) ≃ₗ[α] finsupp.supported α α s)
          (span α (v '' s) →ₗ[α] finsupp.supported α α s) :=
⟨linear_equiv.to_linear_map⟩
local attribute [instance] aux_linear_equiv_to_linear_map

def linear_independent.repr : span α (v '' s) →ₗ[α] ι →₀ α :=
(submodule.subtype _).comp (hs.total_equiv.symm : span α (v '' s) →ₗ[α] finsupp.supported α α s )

lemma linear_independent.total_repr (x) : finsupp.total ι β α v (hs.repr x) = x :=
subtype.ext.1 $ hs.total_equiv.right_inv x

lemma linear_independent.total_comp_repr : (finsupp.total ι β α v).comp hs.repr = submodule.subtype _ :=
linear_map.ext $ hs.total_repr

lemma linear_independent.repr_ker : hs.repr.ker = ⊥ :=
by rw [linear_independent.repr, linear_map.ker_comp, ker_subtype, comap_bot, linear_equiv.ker]

lemma linear_independent.repr_range : hs.repr.range = finsupp.supported α α s :=
by rw [linear_independent.repr, linear_map.range_comp, linear_equiv.range, map_top, range_subtype]

private def aux_linear_map_to_fun : has_coe_to_fun (finsupp.supported α α s →ₗ[α] span α (v '' s)) :=
  ⟨_, linear_map.to_fun⟩
local attribute [instance] aux_linear_map_to_fun

lemma linear_independent.repr_eq
  {l : ι →₀ α} (h : l ∈ finsupp.supported α α s) {x} (eq : finsupp.total ι β α v l = ↑x) :
  hs.repr x = l :=
by rw ← (subtype.eq' eq : (finsupp.total_on ι β α v s : finsupp.supported α α s →ₗ span α (v '' s)) ⟨l, h⟩ = x);
   exact subtype.ext.1 (hs.total_equiv.left_inv ⟨l, h⟩)

lemma linear_independent.repr_eq_single (i) (x) (hi : i ∈ s) (hx : ↑x = v i) : hs.repr x = finsupp.single i 1 :=
begin
  apply hs.repr_eq (finsupp.single_mem_supported _ _ hi),
  simp [finsupp.total_single, hx]
end

def aux_linear_map_to_fun : has_coe_to_fun (span α (v '' s) →ₗ[α] finsupp.supported α α s) :=
  ⟨_, linear_map.to_fun⟩
local attribute [instance] aux_linear_map_to_fun

lemma linear_independent.repr_supported (x) : hs.repr x ∈ finsupp.supported α α s :=
((hs.total_equiv.symm : span α (v '' s) →ₗ[α] finsupp.supported α α s) x).2

lemma linear_independent.repr_eq_repr_of_subset (h : t ⊆ s) (x y) (e : (↑x:β) = ↑y) :
  (hs.mono h).repr x = hs.repr y :=
eq.symm $ hs.repr_eq (finsupp.supported_mono h ((hs.mono h).repr_supported _) : _ ∈ ↑(finsupp.supported α α s))
  (by rw [← e, (hs.mono h).total_repr]).

lemma linear_independent_iff_not_smul_mem_span :
  linear_independent α v s ↔ (∀ (i ∈ s) (a : α), a • (v i) ∈ span α (v '' (s \ {i})) → a = 0) :=
⟨λ hs i hi a ha, begin
  rw [finsupp.span_eq_map_total, mem_map] at ha,
  rcases ha with ⟨l, hl, e⟩,
  have := (finsupp.supported α α s).sub_mem
    (finsupp.supported_mono (diff_subset _ _) hl : _ ∈ ↑(finsupp.supported α α s))
    (finsupp.single_mem_supported α a hi),
  rw [sub_eq_zero.1 (linear_independent_iff.1 hs _ this $ by simp [e])] at hl,
  by_contra hn,
  exact (not_mem_of_mem_diff (hl $ by simp [hn])) (mem_singleton _)
end, λ H, linear_independent_iff.2 $ λ l ls l0, begin
  ext x, simp,
  by_contra hn,
  have xs : x ∈ s := ls (finsupp.mem_support_iff.2 hn),
  refine hn (H _ xs _ _),
  refine (finsupp.mem_span_iff_total _).2 ⟨finsupp.single x (l x) - l, _, _⟩,
  { have : finsupp.single x (l x) - l ∈ finsupp.supported α α s :=
      sub_mem _ (finsupp.single_mem_supported _ _ xs) ls,
    refine λ y hy, ⟨this hy, λ e, _⟩,
    simp at e hy, apply hy, simp [e] },
  { simp [l0] }
end⟩

lemma linear_independent.restrict_univ (hs : linear_independent α v s) :
  linear_independent α (function.restrict v s) univ :=
begin
  have h_restrict : restrict v s = v ∘ (λ x, x.val),
    by refl,
  rw linear_independent_iff at *,
  rw h_restrict,
  rw finsupp.total_comp,
  intros l _ hl,
  simp at hl,
  have h_map_domain_subtype_eq_0 : l.map_domain subtype.val = 0,
  {
    apply hs (finsupp.lmap_domain α α (λ x : subtype s, x.val) l),
    {
      rw finsupp.mem_supported,
      simp,
      intros x hx,
      have := finset.mem_coe.2 (finsupp.map_domain_support (finset.mem_coe.1 hx)),
      rw finset.coe_image at this,
      exact subtype.val_image_subset _ _ this
    },
    {
      simpa
    },
  },
  apply @finsupp.injective_map_domain _ (subtype s) ι,
  { apply subtype.val_injective },
  { simpa },
end

end repr

lemma eq_of_linear_independent_of_span (nz : (1 : α) ≠ 0)
  (hs : linear_independent α v s) (h : t ⊆ s) (hst : v '' s ⊆ span α (v '' t)) : s = t :=
begin
  refine subset.antisymm (λ i hi, _) h,
  have : (hs.mono h).repr ⟨v i, hst (set.mem_image_of_mem _ hi)⟩ = finsupp.single i 1 :=
    (hs.repr_eq_repr_of_subset h ⟨v i, hst (set.mem_image_of_mem _ hi)⟩
      ⟨v i, subset_span (set.mem_image_of_mem _ hi)⟩ rfl).trans
      (hs.repr_eq_single i ⟨v i, _⟩ hi (by simp)),
  have ss := (hs.mono h).repr_supported _,
  rw this at ss, exact ss (by simp [nz]),
end

end indexed

section
variables {s t : set β} {f : β →ₗ[α] γ}
variables (hf_inj : ∀ x y ∈ t, f x = f y → x = y)
variables (ht : linear_independent α id (f '' t))
include hf_inj ht
open linear_map

lemma linear_independent.supported_disjoint_ker :
  disjoint (finsupp.supported α α t) (ker (f.comp (finsupp.total _ _ _ id))) :=
begin
  refine le_trans (le_inf inf_le_left _) (finsupp.lmap_domain_disjoint_ker _ _ f hf_inj),
  haveI : inhabited β := ⟨0⟩,
  rw [linear_independent, disjoint_iff, ← finsupp.lmap_domain_supported α α f t] at ht,
  rw [← @finsupp.lmap_domain_total _ _ α _ _ _ _ _ _ _ _ _ _ _ _ id id f f (by simp), le_ker_iff_map],
  refine eq_bot_mono (le_inf (map_mono inf_le_left) _) ht,
  rw [map_le_iff_le_comap, ← ker_comp], exact inf_le_right,
end

lemma linear_independent.of_image : linear_independent α (id : β → β) t :=
disjoint_mono_right (ker_le_ker_comp _ _) (ht.supported_disjoint_ker hf_inj)

lemma linear_independent.disjoint_ker : disjoint (span α t) f.ker :=
by rw [← set.image_id t, finsupp.span_eq_map_total, disjoint_iff, map_inf_eq_map_inf_comap,
  ← ker_comp, disjoint_iff.1 (ht.supported_disjoint_ker hf_inj), map_bot]

end

lemma linear_independent.inj_span_iff_inj
  {t : set β} {f : β →ₗ[α] γ}
  (ht : linear_independent α id (f '' t)) :
  disjoint (span α t) f.ker ↔ (∀ x y ∈ t, f x = f y → x = y) :=
⟨linear_map.inj_of_disjoint_ker subset_span, λ h, ht.disjoint_ker h⟩

open linear_map

lemma linear_independent.image {s : set β} {f : β →ₗ γ} (hs : linear_independent α id s)
  (hf_inj : disjoint (span α s) f.ker) : linear_independent α id (f '' s) :=
begin
  rw [disjoint, ← set.image_id s, finsupp.span_eq_map_total, map_inf_eq_map_inf_comap,
    map_le_iff_le_comap, comap_bot] at hf_inj,
  haveI : inhabited β := ⟨0⟩,
  rw [linear_independent, disjoint, ← finsupp.lmap_domain_supported _ _ f, map_inf_eq_map_inf_comap,
      map_le_iff_le_comap, ← ker_comp, @finsupp.lmap_domain_total _ _ α _ _ _ _ _ _ _ _ _ _ _ _ id id, ker_comp],
  { exact le_trans (le_inf inf_le_left hf_inj) (le_trans hs bot_le) },
  { simp }
end

lemma linear_independent.image' {f : β →ₗ γ} (hs : linear_independent α v univ)
  (hf_inj : disjoint (span α (range v)) f.ker) : linear_independent α (f ∘ v) univ :=
begin
  rw [disjoint, ← set.image_univ, finsupp.span_eq_map_total, map_inf_eq_map_inf_comap,
    map_le_iff_le_comap, comap_bot, finsupp.supported_univ, top_inf_eq, linear_independent_univ_iff.1 hs] at hf_inj,
  haveI : inhabited β := ⟨0⟩,
  rw [linear_independent_univ_iff, finsupp.total_comp],
  rw [@finsupp.lmap_domain_total _ _ α _ _ _ _ _ _ _ _ _ _ _ _ _ f, ker_comp, eq_bot_iff],
  apply hf_inj,
  exact λ _, rfl,
end

lemma linear_map.linear_independent_image_iff {s : set β} {f : β →ₗ γ}
  (hf_inj : disjoint (span α s) f.ker) :
  linear_independent α id (f '' s) ↔ linear_independent α id s :=
⟨λ hs, hs.of_image (linear_map.inj_of_disjoint_ker subset_span hf_inj),
 λ hs, hs.image hf_inj⟩

lemma linear_independent_inl_union_inr {s : set β} {t : set γ}
  (hs : linear_independent α id s) (ht : linear_independent α id t) :
  linear_independent α id (inl α β γ '' s ∪ inr α β γ '' t) :=
linear_independent_union (hs.image $ by simp) (ht.image $ by simp) $
by rw [set.image_id, span_image, set.image_id, span_image];
    simp [disjoint_iff, prod_inf_prod]

--TODO : move
def sum.elim {α β γ : Type*} (f : α → γ) (g : β → γ) : α ⊕ β → γ := λ x, sum.rec_on x f g

--TODO : move
@[simp] lemma sum.elim_inl {α β γ : Type*} (f : α → γ) (g : β → γ) (x : α) :
  sum.elim f g (sum.inl x) = f x :=
by refl

--TODO : move
@[simp] lemma sum.elim_inr {α β γ : Type*} (f : α → γ) (g : β → γ) (x : β) :
  sum.elim f g (sum.inr x) = g x :=
by refl

--TODO : move
lemma sum.elim_injective {α β γ : Type*} (f : α → γ) (g : β → γ) (hf : injective f) (hg : injective g)
 (hfg : ∀ a b, f a ≠ g b) : injective (sum.elim f g) :=
λ x y, sum.rec_on x
  (sum.rec_on y (λ x y hxy, by rw hf hxy) (λ x y hxy, false.elim $ hfg _ _ hxy))
  (sum.rec_on y (λ x y hxy, false.elim $ hfg x y hxy.symm) (λ x y hxy, by rw hg hxy))

--TODO : move
lemma sum.elim_range {α β γ : Type*} (f : α → γ) (g : β → γ) :
  range (sum.elim f g) = range f ∪ range g :=
begin
  apply subset.antisymm,
  { intros x hx,
    rcases set.mem_range.1 hx with ⟨a, ha⟩,
    cases a,
    { apply mem_union_left,
      convert mem_range_self _,
      exact ha.symm },
    { apply mem_union_right,
      convert mem_range_self _,
      exact ha.symm } },
  { intros x hx,
    cases hx,
    { rcases set.mem_range.1 hx with ⟨a, ha⟩,
      use a,
      simpa },
    { rcases set.mem_range.1 hx with ⟨a, ha⟩,
      apply set.mem_range.2,
      existsi (sum.inr a),
      simpa }}
end

--TODO : move
lemma disjoint_inl_inr : disjoint (inl α β γ).range (inr α β γ).range :=
begin
  rw disjoint_def,
  intros x hx₁ hx₂,
  rcases linear_map.mem_range.1 hx₁ with ⟨b, hb⟩,
  rcases linear_map.mem_range.1 hx₂ with ⟨c, hc⟩,
  have := hc.trans hb.symm,
  simp at this,
  rw this.1.symm at hb,
  simp [hb.symm],
  refl
end

--TODO : move
lemma linear_map.map_le_range {f : β →ₗ[α] γ} {p : submodule α β} : map f p ≤ range f :=
calc
  map f p ≤ map f ⊤ : map_mono le_top
  ... = range f : map_top _

-- TODO use sum.map

lemma linear_independent_inl_union_inr' {v : ι → β} {v' : ι' → γ}
  (hv : linear_independent α v univ) (hv' : linear_independent α v' univ) :
  linear_independent α (sum.elim (inl α β γ ∘ v) (inr α β γ ∘ v')) univ :=
begin
  by_cases zero_eq_one : (0 : α) = 1,
  { apply linear_independent_of_zero_eq_one zero_eq_one },
  have inj_v : injective v := (linear_independent.injective' zero_eq_one hv),
  have inj_v' : injective v' := (linear_independent.injective' zero_eq_one hv'),
  apply linear_independent.univ_of_id,
  { apply sum.elim_injective _ _,
    { exact injective_comp prod.injective_inl inj_v },
    { exact injective_comp prod.injective_inr inj_v' },
    { intros, simp [ne_zero_of_linear_independent zero_eq_one hv] } },
  { rw sum.elim_range,
    apply linear_independent_union,
    { apply linear_independent.id_of_univ,
      apply linear_independent.image' hv,
      simp [ker_inl] },
    { apply linear_independent.id_of_univ,
      apply linear_independent.image' hv',
      simp [ker_inr] },
    {
      apply disjoint_mono _ _ disjoint_inl_inr,
      { rw [image_id, set.range_comp, span_image],
        apply linear_map.map_le_range },
      { rw [image_id, set.range_comp, span_image],
        apply linear_map.map_le_range },
      apply classical.dec_eq α, -- TODO: Why?
      apply classical.dec_eq β,
      apply classical.dec_eq γ, } }
end

variables (α) (v)
/-- A set of vectors is a basis if it is linearly independent and all vectors are in the span α -/
def is_basis := linear_independent α v univ ∧ span α (range v) = ⊤
variables {α} {v}

section is_basis
variables {s t : set β} (hv : is_basis α v)

lemma is_basis.mem_span (hv : is_basis α v) : ∀ x, x ∈ span α (range v) := eq_top_iff'.1 hv.2

lemma is_basis.comp (hv : is_basis α v) (f : ι' → ι) (hf : bijective f) :
  is_basis α (v ∘ f) :=
begin
  split,
  { apply linear_independent.comp_univ f hf.1 hv.1 },
  { rw[set.range_comp, range_iff_surjective.2 hf.2, image_univ, hv.2] }
end

lemma is_basis.injective (hv : is_basis α v) (zero_ne_one : (0 : α) ≠ 1) : injective v :=
  λ x y h, linear_independent.injective zero_ne_one hv.1 x y (mem_univ x) (mem_univ y) h

def is_basis.repr : β →ₗ (ι →₀ α) :=
(hv.1.repr).comp (linear_map.id.cod_restrict _ (by rw [image_univ]; exact hv.mem_span))

lemma is_basis.total_repr (x) : finsupp.total ι β α v (hv.repr x) = x :=
hv.1.total_repr ⟨x, _⟩

lemma is_basis.total_comp_repr : (finsupp.total ι β α v).comp hv.repr = linear_map.id :=
linear_map.ext hv.total_repr

lemma is_basis.repr_ker : hv.repr.ker = ⊥ :=
linear_map.ker_eq_bot.2 $ injective_of_left_inverse hv.total_repr

lemma is_basis.repr_range : hv.repr.range = finsupp.supported α α univ :=
by  rw [is_basis.repr, linear_map.range, submodule.map_comp,
  linear_map.map_cod_restrict, submodule.map_id, comap_top, map_top, hv.1.repr_range]

-- TODO: remove because trivial?
--lemma is_basis.repr_supported (x : β) : hv.repr x ∈ (finsupp.supported α α univ : submodule α (ι →₀ α)) :=
--hv.1.repr_supported ⟨x, _⟩

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
  apply linear_map.ext,
  intro x,
  apply linear_eq_on (range v) _ (hv.mem_span x),
  intros y hy,
  apply exists.elim (set.mem_range.1 hy),
  intros i hi, rw ←hi, exact h i,
end

/- TODO: simple consequence of funext? needed?
lemma constr_congr {f g : ι → γ} (hv : is_basis α v) (h : ∀i, f i = g i) :
  hv.constr f = hv.constr g :=
by ext y; simp [is_basis.constr_apply]; exact
finset.sum_congr rfl (λ x hx, by simp [h x])
-/

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

def module_equiv_finsupp (hv : is_basis α v) : β ≃ₗ[α] finsupp.supported α α (univ : set ι) :=
(hv.1.total_equiv.trans (linear_equiv.of_top _ (by rw set.image_univ; exact hv.2))).symm

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

lemma linear_map.sup_range_inl_inr :
  (inl α β γ).range ⊔ (inr α β γ).range = ⊤ :=
begin
  rw eq_top_iff',
  intro x,
  rw mem_sup,
  cases x,
  have h₁ : prod.mk x_fst (0 : γ) ∈ (inl α β γ).range,
    by simp,
  have h₂ : prod.mk (0 : β) x_snd ∈ (inr α β γ).range,
    by simp,
  use ⟨x_fst, 0⟩,
  use h₁,
  use ⟨0, x_snd⟩,
  use h₂,
  simp
end

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

-- TODO: move
lemma finsupp.unique_single [unique ι] (x : ι →₀ α) : x = finsupp.single (default ι) (x (default ι)) :=
by ext i; simp [unique.eq_default i]

lemma is_basis_singleton_one (α : Type*) [unique ι] [decidable_eq α] [ring α] :
  is_basis α (λ (_ : ι), (1 : α)) :=
begin
  split,
  { intro i,
    simp [unique.eq_default],
    rw finsupp.unique_single i,
    simp,
    intro hi,
    simp [hi] },
  { apply top_unique,
    intros a h,
    simp [submodule.mem_span_singleton] }
end

lemma linear_equiv.is_basis (hs : is_basis α v)
  (f : β ≃ₗ[α] γ) : is_basis α (f ∘ v) :=
begin
  split,
  { apply hs.1.image',
    have := linear_equiv.ker f,
    unfold_coes at this,
    unfold has_coe_t_aux.coe,
    unfold coe_b,
    unfold has_coe.coe,
    simp [this] }, -- TODO: how to get rid of these?
  { rw set.range_comp,
    have : span α ((f : β →ₗ[α] γ) '' range v) = ⊤,
    { rw [span_image (f : β →ₗ[α] γ), hs.2],
      simp },
    exact this }
end

-- TODO: move up
lemma linear_independent_span (hs : linear_independent α v univ) :
  @linear_independent ι α (span α (range v))
      (λ i : ι, ⟨v i, subset_span (mem_range_self i)⟩) _ _ _ _ _ _ univ :=
begin
  rw linear_independent_iff at *,
  intros l hl₀ hl,
  apply hs l hl₀,
  simp [finsupp.total_apply] at *,
  unfold has_scalar.smul at hl,
  simp at hl,
  unfold finsupp.sum at *,
  have := congr_arg (submodule.subtype (span α (range v))) hl,
  rw linear_map.map_sum (submodule.subtype (span α (range v))) at this,
  simp at this,
  exact this,
end

-- TODO : move
lemma submodule.subtype_eq_val (p : submodule α β) :
  ((submodule.subtype p) : p → β) = subtype.val :=
by refl

lemma is_basis_span (hs : linear_independent α v univ) :
  @is_basis ι α (span α (range v)) (λ i : ι, ⟨v i, subset_span (mem_range_self _)⟩) _ _ _ _ _ _ :=
begin
split,
{ apply linear_independent_span hs },
{ simp only [image_univ.symm,finsupp.span_eq_map_total],
  simp [range_eq_top],
  intros x,
  have := x.property,
  simp only [image_univ.symm,finsupp.span_eq_map_total, finsupp.supported_univ, map] at this,
  apply exists.elim this,
  intros l hl,
  use l,
  apply subtype.ext.2,
  simp [finsupp.total_apply, finsupp.sum] at *,
  rw ←submodule.subtype_eq_val,
  rw linear_map.map_sum (submodule.subtype (span α (range v))),
  simp,
  exact hl }
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

--lemma is_basis_empty_bot : is_basis α ({x | false } : set (⊥ : submodule α β)) :=
--is_basis_empty $ assume ⟨x, hx⟩,
--  by change x ∈ (⊥ : submodule α β) at hx; simpa [subtype.ext] using hx

end module

section vector_space
variables [discrete_field α] [add_comm_group β] [add_comm_group γ]
  [vector_space α β] [vector_space α γ] {s t : set β} {x y z : β}
include α
open submodule

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
   (instead of a data containing type class) -/

set_option class.instance_max_depth 36

lemma mem_span_insert_exchange : x ∈ span α (insert y s) → x ∉ span α s → y ∈ span α (insert x s) :=
begin
  simp [mem_span_insert],
  rintro a z hz rfl h,
  refine ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, _⟩,
  have a0 : a ≠ 0, {rintro rfl, simp * at *},
  simp [a0, smul_add, smul_smul]
end

set_option class.instance_max_depth 32

lemma linear_independent_iff_not_mem_span_old : linear_independent α id s ↔ (∀x∈s, x ∉ span α (s \ {x})) :=
linear_independent_iff_not_smul_mem_span.trans
⟨λ H x xs hx, one_ne_zero (H x xs 1 $ by rw set.image_id; simpa),
 λ H x xs a hx, classical.by_contradiction $ λ a0,
   H x xs (by rw [← set.image_id (s \ {x})]; exact (smul_mem_iff _ a0).1 hx)⟩

lemma linear_independent_iff_not_mem_span : linear_independent α v univ ↔ (∀i, v i ∉ span α (v '' (univ \ {i}))) :=
begin
  apply linear_independent_iff_not_smul_mem_span.trans,
  split,
  { intros h i h_in_span,
    apply one_ne_zero (h i (mem_univ _) 1 (by simp [h_in_span])) },
  { intros h i hi a ha,
    by_contradiction ha',
    exact false.elim (h _ ((smul_mem_iff _ ha').1 ha)) }
end

lemma linear_independent_singleton {x : β} (hx : x ≠ 0) : linear_independent α id ({x} : set β) :=
linear_independent_iff_not_mem_span_old.mpr $ by simp [hx] {contextual := tt}

lemma disjoint_span_singleton {p : submodule α β} {x : β} (x0 : x ≠ 0) :
  disjoint p (span α {x}) ↔ x ∉ p :=
⟨λ H xp, x0 (disjoint_def.1 H _ xp (singleton_subset_iff.1 subset_span:_)),
begin
  simp [disjoint_def, mem_span_singleton],
  rintro xp y yp a rfl,
  by_cases a0 : a = 0, {simp [a0]},
  exact xp.elim ((smul_mem_iff p a0).1 yp),
end⟩

lemma linear_independent.insert (hs : linear_independent α id s) (hx : x ∉ span α s) :
  linear_independent α id (insert x s) :=
begin
  rw ← union_singleton,
  have x0 : x ≠ 0 := mt (by rintro rfl; apply zero_mem _) hx,
  apply linear_independent_union hs (linear_independent_singleton x0),
  rwa [set.image_id, set.image_id, disjoint_span_singleton x0],
  exact classical.dec_eq α
end

/- This doesn't really work:
lemma exists_linear_independent (hs : linear_independent α v univ) (hst : range v ⊆ t) :
  ∃ ι' [decidable_eq ι'] (v' : ι' → β), range v ⊆ t ∧ range v ⊆ range v' ∧ t ⊆ span α (range v)
  ∧ linear_independent α v' univ :=
-/

lemma exists_linear_independent (hs : linear_independent α id s) (hst : s ⊆ t) :
  ∃b⊆t, s ⊆ b ∧ t ⊆ span α b ∧ linear_independent α id b :=
begin
  rcases zorn.zorn_subset₀ {b | b ⊆ t ∧ linear_independent α id b} _ _
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

lemma exists_subset_is_basis (hs : linear_independent α id s) :
  ∃b, s ⊆ b ∧ is_basis α (λ i : b, i.val) :=
let ⟨b, hb₀, hx, hb₂, hb₃⟩ := exists_linear_independent hs (@subset_univ _ _) in
⟨ b, hx,
  @linear_independent.restrict_univ _ _ _ id _ _ _ _ _ _ _ hb₃,
  by simp; exact eq_top_iff.2 hb₂⟩

variables (α β)
lemma exists_is_basis : ∃b : set β, is_basis α (λ i : b, i.val) :=
let ⟨b, _, hb⟩ := exists_subset_is_basis linear_independent_empty in ⟨b, hb⟩
variables {α β}

-- TODO(Mario): rewrite?
lemma exists_of_linear_independent_of_finite_span {t : finset β}
  (hs : linear_independent α id s) (hst : s ⊆ (span α ↑t : submodule α β)) :
  ∃t':finset β, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = t.card :=
have ∀t, ∀(s' : finset β), ↑s' ⊆ s → s ∩ ↑t = ∅ → s ⊆ (span α ↑(s' ∪ t) : submodule α β) →
  ∃t':finset β, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = (s' ∪ t).card :=
assume t, finset.induction_on t
  (assume s' hs' _ hss',
    have s = ↑s',
      from eq_of_linear_independent_of_span (@one_ne_zero α _) hs hs' $
          by rw [set.image_id, set.image_id]; simpa using hss',
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
  (ht : finite t) (hs : linear_independent α id s) (hst : s ⊆ span α t) :
  ∃h : finite s, h.to_finset.card ≤ ht.to_finset.card :=
have s ⊆ (span α ↑(ht.to_finset) : submodule α β), by simp; assumption,
let ⟨u, hust, hsu, eq⟩ := exists_of_linear_independent_of_finite_span hs this in
have finite s, from finite_subset u.finite_to_set hsu,
⟨this, by rw [←eq]; exact (finset.card_le_of_subset $ finset.coe_subset.mp $ by simp [hsu])⟩

lemma exists_left_inverse_linear_map_of_injective {f : β →ₗ[α] γ}
  (hf_inj : f.ker = ⊥) : ∃g:γ →ₗ β, g.comp f = linear_map.id :=
begin
  rcases exists_is_basis α β with ⟨B, hB⟩,
  have hB₀ : _ := linear_independent.id_of_univ hB.1,
  have : linear_independent α id (f '' B),
  { have := hB₀.image (show disjoint (span α (range (λ i : B, i.val))) (linear_map.ker f), by simp [hf_inj]),
    simp at this,
    exact this },
  rcases exists_subset_is_basis this with ⟨C, BC, hC⟩,
  haveI : inhabited β := ⟨0⟩,
  use hC.constr (function.restrict (inv_fun f) C : C → β),
  apply @is_basis.ext _ _ _ _ _ _ _ _ (show decidable_eq β, by assumption) _ _ _ _ _ _ _ hB,
  intros b,
  rw image_subset_iff at BC,
  simp,
  have := BC (subtype.mem b),
  rw mem_preimage_eq at this,
  have : f (b.val) = (subtype.mk (f ↑b) (begin rw ←mem_preimage_eq, exact BC (subtype.mem b) end) : C).val,
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
variables (h : is_basis α v)

local attribute [instance] submodule.module

noncomputable def equiv_fun_basis [fintype ι] : β ≃ (ι → α) :=
calc β ≃ finsupp.supported α α (univ : set ι) : (module_equiv_finsupp h).to_equiv
   ... ≃ ((univ : set ι) →₀ α)                : finsupp.restrict_support_equiv _
   ... ≃ (ι →₀ α)                             : finsupp.dom_congr (equiv.set.univ ι)
   ... ≃ (ι → α)                              : finsupp.equiv_fun_on_fintype

theorem vector_space.card_fintype [fintype ι] [fintype α] [fintype β] :
  card β = (card α) ^ (card ι) :=
calc card β = card (ι → α)    : card_congr (equiv_fun_basis h)
        ... = card α ^ card ι : card_fun

theorem vector_space.card_fintype' [fintype α] [fintype β] :
  ∃ n : ℕ, card β = (card α) ^ n :=
begin
  apply exists.elim (exists_is_basis α β),
  intros b hb,
  haveI := classical.dec_pred (λ x, x ∈ b),
  use card b,
  exact vector_space.card_fintype hb,
end

end vector_space

namespace pi
open set linear_map

section module
variables {η : Type*} {ιs : η → Type*} {φ : η → Type*}
variables [ring α] [∀i, add_comm_group (φ i)] [∀i, module α (φ i)] [fintype η] [decidable_eq η]

-- TODO: move
-- TODO: implication in the other direction?
lemma almost_linindep_of_disjoint_aux {ι α β: Type*} [decidable_eq ι] [decidable_eq α] [decidable_eq β] [ring α]
  [add_comm_group β] [module α β] (g : ι → β) :
  (∀ (i : ι) (a : α), a • g i ∈ span α (g '' (univ \ {i})) → a • g i = 0)
    → ∀ l : ι →₀ α, finsupp.total ι β α g l = 0 → ∀ i, l i • g i = 0 :=
begin
  --split,
  { intros hv l hl i,
    have h_mem_supported : finsupp.single i (l i) - l ∈ finsupp.supported α α (univ \ {i}),
    { rw finsupp.mem_supported,
      intros x hx,
      rw [finset.mem_coe, finsupp.mem_support_iff] at hx,
      rw [←compl_eq_univ_diff],
      apply mem_compl,
      intros hx',
      apply hx,
      rw eq_of_mem_singleton hx',
      simp },
    have h₁: finsupp.total ι β α g (finsupp.single i (l i) - l) = l i • g i,
      by simp [hl],
    have := hv,
    simp only [finsupp.mem_span_iff_total] at this,
    exact this i (l i) ⟨finsupp.single i (l i) - l, h_mem_supported, h₁⟩ }
end

-- TODO: move
-- TODO: implication in the other direction?
lemma almost_linindep_of_disjoint {ι α β: Type*} [decidable_eq ι] [decidable_eq α] [decidable_eq β] [ring α]
  [add_comm_group β] [module α β] (f : ι → submodule α β)
  (hf : ∀ (I J : set ι), disjoint I J → disjoint (⨆i∈I, f i) (⨆i∈J, f i))
  (s : set ι) (g : s → β) (hg : ∀ i, g i ∈ f i) :
  ∀ l : s →₀ α, finsupp.total s β α g l = 0 → ∀ i, l i • g i = 0 :=
begin
  have h_span_le : ∀ j, span α (g '' (univ \ {j})) ≤ ⨆i∈(s \ {j}), f i,
  { intro j,
    rw span_le,
    rw image_subset_iff,
    intros i hi,
    rw set.mem_preimage_eq,
    apply mem_supr_of_mem _ (i : ι),
    apply mem_supr_of_mem,
    { simp [mem_diff] at hi,
      simp [mem_diff],
      rw ←subtype.coe_ext,
      exact hi },
    apply hg },
  have h_eq_0_of_mem_span: ∀ (i : s) (a : α), a • g i ∈ span α (g '' (univ \ {i})) → a • g i = 0,
  { intros i a h_mem_span,
    apply disjoint_def.1,
    apply hf {i} (s \ {i}) disjoint_diff,
    { apply mem_supr_of_mem,
      apply mem_supr_of_mem,
      apply mem_singleton,
      apply submodule.smul,
      apply hg },
    { apply (submodule.le_def'.1 (h_span_le _)) _ h_mem_span } },
  apply almost_linindep_of_disjoint_aux,
  apply h_eq_0_of_mem_span
end

lemma linear_independent_std_basis [∀ j, decidable_eq (ιs j)]  [∀ i, decidable_eq (φ i)]
  (v : Πj, ιs j → (φ j)) (hs : ∀i, linear_independent α (v i) univ) :
  linear_independent α (λ (ji : Σ j, ιs j), std_basis α φ ji.1 (v ji.1 ji.2)) univ :=
begin
  have hs' : ∀j : η, linear_independent α (λ i : ιs j, std_basis α φ j (v j i)) univ,
  { intro j,
    apply linear_independent.image' (hs j),
    simp [ker_std_basis] },
  apply linear_independent_Union_finite hs',
  intros s g hs hg,
  have h_g_mem_range_std_basis: ∀ (j : s), g j ∈ linear_map.range (std_basis α φ j),
  { intros j,
    rw ← span_eq (range (std_basis α φ j)),
    apply span_mono _ (hg j),
    rw range_coe,
    convert image_subset_range _ _,
    apply set.range_comp },
  intros l hl i,
  show l i • g i = 0,
  { haveI := classical.dec_eq α,
    apply almost_linindep_of_disjoint,
    apply disjoint_std_basis_std_basis α φ,
    apply h_g_mem_range_std_basis,
    apply hl }
end

lemma is_basis_std_basis [∀ j, decidable_eq (ιs j)] [∀ j, decidable_eq (φ j)]
  (s : Πj, ιs j → (φ j)) (hs : ∀j, is_basis α (s j)) :
  is_basis α (λ (ji : Σ j, ιs j), std_basis α φ ji.1 (s ji.1 ji.2)) :=
begin
  split,
  { apply linear_independent_std_basis _ (assume i, (hs i).1) },
    --rw ←image_univ,

  have h₁ : Union (λ j, set.range (std_basis α φ j ∘ s j))
    ⊆ range (λ (ji : Σ (j : η), ιs j), (std_basis α φ (ji.fst)) (s (ji.fst) (ji.snd))),
  { intros x hx,
    rw mem_Union at hx,
    rcases hx with ⟨j, hj⟩,
    rw set.mem_range at *,
    rcases hj with ⟨i, hi⟩,
    exact ⟨⟨j, i⟩, hi⟩ },
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
