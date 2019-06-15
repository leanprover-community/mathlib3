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




--TODO: move
-- TODO remove b ≠ 0 condition
lemma single_of_emb_domain_single {α₁ α₂ β : Type*}
[has_zero β] [decidable_eq α₁] [decidable_eq α₂] [decidable_eq β]
 (l : α₁ →₀ β) (f : α₁ ↪ α₂) (a : α₂) (b : β) (hb : b ≠ 0)
  (h : l.emb_domain f = finsupp.single a b) :
  ∃ x, l = finsupp.single x b ∧ f x = a :=
begin
  have h_map_support : finset.map f (l.support) = {a},
    by rw [←finsupp.support_emb_domain, h, finsupp.support_single_ne_zero hb],
  have ha : a ∈ finset.map f (l.support),
    by simp [h_map_support],
  rcases finset.mem_map.1 ha with ⟨c, hc₁, hc₂⟩,
  use c,
  split,
  { ext d,
    rw [← finsupp.emb_domain_apply f l, h],
    by_cases h_cases : c = d,
    { simp [h_cases.symm, hc₂] },
    { rw [finsupp.single_apply, finsupp.single_apply, if_neg, if_neg h_cases],
      by_contra hfd,
      exact h_cases (f.inj (hc₂.trans hfd)) } },
  { exact hc₂ }
end

variables {ι : Type*} {ι' : Type*} {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
          {v : ι → β}
variables [decidable_eq ι] [decidable_eq ι'] [decidable_eq α] [decidable_eq β] [decidable_eq γ] [decidable_eq δ]

section module
variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
variables {a b : α} {x y : β}
include α


section indexed

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



--TODO: needed?
def restrict' {α β} (f : α → β) (s : set α) : s → β := λ x, f x.val

--TODO: needed?
lemma restrict_apply {α : Type*} (f : α → β) (s : set α) (a : subtype s) : restrict' f s a = f a := rfl

--TODO: needed?
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

--TODO: needed?
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

-- TODO: move
lemma finsupp.eq_zero_of_zero_eq_one {ι α : Type*} [ring α]
  (zero_eq_one : (0 : α) = 1) (l : ι →₀ α) : l = 0 :=
  by ext i; simp [eq_zero_of_zero_eq_one α zero_eq_one (l i)]

-- TODO: move
lemma module.eq_zero_of_zero_eq_one {α : Type*} {β : Type*} [ring α]
  [add_comm_group β] [module α β] (zero_eq_one : (0 : α) = 1) (x : β) : x = 0 :=
by rw [←one_smul α x, ←zero_eq_one, zero_smul]

-- TODO: move
lemma submodule.eq_bot_of_zero_eq_one {α : Type*} {β : Type*} [ring α]
  [add_comm_group β] [module α β] (p : submodule α β)
  (zero_eq_one : (0 : α) = 1) : p = ⊥ :=
by ext x; simp [module.eq_zero_of_zero_eq_one zero_eq_one x]


lemma linear_independent_of_zero_eq_one (zero_eq_one : (0 : α) = 1) : linear_independent α v :=
  linear_independent_iff.2 (λ l hl, finsupp.eq_zero_of_zero_eq_one zero_eq_one _)


theorem linear_independent_comp_subtype {s : set ι} :
  linear_independent α (v ∘ subtype.val : s → β) ↔
  ∀ l ∈ (finsupp.supported α α s), (finsupp.total ι β α v) l = 0 → l = 0 :=
begin
  rw linear_independent_iff,
  rw finsupp.total_comp,
  simp only [linear_map.comp_apply],
  split,
  { intros h l hl₁ hl₂,
    have h_bij : bij_on subtype.val (subtype.val ⁻¹' l.support.to_set : set s) l.support.to_set,
    { apply bij_on.mk,
      { unfold maps_to },
      { apply finsupp.inj_on_of_injective _ subtype.val_injective },
      intros i hi,
      rw mem_image,
      use subtype.mk i (((finsupp.mem_supported _ _).1 hl₁ : ↑(l.support) ⊆ s) hi),
      rw mem_preimage_eq,
      exact ⟨hi, rfl⟩ },
    show l = 0,
    { apply finsupp.eq_zero_of_comap_domain_eq_zero (subtype.val : s → ι) _ h_bij,
      apply h,
      convert hl₂,
      rw finsupp.lmap_domain_apply,
      rw finsupp.map_domain_comap_domain,
      apply subtype.val_injective,
      rw subtype.range_val,
      exact (finsupp.mem_supported _ _).1 hl₁ } },
  { intros h l hl,
    have hl' : finsupp.total ι β α v (finsupp.emb_domain ⟨subtype.val, subtype.val_injective⟩ l) = 0,
    { rw finsupp.emb_domain_eq_map_domain ⟨subtype.val, subtype.val_injective⟩ l,
      apply hl },
    apply (finsupp.emb_domain_congr ⟨subtype.val, subtype.val_injective⟩ l 0).1,
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

lemma linear_independent_empty : linear_independent α (λ x, x : (∅ : set β) → β) :=
by simp [linear_independent_subtype_disjoint]

lemma linear_independent.mono {t s : set β} (h : t ⊆ s) :
  linear_independent α (λ x, x : s → β) → linear_independent α (λ x, x : t → β) :=
begin
 simp only [linear_independent_subtype_disjoint],
 exact (disjoint_mono_left (finsupp.supported_mono h))
end

lemma linear_independent.unique (hv : linear_independent α v) {l₁ l₂ : ι →₀ α} :
  finsupp.total ι β α v l₁ = finsupp.total ι β α v l₂ → l₁ = l₂ :=
by apply linear_map.ker_eq_bot.1 hv

/-
lemma zero_not_mem_of_linear_independent
  {i : ι} (ne : 0 ≠ (1:α)) (hs : linear_independent α v s) (hi : v i = 0) :
    i ∉ s :=
λ h, ne $ eq.symm begin
  suffices : (finsupp.single i 1 : ι →₀ α) i = 0, {simpa},
  rw disjoint_def.1 hs _ (finsupp.single_mem_supported _ 1 h),
  {refl}, {simp [hi]}
end-/


-- TODO: Strengthen "hd" to what it was before?
lemma linear_independent_Union_finite {η : Type*} {ιs : η → Type*}
  [decidable_eq η] [∀ j, decidable_eq (ιs j)]
  {f : Π j : η, ιs j → β}
  (hindep : ∀j, linear_independent α (f j))
  --(zero_ne_one : (0 : α) ≠ 1)
  --(hd : ∀i, ∀t:set η, finite t → i ∉ t →
  --disjoint (span α (range (f i))) (⨆i∈t, span α (range (f i))))
  (hd : ∀ (s : set η) (g : s → β), (finite s) → (∀ i : s, g i ∈ span α (range (f i))) →
        ∀ l : s →₀ α, finsupp.total s β α g l = 0 → ∀ j : s, l j • g j = 0)
  :
  linear_independent α (λ ji : Σ j, ιs j, f ji.1 ji.2) :=
begin
  by_cases zero_eq_one : (0 : α) = 1,
  { apply linear_independent_of_zero_eq_one zero_eq_one },
  have zero_ne_one: (0 : α) ≠ 1,
    from zero_eq_one,
  simp only [linear_independent_iff, finsupp.total_apply, finsupp.lsum_apply, finsupp.sigma_sum],
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
  { simp only [linear_independent_iff, finsupp.total_apply, finsupp.lsum_apply] at hindep,
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
  (H : ∀ t ⊆ s, finite t → linear_independent α (subtype.val : t → β)) :
  linear_independent α (subtype.val : s → β) :=
linear_independent_subtype.2 $
  λ l hl, linear_independent_subtype.1 (H _ hl (finset.finite_to_set _)) l (subset.refl _)

lemma linear_independent_Union_of_directed {η : Type*}
  {s : η → set β} (hs : directed (⊆) s)
  (h : ∀ i, linear_independent α (subtype.val : s i → β)) :
  linear_independent α (subtype.val : (⋃ i, s i) → β) :=
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
  (h : ∀ a ∈ s, linear_independent α (subtype.val : (a : set β) → β)) :
  linear_independent α (subtype.val : (⋃₀ s) → β) :=
by rw sUnion_eq_Union; exact
linear_independent_Union_of_directed
  ((directed_on_iff_directed _).1 hs) (by simpa using h)

lemma linear_independent_bUnion_of_directed {η} {s : set η} {t : η → set β}
  (hs : directed_on (t ⁻¹'o (⊆)) s) (h : ∀a∈s, linear_independent α (subtype.val : t a → β)) :
  linear_independent α (subtype.val : (⋃a∈s, t a) → β) :=
by rw bUnion_eq_Union; exact
linear_independent_Union_of_directed
  ((directed_comp _ _ _).2 $ (directed_on_iff_directed _).1 hs)
  (by simpa using h)

section repr
variables (hv : linear_independent α v)

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
    { apply finsupp.inj_on_of_injective _ (linear_independent.injective zero_eq_one hv) },
    intros x hx,
    rcases mem_range.1 (((finsupp.mem_supported _ _).1 hl₁ : ↑(l.support) ⊆ range v) hx) with ⟨i, hi⟩,
    rw mem_image,
    use i,
    rw mem_preimage_eq,
    rw hi,
    exact ⟨hx, rfl⟩ },
  apply finsupp.eq_zero_of_comap_domain_eq_zero v l,
  apply linear_independent_iff.1 hv,
  rw finsupp.total_comap_domain,
  rw finsupp.total_apply at hl₂,
  rw finsupp.sum at hl₂,
  rw finset.sum_preimage v l.support h_bij (λ (x : β), l x • x),
  apply hl₂
end

lemma linear_independent.of_subtype_range (hv : injective v)
  (h : linear_independent α (λ x, x : range v → β)) : linear_independent α v :=
begin
  rw linear_independent_subtype at h,
  rw linear_independent_iff,
  intros l hl,
  apply finsupp.injective_map_domain hv,
  apply h (l.map_domain v),
  { rw finsupp.mem_supported,
    intros x hx,
    have := finset.mem_coe.2 (finsupp.map_domain_support hx),
    rw finset.coe_image at this,
    apply set.image_subset_range _ _ this, },
  { rw finsupp.total_map_domain _ _ hv,
    rw left_id,
    exact hl }
end

lemma linear_independent.restrict_of_comp_subtype {s : set ι}
  (hs : linear_independent α (v ∘ subtype.val : s → β)) :
  linear_independent α (function.restrict v s) :=
begin
  have h_restrict : restrict v s = v ∘ (λ x, x.val),
    by refl,
  rw linear_independent_iff,
  rw linear_independent_comp_subtype at hs,
  rw h_restrict,
  rw finsupp.total_comp,
  intros l hl,
  simp at hl,
  have h_map_domain_subtype_eq_0 : l.map_domain subtype.val = 0,
  { apply hs (finsupp.lmap_domain α α (λ x : subtype s, x.val) l),
    { rw finsupp.mem_supported,
      simp,
      intros x hx,
      have := finset.mem_coe.2 (finsupp.map_domain_support (finset.mem_coe.1 hx)),
      rw finset.coe_image at this,
      exact subtype.val_image_subset _ _ this },
    { simpa } },
  apply @finsupp.injective_map_domain _ (subtype s) ι,
  { apply subtype.val_injective },
  { simpa },
end

/-
def linear_independent.supported_equiv_span (hv : linear_independent α v) :
  finsupp.supported α α (range v) ≃ₗ[α] span α (range v) :=
begin
  convert linear_equiv.of_bijective (finsupp.total_on β β α id (range v)) _ _; try { rw image_id },
  apply (linear_independent_iff_total_on.1 hv.to_subtype_range),
  apply (finsupp.total_on_range _ _),
end

def linear_independent.finsupp_equiv_span_range (hv : linear_independent α v):
  (ι →₀ α) ≃ₗ[α] span α (range v) :=
begin
  by_cases zero_eq_one : 0 = (1:α),
  { apply linear_equiv.of_bijective 0,
    rw [linear_map.ker_zero, submodule.eq_bot_of_zero_eq_one ⊤ zero_eq_one],
    rw [linear_map.range_zero, submodule.eq_bot_of_zero_eq_one ⊤ zero_eq_one] },
  { let eq_univ_range: (univ : set ι) ≃ (range v) :=
      equiv.trans (equiv.set.univ ι) (equiv.set.range v (hv.injective zero_eq_one)),
    let eq₁ : (ι →₀ α) ≃ₗ[α] ((univ : set ι) →₀ α):=
      finsupp.dom_lcongr (equiv.set.univ ι).symm,
    let eq₂ : ((univ : set ι) →₀ α) ≃ₗ[α] finsupp.supported α α (univ : set ι) :=
      (finsupp.supported_equiv_finsupp univ).symm,
    let eq₃ : finsupp.supported α α (univ : set ι) ≃ₗ[α] finsupp.supported α α (range v) :=
    finsupp.congr (univ : set ι) (range v) eq_univ_range,
    let eq₄ : finsupp.supported α α (range v) ≃ₗ[α] span α (range v) :=
      hv.supported_equiv_span,
    exact ((eq₁.trans eq₂).trans eq₃).trans eq₄ }
end

def linear_independent.total_equiv_subtype (s : set β) (hs : linear_independent α (subtype.val : s → β)) :
  finsupp.supported α α s ≃ₗ[α] span α s :=
by convert hs.supported_equiv_span; rw subtype.range_val

-/

-- TODO: move & rename vars
lemma finsupp.range_total : (finsupp.total ι β α v).range = span α (range v) :=
begin
  ext x,
  split,
  { intros hx,
    rw [linear_map.mem_range] at hx,
    rcases hx with ⟨l, hl⟩,
    rw ← hl,
    rw finsupp.total_apply,
    unfold finsupp.sum,
    apply sum_mem (span α (range v)),
    { exact λ i hi, submodule.smul _ _ (subset_span (mem_range_self i)) },
    apply_instance },
  { apply span_le.2,
    intros x hx,
    rcases hx with ⟨i, hi⟩,
    rw [mem_coe, linear_map.mem_range],
    use finsupp.single i 1,
    simp [hi] }
end

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

/-
private def aux_linear_map_to_fun : has_coe_to_fun (finsupp.supported α α s →ₗ[α] span α (v '' s)) :=
  ⟨_, linear_map.to_fun⟩
local attribute [instance] aux_linear_map_to_fun
-/



lemma linear_independent.repr_eq
  {l : ι →₀ α} {x} (eq : finsupp.total ι β α v l = ↑x) :
  hv.repr x = l :=
begin
have : (linear_independent.total_equiv hv : ι →₀ α →ₗ[α] span α (range v)) l
  = ⟨(finsupp.total ι β α v) l, _⟩ := rfl,
rw ← linear_equiv.symm_apply_apply hv.total_equiv l,
unfold_coes at this,
dunfold linear_independent.repr,
unfold_coes,
dunfold has_coe_t_aux.coe,
dunfold coe_b,
dunfold has_coe.coe,
unfold_coes at eq, -- TODO : fix this
simp [this, eq],
end

lemma linear_independent.repr_eq_single (i) (x) (hx : ↑x = v i) :
  hv.repr x = finsupp.single i 1 :=
begin
  apply hv.repr_eq,
  simp [finsupp.total_single, hx]
end

/-
def aux_linear_map_to_fun : has_coe_to_fun (span α (v '' s) →ₗ[α] finsupp.supported α α s) :=
  ⟨_, linear_map.to_fun⟩
local attribute [instance] aux_linear_map_to_fun
-/
/-
lemma linear_independent.repr_supported (x) : hv.repr x ∈ finsupp.supported α α s :=
((hs.total_equiv.symm : span α (v '' s) →ₗ[α] finsupp.supported α α s) x).2

lemma linear_independent.repr_eq_repr_of_subset (h : t ⊆ s) (x y) (e : (↑x:β) = ↑y) :
  (hs.mono h).repr x = hs.repr y :=
eq.symm $ hs.repr_eq (finsupp.supported_mono h ((hs.mono h).repr_supported _) : _ ∈ ↑(finsupp.supported α α s))
  (by rw [← e, (hs.mono h).total_repr]).

-/

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
  --have xs : x ∈ s := ls (finsupp.mem_support_iff.2 hn),
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
  rcases single_of_emb_domain_single (repr ⟨v i, _⟩) f i (1 : α) zero_ne_one.symm l_eq with ⟨i', hi'⟩,
  use i',
  exact hi'.2
end

-- TODO: remove nz
lemma eq_of_linear_independent_of_span_subtype {s t : set β} (nz : (1 : α) ≠ 0)
  (hs : linear_independent α (λ x, x : s → β)) (h : t ⊆ s) (hst : s ⊆ span α t) : s = t :=
begin
  let f : t ↪ s := ⟨λ x, ⟨x.1, h x.2⟩, λ a b hab, subtype.val_injective (subtype.mk.inj hab)⟩,
  have h_surj : surjective f,
  { apply surjective_of_linear_independent_of_span hs f _ nz.symm,
    convert hst; simp [f, comp], },
  show s = t,
  { apply subset.antisymm _ h,
    intros x hx,
    rcases h_surj ⟨x, hx⟩ with ⟨y, hy⟩,
    convert y.mem,
    rw ← subtype.mk.inj hy,
    refl }
end


end indexed

/-
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

-/
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
  rw [@finsupp.lmap_domain_total _ _ α _ _ _ _ _ _ _ _ _ _ _ _ _ f, ker_comp, eq_bot_iff],
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
      map_le_iff_le_comap, ← ker_comp, @finsupp.lmap_domain_total _ _ α _ _ _ _ _ _ _ _ _ _ _ _ id id, ker_comp],
  { exact le_trans (le_inf inf_le_left hf_inj) (le_trans (linear_independent_subtype_disjoint.1 hs) bot_le) },
  { simp }
end

/-
lemma linear_map.linear_independent_image_iff {s : set β} {f : β →ₗ γ}
  (hf_inj : disjoint (span α s) f.ker) :
  linear_independent α id (f '' s) ↔ linear_independent α id s :=
⟨λ hs, hs.of_image (linear_map.inj_of_disjoint_ker subset_span hf_inj),
 λ hs, hs.image hf_inj⟩
-/

--TODO replace subtype.val by (λ x, x) everywhere

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
  (hv : linear_independent α v) (hv' : linear_independent α v') :
  linear_independent α (sum.elim (inl α β γ ∘ v) (inr α β γ ∘ v')) :=
begin
  by_cases zero_eq_one : (0 : α) = 1,
  { apply linear_independent_of_zero_eq_one zero_eq_one },
  have inj_v : injective v := (linear_independent.injective zero_eq_one hv),
  have inj_v' : injective v' := (linear_independent.injective zero_eq_one hv'),
  apply linear_independent.of_subtype_range,
  { apply sum.elim_injective _ _,
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
    {
      apply disjoint_mono _ _ disjoint_inl_inr,
      { rw [set.range_comp, span_image],
        apply linear_map.map_le_range },
      { rw [set.range_comp, span_image],
        apply linear_map.map_le_range },
      apply classical.dec_eq α, -- TODO: Why?
      apply classical.dec_eq β,
      apply classical.dec_eq γ, } }
end

variables (α) (v)
/-- A set of vectors is a basis if it is linearly independent and all vectors are in the span α -/
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
  { rw linear_independent_iff,
    intro l,
    rw finsupp.unique_single l,
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
  { apply hs.1.image,
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
lemma linear_independent_span (hs : linear_independent α v) :
  @linear_independent ι α (span α (range v))
      (λ i : ι, ⟨v i, subset_span (mem_range_self i)⟩) _ _ _ _ _ _ :=
begin
  rw linear_independent_iff at *,
  intros l hl,
  apply hs l,
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

lemma is_basis_span (hs : linear_independent α v) :
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
/-
lemma linear_independent_iff_not_mem_span_old : linear_independent α id s ↔ (∀x∈s, x ∉ span α (s \ {x})) :=
linear_independent_iff_not_smul_mem_span.trans
⟨λ H x xs hx, one_ne_zero (H x xs 1 $ by rw set.image_id; simpa),
 λ H x xs a hx, classical.by_contradiction $ λ a0,
   H x xs (by rw [← set.image_id (s \ {x})]; exact (smul_mem_iff _ a0).1 hx)⟩
-/
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
  rw unique.eq_default i,
  rw finsupp.unique_single l at hl,
  rw finsupp.total_single at hl,
  rw finsupp.zero_apply,
  by_contra hc,
  have := smul_smul _ (l (default ι))⁻¹ (l (default ι)) (v (default ι)), --TODO: better way to do this?
  rw [hl, inv_mul_cancel, smul_zero, one_smul] at this,
  exact h this.symm,
  exact hc,
end

--TODO: move
instance unique.singleton {α : Type*} (a : α) : unique ↥({a} : set α) :=
{ default := ⟨a, mem_singleton a⟩,
  uniq :=
  begin
    intros x,
    apply subtype.coe_ext.2,
    apply eq_of_mem_singleton (subtype.mem x),
  end}

lemma linear_independent_singleton {x : β} (hx : x ≠ 0) : linear_independent α (λ x, x : ({x} : set β) → β) :=
begin
  apply @linear_independent_unique _ _ _ _ _ _ _ _ _ _ _ _,
  apply unique.singleton,
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

/- This doesn't really work:
lemma exists_linear_independent (hs : linear_independent α v univ) (hst : range v ⊆ t) :
  ∃ ι' [decidable_eq ι'] (v' : ι' → β), range v ⊆ t ∧ range v ⊆ range v' ∧ t ⊆ span α (range v)
  ∧ linear_independent α v' univ :=
-/

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
      from eq_of_linear_independent_of_span_subtype (@one_ne_zero α _) hs hs' $
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
calc β ≃ (ι →₀ α) : (module_equiv_finsupp h).to_equiv
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
  (v : Πj, ιs j → (φ j)) (hs : ∀i, linear_independent α (v i)) :
  linear_independent α (λ (ji : Σ j, ιs j), std_basis α φ ji.1 (v ji.1 ji.2)) :=
begin
  have hs' : ∀j : η, linear_independent α (λ i : ιs j, std_basis α φ j (v j i)),
  { intro j,
    apply linear_independent.image (hs j),
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
