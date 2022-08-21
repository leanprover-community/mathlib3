/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/

import data.dfinsupp.basic

/-!
# Big operators for dfinsupps

This file contains theorems relevant to big operators in finitely supported dependent functions.
-/

universes u u₁ u₂ v v₁ v₂ v₃ w x y l

open finset
open_locale big_operators

namespace dfinsupp

/-!
### Declarations about `sum` and `prod`

-/

section prod_and_sum

open finset
variables {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
variable [dec : decidable_eq ι]
include dec

/-- `prod f g` is the product of `g i (f i)` over the support of `f`. -/
@[to_additive "`sum f g` is the sum of `g i (f i)` over the support of `f`."]
def prod [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)] [comm_monoid γ]
  (f : Π₀ i, β i) (g : Π i, β i → γ) : γ :=
∏ i in f.support, g i (f i)

@[to_additive]
lemma prod_map_range_index {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
  [Π i, has_zero (β₁ i)] [Π i, has_zero (β₂ i)]
  [Π i (x : β₁ i), decidable (x ≠ 0)] [Π i (x : β₂ i), decidable (x ≠ 0)] [comm_monoid γ]
  {f : Π i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} {h : Π i, β₂ i → γ}
  (h0 : ∀i, h i 0 = 1) :
  (map_range f hf g).prod h = g.prod (λi b, h i (f i b)) :=
begin
  rw [map_range_def],
  refine (finset.prod_subset support_mk_subset _).trans _,
  { intros i h1 h2,
    dsimp, simp [h1] at h2, dsimp at h2,
    simp [h1, h2, h0] },
  { refine finset.prod_congr rfl _,
    intros i h1,
    simp [h1] }
end


-- #exit


@[to_additive]
lemma prod_zero_index [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ] {h : Π i, β i → γ} : (0 : Π₀ i, β i).prod h = 1 :=
rfl

@[to_additive]
lemma prod_single_index [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)] [comm_monoid γ]
  {i : ι} {b : β i} {h : Π i, β i → γ} (h_zero : h i 0 = 1) :
  (single i b).prod h = h i b :=
begin
  by_cases h : b ≠ 0,
  { simp [dfinsupp.prod, support_single_ne_zero h] },
  { rw [not_not] at h, simp [h, prod_zero_index, h_zero], refl }
end

@[to_additive]
lemma prod_neg_index [Π i, add_group (β i)] [Π i (x : β i), decidable (x ≠ 0)] [comm_monoid γ]
  {g : Π₀ i, β i} {h : Π i, β i → γ} (h0 : ∀i, h i 0 = 1) :
  (-g).prod h = g.prod (λi b, h i (- b)) :=
prod_map_range_index h0

omit dec
@[to_additive]
lemma prod_comm {ι₁ ι₂ : Sort*} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*}
  [decidable_eq ι₁] [decidable_eq ι₂] [Π i, has_zero (β₁ i)] [Π i, has_zero (β₂ i)]
  [Π i (x : β₁ i), decidable (x ≠ 0)] [Π i (x : β₂ i), decidable (x ≠ 0)] [comm_monoid γ]
  (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i) (h : Π i, β₁ i → Π i, β₂ i → γ) :
  f₁.prod (λ i₁ x₁, f₂.prod $ λ i₂ x₂, h i₁ x₁ i₂ x₂) =
  f₂.prod (λ i₂ x₂, f₁.prod $ λ i₁ x₁, h i₁ x₁ i₂ x₂) := finset.prod_comm

@[simp] lemma sum_apply {ι₁ : Type u₁} [decidable_eq ι₁] {β₁ : ι₁ → Type v₁}
  [Π i₁, has_zero (β₁ i₁)] [Π i (x : β₁ i), decidable (x ≠ 0)]
  [Π i, add_comm_monoid (β i)]
  {f : Π₀ i₁, β₁ i₁} {g : Π i₁, β₁ i₁ → Π₀ i, β i} {i₂ : ι} :
  (f.sum g) i₂ = f.sum (λi₁ b, g i₁ b i₂) :=
(eval_add_monoid_hom i₂ : (Π₀ i, β i) →+ β i₂).map_sum  _ f.support

include dec

lemma support_sum {ι₁ : Type u₁} [decidable_eq ι₁] {β₁ : ι₁ → Type v₁}
  [Π i₁, has_zero (β₁ i₁)] [Π i (x : β₁ i), decidable (x ≠ 0)]
  [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  {f : Π₀ i₁, β₁ i₁} {g : Π i₁, β₁ i₁ → Π₀ i, β i} :
  (f.sum g).support ⊆ f.support.bUnion (λi, (g i (f i)).support) :=
have ∀i₁ : ι, f.sum (λ (i : ι₁) (b : β₁ i), (g i b) i₁) ≠ 0 →
    (∃ (i : ι₁), f i ≠ 0 ∧ ¬ (g i (f i)) i₁ = 0),
  from assume i₁ h,
  let ⟨i, hi, ne⟩ := finset.exists_ne_zero_of_sum_ne_zero h in
  ⟨i, mem_support_iff.1 hi, ne⟩,
by simpa [finset.subset_iff, mem_support_iff, finset.mem_bUnion, sum_apply] using this

@[simp, to_additive] lemma prod_one [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ] {f : Π₀ i, β i} :
  f.prod (λi b, (1 : γ)) = 1 :=
finset.prod_const_one

@[simp, to_additive] lemma prod_mul [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ] {f : Π₀ i, β i} {h₁ h₂ : Π i, β i → γ} :
  f.prod (λi b, h₁ i b * h₂ i b) = f.prod h₁ * f.prod h₂ :=
finset.prod_mul_distrib

@[simp, to_additive] lemma prod_inv [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_group γ] {f : Π₀ i, β i} {h : Π i, β i → γ} :
  f.prod (λi b, (h i b)⁻¹) = (f.prod h)⁻¹ :=
((inv_monoid_hom : γ →* γ).map_prod _ f.support).symm

@[to_additive] lemma prod_eq_one [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ] {f : Π₀ i, β i} {h : Π i, β i → γ} (hyp : ∀ i, h i (f i) = 1) :
  f.prod h = 1 := finset.prod_eq_one $ λ i hi, hyp i

lemma smul_sum {α : Type*} [monoid α] [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [add_comm_monoid γ] [distrib_mul_action α γ] {f : Π₀ i, β i} {h : Π i, β i → γ} {c : α} :
  c • f.sum h = f.sum (λ a b, c • h a b) := finset.smul_sum

@[to_additive]
lemma prod_add_index [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ] {f g : Π₀ i, β i}
  {h : Π i, β i → γ} (h_zero : ∀i, h i 0 = 1) (h_add : ∀i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
  (f + g).prod h = f.prod h * g.prod h :=
have f_eq : ∏ i in f.support ∪ g.support, h i (f i) = f.prod h,
  from (finset.prod_subset (finset.subset_union_left _ _) $
    by simp [mem_support_iff, h_zero] {contextual := tt}).symm,
have g_eq : ∏ i in f.support ∪ g.support, h i (g i) = g.prod h,
  from (finset.prod_subset (finset.subset_union_right _ _) $
    by simp [mem_support_iff, h_zero] {contextual := tt}).symm,
calc ∏ i in (f + g).support, h i ((f + g) i) =
      ∏ i in f.support ∪ g.support, h i ((f + g) i) :
    finset.prod_subset support_add $
      by simp [mem_support_iff, h_zero] {contextual := tt}
  ... = (∏ i in f.support ∪ g.support, h i (f i)) *
      (∏ i in f.support ∪ g.support, h i (g i)) :
    by simp [h_add, finset.prod_mul_distrib]
  ... = _ : by rw [f_eq, g_eq]

@[to_additive]
lemma _root_.dfinsupp_prod_mem [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ] {S : Type*} [set_like S γ] [submonoid_class S γ] (s : S)
  (f : Π₀ i, β i) (g : Π i, β i → γ) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : f.prod g ∈ s :=
prod_mem $ λ i hi, h _ $ mem_support_iff.1 hi

@[simp, to_additive] lemma prod_eq_prod_fintype [fintype ι] [Π i, has_zero (β i)]
  [Π (i : ι) (x : β i), decidable (x ≠ 0)] [comm_monoid γ] (v : Π₀ i, β i) [f : Π i, β i → γ]
  (hf : ∀ i, f i 0 = 1) :
  v.prod f = ∏ i, f i (dfinsupp.equiv_fun_on_fintype v i) :=
begin
  suffices : ∏ i in v.support, f i (v i) = ∏ i, f i (v i),
  { simp [dfinsupp.prod, this] },
  apply finset.prod_subset v.support.subset_univ,
  intros i hi' hi,
  rw [mem_support_iff, not_not] at hi,
  rw [hi, hf],
end

/--
When summing over an `add_monoid_hom`, the decidability assumption is not needed, and the result is
also an `add_monoid_hom`.
-/
def sum_add_hom [Π i, add_zero_class (β i)] [add_comm_monoid γ] (φ : Π i, β i →+ γ) :
  (Π₀ i, β i) →+ γ :=
{ to_fun := (λ f,
    f.support'.lift (λ s, ∑ i in multiset.to_finset ↑s, φ i (f i)) $
    begin
      rintros ⟨sx, hx⟩ ⟨sy, hy⟩,
      dsimp only [subtype.coe_mk, to_fun_eq_coe] at *,
      have H1 : sx.to_finset ∩ sy.to_finset ⊆ sx.to_finset, from finset.inter_subset_left _ _,
      have H2 : sx.to_finset ∩ sy.to_finset ⊆ sy.to_finset, from finset.inter_subset_right _ _,
      refine (finset.sum_subset H1 _).symm.trans
          ((finset.sum_congr rfl _).trans (finset.sum_subset H2 _)),
      { intros i H1 H2, rw finset.mem_inter at H2,
        simp only [multiset.mem_to_finset] at H1 H2,
        rw [(hy i).resolve_left (mt (and.intro H1) H2), add_monoid_hom.map_zero] },
      { intros i H1, refl },
      { intros i H1 H2, rw finset.mem_inter at H2,
        simp only [multiset.mem_to_finset] at H1 H2,
        rw [(hx i).resolve_left (mt (λ H3, and.intro H3 H1) H2), add_monoid_hom.map_zero] }
    end),
  map_add' := begin
    rintros ⟨f, sf, hf⟩ ⟨g, sg, hg⟩,
    change ∑ i in _, _ = (∑ i in _, _) + (∑ i in _, _),
    simp only [coe_add, coe_mk', subtype.coe_mk, pi.add_apply, map_add, finset.sum_add_distrib],
    congr' 1,
    { refine (finset.sum_subset _ _).symm,
      { intro i, simp only [multiset.mem_to_finset, multiset.mem_add], exact or.inl },
      { intros i H1 H2, simp only [multiset.mem_to_finset, multiset.mem_add] at H2,
        rw [(hf i).resolve_left H2, add_monoid_hom.map_zero] } },
    { refine (finset.sum_subset _ _).symm,
      { intro i, simp only [multiset.mem_to_finset, multiset.mem_add], exact or.inr },
      { intros i H1 H2, simp only [multiset.mem_to_finset, multiset.mem_add] at H2,
        rw [(hg i).resolve_left H2, add_monoid_hom.map_zero] } }
  end,
  map_zero' := rfl }

@[simp] lemma sum_add_hom_single [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  (φ : Π i, β i →+ γ) (i) (x : β i) : sum_add_hom φ (single i x) = φ i x :=
begin
  dsimp [sum_add_hom, single, trunc.lift_mk],
  rw [multiset.to_finset_singleton, finset.sum_singleton, pi.single_eq_same],
end

@[simp] lemma sum_add_hom_comp_single [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  (f : Π i, β i →+ γ) (i : ι) :
  (sum_add_hom f).comp (single_add_hom β i) = f i :=
add_monoid_hom.ext $ λ x, sum_add_hom_single f i x

/-- While we didn't need decidable instances to define it, we do to reduce it to a sum -/
lemma sum_add_hom_apply [Π i, add_zero_class (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [add_comm_monoid γ] (φ : Π i, β i →+ γ) (f : Π₀ i, β i) :
  sum_add_hom φ f = f.sum (λ x, φ x) :=
begin
  rcases f with ⟨f, s, hf⟩,
  change ∑ i in _, _ = (∑ i in finset.filter _ _, _),
  rw [finset.sum_filter, finset.sum_congr rfl],
  intros i _,
  dsimp only [coe_mk', subtype.coe_mk] at *,
  split_ifs,
  refl,
  rw [(not_not.mp h), add_monoid_hom.map_zero],
end

lemma _root_.dfinsupp_sum_add_hom_mem [Π i, add_zero_class (β i)] [add_comm_monoid γ] {S : Type*}
  [set_like S γ] [add_submonoid_class S γ] (s : S) (f : Π₀ i, β i) (g : Π i, β i →+ γ)
  (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : dfinsupp.sum_add_hom g f ∈ s :=
begin
  classical,
  rw dfinsupp.sum_add_hom_apply,
  convert dfinsupp_sum_mem _ _ _ _,
  { apply_instance },
  exact h
end

/-- The supremum of a family of commutative additive submonoids is equal to the range of
`dfinsupp.sum_add_hom`; that is, every element in the `supr` can be produced from taking a finite
number of non-zero elements of `S i`, coercing them to `γ`, and summing them. -/
lemma _root_.add_submonoid.supr_eq_mrange_dfinsupp_sum_add_hom [add_comm_monoid γ]
  (S : ι → add_submonoid γ) : supr S = (dfinsupp.sum_add_hom (λ i, (S i).subtype)).mrange :=
begin
  apply le_antisymm,
  { apply supr_le _,
    intros i y hy,
    exact ⟨dfinsupp.single i ⟨y, hy⟩, dfinsupp.sum_add_hom_single _ _ _⟩, },
  { rintros x ⟨v, rfl⟩,
    exact dfinsupp_sum_add_hom_mem _ v _ (λ i _, (le_supr S i : S i ≤ _) (v i).prop) }
end

/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`dfinsupp.sum_add_hom` composed with `dfinsupp.filter_add_monoid_hom`; that is, every element in the
bounded `supr` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
lemma _root_.add_submonoid.bsupr_eq_mrange_dfinsupp_sum_add_hom (p : ι → Prop)
  [decidable_pred p] [add_comm_monoid γ] (S : ι → add_submonoid γ) :
  (⨆ i (h : p i), S i) =
    ((sum_add_hom (λ i, (S i).subtype)).comp (filter_add_monoid_hom _ p)).mrange :=
begin
  apply le_antisymm,
  { refine supr₂_le (λ i hi y hy, ⟨dfinsupp.single i ⟨y, hy⟩, _⟩),
    rw [add_monoid_hom.comp_apply, filter_add_monoid_hom_apply, filter_single_pos _ _ hi],
    exact sum_add_hom_single _ _ _, },
  { rintros x ⟨v, rfl⟩,
    refine dfinsupp_sum_add_hom_mem _ _ _ (λ i hi, _),
    refine add_submonoid.mem_supr_of_mem i _,
    by_cases hp : p i,
    { simp [hp], },
    { simp [hp] }, }
end

lemma _root_.add_submonoid.mem_supr_iff_exists_dfinsupp [add_comm_monoid γ]
  (S : ι → add_submonoid γ) (x : γ) :
  x ∈ supr S ↔ ∃ f : Π₀ i, S i, dfinsupp.sum_add_hom (λ i, (S i).subtype) f = x :=
set_like.ext_iff.mp (add_submonoid.supr_eq_mrange_dfinsupp_sum_add_hom S) x

/-- A variant of `add_submonoid.mem_supr_iff_exists_dfinsupp` with the RHS fully unfolded. -/
lemma _root_.add_submonoid.mem_supr_iff_exists_dfinsupp' [add_comm_monoid γ]
  (S : ι → add_submonoid γ) [Π i (x : S i), decidable (x ≠ 0)] (x : γ) :
  x ∈ supr S ↔ ∃ f : Π₀ i, S i, f.sum (λ i xi, ↑xi) = x :=
begin
  rw add_submonoid.mem_supr_iff_exists_dfinsupp,
  simp_rw sum_add_hom_apply,
  congr',
end

lemma _root_.add_submonoid.mem_bsupr_iff_exists_dfinsupp (p : ι → Prop)
  [decidable_pred p] [add_comm_monoid γ] (S : ι → add_submonoid γ) (x : γ) :
  x ∈ (⨆ i (h : p i), S i) ↔
    ∃ f : Π₀ i, S i, dfinsupp.sum_add_hom (λ i, (S i).subtype) (f.filter p) = x :=
set_like.ext_iff.mp (add_submonoid.bsupr_eq_mrange_dfinsupp_sum_add_hom p S) x

omit dec
lemma sum_add_hom_comm {ι₁ ι₂ : Sort*} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*} {γ : Type*}
  [decidable_eq ι₁] [decidable_eq ι₂] [Π i, add_zero_class (β₁ i)] [Π i, add_zero_class (β₂ i)]
  [add_comm_monoid γ]
  (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i) (h : Π i j, β₁ i →+ β₂ j →+ γ) :
  sum_add_hom (λ i₂, sum_add_hom (λ i₁, h i₁ i₂) f₁) f₂ =
  sum_add_hom (λ i₁, sum_add_hom (λ i₂, (h i₁ i₂).flip) f₂) f₁ :=
begin
  obtain ⟨⟨f₁, s₁, h₁⟩, ⟨f₂, s₂, h₂⟩⟩ := ⟨f₁, f₂⟩,
  simp only [sum_add_hom, add_monoid_hom.finset_sum_apply, quotient.lift_on_mk,
    add_monoid_hom.coe_mk, add_monoid_hom.flip_apply, trunc.lift],
  exact finset.sum_comm,
end

include dec
/-- The `dfinsupp` version of `finsupp.lift_add_hom`,-/
@[simps apply symm_apply]
def lift_add_hom [Π i, add_zero_class (β i)] [add_comm_monoid γ] :
  (Π i, β i →+ γ) ≃+ ((Π₀ i, β i) →+ γ) :=
{ to_fun := sum_add_hom,
  inv_fun := λ F i, F.comp (single_add_hom β i),
  left_inv := λ x, by { ext, simp },
  right_inv := λ ψ, by { ext, simp },
  map_add' := λ F G, by { ext, simp } }

/-- The `dfinsupp` version of `finsupp.lift_add_hom_single_add_hom`,-/
@[simp] lemma lift_add_hom_single_add_hom [Π i, add_comm_monoid (β i)] :
  lift_add_hom (single_add_hom β) = add_monoid_hom.id (Π₀ i, β i) :=
lift_add_hom.to_equiv.apply_eq_iff_eq_symm_apply.2 rfl

/-- The `dfinsupp` version of `finsupp.lift_add_hom_apply_single`,-/
lemma lift_add_hom_apply_single [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  (f : Π i, β i →+ γ) (i : ι) (x : β i) :
  lift_add_hom f (single i x) = f i x :=
by simp

/-- The `dfinsupp` version of `finsupp.lift_add_hom_comp_single`,-/
lemma lift_add_hom_comp_single [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  (f : Π i, β i →+ γ) (i : ι) :
  (lift_add_hom f).comp (single_add_hom β i) = f i :=
by simp

/-- The `dfinsupp` version of `finsupp.comp_lift_add_hom`,-/
lemma comp_lift_add_hom {δ : Type*} [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  [add_comm_monoid δ] (g : γ →+ δ) (f : Π i, β i →+ γ) :
  g.comp (lift_add_hom f) = lift_add_hom (λ a, g.comp (f a)) :=
lift_add_hom.symm_apply_eq.1 $ funext $ λ a,
  by rw [lift_add_hom_symm_apply, add_monoid_hom.comp_assoc, lift_add_hom_comp_single]

@[simp]
lemma sum_add_hom_zero [Π i, add_zero_class (β i)] [add_comm_monoid γ] :
  sum_add_hom (λ i, (0 : β i →+ γ)) = 0 :=
(lift_add_hom : (Π i, β i →+ γ) ≃+ _).map_zero

@[simp]
lemma sum_add_hom_add [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  (g : Π i, β i →+ γ) (h : Π i, β i →+ γ) :
  sum_add_hom (λ i, g i + h i) = sum_add_hom g + sum_add_hom h :=
lift_add_hom.map_add _ _

@[simp]
lemma sum_add_hom_single_add_hom [Π i, add_comm_monoid (β i)] :
  sum_add_hom (single_add_hom β) = add_monoid_hom.id _ :=
lift_add_hom_single_add_hom

lemma comp_sum_add_hom {δ : Type*} [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  [add_comm_monoid δ] (g : γ →+ δ) (f : Π i, β i →+ γ) :
  g.comp (sum_add_hom f) = sum_add_hom (λ a, g.comp (f a)) :=
comp_lift_add_hom _ _

lemma sum_sub_index [Π i, add_group (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [add_comm_group γ] {f g : Π₀ i, β i}
  {h : Π i, β i → γ} (h_sub : ∀i b₁ b₂, h i (b₁ - b₂) = h i b₁ - h i b₂) :
  (f - g).sum h = f.sum h - g.sum h :=
begin
  have := (lift_add_hom (λ a, add_monoid_hom.of_map_sub (h a) (h_sub a))).map_sub f g,
  rw [lift_add_hom_apply, sum_add_hom_apply, sum_add_hom_apply, sum_add_hom_apply] at this,
  exact this,
end

@[to_additive]
lemma prod_finset_sum_index {γ : Type w} {α : Type x}
  [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ]
  {s : finset α} {g : α → Π₀ i, β i}
  {h : Π i, β i → γ} (h_zero : ∀i, h i 0 = 1) (h_add : ∀i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
  ∏ i in s, (g i).prod h = (∑ i in s, g i).prod h :=
begin
  classical,
  exact finset.induction_on s
  (by simp [prod_zero_index])
  (by simp [prod_add_index, h_zero, h_add] {contextual := tt})
end

@[to_additive]
lemma prod_sum_index {ι₁ : Type u₁} [decidable_eq ι₁] {β₁ : ι₁ → Type v₁}
  [Π i₁, has_zero (β₁ i₁)] [Π i (x : β₁ i), decidable (x ≠ 0)]
  [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ]
  {f : Π₀ i₁, β₁ i₁} {g : Π i₁, β₁ i₁ → Π₀ i, β i}
  {h : Π i, β i → γ} (h_zero : ∀i, h i 0 = 1) (h_add : ∀i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
  (f.sum g).prod h = f.prod (λi b, (g i b).prod h) :=
(prod_finset_sum_index h_zero h_add).symm

@[simp] lemma sum_single [Π i, add_comm_monoid (β i)]
  [Π i (x : β i), decidable (x ≠ 0)] {f : Π₀ i, β i} :
  f.sum single = f :=
begin
  have := add_monoid_hom.congr_fun lift_add_hom_single_add_hom f,
  rw [lift_add_hom_apply, sum_add_hom_apply] at this,
  exact this,
end

@[to_additive]
lemma prod_subtype_domain_index [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ] {v : Π₀ i, β i} {p : ι → Prop} [decidable_pred p]
  {h : Π i, β i → γ} (hp : ∀ x ∈ v.support, p x) :
  (v.subtype_domain p).prod (λi b, h i b) = v.prod h :=
finset.prod_bij (λp _, p)
  (by simp) (by simp)
  (assume ⟨a₀, ha₀⟩ ⟨a₁, ha₁⟩, by simp)
  (λ i hi, ⟨⟨i, hp i hi⟩, by simpa using hi, rfl⟩)

omit dec
lemma subtype_domain_sum [Π i, add_comm_monoid (β i)]
  {s : finset γ} {h : γ → Π₀ i, β i} {p : ι → Prop} [decidable_pred p] :
  (∑ c in s, h c).subtype_domain p = ∑ c in s, (h c).subtype_domain p :=
(subtype_domain_add_monoid_hom β p).map_sum  _ s

lemma subtype_domain_finsupp_sum {δ : γ → Type x} [decidable_eq γ]
  [Π c, has_zero (δ c)] [Π c (x : δ c), decidable (x ≠ 0)]
  [Π i, add_comm_monoid (β i)]
  {p : ι → Prop} [decidable_pred p]
  {s : Π₀ c, δ c} {h : Π c, δ c → Π₀ i, β i} :
  (s.sum h).subtype_domain p = s.sum (λc d, (h c d).subtype_domain p) :=
subtype_domain_sum

end prod_and_sum

end dfinsupp


/-! ### Product and sum lemmas for bundled morphisms.

In this section, we provide analogues of `add_monoid_hom.map_sum`, `add_monoid_hom.coe_finset_sum`,
and `add_monoid_hom.finset_sum_apply` for `dfinsupp.sum` and `dfinsupp.sum_add_hom` instead of
`finset.sum`.

We provide these for `add_monoid_hom`, `monoid_hom`, `ring_hom`, `add_equiv`, and `mul_equiv`.

Lemmas for `linear_map` and `linear_equiv` are in another file.
-/
section

variables {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
variables [decidable_eq ι]

namespace monoid_hom
variables {R S : Type*}
variables [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)]

@[simp, to_additive]
lemma map_dfinsupp_prod [comm_monoid R] [comm_monoid S]
  (h : R →* S) (f : Π₀ i, β i) (g : Π i, β i → R) :
  h (f.prod g) = f.prod (λ a b, h (g a b)) := h.map_prod _ _

@[to_additive]
lemma coe_dfinsupp_prod [monoid R] [comm_monoid S]
  (f : Π₀ i, β i) (g : Π i, β i → R →* S) :
  ⇑(f.prod g) = f.prod (λ a b, (g a b)) := coe_finset_prod _ _

@[simp, to_additive]
lemma dfinsupp_prod_apply [monoid R] [comm_monoid S]
  (f : Π₀ i, β i) (g : Π i, β i → R →* S) (r : R) :
  (f.prod g) r = f.prod (λ a b, (g a b) r) := finset_prod_apply _ _ _

end monoid_hom

namespace ring_hom
variables {R S : Type*}
variables [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)]

@[simp]
lemma map_dfinsupp_prod [comm_semiring R] [comm_semiring S]
  (h : R →+* S) (f : Π₀ i, β i) (g : Π i, β i → R) :
  h (f.prod g) = f.prod (λ a b, h (g a b)) := h.map_prod _ _

@[simp]
lemma map_dfinsupp_sum [non_assoc_semiring R] [non_assoc_semiring S]
  (h : R →+* S) (f : Π₀ i, β i) (g : Π i, β i → R) :
  h (f.sum g) = f.sum (λ a b, h (g a b)) := h.map_sum _ _

end ring_hom

namespace mul_equiv
variables {R S : Type*}
variables [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)]

@[simp, to_additive]
lemma map_dfinsupp_prod [comm_monoid R] [comm_monoid S]
  (h : R ≃* S) (f : Π₀ i, β i) (g : Π i, β i → R) :
  h (f.prod g) = f.prod (λ a b, h (g a b)) := h.map_prod _ _

end mul_equiv

/-! The above lemmas, repeated for `dfinsupp.sum_add_hom`. -/

namespace add_monoid_hom
variables {R S : Type*}

open dfinsupp

@[simp]
lemma map_dfinsupp_sum_add_hom [add_comm_monoid R] [add_comm_monoid S] [Π i, add_zero_class (β i)]
  (h : R →+ S) (f : Π₀ i, β i) (g : Π i, β i →+ R) :
  h (sum_add_hom g f) = sum_add_hom (λ i, h.comp (g i)) f :=
congr_fun (comp_lift_add_hom h g) f

@[simp]
lemma dfinsupp_sum_add_hom_apply [add_zero_class R] [add_comm_monoid S] [Π i, add_zero_class (β i)]
  (f : Π₀ i, β i) (g : Π i, β i →+ R →+ S) (r : R) :
  (sum_add_hom g f) r = sum_add_hom (λ i, (eval r).comp (g i)) f :=
map_dfinsupp_sum_add_hom (eval r) f g

lemma coe_dfinsupp_sum_add_hom [add_zero_class R] [add_comm_monoid S] [Π i, add_zero_class (β i)]
  (f : Π₀ i, β i) (g : Π i, β i →+ R →+ S) :
  ⇑(sum_add_hom g f) = sum_add_hom (λ i, (coe_fn R S).comp (g i)) f :=
map_dfinsupp_sum_add_hom (coe_fn R S) f g

end add_monoid_hom

namespace ring_hom
variables {R S : Type*}

open dfinsupp

@[simp]
lemma map_dfinsupp_sum_add_hom [non_assoc_semiring R] [non_assoc_semiring S]
  [Π i, add_zero_class (β i)] (h : R →+* S) (f : Π₀ i, β i) (g : Π i, β i →+ R) :
  h (sum_add_hom g f) = sum_add_hom (λ i, h.to_add_monoid_hom.comp (g i)) f :=
add_monoid_hom.congr_fun (comp_lift_add_hom h.to_add_monoid_hom g) f

end ring_hom

namespace add_equiv
variables {R S : Type*}

open dfinsupp

@[simp]
lemma map_dfinsupp_sum_add_hom [add_comm_monoid R] [add_comm_monoid S] [Π i, add_zero_class (β i)]
  (h : R ≃+ S) (f : Π₀ i, β i) (g : Π i, β i →+ R) :
  h (sum_add_hom g f) = sum_add_hom (λ i, h.to_add_monoid_hom.comp (g i)) f :=
add_monoid_hom.congr_fun (comp_lift_add_hom h.to_add_monoid_hom g) f

end add_equiv
end
