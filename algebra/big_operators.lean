/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Some big operators for lists and finite sets.
-/
import data.list.basic data.list.perm data.finset
  algebra.group algebra.ordered_group algebra.group_power

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

theorem directed.finset_le {r : α → α → Prop} [is_trans α r]
  {ι} (hι : nonempty ι) {f : ι → α} (D : directed r f) (s : finset ι) :
  ∃ z, ∀ i ∈ s, r (f i) (f z) :=
show ∃ z, ∀ i ∈ s.1, r (f i) (f z), from
multiset.induction_on s.1 (by simp [exists_true_iff_nonempty, hι]) $
begin
  rintro i s ⟨j, H⟩,
  rcases D i j with ⟨k, h₁, h₂⟩, existsi k,
  simp, rintro a (rfl | h),
  exacts [h₁, trans (H _ h) h₂]
end

namespace finset
variables {s s₁ s₂ : finset α} {a : α} {f g : α → β}

/-- `prod s f` is the product of `f x` as `x` ranges over the elements of the finite set `s`. -/
@[to_additive finset.sum]
protected def prod [comm_monoid β] (s : finset α) (f : α → β) : β := (s.1.map f).prod
attribute [to_additive finset.sum.equations._eqn_1] finset.prod.equations._eqn_1

@[to_additive finset.sum_eq_fold]
theorem prod_eq_fold [comm_monoid β] (s : finset α) (f : α → β) : s.prod f = s.fold (*) 1 f := rfl

section comm_monoid
variables [comm_monoid β]

@[simp, to_additive finset.sum_empty]
lemma prod_empty {α : Type u} {f : α → β} : (∅:finset α).prod f = 1 := rfl

@[simp, to_additive finset.sum_insert]
lemma prod_insert [decidable_eq α] : a ∉ s → (insert a s).prod f = f a * s.prod f := fold_insert

@[simp, to_additive finset.sum_singleton]
lemma prod_singleton : (singleton a).prod f = f a :=
eq.trans fold_singleton (by simp)

@[simp] lemma prod_const_one : s.prod (λx, (1 : β)) = 1 :=
by simp [finset.prod]
@[simp] lemma sum_const_zero {β} {s : finset α} [add_comm_monoid β] : s.sum (λx, (0 : β)) = 0 :=
@prod_const_one _ (multiplicative β) _ _
attribute [to_additive finset.sum_const_zero] prod_const_one

@[simp, to_additive finset.sum_image]
lemma prod_image [decidable_eq α] [decidable_eq γ] {s : finset γ} {g : γ → α} :
  (∀x∈s, ∀y∈s, g x = g y → x = y) → (s.image g).prod f = s.prod (λx, f (g x)) :=
fold_image

@[congr, to_additive finset.sum_congr]
lemma prod_congr (h : s₁ = s₂) : (∀x∈s₂, f x = g x) → s₁.prod f = s₂.prod g :=
by rw [h]; exact fold_congr
attribute [congr] finset.sum_congr

@[to_additive finset.sum_union_inter]
lemma prod_union_inter [decidable_eq α] : (s₁ ∪ s₂).prod f * (s₁ ∩ s₂).prod f = s₁.prod f * s₂.prod f :=
fold_union_inter

@[to_additive finset.sum_union]
lemma prod_union [decidable_eq α] (h : s₁ ∩ s₂ = ∅) : (s₁ ∪ s₂).prod f = s₁.prod f * s₂.prod f :=
by rw [←prod_union_inter, h]; simp

@[to_additive finset.sum_sdiff]
lemma prod_sdiff [decidable_eq α] (h : s₁ ⊆ s₂) : (s₂ \ s₁).prod f * s₁.prod f = s₂.prod f :=
by rw [←prod_union (sdiff_inter_self _ _), sdiff_union_of_subset h]

@[to_additive finset.sum_bind]
lemma prod_bind [decidable_eq α] {s : finset γ} {t : γ → finset α} :
  (∀x∈s, ∀y∈s, x ≠ y → t x ∩ t y = ∅) → (s.bind t).prod f = s.prod (λx, (t x).prod f) :=
by haveI := classical.dec_eq γ; exact
finset.induction_on s (by simp)
  (assume x s hxs ih hd,
  have hd' : ∀x∈s, ∀y∈s, x ≠ y → t x ∩ t y = ∅,
    from assume _ hx _ hy, hd _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy),
  have t x ∩ finset.bind s t = ∅,
    from ext.2 $ assume a,
      by simp [mem_bind];
      from assume h₁ y hys hy₂,
      have ha : a ∈ t x ∩ t y, by simp [*],
      have t x ∩ t y = ∅,
        from hd _ (mem_insert_self _ _) _ (mem_insert_of_mem hys) $ assume h, hxs $ h.symm ▸ hys,
      by rwa [this] at ha,
  by simp [hxs, prod_union this, ih hd'] {contextual := tt})

@[to_additive finset.sum_product]
lemma prod_product {s : finset γ} {t : finset α} {f : γ×α → β} :
  (s.product t).prod f = s.prod (λx, t.prod $ λy, f (x, y)) :=
begin
  haveI := classical.dec_eq α, haveI := classical.dec_eq γ,
  rw [product_eq_bind, prod_bind (λ x hx y hy h, ext.2 _)], {simp [prod_image]},
  simp [mem_image], intros, intro, refine h _, cc
end

@[to_additive finset.sum_sigma]
lemma prod_sigma {σ : α → Type*}
  {s : finset α} {t : Πa, finset (σ a)} {f : sigma σ → β} :
  (s.sigma t).prod f = s.prod (λa, (t a).prod $ λs, f ⟨a, s⟩) :=
by haveI := classical.dec_eq α; haveI := (λ a, classical.dec_eq (σ a)); exact
have ∀a₁ a₂:α, ∀s₁ : finset (σ a₁), ∀s₂ : finset (σ a₂), a₁ ≠ a₂ →
    s₁.image (sigma.mk a₁) ∩ s₂.image (sigma.mk a₂) = ∅,
  from assume b₁ b₂ s₁ s₂ h, ext.2 $ assume ⟨b₃, c₃⟩,
    by simp [mem_image, sigma.mk.inj_iff, heq_iff_eq] {contextual := tt}; cc,
calc (s.sigma t).prod f =
       (s.bind (λa, (t a).image (λs, sigma.mk a s))).prod f : by rw sigma_eq_bind
  ... = s.prod (λa, ((t a).image (λs, sigma.mk a s)).prod f) :
    prod_bind $ assume a₁ ha a₂ ha₂ h, this a₁ a₂ (t a₁) (t a₂) h
  ... = (s.prod $ λa, (t a).prod $ λs, f ⟨a, s⟩) :
    by simp [prod_image, sigma.mk.inj_iff, heq_iff_eq]

@[to_additive finset.sum_add_distrib]
lemma prod_mul_distrib : s.prod (λx, f x * g x) = s.prod f * s.prod g :=
eq.trans (by simp; refl) fold_op_distrib

@[to_additive finset.sum_comm]
lemma prod_comm [decidable_eq γ] {s : finset γ} {t : finset α} {f : γ → α → β} :
  s.prod (λx, t.prod $ f x) = t.prod (λy, s.prod $ λx, f x y) :=
finset.induction_on s (by simp) (by simp [prod_mul_distrib] {contextual := tt})

@[to_additive finset.sum_hom]
lemma prod_hom [comm_monoid γ] (g : β → γ)
  (h₁ : g 1 = 1) (h₂ : ∀x y, g (x * y) = g x * g y) : s.prod (λx, g (f x)) = g (s.prod f) :=
eq.trans (by rw [h₁]; refl) (fold_hom h₂)

lemma sum_nat_cast [add_comm_monoid β] [has_one β] (s : finset α) (f : α → ℕ) :
  ↑(s.sum f) = s.sum (λa, f a : α → β) :=
(sum_hom _ nat.cast_zero nat.cast_add).symm

@[to_additive finset.sum_subset]
lemma prod_subset (h : s₁ ⊆ s₂) (hf : ∀x∈s₂, x ∉ s₁ → f x = 1) : s₁.prod f = s₂.prod f :=
by haveI := classical.dec_eq α; exact
have (s₂ \ s₁).prod f = (s₂ \ s₁).prod (λx, 1),
  from prod_congr rfl begin simp [hf] {contextual := tt} end,
by rw [←prod_sdiff h]; simp [this]

@[to_additive finset.sum_eq_single]
lemma prod_eq_single {s : finset α} {f : α → β} (a : α)
  (h₀ : ∀b∈s, b ≠ a → f b = 1) (h₁ : a ∉ s → f a = 1) : s.prod f = f a :=
by haveI := classical.dec_eq α;
from classical.by_cases
  (assume : a ∈ s,
    calc s.prod f = ({a} : finset α).prod f :
      begin
        refine (prod_subset _ _).symm,
        { simp [finset.subset_iff, this] },
        { simpa using h₀ }
      end
      ... = f a : by simp)
  (assume : a ∉ s,
    have ∀b, b ∈ s → f b = 1,
      from assume b hb, h₀ b hb $ assume eq, this $ eq ▸ hb,
    calc s.prod f = (∅ : finset α).prod f : (prod_subset (empty_subset s) $ by simpa).symm
      ... = f a : (h₁ ‹a ∉ s›).symm)

@[to_additive finset.sum_attach]
lemma prod_attach {f : α → β} : s.attach.prod (λx, f x.val) = s.prod f :=
by haveI := classical.dec_eq α; exact
calc s.attach.prod (λx, f x.val) = ((s.attach).image subtype.val).prod f :
    by rw [prod_image]; exact assume x _ y _, subtype.eq
  ... = _ : by rw [attach_image_val]

@[to_additive finset.sum_bij]
lemma prod_bij {s : finset α} {t : finset γ} {f : α → β} {g : γ → β}
  (i : Πa∈s, γ) (hi : ∀a ha, i a ha ∈ t) (h : ∀a ha, f a = g (i a ha))
  (i_inj : ∀a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂) (i_surj : ∀b∈t, ∃a ha, b = i a ha) :
  s.prod f = t.prod g :=
by haveI := classical.prop_decidable; exact
calc s.prod f = s.attach.prod (λx, f x.val) : prod_attach.symm
  ... = s.attach.prod (λx, g (i x.1 x.2)) : prod_congr rfl $ assume x hx, h _ _
  ... = (s.attach.image $ λx:{x // x ∈ s}, i x.1 x.2).prod g :
    (prod_image $ assume (a₁:{x // x ∈ s}) _ a₂ _ eq, subtype.eq $ i_inj a₁.1 a₂.1 a₁.2 a₂.2 eq).symm
  ... = _ :
      prod_subset
        (by simp [subset_iff]; intros b a h eq; subst eq; exact hi _ _)
        (assume b hb, not_imp_comm.mp $ assume hb₂,
          let ⟨a, ha, eq⟩ := i_surj b hb in by simp [eq]; exact ⟨_, _, rfl⟩)

@[to_additive finset.sum_bij_ne_zero]
lemma prod_bij_ne_one {s : finset α} {t : finset γ} {f : α → β} {g : γ → β}
  (i : Πa∈s, f a ≠ 1 → γ) (hi₁ : ∀a h₁ h₂, i a h₁ h₂ ∈ t)
  (hi₂ : ∀a₁ a₂ h₁₁ h₁₂ h₂₁ h₂₂, i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ → a₁ = a₂)
  (hi₃ : ∀b∈t, g b ≠ 1 → ∃a h₁ h₂, b = i a h₁ h₂)
  (h : ∀a h₁ h₂, f a = g (i a h₁ h₂)) :
  s.prod f = t.prod g :=
by haveI := classical.prop_decidable; exact
calc s.prod f = (s.filter $ λx, f x ≠ 1).prod f :
    (prod_subset (filter_subset _) $ by simp {contextual:=tt}).symm
  ... = (t.filter $ λx, g x ≠ 1).prod g :
    prod_bij (assume a ha, i a (mem_filter.mp ha).1 (mem_filter.mp ha).2)
      (assume a ha, (mem_filter.mp ha).elim $ λh₁ h₂, mem_filter.mpr
        ⟨hi₁ a h₁ h₂, λ hg, h₂ (hg ▸ h a h₁ h₂)⟩)
      (assume a ha, (mem_filter.mp ha).elim $ h a)
      (assume a₁ a₂ ha₁ ha₂,
        (mem_filter.mp ha₁).elim $ λha₁₁ ha₁₂, (mem_filter.mp ha₂).elim $ λha₂₁ ha₂₂, hi₂ a₁ a₂ _ _ _ _)
      (assume b hb, (mem_filter.mp hb).elim $ λh₁ h₂,
        let ⟨a, ha₁, ha₂, eq⟩ := hi₃ b h₁ h₂ in ⟨a, mem_filter.mpr ⟨ha₁, ha₂⟩, eq⟩)
  ... = t.prod g :
    (prod_subset (filter_subset _) $ by simp {contextual:=tt})

@[to_additive finset.exists_ne_zero_of_sum_ne_zero]
lemma exists_ne_one_of_prod_ne_one : s.prod f ≠ 1 → ∃a∈s, f a ≠ 1 :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp) (assume a s has ih h,
  classical.by_cases
    (assume ha : f a = 1,
      have s.prod f ≠ 1, by simpa [ha, has] using h,
      let ⟨a, ha, hfa⟩ := ih this in
      ⟨a, mem_insert_of_mem ha, hfa⟩)
    (assume hna : f a ≠ 1,
      ⟨a, mem_insert_self _ _, hna⟩))

@[to_additive finset.sum_range_succ]
lemma prod_range_succ (f : ℕ → β) (n : ℕ) :
  (range (nat.succ n)).prod f = f n * (range n).prod f := by simp

lemma prod_range_succ' (f : ℕ → β) :
  ∀ n : ℕ, (range (nat.succ n)).prod f = (range n).prod (f ∘ nat.succ) * f 0
| 0       := by simp
| (n + 1) := by rw [prod_range_succ (λ m, f (nat.succ m)), mul_assoc, ← prod_range_succ'];
                 exact prod_range_succ _ _

@[simp] lemma prod_const [decidable_eq α] (b : β) : s.prod (λ a, b) = b ^ s.card :=
finset.induction_on s rfl (by simp [pow_add, mul_comm] {contextual := tt})

end comm_monoid

@[simp] lemma sum_const [add_comm_monoid β] [decidable_eq α] (b : β) :
  s.sum (λ a, b) = add_monoid.smul s.card b :=
@prod_const _ (multiplicative β) _ _ _ _
attribute [to_additive finset.sum_const] prod_const

lemma sum_range_succ' [add_comm_monoid β] (f : ℕ → β) :
  ∀ n : ℕ, (range (nat.succ n)).sum f = (range n).sum (f ∘ nat.succ) + f 0 :=
@prod_range_succ' (multiplicative β) _ _
attribute [to_additive finset.sum_range_succ'] prod_range_succ'

section comm_group
variables [comm_group β]

@[simp, to_additive finset.sum_neg_distrib]
lemma prod_inv_distrib : s.prod (λx, (f x)⁻¹) = (s.prod f)⁻¹ :=
prod_hom has_inv.inv one_inv mul_inv

end comm_group

@[simp] theorem card_sigma {σ : α → Type*} (s : finset α) (t : Π a, finset (σ a)) :
  card (s.sigma t) = s.sum (λ a, card (t a)) :=
multiset.card_sigma _ _

end finset

namespace finset
variables {s s₁ s₂ : finset α} {f g : α → β} {b : β} {a : α}

@[simp] lemma sum_sub_distrib [add_comm_group β] : s.sum (λx, f x - g x) = s.sum f - s.sum g :=
by simp [sum_add_distrib]

section ordered_cancel_comm_monoid
variables [decidable_eq α] [ordered_cancel_comm_monoid β]

lemma sum_le_sum : (∀x∈s, f x ≤ g x) → s.sum f ≤ s.sum g :=
finset.induction_on s (by simp) $ assume a s ha ih h,
  have f a + s.sum f ≤ g a + s.sum g,
    from add_le_add (h _ (mem_insert_self _ _)) (ih $ assume x hx, h _ $ mem_insert_of_mem hx),
  by simp [*]

lemma zero_le_sum (h : ∀x∈s, 0 ≤ f x) : 0 ≤ s.sum f := le_trans (by simp) (sum_le_sum h)
lemma sum_le_zero (h : ∀x∈s, f x ≤ 0) : s.sum f ≤ 0 := le_trans (sum_le_sum h) (by simp)

end ordered_cancel_comm_monoid

section semiring
variables [semiring β]

lemma sum_mul : s.sum f * b = s.sum (λx, f x * b) :=
(sum_hom (λx, x * b) (zero_mul b) (assume a c, add_mul a c b)).symm

lemma mul_sum : b * s.sum f = s.sum (λx, b * f x) :=
(sum_hom (λx, b * x) (mul_zero b) (assume a c, mul_add b a c)).symm

end semiring

section comm_semiring
variables [decidable_eq α] [comm_semiring β]

lemma prod_eq_zero (ha : a ∈ s) (h : f a = 0) : s.prod f = 0 :=
calc s.prod f = (insert a (erase s a)).prod f : by simp [ha, insert_erase]
  ... = 0 : by simp [h]

lemma prod_sum {δ : α → Type*} [∀a, decidable_eq (δ a)]
  {s : finset α} {t : Πa, finset (δ a)} {f : Πa, δ a → β} :
  s.prod (λa, (t a).sum (λb, f a b)) =
    (s.pi t).sum (λp, s.attach.prod (λx, f x.1 (p x.1 x.2))) :=
begin
  induction s using finset.induction with a s ha ih,
  { simp },
  { have h₁ : ∀x ∈ t a, ∀y∈t a, ∀h : x ≠ y,
        image (pi.cons s a x) (pi s t) ∩ image (pi.cons s a y) (pi s t) = ∅,
    { assume x hx y hy h,
      apply eq_empty_of_forall_not_mem,
      simp,
      assume p₁ p₂ hp eq p₃ hp₃ eq', subst eq',
      have : pi.cons s a x p₂ a (mem_insert_self _ _) = pi.cons s a y p₃ a (mem_insert_self _ _),
      { rw [eq] },
      rw [pi.cons_same, pi.cons_same] at this,
      exact h this },
    have h₂ : ∀b:δ a, ∀p₁∈pi s t, ∀p₂∈pi s t, pi.cons s a b p₁ = pi.cons s a b p₂ → p₁ = p₂, from
      assume b p₁ h₁ p₂ h₂ eq, injective_pi_cons ha eq,
    have h₃ : ∀(v:{x // x ∈ s}) (b:δ a) (h : v.1 ∈ insert a s) (p : Πa, a ∈ s → δ a),
        pi.cons s a b p v.1 h = p v.1 v.2, from
      assume v b h p, pi.cons_ne $ assume eq, ha $ eq.symm ▸ v.2,
    simp [ha, ih, sum_bind h₁, sum_image (h₂ _), sum_mul, h₃],
    simp [mul_sum] }
end

end comm_semiring

section integral_domain /- add integral_semi_domain to support nat and ennreal -/
variables [decidable_eq α] [integral_domain β]

lemma prod_eq_zero_iff : s.prod f = 0 ↔ (∃a∈s, f a = 0) :=
finset.induction_on s (by simp)
begin
  intros a s,
  rw [bex_def, bex_def, exists_mem_insert],
  simp [mul_eq_zero_iff_eq_zero_or_eq_zero] {contextual := tt}
end

end integral_domain

section ordered_comm_monoid
variables [decidable_eq α] [ordered_comm_monoid β]

lemma sum_le_sum' : (∀x∈s, f x ≤ g x) → s.sum f ≤ s.sum g :=
finset.induction_on s (by simp; refl) $ assume a s ha ih h,
  have f a + s.sum f ≤ g a + s.sum g,
    from add_le_add' (h _ (mem_insert_self _ _)) (ih $ assume x hx, h _ $ mem_insert_of_mem hx),
  by simp [*]

lemma zero_le_sum' (h : ∀x∈s, 0 ≤ f x) : 0 ≤ s.sum f := le_trans (by simp) (sum_le_sum' h)
lemma sum_le_zero' (h : ∀x∈s, f x ≤ 0) : s.sum f ≤ 0 := le_trans (sum_le_sum' h) (by simp)

lemma sum_le_sum_of_subset_of_nonneg
  (h : s₁ ⊆ s₂) (hf : ∀x∈s₂, x ∉ s₁ → 0 ≤ f x) : s₁.sum f ≤ s₂.sum f :=
calc s₁.sum f ≤ (s₂ \ s₁).sum f + s₁.sum f :
    le_add_of_nonneg_left' $ zero_le_sum' $ by simp [hf] {contextual := tt}
  ... = (s₂ \ s₁ ∪ s₁).sum f : (sum_union (sdiff_inter_self _ _)).symm
  ... = s₂.sum f : by rw [sdiff_union_of_subset h]

lemma sum_eq_zero_iff_of_nonneg : (∀x∈s, 0 ≤ f x) → (s.sum f = 0 ↔ ∀x∈s, f x = 0) :=
finset.induction_on s (by simp) $
  by simp [or_imp_distrib, forall_and_distrib, zero_le_sum' ,
           add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg'] {contextual := tt}

lemma single_le_sum (hf : ∀x∈s, 0 ≤ f x) {a} (h : a ∈ s) : f a ≤ s.sum f :=
by simpa using show (singleton a).sum f ≤ s.sum f,
from sum_le_sum_of_subset_of_nonneg
 (λ x e, (mem_singleton.1 e).symm ▸ h) (λ x h _, hf x h)

end ordered_comm_monoid

section canonically_ordered_monoid
variables [decidable_eq α] [canonically_ordered_monoid β] [@decidable_rel β (≤)]

lemma sum_le_sum_of_subset (h : s₁ ⊆ s₂) : s₁.sum f ≤ s₂.sum f :=
sum_le_sum_of_subset_of_nonneg h $ assume x h₁ h₂, zero_le _

lemma sum_le_sum_of_ne_zero (h : ∀x∈s₁, f x ≠ 0 → x ∈ s₂) : s₁.sum f ≤ s₂.sum f :=
calc s₁.sum f = (s₁.filter (λx, f x = 0)).sum f + (s₁.filter (λx, f x ≠ 0)).sum f :
    by rw [←sum_union, filter_union_filter_neg_eq]; apply filter_inter_filter_neg_eq
  ... ≤ s₂.sum f : add_le_of_nonpos_of_le'
      (sum_le_zero' $ by simp {contextual:=tt})
      (sum_le_sum_of_subset $ by simp [subset_iff, *] {contextual:=tt})

end canonically_ordered_monoid

section discrete_linear_ordered_field
variables [discrete_linear_ordered_field α] [decidable_eq β]

lemma abs_sum_le_sum_abs {f : β → α} {s : finset β} : abs (s.sum f) ≤ s.sum (λa, abs (f a)) :=
finset.induction_on s (by simp [abs_zero]) $
  assume a s has ih,
  calc abs (sum (insert a s) f) ≤ abs (f a) + abs (sum s f) :
      by simp [has]; exact abs_add_le_abs_add_abs _ _
    ... ≤ abs (f a) + s.sum (λa, abs (f a)) : add_le_add (le_refl _) ih
    ... ≤ sum (insert a s) (λ (a : β), abs (f a)) : by simp [has]

end discrete_linear_ordered_field

@[simp] lemma card_pi [decidable_eq α] {δ : α → Type*}
  (s : finset α) (t : Π a, finset (δ a)) :
  (s.pi t).card = s.prod (λ a, card (t a)) :=
multiset.card_pi _ _

end finset

section group

open list
variables [group α] [group β]

theorem is_group_hom.prod (f : α → β) [is_group_hom f] (l : list α) :
  f (prod l) = prod (map f l) :=
by induction l; simp [*, is_group_hom.mul f, is_group_hom.one f]

theorem is_group_anti_hom.prod (f : α → β) [is_group_anti_hom f] (l : list α) :
  f (prod l) = prod (map f (reverse l)) :=
by induction l; simp [*, is_group_anti_hom.mul f, is_group_anti_hom.one f]

theorem inv_prod : ∀ l : list α, (prod l)⁻¹ = prod (map (λ x, x⁻¹) (reverse l)) :=
λ l, @is_group_anti_hom.prod _ _ _ _ _ inv_is_group_anti_hom l -- TODO there is probably a cleaner proof of this

end group

namespace multiset
variables [decidable_eq α]

@[simp] lemma to_finset_sum_count_eq (s : multiset α) :
  s.to_finset.sum (λa, s.count a) = s.card :=
multiset.induction_on s (by simp)
  (assume a s ih,
    calc (to_finset (a :: s)).sum (λx, count x (a :: s)) =
      (to_finset (a :: s)).sum (λx, (if x = a then 1 else 0) + count x s) :
        by congr; funext x; split_ifs; simp [h, nat.one_add]
      ... = card (a :: s) :
      begin
        by_cases a ∈ s.to_finset,
        { have : (to_finset s).sum (λx, ite (x = a) 1 0) = ({a}:finset α).sum (λx, ite (x = a) 1 0),
          { apply (finset.sum_subset _ _).symm,
            { simp [finset.subset_iff, *] at * },
            { simp [if_neg] {contextual := tt} } },
          simp [h, ih, this, finset.sum_add_distrib] },
        { have : a ∉ s, by simp * at *,
          have : (to_finset s).sum (λx, ite (x = a) 1 0) = (to_finset s).sum (λx, 0), from
            finset.sum_congr rfl begin assume a ha, split_ifs; simp [*] at * end,
          simp [*, finset.sum_add_distrib], }
      end)

end multiset
