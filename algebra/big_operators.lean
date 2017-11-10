/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Some big operators for lists and finite sets.
-/
import data.list data.list.perm data.set.finite data.finset
  algebra.group algebra.ordered_monoid algebra.group_power

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace finset
variables {s s₁ s₂ : finset α} {a : α} {f g : α → β}

protected def prod [comm_monoid β] (s : finset α) (f : α → β) : β := s.fold (*) 1 f
attribute [to_additive finset.sum._proof_1] finset.prod._proof_1
attribute [to_additive finset.sum._proof_2] finset.prod._proof_2
attribute [to_additive finset.sum] finset.prod
attribute [to_additive finset.sum.equations._eqn_1] finset.prod.equations._eqn_1

variables [decidable_eq α]

section comm_monoid
variables [comm_monoid β]

@[simp, to_additive finset.sum_empty]
lemma prod_empty {α : Type u} {f : α → β} : (∅:finset α).prod f = 1 := rfl

@[simp, to_additive finset.sum_to_finset_of_nodup]
lemma prod_to_finset_of_nodup {l : list α} (h : list.nodup l) :
  (to_finset_of_nodup l h).prod f = (l.map f).prod :=
fold_to_finset_of_nodup h

@[simp, to_additive finset.sum_insert]
lemma prod_insert : a ∉ s → (insert a s).prod f = f a * s.prod f := fold_insert

@[simp, to_additive finset.sum_singleton]
lemma prod_singleton : ({a}:finset α).prod f = f a :=
eq.trans fold_singleton (by simp)

@[simp, to_additive finset.sum_const_zero]
lemma prod_const_one : s.prod (λx, (1 : β)) = 1 :=
s.induction_on (by simp) (by simp {contextual:=tt})

@[simp, to_additive finset.sum_image]
lemma prod_image [decidable_eq γ] {s : finset γ} {g : γ → α} :
  (∀x∈s, ∀y∈s, g x = g y → x = y) → (s.image g).prod f = s.prod (λx, f (g x)) :=
fold_image

@[congr, to_additive finset.sum_congr]
lemma prod_congr : (∀x∈s, f x = g x) → s.prod f = s.prod g :=
fold_congr

@[to_additive finset.sum_union_inter]
lemma prod_union_inter : (s₁ ∪ s₂).prod f * (s₁ ∩ s₂).prod f = s₁.prod f * s₂.prod f :=
fold_union_inter

@[to_additive finset.sum_union]
lemma prod_union (h : s₁ ∩ s₂ = ∅) : (s₁ ∪ s₂).prod f = s₁.prod f * s₂.prod f :=
by rw [←prod_union_inter, h]; simp

@[to_additive finset.sum_sdiff]
lemma prod_sdiff (h : s₁ ⊆ s₂) : (s₂ \ s₁).prod f * s₁.prod f = s₂.prod f :=
by rw [←prod_union sdiff_inter_self, sdiff_union_of_subset h]

@[to_additive finset.sum_bind]
lemma prod_bind [decidable_eq γ] {s : finset γ} {t : γ → finset α} :
  (∀x∈s, ∀y∈s, x ≠ y → t x ∩ t y = ∅) → (s.bind t).prod f = s.prod (λx, (t x).prod f) :=
s.induction_on (by simp) $
  assume x s hxs ih hd,
  have hd' : ∀x∈s, ∀y∈s, x ≠ y → t x ∩ t y = ∅,
    from assume _ hx _ hy, hd _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy),
  have t x ∩ finset.bind s t = ∅,
    from ext $ assume a,
      by simp [mem_bind_iff];
      from assume h₁ y hys hy₂,
      have ha : a ∈ t x ∩ t y, by simp [*],
      have t x ∩ t y = ∅,
        from hd _ mem_insert_self _ (mem_insert_of_mem hys) $ assume h, hxs $ h.symm ▸ hys,
      by rwa [this] at ha,
  by simp [hxs, prod_union this, ih hd'] {contextual := tt}

@[to_additive finset.sum_product]
lemma prod_product [decidable_eq γ] {s : finset γ} {t : finset α} {f : γ×α → β} :
  (s.product t).prod f = (s.prod $ λx, t.prod $ λy, f (x, y)) :=
calc (s.product t).prod f = (s.prod $ λx, (t.image $ λy, (x, y)).prod f) :
    prod_bind $ assume x hx y hy h, ext $ by simp [mem_image_iff]; cc
  ... = _ : begin congr, apply funext, intro x, apply prod_image, simp {contextual := tt} end

@[to_additive finset.sum_sigma]
lemma prod_sigma {σ : α → Type*} [∀a, decidable_eq (σ a)]
  {s : finset α} {t : Πa, finset (σ a)} {f : sigma σ → β} :
  (s.sigma t).prod f = (s.prod $ λa, (t a).prod $ λs, f ⟨a, s⟩) :=
have ∀a₁ a₂:α, ∀s₁ : finset (σ a₁), ∀s₂ : finset (σ a₂), a₁ ≠ a₂ →
    s₁.image (sigma.mk a₁) ∩ s₂.image (sigma.mk a₂) = ∅,
  from assume b₁ b₂ s₁ s₂ h, ext $ assume ⟨b₃, c₃⟩,
    by simp [mem_image_iff, sigma.mk_eq_mk_iff, heq_iff_eq] {contextual := tt}; cc,
calc (s.bind (λa, (t a).image (λs, sigma.mk a s))).prod f =
      s.prod (λa, ((t a).image (λs, sigma.mk a s)).prod f) :
    prod_bind $ assume a₁ ha a₂ ha₂ h, this a₁ a₂ (t a₁) (t a₂) h
  ... = (s.prod $ λa, (t a).prod $ λs, f ⟨a, s⟩) :
    by simp [prod_image, sigma.mk_eq_mk_iff, heq_iff_eq]

@[to_additive finset.sum_add_distrib]
lemma prod_mul_distrib : s.prod (λx, f x * g x) = s.prod f * s.prod g :=
eq.trans (by simp; refl) fold_op_distrib

@[to_additive finset.sum_comm]
lemma prod_comm [decidable_eq γ] {s : finset γ} {t : finset α} {f : γ → α → β} :
  (s.prod $ λx, t.prod $ f x) = (t.prod $ λy, s.prod $ λx, f x y) :=
s.induction_on (by simp) (by simp [prod_mul_distrib] {contextual := tt})

@[to_additive finset.sum_hom]
lemma prod_hom [comm_monoid γ] (g : β → γ)
  (h₁ : g 1 = 1) (h₂ : ∀x y, g (x * y) = g x * g y) : s.prod (λx, g (f x)) = g (s.prod f) :=
eq.trans (by rw [h₁]; refl) (fold_hom h₂)

@[to_additive finset.sum_subset]
lemma prod_subset (h : s₁ ⊆ s₂) (hf : ∀x∈s₂, x ∉ s₁ → f x = 1) : s₁.prod f = s₂.prod f :=
have (s₂ \ s₁).prod f = (s₂ \ s₁).prod (λx, 1),
  from prod_congr begin simp [hf] {contextual := tt} end,
by rw [←prod_sdiff h]; simp [this]

@[to_additive finset.exists_ne_zero_of_sum_ne_zero]
lemma exists_ne_one_of_prod_ne_one [decidable_eq β] : s.prod f ≠ 1 → ∃a∈s, f a ≠ 1 :=
s.induction_on (by simp) $ assume a s has ih h,
  decidable.by_cases
    (assume ha : f a = 1,
      have s.prod f ≠ 1, by simpa [ha, has] using h,
      let ⟨a, ha, hfa⟩ := ih this in
      ⟨a, mem_insert_of_mem ha, hfa⟩)
    (assume hna : f a ≠ 1,
      ⟨a, mem_insert_self, hna⟩)

end comm_monoid

section comm_group
variables [comm_group β]

@[simp, to_additive finset.sum_neg_distrib]
lemma prod_inv_distrib : s.prod (λx, (f x)⁻¹) = (s.prod f)⁻¹ :=
prod_hom has_inv.inv one_inv mul_inv

end comm_group

end finset

namespace finset
variables [decidable_eq α] {s s₁ s₂ : finset α} {f g : α → β} {b : β} {a : α}

@[simp] lemma sum_sub_distrib [add_comm_group β] : s.sum (λx, f x - g x) = s.sum f - s.sum g :=
by simp [sum_add_distrib]

section ordered_cancel_comm_monoid
variables [ordered_cancel_comm_monoid β]

lemma sum_le_sum : (∀x∈s, f x ≤ g x) → s.sum f ≤ s.sum g :=
s.induction_on (by simp) $ assume a s ha ih h,
  have f a + s.sum f ≤ g a + s.sum g,
    from add_le_add (h _ mem_insert_self) (ih $ assume x hx, h _ $ mem_insert_of_mem hx),
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
variables [comm_semiring β]

lemma prod_eq_zero (ha : a ∈ s) (h : f a = 0) : s.prod f = 0 :=
calc s.prod f = (insert a (erase a s)).prod f : by simp [ha, insert_erase]
  ... = 0 : by simp [h]
end comm_semiring

section integral_domain /- add integral_semi_domain to support nat and ennreal -/
variables [integral_domain β]

lemma prod_eq_zero_iff : s.prod f = 0 ↔ (∃a∈s, f a = 0) :=
s.induction_on (by simp)
begin
  intros a s,
  rw [bex_def, bex_def, exists_mem_insert],
  simp [mul_eq_zero_iff_eq_zero_or_eq_zero] {contextual := tt}
end

end integral_domain

section ordered_comm_monoid
variables [ordered_comm_monoid β] [∀a b : β, decidable (a ≤ b)]

lemma sum_le_sum' : (∀x∈s, f x ≤ g x) → s.sum f ≤ s.sum g :=
s.induction_on (by simp; refl) $ assume a s ha ih h,
  have f a + s.sum f ≤ g a + s.sum g,
    from add_le_add' (h _ mem_insert_self) (ih $ assume x hx, h _ $ mem_insert_of_mem hx),
  by simp [*]

lemma zero_le_sum' (h : ∀x∈s, 0 ≤ f x) : 0 ≤ s.sum f := le_trans (by simp) (sum_le_sum' h)
lemma sum_le_zero' (h : ∀x∈s, f x ≤ 0) : s.sum f ≤ 0 := le_trans (sum_le_sum' h) (by simp)

lemma sum_le_sum_of_subset_of_nonneg
  (h : s₁ ⊆ s₂) (hf : ∀x∈s₂, x ∉ s₁ → 0 ≤ f x) : s₁.sum f ≤ s₂.sum f :=
calc s₁.sum f ≤ (s₂ \ s₁).sum f + s₁.sum f :
    le_add_of_nonneg_left' $ zero_le_sum' $ by simp [hf] {contextual := tt}
  ... = (s₂ \ s₁ ∪ s₁).sum f : (sum_union sdiff_inter_self).symm
  ... = s₂.sum f : by rw [sdiff_union_of_subset h]

lemma sum_eq_zero_iff_of_nonneg : (∀x∈s, 0 ≤ f x) → (s.sum f = 0 ↔ ∀x∈s, f x = 0) :=
s.induction_on (by simp) $
  by simp [or_imp_distrib, forall_and_distrib, zero_le_sum' ,
           add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg'] {contextual := tt}

end ordered_comm_monoid

section canonically_ordered_monoid
variables [canonically_ordered_monoid β] [∀a b:β, decidable (a ≤ b)]

lemma sum_le_sum_of_subset (h : s₁ ⊆ s₂) : s₁.sum f ≤ s₂.sum f :=
sum_le_sum_of_subset_of_nonneg h $ assume x h₁ h₂, zero_le

lemma sum_le_sum_of_ne_zero (h : ∀x∈s₁, f x ≠ 0 → x ∈ s₂) : s₁.sum f ≤ s₂.sum f :=
calc s₁.sum f = (s₁.filter (λx, f x = 0)).sum f + (s₁.filter (λx, f x ≠ 0)).sum f :
    by rw [←sum_union filter_inter_filter_neg_eq, filter_union_filter_neg_eq]
  ... ≤ s₂.sum f : add_le_of_nonpos_of_le'
      (sum_le_zero' $ by simp {contextual:=tt})
      (sum_le_sum_of_subset $ by simp [subset_iff, *] {contextual:=tt})

end canonically_ordered_monoid

section discrete_linear_ordered_field
variables [discrete_linear_ordered_field α] [decidable_eq β]

lemma abs_sum_le_sum_abs {f : β → α} {s : finset β} : abs (s.sum f) ≤ s.sum (λa, abs (f a)) :=
s.induction_on (by simp [abs_zero]) $
  assume a s has ih,
  calc abs (sum (insert a s) f) ≤ abs (f a) + abs (sum s f) :
      by simp [has]; exact abs_add_le_abs_add_abs _ _
    ... ≤ abs (f a) + s.sum (λa, abs (f a)) : add_le_add (le_refl _) ih
    ... ≤ sum (insert a s) (λ (a : β), abs (f a)) : by simp [has]

end discrete_linear_ordered_field

end finset
