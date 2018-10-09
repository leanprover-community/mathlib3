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
multiset.induction_on s.1 (let ⟨z⟩ := hι in ⟨z, λ _, false.elim⟩) $
λ i s ⟨j, H⟩, let ⟨k, h₁, h₂⟩ := D i j in
⟨k, λ a h, or.cases_on (multiset.mem_cons.1 h)
  (λ h, h.symm ▸ h₁)
  (λ h, trans (H _ h) h₂)⟩

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
eq.trans fold_singleton $ mul_one _

@[simp] lemma prod_const_one : s.prod (λx, (1 : β)) = 1 :=
by simp only [finset.prod, multiset.map_const, multiset.prod_repeat, one_pow]
@[simp] lemma sum_const_zero {β} {s : finset α} [add_comm_monoid β] : s.sum (λx, (0 : β)) = 0 :=
@prod_const_one _ (multiplicative β) _ _
attribute [to_additive finset.sum_const_zero] prod_const_one

@[simp, to_additive finset.sum_image]
lemma prod_image [decidable_eq α] {s : finset γ} {g : γ → α} :
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
by rw [←prod_union_inter, h]; exact (mul_one _).symm

@[to_additive finset.sum_sdiff]
lemma prod_sdiff [decidable_eq α] (h : s₁ ⊆ s₂) : (s₂ \ s₁).prod f * s₁.prod f = s₂.prod f :=
by rw [←prod_union (sdiff_inter_self _ _), sdiff_union_of_subset h]

@[to_additive finset.sum_bind]
lemma prod_bind [decidable_eq α] {s : finset γ} {t : γ → finset α} :
  (∀x∈s, ∀y∈s, x ≠ y → t x ∩ t y = ∅) → (s.bind t).prod f = s.prod (λx, (t x).prod f) :=
by haveI := classical.dec_eq γ; exact
finset.induction_on s (λ _, by simp only [bind_empty, prod_empty])
  (assume x s hxs ih hd,
  have hd' : ∀x∈s, ∀y∈s, x ≠ y → t x ∩ t y = ∅,
    from assume _ hx _ hy, hd _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy),
  have t x ∩ finset.bind s t = ∅,
    from eq_empty_of_forall_not_mem $ assume a,
      by rw [mem_inter, mem_bind];
      rintro ⟨h₁, y, hys, hy₂⟩;
      exact eq_empty_iff_forall_not_mem.1
        (hd _ (mem_insert_self _ _) _ (mem_insert_of_mem hys) (assume h, hxs (h.symm ▸ hys)))
        _ (mem_inter_of_mem h₁ hy₂),
  by simp only [bind_insert, prod_insert hxs, prod_union this, ih hd'])

@[to_additive finset.sum_product]
lemma prod_product {s : finset γ} {t : finset α} {f : γ×α → β} :
  (s.product t).prod f = s.prod (λx, t.prod $ λy, f (x, y)) :=
begin
  haveI := classical.dec_eq α, haveI := classical.dec_eq γ,
  rw [product_eq_bind, prod_bind (λ x hx y hy h, eq_empty_of_forall_not_mem _)],
  { congr, funext, exact prod_image (λ _ _ _ _ H, (prod.mk.inj H).2) },
  simp only [mem_inter, mem_image], rintro ⟨_, _⟩ ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩, apply h, cc
end

@[to_additive finset.sum_sigma]
lemma prod_sigma {σ : α → Type*}
  {s : finset α} {t : Πa, finset (σ a)} {f : sigma σ → β} :
  (s.sigma t).prod f = s.prod (λa, (t a).prod $ λs, f ⟨a, s⟩) :=
by haveI := classical.dec_eq α; haveI := (λ a, classical.dec_eq (σ a)); exact
calc (s.sigma t).prod f =
       (s.bind (λa, (t a).image (λs, sigma.mk a s))).prod f : by rw sigma_eq_bind
  ... = s.prod (λa, ((t a).image (λs, sigma.mk a s)).prod f) :
    prod_bind $ assume a₁ ha a₂ ha₂ h, eq_empty_of_forall_not_mem $
    by simp only [mem_inter, mem_image];
    rintro ⟨_, _⟩ ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩; apply h; cc
  ... = (s.prod $ λa, (t a).prod $ λs, f ⟨a, s⟩) :
    prod_congr rfl $ λ _ _, prod_image $ λ _ _ _ _ _, by cc

@[to_additive finset.sum_add_distrib]
lemma prod_mul_distrib : s.prod (λx, f x * g x) = s.prod f * s.prod g :=
eq.trans (by rw one_mul; refl) fold_op_distrib

@[to_additive finset.sum_comm]
lemma prod_comm [decidable_eq γ] {s : finset γ} {t : finset α} {f : γ → α → β} :
  s.prod (λx, t.prod $ f x) = t.prod (λy, s.prod $ λx, f x y) :=
finset.induction_on s (by simp only [prod_empty, prod_const_one]) $
λ _ _ H ih, by simp only [prod_insert H, prod_mul_distrib, ih]

@[to_additive finset.sum_hom]
lemma prod_hom [comm_monoid γ] (g : β → γ)
  (h₁ : g 1 = 1) (h₂ : ∀x y, g (x * y) = g x * g y) : s.prod (λx, g (f x)) = g (s.prod f) :=
eq.trans (by rw [h₁]; refl) (fold_hom h₂)

@[to_additive finset.sum_subset]
lemma prod_subset (h : s₁ ⊆ s₂) (hf : ∀x∈s₂, x ∉ s₁ → f x = 1) : s₁.prod f = s₂.prod f :=
by haveI := classical.dec_eq α; exact
have (s₂ \ s₁).prod f = (s₂ \ s₁).prod (λx, 1),
  from prod_congr rfl $ by simpa only [mem_sdiff, and_imp],
by rw [←prod_sdiff h]; simp only [this, prod_const_one, one_mul]

@[to_additive finset.sum_eq_single]
lemma prod_eq_single {s : finset α} {f : α → β} (a : α)
  (h₀ : ∀b∈s, b ≠ a → f b = 1) (h₁ : a ∉ s → f a = 1) : s.prod f = f a :=
by haveI := classical.dec_eq α;
from classical.by_cases
  (assume : a ∈ s,
    calc s.prod f = ({a} : finset α).prod f :
      begin
        refine (prod_subset _ _).symm,
        { intros _ H, rwa mem_singleton.1 H },
        { simpa only [mem_singleton] }
      end
      ... = f a : prod_singleton)
  (assume : a ∉ s,
    (prod_congr rfl $ λ b hb, h₀ b hb $ by rintro rfl; cc).trans $
      prod_const_one.trans (h₁ this).symm)

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
  ... = t.prod g :
      prod_subset
        (by simp only [subset_iff, mem_image, mem_attach]; rintro _ ⟨⟨_, _⟩, _, rfl⟩; solve_by_elim)
        (assume b hb hb1, false.elim $ hb1 $ by rcases i_surj b hb with ⟨a, ha, rfl⟩;
          exact mem_image.2 ⟨⟨_, _⟩, mem_attach _ _, rfl⟩)

@[to_additive finset.sum_bij_ne_zero]
lemma prod_bij_ne_one {s : finset α} {t : finset γ} {f : α → β} {g : γ → β}
  (i : Πa∈s, f a ≠ 1 → γ) (hi₁ : ∀a h₁ h₂, i a h₁ h₂ ∈ t)
  (hi₂ : ∀a₁ a₂ h₁₁ h₁₂ h₂₁ h₂₂, i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ → a₁ = a₂)
  (hi₃ : ∀b∈t, g b ≠ 1 → ∃a h₁ h₂, b = i a h₁ h₂)
  (h : ∀a h₁ h₂, f a = g (i a h₁ h₂)) :
  s.prod f = t.prod g :=
by haveI := classical.prop_decidable; exact
calc s.prod f = (s.filter $ λx, f x ≠ 1).prod f :
    (prod_subset (filter_subset _) $ by simp only [not_imp_comm, mem_filter]; exact λ _, and.intro).symm
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
    (prod_subset (filter_subset _) $ by simp only [not_imp_comm, mem_filter]; exact λ _, and.intro)

@[to_additive finset.exists_ne_zero_of_sum_ne_zero]
lemma exists_ne_one_of_prod_ne_one : s.prod f ≠ 1 → ∃a∈s, f a ≠ 1 :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (λ H, (H rfl).elim) (assume a s has ih h,
  classical.by_cases
    (assume ha : f a = 1,
      let ⟨a, ha, hfa⟩ := ih (by rwa [prod_insert has, ha, one_mul] at h) in
      ⟨a, mem_insert_of_mem ha, hfa⟩)
    (assume hna : f a ≠ 1,
      ⟨a, mem_insert_self _ _, hna⟩))

@[to_additive finset.sum_range_succ]
lemma prod_range_succ (f : ℕ → β) (n : ℕ) :
  (range (nat.succ n)).prod f = f n * (range n).prod f :=
by rw [range_succ, prod_insert not_mem_range_self]

lemma prod_range_succ' (f : ℕ → β) :
  ∀ n : ℕ, (range (nat.succ n)).prod f = (range n).prod (f ∘ nat.succ) * f 0
| 0       := (prod_range_succ _ _).trans $ mul_comm _ _
| (n + 1) := by rw [prod_range_succ (λ m, f (nat.succ m)), mul_assoc, ← prod_range_succ'];
                 exact prod_range_succ _ _

@[simp] lemma prod_const (b : β) : s.prod (λ a, b) = b ^ s.card :=
by haveI := classical.dec_eq α; exact
finset.induction_on s rfl (λ a s has ih,
by rw [prod_insert has, card_insert_of_not_mem has, pow_succ, ih])

lemma prod_pow (s : finset α) (n : ℕ) (f : α → β) :
  s.prod (λ x, f x ^ n) = s.prod f ^ n :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp) (by simp [_root_.mul_pow] {contextual := tt})

lemma prod_nat_pow (s : finset α) (n : ℕ) (f : α → ℕ) :
  s.prod (λ x, f x ^ n) = s.prod f ^ n :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp) (by simp [nat.mul_pow] {contextual := tt})

@[to_additive finset.sum_involution]
lemma prod_involution {s : finset α} {f : α → β} :
  ∀ (g : Π a ∈ s, α)
  (h₁ : ∀ a ha, f a * f (g a ha) = 1)
  (h₂ : ∀ a ha, f a ≠ 1 → g a ha ≠ a)
  (h₃ : ∀ a ha, g a ha ∈ s)
  (h₄ : ∀ a ha, g (g a ha) (h₃ a ha) = a),
  s.prod f = 1 :=
by haveI := classical.dec_eq α;
haveI := classical.dec_eq β; exact
finset.strong_induction_on s
  (λ s ih g h₁ h₂ h₃ h₄,
    if hs : s = ∅ then hs.symm ▸ rfl
    else let ⟨x, hx⟩ := exists_mem_of_ne_empty hs in
      have hmem : ∀ y ∈ (s.erase x).erase (g x hx), y ∈ s,
        from λ y hy, (mem_of_mem_erase (mem_of_mem_erase hy)),
      have g_inj : ∀ {x hx y hy}, g x hx = g y hy → x = y,
        from λ x hx y hy h, by rw [← h₄ x hx, ← h₄ y hy]; simp [h],
      have ih': (erase (erase s x) (g x hx)).prod f = (1 : β) :=
        ih ((s.erase x).erase (g x hx))
          ⟨subset.trans (erase_subset _ _) (erase_subset _ _),
            λ h, not_mem_erase (g x hx) (s.erase x) (h (h₃ x hx))⟩
          (λ y hy, g y (hmem y hy))
          (λ y hy, h₁ y (hmem y hy))
          (λ y hy, h₂ y (hmem y hy))
          (λ y hy, mem_erase.2 ⟨λ (h : g y _ = g x hx), by simpa [g_inj h] using hy,
            mem_erase.2 ⟨λ (h : g y _ = x),
              have y = g x hx, from h₄ y (hmem y hy) ▸ by simp [h],
              by simpa [this] using hy, h₃ y (hmem y hy)⟩⟩)
          (λ y hy, h₄ y (hmem y hy)),
      if hx1 : f x = 1
      then ih' ▸ eq.symm (prod_subset hmem
        (λ y hy hy₁,
          have y = x ∨ y = g x hx, by simp [hy] at hy₁; tauto,
          this.elim (λ h, h.symm ▸ hx1)
            (λ h, h₁ x hx ▸ h ▸ hx1.symm ▸ (one_mul _).symm)))
      else by rw [← insert_erase hx, prod_insert (not_mem_erase _ _),
        ← insert_erase (mem_erase.2 ⟨h₂ x hx hx1, h₃ x hx⟩),
        prod_insert (not_mem_erase _ _), ih', mul_one, h₁ x hx])

end comm_monoid

lemma sum_smul [add_comm_monoid β] (s : finset α) (n : ℕ) (f : α → β) :
  s.sum (λ x, add_monoid.smul n (f x)) = add_monoid.smul n (s.sum f) :=
@prod_pow _ (multiplicative β) _ _ _ _
attribute [to_additive finset.sum_smul] prod_pow

@[simp] lemma sum_const [add_comm_monoid β] (b : β) :
  s.sum (λ a, b) = add_monoid.smul s.card b :=
@prod_const _ (multiplicative β) _ _ _
attribute [to_additive finset.sum_const] prod_const

lemma sum_range_succ' [add_comm_monoid β] (f : ℕ → β) :
  ∀ n : ℕ, (range (nat.succ n)).sum f = (range n).sum (f ∘ nat.succ) + f 0 :=
@prod_range_succ' (multiplicative β) _ _
attribute [to_additive finset.sum_range_succ'] prod_range_succ'

lemma sum_nat_cast [add_comm_monoid β] [has_one β] (s : finset α) (f : α → ℕ) :
  ↑(s.sum f) = s.sum (λa, f a : α → β) :=
(sum_hom _ nat.cast_zero nat.cast_add).symm

section comm_group
variables [comm_group β]

@[simp, to_additive finset.sum_neg_distrib]
lemma prod_inv_distrib : s.prod (λx, (f x)⁻¹) = (s.prod f)⁻¹ :=
prod_hom has_inv.inv one_inv mul_inv

end comm_group

@[simp] theorem card_sigma {σ : α → Type*} (s : finset α) (t : Π a, finset (σ a)) :
  card (s.sigma t) = s.sum (λ a, card (t a)) :=
multiset.card_sigma _ _

lemma card_bind [decidable_eq β] {s : finset α} {t : α → finset β}
  (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → t x ∩ t y = ∅) :
  (s.bind t).card = s.sum (λ u, card (t u)) :=
calc (s.bind t).card = (s.bind t).sum (λ _, 1) : by simp
... = s.sum (λ a, (t a).sum (λ _, 1)) : finset.sum_bind h
... = s.sum (λ u, card (t u)) : by simp

lemma card_bind_le [decidable_eq β] {s : finset α} {t : α → finset β} :
  (s.bind t).card ≤ s.sum (λ a, (t a).card) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp)
  (λ a s has ih,
    calc ((insert a s).bind t).card ≤ (t a).card + (s.bind t).card :
    by rw bind_insert; exact finset.card_union_le _ _
    ... ≤ (insert a s).sum (λ a, card (t a)) :
    by rw sum_insert has; exact add_le_add_left ih _)

end finset

namespace finset
variables {s s₁ s₂ : finset α} {f g : α → β} {b : β} {a : α}

@[simp] lemma sum_sub_distrib [add_comm_group β] : s.sum (λx, f x - g x) = s.sum f - s.sum g :=
sum_add_distrib.trans $ congr_arg _ sum_neg_distrib

section ordered_cancel_comm_monoid
variables [decidable_eq α] [ordered_cancel_comm_monoid β]

lemma sum_le_sum : (∀x∈s, f x ≤ g x) → s.sum f ≤ s.sum g :=
finset.induction_on s (λ _, le_refl _) $ assume a s ha ih h,
  have f a + s.sum f ≤ g a + s.sum g,
    from add_le_add (h _ (mem_insert_self _ _)) (ih $ assume x hx, h _ $ mem_insert_of_mem hx),
  by simpa only [sum_insert ha]

lemma zero_le_sum (h : ∀x∈s, 0 ≤ f x) : 0 ≤ s.sum f := le_trans (by rw [sum_const_zero]) (sum_le_sum h)
lemma sum_le_zero (h : ∀x∈s, f x ≤ 0) : s.sum f ≤ 0 := le_trans (sum_le_sum h) (by rw [sum_const_zero])

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
calc s.prod f = (insert a (erase s a)).prod f : by rw insert_erase ha
  ... = 0 : by rw [prod_insert (not_mem_erase _ _), h, zero_mul]

lemma prod_sum {δ : α → Type*} [∀a, decidable_eq (δ a)]
  {s : finset α} {t : Πa, finset (δ a)} {f : Πa, δ a → β} :
  s.prod (λa, (t a).sum (λb, f a b)) =
    (s.pi t).sum (λp, s.attach.prod (λx, f x.1 (p x.1 x.2))) :=
begin
  induction s using finset.induction with a s ha ih,
  { rw [pi_empty, sum_singleton], refl },
  { have h₁ : ∀x ∈ t a, ∀y ∈ t a, ∀h : x ≠ y,
        image (pi.cons s a x) (pi s t) ∩ image (pi.cons s a y) (pi s t) = ∅,
    { assume x hx y hy h,
      apply eq_empty_of_forall_not_mem,
      simp only [mem_inter, mem_image],
      rintro p₁ ⟨⟨p₂, hp, eq⟩, ⟨p₃, hp₃, rfl⟩⟩,
      have : pi.cons s a x p₂ a (mem_insert_self _ _) = pi.cons s a y p₃ a (mem_insert_self _ _),
      { rw [eq] },
      rw [pi.cons_same, pi.cons_same] at this,
      exact h this },
    rw [prod_insert ha, pi_insert ha, ih, sum_mul, sum_bind h₁],
    refine sum_congr rfl (λ b _, _),
    have h₂ : ∀p₁∈pi s t, ∀p₂∈pi s t, pi.cons s a b p₁ = pi.cons s a b p₂ → p₁ = p₂, from
      assume p₁ h₁ p₂ h₂ eq, injective_pi_cons ha eq,
    rw [sum_image h₂, mul_sum],
    refine sum_congr rfl (λ g _, _),
    rw [attach_insert, prod_insert, prod_image],
    { simp only [pi.cons_same],
      congr', ext ⟨v, hv⟩, congr',
      exact (pi.cons_ne (by rintro rfl; exact ha hv)).symm },
    { exact λ _ _ _ _, subtype.eq ∘ subtype.mk.inj },
    { simp only [mem_image], rintro ⟨⟨_, hm⟩, _, rfl⟩, exact ha hm } }
end

end comm_semiring

section integral_domain /- add integral_semi_domain to support nat and ennreal -/
variables [decidable_eq α] [integral_domain β]

lemma prod_eq_zero_iff : s.prod f = 0 ↔ (∃a∈s, f a = 0) :=
finset.induction_on s ⟨not.elim one_ne_zero, λ ⟨_, H, _⟩, H.elim⟩ $ λ a s ha ih,
by rw [prod_insert ha, mul_eq_zero_iff_eq_zero_or_eq_zero,
  bex_def, exists_mem_insert, ih, ← bex_def]

end integral_domain

section ordered_comm_monoid
variables [decidable_eq α] [ordered_comm_monoid β]

lemma sum_le_sum' : (∀x∈s, f x ≤ g x) → s.sum f ≤ s.sum g :=
finset.induction_on s (λ _, le_refl _) $ assume a s ha ih h,
  have f a + s.sum f ≤ g a + s.sum g,
    from add_le_add' (h _ (mem_insert_self _ _)) (ih $ assume x hx, h _ $ mem_insert_of_mem hx),
  by simpa only [sum_insert ha]

lemma zero_le_sum' (h : ∀x∈s, 0 ≤ f x) : 0 ≤ s.sum f := le_trans (by rw [sum_const_zero]) (sum_le_sum' h)
lemma sum_le_zero' (h : ∀x∈s, f x ≤ 0) : s.sum f ≤ 0 := le_trans (sum_le_sum' h) (by rw [sum_const_zero])

lemma sum_le_sum_of_subset_of_nonneg
  (h : s₁ ⊆ s₂) (hf : ∀x∈s₂, x ∉ s₁ → 0 ≤ f x) : s₁.sum f ≤ s₂.sum f :=
calc s₁.sum f ≤ (s₂ \ s₁).sum f + s₁.sum f :
    le_add_of_nonneg_left' $ zero_le_sum' $ by simpa only [mem_sdiff, and_imp]
  ... = (s₂ \ s₁ ∪ s₁).sum f : (sum_union (sdiff_inter_self _ _)).symm
  ... = s₂.sum f : by rw [sdiff_union_of_subset h]

lemma sum_eq_zero_iff_of_nonneg : (∀x∈s, 0 ≤ f x) → (s.sum f = 0 ↔ ∀x∈s, f x = 0) :=
finset.induction_on s (λ _, ⟨λ _ _, false.elim, λ _, rfl⟩) $ λ a s ha ih H,
have ∀ x ∈ s, 0 ≤ f x, from λ _, H _ ∘ mem_insert_of_mem,
by rw [sum_insert ha,
  add_eq_zero_iff' (H _ $ mem_insert_self _ _) (zero_le_sum' this),
  forall_mem_insert, ih this]

lemma single_le_sum (hf : ∀x∈s, 0 ≤ f x) {a} (h : a ∈ s) : f a ≤ s.sum f :=
have (singleton a).sum f ≤ s.sum f,
  from sum_le_sum_of_subset_of_nonneg
  (λ x e, (mem_singleton.1 e).symm ▸ h) (λ x h _, hf x h),
by rwa sum_singleton at this

end ordered_comm_monoid

section canonically_ordered_monoid
variables [decidable_eq α] [canonically_ordered_monoid β] [@decidable_rel β (≤)]

lemma sum_le_sum_of_subset (h : s₁ ⊆ s₂) : s₁.sum f ≤ s₂.sum f :=
sum_le_sum_of_subset_of_nonneg h $ assume x h₁ h₂, zero_le _

lemma sum_le_sum_of_ne_zero (h : ∀x∈s₁, f x ≠ 0 → x ∈ s₂) : s₁.sum f ≤ s₂.sum f :=
calc s₁.sum f = (s₁.filter (λx, f x = 0)).sum f + (s₁.filter (λx, f x ≠ 0)).sum f :
    by rw [←sum_union, filter_union_filter_neg_eq]; apply filter_inter_filter_neg_eq
  ... ≤ s₂.sum f : add_le_of_nonpos_of_le'
      (sum_le_zero' $ by simp only [mem_filter, and_imp]; exact λ _ _, le_of_eq)
      (sum_le_sum_of_subset $ by simpa only [subset_iff, mem_filter, and_imp])

end canonically_ordered_monoid

section discrete_linear_ordered_field
variables [discrete_linear_ordered_field α] [decidable_eq β]

lemma abs_sum_le_sum_abs {f : β → α} {s : finset β} : abs (s.sum f) ≤ s.sum (λa, abs (f a)) :=
finset.induction_on s (le_of_eq abs_zero) $
  assume a s has ih,
  calc abs (sum (insert a s) f) ≤ abs (f a) + abs (sum s f) :
      by rw sum_insert has; exact abs_add_le_abs_add_abs _ _
    ... ≤ abs (f a) + s.sum (λa, abs (f a)) : add_le_add (le_refl _) ih
    ... ≤ sum (insert a s) (λ (a : β), abs (f a)) : by rw sum_insert has

end discrete_linear_ordered_field

@[simp] lemma card_pi [decidable_eq α] {δ : α → Type*}
  (s : finset α) (t : Π a, finset (δ a)) :
  (s.pi t).card = s.prod (λ a, card (t a)) :=
multiset.card_pi _ _

@[simp] lemma prod_range_id_eq_fact (n : ℕ) : ((range n.succ).erase 0).prod (λ x, x) = nat.fact n :=
calc ((range n.succ).erase 0).prod (λ x, x) = (range n).prod nat.succ :
eq.symm (prod_bij (λ x _, nat.succ x)
  (λ a h₁, mem_erase.2 ⟨nat.succ_ne_zero _, mem_range.2 $ nat.succ_lt_succ $ by simpa using h₁⟩)
  (by simp) (λ _ _ _ _, nat.succ_inj)
  (λ b h,
    have b.pred.succ = b, from nat.succ_pred_eq_of_pos $
      by simp [nat.pos_iff_ne_zero] at *; tauto,
    ⟨nat.pred b, mem_range.2 $ nat.lt_of_succ_lt_succ (by simp [*, - range_succ] at *), this.symm⟩))
... = nat.fact n : by induction n; simp *

end finset

section group

open list
variables [group α] [group β]

theorem is_group_hom.prod (f : α → β) [is_group_hom f] (l : list α) :
  f (prod l) = prod (map f l) :=
by induction l; simp only [*, is_group_hom.mul f, is_group_hom.one f, prod_nil, prod_cons, map]

theorem is_group_anti_hom.prod (f : α → β) [is_group_anti_hom f] (l : list α) :
  f (prod l) = prod (map f (reverse l)) :=
by induction l with hd tl ih; [exact is_group_anti_hom.one f,
  simp only [prod_cons, is_group_anti_hom.mul f, ih, reverse_cons, map_append, prod_append, map_singleton, prod_cons, prod_nil, mul_one]]

theorem inv_prod : ∀ l : list α, (prod l)⁻¹ = prod (map (λ x, x⁻¹) (reverse l)) :=
λ l, @is_group_anti_hom.prod _ _ _ _ _ inv_is_group_anti_hom l -- TODO there is probably a cleaner proof of this

end group

namespace multiset
variables [decidable_eq α]

@[simp] lemma to_finset_sum_count_eq (s : multiset α) :
  s.to_finset.sum (λa, s.count a) = s.card :=
multiset.induction_on s rfl
  (assume a s ih,
    calc (to_finset (a :: s)).sum (λx, count x (a :: s)) =
      (to_finset (a :: s)).sum (λx, (if x = a then 1 else 0) + count x s) :
        finset.sum_congr rfl $ λ _ _, by split_ifs;
        [simp only [h, count_cons_self, nat.one_add], simp only [count_cons_of_ne h, zero_add]]
      ... = card (a :: s) :
      begin
        by_cases a ∈ s.to_finset,
        { have : (to_finset s).sum (λx, ite (x = a) 1 0) = (finset.singleton a).sum (λx, ite (x = a) 1 0),
          { apply (finset.sum_subset _ _).symm,
            { intros _ H, rwa mem_singleton.1 H },
            { exact λ _ _ H, if_neg (mt finset.mem_singleton.2 H) } },
          rw [to_finset_cons, finset.insert_eq_of_mem h, finset.sum_add_distrib, ih, this, finset.sum_singleton, if_pos rfl, add_comm, card_cons] },
        { have ha : a ∉ s, by rwa mem_to_finset at h,
          have : (to_finset s).sum (λx, ite (x = a) 1 0) = (to_finset s).sum (λx, 0), from
            finset.sum_congr rfl (λ x hx, if_neg $ by rintro rfl; cc),
          rw [to_finset_cons, finset.sum_insert h, if_pos rfl, finset.sum_add_distrib, this, finset.sum_const_zero, ih, count_eq_zero_of_not_mem ha, zero_add, add_comm, card_cons] }
      end)

end multiset
