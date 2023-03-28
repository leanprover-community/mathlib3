/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import data.finset.pointwise
import data.set.pointwise.finite
import data.zmod.basic
import group_theory.quotient_group
import set_theory.cardinal.finite

/-!
# For mathlib

A lot of stuff to move
-/

namespace function
variables {α β γ : Type*}

@[simp] lemma on_fun_apply (f : β → β → γ) (g : α → β) (a b : α) :
  on_fun f g a b = f (g a) (g b) := rfl

end function

section dvd
variables {α : Type*} [monoid α] {a b : α}

lemma dvd_of_eq (h : a = b) : a ∣ b := by rw h
lemma dvd_of_eq' (h : a = b) : b ∣ a := by rw h

alias dvd_of_eq ← eq.dvd
alias dvd_of_eq' ← eq.dvd'
alias dvd_add ← has_dvd.dvd.add
alias dvd_sub ← has_dvd.dvd.sub

end dvd

lemma nat.le_of_lt_add_of_dvd {a b n : ℕ} (h : a < b + n) : n ∣ a → n ∣ b → a ≤ b :=
begin
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩,
  rw ←mul_add_one at h,
  exact mul_le_mul_left' (nat.lt_succ_iff.1 $ lt_of_mul_lt_mul_left h bot_le) _,
end

--TODO: Fix implicitness `subgroup.closure_eq_bot_iff`

section
variables {α β : Type*} {r r' : α → α → Prop} {f : β → α}

lemma well_founded.mono (hr : well_founded r) (h : ∀ a b, r' a b → r a b) : well_founded r' :=
subrelation.wf h hr

lemma well_founded.on_fun : well_founded r → well_founded (r on f) := inv_image.wf _

namespace set
variables {s : set α}

@[simp] lemma well_founded_on_univ : (univ : set α).well_founded_on r ↔ well_founded r :=
by simp [well_founded_on_iff]

lemma _root_.well_founded.well_founded_on (hr : well_founded r) : s.well_founded_on r :=
(well_founded_on_univ.2 hr).subset $ subset_univ _

lemma well_founded_on.mono' (h : ∀ a b ∈ s, r' a b → r a b) :
  s.well_founded_on r → s.well_founded_on r' :=
subrelation.wf $ λ a b, h _ a.2 _ b.2

@[simp] lemma well_founded_on_range : (range f).well_founded_on r ↔ well_founded (r on f) :=
begin
  let f' : β → range f := λ c, ⟨f c, c, rfl⟩,
  refine ⟨λ h, (inv_image.wf f' h).mono $ λ c c', id, λ h, ⟨_⟩⟩,
  rintro ⟨_, c, rfl⟩,
  refine acc.of_downward_closed f' _ _ _,
  { rintro _ ⟨_, c', rfl⟩ -,
    exact ⟨c', rfl⟩ },
  { apply h.apply }
end

end set
end

section
variables {α β γ : Type*} {rα : α  → α → Prop} {rβ : β → β → Prop} {f : γ → α} {g : γ → β}
  {s : set γ}

open prod

lemma well_founded.prod_lex (hα : well_founded (rα on f))
  (hβ : ∀ a, (f ⁻¹' {a}).well_founded_on (rβ on g)) :
  well_founded (prod.lex rα rβ on λ c, (f c, g c)) :=
begin
  let p : γ → Σ' a : set.range f, f⁻¹' {a} := λ c, ⟨⟨_, c, rfl⟩, c, rfl⟩,
  refine (inv_image.wf p $ psigma.lex_wf (set.well_founded_on_range.2 hα) $ λ a, hβ a).mono
    (λ c c' h, _),
  obtain h' | h' := prod.lex_iff.1 h,
  { exact psigma.lex.left _ _ h' },
  { dsimp only [inv_image, p, (on)] at h' ⊢,
    convert psigma.lex.right (⟨_, c', rfl⟩ : set.range f) _ using 1, swap,
    exacts [⟨c, h'.1⟩, psigma.subtype_ext (subtype.ext h'.1) rfl, h'.2] },
end

namespace set

lemma well_founded_on.prod_lex (hα : s.well_founded_on (rα on f))
  (hβ : ∀ a, (s ∩ f ⁻¹' {a}).well_founded_on (rβ on g)) :
  s.well_founded_on (prod.lex rα rβ on λ c, (f c, g c)) :=
begin
  refine well_founded.prod_lex hα (λ a, subrelation.wf (λ b c h, _) (hβ a).on_fun),
  exact λ x, ⟨x, x.1.2, x.2⟩,
  assumption,
end

end set
end

section
variables {ι : Sort*} {α : Type*} [conditionally_complete_linear_order_bot α] {f : ι → α} {a : α}

lemma cinfi_le_of_le' (c : ι) : f c ≤ a → infi f ≤ a := cinfi_le_of_le (order_bot.bdd_below _) _

end

namespace nat
variables {ι : Sort*}

@[simp] lemma infi_empty [is_empty ι] (f : ι → ℕ) : (⨅ i : ι, f i) = 0 :=
by rw [infi, set.range_eq_empty, Inf_empty]

@[simp] lemma infi_const_zero : (⨅ i : ι, 0 : ℕ) = 0 :=
begin
  casesI is_empty_or_nonempty ι,
  { exact infi_empty _ },
  { exact cinfi_const }
end

end nat

alias set.not_infinite ↔ _ set.finite.not_infinite

namespace finset
variables {α : Type*} [infinite α]

lemma exists_not_mem (s : finset α) : ∃ a, a ∉ s :=
by { by_contra' h, exact set.infinite_univ (s.finite_to_set.subset $ λ a _, h _) }

lemma exists_card : ∀ n : ℕ, ∃ s : finset α, s.card = n
| 0 := ⟨∅, card_empty⟩
| (n + 1) := begin
  classical,
  obtain ⟨s, rfl⟩ := exists_card n,
  obtain ⟨a, ha⟩ := s.exists_not_mem,
  exact ⟨insert a s, card_insert_of_not_mem ha⟩,
end

end finset

namespace nat
variables {α : Type*} {s t : set α}

open cardinal

lemma card_mono (ht : t.finite) (h : s ⊆ t) : nat.card s ≤ nat.card t :=
to_nat_le_of_le_of_lt_aleph_0 ht.lt_aleph_0 $ mk_le_mk_of_subset h

end nat

attribute [to_additive] finset.bUnion_smul_finset
attribute [protected] subgroup.subtype
attribute [protected] add_subgroup.subtype

namespace set
variables {α : Type*} {s : set α} {a b : α}

lemma singleton_subset_singleton : ({a} : set α) ⊆ {b} ↔ a = b := by simp

end set

namespace finset
variables {α : Type*} {s : finset α} {a : α}

/-- A finset is nontrivial if it has at least two elements. -/
@[reducible] protected def nontrivial' (s : finset α) : Prop := (s : set α).nontrivial

@[simp] lemma not_nontrivial_empty : ¬ (∅ : finset α).nontrivial' := by simp [finset.nontrivial']

@[simp] lemma not_nontrivial_singleton : ¬ ({a} : finset α).nontrivial' :=
by simp [finset.nontrivial']

lemma nontrivial'.ne_singleton (hs : s.nontrivial') : s ≠ {a} :=
by { rintro rfl, exact not_nontrivial_singleton hs }

lemma nontrivial_iff_ne_singleton (ha : a ∈ s) : s.nontrivial' ↔ s ≠ {a} :=
⟨nontrivial'.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩

lemma nontrivial'.one_lt_card : s.nontrivial' → 1 < s.card := finset.one_lt_card.2

end finset

namespace set
variables {α β γ : Type*} {f : α → β → γ} {s s₁ s₂ : set α} {t t₁ t₂ : set β} {u : set γ}

lemma image2_subset_iff_left : image2 f s t ⊆ u ↔ ∀ a ∈ s, f a '' t ⊆ u :=
by simp_rw [image2_subset_iff, image_subset_iff, subset_def, mem_preimage]

lemma image2_subset_iff_right : image2 f s t ⊆ u ↔ ∀ b ∈ t, (λ a, f a b) '' s ⊆ u :=
by rw [image2_swap, image2_subset_iff_left]

lemma image2_inter_union_subset_union :
  image2 f (s₁ ∩ s₂) (t₁ ∪ t₂) ⊆ image2 f s₁ t₁ ∪ image2 f s₂ t₂ :=
by { rw image2_union_right, exact union_subset_union
  (image2_subset_right $ inter_subset_left _ _) (image2_subset_right $ inter_subset_right _ _) }

lemma image2_union_inter_subset_union :
  image2 f (s₁ ∪ s₂) (t₁ ∩ t₂) ⊆ image2 f s₁ t₁ ∪ image2 f s₂ t₂ :=
by { rw image2_union_left, exact union_subset_union
  (image2_subset_left $ inter_subset_left _ _) (image2_subset_left $ inter_subset_right _ _) }

end set

namespace finset
variables {α β γ : Type*} [decidable_eq γ] {f : α → β → γ} {s s₁ s₂ : finset α} {t t₁ t₂ : finset β}
  {u : finset γ} {a : α} {b : β}

open function

lemma image₂_subset_iff_left : image₂ f s t ⊆ u ↔ ∀ a ∈ s, t.image (f a) ⊆ u :=
by simp_rw [image₂_subset_iff, image_subset_iff]

lemma image₂_subset_iff_right : image₂ f s t ⊆ u ↔ ∀ b ∈ t, s.image (λ a, f a b) ⊆ u :=
by rw [image₂_swap, image₂_subset_iff_left]

@[simp] lemma image₂_insert_left [decidable_eq α] :
  image₂ f (insert a s) t = t.image (f a) ∪ image₂ f s t :=
by rw [insert_eq, image₂_union_left, image₂_singleton_left]

@[simp] lemma image₂_insert_right [decidable_eq β] :
  image₂ f s (insert b t) = s.image (λ a, f a b) ∪ image₂ f s t :=
by rw [insert_eq, image₂_union_right, image₂_singleton_right]

lemma card_dvd_card_image₂_right (hf : ∀ a, injective (f a))
  (hs : ((λ a, t.image $ f a) '' s).pairwise_disjoint id) :
  t.card ∣ (image₂ f s t).card :=
begin
  classical,
  induction s using finset.induction with a s ha ih,
  { simp },
  specialize ih (hs.subset $ set.image_subset _ $ coe_subset.2 $ subset_insert _ _),
  rw image₂_insert_left,
  by_cases h : disjoint (image (f a) t) (image₂ f s t),
  { rw card_union_eq h,
    exact (card_image_of_injective _ $ hf _).dvd'.add ih },
  simp_rw [←bUnion_image_left, disjoint_bUnion_right, not_forall] at h,
  obtain ⟨b, hb, h⟩ := h,
  rwa union_eq_right_iff_subset.2,
  exact (hs.eq (set.mem_image_of_mem _ $ mem_insert_self _ _)
    (set.mem_image_of_mem _ $ mem_insert_of_mem hb) h).trans_subset (image_subset_image₂_right hb),
end

lemma card_dvd_card_image₂_left (hf : ∀ b, injective (λ a, f a b))
  (ht : ((λ b, s.image $ λ a, f a b) '' t).pairwise_disjoint id) :
  s.card ∣ (image₂ f s t).card :=
by { rw ←image₂_swap, exact card_dvd_card_image₂_right hf ht }

variables [decidable_eq α] [decidable_eq β]

lemma image₂_inter_union_subset_union :
  image₂ f (s₁ ∩ s₂) (t₁ ∪ t₂) ⊆ image₂ f s₁ t₁ ∪ image₂ f s₂ t₂ :=
coe_subset.1 $ by { push_cast, exact set.image2_inter_union_subset_union }

lemma image₂_union_inter_subset_union :
  image₂ f (s₁ ∪ s₂) (t₁ ∩ t₂) ⊆ image₂ f s₁ t₁ ∪ image₂ f s₂ t₂ :=
coe_subset.1 $ by { push_cast, exact set.image2_union_inter_subset_union }

end finset

open_locale pointwise

attribute [to_additive] finset.nonempty.inv finset.nonempty.of_inv

namespace set
variables {α : Type*} [has_mul α] {s t u : set α}

open mul_opposite

@[to_additive] lemma mul_subset_iff_left : s * t ⊆ u ↔ ∀ a ∈ s, a • t ⊆ u := image2_subset_iff_left
@[to_additive] lemma mul_subset_iff_right : s * t ⊆ u ↔ ∀ b ∈ t, op b • s ⊆ u :=
image2_subset_iff_right

end set

namespace finset
variables {α : Type*} [decidable_eq α] [has_mul α] {s t u : finset α}

open mul_opposite

@[to_additive] lemma mul_subset_iff_left : s * t ⊆ u ↔ ∀ a ∈ s, a • t ⊆ u := image₂_subset_iff_left
@[to_additive] lemma mul_subset_iff_right : s * t ⊆ u ↔ ∀ b ∈ t, op b • s ⊆ u :=
image₂_subset_iff_right

end finset

namespace set
variables {α : Type*} [has_mul α] {s s₁ s₂ t t₁ t₂ : set α}

@[to_additive] lemma inter_mul_union_subset_union : s₁ ∩ s₂ * (t₁ ∪ t₂) ⊆ (s₁ * t₁) ∪ (s₂ * t₂) :=
image2_inter_union_subset_union

@[to_additive] lemma union_mul_inter_subset_union : (s₁ ∪ s₂) * (t₁ ∩ t₂) ⊆ (s₁ * t₁) ∪ (s₂ * t₂) :=
image2_union_inter_subset_union

end set

namespace finset
variables {α : Type*} [decidable_eq α] [has_mul α] {s s₁ s₂ t t₁ t₂ : finset α}

@[to_additive] lemma inter_mul_union_subset_union : s₁ ∩ s₂ * (t₁ ∪ t₂) ⊆ (s₁ * t₁) ∪ (s₂ * t₂) :=
image₂_inter_union_subset_union

@[to_additive] lemma union_mul_inter_subset_union : (s₁ ∪ s₂) * (t₁ ∩ t₂) ⊆ (s₁ * t₁) ∪ (s₂ * t₂) :=
image₂_union_inter_subset_union

end finset

namespace set
variables {α β : Type*} {f : α → β} {s : set α}

lemma infinite.of_image : (f '' s).infinite → s.infinite := infinite_of_infinite_image _

end set

namespace set
variables {α β : Type*} [has_smul α β] {a : α} {s : set β}

@[to_additive] lemma infinite.of_smul_set : (a • s).infinite → s.infinite := infinite.of_image

end set

namespace set
variables {α β : Type*} [group α] [mul_action α β] {a : α} {s : set β}

@[simp, to_additive] lemma finite_smul_set : (a • s).finite ↔ s.finite :=
finite_image_iff $ (mul_action.injective _).inj_on _

@[simp, to_additive] lemma infinite_smul_set : (a • s).infinite ↔ s.infinite :=
infinite_image_iff $ (mul_action.injective _).inj_on _

alias finite_smul_set ↔ finite.of_smul_set _
alias infinite_smul_set ↔ _ infinite.smul_set

attribute [to_additive] finite.of_smul_set infinite.smul_set

end set

namespace set
variables {α : Type*} {s : set α}

lemma infinite_or_finite (s : set α) : s.infinite ∨ s.finite := em' _

lemma infinite.card_eq_zero (hs : s.infinite) : nat.card s = 0 :=
@nat.card_eq_zero_of_infinite _ hs.to_subtype

end set

namespace nat
variables {α β : Type*} [group α] [mul_action α β]

open cardinal

@[simp, to_additive] lemma card_smul_set (a : α) (s : set β) : nat.card ↥(a • s) = nat.card s :=
begin
  obtain hs | hs := s.infinite_or_finite,
  { rw [hs.card_eq_zero, hs.smul_set.card_eq_zero] },
  classical,
  lift s to finset β using hs,
  simp [←finset.coe_smul_finset],
end

end nat

namespace set
variables {α β : Type*} [has_smul α β] {s : set α} {t : set β} {a : α}

@[to_additive] lemma smul_set_subset_smul (ha : a ∈ s) : a • t ⊆ s • t :=
by { rw ←singleton_smul, exact smul_subset_smul_right (singleton_subset_iff.2 ha) }

end set

namespace finset
variables {α β : Type*} [has_smul α β] [decidable_eq β] {s : finset α} {t : finset β} {a : α}

@[to_additive] lemma smul_finset_subset_smul (ha : a ∈ s) : a • t ⊆ s • t :=
by { rw ←singleton_smul, exact smul_subset_smul_right (singleton_subset_iff.2 ha) }

end finset

namespace finset
variables {α β : Type*} [group α] [mul_action α β] [decidable_eq β] {s : finset α} {t : finset β}

@[to_additive] lemma card_dvd_card_smul_right :
  ((• t) '' (s : set α)).pairwise_disjoint id → t.card ∣ (s • t).card :=
card_dvd_card_image₂_right mul_action.injective

end finset

namespace set
variables {α : Type*} [has_mul α]

open mul_opposite

@[simp, to_additive] lemma singleton_mul' (a : α) (s : set α) : {a} * s = a • s := singleton_mul
@[simp, to_additive] lemma mul_singleton' (s : set α) (a : α) : s * {a} = op a • s := mul_singleton

end set

namespace set
variables {α β : Type*} [group α] [mul_action α β]

open mul_opposite

@[to_additive] lemma op_smul_set_smul_eq_smul_smul_set (s : set α) (a : α) (t : set β) :
  (op a • s) • t = s • a • t :=
by rw [←mul_singleton', ←singleton_smul, mul_smul]

@[to_additive] lemma op_smul_set_mul_eq_mul_smul_set (s : set α) (a : α) (t : set α) :
  (op a • s) * t = s * a • t :=
op_smul_set_smul_eq_smul_smul_set _ _ _

end set

namespace finset
variables {α : Type*} [decidable_eq α] [has_mul α]

open mul_opposite

@[simp, to_additive] lemma singleton_mul' (a : α) (s : finset α) : {a} * s = a • s :=
singleton_mul _

@[simp, to_additive] lemma mul_singleton' (s : finset α) (a : α) : s * {a} = op a • s :=
mul_singleton _

end finset

namespace finset
variables {α β : Type*} [decidable_eq α] [decidable_eq β] [group α] [mul_action α β]

open mul_opposite

@[to_additive] lemma op_smul_finset_smul_eq_smul_smul_finset (s : finset α) (a : α) (t : finset β) :
  (op a • s) • t = s • a • t :=
by rw [←mul_singleton', ←singleton_smul, mul_smul]

@[to_additive] lemma op_smul_finset_mul_eq_mul_smul_finset (s : finset α) (a : α) (t : finset α) :
  (op a • s) * t = s * a • t :=
op_smul_finset_smul_eq_smul_smul_finset _ _ _

end finset

namespace subgroup
variables {α : Type*} [group α] {H : subgroup α} [subgroup.normal H] {s t : set α}

open set

@[to_additive]
lemma image_coe_quotient (H : subgroup α) [H.normal] : (coe : α → α ⧸ H) '' H = 1 :=
begin
  ext a,
  dsimp,
  split,
  { rintro ⟨a, ha, rfl⟩,
    rwa [quotient_group.eq_one_iff] },
  { rintro rfl,
    exact ⟨1, H.one_mem, rfl⟩ }
end

@[to_additive] lemma preimage_image_coe (s : set α) : (coe : α → α ⧸ H) ⁻¹' (coe '' s) = H * s :=
begin
  ext a,
  split,
  { rintro ⟨b, hb, h⟩,
    refine ⟨a / b, b, (quotient_group.eq_one_iff _).1 _, hb, div_mul_cancel' _ _⟩,
    simp only [h, quotient_group.coe_div, div_self'] },
  { rintro ⟨a, b, ha, hb, rfl⟩,
    refine ⟨b, hb, _⟩,
    simpa only [quotient_group.coe_mul, self_eq_mul_left, quotient_group.eq_one_iff] }
end

@[to_additive]
lemma image_coe_inj : (coe : α → α ⧸ H) '' s = (coe : α → α ⧸ H) '' t ↔ ↑H * s = H * t :=
by { simp_rw ←preimage_image_coe,
  exact quotient_group.mk_surjective.preimage_injective.eq_iff.symm }

end subgroup

namespace submonoid
variables {G α β : Type*} [monoid G] [has_smul G α] {S : submonoid G}

@[simp, to_additive] lemma mk_smul (g : G) (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

end submonoid

namespace subgroup
variables {G α β : Type*} [group G] [mul_action G α] {S : subgroup G}

@[simp, to_additive] lemma mk_smul (g : G) (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

end subgroup

namespace subgroup
variables {α : Type*} [group α] {s : subgroup α} {a : α}

@[simp, to_additive] lemma coe_sort_coe (s : subgroup α) : ↥(s : set α) = ↥s := rfl

@[to_additive] lemma smul_coe (ha : a ∈ s) : a • (s : set α) = s :=
by { ext, rw set.mem_smul_set_iff_inv_smul_mem, exact subgroup.mul_mem_cancel_left _ (inv_mem ha) }

end subgroup

namespace subgroup
variables {α : Type*} [comm_group α] {s : subgroup α} {a : α}

@[to_additive]
lemma mul_alt_version (N : subgroup α) (s : set α) :
  coe ⁻¹' ((coe : α → α ⧸ N) '' s) = ⋃ x : N, x • s :=
by { simp_rw [quotient_group.preimage_image_coe N s, mul_comm _ (coe _), ← set.Union_inv_smul,
    ←set.preimage_smul _ s], congr }

end subgroup

namespace subgroup
variables {α β : Type*} [group α] [group β] [mul_action α β] [is_scalar_tower α β β]

open set

@[to_additive] lemma pairwise_disjoint_smul (s : subgroup β) :
  (set.range $ λ a : α, a • (s : set β)).pairwise_disjoint id :=
begin
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab,
  dsimp at ⊢ hab,
  rw disjoint_left,
  rintro _ ⟨c, hc, rfl⟩ ⟨d, hd, hcd⟩,
  refine hab _,
  rw [←smul_coe hc, ←smul_assoc, ←hcd, smul_assoc, smul_coe hc, smul_coe hd],
end

end subgroup

namespace mul_action
variables {α β γ : Type*} [group α] [mul_action α β] [mul_action α γ] {a : α}

open function set

section set

@[simp, to_additive] lemma stabilizer_empty : stabilizer α (∅ : set β) = ⊤ :=
subgroup.coe_eq_univ.1 $ eq_univ_of_forall $ λ a, smul_set_empty

@[simp, to_additive] lemma stabilizer_singleton (b : β) :
  stabilizer α ({b} : set β) = stabilizer α b :=
by { ext, simp }

@[to_additive] lemma mem_stabilizer_set {s : set β} :
  a ∈ stabilizer α s ↔ ∀ b, a • b ∈ s ↔ b ∈ s :=
begin
  refine ⟨λ h b, _, λ h, _⟩,
  { rw [←(smul_mem_smul_set_iff : a • b ∈ a • s ↔ _), mem_stabilizer_iff.1 h] },
  simp_rw [mem_stabilizer_iff, set.ext_iff, mem_smul_set_iff_inv_smul_mem],
  exact ((mul_action.to_perm a).forall_congr' $ by simp [iff.comm]).1 h,
end

@[simp, to_additive] lemma stabilizer_subgroup (s : subgroup α) : stabilizer α (s : set α) = s :=
begin
  simp_rw [set_like.ext_iff, mem_stabilizer_set],
  refine λ a, ⟨λ h, _, λ ha b, s.mul_mem_cancel_left ha⟩,
  convert (h 1).2 s.one_mem,
  exact (mul_one _).symm,
end

@[to_additive] lemma map_stabilizer_le (f : α →* α) (s : set α) :
  (stabilizer α s).map f ≤ stabilizer α (f '' s) :=
begin
  rintro a,
  simp only [subgroup.mem_map, mem_stabilizer_iff, exists_prop, forall_exists_index, and_imp],
  rintro a ha rfl,
  rw [←image_smul_distrib, ha],
end

@[simp, to_additive] lemma stabilizer_mul (s : set α) : (stabilizer α s : set α) * s = s :=
begin
  ext,
  refine ⟨_, λ h, ⟨_, _, (stabilizer α s).one_mem, h, one_mul _⟩⟩,
  rintro ⟨a, b, ha, hb, rfl⟩,
  rw ←mem_stabilizer_iff.1 ha,
  exact smul_mem_smul_set hb,
end

@[to_additive]
lemma le_stabilizer_smul_left [has_smul β γ] [is_scalar_tower α β γ] (b : β) (c : γ) :
  stabilizer α b ≤ stabilizer α (b • c) :=
by { simp_rw [set_like.le_def, mem_stabilizer_iff, ←smul_assoc], rintro a h, rw h }

@[simp, to_additive]
lemma stabilizer_mul_eq_left [group β] [is_scalar_tower α β β] (b c : β) :
  stabilizer α (b * c) = stabilizer α b :=
begin
  rw ←smul_eq_mul,
  refine (le_stabilizer_smul_left _ _).antisymm' (λ a ha, _),
  dsimp at ha,
  rwa [←smul_mul_assoc, mul_left_inj] at ha,
end

end set

@[to_additive]
lemma le_stabilizer_smul_right {α} [group α] [mul_action α γ] [has_smul β γ] [smul_comm_class α β γ]
  (b : β) (c : γ) :
  stabilizer α c ≤ stabilizer α (b • c) :=
by { simp_rw [set_like.le_def, mem_stabilizer_iff, smul_comm], rintro a h, rw h }

@[simp, to_additive]
lemma stabilizer_smul_eq_right {α} [group α] [group β] [mul_action α γ] [mul_action β γ]
  [smul_comm_class α β γ] (b : β) (c : γ) :
  stabilizer α (b • c) = stabilizer α c :=
(le_stabilizer_smul_right _ _).antisymm' $ (le_stabilizer_smul_right b⁻¹ _).trans_eq $
  by rw inv_smul_smul

section decidable_eq
variables [decidable_eq β]

@[simp, to_additive] lemma stabilizer_coe_finset (s : finset β) :
  stabilizer α (s : set β) = stabilizer α s :=
by { ext, simp [←finset.coe_smul_finset] }

@[simp, to_additive] lemma stabilizer_finset_empty : stabilizer α (∅ : finset β) = ⊤ :=
subgroup.coe_eq_univ.1 $ eq_univ_of_forall finset.smul_finset_empty

@[simp, to_additive] lemma stabilizer_finset_singleton (b : β) :
  stabilizer α ({b} : finset β) = stabilizer α b :=
by { ext, simp }

@[to_additive] lemma mem_stabilizer_finset {s : finset β} :
  a ∈ stabilizer α s ↔ ∀ b, a • b ∈ s ↔ b ∈ s :=
by simp_rw [←stabilizer_coe_finset, mem_stabilizer_set, finset.mem_coe]

@[to_additive] lemma mem_stabilizer_finset_iff_subset_smul_finset {s : finset β} :
  a ∈ stabilizer α s ↔ s ⊆ a • s :=
by rw [mem_stabilizer_iff, finset.subset_iff_eq_of_card_le (finset.card_smul_finset _ _).le,
  eq_comm]

@[to_additive] lemma mem_stabilizer_finset_iff_smul_finset_subset {s : finset β} :
  a ∈ stabilizer α s ↔ a • s ⊆ s :=
by rw [mem_stabilizer_iff, finset.subset_iff_eq_of_card_le (finset.card_smul_finset _ _).ge]

@[to_additive] lemma mem_stabilizer_finset' {s : finset β} :
  a ∈ stabilizer α s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s :=
by { rw [←subgroup.inv_mem_iff, mem_stabilizer_finset_iff_subset_smul_finset],
  simp_rw [←finset.mem_inv_smul_finset_iff, finset.subset_iff] }

end decidable_eq

@[to_additive] lemma mem_stabilizer_set_iff_subset_smul_set {s : set β} (hs : s.finite) :
  a ∈ stabilizer α s ↔ s ⊆ a • s :=
by { lift s to finset β using hs, classical, norm_cast,
  simp [mem_stabilizer_finset_iff_subset_smul_finset] }

@[to_additive] lemma mem_stabilizer_set_iff_smul_set_subset {s : set β} (hs : s.finite) :
  a ∈ stabilizer α s ↔ a • s ⊆ s :=
by { lift s to finset β using hs, classical, norm_cast,
  simp [mem_stabilizer_finset_iff_smul_finset_subset] }

@[to_additive] lemma mem_stabilizer_set' {s : set β} (hs : s.finite) :
  a ∈ stabilizer α s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s :=
by { lift s to finset β using hs, classical, simp [mem_stabilizer_finset'] }

end mul_action

namespace mul_action
variables {α : Type*} [comm_group α] {s : set α}

open function set
open_locale pointwise

@[simp, to_additive] lemma mul_stabilizer (s : set α) : s * (stabilizer α s : set α) = s :=
by rw [mul_comm, stabilizer_mul]

@[to_additive] lemma stabilizer_image_coe_quotient (s : set α) :
  stabilizer (α ⧸ stabilizer α s) ((coe : α → α ⧸ stabilizer α s) '' s) = ⊥ :=
begin
  ext a,
  induction a using quotient_group.induction_on',
  simp only [mem_stabilizer_iff, subgroup.mem_bot, quotient_group.eq_one_iff],
  have : ↑a • (coe : α → α ⧸ stabilizer α s) '' s = coe '' (a • s) :=
    (image_smul_distrib (quotient_group.mk' $ stabilizer α s) _ _).symm,
  rw this,
  refine ⟨λ h, _, λ h, by rw h⟩,
  rwa [subgroup.image_coe_inj, mul_smul_comm, stabilizer_mul] at h,
end

end mul_action

namespace subgroup
variables {G : Type*} [group G] {s : set G} {g : G}

-- TODO: Rename `zpower_subset` → `zpowers_le`

@[to_additive zmultiples_ne_bot] lemma zpowers_ne_bot : zpowers g ≠ ⊥ ↔ g ≠ 1 := zpowers_eq_bot.not

@[to_additive coe_zmultiplies_subset] lemma coe_zpowers_subset (h_one : (1 : G) ∈ s)
  (h_mul : ∀ a ∈ s, a * g ∈ s) (h_inv : ∀ a ∈ s, a * g⁻¹ ∈ s) : ↑(zpowers g) ⊆ s :=
begin
  rintro _ ⟨n, rfl⟩,
  induction n using int.induction_on with n ih n ih,
  { rwa zpow_zero },
  { rw zpow_add_one,
    exact h_mul _ ih },
  { rw zpow_sub_one,
    exact h_inv _ ih }
end

@[to_additive coe_zmultiplies_subset'] lemma coe_zpowers_subset' (h_one : (1 : G) ∈ s)
  (h_mul : ∀ a ∈ s, g * a ∈ s) (h_inv : ∀ a ∈ s, g⁻¹ * a ∈ s) : ↑(zpowers g) ⊆ s :=
begin
  rintro _ ⟨n, rfl⟩,
  induction n using int.induction_on with n ih n ih,
  { rwa zpow_zero },
  { rw [add_comm, zpow_add, zpow_one],
    exact h_mul _ ih },
  { rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one],
    exact h_inv _ ih }
end

end subgroup

namespace char_p
variables {R : Type*} [add_group_with_one R] (p : ℕ) [char_p R p] {a b n : ℕ}

--TODO: Deduplicate `char_p.int_coe_eq_int_coe_iff`, `eq_iff_modeq_int`.
-- Rename to `char_p.int_cast_eq_int_cast`

lemma cast_eq_cast : (a : R) = b ↔ a ≡ b [MOD p] :=
begin
  rw [←int.cast_coe_nat, ←int.cast_coe_nat b],
  exact (int_coe_eq_int_coe_iff _ _ _ _).trans int.coe_nat_modeq_iff,
end

-- lemma add_order_of_cast (hn : n ≠ 0) : add_order_of (n : R) = p / p.gcd n := sorry

end char_p

namespace int

-- @[simp, norm_cast] lemma coe_nat_mod' (m n : ℤ) : (m.nat_mod n : ℤ) = m % n := sorry

namespace modeq
variables {a b c m : ℤ}

-- TODO: Rename `int.gcd_pos_of_non_zero_left` → `int.gcd_pos_of_ne_zero_left`

/-- To cancel a common factor `c` from a `modeq` we must divide the modulus `m` by `gcd m c` -/
lemma cancel_left_div_gcd (hm : 0 < m) (h : c * a ≡ c * b [ZMOD m]) : a ≡ b [ZMOD m / gcd m c] :=
begin
  let d := gcd m c,
  have hmd := gcd_dvd_left m c,
  have hcd := gcd_dvd_right m c,
  rw modeq_iff_dvd at ⊢ h,
  refine int.dvd_of_dvd_mul_right_of_gcd_one _ _,
  show m / d ∣ c / d * (b - a),
  { rw [mul_comm, ←int.mul_div_assoc (b - a) hcd, mul_comm],
    apply int.div_dvd_div hmd,
    rwa mul_sub },
  { rw [gcd_div hmd hcd, nat_abs_of_nat, nat.div_self (gcd_pos_of_non_zero_left c hm.ne')] }
end

lemma cancel_right_div_gcd (hm : 0 < m) (h : a * c ≡ b * c [ZMOD m]) : a ≡ b [ZMOD m / gcd m c] :=
by { apply cancel_left_div_gcd hm, simpa [mul_comm] using h }

-- TODO: Surely we don't need `0 ≤ c`?
lemma of_div (hc : 0 ≤ c) (h : a / c ≡ b / c [ZMOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m) :
  a ≡ b [ZMOD m] :=
by convert h.mul_left' hc; rwa int.mul_div_cancel'

end modeq
end int

namespace nat
namespace modeq
variables {a b c m : ℕ}

lemma of_div (h : a / c ≡ b / c [MOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m) :
  a ≡ b [MOD m] :=
by convert h.mul_left' c; rwa nat.mul_div_cancel'

end modeq
end nat

instance : unique (zmod 1) := fin.unique
