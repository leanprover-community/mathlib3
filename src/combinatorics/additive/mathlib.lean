/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import data.finset.pointwise
import data.set.pointwise.finite
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

--TODO: Fix implicitness `finset.not_subset`, `subgroup.closure_eq_bot_iff`

section generalized_boolean_algebra
variables {α : Type*} [generalized_boolean_algebra α] {a b c : α}

lemma le_sdiff : a ≤ b \ c ↔ a ≤ b ∧ disjoint a c :=
⟨λ h, ⟨h.trans sdiff_le, disjoint_sdiff_self_left.mono_left h⟩, λ h,
  by { rw ←h.2.sdiff_eq_left, exact sdiff_le_sdiff_right h.1 }⟩

@[simp] lemma sdiff_eq_left : a \ b = a ↔ disjoint a b :=
⟨λ h, disjoint_sdiff_self_left.mono_left h.ge, disjoint.sdiff_eq_left⟩

end generalized_boolean_algebra

section partial_order
variables {α : Type*} [partial_order α] {a b : α}

lemma gt_or_eq_of_le (hab : a ≤ b) : a < b ∨ b = a := (eq_or_gt_of_le hab).symm

alias gt_or_eq_of_le  ← has_le.le.gt_or_eq

end partial_order

section linear_order
variables {α : Type*} [linear_order α] [has_mul α]

open function

@[to_additive] lemma le_or_lt_of_mul_le_mul [covariant_class α α (*) (≤)]
  [covariant_class α α (swap (*)) (<)] {a₁ a₂ b₁ b₂ : α} :
  a₁ * b₁ ≤ a₂ * b₂ → a₁ ≤ a₂ ∨ b₁ < b₂ :=
by { contrapose!, exact λ h, mul_lt_mul_of_lt_of_le h.1 h.2 }

@[to_additive] lemma lt_or_le_of_mul_le_mul [covariant_class α α (*) (<)]
  [covariant_class α α (swap (*)) (≤)] {a₁ a₂ b₁ b₂ : α} :
  a₁ * b₁ ≤ a₂ * b₂ → a₁ < a₂ ∨ b₁ ≤ b₂ :=
by { contrapose!, exact λ h, mul_lt_mul_of_le_of_lt h.1 h.2 }

@[to_additive] lemma le_or_le_of_mul_le_mul [covariant_class α α (*) (<)]
  [covariant_class α α (swap (*)) (<)] {a₁ a₂ b₁ b₂ : α} :
  a₁ * b₁ ≤ a₂ * b₂ → a₁ ≤ a₂ ∨ b₁ ≤ b₂ :=
by { contrapose!, exact λ h, mul_lt_mul_of_lt_of_lt h.1 h.2 }

end linear_order

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

section canonically_ordered_monoid
variables {α : Type*} [canonically_ordered_monoid α] {a b c : α}

@[to_additive] lemma le_mul_of_le_left : a ≤ b → a ≤ b * c := le_self_mul.trans'
@[to_additive] lemma le_mul_of_le_right : a ≤ c → a ≤ b * c := le_mul_self.trans'

end canonically_ordered_monoid

namespace nat
variables {α : Type*} {s t : set α}

open cardinal

lemma card_mono (ht : t.finite) (h : s ⊆ t) : nat.card s ≤ nat.card t :=
to_nat_le_of_le_of_lt_aleph_0 ht.lt_aleph_0 $ mk_le_mk_of_subset h

end nat

attribute [to_additive] finset.bUnion_smul_finset
attribute [simp] finset.singleton_inj
attribute [protected] subgroup.subtype
attribute [protected] add_subgroup.subtype

section subset
variables {α : Type*} [has_subset α] {a b c : α}

lemma subset_of_eq_of_subset (hab : a = b) (hbc : b ⊆ c) : a ⊆ c := by rwa hab
lemma subset_of_subset_of_eq (hab : a ⊆ b) (hbc : b = c) : a ⊆ c := by rwa ←hbc

alias subset_of_eq_of_subset ← eq.trans_subset
alias subset_of_subset_of_eq ← has_subset.subset.trans_eq

end subset

section ssubset
variables {α : Type*} [has_ssubset α] {a b c : α}

lemma ssubset_of_eq_of_ssubset (hab : a = b) (hbc : b ⊂ c) : a ⊂ c := by rwa hab
lemma ssubset_of_ssubset_of_eq (hab : a ⊂ b) (hbc : b = c) : a ⊂ c := by rwa ←hbc

alias ssubset_of_eq_of_ssubset ← eq.trans_ssubset
alias ssubset_of_ssubset_of_eq ← has_ssubset.ssubset.trans_eq

end ssubset

namespace set
variables {α : Type*} {s : set α} {a b : α}

lemma nonempty.exists_eq_singleton_or_nontrivial : s.nonempty → (∃ a, s = {a}) ∨ s.nontrivial :=
λ ⟨a, ha⟩, (eq_singleton_or_nontrivial ha).imp_left $ exists.intro a

lemma singleton_subset_singleton : ({a} : set α) ⊆ {b} ↔ a = b := by simp

end set

namespace finset
variables {α : Type*} {s : finset α} {a b : α}

lemma nonempty.exists_eq_singleton_or_nontrivial :
  s.nonempty → (∃ a, s = {a}) ∨ (s : set α).nontrivial :=
λ ⟨a, ha⟩, (eq_singleton_or_nontrivial ha).imp_left $ exists.intro a

lemma singleton_subset_singleton : ({a} : finset α) ⊆ {b} ↔ a = b := by simp

end finset

namespace finset
variables {α : Type*} [decidable_eq α] {s t u : finset α}

lemma not_disjoint_iff_nonempty_inter : ¬disjoint s t ↔ (s ∩ t).nonempty :=
not_disjoint_iff.trans $ by simp [finset.nonempty]

alias not_disjoint_iff_nonempty_inter ↔ _ nonempty.not_disjoint

lemma disjoint_or_nonempty_inter (s t : finset α) : disjoint s t ∨ (s ∩ t).nonempty :=
by { rw ←not_disjoint_iff_nonempty_inter, exact em _ }

lemma inter_subset_union : s ∩ t ⊆ s ∪ t := le_iff_subset.1 inf_le_sup

lemma subset_sdiff : s ⊆ t \ u ↔ s ⊆ t ∧ disjoint s u := le_iff_subset.symm.trans le_sdiff

lemma card_inter_add_card_union (s t : finset α) : (s ∩ t).card + (s ∪ t).card = s.card + t.card :=
by rw [add_comm, card_union_add_card_inter]

lemma card_le_card_sdiff_add_card : s.card ≤ (s \ t).card + t.card :=
tsub_le_iff_right.1 $ le_card_sdiff _ _

end finset

namespace finset
variables {α : Type*} {s t : finset α}

lemma eq_of_superset_of_card_ge (hst : s ⊆ t) (hts : t.card ≤ s.card) : t = s :=
(eq_of_subset_of_card_le hst hts).symm

lemma subset_iff_eq_of_card_le (h : t.card ≤ s.card) : s ⊆ t ↔ s = t :=
⟨λ hst, eq_of_subset_of_card_le hst h, eq.subset'⟩

end finset

namespace set
variables {β : Type*} {ι : Sort*} [nonempty ι] {f : ι → set β} {s : set β}

lemma Union_eq_const (hf : ∀ i, f i = s) : (⋃ i, f i) = s := (Union_congr hf).trans $ Union_const _
lemma Inter_eq_const (hf : ∀ i, f i = s) : (⋂ i, f i) = s := (Inter_congr hf).trans $ Inter_const _

end set

namespace set
variables {α : Type*} {s : set α} {a : α}

lemma nontrivial_iff_ne_singleton (ha : a ∈ s) : s.nontrivial ↔ s ≠ {a} :=
⟨nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩

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

@[simp]
lemma to_finset_image2 [decidable_eq γ] (f : α → β → γ) (s : set α) (t : set β) [fintype s]
  [fintype t] [fintype (image2 f s t)] :
  (image2 f s t).to_finset = finset.image₂ f s.to_finset t.to_finset :=
finset.coe_injective $ by simp

lemma finite.to_finset_image2 [decidable_eq γ] (f : α → β → γ) (hs : s.finite) (ht : t.finite)
  (hf := hs.image2 f ht) :
  hf.to_finset = finset.image₂ f hs.to_finset ht.to_finset :=
finset.coe_injective $ by simp

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

namespace set
variables {α β : Type*} {f : α → α → β} {s t : set α}

lemma image2_inter_union_subset (hf : ∀ a b, f a b = f b a) :
  image2 f (s ∩ t) (s ∪ t) ⊆ image2 f s t :=
by { rw inter_comm,
  exact image2_inter_union_subset_union.trans (union_subset (image2_comm hf).subset subset.rfl) }

lemma image2_union_inter_subset (hf : ∀ a b, f a b = f b a) :
  image2 f (s ∪ t) (s ∩ t) ⊆ image2 f s t :=
by { rw image2_comm hf, exact image2_inter_union_subset hf }

end set

namespace finset
variables {α β : Type*} [decidable_eq α] [decidable_eq β] {f : α → α → β} {s t : finset α}

lemma image₂_inter_union_subset (hf : ∀ a b, f a b = f b a) :
  image₂ f (s ∩ t) (s ∪ t) ⊆ image₂ f s t :=
coe_subset.1 $ by { push_cast, exact set.image2_inter_union_subset hf }

lemma image₂_union_inter_subset (hf : ∀ a b, f a b = f b a) :
  image₂ f (s ∪ t) (s ∩ t) ⊆ image₂ f s t :=
coe_subset.1 $ by { push_cast, exact set.image2_union_inter_subset hf }

end finset

attribute [simp] finset.singleton_inj

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

namespace finset
variables {α : Type*} [has_one α]

@[simp, to_additive] lemma card_one : (1 : finset α).card = 1 := card_singleton _

end finset

namespace finset
variables {α β : Type*} [group α] [mul_action α β] [decidable_eq β]

@[simp, to_additive] lemma card_smul_finset (a : α) (s : finset β) : (a • s).card = s.card :=
card_image_of_injective _ $ mul_action.injective _

end finset

namespace set
variables {α : Type*} [has_mul α] {s s₁ s₂ t t₁ t₂ : set α}

@[to_additive] lemma inter_mul_union_subset_union : s₁ ∩ s₂ * (t₁ ∪ t₂) ⊆ (s₁ * t₁) ∪ (s₂ * t₂) :=
image2_inter_union_subset_union

@[to_additive] lemma union_mul_inter_subset_union : (s₁ ∪ s₂) * (t₁ ∩ t₂) ⊆ (s₁ * t₁) ∪ (s₂ * t₂) :=
image2_union_inter_subset_union

end set

namespace set
variables {α : Type*} [comm_semigroup α] {s t : set α}

@[to_additive] lemma inter_mul_union_subset : s ∩ t * (s ∪ t) ⊆ s * t :=
image2_inter_union_subset mul_comm

@[to_additive] lemma union_mul_inter_subset : (s ∪ t) * (s ∩ t) ⊆ s * t :=
image2_union_inter_subset mul_comm

end set

namespace finset
variables {α : Type*} [decidable_eq α] [has_mul α] {s s₁ s₂ t t₁ t₂ : finset α}

@[to_additive] lemma inter_mul_union_subset_union : s₁ ∩ s₂ * (t₁ ∪ t₂) ⊆ (s₁ * t₁) ∪ (s₂ * t₂) :=
image₂_inter_union_subset_union

@[to_additive] lemma union_mul_inter_subset_union : (s₁ ∪ s₂) * (t₁ ∩ t₂) ⊆ (s₁ * t₁) ∪ (s₂ * t₂) :=
image₂_union_inter_subset_union

end finset

namespace finset
variables {α : Type*} [decidable_eq α] [comm_semigroup α] {s s₁ s₂ t t₁ t₂ : finset α}

@[to_additive] lemma inter_mul_union_subset : s ∩ t * (s ∪ t) ⊆ s * t :=
image₂_inter_union_subset mul_comm

@[to_additive] lemma union_mul_inter_subset : (s ∪ t) * (s ∩ t) ⊆ s * t :=
image₂_union_inter_subset mul_comm

end finset

namespace set
variables {α β : Type*}

section has_one
variables [has_one α]

@[simp, to_additive] lemma finite_one : (1 : set α).finite := finite_singleton _

@[simp, to_additive] lemma to_finset_one : (1 : set α).to_finset = 1 := rfl

@[simp, to_additive]
lemma finite.to_finset_one (h : (1 : set α).finite := finite_one) : h.to_finset = 1 :=
finite.to_finset_singleton _

end has_one

section has_mul
variables [has_mul α] [decidable_eq α] {s t : set α}

@[simp, to_additive] lemma to_finset_mul (s t : set α) [fintype s] [fintype t] [fintype ↥(s * t)] :
  (s * t).to_finset = s.to_finset * t.to_finset :=
to_finset_image2 _ _ _

@[simp, to_additive] lemma finite.to_finset_mul (hs : s.finite) (ht : t.finite) (hf := hs.mul ht) :
  hf.to_finset = hs.to_finset * ht.to_finset :=
finite.to_finset_image2 _ _ _

end has_mul

section has_smul
variables [has_smul α β] [decidable_eq β] {a : α} {s : set α} {t : set β}

@[simp, to_additive]
lemma to_finset_smul (s : set α) (t : set β) [fintype s] [fintype t] [fintype ↥(s • t)] :
  (s • t).to_finset = s.to_finset • t.to_finset :=
to_finset_image2 _ _ _

@[simp, to_additive]
lemma finite.to_finset_smul (hs : s.finite) (ht : t.finite) (hf := hs.smul ht) :
  hf.to_finset = hs.to_finset • ht.to_finset :=
finite.to_finset_image2 _ _ _

end has_smul

section has_smul
variables [has_smul α β] [decidable_eq β] {a : α} {s : set β}

@[simp, to_additive]
lemma to_finset_smul_set (a : α) (s : set β) [fintype s] [fintype ↥(a • s)] :
  (a • s).to_finset = a • s.to_finset :=
to_finset_image _ _

@[simp, to_additive]
lemma finite.to_finset_smul_set (hs : s.finite) (hf : (a • s).finite := hs.smul_set) :
  hf.to_finset = a • hs.to_finset :=
finite.to_finset_image _ _ _

end has_smul
end set

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

namespace finset
variables {α : Type*} [group α] [decidable_eq α] {s t : finset α}

@[to_additive] lemma card_dvd_card_mul_left :
  ((λ b, s.image $ λ a, a * b) '' (t : set α)).pairwise_disjoint id → s.card ∣ (s * t).card :=
card_dvd_card_image₂_left mul_left_injective

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

namespace set
variables {α β γ : Type*}

section
variables [has_smul α β] [has_smul α γ]

@[to_additive] lemma smul_image (f : β → γ) (s : set β) (a : α) :
  (∀ b, a • f b = f (a • b)) → a • f '' s = f '' (a • s) :=
image_comm

end

variables [monoid α] [monoid β]

@[to_additive] lemma image_smul' (f : α →* β) (s : set α) (a : α) : f '' (a • s) = f a • f '' s :=
image_comm $ map_mul _ _

end set

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
  rw [←image_smul', ha],
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
    (image_smul' (quotient_group.mk' _) _ _).symm,
  rw this,
  refine ⟨λ h, _, λ h, by rw h⟩,
  rwa [subgroup.image_coe_inj, mul_smul_comm, stabilizer_mul] at h,
end

end mul_action

instance : unique (zmod 1) := fin.unique

namespace zmod

open add_subgroup finset

@[simp] lemma card_zmultiples (n a : ℕ) [fintype.{0} (zmultiples (a : zmod n))] :
  fintype.card (zmultiples (a : zmod n)) = n / n.gcd a :=
begin
  have : ((range (n / n.gcd a)).image (λ b, (n.gcd a * ↑b : zmod n)) : set (zmod n)) =
    zmultiples (a : zmod n),
  { ext b,
    simp only [mem_closure_singleton, coe_image, set.mem_image, mem_coe, mem_range,
      set_like.mem_coe, zsmul_eq_mul],
    split,
    { rintro ⟨m, hm, rfl⟩,
      sorry },
    { rintro ⟨m, rfl⟩,
      refine ⟨m.nat_mod (n / n.gcd a), sorry, _⟩,
      sorry } },
  simp_rw [←add_subgroup.coe_sort_coe, ←this, finset.coe_sort_coe, fintype.card_coe],
  rw [card_image_of_inj_on, card_range],
  rintro b hb c hc h,
  dsimp at *,
  simp_rw ←nat.cast_mul at h,
  sorry,
end

end zmod
