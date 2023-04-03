/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import data.finset.pointwise
import data.set.pointwise.finite
import data.zmod.quotient
import group_theory.quotient_group
import group_theory.torsion
import set_theory.cardinal.finite

/-!
# For mathlib

A lot of stuff to move
-/

set_option old_structure_cmd true

/-- An `add_cancel_semigroup` is an additive semigroup such that `a + b = a + c` implies `b = c`,
and `a + c = b + c` implies `a = b`. -/
class add_cancel_semigroup (α : Type*)
  extends add_left_cancel_semigroup α, add_right_cancel_semigroup α

/-- A `cancel_semigroup` is a semigroup such that `a * b = a * c` implies `b = c`, and
`a * c = b * c` implies `a = b`. -/
@[to_additive add_cancel_semigroup]
class cancel_semigroup (α : Type*) extends left_cancel_semigroup α, right_cancel_semigroup α

attribute [to_additive] cancel_semigroup.to_left_cancel_semigroup
  cancel_semigroup.to_right_cancel_semigroup

section dvd
variables {α : Type*} [monoid α] {a b : α}

lemma dvd_of_eq (h : a = b) : a ∣ b := by rw h
lemma dvd_of_eq' (h : a = b) : b ∣ a := by rw h

alias dvd_of_eq ← eq.dvd
alias dvd_of_eq' ← eq.dvd'
alias dvd_add ← has_dvd.dvd.add
alias dvd_sub ← has_dvd.dvd.sub

end dvd

namespace nat
variables {a b m n : ℕ}

lemma eq_of_forall_dvd (h : ∀ c, a ∣ c ↔ b ∣ c) : a = b :=
dvd_antisymm ((h _).2 dvd_rfl) $ (h _).1 dvd_rfl

lemma eq_of_forall_dvd' (h : ∀ c, c ∣ a ↔ c ∣ b) : a = b :=
dvd_antisymm ((h _).1 dvd_rfl) $ (h _).2 dvd_rfl

lemma lcm_pos : 0 < m → 0 < n → 0 < m.lcm n := by { simp_rw pos_iff_ne_zero, exact lcm_ne_zero }

lemma add_sub_one_le_mul (ha : a ≠ 0) (hb : b ≠ 0) : a + b - 1 ≤ a * b :=
begin
  cases a,
  { cases ha rfl },
  { rw [succ_add, succ_sub_one, succ_mul],
    exact add_le_add_right (le_mul_of_one_le_right' $ pos_iff_ne_zero.2 hb) _ }
end

end nat

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

section
variables {α : Type*} [canonically_ordered_comm_semiring α] [pos_mul_strict_mono α]
  [mul_pos_strict_mono α] {a b c d : α}

--TODO: Fix implicitness of `eq_zero_or_pos`
lemma mul_lt_mul_of_lt_of_lt'' (hab : a < b) (hcd : c < d) : a * c < b * d :=
begin
  obtain rfl | hc := @eq_zero_or_pos _ _ c,
  { rw mul_zero,
    exact mul_pos ((zero_le _).trans_lt hab) hcd },
  { exact mul_lt_mul_of_lt_of_lt' hab hcd ((zero_le _).trans_lt hab) hc }
end

end

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

namespace finset
variables {α : Type*} {s : finset α} {a : α}

lemma one_le_card : 1 ≤ s.card ↔ s.nonempty := card_pos

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

-- TODO: Fix implicitness of `finset.attach_nonempty_iff`
protected lemma nonempty.attach : s.nonempty → s.attach.nonempty := s.attach_nonempty_iff.2

end finset

namespace finset
variables {α β γ : Type*} [decidable_eq γ] {f : α → β → γ} {s s₁ s₂ : finset α} {t t₁ t₂ : finset β}
  {u : finset γ} {a : α} {b : β}

open function

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

end finset

open_locale pointwise

namespace set
variables {α : Type*} {s : set α}

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

namespace finset
variables {α : Type*} [decidable_eq α] [has_mul α]

open mul_opposite

@[simp, to_additive] lemma singleton_mul' (a : α) (s : finset α) : {a} * s = a • s :=
singleton_mul _

@[simp, to_additive] lemma mul_singleton' (s : finset α) (a : α) : s * {a} = op a • s :=
mul_singleton _

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

section prod
variables {α β : Type*} [monoid α] [monoid β] {x : α × β} {a : α} {b : β}

@[to_additive is_of_fin_add_order.mono]
lemma is_of_fin_order.mono (ha : is_of_fin_order a) (h : order_of b ∣ order_of a) :
  is_of_fin_order b :=
by { rw ←order_of_pos_iff at ⊢ ha, exact nat.pos_of_dvd_of_pos h ha }

--TODO: `to_additive_reorder` on `prod.pow_fst`
@[to_additive prod.add_order_of] protected lemma prod.order_of (x : α × β) :
  order_of x = (order_of x.1).lcm (order_of x.2) :=
nat.eq_of_forall_dvd $ by cases x; simp [order_of_dvd_iff_pow_eq_one, nat.lcm_dvd_iff]

@[to_additive add_order_of_fst_dvd_add_order_of] lemma order_of_fst_dvd_order_of :
  order_of x.1 ∣ order_of x :=
by { rw prod.order_of, exact nat.dvd_lcm_left _ _ }

@[to_additive add_order_of_snd_dvd_add_order_of] lemma order_of_snd_dvd_order_of :
  order_of x.2 ∣ order_of x :=
by { rw prod.order_of, exact nat.dvd_lcm_right _ _ }

@[to_additive is_of_fin_add_order.fst]
lemma is_of_fin_order.fst {x : α × β} (hx : is_of_fin_order x) : is_of_fin_order x.1 :=
hx.mono order_of_fst_dvd_order_of

@[to_additive is_of_fin_add_order.snd]
lemma is_of_fin_order.snd {x : α × β} (hx : is_of_fin_order x) : is_of_fin_order x.2 :=
hx.mono order_of_snd_dvd_order_of

@[to_additive is_of_fin_add_order.prod_mk]
lemma is_of_fin_order.prod_mk : is_of_fin_order a → is_of_fin_order b → is_of_fin_order (a, b) :=
by simpa only [←order_of_pos_iff, prod.order_of] using nat.lcm_pos

end prod

section monoid
variables {α : Type*} [monoid α] {a : α}

open function set subgroup submonoid

@[to_additive] lemma range_pow (a : α) : range (λ n : ℕ, a ^ n) = powers a := rfl

--TODO: Fix name `order_eq_card_zpowers` to `order_of_eq_card_zpowers`
/-- See also `order_eq_card_powers`. -/
@[to_additive add_order_eq_card_multiples' "See also `add_order_eq_card_multiples`."]
lemma order_of_eq_card_powers' : order_of a = nat.card (powers a) := sorry

@[to_additive is_of_fin_add_order.finite_multiples]
lemma is_of_fin_order.finite_powers (h : is_of_fin_order a) : (powers a : set α).finite :=
begin
  rw [←order_of_pos_iff, order_of_eq_card_powers'] at h,
  exact finite_coe_iff.1 (nat.finite_of_card_ne_zero h.ne'),
end

end monoid

namespace monoid
variables {α : Type*} [monoid α]

@[simp, to_additive] lemma is_torsion_free_of_subsingleton [subsingleton α] : is_torsion_free α :=
λ a ha _, ha $ subsingleton.elim _ _

end monoid

section left_cancel_monoid
variables {α : Type*} [left_cancel_monoid α] {a : α}

open function set subgroup submonoid

@[simp, to_additive finite_multiples] lemma finite_powers :
  (powers a : set α).finite ↔ is_of_fin_order a :=
⟨λ h, of_not_not $ λ h', infinite_range_of_injective (injective_pow_iff_not_is_of_fin_order.2 h')
  h, is_of_fin_order.finite_powers⟩

@[simp, to_additive infinite_zmultiples] lemma infinite_powers :
  (powers a : set α).infinite ↔ ¬ is_of_fin_order a :=
finite_powers.not

end left_cancel_monoid

section group
variables {α : Type*} [group α] {s : subgroup α} {a : α} {m n : ℤ}

open function int set subgroup submonoid

@[to_additive] lemma range_zpow (a : α) : range (λ n : ℤ, a ^ n) = zpowers a := rfl

--TODO: Turn `is_of_fin_order_iff_coe` around. Rename to `subgroup.is_of_fin_order_coe`

@[to_additive] lemma zpow_eq_one_iff_modeq : a ^ n = 1 ↔ n ≡ 0 [ZMOD (order_of a)] :=
by rw [modeq_zero_iff_dvd, order_of_dvd_iff_zpow_eq_one]

@[to_additive] lemma zpow_eq_zpow_iff_modeq : a ^ m = a ^ n ↔ m ≡ n [ZMOD (order_of a)] :=
by rw [←mul_inv_eq_one, ←zpow_sub, zpow_eq_one_iff_modeq, modeq_iff_dvd, modeq_iff_dvd, zero_sub,
  neg_sub]

@[simp, to_additive] lemma injective_zpow_iff_not_is_of_fin_order :
  injective (λ n : ℤ, a ^ n) ↔ ¬ is_of_fin_order a :=
begin
  refine ⟨_, λ h n m hnm, _⟩,
  { simp_rw is_of_fin_order_iff_pow_eq_one,
    rintro h ⟨n, hn, ha⟩,
    exact nat.cast_ne_zero.2 hn.ne' (h $ by simpa using ha) },
  rwa [zpow_eq_zpow_iff_modeq, order_of_eq_zero_iff.mpr h, nat.cast_zero, modeq_zero_iff] at hnm,
end

@[simp, to_additive finite_zmultiples] lemma finite_zpowers :
  (zpowers a : set α).finite ↔ is_of_fin_order a :=
⟨λ h, of_not_not $ λ h', infinite_range_of_injective (injective_zpow_iff_not_is_of_fin_order.2 h')
  h, λ h, finite_coe_iff.1 h.finite_zpowers⟩

@[simp, to_additive infinite_zmultiples] lemma infinite_zpowers :
  (zpowers a : set α).infinite ↔ ¬ is_of_fin_order a :=
finite_zpowers.not

@[to_additive is_of_fin_add_order.finite_zmultiples']
lemma is_of_fin_order.finite_zpowers' (h : is_of_fin_order a) : (zpowers a : set α).finite :=
finite_coe_iff.1 h.finite_zpowers

@[simp, to_additive nat.card_zmultiples] lemma nat.card_zpowers (a : α) :
  nat.card (zpowers a) = order_of a := (order_eq_card_zpowers' _).symm

@[to_additive add_order_of_le_card]
lemma order_of_le_card (hs : (s : set α).finite) (ha : a ∈ s) : order_of a ≤ nat.card s :=
by { rw [←nat.card_zpowers], refine nat.card_mono hs (zpowers_le.2 ha) }

end group

namespace char_p
variables {R : Type*} [add_group_with_one R] (p : ℕ) [char_p R p] {a b n : ℕ}

-- lemma add_order_of_cast (hn : n ≠ 0) : add_order_of (n : R) = p / p.gcd n := sorry

end char_p

instance : unique (zmod 1) := fin.unique
