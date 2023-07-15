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

--TODO: Fix implicitness `subgroup.closure_eq_bot_iff`

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
variables {α : Type*} [has_one α] {s : finset α}

open_locale pointwise

@[simp, norm_cast, to_additive] lemma coe_eq_one : (s : set α) = 1 ↔ s = 1 := coe_eq_singleton

end finset

namespace subgroup
variables {G : Type*} [group G]

attribute [norm_cast] coe_eq_univ add_subgroup.coe_eq_univ

open_locale pointwise

@[norm_cast, to_additive] lemma coe_eq_one {H : subgroup G} : (H : set G) = 1 ↔ H = ⊥ :=
(set_like.ext'_iff.trans (by refl)).symm

end subgroup

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

instance {n : ℕ} : is_add_cyclic (zmod n) := ⟨⟨1, λ x, (zmod.int_cast_surjective x).imp $ by simp⟩⟩

instance {p : ℕ} [fact p.prime] : is_simple_add_group (zmod p) :=
add_comm_group.is_simple_iff_is_add_cyclic_and_prime_card.2
  ⟨by apply_instance, by simpa using fact.out p.prime⟩
