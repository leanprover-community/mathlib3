/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import order.bounds.basic
import data.set.intervals.basic

/-!
# Intervals without endpoints ordering

In any decidable linear order `α`, we define the set of elements lying between two elements `a` and
`b` as `Icc (min a b) (max a b)`.

`Icc a b` requires the assumption `a ≤ b` to be meaningful, which is sometimes inconvenient. The
interval as defined in this file is always the set of things lying between `a` and `b`, regardless
of the relative order of `a` and `b`.

For real numbers, `Icc (min a b) (max a b)` is the same as `segment ℝ a b`.

## Notation

We use the localized notation `[a, b]` for `interval a b`. One can open the locale `interval` to
make the notation available.

-/

open function order_dual (to_dual of_dual)

namespace set

section linear_order
variables {α β : Type*} [linear_order α] [linear_order β] {f : α → β} {s : set α}
  {a a₁ a₂ b b₁ b₂ c x : α}

/-- `interval a b` is the set of elements lying between `a` and `b`, with `a` and `b` included. -/
def interval (a b : α) := Icc (min a b) (max a b)

localized "notation (name := set.interval) `[`a `, ` b `]` := set.interval a b" in interval

@[simp] lemma dual_interval (a b : α) : [to_dual a, to_dual b] = of_dual ⁻¹' [a, b] := dual_Icc

@[simp] lemma interval_of_le (h : a ≤ b) : [a, b] = Icc a b :=
by rw [interval, min_eq_left h, max_eq_right h]

@[simp] lemma interval_of_ge (h : b ≤ a) : [a, b] = Icc b a :=
by { rw [interval, min_eq_right h, max_eq_left h] }

lemma interval_swap (a b : α) : [a, b] = [b, a] :=
by rw [interval, interval, min_comm, max_comm]

lemma interval_of_lt (h : a < b) : [a, b] = Icc a b :=
interval_of_le (le_of_lt h)

lemma interval_of_gt (h : b < a) : [a, b] = Icc b a :=
interval_of_ge (le_of_lt h)

lemma interval_of_not_le (h : ¬ a ≤ b) : [a, b] = Icc b a :=
interval_of_gt (lt_of_not_ge h)

lemma interval_of_not_ge (h : ¬ b ≤ a) : [a, b] = Icc a b :=
interval_of_lt (lt_of_not_ge h)

lemma interval_eq_union : [a, b] = Icc a b ∪ Icc b a := by rw [Icc_union_Icc', max_comm]; refl

lemma mem_interval : a ∈ [b, c] ↔ b ≤ a ∧ a ≤ c ∨ c ≤ a ∧ a ≤ b := by simp [interval_eq_union]

@[simp] lemma interval_self : [a, a] = {a} :=
set.ext $ by simp [le_antisymm_iff, and_comm]

@[simp] lemma nonempty_interval : set.nonempty [a, b] :=
by { simp only [interval, min_le_iff, le_max_iff, nonempty_Icc], left, left, refl }

@[simp] lemma left_mem_interval : a ∈ [a, b] := by simp [mem_interval, le_total]
@[simp] lemma right_mem_interval : b ∈ [a, b] := by simp [mem_interval, le_total]

lemma Icc_subset_interval : Icc a b ⊆ [a, b] :=
Icc_subset_Icc (min_le_left _ _) (le_max_right _ _)

lemma Icc_subset_interval' : Icc b a ⊆ [a, b] :=
by { rw interval_swap, apply Icc_subset_interval }

lemma mem_interval_of_le (ha : a ≤ x) (hb : x ≤ b) : x ∈ [a, b] :=
Icc_subset_interval ⟨ha, hb⟩

lemma mem_interval_of_ge (hb : b ≤ x) (ha : x ≤ a) : x ∈ [a, b] :=
Icc_subset_interval' ⟨hb, ha⟩

lemma not_mem_interval_of_lt (ha : c < a) (hb : c < b) : c ∉ [a, b] :=
not_mem_Icc_of_lt $ lt_min_iff.mpr ⟨ha, hb⟩

lemma not_mem_interval_of_gt (ha : a < c) (hb : b < c) : c ∉ [a, b] :=
not_mem_Icc_of_gt $ max_lt_iff.mpr ⟨ha, hb⟩

lemma interval_subset_interval (h₁ : a₁ ∈ [a₂, b₂]) (h₂ : b₁ ∈ [a₂, b₂]) : [a₁, b₁] ⊆ [a₂, b₂] :=
Icc_subset_Icc (le_min h₁.1 h₂.1) (max_le h₁.2 h₂.2)

lemma interval_subset_Icc (ha : a₁ ∈ Icc a₂ b₂) (hb : b₁ ∈ Icc a₂ b₂) : [a₁, b₁] ⊆ Icc a₂ b₂ :=
Icc_subset_Icc (le_min ha.1 hb.1) (max_le ha.2 hb.2)

lemma interval_subset_interval_iff_mem : [a₁, b₁] ⊆ [a₂, b₂] ↔ a₁ ∈ [a₂, b₂] ∧ b₁ ∈ [a₂, b₂] :=
iff.intro (λh, ⟨h left_mem_interval, h right_mem_interval⟩) (λ h, interval_subset_interval h.1 h.2)

lemma interval_subset_interval_iff_le :
  [a₁, b₁] ⊆ [a₂, b₂] ↔ min a₂ b₂ ≤ min a₁ b₁ ∧ max a₁ b₁ ≤ max a₂ b₂ :=
by { rw [interval, interval, Icc_subset_Icc_iff], exact min_le_max }

lemma interval_subset_interval_right (h : x ∈ [a, b]) : [x, b] ⊆ [a, b] :=
interval_subset_interval h right_mem_interval

lemma interval_subset_interval_left (h : x ∈ [a, b]) : [a, x] ⊆ [a, b] :=
interval_subset_interval left_mem_interval h

/-- A sort of triangle inequality. -/
lemma interval_subset_interval_union_interval : [a, c] ⊆ [a, b] ∪ [b, c] :=
λ x, by simp only [mem_interval, mem_union]; cases le_total a c; cases le_total x b; tauto

lemma eq_of_mem_interval_of_mem_interval : a ∈ [b, c] → b ∈ [a, c] → a = b :=
by simp_rw mem_interval; rintro (⟨_, _⟩ | ⟨_, _⟩) (⟨_, _⟩ | ⟨_, _⟩); apply le_antisymm;
  assumption <|> { exact le_trans ‹_› ‹_› }

lemma eq_of_mem_interval_of_mem_interval' : b ∈ [a, c] → c ∈ [a, b] → b = c :=
by simpa only [interval_swap a] using eq_of_mem_interval_of_mem_interval

lemma interval_injective_right (a : α) : injective (λ b, interval b a) :=
λ b c h, by { rw ext_iff at h,
  exact eq_of_mem_interval_of_mem_interval ((h _).1 left_mem_interval) ((h _).2 left_mem_interval) }

lemma interval_injective_left (a : α) : injective (interval a) :=
by simpa only [interval_swap] using interval_injective_right a

lemma bdd_below_bdd_above_iff_subset_interval (s : set α) :
  bdd_below s ∧ bdd_above s ↔ ∃ a b, s ⊆ [a, b] :=
begin
  rw [bdd_below_bdd_above_iff_subset_Icc],
  split,
  { rintro ⟨a, b, h⟩, exact ⟨a, b, λ x hx, Icc_subset_interval (h hx)⟩ },
  { rintro ⟨a, b, h⟩, exact ⟨min a b, max a b, h⟩ }
end

lemma monotone_or_antitone_iff_interval :
  monotone f ∨ antitone f ↔ ∀ a b c, c ∈ [a, b] → f c ∈ [f a, f b] :=
begin
  split,
  { rintro (hf | hf) a b c; simp_rw [interval, ←hf.map_min, ←hf.map_max],
    exacts [λ hc, ⟨hf hc.1, hf hc.2⟩, λ hc, ⟨hf hc.2, hf hc.1⟩] },
  contrapose!,
  rw not_monotone_not_antitone_iff_exists_le_le,
  rintro ⟨a, b, c, hab, hbc, ⟨hfab, hfcb⟩ | ⟨hfba, hfbc⟩⟩,
  { exact ⟨a, c, b, Icc_subset_interval ⟨hab, hbc⟩, λ h, h.2.not_lt $ max_lt hfab hfcb⟩ },
  { exact ⟨a, c, b, Icc_subset_interval ⟨hab, hbc⟩, λ h, h.1.not_lt $ lt_min hfba hfbc⟩ }
end

lemma monotone_on_or_antitone_on_iff_interval :
  monotone_on f s ∨ antitone_on f s ↔ ∀ a b c ∈ s, c ∈ [a, b] → f c ∈ [f a, f b] :=
by simp [monotone_on_iff_monotone, antitone_on_iff_antitone, monotone_or_antitone_iff_interval,
  mem_interval]

/-- The open-closed interval with unordered bounds. -/
def interval_oc : α → α → set α := λ a b, Ioc (min a b) (max a b)

-- Below is a capital iota
localized "notation `Ι` := set.interval_oc" in interval

@[simp] lemma interval_oc_of_le (h : a ≤ b) : Ι a b = Ioc a b :=
by simp [interval_oc, h]

@[simp] lemma interval_oc_of_lt (h : b < a) : Ι a b = Ioc b a :=
by simp [interval_oc, le_of_lt h]

lemma interval_oc_eq_union : Ι a b = Ioc a b ∪ Ioc b a :=
by cases le_total a b; simp [interval_oc, *]

lemma mem_interval_oc : a ∈ Ι b c ↔ b < a ∧ a ≤ c ∨ c < a ∧ a ≤ b :=
by simp only [interval_oc_eq_union, mem_union, mem_Ioc]

lemma not_mem_interval_oc : a ∉ Ι b c ↔ a ≤ b ∧ a ≤ c ∨ c < a ∧ b < a :=
by { simp only [interval_oc_eq_union, mem_union, mem_Ioc, not_lt, ←not_le], tauto }

@[simp] lemma left_mem_interval_oc : a ∈ Ι a b ↔ b < a := by simp [mem_interval_oc]
@[simp] lemma right_mem_interval_oc : b ∈ Ι a b ↔ a < b := by simp [mem_interval_oc]

lemma forall_interval_oc_iff  {P : α → Prop} :
  (∀ x ∈ Ι a b, P x) ↔ (∀ x ∈ Ioc a b, P x) ∧ (∀ x ∈ Ioc b a, P x) :=
by simp only [interval_oc_eq_union, mem_union, or_imp_distrib, forall_and_distrib]

lemma interval_oc_subset_interval_oc_of_interval_subset_interval {a b c d : α}
  (h : [a, b] ⊆ [c, d]) : Ι a b ⊆ Ι c d :=
Ioc_subset_Ioc (interval_subset_interval_iff_le.1 h).1 (interval_subset_interval_iff_le.1 h).2

lemma interval_oc_swap (a b : α) : Ι a b = Ι b a :=
by simp only [interval_oc, min_comm a b, max_comm a b]

lemma Ioc_subset_interval_oc : Ioc a b ⊆ Ι a b :=
Ioc_subset_Ioc (min_le_left _ _) (le_max_right _ _)

lemma Ioc_subset_interval_oc' : Ioc a b ⊆ Ι b a :=
Ioc_subset_Ioc (min_le_right _ _) (le_max_left _ _)

lemma eq_of_mem_interval_oc_of_mem_interval_oc : a ∈ Ι b c → b ∈ Ι a c → a = b :=
by simp_rw mem_interval_oc; rintro (⟨_, _⟩ | ⟨_, _⟩) (⟨_, _⟩ | ⟨_, _⟩); apply le_antisymm;
  assumption <|> exact le_of_lt ‹_› <|> exact le_trans ‹_› (le_of_lt ‹_›)

lemma eq_of_mem_interval_oc_of_mem_interval_oc' : b ∈ Ι a c → c ∈ Ι a b → b = c :=
by simpa only [interval_oc_swap a] using eq_of_mem_interval_oc_of_mem_interval_oc

lemma eq_of_not_mem_interval_oc_of_not_mem_interval_oc (ha : a ≤ c) (hb : b ≤ c) :
  a ∉ Ι b c → b ∉ Ι a c → a = b :=
by simp_rw not_mem_interval_oc; rintro (⟨_, _⟩ | ⟨_, _⟩) (⟨_, _⟩ | ⟨_, _⟩); apply le_antisymm;
    assumption <|> exact le_of_lt ‹_› <|> cases not_le_of_lt ‹_› ‹_›

lemma interval_oc_injective_right (a : α) : injective (λ b, Ι b a) :=
begin
  rintro b c h,
  rw ext_iff at h,
  obtain ha | ha := le_or_lt b a,
  { have hb := (h b).not,
    simp only [ha, left_mem_interval_oc, not_lt, true_iff, not_mem_interval_oc, ←not_le, and_true,
      not_true, false_and, not_false_iff, true_iff, or_false] at hb,
    refine hb.eq_of_not_lt (λ hc, _),
    simpa [ha, and_iff_right hc, ←@not_le _ _ _ a, -not_le] using h c },
  { refine eq_of_mem_interval_oc_of_mem_interval_oc ((h _).1 $ left_mem_interval_oc.2 ha)
      ((h _).2 $ left_mem_interval_oc.2 $ ha.trans_le _),
    simpa [ha, ha.not_le, mem_interval_oc] using h b }
end

lemma interval_oc_injective_left (a : α) : injective (Ι a) :=
by simpa only [interval_oc_swap] using interval_oc_injective_right a

end linear_order
end set
