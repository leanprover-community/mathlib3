/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import data.dfinsupp.lex
import order.game_add
import order.antisymmetrization
import set_theory.ordinal.basic

/-!
# Well-foundedness of the lexicographic and product orders on `dfinsupp` and `pi`

The proof is modelled on the proof of `well_founded.cut_expand`.
-/

variables {ι : Type*} {α : ι → Type*}

namespace dfinsupp

variables [hz : Π i, has_zero (α i)] (r : ι → ι → Prop) (s : Π i, α i → α i → Prop)
include hz

open relation prod

lemma lex_fibration : fibration
  (inv_image (game_add (dfinsupp.lex r s) (dfinsupp.lex r s)) snd)
  (dfinsupp.lex r s)
  (λ x, merge x.1 x.2.1 x.2.2) :=
begin
  rintro ⟨p, x₁, x₂⟩ x ⟨i, hr, hs⟩,
  simp_rw [merge_apply] at hs hr,
  split_ifs at hs, classical,
  work_on_goal 1
  { refine ⟨⟨λ j, r j i → p j, merge (λ j, r j i) x₁ x, x₂⟩, game_add.fst ⟨i, _⟩, _⟩ },
  work_on_goal 3
  { refine ⟨⟨λ j, r j i ∧ p j, x₁, merge (λ j, r j i) x₂ x⟩, game_add.snd ⟨i, _⟩, _⟩ },
  swap 3, iterate 2
  { simp_rw merge_apply,
    refine ⟨λ j h, if_pos h, _⟩,
    convert hs,
    refine ite_eq_right_iff.2 (λ h', (hr i h').symm ▸ _),
    rw if_neg h <|> rw if_pos h },
  all_goals { ext j, simp_rw merge_apply, split_ifs with h₁ h₂ },
  { rw [hr j h₂, if_pos (h₁ h₂)] },
  { refl },
  { rw not_imp at h₁, rw [hr j h₁.1, if_neg h₁.2] },
  { rw [hr j h₁.1, if_pos h₁.2] },
  { rw [hr j h₂, if_neg (λ h', h₁ ⟨h₂, h'⟩)] },
  { refl },
end

variables {r s}

lemma lex.acc_of_single_erase [decidable_eq ι] {x : Π₀ i, α i} (i : ι)
  (hs : acc (dfinsupp.lex r s) (single i (x i)))
  (hu : acc (dfinsupp.lex r s) (x.erase i)) : acc (dfinsupp.lex r s) x :=
begin
  classical, rw ← merge_single_erase x i,
  convert acc.of_fibration _ (lex_fibration r s) _,
  work_on_goal 4 { refine ⟨_, _, _⟩ }, iterate 3 { refl },
  exact inv_image.accessible snd (hs.prod_game_add hu),
end

variable (hbot : ∀ ⦃i a⦄, ¬ s i a 0)
include hbot

lemma lex.acc_zero : acc (dfinsupp.lex r s) 0 := acc.intro 0 $ λ x ⟨_, _, h⟩, (hbot h).elim

lemma lex.acc_of_single [decidable_eq ι] [Π i (x : α i), decidable (x ≠ 0)] (x : Π₀ i, α i) :
  (∀ i ∈ x.support, acc (dfinsupp.lex r s) $ single i (x i)) → acc (dfinsupp.lex r s) x :=
begin
  generalize ht : x.support = t, revert x, classical,
  induction t using finset.induction with b t hb ih,
  { intros x ht, rw support_eq_empty.1 ht, exact λ _, lex.acc_zero hbot },
  refine λ x ht h, lex.acc_of_single_erase b (h b $ t.mem_insert_self b) _,
  refine ih _ (by rw [support_erase, ht, finset.erase_insert hb]) (λ a ha, _),
  rw [erase_ne (ha.ne_of_not_mem hb)],
  exact h a (finset.mem_insert_of_mem ha),
end

variable (hs : ∀ i, well_founded (s i))
include hs

lemma lex.acc_single [decidable_eq ι] {i : ι} (a : α i)
  (hi : acc (rᶜ ⊓ (≠)) i) : acc (dfinsupp.lex r s) (single i a) :=
begin
  revert a, induction hi with i hi ih,
  refine λ a, (hs i).induction a (λ a ha, _),
  refine acc.intro _ (λ x, _),
  rintro ⟨k, hr, hs⟩, classical,
  rw single_apply at hs,
  split_ifs at hs with hik,
  swap, { exact (hbot hs).elim }, subst hik,
  refine lex.acc_of_single hbot x (λ j hj, _),
  obtain rfl | hij := eq_or_ne i j, { exact ha _ hs },
  by_cases r j i,
  { rw [hr j h, single_eq_of_ne hij, single_zero], exact lex.acc_zero hbot },
  { exact ih _ ⟨h, hij.symm⟩ _ },
end

lemma lex.acc [decidable_eq ι] [Π i (x : α i), decidable (x ≠ 0)] (x : Π₀ i, α i)
  (h : ∀ i ∈ x.support, acc (rᶜ ⊓ (≠)) i) : acc (dfinsupp.lex r s) x :=
lex.acc_of_single hbot x $ λ i hi, lex.acc_single hbot hs _ (h i hi)

theorem lex.well_founded (hr : well_founded $ rᶜ ⊓ (≠)) : well_founded (dfinsupp.lex r s) :=
⟨λ x, by classical; exact lex.acc hbot hs x (λ i _, hr.apply i)⟩

theorem lex.well_founded' [is_trichotomous ι r]
  (hr : well_founded r.swap) : well_founded (dfinsupp.lex r s) :=
lex.well_founded hbot hs $ subrelation.wf
  (λ i j h, ((@is_trichotomous.trichotomous ι r _ i j).resolve_left h.1).resolve_left h.2) hr

omit hz hbot hs

instance lex.well_founded_lt [has_lt ι] [is_trichotomous ι (<)]
  [hι : well_founded_gt ι] [Π i, canonically_ordered_add_monoid (α i)]
  [hα : ∀ i, well_founded_lt (α i)] : well_founded_lt (lex (Π₀ i, α i)) :=
⟨lex.well_founded' (λ i a, (zero_le a).not_lt) (λ i, (hα i).wf) hι.wf⟩

end dfinsupp

open dfinsupp

variables (r : ι → ι → Prop) {s : Π i, α i → α i → Prop}

theorem pi.lex.well_founded [is_strict_total_order ι r] [finite ι]
  (hs : ∀ i, well_founded (s i)) : well_founded (pi.lex r s) :=
begin
  by_cases is_empty (Π i, α i),
  { convert empty_wf, ext1 x, exact (h.1 x).elim },
  simp_rw [is_empty_pi, not_exists, not_is_empty_iff, set.nonempty_iff_univ_nonempty] at h,
  letI : Π i, has_zero (α i) := λ i, ⟨(hs i).min ⊤ (h i)⟩,
  haveI := is_trans.swap r, haveI := is_irrefl.swap r, haveI := fintype.of_finite ι,
  refine inv_image.wf equiv_fun_on_fintype.symm (lex.well_founded' (λ i a, _) hs _),
  exacts [(hs i).not_lt_min ⊤ _ trivial, finite.well_founded_of_trans_of_irrefl r.swap],
end

instance pi.lex.well_founded_lt [linear_order ι] [finite ι] [Π i, has_lt (α i)]
  [hwf : ∀ i, well_founded_lt (α i)] : well_founded_lt (lex (Π i, α i)) :=
⟨pi.lex.well_founded (<) (λ i, (hwf i).1)⟩

instance function.lex.well_founded_lt {α} [linear_order ι] [finite ι] [has_lt α]
  [well_founded_lt α] : well_founded_lt (lex (ι → α)) := pi.lex.well_founded_lt

theorem dfinsupp.lex.well_founded_of_finite [is_strict_total_order ι r] [finite ι]
  [Π i, has_zero (α i)] (hs : ∀ i, well_founded (s i)) : well_founded (dfinsupp.lex r s) :=
have _ := fintype.of_finite ι,
  by exactI inv_image.wf equiv_fun_on_fintype (pi.lex.well_founded r hs)

instance dfinsupp.lex.well_founded_lt_of_finite [linear_order ι] [finite ι] [Π i, has_zero (α i)]
  [Π i, has_lt (α i)] [hwf : ∀ i, well_founded_lt (α i)] : well_founded_lt (lex (Π₀ i, α i)) :=
⟨dfinsupp.lex.well_founded_of_finite (<) $ λ i, (hwf i).1⟩

protected theorem dfinsupp.well_founded_lt [Π i, has_zero (α i)] [Π i, preorder (α i)]
  [∀ i, well_founded_lt (α i)] (hbot : ∀ ⦃i⦄ ⦃a : α i⦄, ¬ a < 0) : well_founded_lt (Π₀ i, α i) :=
⟨begin
  letI : Π i, has_zero (antisymmetrization (α i) (≤)) := λ i, ⟨to_antisymmetrization (≤) 0⟩,
  let f := map_range (λ i, @to_antisymmetrization (α i) (≤) _) (λ i, rfl),
  refine subrelation.wf (λ x y h, _) (inv_image.wf f $ lex.well_founded' _ (λ i, _) _),
  { exact well_ordering_rel.swap }, { exact λ i, (<) },
  { haveI := is_strict_order.swap (@well_ordering_rel ι),
    obtain ⟨i, he, hl⟩ := lex_lt_of_lt_of_preorder well_ordering_rel.swap h,
    exact ⟨i, λ j hj, quot.sound (he j hj), hl⟩ },
  { rintro i ⟨a⟩, apply hbot },
  exacts [is_well_founded.wf, is_trichotomous.swap _, is_well_founded.wf],
end⟩

instance dfinsupp.well_founded_lt' [Π i, canonically_ordered_add_monoid (α i)]
  [∀ i, well_founded_lt (α i)] : well_founded_lt (Π₀ i, α i) :=
dfinsupp.well_founded_lt $ λ i a, (zero_le a).not_lt

instance pi.well_founded_lt [finite ι] [Π i, preorder (α i)]
  [hwf : ∀ i, well_founded_lt (α i)] : well_founded_lt (Π i, α i) :=
⟨begin
  by_cases is_empty (Π i, α i),
  { convert empty_wf, ext1 x, exact (h.1 x).elim },
  simp_rw [is_empty_pi, not_exists, not_is_empty_iff, set.nonempty_iff_univ_nonempty] at h,
  letI : Π i, has_zero (α i) := λ i, ⟨(hwf i).wf.min ⊤ (h i)⟩, haveI := fintype.of_finite ι,
  refine inv_image.wf equiv_fun_on_fintype.symm (dfinsupp.well_founded_lt $ λ i a, _).wf,
  exact (hwf i).wf.not_lt_min ⊤ _ trivial,
end⟩

instance function.well_founded_lt {α} [finite ι] [preorder α]
  [well_founded_lt α] : well_founded_lt (ι → α) := pi.well_founded_lt

instance dfinsupp.well_founded_lt_of_finite [finite ι] [Π i, has_zero (α i)] [Π i, preorder (α i)]
  [∀ i, well_founded_lt (α i)] : well_founded_lt (Π₀ i, α i) :=
have _ := fintype.of_finite ι,
  by exactI ⟨inv_image.wf equiv_fun_on_fintype pi.well_founded_lt.wf⟩
