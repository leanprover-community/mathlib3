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

The primary results are `dfinsupp.lex.well_founded` and the two variants that follow it,
which essentially say that if `(>)` is a well order on `ι`, `(<)` is well-founded on each
`α i`, and `0` is a bottom element in `α i`, then the lexicographic `(<)` is well-founded
on `Π₀ i, α i`. The proof is modelled on the proof of `well_founded.cut_expand`.

The results are used to prove `pi.lex.well_founded` and two variants, which say that if
`ι` is finite and equipped with a linear order and `(<)` is well-founded on each `α i`,
then the lexicographic `(<)` is well-founded on `Π i, α i`, and the same is true for
`Π₀ i, α i` (`dfinsupp.lex.well_founded_of_finite`), because `dfinsupp` is order-isomorphic
to `pi` when `ι` is finite.

Finally, we deduce `dfinsupp.well_founded_lt`, `pi.well_founded_lt`,
`dfinsupp.well_founded_lt_of_finite` and variants, which concern the product order
rather than the lexicographic one. An order on `ι` is not required in these results,
but we deduce them from the well-foundedness of the lexicographic order by choosing
a well order on `ι` so that the product order `(<)` becomes a subrelation
of the lexicographic `(<)`.

All results are provided in two forms whenever possible: a general form where the relations
can be arbitrary (not the `(<)` of a preorder, or not even transitive, etc.) and a specialized
form provided as `well_founded_lt` instances where the `(d)finsupp/pi` type (or their `lex`
type synonyms) carries a natural `(<)`.

Notice that the definition of `dfinsupp.lex` says that `x < y` according to `dfinsupp.lex r s`
iff there exists a coordinate `i : ι` such that `x i < y i` according to `s i`, and at all
`r`-smaller coordinates `j` (i.e. satisfying `r j i`), `x` remains unchanged relative to `y`;
in other words, coordinates `j` such that `¬ r j i` and `j ≠ i` are exactly where changes
can happen arbitrarily. This explains the appearance of `rᶜ ⊓ (≠)` in
`dfinsupp.acc_single` and `dfinsupp.well_founded`. When `r` is trichotomous (e.g. the `(<)`
of a linear order), `¬ r j i ∧ j ≠ i` implies `r i j`, so it suffices to require `r.swap`
to be well-founded.
-/

variables {ι : Type*} {α : ι → Type*}

namespace dfinsupp

variables [hz : Π i, has_zero (α i)] (r : ι → ι → Prop) (s : Π i, α i → α i → Prop)
include hz

open relation prod

/-- This key lemma says that if a finitely supported dependent function `x₀` is obtained by merging
  two such functions `x₁` and `x₂`, and if we evolve `x₀` down the `dfinsupp.lex` relation one
  step and get `x`, we can always evolve one of `x₁` and `x₂` down the `dfinsupp.lex` relation
  one step while keeping the other unchanged, and merge them back (possibly in a different way)
  to get back `x`. In other words, the two parts evolve essentially independently under
  `dfinsupp.lex`. This is used to show that a function `x` is accessible if
  `dfinsupp.single i (x i)` is accessible for each `i` in the (finite) support of `x`
  (`dfinsupp.lex.acc_of_single`). -/
lemma lex_fibration [Π i (s : set ι), decidable (i ∈ s)] : fibration
  (inv_image (game_add (dfinsupp.lex r s) (dfinsupp.lex r s)) snd)
  (dfinsupp.lex r s)
  (λ x, piecewise x.2.1 x.2.2 x.1) :=
begin
  rintro ⟨p, x₁, x₂⟩ x ⟨i, hr, hs⟩,
  simp_rw [piecewise_apply] at hs hr,
  split_ifs at hs, classical,
  work_on_goal 1
  { refine ⟨⟨{j | r j i → j ∈ p}, piecewise x₁ x {j | r j i}, x₂⟩, game_add.fst ⟨i, _⟩, _⟩ },
  work_on_goal 3
  { refine ⟨⟨{j | r j i ∧ j ∈ p}, x₁, piecewise x₂ x {j | r j i}⟩, game_add.snd ⟨i, _⟩, _⟩ },
  swap 3, iterate 2
  { simp_rw piecewise_apply,
    refine ⟨λ j h, if_pos h, _⟩,
    convert hs,
    refine ite_eq_right_iff.2 (λ h', (hr i h').symm ▸ _),
    rw if_neg h <|> rw if_pos h },
  all_goals { ext j, simp_rw piecewise_apply, split_ifs with h₁ h₂ },
  { rw [hr j h₂, if_pos (h₁ h₂)] },
  { refl },
  { rw [set.mem_set_of, not_imp] at h₁, rw [hr j h₁.1, if_neg h₁.2] },
  { rw [hr j h₁.1, if_pos h₁.2] },
  { rw [hr j h₂, if_neg (λ h', h₁ ⟨h₂, h'⟩)] },
  { refl },
end

variables {r s}

lemma lex.acc_of_single_erase [decidable_eq ι] {x : Π₀ i, α i} (i : ι)
  (hs : acc (dfinsupp.lex r s) $ single i (x i))
  (hu : acc (dfinsupp.lex r s) $ x.erase i) : acc (dfinsupp.lex r s) x :=
begin
  classical,
  convert ← @acc.of_fibration _ _ _ _ _
    (lex_fibration r s) ⟨{i}, _⟩ (inv_image.accessible snd $ hs.prod_game_add hu),
  convert piecewise_single_erase x i,
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

lemma lex.acc_single [decidable_eq ι] {i : ι} (hi : acc (rᶜ ⊓ (≠)) i) :
  ∀ a, acc (dfinsupp.lex r s) (single i a) :=
begin
  induction hi with i hi ih,
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
lex.acc_of_single hbot x $ λ i hi, lex.acc_single hbot hs (h i hi) _

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
  obtain h | ⟨⟨x⟩⟩ := is_empty_or_nonempty (Π i, α i),
  { convert empty_wf, ext1 x, exact (h.1 x).elim },
  letI : Π i, has_zero (α i) := λ i, ⟨(hs i).min ⊤ ⟨x i, trivial⟩⟩,
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
  [hw : ∀ i, well_founded_lt (α i)] : well_founded_lt (Π i, α i) :=
⟨begin
  obtain h | ⟨⟨x⟩⟩ := is_empty_or_nonempty (Π i, α i),
  { convert empty_wf, ext1 x, exact (h.1 x).elim },
  letI : Π i, has_zero (α i) := λ i, ⟨(hw i).wf.min ⊤ ⟨x i, trivial⟩⟩,
  haveI := fintype.of_finite ι,
  refine inv_image.wf equiv_fun_on_fintype.symm (dfinsupp.well_founded_lt $ λ i a, _).wf,
  exact (hw i).wf.not_lt_min ⊤ _ trivial,
end⟩

instance function.well_founded_lt {α} [finite ι] [preorder α]
  [well_founded_lt α] : well_founded_lt (ι → α) := pi.well_founded_lt

instance dfinsupp.well_founded_lt_of_finite [finite ι] [Π i, has_zero (α i)] [Π i, preorder (α i)]
  [∀ i, well_founded_lt (α i)] : well_founded_lt (Π₀ i, α i) :=
have _ := fintype.of_finite ι,
  by exactI ⟨inv_image.wf equiv_fun_on_fintype pi.well_founded_lt.wf⟩
