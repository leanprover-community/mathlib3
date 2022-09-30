/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import data.dfinsupp.order
import order.game_add

/-!
# Lexicographic order on finitely supported dependent functions
This file defines the lexicographic order on `dfinsupp`.

TODO: port `finsupp.ne_locus` and `finsupp.lex.linear_order` to `dfinsupp`.
-/

variables {ι : Type*} {α : ι → Type*}

namespace dfinsupp

section has_zero

variable [Π i, has_zero (α i)]

/-- `dfinsupp.lex r s` is the lexicographic relation on `Π₀ i, α i`, where `ι` is ordered by `r`,
and `α i` is ordered by `s i`.
The type synonym `lex (Π₀ i, α i)` has an order given by `dfinsupp.lex (<) (<)`.
-/
protected def lex (r : ι → ι → Prop) (s : Π i, α i → α i → Prop) (x y : Π₀ i, α i) : Prop :=
pi.lex r s x y

instance [has_lt ι] [Π i, has_lt (α i)] : has_lt (lex (Π₀ i, α i)) :=
⟨λ f g, dfinsupp.lex (<) (λ i, (<)) (of_lex f) (of_lex g)⟩

instance lex.is_strict_order [linear_order ι] [Π i, partial_order (α i)] :
  is_strict_order (lex (Π₀ i, α i)) (<) :=
let i : is_strict_order (lex (Π i, α i)) (<) := pi.lex.is_strict_order in
{ irrefl := to_lex.surjective.forall.2 $ λ a, @irrefl _ _ i.to_is_irrefl a,
  trans := to_lex.surjective.forall₃.2 $ λ a b c, @trans _ _ i.to_is_trans a b c }

end has_zero

section well_founded

variable [hz : Π i, has_zero (α i)]
include hz

/-- Merge two finitely supported functions `x y : Π₀ i, α i`; at every coordinate `a : α`, use the
  predicate `p` to decide whether to take the value of `x` or the value of `y`. -/
noncomputable def merge (p : ι → Prop) (x y : Π₀ i, α i) : Π₀ i, α i :=
by classical; exactI mk (x.support ∪ y.support) (λ i, if p i then x i else y i)

lemma merge_apply (p : ι → Prop) (x y : Π₀ i, α i) (i : ι) :
  merge p x y i = if p i then x i else y i :=
mk_apply.trans begin
  split_ifs with h h' h', refl, refl,
  all_goals { rw [eq_comm, ← not_mem_support_iff], rw finset.not_mem_union at h },
  exacts [h.1, h.2],
end

open relation prod
variables (r : ι → ι → Prop) (s : Π i, α i → α i → Prop)

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

lemma merge_single_erase (x : Π₀ i, α i) (i : ι) :
  merge (λ j, j = i) (single i (x i)) (x.erase i) = x :=
begin
  ext j, rw merge_apply, split_ifs,
  { rw [h, single_eq_same] }, { exact erase_ne h },
end

lemma lex.acc_of_single_erase {x : Π₀ i, α i} (i : ι)
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

lemma lex.acc_of_single (x : Π₀ i, α i) :
  (∀ i ∈ x.support, acc (dfinsupp.lex r s) $ single i (x i)) → acc (dfinsupp.lex r s) x :=
begin
  generalize ht : x.support = t, revert x, classical,
  induction t using finset.induction with b t hb ih,
  { intros x ht, rw support_eq_empty.1 ht, exact λ _, lex.acc_zero r s hbot },
  refine λ x ht h, lex.acc_of_single_erase r s b (h b $ t.mem_insert_self b) _,
  refine ih _ (by rw [support_erase, ht, finset.erase_insert hb]) (λ a ha, _),
  rw [erase_ne (ha.ne_of_not_mem hb)],
  exact h a (finset.mem_insert_of_mem ha),
end

variable (hs : ∀ i, well_founded (s i))
include hs

lemma lex.acc_single {i : ι} (a : α i)
  (hi : acc (rᶜ ⊓ (≠)) i) : acc (dfinsupp.lex r s) (single i a) :=
begin
  revert a, induction hi with i hi ih,
  refine λ a, (hs i).induction a (λ a ha, _),
  refine acc.intro _ (λ x, _),
  rintro ⟨k, hr, hs⟩, classical,
  rw single_apply at hs,
  split_ifs at hs with hik,
  swap, { exact (hbot hs).elim }, subst hik,
  refine lex.acc_of_single r s hbot x (λ j hj, _),
  obtain rfl | hij := eq_or_ne i j, { exact ha _ hs },
  by_cases r j i,
  { rw [hr j h, single_eq_of_ne hij, single_zero], exact lex.acc_zero r s hbot },
  { exact ih _ ⟨h, hij.symm⟩ _ },
end

lemma lex.acc (x : Π₀ i, α i)
  (h : ∀ i ∈ x.support, acc (rᶜ ⊓ (≠)) i) : acc (dfinsupp.lex r s) x :=
lex.acc_of_single r s hbot x $ λ i hi, lex.acc_single r s hbot hs _ (h i hi)

theorem lex.well_founded (hr : well_founded $ rᶜ ⊓ (≠)) : well_founded (dfinsupp.lex r s) :=
⟨λ x, lex.acc r s hbot hs x $ λ i _, hr.apply i⟩

theorem lex.well_founded' [is_trichotomous ι r]
  (hr : well_founded r.swap) : well_founded (dfinsupp.lex r s) :=
lex.well_founded r s hbot hs $ subrelation.wf
  (λ i j h, ((@is_trichotomous.trichotomous ι r _ i j).resolve_left h.1).resolve_left h.2) hr

omit hz hbot hs

instance lex.well_founded_lt [has_lt ι] [is_trichotomous ι (<)] [hι : well_founded_gt ι]
  [Π i, canonically_ordered_add_monoid (α i)]
  [hα : ∀ i, well_founded_lt (α i)] : well_founded_lt (lex (Π₀ i, α i)) :=
⟨lex.well_founded' (<) (λ i, (<)) (λ i a, (zero_le a).not_lt) (λ i, (hα i).wf) hι.wf⟩

/- instance vs. general -/
/- pi.lex (finite linear(?)) vs. finsupp.lex -/
/- product order -/

end well_founded

-- connection between product order (has_le) and lex
-- connection between finsupp and dfinsupp
-- Add is_well_order (Π₀ i, α i) (<). (product order)
-- Future work: relation.cut_expand -> multiset.lex? Reorganize directory, hydra -> well_founded / lex

end dfinsupp
