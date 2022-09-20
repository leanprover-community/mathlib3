/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import data.fin.tuple.sort
import order.well_founded_set

/-!
# "Bubble sort" induction

We implement the following induction principle `tuple.bubble_sort_induction`
on tuples with values in a linear order `α`.

Let `f : fin n  → α` and let `P` be a predicate on `fin n → α`. Then we can show that
`f ∘ sort f` satisfies `P` if `f` satisfies `P`, and whenever some `g : fin n → α`
satisfies `P` and `g i > g j` for some `i < j`, then `g ∘ swap i j` also satisfies `P`.

We deduce it from a stronger variant `tuple.bubble_sort_induction'`, which
requires the assumption only for `g` that are permutations of `f`.

The latter is proved by well-founded induction with respect to the lexicographic ordering
on the finite set of all permutations of `f`.
-/

namespace tuple

/-- *Bubble sort induction*: Prove that the sorted version of `f` has some property `P`
if `f` satsifies `P` and `P` is preserved on permutations of `f` when swapping two
antitone values. -/
lemma bubble_sort_induction' {n : ℕ} {α : Type*} [linear_order α] {f : fin n → α}
  {P : (fin n → α) → Prop} (hf : P f)
  (h : ∀ (σ : equiv.perm (fin n)) (i j : fin n),
              i < j → (f ∘ σ) j < (f ∘ σ) i → P (f ∘ σ) → P (f ∘ σ ∘ equiv.swap i j)) :
  P (f ∘ sort f) :=
begin
  let φ : equiv.perm (fin n) → lex (fin n → α) := λ σ, to_lex (f ∘ σ),
  let Of := set.range φ,
  let φ' := set.cod_restrict φ Of set.mem_range_self,
  have hφ : ∀ σ, (φ' σ : lex (fin n → α)) = φ σ := set.coe_cod_restrict_apply φ Of _,
  let POf : Of → Prop := λ g, P (of_lex (g : lex (fin n → α))),
  have hf₁ : ∀ σ : equiv.perm (fin n),  P (f ∘ σ) ↔ POf (φ' σ),
  { intro σ, simp only [POf, φ', function.comp_app], congr' 1, },
  rw [hf₁],
  refine @well_founded.induction_bot Of _
    (@set.finite.well_founded_on _ (<) _ _ (set.finite_range φ)) (φ' 1) _ POf (λ g hg₁ hg₂, _) _,
  { obtain ⟨σ, hσ⟩ := set.mem_range.mp (subtype.mem g),
    have hg₁' : (g : lex (fin n → α)) ≠ φ (sort f),
    { rw [← hφ],
      by_contra' hf,
      exact hg₁ (subtype.coe_injective hf), },
    rw [← hσ, ne.def, to_lex_inj, ← ne.def] at hg₁',
    obtain ⟨i, j, hij₁, hij₂⟩ := antitone_pair_of_not_sorted' hg₁',
    have hσ': POf (φ' σ),
    { convert hg₂,
      apply_fun (coe : Of → lex (fin n → α)) using subtype.coe_injective,
      rwa hφ, },
    refine ⟨φ' (σ * (equiv.swap i j)), _, _⟩,
    { convert lex_desc hij₁ hij₂,
      simp only [inv_image, φ', ←hσ, φ, set.coe_cod_restrict_apply, equiv.perm.coe_mul], },
    { simp only [← hf₁, equiv.perm.coe_mul],
      rw [← function.comp.assoc],
      exact h σ i j hij₁ hij₂ ((hf₁ σ).mpr hσ'), } },
  { simp only [POf, φ', φ, function.comp_app],
    rwa [set.coe_cod_restrict_apply, of_lex_to_lex, equiv.perm.coe_one, function.comp.right_id] }
end

/-- *Bubble sort induction*: Prove that the sorted version of `f` has some property `P`
if `f` satsifies `P` and `P` is preserved when swapping two antitone values. -/
lemma bubble_sort_induction {n : ℕ} {α : Type*} [linear_order α] {f : fin n → α}
  {P : (fin n → α) → Prop} (hf : P f)
  (h : ∀ (g : fin n → α) (i j : fin n), i < j → g j < g i → P g → P (g ∘ equiv.swap i j)) :
  P (f ∘ sort f) :=
bubble_sort_induction' hf (λ σ, h _)

end tuple
