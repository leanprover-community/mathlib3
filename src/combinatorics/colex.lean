/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import data.finset
import data.fintype.basic
import algebra.geom_sum
import combinatorics.to_mathlib

/-!
# Colex

We define the colex ordering for finite sets, and give a couple of important
lemmas and properties relating to it.

The colex ordering likes to avoid large values - it can be thought of on
`finset ℕ` as the "binary" ordering. That is, order A based on
`∑_{i ∈ A} 2^i`.
It's defined here a slightly more general way, requiring only `has_lt α` in
the definition of colex on `finset α`. In the context of the Kruskal-Katona
theorem, we are interested in particular on how colex behaves for sets of a
fixed size. If the size is 3, colex on ℕ starts
123, 124, 134, 234, 125, 135, 235, 145, 245, 345, ...

## Main statements
* `colex_hom`: strictly monotone functions preserve colex
* Colex order properties - linearity, decidability and so on.
* `max_colex`: if A < B in colex, and everything in B is < t, then everything
  in A is < t. This confirms the idea that an enumeration under colex will
  exhaust all sets using elements < t before allowing t to be included.
* `binary_iff`: colex for α = ℕ is the same as binary
  (this also proves binary expansions are unique)

## Notation
We define `<ᶜ` and `≤ᶜ` to denote colex ordering, useful in particular when
multiple orderings are available in context.

## Tags
colex, colexicographic, binary

## References
* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
-/

variable {α : Type*}

open finset

/--
A <ᶜ B if the largest thing that's not in both sets is in B.
In other words, max (A ▵ B) ∈ B.
-/
def colex_lt [has_lt α] (A B : finset α) : Prop :=
  ∃ (k : α), (∀ {x}, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A ∧ k ∈ B
/--
We can define ≤ in the obvious way.
-/
def colex_le [has_lt α] (A B : finset α) : Prop := colex_lt A B ∨ A = B

infix ` <ᶜ `:50 := colex_lt
infix ` ≤ᶜ `:50 := colex_le

/-- Strictly monotone functions preserve the colex ordering. -/
lemma colex_hom {β : Type*} [linear_order α] [decidable_eq β] [preorder β]
  {f : α → β} (h₁ : strict_mono f) (A B : finset α) :
  image f A <ᶜ image f B ↔ A <ᶜ B :=
begin
  simp [colex_lt],
  split,
    rintro ⟨k, z, q, k', _, rfl⟩,
    refine ⟨k', λ x hx, _, λ t, q _ t rfl, ‹k' ∈ B›⟩, have := z (h₁ hx),
    simp [strict_mono.injective h₁] at this, assumption,
  rintro ⟨k, z, ka, _⟩,
  refine ⟨f k, λ x hx, _, _, k, ‹k ∈ B›, rfl⟩,
  split, any_goals {
    rintro ⟨x', x'in, rfl⟩, refine ⟨x', _, rfl⟩,
    rwa ← z _ <|> rwa z _, rwa strict_mono.lt_iff_lt h₁ at hx },
  simp [strict_mono.injective h₁], exact λ x hx, ne_of_mem_of_not_mem hx ka
end

/-- A special case of `colex_hom` which is sometimes useful. -/
lemma colex_hom_fin {n : ℕ} (A B : finset (fin n)) :
  image fin.val A <ᶜ image fin.val B ↔ A <ᶜ B :=
colex_hom (λ x y k, k) _ _

-- The basic order properties of colex.

instance [has_lt α] : is_irrefl (finset α) (<ᶜ) :=
⟨λ A h, exists.elim h (λ _ ⟨_,a,b⟩, a b)⟩
instance [has_lt α] : is_refl (finset α) (≤ᶜ) := ⟨λ A, or.inr rfl⟩
instance [linear_order α] : is_trans (finset α) (<ᶜ) :=
begin
  constructor,
  rintros A B C ⟨k₁, k₁z, notinA, inB⟩ ⟨k₂, k₂z, notinB, inC⟩,
  have: k₁ ≠ k₂ := ne_of_mem_of_not_mem inB notinB,
  cases lt_or_gt_of_ne this,
    refine ⟨k₂, _, by rwa k₁z h, inC⟩,
    intros x hx, rw ← k₂z hx, apply k₁z (trans h hx),
  refine ⟨k₁, _, notinA, by rwa ← k₂z h⟩,
  intros x hx, rw k₁z hx, apply k₂z (trans h hx)
end
instance [linear_order α] : is_asymm (finset α) (<ᶜ) := by apply_instance
instance [linear_order α] : is_antisymm (finset α) (≤ᶜ) :=
⟨λ A B AB BA, AB.elim (λ k, BA.elim (λ t, (asymm k t).elim) (λ t, t.symm)) id⟩
instance [linear_order α] : is_trans (finset α) (≤ᶜ) :=
⟨λ A B C AB BC, AB.elim (λ k, BC.elim (λ t, or.inl (trans k t)) (λ t, t ▸ AB))
                        (λ k, k.symm ▸ BC)⟩
instance [linear_order α] : is_strict_order (finset α) (<ᶜ) := {}

instance [linear_order α] [decidable_eq α] : is_trichotomous (finset α) (<ᶜ) :=
begin
  split, intros A B,
  by_cases (A = B), right, left, assumption,
  rcases (exists_max_image (A \ B ∪ B \ A) id _) with ⟨k, hk, z⟩,
    simp at hk, cases hk, right, right, swap, left, swap,
      any_goals { refine ⟨k, λ t th, _, hk.2, hk.1⟩, specialize z t, by_contra,
                  simp only [mem_union, mem_sdiff, id] at z, rw [not_iff,
                  iff_iff_and_or_not_and_not, not_not, and_comm] at a,
                  apply not_le_of_lt th (z _) },
      { exact a }, { exact a.symm },
  rw nonempty_iff_ne_empty,
  intro a, simp only [union_eq_empty_iff, sdiff_eq_empty_iff_subset] at a,
  apply h (subset.antisymm a.1 a.2)
end

instance [linear_order α] [decidable_eq α] : is_total (finset α) (≤ᶜ) := ⟨λ A B,
(trichotomous A B).elim3 (or.inl ∘ or.inl) (or.inl ∘ or.inr) (or.inr ∘ or.inl)⟩

instance [linear_order α] [decidable_eq α] :
  is_linear_order (finset α) (≤ᶜ) := {}
instance [linear_order α] [decidable_eq α] : is_incomp_trans (finset α) (<ᶜ) :=
begin
  constructor,
  rintros A B C ⟨nAB, nBA⟩ ⟨nBC, nCB⟩,
  have: A = B := ((trichotomous A B).resolve_left nAB).resolve_right nBA,
  have: B = C := ((trichotomous B C).resolve_left nBC).resolve_right nCB,
  rw [‹A = B›, ‹B = C›], rw and_self, apply irrefl
end
instance [linear_order α] [decidable_eq α] :
  is_strict_weak_order (finset α) (<ᶜ) := {}
instance [linear_order α] [decidable_eq α] :
  is_strict_total_order (finset α) (<ᶜ) := {}
instance colex_order [has_lt α] : has_le (finset α) := {le := (≤ᶜ)}
instance colex_preorder [linear_order α] : preorder (finset α) :=
{le_refl := refl_of (≤ᶜ), le_trans := is_trans.trans, ..colex_order}
instance colex_partial_order [linear_order α] : partial_order (finset α) :=
{le_antisymm := is_antisymm.antisymm, ..colex_preorder}
instance colex_linear_order [linear_order α] [decidable_eq α] :
  linear_order (finset α) :=
{le_total := is_total.total, ..colex_partial_order}

/--
Rewrite colex in a particular way so that it uses only bounded quantification,
so we can infer decidability.
-/
lemma colex_dec [has_lt α] (A B : finset α) : A <ᶜ B ↔
  ∃ (k ∈ B), (∀ x ∈ A, k < x → x ∈ B) ∧ (∀ x ∈ B, k < x → x ∈ A) ∧ k ∉ A :=
begin
  rw colex_lt, split,
  { rintro ⟨k, z, kA, kB⟩,
    refine ⟨k, kB, λ t th kt, (z kt).1 th, λ t th kt, (z kt).2 th, kA⟩ },
  { rintro ⟨k, kB, zAB, zBA, kA⟩,
    refine ⟨k, λ t th, _, kA, kB⟩, refine ⟨λ z, zAB _ z th, λ z, zBA _ z th⟩ }
end
instance colex_lt_decidable [decidable_linear_order α] (A B : finset α) :
  decidable (A <ᶜ B) := by rw colex_dec; apply_instance
instance colex_le_decidable [decidable_linear_order α] (A B : finset α) :
  decidable (A ≤ᶜ B) := or.decidable
instance colex_decidable_order [decidable_linear_order α] :
  decidable_linear_order (finset α) :=
{decidable_le := infer_instance, ..colex_linear_order}

/-- Colex is an extension of the base ordering on α. -/
lemma colex_singleton [linear_order α] {x y : α} :
  finset.singleton x <ᶜ finset.singleton y ↔ x < y :=
begin
  rw colex_lt, simp, conv_lhs { conv {congr, funext, rw and_comm,
                                      rw and_comm (¬k=x), rw and_assoc},
                                rw exists_eq_left },
  split, rintro ⟨p, q⟩, apply (lt_trichotomy x y).resolve_right,
    rw not_or_distrib, split, intro, apply p, symmetry, assumption,
    intro a, specialize q a, apply p, symmetry, rw ← q,
  intro, split, apply ne_of_gt a, intros z hz, rw iff_false_left,
    apply ne_of_gt hz, apply ne_of_gt (trans hz a)
end
/--
If A is before B in colex, and everything in B is small, then everything in
A is small.
-/
lemma max_colex [decidable_linear_order α] {A B : finset α} (t : α)
  (h₁ : A <ᶜ B) (h₂ : ∀ x ∈ B, x < t) :
  ∀ x ∈ A, x < t :=
begin
  rw colex_lt at h₁, rcases h₁ with ⟨k, z, _, _⟩,
  intros x hx, apply lt_of_not_ge, intro, apply not_lt_of_ge a, apply h₂,
  rwa ← z, apply lt_of_lt_of_le (h₂ k ‹_›) a,
end

/-- If everything in A is less than k, we can bound the sum of powers. -/
lemma binary_sum_nat {k : ℕ} {A : finset ℕ} (h₁ : ∀ {x}, x ∈ A → x < k) :
  A.sum (pow 2) < 2^k :=
begin
  apply lt_of_le_of_lt (sum_le_sum_of_subset (λ t, mem_range.2 ∘ h₁)),
  have z := geom_sum_mul_add 1 k, rw [geom_series, mul_one] at z,
  simp only [nat.pow_eq_pow] at z, rw ← z, apply nat.lt_succ_self
end

/-- Colex doesn't care if you remove the other set -/
lemma colex_ignores_sdiff [has_lt α] [decidable_eq α] (A B : finset α) :
  A <ᶜ B ↔ A \ B <ᶜ B \ A :=
begin
  rw colex_lt, rw colex_lt, apply exists_congr, intro k,
  split; rintro ⟨z, kA, kB⟩; refine ⟨_, _, _⟩; simp at kA kB z ⊢,
  intros x hx, rw z hx, intro, exact kB, exact ⟨kB, kA⟩,
  intros x hx, specialize z hx, tauto, tauto, tauto
end

/-- For subsets of ℕ, we can show that colex is equivalent to binary. -/
lemma binary_iff (A B : finset ℕ) : A.sum (pow 2) < B.sum (pow 2) ↔ A <ᶜ B :=
begin
  have z: ∀ (A B : finset ℕ), A <ᶜ B → A.sum (pow 2) < B.sum (pow 2),
    intros A B, rw colex_ignores_sdiff, rintro ⟨k, z, kA, kB⟩,
    rw ← sdiff_union_inter A B, conv_rhs {rw ← sdiff_union_inter B A},
    rw [sum_union (disjoint_sdiff_inter _ _), sum_union (disjoint_sdiff_inter _ _),
        inter_comm, add_lt_add_iff_right],
    apply lt_of_lt_of_le (@binary_sum_nat k (A \ B) _),
      apply single_le_sum (λ _ _, nat.zero_le _) kB,
    intros x hx, apply lt_of_le_of_ne (le_of_not_lt (λ kx, _)),
      apply (ne_of_mem_of_not_mem hx kA), specialize z kx, have := z.1 hx,
    rw mem_sdiff at this hx, exact hx.2 this.1,
  refine ⟨λ h, (trichotomous A B).resolve_right
               (λ h₁, h₁.elim _ (not_lt_of_gt h ∘ z _ _)), z A B⟩,
  rintro rfl, apply irrefl _ h
end
