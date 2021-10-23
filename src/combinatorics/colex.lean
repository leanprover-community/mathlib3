/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import data.finset
import data.fintype.basic
import algebra.geom_sum

/-!
# Colex

We define the colex ordering for finite sets, and give a couple of important
lemmas and properties relating to it.

The colex ordering likes to avoid large values - it can be thought of on
`finset ℕ` as the "binary" ordering. That is, order A based on
`∑_{i ∈ A} 2^i`.
It's defined here in a slightly more general way, requiring only `has_lt α` in
the definition of colex on `finset α`. In the context of the Kruskal-Katona
theorem, we are interested in particular on how colex behaves for sets of a
fixed size. If the size is 3, colex on ℕ starts
123, 124, 134, 234, 125, 135, 235, 145, 245, 345, ...

## Main statements
* `colex.hom_lt_iff`: strictly monotone functions preserve colex
* Colex order properties - linearity, decidability and so on.
* `forall_lt_of_colex_lt_of_forall_lt`: if A < B in colex, and everything
  in B is < t, then everything in A is < t. This confirms the idea that
  an enumeration under colex will exhaust all sets using elements < t before
  allowing t to be included.
* `sum_two_pow_le_iff_lt`: colex for α = ℕ is the same as binary
  (this also proves binary expansions are unique)

## Notation
We define `<` and `≤` to denote colex ordering, useful in particular when
multiple orderings are available in context.

## Tags
colex, colexicographic, binary

## References
* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

-/

variable {α : Type*}

open finset
open_locale big_operators

/--
We define this type synonym to refer to the colexicographic ordering on finsets
rather than the natural subset ordering.
-/
@[derive inhabited]
def finset.colex (α) := finset α

/--
A convenience constructor to turn a `finset α` into a `finset.colex α`, useful in order to
use the colex ordering rather than the subset ordering.
-/
def finset.to_colex {α} (s : finset α) : finset.colex α := s

@[simp]
lemma colex.eq_iff (A B : finset α) :
  A.to_colex = B.to_colex ↔ A = B := iff.rfl

/--
`A` is less than `B` in the colex ordering if the largest thing that's not in both sets is in B.
In other words, max (A Δ B) ∈ B (if the maximum exists).
-/
instance [has_lt α] : has_lt (finset.colex α) :=
⟨λ (A B : finset α), ∃ (k : α), (∀ {x}, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A ∧ k ∈ B⟩

/-- We can define (≤) in the obvious way. -/
instance [has_lt α] : has_le (finset.colex α) :=
⟨λ A B, A < B ∨ A = B⟩

lemma colex.lt_def [has_lt α] (A B : finset α) :
  A.to_colex < B.to_colex ↔ ∃ k, (∀ {x}, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A ∧ k ∈ B :=
iff.rfl
lemma colex.le_def [has_lt α] (A B : finset α) :
  A.to_colex ≤ B.to_colex ↔ A.to_colex < B.to_colex ∨ A = B :=
iff.rfl

/-- If everything in `A` is less than `k`, we can bound the sum of powers. -/
lemma nat.sum_two_pow_lt {k : ℕ} {A : finset ℕ} (h₁ : ∀ {x}, x ∈ A → x < k) :
  A.sum (pow 2) < 2^k :=
begin
  apply lt_of_le_of_lt (sum_le_sum_of_subset (λ t, mem_range.2 ∘ h₁)),
  have z := geom_sum_mul_add 1 k,
  rw [geom_sum, mul_one, one_add_one_eq_two] at z,
  rw ← z,
  apply nat.lt_succ_self,
end

namespace colex

/-- Strictly monotone functions preserve the colex ordering. -/
lemma hom_lt_iff {β : Type*} [linear_order α] [decidable_eq β] [preorder β]
  {f : α → β} (h₁ : strict_mono f) (A B : finset α) :
  (A.image f).to_colex < (B.image f).to_colex ↔ A.to_colex < B.to_colex :=
begin
  simp only [colex.lt_def, not_exists, mem_image, exists_prop, not_and],
  split,
  { rintro ⟨k, z, q, k', _, rfl⟩,
    exact ⟨k', λ x hx, by simpa [h₁.injective.eq_iff] using z (h₁ hx), λ t, q _ t rfl, ‹k' ∈ B›⟩ },
  rintro ⟨k, z, ka, _⟩,
  refine ⟨f k, λ x hx, _, _, k, ‹k ∈ B›, rfl⟩,
  { split,
    any_goals {
      rintro ⟨x', hx', rfl⟩,
      refine ⟨x', _, rfl⟩,
      rwa ← z _ <|> rwa z _,
      rwa strict_mono.lt_iff_lt h₁ at hx } },
  { simp only [h₁.injective, function.injective.eq_iff],
    exact λ x hx, ne_of_mem_of_not_mem hx ka }
end

/-- A special case of `colex.hom_lt_iff` which is sometimes useful. -/
@[simp] lemma hom_fin_lt_iff {n : ℕ} (A B : finset (fin n)) :
  (A.image (λ i : fin n, (i : ℕ))).to_colex < (B.image (λ i : fin n, (i : ℕ))).to_colex
   ↔ A.to_colex < B.to_colex :=
colex.hom_lt_iff (λ x y k, k) _ _

instance [has_lt α] : is_irrefl (finset.colex α) (<) :=
⟨λ A h, exists.elim h (λ _ ⟨_,a,b⟩, a b)⟩

@[trans]
lemma lt_trans [linear_order α] {a b c : finset.colex α} :
  a < b → b < c → a < c :=
begin
  rintros ⟨k₁, k₁z, notinA, inB⟩ ⟨k₂, k₂z, notinB, inC⟩,
  cases lt_or_gt_of_ne (ne_of_mem_of_not_mem inB notinB),
  { refine ⟨k₂, _, by rwa k₁z h, inC⟩,
    intros x hx,
    rw ← k₂z hx,
    apply k₁z (trans h hx) },
  { refine ⟨k₁, _, notinA, by rwa ← k₂z h⟩,
    intros x hx,
    rw k₁z hx,
    apply k₂z (trans h hx) }
end

@[trans]
lemma le_trans [linear_order α] (a b c : finset.colex α) :
  a ≤ b → b ≤ c → a ≤ c :=
λ AB BC, AB.elim (λ k, BC.elim (λ t, or.inl (lt_trans k t)) (λ t, t ▸ AB)) (λ k, k.symm ▸ BC)

instance [linear_order α] : is_trans (finset.colex α) (<) := ⟨λ _ _ _, colex.lt_trans⟩

lemma lt_trichotomy [linear_order α] (A B : finset.colex α) :
  A < B ∨ A = B ∨ B < A :=
begin
  by_cases h₁ : (A = B),
  { tauto },
  rcases (exists_max_image (A \ B ∪ B \ A) id _) with ⟨k, hk, z⟩,
  { simp only [mem_union, mem_sdiff] at hk,
    cases hk,
    { right,
      right,
      refine ⟨k, λ t th, _, hk.2, hk.1⟩,
      specialize z t,
      by_contra h₂,
      simp only [mem_union, mem_sdiff, id.def] at z,
      rw [not_iff, iff_iff_and_or_not_and_not, not_not, and_comm] at h₂,
      apply not_le_of_lt th (z h₂) },
    { left,
      refine ⟨k, λ t th, _, hk.2, hk.1⟩,
      specialize z t,
      by_contra h₃,
      simp only [mem_union, mem_sdiff, id.def] at z,
      rw [not_iff, iff_iff_and_or_not_and_not, not_not, and_comm, or_comm] at h₃,
      apply not_le_of_lt th (z h₃) }, },
  rw nonempty_iff_ne_empty,
  intro a,
  simp only [union_eq_empty_iff, sdiff_eq_empty_iff_subset] at a,
  apply h₁ (subset.antisymm a.1 a.2)
end

instance [linear_order α] : is_trichotomous (finset.colex α) (<) := ⟨lt_trichotomy⟩

instance decidable_lt [linear_order α] : ∀ {A B : finset.colex α}, decidable (A < B) :=
show ∀ A B : finset α, decidable (A.to_colex < B.to_colex),
from λ A B, decidable_of_iff'
  (∃ (k ∈ B), (∀ x ∈ A ∪ B, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A)
  begin
    rw colex.lt_def,
    apply exists_congr,
    simp only [mem_union, exists_prop, or_imp_distrib, and_comm (_ ∈ B), and_assoc],
    intro k,
    refine and_congr_left' (forall_congr _),
    tauto,
  end

instance [linear_order α] : linear_order (finset.colex α) :=
{ le_refl := λ A, or.inr rfl,
  le_trans := le_trans,
  le_antisymm := λ A B AB BA, AB.elim (λ k, BA.elim (λ t, (asymm k t).elim) (λ t, t.symm)) id,
  le_total := λ A B,
          (lt_trichotomy A B).elim3 (or.inl ∘ or.inl) (or.inl ∘ or.inr) (or.inr ∘ or.inl),
  decidable_le := λ A B, by apply_instance,
  decidable_lt := λ A B, by apply_instance,
  decidable_eq := λ A B, by apply_instance,
  lt_iff_le_not_le := λ A B,
  begin
    split,
    { intro t,
      refine ⟨or.inl t, _⟩,
      rintro (i | rfl),
      { apply asymm_of _ t i },
      { apply irrefl _ t } },
    rintro ⟨h₁ | rfl, h₂⟩,
    { apply h₁ },
    apply h₂.elim (or.inr rfl),
  end,
  ..finset.colex.has_lt,
  ..finset.colex.has_le }

/-- The instances set up let us infer that `colex.lt` is a strict total order. -/
example [linear_order α] : is_strict_total_order (finset.colex α) (<) := infer_instance

/-- Strictly monotone functions preserve the colex ordering. -/
lemma hom_le_iff {β : Type*} [linear_order α] [linear_order β]
  {f : α → β} (h₁ : strict_mono f) (A B : finset α) :
  (A.image f).to_colex ≤ (B.image f).to_colex ↔ A.to_colex ≤ B.to_colex :=
by rw [le_iff_le_iff_lt_iff_lt, hom_lt_iff h₁]

/-- A special case of `colex_hom` which is sometimes useful. -/
@[simp] lemma hom_fin_le_iff {n : ℕ} (A B : finset (fin n)) :
  (A.image (λ i : fin n, (i : ℕ))).to_colex ≤ (B.image (λ i : fin n, (i : ℕ))).to_colex
   ↔ A.to_colex ≤ B.to_colex :=
colex.hom_le_iff (λ x y k, k) _ _

/--
If `A` is before `B` in colex, and everything in `B` is small, then everything in `A` is small.
-/
lemma forall_lt_of_colex_lt_of_forall_lt [linear_order α] {A B : finset α}
  (t : α) (h₁ : A.to_colex < B.to_colex) (h₂ : ∀ x ∈ B, x < t) :
  ∀ x ∈ A, x < t :=
begin
  rw colex.lt_def at h₁,
  rcases h₁ with ⟨k, z, _, _⟩,
  intros x hx,
  apply lt_of_not_ge,
  intro a,
  refine not_lt_of_ge a (h₂ x _),
  rwa ← z,
  apply lt_of_lt_of_le (h₂ k ‹_›) a,
end

/-- `s.to_colex < {r}.to_colex` iff all elements of `s` are less than `r`. -/
lemma lt_singleton_iff_mem_lt [linear_order α] {r : α} {s : finset α} :
  s.to_colex < ({r} : finset α).to_colex ↔ ∀ x ∈ s, x < r :=
begin
  simp only [lt_def, mem_singleton, ←and_assoc, exists_eq_right],
  split,
  { intros t x hx,
    rw ←not_le,
    intro h,
    rcases lt_or_eq_of_le h with h₁ | rfl,
    { exact ne_of_irrefl h₁ ((t.1 h₁).1 hx).symm },
    { exact t.2 hx } },
  { exact λ h, ⟨λ z hz, ⟨λ i, (asymm hz (h _ i)).elim, λ i, (hz.ne' i).elim⟩, by simpa using h r⟩ }
end

/-- If {r} is less than or equal to s in the colexicographical sense,
  then s contains an element greater than or equal to r. -/
lemma mem_le_of_singleton_le [linear_order α] {r : α} {s : finset α}:
  ({r} : finset α).to_colex ≤ s.to_colex ↔ ∃ x ∈ s, r ≤ x :=
by { rw ←not_lt, simp [lt_singleton_iff_mem_lt] }

/-- Colex is an extension of the base ordering on α. -/
lemma singleton_lt_iff_lt [linear_order α] {r s : α} :
  ({r} : finset α).to_colex < ({s} : finset α).to_colex ↔ r < s :=
by simp [lt_singleton_iff_mem_lt]

/-- Colex is an extension of the base ordering on α. -/
lemma singleton_le_iff_le [linear_order α] {r s : α} :
  ({r} : finset α).to_colex ≤ ({s} : finset α).to_colex ↔ r ≤ s :=
by rw [le_iff_le_iff_lt_iff_lt, singleton_lt_iff_lt]

/-- Colex doesn't care if you remove the other set -/
@[simp] lemma sdiff_lt_sdiff_iff_lt [has_lt α] [decidable_eq α] (A B : finset α) :
  (A \ B).to_colex < (B \ A).to_colex ↔ A.to_colex < B.to_colex :=
begin
  rw [colex.lt_def, colex.lt_def],
  apply exists_congr,
  intro k,
  simp only [mem_sdiff, not_and, not_not],
  split,
  { rintro ⟨z, kAB, kB, kA⟩,
    refine ⟨_, kA, kB⟩,
    { intros x hx,
      specialize z hx,
      tauto } },
  { rintro ⟨z, kA, kB⟩,
    refine ⟨_, λ _, kB, kB, kA⟩,
    intros x hx,
    rw z hx },
end

/-- Colex doesn't care if you remove the other set -/
@[simp] lemma sdiff_le_sdiff_iff_le [linear_order α] (A B : finset α) :
  (A \ B).to_colex ≤ (B \ A).to_colex ↔ A.to_colex ≤ B.to_colex :=
by rw [le_iff_le_iff_lt_iff_lt, sdiff_lt_sdiff_iff_lt]

lemma empty_to_colex_lt [linear_order α] {A : finset α} (hA : A.nonempty) :
  (∅ : finset α).to_colex < A.to_colex :=
begin
  rw [colex.lt_def],
  refine ⟨max' _ hA, _, by simp, max'_mem _ _⟩,
  simp only [false_iff, not_mem_empty],
  intros x hx t,
  apply not_le_of_lt hx (le_max' _ _ t),
end

/-- If `A ⊂ B`, then `A` is less than `B` in the colex order. Note the converse does not hold, as
`⊆` is not a linear order. -/
lemma colex_lt_of_ssubset [linear_order α] {A B : finset α} (h : A ⊂ B) :
  A.to_colex < B.to_colex :=
begin
  rw [←sdiff_lt_sdiff_iff_lt, sdiff_eq_empty_iff_subset.2 h.1],
  exact empty_to_colex_lt (by simpa [finset.nonempty] using exists_of_ssubset h),
end

@[simp] lemma empty_to_colex_le [linear_order α] {A : finset α} :
  (∅ : finset α).to_colex ≤ A.to_colex :=
begin
  rcases A.eq_empty_or_nonempty with rfl | hA,
  { simp },
  { apply (empty_to_colex_lt hA).le },
end

/-- If `A ⊆ B`, then `A ≤ B` in the colex order. Note the converse does not hold, as `⊆` is not a
linear order. -/
lemma colex_le_of_subset [linear_order α] {A B : finset α} (h : A ⊆ B) :
  A.to_colex ≤ B.to_colex :=
begin
  rw [←sdiff_le_sdiff_iff_le, sdiff_eq_empty_iff_subset.2 h],
  apply empty_to_colex_le
end

/-- The function from finsets to finsets with the colex order is a relation homomorphism. -/
@[simps]
def to_colex_rel_hom [linear_order α] :
  ((⊆) : finset α → finset α → Prop) →r ((≤) : finset.colex α → finset.colex α → Prop) :=
{ to_fun := finset.to_colex,
  map_rel' := λ A B, colex_le_of_subset }

instance [linear_order α] : order_bot (finset.colex α) :=
{ bot := (∅ : finset α).to_colex,
  bot_le := λ x, empty_to_colex_le,
  ..(by apply_instance : partial_order (finset.colex α)) }

instance [linear_order α] : semilattice_inf_bot (finset.colex α) :=
{ ..finset.colex.order_bot,
  ..(by apply_instance : semilattice_inf (finset.colex α)) }

instance [linear_order α] : semilattice_sup_bot (finset.colex α) :=
{ ..finset.colex.order_bot,
  ..(by apply_instance : semilattice_sup (finset.colex α)) }

instance [linear_order α] [fintype α] : bounded_lattice (finset.colex α) :=
{ top := finset.univ.to_colex,
  le_top := λ x, colex_le_of_subset (subset_univ _),
  ..(by apply_instance : semilattice_sup (finset.colex α)),
  ..(by apply_instance : semilattice_inf_bot (finset.colex α)) }

/-- For subsets of ℕ, we can show that colex is equivalent to binary. -/
lemma sum_two_pow_lt_iff_lt (A B : finset ℕ) :
  ∑ i in A, 2^i < ∑ i in B, 2^i ↔ A.to_colex < B.to_colex :=
begin
  have z : ∀ (A B : finset ℕ), A.to_colex < B.to_colex → ∑ i in A, 2^i < ∑ i in B, 2^i,
  { intros A B,
    rw [← sdiff_lt_sdiff_iff_lt, colex.lt_def],
    rintro ⟨k, z, kA, kB⟩,
    rw ← sdiff_union_inter A B,
    conv_rhs { rw ← sdiff_union_inter B A },
    rw [sum_union (disjoint_sdiff_inter _ _), sum_union (disjoint_sdiff_inter _ _),
        inter_comm, add_lt_add_iff_right],
    apply lt_of_lt_of_le (@nat.sum_two_pow_lt k (A \ B) _),
    { apply single_le_sum (λ _ _, nat.zero_le _) kB },
    intros x hx,
    apply lt_of_le_of_ne (le_of_not_lt (λ kx, _)),
    { apply (ne_of_mem_of_not_mem hx kA) },
    have := (z kx).1 hx,
    rw mem_sdiff at this hx,
    exact hx.2 this.1 },
  refine ⟨λ h, (lt_trichotomy A B).resolve_right (λ h₁, h₁.elim _ (not_lt_of_gt h ∘ z _ _)), z A B⟩,
  rintro rfl,
  apply irrefl _ h
end

/-- For subsets of ℕ, we can show that colex is equivalent to binary. -/
lemma sum_two_pow_le_iff_lt (A B : finset ℕ) :
  ∑ i in A, 2^i ≤ ∑ i in B, 2^i ↔ A.to_colex ≤ B.to_colex :=
by rw [le_iff_le_iff_lt_iff_lt, sum_two_pow_lt_iff_lt]

end colex
