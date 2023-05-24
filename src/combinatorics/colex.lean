/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
import algebra.geom_sum
import data.finset.slice

/-!
# Colex

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

* Colex order properties - linearity, decidability and so on.
* `finset.colex.forall_lt_mono`: if `s < t` in colex, and everything in `t` is `< a`, then
  everything in `s` is `< a`. This confirms the idea that an enumeration under colex will exhaust
  all sets using elements `< a` before allowing `a` to be included.
* `finset.to_colex_image_lt_to_colex_image`: Strictly monotone functions preserve colex.
* `finset.sum_two_pow_le_iff_colex_le`: colex for α = ℕ is the same as binary
  (this also proves binary expansions are unique)

## See also

Related files are:
* `data.list.lex`: Lexicographic order on lists.
* `data.pi.lex`: Lexicographic order on `Πₗ i, α i`.
* `data.psigma.order`: Lexicographic order on `Σ' i, α i`.
* `data.sigma.order`: Lexicographic order on `Σ i, α i`.
* `data.prod.lex`: Lexicographic order on `α × β`.

## TODO

* Generalise `colex.init_seg` so that it applies to `ℕ`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

colex, colexicographic, binary
-/

namespace finset
variables {α : Type*} [decidable_eq α] {s t : finset α}

@[simp] lemma symm_diff_eq_empty : s ∆ t = ∅ ↔ s = t := symm_diff_eq_bot

@[simp] lemma symm_diff_nonempty : (s ∆ t).nonempty ↔ s ≠ t :=
nonempty_iff_ne_empty.trans symm_diff_eq_empty.not

end finset

section
variables {α β : Type*} [decidable_eq β] {f : α → β}

open finset function

lemma function.injective.finset_image (hf : injective f) : injective (image f) :=
λ s t hst, coe_injective $ hf.image_injective $ by simpa using congr_arg (coe : _ → set β) hst

end

section
variables {k : ℕ} {s : finset ℕ}

open finset
open_locale big_operators

/-- If everything in `A` is less than `k`, we can bound the sum of powers. -/
lemma nat.sum_two_pow_lt (h₁ : ∀ a ∈ s, a < k) : ∑ a in s, 2 ^ a < 2^k :=
(sum_le_sum_of_subset $ λ t, mem_range.2 ∘ h₁ _).trans_lt $
  by simpa [one_add_one_eq_two] using (geom_sum_mul_add 1 k).le

end

variables {α β : Type*}

open finset
open_locale big_operators

namespace finset

/-- Type synonym of `finset α` equipped with the colexicographic order rather than the inclusion
order. -/
@[derive inhabited] def colex (α) := finset α

/-- `to_colex` is the "identity" function between `finset α` and `finset.colex α`. -/
def to_colex : finset α ≃ colex α := equiv.refl _
/-- `of_colex` is the "identity" function between `finset.colex α` and `finset α`. -/
def of_colex : colex α ≃ finset α := equiv.refl _

@[simp] lemma to_colex_symm_eq : (@to_colex α).symm = of_colex := rfl
@[simp] lemma of_colex_symm_eq : (@of_colex α).symm = to_colex := rfl
@[simp] lemma to_colex_of_colex (s : colex α) : to_colex (of_colex s) = s := rfl
@[simp] lemma of_colex_to_colex (s : finset α) : of_colex (to_colex s) = s := rfl
@[simp] lemma to_colex_inj {s t : finset α} : to_colex s = to_colex t ↔ s = t := iff.rfl
@[simp] lemma of_colex_inj {s t : colex α} : of_colex s = of_colex t ↔ s = t := iff.rfl
lemma to_colex_ne_to_colex {s t : finset α} : to_colex s ≠ to_colex t ↔ s ≠ t := iff.rfl
lemma of_colex_ne_of_colex {s t : colex α} : of_colex s ≠ of_colex t ↔ s ≠ t := iff.rfl

/-- Recursor for `colex α`. -/
@[elab_as_eliminator]
def colex.rec {C : colex α → Sort*} (h : Π s, C (to_colex s)) : Π s, C s := h

namespace colex

section has_lt
variables [has_lt α] {s t : finset α}

/--
`A` is less than `B` in the colex ordering if the largest thing that's not in both sets is in B.
In other words, `max (A ∆ B) ∈ B` (if the maximum exists).
-/
instance : has_lt (colex α) :=
⟨λ A B, ∃ k, (∀ ⦃x⦄, k < x → (x ∈ of_colex A ↔ x ∈ of_colex B)) ∧ k ∉ of_colex A ∧ k ∈ of_colex B⟩

/-- We can define (≤) in the obvious way. -/
instance : has_le (colex α) := ⟨λ A B, A = B ∨ A < B⟩

lemma lt_def : s.to_colex < t.to_colex ↔ ∃ k, (∀ ⦃x⦄, k < x → (x ∈ s ↔ x ∈ t)) ∧ k ∉ s ∧ k ∈ t :=
iff.rfl

lemma le_def :
  s.to_colex ≤ t.to_colex ↔ s = t ∨ ∃ k, (∀ ⦃x⦄, k < x → (x ∈ s ↔ x ∈ t)) ∧ k ∉ s ∧ k ∈ t :=
iff.rfl

instance : is_irrefl (colex α) (<) := ⟨by simp [(<)]⟩

/-- Colex doesn't care if you remove the other set -/
@[simp] lemma sdiff_lt_sdiff_iff_lt [decidable_eq α] (s t : finset α) :
  (s \ t).to_colex < (t \ s).to_colex ↔ s.to_colex < t.to_colex :=
begin
  rw [lt_def, lt_def],
  refine exists_congr (λ k, _),
  simp only [mem_sdiff, not_and, not_not],
  split,
  { rintro ⟨z, kAB, kB, kA⟩,
    refine ⟨λ x hx, _, kA, kB⟩,
    specialize z hx,
    tauto },
  { rintro ⟨z, kA, kB⟩,
    refine ⟨λ x hx, _, λ _, kB, kB, kA⟩,
    rw z hx }
end

end has_lt

section linear_order
variables [linear_order α] [linear_order β] {f : α → β} {𝒜 𝒜₁ 𝒜₂ : finset (finset α)}
  {s t : finset α} {a b : α} {r : ℕ}

instance : is_strict_total_order (colex α) (<) :=
{ irrefl := irrefl_of (<),
  trans := λ s t u, begin
    rintro ⟨k₁, k₁z, notinA, inB⟩ ⟨k₂, k₂z, notinB, inC⟩,
    cases (ne_of_mem_of_not_mem inB notinB).lt_or_lt,
    { refine ⟨k₂, λ x hx, _, by rwa k₁z h, inC⟩,
      rw ← k₂z hx,
      exact k₁z (trans h hx) },
    { refine ⟨k₁, λ x hx, _, notinA, by rwa ← k₂z h⟩,
      rw k₁z hx,
      exact k₂z (trans h hx) }
  end,
  trichotomous := λ s t, begin
    classical,
    obtain rfl | hts := eq_or_ne t s,
    { simp },
    obtain ⟨k, hk, z⟩ := exists_max_image (of_colex t ∆ of_colex s) id (symm_diff_nonempty.2 hts),
    refine (mem_symm_diff.1 hk).imp (λ hk, ⟨k, λ a ha, _, hk.2, hk.1⟩)
      (λ hk, or.inr ⟨k, λ a ha, _, hk.2, hk.1⟩);
      simpa [mem_symm_diff, not_or_distrib, iff_iff_implies_and_implies, and_comm]
        using not_imp_not.2 (z a) ha.not_le,
  end }

instance decidable_lt : @decidable_rel (colex α) (<) :=
λ s t, decidable_of_iff'
  (∃ k ∈ of_colex t, (∀ x ∈ of_colex s ∪ of_colex t, k < x → (x ∈ of_colex s ↔ x ∈ of_colex t))
    ∧ k ∉ of_colex s)
  begin
    apply exists_congr,
    simp only [mem_union, exists_prop, or_imp_distrib, and_comm (_ ∈ of_colex t), and_assoc],
    exact λ k, and_congr_left' (forall_congr $ by tauto),
  end

instance : linear_order (colex α) := linear_order_of_STO (<)

instance : order_bot (colex α) :=
{ bot := (∅ : finset α).to_colex,
  bot_le := λ s, begin
    induction s using finset.colex.rec,
    rw le_def,
    obtain rfl | hs := s.eq_empty_or_nonempty,
    { simp },
    refine or.inr ⟨max' _ hs, _, by simp, max'_mem _ _⟩,
    simp only [false_iff, not_mem_empty],
    exact λ x hx t, not_le_of_lt hx (le_max' _ _ t),
  end }

@[simp] lemma to_colex_empty : to_colex (∅ : finset α) = ⊥ := rfl
--TODO: This lemma should be simp, but its LHS is not in simp normal form because
-- `finset.bot_eq_empty` (wrongfully) applies
lemma of_colex_bot : of_colex (⊥ : colex α) = ∅ := rfl

/-- Colex doesn't care if you remove the other set -/
@[simp] lemma sdiff_le_sdiff_iff_le (A B : finset α) :
  (A \ B).to_colex ≤ (B \ A).to_colex ↔ A.to_colex ≤ B.to_colex :=
by rw [le_iff_le_iff_lt_iff_lt, sdiff_lt_sdiff_iff_lt]

/-- If `A ⊂ B`, then `A` is less than `B` in the colex order. Note the converse does not hold, as
`⊆` is not a linear order. -/
lemma colex_lt_of_ssubset (h : s ⊂ t) : s.to_colex < t.to_colex :=
begin
  rw [←sdiff_lt_sdiff_iff_lt, sdiff_eq_empty_iff_subset.2 h.1, to_colex_empty, bot_lt_iff_ne_bot,
    ←to_colex_empty, to_colex_ne_to_colex],
  simpa using h.not_subset,
end

/-- If `A ⊆ B`, then `A ≤ B` in the colex order. Note the converse does not hold, as `⊆` is not a
linear order. -/
lemma colex_le_of_subset (h : s ⊆ t) : s.to_colex ≤ t.to_colex :=
by { rw [←sdiff_le_sdiff_iff_le, sdiff_eq_empty_iff_subset.2 h, to_colex_empty], exact bot_le }

instance [fintype α] : bounded_order (colex α) :=
{ top := univ.to_colex,
  le_top := λ x, colex_le_of_subset (subset_univ _),
  ..colex.order_bot }

@[simp] lemma to_colex_univ [fintype α] : to_colex (univ : finset α) = ⊤ := rfl
--TODO: This lemma should be simp, but its LHS is not in simp normal form because
-- `finset.top_eq_univ` (wrongfully) applies
lemma of_colex_top [fintype α] : of_colex (⊤ : colex α) = univ := rfl

/-- `s < {a}` in colex iff all elements of `s` are strictly less than `a`. -/
lemma to_colex_lt_singleton : s.to_colex < ({a} : finset α).to_colex ↔ ∀ x ∈ s, x < a :=
begin
  simp only [lt_def, mem_singleton, ←and_assoc, exists_eq_right],
  split,
  { intros t x hx,
    rw ←not_le,
    intro h,
    rcases lt_or_eq_of_le h with h₁ | rfl,
    { exact ne_of_irrefl h₁ ((t.1 h₁).1 hx).symm },
    { exact t.2 hx } },
  { exact λ h, ⟨λ z hz, ⟨λ i, (asymm hz (h _ i)).elim, λ i, (hz.ne' i).elim⟩, by simpa using h a⟩ }
end

/-- `{a} ≤ s` in colex iff `r` contains an element greated than or equal to `a`. -/
lemma singleton_le_to_colex : ({a} : finset α).to_colex ≤ s.to_colex ↔ ∃ x ∈ s, a ≤ x :=
by simp [←not_lt, to_colex_lt_singleton]

/-- Colex is an extension of the base order. -/
lemma singleton_lt_singleton : ({a} : finset α).to_colex < ({b} : finset α).to_colex ↔ a < b :=
by simp [to_colex_lt_singleton]

/-- Colex is an extension of the base order. -/
lemma singleton_le_singleton : ({a} : finset α).to_colex ≤ ({b} : finset α).to_colex ↔ a ≤ b :=
by rw [le_iff_le_iff_lt_iff_lt, singleton_lt_singleton]

/-- If `s` is before `t` in colex, and everything in `t` is small, then everything in `s` is small.
-/
lemma forall_lt_mono (h₁ : s.to_colex ≤ t.to_colex) (h₂ : ∀ x ∈ t, x < a) : ∀ x ∈ s, x < a :=
begin
  rw le_def at h₁,
  obtain rfl | ⟨k, z, -, hk⟩ := h₁,
  { assumption },
  { refine λ x hx, lt_of_not_le (λ h, h.not_lt $ h₂ x _),
    rwa ←z ((h₂ k hk).trans_le h) }
end

/-- Strictly monotone functions preserve the colex ordering. -/
lemma _root_.finset.to_colex_image_lt_to_colex_image (hf : strict_mono f) :
  (s.image f).to_colex < (t.image f).to_colex ↔ s.to_colex < t.to_colex :=
begin
  simp only [lt_def, not_exists, mem_image, exists_prop, not_and],
  split,
  { rintro ⟨k, z, q, k', _, rfl⟩,
    exact ⟨k', λ x hx, by simpa [hf.injective.eq_iff] using z (hf hx), λ t, q _ t rfl, ‹k' ∈ t›⟩ },
  rintro ⟨k, z, ka, _⟩,
  refine ⟨f k, λ x hx, _, _, k, ‹k ∈ t›, rfl⟩,
  { split,
    any_goals
    { rintro ⟨x', hx', rfl⟩,
      refine ⟨x', _, rfl⟩,
      rwa ← z _ <|> rwa z _,
      rwa strict_mono.lt_iff_lt hf at hx } },
  { simp only [hf.injective, function.injective.eq_iff],
    exact λ x hx, ne_of_mem_of_not_mem hx ka }
end

/-- Strictly monotone functions preserve the colex ordering. -/
lemma _root_.finset.to_colex_image_le_to_colex_image (hf : strict_mono f) :
  (s.image f).to_colex ≤ (t.image f).to_colex ↔ s.to_colex ≤ t.to_colex :=
by rw [le_iff_le_iff_lt_iff_lt, to_colex_image_lt_to_colex_image hf]

/-! ### Initial segments -/

/-- `𝒜` is an initial segment of the colexigraphic order on sets of `r`, and that if `B` is below
`A` in colex where `B` has size `r` and `A` is in `𝒜`, then `B` is also in `𝒜`. In effect, `𝒜` is
downwards closed with respect to colex among sets of size `r`. -/
def is_init_seg (𝒜 : finset (finset α)) (r : ℕ) : Prop :=
(𝒜 : set (finset α)).sized r ∧
  ∀ ⦃A B : finset α⦄, A ∈ 𝒜 → B.to_colex < A.to_colex ∧ B.card = r → B ∈ 𝒜

@[simp] lemma is_init_set_empty : is_init_seg (∅ : finset (finset α)) r := by simp [is_init_seg]

/-- Initial segments are nested in some way. In particular, if they're the same size they're equal.
-/
lemma is_init_seg.total (h₁ : is_init_seg 𝒜₁ r) (h₂ : is_init_seg 𝒜₂ r) : 𝒜₁ ⊆ 𝒜₂ ∨ 𝒜₂ ⊆ 𝒜₁ :=
begin
  classical,
  simp_rw [←sdiff_eq_empty_iff_subset, ←not_nonempty_iff_eq_empty],
  by_contra' h,
  obtain ⟨⟨A, Ah⟩, B, hB⟩ := h,
  rw mem_sdiff at Ah hB,
  obtain lt | eq | gt := trichotomous_of (<) A.to_colex B.to_colex,
  { exact Ah.2 (h₂.2 hB.1 ⟨lt, h₁.1 Ah.1⟩) },
  { rw to_colex_inj.1 eq at Ah,
    exact hB.2 Ah.1 },
  { exact hB.2 (h₁.2 Ah.1 ⟨gt, h₂.1 hB.1⟩) }
end

variables [fintype α]

/-- Gives all sets up to `A` with the same size as it: this is equivalent to
being an initial segment of colex. -/
def init_seg (s : finset α) : finset (finset α) :=
univ.filter $ λ t, s.card = t.card ∧ t.to_colex ≤ s.to_colex

@[simp] lemma mem_init_seg : t ∈ init_seg s ↔ s.card = t.card ∧ t.to_colex ≤ s.to_colex :=
by simp [init_seg]

@[simp] lemma mem_init_seg_self : s ∈ init_seg s := by simp

@[simp] lemma init_seg_nonempty : (init_seg s).nonempty := ⟨s, mem_init_seg_self⟩

/-- Being a nonempty initial segment of colex if equivalent to being an `init_seg`. -/
lemma is_init_seg_iff_exists_init_seg :
  𝒜.nonempty ∧ is_init_seg 𝒜 r ↔ ∃ s : finset α, s.card = r ∧ 𝒜 = init_seg s :=
begin
  split,
  { rintro ⟨ne, layer, IS⟩,
    have Ah := @max'_mem (colex α) _ 𝒜 ne,
    refine ⟨@max' (colex α) _ 𝒜 ne, layer Ah, _⟩,
    ext B,
    rw mem_init_seg,
    refine ⟨λ p, _, _⟩,
    { rw [layer p, layer Ah],
      exact ⟨rfl, le_max' _ _ p⟩ },
    rintro ⟨cards, le⟩,
    obtain p | p := le.eq_or_lt,
    { rwa to_colex_inj.1 p, },
    { exact IS Ah ⟨p, cards ▸ layer Ah⟩ } },
  { rintro ⟨s, hs, rfl⟩,
    refine ⟨init_seg_nonempty, λ B hB, (mem_init_seg.1 hB).1.symm.trans hs,
      λ B₁ B₂ hB₁ hB₂, mem_init_seg.2 ⟨_, _⟩⟩,
    { rwa hB₂.2 },
    { rw mem_init_seg at hB₁,
      exact hB₂.1.le.trans hB₁.2 } }
end

lemma is_init_seg_init_seg : is_init_seg (init_seg s) s.card :=
(is_init_seg_iff_exists_init_seg.2 ⟨s, rfl, rfl⟩).2

end linear_order
end colex

open colex

/-!
### Colex on `ℕ`

The colexicographic order agrees with the order induced by interpreting a set of naturals as a
binary expansion.
-/

section nat

/-- For subsets of ℕ, we can show that colex is equivalent to binary. -/
lemma sum_two_pow_lt_iff_colex_lt (A B : finset ℕ) :
  ∑ i in A, 2^i < ∑ i in B, 2^i ↔ A.to_colex < B.to_colex :=
begin
  have z : ∀ (A B : finset ℕ), A.to_colex < B.to_colex → ∑ i in A, 2^i < ∑ i in B, 2^i,
  { intros A B,
    rw [← sdiff_lt_sdiff_iff_lt, lt_def],
    rintro ⟨k, z, kA, kB⟩,
    rw ← sdiff_union_inter A B,
    conv_rhs { rw ← sdiff_union_inter B A },
    rw [sum_union (disjoint_sdiff_inter _ _), sum_union (disjoint_sdiff_inter _ _),
        inter_comm, add_lt_add_iff_right],
    apply lt_of_lt_of_le (@nat.sum_two_pow_lt k (A \ B) _),
    { apply single_le_sum (λ _ _, nat.zero_le _) kB },
    intros x hx,
    apply lt_of_le_of_ne (le_of_not_lt (λ kx, _)),
    { exact (ne_of_mem_of_not_mem hx kA) },
    have := (z kx).1 hx,
    rw mem_sdiff at this hx,
    exact hx.2 this.1 },
  refine ⟨λ h, (lt_trichotomy (to_colex A) $ to_colex B).resolve_right
    (λ h₁, h₁.elim _ (not_lt_of_gt h ∘ z _ _)), z A B⟩,
  rw to_colex_inj,
  rintro rfl,
  exact irrefl _ h,
end

/-- For subsets of ℕ, we can show that colex is equivalent to binary. -/
lemma sum_two_pow_le_iff_colex_le (A B : finset ℕ) :
  ∑ i in A, 2^i ≤ ∑ i in B, 2^i ↔ A.to_colex ≤ B.to_colex :=
by rw [le_iff_le_iff_lt_iff_lt, sum_two_pow_lt_iff_colex_lt]

end nat
end finset
