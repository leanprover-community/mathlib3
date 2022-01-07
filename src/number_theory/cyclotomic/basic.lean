/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import ring_theory.polynomial.cyclotomic.basic
import number_theory.number_field
import algebra.char_p.algebra

/-!
# Cyclotomic extensions

Let `A` and `B` be commutative rings with `algebra A B`. For `S : set ℕ+`, we define a class
`is_cyclotomic_extension S A B` expressing the fact that `B` is obtained from `A` by adding `n`-th
primitive roots of unity, for all `n ∈ S`.

## Main definition

* `is_cyclotomic_extension S A B` : means that `B` is obtained from `A` by adding `n`-th primitive
roots of unity, for all `n ∈ S`.

## Main results

* `is_cyclotomic_extension.trans`: if `is_cyclotomic_extension S A B` and
  `is_cyclotomic_extension T B C`, then `is_cyclotomic_extension (S ∪ T) A C`.
* `is_cyclotomic_extension.union_right` : given `is_cyclotomic_extension (S ∪ T) A B`, then
  `is_cyclotomic_extension T (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) B`.
* `is_cyclotomic_extension.union_right` : given `is_cyclotomic_extension T A B` and `S ⊆ T`, then
  `is_cyclotomic_extension S A (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 })`.
* `is_cyclotomic_extension.finite` : if `S` is finite and `is_cyclotomic_extension S A B`, then
  `B` is a finite `A`-algebra.
* `is_cyclotomic_extension.number_field` : a finite cyclotomic extension of a number field is a
  number field.

## Implementation details

Our definition of `is_cyclotomic_extension` is very general, to allow rings of any characteristic
and infinite extensions, but it will mainly be used in the case `S = {n}` with `(n : A) ≠ 0` (and
for integral domains).
All results are in the `is_cyclotomic_extension` namespace.
Note that some results, `is_cyclotomic_extension.trans`, `is_cyclotomic_extension.finite` and
`is_cyclotomic_extension.number_field` are lemmas, but they can be made local instances.

-/

open polynomial algebra finite_dimensional module set

open_locale big_operators

universes u v w z

variables (n : ℕ+) (S T : set ℕ+) (A : Type u) (B : Type v) (K : Type w) (L : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L] [algebra K L]

noncomputable theory

/-- Given an `A`-algebra `B` and `S : set ℕ+`, we define `is_cyclotomic_extension S A B` requiring
that `cyclotomic a A` has a root in `B` for all `a ∈ S` and that `B` is generated over `A` by the
roots of `X ^ n - 1`. -/
@[mk_iff] class is_cyclotomic_extension : Prop :=
(exists_root {a : ℕ+} (ha : a ∈ S) : ∃ r : B, aeval r (cyclotomic a A) = 0)
(adjoin_roots : ∀ (x : B), x ∈ adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 })

namespace is_cyclotomic_extension

section basic

/-- A reformulation of `is_cyclotomic_extension` that uses `⊤`. -/
lemma iff_adjoin_eq_top : is_cyclotomic_extension S A B ↔
 (∀ (a : ℕ+), a ∈ S → ∃ r : B, aeval r (cyclotomic a A) = 0) ∧
 (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 } = ⊤) :=
⟨λ h, ⟨h.exists_root, algebra.eq_top_iff.2 h.adjoin_roots⟩, λ h, ⟨h.1, algebra.eq_top_iff.1 h.2⟩⟩

/-- A reformulation of `is_cyclotomic_extension` in the case `S` is a singleton. -/
lemma iff_singleton : is_cyclotomic_extension {n} A B ↔
 (∃ r : B, aeval r (cyclotomic n A) = 0) ∧
 (∀ x, x ∈ adjoin A { b : B | b ^ (n : ℕ) = 1 }) :=
by simp [is_cyclotomic_extension_iff]

/-- If `is_cyclotomic_extension ∅ A B`, then `A = B`. -/
lemma empty [h : is_cyclotomic_extension ∅ A B] : (⊥ : subalgebra A B) = ⊤ :=
by simpa [algebra.eq_top_iff, is_cyclotomic_extension_iff] using h

/-- Transitivity of cyclotomic extensions. -/
lemma trans (C : Type w) [comm_ring C] [algebra A C] [algebra B C]
  [is_scalar_tower A B C] [hS : is_cyclotomic_extension S A B]
  [hT : is_cyclotomic_extension T B C] : is_cyclotomic_extension (S ∪ T) A C :=
begin
  refine ⟨λ n hn, _, λ x, _⟩,
  { cases hn,
    { obtain ⟨b, hb⟩ := ((is_cyclotomic_extension_iff _ _ _).1 hS).1 hn,
      refine ⟨algebra_map B C b, _⟩,
      replace hb := congr_arg (algebra_map B C) hb,
      rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ring_hom.map_zero, ← eval₂_at_apply,
        eval₂_eq_eval_map, map_cyclotomic] at hb,
      rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] },
    { obtain ⟨c, hc⟩ := ((is_cyclotomic_extension_iff _ _ _).1 hT).1 hn,
      refine ⟨c, _⟩,
      rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic] at hc,
      rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] } },
  { refine adjoin_induction (((is_cyclotomic_extension_iff _ _ _).1 hT).2 x) (λ c ⟨n, hn⟩,
      subset_adjoin ⟨n, or.inr hn.1, hn.2⟩) (λ b, _) (λ x y hx hy, subalgebra.add_mem _ hx hy)
      (λ x y hx hy, subalgebra.mul_mem _ hx hy),
    { let f := is_scalar_tower.to_alg_hom A B C,
      have hb : f b ∈ (adjoin A { b : B | ∃ (a : ℕ+), a ∈ S ∧ b ^ (a : ℕ) = 1 }).map f :=
        ⟨b, ((is_cyclotomic_extension_iff _ _ _).1 hS).2 b, rfl⟩,
      rw [is_scalar_tower.to_alg_hom_apply, ← adjoin_image] at hb,
      refine adjoin_mono (λ y hy, _) hb,
      obtain ⟨b₁, ⟨⟨n, hn⟩, h₁⟩⟩ := hy,
      exact ⟨n, ⟨mem_union_left T hn.1, by rw [← h₁, ← alg_hom.map_pow, hn.2, alg_hom.map_one]⟩⟩ } }
end

/-- If `B` is a cyclotomic extension of `A` given by roots of unity of order in `S ∪ T`, then `B`
is a cyclotomic extension of `adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 } ` given by
roots of unity of order in `T`. -/
lemma union_right [h : is_cyclotomic_extension (S ∪ T) A B] :
  is_cyclotomic_extension T (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) B :=
begin
  have : { b : B | ∃ (n : ℕ+), n ∈ S ∪ T ∧ b ^ (n : ℕ) = 1 } =
    { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 } ∪
    { b : B | ∃ (n : ℕ+), n ∈ T ∧ b ^ (n : ℕ) = 1 },
  { refine le_antisymm (λ x hx, _) (λ x hx, _),
    { rcases hx with ⟨n, hn₁ | hn₂, hnpow⟩,
      { left, exact ⟨n, hn₁, hnpow⟩ },
      { right, exact ⟨n, hn₂, hnpow⟩ } },
    { rcases hx with ⟨n, hn⟩ | ⟨n, hn⟩,
      { exact ⟨n, or.inl hn.1, hn.2⟩ },
      { exact ⟨n, or.inr hn.1, hn.2⟩ } } },

  refine ⟨λ n hn, _, λ b, _⟩,
  { obtain ⟨b, hb⟩ := ((is_cyclotomic_extension_iff _ _ _).1 h).1 (mem_union_right S hn),
    refine ⟨b, _⟩,
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic] at hb,
    rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] },
  { replace h := ((is_cyclotomic_extension_iff _ _ _).1 h).2 b,
    rwa [this, adjoin_union_eq_adjoin_adjoin,
      subalgebra.mem_restrict_scalars] at h }
end

/-- If `B` is a cyclotomic extension of `A` given by roots of unity of order in `T` and `S ⊆ T`,
then `adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }` is a cyclotomic extension of `B`
given by roots of unity of order in `S`. -/
lemma union_left [h : is_cyclotomic_extension T A B] (hS : S ⊆ T) :
  is_cyclotomic_extension S A (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) :=
begin
  refine ⟨λ n hn, _, λ b, _⟩,
  { obtain ⟨b, hb⟩ := ((is_cyclotomic_extension_iff _ _ _).1 h).1 (hS hn),
    refine ⟨⟨b, subset_adjoin ⟨n, hn, _⟩⟩, _⟩,
    { rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← is_root.def] at hb,
      suffices : (X ^ (n : ℕ) - 1).is_root b,
      { simpa [sub_eq_zero] using this },
      exact hb.dvd (cyclotomic.dvd_X_pow_sub_one _ _) },
      rwa [← subalgebra.coe_eq_zero, aeval_subalgebra_coe, subtype.coe_mk] },
  { convert mem_top,
    rw ← adjoin_adjoin_coe_preimage,
    simp,
    norm_cast, }
end

end basic

section fintype

lemma finite_of_singleton [is_domain B] [h : is_cyclotomic_extension {n} A B] : finite A B :=
begin
  classical,
  rw [module.finite_def, ← top_to_submodule, ← ((iff_adjoin_eq_top _ _ _).1 h).2],
  refine fg_adjoin_of_finite _ (λ b hb, _),
  { simp only [mem_singleton_iff, exists_eq_left],
    have : {b : B | b ^ (n : ℕ) = 1} = (nth_roots n (1 : B)).to_finset :=
      set.ext (λ x, ⟨λ h, by simpa using h, λ h, by simpa using h⟩),
    rw [this],
    exact (nth_roots ↑n 1).to_finset.finite_to_set },
  { simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq] at hb,
    refine ⟨X ^ (n : ℕ) - 1, ⟨monic_X_pow_sub_C _ n.pos.ne.symm, by simp [hb]⟩⟩ }
end

/-- If `S` is finite and `is_cyclotomic_extension S A B`, then `B` is a finite `A`-algebra. -/
lemma finite [is_domain B] [h₁ : fintype S] [h₂ : is_cyclotomic_extension S A B] : finite A B :=
begin
  unfreezingI {revert h₂ A B},
  refine set.finite.induction_on (set.finite.intro h₁) (λ A B, _) (λ n S hn hS H A B, _),
  { introsI _ _ _ _ _,
    refine module.finite_def.2 ⟨({1} : finset B), _⟩,
    simp [← top_to_submodule, ← empty, to_submodule_bot] },
  { introsI _ _ _ _ h,
    haveI : is_cyclotomic_extension S A (adjoin A { b : B | ∃ (n : ℕ+),
      n ∈ S ∧ b ^ (n : ℕ) = 1 }) := union_left _ (insert n S) _ _ (subset_insert n S),
    haveI := H A (adjoin A { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 }),
    haveI : finite (adjoin A { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 }) B,
    { rw [← union_singleton] at h,
      letI := @union_right S {n} A B _ _ _ h,
      exact finite_of_singleton n _ _ },
    exact finite.trans (adjoin A { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 }) _ }
end

/-- A cyclotomic finite extension of a number field is a number field. -/
lemma number_field [h : number_field K] [fintype S] [is_cyclotomic_extension S K L] :
  number_field L :=
{ to_char_zero := char_zero_of_injective_algebra_map (algebra_map K L).injective,
  to_finite_dimensional := @finite.trans _ K L _ _ _ _
    (@algebra_rat L _ (char_zero_of_injective_algebra_map (algebra_map K L).injective)) _ _
    h.to_finite_dimensional (finite S K L) }

end fintype

end is_cyclotomic_extension
