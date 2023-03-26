/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ring_theory.adjoin.fg

/-!
# Adjoining elements and being finitely generated in an algebra tower

## Main results

 * `algebra.fg_trans'`: if `S` is finitely generated as `R`-algebra and `A` as `S`-algebra,
   then `A` is finitely generated as `R`-algebra
 * `fg_of_fg_of_fg`: **Artin--Tate lemma**: if C/B/A is a tower of rings, and A is noetherian, and
   C is algebra-finite over A, and C is module-finite over B, then B is algebra-finite over A.
-/

open_locale pointwise
universes u v w u₁

variables (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

namespace algebra

theorem adjoin_algebra_map (R : Type u) (S : Type v) (A : Type w)
  [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A]
  [is_scalar_tower R S A] (s : set S) :
  adjoin R (algebra_map S A '' s) = (adjoin R s).map (is_scalar_tower.to_alg_hom R S A) :=
le_antisymm (adjoin_le $ set.image_subset_iff.2 $ λ y hy, ⟨y, subset_adjoin hy, rfl⟩)
  (subalgebra.map_le.2 $ adjoin_le $ λ y hy, subset_adjoin ⟨y, hy, rfl⟩)

lemma adjoin_restrict_scalars (C D E : Type*) [comm_semiring C] [comm_semiring D] [comm_semiring E]
  [algebra C D] [algebra C E] [algebra D E] [is_scalar_tower C D E] (S : set E) :
(algebra.adjoin D S).restrict_scalars C =
  (algebra.adjoin
    ((⊤ : subalgebra C D).map (is_scalar_tower.to_alg_hom C D E)) S).restrict_scalars C :=
begin
  suffices : set.range (algebra_map D E) =
    set.range (algebra_map ((⊤ : subalgebra C D).map (is_scalar_tower.to_alg_hom C D E)) E),
  { ext x, change x ∈ subsemiring.closure (_ ∪ S) ↔ x ∈ subsemiring.closure (_ ∪ S), rw this },
  ext x,
  split,
  { rintros ⟨y, hy⟩,
    exact ⟨⟨algebra_map D E y, ⟨y, ⟨algebra.mem_top, rfl⟩⟩⟩, hy⟩ },
  { rintros ⟨⟨y, ⟨z, ⟨h0, h1⟩⟩⟩, h2⟩,
    exact ⟨z, eq.trans h1 h2⟩ },
end

lemma adjoin_res_eq_adjoin_res (C D E F : Type*) [comm_semiring C] [comm_semiring D]
  [comm_semiring E] [comm_semiring F] [algebra C D] [algebra C E] [algebra C F] [algebra D F]
  [algebra E F] [is_scalar_tower C D F] [is_scalar_tower C E F] {S : set D} {T : set E}
  (hS : algebra.adjoin C S = ⊤) (hT : algebra.adjoin C T = ⊤) :
(algebra.adjoin E (algebra_map D F '' S)).restrict_scalars C =
  (algebra.adjoin D (algebra_map E F '' T)).restrict_scalars C :=
by rw [adjoin_restrict_scalars C E, adjoin_restrict_scalars C D, ←hS, ←hT, ←algebra.adjoin_image,
  ←algebra.adjoin_image, ←alg_hom.coe_to_ring_hom, ←alg_hom.coe_to_ring_hom,
  is_scalar_tower.coe_to_alg_hom, is_scalar_tower.coe_to_alg_hom, ←adjoin_union_eq_adjoin_adjoin,
  ←adjoin_union_eq_adjoin_adjoin, set.union_comm]

end algebra

section
open_locale classical
lemma algebra.fg_trans' {R S A : Type*} [comm_semiring R] [comm_semiring S] [comm_semiring A]
  [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A]
  (hRS : (⊤ : subalgebra R S).fg) (hSA : (⊤ : subalgebra S A).fg) :
  (⊤ : subalgebra R A).fg :=
let ⟨s, hs⟩ := hRS, ⟨t, ht⟩ := hSA in ⟨s.image (algebra_map S A) ∪ t,
by rw [finset.coe_union, finset.coe_image, algebra.adjoin_union_eq_adjoin_adjoin,
  algebra.adjoin_algebra_map, hs, algebra.map_top, is_scalar_tower.adjoin_range_to_alg_hom, ht,
  subalgebra.restrict_scalars_top]⟩
end

section artin_tate

variables (C : Type*)

section semiring

variables [comm_semiring A] [comm_semiring B] [semiring C]
variables [algebra A B] [algebra B C] [algebra A C] [is_scalar_tower A B C]

open finset submodule
open_locale classical

lemma exists_subalgebra_of_fg (hAC : (⊤ : subalgebra A C).fg) (hBC : (⊤ : submodule B C).fg) :
  ∃ B₀ : subalgebra A B, B₀.fg ∧ (⊤ : submodule B₀ C).fg :=
begin
  cases hAC with x hx,
  cases hBC with y hy, have := hy,
  simp_rw [eq_top_iff', mem_span_finset] at this, choose f hf,
  let s : finset B := finset.image₂ f (x ∪ (y * y)) y,
  have hxy : ∀ xi ∈ x, xi ∈ span (algebra.adjoin A (↑s : set B))
               (↑(insert 1 y : finset C) : set C) :=
    λ xi hxi, hf xi ▸ sum_mem (λ yj hyj, smul_mem
      (span (algebra.adjoin A (↑s : set B)) (↑(insert 1 y : finset C) : set C))
      ⟨f xi yj, algebra.subset_adjoin $ mem_image₂_of_mem (mem_union_left _ hxi) hyj⟩
      (subset_span $ mem_insert_of_mem hyj)),
  have hyy : span (algebra.adjoin A (↑s : set B)) (↑(insert 1 y : finset C) : set C) *
      span (algebra.adjoin A (↑s : set B)) (↑(insert 1 y : finset C) : set C) ≤
    span (algebra.adjoin A (↑s : set B)) (↑(insert 1 y : finset C) : set C),
  { rw [span_mul_span, span_le, coe_insert], rintros _ ⟨yi, yj, rfl | hyi, rfl | hyj, rfl⟩,
    { rw mul_one, exact subset_span (set.mem_insert _ _) },
    { rw one_mul, exact subset_span (set.mem_insert_of_mem _ hyj) },
    { rw mul_one, exact subset_span (set.mem_insert_of_mem _ hyi) },
    { rw ← hf (yi * yj), exact set_like.mem_coe.2 (sum_mem $ λ yk hyk, smul_mem
        (span (algebra.adjoin A (↑s : set B)) (insert 1 ↑y : set C))
        ⟨f (yi * yj) yk, algebra.subset_adjoin $ mem_image₂_of_mem (mem_union_right _ $
          mul_mem_mul hyi hyj) hyk⟩
        (subset_span $ set.mem_insert_of_mem _ hyk : yk ∈ _)) } },
  refine ⟨algebra.adjoin A (↑s : set B), subalgebra.fg_adjoin_finset _, insert 1 y, _⟩,
  refine restrict_scalars_injective A _ _ _,
  rw [restrict_scalars_top, eq_top_iff, ← algebra.top_to_submodule, ← hx,
    algebra.adjoin_eq_span, span_le],
  refine λ r hr, submonoid.closure_induction hr (λ c hc, hxy c hc)
    (subset_span $ mem_insert_self _ _) (λ p q hp hq, hyy $ submodule.mul_mem_mul hp hq)
end

end semiring

section ring

variables [comm_ring A] [comm_ring B] [comm_ring C]
variables [algebra A B] [algebra B C] [algebra A C] [is_scalar_tower A B C]

/-- **Artin--Tate lemma**: if A ⊆ B ⊆ C is a chain of subrings of commutative rings, and
A is noetherian, and C is algebra-finite over A, and C is module-finite over B,
then B is algebra-finite over A.

References: Atiyah--Macdonald Proposition 7.8; Stacks 00IS; Altman--Kleiman 16.17. -/
theorem fg_of_fg_of_fg [is_noetherian_ring A]
  (hAC : (⊤ : subalgebra A C).fg) (hBC : (⊤ : submodule B C).fg)
  (hBCi : function.injective (algebra_map B C)) :
  (⊤ : subalgebra A B).fg :=
let ⟨B₀, hAB₀, hB₀C⟩ := exists_subalgebra_of_fg A B C hAC hBC in
algebra.fg_trans' (B₀.fg_top.2 hAB₀) $ subalgebra.fg_of_submodule_fg $
have is_noetherian_ring B₀, from is_noetherian_ring_of_fg hAB₀,
have is_noetherian B₀ C, by exactI is_noetherian_of_fg_of_noetherian' hB₀C,
by exactI fg_of_injective (is_scalar_tower.to_alg_hom B₀ B C).to_linear_map hBCi

end ring

end artin_tate
