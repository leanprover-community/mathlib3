/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.char_p.algebra
import field_theory.intermediate_field
import ring_theory.adjoin.field

/-!
# Splitting fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file introduces the notion of a splitting field of a polynomial and provides an embedding from
a splitting field to any field that splits the polynomial. A polynomial `f : K[X]` splits
over a field extension `L` of `K` if it is zero or all of its irreducible factors over `L` have
degree `1`. A field extension of `K` of a polynomial `f : K[X]` is called a splitting field
if it is the smallest field extension of `K` such that `f` splits.

## Main definitions

* `polynomial.is_splitting_field`: A predicate on a field to be a splitting field of a polynomial
  `f`.

## Main statements

* `polynomial.is_splitting_field.lift`: An embedding of a splitting field of the polynomial `f` into
  another field such that `f` splits.

-/

noncomputable theory
open_locale classical big_operators polynomial

universes u v w

variables {F : Type u} (K : Type v) (L : Type w)

namespace polynomial

variables [field K] [field L] [field F] [algebra K L]

/-- Typeclass characterising splitting fields. -/
class is_splitting_field (f : K[X]) : Prop :=
(splits [] : splits (algebra_map K L) f)
(adjoin_root_set [] : algebra.adjoin K (f.root_set L) = ⊤)

variables {K L F}

namespace is_splitting_field

section scalar_tower

variables [algebra F K] [algebra F L] [is_scalar_tower F K L]

instance map (f : F[X]) [is_splitting_field F L f] :
  is_splitting_field K L (f.map $ algebra_map F K) :=
⟨by { rw [splits_map_iff, ← is_scalar_tower.algebra_map_eq], exact splits L f },
 subalgebra.restrict_scalars_injective F $
  by { rw [root_set, map_map, ← is_scalar_tower.algebra_map_eq, subalgebra.restrict_scalars_top,
    eq_top_iff, ← adjoin_root_set L f, algebra.adjoin_le_iff],
  exact λ x hx, @algebra.subset_adjoin K _ _ _ _ _ _ hx }⟩

variables (L)
theorem splits_iff (f : K[X]) [is_splitting_field K L f] :
  polynomial.splits (ring_hom.id K) f ↔ (⊤ : subalgebra K L) = ⊥ :=
⟨λ h, eq_bot_iff.2 $ adjoin_root_set L f ▸
  algebra.adjoin_le_iff.2 (λ y hy,
    let ⟨x, hxs, hxy⟩ := finset.mem_image.1
      (by rwa [root_set, roots_map _ h, multiset.to_finset_map] at hy) in
    hxy ▸ set_like.mem_coe.2 $ subalgebra.algebra_map_mem _ _),
 λ h, @ring_equiv.to_ring_hom_refl K _ ▸
  ring_equiv.self_trans_symm (ring_equiv.of_bijective _ $ algebra.bijective_algebra_map_iff.2 h) ▸
  by { rw ring_equiv.to_ring_hom_trans, exact splits_comp_of_splits _ _ (splits L f) }⟩

theorem mul (f g : F[X]) (hf : f ≠ 0) (hg : g ≠ 0) [is_splitting_field F K f]
  [is_splitting_field K L (g.map $ algebra_map F K)] :
  is_splitting_field F L (f * g) :=
⟨(is_scalar_tower.algebra_map_eq F K L).symm ▸ splits_mul _
  (splits_comp_of_splits _ _ (splits K f))
  ((splits_map_iff _ _).1 (splits L $ g.map $ algebra_map F K)),
 by rw [root_set, polynomial.map_mul,
      roots_mul (mul_ne_zero (map_ne_zero hf : f.map (algebra_map F L) ≠ 0)
        (map_ne_zero hg)), multiset.to_finset_add, finset.coe_union,
      algebra.adjoin_union_eq_adjoin_adjoin,
      is_scalar_tower.algebra_map_eq F K L, ← map_map,
      roots_map (algebra_map K L) ((splits_id_iff_splits $ algebra_map F K).2 $ splits K f),
      multiset.to_finset_map, finset.coe_image, algebra.adjoin_algebra_map, ←root_set,
      adjoin_root_set, algebra.map_top, is_scalar_tower.adjoin_range_to_alg_hom, ← map_map,
      ←root_set, adjoin_root_set, subalgebra.restrict_scalars_top]⟩

end scalar_tower

variable (L)

/-- Splitting field of `f` embeds into any field that splits `f`. -/
def lift [algebra K F] (f : K[X]) [is_splitting_field K L f]
  (hf : polynomial.splits (algebra_map K F) f) : L →ₐ[K] F :=
if hf0 : f = 0 then (algebra.of_id K F).comp $
  (algebra.bot_equiv K L : (⊥ : subalgebra K L) →ₐ[K] K).comp $
  by { rw ← (splits_iff L f).1 (show f.splits (ring_hom.id K), from hf0.symm ▸ splits_zero _),
  exact algebra.to_top } else
alg_hom.comp (by { rw ← adjoin_root_set L f, exact classical.choice (lift_of_splits _ $ λ y hy,
    have aeval y f = 0, from (eval₂_eq_eval_map _).trans $
      (mem_roots $ by exact map_ne_zero hf0).1 (multiset.mem_to_finset.mp hy),
    ⟨is_algebraic_iff_is_integral.1 ⟨f, hf0, this⟩,
      splits_of_splits_of_dvd _ hf0 hf $ minpoly.dvd _ _ this⟩) })
  algebra.to_top

theorem finite_dimensional (f : K[X]) [is_splitting_field K L f] : finite_dimensional K L :=
⟨@algebra.top_to_submodule K L _ _ _ ▸ adjoin_root_set L f ▸
  fg_adjoin_of_finite (finset.finite_to_set _) (λ y hy,
  if hf : f = 0
  then by { rw [hf, root_set_zero] at hy, cases hy }
  else is_algebraic_iff_is_integral.1 ⟨f, hf, (eval₂_eq_eval_map _).trans $
    (mem_roots $ by exact map_ne_zero hf).1 (multiset.mem_to_finset.mp hy)⟩)⟩

lemma of_alg_equiv [algebra K F] (p : K[X]) (f : F ≃ₐ[K] L) [is_splitting_field K F p] :
  is_splitting_field K L p :=
begin
  split,
  { rw ← f.to_alg_hom.comp_algebra_map,
    exact splits_comp_of_splits _ _ (splits F p) },
  { rw [←(algebra.range_top_iff_surjective f.to_alg_hom).mpr f.surjective,
        adjoin_root_set_eq_range (splits F p), adjoin_root_set F p] },
end

end is_splitting_field

end polynomial

namespace intermediate_field

open polynomial

variables {K L} [field K] [field L] [algebra K L] {p : K[X]}

lemma splits_of_splits {F : intermediate_field K L} (h : p.splits (algebra_map K L))
  (hF : ∀ x ∈ p.root_set L, x ∈ F) : p.splits (algebra_map K F) :=
begin
  simp_rw [root_set, finset.mem_coe, multiset.mem_to_finset] at hF,
  rw splits_iff_exists_multiset,
  refine ⟨multiset.pmap subtype.mk _ hF, map_injective _ (algebra_map F L).injective _⟩,
  conv_lhs { rw [polynomial.map_map, ←is_scalar_tower.algebra_map_eq,
    eq_prod_roots_of_splits h, ←multiset.pmap_eq_map _ _ _ hF] },
  simp_rw [polynomial.map_mul, polynomial.map_multiset_prod,
    multiset.map_pmap, polynomial.map_sub, map_C, map_X],
  refl,
end

end intermediate_field
