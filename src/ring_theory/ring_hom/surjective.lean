/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import ring_theory.local_properties

/-!

# The meta properties of surjective ring homomorphisms.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

namespace ring_hom

open_locale tensor_product

open tensor_product algebra.tensor_product

local notation `surjective` := λ {X Y : Type*} [comm_ring X] [comm_ring Y] ,
  by exactI λ (f : X →+* Y), function.surjective f

lemma surjective_stable_under_composition :
  stable_under_composition surjective :=
by { introv R hf hg, exactI hg.comp hf }

lemma surjective_respects_iso :
  respects_iso surjective :=
begin
  apply surjective_stable_under_composition.respects_iso,
  introsI,
  exact e.surjective
end

lemma surjective_stable_under_base_change :
  stable_under_base_change surjective :=
begin
  refine stable_under_base_change.mk _ surjective_respects_iso _,
  classical,
  introv h x,
  resetI,
  induction x using tensor_product.induction_on with x y x y ex ey,
  { exact ⟨0, map_zero _⟩ },
  { obtain ⟨y, rfl⟩ := h y, use y • x, dsimp,
    rw [tensor_product.smul_tmul, algebra.algebra_map_eq_smul_one] },
  { obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := ⟨ex, ey⟩, exact ⟨x + y, map_add _ x y⟩ }
end

open_locale big_operators

lemma surjective_of_localization_span :
  of_localization_span surjective :=
begin
  introv R hs H,
  resetI,
  letI := f.to_algebra,
  show function.surjective (algebra.of_id R S),
  rw [← algebra.range_top_iff_surjective, eq_top_iff],
  rintro x -,
  obtain ⟨l, hl⟩ :=
    (finsupp.mem_span_iff_total R s 1).mp (show _ ∈ ideal.span s, by { rw hs, trivial }),
  fapply subalgebra.mem_of_finset_sum_eq_one_of_pow_smul_mem _
    l.support (λ x : s, f x) (λ x : s, f (l x)),
  { dsimp only, simp_rw [← _root_.map_mul, ← map_sum, ← f.map_one], exact f.congr_arg hl },
  { exact λ _, set.mem_range_self _ },
  { exact λ _, set.mem_range_self _ },
  { intro r,
    obtain ⟨y, hy⟩ := H r (is_localization.mk' _ x (1 : submonoid.powers (f r))),
    obtain ⟨z, ⟨_, n, rfl⟩, rfl⟩ := is_localization.mk'_surjective (submonoid.powers (r : R)) y,
    erw [is_localization.map_mk', is_localization.eq] at hy,
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := hy,
    refine ⟨m + n, _⟩,
    dsimp at hm ⊢,
    simp_rw [_root_.one_mul, ← _root_.mul_assoc, ← map_pow, ← f.map_mul, ← pow_add, map_pow] at hm,
    exact ⟨_, hm⟩ }
end

end ring_hom
