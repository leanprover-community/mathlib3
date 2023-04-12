/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.function
import analysis.convex.mathlib
import data.set.intervals.proj_Icc

/-!
# Convexity of extension from intervals

This file proves that constantly extending monotone/antitone functions preserves their convexity.

## TODO

We could deduplicate the proofs if we had a typeclass stating that `segment 𝕜 x y = [x -[𝕜] y]` as
`𝕜ᵒᵈ` respects it if `𝕜`, while `𝕜ᵒᵈ` isn't a `linear_ordered_field` if `𝕜` is.
-/

open set

variables {𝕜 β : Type*} [linear_ordered_field 𝕜] [linear_ordered_add_comm_monoid β] [has_smul 𝕜 β]
  {s : set 𝕜} {f : 𝕜 → β} {z : 𝕜}

/-- A convex set extended towards minus infinity is convex. -/
protected lemma convex.Ici_extend (hf : convex 𝕜 s) :
  convex 𝕜 {x | Ici_extend (restrict (Ici z) (∈ s)) x} :=
by { rw convex_iff_ord_connected at ⊢ hf, exact hf.restrict.Ici_extend }

/-- A convex set extended towards infinity is convex. -/
protected lemma convex.Iic_extend (hf : convex 𝕜 s) :
  convex 𝕜 {x | Iic_extend (restrict (Iic z) (∈ s)) x} :=
by { rw convex_iff_ord_connected at ⊢ hf, exact hf.restrict.Iic_extend }

/-- A convex monotone function extended constantly towards minus infinity is convex. -/
protected lemma convex_on.Ici_extend (hf : convex_on 𝕜 s f) (hf' : monotone_on f s) :
  convex_on 𝕜 {x | Ici_extend (restrict (Ici z) (∈ s)) x} (Ici_extend $ restrict (Ici z) f) :=
begin
  refine ⟨hf.1.Ici_extend, λ x hx y hy a b ha hb hab, _⟩,
  dsimp [Ici_extend_apply] at ⊢ hx hy,
  refine (hf' (hf.1.ord_connected.uIcc_subset hx hy $ monotone.image_uIcc_subset (λ _ _, max_le_max
    le_rfl) $ mem_image_of_mem _ $ convex_uIcc _ _ left_mem_uIcc right_mem_uIcc ha hb hab)
    (hf.1 hx hy ha hb hab) _).trans (hf.2 hx hy ha hb hab),
  rw [smul_max ha z, smul_max hb z],
  refine le_trans _ max_add_add_le_max_add_max,
  rw [convex.combo_self hab, smul_eq_mul, smul_eq_mul],
end

/-- A convex antitone function extended constantly towards infinity is convex. -/
protected lemma convex_on.Iic_extend (hf : convex_on 𝕜 s f) (hf' : antitone_on f s) :
  convex_on 𝕜 {x | Iic_extend (restrict (Iic z) (∈ s)) x} (Iic_extend $ restrict (Iic z) f) :=
begin
  refine ⟨hf.1.Iic_extend, λ x hx y hy a b ha hb hab, _⟩,
  dsimp [Iic_extend_apply] at ⊢ hx hy,
  refine (hf' (hf.1 hx hy ha hb hab) (hf.1.ord_connected.uIcc_subset hx hy $
    monotone.image_uIcc_subset (λ _ _, min_le_min le_rfl) $ mem_image_of_mem _ $ convex_uIcc _ _ left_mem_uIcc right_mem_uIcc ha hb hab) _).trans (hf.2 hx hy ha hb hab),
  rw [smul_min ha z, smul_min hb z],
  refine min_add_min_le_min_add_add.trans _ ,
  rw [convex.combo_self hab, smul_eq_mul, smul_eq_mul],
end

/-- A concave antitone function extended constantly minus towards infinity is concave. -/
protected lemma concave_on.Ici_extend (hf : concave_on 𝕜 s f) (hf' : antitone_on f s) :
  concave_on 𝕜 {x | Ici_extend (restrict (Ici z) (∈ s)) x} (Ici_extend $ restrict (Ici z) f) :=
hf.dual.Ici_extend hf'.dual_right

/-- A concave monotone function extended constantly towards infinity is concave. -/
protected lemma concave_on.Iic_extend (hf : concave_on 𝕜 s f) (hf' : monotone_on f s) :
  concave_on 𝕜 {x | Iic_extend (restrict (Iic z) (∈ s)) x} (Iic_extend $ restrict (Iic z) f) :=
hf.dual.Iic_extend hf'.dual_right

/-- A convex monotone function extended constantly towards minus infinity is convex. -/
protected lemma convex_on.Ici_extend_of_monotone (hf : convex_on 𝕜 univ f) (hf' : monotone f) :
  convex_on 𝕜 univ (Ici_extend $ restrict (Ici z) f) :=
hf.Ici_extend $ hf'.monotone_on _

/-- A convex antitone function extended constantly towards infinity is convex. -/
protected lemma convex_on.Iic_extend_of_antitone (hf : convex_on 𝕜 univ f) (hf' : antitone f) :
  convex_on 𝕜 univ (Iic_extend $ restrict (Iic z) f) :=
hf.Iic_extend $ hf'.antitone_on _

/-- A concave antitone function extended constantly minus towards infinity is concave. -/
protected lemma concave_on.Ici_extend_of_antitone (hf : concave_on 𝕜 univ f) (hf' : antitone f) :
  concave_on 𝕜 univ (Ici_extend $ restrict (Ici z) f) :=
hf.Ici_extend $ hf'.antitone_on _

/-- A concave monotone function extended constantly towards infinity is concave. -/
protected lemma concave_on.Iic_extend_of_monotone (hf : concave_on 𝕜 univ f) (hf' : monotone f) :
  concave_on 𝕜 univ (Iic_extend $ restrict (Iic z) f) :=
hf.Iic_extend $ hf'.monotone_on _
