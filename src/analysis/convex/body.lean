/-
Copyright (c) 2022 Paul A. Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul A. Reichert
-/
import analysis.convex.basic
import analysis.normed_space.basic
import topology.metric_space.hausdorff_distance

/-!
# Convex bodies

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition of the type `convex_body V`
consisting of
convex, compact, nonempty subsets of a real topological vector space `V`.

`convex_body V` is a module over the nonnegative reals (`nnreal`) and a pseudo-metric space.
If `V` is a normed space, `convex_body V` is a metric space.

## TODO

- define positive convex bodies, requiring the interior to be nonempty
- introduce support sets
- Characterise the interaction of the distance with algebraic operations, eg
  `dist (a • K) (a • L) = ‖a‖ * dist K L`, `dist (a +ᵥ K) (a +ᵥ L) = dist K L`

## Tags

convex, convex body
-/

open_locale pointwise
open_locale nnreal

variables {V : Type*}

/--
Let `V` be a real topological vector space. A subset of `V` is a convex body if and only if
it is convex, compact, and nonempty.
-/
structure convex_body (V : Type*) [topological_space V] [add_comm_monoid V] [has_smul ℝ V] :=
(carrier : set V)
(convex' : convex ℝ carrier)
(is_compact' : is_compact carrier)
(nonempty' : carrier.nonempty)

namespace convex_body
section TVS
variables [topological_space V] [add_comm_group V] [module ℝ V]

instance : set_like (convex_body V) V :=
{ coe := convex_body.carrier,
  coe_injective' := λ K L h, by { cases K, cases L, congr' } }

protected lemma convex (K : convex_body V) : convex ℝ (K : set V) := K.convex'
protected lemma is_compact (K : convex_body V) : is_compact (K : set V) := K.is_compact'
protected lemma nonempty (K : convex_body V) : (K : set V).nonempty := K.nonempty'

@[ext]
protected lemma ext {K L : convex_body V} (h : (K : set V) = L) : K = L := set_like.ext' h

@[simp]
lemma coe_mk (s : set V) (h₁ h₂ h₃) : (mk s h₁ h₂ h₃ : set V) = s := rfl

section has_continuous_add
variables [has_continuous_add V]

instance : add_monoid (convex_body V) :=
-- we cannot write K + L to avoid reducibility issues with the set.has_add instance
{ add := λ K L, ⟨set.image2 (+) K L,
                 K.convex.add L.convex,
                 K.is_compact.add L.is_compact,
                 K.nonempty.add L.nonempty⟩,
  add_assoc := λ K L M, by { ext, simp only [coe_mk, set.image2_add, add_assoc] },
  zero := ⟨0, convex_singleton 0, is_compact_singleton, set.singleton_nonempty 0⟩,
  zero_add := λ K, by { ext, simp only [coe_mk, set.image2_add, zero_add] },
  add_zero := λ K, by { ext, simp only [coe_mk, set.image2_add, add_zero] } }

@[simp]
lemma coe_add (K L : convex_body V) : (↑(K + L) : set V) = (K : set V) + L := rfl

@[simp]
lemma coe_zero : (↑(0 : convex_body V) : set V) = 0 := rfl

instance : inhabited (convex_body V) := ⟨0⟩

instance : add_comm_monoid (convex_body V) :=
{ add_comm := λ K L, by { ext, simp only [coe_add, add_comm] },
  .. convex_body.add_monoid }

end has_continuous_add

variables [has_continuous_smul ℝ V]

instance : has_smul ℝ (convex_body V) :=
{ smul := λ c K, ⟨c • (K : set V), K.convex.smul _, K.is_compact.smul _, K.nonempty.smul_set⟩ }

@[simp]
lemma coe_smul (c : ℝ) (K : convex_body V) : (↑(c • K) : set V) = c • (K : set V) := rfl

variables [has_continuous_add V]

instance : distrib_mul_action ℝ (convex_body V) :=
{ to_has_smul := convex_body.has_smul,
  one_smul := λ K, by { ext, simp only [coe_smul, one_smul] },
  mul_smul := λ c d K, by { ext, simp only [coe_smul, mul_smul] },
  smul_add := λ c K L, by { ext, simp only [coe_smul, coe_add, smul_add] },
  smul_zero := λ c, by { ext, simp only [coe_smul, coe_zero, smul_zero] } }

@[simp]
lemma coe_smul' (c : ℝ≥0) (K : convex_body V) : (↑(c • K) : set V) = c • (K : set V) := rfl

/--
The convex bodies in a fixed space $V$ form a module over the nonnegative reals.
-/
instance : module ℝ≥0 (convex_body V) :=
{ add_smul := λ c d K,
  begin
    ext1,
    simp only [coe_smul, coe_add],
    exact convex.add_smul K.convex (nnreal.coe_nonneg _) (nnreal.coe_nonneg _),
  end,
  zero_smul := λ K, by { ext1, exact set.zero_smul_set K.nonempty } }

end TVS

section seminormed_add_comm_group
variables [seminormed_add_comm_group V] [normed_space ℝ V] (K L : convex_body V)

protected lemma bounded : metric.bounded (K : set V) := K.is_compact.bounded

lemma Hausdorff_edist_ne_top {K L : convex_body V} : emetric.Hausdorff_edist (K : set V) L ≠ ⊤ :=
by apply_rules [metric.Hausdorff_edist_ne_top_of_nonempty_of_bounded, convex_body.nonempty,
  convex_body.bounded]

/-- Convex bodies in a fixed seminormed space $V$ form a pseudo-metric space under the Hausdorff
metric. -/
noncomputable instance : pseudo_metric_space (convex_body V) :=
{ dist := λ K L, metric.Hausdorff_dist (K : set V) L,
  dist_self := λ _, metric.Hausdorff_dist_self_zero,
  dist_comm := λ _ _, metric.Hausdorff_dist_comm,
  dist_triangle := λ K L M, metric.Hausdorff_dist_triangle Hausdorff_edist_ne_top }

@[simp, norm_cast]
lemma Hausdorff_dist_coe : metric.Hausdorff_dist (K : set V) L = dist K L := rfl

@[simp, norm_cast] lemma Hausdorff_edist_coe : emetric.Hausdorff_edist (K : set V) L = edist K L :=
by { rw edist_dist, exact (ennreal.of_real_to_real Hausdorff_edist_ne_top).symm }

end seminormed_add_comm_group

section normed_add_comm_group
variables [normed_add_comm_group V] [normed_space ℝ V]

/-- Convex bodies in a fixed normed space `V` form a metric space under the Hausdorff metric. -/
noncomputable instance : metric_space (convex_body V) :=
{ eq_of_dist_eq_zero := λ K L hd, convex_body.ext $
    (K.is_compact.is_closed.Hausdorff_dist_zero_iff_eq
      L.is_compact.is_closed Hausdorff_edist_ne_top).mp hd }

end normed_add_comm_group
end convex_body
