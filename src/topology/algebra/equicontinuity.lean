/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.algebra.uniform_convergence

/-!
# Algebra-related equicontinuity criterions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open function
open_locale uniform_convergence

@[to_additive] lemma equicontinuous_of_equicontinuous_at_one {ι G M hom : Type*}
  [topological_space G] [uniform_space M] [group G] [group M] [topological_group G]
  [uniform_group M] [monoid_hom_class hom G M] (F : ι → hom)
  (hf : equicontinuous_at (coe_fn ∘ F) (1 : G)) :
  equicontinuous (coe_fn ∘ F) :=
begin
  letI : has_coe_to_fun hom (λ _, G → M) := fun_like.has_coe_to_fun,
  rw equicontinuous_iff_continuous,
  rw equicontinuous_at_iff_continuous_at at hf,
  let φ : G →* (ι → M) :=
  { to_fun := swap (coe_fn ∘ F),
    map_one' := by ext; exact map_one _,
    map_mul' := λ a b, by ext; exact map_mul _ _ _ },
  exact continuous_of_continuous_at_one φ hf
end

@[to_additive] lemma uniform_equicontinuous_of_equicontinuous_at_one {ι G M hom : Type*}
  [uniform_space G] [uniform_space M] [group G] [group M] [uniform_group G] [uniform_group M]
  [monoid_hom_class hom G M] (F : ι → hom) (hf : equicontinuous_at (coe_fn ∘ F) (1 : G)) :
  uniform_equicontinuous (coe_fn ∘ F) :=
begin
  letI : has_coe_to_fun hom (λ _, G → M) := fun_like.has_coe_to_fun,
  rw uniform_equicontinuous_iff_uniform_continuous,
  rw equicontinuous_at_iff_continuous_at at hf,
  let φ : G →* (ι → M) :=
  { to_fun := swap (coe_fn ∘ F),
    map_one' := by ext; exact map_one _,
    map_mul' := λ a b, by ext; exact map_mul _ _ _ },
  exact uniform_continuous_of_continuous_at_one φ hf
end
