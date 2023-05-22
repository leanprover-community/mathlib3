/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import topology.category.CompHaus.basic
import topology.stone_cech
import category_theory.preadditive.projective

/-!
# CompHaus has enough projectives

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we show that `CompHaus` has enough projectives.

## Main results

Let `X` be a compact Hausdorff space.

* `CompHaus.projective_ultrafilter`: the space `ultrafilter X` is a projective object
* `CompHaus.projective_presentation`: the natural map `ultrafilter X → X`
  is a projective presentation

## Reference

See [miraglia2006introduction] Chapter 21 for a proof that `CompHaus` has enough projectives.

-/

noncomputable theory

open category_theory function

namespace CompHaus

instance projective_ultrafilter (X : Type*) :
  projective (of $ ultrafilter X) :=
{ factors := λ Y Z f g hg,
  begin
    rw epi_iff_surjective at hg,
    obtain ⟨g', hg'⟩ := hg.has_right_inverse,
    let t : X → Y := g' ∘ f ∘ (pure : X → ultrafilter X),
    let h : ultrafilter X → Y := ultrafilter.extend t,
    have hh : continuous h := continuous_ultrafilter_extend _,
    use ⟨h, hh⟩,
    apply faithful.map_injective (forget CompHaus),
    simp only [forget_map_eq_coe, continuous_map.coe_mk, coe_comp],
    convert dense_range_pure.equalizer (g.continuous.comp hh) f.continuous _,
    rw [comp.assoc, ultrafilter_extend_extends, ← comp.assoc, hg'.comp_eq_id, comp.left_id],
  end }

/-- For any compact Hausdorff space `X`,
  the natural map `ultrafilter X → X` is a projective presentation. -/
def projective_presentation (X : CompHaus) : projective_presentation X :=
{ P := of $ ultrafilter X,
  f := ⟨_, continuous_ultrafilter_extend id⟩,
  projective := CompHaus.projective_ultrafilter X,
  epi := concrete_category.epi_of_surjective _ $
    λ x, ⟨(pure x : ultrafilter X), congr_fun (ultrafilter_extend_extends (𝟙 X)) x⟩ }

instance : enough_projectives CompHaus :=
{ presentation := λ X, ⟨projective_presentation X⟩ }

end CompHaus
