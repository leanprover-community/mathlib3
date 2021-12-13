/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import topology.category.Profinite
import topology.stone_cech
import category_theory.preadditive.projective

/-!
# Profinite sets have enough projectives

In this file we show that `Profinite` has enough projectives.

## Main results

Let `X` be a profinite set.

* `Profinite.projective_ultrafilter`: the space `ultrafilter X` is a projective object
* `Profinite.projective_presentation`: the natural map `ultrafilter X → X`
  is a projective presentation

-/

noncomputable theory

universe variables u v w
open category_theory function

namespace Profinite

instance projective_ultrafilter (X : Type u) :
  projective (of $ ultrafilter X) :=
{ factors := λ Y Z f g hg,
  begin
    rw epi_iff_surjective at hg,
    obtain ⟨g', hg'⟩ := hg.has_right_inverse,
    let t : X → Y := g' ∘ f ∘ (pure : X → ultrafilter X),
    let h : ultrafilter X → Y := ultrafilter.extend t,
    have hh : continuous h := continuous_ultrafilter_extend _,
    use ⟨h, hh⟩,
    apply faithful.map_injective (forget Profinite),
    simp only [forget_map_eq_coe, continuous_map.coe_mk, coe_comp],
    refine dense_range_pure.equalizer (g.continuous.comp hh) f.continuous _,
    rw [comp.assoc, ultrafilter_extend_extends, ← comp.assoc, hg'.comp_eq_id, comp.left_id],
  end }

/-- For any profinite `X`, the natural map `ultrafilter X → X` is a projective presentation. -/
def projective_presentation (X : Profinite.{u}) : projective_presentation X :=
{ P := of $ ultrafilter X,
  f := ⟨_, continuous_ultrafilter_extend id⟩,
  projective := Profinite.projective_ultrafilter X,
  epi := concrete_category.epi_of_surjective _ $
    λ x, ⟨(pure x : ultrafilter X), congr_fun (ultrafilter_extend_extends (𝟙 X)) x⟩ }

instance : enough_projectives Profinite.{u} :=
{ presentation := λ X, ⟨projective_presentation X⟩ }

end Profinite
