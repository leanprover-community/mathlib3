/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.preadditive.injective
import category_theory.preadditive.projective
import algebra.category.Group.epi_mono
import algebra.category.Module.epi_mono

universes v u

/-!
An object is injective iff the preadditive yoneda functor on it preserves epimorphisms.
-/

open category_theory
open category_theory.limits
open opposite
open category_theory.projective

namespace category_theory
variables {C : Type u} [category.{v} C]

section preadditive
variables [preadditive C]

namespace injective

lemma injective_iff_preserves_epimorphisms_preadditive_yoneda_obj (J : C) :
  injective J ↔ (preadditive_yoneda.obj J).preserves_epimorphisms :=
begin
  rw injective_iff_preserves_epimorphisms_yoneda_obj,
  refine ⟨λ (h : (preadditive_yoneda.obj J ⋙ (forget _)).preserves_epimorphisms), _, _⟩,
  { exactI functor.preserves_epimorphisms_of_preserves_of_reflects (preadditive_yoneda.obj J)
      (forget _) },
  { introI,
    exact (infer_instance : (preadditive_yoneda.obj J ⋙ forget _).preserves_epimorphisms) }
end

lemma injective_iff_preserves_epimorphisms_preadditive_yoneda_obj' (J : C) :
  injective J ↔ (preadditive_yoneda_obj J).preserves_epimorphisms :=
begin
  rw injective_iff_preserves_epimorphisms_yoneda_obj,
  refine ⟨λ (h : (preadditive_yoneda_obj J ⋙ (forget _)).preserves_epimorphisms), _, _⟩,
  { exactI functor.preserves_epimorphisms_of_preserves_of_reflects (preadditive_yoneda_obj J)
      (forget _) },
  { introI,
    exact (infer_instance : (preadditive_yoneda_obj J ⋙ forget _).preserves_epimorphisms) }
end

end injective

end preadditive

end category_theory
