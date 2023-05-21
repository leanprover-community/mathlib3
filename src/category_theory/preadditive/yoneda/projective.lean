/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.preadditive.yoneda.basic
import category_theory.preadditive.projective
import algebra.category.Group.epi_mono
import algebra.category.Module.epi_mono

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An object is projective iff the preadditive coyoneda functor on it preserves epimorphisms.
-/

universes v u

open opposite

namespace category_theory
variables {C : Type u} [category.{v} C]

section preadditive
variables [preadditive C]

namespace projective

lemma projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj (P : C) :
  projective P ↔ (preadditive_coyoneda.obj (op P)).preserves_epimorphisms :=
begin
  rw projective_iff_preserves_epimorphisms_coyoneda_obj,
  refine ⟨λ (h : (preadditive_coyoneda.obj (op P) ⋙ (forget _)).preserves_epimorphisms), _, _⟩,
  { exactI functor.preserves_epimorphisms_of_preserves_of_reflects (preadditive_coyoneda.obj (op P))
      (forget _) },
  { introI,
    exact (infer_instance : (preadditive_coyoneda.obj (op P) ⋙ forget _).preserves_epimorphisms) }
end

lemma projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj' (P : C) :
  projective P ↔ (preadditive_coyoneda_obj (op P)).preserves_epimorphisms :=
begin
  rw projective_iff_preserves_epimorphisms_coyoneda_obj,
  refine ⟨λ (h : (preadditive_coyoneda_obj (op P) ⋙ (forget _)).preserves_epimorphisms), _, _⟩,
  { exactI functor.preserves_epimorphisms_of_preserves_of_reflects (preadditive_coyoneda_obj (op P))
      (forget _) },
  { introI,
    exact (infer_instance : (preadditive_coyoneda_obj (op P) ⋙ forget _).preserves_epimorphisms) }
end

end projective

end preadditive

end category_theory
