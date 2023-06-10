/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.preadditive.yoneda.basic
import category_theory.preadditive.injective
import algebra.category.Group.epi_mono
import algebra.category.Module.epi_mono

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An object is injective iff the preadditive yoneda functor on it preserves epimorphisms.
-/

universes v u

open opposite

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
