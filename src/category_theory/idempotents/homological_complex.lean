/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebra.homology.homological_complex
import category_theory.idempotents.karoubi

/-!
# Idempotent completeness and homological complexes

This file contains simplifications lemmas for categories
`karoubi (homological_complex C c)`.

TODO @joelriou : Get an equivalence of categories
`karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`
for all preadditive categories `C` and complex shape `c`.

-/

namespace category_theory

variables {C : Type*} [category C] [preadditive C] {ι : Type*} {c : complex_shape ι}

namespace idempotents

namespace karoubi

namespace homological_complex

variables {P Q : karoubi (homological_complex C c)} (f : P ⟶ Q) (n : ι)

@[simp, reassoc]
lemma p_comp_d : P.p.f n ≫ f.f.f n = f.f.f n :=
homological_complex.congr_hom (p_comp f) n

@[simp, reassoc]
lemma comp_p_d : f.f.f n ≫ Q.p.f n = f.f.f n :=
homological_complex.congr_hom (comp_p f) n

@[reassoc]
lemma p_comm_f : P.p.f n ≫ f.f.f n = f.f.f n ≫ Q.p.f n :=
homological_complex.congr_hom (p_comm f) n

end homological_complex

end karoubi

end idempotents

end category_theory
