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
`karoubi (homological_complex C c)` and the construction of an equivalence
of categories `karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`.

-/

namespace category_theory

open category

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

variable (P)

@[simp, reassoc]
lemma p_idem : P.p.f n ≫ P.p.f n = P.p.f n :=
homological_complex.congr_hom P.idem n

end homological_complex

end karoubi


namespace karoubi_homological_complex_equivalence

namespace functor

@[simps]
def obj (P : karoubi (homological_complex C c)) : homological_complex (karoubi C) c :=
{ X := λ n, ⟨P.X.X n, P.p.f n, by simpa only [homological_complex.comp_f]
    using homological_complex.congr_hom P.idem n⟩,
  d := λ i j,
    { f := P.p.f i ≫ P.X.d i j,
      comm := by tidy, },
  shape' := λ i j hij, by simp only [karoubi.hom_eq_zero_iff,
    P.X.shape i j hij, limits.comp_zero], }

@[simps]
def map {P Q : karoubi (homological_complex C c)} (f : P ⟶ Q) : obj P ⟶ obj Q :=
{ f:= λ n,
  { f:= f.f.f n,
    comm := by simp, }, }

end functor

@[simps]
def functor :
  karoubi (homological_complex C c) ⥤ homological_complex (karoubi C) c :=
{ obj := functor.obj,
  map := λ P Q f, functor.map f, }

namespace inverse

@[simps]
def obj (K : homological_complex (karoubi C) c) : karoubi (homological_complex C c) :=
{ X :=
  { X := λ n, (K.X n).X,
    d := λ i j, (K.d i j).f,
    shape' := λ i j hij, karoubi.hom_eq_zero_iff.mp (K.shape i j hij),
    d_comp_d' := λ i j k hij hjk, by { simpa only [karoubi.comp_f]
      using karoubi.hom_eq_zero_iff.mp (K.d_comp_d i j k), }, },
  p :=
    { f := λ n, (K.X n).p,
      comm' := by simp, },
  idem := by tidy, }

@[simps]
def map {K L : homological_complex (karoubi C) c} (f : K ⟶ L) : obj K ⟶ obj L :=
{ f:=
  { f := λ n, (f.f n).f,
    comm' := λ i j hij, by simpa only [karoubi.comp_f]
      using karoubi.hom_ext.mp (f.comm' i j hij), },
  comm := by tidy, }

end inverse

@[simps]
def inverse :
  homological_complex (karoubi C) c ⥤ karoubi (homological_complex C c) :=
{ obj := inverse.obj,
  map := λ K L f, inverse.map f, }

@[simps]
def counit_iso : inverse ⋙ functor ≅ 𝟭 (homological_complex (karoubi C) c) :=
eq_to_iso (functor.ext (λ P, homological_complex.ext (by tidy) (by tidy)) (by tidy))

@[simps]
def unit_iso : 𝟭 (karoubi (homological_complex C c)) ≅ functor ⋙ inverse :=
{ hom :=
  { app := λ P,
    { f := { f := λ n, P.p.f n, },
      comm := by tidy, }, },
  inv :=
  { app := λ P,
    { f := { f := λ n, P.p.f n, },
      comm := by tidy, }, }, }

end karoubi_homological_complex_equivalence

variables (C) (c)

@[simps]
def karoubi_homological_complex_equivalence :
  karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c :=
{ functor    := karoubi_homological_complex_equivalence.functor,
  inverse    := karoubi_homological_complex_equivalence.inverse,
  unit_iso   := karoubi_homological_complex_equivalence.unit_iso,
  counit_iso := karoubi_homological_complex_equivalence.counit_iso, }

variables (α : Type*) [add_right_cancel_semigroup α] [has_one α]

@[simps]
def karoubi_chain_complex_equivalence :
  karoubi (chain_complex C α) ≌
    chain_complex (karoubi C) α :=
karoubi_homological_complex_equivalence C (complex_shape.down α)

@[simps]
def karoubi_cochain_complex_equivalence :
  karoubi (cochain_complex C α) ≌
    cochain_complex (karoubi C) α :=
karoubi_homological_complex_equivalence C (complex_shape.up α)

end idempotents

end category_theory
