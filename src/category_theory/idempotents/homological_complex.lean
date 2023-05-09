/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebra.homology.additive
import category_theory.idempotents.karoubi

/-!
# Idempotent completeness and homological complexes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains simplifications lemmas for categories
`karoubi (homological_complex C c)` and the construction of an equivalence
of categories `karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`.

When the category `C` is idempotent complete, it is shown that
`homological_complex (karoubi C) c` is also idempotent complete.

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

open karoubi

namespace karoubi_homological_complex_equivalence

namespace functor

/-- The functor `karoubi (homological_complex C c) ⥤ homological_complex (karoubi C) c`,
on objects. -/
@[simps]
def obj (P : karoubi (homological_complex C c)) : homological_complex (karoubi C) c :=
{ X := λ n, ⟨P.X.X n, P.p.f n, by simpa only [homological_complex.comp_f]
    using homological_complex.congr_hom P.idem n⟩,
  d := λ i j,
    { f := P.p.f i ≫ P.X.d i j,
      comm := by tidy, },
  shape' := λ i j hij, by simp only [hom_eq_zero_iff,
    P.X.shape i j hij, limits.comp_zero], }

/-- The functor `karoubi (homological_complex C c) ⥤ homological_complex (karoubi C) c`,
on morphisms. -/
@[simps]
def map {P Q : karoubi (homological_complex C c)} (f : P ⟶ Q) : obj P ⟶ obj Q :=
{ f:= λ n,
  { f:= f.f.f n,
    comm := by simp, }, }

end functor

/-- The functor `karoubi (homological_complex C c) ⥤ homological_complex (karoubi C) c`. -/
@[simps]
def functor : karoubi (homological_complex C c) ⥤ homological_complex (karoubi C) c :=
{ obj := functor.obj,
  map := λ P Q f, functor.map f, }

namespace inverse

/-- The functor `homological_complex (karoubi C) c ⥤ karoubi (homological_complex C c)`,
on objects -/
@[simps]
def obj (K : homological_complex (karoubi C) c) : karoubi (homological_complex C c) :=
{ X :=
  { X := λ n, (K.X n).X,
    d := λ i j, (K.d i j).f,
    shape' := λ i j hij, hom_eq_zero_iff.mp (K.shape i j hij),
    d_comp_d' := λ i j k hij hjk, by { simpa only [comp_f]
      using hom_eq_zero_iff.mp (K.d_comp_d i j k), }, },
  p :=
    { f := λ n, (K.X n).p,
      comm' := by simp, },
  idem := by tidy, }

/-- The functor `homological_complex (karoubi C) c ⥤ karoubi (homological_complex C c)`,
on morphisms -/
@[simps]
def map {K L : homological_complex (karoubi C) c} (f : K ⟶ L) : obj K ⟶ obj L :=
{ f:=
  { f := λ n, (f.f n).f,
    comm' := λ i j hij, by simpa only [comp_f]
      using hom_ext.mp (f.comm' i j hij), },
  comm := by tidy, }

end inverse

/-- The functor `homological_complex (karoubi C) c ⥤ karoubi (homological_complex C c)`. -/
@[simps]
def inverse :
  homological_complex (karoubi C) c ⥤ karoubi (homological_complex C c) :=
{ obj := inverse.obj,
  map := λ K L f, inverse.map f, }


/-- The counit isomorphism of the equivalence
`karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`. -/
@[simps]
def counit_iso : inverse ⋙ functor ≅ 𝟭 (homological_complex (karoubi C) c) :=
eq_to_iso (functor.ext (λ P, homological_complex.ext (by tidy) (by tidy)) (by tidy))

/-- The unit isomorphism of the equivalence
`karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`. -/
@[simps]
def unit_iso : 𝟭 (karoubi (homological_complex C c)) ≅ functor ⋙ inverse :=
{ hom :=
  { app := λ P,
    { f :=
      { f := λ n, P.p.f n,
        comm' := λ i j hij, begin
          dsimp,
          simp only [homological_complex.hom.comm, homological_complex.hom.comm_assoc,
            homological_complex.p_idem],
        end },
      comm := by { ext n, dsimp, simp only [homological_complex.p_idem], }, },
    naturality' := λ P Q φ, begin
      ext,
      dsimp,
      simp only [comp_f, homological_complex.comp_f, homological_complex.comp_p_d,
        inverse.map_f_f, functor.map_f_f, homological_complex.p_comp_d],
    end, },
  inv :=
  { app := λ P,
    { f :=
      { f := λ n, P.p.f n,
        comm' := λ i j hij, begin
          dsimp,
          simp only [homological_complex.hom.comm, assoc, homological_complex.p_idem],
        end },
      comm := by { ext n, dsimp, simp only [homological_complex.p_idem], }, },
    naturality' := λ P Q φ, begin
      ext,
      dsimp,
      simp only [comp_f, homological_complex.comp_f, inverse.map_f_f, functor.map_f_f,
        homological_complex.comp_p_d, homological_complex.p_comp_d],
    end, },
  hom_inv_id' := begin
    ext,
    dsimp,
    simp only [homological_complex.p_idem, comp_f, homological_complex.comp_f, id_eq],
  end,
  inv_hom_id' := begin
    ext,
    dsimp,
    simp only [homological_complex.p_idem, comp_f, homological_complex.comp_f, id_eq,
      inverse.obj_p_f, functor.obj_X_p],
  end, }

end karoubi_homological_complex_equivalence

variables (C) (c)

/-- The equivalence `karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`. -/
@[simps]
def karoubi_homological_complex_equivalence :
  karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c :=
{ functor    := karoubi_homological_complex_equivalence.functor,
  inverse    := karoubi_homological_complex_equivalence.inverse,
  unit_iso   := karoubi_homological_complex_equivalence.unit_iso,
  counit_iso := karoubi_homological_complex_equivalence.counit_iso, }

variables (α : Type*) [add_right_cancel_semigroup α] [has_one α]

/-- The equivalence `karoubi (chain_complex C α) ≌ chain_complex (karoubi C) α`. -/
@[simps]
def karoubi_chain_complex_equivalence :
  karoubi (chain_complex C α) ≌ chain_complex (karoubi C) α :=
karoubi_homological_complex_equivalence C (complex_shape.down α)

/-- The equivalence `karoubi (cochain_complex C α) ≌ cochain_complex (karoubi C) α`. -/
@[simps]
def karoubi_cochain_complex_equivalence :
  karoubi (cochain_complex C α) ≌ cochain_complex (karoubi C) α :=
karoubi_homological_complex_equivalence C (complex_shape.up α)

instance [is_idempotent_complete C] : is_idempotent_complete (homological_complex C c) :=
begin
  rw [is_idempotent_complete_iff_of_equivalence
    ((to_karoubi_equivalence C).map_homological_complex c),
    ← is_idempotent_complete_iff_of_equivalence (karoubi_homological_complex_equivalence C c)],
  apply_instance,
end

end idempotents

end category_theory
