/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.projections
import category_theory.idempotents.functor_categories
import category_theory.idempotents.functor_extension

/-!

# Construction of the projection `P_infty` for the Dold-Kan correspondence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

TODO (@joelriou) continue adding the various files referenced below

In this file, we construct the projection `P_infty : K[X] ⟶ K[X]` by passing
to the limit the projections `P q` defined in `projections.lean`. This
projection is a critical tool in this formalisation of the Dold-Kan correspondence,
because in the case of abelian categories, `P_infty` corresponds to the
projection on the normalized Moore subcomplex, with kernel the degenerate subcomplex.
(See `equivalence.lean` for the general strategy of proof.)

-/

open category_theory
open category_theory.category
open category_theory.preadditive
open category_theory.simplicial_object
open category_theory.idempotents
open opposite
open_locale simplicial dold_kan

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C] {X : simplicial_object C}

lemma P_is_eventually_constant {q n : ℕ} (hqn : n ≤ q) :
  ((P (q+1)).f n : X _[n] ⟶ _ ) = (P q).f n :=
begin
  cases n,
  { simp only [P_f_0_eq], },
  { unfold P,
    simp only [add_right_eq_self, comp_add, homological_complex.comp_f,
      homological_complex.add_f_apply, comp_id],
    exact (higher_faces_vanish.of_P q n).comp_Hσ_eq_zero
      (nat.succ_le_iff.mp hqn), },
end

lemma Q_is_eventually_constant {q n : ℕ} (hqn : n ≤ q) :
  ((Q (q+1)).f n : X _[n] ⟶ _ ) = (Q q).f n :=
by simp only [Q, homological_complex.sub_f_apply, P_is_eventually_constant hqn]

/-- The endomorphism `P_infty : K[X] ⟶ K[X]` obtained from the `P q` by passing to the limit. -/
def P_infty : K[X] ⟶ K[X] := chain_complex.of_hom _ _ _ _ _ _
  (λ n, ((P n).f n : X _[n] ⟶ _ ))
  (λ n, by simpa only [← P_is_eventually_constant (show n ≤ n, by refl),
    alternating_face_map_complex.obj_d_eq] using (P (n+1)).comm (n+1) n)

/-- The endomorphism `Q_infty : K[X] ⟶ K[X]` obtained from the `Q q` by passing to the limit. -/
def Q_infty : K[X] ⟶ K[X] := 𝟙 _ - P_infty

@[simp]
lemma P_infty_f_0 : (P_infty.f 0 : X _[0] ⟶ X _[0]) = 𝟙 _ := rfl

lemma P_infty_f (n : ℕ) : (P_infty.f n : X _[n] ⟶  X _[n] ) = (P n).f n := rfl

@[simp]
lemma Q_infty_f_0 : (Q_infty.f 0 : X _[0] ⟶ X _[0]) = 0 :=
by { dsimp [Q_infty], simp only [sub_self], }

lemma Q_infty_f (n : ℕ) : (Q_infty.f n : X _[n] ⟶  X _[n] ) = (Q n).f n := rfl

@[simp, reassoc]
lemma P_infty_f_naturality (n : ℕ) {X Y : simplicial_object C} (f : X ⟶ Y) :
  f.app (op [n]) ≫ P_infty.f n = P_infty.f n ≫ f.app (op [n]) :=
P_f_naturality n n f

@[simp, reassoc]
lemma Q_infty_f_naturality (n : ℕ) {X Y : simplicial_object C} (f : X ⟶ Y) :
  f.app (op [n]) ≫ Q_infty.f n = Q_infty.f n ≫ f.app (op [n]) :=
Q_f_naturality n n f

@[simp, reassoc]
lemma P_infty_f_idem (n : ℕ) :
  (P_infty.f n : X _[n] ⟶ _) ≫ (P_infty.f n) = P_infty.f n :=
by simp only [P_infty_f, P_f_idem]

@[simp, reassoc]
lemma P_infty_idem : (P_infty : K[X] ⟶ _) ≫ P_infty = P_infty :=
by { ext n, exact P_infty_f_idem n, }

@[simp, reassoc]
lemma Q_infty_f_idem (n : ℕ) :
  (Q_infty.f n : X _[n] ⟶ _) ≫ (Q_infty.f n) = Q_infty.f n :=
Q_f_idem _ _

@[simp, reassoc]
lemma Q_infty_idem : (Q_infty : K[X] ⟶ _) ≫ Q_infty = Q_infty :=
by { ext n, exact Q_infty_f_idem n, }

@[simp, reassoc]
lemma P_infty_f_comp_Q_infty_f (n : ℕ) :
  (P_infty.f n : X _[n] ⟶ _) ≫ Q_infty.f n = 0 :=
begin
  dsimp only [Q_infty],
  simp only [homological_complex.sub_f_apply, homological_complex.id_f, comp_sub, comp_id,
    P_infty_f_idem, sub_self],
end

@[simp, reassoc]
lemma P_infty_comp_Q_infty :
  (P_infty : K[X] ⟶ _) ≫ Q_infty = 0 :=
by { ext n, apply P_infty_f_comp_Q_infty_f, }

@[simp, reassoc]
lemma Q_infty_f_comp_P_infty_f (n : ℕ) :
  (Q_infty.f n : X _[n] ⟶ _) ≫ P_infty.f n = 0 :=
begin
  dsimp only [Q_infty],
  simp only [homological_complex.sub_f_apply, homological_complex.id_f, sub_comp, id_comp,
    P_infty_f_idem, sub_self],
end

@[simp, reassoc]
lemma Q_infty_comp_P_infty :
  (Q_infty : K[X] ⟶ _) ≫ P_infty = 0 :=
by { ext n, apply Q_infty_f_comp_P_infty_f, }

@[simp]
lemma P_infty_add_Q_infty :
  (P_infty : K[X] ⟶ _) + Q_infty = 𝟙 _ :=
by { dsimp only [Q_infty], simp only [add_sub_cancel'_right], }

lemma P_infty_f_add_Q_infty_f (n : ℕ) :
  (P_infty.f n : X _[n] ⟶ _ ) + Q_infty.f n = 𝟙 _ :=
homological_complex.congr_hom (P_infty_add_Q_infty) n

variable (C)

/-- `P_infty` induces a natural transformation, i.e. an endomorphism of
the functor `alternating_face_map_complex C`. -/
@[simps]
def nat_trans_P_infty :
  alternating_face_map_complex C ⟶ alternating_face_map_complex C :=
{ app := λ _, P_infty,
  naturality' := λ X Y f, by { ext n, exact P_infty_f_naturality n f, }, }

/-- The natural transformation in each degree that is induced by `nat_trans_P_infty`. -/
@[simps]
def nat_trans_P_infty_f (n : ℕ) :=
nat_trans_P_infty C ◫ 𝟙 (homological_complex.eval _ _ n)

variable {C}

@[simp]
lemma map_P_infty_f {D : Type*} [category D] [preadditive D]
  (G : C ⥤ D) [G.additive] (X : simplicial_object C) (n : ℕ) :
  (P_infty : K[((whiskering C D).obj G).obj X] ⟶ _).f n =
  G.map ((P_infty : alternating_face_map_complex.obj X ⟶ _).f n) :=
by simp only [P_infty_f, map_P]

/-- Given an object `Y : karoubi (simplicial_object C)`, this lemma
computes `P_infty` for the associated object in `simplicial_object (karoubi C)`
in terms of `P_infty` for `Y.X : simplicial_object C` and `Y.p`. -/
lemma karoubi_P_infty_f {Y : karoubi (simplicial_object C)} (n : ℕ) :
  ((P_infty : K[(karoubi_functor_category_embedding _ _).obj Y] ⟶ _).f n).f =
    Y.p.app (op [n]) ≫ (P_infty : K[Y.X] ⟶ _).f n :=
begin
  -- We introduce P_infty endomorphisms P₁, P₂, P₃, P₄ on various objects Y₁, Y₂, Y₃, Y₄.
  let Y₁ := (karoubi_functor_category_embedding _ _).obj Y,
  let Y₂ := Y.X,
  let Y₃ := (((whiskering _ _).obj (to_karoubi C)).obj Y.X),
  let Y₄ := (karoubi_functor_category_embedding _ _).obj ((to_karoubi _).obj Y.X),
  let P₁ : K[Y₁] ⟶ _ := P_infty,
  let P₂ : K[Y₂] ⟶ _ := P_infty,
  let P₃ : K[Y₃] ⟶ _ := P_infty,
  let P₄ : K[Y₄] ⟶ _ := P_infty,
  -- The statement of lemma relates P₁ and P₂.
  change (P₁.f n).f = Y.p.app (op [n]) ≫ P₂.f n,
  -- The proof proceeds by obtaining relations h₃₂, h₄₃, h₁₄.
  have h₃₂ : (P₃.f n).f = P₂.f n := karoubi.hom_ext.mp (map_P_infty_f (to_karoubi C) Y₂ n),
  have h₄₃ : P₄.f n = P₃.f n,
  { have h := functor.congr_obj (to_karoubi_comp_karoubi_functor_category_embedding _ _) Y₂,
    simp only [← nat_trans_P_infty_f_app],
    congr', },
  let τ₁ := 𝟙 (karoubi_functor_category_embedding (simplex_categoryᵒᵖ) C),
  let τ₂ := nat_trans_P_infty_f (karoubi C) n,
  let τ := τ₁ ◫ τ₂,
  have h₁₄ := idempotents.nat_trans_eq τ Y,
  dsimp [τ, τ₁, τ₂, nat_trans_P_infty_f] at h₁₄,
  rw [id_comp, id_comp, comp_id, comp_id] at h₁₄,
  /- We use the three equalities h₃₂, h₄₃, h₁₄. -/
  rw [← h₃₂, ← h₄₃, h₁₄],
  simp only [karoubi_functor_category_embedding.map_app_f, karoubi.decomp_id_p_f,
    karoubi.decomp_id_i_f, karoubi.comp_f],
  let π : Y₄ ⟶ Y₄ := (to_karoubi _ ⋙ karoubi_functor_category_embedding _ _).map Y.p,
  have eq := karoubi.hom_ext.mp (P_infty_f_naturality n π),
  simp only [karoubi.comp_f] at eq,
  dsimp [π] at eq,
  rw [← eq, reassoc_of (app_idem Y (op [n]))],
end

end dold_kan

end algebraic_topology
