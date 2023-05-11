/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.faces
import category_theory.idempotents.basic

/-!

# Construction of projections for the Dold-Kan correspondence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

TODO (@joelriou) continue adding the various files referenced below

In this file, we construct endomorphisms `P q : K[X] ⟶ K[X]` for all
`q : ℕ`. We study how they behave with respect to face maps with the lemmas
`higher_faces_vanish.of_P`, `higher_faces_vanish.comp_P_eq_self` and
`comp_P_eq_self_iff`.

Then, we show that they are projections (see `P_f_idem`
and `P_idem`). They are natural transformations (see `nat_trans_P`
and `P_f_naturality`) and are compatible with the application
of additive functors (see `map_P`).

By passing to the limit, these endomorphisms `P q` shall be used in `p_infty.lean`
in order to define `P_infty : K[X] ⟶ K[X]`, see `equivalence.lean` for the general
strategy of proof of the Dold-Kan equivalence.

-/

open category_theory category_theory.category category_theory.limits
  category_theory.preadditive category_theory.simplicial_object opposite
  category_theory.idempotents
open_locale simplicial dold_kan

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C] {X : simplicial_object C}

/-- This is the inductive definition of the projections `P q : K[X] ⟶ K[X]`,
with `P 0 := 𝟙 _` and `P (q+1) := P q ≫ (𝟙 _ + Hσ q)`. -/
noncomputable def P : ℕ → (K[X] ⟶ K[X])
| 0     := 𝟙 _
| (q+1) := P q ≫ (𝟙 _ + Hσ q)

/-- All the `P q` coincide with `𝟙 _` in degree 0. -/
@[simp]
lemma P_f_0_eq (q : ℕ) : ((P q).f 0 : X _[0] ⟶ X _[0]) = 𝟙 _ :=
begin
  induction q with q hq,
  { refl, },
  { unfold P,
    simp only [homological_complex.add_f_apply, homological_complex.comp_f,
      homological_complex.id_f, id_comp, hq, Hσ_eq_zero, add_zero], },
end

/-- `Q q` is the complement projection associated to `P q` -/
def Q (q : ℕ) : K[X] ⟶ K[X] := 𝟙 _ - P q

lemma P_add_Q (q : ℕ) : P q + Q q = 𝟙 K[X] := by { rw Q, abel, }

lemma P_add_Q_f (q n : ℕ) : (P q).f n + (Q q).f n = 𝟙 (X _[n]) :=
homological_complex.congr_hom (P_add_Q q) n

@[simp]
lemma Q_eq_zero : (Q 0 : K[X] ⟶ _) = 0 := sub_self _

lemma Q_eq (q : ℕ) : (Q (q+1) : K[X] ⟶ _) = Q q - P q ≫ Hσ q :=
by { unfold Q P, simp only [comp_add, comp_id], abel, }

/-- All the `Q q` coincide with `0` in degree 0. -/
@[simp]
lemma Q_f_0_eq (q : ℕ) : ((Q q).f 0 : X _[0] ⟶ X _[0]) = 0 :=
by simp only [homological_complex.sub_f_apply, homological_complex.id_f, Q, P_f_0_eq, sub_self]

namespace higher_faces_vanish

/-- This lemma expresses the vanishing of
`(P q).f (n+1) ≫ X.δ k : X _[n+1] ⟶ X _[n]` when `k≠0` and `k≥n-q+2` -/
lemma of_P : Π (q n : ℕ), higher_faces_vanish q (((P q).f (n+1) : X _[n+1] ⟶ X _[n+1]))
| 0     := λ n j hj₁, by { exfalso, have hj₂ := fin.is_lt j, linarith, }
| (q+1) := λ n, by { unfold P, exact (of_P q n).induction, }

@[reassoc]
lemma comp_P_eq_self {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : φ ≫ (P q).f (n+1) = φ :=
begin
  induction q with q hq,
  { unfold P,
    apply comp_id, },
  { unfold P,
    simp only [comp_add, homological_complex.comp_f, homological_complex.add_f_apply,
      comp_id, ← assoc, hq v.of_succ, add_right_eq_self],
    by_cases hqn : n<q,
    { exact v.of_succ.comp_Hσ_eq_zero hqn, },
    { cases nat.le.dest (not_lt.mp hqn) with a ha,
      have hnaq : n=a+q := by linarith,
      simp only [v.of_succ.comp_Hσ_eq hnaq, neg_eq_zero, ← assoc],
      have eq := v ⟨a, by linarith⟩
        (by simp only [hnaq, fin.coe_mk, nat.succ_eq_add_one, add_assoc]),
      simp only [fin.succ_mk] at eq,
      simp only [eq, zero_comp], }, },
end

end higher_faces_vanish

lemma comp_P_eq_self_iff {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n+1]} :
  φ ≫ (P q).f (n+1) = φ ↔ higher_faces_vanish q φ :=
begin
  split,
  { intro hφ,
    rw ← hφ,
    apply higher_faces_vanish.of_comp,
    apply higher_faces_vanish.of_P, },
  { exact higher_faces_vanish.comp_P_eq_self, },
end

@[simp, reassoc]
lemma P_f_idem (q n : ℕ) :
  ((P q).f n : X _[n] ⟶ _) ≫ ((P q).f n) = (P q).f n :=
begin
  cases n,
  { rw [P_f_0_eq q, comp_id], },
  { exact (higher_faces_vanish.of_P q n).comp_P_eq_self, }
end

@[simp, reassoc]
lemma Q_f_idem (q n : ℕ) :
  ((Q q).f n : X _[n] ⟶ _) ≫ ((Q q).f n) = (Q q).f n :=
idem_of_id_sub_idem _ (P_f_idem q n)

@[simp, reassoc]
lemma P_idem (q : ℕ) : (P q : K[X] ⟶ K[X]) ≫ P q = P q :=
by { ext n, exact P_f_idem q n, }

@[simp, reassoc]
lemma Q_idem (q : ℕ) : (Q q : K[X] ⟶ K[X]) ≫ Q q = Q q :=
by { ext n, exact Q_f_idem q n, }

/-- For each `q`, `P q` is a natural transformation. -/
@[simps]
def nat_trans_P (q : ℕ) :
  alternating_face_map_complex C ⟶ alternating_face_map_complex C :=
{ app := λ X, P q,
  naturality' := λ X Y f, begin
    induction q with q hq,
    { unfold P,
      dsimp only [alternating_face_map_complex],
      rw [id_comp, comp_id], },
    { unfold P,
      simp only [add_comp, comp_add, assoc, comp_id, hq],
      congr' 1,
      rw [← assoc, hq, assoc],
      congr' 1,
      exact (nat_trans_Hσ q).naturality' f, }
  end }

@[simp, reassoc]
lemma P_f_naturality (q n : ℕ) {X Y : simplicial_object C} (f : X ⟶ Y) :
  f.app (op [n]) ≫ (P q).f n = (P q).f n ≫ f.app (op [n]) :=
homological_complex.congr_hom ((nat_trans_P q).naturality f) n

@[simp, reassoc]
lemma Q_f_naturality (q n : ℕ) {X Y : simplicial_object C} (f : X ⟶ Y) :
  f.app (op [n]) ≫ (Q q).f n = (Q q).f n ≫ f.app (op [n]) :=
begin
  simp only [Q, homological_complex.sub_f_apply, homological_complex.id_f,
    comp_sub, P_f_naturality, sub_comp, sub_left_inj],
  dsimp,
  simp only [comp_id, id_comp],
end

/-- For each `q`, `Q q` is a natural transformation. -/
@[simps]
def nat_trans_Q (q : ℕ) :
  alternating_face_map_complex C ⟶ alternating_face_map_complex C :=
{ app := λ X, Q q, }

lemma map_P {D : Type*} [category D] [preadditive D]
  (G : C ⥤ D) [G.additive] (X : simplicial_object C) (q n : ℕ) :
  G.map ((P q : K[X] ⟶ _).f n) = (P q : K[((whiskering C D).obj G).obj X] ⟶ _).f n :=
begin
  induction q with q hq,
  { unfold P,
    apply G.map_id, },
  { unfold P,
    simp only [comp_add, homological_complex.comp_f, homological_complex.add_f_apply,
      comp_id, functor.map_add, functor.map_comp, hq, map_Hσ], }
end

lemma map_Q {D : Type*} [category D] [preadditive D]
  (G : C ⥤ D) [G.additive] (X : simplicial_object C) (q n : ℕ) :
  G.map ((Q q : K[X] ⟶ _).f n) = (Q q : K[((whiskering C D).obj G).obj X] ⟶ _).f n :=
begin
  rw [← add_right_inj (G.map ((P q : K[X] ⟶ _).f n)), ← G.map_add, map_P G X q n,
    P_add_Q_f, P_add_Q_f],
  apply G.map_id,
end

end dold_kan

end algebraic_topology
