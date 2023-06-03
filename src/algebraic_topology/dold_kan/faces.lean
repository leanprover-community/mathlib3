/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.homotopies
import tactic.ring_exp

/-!

# Study of face maps for the Dold-Kan correspondence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

TODO (@joelriou) continue adding the various files referenced below

In this file, we obtain the technical lemmas that are used in the file
`projections.lean` in order to get basic properties of the endomorphisms
`P q : K[X] ⟶ K[X]` with respect to face maps (see `homotopies.lean` for the
role of these endomorphisms in the overall strategy of proof).

The main lemma in this file is `higher_faces_vanish.induction`. It is based
on two technical lemmas `higher_faces_vanish.comp_Hσ_eq` and
`higher_faces_vanish.comp_Hσ_eq_zero`.

-/

open nat
open category_theory
open category_theory.limits
open category_theory.category
open category_theory.preadditive
open category_theory.simplicial_object
open_locale simplicial dold_kan

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]
variables {X : simplicial_object C}

/-- A morphism `φ : Y ⟶ X _[n+1]` satisfies `higher_faces_vanish q φ`
when the compositions `φ ≫ X.δ j` are `0` for `j ≥ max 1 (n+2-q)`. When `q ≤ n+1`,
it basically means that the composition `φ ≫ X.δ j` are `0` for the `q` highest
possible values of a nonzero `j`. Otherwise, when `q ≥ n+2`, all the compositions
`φ ≫ X.δ j` for nonzero `j` vanish. See also the lemma `comp_P_eq_self_iff` in
`projections.lean` which states that `higher_faces_vanish q φ` is equivalent to
the identity `φ ≫ (P q).f (n+1) = φ`. -/
def higher_faces_vanish {Y : C} {n : ℕ} (q : ℕ) (φ : Y ⟶ X _[n+1]) : Prop :=
∀ (j : fin (n+1)), (n+1 ≤ (j : ℕ) + q) → φ ≫ X.δ j.succ = 0

namespace higher_faces_vanish

@[reassoc]
lemma comp_δ_eq_zero {Y : C} {n : ℕ} {q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) (j : fin (n+2)) (hj₁ : j ≠ 0) (hj₂ : n+2 ≤ (j : ℕ) + q) :
  φ ≫ X.δ j = 0 :=
begin
  obtain ⟨i, hi⟩ := fin.eq_succ_of_ne_zero hj₁,
  subst hi,
  apply v i,
  rw [← @nat.add_le_add_iff_right 1, add_assoc],
  simpa only [fin.coe_succ, add_assoc, add_comm 1] using hj₂,
end

lemma of_succ {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish (q+1) φ) : higher_faces_vanish q φ :=
λ j hj, v j (by simpa only [← add_assoc] using le_add_right hj)

lemma of_comp {Y Z : C} {q n : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) (f : Z ⟶ Y) :
  higher_faces_vanish q (f ≫ φ) := λ j hj,
by rw [assoc, v j hj, comp_zero]

lemma comp_Hσ_eq {Y : C} {n a q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) (hnaq : n=a+q) : φ ≫ (Hσ q).f (n+1) =
  - φ ≫ X.δ ⟨a+1, nat.succ_lt_succ (nat.lt_succ_iff.mpr (nat.le.intro hnaq.symm))⟩ ≫
    X.σ ⟨a, nat.lt_succ_iff.mpr (nat.le.intro hnaq.symm)⟩ :=
begin
  have hnaq_shift : Π d : ℕ, n+d=(a+d)+q,
  { intro d, rw [add_assoc, add_comm d, ← add_assoc, hnaq], },
  rw [Hσ, homotopy.null_homotopic_map'_f (c_mk (n+2) (n+1) rfl) (c_mk (n+1) n rfl),
    hσ'_eq hnaq (c_mk (n+1) n rfl), hσ'_eq (hnaq_shift 1) (c_mk (n+2) (n+1) rfl)],
  simp only [alternating_face_map_complex.obj_d_eq, eq_to_hom_refl,
    comp_id, comp_sum, sum_comp, comp_add],
  simp only [comp_zsmul, zsmul_comp, ← assoc, ← mul_zsmul],
  /- cleaning up the first sum -/
  rw [← fin.sum_congr' _ (hnaq_shift 2).symm, fin.sum_trunc], swap,
  { rintro ⟨k, hk⟩,
    suffices : φ ≫ X.δ (⟨a+2+k, by linarith⟩ : fin (n+2)) = 0,
    { simp only [this, fin.nat_add_mk, fin.cast_mk, zero_comp, smul_zero], },
    convert v ⟨a+k+1, by linarith⟩ (by { rw fin.coe_mk, linarith, }),
    rw [nat.succ_eq_add_one],
    linarith, },
  /- cleaning up the second sum -/
  rw [← fin.sum_congr' _ (hnaq_shift 3).symm, @fin.sum_trunc _ _ (a+3)], swap,
  { rintros ⟨k, hk⟩,
    rw [assoc, X.δ_comp_σ_of_gt', v.comp_δ_eq_zero_assoc, zero_comp, zsmul_zero],
    { intro h,
      rw [fin.pred_eq_iff_eq_succ, fin.ext_iff] at h,
      dsimp at h,
      linarith, },
    { dsimp,
      simp only [fin.coe_pred, fin.coe_mk, succ_add_sub_one],
      linarith, },
    { dsimp,
      linarith, }, },
  /- leaving out three specific terms -/
  conv_lhs { congr, skip, rw [fin.sum_univ_cast_succ, fin.sum_univ_cast_succ], },
  rw fin.sum_univ_cast_succ,
  simp only [fin.last, fin.cast_le_mk, fin.coe_cast, fin.cast_mk,
    fin.coe_cast_le, fin.coe_mk, fin.cast_succ_mk, fin.coe_cast_succ],
  /- the purpose of the following `simplif` is to create three subgoals in order
    to finish the proof -/
  have simplif : ∀ (a b c d e f : Y ⟶ X _[n+1]), b=f → d+e=0 → c+a=0 → a+b+(c+d+e) = f,
  { intros a b c d e f h1 h2 h3,
    rw [add_assoc c d e, h2, add_zero, add_comm a b, add_assoc,
      add_comm a c, h3, add_zero, h1], },
  apply simplif,
  { /- b=f -/
    rw [← pow_add, odd.neg_one_pow, neg_smul, one_zsmul],
    use a,
    linarith, },
  { /- d+e = 0 -/
    rw [assoc, assoc, X.δ_comp_σ_self' (fin.cast_succ_mk _ _ _).symm,
      X.δ_comp_σ_succ' (fin.succ_mk _ _ _).symm],
    simp only [comp_id, pow_add _ (a+1) 1, pow_one, mul_neg, mul_one, neg_smul,
      add_right_neg], },
  { /- c+a = 0 -/
    rw ← finset.sum_add_distrib,
    apply finset.sum_eq_zero,
    rintros ⟨i, hi⟩ h₀,
    have hia : (⟨i, by linarith⟩ : fin (n+2)) ≤ fin.cast_succ (⟨a, by linarith⟩ : fin (n+1)) :=
      by simpa only [fin.le_iff_coe_le_coe, fin.coe_mk, fin.cast_succ_mk, ← lt_succ_iff] using hi,
    simp only [fin.coe_mk, fin.cast_le_mk, fin.cast_succ_mk, fin.succ_mk, assoc, fin.cast_mk,
      ← δ_comp_σ_of_le X hia, add_eq_zero_iff_eq_neg, ← neg_zsmul],
    congr,
    ring_exp, },
end

lemma comp_Hσ_eq_zero {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) (hqn : n<q) : φ ≫ (Hσ q).f (n+1) = 0 :=
begin
  simp only [Hσ, homotopy.null_homotopic_map'_f (c_mk (n+2) (n+1) rfl) (c_mk (n+1) n rfl)],
  rw [hσ'_eq_zero hqn (c_mk (n+1) n rfl), comp_zero, zero_add],
  by_cases hqn' : n+1<q,
  { rw [hσ'_eq_zero hqn' (c_mk (n+2) (n+1) rfl), zero_comp, comp_zero], },
  { simp only [hσ'_eq (show n+1=0+q, by linarith) (c_mk (n+2) (n+1) rfl),
      pow_zero, fin.mk_zero, one_zsmul, eq_to_hom_refl, comp_id,
      comp_sum, alternating_face_map_complex.obj_d_eq],
    rw [← fin.sum_congr' _ (show 2+(n+1)=n+1+2, by linarith), fin.sum_trunc],
    { simp only [fin.sum_univ_cast_succ, fin.sum_univ_zero, zero_add, fin.last,
        fin.cast_le_mk, fin.cast_mk, fin.cast_succ_mk],
      simp only [fin.mk_zero, fin.coe_zero, pow_zero, one_zsmul, fin.mk_one,
        fin.coe_one, pow_one, neg_smul, comp_neg],
      erw [δ_comp_σ_self, δ_comp_σ_succ, add_right_neg], },
    { intro j,
      rw [comp_zsmul, comp_zsmul, δ_comp_σ_of_gt', v.comp_δ_eq_zero_assoc, zero_comp, zsmul_zero],
      { intro h,
        rw [fin.pred_eq_iff_eq_succ, fin.ext_iff] at h,
        dsimp at h,
        linarith, },
      { dsimp,
        simp only [fin.cast_nat_add, fin.coe_pred, fin.coe_add_nat, add_succ_sub_one],
        linarith, },
      { rw fin.lt_iff_coe_lt_coe,
        dsimp,
        linarith, }, }, },
end

lemma induction {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : higher_faces_vanish (q+1) (φ ≫ (𝟙 _ + Hσ q).f (n+1)) :=
begin
  intros j hj₁,
  dsimp,
  simp only [comp_add, add_comp, comp_id],
  -- when n < q, the result follows immediately from the assumption
  by_cases hqn : n<q,
  { rw [v.comp_Hσ_eq_zero hqn, zero_comp, add_zero, v j (by linarith)], },
  -- we now assume that n≥q, and write n=a+q
  cases nat.le.dest (not_lt.mp hqn) with a ha,
  rw [v.comp_Hσ_eq (show n=a+q, by linarith), neg_comp, add_neg_eq_zero, assoc, assoc],
  cases n with m hm,
  -- the boundary case n=0
  { simpa only [nat.eq_zero_of_add_eq_zero_left ha, fin.eq_zero j,
      fin.mk_zero, fin.mk_one, δ_comp_σ_succ, comp_id], },
  -- in the other case, we need to write n as m+1
  -- then, we first consider the particular case j = a
  by_cases hj₂ : a = (j : ℕ),
  { simp only [hj₂, fin.eta, δ_comp_σ_succ, comp_id],
    congr,
    ext,
    simp only [fin.coe_succ, fin.coe_mk], },
  -- now, we assume j ≠ a (i.e. a < j)
  have haj : a<j := (ne.le_iff_lt hj₂).mp (by linarith),
  have hj₃ := j.is_lt,
  have ham : a≤m,
  { by_contradiction,
    rw [not_le, ← nat.succ_le_iff] at h,
    linarith, },
  rw [X.δ_comp_σ_of_gt', j.pred_succ], swap,
  { rw fin.lt_iff_coe_lt_coe,
    simpa only [fin.coe_mk, fin.coe_succ, add_lt_add_iff_right] using haj, },
  obtain (ham' | ham'') := ham.lt_or_eq,
  { -- case where `a<m`
    rw ← X.δ_comp_δ''_assoc, swap,
    { rw fin.le_iff_coe_le_coe,
      dsimp,
      linarith, },
    simp only [← assoc, v j (by linarith), zero_comp], },
  { -- in the last case, a=m, q=1 and j=a+1
    rw X.δ_comp_δ_self'_assoc, swap,
    { ext,
      dsimp,
      have hq : q = 1 := by rw [← add_left_inj a, ha, ham'', add_comm],
      linarith, },
    simp only [← assoc, v j (by linarith), zero_comp], },
end

end higher_faces_vanish

end dold_kan

end algebraic_topology
