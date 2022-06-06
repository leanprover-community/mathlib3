/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.alternating_face_map_complex
import algebraic_topology.cech_nerve
import algebra.homology.homotopy
import tactic.equiv_rw
import tactic.fin_cases

noncomputable theory

open_locale simplicial

open category_theory category_theory.category category_theory.limits
open category_theory.simplicial_object.augmented
open opposite simplex_category

namespace algebraic_topology

variables {C : Type*} [category C]

/-- The datum of an extra degeneracy is a technical condition on
augmented simplicial objects. The morphisms `s'` and `s n` of the
structure formally behave like extra degeneracies `σ (-1)`. In
the case of augmented simplicial sets, the existence of an extra
degeneray implies the augmentation is an homotopy equivalence. -/
@[nolint has_inhabited_instance]
structure extra_degeneracy (X : simplicial_object.augmented C) :=
(s' : point.obj X ⟶ (drop.obj X) _[0])
(s : Π (n : ℕ), (drop.obj X) _[n] ⟶ (drop.obj X) _[n+1])
(d₀s' : s' ≫ X.hom.app (op [0]) = 𝟙 _)
(ds₀ : s 0 ≫ (drop.obj X).δ 1 = X.hom.app (op [0]) ≫ s')
(d₀s : Π (n : ℕ), s n ≫ (drop.obj X).δ 0 = 𝟙 _)
(ds : Π (n : ℕ) (i : fin (n+2)), s (n+1) ≫ (drop.obj X).δ i.succ =
  (drop.obj X).δ i ≫ s n)
(ss : Π (n : ℕ) (i : fin (n+1)), s n ≫ (drop.obj X).σ i.succ =
  (drop.obj X).σ i ≫ s (n+1))

namespace extra_degeneracy

/-- If `ed` is an extra degeneracy for `X : simplicial_object.augmented C` and
`F : C ⥤ D` is a functor, then `ed.map F` is an extra degeneracy for
augmented simplical objects in `D` obtained by applying `F` to `X`. -/
def map {D : Type*} [category D]
  {X : simplicial_object.augmented C} (ed : extra_degeneracy X) (F : C ⥤ D) :
  extra_degeneracy (((whiskering _ _).obj F).obj X) :=
{ s' := F.map ed.s',
  s := λ n, F.map (ed.s n),
  d₀s' := by { dsimp, erw [comp_id, ← F.map_comp, ed.d₀s', F.map_id], },
  ds₀ := by { dsimp, erw [comp_id, ← F.map_comp, ← F.map_comp, ed.ds₀], },
  d₀s := λ n, by { dsimp, erw [← F.map_comp, ed.d₀s, F.map_id], },
  ds := λ n i, by { dsimp, erw [← F.map_comp, ← F.map_comp, ed.ds], refl, },
  ss := λ n i, by { dsimp, erw [← F.map_comp, ← F.map_comp, ed.ss], refl, }, }

/-- If `X` and `Y` are isomorphism augmented simplicial objects, then an extra
degeneracy for `X` gives also an extra degeneracy for `Y` -/
def of_iso {X Y : simplicial_object.augmented C} (e : X ≅ Y) (ed : extra_degeneracy X) :
  extra_degeneracy Y :=
{ s' := (point.map_iso e).inv ≫ ed.s' ≫ (drop.map_iso e).hom.app (op [0]),
  s := λ n, (drop.map_iso e).inv.app (op [n]) ≫ ed.s n ≫ (drop.map_iso e).hom.app (op [n+1]),
  d₀s' := begin
    simp only [assoc],
    erw w₀,
    slice_lhs 2 3 { rw ed.d₀s', },
    rw id_comp,
    exact (point.map_iso e).inv_hom_id,
  end,
  ds₀ := begin
    slice_rhs 1 2 { erw [← w₀], },
    slice_rhs 2 3 { rw [← ed.ds₀], },
    slice_rhs 3 4 { erw (drop.map e.hom).naturality, },
    simpa only [assoc],
  end,
  d₀s := λ n, begin
    slice_lhs 3 4 { erw ← (drop.map e.hom).naturality, },
    slice_lhs 2 3 { erw ed.d₀s, },
    rw id_comp,
    convert congr_app (drop.map_iso e).inv_hom_id (op [n]),
  end,
  ds := λ n i, begin
    slice_lhs 3 4 { erw ← (drop.map e.hom).naturality, },
    slice_lhs 2 3 { erw ed.ds, },
    slice_lhs 1 2 { erw ← (drop.map e.inv).naturality, },
    simpa only [assoc],
  end,
  ss := λ n i, begin
    slice_lhs 3 4 { erw ← (drop.map e.hom).naturality, },
    slice_lhs 2 3 { erw ed.ss, },
    slice_lhs 1 2 { erw ← (drop.map e.inv).naturality, },
    simpa only [assoc],
  end, }

/-- In the (pre)additive case, if an augmented simplicial object `X` has an extra
degeneracy, then the augmentation `alternating_face_map_complex.ε.app X` is a
homotopy equivalence of chain complexes. -/
def homotopy_equivalence [preadditive C] [limits.has_zero_object C]
  {X : simplicial_object.augmented C} (ed : extra_degeneracy X) :
  homotopy_equiv (algebraic_topology.alternating_face_map_complex.obj (drop.obj X))
    ((chain_complex.single₀ C).obj (point.obj X)) :=
{ hom := alternating_face_map_complex.ε.app X,
  inv := begin
    equiv_rw chain_complex.from_single₀_equiv _ _,
    exact ed.s',
  end,
  homotopy_hom_inv_id :=
  { hom := λ i j, begin
      by_cases i+1 = j,
      { exact (-ed.s i) ≫ eq_to_hom (by congr'), },
      { exact 0, },
    end,
    zero' := λ i j hij, begin
      split_ifs,
      { exfalso, exact hij h, },
      { simp only [eq_self_iff_true], },
    end,
    comm := λ i, begin
      cases i,
      { dsimp [chain_complex.to_single₀_equiv, chain_complex.from_single₀_equiv],
        simp only [preadditive.neg_comp, homotopy.d_next_zero_chain_complex,
          homotopy.prev_d_chain_complex, eq_self_iff_true, eq_to_hom_refl, category.comp_id,
          dite_eq_ite, if_true, zero_add],
        erw [chain_complex.of_d],
        simp only [alternating_face_map_complex.obj_d, fin.sum_univ_two,
          fin.coe_zero, pow_zero, one_zsmul, fin.coe_one, pow_one, neg_smul, add_assoc,
          preadditive.comp_add, preadditive.comp_neg, neg_add_rev, neg_neg],
        erw [ed.d₀s, ed.ds₀],
        convert (add_zero _).symm,
        apply neg_add_self, },
      { dsimp [chain_complex.to_single₀_equiv, chain_complex.from_single₀_equiv],
        simp only [limits.zero_comp, homotopy.d_next_succ_chain_complex, eq_self_iff_true,
          eq_to_hom_refl, category.comp_id, dite_eq_ite, if_true, homotopy.prev_d_chain_complex],
        erw [chain_complex.of_d, chain_complex.of_d],
        simp only [alternating_face_map_complex.obj_d, preadditive.comp_sum,
          preadditive.sum_comp, @fin.sum_univ_succ _ _ (i+2), fin.coe_zero, pow_zero,
          one_smul, preadditive.comp_add],
        have simplif : Π (a b c d : X.left _[i+1] ⟶ X.left _[i+1])
          (h₁ : a + c = 0) (h₂ : b + d = 0), 0 = a + (b+c) + d,
        { intros a b c d h₁ h₂,
          rw [add_comm b, ← add_assoc a, h₁, zero_add, h₂], },
        apply simplif,
        { simp only [← finset.sum_add_distrib],
          apply finset.sum_eq_zero,
          intros j hj,
          simp only [preadditive.zsmul_comp, preadditive.comp_zsmul, fin.coe_succ, pow_succ,
            preadditive.comp_neg, preadditive.neg_comp,
            neg_mul, one_mul, neg_smul, neg_neg],
          rw neg_add_eq_zero,
          congr' 1,
          exact (ed.ds i j).symm, },
        { erw [preadditive.neg_comp, ed.d₀s i.succ],
          apply neg_add_self, }, },
    end, },
  homotopy_inv_hom_id := homotopy.of_eq begin
    ext n,
    cases n,
    { exact ed.d₀s', },
    { tidy, },
  end, }

/-- The augmented Čech nerve associated to a split epimorphism has an extra degeneracy. -/
def for_cech_nerve_of_split_epi (f : arrow C)
  [∀ n : ℕ, has_wide_pullback f.right (λ i : ulift (fin (n+1)), f.left) (λ i, f.hom)]
  [split_epi f.hom] :
  extra_degeneracy (f.augmented_cech_nerve) :=
{ s' := section_ f.hom ≫ wide_pullback.lift f.hom (λ i, 𝟙 _) (λ i, by rw id_comp),
  s := λ n, wide_pullback.lift (wide_pullback.base _)
  begin
    rintro ⟨i⟩,
    by_cases i = 0,
    { exact wide_pullback.base _ ≫ section_ f.hom, },
    { exact wide_pullback.π _ (ulift.up ((σ 0).to_order_hom i)), },
  end
  begin
    intro j,
    cases j,
    dsimp,
    split_ifs,
    { subst h,
      simp only [assoc, split_epi.id, comp_id], },
    { simp only [wide_pullback.π_arrow], },
  end,
  d₀s' := by simp only [arrow.augmented_cech_nerve_hom_app, assoc,
    wide_pullback.lift_base, split_epi.id],
  ds₀ := begin
    ext; dsimp [simplicial_object.δ],
    { simp only [assoc, comp_id, wide_pullback.lift_π, ite_eq_left_iff],
      intro h,
      exfalso,
      apply h,
      fin_cases j,
      refl, },
    { simp only [assoc, split_epi.id, comp_id, wide_pullback.lift_base], },
  end,
  d₀s := λ n, begin
    ext; dsimp [simplicial_object.δ],
    { simp only [assoc, wide_pullback.lift_π, id_comp],
      split_ifs,
      { exfalso,
        exact j.down.succ_ne_zero h, },
      { congr,
        cases j,
        ext1,
        have eq : δ 0 ≫ σ 0 = 𝟙 [n] := δ_comp_σ_self,
        exact hom.congr_eval eq j, }, },
    { simp only [assoc, wide_pullback.lift_base, id_comp], },
  end,
  ds := λ n i, begin
    ext,
    { cases j,
      dsimp [simplicial_object.δ],
      simp only [assoc, wide_pullback.lift_π],
      by_cases hj : j = 0,
      { subst hj,
        split_ifs,
        { simp only [wide_pullback.lift_base_assoc], },
        { exfalso,
          apply h,
          apply fin.succ_above_below i.succ 0,
          simp only [fin.cast_succ_zero, fin.succ_pos], }, },
      { split_ifs with h₁,
        { exfalso,
          have h₂ : i.succ.succ_above j = 0 := h₁,
          by_cases h₃ : fin.cast_succ j < i.succ,
          { apply hj,
            ext,
            erw fin.succ_above_below _ _ h₃ at h₁,
            simpa only [fin.ext_iff] using h₁, },
          { simp only [not_lt] at h₃,
            rw fin.succ_above_above i.succ j h₃ at h₂,
            exact (fin.succ_ne_zero j) h₂, }, },
        { simp only [wide_pullback.lift_π],
          congr,
          cases nonzero_as_δ₀ hj with k hk,
          subst hk,
          have eq : δ 0 ≫ δ i.succ ≫ σ 0 = δ 0 ≫ σ 0 ≫ δ i,
          { slice_lhs 1 2 { rw δ_comp_δ (fin.zero_le i), },
            slice_lhs 2 3 { rw δ_comp_σ_self, },
            slice_rhs 1 2 { erw δ_comp_σ_self, },
            rw [id_comp, comp_id], },
          simpa only [coe_coe, fin.coe_coe_eq_self] using hom.congr_eval eq k, }, }, },
    { dsimp [simplicial_object.δ],
      simp only [assoc, wide_pullback.lift_base], },
  end,
  ss := λ n i, begin
    ext,
    { cases j,
      dsimp [simplicial_object.σ],
      simp only [assoc, wide_pullback.lift_π],
      by_cases hj : j = 0,
      { subst hj,
        split_ifs,
        { simp only [wide_pullback.lift_base_assoc], },
        { exfalso,
          apply h,
          refl, }, },
      { split_ifs with h₁,
        { exfalso,
          apply hj,
          ext,
          have h₂ : i.succ.pred_above j = 0 := h₁,
          dsimp [fin.pred_above] at h₂,
          split_ifs at h₂ with h₃,
          { rw [← fin.succ_pred j hj, h₂, fin.lt_iff_coe_lt_coe] at h₃,
            simpa only [fin.coe_cast_succ, fin.coe_succ, fin.succ_zero_eq_one,
              fin.coe_one, nat.lt_one_iff] using h₃, },
          { simpa only [fin.ext_iff] using h₂, }, },
        { simp only [wide_pullback.lift_π],
          congr' 1,
          ext1,
          cases nonzero_as_δ₀ hj with k hk,
          subst hk,
          have eq : δ 0 ≫ σ i.succ ≫ σ 0 = δ 0 ≫ σ 0 ≫ σ i,
          { slice_lhs 1 2 { erw δ_comp_σ_of_le (fin.cast_succ i).zero_le, },
            slice_lhs 2 3 { erw δ_comp_σ_self, },
            slice_rhs 1 2 { erw δ_comp_σ_self, },
            rw [id_comp, comp_id], },
          simpa only [coe_coe, fin.coe_coe_eq_self] using hom.congr_eval eq k, }, }, },
      { dsimp [simplicial_object.σ],
        simp only [assoc, wide_pullback.lift_base], },
  end, }

end extra_degeneracy

end algebraic_topology
