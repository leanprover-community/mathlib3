/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.alternating_face_map_complex
import algebraic_topology.cech_nerve
import algebra.homology.homotopy
import algebraic_topology.simplicial_set
import tactic.equiv_rw
import tactic.fin_cases

/-!

# Augmented simplicial objects with an extra degeneracy

In simplicial homotopy theory, in order to prove that the connected components
of a simplicial set `X` are contractible, it suffices to construct an extra
degeneracy as it is defined in *Simplicial Homotopy Theory* by Goerrs-Jardine p. 190.
It consists of a series of maps `π₀ X → X _[0]` and `X _[n] → X _[n+1]` which
behaves formally like an extra degeneracy `σ (-1)`. It can be thought as a datum
associated to the augmented simplicial set `X → π₀ X`.

In this file, we adapt this definition to the case of augmented
simplicial objects in any category.

## Main definitions

- the structure `extra_degeneracy X` for any `X : simplicial_object.augmented C`
- `extra_degeneracy.map`: extra degeneracies are preserved by the application of any
functor `C ⥤ D`
- `extra_degeneracy.for_cech_nerve_of_split_epi`: the augmented Čech nerve of a split
epimorphism has an extra degeneracy
- `extra_degeneracy.preadditive.homotopy_equivalence`: when the category `C` is
preadditive and has a zero object, and `X : simplicial_object.augmented C` has an extra
degeneracy, then the augmentation `alternating_face_map_complex.ε.app X` is a homotopy
equivalence of chain complexes

## References
* [Paul G. Goerss, John F. Jardine, *Simplical Homotopy Theory*][goerss-jardine-2009]

-/

noncomputable theory

open category_theory category_theory.category category_theory.limits
open category_theory.simplicial_object.augmented
open opposite simplex_category
open_locale simplicial

universes u

lemma fin.is_succ_of_ne_zero {n : ℕ} (x : fin (n+1)) (hx : x ≠ 0) :
  ∃ (y : fin n), x = y.succ :=
⟨x.pred hx, by simp only [fin.succ_pred]⟩

lemma fin.coe_cast_pred {n : ℕ} (x : fin (n+2)) (hx : x ≠ fin.last _) :
  (x.cast_pred : ℕ) = x :=
begin
  dsimp only [fin.cast_pred, fin.pred_above],
  split_ifs,
  { exfalso,
    simp only [fin.lt_iff_coe_lt_coe, fin.coe_cast_succ,
      fin.coe_last] at h,
    have h' := x.is_lt,
    apply hx,
    ext,
    dsimp,
    linarith, },
  { refl, },
end

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

/-- The augmented Čech nerve associated to a split epimorphism has an extra degeneracy. -/
def for_cech_nerve_of_split_epi (f : arrow C)
  [∀ n : ℕ, has_wide_pullback f.right (λ i : fin (n+1), f.left) (λ i, f.hom)]
  [split_epi f.hom] :
  extra_degeneracy (f.augmented_cech_nerve) :=
{ s' := section_ f.hom ≫ wide_pullback.lift f.hom (λ i, 𝟙 _) (λ i, by rw id_comp),
  s := λ n, wide_pullback.lift (wide_pullback.base _)
  begin
    rintro ⟨i⟩,
    by_cases i = 0,
    { exact wide_pullback.base _ ≫ section_ f.hom, },
    { exact wide_pullback.π _ ((σ (0 : fin (n+1))).to_order_hom i), },
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
    sorry,
  end,
  d₀s := begin
    sorry,
  end,
  ds := begin
    sorry,
  end,
  ss := begin
    sorry,
  end, }

/-
ds₀ := begin
    sorry,
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
  end, } -/

namespace preadditive

/-- In the (pre)additive case, if an augmented simplicial object `X` has an extra
degeneracy, then the augmentation `alternating_face_map_complex.ε.app X` is a
homotopy equivalence of chain complexes. -/
def homotopy_equivalence [preadditive C] [has_zero_object C]
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
      sorry,
/-      cases i,
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
        simp only [zero_comp, homotopy.d_next_succ_chain_complex, eq_self_iff_true,
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
          apply neg_add_self, }, },-/
    end, },
  homotopy_inv_hom_id := homotopy.of_eq begin
    ext n,
    cases n,
    { exact ed.d₀s', },
    { tidy, },
  end, }

end preadditive

end extra_degeneracy

end algebraic_topology

open algebraic_topology

namespace sSet

abbreviation augmented := simplicial_object.augmented (Type u)

@[simps]
def augmented_std_simplex (Δ : simplex_category) : sSet.augmented :=
{ left := yoneda.obj Δ,
  right := terminal _,
  hom := { app := λ Δ', terminal.from _, }, }

@[simp]
def shift {n : ℕ} {Δ : simplex_category} (f : [n] ⟶ Δ) : [n+1] ⟶ Δ :=
simplex_category.hom.mk
{ to_fun := λ x, begin
    by_cases x = 0,
    { exact 0, },
    { exact f.to_order_hom (x.pred h), },
  end,
  monotone' := λ x₁ x₂ ineq, begin
    dsimp,
    split_ifs with h₁ h₂ h₂,
    { refl, },
    { simp only [fin.zero_le], },
    { exfalso,
      apply h₁,
      rw [h₂] at ineq,
      apply le_antisymm,
      { exact ineq, },
      { simp only [fin.zero_le], }, },
    { apply f.to_order_hom.monotone,
      simpa only [fin.pred_le_pred_iff] using ineq, },
  end }

@[simp]
lemma fin.succ_pred_above_succ {n : ℕ} (x : fin n) (y : fin (n+1)) :
  x.succ.pred_above y.succ = (x.pred_above y).succ :=
begin
  obtain h₁ | h₂ := lt_or_le x.cast_succ y,
  { rw [fin.pred_above_above _ _ h₁, fin.succ_pred,
      fin.pred_above_above, fin.pred_succ],
    simpa only [fin.lt_iff_coe_lt_coe, fin.coe_cast_succ,
      fin.coe_succ, add_lt_add_iff_right] using h₁, },
  { cases n,
    { exfalso,
      exact not_lt_zero' x.is_lt, },
    { rw [fin.pred_above_below _ _ h₂, fin.pred_above_below],
      ext,
      have hx : (x : ℕ) < n+1 := x.is_lt,
      rw [fin.coe_succ, fin.coe_cast_pred, fin.coe_cast_pred, fin.coe_succ],
      { by_contra,
        simp only [h, fin.le_iff_coe_le_coe, fin.coe_last, fin.coe_cast_succ] at h₂,
        linarith, },
      { by_contra,
        rw [← fin.succ_le_succ_iff] at h₂,
        simp only [h, fin.le_iff_coe_le_coe, fin.coe_last, fin.coe_succ, fin.coe_cast_succ,
          add_le_add_iff_right] at h₂,
        change n+1 ≤ x at h₂,
        linarith, },
      { rw ← fin.succ_le_succ_iff at h₂,
        convert h₂,
        ext,
        simp only [fin.coe_cast_succ, fin.coe_succ], }, }, },
end

def augmented_std_simplex.extra_degeneracy (Δ : simplex_category) :
  extra_degeneracy (augmented_std_simplex Δ) :=
{ s' := λ x, simplex_category.hom.mk (order_hom.const _ 0),
  s := λ n f, shift f,
  d₀s' := by { dsimp, apply subsingleton.elim, },
  ds₀ := begin
    ext f x : 4,
    dsimp at x f ⊢,
    have eq : x = 0 := by { simp only [eq_iff_true_of_subsingleton], },
    subst eq,
    refl,
  end,
  d₀s := λ n, begin
    ext f x : 4,
    dsimp [simplicial_object.δ] at x f ⊢,
    split_ifs,
    { exfalso,
      exact fin.succ_ne_zero _ h, },
    { congr' 1,
      apply fin.pred_succ, },
  end,
  ds := λ n i, begin
    ext f x : 4,
    dsimp [simplicial_object.δ],
    split_ifs with h₁ h₂ h₂,
    { refl, },
    { exfalso,
      change fin.succ_above i.succ x = 0 at h₁,
      dsimp [fin.succ_above] at h₁,
      split_ifs at h₁,
      { apply h₂,
        simpa only [fin.ext_iff] using h₁, },
      { exact fin.succ_ne_zero x h₁, }, },
    { subst h₂,
      exfalso,
      apply h₁,
      change fin.succ_above i.succ 0 = 0,
      rw fin.succ_above_eq_zero_iff,
      apply fin.succ_ne_zero, },
    { cases x.is_succ_of_ne_zero h₂ with y hy,
      subst hy,
      congr' 1,
      simp only [fin.pred_succ],
      change (fin.succ_above i.succ y.succ).pred h₁ = fin.succ_above i y,
      apply fin.succ_injective,
      simp only [fin.succ_succ_above_succ, fin.pred_succ], },
  end,
  ss := λ n i, begin
    ext f x : 4,
    dsimp [simplicial_object.σ] at x f ⊢,
    split_ifs with h₁ h₂ h₂,
    { refl, },
    { exfalso,
      change i.succ.pred_above x = 0 at h₁,
      cases x.is_succ_of_ne_zero h₂ with y hy,
      subst hy,
      simp only [fin.succ_pred_above_succ] at h₁,
      exact fin.succ_ne_zero _ h₁, },
    { exfalso,
      rw h₂ at h₁,
      apply h₁,
      refl, },
    { congr' 1,
      cases x.is_succ_of_ne_zero h₂ with y hy,
      subst hy,
      simp only [fin.pred_succ],
      change (fin.pred_above i.succ y.succ).pred h₁ = fin.pred_above i y,
      apply fin.succ_injective,
      simp only [fin.succ_pred, fin.succ_pred_above_succ], },
  end, }

end sSet
