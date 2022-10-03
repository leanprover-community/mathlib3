/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.simplicial_set
import algebraic_topology.cech_nerve
import tactic.fin_cases

/-!

# Augmented simplicial objects with an extra degeneracy

In simplicial homotopy theory, in order to prove that the connected components
of a simplicial set `X` are contractible, it suffices to construct an extra
degeneracy as it is defined in *Simplicial Homotopy Theory* by Goerss-Jardine p. 190.
It consists of a series of maps `π₀ X → X _[0]` and `X _[n] → X _[n+1]` which
behave formally like an extra degeneracy `σ (-1)`. It can be thought as a datum
associated to the augmented simplicial set `X → π₀ X`.

In this file, we adapt this definition to the case of augmented
simplicial objects in any category.

## Main definitions

- the structure `extra_degeneracy X` for any `X : simplicial_object.augmented C`
- `extra_degeneracy.map`: extra degeneracies are preserved by the application of any
functor `C ⥤ D`
- `sSet.augmented.standard_simplex.extra_degeneracy`: the standard `n`-simplex has
an extra degeneracy

TODO @joelriou:
1) when the category `C` is preadditive and has a zero object, and
`X : simplicial_object.augmented C` has an extra degeneracy, then the augmentation
on the alternating face map complex of `X` is a homotopy equivalence of chain
complexes.

## References
* [Paul G. Goerss, John F. Jardine, *Simplical Homotopy Theory*][goerss-jardine-2009]

-/

open category_theory category_theory.category
open category_theory.simplicial_object.augmented
open opposite
open_locale simplicial

namespace simplicial_object

namespace augmented

variables {C : Type*} [category C]

/-- The datum of an extra degeneracy is a technical condition on
augmented simplicial objects. The morphisms `s'` and `s n` of the
structure formally behave like extra degeneracies `σ (-1)`. -/
@[ext]
structure extra_degeneracy (X : simplicial_object.augmented C) :=
(s' : point.obj X ⟶ (drop.obj X) _[0])
(s : Π (n : ℕ), (drop.obj X) _[n] ⟶ (drop.obj X) _[n+1])
(s'_comp_ε' : s' ≫ X.hom.app (op [0]) = 𝟙 _)
(s₀_comp_δ₁' : s 0 ≫ (drop.obj X).δ 1 = X.hom.app (op [0]) ≫ s')
(s_comp_δ₀' : Π (n : ℕ), s n ≫ (drop.obj X).δ 0 = 𝟙 _)
(s_comp_δ' : Π (n : ℕ) (i : fin (n+2)), s (n+1) ≫ (drop.obj X).δ i.succ =
  (drop.obj X).δ i ≫ s n)
(s_comp_σ' : Π (n : ℕ) (i : fin (n+1)), s n ≫ (drop.obj X).σ i.succ =
  (drop.obj X).σ i ≫ s (n+1))

namespace extra_degeneracy

restate_axiom s'_comp_ε'
restate_axiom s₀_comp_δ₁'
restate_axiom s_comp_δ₀'
restate_axiom s_comp_δ'
restate_axiom s_comp_σ'
attribute [reassoc] s'_comp_ε s₀_comp_δ₁ s_comp_δ₀ s_comp_δ s_comp_σ
attribute [simp] s'_comp_ε s_comp_δ₀

/-- If `ed` is an extra degeneracy for `X : simplicial_object.augmented C` and
`F : C ⥤ D` is a functor, then `ed.map F` is an extra degeneracy for the
augmented simplical object in `D` obtained by applying `F` to `X`. -/
def map {D : Type*} [category D]
  {X : simplicial_object.augmented C} (ed : extra_degeneracy X) (F : C ⥤ D) :
  extra_degeneracy (((whiskering _ _).obj F).obj X) :=
{ s' := F.map ed.s',
  s := λ n, F.map (ed.s n),
  s'_comp_ε' := by { dsimp, erw [comp_id, ← F.map_comp, ed.s'_comp_ε, F.map_id], },
  s₀_comp_δ₁' := by { dsimp, erw [comp_id, ← F.map_comp, ← F.map_comp, ed.s₀_comp_δ₁], },
  s_comp_δ₀' := λ n, by { dsimp, erw [← F.map_comp, ed.s_comp_δ₀, F.map_id], },
  s_comp_δ' := λ n i, by { dsimp, erw [← F.map_comp, ← F.map_comp, ed.s_comp_δ], refl, },
  s_comp_σ' := λ n i, by { dsimp, erw [← F.map_comp, ← F.map_comp, ed.s_comp_σ], refl, }, }

/-- If `X` and `Y` are isomorphic augmented simplicial objects, then an extra
degeneracy for `X` gives also an extra degeneracy for `Y` -/
def of_iso {X Y : simplicial_object.augmented C} (e : X ≅ Y) (ed : extra_degeneracy X) :
  extra_degeneracy Y :=
{ s' := (point.map_iso e).inv ≫ ed.s' ≫ (drop.map_iso e).hom.app (op [0]),
  s := λ n, (drop.map_iso e).inv.app (op [n]) ≫ ed.s n ≫ (drop.map_iso e).hom.app (op [n+1]),
  s'_comp_ε' := by simpa only [functor.map_iso, assoc, w₀, ed.s'_comp_ε_assoc]
    using (point.map_iso e).inv_hom_id,
  s₀_comp_δ₁' := begin
    have h := w₀ e.inv,
    dsimp at h ⊢,
    simp only [assoc, ← simplicial_object.δ_naturality, ed.s₀_comp_δ₁_assoc, reassoc_of h],
  end,
  s_comp_δ₀' := λ n, begin
    have h := ed.s_comp_δ₀',
    dsimp at ⊢ h,
    simpa only [assoc, ← simplicial_object.δ_naturality, reassoc_of h]
      using congr_app (drop.map_iso e).inv_hom_id (op [n]),
  end,
  s_comp_δ' := λ n i, begin
    have h := ed.s_comp_δ' n i,
    dsimp at ⊢ h,
    simp only [assoc, ← simplicial_object.δ_naturality, reassoc_of h,
      ← simplicial_object.δ_naturality_assoc],
  end,
  s_comp_σ' := λ n i, begin
    have h := ed.s_comp_σ' n i,
    dsimp at ⊢ h,
    simp only [assoc, ← simplicial_object.σ_naturality, reassoc_of h,
      ← simplicial_object.σ_naturality_assoc],
  end,}

end extra_degeneracy

end augmented

end simplicial_object

namespace sSet

namespace augmented

namespace standard_simplex

/-- When `[has_zero X]`, the shift of a map `f : fin n → X`
is a map `fin (n+1) → X` which sends `0` to `0` and `i.succ` to `f i`. -/
def shift_fun {n : ℕ} {X : Type*} [has_zero X] (f : fin n → X) (i : fin (n+1)) : X :=
dite (i = 0) (λ h, 0) (λ h, f (i.pred h))

@[simp]
lemma shift_fun_0 {n : ℕ} {X : Type*} [has_zero X] (f : fin n → X) : shift_fun f 0 = 0 := rfl

@[simp]
lemma shift_fun_succ {n : ℕ} {X : Type*} [has_zero X] (f : fin n → X)
  (i : fin n) : shift_fun f i.succ = f i :=
begin
  dsimp [shift_fun],
  split_ifs,
  { exfalso,
    simpa only [fin.ext_iff, fin.coe_succ] using h, },
  { simp only [fin.pred_succ], },
end

/-- The shift of a morphism `f : [n] → Δ` in `simplex_category` corresponds to
the monotone map which sends `0` to `0` and `i.succ` to `f.to_order_hom i`. -/
@[simp]
def shift {n : ℕ} {Δ : simplex_category} (f : [n] ⟶ Δ) : [n+1] ⟶ Δ := simplex_category.hom.mk
{ to_fun := shift_fun f.to_order_hom,
  monotone' := λ i₁ i₂ hi, begin
    by_cases h₁ : i₁ = 0,
    { subst h₁,
      simp only [shift_fun_0, fin.zero_le], },
    { have h₂ : i₂ ≠ 0 := by { intro h₂, subst h₂, exact h₁ (le_antisymm hi (fin.zero_le _)), },
      cases fin.eq_succ_of_ne_zero h₁ with j₁ hj₁,
      cases fin.eq_succ_of_ne_zero h₂ with j₂ hj₂,
      substs hj₁ hj₂,
      simpa only [shift_fun_succ] using f.to_order_hom.monotone (fin.succ_le_succ_iff.mp hi), },
  end, }

/-- The obvious extra degeneracy on the standard simplex. -/
@[protected]
def extra_degeneracy (Δ : simplex_category) :
  simplicial_object.augmented.extra_degeneracy (standard_simplex.obj Δ) :=
{ s' := λ x, simplex_category.hom.mk (order_hom.const _ 0),
  s := λ n f, shift f,
  s'_comp_ε' := by { ext1 j, fin_cases j, },
  s₀_comp_δ₁' := by { ext x j, fin_cases j, refl, },
  s_comp_δ₀' := λ n, begin
    ext φ i : 4,
    dsimp [simplicial_object.δ, simplex_category.δ, sSet.standard_simplex],
    simp only [shift_fun_succ],
  end,
  s_comp_δ' := λ n i, begin
    ext φ j : 4,
    dsimp [simplicial_object.δ, simplex_category.δ, sSet.standard_simplex],
    by_cases j = 0,
    { subst h,
      simp only [fin.succ_succ_above_zero, shift_fun_0], },
    { cases fin.eq_succ_of_ne_zero h with k hk,
      subst hk,
      simp only [fin.succ_succ_above_succ, shift_fun_succ], },
  end,
  s_comp_σ' := λ n i, begin
    ext φ j : 4,
    dsimp [simplicial_object.σ, simplex_category.σ, sSet.standard_simplex],
    by_cases j = 0,
    { subst h,
      simpa only [shift_fun_0] using shift_fun_0 φ.to_order_hom, },
    { cases fin.eq_succ_of_ne_zero h with k hk,
      subst hk,
      simp only [fin.succ_pred_above_succ, shift_fun_succ], },
  end, }

instance nonempty_extra_degeneracy_standard_simplex (Δ : simplex_category) :
  nonempty (simplicial_object.augmented.extra_degeneracy (standard_simplex.obj Δ)) :=
⟨standard_simplex.extra_degeneracy Δ⟩

end standard_simplex

end augmented

end sSet

namespace category_theory

open limits

namespace arrow

namespace augmented_cech_nerve

variables {C : Type*} [category C] (f : arrow C)
  [∀ n : ℕ, has_wide_pullback f.right (λ i : fin (n+1), f.left) (λ i, f.hom)]
  (S : split_epi f.hom)

include S

/-- The extra degeneracy map on the Čech nerve of a split epi. It is
given on the `0`-projection by the given section of the split epi,
and by shifting the indices on the other projections. -/
noncomputable def extra_degeneracy.s (n : ℕ) :
  f.cech_nerve.obj (op [n]) ⟶ f.cech_nerve.obj (op [n + 1]) :=
wide_pullback.lift (wide_pullback.base _)
  (λ i, dite (i = 0) (λ h, wide_pullback.base _ ≫ S.section_)
    (λ h, wide_pullback.π _ (i.pred h)))
  (λ i, begin
    split_ifs,
    { subst h,
      simp only [assoc, split_epi.id, comp_id], },
    { simp only [wide_pullback.π_arrow], },
  end)

@[simp]
lemma extra_degeneracy.s_comp_π_0 (n : ℕ) :
  extra_degeneracy.s f S n ≫ wide_pullback.π _ 0 = wide_pullback.base _ ≫ S.section_ :=
by { dsimp [extra_degeneracy.s], simpa only [wide_pullback.lift_π], }

@[simp]
lemma extra_degeneracy.s_comp_π_succ (n : ℕ) (i : fin (n+1)) :
  extra_degeneracy.s f S n ≫ wide_pullback.π _ i.succ = wide_pullback.π _ i :=
begin
  dsimp [extra_degeneracy.s],
  simp only [wide_pullback.lift_π],
  split_ifs,
  { exfalso,
    simpa only [fin.ext_iff, fin.coe_succ, fin.coe_zero, nat.succ_ne_zero] using h, },
  { congr,
    apply fin.pred_succ, },
end

@[simp]
lemma extra_degeneracy.s_comp_base (n : ℕ) :
  extra_degeneracy.s f S n ≫ wide_pullback.base _ = wide_pullback.base _ :=
by apply wide_pullback.lift_base

/-- The augmented Čech nerve associated to a split epimorphism has an extra degeneracy. -/
noncomputable def extra_degeneracy :
  simplicial_object.augmented.extra_degeneracy f.augmented_cech_nerve :=
{ s' := S.section_ ≫ wide_pullback.lift f.hom (λ i, 𝟙 _) (λ i, by rw id_comp),
  s := λ n, extra_degeneracy.s f S n,
  s'_comp_ε' :=
    by simp only [augmented_cech_nerve_hom_app, assoc, wide_pullback.lift_base, split_epi.id],
  s₀_comp_δ₁' := begin
    dsimp [cech_nerve, simplicial_object.δ, simplex_category.δ],
    ext j,
    { fin_cases j,
      simpa only [assoc, wide_pullback.lift_π, comp_id] using extra_degeneracy.s_comp_π_0 f S 0, },
    { simpa only [assoc, wide_pullback.lift_base, split_epi.id, comp_id]
        using extra_degeneracy.s_comp_base f S 0, },
  end,
  s_comp_δ₀' := λ n, begin
    dsimp [cech_nerve, simplicial_object.δ, simplex_category.δ],
    ext j,
    { simpa only [assoc, wide_pullback.lift_π, id_comp]
        using extra_degeneracy.s_comp_π_succ f S n j, },
    { simpa only [assoc, wide_pullback.lift_base, id_comp]
        using extra_degeneracy.s_comp_base f S n, },
  end,
  s_comp_δ' := λ n i, begin
    dsimp [cech_nerve, simplicial_object.δ, simplex_category.δ],
    ext j,
    { simp only [assoc, wide_pullback.lift_π],
      by_cases j = 0,
      { subst h,
        erw [fin.succ_succ_above_zero, extra_degeneracy.s_comp_π_0, extra_degeneracy.s_comp_π_0],
        dsimp,
        simp only [wide_pullback.lift_base_assoc], },
      { cases fin.eq_succ_of_ne_zero h with k hk,
        subst hk,
        erw [fin.succ_succ_above_succ, extra_degeneracy.s_comp_π_succ,
          extra_degeneracy.s_comp_π_succ],
        dsimp,
        simp only [wide_pullback.lift_π], }, },
    { simp only [assoc, wide_pullback.lift_base],
      erw [extra_degeneracy.s_comp_base, extra_degeneracy.s_comp_base],
      dsimp,
      simp only [wide_pullback.lift_base], },
  end,
  s_comp_σ' := λ n i, begin
    dsimp [cech_nerve, simplicial_object.σ, simplex_category.σ],
    ext j,
    { simp only [assoc, wide_pullback.lift_π],
      by_cases j = 0,
      { subst h,
        erw [extra_degeneracy.s_comp_π_0, extra_degeneracy.s_comp_π_0],
        dsimp,
        simp only [wide_pullback.lift_base_assoc], },
      { cases fin.eq_succ_of_ne_zero h with k hk,
        subst hk,
        erw [fin.succ_pred_above_succ, extra_degeneracy.s_comp_π_succ,
          extra_degeneracy.s_comp_π_succ],
        dsimp,
        simp only [wide_pullback.lift_π], }, },
    { simp only [assoc, wide_pullback.lift_base],
      erw [extra_degeneracy.s_comp_base, extra_degeneracy.s_comp_base],
      dsimp,
      simp only [wide_pullback.lift_base], },
  end, }

end augmented_cech_nerve

end arrow

end category_theory
