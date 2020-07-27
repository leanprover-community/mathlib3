/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import order.category.NonemptyFinLinOrd.basic

import tactic.linarith

/-! # The simplex category

TODO: explain that this shouldn't be used by default,
but it gives access to a useful constructor.

-/

universe variables u

open category_theory

/-- The simplex category:
* objects are natural numbers `n : ℕ`
* morphisms are monotone functions `fin (m+1) → fin (n+1)`
-/
def simplex_category := ℕ

namespace simplex_category

instance : small_category simplex_category :=
{ hom := λ m n, preorder_hom (fin (m+1)) (fin (n+1)),
  id := λ m, preorder_hom.id,
  comp := λ _ _ _ f g, preorder_hom.comp g f, }

section generators
/-!
## Generating maps for the simplex category

TODO: prove the remaining simplicial identities
TODO: prove that these generate the category
-/

def δ {n} (i : fin (n+2)) :
  @has_hom.hom simplex_category _ n (n+1 : ℕ) :=
{ to_fun := fin.succ_above i,
  monotone :=
  begin
    intros a b H,
    change a.val ≤ b.val at H,
    dsimp [fin.succ_above],
    split_ifs with ha hb hb,
    all_goals
    { simp [fin.le_iff_val_le_val, nat.succ_eq_add_one],
      linarith },
  end }

/-- The i-th degeneracy map from [n+1] to [n] -/
def σ {n} (i : fin (n+1)) :
  @has_hom.hom simplex_category _ (n+1 : ℕ) n :=
{ to_fun := λ a, if h : a.val ≤ i.val
  then a.cast_lt (lt_of_le_of_lt h i.is_lt)
  else ⟨a.val.pred,
    (nat.sub_lt_right_iff_lt_add (lt_of_le_of_lt i.val.zero_le (not_le.mp h))).mpr a.is_lt⟩,
  monotone := λ a b (H : a.val ≤ b.val),
  begin
    dsimp,
    split_ifs with ha hb,
    all_goals
    { simp [fin.le_iff_val_le_val], try { linarith }, },
    { simp at hb,
      have hb' : i.val ≤ nat.pred b.val,
      { rw ←nat.pred_succ i.val,
        exact nat.pred_le_pred hb },
      exact nat.le_trans ha hb' },
    { exact nat.pred_le_pred H },
  end }

/-- The first simplicial identity -/
lemma δ_comp_δ {n} {i j : fin (n+2)} (H : i ≤ j) :
  δ i ≫ δ j.succ = δ j ≫ δ i.cast_succ :=
begin
  change i.val ≤ j.val at H,
  ext k,
  show (j.succ.succ_above (i.succ_above k)).val = (i.cast_succ.succ_above (j.succ_above k)).val,
  dsimp [fin.succ_above],
  split_ifs; { simp [nat.succ_eq_add_one] at *, try { linarith } },
end

end generators

section skeleton

/-- The functor that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
def skeletal_functor :
  simplex_category ⥤ NonemptyFinLinOrd.{u} :=
{ obj := λ n, NonemptyFinLinOrd.of $ ulift (fin (n+1)),
  map := λ m n f, ⟨λ i, ⟨f i.down⟩, λ ⟨i⟩ ⟨j⟩ h, show f i ≤ f j, from f.monotone h⟩, }

namespace skeletal_functor

instance full : full.{0 u 0 (u+1)} skeletal_functor.{u} :=
{ preimage := λ m n f, ⟨λ i, (f ⟨i⟩).down, λ i j h, f.monotone h⟩,
  witness' := by { intros m n f, dsimp at *, ext1 ⟨i⟩, ext1, refl } }

instance : faithful skeletal_functor.{u} :=
{ map_injective' := λ m n f g h,
  begin
    ext1 i, apply equiv.ulift.symm.injective,
    show skeletal_functor.map f ⟨i⟩ = skeletal_functor.map g ⟨i⟩,
    rw h,
  end }

noncomputable instance : ess_surj skeletal_functor.{u} :=
{ obj_preimage := λ X, (fintype.card X - 1 : ℕ),
  iso' :=
  begin
    intro X,
    have aux : fintype.card X = fintype.card X - 1 + 1,
    { exact (nat.succ_pred_eq_of_pos $ fintype.card_pos_iff.mpr ⟨⊥⟩).symm, },
    let f := mono_equiv_of_fin X aux,
    have hf := (finset.mono_of_fin_strict_mono finset.univ aux),
    refine
    { hom := ⟨λ i, f i.down, _⟩,
      inv := ⟨λ i, ⟨f.symm i⟩, _⟩,
      hom_inv_id' := _,
      inv_hom_id' := _ },
    { rintro ⟨i⟩ ⟨j⟩ h, show f i ≤ f j, exact hf.monotone h, },
    { intros i j h, show f.symm i ≤ f.symm j, rw ← hf.le_iff_le,
      show f (f.symm i) ≤ f (f.symm j), simpa only [equiv.apply_symm_apply], },
    { ext1 ⟨i⟩, ext1, exact f.symm_apply_apply i },
    { ext1 i, exact f.apply_symm_apply i },
  end }

noncomputable instance is_equivalence : is_equivalence skeletal_functor.{u} :=
equivalence.equivalence_of_fully_faithfully_ess_surj skeletal_functor

end skeletal_functor

/-- The equivalence that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
noncomputable def skeletal_equivalence :
  simplex_category ≌ NonemptyFinLinOrd.{u} :=
functor.as_equivalence skeletal_functor.{u}

end skeleton

end simplex_category
