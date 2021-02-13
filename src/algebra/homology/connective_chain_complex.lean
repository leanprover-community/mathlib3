/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.chain_complex
import tactic.linarith

/-!
## Connective chain complexes

Often we want to work with `ℕ`-indexed chain complexes.
While it is possible to work with `ℤ`-indexed chain complexes which are zero in negative degrees
(typically called 'connective'), sometimes it is more convenient to actually index by `ℕ`.

To this end, we define `connective_chain_complex V`, and aim to prove an equivalence
`connective_chain_complex V ≌ { C : chain_complex V // is_connective C}`
(where `is_connective` asserts that the complex is zero in negative degrees).

Note that in `chain_complex V`, `C.d i : C.X i ⟶ C.X (i-1)`,
while in `connective_chain_complex V`, we have `C.d i : C.X (i+1) ⟶ C.X i`.
This makes `connective_chain_complex V` nicer to work with,
but adds to the tedium (lots of monus wrangling) when setting up the equivalence.
-/

universes v u

open category_theory
open category_theory.limits

variables (V : Type u) [category.{v} V]
variables [has_zero_morphisms V]

structure connective_chain_complex :=
(X : ℕ → V)
(d : Π n : ℕ, X (n+1) ⟶ X n)
(d_squared' : ∀ n, d (n+1) ≫ d n = 0)

namespace connective_chain_complex

variables {V}

lemma eq_to_hom_d (C : connective_chain_complex V) {n m : ℕ} (h : n = m) :
  eq_to_hom (congr_arg C.X (congr_arg nat.succ h)) ≫ C.d m = C.d n ≫ eq_to_hom (congr_arg C.X h) :=
begin
  induction h,
  simp,
end

@[ext]
structure hom (C D : connective_chain_complex V) :=
(f : Π n, C.X n ⟶ D.X n)
(comm' : ∀ n, f (n+1) ≫ D.d n = C.d n ≫ f n . obviously)

restate_axiom hom.comm'
attribute [simp, reassoc] hom.comm

namespace hom

@[simps]
def id (C : connective_chain_complex V) : hom C C :=
{ f := λ n, 𝟙 (C.X n) }

@[simps]
def comp {C D E : connective_chain_complex V} (f : hom C D) (g : hom D E) : hom C E :=
{ f := λ n, f.f n ≫ g.f n, }

end hom

instance : category (connective_chain_complex V) :=
{ hom := hom,
  id := hom.id,
  comp := λ X Y Z f g, hom.comp f g, }

lemma eq_to_hom_f {C D : connective_chain_complex V} (f : C ⟶ D) {n m : ℕ} (h : n = m) :
  eq_to_hom (congr_arg C.X h) ≫ f.f m = f.f n ≫ eq_to_hom (congr_arg D.X h) :=
begin
  induction h,
  simp
end

variables [has_zero_object V]
local attribute [instance] has_zero_object.has_zero

/-! Auxiliary constructions for the `to_chain_complex` functor. -/
namespace to_chain_complex

def X_ℤ (C : connective_chain_complex V) (i : ℤ) : V :=
if 0 ≤ i then C.X i.to_nat else 0

@[norm_cast] lemma int.coe_pred_of_pos (n : ℕ) (h : 0 < n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 :=
by { cases n, cases h, simp, }

@[simp]
lemma int.of_nat_to_nat_pred_of_pos {i : ℤ} (h : 0 < i) : int.of_nat (i.to_nat - 1) = i - 1 :=
by simp [h, le_of_lt h] with push_cast

@[simp]
lemma int.of_nat_to_nat_pred_succ_of_pos {i : ℤ} (h : 0 < i) : int.of_nat (i.to_nat - 1) + 1 = i :=
by simp [h]

def d_ℤ (C : connective_chain_complex V) (i : ℤ) : (X_ℤ C) i ⟶ (X_ℤ C) (i-1) :=
if h : 0 < i then
  eq_to_hom (congr_arg (X_ℤ C) (int.of_nat_to_nat_pred_succ_of_pos h).symm) ≫
    C.d _ ≫
    eq_to_hom (congr_arg (X_ℤ C) (int.of_nat_to_nat_pred_of_pos h))
else 0

@[simp] lemma d_ℤ_0 (C : connective_chain_complex V) : d_ℤ C 0 = 0 := rfl

@[simp] lemma d_ℤ_neg (C : connective_chain_complex V) (n : ℕ) : d_ℤ C -[1+ n] = 0 :=
begin
  dsimp [d_ℤ],
  rw [dif_neg],
  dec_trivial,
end

lemma d_squared (C : connective_chain_complex V) (i : ℤ) :
  d_ℤ C i ≫ d_ℤ C (i + -1) = 0 :=
begin
  rcases i with n|n,
  -- 0 ≤ i, so i = of_nat n
  { dsimp [d_ℤ], cases n,
    { -- i = 0,
      simp, },
    { simp, -- nonterminal simp; replacing with `simp?` proposal breaks the proof later.
      cases n,
      { -- i = 1
        simp, },
      { -- 2 ≤ i, the interesting case
        simp,
        have w : n = ((n : ℤ) + 1 + 1 + -1).to_nat - 1 := by simp,
        slice_lhs 2 3 { erw C.eq_to_hom_d w },
        slice_lhs 1 2 { erw C.d_squared', },
        simp, }, }, },
  -- i < 0
  { simp, },
end

end to_chain_complex

open to_chain_complex

example (i : ℤ) (h : 0 ≤ i) : i.to_nat - 1 = (i + -1).to_nat :=
sorry

def to_chain_complex : connective_chain_complex V ⥤ chain_complex V :=
{ obj := λ C,
  { X := X_ℤ C,
    d := d_ℤ C,
    d_squared' := by { ext i, exact d_squared C i } },
  map := λ C D f,
  { f := λ i, if h : 0 ≤ i then
    begin
      dsimp [X_ℤ],
      exact eq_to_hom (by rw [if_pos h]) ≫ f.f i.to_nat ≫ eq_to_hom (by rw [if_pos h]),
    end else 0,
    comm' :=
    begin
      ext i, dsimp,
      by_cases h : 0 ≤ i,
      { by_cases h' : 0 ≤ i + -1,
        { dsimp [X_ℤ, d_ℤ],
          have h'' : 0 < i := by linarith,
          simp only [dif_pos h, dif_pos h', dif_pos h''],
          simp,
          have w₁ : i.to_nat = i.to_nat - 1 + 1 :=
            (nat.succ_pred_eq_of_pos (by simp [h''] : 0 < i.to_nat)).symm,
          slice_rhs 2 3 { erw ←eq_to_hom_f f w₁, },
          slice_rhs 3 4 { rw f.comm, },
          have w₂ : i.to_nat - 1 = (i + -1).to_nat := sorry,
          slice_lhs 3 4 { erw eq_to_hom_f f w₂ },
          simp only [category.assoc, eq_to_hom_trans, eq_to_hom_trans_assoc],
          refl, },
        { rw [dif_pos h, dif_neg h'],
          have h'' : i = 0 := by linarith,
          subst h'',
          simp, } },
      { have h' : ¬ 0 ≤ i + -1 := by linarith,
        rw [dif_neg h, dif_neg h'],
        simp, }
    end, }, }

end connective_chain_complex
