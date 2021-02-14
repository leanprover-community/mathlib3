/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.isomorphism_classes
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

section
variables {V} [has_zero_object V]
local attribute [instance] has_zero_object.has_zero

/--
A `ℤ`-indexed chain complex `is_connective` if all objects in negative degrees are 0.
-/
def is_connective (C : chain_complex V) : Prop := ∀ i : ℤ, i < 0 → is_isomorphic (C.X i) 0

/-- If an object `X` is isomorphic to 0, there's no need to use choice to construct
an explicit isomorphism: the zero morphism suffices. -/
def iso_of_is_isomorphic_zero {X : V} (P : is_isomorphic X 0) : X ≅ 0 :=
{ hom := 0,
  inv := 0,
  hom_inv_id' :=
  begin
    casesI P,
    rw ←P.hom_inv_id,
    rw ←category.id_comp P.inv,
    rw (show 𝟙 (0 : V) = 0, by simp),
    simp,
  end,
  inv_hom_id' := by simp, }

end

structure connective_chain_complex :=
(X : ℕ → V)
(d : Π n : ℕ, X (n+1) ⟶ X n)
(d_squared' : ∀ n, d (n+1) ≫ d n = 0 . obviously)

restate_axiom connective_chain_complex.d_squared'
attribute [simp, reassoc] connective_chain_complex.d_squared

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

@[simp] lemma id_f (C : connective_chain_complex V) (n : ℕ) : hom.f (𝟙 C) n = 𝟙 (C.X n) := rfl
@[simp] lemma comp_f {C D E : connective_chain_complex V} (f : C ⟶ D) (g : D ⟶ E) (n : ℕ) :
  hom.f (f ≫ g) n = f.f n ≫ g.f n := rfl

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

@[simp] lemma id_chain_complex_subtype_f_apply {Z : chain_complex V → Prop}
  (C : { C : chain_complex V // Z C }) (i : ℤ) :
  differential_object.hom.f (𝟙 C) i = 𝟙 (C.val.X i) :=
rfl

@[simp] lemma comp_chain_complex_subtype_f_apply {Z : chain_complex V → Prop}
  {C D E : { C : chain_complex V // Z C }} (f : C ⟶ D) (g : D ⟶ E) (i : ℤ) :
  differential_object.hom.f (f ≫ g) i = f.f i ≫ g.f i :=
rfl

end to_chain_complex

open to_chain_complex

@[simp] lemma int.add_neg_one (i : ℤ) : i + -1 = i - 1 := rfl

@[simp] lemma int.coe_nat_succ_pos (n : ℕ) : 0 < (n : ℤ) + 1 := sorry

@[simp] lemma int.neg_succ_not_nonneg (n : ℕ) : 0 ≤ -[1+ n] ↔ false :=
by { simp only [not_le, iff_false], exact int.neg_succ_lt_zero n, }

@[simp] lemma int.neg_succ_sub_one (n : ℕ) : -[1+ n] - 1 = -[1+ (n+1)] := rfl

lemma int.pred_to_nat (i : ℤ) : (i - 1).to_nat = i.to_nat - 1 :=
begin
  cases i,
  { cases i,
    { simp, refl, },
    { simp, }, },
  { simp only [int.neg_succ_sub_one, int.to_nat], }
end

variables (V)

/-- Turn a `ℕ`-indexed chain complex into a `ℤ`-indexed chain complex. -/
@[simps]
def to_chain_complex : connective_chain_complex V ⥤ { C : chain_complex V // is_connective C } :=
{ obj := λ C,
  { val :=
    { X := X_ℤ C,
      d := d_ℤ C,
      d_squared' := by { ext i, exact to_chain_complex.d_squared C i } },
    property := λ i h, ⟨by { dsimp [X_ℤ], rw [if_neg], simpa using h, }⟩, },
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
      { by_cases h' : 0 ≤ i - 1,
        { dsimp [X_ℤ, d_ℤ],
          have h'' : 0 < i := by linarith,
          simp only [dif_pos h, dif_pos h', dif_pos h''],
          simp,
          have w₁ : i.to_nat = i.to_nat - 1 + 1 :=
            (nat.succ_pred_eq_of_pos (by simp [h''] : 0 < i.to_nat)).symm,
          slice_rhs 2 3 { erw ←eq_to_hom_f f w₁, },
          slice_rhs 3 4 { rw f.comm, },
          slice_lhs 3 4 { erw eq_to_hom_f f (int.pred_to_nat _).symm },
          simp only [category.assoc, eq_to_hom_trans, eq_to_hom_trans_assoc],
          refl, },
        { rw [dif_pos h, dif_neg h'],
          have h'' : i = 0 := by linarith,
          subst h'',
          simp, } },
      { have h' : ¬ 0 ≤ i - 1 := by linarith,
        rw [dif_neg h, dif_neg h'],
        simp, }
    end, },
    map_id' := λ C,
    begin
      ext i, dsimp [X_ℤ],
      split_ifs,
      { simp, },
      { erw [if_neg h], simp, },
    end,
    map_comp' := λ C D E f g,
    begin
      ext i, dsimp [X_ℤ],
      split_ifs,
      { simp, },
      { erw [if_neg h], simp, },
    end }.

/--
Turn a `ℤ`-indexed chain complex supported in non-negative degrees
into a `ℕ`-indexed chain complex.
-/
@[simps]
def to_connective_chain_complex :
  { C : chain_complex V // is_connective C } ⥤ connective_chain_complex V :=
{ obj := λ C,
  { X := λ n, C.val.X n,
    d := λ n, eq_to_hom (congr_arg C.val.X (by simp)) ≫ C.val.d (n+1) ≫
      eq_to_hom (congr_arg C.val.X (by simp)),
    d_squared' := λ n,
    begin
      simp only [category.id_comp, category.assoc, eq_to_hom_refl],
      slice_lhs 2 3 { erw homological_complex.eq_to_hom_d, },
      slice_lhs 1 2 { erw homological_complex.d_squared, },
      simp only [limits.zero_comp],
    end, },
  map := λ C D f,
  { f := λ n, f.f n,
    comm' := λ n,
    begin
      dsimp, simp,
      slice_rhs 2 3 { erw homological_complex.eq_to_hom_f, },
      erw homological_complex.comm_at_assoc f,
      refl,
     end, }, }.

def equivalence_unit_iso :
  𝟭 (connective_chain_complex V) ≅ to_chain_complex V ⋙ to_connective_chain_complex V :=
{ hom := { app := λ C,
  { f := λ n, 𝟙 _, comm' := λ n, by { dsimp [d_ℤ], simp, refl, }, }, },
  inv := { app := λ C,
  { f := λ n, 𝟙 _, comm' := λ n, by { dsimp [d_ℤ], simp, refl, }, }, }, }

def equivalence_counit_iso :
  to_connective_chain_complex V ⋙ to_chain_complex V ≅ 𝟭 _ :=
{ hom := { app := λ C,
  { f := λ i,
    begin
      dsimp [X_ℤ],
      split_ifs,
      { refine eq_to_hom (congr_arg C.val.X _),
        simp [h], },
      { simp at h,
        exact (iso_of_is_isomorphic_zero (C.property i h)).inv, },
    end,
    comm' :=
    begin
      ext i, dsimp [d_ℤ],
    end, }, },
  inv := sorry, }

def equivalence : connective_chain_complex V ≌ { C : chain_complex V // is_connective C } :=
{ functor := to_chain_complex V,
  inverse := to_connective_chain_complex V,
  unit_iso := equivalence_unit_iso V,
  counit_iso := sorry, }

end connective_chain_complex
