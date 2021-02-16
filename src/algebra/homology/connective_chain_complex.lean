/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.chain_complex
import tactic.linarith

/-!
## Connective chain complexes

Our definition of `chain_complex V`, as `differential_object (graded_object_with_shift (-1 : ℤ) V)`,
is intrinsically an `ℤ`-indexed object. (The formulation of `graded_object_with_shift` requires
that the grading is by an abelian group.)

Often, however, one encounters chain complexes in the wild which are naturally `ℕ`-indexed.
(e.g. when working with simplicial topology or simplicial objects).

In this file we provide an independent formulation of such chain complexes, as
```
structure connective_chain_complex :=
(X : ℕ → V)
(d : Π n : ℕ, X (n+1) ⟶ X n)
(d_squared' : ∀ n, d (n+1) ≫ d n = 0 . obviously)
```

Notice here that the differential is indexed differently than in `chain_complex`.
Here `d 0 : X 1 ⟶ X 0`, while in `chain_complex` we have `d 0 : X 0 ⟶ X (-1)`.
This indexing is very natural for connective complexes.
It's not hard to find references that switch between these two conventions mid-page.

Sometimes one wants to move between these two worlds!
We provide a predicate `is_connective` on `chain_complex`,
which asserts that the complex is zero in all negative `ℤ` degrees,
and construct the equivalence
`connective_chain_complex V ≌ { C : chain_complex V // is_connective C}`.

While one might hope this equivalence is easy and straightforward,
it's rather painful to build.
Partly this is because we need to define objects via `if` statements
(or, alternatively, by pattern matching),
and then find ourselves wanting to use rewriting at the level of objects in a category
(which is best avoided in favour of explicit `eq_to_hom` morphisms).
Partly this is because of the natural discrepancy in the indexing of differentials,
as described above, requiring us to manipulate indentities in `ℕ` and `ℤ` (lots of monus wrangling!)
which appear in the index of a type family, leading to dependent type theory hell
(which we again handle through explicit `eq_to_hom` morphisms).

The unpleasantness in the construction of the equivalence is hopefully not actually a problem, and
one should view it as an unfortunate necessity to guarantee that we've got our definitions correct,
and then avoid using it.
-/

universes v u

open category_theory
open category_theory.limits

variables (V : Type u) [category.{v} V]
variables [has_zero_morphisms V]

section is_connective
variables {V} [has_zero_object V]
local attribute [instance] has_zero_object.has_zero

/--
A `ℤ`-indexed chain complex `is_connective` if all objects in negative degrees are 0.
-/
def is_connective (C : chain_complex V) : Prop := ∀ i : ℤ, i < 0 → is_isomorphic (C.X i) 0

lemma is_connective.d_nonpos {C : chain_complex V} (P : is_connective C) {i : ℤ} (h : i ≤ 0) :
  C.d i = 0 :=
zero_of_target_iso_zero' (C.d i) (P (i-1) (by linarith))

@[simp]
lemma is_connective.d_nonpos' (C : { C : chain_complex V // is_connective C }) {i : ℤ} (h : i ≤ 0) :
  (C : chain_complex V).d i = 0 :=
is_connective.d_nonpos C.property h

lemma is_connective.d_0 {C : chain_complex V} (P : is_connective C) : C.d 0 = 0 :=
is_connective.d_nonpos P (le_refl _)

@[simp]
lemma is_connective.d_0' (C : { C : chain_complex V // is_connective C }) :
  (C : chain_complex V).d 0 = 0 :=
is_connective.d_0 C.property

lemma is_connective.f_neg_left {C D : chain_complex V} (P : is_connective C) (f : C ⟶ D)
  {i : ℤ} (h : i < 0) :
  f.f i = 0 :=
zero_of_source_iso_zero' (f.f i) (P i h)

lemma is_connective.f_neg_right {C D : chain_complex V} (P : is_connective D) (f : C ⟶ D)
  {i : ℤ} (h : i < 0) :
  f.f i = 0 :=
zero_of_target_iso_zero' (f.f i) (P i h)

@[simp]
lemma is_connective.f_neg' {C D : { C : chain_complex V // is_connective C }} (f : C ⟶ D)
  {i : ℤ} (h : i < 0) :
  f.f i = 0 :=
is_connective.f_neg_left C.property f h

@[simp]
lemma is_connective.id_neg (C : { C : chain_complex V // is_connective C })
 {i : ℤ} (h : i < 0) : (𝟙 ((C : chain_complex V).X i)) = 0 :=
zero_of_source_iso_zero' _ (C.property i h)

end is_connective

/--
A connective chain complex in `V` is a `ℕ`-indexed collection of objects `X n : V`,
and differentials `d n : X (n+1) ⟶ X n` satisfying `d (n+1) ≫ d n = 0`.

See `connective_chain_complex.equivalence` for the equivalence with the category
of `ℤ`-indexed chain complexes which are supported in non-negative degrees.
-/
@[nolint has_inhabited_instance]
structure connective_chain_complex :=
(X : ℕ → V)
(d : Π n : ℕ, X (n+1) ⟶ X n)
(d_squared' : ∀ n, d (n+1) ≫ d n = 0 . obviously)

restate_axiom connective_chain_complex.d_squared'
attribute [simp, reassoc] connective_chain_complex.d_squared

namespace connective_chain_complex

variables {V}

@[reassoc]
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

instance (C : connective_chain_complex V) : inhabited (hom C C) := ⟨id C⟩

@[simps]
def comp {C D E : connective_chain_complex V} (f : hom C D) (g : hom D E) : hom C E :=
{ f := λ n, f.f n ≫ g.f n, }

end hom

/--
The category of connective chain complexes in V.
-/
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

/--
The objects of a connective chain complex, extended to a function on `ℤ` by `0`.
-/
def X_ℤ (C : connective_chain_complex V) (i : ℤ) : V :=
if 0 ≤ i then C.X i.to_nat else 0

/--
The morphisms of a connective chain complex, extended to a function on `ℤ`.
We also introduce an off-by-one offset, as in connective_chain_complex `d n : X (n+1) ⟶ X n`,
while in chain_complex `d i : X i ⟶ X (i-1)`.
-/

def d_ℤ (C : connective_chain_complex V) (i : ℤ) : (X_ℤ C) i ⟶ (X_ℤ C) (i-1) :=
if h : 0 < i then
  eq_to_hom (congr_arg (X_ℤ C) (show i = ((i.to_nat - 1 : ℕ) : ℤ) + 1, by simp [h])) ≫
    C.d _ ≫
    eq_to_hom (congr_arg (X_ℤ C) (show ((i.to_nat - 1 : ℕ) : ℤ) = i - 1, by simp [h]))
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

@[simp] lemma lt_self_iff_false {α : Sort*} [partial_order α] (a : α) : a < a ↔ false :=
by simp [lt_irrefl a]

@[simp] lemma int.add_minus_one (i : ℤ) : i + -1 = i - 1 := rfl

@[simp] lemma int.coe_nat_succ_pos (n : ℕ) : 0 < (n : ℤ) + 1 :=
int.lt_add_one_iff.mpr (by simp)

@[simp] lemma int.neg_succ_not_nonneg (n : ℕ) : 0 ≤ -[1+ n] ↔ false :=
by { simp only [not_le, iff_false], exact int.neg_succ_lt_zero n, }

@[simp] lemma int.neg_succ_not_pos (n : ℕ) : 0 < -[1+ n] ↔ false :=
by { simp only [not_lt, iff_false], exact le_of_lt (int.neg_succ_lt_zero n) }

@[simp] lemma int.neg_succ_sub_one (n : ℕ) : -[1+ n] - 1 = -[1+ (n+1)] := rfl

lemma int.pred_to_nat (i : ℤ) : (i - 1).to_nat = i.to_nat - 1 :=
begin
  cases i,
  { cases i,
    { simp, refl, },
    { simp, }, },
  { simp only [int.neg_succ_sub_one, int.to_nat], }
end

@[simp]
lemma int.to_nat_pred_coe_succ_eq_self_of_pos {i : ℤ} (h : 0 < i) :
  ((i.to_nat - 1 : ℕ) : ℤ) + 1 = i :=
begin
  cases i,
  { cases i,
    { simpa using h, },
    { simp, }, },
  { simpa using h, }
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
          simp only [category.assoc, eq_to_hom_trans_assoc],
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

/-!
We now prepare some auxiliary definitions for
`connective_chain_complex V ≌ { C : chain_complex V // is_connective C }`.
That these are anything other the identities is dependent-type theory hell,
coping with identities in `ℕ` or `ℤ` which we can't avoid because of indexing discrepancies
between the two definitions.
-/
namespace equivalence

/-- The unit for the equivalence. -/
@[simps]
def unit_hom :
  𝟭 (connective_chain_complex V) ⟶ to_chain_complex V ⋙ to_connective_chain_complex V :=
{ app := λ C,
  { f := λ n, 𝟙 _,
    comm' := λ n, by { dsimp [d_ℤ], simp, refl, }, }, }

/-- The inverse of the unit for the equivalence. -/
@[simps]
def unit_inv :
  to_chain_complex V ⋙ to_connective_chain_complex V ⟶ 𝟭 (connective_chain_complex V) :=
{ app := λ C,
  { f := λ n, 𝟙 _,
    comm' := λ n, by { dsimp [d_ℤ], simp, refl, }, }, }

/--
The unit isomorphism for the equivalence
`connective_chain_complex V ≌ { C : chain_complex V // is_connective C }`.
-/
@[simps]
def unit_iso :
  𝟭 (connective_chain_complex V) ≅ to_chain_complex V ⋙ to_connective_chain_complex V :=
{ hom := unit_hom V,
  inv := unit_inv V, }.

/-- The counit for the equivalence. -/
@[simps]
def counit_hom : to_connective_chain_complex V ⋙ to_chain_complex V ⟶ 𝟭 _ :=
{ app := λ C,
  { f := λ i,
    if h : 0 ≤ i then eq_to_hom (by simp [X_ℤ, if_pos h, int.to_nat_of_nonneg h]) else
      eq_to_hom (show ite (0 ≤ i) (C.val.X i.to_nat) 0 = 0, by simp [if_neg h]) ≫
        (iso_of_is_isomorphic_zero (C.property i (show i < 0, by simpa using h))).inv,
    comm' :=
    begin
      ext i, dsimp [d_ℤ],
      by_cases h : 0 ≤ i,
      { by_cases h' : 0 ≤ i - 1,
        { have h'' : 0 < i := by linarith,
          simp only [dif_pos h, dif_pos h', dif_pos h''],
          simp only [category.id_comp, category.assoc, eq_to_hom_trans],
          erw ←homological_complex.eq_to_hom_d C.val (int.to_nat_pred_coe_succ_eq_self_of_pos h''),
          simp, refl, },
        { rw [dif_pos h, dif_neg h'],
          have h'' : i = 0 := by linarith,
          subst h'',
          simp, }, },
      { have h' : ¬ 0 ≤ i - 1 := by linarith,
        have h'' : ¬ 0 < i := by linarith,
        rw [dif_neg h, dif_neg h', dif_neg h''],
        simp at h'',
        simp [h''], },
    end, },
  naturality' := λ C D f,
  begin
    ext i,
    dsimp,
    split_ifs,
    { simp only [category.assoc, eq_to_hom_trans],
      rw [←homological_complex.eq_to_hom_f _ (int.to_nat_of_nonneg h)],
      simp, },
    { simp at h, simp [h], }
  end, }.

/-- The inverse of the counit for the equivalence. -/
@[simps]
def counit_inv : 𝟭 _ ⟶ to_connective_chain_complex V ⋙ to_chain_complex V :=
{ app := λ C,
  { f := λ i,
    if h : 0 ≤ i then eq_to_hom (by simp [X_ℤ, if_pos h, int.to_nat_of_nonneg h]) else
      (iso_of_is_isomorphic_zero (C.property i (show i < 0, by simpa using h))).hom ≫
        eq_to_hom (show 0 = ite (0 ≤ i) (C.val.X (i.to_nat)) 0, by simp [if_neg h]),
    comm' :=
    begin
      ext i, dsimp [d_ℤ],
      by_cases h : 0 ≤ i,
      { by_cases h' : 0 ≤ i - 1,
        { dsimp [X_ℤ],
          have h'' : 0 < i := by linarith,
          simp only [dif_pos h, dif_pos h', dif_pos h''],
          simp only [category.id_comp, category.assoc, eq_to_hom_trans, eq_to_hom_trans_assoc],
          erw homological_complex.eq_to_hom_d_assoc C.val
            (int.to_nat_pred_coe_succ_eq_self_of_pos h'').symm,
          simp, refl, },
        { rw [dif_pos h, dif_neg h'],
          have h'' : i = 0 := by linarith,
          subst h'',
          simp, }, },
      { have h' : ¬ 0 ≤ i - 1 := by linarith,
        have h'' : ¬ 0 < i := by linarith,
        rw [dif_neg h, dif_neg h', dif_neg h''],
        simp at h'',
        simp [h''], },
    end, },
  naturality' := λ C D f,
  begin
    ext i,
    dsimp,
    split_ifs,
    { simp only [eq_to_hom_trans_assoc],
      rw [homological_complex.eq_to_hom_f_assoc _ (int.to_nat_of_nonneg h).symm],
      simp, },
    { simp at h, simp [h], }
  end, }.

/--
The counit isomorphism for the equivalence
`connective_chain_complex V ≌ { C : chain_complex V // is_connective C }`.
-/
@[simps]
def counit_iso :
  to_connective_chain_complex V ⋙ to_chain_complex V ≅ 𝟭 _ :=
{ hom := counit_hom V,
  inv := counit_inv V,
  hom_inv_id' := by { ext C i, dsimp, split_ifs; simp, },
  inv_hom_id' := begin
    ext C i,
    dsimp,
    split_ifs with h,
    { simp, },
    { simp at h, simp [h], }
  end, }.

lemma functor_unit_iso_comp (C : connective_chain_complex V) :
  (to_chain_complex V).map ((unit_iso V).hom.app C) ≫
      (counit_iso V).hom.app ((to_chain_complex V).obj C) =
    𝟙 ((to_chain_complex V).obj C) :=
begin
  ext i,
  dsimp,
  split_ifs,
  { simp only [category.id_comp, eq_to_hom_refl, eq_to_hom_trans],
    simp [if_pos h], refl, },
  { dsimp [X_ℤ],
    simp only [limits.zero_comp],
    refine (zero_of_target_iso_zero _ _).symm,
    simp [if_neg h], },
end

end equivalence
open equivalence

@[simps]
def equivalence : connective_chain_complex V ≌ { C : chain_complex V // is_connective C } :=
{ functor := to_chain_complex V,
  inverse := to_connective_chain_complex V,
  unit_iso := unit_iso V,
  counit_iso := counit_iso V,
  functor_unit_iso_comp' := λ C, functor_unit_iso_comp V C, }

end connective_chain_complex
#lint
