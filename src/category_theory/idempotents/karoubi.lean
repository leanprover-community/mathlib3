/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.idempotents.basic
import category_theory.preadditive.additive_functor
import category_theory.equivalence

/-!
# The Karoubi envelope of a category

In this file, we define the Karoubi envelope `karoubi C` of a category `C`.

## Main constructions and definitions

- `karoubi C` is the Karoubi envelope of a category `C`: it is an idempotent
complete category. It is also preadditive when `C` is preadditive.
- `to_karoubi C : C ⥤ karoubi C` is a fully faithful functor, which is an equivalence
(`to_karoubi_is_equivalence`) when `C` is idempotent complete.

-/

noncomputable theory

open category_theory.category
open category_theory.preadditive
open category_theory.limits
open_locale big_operators

namespace category_theory

variables (C : Type*) [category C]

namespace idempotents

/-- In a preadditive category `C`, when an object `X` decomposes as `X ≅ P ⨿ Q`, one may
consider `P` as a direct factor of `X` and up to unique isomorphism, it is determined by the
obvious idempotent `X ⟶ P ⟶ X` which is the projection onto `P` with kernel `Q`. More generally,
one may define a formal direct factor of an object `X : C` : it consists of an idempotent
`p : X ⟶ X` which is thought as the "formal image" of `p`. The type `karoubi C` shall be the
type of the objects of the karoubi enveloppe of `C`. It makes sense for any category `C`. -/
@[nolint has_nonempty_instance]
structure karoubi := (X : C) (p : X ⟶ X) (idem : p ≫ p = p)

namespace karoubi

variables {C}

attribute [simp, reassoc] idem

@[ext]
lemma ext {P Q : karoubi C} (h_X : P.X = Q.X)
  (h_p : P.p ≫ eq_to_hom h_X = eq_to_hom h_X ≫ Q.p) : P = Q :=
begin
  cases P,
  cases Q,
  dsimp at h_X h_p,
  subst h_X,
  simpa only [true_and, eq_self_iff_true, id_comp, eq_to_hom_refl,
    heq_iff_eq, comp_id] using h_p,
end

/-- A morphism `P ⟶ Q` in the category `karoubi C` is a morphism in the underlying category
`C` which satisfies a relation, which in the preadditive case, expresses that it induces a
map between the corresponding "formal direct factors" and that it vanishes on the complement
formal direct factor. -/
@[ext]
structure hom (P Q : karoubi C) := (f : P.X ⟶ Q.X) (comm : f = P.p ≫ f ≫ Q.p)

instance [preadditive C] (P Q : karoubi C) : inhabited (hom P Q) :=
⟨⟨0, by rw [zero_comp, comp_zero]⟩⟩

@[simp]
lemma hom_ext {P Q : karoubi C} {f g : hom P Q} : f = g ↔ f.f = g.f :=
begin
  split,
  { intro h, rw h, },
  { ext, }
end

@[simp, reassoc]
lemma p_comp {P Q : karoubi C} (f : hom P Q) : P.p ≫ f.f = f.f :=
by rw [f.comm, ← assoc, P.idem]

@[simp, reassoc]
lemma comp_p {P Q : karoubi C} (f : hom P Q) : f.f ≫ Q.p = f.f :=
by rw [f.comm, assoc, assoc, Q.idem]

lemma p_comm {P Q : karoubi C} (f : hom P Q) : P.p ≫ f.f = f.f ≫ Q.p :=
by rw [p_comp, comp_p]

lemma comp_proof {P Q R : karoubi C} (g : hom Q R) (f : hom P Q) :
  f.f ≫ g.f = P.p ≫ (f.f ≫ g.f) ≫ R.p :=
by rw [assoc, comp_p, ← assoc, p_comp]

/-- The category structure on the karoubi envelope of a category. -/
instance : category (karoubi C) :=
{ hom      := karoubi.hom,
  id       := λ P, ⟨P.p, by { repeat { rw P.idem, }, }⟩,
  comp     := λ P Q R f g, ⟨f.f ≫ g.f, karoubi.comp_proof g f⟩, }

@[simp]
lemma comp_f {P Q R : karoubi C} (f : P ⟶ Q) (g : Q ⟶ R) :
  (f ≫ g).f = f.f ≫ g.f := by refl

@[simp]
lemma id_eq {P : karoubi C} : 𝟙 P = ⟨P.p, by repeat { rw P.idem, }⟩ := by refl

/-- It is possible to coerce an object of `C` into an object of `karoubi C`.
See also the functor `to_karoubi`. -/
instance coe : has_coe_t C (karoubi C) := ⟨λ X, ⟨X, 𝟙 X, by rw comp_id⟩⟩

@[simp]
lemma coe_X (X : C) : (X : karoubi C).X = X := by refl

@[simp]
lemma coe_p (X : C) : (X : karoubi C).p = 𝟙 X := by refl

@[simp]
lemma eq_to_hom_f {P Q : karoubi C} (h : P = Q) :
  karoubi.hom.f (eq_to_hom h) = P.p ≫ eq_to_hom (congr_arg karoubi.X h) :=
by { subst h, simp only [eq_to_hom_refl, karoubi.id_eq, comp_id], }

end karoubi

/-- The obvious fully faithful functor `to_karoubi` sends an object `X : C` to the obvious
formal direct factor of `X` given by `𝟙 X`. -/
@[simps]
def to_karoubi : C ⥤ karoubi C :=
{ obj := λ X, ⟨X, 𝟙 X, by rw comp_id⟩,
  map := λ X Y f, ⟨f, by simp only [comp_id, id_comp]⟩ }

instance : full (to_karoubi C) :=
{ preimage := λ X Y f, f.f, }

instance : faithful (to_karoubi C) := { }

variables {C}

@[simps]
instance [preadditive C] {P Q : karoubi C} : add_comm_group (P ⟶ Q) :=
{ add := λ f g, ⟨f.f+g.f, begin
    rw [add_comp, comp_add],
    congr',
    exacts [f.comm, g.comm],
  end⟩,
  zero := ⟨0, by simp only [comp_zero, zero_comp]⟩,
  zero_add := λ f, by { ext, simp only [zero_add], },
  add_zero := λ f, by { ext, simp only [add_zero], },
  add_assoc := λ f g h', by simp only [add_assoc],
  add_comm := λ f g, by { ext, apply_rules [add_comm], },
  neg := λ f, ⟨-f.f, by simpa only [neg_comp, comp_neg, neg_inj] using f.comm⟩,
  add_left_neg := λ f, by { ext, apply_rules [add_left_neg], }, }

namespace karoubi

lemma hom_eq_zero_iff [preadditive C] {P Q : karoubi C} {f : hom P Q} : f = 0 ↔ f.f = 0 := hom_ext

/-- The map sending `f : P ⟶ Q` to `f.f : P.X ⟶ Q.X` is additive. -/
@[simps]
def inclusion_hom [preadditive C] (P Q : karoubi C) : add_monoid_hom (P ⟶ Q) (P.X ⟶ Q.X) :=
{ to_fun    := λ f, f.f,
  map_zero' := rfl,
  map_add'  := λ f g, rfl }

@[simp]
lemma sum_hom [preadditive C] {P Q : karoubi C} {α : Type*} (s : finset α) (f : α → (P ⟶ Q)) :
  (∑ x in s, f x).f = ∑ x in s, (f x).f  :=
add_monoid_hom.map_sum (inclusion_hom P Q) f s

end karoubi

/-- The category `karoubi C` is preadditive if `C` is. -/
instance [preadditive C] : preadditive (karoubi C) :=
{ hom_group := λ P Q, by apply_instance, }

instance [preadditive C] : functor.additive (to_karoubi C) := { }

open karoubi

variables (C)

instance : is_idempotent_complete (karoubi C) :=
begin
  refine ⟨_⟩,
  intros P p hp,
  have hp' := hom_ext.mp hp,
  simp only [comp_f] at hp',
  use ⟨P.X, p.f, hp'⟩,
  use ⟨p.f, by rw [comp_p p, hp']⟩,
  use ⟨p.f, by rw [hp', p_comp p]⟩,
  split; simpa only [hom_ext] using hp',
end

instance [is_idempotent_complete C] : ess_surj (to_karoubi C) := ⟨λ P, begin
  have h : is_idempotent_complete C := infer_instance,
  rcases is_idempotent_complete.idempotents_split P.X P.p P.idem
    with ⟨Y,i,e,⟨h₁,h₂⟩⟩,
  use Y,
  exact nonempty.intro
    { hom := ⟨i, by erw [id_comp, ← h₂, ← assoc, h₁, id_comp]⟩,
      inv := ⟨e, by erw [comp_id, ← h₂, assoc, h₁, comp_id]⟩, },
end⟩

/-- If `C` is idempotent complete, the functor `to_karoubi : C ⥤ karoubi C` is an equivalence. -/
def to_karoubi_is_equivalence [is_idempotent_complete C] :
  is_equivalence (to_karoubi C) :=
equivalence.of_fully_faithfully_ess_surj (to_karoubi C)

namespace karoubi

variables {C}

/-- The split mono which appears in the factorisation `decomp_id P`. -/
@[simps]
def decomp_id_i (P : karoubi C) : P ⟶ P.X := ⟨P.p, by erw [coe_p, comp_id, P.idem]⟩

/-- The split epi which appears in the factorisation `decomp_id P`. -/
@[simps]
def decomp_id_p (P : karoubi C) : (P.X : karoubi C) ⟶ P :=
⟨P.p, by erw [coe_p, id_comp, P.idem]⟩

/-- The formal direct factor of `P.X` given by the idempotent `P.p` in the category `C`
is actually a direct factor in the category `karoubi C`. -/
lemma decomp_id (P : karoubi C) :
  𝟙 P = (decomp_id_i P) ≫ (decomp_id_p P) :=
by { ext, simp only [comp_f, id_eq, P.idem, decomp_id_i, decomp_id_p], }

lemma decomp_p (P : karoubi C) :
  (to_karoubi C).map P.p = (decomp_id_p P) ≫ (decomp_id_i P) :=
by { ext, simp only [comp_f, decomp_id_p_f, decomp_id_i_f, P.idem, to_karoubi_map_f], }

lemma decomp_id_i_to_karoubi (X : C) : decomp_id_i ((to_karoubi C).obj X) = 𝟙 _ :=
by { ext, refl, }

lemma decomp_id_p_to_karoubi (X : C) : decomp_id_p ((to_karoubi C).obj X) = 𝟙 _ :=
by { ext, refl, }

lemma decomp_id_i_naturality {P Q : karoubi C} (f : P ⟶ Q) : f ≫ decomp_id_i _ =
  decomp_id_i _ ≫ ⟨f.f, by erw [comp_id, id_comp]⟩ :=
by { ext, simp only [comp_f, decomp_id_i_f, karoubi.comp_p, karoubi.p_comp], }

lemma decomp_id_p_naturality {P Q : karoubi C} (f : P ⟶ Q) : decomp_id_p P ≫ f =
  (⟨f.f, by erw [comp_id, id_comp]⟩ : (P.X : karoubi C) ⟶ Q.X) ≫ decomp_id_p Q :=
by { ext, simp only [comp_f, decomp_id_p_f, karoubi.comp_p, karoubi.p_comp], }

@[simp]
lemma zsmul_hom [preadditive C] {P Q : karoubi C} (n : ℤ) (f : P ⟶ Q) :
  (n • f).f = n • f.f :=
map_zsmul (inclusion_hom P Q) n f

end karoubi

end idempotents

end category_theory
