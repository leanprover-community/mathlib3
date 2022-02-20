/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.path_category
import category_theory.fully_faithful
import category_theory.bicategory.free
import category_theory.bicategory.locally_discrete
/-!
# The coherence theorem for bicategories

In this file, we prove the coherence theorem for bicategories, stated in the following form: the
free bicategory over any quiver is locally thin.

The proof is almost the same as the proof of the coherence theorem for monoidal categories that
has been previously formalized in mathlib, which is based on the proof described by Ilya Beylin
and Peter Dybjer. The idea is to view a path on a quiver as a normal form of a 1-morphism in the
free bicategory on the same quiver. A normalization procedure is then described by
`full_normalize : pseudofunctor (free_bicategory B) (locally_discrete (paths B))`, which is a
pseudofunctor from the free bicategory to the locally discrete bicategory on the path category.
It turns out that this pseudofunctor is locally an equivalence of categories, and the coherence
theorem follows immediately from this fact.

## Main statements

* `locally_thin` : the free bicategory is locally thin, that is, there is at most one
  2-morphism between two fixed 1-morphisms.

## References

* [Ilya Beylin and Peter Dybjer, Extracting a proof of coherence for monoidal categories from a
   proof of normalization for monoids][beylin1996]
-/

open quiver (path) quiver.path

namespace category_theory

open bicategory category
open_locale bicategory

universes v u

namespace free_bicategory

variables {B : Type u} [quiver.{v+1} B]

/-- Auxiliary definition for `inclusion_path`. -/
@[simp]
def inclusion_path_aux {a : B} : ∀ {b : B}, path a b → hom a b
| _ nil := hom.id a
| _ (cons p f) := (inclusion_path_aux p).comp (hom.of f)

/--
The discrete category on the paths includes into the category of 1-morphisms in the free
bicategory.
-/
def inclusion_path (a b : B) : discrete (path.{v+1} a b) ⥤ hom a b :=
discrete.functor inclusion_path_aux
/- should simply be `discrete.functor inclusion_path_aux`, but `discrete.functor` defines
the `map` field using the `cases` tactic, which is bad. I think we should redefine
`discrete.functor` to use `eq_to_hom`. -/

variables (B)

/--
The inclusion from the locally discrete bicategory on the path category into the free bicategory
as a prelax functor. This will be promoted to a pseudofunctor after proving the coherence theorem.
See `inclusion`.
-/
@[simps]
def preinclusion : prelax_functor (locally_discrete (paths B)) (free_bicategory B) :=
{ obj := id,
  map := λ a b, (inclusion_path a b).obj,
  map₂ := λ a b, (inclusion_path a b).map }

variables {B}

@[simp]
def normalize_map : ∀ {a b : B}, hom a b → path a b
| _ _ (hom.of f) := f.to_path
| _ _ (hom.id a) := nil
| _ _ (hom.comp f g) := (normalize_map f).comp (normalize_map g)

lemma normalize_map_congr {a b : B} {f g : hom a b} (η : hom₂ f g) :
  normalize_map f = normalize_map g :=
begin
  induction η,
  case vcomp { apply eq.trans; assumption },
  case whisker_left : _ _ _ _ _ _ _ ih { apply congr_arg _ ih },
  case whisker_right : _ _ _ _ _ _ _ ih { exact congr_arg2 _ ih rfl },
  all_goals { simp },
end
/-- the lemmas
@[simp] lemma id_def : hom.id a = 𝟙 a := rfl
@[simp] lemma comp_def : hom.comp f g = f ≫ g := rfl
in bicategory.free works against `dsimp`, so I removed them. -/

variable (B)

/-- The normalization pseudofunctor for the free bicategory on a quiver `B`. -/
def full_normalize : oplax_functor (free_bicategory B) (locally_discrete (paths B)) :=
{ obj := id,
  map := λ a b, normalize_map,
  map₂ := λ a b f g η, ⟨⟨quot.ind normalize_map_congr η⟩⟩,
  map_id := λ a, 𝟙 _,
  map_comp := λ a b c f g, 𝟙 _ }

/--
Auxiliary definition for `normalize`. Given a 2-morphism between `f` and `g` in the free
bicategory, we have a natural transformation between `normalize_hom f` and `normalize_hom g`
that are viewed as functors between discrete categories.
-/
@[simps]
def normalize_map_aux {a b c : B} {f g : hom b c} (η : hom₂ f g) :
  (discrete.functor (normalize_hom f) : _ ⥤ discrete (path.{v+1} a c)) ⟶
    discrete.functor (normalize_hom g) :=
discrete.nat_trans (λ p, eq_to_hom (normalize_hom_congr η p))
--⟨⟨normalize_hom_congr η p⟩⟩ also works

/--
The normalization of the composition of `p : path a b` and `f : hom b c` as a functor.
-/
def normalize (a b c : B) : hom b c ⥤ discrete (path.{v+1} a b) ⥤ discrete (path.{v+1} a c) :=
{ obj := λ f, discrete.functor (normalize_hom f),
  map := λ f g, quot.lift normalize_map_aux (by tidy) }

/--
A variant of the normalization functor where we consider the result as a 1-morphism in the free
bicategory rather than a path.
-/
def normalize' (a b c : B) : hom b c ⥤ discrete (path.{v+1} a b) ⥤ hom a c :=
normalize _ _ _ ⋙ (whiskering_right _ _ _).obj (inclusion_path _ _)

variables {B}

/--
Given a 1-morphism `f : hom b c` in the free bicategory and a path `p : path a b`, taking the
composition of `p` and `f` in the free bicategory is functorial in both `f` and `p`.
-/
def whisker_path (a b c : B) : hom b c ⥤ discrete (path.{v+1} a b) ⥤ hom a c :=
{ obj := λ f, discrete.functor (λ p, (preinclusion _).map p ≫ f),
  map := λ f g η, discrete.nat_trans (λ p, (preinclusion _).map p ◁ η) }

lemma whisker_path_obj_map
  (a : B) {b c : B} (f : hom b c) {p p' : discrete (path.{v+1} a b)} (η : p ⟶ p') :
  ((whisker_path _ _ _).obj f).map η = (inclusion_path _ _).map η ▷ f :=
by tidy

/--
Auxiliary definition for `normalize_iso`. Here we construct the isomorphism between
`inclusion_path_aux p ≫ f` and `inclusion_path_aux (normalize_hom f p)`.
-/
@[simp]
def normalize_iso_app {a : B} : Π {b c : B} (f : hom b c) (p : path a b),
  ((whisker_path a b c).obj f).obj p ≅ ((normalize' a b c).obj f).obj p
| _ _ (hom.of f) p := iso.refl _
| _ _ (hom.id a) p := ρ_ ((preinclusion _).map p)
| _ _ (hom.comp f g) p :=
    (α_ _ _ _).symm ≪≫ whisker_right_iso (normalize_iso_app f p) g ≪≫
      normalize_iso_app g (((normalize _ _ _).obj f).obj p)

/-- Auxiliary definition for `normalize_iso`. -/
@[simp]
def normalize_iso_aux (a : B) {b c : B} (f : hom b c) :
  (whisker_path a b c).obj f ≅ (normalize' a b c).obj f :=
nat_iso.of_components (normalize_iso_app f) (by tidy)

/--
The isomorphism between `inclusion_path_aux p ≫ f` and `inclusion_path_aux (normalize_hom f p)`
is natural (in both `p` and `f`, but naturality in `p` is trivial and was "proved" in
`normalize_iso_aux`). This is the real heart of our proof of the coherence theorem.
-/
def normalize_iso (a b c : B) : whisker_path a b c ≅ normalize' a b c :=
nat_iso.of_components (normalize_iso_aux a)
begin
  rintros f g ⟨η⟩,
  ext p,
  dsimp only [whisker_path, normalize_iso_aux, nat_trans.comp_app, discrete.nat_trans_app,
    discrete.functor, nat_iso.of_components.hom_app],
  induction η,
  case id { erw [comp_id, bicategory.whisker_left_id, id_comp] },
  case vcomp : _ _ _ _ _ _ _ ihf ihg
  { simp only [mk_vcomp, bicategory.whisker_left_comp],
    slice_lhs 2 3 { rw ihg },
    slice_lhs 1 2 { rw ihf },
    rw (normalize' _ _ _).map_comp,
    simpa only [assoc] },
  case whisker_left : _ _ _ _ _ _ _ ih
  { dsimp only [mk_whisker_left, normalize_iso_app, iso.trans_hom],
    slice_lhs 1 2 { erw associator_inv_naturality_right },
    slice_lhs 2 3 { erw whisker_exchange },
    slice_lhs 3 4 { erw ih },
    simpa only [assoc] },
  case whisker_right  : _ _ _ _ _ _ _ ih
  { dsimp only [mk_whisker_right, normalize_iso_app, iso.trans_hom],
    slice_lhs 1 2 { erw associator_inv_naturality_middle },
    slice_lhs 2 3 { erw [←bicategory.whisker_right_comp, ih, bicategory.whisker_right_comp,
      ←whisker_path_obj_map] },
    slice_lhs 3 4 { erw (normalize_iso_aux _ _).hom.naturality ((normalize_map_aux _).app p) },
    simpa only [assoc] },
  case associator
  { dsimp only [mk_associator_hom, normalize_iso_app, iso.trans_hom, whisker_right_iso_hom],
    erw comp_id,
    slice_lhs 3 4 { erw associator_inv_naturality_left },
    slice_lhs 1 3 { erw pentagon_hom_inv_inv_inv_inv },
    simpa only [assoc, bicategory.whisker_right_comp] },
  case associator_inv
  { dsimp only [mk_associator_inv, normalize_iso_app, iso.trans_hom, whisker_right_iso_hom],
    erw comp_id,
    slice_rhs 2 3 { erw associator_inv_naturality_left },
    slice_rhs 1 2 { erw ←pentagon_inv },
    simpa only [assoc, bicategory.whisker_right_comp] },
  case left_unitor
  { dsimp only [normalize_iso_app, mk_left_unitor_hom, iso.trans_hom, whisker_right_iso_hom],
    slice_rhs 1 2 { erw triangle_assoc_comp_right },
    erw comp_id,
    refl },
  case left_unitor_inv
  { dsimp only [normalize_iso_app, mk_left_unitor_inv, iso.trans_hom, whisker_right_iso_hom],
    slice_lhs 1 2 { erw triangle_assoc_comp_left_inv },
    erw [inv_hom_whisker_right, id_comp, comp_id],
    refl },
  case right_unitor
  { erw [comp_id, whisker_left_right_unitor, assoc, ←right_unitor_naturality],
    refl },
  case right_unitor_inv
  { erw [comp_id, whisker_left_right_unitor_inv, assoc, iso.hom_inv_id_assoc,
      right_unitor_conjugation] }
end

/-- Auxiliary definition for `normalize_unit_iso`. -/
@[simp]
def normalize_unit_iso_app_aux {a b : free_bicategory B} (f : a ⟶ b) :
  (preinclusion B).map (𝟙 a) ≫ f ≅
    (preinclusion B).map (((full_normalize B).map_functor a b).obj f) :=
((normalize_iso _ _ _).app f).app nil

/-- Auxiliary definition for `normalize_equiv`. -/
def normalize_unit_iso (a b : free_bicategory B) :
  𝟭 (a ⟶ b) ≅ (full_normalize B).map_functor _ _ ⋙ inclusion_path _ _ :=
nat_iso.of_components (λ f, (λ_ f).symm ≪≫ normalize_unit_iso_app_aux f)
begin
  intros f g η,
  erw [left_unitor_inv_naturality_assoc, assoc, iso.cancel_iso_inv_left],
  apply congr_arg (λ β, nat_trans.app β nil) ((normalize_iso _ _ _).hom.naturality η)
end

/-- The normalization as an equivalence of categories. -/
def normalize_equiv (a b : B) : hom a b ≌ discrete (path.{v+1} a b) :=
equivalence.mk ((full_normalize _).map_functor a b) (inclusion_path a b)
  (normalize_unit_iso a b)
  (nat_iso.of_components (λ f, eq_to_iso (by { induction f, tidy })) (by tidy))

/-- The coherence theorem for bicategories. -/
instance locally_thin {a b : free_bicategory B} (f g : a ⟶ b) : subsingleton (f ⟶ g) :=
⟨λ η θ, (normalize_equiv a b).functor.map_injective (subsingleton.elim _ _)⟩

/-- Auxiliary definition for `inclusion`. -/
def inclusion_map_comp_aux {a b : B} : ∀ {c : B} (f : path a b) (g : path b c),
  (preinclusion _).map (f ≫ g) ≅ (preinclusion _).map f ≫ (preinclusion _).map g
| _ f nil := (ρ_ ((preinclusion _).map f)).symm
| _ f (cons g₁ g₂) := whisker_right_iso (inclusion_map_comp_aux f g₁) (hom.of g₂) ≪≫ α_ _ _ _

variables (B)

 /--
The inclusion pseudofunctor from the locally discrete bicategory on the path category into the
free bicategory.
-/
@[simps]
def inclusion : pseudofunctor (locally_discrete (paths B)) (free_bicategory B) :=
{ map_id := λ a, iso.refl (𝟙 a),
  map_comp := λ a b c f g, inclusion_map_comp_aux f g,
  -- All the conditions for 2-morphisms are trivial thanks to the coherence theorem!
  .. preinclusion B }

end free_bicategory

end category_theory
