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
`normalize : pseudofunctor (free_bicategory B) (locally_discrete (paths B))`, which is a
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
| _ nil         := hom.id a
| _ (cons p f)  := (inclusion_path_aux p).comp (hom.of f)

/--
The discrete category on the paths includes into the category of 1-morphisms in the free
bicategory.
-/
def inclusion_path (a b : B) : discrete (path.{v+1} a b) ⥤ hom a b :=
{ obj := inclusion_path_aux,
  map := λ f g η, eq_to_hom (congr_arg inclusion_path_aux (discrete.eq_of_hom η)) }

/--
The inclusion from the locally discrete bicategory on the path category into the free bicategory
as a prelax functor. This will be promoted to a pseudofunctor after proving the coherence theorem.
See `inclusion`.
-/
def preinclusion (B : Type u) [quiver.{v+1} B] :
  prelax_functor (locally_discrete (paths B)) (free_bicategory B) :=
{ obj   := id,
  map   := λ a b, (inclusion_path a b).obj,
  map₂  := λ a b, (inclusion_path a b).map }

/--
The normalization of the composition of `p : path a b` and `f : hom b c`.
`p` will eventually be taken to be `nil` and we then get the normalization
of `f` alone, but the auxiliary `p` is necessary for Lean to accept the definition of
`normalize_iso` and the `whisker_left` case of `normalize_aux_congr` and `normalize_naturality`.
-/
@[simp]
def normalize_aux {a : B} : ∀ {b c : B}, path a b → hom b c → path a c
| _ _ p (hom.of f)      := p.cons f
| _ _ p (hom.id b)      := p
| _ _ p (hom.comp f g)  := normalize_aux (normalize_aux p f) g

/-
We may define
def normalize_aux' : ∀ {a b : B}, hom a b → path a b
| _ _ (hom.of f) := f.to_path
| _ _ (hom.id b) := nil
| _ _ (hom.comp f g) := (normalize_aux' f).comp (normalize_aux' g)
and define `normalize_aux p f` to be `p.comp (normalize_aux' f)` and this will be
equal to the above definition, but the equality proof requires `comp_assoc`, and it
thus lacks the correct definitional property to make the definition of `normalize_iso`
typecheck.
example {a b c : B} (p : path a b) (f : hom b c) :
  normalize_aux p f = p.comp (normalize_aux' f) :=
by { induction f, refl, refl,
  case comp : _ _ _ _ _ ihf ihg { rw [normalize_aux, ihf, ihg], apply comp_assoc } }
-/

/--
A 2-isomorphism between a partially-normalized 1-morphism in the free bicategory to the
fully-normalized 1-morphism.
-/
@[simp]
def normalize_iso {a : B} : ∀ {b c : B} (p : path a b) (f : hom b c),
  (preinclusion B).map p ≫ f ≅ (preinclusion B).map (normalize_aux p f)
| _ _ p (hom.of f)      := iso.refl _
| _ _ p (hom.id b)      := ρ_ _
| _ _ p (hom.comp f g)  := (α_ _ _ _).symm ≪≫
    whisker_right_iso (normalize_iso p f) g ≪≫ normalize_iso (normalize_aux p f) g

/--
Given a 2-morphism between `f` and `g` in the free bicategory, we have the equality
`normalize_aux f p = normalize_aux g p`.
-/
lemma normalize_aux_congr {a b c : B} (p : path a b) {f g : hom b c} (η : f ⟶ g) :
  normalize_aux p f = normalize_aux p g :=
begin
  rcases η,
  apply @congr_fun _ _ (λ p, normalize_aux p f),
  clear p,
  induction η,
  case vcomp { apply eq.trans; assumption },
  /- p ≠ nil required! See the docstring of `normalize_aux`. -/
  case whisker_left  : _ _ _ _ _ _ _ ih { funext, apply congr_fun ih },
  case whisker_right : _ _ _ _ _ _ _ ih { funext, apply congr_arg2 _ (congr_fun ih p) rfl },
  all_goals { funext, refl }
end

/-- The 2-isomorphism `normalize_iso p f` is natural in `f`. -/
lemma normalize_naturality {a b c : B} (p : path a b) {f g : hom b c} (η : f ⟶ g) :
  ((preinclusion B).map p ◁ η) ≫ (normalize_iso p g).hom =
    (normalize_iso p f).hom ≫ eq_to_hom (congr_arg _ (normalize_aux_congr p η)) :=
begin
  rcases η, induction η,
  case id : { simp },
  case vcomp : _ _ _ _ _ _ _ ihf ihg
  { rw [mk_vcomp, bicategory.whisker_left_comp],
    slice_lhs 2 3 { rw ihg },
    slice_lhs 1 2 { rw ihf },
    simp },
  case whisker_left : _ _ _ _ _ _ _ ih
  { dsimp,
    slice_lhs 1 2 { rw associator_inv_naturality_right },
    slice_lhs 2 3 { rw whisker_exchange },
    slice_lhs 3 4 { erw ih }, /- p ≠ nil required! See the docstring of `normalize_aux`. -/
    simp only [assoc] },
  case whisker_right : _ _ _ _ _ h η ih
  { dsimp,
    slice_lhs 1 2 { rw associator_inv_naturality_middle },
    slice_lhs 2 3 { erw [←bicategory.whisker_right_comp, ih, bicategory.whisker_right_comp] },
    have := dcongr_arg (λ x, (normalize_iso x h).hom) (normalize_aux_congr p (quot.mk _ η)),
    dsimp at this, simp [this] },
  case associator
  { dsimp,
    slice_lhs 3 4 { erw associator_inv_naturality_left },
    slice_lhs 1 3 { erw pentagon_hom_inv_inv_inv_inv },
    simpa only [assoc, bicategory.whisker_right_comp, comp_id] },
  case associator_inv
  { dsimp,
    slice_rhs 2 3 { erw associator_inv_naturality_left },
    slice_rhs 1 2 { erw ←pentagon_inv },
    simpa only [bicategory.whisker_right_comp, assoc, comp_id] },
  case left_unitor { erw [comp_id, ←triangle_assoc_comp_right_assoc], refl },
  case left_unitor_inv
  { dsimp,
    slice_lhs 1 2 { erw triangle_assoc_comp_left_inv },
    rw [inv_hom_whisker_right, id_comp, comp_id] },
  case right_unitor
  { erw [comp_id, whisker_left_right_unitor, assoc, ←right_unitor_naturality], refl },
  case right_unitor_inv
  { erw [comp_id, whisker_left_right_unitor_inv, assoc, iso.hom_inv_id_assoc,
      right_unitor_conjugation] }
end

@[simp]
lemma normalize_aux_nil_comp {a b c : B} (f : hom a b) (g : hom b c) :
  normalize_aux nil (f.comp g) = (normalize_aux nil f).comp (normalize_aux nil g) :=
begin
  induction g generalizing a,
  case id { refl },
  case of { refl },
  case comp : _ _ _ g _ ihf ihg { erw [ihg (f.comp g), ihf f, ihg g, comp_assoc] }
end

/-- The normalization pseudofunctor for the free bicategory on a quiver `B`. -/
def normalize (B : Type u) [quiver.{v+1} B] :
  pseudofunctor (free_bicategory B) (locally_discrete (paths B)) :=
{ obj       := id,
  map       := λ a b, normalize_aux nil,
  map₂      := λ a b f g η, eq_to_hom (normalize_aux_congr nil η),
  map_id    := λ a, iso.refl nil,
  map_comp  := λ a b c f g, eq_to_iso (normalize_aux_nil_comp f g) }

@[simp] lemma normalize_obj : (normalize B).obj = id := rfl
@[simp] lemma normalize_map_hom_of {a b : B} (f : a ⟶ b) :
  (normalize B).map (hom.of f) = nil.cons f := rfl
@[simp] lemma normalize_map_hom_id (a : B) :
  (normalize B).map (hom.id a) = nil := rfl
@[simp] lemma normalize_map_hom_comp {a b c : B} (f : hom a b) (g : hom b c) :
  (normalize B).map (f.comp g) =
    ((normalize B).map f).comp ((normalize B).map g) := normalize_aux_nil_comp f g
@[simp] lemma normalize_map₂ {a b : B} {f g : hom a b} (η : f ⟶ g) :
  (normalize B).map₂ η = eq_to_hom (normalize_aux_congr nil η) := rfl
@[simp] lemma normalize_map₂' {a b : free_bicategory B} {f g : a ⟶ b} (η : f ⟶ g) :
  (normalize B).map₂ η = eq_to_hom (normalize_aux_congr nil η) := rfl
@[simp] lemma normalize_map_id (a : B) : (normalize B).map_id a = iso.refl nil := rfl
@[simp] lemma normalize_map_comp {a b c : B} (f : hom a b) (g : hom b c) :
  (normalize B).map_comp f g = eq_to_iso (normalize_aux_nil_comp f g) := rfl

/-- Auxiliary definition for `normalize_equiv`. -/
def normalize_unit_iso (a b : free_bicategory B) :
  𝟭 (a ⟶ b) ≅ (normalize B).map_functor a b ⋙ inclusion_path a b :=
nat_iso.of_components (λ f, (λ_ f).symm ≪≫ normalize_iso nil f)
begin
  intros f g η,
  erw [left_unitor_inv_naturality_assoc, assoc],
  congr' 1,
  exact normalize_naturality nil η
end

/-- Normalization as an equivalence of categories. -/
def normalize_equiv (a b : B) : hom a b ≌ discrete (path.{v+1} a b) :=
equivalence.mk ((normalize _).map_functor a b) (inclusion_path a b)
  (normalize_unit_iso a b)
  (discrete.nat_iso (λ f, eq_to_iso (by { induction f; tidy })))

/-- The coherence theorem for bicategories. -/
instance locally_thin {a b : free_bicategory B} (f g : a ⟶ b) : subsingleton (f ⟶ g) :=
⟨λ η θ, (normalize_equiv a b).functor.map_injective (subsingleton.elim _ _)⟩

/-- Auxiliary definition for `inclusion`. -/
def inclusion_map_comp_aux {a b : B} : ∀ {c : B} (f : path a b) (g : path b c),
  (preinclusion _).map (f ≫ g) ≅ (preinclusion _).map f ≫ (preinclusion _).map g
| _ f nil := (ρ_ ((preinclusion _).map f)).symm
| _ f (cons g₁ g₂) := whisker_right_iso (inclusion_map_comp_aux f g₁) (hom.of g₂) ≪≫ α_ _ _ _

/--
The inclusion pseudofunctor from the locally discrete bicategory on the path category into the
free bicategory.
-/
def inclusion (B : Type u) [quiver.{v+1} B] :
  pseudofunctor (locally_discrete (paths B)) (free_bicategory B) :=
{ map_id    := λ a, iso.refl (𝟙 a),
  map_comp  := λ a b c f g, inclusion_map_comp_aux f g,
  -- All the conditions for 2-morphisms are trivial thanks to the coherence theorem!
  .. preinclusion B }

@[simp] lemma inclusion_obj : (inclusion B).obj = id := rfl
@[simp] lemma inclusion_map_nil (a : B) : (inclusion B).map nil = hom.id a := rfl
@[simp] lemma inclusion_map_cons {a b c : B} (p : path a b) (q : b ⟶ c) :
  (inclusion B).map (p.cons q) = ((inclusion B).map p).comp (hom.of q) := rfl
@[simp] lemma inclusion_map₂ {a b : B} (p q : discrete (path.{v+1} a b)) (h : p ⟶ q) :
  (inclusion B).map₂ h = eq_to_hom (congr_arg _ (discrete.eq_of_hom h)) := rfl
@[simp] lemma inclusion_map_id (a : B) : (inclusion B).map_id a = iso.refl (𝟙 a) := rfl
@[simp] lemma inclusion_map_comp_nil {a b : B} (f : path a b) :
  (inclusion B).map_comp f nil = (ρ_ ((inclusion B).map (f.comp nil))).symm := rfl
@[simp] lemma inclusion_map_comp_cons {a b c d : B} (p : path a b) (q : path b c) (f : c ⟶ d) :
  (inclusion B).map_comp p (q.cons f) =
    whisker_right_iso ((inclusion B).map_comp p q) (hom.of f) ≪≫ α_ _ _ _ := rfl

end free_bicategory

end category_theory
