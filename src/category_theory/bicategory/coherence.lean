import category_theory.bicategory.free
import category_theory.path_category
import category_theory.fully_faithful
import category_theory.bicategory.locally_discrete
/-!
## The coherence theorem for bicategories

In this file, we prove the coherence theorem for bicategories, stated in the following form: the
free bicategory over any quiver is locally subsingleton.

The proof is almost the same as the proof of the coherence theorem for monoidal categories that
has been previously formalized in mathlib, which is based on the proof described by Ilya Beylin
and Peter Dybjer. The idea is to view paths on a quiver as a normal form of 1-morphisms in the
free bicategory on the same quiver. It turns out that the normalization of 1-morphisms in the
free bicategory gives an bicategorical equivalence between `free_bicategory B` and
`locally_discrete (paths B)`, and the coherence theorem for bicategories is obtained along the way
of proving this fact.

# Main definitions and statements

* `locally_subsingleton` : the free bicategory is locally subsingleton, that is, there is at most
  one 2-morphism between two fixed 1-morphisms.

## References

* [Ilya Beylin and Peter Dybjer, Extracting a proof of coherence for monoidal categories from a
   proof of normalization for monoids][beylin1996]
-/

open quiver (path)
open quiver.path

namespace category_theory

open bicategory category
open_locale bicategory

universes v u

namespace free_bicategory

variables {B : Type u} [quiver.{v+1} B]

/-- Auxiliary definition for `inclusion_map_functor`. -/
@[simp]
def inclusion_map {a : B} : ∀ {b : B}, path a b → hom a b
| _ nil := hom.id a
| _ (cons p f) := (inclusion_map p).comp (hom.of f)

/-- The discrete subcategory of objects in normal form includes into the free bicategory. -/
@[simps]
def inclusion_map_functor (a b : B) : discrete (path.{v+1} a b) ⥤ hom a b :=
{ obj := inclusion_map,
  map := λ f g η, eq_to_hom (congr_arg inclusion_map (discrete.eq_of_hom η)) }

/-- The inclusion of paths into the free bicategory. -/
@[simps]
def inclusion_prelax : prelax_functor (locally_discrete (paths B)) (free_bicategory B) :=
{ obj := id,
  map := λ a b, (inclusion_map_functor a b).obj,
  map₂ := λ a b, (inclusion_map_functor a b).map }

/-- Auxiliary definition for `normalize_hom`. -/
@[simp]
def normalize_map {a : B} : ∀ {b c : B}, path a b → hom b c → path a c
| _ _ p (hom.of f) := p.cons f
| _ _ p (hom.id b) := p
| _ _ p (hom.comp f g) := normalize_map (normalize_map p f) g

@[simps]
def normalize_map_functor (a : B) {b c : B} (f : hom b c) :
  discrete (path.{v+1} a b) ⥤ discrete (path.{v+1} a c) :=
{ obj := λ p, normalize_map p f,
  map := λ g h η, eq_to_hom (congr_arg2 normalize_map (discrete.eq_of_hom η) rfl) }

@[simp]
def normalize_map₂ {a : B} : ∀ {b c : B} {f g : hom b c} (η : hom₂ f g),
  (normalize_map_functor a f ⟶ normalize_map_functor a g)
| _ _ _ _ (hom₂.id _) := 𝟙 _
| _ _ _ _ (hom₂.vcomp η θ) := normalize_map₂ η ≫ normalize_map₂ θ
| _ _ _ _ (hom₂.whisker_left f η) :=
    discrete.nat_trans (λ p, (normalize_map₂ η).app ((normalize_map_functor a f).obj p))
| _ _ _ _ (hom₂.whisker_right h η) :=
    discrete.nat_trans (λ p, (normalize_map_functor a h).map ((normalize_map₂ η).app p))
| _ _ _ _ (hom₂.associator f g h)     := 𝟙 _
| _ _ _ _ (hom₂.associator_inv f g h) := 𝟙 _
| _ _ _ _ (hom₂.left_unitor f)        := 𝟙 _
| _ _ _ _ (hom₂.left_unitor_inv f)    := 𝟙 _
| _ _ _ _ (hom₂.right_unitor f)       := 𝟙 _
| _ _ _ _ (hom₂.right_unitor_inv f)   := 𝟙 _

def normalize (a b c : B) : hom b c ⥤ discrete (path.{v+1} a b) ⥤ discrete (path.{v+1} a c) :=
{ obj := normalize_map_functor a,
  map := λ f g, quot.lift normalize_map₂ (by tidy) }

def normalize' (a b c : B) : hom b c ⥤ discrete (path.{v+1} a b) ⥤ hom a c :=
normalize _ _ _ ⋙ (whiskering_right _ _ _).obj (inclusion_map_functor _ _)

/-- The normalization functor for the free monoidal category over `C`. -/
def full_normalize : pseudofunctor (free_bicategory B) (locally_discrete (paths B)) :=
{ obj := id,
  map := λ a b f, ((normalize _ _ _).obj f).obj nil,
  map₂ := λ a b f g η, ((normalize _ _ _).map η).app nil,
  map_id := λ a, iso.refl (𝟙 a),
  map_comp := λ a b c f g, eq_to_iso
  begin
    induction g generalizing a,
    case id { refl },
    case of { refl },
    case comp : _ _ _ g _ ihf ihg { erw [ihg _ (f.comp g), ihf _ f, ihg _ g, assoc] }
  end }

def whisker_left_path (a b c : B) : hom b c ⥤ discrete (path.{v+1} a b) ⥤ hom a c :=
{ obj := λ f, discrete.functor (λ p, inclusion_prelax.map p ≫ f),
  map := λ f g η, discrete.nat_trans (λ p, inclusion_prelax.map p ◁ η) }

lemma whisker_left_path_obj_map
  (a : B) {b c : B} (f : hom b c) {p p' : discrete (path.{v+1} a b)} (η : p ⟶ p') :
  ((whisker_left_path _ _ _).obj f).map η = (inclusion_map_functor _ _).map η ▷ f :=
by tidy

/-- Auxiliary definition for `normalize_iso`. Here we construct the isomorphism between
    `n ⊗ X` and `normalize X n`. -/
@[simp]
def normalize_iso_app {a : B} : Π {b c : B} (f : hom b c) (p : path a b),
  ((whisker_left_path a b c).obj f).obj p ≅ ((normalize' a b c).obj f).obj p
| _ _ (hom.of f) p := iso.refl _
| _ _ (hom.id a) p := ρ_ (inclusion_prelax.map p)
| _ _ (hom.comp f g) p :=
    (α_ _ _ _).symm ≪≫ whisker_right_iso (normalize_iso_app f p) g ≪≫
      normalize_iso_app g (((normalize _ _ _).obj f).obj p)

@[simp]
def full_normalize_iso_app {a b : free_bicategory B} (f : a ⟶ b) :
  inclusion_prelax.map (𝟙 a) ≫ f ≅ inclusion_prelax.map ((full_normalize.map_functor a b).obj f) :=
normalize_iso_app f nil

/-- Auxiliary definition for `normalize_iso`. -/
@[simp]
def normalize_iso_aux (a : B) {b c : B} (f : hom b c) :
  (whisker_left_path a b c).obj f ≅ (normalize' a b c).obj f :=
nat_iso.of_components (normalize_iso_app f) (by tidy)

def normalize_iso (a b c : B) : whisker_left_path a b c ≅ normalize' a b c :=
nat_iso.of_components (normalize_iso_aux a)
begin
  rintros f g ⟨η⟩,
  ext p,
  dsimp only [whisker_left_path, normalize_iso_aux, nat_trans.comp_app, discrete.nat_trans_app,
    discrete.functor, nat_iso.of_components.hom_app],
  induction η,
  case id { erw [comp_id, bicategory.whisker_left_id, id_comp] },
  case vcomp : _ _ _ _ _ _ _ ihf ihg
  { simp only [mk_vcomp, bicategory.whisker_left_comp],
    slice_lhs 2 3 { rw ihg },
    slice_lhs 1 2 { rw ihf },
    slice_rhs 1 2 { erw (normalize' _ _ _).map_comp },
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
      ←whisker_left_path_obj_map] },
    slice_lhs 3 4 { erw (normalize_iso_aux _ _).hom.naturality ((normalize_map₂ _).app p) },
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

/-- The isomorphism between an object and its normal form is natural. -/
def full_normalize_unit_iso (a b : free_bicategory B) :
  𝟭 (a ⟶ b) ≅ full_normalize.map_functor _ _ ⋙ inclusion_map_functor _ _  :=
nat_iso.of_components (λ f, (λ_ f).symm ≪≫ full_normalize_iso_app f)
begin
  intros f g η,
  dsimp only [iso.trans_hom],
  slice_lhs 1 2 { erw left_unitor_inv_naturality },
  simp only [assoc],
  congr' 1,
  apply congr_arg (λ η, nat_trans.app η nil) ((normalize_iso _ _ _).hom.naturality η)
end

/-- The coherence theorem for bicategories. -/
instance locally_subsingleton {a b : free_bicategory B} (f g : a ⟶ b) : subsingleton (f ⟶ g) :=
subsingleton.intro
begin
  intros η θ,
  have H := λ η : f ⟶ g, nat_iso.naturality_2 (full_normalize_unit_iso _ _) η,
  erw [←functor.id_map η, ←functor.id_map θ, ←H η, ←H θ],
  refl
end

@[simp]
def inclusion_map_comp {a b : B} : ∀ {c : B} (f : path a b) (g : path b c),
  inclusion_prelax.map (f ≫ g) ≅ inclusion_prelax.map f ≫ inclusion_prelax.map g
| _ f nil := (ρ_ (inclusion_prelax.map f)).symm
| _ f (cons g₁ g₂) :=
    whisker_right_iso (inclusion_map_comp f g₁) (hom.of g₂) ≪≫ α_ _ _ _

 /-- The discrete subcategory of objects in normal form includes into the free monoidal category. -/
@[simps]
def inclusion : pseudofunctor (locally_discrete (paths B)) (free_bicategory B) :=
{ map_id := λ a, iso.refl (𝟙 a),
  map_comp := λ a b c f g, inclusion_map_comp f g,
  .. inclusion_prelax }

/-- The isomorphism between an object and its normal form is natural. -/
def full_normalize_counit_iso (a b : locally_discrete (paths B)) :
  (inclusion.map_functor _ _ ⋙ full_normalize.map_functor _ _ : (a ⟶ b) ⥤ _) ≅ 𝟭 (a ⟶ b) :=
nat_iso.of_components (λ f, eq_to_iso (by { induction f, tidy })) (by tidy)

instance locally_is_equivalence (a b : free_bicategory B) :
  is_equivalence (full_normalize.map_functor a b) :=
is_equivalence.mk (inclusion_map_functor a b)
  (full_normalize_unit_iso a b) (full_normalize_counit_iso _ _)

end free_bicategory

end category_theory
