/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Junyan Xu
-/

import category_theory.category.Cat
import category_theory.bicategory.natural_transformation
import category_theory.bicategory.locally_discrete
import category_theory.elements
import category_theory.over
import category_theory.limits.preserves.basic
import category_theory.adjunction.reflective
import category_theory.adjunction.limits

/-!
# The Grothendieck construction for lax functors

Given a lax functor `F` from a 1-category `C` to the 2-category `Cat`,
the objects of `grothendieck F` consist of dependent pairs `(b, f)`,
where `b : C` and `f : F.obj c`, and a morphism `(b, f) ⟶ (b', f')` is a
pair `β : b ⟶ b'` in `C`, and `φ : (F.map β).obj f ⟶ f'`. The forgetful
functor `grothendieck F ⥤ C` can be seen as a fibration of categories,
with base category `C`, total (Grothendieck) category `grothendieck F`,
and fiber categories `F.obj b`, `b : C`. When `F` is a pseudofunctor,
this is a Grothendieck fibration.

Notice that `F` gives a functor `F.map β` between fiber categories `F.obj b`
and `F.obj b'` for each morphism `β : b ⟶ b'` in `C`, which we call a component
functor. We show that if `F` is a pseudofunctor, the base category and all fiber
categories have colimits and the component functors all preserve colimits, then
the Grothendieck category also has colimits.

https://ncatlab.org/nlab/show/Grothendieck+construction#limits_and_colimits

In case all component functors have right adjoints, we can transfer the
lax functor structure of `F` across the adjunctions to obtain a lax functor
`G` from `Cᵒᵖ` to `Cat` with component functors opposites (`functor.op`) of
the right adjoints. We show that `grothendieck G` is isomorphic to the
opposite of `grothenieck F`, and we may show that `grothendieck F` has
limits by showing that `grothendieck G` has colimits.

(what about left adjoints?)

This will be used to construct the category `PrimedPreringedSpace` and
to show that `PresheafedSpace`, `SheafedSpace` and `PrimedPreringedSpace` has
(co)limits. Fibrations of categories such as `Top` over `Type`, or `PresheafedSpace`
over `Top` are also examples of this construction, and it may be preferable to
have the existence of (co)limits in `Top` refactored to use results here.

## References

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

See also `category_theory.elements` for the category of elements of functor `F : C ⥤ Type`.

-/

universes v' u' v u

namespace category_theory

variables {C : Type u} [category.{v} C] (F : oplax_functor (locally_discrete C) Cat.{v' u'})

/--
The Grothendieck construction (often written as `∫ F` in mathematics) for a functor `F : C ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : C` and `X.fiber : F.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`
-/
@[nolint has_inhabited_instance]
structure grothendieck :=
(base : C)
(fiber : F.obj base)

namespace grothendieck

variables {F}

/--
A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure hom (X Y : grothendieck F) :=
(base : X.base ⟶ Y.base)
(fiber : (F.map base).obj X.fiber ⟶ Y.fiber)

@[ext] lemma ext {X Y : grothendieck F} (f g : hom X Y)
  (w_base : f.base = g.base) (w_fiber : eq_to_hom (by rw w_base) ≫ f.fiber = g.fiber) : f = g :=
begin
  cases f; cases g,
  congr,
  dsimp at w_base,
  induction w_base,
  refl,
  dsimp at w_base,
  induction w_base,
  simpa using w_fiber,
end

/--
The identity morphism in the Grothendieck category.
-/
@[simps]
def id (X : grothendieck F) : hom X X :=
{ base := 𝟙 X.base,
  fiber := (F.map_id X.base).app X.fiber }

instance (X : grothendieck F) : inhabited (hom X X) := ⟨id X⟩


variables {W X Y : grothendieck F} {Z : C}

section fiber_push_map

variables (e : hom W X) (f : hom X Y) (g : Y.base ⟶ Z)

/-- Given a morphism `f : X ⟶ Y` in the Grothendieck category and a morphism in the
    base category `Y.base ⟶ Z`, there is a natural morphism from the "pushforward"
    of `X.fiber` to `Z` and the "pushforward" of `Y.fiber` to `Z`. This will be used
    to define composition in the Grothendieck category, as well as a functor from the
    costructured arrow category over `Z` to the fiber category over `Z`. -/
def fiber_push_map : (F.map (f.base ≫ g)).obj X.fiber ⟶ (F.map g).obj Y.fiber :=
(F.map_comp f.base g).app X.fiber ≫ (F.map g).map f.fiber

/--
Composition of morphisms in the Grothendieck category.
-/
@[simps]
def comp : hom W Y :=
{ base := e.base ≫ f.base,
  fiber := fiber_push_map e f.base ≫ f.fiber }

instance : category (grothendieck F) :=
{ hom := λ X Y, grothendieck.hom X Y,
  id := λ X, grothendieck.id X,
  comp := λ X Y Z f g, grothendieck.comp f g,
  id_comp' := λ X Y f, by { ext, { dsimp [fiber_push_map], simp }, simp },
  comp_id' := λ X Y f, by { ext, { dsimp [fiber_push_map], simp }, simp },
  assoc' := λ W X Y Z e f g, by { ext, { dsimp [fiber_push_map], simp }, simp } }

end fiber_push_map

@[simp] lemma id_base' : hom.base (𝟙 X) = 𝟙 X.base := rfl

@[simp] lemma id_fiber' (X : grothendieck F) :
  hom.fiber (𝟙 X) = (F.map_id X.base).app X.fiber := rfl

lemma congr {X Y : grothendieck F} {f g : X ⟶ Y} (h : f = g) :
  f.fiber = eq_to_hom (by rw h) ≫ g.fiber := by { subst h, simp }

section fiber_push_map

variables {Z' : C} (e : W ⟶ X) (f : X ⟶ Y) (g : Y.base ⟶ Z) (h : Z ⟶ Z')

@[simp] lemma comp_base' : (e ≫ f).base = e.base ≫ f.base := rfl

@[simp] lemma comp_fiber' : (e ≫ f).fiber = fiber_push_map e f.base ≫ f.fiber := rfl

@[simp]
lemma fiber_push_map_id_left : fiber_push_map (𝟙 Y) g = eq_to_hom (by simp) :=
by { dsimp [fiber_push_map], simpa }

@[simp]
lemma fiber_push_map_id_right : (f ≫ 𝟙 Y).fiber = eq_to_hom (by simp) ≫ f.fiber :=
congr (by simp)

@[simp, reassoc]
lemma fiber_push_map_comp_left : fiber_push_map (e ≫ f) g =
  eq_to_hom (by simp) ≫ fiber_push_map e (f.base ≫ g) ≫ fiber_push_map f g :=
by { dsimp [fiber_push_map], simp }

@[simp, reassoc]
lemma fiber_push_map_comp_right : fiber_push_map f (g ≫ h) ≫ (F.map_comp _ _).app _ =
  eq_to_hom (by simp) ≫ (F.map_comp _ _).app _ ≫ (F.map h).map (fiber_push_map f g) :=
by { dsimp [fiber_push_map], simp }

end fiber_push_map

section
variables (F)

/-- The forgetful functor from `grothendieck F` to the source category. -/
@[simps]
def forget : grothendieck F ⥤ C :=
{ obj := λ X, X.1,
  map := λ X Y f, f.1 }

section has_terminal

variables [∀ X, limits.has_terminal (F.obj X).1]

/-- If every fiber category has a terminal object, a functor from the base category
    to the Grothendieck category is obtained by using the terminal objects as fibers. -/
noncomputable def with_terminal_fiber : C ⥤ grothendieck F :=
{ obj := λ X, { base := X, fiber := limits.terminal (F.obj X).1 },
  map := λ X Y f, { base := f, fiber := limits.terminal.from _ } }

/-- Adjunction between the forgetful functor and the "with terminal object as fiber"
    functor. -/
noncomputable def forget_terminal_adjunction : forget F ⊣ with_terminal_fiber F :=
adjunction.mk_of_unit_counit
{ unit := { app := λ X, ⟨𝟙 _, limits.terminal.from _⟩ },
  counit := { app := λ X, 𝟙 _ } }

/-- `with_terminal_fiber` is reflective. -/
noncomputable instance : reflective (with_terminal_fiber F) :=
{ to_is_right_adjoint := { left := forget F, adj := forget_terminal_adjunction F },
  to_full := { preimage := λ _ _ f, f.base },
  to_faithful := { map_injective' := λ _ _ _ _ h, congr_arg hom.base h } }

/-- If every fiber category has a terminal object, then the forgetful functor preserves
    colimits. -/
noncomputable instance : limits.preserves_colimits_of_size.{v u} (forget F) :=
adjunction.left_adjoint_preserves_colimits (forget_terminal_adjunction F)

end has_terminal

/-- Given an object `Y` in the Grothendieck category and a morphism `f` from its base to
    an object `X` in the base category, we may push the fiber object of `Y` to a fiber
    object over `X`, and this is functorial in `f`, with `X` fixed. -/
@[simps obj]
def fiber_push (X : C) : costructured_arrow (forget F) X ⥤ (F.obj X).1 :=
{ obj := λ f, (F.map f.hom).obj f.left.fiber,
  map := λ f₁ f₂ g, eq_to_hom (by erw costructured_arrow.w g) ≫ fiber_push_map g.left f₂.hom,
  map_id' := λ f, by { dsimp, simp },
  map_comp' := λ _ _ _ g₁ g₂, by { rw eq_to_hom.family_congr
    (fiber_push_map g₁.left) (costructured_arrow.w g₂).symm, dsimp, simp } }

/-- Given an morphism `f : Y ⟶ X` in the Grothendieck category, we obtain a morphism from
    `(fiber_push X.base).obj f` to `X.fiber`, and this is functorial in `f`, with `X` fixed. -/
def fiber_push_over (X : grothendieck F) : over X ⥤ over X.fiber :=
{ obj := λ f, over.mk f.hom.fiber,
  map := λ _ _ g, over.hom_mk
    ((fiber_push F X.base).map ((costructured_arrow.post _ (forget F) _).map g))
    (by {rw congr (over.w g).symm, dsimp [fiber_push], simpa}) }

/-- `fiber_push X` is natural in `X`: it is a 2-natural transformation between two lax
    functors `costructured_arrow` and `F` from the base category to `Cat`. -/
def fiber_push_naturality {X Y : C} (f : X ⟶ Y) :
  costructured_arrow.map f ⋙ fiber_push F Y ⟶ fiber_push F X ⋙ F.map f :=
{ app := λ e, (F.map_comp e.hom f).app e.left.fiber,
  naturality' := λ f₁ f₂ g, by { let fn := λ g, F.map_comp g f,
    have := eq_to_hom.family_congr fn (costructured_arrow.w g).symm,
    dsimp [fn, fiber_push] at ⊢ this, simp [this] } }

/-
def costructured_arrow_map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  costructured_arrow.map (f ≫ g) ⟶ costructured_arrow.map f ⋙ costructured_arrow.map g :=
{ app :=

}

def fiber_push_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  fiber_push_naturality F (f ≫ g) ≫ whisker_left (fiber_push F X) (F.map_comp f g) =
  eq_to_hom (by { apply functor.hext, intro, simp, intros, dsimp, congr' 1,apply comma_morphism.ext,  ext, simp, intros, simp, ext,  }) ≫
  whisker_left (costructured_arrow.map f) (fiber_push_naturality F g) ≫
  whisker_right (fiber_push_naturality F f) (F.map g)
-/

/- what about the functor from `(F.obj X).1` to `grothendieck F`'s fiber over `X` ?
    the "fiber category" is indeed isomorphic to the fiber over a point in the base category ...
    restrict to identity on base -/

end

section colimit

open limits

variables {J : Type u} [category.{v} J] {𝒟 : J ⥤ grothendieck F}
(cb cb₁ cb₂ : cocone (𝒟 ⋙ forget F)) (c : cocone 𝒟)

/-- From a diagram `𝒟` in the Grothendieck category, `𝒟 ⋙ forget F` is its "projection"
    to the base category. Given and a cocone over the projection, obtain a diagram in the
    fiber category over the cocone point. -/
def fiber_diagram : J ⥤ (F.obj cb.X).1 :=
costructured_arrow.of_cocone _ _ cb.ι ⋙ costructured_arrow.pre _ _ _ ⋙ fiber_push _ _

lemma fiber_diagram_map {j j' : J} (f : j ⟶ j') :
  (fiber_diagram ((forget F).map_cocone c)).map f =
  (@functor.map _ _ _ _ (fiber_push_over F c.X)
    (over.mk (c.ι.app j)) (over.mk (c.ι.app j')) (over.hom_mk (𝒟.map f))).left := rfl

/-- From a diagram in the Grothendieck category and a cocone over it, obtain a cocone
    over the `fiber_diagram` of the projected cocone. -/
def fiber_cocone : cocone (fiber_diagram ((forget F).map_cocone c)) :=
{ X := c.X.fiber,
  ι := { app := λ j, ((fiber_push_over F c.X).obj (over.mk (c.ι.app j))).hom,
    naturality' := λ j j' f, by { dsimp [fiber_diagram_map], simp } } }

variables ⦃cb₁ cb₂⦄ (fb₀ : cb ⟶ cb₁) (fb : cb₁ ⟶ cb₂)

def fiber_trans : fiber_diagram cb₂ ⟶ fiber_diagram cb₁ ⋙ F.map fb.hom :=
{ app := λ j, eq_to_hom (by {dsimp, erw fb.w, refl}) ≫ (fiber_push_naturality F fb.hom).app _,
  naturality' := λ j j' f, by { rw category.assoc,
    erw ← nat_trans.naturality, dsimp [fiber_diagram, fiber_push],
    erw eq_to_hom.family_congr (fiber_push_map _) (fb.w j'), simpa } }

variable (𝒟)

@[simps]
def fiber_cocone_prefunctor : prefunctor (cocone (𝒟 ⋙ forget F)) Cat :=
{ obj := λ cb, ⟨cocone (fiber_diagram cb)⟩,
  map := λ _ _ fb, cocones.functoriality _ (F.map fb.hom) ⋙ cocones.precompose (fiber_trans fb) }

@[simps]
def fiber_cocone_map_id : (fiber_cocone_prefunctor 𝒟).map (𝟙 cb) ⟶ 𝟭 _ :=
{ app := λ cf, { hom := (F.map_id cb.X).app cf.X,
    w' := λ j, by { dsimp [fiber_trans, fiber_push_naturality, fiber_diagram], simpa } } }

variables ⦃cb⦄
@[simps]
def fiber_cocone_map_comp : (fiber_cocone_prefunctor 𝒟).map (fb₀ ≫ fb) ⟶
  (fiber_cocone_prefunctor 𝒟).map fb₀ ⋙ (fiber_cocone_prefunctor 𝒟).map fb :=
{ app := λ cf,
  { hom := (F.map_comp fb₀.hom fb.hom).app cf.X,
    w' := λ j, by { let fn := λ f, F.map_comp f fb.hom,
      have := eq_to_hom.family_congr fn (fb₀.w j).symm,
      dsimp [fiber_trans, fiber_push_naturality, fiber_diagram, fn] at this ⊢,
      simpa [this] } },
  naturality' := λ _ _ ff,
    cocone_morphism.ext _ _ ((F.map_comp fb₀.hom fb.hom).naturality ff.hom) }

def fiber_cocone_functor : lax_functor_to_Cat (cocone (𝒟 ⋙ forget F)) :=
{ to_prefunctor := fiber_cocone_prefunctor 𝒟,
  map_id := fiber_cocone_map_id 𝒟,
  map_comp := fiber_cocone_map_comp 𝒟,
  id_comp := by { intros, ext, dsimp, simpa },
  comp_id := by { intros, ext, dsimp, simpa },
  assoc := by { intros, ext, dsimp, simpa } }

@[simps]
def cocone_to_grothendieck : cocone 𝒟 ⥤ grothendieck (fiber_cocone_functor 𝒟) :=
{ obj := λ c, { base := (forget F).map_cocone c, fiber := fiber_cocone c },
  map := λ c₁ c₂ f,
  { base := { hom := f.hom.base, w' := λ j, congr_arg hom.base (f.w j) } ,
    fiber := { hom := f.hom.fiber,
      w' := λ j, by { convert (congr (f.w j).symm).symm using 1,
        dsimp [fiber_cocone_functor, fiber_trans, fiber_push_naturality, fiber_push_map],
        simpa } } } }

variables {𝒟} (cb) (cf : cocone (fiber_diagram cb))
/-- From a cocone over the projected diagram in the base category and a cocone over its
    `fiber_diagram`, obtain a cocone over the diagram upstairs in the Grothendieck category. -/
@[simps]
def total_cocone : cocone 𝒟 :=
{ X := { base := cb.X, fiber := cf.X },
  ι := { app := λ j, { base := cb.ι.app j, fiber := cf.ι.app j },
    naturality' := λ j j' f, by { erw category.comp_id, ext,
    { erw ← category.assoc, exact cocone.w cf f }, exact cocone.w cb f } } }

variable (𝒟)
@[simps]
def grothendieck_to_cocone : grothendieck (fiber_cocone_functor 𝒟) ⥤ cocone 𝒟 :=
{ obj := λ c, total_cocone c.base c.fiber,
  map := λ c₁ c₂ f,
  { hom := { base := f.base.hom, fiber := f.fiber.hom },
    w' := λ j, by { ext, { convert f.fiber.w j using 1,
      dsimp [fiber_cocone_functor, fiber_trans, fiber_push_naturality, fiber_push_map],
      simpa }, simp } } }

def cocone_grothendieck_counit : grothendieck_to_cocone 𝒟 ⋙ cocone_to_grothendieck 𝒟 ⟶ 𝟭 _ :=
{ app := λ c,
  { base := { hom := 𝟙 _, w' := λ j, by { dsimp, simp } },
    fiber := { hom := (F.map_id c.base.X).app c.fiber.X,
      w' := λ j, by {dsimp [fiber_cocone_functor, fiber_cocone, fiber_trans,
        fiber_push_over, fiber_push_naturality, fiber_diagram], simpa } } },
  naturality' := λ c₁ c₂ f, by { ext, dsimp [fiber_push_map], simp, },
}


def cocone_grothendieck_adjunction : cocone_to_grothendieck 𝒟 ⊣ grothendieck_to_cocone 𝒟 :=
adjunction.mk_of_unit_counit
{ unit :=
  { app := λ c,
    { hom := { base := 𝟙 _, fiber := (F.map_id c.X.base).app c.X.fiber },
      w' := λ j, by { ext,
        exact (congr (category.comp_id (c.ι.app j)).symm).symm, { dsimp, simp } } },
    naturality' := λ _ _ _, by { ext, { dsimp [fiber_push_map], simpa }, simp } },
  counit :=
  { app := λ c,
    { base := { hom := 𝟙 _, w' := λ j, by { dsimp, simp } },
      fiber := { hom := (F.map_id c.base.X).app c.fiber.X,
        w' := λ j, by { dsimp [fiber_cocone_functor, fiber_cocone, fiber_trans,
          fiber_push_over, fiber_push_naturality, fiber_diagram], simpa } } },
    naturality' := λ c₁ c₂ f, by { ext, { dsimp [fiber_push_map], simpa} , simp } },
}

-- first construct adjunction! may not use inverse of map_id, map_comp
-- what does adjunction say about initial object/preserve colimits?
-- !! isomorphism in grothendieck F in terms of base and fiber!
-- maybe over X and under X are also fibered categories? and costructured_arrow category?
def cocone_grothendieck_equivalence : cocone 𝒟 ≌ grothendieck (fiber_cocone_functor 𝒟) :=
{ functor := cocone_to_grothendieck 𝒟,
  inverse := grothendieck_to_cocone 𝒟,
  unit_iso :=
  { hom :=
    { app := λ c, { hom := { base := 𝟙 _, fiber := (F.map_id c.X.base).app c.X.fiber },
        w' := λ j, by { ext, exact (congr (category.comp_id (c.ι.app j)).symm).symm,
          { dsimp, simp } } },
      naturality' := λ c₁ c₂ f, by { ext, { dsimp [fiber_push_map], simpa }, simp } },
    inv := , }
}

def total_cocone_hom (ff : fiber_cocone_trans c cf fb ⟶ fiber_cocone c) :
  total_cocone cb cf ⟶ c :=
{ hom := { base := fb.hom, fiber := ff.hom },
  w' := λ j, by { ext, swap, exact fb.w j,
    { convert ff.w j using 1, dsimp, simp [fiber_push_total_cocone] } } }

def id_cocone_hom {cf} (ff : cf ⟶ fiber_cocone c) :
  total_cocone ((forget F).map_cocone c) cf ⟶ c :=
total_cocone_hom c cf
{ hom := 𝟙 _, w' := λ j, by erw category.comp_id }
{ hom := (F.map_id _).app _ ≫ ff.hom,
  w' := λ j, by { dsimp [fiber_trans, fiber_push_comp, fiber_diagram], simp } }

lemma id_cocone_hom_base (h : is_colimit c) {cf}
  (f : c ⟶ total_cocone ((forget F).map_cocone c) cf) : f.hom.base = 𝟙 _ :=
by { have := h.uniq_cocone_morphism, swap 3, exact id_cocone_hom}


def id_cocone_iso (h : is_colimit c) {cf} (hf : is_colimit cf) :
  total_cocone ((forget F).map_cocone c) cf ≅ c :=
{ hom := id_cocone_hom c (hf.desc_cocone_morphism _),
  inv := h.desc_cocone_morphism _,
  hom_inv_id' := by { ext, dsimp, exact hf.uniq_cocone_morphism, },
  inv_hom_id' := h.uniq_cocone_morphism }

/-- If the a cocone in the Grothendieck category is a colimit, then its `fiber_cocone`
    is also a colimit, provided that the underlying diagram has a colimit. -/
def is_colimit_fiber_of_is_colimit (h : is_colimit c)
  (hf : has_colimit (fiber_diagram ((forget F).map_cocone c))) :
  is_colimit (fiber_cocone c) :=
is_colimit.of_iso_colimit (colimit.is_colimit _)
{ hom := (colimit.is_colimit _).desc_cocone_morphism (fiber_cocone c),
  inv := }
/-(cocones.ext
{ hom := (colimit.is_colimit _).desc (fiber_cocone c),
  inv := by { let := (h.desc (total_cocone ((forget F).map_cocone c) (colimit.cocone _))).fiber,
  dsimp at this ⊢ ,
    --(h.desc (total_cocone ((forget F).map_cocone c) (colimit.cocone _))).fiber
    },
  hom_inv_id' := _,
  inv_hom_id' := _ }
(by { }))-/

/-{ desc := λ cf, by { let := (h.desc (total_cocone _ cf)).fiber, dsimp at this ⊢, },
  fac' := _,
  uniq' := _ }-/

variables {cb} (lb : is_colimit cb)

def desc_base : cb.X ⟶ c.X.base := lb.desc ((forget F).map_cocone c)



variable [∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z), is_iso (F.map_comp f g)]

instance {X Y : C} (f : X ⟶ Y) : is_iso (fiber_push_comp F f) :=
by { fapply nat_iso.is_iso_of_is_iso_app _, dsimp [fiber_push_comp], apply_instance }

instance : is_iso (fiber_trans c lb) :=
by { fapply nat_iso.is_iso_of_is_iso_app _, dsimp [fiber_trans], apply_instance }


variables {cf} (lf : ∀ {c : C} (f : cb.X ⟶ c), is_colimit (functor.map_cocone (F.map f) cf))

noncomputable def total_cocone_is_colimit : is_colimit (total_cocone cb cf) :=
let cf' := λ c, (cocones.precompose (inv (fiber_trans c lb))).obj (fiber_cocone c) in
{ desc := λ c,
  { base := desc_base c lb,
    fiber := (lf (desc_base c lb)).desc (cf' c) },
  fac' := λ c j, by { ext, swap, apply lb.fac,
    { dsimp, simp only [fiber_push_total_cocone, category.assoc], erw (lf _).fac, simpa } },
  uniq' := λ c f h, by {
    have := lb.uniq ((forget F).map_cocone c) f.base (λ j, by {dsimp, rw ← h, refl}),
    ext, swap, exact this,
    { apply (lf _).uniq (cf' c), intro j,
      change _ = _ ≫ (c.ι.app j).fiber, rw congr (h j).symm, dsimp,
      rw eq_to_hom.family_congr (fiber_push_map _) this, erw fiber_push_total_cocone, simpa } } }

/-- forgetful functor preserves colimit .. whenever colimit exist?
    or whenever both the base and fiber categories has colimits ...
    whenever Hb Hf Hp all holds .. -/

variables [Hb : has_colimits_of_shape J C]
[Hf : ∀ X : C, has_colimits_of_shape J (F.obj X).1]
(Hp : ∀ {X Y : C} (f : X ⟶ Y), preserves_colimits_of_shape J (F.map f))

include Hb Hf Hp
lemma has_colimits_of_shape : has_colimits_of_shape J (grothendieck F) :=
{ has_colimit := λ 𝒟, { exists_colimit := ⟨ { cocone := _, is_colimit :=
  let base := get_colimit_cocone (𝒟 ⋙ forget F) in
  total_cocone_is_colimit base.is_colimit (λ _ f,
    is_colimit_of_preserves _ (get_colimit_cocone (fiber_diagram base.cocone)).is_colimit ) } ⟩ } }
omit Hp

open adjunction

lemma has_colimits_of_shape_of_left_adjoint
  (H : ∀ {X Y : C} (f : X ⟶ Y), is_left_adjoint (F.map f)) :
  limits.has_colimits_of_shape J (grothendieck F) :=
has_colimits_of_shape
  (λ _ _ f, by apply (left_adjoint_preserves_colimits (of_left_adjoint (F.map f))).1)

end colimit

#set_option pp.universes true

#check has_colimits_of_shape_of_left_adjoint

/-
section

variables (G : pseudofunctor_to_Cat C) (X : grothendieck G.to_lax_functor_to_Cat)

@[simps obj map]
noncomputable def cleavage : under X.base ⥤ under X :=
{ obj := λ f, ⟨punit.star, ⟨f.right, (G.map f.hom).obj X.fiber⟩, ⟨f.hom, 𝟙 _⟩⟩,
  map := λ f₁ f₂ g, ⟨𝟙 _,
    ⟨g.right, (inv (G.map_comp f₁.hom g.right) ≫ eq_to_hom (by rw under.w g)).app X.fiber⟩,
    by { erw category.id_comp, ext1, {erw comp_fiber, dsimp, simpa}, exact (under.w g).symm }⟩,
  map_id' := λ f, by {ext1, ext1, {dsimp, simpa}, refl},
  map_comp' := λ f₁ f₂ f₃ g₁ g₂, by { congr, dsimp,
    have h := (G.1.assoc_components f₁.hom g₁.right g₂.right X.fiber).symm,
    let a := λ f, G.map_comp f g₂.right, have b := under.w g₁,
    have h' := eq_to_hom.family_congr a b, dsimp [a] at h',
    rw [h', ← category.assoc, ← is_iso.eq_comp_inv, ← is_iso.inv_eq_inv] at h,
    convert eq_whisker h (eq_to_hom (by simp : _ = (G.map f₃.hom).obj X.fiber)) using 1,
    simp, simpa } }

def cleavage_forget_counit : under.post (forget G.1) ⋙ cleavage G X ⟶ 𝟭 (under X) :=
{ app := λ f, ⟨eq_to_hom (by simp), ⟨𝟙 _, (G.map_id _).app _ ≫ f.hom.fiber⟩,
    by { dsimp, rw category.id_comp, ext,
      { erw comp_fiber, dsimp, simpa }, { erw comp_base, simp } }⟩,
  naturality' := λ f₁ f₂ g, by { ext,
    { dsimp, erw [comp_fiber, comp_fiber], dsimp, simp, } }}


def cleavage_forget_adjunction :
  cleavage G X ⊣ under.post (forget G.1) := adjunction.mk_of_unit_counit
{ unit := eq_to_hom $ by { apply functor.hext, { rintro ⟨⟨_⟩,_⟩, refl },
    { rintros ⟨⟨_⟩,_⟩ ⟨⟨_⟩,_⟩ ⟨⟨_⟩,_⟩, dsimp, congr } },
  counit := ,
  left_triangle' := ,
  right_triangle' := }

end
-/
universe w
variables (G : C ⥤ Type w)

/-- Auxiliary definition for `grothendieck_Type_to_Cat`, to speed up elaboration. -/
@[simps]
def grothendieck_Type_to_Cat_functor : grothendieck (G ⋙ Type_to_Cat).to_lax ⥤ G.elements :=
{ obj := λ X, ⟨X.1, X.2⟩,
  map := λ X Y f, ⟨f.1, f.2.1.1⟩ }

/-- Auxiliary definition for `grothendieck_Type_to_Cat`, to speed up elaboration. -/
@[simps]
def grothendieck_Type_to_Cat_inverse : G.elements ⥤ grothendieck (G ⋙ Type_to_Cat).to_lax :=
{ obj := λ X, ⟨X.1, X.2⟩,
  map := λ X Y f, ⟨f.1, ⟨⟨f.2⟩⟩⟩ }

/--
The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
@[simps]
def grothendieck_Type_to_Cat : grothendieck (G ⋙ Type_to_Cat).to_lax ≌ G.elements :=
{ functor := grothendieck_Type_to_Cat_functor G,
  inverse := grothendieck_Type_to_Cat_inverse G,
  unit_iso := nat_iso.of_components (λ X, by { cases X, exact iso.refl _, })
    (by { rintro ⟨⟩ ⟨⟩ ⟨base, ⟨⟨f⟩⟩⟩, dsimp at *, subst f, ext, simp, }),
  counit_iso := nat_iso.of_components (λ X, by { cases X, exact iso.refl _, })
    (by { rintro ⟨⟩ ⟨⟩ ⟨f, e⟩, dsimp at *, subst e, ext, simp, }),
  functor_unit_iso_comp' := by { rintro ⟨⟩, dsimp, simp, refl, } }

end grothendieck

end category_theory
