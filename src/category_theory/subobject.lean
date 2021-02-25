/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison
-/
import category_theory.opposites
import category_theory.full_subcategory
import category_theory.skeletal
import category_theory.currying
import category_theory.limits.lattice
import category_theory.limits.over
import category_theory.limits.shapes.images
import category_theory.limits.shapes.kernels
import category_theory.monad.adjunction

/-!
# The lattice of subobjects

We define `subobject X` as the quotient (by isomorphisms) of
`mono_over X := {f : over X // mono f.hom}`.

Here `mono_over X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not a partial order.

There is a coercion from `subobject X` back to the ambient category `C`
(using choice to pick a representative), and for `P : subobject X`,
`P.arrow : (P : C) ⟶ X` is the inclusion morphism.

The predicate `h : P.factors f`, for `P : subobject Y` and `f : X ⟶ Y`
asserts the existence of some `P.factor_thru f : X ⟶ (P : C)` making the obvious diagram commute.
We provide conditions for `P.factors f`, when `P` is a kernel/equalizer/image/inf/sup subobject.

TODO: Add conditions for when `P` is a pullback subobject.

We provide
* `def pullback [has_pullbacks C] (f : X ⟶ Y) : subobject Y ⥤ subobject X`
* `def map (f : X ⟶ Y) [mono f] : subobject X ⥤ subobject Y`
* `def «exists» [has_images C] (f : X ⟶ Y) : subobject X ⥤ subobject Y`
(each first at the level of `mono_over`), and prove their basic properties and relationships.

We also provide the `semilattice_inf_top (subobject X)` instance when `[has_pullback C]`,
and the `semilattice_sup (subobject X)` instance when `[has_images C] [has_binary_coproducts C]`.

## Notes

This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Scott Morrison.

### Implementation note

Currently we describe `pullback`, `map`, etc., as functors.
It may be better to just say that they are monotone functions,
and even avoid using categorical language entirely when describing `subobject X`.
(It's worth keeping this in mind in future use; it should be a relatively easy change here
if it looks preferable.)

### Relation to pseudoelements

There is a separate development of pseudoelements in `category_theory.abelian.pseudoelements`,
as a quotient (but not by isomorphism) of `over X`.

When a morphism `f` has an image, it represents the same pseudoelement.
In a category with images `pseudoelements X` could be constructed as a quotient of `mono_over X`.
In fact, in an abelian category (I'm not sure in what generality beyond that),
`pseudoelements X` agrees with `subobject X`, but we haven't developed this in mathlib yet.

-/

universes v₁ v₂ u₁ u₂

noncomputable theory
namespace category_theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v₁} C] {X Y Z : C}
variables {D : Type u₂} [category.{v₂} D]

/--
The category of monomorphisms into `X` as a full subcategory of the over category.
This isn't skeletal, so it's not a partial order.

Later we define `subobject X` as the quotient of this by isomorphisms.
-/
@[derive [category, λ t, has_coe t (over X)]]
def mono_over (X : C) := {f : over X // mono f.hom}

attribute [priority 100] mono_over.has_coe

namespace mono_over

/-- Construct a `mono_over X`. -/
@[simps]
def mk' {X A : C} (f : A ⟶ X) [hf : mono f] : mono_over X := { val := over.mk f, property := hf }

/-- The inclusion from monomorphisms over X to morphisms over X. -/
def forget (X : C) : mono_over X ⥤ over X := full_subcategory_inclusion _

@[simp]
lemma forget_obj_left {f} : ((forget X).obj f).left = f.val.left := rfl

/-- Convenience notation for the underlying arrow of a monomorphism over X. -/
abbreviation arrow (f : mono_over X) : _ ⟶ X := ((forget X).obj f).hom

@[simp] lemma mk'_arrow {X A : C} (f : A ⟶ X) [hf : mono f] : (mk' f).arrow = f := rfl

@[simp]
lemma forget_obj_hom {f} : ((forget X).obj f).hom = f.arrow := rfl

instance : full (forget X) := full_subcategory.full _
instance : faithful (forget X) := full_subcategory.faithful _

instance mono (f : mono_over X) : mono f.arrow := f.property

/-- The category of monomorphisms over X is a thin category,
which makes defining its skeleton easy. -/
instance is_thin {X : C} (f g : mono_over X) : subsingleton (f ⟶ g) :=
⟨begin
  intros h₁ h₂,
  ext1,
  erw [← cancel_mono g.arrow, over.w h₁, over.w h₂],
end⟩

@[reassoc] lemma w {f g : mono_over X} (k : f ⟶ g) : k.left ≫ g.arrow = f.arrow := over.w _

/-- Convenience constructor for a morphism in monomorphisms over `X`. -/
abbreviation hom_mk {f g : mono_over X} (h : f.val.left ⟶ g.val.left) (w : h ≫ g.arrow = f.arrow) :
  f ⟶ g :=
over.hom_mk h w

/-- Convenience constructor for an isomorphism in monomorphisms over `X`. -/
@[simps]
def iso_mk {f g : mono_over X} (h : f.val.left ≅ g.val.left) (w : h.hom ≫ g.arrow = f.arrow) :
  f ≅ g :=
{ hom := hom_mk h.hom w,
  inv := hom_mk h.inv (by rw [h.inv_comp_eq, w]) }

/--
Lift a functor between over categories to a functor between `mono_over` categories,
given suitable evidence that morphisms are taken to monomorphisms.
-/
@[simps]
def lift {Y : D} (F : over Y ⥤ over X)
  (h : ∀ (f : mono_over Y), mono (F.obj ((mono_over.forget Y).obj f)).hom) :
  mono_over Y ⥤ mono_over X :=
{ obj := λ f, ⟨_, h f⟩,
  map := λ _ _ k, (mono_over.forget X).preimage ((mono_over.forget Y ⋙ F).map k), }

/--
Isomorphic functors `over Y ⥤ over X` lift to isomorphic functors `mono_over Y ⥤ mono_over X`.
-/
def lift_iso {Y : D} {F₁ F₂ : over Y ⥤ over X} (h₁ h₂) (i : F₁ ≅ F₂) :
  lift F₁ h₁ ≅ lift F₂ h₂ :=
fully_faithful_cancel_right (mono_over.forget X) (iso_whisker_left (mono_over.forget Y) i)

/-- `mono_over.lift` commutes with composition of functors. -/
def lift_comp {X Z : C} {Y : D} (F : over X ⥤ over Y) (G : over Y ⥤ over Z) (h₁ h₂) :
  lift F h₁ ⋙ lift G h₂ ≅ lift (F ⋙ G) (λ f, h₂ ⟨_, h₁ f⟩) :=
fully_faithful_cancel_right (mono_over.forget _) (iso.refl _)

/-- `mono_over.lift` preserves the identity functor. -/
def lift_id :
  lift (𝟭 (over X)) (λ f, f.2) ≅ 𝟭 _ :=
fully_faithful_cancel_right (mono_over.forget _) (iso.refl _)

@[simp]
lemma lift_comm (F : over Y ⥤ over X)
  (h : ∀ (f : mono_over Y), mono (F.obj ((mono_over.forget Y).obj f)).hom) :
  lift F h ⋙ mono_over.forget X = mono_over.forget Y ⋙ F :=
rfl

/--
Monomorphisms over an object `f : over A` in an over category
are equivalent to monomorphisms over the source of `f`.
-/
def slice {A : C} {f : over A} (h₁ h₂) : mono_over f ≌ mono_over f.left :=
{ functor := mono_over.lift f.iterated_slice_equiv.functor h₁,
  inverse := mono_over.lift f.iterated_slice_equiv.inverse h₂,
  unit_iso := mono_over.lift_id.symm ≪≫
    mono_over.lift_iso _ _ f.iterated_slice_equiv.unit_iso ≪≫
    (mono_over.lift_comp _ _ _ _).symm,
  counit_iso := mono_over.lift_comp _ _ _ _ ≪≫
    mono_over.lift_iso _ _ f.iterated_slice_equiv.counit_iso ≪≫
    mono_over.lift_id }

/-- When `f : X ⟶ Y` and `P : mono_over Y`,
`P.factors f` expresses that there exists a factorisation of `f` through `P`.
Given `h : P.factors f`, you can recover the morphism as `P.factor_thru f h`.
-/
def factors {X Y : C} (P : mono_over Y) (f : X ⟶ Y) : Prop := ∃ g : X ⟶ P.val.left, g ≫ P.arrow = f

/-- `P.factor_thru f h` provides a factorisation of `f : X ⟶ Y` through some `P : mono_over Y`,
given the evidence `h : P.factors f` that such a factorisation exists. -/
def factor_thru {X Y : C} (P : mono_over Y) (f : X ⟶ Y) (h : factors P f) : X ⟶ P.val.left :=
classical.some h

section pullback
variables [has_pullbacks C]

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `mono_over Y ⥤ mono_over X`,
by pulling back a monomorphism along `f`. -/
def pullback (f : X ⟶ Y) : mono_over Y ⥤ mono_over X :=
mono_over.lift (over.pullback f)
begin
  intro g,
  apply @pullback.snd_of_mono _ _ _ _ _ _ _ _ _,
  change mono g.arrow,
  apply_instance,
end

/-- pullback commutes with composition (up to a natural isomorphism) -/
def pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) : pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
lift_iso _ _ (over.pullback_comp _ _) ≪≫ (lift_comp _ _ _ _).symm

/-- pullback preserves the identity (up to a natural isomorphism) -/
def pullback_id : pullback (𝟙 X) ≅ 𝟭 _ :=
lift_iso _ _ over.pullback_id ≪≫ lift_id

@[simp] lemma pullback_obj_left (f : X ⟶ Y) (g : mono_over Y) :
(↑((pullback f).obj g) : over X).left = limits.pullback g.arrow f :=
rfl

@[simp] lemma pullback_obj_arrow (f : X ⟶ Y) (g : mono_over Y) :
((pullback f).obj g).arrow = pullback.snd :=
rfl

end pullback

section map

attribute [instance] mono_comp

/--
We can map monomorphisms over `X` to monomorphisms over `Y`
by post-composition with a monomorphism `f : X ⟶ Y`.
-/
def map (f : X ⟶ Y) [mono f] : mono_over X ⥤ mono_over Y :=
lift (over.map f)
(λ g, by apply mono_comp g.arrow f)

/-- `mono_over.map` commutes with composition (up to a natural isomorphism). -/
def map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] :
  map (f ≫ g) ≅ map f ⋙ map g :=
lift_iso _ _ (over.map_comp _ _) ≪≫ (lift_comp _ _ _ _).symm

/-- `mono_over.map` preserves the identity (up to a natural isomorphism). -/
def map_id : map (𝟙 X) ≅ 𝟭 _ :=
lift_iso _ _ over.map_id ≪≫ lift_id

@[simp] lemma map_obj_left (f : X ⟶ Y) [mono f] (g : mono_over X) :
(↑((map f).obj g) : over Y).left = g.val.left :=
rfl

@[simp]
lemma map_obj_arrow (f : X ⟶ Y) [mono f] (g : mono_over X) :
((map f).obj g).arrow = g.arrow ≫ f := rfl

instance full_map (f : X ⟶ Y) [mono f] : full (map f) :=
{ preimage := λ g h e,
  begin
    refine hom_mk e.left _,
    rw [← cancel_mono f, assoc],
    apply w e,
  end }

instance faithful_map (f : X ⟶ Y) [mono f] : faithful (map f) := {}.

/--
Isomorphic objects have equivalent `mono_over` categories.
-/
def map_iso {A B : C} (e : A ≅ B) : mono_over A ≌ mono_over B :=
{ functor := map e.hom,
  inverse := map e.inv,
  unit_iso := ((map_comp _ _).symm ≪≫ eq_to_iso (by simp) ≪≫ map_id).symm,
  counit_iso := ((map_comp _ _).symm ≪≫ eq_to_iso (by simp) ≪≫ map_id) }

section
variable [has_pullbacks C]

/-- `map f` is left adjoint to `pullback f` when `f` is a monomorphism -/
def map_pullback_adj (f : X ⟶ Y) [mono f] : map f ⊣ pullback f :=
adjunction.restrict_fully_faithful
  (forget X) (forget Y) (over.map_pullback_adj f) (iso.refl _) (iso.refl _)

/-- `mono_over.map f` followed by `mono_over.pullback f` is the identity. -/
def pullback_map_self (f : X ⟶ Y) [mono f] :
  map f ⋙ pullback f ≅ 𝟭 _ :=
(as_iso (mono_over.map_pullback_adj f).unit).symm

end

end map

section image

variables [has_images C]

/--
Taking the image of a morphism gives a functor `over X ⥤ mono_over X`.
-/
@[simps]
def image : over X ⥤ mono_over X :=
{ obj := λ f, mk' (image.ι f.hom),
  map := λ f g k,
  begin
    apply (forget X).preimage _,
    apply over.hom_mk _ _,
    refine image.lift {I := image _, m := image.ι g.hom, e := k.left ≫ factor_thru_image g.hom},
    apply image.lift_fac,
  end }

/--
`mono_over.image : over X ⥤ mono_over X` is left adjoint to
`mono_over.forget : mono_over X ⥤ over X`
-/
def image_forget_adj : image ⊣ forget X :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ f g,
  { to_fun := λ k,
    begin
      apply over.hom_mk (factor_thru_image f.hom ≫ k.left) _,
      change (factor_thru_image f.hom ≫ k.left) ≫ _ = f.hom,
      rw [assoc, over.w k],
      apply image.fac
    end,
    inv_fun := λ k,
    begin
      refine over.hom_mk _ _,
      refine image.lift {I := g.val.left, m := g.arrow, e := k.left, fac' := over.w k},
      apply image.lift_fac,
    end,
    left_inv := λ k, subsingleton.elim _ _,
    right_inv := λ k,
    begin
      ext1,
      change factor_thru_image _ ≫ image.lift _ = _,
      rw [← cancel_mono g.arrow, assoc, image.lift_fac, image.fac f.hom],
      exact (over.w k).symm,
    end } }

instance : is_right_adjoint (forget X) :=
{ left := image, adj := image_forget_adj }

instance reflective : reflective (forget X) := {}.

/--
Forgetting that a monomorphism over `X` is a monomorphism, then taking its image,
is the identity functor.
-/
def forget_image : forget X ⋙ image ≅ 𝟭 (mono_over X) :=
as_iso (adjunction.counit image_forget_adj)

end image

section «exists»
variables [has_images C]

/--
In the case where `f` is not a monomorphism but `C` has images,
we can still take the "forward map" under it, which agrees with `mono_over.map f`.
-/
def «exists» (f : X ⟶ Y) : mono_over X ⥤ mono_over Y :=
forget _ ⋙ over.map f ⋙ image

instance faithful_exists (f : X ⟶ Y) : faithful («exists» f) := {}.

/--
When `f : X ⟶ Y` is a monomorphism, `exists f` agrees with `map f`.
-/
def exists_iso_map (f : X ⟶ Y) [mono f] : «exists» f ≅ map f :=
nat_iso.of_components
begin
  intro Z,
  suffices : (forget _).obj ((«exists» f).obj Z) ≅ (forget _).obj ((map f).obj Z),
    apply preimage_iso this,
  apply over.iso_mk _ _,
  apply image_mono_iso_source (Z.arrow ≫ f),
  apply image_mono_iso_source_hom_self,
end
begin
  intros Z₁ Z₂ g,
  ext1,
  change image.lift ⟨_, _, _, _⟩ ≫ (image_mono_iso_source (Z₂.arrow ≫ f)).hom =
         (image_mono_iso_source (Z₁.arrow ≫ f)).hom ≫ g.left,
  rw [← cancel_mono (Z₂.arrow ≫ f), assoc, assoc, w_assoc g, image_mono_iso_source_hom_self,
      image_mono_iso_source_hom_self],
  apply image.lift_fac,
end

/-- `exists` is adjoint to `pullback` when images exist -/
def exists_pullback_adj (f : X ⟶ Y) [has_pullbacks C] : «exists» f ⊣ pullback f :=
adjunction.restrict_fully_faithful (forget X) (𝟭 _)
  ((over.map_pullback_adj f).comp _ _ image_forget_adj)
  (iso.refl _)
  (iso.refl _)

end «exists»

section has_top

instance {X : C} : has_top (mono_over X) :=
{ top := mk' (𝟙 _) }

instance {X : C} : inhabited (mono_over X) := ⟨⊤⟩

/-- The morphism to the top object in `mono_over X`. -/
def le_top (f : mono_over X) : f ⟶ ⊤ :=
hom_mk f.arrow (comp_id _)

@[simp] lemma top_left (X : C) : ((⊤ : mono_over X) : over X).left = X := rfl
@[simp] lemma top_arrow (X : C) : (⊤ : mono_over X).arrow = 𝟙 X := rfl

/-- `map f` sends `⊤ : mono_over X` to `⟨X, f⟩ : mono_over Y`. -/
def map_top (f : X ⟶ Y) [mono f] : (map f).obj ⊤ ≅ mk' f :=
iso_of_both_ways (hom_mk (𝟙 _) rfl) (hom_mk (𝟙 _) (by simp [id_comp f]))

section
variable [has_pullbacks C]

/-- The pullback of the top object in `mono_over Y`
is (isomorphic to) the top object in `mono_over X`. -/
def pullback_top (f : X ⟶ Y) : (pullback f).obj ⊤ ≅ ⊤ :=
iso_of_both_ways (le_top _) (hom_mk (pullback.lift f (𝟙 _) (by tidy)) (pullback.lift_snd _ _ _))

/-- There is a morphism from `⊤ : mono_over A` to the pullback of a monomorphism along itself;
as the category is thin this is an isomorphism. -/
def top_le_pullback_self {A B : C} (f : A ⟶ B) [mono f] :
  (⊤ : mono_over A) ⟶ (pullback f).obj (mk' f) :=
hom_mk _ (pullback.lift_snd _ _ rfl)

/-- The pullback of a monomorphism along itself is isomorphic to the top object. -/
def pullback_self {A B : C} (f : A ⟶ B) [mono f] :
  (pullback f).obj (mk' f) ≅ ⊤ :=
iso_of_both_ways (le_top _) (top_le_pullback_self _)

end

end has_top

section has_bot
variables [has_zero_morphisms C] [has_zero_object C]
local attribute [instance] has_zero_object.has_zero

instance {X : C} : has_bot (mono_over X) :=
{ bot := mk' (0 : 0 ⟶ X) }

@[simp] lemma bot_left (X : C) : ((⊥ : mono_over X) : over X).left = 0 := rfl
@[simp] lemma bot_arrow {X : C} : (⊥ : mono_over X).arrow = 0 :=
by ext

/-- The (unique) morphism from `⊥ : mono_over X` to any other `f : mono_over X`. -/
def bot_le {X : C} (f : mono_over X) : ⊥ ⟶ f :=
hom_mk 0 (by simp)

/-- `map f` sends `⊥ : mono_over X` to `⊥ : mono_over Y`. -/
def map_bot (f : X ⟶ Y) [mono f] : (map f).obj ⊥ ≅ ⊥ :=
iso_of_both_ways (hom_mk 0 (by simp)) (hom_mk (𝟙 _) (by simp [id_comp f]))

end has_bot

section inf
variables [has_pullbacks C]

/--
When `[has_pullbacks C]`, `mono_over A` has "intersections", functorial in both arguments.

As `mono_over A` is only a preorder, this doesn't satisfy the axioms of `semilattice_inf`,
but we reuse all the names from `semilattice_inf` because they will be used to construct
`semilattice_inf (subobject A)` shortly.
-/
@[simps]
def inf {A : C} : mono_over A ⥤ mono_over A ⥤ mono_over A :=
{ obj := λ f, pullback f.arrow ⋙ map f.arrow,
  map := λ f₁ f₂ k,
  { app := λ g,
    begin
      apply hom_mk _ _,
      apply pullback.lift pullback.fst (pullback.snd ≫ k.left) _,
      rw [pullback.condition, assoc, w k],
      dsimp,
      rw [pullback.lift_snd_assoc, assoc, w k],
    end } }.

/-- A morphism from the "infimum" of two objects in `mono_over A` to the first object. -/
def inf_le_left {A : C} (f g : mono_over A) :
  (inf.obj f).obj g ⟶ f :=
hom_mk _ rfl

/-- A morphism from the "infimum" of two objects in `mono_over A` to the second object. -/
def inf_le_right {A : C} (f g : mono_over A) :
  (inf.obj f).obj g ⟶ g :=
hom_mk _ pullback.condition

/-- A morphism version of the `le_inf` axiom. -/
def le_inf {A : C} (f g h : mono_over A) :
  (h ⟶ f) → (h ⟶ g) → (h ⟶ (inf.obj f).obj g) :=
begin
  intros k₁ k₂,
  refine hom_mk (pullback.lift k₂.left k₁.left _) _,
  rw [w k₁, w k₂],
  erw [pullback.lift_snd_assoc, w k₁],
end

end inf

section sup
variables [has_images C] [has_binary_coproducts C]

/-- When `[has_images C] [has_binary_coproducts C]`, `mono_over A` has a `sup` construction,
which is functorial in both arguments,
and which on `subobject A` will induce a `semilattice_sup`. -/
def sup  {A : C} : mono_over A ⥤ mono_over A ⥤ mono_over A :=
curry_obj ((forget A).prod (forget A) ⋙ uncurry.obj over.coprod ⋙ image)

/-- A morphism version of `le_sup_left`. -/
def le_sup_left {A : C} (f g : mono_over A) :
  f ⟶ (sup.obj f).obj g :=
begin
  refine hom_mk (coprod.inl ≫ factor_thru_image _) _,
  erw [category.assoc, image.fac, coprod.inl_desc],
  refl,
end

/-- A morphism version of `le_sup_right`. -/
def le_sup_right {A : C} (f g : mono_over A) :
  g ⟶ (sup.obj f).obj g :=
begin
  refine hom_mk (coprod.inr ≫ factor_thru_image _) _,
  erw [category.assoc, image.fac, coprod.inr_desc],
  refl,
end

/-- A morphism version of `sup_le`. -/
def sup_le {A : C} (f g h : mono_over A) :
  (f ⟶ h) → (g ⟶ h) → ((sup.obj f).obj g ⟶ h) :=
begin
  intros k₁ k₂,
  refine hom_mk _ _,
  apply image.lift ⟨_, h.arrow, coprod.desc k₁.left k₂.left, _⟩,
  { dsimp,
    ext1,
    { simp [w k₁] },
    { simp [w k₂] } },
  { apply image.lift_fac }
end

end sup

end mono_over

/-!
We now construct the subobject lattice for `X : C`,
as the quotient by isomorphisms of `mono_over X`.

Since `mono_over X` is a thin category, we use `thin_skeleton` to take the quotient.

Essentially all the structure defined above on `mono_over X` descends to `subobject X`,
with morphisms becoming inequalities, and isomorphisms becoming equations.
-/

/--
The category of subobjects of `X : C`, defined as isomorphism classes of monomorphisms into `X`.
-/
@[derive [partial_order, category]]
def subobject (X : C) := thin_skeleton (mono_over X)

namespace subobject

/-- Convenience constructor for a subobject. -/
abbreviation mk {X A : C} (f : A ⟶ X) [mono f] : subobject X :=
(to_thin_skeleton _).obj (mono_over.mk' f)

/--
Use choice to pick a representative `mono_over X` for each `subobject X`.
-/
noncomputable
def representative {X : C} : subobject X ⥤ mono_over X :=
thin_skeleton.from_thin_skeleton _


/--
Starting with `A : mono_over X`, we can take its equivalence class in `subobject X`
then pick an arbitrary representative using `representative.obj`.
This is isomorphic (in `mono_over X`) to the original `A`.
-/
noncomputable
def representative_iso {X : C} (A : mono_over X) :
  representative.obj ((to_thin_skeleton _).obj A) ≅ A :=
(thin_skeleton.from_thin_skeleton _).as_equivalence.counit_iso.app A

/--
Use choice to pick a representative underlying object in `C` for any `subobject X`.

Prefer to use the coercion `P : C` rather than explicitly writing `underlying.obj P`.
-/
noncomputable
def underlying {X : C} : subobject X ⥤ C :=
representative ⋙ mono_over.forget _ ⋙ over.forget _

instance : has_coe (subobject X) C :=
{ coe := λ Y, underlying.obj Y, }

@[simp] lemma underlying_as_coe {X : C} (P : subobject X) : underlying.obj P = P := rfl

/--
If we construct a `subobject Y` from an explicit `f : X ⟶ Y` with `[mono f]`,
then pick an arbitrary choice of underlying object `(subobject.mk f : C)` back in `C`,
it is isomorphic (in `C`) to the original `X`.
-/
noncomputable
def underlying_iso {X Y : C} (f : X ⟶ Y) [mono f] : (subobject.mk f : C) ≅ X :=
(mono_over.forget _ ⋙ over.forget _).map_iso (representative_iso (mono_over.mk' f))

/--
The morphism in `C` from the arbitrarily chosen underlying object to the ambient object.
-/
noncomputable
def arrow {X : C} (Y : subobject X) : (Y : C) ⟶ X :=
(representative.obj Y).val.hom

instance arrow_mono {X : C} (Y : subobject X) : mono (Y.arrow) :=
(representative.obj Y).property

@[simp]
lemma representative_val_left (Y : subobject X) :
  (representative.obj Y).val.left = Y :=
rfl

@[simp]
lemma representative_arrow (Y : subobject X) :
  (representative.obj Y).arrow = Y.arrow :=
rfl

@[simp]
lemma underlying_arrow {X : C} {Y Z : subobject X} (f : Y ⟶ Z) :
  underlying.map f ≫ arrow Z = arrow Y :=
over.w (representative.map f)

@[simp]
lemma underlying_iso_arrow {X Y : C} (f : X ⟶ Y) [mono f] :
  (underlying_iso f).inv ≫ (subobject.mk f).arrow = f :=
over.w _

/-- Two morphisms into a subobject are equal exactly if
the morphisms into the ambient object are equal -/
@[ext]
lemma eq_of_comp_arrow_eq {X Y : C} {P : subobject Y}
  {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g :=
(cancel_mono P.arrow).mp h

-- TODO surely there is a cleaner proof here
lemma le_of_comm {B : C} {X Y : subobject B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) :
  X ≤ Y :=
begin
  revert f w,
  refine quotient.induction_on₂' X Y _,
  intros P Q f w,
  fsplit,
  refine over.hom_mk ((representative_iso P).inv.left ≫ f ≫ (representative_iso Q).hom.left) _,
  dsimp,
  simp only [over.w, category.assoc],
  erw [w, (representative_iso P).inv.w],
  dsimp,
  simp only [category.comp_id],
end

/-- When `f : X ⟶ Y` and `P : subobject Y`,
`P.factors f` expresses that there exists a factorisation of `f` through `P`.
Given `h : P.factors f`, you can recover the morphism as `P.factor_thru f h`.
-/
def factors {X Y : C} (P : subobject Y) (f : X ⟶ Y) : Prop :=
quotient.lift_on' P (λ P, P.factors f)
begin
  rintros P Q ⟨h⟩,
  apply propext,
  split,
  { rintro ⟨i, w⟩,
    exact ⟨i ≫ h.hom.left, by erw [category.assoc, over.w h.hom, w]⟩, },
  { rintro ⟨i, w⟩,
    exact ⟨i ≫ h.inv.left, by erw [category.assoc, over.w h.inv, w]⟩, },
end

lemma factors_iff {X Y : C} (P : subobject Y) (f : X ⟶ Y) :
  P.factors f ↔ (representative.obj P).factors f :=
begin
  induction P,
  { rcases P with ⟨⟨P, ⟨⟩, g⟩, hg⟩,
    resetI,
    fsplit,
    { rintro ⟨i, w⟩,
      refine ⟨i ≫ (underlying_iso g).inv, _⟩,
      simp only [category_theory.category.assoc],
      convert w,
      convert underlying_iso_arrow _, },
    { rintro ⟨i, w⟩,
      refine ⟨i ≫ (underlying_iso g).hom, _⟩,
      simp only [category_theory.category.assoc],
      convert w,
      rw ←iso.eq_inv_comp,
      symmetry,
      convert underlying_iso_arrow _, }, },
  { refl, },
end

/-- `P.factor_thru f h` provides a factorisation of `f : X ⟶ Y` through some `P : subobject Y`,
given the evidence `h : P.factors f` that such a factorisation exists. -/
def factor_thru {X Y : C} (P : subobject Y) (f : X ⟶ Y) (h : factors P f) : X ⟶ P :=
classical.some ((factors_iff _ _).mp h)

@[simp, reassoc] lemma factor_thru_arrow {X Y : C} (P : subobject Y) (f : X ⟶ Y) (h : factors P f) :
  P.factor_thru f h ≫ P.arrow = f :=
classical.some_spec ((factors_iff _ _).mp h)

@[simp] lemma factor_thru_eq_zero [has_zero_morphisms C]
  {X Y : C} {P : subobject Y} {f : X ⟶ Y} {h : factors P f} :
  P.factor_thru f h = 0 ↔ f = 0 :=
begin
  fsplit,
  { intro w,
    replace w := w =≫ P.arrow,
    simpa using w, },
  { rintro rfl,
    apply (cancel_mono P.arrow).mp,
    simp, },
end

lemma factors_comp_arrow {X Y : C} {P : subobject Y} (f : X ⟶ P) : P.factors (f ≫ P.arrow) :=
(factors_iff _ _).mpr ⟨f, rfl⟩

lemma factors_of_factors_right {X Y Z : C} {P : subobject Z} (f : X ⟶ Y) {g : Y ⟶ Z}
  (h : P.factors g) : P.factors (f ≫ g) :=
begin
  revert P,
  refine quotient.ind' _,
  intro P,
  rintro ⟨g, rfl⟩,
  exact ⟨f ≫ g, by simp⟩,
end

lemma factors_of_le {Y Z : C} {P Q : subobject Y} (f : Z ⟶ Y) (h : P ≤ Q) :
  P.factors f → Q.factors f :=
begin
  revert P Q,
  refine quotient.ind₂' _,
  rintro P Q ⟨h⟩ ⟨g, rfl⟩,
  refine ⟨g ≫ h.left, _⟩,
  rw assoc,
  congr' 1,
  apply over.w h,
end

@[simp]
lemma factor_thru_right {X Y Z : C} {P : subobject Z} (f : X ⟶ Y) (g : Y ⟶ Z) (h : P.factors g) :
  f ≫ P.factor_thru g h = P.factor_thru (f ≫ g) (factors_of_factors_right f h) :=
begin
  apply (cancel_mono P.arrow).mp,
  simp,
end

end subobject

namespace limits

section equalizer
variables (f g : X ⟶ Y) [has_equalizer f g]

/-- The equalizer of morphisms `f g : X ⟶ Y` as a `subobject X`. -/
def equalizer_subobject : subobject X :=
subobject.mk (equalizer.ι f g)

/-- The underlying object of `equalizer_subobject f g` is (up to isomorphism!)
the same as the chosen object `equalizer f g`. -/
def equalizer_subobject_iso : (equalizer_subobject f g : C) ≅ equalizer f g :=
subobject.underlying_iso (equalizer.ι f g)

lemma equalizer_subobject_arrow :
  (equalizer_subobject f g).arrow = (equalizer_subobject_iso f g).hom ≫ equalizer.ι f g :=
(over.w (subobject.representative_iso (mono_over.mk' (equalizer.ι f g))).hom).symm

@[simp] lemma equalizer_subobject_arrow' :
  (equalizer_subobject_iso f g).inv ≫ (equalizer_subobject f g).arrow = equalizer.ι f g :=
over.w (subobject.representative_iso (mono_over.mk' (equalizer.ι f g))).inv

@[reassoc]
lemma equalizer_subobject_arrow_comp :
  (equalizer_subobject f g).arrow ≫ f = (equalizer_subobject f g).arrow ≫ g :=
by simp [equalizer_subobject_arrow, equalizer.condition]

lemma equalizer_subobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = h ≫ g) :
  (equalizer_subobject f g).factors h :=
⟨equalizer.lift h w, by simp⟩

lemma equalizer_subobject_factors_iff {W : C} (h : W ⟶ X) :
  (equalizer_subobject f g).factors h ↔ h ≫ f = h ≫ g :=
⟨λ w, by rw [←subobject.factor_thru_arrow _ _ w, category.assoc,
  equalizer_subobject_arrow_comp, category.assoc],
equalizer_subobject_factors f g h⟩

end equalizer

section kernel
variables [has_zero_morphisms C] (f : X ⟶ Y) [has_kernel f]

/-- The kernel of a morphism `f : X ⟶ Y` as a `subobject X`. -/
def kernel_subobject : subobject X :=
subobject.mk (kernel.ι f)

/-- The underlying object of `kernel_subobject f` is (up to isomorphism!)
the same as the chosen object `kernel f`. -/
def kernel_subobject_iso :
  (kernel_subobject f : C) ≅ kernel f :=
subobject.underlying_iso (kernel.ι f)

lemma kernel_subobject_arrow :
  (kernel_subobject f).arrow = (kernel_subobject_iso f).hom ≫ kernel.ι f :=
(over.w (subobject.representative_iso (mono_over.mk' (kernel.ι f))).hom).symm

@[simp] lemma kernel_subobject_arrow' :
  (kernel_subobject_iso f).inv ≫ (kernel_subobject f).arrow = kernel.ι f :=
over.w (subobject.representative_iso (mono_over.mk' (kernel.ι f))).inv

@[simp]
lemma kernel_subobject_arrow_comp :
  (kernel_subobject f).arrow ≫ f = 0 :=
by simp [kernel_subobject_arrow, kernel.condition]

lemma kernel_subobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
  (kernel_subobject f).factors h :=
⟨kernel.lift _ h w, by simp⟩

lemma kernel_subobject_factors_iff {W : C} (h : W ⟶ X) :
  (kernel_subobject f).factors h ↔ h ≫ f = 0 :=
⟨λ w, by rw [←subobject.factor_thru_arrow _ _ w, category.assoc,
  kernel_subobject_arrow_comp, comp_zero],
kernel_subobject_factors f h⟩

end kernel

section image
variables (f : X ⟶ Y) [has_image f]

/-- The image of a morphism `f g : X ⟶ Y` as a `subobject Y`. -/
def image_subobject : subobject Y :=
subobject.mk (image.ι f)

/-- The underlying object of `image_subobject f` is (up to isomorphism!)
the same as the chosen object `image f`. -/
def image_subobject_iso :
  (image_subobject f : C) ≅ image f :=
subobject.underlying_iso (image.ι f)

lemma image_subobject_arrow :
  (image_subobject f).arrow = (image_subobject_iso f).hom ≫ image.ι f :=
(over.w (subobject.representative_iso (mono_over.mk' (image.ι f))).hom).symm

@[simp] lemma image_subobject_arrow' :
  (image_subobject_iso f).inv ≫ (image_subobject f).arrow = image.ι f :=
over.w (subobject.representative_iso (mono_over.mk' (image.ι f))).inv

/-- A factorisation of `f : X ⟶ Y` through `image_subobject f`. -/
def factor_thru_image_subobject : X ⟶ image_subobject f :=
factor_thru_image f ≫ (image_subobject_iso f).inv

lemma image_subobject_arrow_comp :
  factor_thru_image_subobject f ≫ (image_subobject f).arrow = f :=
by simp [factor_thru_image_subobject, image_subobject_arrow]

-- TODO an iff characterisation of `(image_subobject f).factors h`
lemma image_subobject_factors {W : C} (h : W ⟶ Y) (k : W ⟶ X) (w : k ≫ f = h) :
  (image_subobject f).factors h :=
⟨k ≫ factor_thru_image f, by simp [w]⟩

lemma image_subobject_le {A B : C} {X : subobject B} (f : A ⟶ B) [has_image f]
  (h : A ⟶ X) (w : h ≫ X.arrow = f) :
  image_subobject f ≤ X :=
subobject.le_of_comm
  ((image_subobject_iso f).hom ≫ image.lift { I := (X : C), e := h, m := X.arrow, })
  (by simp [←image_subobject_arrow f])

end image

end limits

open category_theory.limits

namespace subobject

/-- Any functor `mono_over X ⥤ mono_over Y` descends to a functor
`subobject X ⥤ subobject Y`, because `mono_over Y` is thin. -/
def lower {Y : D} (F : mono_over X ⥤ mono_over Y) : subobject X ⥤ subobject Y :=
thin_skeleton.map F

/-- Isomorphic functors become equal when lowered to `subobject`.
(It's not as evil as usual to talk about equality between functors
because the categories are thin and skeletal.) -/
lemma lower_iso (F₁ F₂ : mono_over X ⥤ mono_over Y) (h : F₁ ≅ F₂) :
  lower F₁ = lower F₂ :=
thin_skeleton.map_iso_eq h

/-- A ternary version of `subobject.lower`. -/
def lower₂ (F : mono_over X ⥤ mono_over Y ⥤ mono_over Z) :
  subobject X ⥤ subobject Y ⥤ subobject Z :=
thin_skeleton.map₂ F

@[simp]
lemma lower_comm (F : mono_over Y ⥤ mono_over X) :
  to_thin_skeleton _ ⋙ lower F = F ⋙ to_thin_skeleton _ :=
rfl

/-- An adjunction between `mono_over A` and `mono_over B` gives an adjunction
between `subobject A` and `subobject B`. -/
def lower_adjunction {A : C} {B : D}
  {L : mono_over A ⥤ mono_over B} {R : mono_over B ⥤ mono_over A} (h : L ⊣ R) :
  lower L ⊣ lower R :=
thin_skeleton.lower_adjunction _ _ h

/-- An equivalence between `mono_over A` and `mono_over B` gives an equivalence
between `subobject A` and `subobject B`. -/
@[simps]
def lower_equivalence {A : C} {B : D} (e : mono_over A ≌ mono_over B) : subobject A ≌ subobject B :=
{ functor := lower e.functor,
  inverse := lower e.inverse,
  unit_iso :=
  begin
    apply eq_to_iso,
    convert thin_skeleton.map_iso_eq e.unit_iso,
    { exact thin_skeleton.map_id_eq.symm },
    { exact (thin_skeleton.map_comp_eq _ _).symm },
  end,
  counit_iso :=
  begin
    apply eq_to_iso,
    convert thin_skeleton.map_iso_eq e.counit_iso,
    { exact (thin_skeleton.map_comp_eq _ _).symm },
    { exact thin_skeleton.map_id_eq.symm },
  end }

section pullback
variables [has_pullbacks C]

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `subobject Y ⥤ subobject X`,
by pulling back a monomorphism along `f`. -/
def pullback (f : X ⟶ Y) : subobject Y ⥤ subobject X :=
lower (mono_over.pullback f)

lemma pullback_id (x : subobject X) : (pullback (𝟙 X)).obj x = x :=
begin
  apply quotient.induction_on' x,
  intro f,
  apply quotient.sound,
  exact ⟨mono_over.pullback_id.app f⟩,
end

lemma pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : subobject Z) :
  (pullback (f ≫ g)).obj x = (pullback f).obj ((pullback g).obj x) :=
begin
  apply quotient.induction_on' x,
  intro t,
  apply quotient.sound,
  refine ⟨(mono_over.pullback_comp _ _).app t⟩,
end

instance (f : X ⟶ Y) : faithful (pullback f) := {}

end pullback

section map

/--
We can map subobjects of `X` to subobjects of `Y`
by post-composition with a monomorphism `f : X ⟶ Y`.
-/
def map (f : X ⟶ Y) [mono f] : subobject X ⥤ subobject Y :=
lower (mono_over.map f)

lemma map_id (x : subobject X) : (map (𝟙 X)).obj x = x :=
begin
  apply quotient.induction_on' x,
  intro f,
  apply quotient.sound,
  exact ⟨mono_over.map_id.app f⟩,
end

lemma map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] (x : subobject X) :
  (map (f ≫ g)).obj x = (map g).obj ((map f).obj x) :=
begin
  apply quotient.induction_on' x,
  intro t,
  apply quotient.sound,
  refine ⟨(mono_over.map_comp _ _).app t⟩,
end

/-- Isomorphic objects have equivalent subobject lattices. -/
def map_iso {A B : C} (e : A ≅ B) : subobject A ≌ subobject B :=
lower_equivalence (mono_over.map_iso e)

/-- In fact, there's a type level bijection between the subobjects of isomorphic objects,
which preserves the order. -/
-- @[simps] here generates a lemma `map_iso_to_order_iso_to_equiv_symm_apply`
-- whose left hand side is not in simp normal form.
def map_iso_to_order_iso (e : X ≅ Y) : subobject X ≃o subobject Y :=
{ to_fun := (map e.hom).obj,
  inv_fun := (map e.inv).obj,
  left_inv := λ g, by simp_rw [← map_comp, e.hom_inv_id, map_id],
  right_inv := λ g, by simp_rw [← map_comp, e.inv_hom_id, map_id],
  map_rel_iff' := λ A B, begin
    dsimp, fsplit,
    { intro h,
      apply_fun (map e.inv).obj at h,
      simp_rw [← map_comp, e.hom_inv_id, map_id] at h,
      exact h, },
    { intro h,
      apply_fun (map e.hom).obj at h,
      exact h, },
  end }

@[simp] lemma map_iso_to_order_iso_apply (e : X ≅ Y) (P : subobject X) :
  map_iso_to_order_iso e P = (map e.hom).obj P :=
rfl

@[simp] lemma map_iso_to_order_iso_symm_apply (e : X ≅ Y) (Q : subobject Y) :
  (map_iso_to_order_iso e).symm Q = (map e.inv).obj Q :=
rfl

/-- `map f : subobject X ⥤ subobject Y` is
the left adjoint of `pullback f : subobject Y ⥤ subobject X`. -/
def map_pullback_adj [has_pullbacks C] (f : X ⟶ Y) [mono f] : map f ⊣ pullback f :=
lower_adjunction (mono_over.map_pullback_adj f)

@[simp]
lemma pullback_map_self [has_pullbacks C] (f : X ⟶ Y) [mono f] (g : subobject X) :
  (pullback f).obj ((map f).obj g) = g :=
begin
  revert g,
  apply quotient.ind,
  intro g',
  apply quotient.sound,
  exact ⟨(mono_over.pullback_map_self f).app _⟩,
end

lemma map_pullback [has_pullbacks C]
  {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} [mono h] [mono g]
  (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk f g comm)) (p : subobject Y) :
  (map g).obj ((pullback f).obj p) = (pullback k).obj ((map h).obj p) :=
begin
  revert p,
  apply quotient.ind',
  intro a,
  apply quotient.sound,
  apply thin_skeleton.equiv_of_both_ways,
  { refine mono_over.hom_mk (pullback.lift pullback.fst _ _) (pullback.lift_snd _ _ _),
    change _ ≫ a.arrow ≫ h = (pullback.snd ≫ g) ≫ _,
    rw [assoc, ← comm, pullback.condition_assoc] },
  { refine mono_over.hom_mk (pullback.lift pullback.fst
                        (pullback_cone.is_limit.lift' t (pullback.fst ≫ a.arrow) pullback.snd _).1
                        (pullback_cone.is_limit.lift' _ _ _ _).2.1.symm) _,
    { rw [← pullback.condition, assoc], refl },
    { dsimp, rw [pullback.lift_snd_assoc],
      apply (pullback_cone.is_limit.lift' _ _ _ _).2.2 } }
end

end map

section «exists»
variables [has_images C]

/--
The functor from subobjects of `X` to subobjects of `Y` given by
sending the subobject `S` to its "image" under `f`, usually denoted $\exists_f$.
For instance, when `C` is the category of types,
viewing `subobject X` as `set X` this is just `set.image f`.

This functor is left adjoint to the `pullback f` functor (shown in `exists_pullback_adj`)
provided both are defined, and generalises the `map f` functor, again provided it is defined.
-/
def «exists» (f : X ⟶ Y) : subobject X ⥤ subobject Y :=
lower (mono_over.exists f)

/--
When `f : X ⟶ Y` is a monomorphism, `exists f` agrees with `map f`.
-/
lemma exists_iso_map (f : X ⟶ Y) [mono f] : «exists» f = map f :=
lower_iso _ _ (mono_over.exists_iso_map f)

/--
`exists f : subobject X ⥤ subobject Y` is
left adjoint to `pullback f : subobject Y ⥤ subobject X`.
-/
def exists_pullback_adj (f : X ⟶ Y) [has_pullbacks C] : «exists» f ⊣ pullback f :=
lower_adjunction (mono_over.exists_pullback_adj f)

end  «exists»

section order_top

instance order_top {X : C} : order_top (subobject X) :=
{ top := quotient.mk' ⊤,
  le_top :=
  begin
    refine quotient.ind' (λ f, _),
    exact ⟨mono_over.le_top f⟩,
  end,
  ..subobject.partial_order X}

instance {X : C} : inhabited (subobject X) := ⟨⊤⟩

lemma top_eq_id {B : C} : (⊤ : subobject B) = subobject.mk (𝟙 B) := rfl

/-- The object underlying `⊤ : subobject B` is (up to isomorphism) `B`. -/
def top_coe_iso_self {B : C} : ((⊤ : subobject B) : C) ≅ B := underlying_iso _

@[simp]
lemma underlying_iso_id_eq_top_coe_iso_self {B : C} : underlying_iso (𝟙 B) = top_coe_iso_self :=
rfl

@[simp, reassoc]
lemma underlying_iso_inv_top_arrow {B : C} :
  top_coe_iso_self.inv ≫ (⊤ : subobject B).arrow = 𝟙 B :=
underlying_iso_arrow _

lemma map_top (f : X ⟶ Y) [mono f] : (map f).obj ⊤ = quotient.mk' (mono_over.mk' f) :=
quotient.sound' ⟨mono_over.map_top f⟩

lemma top_factors {A B : C} (f : A ⟶ B) : (⊤ : subobject B).factors f :=
⟨f, comp_id _⟩

section
variables [has_pullbacks C]

lemma pullback_top (f : X ⟶ Y) : (pullback f).obj ⊤ = ⊤ :=
quotient.sound' ⟨mono_over.pullback_top f⟩

lemma pullback_self {A B : C} (f : A ⟶ B) [mono f] :
  (pullback f).obj (mk f) = ⊤ :=
quotient.sound' ⟨mono_over.pullback_self f⟩

end

end order_top

section order_bot
variables [has_zero_morphisms C] [has_zero_object C]
local attribute [instance] has_zero_object.has_zero

instance order_bot {X : C} : order_bot (subobject X) :=
{ bot := quotient.mk' ⊥,
  bot_le :=
  begin
    refine quotient.ind' (λ f, _),
    exact ⟨mono_over.bot_le f⟩,
  end,
  ..subobject.partial_order X}

lemma bot_eq_zero {B : C} : (⊥ : subobject B) = subobject.mk (0 : 0 ⟶ B) := rfl

/-- The object underlying `⊥ : subobject B` is (up to isomorphism) the zero object. -/
def bot_coe_iso_zero {B : C} : ((⊥ : subobject B) : C) ≅ 0 := underlying_iso _

@[simp] lemma bot_arrow {B : C} : (⊥ : subobject B).arrow = 0 :=
zero_of_source_iso_zero _ bot_coe_iso_zero

lemma map_bot (f : X ⟶ Y) [mono f] : (map f).obj ⊥ = ⊥ :=
quotient.sound' ⟨mono_over.map_bot f⟩

lemma bot_factors_iff_zero {A B : C} (f : A ⟶ B) : (⊥ : subobject B).factors f ↔ f = 0 :=
⟨by { rintro ⟨h, w⟩, simp at w, exact w.symm, }, by { rintro rfl, exact ⟨0, by simp⟩, }⟩

end order_bot

section functor
variable (C)

/-- Sending `X : C` to `subobject X` is a contravariant functor `Cᵒᵖ ⥤ Type`. -/
@[simps]
def functor [has_pullbacks C] : Cᵒᵖ ⥤ Type (max u₁ v₁) :=
{ obj := λ X, subobject X.unop,
  map := λ X Y f, (pullback f.unop).obj,
  map_id' := λ X, funext pullback_id,
  map_comp' := λ X Y Z f g, funext (pullback_comp _ _) }

end functor

section semilattice_inf_top
variables [has_pullbacks C]

/-- The functorial infimum on `mono_over A` descends to an infimum on `subobject A`. -/
def inf {A : C} : subobject A ⥤ subobject A ⥤ subobject A :=
thin_skeleton.map₂ mono_over.inf

lemma inf_le_left  {A : C} (f g : subobject A) :
  (inf.obj f).obj g ≤ f :=
quotient.induction_on₂' f g (λ a b, ⟨mono_over.inf_le_left _ _⟩)

lemma inf_le_right {A : C} (f g : subobject A) :
  (inf.obj f).obj g ≤ g :=
quotient.induction_on₂' f g (λ a b, ⟨mono_over.inf_le_right _ _⟩)

lemma le_inf {A : C} (h f g : subobject A) :
  h ≤ f → h ≤ g → h ≤ (inf.obj f).obj g :=
quotient.induction_on₃' h f g
begin
  rintros f g h ⟨k⟩ ⟨l⟩,
  exact ⟨mono_over.le_inf _ _ _ k l⟩,
end

instance {B : C} : semilattice_inf_top (subobject B) :=
{ inf := λ m n, (inf.obj m).obj n,
  inf_le_left := inf_le_left,
  inf_le_right := inf_le_right,
  le_inf := le_inf,
  ..subobject.order_top }

lemma factors_left_of_inf_factors {A B : C} {X Y : subobject B} {f : A ⟶ B}
  (h : (X ⊓ Y).factors f) : X.factors f :=
factors_of_le _ (inf_le_left _ _) h

lemma factors_right_of_inf_factors {A B : C} {X Y : subobject B} {f : A ⟶ B}
  (h : (X ⊓ Y).factors f) : Y.factors f :=
factors_of_le _ (inf_le_right _ _) h

@[simp]
lemma inf_factors {A B : C} {X Y : subobject B} (f : A ⟶ B) :
  (X ⊓ Y).factors f ↔ X.factors f ∧ Y.factors f :=
⟨λ h, ⟨factors_left_of_inf_factors h, factors_right_of_inf_factors h⟩,
  begin
    revert X Y,
    refine quotient.ind₂' _,
    rintro X Y ⟨⟨g₁, rfl⟩, ⟨g₂, hg₂⟩⟩,
    exact ⟨_, pullback.lift_snd_assoc _ _ hg₂ _⟩,
  end⟩

lemma inf_arrow_factors_left {B : C} (X Y : subobject B) : X.factors (X ⊓ Y).arrow :=
(factors_iff _ _).mpr ⟨underlying.map (hom_of_le (inf_le_left X Y)), by simp⟩

lemma inf_arrow_factors_right {B : C} (X Y : subobject B) : Y.factors (X ⊓ Y).arrow :=
(factors_iff _ _).mpr ⟨underlying.map (hom_of_le (inf_le_right X Y)), by simp⟩

@[simp]
lemma finset_inf_factors {I : Type*} {A B : C} {s : finset I} {P : I → subobject B}
  (f : A ⟶ B) :
  (s.inf P).factors f ↔ ∀ i ∈ s, (P i).factors f :=
begin
  classical,
  apply finset.induction_on s,
  { simp [top_factors] },
  { intros i s nm ih, simp [ih] },
end

-- `i` is explicit here because often we'd like to defer a proof of `m`
lemma finset_inf_arrow_factors {I : Type*} {B : C} (s : finset I) (P : I → subobject B)
  (i : I) (m : i ∈ s) : (P i).factors (s.inf P).arrow :=
begin
  revert i m,
  classical,
  apply finset.induction_on s,
  { rintro _ ⟨⟩, },
  { intros i s nm ih j m,
    rw [finset.inf_insert],
    simp only [finset.mem_insert] at m, rcases m with (rfl|m),
    { rw ←factor_thru_arrow _ _ (inf_arrow_factors_left _ _),
      exact factors_comp_arrow _, },
    { rw ←factor_thru_arrow _ _ (inf_arrow_factors_right _ _),
      apply factors_of_factors_right,
      exact ih _ m, } },
end

lemma inf_eq_map_pullback' {A : C} (f₁ : mono_over A) (f₂ : subobject A) :
  (subobject.inf.obj (quotient.mk' f₁)).obj f₂ =
    (subobject.map f₁.arrow).obj ((subobject.pullback f₁.arrow).obj f₂) :=
begin
  apply quotient.induction_on' f₂,
  intro f₂,
  refl,
end

lemma inf_eq_map_pullback {A : C} (f₁ : mono_over A) (f₂ : subobject A) :
  (quotient.mk' f₁ ⊓ f₂ : subobject A) = (map f₁.arrow).obj ((pullback f₁.arrow).obj f₂) :=
inf_eq_map_pullback' f₁ f₂

lemma prod_eq_inf {A : C} {f₁ f₂ : subobject A} [has_binary_product f₁ f₂] :
  (f₁ ⨯ f₂) = f₁ ⊓ f₂ :=
le_antisymm
  (_root_.le_inf
    (le_of_hom limits.prod.fst)
    (le_of_hom limits.prod.snd))
  (le_of_hom
    (prod.lift
      (hom_of_le _root_.inf_le_left)
      (hom_of_le _root_.inf_le_right)))

lemma inf_def {B : C} (m m' : subobject B) :
  m ⊓ m' = (inf.obj m).obj m' := rfl

/-- `⊓` commutes with pullback. -/
lemma inf_pullback {X Y : C} (g : X ⟶ Y) (f₁ f₂) :
  (pullback g).obj (f₁ ⊓ f₂) = (pullback g).obj f₁ ⊓ (pullback g).obj f₂ :=
begin
  revert f₁,
  apply quotient.ind',
  intro f₁,
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← pullback_comp,
       ← map_pullback pullback.condition (pullback_is_pullback f₁.arrow g),
       ← pullback_comp, pullback.condition],
  refl,
end

/-- `⊓` commutes with map. -/
lemma inf_map {X Y : C} (g : Y ⟶ X) [mono g] (f₁ f₂) :
  (map g).obj (f₁ ⊓ f₂) = (map g).obj f₁ ⊓ (map g).obj f₂ :=
begin
  revert f₁,
  apply quotient.ind',
  intro f₁,
  erw [inf_def, inf_def, inf_eq_map_pullback',
       inf_eq_map_pullback', ← map_comp],
  dsimp,
  rw [pullback_comp, pullback_map_self],
end

end semilattice_inf_top

section semilattice_sup
variables [has_images C] [has_binary_coproducts C]

/-- The functorial supremum on `mono_over A` descends to an supremum on `subobject A`. -/
def sup {A : C} : subobject A ⥤ subobject A ⥤ subobject A :=
thin_skeleton.map₂ mono_over.sup

instance {B : C} : semilattice_sup (subobject B) :=
{ sup := λ m n, (sup.obj m).obj n,
  le_sup_left := λ m n, quotient.induction_on₂' m n (λ a b, ⟨mono_over.le_sup_left _ _⟩),
  le_sup_right := λ m n, quotient.induction_on₂' m n (λ a b, ⟨mono_over.le_sup_right _ _⟩),
  sup_le := λ m n k, quotient.induction_on₃' m n k (λ a b c ⟨i⟩ ⟨j⟩, ⟨mono_over.sup_le _ _ _ i j⟩),
  ..subobject.partial_order B }

lemma sup_factors_of_factors_left {A B : C} {X Y : subobject B} {f : A ⟶ B} (P : X.factors f) :
  (X ⊔ Y).factors f :=
factors_of_le f le_sup_left P

lemma sup_factors_of_factors_right {A B : C} {X Y : subobject B} {f : A ⟶ B} (P : Y.factors f) :
  (X ⊔ Y).factors f :=
factors_of_le f le_sup_right P

section
variables [has_zero_morphisms C] [has_zero_object C]

instance {B : C} : semilattice_sup_bot (subobject B) :=
{ ..subobject.order_bot,
  ..subobject.semilattice_sup }

lemma finset_sup_factors {I : Type*} {A B : C} {s : finset I} {P : I → subobject B}
  {f : A ⟶ B} (h : ∃ i ∈ s, (P i).factors f) :
  (s.sup P).factors f :=
begin
  classical,
  revert h,
  apply finset.induction_on s,
  { rintro ⟨_, ⟨⟨⟩, _⟩⟩, },
  { rintros i s nm ih ⟨j, ⟨m, h⟩⟩,
    simp only [finset.sup_insert],
    simp at m, rcases m with (rfl|m),
    { exact sup_factors_of_factors_left h, },
    { exact sup_factors_of_factors_right (ih ⟨j, ⟨m, h⟩⟩), }, },
end

end

end semilattice_sup

section lattice
variables [has_pullbacks C] [has_images C] [has_binary_coproducts C]

instance {B : C} : lattice (subobject B) :=
{ ..subobject.semilattice_inf_top,
  ..subobject.semilattice_sup }

variables [has_zero_morphisms C] [has_zero_object C]

instance {B : C} : bounded_lattice (subobject B) :=
{ ..subobject.semilattice_inf_top,
  ..subobject.semilattice_sup_bot }

end lattice

end subobject

end category_theory
