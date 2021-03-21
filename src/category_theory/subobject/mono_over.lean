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
# Monomorphisms over a fixed object

As preparation for defining `subobject X`, we set up the theory for
`mono_over X := {f : over X // mono f.hom}`.

Here `mono_over X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not yet a partial order.

`subobject X` will be defined as the skeletalization of `mono_over X`.

We provide
* `def pullback [has_pullbacks C] (f : X ⟶ Y) : mono_over Y ⥤ mono_over X`
* `def map (f : X ⟶ Y) [mono f] : mono_over X ⥤ mono_over Y`
* `def «exists» [has_images C] (f : X ⟶ Y) : mono_over X ⥤ mono_over Y`
and prove their basic properties and relationships.

## Notes

This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Scott Morrison.

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
@[derive [category]]
def mono_over (X : C) := {f : over X // mono f.hom}

namespace mono_over

/-- Construct a `mono_over X`. -/
@[simps]
def mk' {X A : C} (f : A ⟶ X) [hf : mono f] : mono_over X := { val := over.mk f, property := hf }

/-- The inclusion from monomorphisms over X to morphisms over X. -/
def forget (X : C) : mono_over X ⥤ over X := full_subcategory_inclusion _

instance : has_coe (mono_over X) C :=
{ coe := λ Y, Y.val.left, }

@[simp]
lemma forget_obj_left {f} : ((forget X).obj f).left = (f : C) := rfl

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
  (((pullback f).obj g) : C) = limits.pullback g.arrow f :=
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
  (((map f).obj g) : C) = g.val.left :=
rfl

@[simp]
lemma map_obj_arrow (f : X ⟶ Y) [mono f] (g : mono_over X) :
  ((map f).obj g).arrow = g.arrow ≫ f :=
rfl

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
variables (f : X ⟶ Y) [has_image f]

/--
The `mono_over Y` for the image inclusion for a morphism `f : X ⟶ Y`.
-/
def image_mono_over (f : X ⟶ Y) [has_image f] : mono_over Y := mono_over.mk' (image.ι f)

@[simp] lemma image_mono_over_arrow (f : X ⟶ Y) [has_image f] :
  (image_mono_over f).arrow = image.ι f :=
rfl

end image

section image

variables [has_images C]

/--
Taking the image of a morphism gives a functor `over X ⥤ mono_over X`.
-/
@[simps]
def image : over X ⥤ mono_over X :=
{ obj := λ f, image_mono_over f.hom,
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

@[simp] lemma top_left (X : C) : ((⊤ : mono_over X) : C) = X := rfl
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

@[simp] lemma bot_left (X : C) : ((⊥ : mono_over X) : C) = 0 := rfl
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

end category_theory
