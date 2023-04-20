/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.sites.sheaf
import category_theory.sites.cover_lifting
import category_theory.adjunction.fully_faithful

/-!
# Dense subsites

We define `cover_dense` functors into sites as functors such that there exists a covering sieve
that factors through images of the functor for each object in `D`.

We will primarily consider cover-dense functors that are also full, since this notion is in general
not well-behaved otherwise. Note that https://ncatlab.org/nlab/show/dense+sub-site indeed has a
weaker notion of cover-dense that loosens this requirement, but it would not have all the properties
we would need, and some sheafification would be needed for here and there.

## Main results

- `category_theory.cover_dense.presheaf_hom`: If `G : C ⥤ (D, K)` is full and cover-dense,
  then given any presheaf `ℱ` and sheaf `ℱ'` on `D`, and a morphism `α : G ⋙ ℱ ⟶ G ⋙ ℱ'`,
  we may glue them together to obtain a morphism of presheaves `ℱ ⟶ ℱ'`.
- `category_theory.cover_dense.sheaf_iso`: If `ℱ` above is a sheaf and `α` is an iso,
  then the result is also an iso.
- `category_theory.cover_dense.iso_of_restrict_iso`: If `G : C ⥤ (D, K)` is full and cover-dense,
  then given any sheaves `ℱ, ℱ'` on `D`, and a morphism `α : ℱ ⟶ ℱ'`, then `α` is an iso if
  `G ⋙ ℱ ⟶ G ⋙ ℱ'` is iso.
- `category_theory.cover_dense.Sheaf_equiv_of_cover_preserving_cover_lifting`:
  If `G : (C, J) ⥤ (D, K)` is fully-faithful, cover-lifting, cover-preserving, and cover-dense,
  then it will induce an equivalence of categories of sheaves valued in a complete category.

## References

* [Elephant]: *Sketches of an Elephant*, ℱ. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

universes w v u

namespace category_theory

variables {C : Type*} [category C] {D : Type*} [category D] {E : Type*} [category E]
variables (J : grothendieck_topology C) (K : grothendieck_topology D)
variables {L : grothendieck_topology E}

/--
An auxiliary structure that witnesses the fact that `f` factors through an image object of `G`.
-/
@[nolint has_nonempty_instance]
structure presieve.cover_by_image_structure (G : C ⥤ D) {V U : D} (f : V ⟶ U) :=
(obj : C)
(lift : V ⟶ G.obj obj)
(map : G.obj obj ⟶ U)
(fac' : lift ≫ map = f . obviously)

restate_axiom presieve.cover_by_image_structure.fac'

attribute [simp, reassoc] presieve.cover_by_image_structure.fac

/--
For a functor `G : C ⥤ D`, and an object `U : D`, `presieve.cover_by_image G U` is the presieve
of `U` consisting of those arrows that factor through images of `G`.
-/
def presieve.cover_by_image (G : C ⥤ D) (U : D) : presieve U :=
λ Y f, nonempty (presieve.cover_by_image_structure G f)

/--
For a functor `G : C ⥤ D`, and an object `U : D`, `sieve.cover_by_image G U` is the sieve of `U`
consisting of those arrows that factor through images of `G`.
-/
def sieve.cover_by_image (G : C ⥤ D) (U : D) : sieve U :=
⟨presieve.cover_by_image G U,
  λ X Y f ⟨⟨Z, f₁, f₂, (e : _ = _)⟩⟩ g,
    ⟨⟨Z, g ≫ f₁, f₂, show (g ≫ f₁) ≫ f₂ = g ≫ f, by rw [category.assoc, ← e]⟩⟩⟩

lemma presieve.in_cover_by_image (G : C ⥤ D) {X : D} {Y : C} (f : G.obj Y ⟶ X) :
  presieve.cover_by_image G X f := ⟨⟨Y, 𝟙 _, f, by simp⟩⟩

/--
A functor `G : (C, J) ⥤ (D, K)` is called `cover_dense` if for each object in `D`,
  there exists a covering sieve in `D` that factors through images of `G`.

This definition can be found in https://ncatlab.org/nlab/show/dense+sub-site Definition 2.2.
-/
structure cover_dense (K : grothendieck_topology D) (G : C ⥤ D) : Prop :=
(is_cover : ∀ (U : D), sieve.cover_by_image G U ∈ K U)

open presieve opposite

namespace cover_dense

variable {K}

variables {A : Type*} [category A] {G : C ⥤ D} (H : cover_dense K G)

-- this is not marked with `@[ext]` because `H` can not be inferred from the type
lemma ext (H : cover_dense K G) (ℱ : SheafOfTypes K) (X : D) {s t : ℱ.val.obj (op X)}
  (h : ∀ ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ.val.map f.op s = ℱ.val.map f.op t) :
  s = t :=
begin
  apply (ℱ.cond (sieve.cover_by_image G X) (H.is_cover X)).is_separated_for.ext,
  rintros Y _ ⟨Z, f₁, f₂, ⟨rfl⟩⟩,
  simp [h f₂]
end

lemma functor_pullback_pushforward_covering [full G] (H : cover_dense K G) {X : C}
  (T : K (G.obj X)) : (T.val.functor_pullback G).functor_pushforward G ∈ K (G.obj X) :=
begin
  refine K.superset_covering _ (K.bind_covering T.property (λ Y f Hf, H.is_cover Y)),
  rintros Y _ ⟨Z, _, f, hf, ⟨W, g, f', ⟨rfl⟩⟩, rfl⟩,
  use W, use G.preimage (f' ≫ f), use g,
  split,
  { simpa using T.val.downward_closed hf f' },
  { simp },
end

/--
(Implementation). Given an hom between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain an hom between the pullbacks of the sheaves of maps from `X`.
-/
@[simps] def hom_over {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) (X : A) :
  G.op ⋙ (ℱ ⋙ coyoneda.obj (op X)) ⟶ G.op ⋙ (sheaf_over ℱ' X).val :=
whisker_right α (coyoneda.obj (op X))

/--
(Implementation). Given an iso between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain an iso between the pullbacks of the sheaves of maps from `X`.
-/
@[simps] def iso_over {ℱ ℱ' : Sheaf K A} (α : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X : A) :
  G.op ⋙ (sheaf_over ℱ X).val ≅ G.op ⋙ (sheaf_over ℱ' X).val :=
iso_whisker_right α (coyoneda.obj (op X))


lemma sheaf_eq_amalgamation (ℱ : Sheaf K A) {X : A} {U : D} {T : sieve U} (hT)
  (x : family_of_elements _ T) (hx) (t) (h : x.is_amalgamation t) :
  t = (ℱ.cond X T hT).amalgamate x hx :=
(ℱ.cond X T hT).is_separated_for x t _ h ((ℱ.cond X T hT).is_amalgamation hx)

include H
variable [full G]
namespace types
variables {ℱ : Dᵒᵖ ⥤ Type v} {ℱ' : SheafOfTypes.{v} K} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val)

/--
(Implementation). Given a section of `ℱ` on `X`, we can obtain a family of elements valued in `ℱ'`
that is defined on a cover generated by the images of `G`. -/
@[simp, nolint unused_arguments] noncomputable
def pushforward_family {X} (x : ℱ.obj (op X)) :
  family_of_elements ℱ'.val (cover_by_image G X) := λ Y f hf,
ℱ'.val.map hf.some.lift.op $ α.app (op _) (ℱ.map hf.some.map.op x : _)

/-- (Implementation). The `pushforward_family` defined is compatible. -/
lemma pushforward_family_compatible {X} (x : ℱ.obj (op X)) :
  (pushforward_family H α x).compatible :=
begin
  intros Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e,
  apply H.ext,
  intros Y f,
  simp only [pushforward_family, ← functor_to_types.map_comp_apply, ← op_comp],
  change (ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _) _ =
    (ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _) _,
  rw ← G.image_preimage (f ≫ g₁ ≫ _),
  rw ← G.image_preimage (f ≫ g₂ ≫ _),
  erw ← α.naturality (G.preimage _).op,
  erw ← α.naturality (G.preimage _).op,
  refine congr_fun _ x,
  simp only [quiver.hom.unop_op, functor.comp_map, ← op_comp, ← category.assoc,
    functor.op_map, ← ℱ.map_comp, G.image_preimage],
  congr' 3,
  simp [e]
end

/-- (Implementation). The morphism `ℱ(X) ⟶ ℱ'(X)` given by gluing the `pushforward_family`. -/
noncomputable
def app_hom (X : D) : ℱ.obj (op X) ⟶ ℱ'.val.obj (op X) := λ x,
  (ℱ'.cond _ (H.is_cover X)).amalgamate
    (pushforward_family H α x)
    (pushforward_family_compatible H α x)

@[simp] lemma pushforward_family_apply {X} (x : ℱ.obj (op X)) {Y : C} (f : G.obj Y ⟶ X) :
  pushforward_family H α x f (presieve.in_cover_by_image G f) = α.app (op Y) (ℱ.map f.op x) :=
begin
  unfold pushforward_family,
  refine congr_fun _ x,
  rw ← G.image_preimage (nonempty.some _ : presieve.cover_by_image_structure _ _).lift,
  change ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _ = ℱ.map f.op ≫ α.app (op Y),
  erw ← α.naturality (G.preimage _).op,
  simp only [← functor.map_comp, ← category.assoc, functor.comp_map, G.image_preimage,
     G.op_map, quiver.hom.unop_op, ← op_comp, presieve.cover_by_image_structure.fac],
end

@[simp] lemma app_hom_restrict {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) (x) :
  ℱ'.val.map f (app_hom H α X x) = α.app (op Y) (ℱ.map f x) :=
begin
  refine ((ℱ'.cond _ (H.is_cover X)).valid_glue
    (pushforward_family_compatible H α x) f.unop (presieve.in_cover_by_image G f.unop)).trans _,
  apply pushforward_family_apply
end

@[simp] lemma app_hom_valid_glue {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) :
  app_hom H α X ≫ ℱ'.val.map f = ℱ.map f ≫ α.app (op Y) :=
by { ext, apply app_hom_restrict }

/--
(Implementation). The maps given in `app_iso` is inverse to each other and gives a `ℱ(X) ≅ ℱ'(X)`.
-/
@[simps] noncomputable
def app_iso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X : D) :
  ℱ.val.obj (op X) ≅ ℱ'.val.obj (op X) :=
{ hom := app_hom H i.hom X,
  inv := app_hom H i.inv X,
  hom_inv_id' := by { ext x, apply H.ext, intros Y f, simp },
  inv_hom_id' := by { ext x, apply H.ext, intros Y f, simp } }

/--
Given an natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of types, where `G` is full
and cover-dense, and `ℱ'` is a sheaf, we may obtain a natural transformation between sheaves.
-/
@[simps] noncomputable
def presheaf_hom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⟶ ℱ'.val :=
{ app := λ X, app_hom H α (unop X), naturality' := λ X Y f,
  begin
    ext x,
    apply H.ext ℱ' (unop Y),
    intros Y' f',
    simp only [app_hom_restrict, types_comp_apply, ← functor_to_types.map_comp_apply],
    rw app_hom_restrict H α (f ≫ f'.op : op (unop X) ⟶ _)
  end }

/--
Given an natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types, where `G` is full and
cover-dense, and `ℱ, ℱ'` are sheaves, we may obtain a natural isomorphism between presheaves.
-/
@[simps] noncomputable
def presheaf_iso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
  ℱ.val ≅ ℱ'.val :=
nat_iso.of_components (λ X, app_iso H i (unop X)) (presheaf_hom H i.hom).naturality

/--
Given an natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types, where `G` is full and
cover-dense, and `ℱ, ℱ'` are sheaves, we may obtain a natural isomorphism between sheaves.
-/
@[simps] noncomputable
def sheaf_iso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) : ℱ ≅ ℱ' :=
{ hom := ⟨(presheaf_iso H i).hom⟩,
  inv := ⟨(presheaf_iso H i).inv⟩,
  hom_inv_id' := by { ext1, apply (presheaf_iso H i).hom_inv_id },
  inv_hom_id' := by { ext1, apply (presheaf_iso H i).inv_hom_id } }

end types
open types

variables {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A}

/-- (Implementation). The sheaf map given in `types.sheaf_hom` is natural in terms of `X`. -/
@[simps] noncomputable
def sheaf_coyoneda_hom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
  coyoneda ⋙ (whiskering_left Dᵒᵖ A Type*).obj ℱ ⟶
  coyoneda ⋙ (whiskering_left Dᵒᵖ A Type*).obj ℱ'.val :=
{ app := λ X, presheaf_hom H (hom_over α (unop X)), naturality' := λ X Y f,
  begin
    ext U x,
    change app_hom H (hom_over α (unop Y)) (unop U) (f.unop ≫ x) =
      f.unop ≫ app_hom H (hom_over α (unop X)) (unop U) x,
    symmetry,
    apply sheaf_eq_amalgamation,
    apply H.is_cover,
    intros Y' f' hf',
    change unop X ⟶ ℱ.obj (op (unop _)) at x,
    dsimp,
    simp only [pushforward_family, functor.comp_map,
      coyoneda_obj_map, hom_over_app, category.assoc],
    congr' 1,
    conv_lhs { rw ← hf'.some.fac },
    simp only [← category.assoc, op_comp, functor.map_comp],
    congr' 1,
    refine (app_hom_restrict H (hom_over α (unop X)) hf'.some.map.op x).trans _,
    simp
  end }

/--
(Implementation). `sheaf_coyoneda_hom` but the order of the arguments of the functor are swapped.
-/
noncomputable
def sheaf_yoneda_hom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
  ℱ ⋙ yoneda ⟶ ℱ'.val ⋙ yoneda :=
begin
  let α := sheaf_coyoneda_hom H α,
  refine { app := _, naturality' := _ },
  { intro U,
    refine { app := λ X, (α.app X).app U,
      naturality' := λ X Y f, by simpa using congr_app (α.naturality f) U } },
  { intros U V i,
    ext X x,
    exact congr_fun ((α.app X).naturality i) x },
end

/--
Given an natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is full and cover-dense, and `ℱ'` is a sheaf, we may obtain a natural transformation
between presheaves.
-/
noncomputable
def sheaf_hom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
  ℱ ⟶ ℱ'.val :=
let α' := sheaf_yoneda_hom H α in
  { app := λ X, yoneda.preimage (α'.app X),
    naturality' := λ X Y f, yoneda.map_injective (by simpa using α'.naturality f) }

/--
Given an natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps] noncomputable
def presheaf_iso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
  ℱ.val ≅ ℱ'.val :=
begin
  haveI : ∀ (X : Dᵒᵖ), is_iso ((sheaf_hom H i.hom).app X),
  { intro X,
    apply is_iso_of_reflects_iso _ yoneda,
    use (sheaf_yoneda_hom H i.inv).app X,
    split;
      ext x : 2;
      simp only [sheaf_hom, nat_trans.comp_app, nat_trans.id_app, functor.image_preimage],
      exact ((presheaf_iso H (iso_over i (unop x))).app X).hom_inv_id,
      exact ((presheaf_iso H (iso_over i (unop x))).app X).inv_hom_id,
    apply_instance },
  haveI : is_iso (sheaf_hom H i.hom) := by apply nat_iso.is_iso_of_is_iso_app,
  apply as_iso (sheaf_hom H i.hom),
end

/--
Given an natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps] noncomputable
def sheaf_iso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) : ℱ ≅ ℱ' :=
{ hom := ⟨(presheaf_iso H i).hom⟩,
  inv := ⟨(presheaf_iso H i).inv⟩,
  hom_inv_id' := by { ext1, apply (presheaf_iso H i).hom_inv_id },
  inv_hom_id' := by { ext1, apply (presheaf_iso H i).inv_hom_id } }

/--
The constructed `sheaf_hom α` is equal to `α` when restricted onto `C`.
-/
lemma sheaf_hom_restrict_eq (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
  whisker_left G.op (sheaf_hom H α) = α :=
begin
  ext X,
  apply yoneda.map_injective,
  ext U,
  erw yoneda.image_preimage,
  symmetry,
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (G.obj (unop X))), from _) = _,
  apply sheaf_eq_amalgamation ℱ' (H.is_cover _),
  intros Y f hf,
  conv_lhs { rw ← hf.some.fac },
  simp only [pushforward_family, functor.comp_map, yoneda_map_app,
    coyoneda_obj_map, op_comp, functor_to_types.map_comp_apply, hom_over_app, ← category.assoc],
  congr' 1,
  simp only [category.assoc],
  congr' 1,
  rw ← G.image_preimage hf.some.map,
  symmetry,
  apply α.naturality (G.preimage hf.some.map).op,
  apply_instance
end

/--
If the pullback map is obtained via whiskering,
then the result `sheaf_hom (whisker_left G.op α)` is equal to `α`.
-/
lemma sheaf_hom_eq (α : ℱ ⟶ ℱ'.val) : sheaf_hom H (whisker_left G.op α) = α :=
begin
  ext X,
  apply yoneda.map_injective,
  swap, { apply_instance },
  ext U,
  erw yoneda.image_preimage,
  symmetry,
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (unop X)), from _) = _,
  apply sheaf_eq_amalgamation ℱ' (H.is_cover _),
  intros Y f hf,
  conv_lhs { rw ← hf.some.fac },
  dsimp,
  simp,
end

/--
A full and cover-dense functor `G` induces an equivalence between morphisms into a sheaf and
morphisms over the restrictions via `G`.
-/
noncomputable
def restrict_hom_equiv_hom : (G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) ≃ (ℱ ⟶ ℱ'.val) :=
{ to_fun := sheaf_hom H,
  inv_fun := whisker_left G.op,
  left_inv := sheaf_hom_restrict_eq H,
  right_inv := sheaf_hom_eq H }

/--
Given a full and cover-dense functor `G` and a natural transformation of sheaves `α : ℱ ⟶ ℱ'`,
if the pullback of `α` along `G` is iso, then `α` is also iso.
-/
lemma iso_of_restrict_iso {ℱ ℱ' : Sheaf K A} (α : ℱ ⟶ ℱ')
  (i : is_iso (whisker_left G.op α.val)) : is_iso α :=
begin
  convert is_iso.of_iso (sheaf_iso H (as_iso (whisker_left G.op α.val))) using 1,
  ext1,
  apply (sheaf_hom_eq _ _).symm
end

/-- A fully faithful cover-dense functor preserves compatible families. -/
lemma compatible_preserving [faithful G] : compatible_preserving K G :=
begin
  constructor,
  intros ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq,
  apply H.ext,
  intros W i,
  simp only [← functor_to_types.map_comp_apply, ← op_comp],
  rw ← G.image_preimage (i ≫ f₁),
  rw ← G.image_preimage (i ≫ f₂),
  apply hx,
  apply G.map_injective,
  simp [eq]
end

noncomputable
instance sites.pullback.full [faithful G] (Hp : cover_preserving J K G) :
  full (sites.pullback A H.compatible_preserving Hp) :=
{ preimage := λ ℱ ℱ' α, ⟨H.sheaf_hom α.val⟩,
  witness' := λ ℱ ℱ' α, Sheaf.hom.ext _ _ $ H.sheaf_hom_restrict_eq α.val }

instance sites.pullback.faithful [faithful G] (Hp : cover_preserving J K G) :
  faithful (sites.pullback A H.compatible_preserving Hp) :=
{ map_injective' := begin
    intros ℱ ℱ' α β e,
    ext1,
    apply_fun (λ e, e.val) at e,
    dsimp at e,
    rw [← H.sheaf_hom_eq α.val, ← H.sheaf_hom_eq β.val, e],
  end }

end cover_dense

end category_theory

namespace category_theory.cover_dense

open category_theory

variables {C D : Type u} [category.{v} C] [category.{v} D]
variables {G : C ⥤ D} [full G] [faithful G]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}
variables {A : Type w} [category.{max u v} A] [limits.has_limits A]
variables (Hd : cover_dense K G) (Hp : cover_preserving J K G) (Hl : cover_lifting J K G)

include Hd Hp Hl

/--
Given a functor between small sites that is cover-dense, cover-preserving, and cover-lifting,
it induces an equivalence of category of sheaves valued in a complete category.
-/
@[simps functor inverse] noncomputable
def Sheaf_equiv_of_cover_preserving_cover_lifting : Sheaf J A ≌ Sheaf K A :=
begin
  symmetry,
  let α := sites.pullback_copullback_adjunction.{w v u} A Hp Hl Hd.compatible_preserving,
  haveI : ∀ (X : Sheaf J A), is_iso (α.counit.app X),
  { intro ℱ,
    apply_with (reflects_isomorphisms.reflects (Sheaf_to_presheaf J A)) { instances := ff },
    exact is_iso.of_iso ((@as_iso _ _ _ _ _ (Ran.reflective A G.op)).app ℱ.val) },
  haveI : is_iso α.counit := nat_iso.is_iso_of_is_iso_app _,
  exact
  { functor := sites.pullback A Hd.compatible_preserving Hp,
    inverse := sites.copullback A Hl,
    unit_iso := as_iso α.unit,
    counit_iso := as_iso α.counit,
    functor_unit_iso_comp' := λ ℱ, by convert α.left_triangle_components }
end

end category_theory.cover_dense
