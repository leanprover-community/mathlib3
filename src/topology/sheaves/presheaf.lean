/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Mario Carneiro, Reid Barton, Andrew Yang
-/
import category_theory.limits.kan_extension
import topology.category.Top.opens
import category_theory.adjunction.opposites

/-!
# Presheaves on a topological space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `presheaf C X` simply as `(opens X)ᵒᵖ ⥤ C`,
and inherit the category structure with natural transformations as morphisms.

We define
* `pushforward_obj {X Y : Top.{w}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C`
with notation `f _* ℱ`
and for `ℱ : X.presheaf C` provide the natural isomorphisms
* `pushforward.id : (𝟙 X) _* ℱ ≅ ℱ`
* `pushforward.comp : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ)`
along with their `@[simp]` lemmas.

We also define the functors `pushforward` and `pullback` between the categories
`X.presheaf C` and `Y.presheaf C`, and provide their adjunction at
`pushforward_pullback_adjunction`.
-/

universes w v u

open category_theory
open topological_space
open opposite

variables (C : Type u) [category.{v} C]

namespace Top

/-- The category of `C`-valued presheaves on a (bundled) topological space `X`. -/
@[derive category, nolint has_nonempty_instance]
def presheaf (X : Top.{w}) : Type (max u v w) := (opens X)ᵒᵖ ⥤ C

variables {C}

namespace presheaf

local attribute [instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

/-- Tag lemmas to use in `Top.presheaf.restrict_tac`.  -/
@[user_attribute]
meta def restrict_attr : user_attribute (tactic unit → tactic unit) unit :=
{ name      := `sheaf_restrict,
  descr     := "tag lemmas to use in `Top.presheaf.restrict_tac`",
  cache_cfg :=
  { mk_cache := λ ns, pure $ λ t, do
    { ctx <- tactic.local_context,
      ctx.any_of (tactic.focus1 ∘ (tactic.apply' >=> (λ _, tactic.done)) >=> (λ _, t)) <|>
      ns.any_of (tactic.focus1 ∘ (tactic.resolve_name >=> tactic.to_expr >=> tactic.apply' >=>
        (λ _, tactic.done)) >=> (λ _, t)) },
    dependencies := [] } }

/-- A tactic to discharge goals of type `U ≤ V` for `Top.presheaf.restrict_open` -/
meta def restrict_tac : Π (n : ℕ), tactic unit
| 0 := tactic.fail "`restrict_tac` failed"
| (n + 1) := monad.join (restrict_attr.get_cache <*> pure tactic.done) <|>
    `[apply' le_trans, mjoin (restrict_attr.get_cache <*> pure (restrict_tac n))]

/-- A tactic to discharge goals of type `U ≤ V` for `Top.presheaf.restrict_open`.
Defaults to three iterations. -/
meta def restrict_tac' := restrict_tac 3

attribute [sheaf_restrict] bot_le le_top le_refl inf_le_left inf_le_right le_sup_left le_sup_right

example {X : Top} {v w x y z : opens X} (h₀ : v ≤ x) (h₁ : x ≤ z ⊓ w) (h₂ : x ≤ y ⊓ z) :
  v ≤ y := by restrict_tac'

/-- The restriction of a section along an inclusion of open sets.
For `x : F.obj (op V)`, we provide the notation `x |_ₕ i` (`h` stands for `hom`) for `i : U ⟶ V`,
and the notation `x |_ₗ U ⟪i⟫` (`l` stands for `le`) for `i : U ≤ V`.
-/
def restrict {X : Top} {C : Type*} [category C] [concrete_category C]
  {F : X.presheaf C} {V : opens X} (x : F.obj (op V)) {U : opens X} (h : U ⟶ V) : F.obj (op U) :=
F.map h.op x

localized "infixl ` |_ₕ `: 80 := Top.presheaf.restrict" in algebraic_geometry

localized "notation x ` |_ₗ `: 80 U ` ⟪` e `⟫ ` :=
@Top.presheaf.restrict _ _ _ _ _ _ x U (@hom_of_le (opens _) _ U _ e)" in algebraic_geometry

/-- The restriction of a section along an inclusion of open sets.
For `x : F.obj (op V)`, we provide the notation `x |_ U`, where the proof `U ≤ V` is inferred by
the tactic `Top.presheaf.restrict_tac'` -/
abbreviation restrict_open {X : Top} {C : Type*} [category C] [concrete_category C]
  {F : X.presheaf C} {V : opens X} (x : F.obj (op V)) (U : opens X)
  (e : U ≤ V . Top.presheaf.restrict_tac') : F.obj (op U) :=
x |_ₗ U ⟪e⟫

localized "infixl ` |_ `: 80 := Top.presheaf.restrict_open" in algebraic_geometry

@[simp]
lemma restrict_restrict {X : Top} {C : Type*} [category C] [concrete_category C]
  {F : X.presheaf C} {U V W : opens X} (e₁ : U ≤ V) (e₂ : V ≤ W) (x : F.obj (op W)) :
    x |_ V |_ U = x |_ U :=
by { delta restrict_open restrict, rw [← comp_apply, ← functor.map_comp], refl }

@[simp]
lemma map_restrict {X : Top} {C : Type*} [category C] [concrete_category C]
  {F G : X.presheaf C} (e : F ⟶ G) {U V : opens X} (h : U ≤ V) (x : F.obj (op V)) :
    e.app _ (x |_ U) = (e.app _ x) |_ U :=
by { delta restrict_open restrict, rw [← comp_apply, nat_trans.naturality, comp_apply] }

/-- Pushforward a presheaf on `X` along a continuous map `f : X ⟶ Y`, obtaining a presheaf
on `Y`. -/
def pushforward_obj {X Y : Top.{w}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C :=
(opens.map f).op ⋙ ℱ

infix ` _* `: 80 := pushforward_obj

@[simp] lemma pushforward_obj_obj {X Y : Top.{w}} (f : X ⟶ Y) (ℱ : X.presheaf C) (U : (opens Y)ᵒᵖ) :
  (f _* ℱ).obj U = ℱ.obj ((opens.map f).op.obj U) := rfl

@[simp] lemma pushforward_obj_map {X Y : Top.{w}} (f : X ⟶ Y) (ℱ : X.presheaf C)
  {U V : (opens Y)ᵒᵖ} (i : U ⟶ V) :
  (f _* ℱ).map i = ℱ.map ((opens.map f).op.map i) := rfl

/--
An equality of continuous maps induces a natural isomorphism between the pushforwards of a presheaf
along those maps.
-/
def pushforward_eq {X Y : Top.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.presheaf C) :
  f _* ℱ ≅ g _* ℱ :=
iso_whisker_right (nat_iso.op (opens.map_iso f g h).symm) ℱ

lemma pushforward_eq' {X Y : Top.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.presheaf C) :
  f _* ℱ = g _* ℱ :=
by rw h

@[simp] lemma pushforward_eq_hom_app
  {X Y : Top.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.presheaf C) (U) :
  (pushforward_eq h ℱ).hom.app U =
    ℱ.map (begin dsimp [functor.op], apply quiver.hom.op, apply eq_to_hom, rw h, end) :=
by simp [pushforward_eq]

lemma pushforward_eq'_hom_app
  {X Y : Top.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.presheaf C) (U) :
  nat_trans.app (eq_to_hom (pushforward_eq' h ℱ)) U = ℱ.map (eq_to_hom (by rw h)) :=
by simpa [eq_to_hom_map]

@[simp]
lemma pushforward_eq_rfl {X Y : Top.{w}} (f : X ⟶ Y) (ℱ : X.presheaf C) (U) :
  (pushforward_eq (rfl : f = f) ℱ).hom.app (op U) = 𝟙 _ :=
begin
  dsimp [pushforward_eq],
  simp,
end

lemma pushforward_eq_eq {X Y : Top.{w}} {f g : X ⟶ Y} (h₁ h₂ : f = g) (ℱ : X.presheaf C) :
  ℱ.pushforward_eq h₁ = ℱ.pushforward_eq h₂ :=
rfl

namespace pushforward
variables {X : Top.{w}} (ℱ : X.presheaf C)

/-- The natural isomorphism between the pushforward of a presheaf along the identity continuous map
and the original presheaf. -/
def id : (𝟙 X) _* ℱ ≅ ℱ :=
(iso_whisker_right (nat_iso.op (opens.map_id X).symm) ℱ) ≪≫ functor.left_unitor _

lemma id_eq : (𝟙 X) _* ℱ = ℱ :=
by { unfold pushforward_obj, rw opens.map_id_eq, erw functor.id_comp }

@[simp] lemma id_hom_app' (U) (p) :
  (id ℱ).hom.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) :=
by { dsimp [id], simp, }

local attribute [tidy] tactic.op_induction'

@[simp, priority 990] lemma id_hom_app (U) :
  (id ℱ).hom.app U = ℱ.map (eq_to_hom (opens.op_map_id_obj U)) :=
begin
  -- was `tidy`
  induction U using opposite.rec,
  cases U,
  rw [id_hom_app'],
  congr
end

@[simp] lemma id_inv_app' (U) (p) : (id ℱ).inv.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) :=
by { dsimp [id], simp, }

/-- The natural isomorphism between
the pushforward of a presheaf along the composition of two continuous maps and
the corresponding pushforward of a pushforward. -/
def comp {Y Z : Top.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ) :=
iso_whisker_right (nat_iso.op (opens.map_comp f g).symm) ℱ

lemma comp_eq {Y Z : Top.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) _* ℱ = g _* (f _* ℱ) :=
rfl

@[simp] lemma comp_hom_app {Y Z : Top.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (comp ℱ f g).hom.app U = 𝟙 _ :=
by { dsimp [comp], tidy, }

@[simp] lemma comp_inv_app {Y Z : Top.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (comp ℱ f g).inv.app U = 𝟙 _ :=
by { dsimp [comp], tidy, }

end pushforward

/--
A morphism of presheaves gives rise to a morphisms of the pushforwards of those presheaves.
-/
@[simps]
def pushforward_map {X Y : Top.{w}} (f : X ⟶ Y) {ℱ 𝒢 : X.presheaf C} (α : ℱ ⟶ 𝒢) :
  f _* ℱ ⟶ f _* 𝒢 :=
{ app := λ U, α.app _,
  naturality' := λ U V i, by { erw α.naturality, refl, } }

open category_theory.limits
section pullback
variable [has_colimits C]
noncomputable theory

/--
Pullback a presheaf on `Y` along a continuous map `f : X ⟶ Y`, obtaining a presheaf on `X`.

This is defined in terms of left Kan extensions, which is just a fancy way of saying
"take the colimits over the open sets whose preimage contains U".
-/
@[simps]
def pullback_obj {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : Y.presheaf C) : X.presheaf C :=
(Lan (opens.map f).op).obj ℱ

/-- Pulling back along continuous maps is functorial. -/
def pullback_map {X Y : Top.{v}} (f : X ⟶ Y) {ℱ 𝒢 : Y.presheaf C} (α : ℱ ⟶ 𝒢) :
  pullback_obj f ℱ ⟶ pullback_obj f 𝒢 :=
(Lan (opens.map f).op).map α

/-- If `f '' U` is open, then `f⁻¹ℱ U ≅ ℱ (f '' U)`.  -/
@[simps]
def pullback_obj_obj_of_image_open {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : Y.presheaf C) (U : opens X)
  (H : is_open (f '' U)) : (pullback_obj f ℱ).obj (op U) ≅ ℱ.obj (op ⟨_, H⟩) :=
begin
  let x : costructured_arrow (opens.map f).op (op U) := begin
    refine @costructured_arrow.mk _ _ _ _ _ (op (opens.mk (f '' U) H)) _ _,
    exact ((@hom_of_le _ _ _ ((opens.map f).obj ⟨_, H⟩) (set.image_preimage.le_u_l _)).op),
  end,
  have hx : is_terminal x :=
  { lift := λ s,
    begin
      fapply costructured_arrow.hom_mk,
      change op (unop _) ⟶ op (⟨_, H⟩ : opens _),
      refine (hom_of_le _).op,
      exact (set.image_subset f s.X.hom.unop.le).trans (set.image_preimage.l_u_le ↑(unop s.X.left)),
      simp
    end },
  exact is_colimit.cocone_point_unique_up_to_iso
    (colimit.is_colimit _)
    (colimit_of_diagram_terminal hx _),
end

namespace pullback
variables {X Y : Top.{v}} (ℱ : Y.presheaf C)

/-- The pullback along the identity is isomorphic to the original presheaf. -/
def id : pullback_obj (𝟙 _) ℱ ≅ ℱ :=
nat_iso.of_components
  (λ U, pullback_obj_obj_of_image_open (𝟙 _) ℱ (unop U) (by simpa using U.unop.2) ≪≫
    ℱ.map_iso (eq_to_iso (by simp)))
  (λ U V i,
  begin
      ext, simp,
      erw colimit.pre_desc_assoc,
      erw colimit.ι_desc_assoc,
      erw colimit.ι_desc_assoc,
      dsimp, simp only [←ℱ.map_comp], congr
  end)

lemma id_inv_app (U : opens Y) :
  (id ℱ).inv.app (op U) = colimit.ι (Lan.diagram (opens.map (𝟙 Y)).op ℱ (op U))
    (@costructured_arrow.mk _ _ _ _ _ (op U) _ (eq_to_hom (by simp))) :=
begin
  rw [← category.id_comp ((id ℱ).inv.app (op U)), ← nat_iso.app_inv, iso.comp_inv_eq],
  dsimp [id],
  rw colimit.ι_desc_assoc,
  dsimp,
  rw [← ℱ.map_comp, ← ℱ.map_id], refl,
end

end pullback
end pullback
variable (C)

/--
The pushforward functor.
-/
def pushforward {X Y : Top.{w}} (f : X ⟶ Y) : X.presheaf C ⥤ Y.presheaf C :=
{ obj := pushforward_obj f,
  map := @pushforward_map _ _ X Y f }

@[simp]
lemma pushforward_map_app' {X Y : Top.{w}} (f : X ⟶ Y)
  {ℱ 𝒢 : X.presheaf C} (α : ℱ ⟶ 𝒢) {U : (opens Y)ᵒᵖ} :
  ((pushforward C f).map α).app U = α.app (op $ (opens.map f).obj U.unop) := rfl

lemma id_pushforward {X : Top.{w}} : pushforward C (𝟙 X) = 𝟭 (X.presheaf C) :=
begin
  apply category_theory.functor.ext,
  { intros,
    ext U,
    have h := f.congr, erw h (opens.op_map_id_obj U),
    simpa [eq_to_hom_map], },
  { intros, apply pushforward.id_eq },
end

section iso

/-- A homeomorphism of spaces gives an equivalence of categories of presheaves. -/
@[simps] def presheaf_equiv_of_iso {X Y : Top} (H : X ≅ Y) :
  X.presheaf C ≌ Y.presheaf C :=
equivalence.congr_left (opens.map_map_iso H).symm.op

variable {C}

/--
If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
def to_pushforward_of_iso {X Y : Top} (H : X ≅ Y) {ℱ : X.presheaf C} {𝒢 : Y.presheaf C}
  (α : H.hom _* ℱ ⟶ 𝒢) : ℱ ⟶ H.inv _* 𝒢 :=
(presheaf_equiv_of_iso _ H).to_adjunction.hom_equiv ℱ 𝒢 α

@[simp]
lemma to_pushforward_of_iso_app {X Y : Top} (H₁ : X ≅ Y) {ℱ : X.presheaf C} {𝒢 : Y.presheaf C}
  (H₂ : H₁.hom _* ℱ ⟶ 𝒢) (U : (opens X)ᵒᵖ) :
(to_pushforward_of_iso H₁ H₂).app U =
  ℱ.map (eq_to_hom (by simp [opens.map, set.preimage_preimage])) ≫
  H₂.app (op ((opens.map H₁.inv).obj (unop U))) :=
begin
  delta to_pushforward_of_iso,
  simp only [equiv.to_fun_as_coe, nat_trans.comp_app, equivalence.equivalence_mk'_unit,
    eq_to_hom_map, eq_to_hom_op, eq_to_hom_trans, presheaf_equiv_of_iso_unit_iso_hom_app_app,
    equivalence.to_adjunction, equivalence.equivalence_mk'_counit,
    presheaf_equiv_of_iso_inverse_map_app, adjunction.mk_of_unit_counit_hom_equiv_apply],
  congr,
end

/--
If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
def pushforward_to_of_iso {X Y : Top} (H₁ : X ≅ Y) {ℱ : Y.presheaf C} {𝒢 : X.presheaf C}
  (H₂ : ℱ ⟶ H₁.hom _* 𝒢) : H₁.inv _* ℱ ⟶ 𝒢 :=
((presheaf_equiv_of_iso _ H₁.symm).to_adjunction.hom_equiv ℱ 𝒢).symm H₂

@[simp]
lemma pushforward_to_of_iso_app {X Y : Top} (H₁ : X ≅ Y) {ℱ : Y.presheaf C} {𝒢 : X.presheaf C}
  (H₂ : ℱ ⟶ H₁.hom _* 𝒢) (U : (opens X)ᵒᵖ) :
(pushforward_to_of_iso H₁ H₂).app U =
  H₂.app (op ((opens.map H₁.inv).obj (unop U))) ≫
  𝒢.map (eq_to_hom (by simp [opens.map, set.preimage_preimage])) :=
by simpa [pushforward_to_of_iso, equivalence.to_adjunction]

end iso

variables (C) [has_colimits C]

/-- Pullback a presheaf on `Y` along a continuous map `f : X ⟶ Y`, obtaining a presheaf
on `X`. -/
@[simps map_app]
def pullback {X Y : Top.{v}} (f : X ⟶ Y) : Y.presheaf C ⥤ X.presheaf C := Lan (opens.map f).op

@[simp] lemma pullback_obj_eq_pullback_obj {C} [category C] [has_colimits C] {X Y : Top.{w}}
  (f : X ⟶ Y) (ℱ : Y.presheaf C) : (pullback C f).obj ℱ = pullback_obj f ℱ := rfl

/-- The pullback and pushforward along a continuous map are adjoint to each other. -/
@[simps unit_app_app counit_app_app]
def pushforward_pullback_adjunction {X Y : Top.{v}} (f : X ⟶ Y) :
  pullback C f ⊣ pushforward C f := Lan.adjunction _ _

/-- Pulling back along a homeomorphism is the same as pushing forward along its inverse. -/
def pullback_hom_iso_pushforward_inv {X Y : Top.{v}} (H : X ≅ Y) :
  pullback C H.hom ≅ pushforward C H.inv :=
adjunction.left_adjoint_uniq
  (pushforward_pullback_adjunction C H.hom)
  (presheaf_equiv_of_iso C H.symm).to_adjunction

/-- Pulling back along the inverse of a homeomorphism is the same as pushing forward along it. -/
def pullback_inv_iso_pushforward_hom {X Y : Top.{v}} (H : X ≅ Y) :
  pullback C H.inv ≅ pushforward C H.hom :=
adjunction.left_adjoint_uniq
  (pushforward_pullback_adjunction C H.inv)
  (presheaf_equiv_of_iso C H).to_adjunction

end presheaf
end Top
