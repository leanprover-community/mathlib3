/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import category_theory.comma
import category_theory.pempty
import category_theory.limits.connected
import category_theory.limits.creates
import category_theory.limits.shapes.constructions.limits_of_products_and_equalizers
import category_theory.limits.shapes.constructions.equalizers

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

open category_theory category_theory.limits

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C]
variable {X : C}

namespace category_theory.functor

@[simps] def to_cocone (F : J ⥤ over X) : cocone (F ⋙ over.forget) :=
{ X := X,
  ι := { app := λ j, (F.obj j).hom } }

@[simps] def to_cone (F : J ⥤ under X) : cone (F ⋙ under.forget) :=
{ X := X,
  π := { app := λ j, (F.obj j).hom } }

end category_theory.functor

namespace category_theory.over

@[simps] def colimit (F : J ⥤ over X) [has_colimit (F ⋙ forget)] : cocone F :=
{ X := mk $ colimit.desc (F ⋙ forget) F.to_cocone,
  ι :=
  { app := λ j, hom_mk $ colimit.ι (F ⋙ forget) j,
    naturality' :=
    begin
      intros j j' f,
      have := colimit.w (F ⋙ forget) f,
      tidy
    end } }

def forget_colimit_is_colimit (F : J ⥤ over X) [has_colimit (F ⋙ forget)] :
  is_colimit (forget.map_cocone (colimit F)) :=
is_colimit.of_iso_colimit (colimit.is_colimit (F ⋙ forget)) (cocones.ext (iso.refl _) (by tidy))

instance : reflects_colimits (forget : over X ⥤ C) :=
{ reflects_colimits_of_shape := λ J 𝒥,
  { reflects_colimit := λ F,
    by constructor; exactI λ t ht,
    { desc := λ s, hom_mk (ht.desc (forget.map_cocone s))
        begin
          apply ht.hom_ext, intro j,
          rw [←category.assoc, ht.fac],
          transitivity (F.obj j).hom,
          exact w (s.ι.app j), -- TODO: How to write (s.ι.app j).w?
          exact (w (t.ι.app j)).symm,
        end,
      fac' := begin
        intros s j, ext, exact ht.fac (forget.map_cocone s) j
        -- TODO: Ask Simon about multiple ext lemmas for defeq types (comma_morphism & over.category.hom)
      end,
      uniq' :=
      begin
        intros s m w,
        ext1 j,
        exact ht.uniq (forget.map_cocone s) m.left (λ j, congr_arg comma_morphism.left (w j))
      end } } }

instance has_colimit {F : J ⥤ over X} [has_colimit (F ⋙ forget)] : has_colimit F :=
{ cocone := colimit F,
  is_colimit := reflects_colimit.reflects (forget_colimit_is_colimit F) }

instance has_colimits_of_shape [has_colimits_of_shape J C] :
  has_colimits_of_shape J (over X) :=
{ has_colimit := λ F, by apply_instance }

instance has_colimits [has_colimits C] : has_colimits (over X) :=
{ has_colimits_of_shape := λ J 𝒥, by resetI; apply_instance }

instance forget_preserves_colimit {X : C} {F : J ⥤ over X} [has_colimit (F ⋙ forget)] :
  preserves_colimit F (forget : over X ⥤ C) :=
preserves_colimit_of_preserves_colimit_cocone (colimit.is_colimit F) (forget_colimit_is_colimit F)

instance forget_preserves_colimits_of_shape [has_colimits_of_shape J C] {X : C} :
  preserves_colimits_of_shape J (forget : over X ⥤ C) :=
{ preserves_colimit := λ F, by apply_instance }

instance forget_preserves_colimits [has_colimits C] {X : C} :
  preserves_colimits (forget : over X ⥤ C) :=
{ preserves_colimits_of_shape := λ J 𝒥, by apply_instance }

namespace construct_products

/-- (Impl) Given a product shape in `C/B`, construct the corresponding wide pullback diagram in `C`. -/
@[reducible]
def wide_pullback_diagram_of_diagram_over (B : C) {J : Type v} (F : discrete J ⥤ over B) : wide_pullback_shape J ⥤ C :=
wide_pullback_shape.wide_cospan B (λ j, (F.obj j).left) (λ j, (F.obj j).hom)

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def cones_equiv_inverse_obj (B : C) {J : Type v} (F : discrete J ⥤ over B) (c : cone F) :
  cone (wide_pullback_diagram_of_diagram_over B F) :=
{ X := c.X.left,
  π :=
  { app := λ X, option.cases_on X c.X.hom (λ (j : J), (c.π.app j).left),
  -- `tidy` can do this using `case_bash`, but let's try to be a good `-T50000` citizen:
    naturality' := λ X Y f,
    begin
      dsimp, cases X; cases Y; cases f,
      { rw [category.id_comp, category.comp_id], },
      { rw [over.w, category.id_comp], },
      { rw [category.id_comp, category.comp_id], },
    end } }

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def cones_equiv_inverse (B : C) {J : Type v} (F : discrete J ⥤ over B) :
  cone F ⥤ cone (wide_pullback_diagram_of_diagram_over B F) :=
{ obj := cones_equiv_inverse_obj B F,
  map := λ c₁ c₂ f,
  { hom := f.hom.left,
    w' := λ j,
    begin
      cases j,
      { simp },
      { dsimp,
        rw ← f.w j,
        refl }
    end } }

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def cones_equiv_functor (B : C) {J : Type v} (F : discrete J ⥤ over B) :
  cone (wide_pullback_diagram_of_diagram_over B F) ⥤ cone F :=
{ obj := λ c,
  { X := over.mk (c.π.app none),
    π := { app := λ j, over.hom_mk (c.π.app (some j)) (by apply c.w (wide_pullback_shape.hom.term j)) } },
  map := λ c₁ c₂ f,
  { hom := over.hom_mk f.hom } }

local attribute [tidy] tactic.case_bash

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp]
def cones_equiv_unit_iso (B : C) {J : Type v} (F : discrete J ⥤ over B) :
  𝟭 (cone (wide_pullback_diagram_of_diagram_over B F)) ≅
    cones_equiv_functor B F ⋙ cones_equiv_inverse B F :=
nat_iso.of_components (λ _, cones.ext {hom := 𝟙 _, inv := 𝟙 _} (by tidy)) (by tidy)

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp]
def cones_equiv_counit_iso (B : C) {J : Type v} (F : discrete J ⥤ over B) :
  cones_equiv_inverse B F ⋙ cones_equiv_functor B F ≅ 𝟭 (cone F) :=
nat_iso.of_components
  (λ _, cones.ext {hom := over.hom_mk (𝟙 _), inv := over.hom_mk (𝟙 _)} (by tidy)) (by tidy)

-- TODO: Can we add `. obviously` to the second arguments of `nat_iso.of_components` and `cones.ext`?
/-- (Impl) Establish an equivalence between the category of cones for `F` and for the "grown" `F`. -/
@[simps]
def cones_equiv (B : C) {J : Type v} (F : discrete J ⥤ over B) :
  cone (wide_pullback_diagram_of_diagram_over B F) ≌ cone F :=
{ functor := cones_equiv_functor B F,
  inverse := cones_equiv_inverse B F,
  unit_iso := cones_equiv_unit_iso B F,
  counit_iso := cones_equiv_counit_iso B F, }

/-- Use the above equivalence to prove we have a limit. -/
def has_over_limit_discrete_of_wide_pullback_limit {B : C} {J : Type v} (F : discrete J ⥤ over B)
  [has_limit (wide_pullback_diagram_of_diagram_over B F)] :
  has_limit F :=
{ cone := _,
  is_limit := is_limit.of_cone_equiv
    (cones_equiv B F).functor (limit.is_limit (wide_pullback_diagram_of_diagram_over B F)) }

/-- Given a wide pullback in `C`, construct a product in `C/B`. -/
def over_product_of_wide_pullback {J : Type v} [has_limits_of_shape (wide_pullback_shape J) C] {B : C} :
  has_limits_of_shape (discrete J) (over B) :=
{ has_limit := λ F, has_over_limit_discrete_of_wide_pullback_limit F }

/-- Given a pullback in `C`, construct a binary product in `C/B`. -/
def over_binary_product_of_pullback [has_pullbacks C] {B : C} :
  has_binary_products (over B) :=
{ has_limits_of_shape := over_product_of_wide_pullback }

/-- Given all wide pullbacks in `C`, construct products in `C/B`. -/
def over_products_of_wide_pullbacks [has_wide_pullbacks C] {B : C} :
  has_products (over B) :=
{ has_limits_of_shape := λ J, over_product_of_wide_pullback }

/-- Given all finite wide pullbacks in `C`, construct finite products in `C/B`. -/
def over_finite_products_of_finite_wide_pullbacks [has_finite_wide_pullbacks C] {B : C} :
  has_finite_products (over B) :=
{ has_limits_of_shape := λ J 𝒥₁ 𝒥₂, by exactI over_product_of_wide_pullback }

end construct_products

/-- Construct terminal object in the over category. -/
instance (B : C) : has_terminal (over B) :=
{ has_limits_of_shape :=
  { has_limit := λ F,
    { cone :=
      { X := over.mk (𝟙 _),
        π := { app := λ p, pempty.elim p } },
      is_limit :=
        { lift := λ s, over.hom_mk _,
          fac' := λ _ j, j.elim,
          uniq' := λ s m _,
            begin
              ext,
              rw over.hom_mk_left,
              have := m.w,
              dsimp at this,
              rwa [category.comp_id, category.comp_id] at this
            end } } } }

namespace creates_connected

/--
(Impl) Given a diagram in the over category, produce a natural transformation from the
diagram legs to the specific object.
-/
def nat_trans_in_over {B : C} (F : J ⥤ over B) :
  F ⋙ forget ⟶ (category_theory.functor.const J).obj B :=
{ app := λ j, (F.obj j).hom }

local attribute [tidy] tactic.case_bash

/--
(Impl) Given a cone in the base category, raise it to a cone in the over category. Note this is
where the connected assumption is used.
-/
@[simps]
def raise_cone [connected J] {B : C} {F : J ⥤ over B} (c : cone (F ⋙ forget)) :
  cone F :=
{ X := over.mk (c.π.app (default J) ≫ (F.obj (default J)).hom),
  π :=
  { app := λ j, over.hom_mk (c.π.app j) (nat_trans_from_connected (c.π ≫ nat_trans_in_over F) j) } }

lemma raised_cone_lowers_to_original [connected J] {B : C} {F : J ⥤ over B}
  (c : cone (F ⋙ forget)) (t : is_limit c) :
  forget.map_cone (raise_cone c) = c :=
by tidy

/-- (Impl) Show that the raised cone is a limit. -/
def raised_cone_is_limit [connected J] {B : C} {F : J ⥤ over B} {c : cone (F ⋙ forget)} (t : is_limit c) :
  is_limit (raise_cone c) :=
{ lift := λ s, over.hom_mk (t.lift (forget.map_cone s))
               (by { dsimp, simp }),
  uniq' := λ s m K, by { ext1, apply t.hom_ext, intro j, simp [← K j] } }

end creates_connected

/-- The forgetful functor from the over category creates any connected limit. -/
instance forget_creates_connected_limits [connected J] {B : C} : creates_limits_of_shape J (forget : over B ⥤ C) :=
{ creates_limit := λ K,
    creates_limit_of_reflects_iso (λ c t,
      { lifted_cone := creates_connected.raise_cone c,
        valid_lift := eq_to_iso (creates_connected.raised_cone_lowers_to_original c t),
        makes_limit := creates_connected.raised_cone_is_limit t } ) }

/-- The over category has any connected limit which the original category has. -/
instance has_connected_limits {B : C} [connected J] [has_limits_of_shape J C] : has_limits_of_shape J (over B) :=
{ has_limit := λ F, has_limit_of_created F (forget : over B ⥤ C) }

/-- Make sure we can derive pullbacks in `over B`. -/
example {B : C} [has_pullbacks C] : has_pullbacks (over B) :=
{ has_limits_of_shape := infer_instance }

/-- Make sure we can derive equalizers in `over B`. -/
example {B : C} [has_equalizers C] : has_equalizers (over B) :=
{ has_limits_of_shape := infer_instance }

instance has_finite_limits {B : C} [has_finite_wide_pullbacks C] : has_finite_limits (over B) :=
begin
  apply @finite_limits_from_equalizers_and_finite_products _ _ _ _,
  { exact construct_products.over_finite_products_of_finite_wide_pullbacks },
  { apply @has_equalizers_of_pullbacks_and_binary_products _ _ _ _,
    { haveI: has_pullbacks C := ⟨infer_instance⟩,
      exact construct_products.over_binary_product_of_pullback },
    { split,
      apply_instance} }
end

instance has_limits {B : C} [has_wide_pullbacks C] : has_limits (over B) :=
begin
  apply @limits_from_equalizers_and_products _ _ _ _,
  { exact construct_products.over_products_of_wide_pullbacks },
  { apply @has_equalizers_of_pullbacks_and_binary_products _ _ _ _,
    { haveI: has_pullbacks C := ⟨infer_instance⟩,
      exact construct_products.over_binary_product_of_pullback },
    { split,
      apply_instance } }
end

end category_theory.over

namespace category_theory.under

@[simps] def limit (F : J ⥤ under X) [has_limit (F ⋙ forget)] : cone F :=
{ X := mk $ limit.lift (F ⋙ forget) F.to_cone,
  π :=
  { app := λ j, hom_mk $ limit.π (F ⋙ forget) j,
    naturality' :=
    begin
      intros j j' f,
      have := (limit.w (F ⋙ forget) f).symm,
      tidy
    end } }

def forget_limit_is_limit (F : J ⥤ under X) [has_limit (F ⋙ forget)] :
  is_limit (forget.map_cone (limit F)) :=
is_limit.of_iso_limit (limit.is_limit (F ⋙ forget)) (cones.ext (iso.refl _) (by tidy))

instance : reflects_limits (forget : under X ⥤ C) :=
{ reflects_limits_of_shape := λ J 𝒥,
  { reflects_limit := λ F,
    by constructor; exactI λ t ht,
    { lift := λ s, hom_mk (ht.lift (forget.map_cone s))
        begin
          apply ht.hom_ext, intro j,
          rw [category.assoc, ht.fac],
          transitivity (F.obj j).hom,
          exact w (s.π.app j),
          exact (w (t.π.app j)).symm,
        end,
      fac' := begin
        intros s j, ext, exact ht.fac (forget.map_cone s) j
      end,
      uniq' :=
      begin
        intros s m w,
        ext1 j,
        exact ht.uniq (forget.map_cone s) m.right (λ j, congr_arg comma_morphism.right (w j))
      end } } }

instance has_limit {F : J ⥤ under X} [has_limit (F ⋙ forget)] : has_limit F :=
{ cone := limit F,
  is_limit := reflects_limit.reflects (forget_limit_is_limit F) }

instance has_limits_of_shape [has_limits_of_shape J C] :
  has_limits_of_shape J (under X) :=
{ has_limit := λ F, by apply_instance }

instance has_limits [has_limits C] : has_limits (under X) :=
{ has_limits_of_shape := λ J 𝒥, by resetI; apply_instance }

instance forget_preserves_limits [has_limits C] {X : C} :
  preserves_limits (forget : under X ⥤ C) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by exactI
    preserves_limit_of_preserves_limit_cone (limit.is_limit F) (forget_limit_is_limit F) } }

end category_theory.under
