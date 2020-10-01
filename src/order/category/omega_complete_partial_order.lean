/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/


import order.omega_complete_partial_order
import order.category.Preorder
import category_theory.closed.cartesian
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.types
import category_theory.currying
import tactic.find_unused

/-!
# Category of types with a omega complete partial order

In this file, we bundle the class `omega_complete_partial_order` into a
concrete category and prove that continuous functions also form
a `omega_complete_partial_order`.

## Main definitions

 * `ωCPO`
   * an instance of `category` and `concrete_category`
   * an instance of `has_binary_products`
   * an instance of `monoidal_category` (based of binary products)
   * an instance of `closed`
   * an instance of `monoidal_closed`

In total, ωCPOs form a cartesian closed category.

 -/

open category_theory

universes u v w

/-- The category of types with a omega complete partial order. -/
def ωCPO := bundled omega_complete_partial_order

namespace ωCPO

open omega_complete_partial_order

instance : bundled_hom @continuous_hom :=
{ to_fun := @continuous_hom.to_fun,
  id := @continuous_hom.id,
  comp := @continuous_hom.comp,
  hom_ext := @continuous_hom.coe_inj }

attribute [derive [has_coe_to_sort, large_category, concrete_category]] ωCPO

/-- Construct a bundled ωCPO from the underlying type and typeclass. -/
def of (α : Type*) [omega_complete_partial_order α] : ωCPO := bundled.of α

instance : inhabited ωCPO := ⟨of punit⟩

instance (α : ωCPO) : omega_complete_partial_order α := α.str

open category_theory.limits

instance : has_terminal ωCPO.{u} :=
{ has_limit := λ F,
  { exists_limit :=
    ⟨ { cone :=
        { X := of punit,
          π := { app := λ X, pempty.elim X } },
        is_limit :=
        { lift := λ s, ⟨λ x, punit.star,λ x y h, le_refl _,λ c, punit_eq _ _⟩ } } ⟩ } }

open omega_complete_partial_order category_theory category_theory.limits

/--
(internal implementation) the limit cone of the binary product in a ωCPO.
It is implemented as the product type -/
def product_cone (X Y : ωCPO.{u}) : cone (pair X Y) :=
binary_fan.mk
  (continuous_hom.of_mono preorder_hom.prod.fst (λ c, rfl) : ωCPO.of (X × Y) ⟶ _)
  (continuous_hom.of_mono preorder_hom.prod.snd (λ c, rfl))

/-- (internal implementation) the fact that the proposed product cone is the limit -/
def product_cone_is_limit (X Y : ωCPO.{u}) : is_limit (product_cone X Y) :=
{ lift := λ s, ⟨λ x, (s.π.app walking_pair.left x, s.π.app walking_pair.right x),
               λ x y h, ⟨(s.π.app walking_pair.left).monotone h, (s.π.app walking_pair.right).monotone h⟩,
               λ c, by ext; dsimp; rw continuous_hom.continuous; refl⟩,
  fac' := by rintros s ⟨ ⟩; ext; refl,
  uniq' := by { dsimp, intros, ext; dsimp; delta binary_fan.fst binary_fan.snd; rw ← w; simp only [continuous_hom.continuous_hom.coe_fn_mk, binary_fan.π_app_left, binary_fan.π_app_right]; refl, } }

instance {X Y : ωCPO} : has_limit (pair X Y) :=
has_limit.mk ⟨_, product_cone_is_limit X Y⟩

instance : has_binary_products ωCPO.{u} :=
has_binary_products_of_has_limit_pair _

/-- Constructor for values in binary products of ωCPOs, as an arrow from a unit type -/
noncomputable def prod_lift {X Y : ωCPO.{u}} (x : X) (y : Y) : ωCPO.of punit.{u + 1} ⟶ X ⨯ Y :=
limits.prod.lift (continuous_hom.const x) (continuous_hom.const y)

/-- Constructor for values in binary products of ωCPOs -/
noncomputable def prod.mk {X Y : ωCPO.{u}} (x : X) (y : Y) : ↥(X ⨯ Y) :=
prod_lift x y punit.star

/-- Isomorphism between binary products of ωCPOs and product types -/
noncomputable def of_prod_iso (X Y : ωCPO.{u}) : X ⨯ Y ≅ ωCPO.of (X × Y) :=
limits.is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (product_cone_is_limit X Y)

@[simp]
lemma prod_lift_binary_fst {X Y : ωCPO.{u}} (x : X) (y : Y) :
  prod_lift.{u} x y ≫ binary_fan.fst _ = continuous_hom.const x :=
prod.lift_fst _ _

@[simp]
lemma prod_lift_binary_snd {X Y : ωCPO.{u}} (x : X) (y : Y) :
  prod_lift.{u} x y ≫ binary_fan.snd _ = continuous_hom.const y :=
prod.lift_snd _ _

@[simp]
lemma prod_lift_prod_fst {X Y : ωCPO.{u}} (x : X) (y : Y) :
  prod_lift.{u} x y ≫ limits.prod.fst = continuous_hom.const x :=
prod.lift_fst _ _

@[simp]
lemma prod_lift_prod_snd {X Y : ωCPO.{u}} (x : X) (y : Y) :
  prod_lift.{u} x y ≫ limits.prod.snd = continuous_hom.const y :=
prod.lift_snd _ _

lemma of_prod_iso_prod_fst {X Y : ωCPO.{u}} :
  (ωCPO.of_prod_iso X Y).hom ≫ continuous_hom.prod.fst = limits.prod.fst :=
begin
  rw [ωCPO.of_prod_iso, ← iso.eq_inv_comp],
  erw limits.is_limit.cone_point_unique_up_to_iso_inv_comp,
  refl,
end

lemma of_prod_iso_prod_snd {X Y : ωCPO.{u}} :
  (ωCPO.of_prod_iso X Y).hom ≫ continuous_hom.prod.snd = limits.prod.snd :=
begin
  rw [ωCPO.of_prod_iso, ← iso.eq_inv_comp],
  erw limits.is_limit.cone_point_unique_up_to_iso_inv_comp,
  refl,
end

@[main_declaration, simp]
lemma prod.mk_le {X Y : ωCPO.{u}} (x x' : X) (y y' : Y) :
  prod.mk x y ≤ prod.mk x' y' ↔ x ≤ x' ∧ y ≤ y' :=
begin
  let i : X ⨯ Y ≅ ωCPO.of (X × Y) :=
    ωCPO.of_prod_iso _ _,
  split,
  { intro h,
    have : i.hom (prod.mk x y) ≤ i.hom (prod.mk x' y'),
    { exact i.hom.monotone h },
    have ha := ((product_cone X Y).π.app walking_pair.left).monotone this,
    have hb := ((product_cone X Y).π.app walking_pair.right).monotone this,
    simp only [continuous_hom.const_apply, prod_lift_binary_fst, prod_lift_binary_snd, ← coe_comp, is_limit.cone_point_unique_up_to_iso_hom_comp, binary_fan.π_app_left, prod.mk, category.assoc, ωCPO.of_prod_iso, i] at ha hb,
    simp [ha, hb], },
  { rintro ⟨h₀, h₁⟩,
    suffices : i.hom (prod.mk x y) ≤ i.hom (prod.mk x' y'),
    { replace this := i.inv.monotone this,
      simpa using this },
    change (prod_lift x  y  ≫ i.hom ≫ continuous_hom.prod.fst) punit.star ≤
           (prod_lift x' y' ≫ i.hom ≫ continuous_hom.prod.fst) punit.star   ∧
           (prod_lift x  y  ≫ i.hom ≫ continuous_hom.prod.snd) punit.star ≤
           (prod_lift x' y' ≫ i.hom ≫ continuous_hom.prod.snd) punit.star,
    simp only [i, ωCPO.of_prod_iso_prod_fst, ωCPO.of_prod_iso_prod_snd, prod_lift_prod_fst, prod_lift_prod_snd, continuous_hom.const_apply, *],
    exact ⟨trivial, trivial⟩ }
end

@[simp]
lemma prod.fst_map' {X X' Y Y' : ωCPO.{u}} (f : X ⟶ Y) (g : X' ⟶ Y') (x : X ⨯ X') :
  (limits.prod.fst : Y ⨯ Y' ⟶ Y) (limits.prod.map f g x) = f ((limits.prod.fst : X ⨯ X' ⟶ X) x) :=
begin
  change (limits.prod.map f g ≫ limits.prod.fst) x = (limits.prod.fst ≫ f) x,
  rw limits.prod.map_fst
end

@[simp]
lemma prod.snd_map' {X X' Y Y' : ωCPO.{u}} (f : X ⟶ Y) (g : X' ⟶ Y') (x : X ⨯ X') :
  (limits.prod.snd : Y ⨯ Y' ⟶ Y') (limits.prod.map f g x) = g ((limits.prod.snd : X ⨯ X' ⟶ X') x) :=
begin
  change (limits.prod.map f g ≫ limits.prod.snd) x = (limits.prod.snd ≫ g) x,
  rw limits.prod.map_snd
end

/-- Convert a binary product into a product type -/
@[simps]
noncomputable def prod.elim {X Y : ωCPO.{u}} : ↥(X ⨯ Y) →𝒄 X × Y :=
{ to_fun := λ a, ((limits.prod.fst : (X ⨯ Y) ⟶ X) a, (limits.prod.snd : (X ⨯ Y) ⟶ Y) a),
  monotone' := λ a b h, ⟨continuous_hom.monotone _ h, continuous_hom.monotone _ h⟩,
  cont := λ c, by ext; dsimp; rw continuous_hom.continuous; refl
 }

noncomputable instance : monoidal_category ωCPO :=
monoidal_of_has_finite_products _

noncomputable instance : symmetric_category ωCPO :=
symmetric_of_has_finite_products _

/-- Definition of `obj` for `hom` functor. -/
def hom_obj (X Y : ωCPO) : ωCPO := of (X ⟶ Y)

/-- Definition of `map` for `hom` functor. -/
@[simps]
def hom_map {X X' : ωCPO.{u}} {Y Y' : ωCPO.{u}}
  (f : X' ⟶ X) (g : Y ⟶ Y') :
  of (X ⟶ Y) ⟶ of (X' ⟶ Y') :=
{ to_fun := λ h, f ≫ h ≫ g,
  monotone' := λ x y h a, g.monotone (h _),
  cont := λ c, by ext; simp; rw g.continuous; refl }

/-- `hom` functor, mapping arrows in `ωCPO` to an object in `ωCPO` -/
@[pp_nodot, simps obj]
def hom : ωCPO.{u}ᵒᵖ × ωCPO.{u} ⥤ ωCPO.{u} :=
{ obj := λ x, hom_obj x.1.unop x.2,
  map := λ X Y f, hom_map f.1.unop f.2 }

@[simp]
lemma hom_map_coe_to_fun {X₀ X₁ : ωCPO.{u}ᵒᵖ} {Y₀ Y₁ : ωCPO.{u}} (x : hom.obj (X₀, Y₀))
  (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) : hom.map ((f, g) : (X₀, Y₀) ⟶ (X₁, Y₁)) x = f.unop ≫ x ≫ g := rfl

/--
Evaluation morphisms for arrow objects
-/
@[pp_nodot, simps {rhs_md := semireducible}]
noncomputable def eval (X Y : ωCPO.{u}) : (ωCPO.of (X ⟶ Y) ⨯ X : ωCPO) ⟶ Y :=
continuous_hom.of_mono (continuous_hom.prod.apply.comp prod.elim.to_preorder_hom)
 (λ c, by simp [continuous_hom.ωSup_apply, ← chain.map_comp, ← continuous_hom.ωSup_apply, ← prod.elim.continuous])

open opposite (op)

@[reassoc]
lemma eval_nat (X Y Y' : ωCPO) (f : Y ⟶ Y') :
  eval X Y ≫ f = limits.prod.map (hom.map (𝟙 _, f) : hom.obj (op X, Y) ⟶ hom.obj (op X, Y')) (𝟙 _) ≫ eval X Y' :=
by ext; simp

/--
Auxiliary definition for exponentiation in `ωCPO`
-/
@[pp_nodot, simps]
def exp₀ {X Y : Type u}
  [omega_complete_partial_order X]
  [omega_complete_partial_order Y]
  {Z : ωCPO.{u}} (f : ωCPO.of (X × Y) ⟶ Z) : of X ⟶ of (of Y ⟶ Z) :=
{ to_fun := λ x,
  { to_fun := λ y, f (x, y),
    monotone' := λ a b h, f.monotone ⟨le_refl _, h⟩,
    cont :=
    begin
      intro, dsimp, rw ← continuous_hom.ωSup_const x,
      transitivity f (ωSup $ chain.zip (preorder_hom.const _ x) c),
      { congr, ext; refl },
      { rw continuous_hom.continuous,
        congr' 1, ext, dsimp, rw continuous_hom.ωSup_const x }
    end},
  monotone' := λ a b h y, f.monotone ⟨h, le_refl _⟩,
  cont :=
  begin
    intro, ext, dsimp [continuous_hom.ωSup],
    transitivity f (ωSup $ c.zip (preorder_hom.const _ x)),
    { congr' 1, ext; simp [continuous_hom.ωSup_const], },
    { rw continuous_hom.continuous, refl }
  end }

/--
Exponentiation in `ωCPO`
-/
@[pp_nodot, simps {rhs_md := semireducible}]
noncomputable def exp {X Y Z : ωCPO.{u}} (f : (X ⨯ Y) ⟶ Z) : X ⟶ of (Y ⟶ Z) :=
exp₀ (prod.lift continuous_hom.prod.fst continuous_hom.prod.snd ≫ f)

/--
Exponentiation in `ωCPO` with arguments flipped
-/
@[pp_nodot, simps {rhs_md := semireducible}]
noncomputable def exp' {X Y Z : ωCPO.{u}} (f : Y ⨯ X ⟶ Z) : X ⟶ of (Y ⟶ Z) :=
exp.{u} $ (β_ _ _).hom ≫ f

@[simp, reassoc]
lemma exp₀_nat_left
 {X X' Y Z : ωCPO.{u}}
  (f : of (X × Y) ⟶ Z) (g : X' ⟶ X) :
  g ≫ exp₀ f = exp₀ (@category_struct.comp _ _ (of $ X' × Y) (of $ X × Y) Z (continuous_hom.prod.map.{u u u u} g (@continuous_hom.id.{u} Y _)) f) :=
by  { ext, simp }

@[simp, reassoc]
lemma exp_nat_left {X X' Y Z : ωCPO} (f : X ⨯ Y ⟶ Z) (g : X' ⟶ X) :
  g ≫ exp f = exp (limits.prod.map g (𝟙 _) ≫ f) :=
begin
  rw [exp, exp, prod.lift_map_assoc],
  rw [exp₀_nat_left, ← prod.lift_comp_comp_assoc],
  dsimp [(≫), category_theory.bundled_hom.comp],
  erw [continuous_hom.prod.map_fst, continuous_hom.prod.map_snd],
end

@[reassoc]
lemma exp_nat_right {X Y Z Z' : ωCPO} (f : X ⨯ Y ⟶ Z) (g : Z ⟶ Z') :
  exp f ≫ (hom.map (𝟙 (opposite.op Y), g) : hom.obj (opposite.op Y, Z) ⟶ hom.obj (opposite.op Y, Z')) = exp (f ≫ g) :=
by ext; simp

lemma hcongr_fun {α : Sort*} {β : Sort*} [omega_complete_partial_order α] [omega_complete_partial_order β] {f g : α →𝒄 β} (h : f = g) (a : α) : f a = g a :=
congr_arg _ h

@[simp]
lemma limits.prod.fst_mk {X Y : ωCPO} (x : X) (y : Y) : (limits.prod.fst : X ⨯ Y ⟶ X) (prod.mk x y) = x :=
begin
  simp only [prod.mk, prod_lift, ← coe_comp, limits.prod.lift_fst],
  refl,
end

@[simp]
lemma limits.prod.snd_mk {X Y : ωCPO} (x : X) (y : Y) : (limits.prod.snd : X ⨯ Y ⟶ Y) (prod.mk x y) = y :=
begin
  simp only [prod.mk, prod_lift, ← coe_comp, limits.prod.lift_snd],
  refl,
end

@[simp]
lemma limits.prod.lift_coe_fn {X Y Z : ωCPO} (f : X ⟶ Y) (g : X ⟶ Z) (x : X) :
  limits.prod.lift f g x = prod.mk (f x) (g x) :=
begin
  suffices : (continuous_hom.const x ≫ limits.prod.lift f g : of punit ⟶ (Y ⨯ Z)) =
             limits.prod.lift (continuous_hom.const x ≫ f) (continuous_hom.const x ≫ g),
  { replace this := hcongr_fun this punit.star,
    simpa only [-prod.lift_comp_comp] using this },
  rw prod.lift_comp_comp
end

@[simp, reassoc]
lemma exp_eval {X Y Z : ωCPO} (f : X ⨯ Y ⟶ Z) : limits.prod.map (exp f) (𝟙 _) ≫ eval _ _ = f :=
by ext; simp [exp]; rw [← limits.prod.lift_coe_fn, prod_lift_fst_snd]; simp

noncomputable instance {X : ωCPO.{u}} : closed X :=
{ is_adj :=
  { right := (curry.{u u}.obj hom).obj (op X),
    adj :=
    { hom_equiv := λ Y Z,
      { to_fun := λ f, exp'.{u} f,
        inv_fun := λ f, (β_ _ _).hom ≫ limits.prod.map f (𝟙 _) ≫ eval.{u} X _,
        left_inv := λ f, by simp [exp'],
        right_inv := λ f, by ext; simp },
        unit := { app := λ Y, exp (β_ _ _).hom,
                  naturality' := by { intros Y Z f, dsimp, simp [exp_nat_right, limits.prod.lift_map, ← limits.prod.lift_comp_comp, limits.prod.map_fst, limits.prod.map_snd], } },
      counit := { app := λ Y, (β_ _ _).hom ≫ eval X _,
                  naturality' := by { intros Y Z f, dsimp, simp [eval_nat, limits.prod.lift_map_assoc, ← limits.prod.lift_comp_comp_assoc], dsimp, rw category.comp_id } },
      hom_equiv_unit' := λ Y Z f, by ext; refl,
      hom_equiv_counit' := λ Y Z f, by ext; simp } } }

@[main_declaration]
noncomputable instance : monoidal_closed ωCPO.{u} :=
⟨ λ X, by apply_instance ⟩

end ωCPO
