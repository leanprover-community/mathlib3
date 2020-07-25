/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers, Thomas Read. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers, Thomas Read
-/

import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.constructions.preserve_binary_products
import category_theory.closed.monoidal
import category_theory.monoidal.of_has_finite_products
import category_theory.adjunction
import category_theory.epi_mono

/-!
# Cartesian closed categories

Given a category with finite products, the cartesian monoidal structure is provided by the local
instance `monoidal_of_has_finite_products`.

We define exponentiable objects to be closed objects with respect to this monoidal structure,
i.e. `(X × -)` is a left adjoint.

We say a category is cartesian closed if every object is exponentiable
(equivalently, that the category equipped with the cartesian monoidal structure is closed monoidal).

Show that exponential forms a difunctor and define the exponential comparison morphisms.

## TODO
Some of the results here are true more generally for closed objects and
for closed monoidal categories, and these could be generalised.
-/
universes v u u₂

namespace category_theory

open category_theory category_theory.category category_theory.limits

local attribute [instance] monoidal_of_has_finite_products

/--
An object `X` is *exponentiable* if `(X × -)` is a left adjoint.
We define this as being `closed` in the cartesian monoidal structure.
-/
abbreviation exponentiable {C : Type u} [category.{v} C] [has_finite_products C] (X : C) :=
closed X

/--
If `X` and `Y` are exponentiable then `X ⨯ Y` is.
This isn't an instance because it's not usually how we want to construct exponentials, we'll usually
prove all objects are exponential uniformly.
-/
def binary_product_exponentiable {C : Type u} [category.{v} C] [has_finite_products C] {X Y : C}
  (hX : exponentiable X) (hY : exponentiable Y) : exponentiable (X ⨯ Y) :=
{ is_adj :=
  begin
    haveI := hX.is_adj,
    haveI := hY.is_adj,
    exact adjunction.left_adjoint_of_nat_iso (monoidal_category.tensor_left_tensor _ _).symm
  end }

/--
The terminal object is always exponentiable.
This isn't an instance because most of the time we'll prove cartesian closed for all objects
at once, rather than just for this one.
-/
def terminal_exponentiable {C : Type u} [category.{v} C] [has_finite_products C] :
  exponentiable ⊤_C :=
unit_closed

/--
A category `C` is cartesian closed if it has finite products and every object is exponentiable.
We define this as `monoidal_closed` with respect to the cartesian monoidal structure.
-/
abbreviation cartesian_closed (C : Type u) [category.{v} C] [has_finite_products C] :=
monoidal_closed C

variables {C : Type u} [category.{v} C] (A B : C) {X X' Y Y' Z : C}

section exp
variables [has_finite_products C] [exponentiable A]

/-- This is (-)^A. -/
def exp : C ⥤ C :=
(@closed.is_adj _ _ _ A _).right

/-- The adjunction between A ⨯ - and (-)^A. -/
def exp.adjunction : prod_functor.obj A ⊣ exp A :=
closed.is_adj.adj

/-- The evaluation natural transformation. -/
def ev : exp A ⋙ prod_functor.obj A ⟶ 𝟭 C :=
closed.is_adj.adj.counit

/-- The coevaluation natural transformation. -/
def coev : 𝟭 C ⟶ prod_functor.obj A ⋙ exp A :=
closed.is_adj.adj.unit

notation A ` ⟹ `:20 B:20 := (exp A).obj B
notation B ` ^^ `:30 A:30 := (exp A).obj B

@[simp, reassoc] lemma ev_coev :
  limits.prod.map (𝟙 A) ((coev A).app B) ≫ (ev A).app (A ⨯ B) = 𝟙 (A ⨯ B) :=
adjunction.left_triangle_components (exp.adjunction A)

@[simp, reassoc] lemma coev_ev : (coev A).app (A⟹B) ≫ (exp A).map ((ev A).app B) = 𝟙 (A⟹B) :=
adjunction.right_triangle_components (exp.adjunction A)

end exp

variables {A}

-- Wrap these in a namespace so we don't clash with the core versions.
namespace cartesian_closed

variables [has_finite_products C] [exponentiable A]

/-- Currying in a cartesian closed category. -/
def curry : (A ⨯ Y ⟶ X) → (Y ⟶ A ⟹ X) :=
(closed.is_adj.adj.hom_equiv _ _).to_fun
/-- Uncurrying in a cartesian closed category. -/
def uncurry : (Y ⟶ A ⟹ X) → (A ⨯ Y ⟶ X) :=
(closed.is_adj.adj.hom_equiv _ _).inv_fun

end cartesian_closed

open cartesian_closed

variables [has_finite_products C] [exponentiable A]

@[reassoc]
lemma curry_natural_left (f : X ⟶ X') (g : A ⨯ X' ⟶ Y) :
  curry (limits.prod.map (𝟙 _) f ≫ g) = f ≫ curry g :=
adjunction.hom_equiv_naturality_left _ _ _

@[reassoc]
lemma curry_natural_right (f : A ⨯ X ⟶ Y) (g : Y ⟶ Y') :
  curry (f ≫ g) = curry f ≫ (exp _).map g :=
adjunction.hom_equiv_naturality_right _ _ _

@[reassoc]
lemma uncurry_natural_right  (f : X ⟶ A⟹Y) (g : Y ⟶ Y') :
  uncurry (f ≫ (exp _).map g) = uncurry f ≫ g :=
adjunction.hom_equiv_naturality_right_symm _ _ _

@[reassoc]
lemma uncurry_natural_left  (f : X ⟶ X') (g : X' ⟶ A⟹Y) :
  uncurry (f ≫ g) = limits.prod.map (𝟙 _) f ≫ uncurry g :=
adjunction.hom_equiv_naturality_left_symm _ _ _

@[simp]
lemma uncurry_curry (f : A ⨯ X ⟶ Y) : uncurry (curry f) = f :=
(closed.is_adj.adj.hom_equiv _ _).left_inv f

@[simp]
lemma curry_uncurry (f : X ⟶ A⟹Y) : curry (uncurry f) = f :=
(closed.is_adj.adj.hom_equiv _ _).right_inv f

lemma curry_eq_iff (f : A ⨯ Y ⟶ X) (g : Y ⟶ A ⟹ X) :
  curry f = g ↔ f = uncurry g :=
adjunction.hom_equiv_apply_eq _ f g

lemma eq_curry_iff (f : A ⨯ Y ⟶ X) (g : Y ⟶ A ⟹ X) :
  g = curry f ↔ uncurry g = f :=
adjunction.eq_hom_equiv_apply _ f g

-- I don't think these two should be simp.
lemma uncurry_eq (g : Y ⟶ A ⟹ X) : uncurry g = limits.prod.map (𝟙 A) g ≫ (ev A).app X :=
adjunction.hom_equiv_counit _

lemma curry_eq (g : A ⨯ Y ⟶ X) : curry g = (coev A).app Y ≫ (exp A).map g :=
adjunction.hom_equiv_unit _

lemma uncurry_id_eq_ev (A X : C) [exponentiable A] : uncurry (𝟙 (A ⟹ X)) = (ev A).app X :=
by rw [uncurry_eq, prod_map_id_id, id_comp]

lemma curry_id_eq_coev (A X : C) [exponentiable A] : curry (𝟙 _) = (coev A).app X :=
by { rw [curry_eq, (exp A).map_id (A ⨯ _)], apply comp_id }

lemma curry_injective : function.injective (curry : (A ⨯ Y ⟶ X) → (Y ⟶ A ⟹ X)) :=
(closed.is_adj.adj.hom_equiv _ _).injective

lemma uncurry_injective : function.injective (uncurry : (Y ⟶ A ⟹ X) → (A ⨯ Y ⟶ X)) :=
(closed.is_adj.adj.hom_equiv _ _).symm.injective

/--
Show that the exponential of the terminal object is isomorphic to itself, i.e. `X^1 ≅ X`.

The typeclass argument is explicit: any instance can be used.
-/
def exp_terminal_iso_self [exponentiable ⊤_C] : (⊤_C ⟹ X) ≅ X :=
yoneda.ext (⊤_ C ⟹ X) X
  (λ Y f, (prod.left_unitor Y).inv ≫ uncurry f)
  (λ Y f, curry ((prod.left_unitor Y).hom ≫ f))
  (λ Z g, by rw [curry_eq_iff, iso.hom_inv_id_assoc] )
  (λ Z g, by simp)
  (λ Z W f g, by rw [uncurry_natural_left, prod_left_unitor_inv_naturality_assoc f] )

/-- The internal element which points at the given morphism. -/
def internalize_hom (f : A ⟶ Y) : ⊤_C ⟶ (A ⟹ Y) :=
curry (limits.prod.fst ≫ f)

section pre

variables {B}

/-- Pre-compose an internal hom with an external hom. -/
def pre (X : C) (f : B ⟶ A) [exponentiable B] : (A⟹X) ⟶ B⟹X :=
curry (limits.prod.map f (𝟙 _) ≫ (ev A).app X)

lemma pre_id (A X : C) [exponentiable A] : pre X (𝟙 A) = 𝟙 (A⟹X) :=
by { rw [pre, prod_map_id_id, id_comp, ← uncurry_id_eq_ev], simp }

-- There's probably a better proof of this somehow
/-- Precomposition is contrafunctorial. -/
lemma pre_map [exponentiable B] {D : C} [exponentiable D] (f : A ⟶ B) (g : B ⟶ D) :
  pre X (f ≫ g) = pre X g ≫ pre X f :=
begin
  rw [pre, curry_eq_iff, pre, pre, uncurry_natural_left, uncurry_curry, prod_map_map_assoc,
      prod_map_comp_id, assoc, ← uncurry_id_eq_ev, ← uncurry_id_eq_ev, ← uncurry_natural_left,
      curry_natural_right, comp_id, uncurry_natural_right, uncurry_curry],
end

end pre

lemma pre_post_comm [cartesian_closed C] {A B : C} {X Y : Cᵒᵖ} (f : A ⟶ B) (g : X ⟶ Y) :
  pre A g.unop ≫ (exp Y.unop).map f = (exp X.unop).map f ≫ pre B g.unop :=
begin
  erw [← curry_natural_left, eq_curry_iff, uncurry_natural_right, uncurry_curry, prod_map_map_assoc,
       (ev _).naturality, assoc], refl
end

/-- The internal hom functor given by the cartesian closed structure. -/
def internal_hom [cartesian_closed C] : C ⥤ Cᵒᵖ ⥤ C :=
{ obj := λ X,
  { obj := λ Y, Y.unop ⟹ X,
    map := λ Y Y' f, pre _ f.unop,
    map_id' := λ Y, pre_id _ _,
    map_comp' := λ Y Y' Y'' f g, pre_map _ _ },
  map := λ A B f, { app := λ X, (exp X.unop).map f, naturality' := λ X Y g, pre_post_comm _ _ },
  map_id' := λ X, by { ext, apply functor.map_id },
  map_comp' := λ X Y Z f g, by { ext, apply functor.map_comp } }

/-- If an initial object `0` exists in a CCC, then `A ⨯ 0 ≅ 0`. -/
@[simps]
def zero_mul [has_initial C] : A ⨯ ⊥_ C ≅ ⊥_ C :=
{ hom := limits.prod.snd,
  inv := default (⊥_ C ⟶ A ⨯ ⊥_ C),
  hom_inv_id' :=
  begin
    have: (limits.prod.snd : A ⨯ ⊥_ C ⟶ ⊥_ C) = uncurry (default _),
      rw ← curry_eq_iff,
      apply subsingleton.elim,
    rw [this, ← uncurry_natural_right, ← eq_curry_iff],
    apply subsingleton.elim
  end,
  }

/-- If an initial object `0` exists in a CCC, then `0 ⨯ A ≅ 0`. -/
def mul_zero [has_initial C] : ⊥_ C ⨯ A ≅ ⊥_ C :=
limits.prod.braiding _ _ ≪≫ zero_mul

/-- If an initial object `0` exists in a CCC then `0^B ≅ 1` for any `B`. -/
def pow_zero [has_initial C] [cartesian_closed C] : ⊥_C ⟹ B ≅ ⊤_ C :=
{ hom := default _,
  inv := curry (mul_zero.hom ≫ default (⊥_ C ⟶ B)),
  hom_inv_id' :=
  begin
    rw [← curry_natural_left, curry_eq_iff, ← cancel_epi mul_zero.inv],
    { apply subsingleton.elim },
    { apply_instance },
    { apply_instance }
  end }

-- TODO: Generalise the below to its commutated variants.
-- TODO: Define a distributive category, so that zero_mul and friends can be derived from this.
/-- In a CCC with binary coproducts, the distribution morphism is an isomorphism. -/
def prod_coprod_distrib [has_binary_coproducts C] [cartesian_closed C] (X Y Z : C) :
  (Z ⨯ X) ⨿ (Z ⨯ Y) ≅ Z ⨯ (X ⨿ Y) :=
{ hom := coprod.desc (limits.prod.map (𝟙 _) coprod.inl) (limits.prod.map (𝟙 _) coprod.inr),
  inv := uncurry (coprod.desc (curry coprod.inl) (curry coprod.inr)),
  hom_inv_id' :=
  begin
    apply coprod.hom_ext,
    rw [coprod.inl_desc_assoc, comp_id, ←uncurry_natural_left, coprod.inl_desc, uncurry_curry],
    rw [coprod.inr_desc_assoc, comp_id, ←uncurry_natural_left, coprod.inr_desc, uncurry_curry],
  end,
  inv_hom_id' :=
  begin
    rw [← uncurry_natural_right, ←eq_curry_iff],
    apply coprod.hom_ext,
    rw [coprod.inl_desc_assoc, ←curry_natural_right, coprod.inl_desc, ←curry_natural_left, comp_id],
    rw [coprod.inr_desc_assoc, ←curry_natural_right, coprod.inr_desc, ←curry_natural_left, comp_id],
  end }

/--
If an initial object `0` exists in a CCC then it is a strict initial object,
i.e. any morphism to `0` is an iso.
-/
instance strict_initial [has_initial C] {f : A ⟶ ⊥_ C} : is_iso f :=
begin
  haveI : mono (limits.prod.lift (𝟙 A) f ≫ zero_mul.hom) := mono_comp _ _,
  rw [zero_mul_hom, prod.lift_snd] at _inst,
  haveI: split_epi f := ⟨default _, subsingleton.elim _ _⟩,
  apply is_iso_of_mono_of_split_epi
end

/-- If an initial object `0` exists in a CCC then every morphism from it is monic. -/
instance initial_mono (B : C) [has_initial C] [cartesian_closed C] : mono (initial.to B) :=
⟨λ B g h _, eq_of_inv_eq_inv (subsingleton.elim (inv g) (inv h))⟩

variables {D : Type u₂} [category.{v} D]
section functor

variables [has_finite_products D]

/--
Transport the property of being cartesian closed across an equivalence of categories.

Note we didn't require any coherence between the choice of finite products here, since we transport
along the `prod_comparison` isomorphism.
-/
def cartesian_closed_of_equiv (e : C ≌ D) [h : cartesian_closed C] : cartesian_closed D :=
{ closed := λ X,
  { is_adj :=
    begin
      haveI q : exponentiable (e.inverse.obj X) := infer_instance,
      have : is_left_adjoint (prod_functor.obj (e.inverse.obj X)) := q.is_adj,
      have : e.functor ⋙ prod_functor.obj X ⋙ e.inverse ≅ prod_functor.obj (e.inverse.obj X),
      apply nat_iso.of_components _ _,
      intro Y,
      { apply as_iso (prod_comparison e.inverse X (e.functor.obj Y)) ≪≫ _,
        exact ⟨limits.prod.map (𝟙 _) (e.unit_inv.app _),
              limits.prod.map (𝟙 _) (e.unit.app _),
              by simpa [←prod_map_id_comp, prod_map_id_id],
              by simpa [←prod_map_id_comp, prod_map_id_id]⟩, },
      { intros Y Z g,
        simp only [prod_comparison, inv_prod_comparison_map_fst, inv_prod_comparison_map_snd,
          prod.lift_map, functor.comp_map, prod_functor_obj_map, assoc, comp_id,
          iso.trans_hom, as_iso_hom],
        apply prod.hom_ext,
        { rw [assoc, prod.lift_fst, prod.lift_fst, ←functor.map_comp,
            limits.prod.map_fst, comp_id], },
        { rw [assoc, prod.lift_snd, prod.lift_snd, ←functor.map_comp_assoc, limits.prod.map_snd],
          simp only [iso.hom_inv_id_app, assoc, equivalence.inv_fun_map,
            functor.map_comp, comp_id],
          erw comp_id, }, },
      { have : is_left_adjoint (e.functor ⋙ prod_functor.obj X ⋙ e.inverse) :=
          by exactI adjunction.left_adjoint_of_nat_iso this.symm,
        have : is_left_adjoint (e.inverse ⋙ e.functor ⋙ prod_functor.obj X ⋙ e.inverse) :=
          by exactI adjunction.left_adjoint_of_comp e.inverse _,
        have : (e.inverse ⋙ e.functor ⋙ prod_functor.obj X ⋙ e.inverse) ⋙ e.functor ≅
          prod_functor.obj X,
        { apply iso_whisker_right e.counit_iso (prod_functor.obj X ⋙ e.inverse ⋙ e.functor) ≪≫ _,
          change prod_functor.obj X ⋙ e.inverse ⋙ e.functor ≅ prod_functor.obj X,
          apply iso_whisker_left (prod_functor.obj X) e.counit_iso, },
        resetI,
        apply adjunction.left_adjoint_of_nat_iso this },
    end } }

variables [cartesian_closed C] [cartesian_closed D]
variables (F : C ⥤ D) [preserves_limits_of_shape (discrete walking_pair) F]

/--
The exponential comparison map.
`F` is a cartesian closed functor if this is an iso for all `A,B`.
-/
def exp_comparison (A B : C) :
  F.obj (A ⟹ B) ⟶ F.obj A ⟹ F.obj B :=
curry (inv (prod_comparison F A _) ≫ F.map ((ev _).app _))

/-- The exponential comparison map is natural in its left argument. -/
lemma exp_comparison_natural_left (A A' B : C) (f : A' ⟶ A) :
  exp_comparison F A B ≫ pre (F.obj B) (F.map f) = F.map (pre B f) ≫ exp_comparison F A' B :=
begin
  rw [exp_comparison, exp_comparison, ← curry_natural_left, eq_curry_iff, uncurry_natural_left,
       pre, uncurry_curry, prod_map_map_assoc, curry_eq, prod_map_id_comp, assoc],
  erw [(ev _).naturality, ev_coev_assoc, ← F.map_id, ← prod_comparison_inv_natural_assoc,
       ← F.map_id, ← prod_comparison_inv_natural_assoc, ← F.map_comp, ← F.map_comp, pre, curry_eq,
       prod_map_id_comp, assoc, (ev _).naturality, ev_coev_assoc], refl,
end

/-- The exponential comparison map is natural in its right argument. -/
lemma exp_comparison_natural_right (A B B' : C) (f : B ⟶ B') :
  exp_comparison F A B ≫ (exp (F.obj A)).map (F.map f) =
    F.map ((exp A).map f) ≫ exp_comparison F A B' :=
by
  erw [exp_comparison, ← curry_natural_right, curry_eq_iff, exp_comparison, uncurry_natural_left,
       uncurry_curry, assoc, ← F.map_comp, ← (ev _).naturality, F.map_comp,
       prod_comparison_inv_natural_assoc, F.map_id]

-- TODO: If F has a left adjoint L, then F is cartesian closed if and only if
-- L (B ⨯ F A) ⟶ L B ⨯ L F A ⟶ L B ⨯ A
-- is an iso for all A ∈ D, B ∈ C.
-- Corollary: If F has a left adjoint L which preserves finite products, F is cartesian closed iff
-- F is full and faithful.

end functor

end category_theory
