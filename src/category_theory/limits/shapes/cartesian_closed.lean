/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers, Thomas Read. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers, Thomas Read
-/

import category_theory.limits.shapes.binary_products
import category_theory.adjunction
import category_theory.epi_mono
import tactic

/-!
# Cartesian closed categories

Define exponentiable objects and cartesian closed categories.
Show that exponential forms a difunctor.
Define the exponential comparison morphisms.
-/
universes v u u₂

namespace category_theory

open limits category

class exponentiable {C : Type u} [category.{v} C] [bp : has_finite_products.{v} C] (X : C) :=
(is_adj : is_left_adjoint (prod_functor.obj X))

def binary_product_exponentiable {C : Type u} [category.{v} C] [bp : has_finite_products.{v} C] {X Y : C}
  (hX : exponentiable X) (hY : exponentiable Y) : exponentiable (X ⨯ Y) :=
{ is_adj :=
  { right := hX.is_adj.right ⋙ hY.is_adj.right,
    adj := adjunction.of_nat_iso_left (adjunction.comp _ _ hY.is_adj.adj hX.is_adj.adj) (prod_functor_left_comp _ _).symm } }

class is_cartesian_closed (C : Type u) [category.{v} C] [has_finite_products.{v} C] :=
(cart_closed : Π (X : C), exponentiable X)

attribute [instance] is_cartesian_closed.cart_closed

variables {C : Type u} [𝒞 : category.{v} C] (A B : C) {X X' Y Y' Z : C}
include 𝒞

section exp
variables [has_finite_products.{v} C] [exponentiable A]

/-- This is (-)^A -/
def exp.functor (A : C) [exponentiable A] : C ⥤ C :=
(@exponentiable.is_adj _ _ _ A _).right

def exp.adjunction (A : C) [exponentiable A] : prod_functor.obj A ⊣ exp.functor A :=
exponentiable.is_adj.adj

def ev.nat_trans (A : C) [exponentiable A] : exp.functor A ⋙ prod_functor.obj A ⟶ 𝟭 C :=
exponentiable.is_adj.adj.counit

def coev.nat_trans (A : C) [exponentiable A] : 𝟭 C ⟶ prod_functor.obj A ⋙ exp.functor A :=
exponentiable.is_adj.adj.unit

/-- `B ^ A` or `A ⟹ B` -/
def exp (A : C) (B : C) [exponentiable A] : C := (exp.functor A).obj B

infixl `⟹`:20 := exp
infixr `^^`:30 := pow

-- [todo] rename as 'post compose' or similar?
def post (A : C) [exponentiable A] {X Y : C} (f : X ⟶ Y) : A⟹X ⟶ A⟹Y :=
(exp.functor A).map f

lemma post.map_comp {f : X ⟶ Y} {g : Y ⟶ Z} : post A (f ≫ g) = post A f ≫ post A g :=
(exp.functor A).map_comp _ _

def ev : A ⨯ (A⟹B) ⟶ B :=
(ev.nat_trans A).app B

def coev : B ⟶ A⟹(A⨯B) :=
(coev.nat_trans A).app B

@[simp, reassoc] lemma ev_coev : limits.prod.map (𝟙 A) (coev A B) ≫ ev A (A ⨯ B) = 𝟙 (A ⨯ B) :=
adjunction.left_triangle_components (exp.adjunction A)

@[simp, reassoc] lemma coev_ev : coev A (A⟹B) ≫ post A (ev A B) = 𝟙 (A⟹B) :=
adjunction.right_triangle_components (exp.adjunction A)

@[simp, reassoc, priority 10]
lemma coev_nat (f : X ⟶ Y) : f ≫ coev A Y = coev A X ≫ post A (limits.prod.map (𝟙 A) f) :=
(coev.nat_trans A).naturality f

@[simp, reassoc, priority 10]
lemma ev_nat (f : X ⟶ Y) : limits.prod.map (𝟙 A) (post _ f) ≫ ev A Y = ev A X ≫ f :=
(ev.nat_trans A).naturality f

end exp

variables {A}

-- Wrap these in a namespace so we don't clash with the core versions.
namespace cart_closed

variables [has_finite_products.{v} C] [exponentiable A]

def curry : (A ⨯ Y ⟶ X) → (Y ⟶ A ⟹ X) :=
(exponentiable.is_adj.adj.hom_equiv _ _).to_fun
def uncurry : (Y ⟶ A ⟹ X) → (A ⨯ Y ⟶ X) :=
(exponentiable.is_adj.adj.hom_equiv _ _).inv_fun

end cart_closed

open cart_closed

variables [has_finite_products.{v} C] [exponentiable A]

@[reassoc]
lemma curry_natural_left (f : X ⟶ X') (g : A ⨯ X' ⟶ Y) :
  curry (limits.prod.map (𝟙 _) f ≫ g) = f ≫ curry g :=
adjunction.hom_equiv_naturality_left _ _ _

@[reassoc]
lemma curry_natural_right (f : A ⨯ X ⟶ Y) (g : Y ⟶ Y') :
  curry (f ≫ g) = curry f ≫ post _ g :=
adjunction.hom_equiv_naturality_right _ _ _

@[reassoc]
lemma uncurry_natural_right  (f : X ⟶ A⟹Y) (g : Y ⟶ Y') :
  uncurry (f ≫ post A g) = uncurry f ≫ g :=
adjunction.hom_equiv_naturality_right_symm _ _ _

@[reassoc]
lemma uncurry_natural_left  (f : X ⟶ X') (g : X' ⟶ A⟹Y) :
  uncurry (f ≫ g) = limits.prod.map (𝟙 _) f ≫ uncurry g :=
adjunction.hom_equiv_naturality_left_symm _ _ _

@[simp]
lemma uncurry_curry (f : A ⨯ X ⟶ Y) : uncurry (curry f) = f :=
(exponentiable.is_adj.adj.hom_equiv _ _).left_inv f

@[simp]
lemma curry_uncurry (f : X ⟶ A⟹Y) : curry (uncurry f) = f :=
(exponentiable.is_adj.adj.hom_equiv _ _).right_inv f

lemma curry_eq_iff (f : A ⨯ Y ⟶ X) (g : Y ⟶ A ⟹ X) :
  curry f = g ↔ f = uncurry g :=
adjunction.hom_equiv_apply_eq _ f g

lemma eq_curry_iff [exponentiable A] (f : A ⨯ Y ⟶ X) (g : Y ⟶ A ⟹ X) :
  g = curry f ↔ uncurry g = f :=
adjunction.eq_hom_equiv_apply _ f g

-- I don't think these two should be simp.
lemma uncurry_eq (g : Y ⟶ A ⟹ X) : uncurry g = limits.prod.map (𝟙 A) g ≫ ev A X :=
adjunction.hom_equiv_counit _

lemma curry_eq (g : A ⨯ Y ⟶ X) : curry g = coev A Y ≫ post A g :=
adjunction.hom_equiv_unit _

lemma uncurry_id_eq_ev (A X : C) [exponentiable A] : uncurry (𝟙 (A ⟹ X)) = ev A X :=
by rw [uncurry_eq, prod_map_id_id, id_comp]

lemma curry_id_eq_coev (A X : C) [exponentiable A] : curry (𝟙 _) = coev A X :=
by { rw [curry_eq, post, functor.map_id], apply comp_id }

lemma curry_injective : function.injective (curry : (A ⨯ Y ⟶ X) → (Y ⟶ A ⟹ X)) :=
(exponentiable.is_adj.adj.hom_equiv _ _).injective

lemma uncurry_injective : function.injective (uncurry : (Y ⟶ A ⟹ X) → (A ⨯ Y ⟶ X)) :=
(exponentiable.is_adj.adj.hom_equiv _ _).symm.injective

section terminal
variable [has_finite_products.{v} C]


-- This isn't an instance because most of the time we'll prove cartesian closed for all objects
-- at once, rather than just for this one.
def terminal_exponentiable : exponentiable ⊤_C :=
{ is_adj :=
  { right := 𝟭 C,
    adj := adjunction.mk_of_hom_equiv
    { hom_equiv := λ X _, have unitor : _, from prod.left_unitor X,
        ⟨λ a, unitor.inv ≫ a, λ a, unitor.hom ≫ a, by tidy, by tidy⟩ } } }

/-- The typeclass argument is explicit so that any instance can be used, not just the above. -/
def exp_terminal_iso [exponentiable ⊤_C] : (⊤_C ⟹ X) ≅ X :=
yoneda.ext (⊤_ C ⟹ X) X
  (λ Y f, (prod.left_unitor Y).inv ≫ uncurry f)
  (λ Y f, curry ((prod.left_unitor Y).hom ≫ f))
  (λ Z g, by rw [curry_eq_iff, iso.hom_inv_id_assoc] )
  (λ Z g, by simp)
  (λ Z W f g, by rw [uncurry_natural_left, prod_left_unitor_inv_naturality_assoc f] )

@[reducible]
def point_at_hom [exponentiable A] (f : A ⟶ Y) : ⊤_C ⟶ (A ⟹ Y) :=
curry (limits.prod.fst ≫ f)

end terminal

section pre

variables [has_finite_products.{v} C] {B}

def pre (X : C) (f : B ⟶ A) [exponentiable A] [exponentiable B] :  (A⟹X) ⟶ B⟹X :=
curry (limits.prod.map f (𝟙 _) ≫ ev A X)

lemma pre_id (A X : C) [exponentiable A] : pre X (𝟙 A) = 𝟙 (A⟹X) :=
by { rw [pre, prod_map_id_id, id_comp, ← uncurry_id_eq_ev], simp }

-- There's probably a better proof of this somehow
lemma pre_map [exponentiable A] [exponentiable B] {D : C} [exponentiable D] (f : A ⟶ B) (g : B ⟶ D) :
  pre X (f ≫ g) = pre X g ≫ pre X f :=
begin
  rw [pre, curry_eq_iff, pre, pre, uncurry_natural_left, uncurry_curry, prod_map_comm_assoc,
      prod_functorial, assoc, ← uncurry_id_eq_ev, ← uncurry_id_eq_ev, ← uncurry_natural_left,
      curry_natural_right, comp_id, uncurry_natural_right, uncurry_curry],
end

end pre

@[simps]
def pre.functor [has_finite_products.{v} C] [is_cartesian_closed C] (X : C) : Cᵒᵖ ⥤ C :=
{ obj := λ A, (A.unop) ⟹ X,
  map := λ A B f, pre X f.unop,
  map_id' := λ B, pre_id B.unop X,
  map_comp' := λ P Q R f g, pre_map g.unop f.unop }

lemma exp_natural [has_finite_products.{v} C] [is_cartesian_closed C] {A B : C} {X Y : Cᵒᵖ} (f : A ⟶ B) (g : X ⟶ Y) :
  (pre.functor A).map g ≫ post (opposite.unop Y) f = post (opposite.unop X) f ≫ (pre.functor B).map g :=
begin
  dsimp [pre],
  rw [← curry_natural_left, eq_curry_iff, uncurry_natural_right, uncurry_curry, prod_map_comm_assoc],
  simp,
end

def exp.difunctor [has_finite_products.{v} C] [is_cartesian_closed C] : C ⥤ Cᵒᵖ ⥤ C :=
{ obj := pre.functor,
  map := λ A B f, { app := λ X, post X.unop f, naturality' := λ X Y g, exp_natural _ _ },
  map_id' := λ X, by { ext, apply functor.map_id },
  map_comp' := λ X Y Z f g, by { ext, apply functor.map_comp } }

@[simps]
def zero_mul [has_initial.{v} C] : A ⨯ ⊥_ C ≅ ⊥_ C :=
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

def mul_zero [has_initial.{v} C] : ⊥_ C ⨯ A ≅ ⊥_ C :=
limits.prod.braiding _ _ ≪≫ zero_mul

def pow_zero [has_initial.{v} C] [is_cartesian_closed C] : ⊥_C ⟹ B ≅ ⊤_ C :=
{ hom := default _,
  inv := curry (mul_zero.hom ≫ default (⊥_ C ⟶ B)),
  hom_inv_id' :=
  begin
    rw [← curry_natural_left, curry_eq_iff, ← cancel_epi mul_zero.inv],
    { apply subsingleton.elim },
    { apply_instance },
    { apply_instance }
  end }

-- MOVE TO SOMEWHERE ELSE BEFORE PR
def is_iso_of_mono_of_split_epi {X Y : C} (f : X ⟶ Y) [mono f] [split_epi f] : is_iso f :=
{ inv := section_ f,
  hom_inv_id' := by simp [← cancel_mono f] }

instance strict_initial [has_initial.{v} C] {f : A ⟶ ⊥_ C} : is_iso f :=
begin
  haveI : mono (limits.prod.lift (𝟙 A) f ≫ zero_mul.hom) := mono_comp _ _,
  rw [zero_mul_hom, prod.lift_snd] at _inst,
  haveI: split_epi f := ⟨default _, subsingleton.elim _ _⟩,
  apply is_iso_of_mono_of_split_epi
end

instance initial_mono (B : C) [has_initial.{v} C] [is_cartesian_closed C] : mono (initial.to B) :=
⟨λ B g h _, eq_of_inv_eq_inv (subsingleton.elim (inv g) (inv h))⟩

variables {D : Type u₂} [category.{v} D]
section functor

variables [has_finite_products.{v} C] [has_finite_products.{v} D]

/--
Note we didn't require any coherence between the choice of finite products here, since we transport
along the `mult_comparison` isomorphism.
-/
def cartesian_closed_of_equiv (e : C ≌ D) [h : is_cartesian_closed C] : is_cartesian_closed D :=
{ cart_closed := λ X,
  { is_adj :=
    begin
      haveI q : exponentiable (e.inverse.obj X) := infer_instance,
      have := q.is_adj,
      have: e.functor ⋙ prod_functor.obj X ⋙ e.inverse ≅ prod_functor.obj (e.inverse.obj X),
      apply nat_iso.of_components _ _,
      intro Y,
      apply mult_comparison e.inverse X (e.functor.obj Y) ≪≫ _,
      refine ⟨limits.prod.map (𝟙 _) (e.unit_inv.app _),
              limits.prod.map (𝟙 _) (e.unit.app _),
              by simpa [← prod_functorial', prod_map_id_id],
              by simpa [← prod_functorial', prod_map_id_id]⟩,
      intros Y Z g,
      simp only [mult_comparison, prod.lift_map, equivalence.unit_inv, functor.comp_map,
                 prod_functor_obj_map, assoc, comp_id, iso.trans_hom],
      apply prod.hom_ext,
      rw [assoc, prod.lift_fst, prod.lift_fst, ← functor.map_comp, limits.prod.map_fst, comp_id],
      rw [assoc, prod.lift_snd, prod.lift_snd, ← functor.map_comp_assoc, limits.prod.map_snd],
      simp only [equivalence.unit, equivalence.unit_inv, nat_iso.hom_inv_id_app, assoc, equivalence.inv_fun_map, functor.map_comp, comp_id],
      erw comp_id,
      haveI : is_left_adjoint (e.functor ⋙ prod_functor.obj X ⋙ e.inverse) := adjunction.left_adjoint_of_nat_iso this.symm,
      haveI : is_left_adjoint e.inverse := functor.left_adjoint_of_equivalence,
      haveI : is_left_adjoint e.functor := functor.left_adjoint_of_equivalence,
      haveI : is_left_adjoint (e.inverse ⋙ e.functor ⋙ prod_functor.obj X ⋙ e.inverse) := adjunction.left_adjoint_of_comp e.inverse _,
      haveI := adjunction.left_adjoint_of_comp (e.inverse ⋙ e.functor ⋙ prod_functor.obj X ⋙ e.inverse) e.functor,
      have : (e.inverse ⋙ e.functor ⋙ prod_functor.obj X ⋙ e.inverse) ⋙ e.functor ≅ prod_functor.obj X,
        apply iso_whisker_right e.counit_iso (prod_functor.obj X ⋙ e.inverse ⋙ e.functor) ≪≫ _,
        change prod_functor.obj X ⋙ e.inverse ⋙ e.functor ≅ prod_functor.obj X,
        apply iso_whisker_left (prod_functor.obj X) e.counit_iso,
      apply adjunction.left_adjoint_of_nat_iso this,
    end
  }
}

variables [is_cartesian_closed C] [is_cartesian_closed D]
variables (F : C ⥤ D) [preserves_limits_of_shape (discrete walking_pair) F]

/--
The exponential comparison map.
`F` is a cartesian closed functor if this is an iso for all `A,B`.
-/
def exp_comparison (A B : C) :
  F.obj (A ⟹ B) ⟶ F.obj A ⟹ F.obj B :=
curry ((mult_comparison F A _).inv ≫ F.map (ev _ _))

lemma exp_comparison_natural_left (A A' B : C) (f : A' ⟶ A) :
  exp_comparison F A B ≫ pre (F.obj B) (F.map f) = F.map (pre B f) ≫ exp_comparison F A' B :=
by rw [exp_comparison, exp_comparison, ← curry_natural_left, eq_curry_iff, uncurry_natural_left,
       pre, uncurry_curry, prod_map_comm_assoc, curry_eq, prod_functorial', assoc, ev_nat,
       ev_coev_assoc, ← F.map_id, ← mult_comparison_inv_natural_assoc, ← F.map_id,
       ← mult_comparison_inv_natural_assoc, ← F.map_comp, ← F.map_comp, pre, curry_eq,
       prod_functorial', assoc, ev_nat, ev_coev_assoc]

lemma exp_comparison_natural_right (A B B' : C) (f : B ⟶ B') :
  exp_comparison F A B ≫ post (F.obj A) (F.map f) = F.map (post A f) ≫ exp_comparison F A B' :=
by rw [exp_comparison, ← curry_natural_right, curry_eq_iff, exp_comparison, uncurry_natural_left,
      uncurry_curry, assoc, ← F.map_comp, ← ev_nat, F.map_comp, mult_comparison_inv_natural_assoc,
      F.map_id]

-- TODO: If F has a left adjoint L, then F is cartesian closed if and only if
-- L (B ⨯ F A) ⟶ L B ⨯ L F A ⟶ L B ⨯ A
-- is an iso for all A ∈ D, B ∈ C.
-- Corollary: If F has a left adjoint L which preserves finite products, F is cartesian closed iff
-- F is full and faithful.

end functor

end category_theory
