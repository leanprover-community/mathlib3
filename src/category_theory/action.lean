/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import category_theory.elements
import category_theory.is_connected
import category_theory.single_obj
import group_theory.group_action.basic
import group_theory.semidirect_product

/-!
# Actions as functors and as categories

From a multiplicative action M ↻ X, we can construct a functor from M to the category of
types, mapping the single object of M to X and an element `m : M` to map `X → X` given by
multiplication by `m`.
  This functor induces a category structure on X -- a special case of the category of elements.
A morphism `x ⟶ y` in this category is simply a scalar `m : M` such that `m • x = y`. In the case
where M is a group, this category is a groupoid -- the `action groupoid'.
-/

open mul_action semidirect_product
namespace category_theory

universes u

variables (M : Type*) [monoid M] (X : Type u) [mul_action M X]

/-- A multiplicative action M ↻ X viewed as a functor mapping the single object of M to X
  and an element `m : M` to the map `X → X` given by multiplication by `m`. -/
@[simps]
def action_as_functor : single_obj M ⥤ Type u :=
{ obj := λ _, X,
  map := λ _ _, (•),
  map_id' := λ _, funext $ mul_action.one_smul,
  map_comp' := λ _ _ _ f g, funext $ λ x, (smul_smul g f x).symm }

/-- A multiplicative action M ↻ X induces a category strucure on X, where a morphism
 from x to y is a scalar taking x to y. Due to implementation details, the object type
 of this category is not equal to X, but is in bijection with X. -/
@[derive category]
def action_category := (action_as_functor M X).elements

namespace action_category

/-- The projection from the action category to the monoid, mapping a morphism to its
  label. -/
def π : action_category M X ⥤ single_obj M :=
category_of_elements.π _

@[simp]
lemma π_map (p q : action_category M X) (f : p ⟶ q) : (π M X).map f = f.val := rfl

@[simp]
lemma π_obj (p : action_category M X) : (π M X).obj p = single_obj.star M :=
unit.ext

variables {M X}
/-- The canonical map `action_category M X → X`. It is given by `λ x, x.snd`, but
  has a more explicit type. -/
protected def back : action_category M X → X :=
λ x, x.snd

instance : has_coe_t X (action_category M X) :=
⟨λ x, ⟨(), x⟩⟩

@[simp] lemma coe_back (x : X) : (↑x : action_category M X).back = x := rfl
@[simp] lemma back_coe (x : action_category M X) : ↑(x.back) = x := by ext; refl

variables (M X)

/-- An object of the action category given by M ↻ X corresponds to an element of X. -/
def obj_equiv : X ≃ action_category M X :=
{ to_fun := coe,
  inv_fun := λ x, x.back,
  left_inv := coe_back,
  right_inv := back_coe }

lemma hom_as_subtype (p q : action_category M X) :
  (p ⟶ q) = { m : M // m • p.back = q.back } := rfl

instance [inhabited X] : inhabited (action_category M X) :=
{ default := ↑(default X) }

instance [nonempty X] : nonempty (action_category M X) :=
nonempty.map (obj_equiv M X) infer_instance

variables {X} (x : X)
/-- The stabilizer of a point is isomorphic to the endomorphism monoid at the
  corresponding point. In fact they are definitionally equivalent. -/
def stabilizer_iso_End : stabilizer.submonoid M x ≃* End (↑x : action_category M X) :=
mul_equiv.refl _

@[simp]
lemma stabilizer_iso_End_apply (f : stabilizer.submonoid M x) :
  (stabilizer_iso_End M x).to_fun f = f := rfl

@[simp]
lemma stabilizer_iso_End_symm_apply (f : End _) :
  (stabilizer_iso_End M x).inv_fun f = f := rfl

variables {M X}

@[simp] protected lemma id_val (x : action_category M X) : subtype.val (𝟙 x) = 1 := rfl

@[simp] protected lemma comp_val {x y z : action_category M X}
  (f : x ⟶ y) (g : y ⟶ z) : (f ≫ g).val = g.val * f.val := rfl

instance [is_pretransitive M X] [nonempty X] : is_connected (action_category M X) :=
zigzag_is_connected $ λ x y, relation.refl_trans_gen.single $ or.inl $
  nonempty_subtype.mpr (show _, from exists_smul_eq M x.back y.back)

section group

variables {G : Type*} [group G] [mul_action G X]

noncomputable instance : groupoid (action_category G X) :=
category_theory.groupoid_of_elements _

/-- Any subgroup of `G` is a vertex group in its action groupoid. -/
def End_mul_equiv_subgroup (H : subgroup G) :
  End (obj_equiv G (quotient_group.quotient H) ↑(1 : G)) ≃* H :=
mul_equiv.trans
  (stabilizer_iso_End G ((1 : G) : quotient_group.quotient H)).symm
  (mul_equiv.subgroup_congr $ stabilizer_quotient H)

/-- A target vertex `t` and a scalar `g` determine a morphism in the action groupoid. -/
def hom_of_pair (t : X) (g : G) : ↑(g⁻¹ • t) ⟶ (t : action_category G X) :=
subtype.mk g (smul_inv_smul g t)

@[simp] lemma hom_of_pair.val (t : X) (g : G) : (hom_of_pair t g).val = g := rfl

/-- Any morphism in the action groupoid is given by some pair. -/
protected def cases {P : Π ⦃a b : action_category G X⦄, (a ⟶ b) → Sort*}
  (hyp : ∀ t g, P (hom_of_pair t g)) ⦃a b⦄ (f : a ⟶ b) : P f :=
begin
  refine cast _ (hyp b.back f.val),
  rcases a with ⟨⟨⟩, a : X⟩,
  rcases b with ⟨⟨⟩, b : X⟩,
  rcases f with ⟨g : G, h : g • a = b⟩,
  cases (inv_smul_eq_iff.mpr h.symm),
  refl
end

variables {H : Type*} [group H]

/-- Given `G` acting on `X`, a functor from the corresponding action groupoid to a group `H`
    can be curried to a group homomorphism `G →* (X → H) ⋊ G`. -/
@[simps] def curry (F : action_category G X ⥤ single_obj H) :
  G →* (X → H) ⋊[mul_aut_arrow] G :=
have F_map_eq : ∀ {a b} {f : a ⟶ b}, F.map f = (F.map (hom_of_pair b.back f.val) : H) :=
  action_category.cases (λ _ _, rfl),
{ to_fun := λ g, ⟨λ b, F.map (hom_of_pair b g), g⟩,
  map_one' := by { congr, funext, exact F_map_eq.symm.trans (F.map_id b) },
  map_mul' := begin
    intros g h,
    congr, funext,
    exact F_map_eq.symm.trans (F.map_comp (hom_of_pair (g⁻¹ • b) h) (hom_of_pair b g)),
  end }

/-- Given `G` acting on `X`, a group homomorphism `φ : G →* (X → H) ⋊ G` can be uncurried to
    a functor from the action groupoid to `H`, provided that `φ g = (_, g)` for all `g`. -/
@[simps] def uncurry (F : G →* (X → H) ⋊[mul_aut_arrow] G) (sane : ∀ g, (F g).right = g) :
  action_category G X ⥤ single_obj H :=
{ obj := λ _, (),
  map := λ a b f, ((F f.val).left b.back),
  map_id' := by { intro x, rw [action_category.id_val, F.map_one], refl },
  map_comp' := begin
    intros x y z f g, revert y z g,
    refine action_category.cases _,
    simp [single_obj.comp_as_mul, sane],
  end }

end group

end action_category
end category_theory
