/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.ring.basic
import tactic.nth_rewrite
import algebra.group.hom_instances

/-!
# Centroid homomorphisms

This file defines centroid homomorphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `centroid_hom`: Maps which preserve `⊔`.

## Typeclasses

* `centroid_hom_class`
-/

open function

variables {F α : Type*}

/-- The type of centroid homomorphisms from `α` to `α`. -/
structure centroid_hom (α : Type*) [non_unital_non_assoc_semiring α] extends α →+ α :=
(map_mul_left' (a b : α) : to_fun (a * b) = a * to_fun b)
(map_mul_right' (a b : α) : to_fun (a * b) = to_fun a * b)

/-- `centroid_hom_class F α` states that `F` is a type of centroid homomorphisms.

You should extend this class when you extend `centroid_hom`. -/
class centroid_hom_class (F : Type*) (α : out_param $ Type*) [non_unital_non_assoc_semiring α]
  extends add_monoid_hom_class F α α :=
(map_mul_left (f : F) (a b : α) : f (a * b) = a * f b)
(map_mul_right (f : F) (a b : α) : f (a * b) = f a * b)

export centroid_hom_class (map_mul_left map_mul_right)

instance [non_unital_non_assoc_semiring α] [centroid_hom_class F α] :
  has_coe_t F (centroid_hom α) :=
⟨λ f, { to_fun := f, map_mul_left' := map_mul_left f, map_mul_right' := map_mul_right f,
  ..(f : α →+ α) }⟩

/-! ### Centroid homomorphisms -/

namespace centroid_hom

section non_unital_non_assoc_semiring

variables [non_unital_non_assoc_semiring α]

instance : centroid_hom_class (centroid_hom α) α :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_zero := λ f, f.map_zero',
  map_add := λ f, f.map_add',
  map_mul_left := λ f, f.map_mul_left',
  map_mul_right := λ f, f.map_mul_right' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (centroid_hom α) (λ _, α → α) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : centroid_hom α} : f.to_fun = (f : α → α) := rfl

@[ext] lemma ext {f g : centroid_hom α} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `centroid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : centroid_hom α) (f' : α → α) (h : f' = f) :
  centroid_hom α :=
{ to_fun := f',
  map_mul_left' := λ a b, by simp_rw [h, map_mul_left],
  map_mul_right' := λ a b, by simp_rw [h, map_mul_right],
  ..f.to_add_monoid_hom.copy f' $ by exact h }

variables (α)

/-- `id` as a `centroid_hom`. -/
protected def id : centroid_hom α := ⟨add_monoid_hom.id α, λ _ _, rfl, λ _ _, rfl⟩

instance : inhabited (centroid_hom α) := ⟨centroid_hom.id α⟩

@[simp] lemma coe_id : ⇑(centroid_hom.id α) = id := rfl

lemma coe_to_add_monoid_hom_id : (centroid_hom.id α : α →+ α) = add_monoid_hom.id α := rfl

variables {α}

@[simp] lemma id_apply (a : α) : centroid_hom.id α a = a := rfl

/-- Composition of `centroid_hom`s as a `centroid_hom`. -/
def comp (g f : centroid_hom α) : centroid_hom α :=
⟨g.to_add_monoid_hom.comp f.to_add_monoid_hom,
  λ a b, (congr_arg g $ f.map_mul_left' _ _).trans $ g.map_mul_left' _ _,
  λ a b, (congr_arg g $ f.map_mul_right' _ _).trans $ g.map_mul_right' _ _⟩

@[simp] lemma coe_comp (g f : centroid_hom α) : ⇑(g.comp f) = g ∘ f := rfl
@[simp] lemma comp_apply (g f : centroid_hom α) (a : α) : g.comp f a = g (f a) := rfl
@[simp] lemma coe_comp_add_monoid_hom (g f : centroid_hom α) :
  (g.comp f : α →+ α) = (g : α →+ α).comp f := rfl
@[simp] lemma comp_assoc (h g f : centroid_hom α) : (h.comp g).comp f = h.comp (g.comp f) := rfl
@[simp] lemma comp_id (f : centroid_hom α) : f.comp (centroid_hom.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : centroid_hom α) : (centroid_hom.id α).comp f = f := ext $ λ a, rfl

lemma cancel_right {g₁ g₂ f : centroid_hom α} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g f₁ f₂ : centroid_hom α} (hg : injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

-- c.f. https://github.com/leanprover-community/mathlib/blob/5d405e2a7028f87e962e7cc2133dc0cfc9c55f7d/src/algebra/group/hom.lean#L885
instance : monoid (centroid_hom α) :=
{ mul := centroid_hom.comp,
  one := centroid_hom.id α,
  mul_assoc := λ _ _ _, centroid_hom.comp_assoc _ _ _,
  mul_one := centroid_hom.comp_id,
  one_mul := centroid_hom.id_comp }

@[simp] lemma coe_mul (f g) : ((f * g : centroid_hom α) : α → α) = f ∘ g := rfl

/-- Addition of `centroid_hom`s as a `centroid_hom`. -/
def add (g f : centroid_hom α) : centroid_hom α :=
⟨g.to_add_monoid_hom + f.to_add_monoid_hom,
λ a b, by rw [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.add_apply,
  ← add_monoid_hom.to_fun_eq_coe, ← add_monoid_hom.to_fun_eq_coe, map_mul_left', map_mul_left',
  ← mul_add, add_monoid_hom.to_fun_eq_coe, add_monoid_hom.to_fun_eq_coe, add_monoid_hom.add_apply],
λ a b, by rw [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.add_apply,
  ← add_monoid_hom.to_fun_eq_coe, ← add_monoid_hom.to_fun_eq_coe, map_mul_right', map_mul_right',
  ← add_mul, add_monoid_hom.to_fun_eq_coe, add_monoid_hom.to_fun_eq_coe, add_monoid_hom.add_apply]
⟩

/-- The zero `centroid_hom` -/
def zero : centroid_hom α :=
⟨(0 : add_monoid.End α) ,
λ a b, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.zero_apply, mul_zero],
λ a b, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.zero_apply, zero_mul],⟩

-- c.f. https://github.com/leanprover-community/mathlib/blob/master/src/algebra/group/hom_instances.lean#L28
instance : add_comm_monoid (centroid_hom α) :=
{ add := centroid_hom.add,
  add_assoc := by intros; ext; apply add_assoc,
  zero := zero,
  zero_add := by intros; ext; apply zero_add,
  add_zero := by intros; ext; apply add_zero,
  add_comm := by intros; ext; apply add_comm, }

lemma add_apply (f g : centroid_hom α) (a : α) : (f + g) a = f a + g a := rfl

@[simp] lemma zero_apply (a: α): (0 : centroid_hom α) a = 0 := rfl

-- c.f https://github.com/leanprover-community/mathlib/blob/master/src/algebra/group/hom_instances.lean#L58
instance : semiring (centroid_hom α) :=
{ zero_mul := λ x, centroid_hom.ext $ λ i, rfl,
  mul_zero := λ x, centroid_hom.ext $ λ i, add_monoid_hom.map_zero _,
  left_distrib :=  λ x y z, centroid_hom.ext $ λ i, add_monoid_hom.map_add _ _ _,
  right_distrib := λ x y z, centroid_hom.ext $ λ i, rfl,
  .. centroid_hom.monoid,
  .. centroid_hom.add_comm_monoid }

lemma comm_comp_mul (T S : centroid_hom α) (a b : α) : (T ∘ S)(a * b) = (S ∘ T)(a * b) :=
  by rw [comp_app, map_mul_right, map_mul_left, ←map_mul_right, ←map_mul_left]

end non_unital_non_assoc_semiring

section non_unital_non_assoc_ring

variables [non_unital_non_assoc_ring α]

/-- Negation of `centroid_hom`s as a `centroid_hom`. -/
def neg (f : centroid_hom α) : centroid_hom α :=
⟨ -(f.to_add_monoid_hom) ,
λ a b, by rw [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.neg_apply, add_monoid_hom.neg_apply,
  mul_neg, ← add_monoid_hom.to_fun_eq_coe, map_mul_left'],
λ a b, by rw [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.neg_apply, add_monoid_hom.neg_apply,
  ← add_monoid_hom.to_fun_eq_coe, map_mul_right', ← neg_mul],
⟩

instance : add_comm_group (centroid_hom α) :=
{ neg := neg,
  add_left_neg := by intros; ext; apply add_left_neg,
  ..centroid_hom.add_comm_monoid }

instance  : ring (centroid_hom α) :=
{ .. centroid_hom.semiring,
  .. centroid_hom.add_comm_group }

lemma neg_apply (f : centroid_hom α) (a : α) : (-f) a = - (f a) := rfl

lemma sub_apply (f g : centroid_hom α) (a : α) : (f - g) a = f a - g a :=
by rw [sub_eq_add_neg, sub_eq_add_neg, add_apply, neg_apply]

end non_unital_non_assoc_ring

section non_unital_ring

variables [non_unital_ring α]

-- https://msp.org/pjm/1975/60-1/pjm-v60-n1-p06-s.pdf
/-- A prime associative ring has commutative centroid -/
def prime_centroid_commutative (h: ∀ a b : α, ∀ r : α, a * r * b = 0 → a = 0 ∨ b = 0) :
  comm_ring (centroid_hom α) :=
{
  mul_comm := λ f g, begin
    rw ← sub_eq_zero,
    have h' : ∀ a : α, ∀ r : α, a * r * a = 0 → a = 0 := begin
      intros a r h'',
      rw ← or_self (a=0),
      apply h a a r,
      exact h'',
    end,
    ext,
    rw zero_apply,
    have h''' : ∀ r : α, ((f * g - g * f) a) * r * ((f * g - g * f) a) = 0 := λ r, by rw [mul_assoc,
      sub_apply, sub_mul, sub_eq_zero, ← map_mul_right, ← map_mul_right, coe_mul, coe_mul,
      comm_comp_mul],
    have e : (f * g - g * f) a = 0 := begin
      apply h' ((f * g - g * f) a),
      apply h''',
      sorry,
      --apply h' ((f * g - g * f) a) h''',
    end,
    --rw zero_apply,
    --convert h' ((f * g - g * f) a),
    apply e,
  end,
  ..centroid_hom.ring
}

end non_unital_ring

end centroid_hom
