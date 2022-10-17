/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.category.basic
import category_theory.functor.basic
import category_theory.groupoid
import category_theory.groupoid.basic
import category_theory.groupoid.vertex_group



/-!
# Actions of groupoids

-/

namespace category_theory

namespace groupoid


universes u v u' v' u'' v''

/-- Following Brown -/
class groupoid_action (V : Type*) [groupoid V] (X : Type*) :=
(w : X → V)
(mul : Π (x : X) {t : V} (f : w x ⟶ t), X)
(mul_w : Π (x : X) {t : V} (f : w x ⟶ t), w (mul x f) = t )
(mul_id' : Π (x : X), mul x (𝟙 $ w x) = x)
(mul_comp' : Π (x : X) {s t : V} (f : w x ⟶ s) (g : s ⟶ t),
             mul x (f ≫ g) = mul (mul x f) ((eq_to_hom $ mul_w x f) ≫ g))

infix ` •≫ `:73 := groupoid_action.mul
prefix ` · ` :73 := groupoid_action.w
infix ` •≫= `:73 := groupoid_action.mul_w

def groupoid_action.mul_w_hom {V : Type*} [groupoid V] {X : Type*} (g : groupoid_action V X)
  (x : X) {t : V} (f : g.w x ⟶ t) := (eq_to_hom $ g.mul_w x f)

variables {V : Type*} [groupoid V] {X : Type*} [g : groupoid_action V X]

lemma mul_id (x : X) :
  x •≫ (𝟙 (g.w x)) = x := groupoid_action.mul_id' x
lemma mul_comp (x : X) {s t : V} (f : g.w x ⟶ s) (h : s ⟶ t) :
  x •≫ (f ≫ h) = (x •≫ f) •≫ (g.mul_w_hom x f ≫ h) := g.mul_comp' x f h

def action_map {s t : V} (f : s ⟶ t) :
  {x | g.w x = s} → {y | g.w y = t} :=
λ xx, ⟨xx.val •≫ (eq_to_hom xx.prop ≫ f), groupoid_action.mul_w _ _⟩

lemma action_map_bij  {s t : V} (f : s ⟶ t) :
  function.bijective (@action_map V _ X g s t f) := sorry

def is_transitive := ∀ (x y : X), ∃ (f : g.w x ⟶ g.w y), x •≫ f = y

def stabilizer (x : X) : subgroup (g.w x ⟶ g.w x) :=
{ carrier := { f | x •≫ f = x },
  one_mem' := mul_id x,
  mul_mem' := λ f f' hf hf', by
  { simp only [vertex_group_mul, set.mem_set_of_eq] at hf hf' ⊢,
    rw groupoid_action.mul_comp',
    nth_rewrite_rhs 0 ←hf',
    congr,
    assumption, sorry,
    },
  inv_mem' := λ f hf, by
  { simp, rw hf, } }

end groupoid


end category_theory
