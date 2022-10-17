/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.category.basic
import category_theory.functor.basic
import category_theory.groupoid
import category_theory.groupoid.basic
--import category_theory.groupoid.vertex_group



/-!
# Actions of groupoids

-/

namespace category_theory

namespace groupoid

universes u v u' v' u'' v''

/--
Following Brown, but instead of a map `w : X → V` we take `p : V → set X`
plus the fact that it partitions `X`
-/
class groupoid_action (V : Type*) [groupoid V] (X : Type*) :=
(p : V → set X)
(p_part : ∀ x, ∃! v, x ∈ p v) -- needed?
(mul : Π {s t : V} (f : s ⟶ t), p s → p t)
(mul_id' : Π (v  : V), mul (𝟙 v) = id)
(mul_comp' : Π {r s t : V} (f : r ⟶ s) (g : s ⟶ t), (mul g) ∘ (mul f) = mul (f ≫ g))

namespace action

notation x ` •≫ ` f:73 := groupoid_action.mul f x

variables  {V : Type*} [groupoid V] {X : Type*} [g : groupoid_action V X]

def is_transitive :=
∀ (x y : X),
  ∃ (s t : V) (xs : x ∈ g.p s) (yt : y ∈ g.p t) (f : s ⟶ t),
    ⟨x,xs⟩ •≫ f = ⟨y,yt⟩

noncomputable def obj (g : groupoid_action V X) (x : X) : V := (g.p_part x).exists.some

def obj_p (g : groupoid_action V X) (x : X) : x ∈ g.p (obj g x) := (g.p_part x).exists.some_spec

noncomputable def mul' (x : X) {t : V} (f : obj g x ⟶ t) : X :=
(⟨x,obj_p g x⟩ •≫ f).val


notation x ` ·≫ ` f:100 := mul' x f

@[simp]
lemma mul_eq_mul' (x : X) {t : V} (f : obj g x ⟶ t) : x ·≫ f = (⟨x,obj_p g x⟩ •≫ f).val := rfl

/-
def stabilizer (v : V) (x : g.p v) : subgroup (v ⟶ v) :=
{ carrier := {f | x •≫ f = x},
  one_mem' := congr_fun (groupoid_action.mul_id' v) x,
  mul_mem' := λ f f' hf hf', by
  { rw [set.mem_set_of_eq] at hf hf' ⊢,
    rw [vertex_group_mul, ←congr_fun (groupoid_action.mul_comp' f f') x,
        function.comp_app,hf,hf'], },
  inv_mem' := λ f hf, by
  { rw [set.mem_set_of_eq] at hf ⊢,
    nth_rewrite 0 ←hf,
    convert ←congr_fun (groupoid_action.mul_comp' f (inv f)) x,
    rw [inv_eq_inv, is_iso.hom_inv_id],
    exact congr_fun (groupoid_action.mul_id' v) x, } }-/

set_option profiler true

noncomputable instance semidirect_product : groupoid X :=
{ hom := λ x y, { f : obj g x ⟶ obj g y | x ·≫ f = y},
  id := λ x,
  ⟨ 𝟙 $ obj g x,
    by
    { dsimp only [mul'],
      rw [set.mem_set_of_eq, groupoid_action.mul_id'],
      refl, } ⟩,
  comp := λ x y z f h,
  ⟨ f.val ≫ h.val,
    by
    { dsimp only [mul'],
      rw [set.mem_set_of_eq,←groupoid_action.mul_comp', function.comp_app],
      rw [subtype.val_eq_coe, subtype.val_eq_coe, subtype.val_eq_coe],
      rw [subtype.coe_eq_of_eq_mk f.prop, subtype.coe_eq_of_eq_mk h.prop],
      refl, } ⟩,
  id_comp' := λ _ _ _, by simp_rw [subtype.val_eq_coe, category.id_comp, subtype.coe_eta],
  comp_id' := λ _ _ _, by simp_rw [subtype.val_eq_coe, category.comp_id, subtype.coe_eta],
  assoc' := λ _ _ _ _ _ _ _, by simp_rw [category.assoc],
  inv := λ x y f,
  ⟨ inv f,
    by
    { sorry, /-simp only [set.mem_set_of_eq, subtype.val_eq_coe, inv_eq_inv, mul_eq_mul'],
      have : x = ((⟨x, obj_p g x⟩ •≫ f.val) •≫ (inv f.val)) := sorry,
      nth_rewrite_rhs 0 this,
      let := subtype.coe_eq_of_eq_mk f.prop,
      nth_rewrite_lhs 0 ←this,
      simp only [subtype.val_eq_coe, inv_eq_inv],-/
    } ⟩,
  inv_comp' := λ _ _ _, by sorry, --simp_rw [subtype.val_eq_coe, inv_eq_inv, is_iso.inv_hom_id],
  comp_inv' := λ _ _ _, by sorry--simp_rw [subtype.val_eq_coe, inv_eq_inv, is_iso.hom_inv_id]
}


end action

end groupoid

end category_theory
