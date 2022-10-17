/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.category.basic
import category_theory.functor.basic
import category_theory.groupoid
import category_theory.groupoid.basic
import combinatorics.quiver.basic
import combinatorics.quiver.symmetric
import logic.relation
import tactic.nth_rewrite
import category_theory.path_category
import category_theory.quotient
import category_theory.groupoid.vertex_group
import category_theory.groupoid.action

/-!
# Covering of groupoids

-/

namespace category_theory

namespace groupoid


universes u v u' v' u'' v''

variables {V : Type*}   [groupoid V]
          {V' : Type*}  [groupoid V']  (φ : V ⥤ V')
          {V'' : Type*} [groupoid V''] (φ' : V' ⥤ V'')

/-- Definition following Brown -/
def _root_.category_theory.functor.is_covering :=
∀ (v : V) (F' : Σ (u' : V'), φ.obj v ⟶ u'),
  ∃! (F : Σ (u : V), v ⟶ u),
    ∃ (h : φ.obj F.1 = F'.1), (φ.map F.2) ≫ (eq_to_hom h) = F'.2

def _root_.category_theory.functor.star_map (v : V) :
  (Σ u, v ⟶ u) → (Σ u', φ.obj v ⟶ u') :=
λ F, ⟨φ.obj F.1, φ.map F.2⟩

def _root_.category_theory.functor.costar_map (v : V) :
  (Σ u, u ⟶ v) → (Σ u', u' ⟶ φ.obj v) :=
λ F, ⟨φ.obj F.1, φ.map F.2⟩

lemma is_covering_iff_star_map_bij :
  φ.is_covering ↔ (∀ v, function.bijective $ φ.star_map v) := sorry

namespace covering

variables (φ)

lemma _root_.category_theory.functor.star_map_comp (v : V) :
  (φ ⋙ φ').star_map v = (φ'.star_map $ φ.obj v) ∘ (φ.star_map v) := rfl

lemma _root_.category_theory.functor.costar_map_comp (v : V) :
  (φ ⋙ φ').costar_map v = (φ'.costar_map $ φ.obj v) ∘ (φ.costar_map v) := rfl

def star_equiv_costar (v : V) : (Σ u, v ⟶ u) ≃ (Σ u, u ⟶ v) :=
{ to_fun := λ F, ⟨F.1, inv F.2⟩,
  inv_fun := λ F, ⟨F.1, inv F.2⟩,
  left_inv := λ F, by simp only [inv_eq_inv, is_iso.inv_inv, sigma.eta],
  right_inv := λ F, by simp only [inv_eq_inv, is_iso.inv_inv, sigma.eta]}

lemma star_equiv_costar_map (v : V) :
  (φ.costar_map v) ∘ (star_equiv_costar v) = star_equiv_costar (φ.obj v) ∘ (φ.star_map v) :=
begin
  dsimp only [functor.star_map, functor.costar_map, star_equiv_costar],
  apply funext, rintro ⟨u,f⟩,
  simp only [inv_eq_inv, equiv.coe_fn_mk, function.comp_app,
             functor.map_inv, eq_self_iff_true, heq_iff_eq, and_self],
end

lemma star_map_bij_iff_costar_map_bij :
  (∀ v, function.bijective $ φ.star_map v) ↔ (∀ v, function.bijective $ φ.costar_map v) :=
begin
  sorry, -- using `star_equiv_costar` and `star_equiv_costar_map`
end

def above_start {u' v' : V'} (f' : u' ⟶ v') :
  { F : Σ (u v : V), u ⟶ v |
    ∃ (hu : u' = φ.obj F.1) (hv : v' = φ.obj F.2.1),
    (eq_to_hom hu) ≫ φ.map F.2.2 = f' ≫ (eq_to_hom hv) } → {u : V | φ.obj u = u'} :=
λ ⟨⟨u,v,f⟩,h⟩, ⟨u, h.some.symm⟩

def above_end  {u' v' : V'} (f' : u' ⟶ v') :
  { F : Σ (u v : V), u ⟶ v |
    ∃ (hu : u' = φ.obj F.1) (hv : v' = φ.obj F.2.1),
    (eq_to_hom hu) ≫ φ.map F.2.2 = f' ≫ (eq_to_hom hv) } → {v : V | φ.obj v = v'} :=
λ ⟨⟨u,v,f⟩,h⟩, ⟨v, h.some_spec.some.symm⟩

lemma above_start_bij  (φc : φ.is_covering) {u' v' : V'} (f' : u' ⟶ v') :
  function.bijective (above_start φ  f') :=
begin
  split,
  { rw is_covering_iff_star_map_bij at φc,
    rintro ⟨uf,vf,f⟩ ⟨ug,vg,g⟩, },
end

lemma above_end_bij {u' v' : V'} (f' : u' ⟶ v') :
  function.bijective (above_start φ  f') := sorry



variables {φ}

/-- Following brown -/
def characteristic_group  (φc : φ.is_covering) (v : V) := (φ.map_vertex_group v).range

lemma map_vertex_group_mono  (φc : φ.is_covering) (v : V) : (φ.map_vertex_group v).ker = ⊥ :=
begin
  rw [monoid_hom.ker_eq_bot_iff],
  rintro f g he,
  simp only [functor.map_vertex_group_apply] at he,
  obtain hf := (φc v ⟨φ.obj v, φ.map f⟩),
  have := @exists_unique.unique _ _ hf ⟨v,f⟩ ⟨v,g⟩ _ _, rotate,
  { use rfl, apply category.comp_id', },
  { use rfl, simp, exact he.symm, },
  simpa only [sigma.ext_iff, eq_self_iff_true, heq_iff_eq, true_and] using this,
end

lemma comp (φc : φ.is_covering) (φ'c : φ'.is_covering) :
  (φ ⋙ φ').is_covering := sorry
lemma comp' (φ'c : φ'.is_covering) (φφ'c : (φ ⋙ φ').is_covering ) :
  φ.is_covering := sorry
lemma comp'' (φc : φ.is_covering) (φφ'c : (φ ⋙ φ').is_covering) (φ'sur : function.surjective φ'.obj) :
  φ.is_covering := sorry


instance (φc : φ.is_covering) : groupoid_action V' V :=
{ w := φ.obj,
  mul := λ x t f, sorry,
  mul_w := λ x t f, sorry,
  mul_id' := λ x, sorry,
  mul_comp' := λ x s t f g, sorry, }


end covering

end groupoid

end category_theory
