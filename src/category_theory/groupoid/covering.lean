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

/-!
# Covering of groupoids

-/

namespace category_theory

namespace groupoid


universes u v u' v' u'' v''

variables {V : Type*}   [groupoid V]
          {V' : Type*}  [groupoid V']  (φ : V ⥤ V')
          {V'' : Type*} [groupoid V''] (φ' : V' ⥤ V'')



def _root_.category_theory.functor.star_map (v : V) :
  (Σ u, v ⟶ u) → (Σ u', φ.obj v ⟶ u') :=
λ F, ⟨φ.obj F.1, φ.map F.2⟩

def _root_.category_theory.functor.costar_map (v : V) :
  (Σ u, u ⟶ v) → (Σ u', u' ⟶ φ.obj v) :=
λ F, ⟨φ.obj F.1, φ.map F.2⟩

def _root_.category_theory.functor.is_covering := ∀ v, function.bijective $ φ.star_map v

namespace covering

@[simp] lemma _root_.category_theory.functor.star_map_comp (v : V) :
  (φ ⋙ φ').star_map v = (φ'.star_map $ φ.obj v) ∘ (φ.star_map v) := rfl

@[simp] lemma _root_.category_theory.functor.costar_map_comp (v : V) :
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
  split,
  { rintros h v,
    rw ←@function.bijective.of_comp_iff _ _ _ _ (star_equiv_costar v),
    { rw star_equiv_costar_map,
      rw function.bijective.of_comp_iff,
      apply equiv.bijective,
      exact h v, },
    { apply equiv.bijective, },
  },
  { rintros h v,
    rw ←@function.bijective.of_comp_iff' _ _ _ (star_equiv_costar (φ.obj v)),
    { rw ←star_equiv_costar_map,
      rw function.bijective.of_comp_iff,
      exact h v,
      apply equiv.bijective, },
    { apply equiv.bijective, }, },
end


inductive above' : Π {u' v' : V'} (f' : u' ⟶ v'),  Sort*
| mk {u v : V} (f : u ⟶ v) : above' (φ.map f)

inductive above'' : (Σ (u' v' : V'), u' ⟶ v') → (Σ (u v : V), u ⟶ v) → Prop
| mk {u v : V} (f : u ⟶ v) : above'' ⟨φ.obj u,φ.obj v, φ.map f⟩ ⟨u,v,f⟩

def above_start'' (F' : Σ (u' v' : V'),  u' ⟶ v') :
  (set_of $ above'' φ F') → {u | φ.obj u = F'.1} := λ Fh,
⟨ Fh.val.1,
  by { rcases Fh with ⟨F,⟨u,v,f⟩⟩, rw [set.mem_set_of_eq], }⟩

def above_end'' (F' : Σ (u' v' : V'),  u' ⟶ v') :
  (set_of $ above'' φ F') → {v | φ.obj v = F'.2.1} := λ Fh,
⟨ Fh.val.2.1,
  by { rcases Fh with ⟨F,⟨u,v,f⟩⟩, rw [set.mem_set_of_eq], }⟩



lemma above_start_bij'' (φc : φ.is_covering) (F' : Σ (u' v' : V'),  u' ⟶ v') :
  function.bijective (above_start'' φ F') :=
begin
  split,
  { rintros, sorry},
  { rcases F' with ⟨u',v',f'⟩,
    rintro ⟨u,hu⟩, dsimp at hu, subst hu, sorry }
end


lemma above'_equiv {u' v' : V'} (f' : u' ⟶ v') : above' φ f ≃ above φ f



def above_start' {u' v' : V'} (f' : u' ⟶ v') : above' φ f' →  {u | φ.obj u = u'} :=
begin
  rintro ⟨u,v,f⟩,
  exact ⟨u,rfl⟩,
end

def above_end' {u' v' : V'} (f' : u' ⟶ v') : above' φ f' →  {v | φ.obj v = v'} :=
begin
  rintro ⟨u,v,f⟩,
  exact ⟨v,rfl⟩,
end

lemma above_start'_bij  {u' v' : V'} (f' : u' ⟶ v') : function.bijective (above_start' φ f') :=
begin
  split,
  { rintros ⟨u₁,v₁,f₁⟩,}
end


def above_start {u' v' : V'} (f' : u' ⟶ v') :
  above φ f' → { u : V | φ.obj u = u' } :=
λ F, ⟨F.val.1, F.prop.some.symm⟩

def above_end  {u' v' : V'} (f' : u' ⟶ v') :
  above φ f' → { v : V | φ.obj v = v' } :=
λ F, ⟨F.val.2.1, F.prop.some_spec.some.symm⟩

lemma above_start_bij  (φc : φ.is_covering) {u' v' : V'} (f' : u' ⟶ v') :
  function.bijective (above_start φ  f') :=
begin
  dsimp [above_start],
  split,
  { rintro ⟨⟨uf,vf,f⟩,huf,hvf,hef⟩ ⟨⟨ug,vg,g⟩,hug,hvg,hef⟩ e,
    subst_vars, simp at hug hvg e, subst_vars,
    sorry, },
  sorry
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
  (φ ⋙ φ').is_covering :=
begin
  simp only [functor.is_covering,functor.star_map_comp],
  rintro v, apply function.bijective.comp (φ'c $ φ.obj v) (φc v),
end
lemma comp' (φ'c : φ'.is_covering) (φφ'c : (φ ⋙ φ').is_covering ) :
  φ.is_covering :=
begin
  simp only [functor.is_covering,functor.star_map_comp],
  rintro v,
  rw ←@function.bijective.of_comp_iff' _ _ _ (φ'.star_map $ φ.obj v) (φ'c $ φ.obj v) (φ.star_map v),
  exact φφ'c v,
end
lemma comp'' (φc : φ.is_covering) (φφ'c : (φ ⋙ φ').is_covering) (φsur : function.surjective φ.obj) :
  φ'.is_covering :=
begin
  simp only [functor.is_covering,functor.star_map_comp],
  rintro v,
  obtain ⟨u,rfl⟩ := φsur v,
  rw ←@function.bijective.of_comp_iff _ _ _ (φ'.star_map $ φ.obj u) (φ.star_map u)  (φc u),
  exact φφ'c u,
end


end covering

end groupoid

end category_theory
