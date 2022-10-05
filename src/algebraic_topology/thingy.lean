import algebraic_topology.extra_degeneracy
import algebra.category.Module.adjunctions

universes v u v' u'
noncomputable theory
variables (k : Type u) [comm_ring k]

open category_theory category_theory.category category_theory.limits
open simplicial_object.augmented
open opposite simplex_category
open_locale simplicial

lemma whiskering_δ {C : Type u} [category.{v} C] {D : Type u'} [category.{v'} D] (F : C ⥤ D)
  (s : simplicial_object C) (n : ℕ) (i : fin (n + 2)) :
  (((simplicial_object.whiskering _ _).obj F).obj s).δ i = F.map (s.δ i) :=
rfl

lemma whiskering_σ {C : Type u} [category.{v} C] {D : Type u'} [category.{v'} D] (F : C ⥤ D)
  (s : simplicial_object C) (n : ℕ) (i : fin (n + 1)) :
  (((simplicial_object.whiskering _ _).obj F).obj s).σ i = F.map (s.σ i) :=
rfl

variables {C : Type u} [category.{v} C] {D : Type u'} [category.{v'} D] (F : C ⥤ D)

def category_theory.functor.map_extra_degeneracy
  (s : simplicial_object.augmented C) (ed : extra_degeneracy s) :
  extra_degeneracy (((simplicial_object.augmented.whiskering _ _).obj F).obj s) :=
{ s' := F.map ed.s',
  s := λ n, F.map (ed.s n),
  s'_comp_ε' :=
  begin
    dsimp,
    rw [category.comp_id, ←F.map_comp, ed.s'_comp_ε'],
    exact F.map_id _,
  end,
  s₀_comp_δ₁' :=
  begin
    dsimp,
    simpa only [whiskering_δ, ←F.map_comp, category.comp_id, ←ed.s₀_comp_δ₁'],
  end,
  s_comp_δ₀' := λ n,
  begin
    dsimp,
    simp only [whiskering_δ, ←F.map_comp, ←F.map_id],
    congr,
    exact ed.s_comp_δ₀' _,
  end,
  s_comp_δ' := λ n i,
  begin
    dsimp,
    simp only [whiskering_δ, ←F.map_comp],
    congr' 1,
    exact ed.s_comp_δ' n i,
  end,
  s_comp_σ' := λ n i,
  begin
    dsimp,
    simp only [whiskering_σ, ←F.map_comp],
    congr' 1,
    exact ed.s_comp_σ' n i,
  end }
