/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.sheaf
import topology.sheaves.stalks

universes v u

open category_theory
open category_theory.limits
open topological_space
open topological_space.opens
open Top.presheaf
open opposite

namespace Top

variables {X : Top.{v}} (F G : sheaf (Type v) X) (f : F ⟶ G)

lemma foo (U : opens X) (x : U) (inj : function.injective ((stalk_functor (Type v) (x : X)).map f))
  (s t : F.presheaf.obj (op U)) (w : G.presheaf.germ x (f.app (op U) s) = G.presheaf.germ x (f.app (op U) t)) :
  ∃ (V : opens X) (i : V ⟶ U) (m : (x : X) ∈ V), F.presheaf.map i.op s = F.presheaf.map i.op t :=
sorry

/--
A morphism of sheaves is injective on every stalk if and only if it is a monomorphism.

-/
def mono_stalkwise : mono f ↔ ∀ x, function.injective ((stalk_functor (Type v) x).map f) :=
begin
  fsplit,
  sorry, -- easy?
  intro i,
  fsplit,
  intros H g h w,
  ext1, ext1 U, op_induction U, ext x,

  let 𝒰 : cover U := { ι := U, 𝒰 := _, supr := _, le_supr := _, }, -- postpone picking a cover
  have is_limit := F.is_limit_of_cover 𝒰,
  have mono := mono_of_is_limit_parallel_pair is_limit,
  rw mono_iff_injective at mono,
  dsimp [function.injective] at mono,
  apply mono,
  dsimp [cover.fork],
  dsimp [sheaf_condition.res],

  apply types.limit_ext, -- make this work by simp?
  intro i,
  simp,

end

def epi_stalkwise : epi f ↔ ∀ x, function.surjective ((stalk_functor (Type v) x).map f) :=
sorry

def is_iso_stalkwise : is_iso f ≃ ∀ x, function.bijective ((stalk_functor (Type v) x).map f) :=
sorry

end Top
