/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import topology.topological_fiber_bundle
import analysis.calculus.deriv
import linear_algebra.dual

/-!
# Topological vector bundles

In this file we define topological vector bundles.

I believe it is an enough important concept that it should deserve to be a class, unlike fiber
bundles. The most important idea here is that vector bundles are named through their fibers.
Let `B` be the base space. The collection of the fibers is a function `E : B → Type*` for which
there is an appropriate instance on each `E x` and an instance of topological space over `Σ x, E x`.
Naming conventions are essential to work with vector bundles this way.
-/

notation V `ᵛ` R := module.dual R V

variables {B : Type*}

/--
Type synonim not to have conflict with sigma types. It is the total space of the vector bundle.
-/
def total_space (E : B → Type*) := Σ x, E x

/-- Canonical projection on the base space. -/
def vector_bundle.proj (E : B → Type*) : total_space E → B := λ y : (total_space E), y.1

variables (R : Type*) (E : B → Type*) (F : Type*)
  [comm_semiring R] [topological_space B] [∀ x, add_comm_monoid (E x)]
  [∀ x, topological_space (E x)] [∀ x, semimodule R (E x)]
  [topological_space F] [add_comm_monoid F] [semimodule R F]
  [topological_space (total_space E)]

open vector_bundle

/-@[reducible] def dual := (Σ x, (E x)ᵛR)-/

instance is_this_a_good_idea {x : B} :
  has_coe (E x) (total_space E) := ⟨λ y, (⟨x, y⟩ : total_space E)⟩

/-- Local trivialization for vector bunlde. -/
structure vector_bundle_trivialization extends bundle_trivialization F (proj E) :=
(linear : ∀ x ∈ base_set, is_linear_map R (λ y : (E x), (to_fun y).2))

instance : has_coe (vector_bundle_trivialization R E F) (bundle_trivialization F (proj E)) :=
⟨vector_bundle_trivialization.to_bundle_trivialization⟩

/-- Topological vector bundle of fiber `F`. -/
class topological_vector_bundle :=
(trivialization_at [] : B → (vector_bundle_trivialization R E F))
(mem_trivialization_source [] : ∀ x : total_space E, x ∈ (trivialization_at x.1).source)

variable (B)

/-- Tirvial bundle of fiber `F`. -/
def trivial_bundle : B → Type* := λ x, F

/-- The trivial bundle, unlike other bundles, has a canonical projection on the fiber. -/
def trivial_bundle.proj_snd : (total_space (trivial_bundle B F)) → F := sigma.snd

instance [I : add_comm_monoid F] : ∀ x : B, add_comm_monoid (trivial_bundle B F x) := λ x, I
instance [I : semimodule R F] : ∀ x : B, semimodule R (trivial_bundle B F x) := λ x, I
instance [I : topological_space F] : ∀ x : B, topological_space (trivial_bundle B F x) := λ x, I
instance [t₁ : topological_space B] [t₂ : topological_space F] :
  topological_space (total_space (trivial_bundle B F)) :=
topological_space.induced (proj (trivial_bundle B F)) t₁ ⊓
  topological_space.induced (trivial_bundle.proj_snd B F) t₂

/-- Local trivialization for trivial bundle. -/
def trivial_bundle_trivialization : vector_bundle_trivialization R (trivial_bundle B F) F :=
{ to_fun := λ x, ⟨x.fst, x.snd⟩,
  inv_fun := λ y, ⟨y.fst, y.snd⟩,
  source := set.univ,
  target := set.univ,
  map_source' := λ x h, set.mem_univ (x.fst, x.snd),
  map_target' :=λ y h,  set.mem_univ ⟨y.fst, y.snd⟩,
  left_inv' := λ x h, sigma.eq rfl rfl,
  right_inv' := λ x h, prod.ext rfl rfl,
  open_source := is_open_univ,
  open_target := is_open_univ,
  continuous_to_fun := by { dsimp, rw ← continuous_iff_continuous_on_univ, sorry },
  continuous_inv_fun := by { dsimp, rw ← continuous_iff_continuous_on_univ, sorry },
  base_set := set.univ,
  open_base_set := is_open_univ,
  source_eq := rfl,
  target_eq := by simp only [set.univ_prod_univ],
  proj_to_fun := λ y hy, rfl,
  linear := λ x hx, ⟨λ y z, rfl, λ c y, rfl⟩ }

instance trivial_bundle.topological_vector_bundle :
  topological_vector_bundle R (trivial_bundle B F) F :=
⟨λ x, trivial_bundle_trivialization B R F, λ x, set.mem_univ x⟩

variables {R} {F} {E} {B}

lemma is_topological_vector_bundle_is_topological_fiber_bundle [topological_vector_bundle R E F] :
  is_topological_fiber_bundle F (proj E) :=
λ x, ⟨topological_vector_bundle.trivialization_at R E F x.1,
  topological_vector_bundle.mem_trivialization_source R F x⟩
