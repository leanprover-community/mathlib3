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
Let `B` be the base space. The collection of the fibers is a function `E : B → Type*` for which there
is an appropriate instance on each `E x` and an instance of topological space over `Σ x, E x`.
Naming conventions are essential to work with vector bundles this way.
-/

notation V `ᵛ` R := module.dual R V

variables {B : Type*}

def total_space (E : B → Type*) := Σ x, E x

def vector_bundle.proj (E : B → Type*) : total_space E → B := λ y : (total_space E), y.1

variables (R : Type*) (E : B → Type*) (F : Type*)
  [comm_semiring R] [topological_space B] [∀ x, add_comm_monoid (E x)] [∀ x, topological_space (E x)]
  [∀ x, semimodule R (E x)]
  [topological_space F] [add_comm_monoid F] [semimodule R F]
  [topological_space (total_space E)]

open vector_bundle

/-@[reducible] def dual := (Σ x, (E x)ᵛR)-/

instance is_this_a_good_idea {x : B} : has_coe (E x) (total_space E) := ⟨λ y, (⟨x, y⟩ : total_space E)⟩

structure vector_bundle_trivialization extends bundle_trivialization F (proj E) :=
(linear : ∀ x ∈ base_set, is_linear_map R (λ y : (E x), (to_fun y).2))

instance : has_coe (vector_bundle_trivialization R E F) (bundle_trivialization F (proj E)) :=
⟨vector_bundle_trivialization.to_bundle_trivialization⟩

class topological_vector_bundle :=
(trivialization_at [] : B → (vector_bundle_trivialization R E F))
(mem_trivialization_source [] : ∀ x : total_space E, x ∈ (trivialization_at x.1).source)

variable (B)

def trivial_bundle : B → Type* := λ x, F

def trivial_bundle.proj_snd : (total_space (trivial_bundle B F)) → F := sigma.snd

instance [I : add_comm_monoid F] : ∀ x : B, add_comm_monoid (trivial_bundle B F x) := λ x, I
instance [I : semimodule R F] : ∀ x : B, semimodule R (trivial_bundle B F x) := λ x, I
instance [I : topological_space F] : ∀ x : B, topological_space (trivial_bundle B F x) := λ x, I
instance [t₁ : topological_space B] [t₂ : topological_space F] :
  topological_space (total_space (trivial_bundle B F)) :=
topological_space.induced (proj (trivial_bundle B F)) t₁ ⊓
  topological_space.induced (trivial_bundle.proj_snd B F) t₂

variables {R} {F} {E} {B}

lemma is_topological_vector_bundle_is_topological_fiber_bundle [topological_vector_bundle R E F] :
  is_topological_fiber_bundle F (proj E) :=
λ x, ⟨topological_vector_bundle.trivialization_at R E F x.1,
  topological_vector_bundle.mem_trivialization_source R F x⟩
