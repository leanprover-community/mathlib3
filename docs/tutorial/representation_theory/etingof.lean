/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.simple
import category_theory.subobject.basic
import category_theory.preadditive.schur
import algebra.algebra.restrict_scalars
import algebra.algebra.tower
import algebra.category.Module.algebra
import algebra.category.Module.images
import algebra.category.Module.biproducts
import algebra.category.Module.simple
import data.mv_polynomial.basic
import algebra.free_algebra
import data.complex.module

/-!
# "Introduction to representation theory" by Etingof

This tutorial file follows along with the lecture notes "Introduction to representation theory",
by Pavel Etingof and other contributors.

These lecture notes are available freely online at <https://klein.mit.edu/~etingof/repb.pdf>.

This tutorial is (extremely) incomplete at present.
The goal is to work through the lecture notes,
showing how to use the definitions and results from mathlib
to establish the results in Etingof's notes. (We are not giving separate proofs here!)

Our intention is (sadly) to skip all the problems, and many of the examples.

Often results are proved by reference to (much) more general facts in mathlib.
-/

axiom skipped {p : Sort*} : p

universes u
open category_theory finite_dimensional

noncomputable theory

/-!
## Chapter 2 "Basic notions of representation theory"
-/

/-!
### 2.2 "Algebras"
-/

-- Definition 2.2.1: An associative algebra.
variables {k : Type*} [field k]
variables {A : Type*} [ring A] [algebra k A]

-- Etingof uses the word "unit" to refer to the identity in an algebra.
-- Currently in mathlib all algebras are unital
-- (although non-unital rings exists as `non_unital_ring`)
-- Thus we skip Definition 2.2.2 and Proposition 2.2.3

-- Example 2.2.4 (1)-(5)
example : algebra k k := by apply_instance
example {X : Type*} [fintype X] : algebra k (mv_polynomial X k) := by apply_instance
example {V : Type*} [add_comm_group V] [module k V] : algebra k (V →ₗ[k] V) := by apply_instance
example {X : Type*} : algebra k (free_algebra k X) := by apply_instance
example {G : Type*} [group G] : algebra k (monoid_algebra k G) := by apply_instance

-- Definition 2.2.5: A commutative algebra is described as:
example {A : Type*} [comm_ring A] [algebra k A] := true

-- Definition 2.2.6: algebra homomorphisms:
example {B : Type*} [ring B] [algebra k B] (f : A →ₐ[k] B) := true

/-!
## 2.3 "Representations"
-/

-- Definition 2.3.1
-- A representation (of an associative algebra) will usually be described as a module.
variables {M : Type*} [add_comm_group M] [module k M] [module A M] [is_scalar_tower k A M]

-- or we can use `Module A`, for a "bundled" `A`-module,
-- which is useful when we want access to the category theory library.
variables (N : Module.{u} A)

-- We can translate between these easily:
-- "bundle" a type with appropriate typeclasses
example : Module A := Module.of A M
-- a "bundled" module has a coercion to `Type`,
-- that comes equipped with the appropriate typeclasses:
example : module A N := by apply_instance

-- Remark 2.3.2: Right `A`-modules are handled as left `Aᵐᵒᵖ`-modules:
example : Module Aᵐᵒᵖ := Module.of Aᵐᵒᵖ A
-- Right modules are not extensively developed in mathlib at this point,
-- and you may run into difficulty using them.

-- It is helpful when working with `Module` to run
open_locale Module
-- which adds some instances.

-- Example 2.3.3
-- (1) The zero module
example : Module A := Module.of A punit
-- (2) The left regular module
example : Module A := Module.of A A
-- (3) Modules over a field are vector spaces.
-- (Because we handle vector spaces as modules in mathlib, this is empty of content.)
example (V : Type*) [add_comm_group V] [module k V] : Module k := Module.of k V
-- (4) is trickier,
-- and we would probably want to formalise as an equivalence of categories,
-- because "it's hard to get back to where we started".
example (X : Type*) : Module (free_algebra k X) ≃ Σ (V : Module k), X → (V ⟶ V) := skipped

-- Definition 2.3.4
-- A subrepresentation can be described using `submodule`,
variables (S : submodule A M)
-- or using the category theory library either as a monomorphism
variables (S' : Module.{u} A) (i : S' ⟶ N) [mono i]
-- or a subobject (defined as an isomorphism class of monomorphisms)
variables (S'' : subobject N)

-- Definition 2.3.5: We express that a representation is "irreducible" using `simple`.
example (N : Module A) : Prop := simple N
-- there's also a predicate for unbundled modules:
example : simple (Module.of A M) ↔ is_simple_module A M := simple_iff_is_simple_module

-- Definition 2.3.6: homomorphisms, intertwiners, isomorphisms
-- For unbundled representations, we use linear maps:
variables {M' : Type*} [add_comm_group M'] [module k M'] [module A M'] [is_scalar_tower k A M']
variables (f : M →ₗ[A] M')
-- while for bundled representations we use the categorical morphism arrow:
variables (N₁ N₂ : Module.{u} A) (g : N₁ ⟶ N₂)
-- For isomorphisms, use one of
variables (e : M ≃ₗ[A] M') (j : N₁ ≅ N₂)

-- Definition 2.3.7: direct sum
example : module A (M × M') := by apply_instance
example (N₁ N₂ : Module.{u} A) : Module.{u} A := N₁ ⊞ N₂
example (N₁ N₂ : Module.{u} A) : N₁ ⊞ N₂ ≅ Module.of A (N₁ × N₂) := Module.biprod_iso_prod N₁ N₂

-- Definition 2.3.8: indecomposable
example (N : Module A) : Prop := indecomposable N
example (N : Module A) [simple N] : indecomposable N := indecomposable_of_simple N

-- Proposition 2.3.9 (Schur's lemma)
example (N₁ N₂ : Module.{u} A) [simple N₁] (f : N₁ ⟶ N₂) (w : f ≠ 0) : mono f :=
mono_of_nonzero_from_simple w
example (N₁ N₂ : Module.{u} A) [simple N₂] (f : N₁ ⟶ N₂) (w : f ≠ 0) : epi f :=
epi_of_nonzero_to_simple w
example (N₁ N₂ : Module.{u} A) [simple N₁] [simple N₂] (f : N₁ ⟶ N₂) (w : f ≠ 0) : is_iso f :=
is_iso_of_hom_simple w

-- Corollary 2.3.10 (Schur's lemma over an algebraically closed field)
-- Unfortunately these can't be global instances
example [is_alg_closed k] (V : Module.{u} A) [simple V] [finite_dimensional k V] (f : V ⟶ V) :
  ∃ φ : k, φ • 𝟙 V = f :=
endomorphism_simple_eq_smul_id k f
-- Note that some magic is going on behind the scenes in this proof.
-- We're using a version of Schur's lemma that applies to any `k`-linear category,
-- and its hypotheses include `finite_dimensional k (V ⟶ V)`
-- rather than `finite_dimensional k V` (because `V` need not even be a vector space).
-- Typeclass inference is automatically generating this fact.

-- Remark 2.3.11 (Schur's lemma doesn't hold over a non-algebraically closed field)
example : simple (Module.of ℂ ℂ) := simple_of_finrank_eq_one (finrank_self ℂ)
example : finite_dimensional ℝ (Module.of ℂ ℂ) := by { dsimp, apply_instance, }
example :
  let V := Module.of ℂ ℂ in
  ∃ (f : V ⟶ V), ∀ φ : ℝ, (φ : ℂ) • 𝟙 V ≠ f :=
⟨algebra.lsmul ℂ ℂ complex.I,
  λ φ w, by simpa using congr_arg complex.im (linear_map.congr_fun w (1 : ℂ))⟩

-- Corollary 2.3.12
-- Every irreducible finite dimensional representation of a commutative algebra is 1-dimensional
example (A : Type*) [comm_ring A] [algebra k A] (V : Module A) [finite_dimensional k V] [simple V] :
  finrank k V = 1 :=
skipped

-- Remark 2.3.13: Every 1-dimensional representation is irreducible
example (V : Module A) [finite_dimensional k V] (h : finrank k V = 1) : simple V :=
simple_of_finrank_eq_one h

-- Example 2.3.14: skipped (1 and 3 we can do, 2 requires Jordan normal form)

/-!
## 2.4 "Ideals"
-/

-- To be continued...
