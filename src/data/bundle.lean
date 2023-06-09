/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import algebra.module.basic

/-!
# Bundle

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
Basic data structure to implement fiber bundles, vector bundles (maybe fibrations?), etc. This file
should contain all possible results that do not involve any topology.

We represent a bundle `E` over a base space `B` as a dependent type `E : B → Type*`.

We provide a type synonym of `Σ x, E x` as `bundle.total_space E`, to be able to endow it with
a topology which is not the disjoint union topology `sigma.topological_space`. In general, the
constructions of fiber bundles we will make will be of this form.

## Main Definitions

* `bundle.total_space` the total space of a bundle.
* `bundle.total_space.proj` the projection from the total space to the base space.
* `bundle.total_space_mk` the constructor for the total space.

## References
- https://en.wikipedia.org/wiki/Bundle_(mathematics)
-/

namespace bundle

variables {B : Type*} (E : B → Type*)

/--
`bundle.total_space E` is the total space of the bundle `Σ x, E x`.
This type synonym is used to avoid conflicts with general sigma types.
-/
def total_space := Σ x, E x

instance [inhabited B] [inhabited (E default)] :
  inhabited (total_space E) := ⟨⟨default, default⟩⟩

variables {E}

/-- `bundle.total_space.proj` is the canonical projection `bundle.total_space E → B` from the
total space to the base space. -/
@[simp, reducible] def total_space.proj : total_space E → B := sigma.fst

-- this notation won't be used in the pretty-printer
localized "notation `π` := @bundle.total_space.proj _" in bundle

/-- Constructor for the total space of a bundle. -/
@[simp, reducible] def total_space_mk (b : B) (a : E b) :
  bundle.total_space E := ⟨b, a⟩

lemma total_space.proj_mk {x : B} {y : E x} : (total_space_mk x y).proj = x :=
rfl

lemma sigma_mk_eq_total_space_mk {x : B} {y : E x} : sigma.mk x y = total_space_mk x y :=
rfl

lemma total_space.mk_cast {x x' : B} (h : x = x') (b : E x) :
  total_space_mk x' (cast (congr_arg E h) b) = total_space_mk x b :=
by { subst h, refl }

lemma total_space.eta (z : total_space E) :
  total_space_mk z.proj z.2 = z :=
sigma.eta z

instance {x : B} : has_coe_t (E x) (total_space E) := ⟨total_space_mk x⟩

@[simp] lemma coe_fst (x : B) (v : E x) : (v : total_space E).fst = x := rfl
@[simp] lemma coe_snd {x : B} {y : E x} : (y : total_space E).snd = y := rfl

lemma to_total_space_coe {x : B} (v : E x) : (v : total_space E) = total_space_mk x v := rfl

-- notation for the direct sum of two bundles over the same base
notation E₁ ` ×ᵇ `:100 E₂ := λ x, E₁ x × E₂ x

/-- `bundle.trivial B F` is the trivial bundle over `B` of fiber `F`. -/
def trivial (B : Type*) (F : Type*) : B → Type* := function.const B F

instance {F : Type*} [inhabited F] {b : B} : inhabited (bundle.trivial B F b) := ⟨(default : F)⟩

/-- The trivial bundle, unlike other bundles, has a canonical projection on the fiber. -/
def trivial.proj_snd (B : Type*) (F : Type*) : total_space (bundle.trivial B F) → F := sigma.snd

section pullback

variable {B' : Type*}

/-- The pullback of a bundle `E` over a base `B` under a map `f : B' → B`, denoted by `pullback f E`
or `f *ᵖ E`,  is the bundle over `B'` whose fiber over `b'` is `E (f b')`. -/
@[nolint has_nonempty_instance] def pullback (f : B' → B) (E : B → Type*) := λ x, E (f x)

notation f ` *ᵖ ` E := pullback f E

/-- Natural embedding of the total space of `f *ᵖ E` into `B' × total_space E`. -/
@[simp] def pullback_total_space_embedding (f : B' → B) :
  total_space (f *ᵖ E) → B' × total_space E :=
λ z, (z.proj, total_space_mk (f z.proj) z.2)

/-- The base map `f : B' → B` lifts to a canonical map on the total spaces. -/
def pullback.lift (f : B' → B) : total_space (f *ᵖ E) → total_space E :=
λ z, total_space_mk (f z.proj) z.2

@[simp] lemma pullback.proj_lift (f : B' → B) (x : total_space (f *ᵖ E)) :
  (pullback.lift f x).proj = f x.1 :=
rfl

@[simp] lemma pullback.lift_mk (f : B' → B) (x : B') (y : E (f x)) :
  pullback.lift f (total_space_mk x y) = total_space_mk (f x) y :=
rfl

lemma pullback_total_space_embedding_snd (f : B' → B) (x : total_space (f *ᵖ E)) :
  (pullback_total_space_embedding f x).2 = pullback.lift f x :=
rfl

end pullback

section fiber_structures

variable [∀ x, add_comm_monoid (E x)]

@[simp] lemma coe_snd_map_apply (x : B) (v w : E x) :
  (↑(v + w) : total_space E).snd = (v : total_space E).snd + (w : total_space E).snd := rfl

variables (R : Type*) [semiring R] [∀ x, module R (E x)]

@[simp] lemma coe_snd_map_smul (x : B) (r : R) (v : E x) :
  (↑(r • v) : total_space E).snd = r • (v : total_space E).snd := rfl

end fiber_structures

section trivial_instances

variables {F : Type*} {R : Type*} [semiring R] (b : B)

instance [add_comm_monoid F] : add_comm_monoid (bundle.trivial B F b) := ‹add_comm_monoid F›
instance [add_comm_group F] : add_comm_group (bundle.trivial B F b) := ‹add_comm_group F›
instance [add_comm_monoid F] [module R F] : module R (bundle.trivial B F b) := ‹module R F›

end trivial_instances

end bundle
