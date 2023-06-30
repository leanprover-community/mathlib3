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

We define `bundle.total_space F E` to be the type of pairs `⟨b, x⟩`, where `b : B` and `x : E x`.
This type is isomorphic to `Σ x, E x` and uses an extra argument `F` for reasons explained below. In
general, the constructions of fiber bundles we will make will be of this form.

## Main Definitions

* `bundle.total_space` the total space of a bundle.
* `bundle.total_space.proj` the projection from the total space to the base space.
* `bundle.total_space.mk` the constructor for the total space.

## Implementation Notes

- We use a custom structure for the total space of a bundle instead of using a type synonym for the
  canonical disjoint union `Σ x, E x` because the total space usually has a different topology and
  Lean 4 `simp` fails to apply lemmas about `Σ x, E x` to elements of the total space.

- The definition of `bundle.total_space` has an unused argument `F`. The reason is that in some
  constructions (e.g., `bundle.continuous_linear_map.vector_bundle`) we need access to the atlas of
  trivializations of original fiber bundles to construct the topology on the total space of the new
  fiber bundle.

## References
- https://en.wikipedia.org/wiki/Bundle_(mathematics)
-/

namespace bundle

variables {B F : Type*} (E : B → Type*)

/--
`bundle.total_space E` is the total space of the bundle. It consists of pairs
`(proj : B, snd : E proj)`.
-/
@[ext]
structure total_space (F : Type*) (E : B → Type*) :=
(proj : B)
(snd : E proj)

instance [inhabited B] [inhabited (E default)] :
  inhabited (total_space F E) := ⟨⟨default, default⟩⟩

variables {E}

/-- `bundle.total_space.proj` is the canonical projection `bundle.total_space E → B` from the
total space to the base space. -/
add_decl_doc total_space.proj

-- this notation won't be used in the pretty-printer
localized "notation `π` := @bundle.total_space.proj _" in bundle

-- TODO: try `abbrev` in Lean 4
localized "notation `total_space.mk'` F:max := @bundle.total_space.mk _ F _" in bundle

lemma total_space.mk_cast {x x' : B} (h : x = x') (b : E x) :
  total_space.mk' F x' (cast (congr_arg E h) b) = total_space.mk x b :=
by { subst h, refl }

instance {x : B} : has_coe_t (E x) (total_space F E) := ⟨total_space.mk x⟩

@[simp] lemma total_space.coe_proj (x : B) (v : E x) : (v : total_space F E).proj = x := rfl
@[simp] lemma total_space.coe_snd {x : B} {y : E x} : (y : total_space F E).snd = y := rfl

lemma total_space.coe_eq_mk {x : B} (v : E x) : (v : total_space F E) = total_space.mk x v := rfl

lemma total_space.eta (z : total_space F E) :
  total_space.mk z.proj z.2 = z :=
by cases z; refl

-- notation for the direct sum of two bundles over the same base
notation E₁ ` ×ᵇ `:100 E₂ := λ x, E₁ x × E₂ x

/-- `bundle.trivial B F` is the trivial bundle over `B` of fiber `F`. -/
@[reducible]
def trivial (B : Type*) (F : Type*) : B → Type* := λ _, F

/-- The trivial bundle, unlike other bundles, has a canonical projection on the fiber. -/
def total_space.trivial_snd (B : Type*) (F : Type*) : total_space F (bundle.trivial B F) → F :=
total_space.snd

/-- A trivial bundle is equivalent to the product `B × F`. -/
@[simps { attrs := [`simp, `mfld_simps] }]
def total_space.to_prod (B F : Type*) : total_space F (λ _ : B, F) ≃ B × F :=
{ to_fun := λ x, (x.1, x.2),
  inv_fun := λ x, ⟨x.1, x.2⟩,
  left_inv := λ ⟨_, _⟩, rfl,
  right_inv := λ ⟨_, _⟩, rfl }

section pullback

variable {B' : Type*}

/-- The pullback of a bundle `E` over a base `B` under a map `f : B' → B`, denoted by `pullback f E`
or `f *ᵖ E`,  is the bundle over `B'` whose fiber over `b'` is `E (f b')`. -/
def pullback (f : B' → B) (E : B → Type*) : B' → Type* := λ x, E (f x)

notation f ` *ᵖ ` E:max := pullback f E

instance {f : B' → B} {x : B'} [nonempty (E (f x))] : nonempty (f *ᵖ E x) := ‹nonempty (E (f x))›

/-- Natural embedding of the total space of `f *ᵖ E` into `B' × total_space E`. -/
@[simp] def pullback_total_space_embedding (f : B' → B) :
  total_space F (f *ᵖ E) → B' × total_space F E :=
λ z, (z.proj, total_space.mk (f z.proj) z.2)

/-- The base map `f : B' → B` lifts to a canonical map on the total spaces. -/
@[simps { attrs := [`simp, `mfld_simps] }]
def pullback.lift (f : B' → B) : total_space F (f *ᵖ E) → total_space F E :=
λ z, ⟨f z.proj, z.2⟩

@[simp, mfld_simps] lemma pullback.lift_mk (f : B' → B) (x : B') (y : E (f x)) :
  pullback.lift f (total_space.mk' F x y) = ⟨f x, y⟩ :=
rfl

end pullback

section fiber_structures

@[simp] lemma coe_snd_map_apply [∀ x, has_add (E x)] (x : B) (v w : E x) :
  (↑(v + w) : total_space F E).snd = (v : total_space F E).snd + (w : total_space F E).snd := rfl

@[simp] lemma coe_snd_map_smul {R} [∀ x, has_smul R (E x)] (x : B) (r : R) (v : E x) :
  (↑(r • v) : total_space F E).snd = r • (v : total_space F E).snd := rfl

end fiber_structures

end bundle
