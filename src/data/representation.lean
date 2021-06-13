/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.monoid_algebra
import linear_algebra.basic
import ring_theory.algebra

/-!
# Representations

For a monoid G and a commutative ring k, there are many equivalent ways of talking about
k-linear G-representations.

1. As a typeclass `representation k G M`, extending `distrib_mul_action G M`
  (which we introduce here).
2. As a `module (monoid_algebra k G) M`.
3. As a multiplicative function `G →* (M →ₗ[k] M)`.
4. As a multiplicative function `k × G →* (M →+ M)`
  (although note we haven't installed a monoid structure on `M →+ M` at this point).
5. As a k-algebra morphism `monoid_algebra (k G) →ₐ[k] (M →ₗ[k] M)`.

(Note the slight subtlety here that in points 1., 3., and 5. there is a "background" k-module
structure, while in points 2. and 4. the presented data determines the k-module structure.
For that matter, at this point we haven't even described the equivalence
`module k M ≃ (k →* (M →+ M))`.
In this file we define the typeclass `representation k G M`, and provide the functions
```
representation.as_monoid_hom [representation k G M] : G →* (M →ₗ[k] M)
of_monoid_hom (ρ : G →* (M →ₗ[k] M)) : representation k G M
```
(addressing the equivalence between 1. and 3. above)
and the functions
```
extend_scalars [representation k G M] : module (monoid_algebra k G) M
representation.of_monoid_algebra_module [module (monoid_algebra k G) M] : representation k G M
```
(where the second function provides the `representation k G M` relative to the `module k M`
coming from `restrict_scalars k (monoid_algebra k G) M`).
These provide the equivalence between 1. and 2. above.

The function `monoid_algebra.lift` in `data.monoid_algebra` then provides the equivalence
between 3. and 5.

(There's obviously a quite direct connection between points 2. and 5. above,
which hasn't been developed yet.)

(We don't yet say anything about point 4. above; perhaps it's less useful.)

Finally, note that really all of these equivalences should be done as equivalences of categories,
not just functions back and forth.
We'll get there in a later file!

## Tags

linear action, representation
-/

universes u v w

section prio
set_option default_priority 100 -- see Note [default priority]
/--
A k-linear representation of a group G.
-/
class representation
  (k : out_param $ Type v) [comm_ring k] (G : Type u) [monoid G] (M : Type w) [add_comm_group M] [module k M]
  extends distrib_mul_action G M : Type (max u v w) :=
(smul_smul : ∀ (g : G) (r : k) (m : M), g • (r • m) = r • (g • m))

-- k is an `out_param`, so this is a false positive.
attribute [nolint dangerous_instance] representation.to_distrib_mul_action

end prio

section
variables {k : Type v} {G : Type u} {M : Type w}
variables [comm_ring k] [monoid G] [add_comm_group M] [module k M]

/-- A group element acts by an k-linear map in any k-linear representation. -/
def smul.linear_map [representation k G M] (g : G) : M →ₗ[k] M :=
{ to_fun := λ m, g • m,
  add := λ m m', by simp [smul_add],
  smul := λ r m, by simp [representation.smul_smul], }

@[simp]
lemma smul.linear_map_apply [representation k G M] (g : G) (m : M) :
  (smul.linear_map g : M →ₗ[k] M) m = g • m := rfl
end

namespace representation
variables (k : Type v) (G : Type u)
variables [comm_ring k] [monoid G]
variables (M : Type w) [add_comm_group M] [module k M]

/--
A k-linear representation of G on M can be thought of as
a multiplicative map from G into the k-linear endomorphisms of M.
-/
def as_monoid_hom [representation k G M] : G →* (M →ₗ[k] M) :=
{ to_fun := λ g, smul.linear_map g,
  map_one' := by { ext, simp, },
  map_mul' := λ g g', by { ext, simp [mul_smul], }, }

@[simp]
lemma as_monoid_hom_apply_apply [representation k G M] (g : G) (m : M) :
  (as_monoid_hom k G M) g m = g • m := rfl

variables {k G M}

/--
We get a k-linear representation of G on M from
a multiplicative map from G into the k-linear endomorphisms of M.
-/
def of_monoid_hom (ρ : G →* (M →ₗ[k] M)) : representation k G M :=
{ smul := λ g m, ρ g m,
  one_smul := λ m, by { simp, erw [monoid_hom.map_one ρ], simp, }, -- FIXME: anyone know why we need `erw`?
  mul_smul := λ g g' m, by { simp, erw [monoid_hom.map_mul ρ], simp, }, -- FIXME: here to
  smul_zero := λ g, by { simp, },
  smul_add := λ g m m', by { simp, },
  smul_smul := λ g r m, by { simp, }, }

end representation

section

variables (k : Type v) (G : Type u)
variables [comm_ring k] [group G]

/-- The trivial k-linear representation of G on k. -/
@[derive [add_comm_group, module k], nolint unused_arguments]
def trivial_representation (k : Type v) [comm_ring k] (G : Type u) [group G] := k

instance : inhabited (trivial_representation k G) := ⟨0⟩

instance : representation k G (trivial_representation k G) :=
by refine_struct { smul := λ g m, m, .. }; simp

noncomputable theory

/-- The regular representation of G on `monoid_algebra k G`. -/
-- We provide a type synonym here precisely to forget all the other type classes available
-- on `monoid_algebra`!
@[derive [add_comm_group, module k, distrib_mul_action G, inhabited], nolint unused_arguments]
def regular_representation := monoid_algebra k G

-- Check that we didn't pick 37.
example : default (regular_representation k G) = 0 := rfl

instance :
  representation k G (regular_representation k G) :=
{ smul_smul := λ g r m, by { ext g', simp, } }

end

namespace representation
namespace extend_scalars
variables {k : Type v} {G : Type u}
variables [comm_ring k] [group G]
variables (M : Type w) [add_comm_group M] [module k M] [representation k G M]

/-- (Implementation detail). The action of `monoid_algebra k G` on a k-linear G-representation. -/
def monoid_algebra_has_scalar : has_scalar (monoid_algebra k G) M :=
{ smul := λ f v, f.sum (λ g r, r • (g • v)), }

local attribute [instance] monoid_algebra_has_scalar

lemma one_smul (m : M) : (1 : monoid_algebra k G) • m = m :=
begin
  dsimp [(•)],
  change finsupp.sum (finsupp.single _ _) _ = _,
  rw finsupp.sum_single_index; simp,
end

lemma zero_smul (m : M) : (0 : monoid_algebra k G) • m = 0 :=
by { dsimp [(•)], simp, }

lemma smul_zero (x : monoid_algebra k G) : x • (0 : M) = 0 :=
by { dsimp [(•)], simp, }

lemma add_smul (x y : monoid_algebra k G) (m : M) : (x + y) • m = x • m + y • m :=
begin
  dsimp [(•)],
  rw [finsupp.sum_add_index],
  { simp, },
  { intros g r₁ r₂, simp [add_smul], }
end

lemma sum_smul (x : monoid_algebra k G) (f : G → k → monoid_algebra k G) (m : M) :
  (finsupp.sum x f) • m = finsupp.sum x (λ g r, f g r • m) :=
begin
  convert add_monoid_hom.map_finsupp_sum x f ⟨λ r, r • m, _, _⟩,
  { simp [zero_smul], },
  { simp [add_smul], },
end

-- This is the only real work.
-- (... and a pity it looks so unlike the pen and paper proof!)
lemma mul_smul (x y : monoid_algebra k G) (m : M) : (x * y) • m = x • y • m :=
begin
  simp only [monoid_algebra.mul_def, sum_smul],
  dsimp only [(•)],
  congr, funext,
  change _ = (smul.add_monoid_hom r M) ((smul.add_monoid_hom g M) _),
  simp only [add_monoid_hom.map_finsupp_sum],
  congr, funext,
  rw [finsupp.sum_single_index],
  { simp [mul_smul, smul_smul], },
  { simp, },
end

lemma smul_add (x : monoid_algebra k G) (m m' : M) : x • (m + m') = x • m + x • m' :=
by { dsimp [(•)], simp [smul_add], }

end extend_scalars

open extend_scalars
variables (k : Type v) (G : Type u)
variables [comm_ring k] [group G]
section
variables (M : Type w) [add_comm_group M] [module k M] [representation k G M]

/-- Any k-linear G-representation gives a `monoid_algebra k G` module. -/
def extend_scalars : module (monoid_algebra k G) M :=
{ one_smul := λ m, one_smul M m,
  mul_smul := λ x y m, mul_smul M x y m,
  add_smul := λ x y m, add_smul M x y m,
  smul_add := λ x m m', smul_add M x m m',
  zero_smul := λ m, zero_smul M m,
  smul_zero := λ x, smul_zero M x,
  ..extend_scalars.monoid_algebra_has_scalar M }
end

section
variables (M : Type w) [add_comm_group M] [module (monoid_algebra k G) M]

/--
The k-module structure coming from a `monoid_algebra k G` module structure by
restriction of scalars.

Design note: in fact, I'm tempted to introduce `algebra_module A M`,
which requires an existing `[module k M]`, and requires that elements of k act
(when thought of as elements of A) in the specified way.
-/
def module_of_monoid_algebra_module : module k M := module.restrict_scalars k (monoid_algebra k G) M

local attribute [instance] module_of_monoid_algebra_module

@[simp]
lemma restrict_scalars (r : k) (m : M) : (r • m) = (monoid_algebra.single (1 : G) r) • m := rfl

/-- Scalar multiplication by a group element, given a `monoid_algebra k G` module structure. -/
def has_scalar_of_monoid_algebra_module : has_scalar G M :=
{ smul := λ g m, (monoid_algebra.single g (1 : k)) • m, }

local attribute [instance] has_scalar_of_monoid_algebra_module

/--
Scalar multiplication by a group element, given a `monoid_algebra k G` module structure,
is multiplicative in the first argument.
-/
def mul_action_of_monoid_algebra_module : mul_action G M :=
{ one_smul := λ m, by { change (1 : monoid_algebra k G) • m = m, simp, },
  mul_smul := λ g g' m,
  by { dsimp [(•)], simp [←mul_action.mul_smul, monoid_algebra.single_mul_single], },
  ..representation.has_scalar_of_monoid_algebra_module k G M }.

local attribute [instance] has_scalar_of_monoid_algebra_module

/--
Scalar multiplication by a group element, given a `monoid_algebra k G` module structure,
is additive in the second argument.
-/
def distrib_mul_action_of_monoid_algebra_module : distrib_mul_action G M :=
{ smul_zero := λ g, begin dsimp, erw [distrib_mul_action.smul_zero], end,
  smul_add := λ g m m', begin dsimp, erw [distrib_mul_action.smul_add], refl, end,
  ..representation.mul_action_of_monoid_algebra_module k G M}.

local attribute [instance] distrib_mul_action_of_monoid_algebra_module

@[simp]
lemma group_action (g : G) (m : M) :
  g • m = (monoid_algebra.single g (1 : k)) • m :=
rfl

/--
A `monoid_algebra k G` structure gives us a multiplicative map `G →* (M →ₗ[k] M)`.
-/
def action_of_monoid_algebra_module : G →* (M →ₗ[k] M) :=
{ to_fun := λ g, linear_map.of_add_monoid_hom (smul.add_monoid_hom g M)
    (λ r m, by simp [←mul_action.mul_smul, monoid_algebra.single_one_mul_comm]),
  map_one' := by { ext, change (1 : monoid_algebra k G) • x = x, simp, },
  map_mul' := λ g h, by { ext, simp [←mul_action.mul_smul, monoid_algebra.single_mul_single], }, }

@[simp]
lemma action_of_monoid_algebra_module_apply_apply (g : G) (m : M) :
  (action_of_monoid_algebra_module k G M g : M → M) m = (monoid_algebra.single g (1 : k)) • m :=
rfl

/--
A `monoid_algebra k G` module structure on `M` gives a `representation k G M`.

Note that this is relative to the k-module structure
`module.restrict_scalars k (monoid_algebra k G) M`.
-/
def of_monoid_algebra_module : representation k G M :=
representation.of_monoid_hom (action_of_monoid_algebra_module k G M)

-- We should prove that `of_monoid_algebra_module` and `extend_scalars`
-- form an equivalence of categories, but let's wait until we have the bundled categories
-- available, and some automation.

end
end representation
