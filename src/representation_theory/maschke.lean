/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import algebra.monoid_algebra
import algebra.invertible
import algebra.char_p
import linear_algebra.basis

/-!
# Maschke's theorem

We prove Maschke's theorem for finite groups,
in the formulation that every submodule of a `k[G]` module has a complement,
when `k` is a field with `¬(ring_char k ∣ fintype.card G)`.

We do the core computation in greater generality.
For any `[comm_ring k]` in which  `[invertible (fintype.card G : k)]`,
and a `k[G]`-linear map `i : V → W` which admits a `k`-linear retraction `π`,
we produce a `k[G]`-linear retraction by
taking the average over `G` of the conjugates of `π`.

## Future work
It's not so far to give the usual statement, that every finite dimensional representation
of a finite group is semisimple (i.e. a direct sum of irreducibles).
-/

universes u

noncomputable theory
open semimodule
open monoid_algebra
open_locale big_operators

section

-- At first we work with any `[comm_ring k]`, and add the assumption that
-- `[invertible (fintype.card G : k)]` when it is required.
variables {k : Type u} [comm_ring k] {G : Type u} [group G]

variables {V : Type u} [add_comm_group V] [module (monoid_algebra k G) V]
variables {W : Type u} [add_comm_group W] [module (monoid_algebra k G) W]

/-!
We now do the key calculation in Maschke's theorem.

Given `V → W`, an inclusion of `k[G]` modules,,
assume we have some retraction `π` (i.e. `∀ v, π (i v) = v`),
just as a `k`-linear map.
(When `k` is a field, this will be available cheaply, by choosing a basis.)

We now construct a retraction of the inclusion as a `k[G]`-linear map,
by the formula
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/

variables (π : (restrict_scalars k (monoid_algebra k G) W) →ₗ[k]
               (restrict_scalars k (monoid_algebra k G) V))
include π

/--
We define the conjugate of `π` by `g`, as a `k`-linear map.
-/
def conjugate (g : G) :
  (restrict_scalars k (monoid_algebra k G) W) →ₗ[k] (restrict_scalars k (monoid_algebra k G) V) :=
((group_smul.linear_map k V g⁻¹).comp π).comp (group_smul.linear_map k W g)

variables (i : V →ₗ[monoid_algebra k G] W) (h : ∀ v : V, π (i v) = v)

section
include h

lemma conjugate_i (g : G) (v : V) : (conjugate π g) (i v) = v :=
begin
  dsimp [conjugate],
  simp only [←i.map_smul, h, ←mul_smul, single_mul_single, mul_one, mul_left_inv],
  change (1 : monoid_algebra k G) • v = v,
  simp,
end
end

variables [fintype G]

/--
The sum of the conjugates of `π` by each element `g : G`, as a `k`-linear map.

(We postpone dividing by the size of the group as long as possible.)
-/
def sum_of_conjugates :
  (restrict_scalars k (monoid_algebra k G) W) →ₗ[k] (restrict_scalars k (monoid_algebra k G) V) :=
∑ g : G, conjugate π g

/--
In fact, the sum over `g : G` of the conjugate of `π` by `g` is a `k[G]`-linear map.
-/
def sum_of_conjugates_equivariant :
  W →ₗ[monoid_algebra k G] V :=
monoid_algebra.equivariant_of_linear_of_comm (sum_of_conjugates π) (λ g v,
begin
  dsimp [sum_of_conjugates],
  simp only [linear_map.sum_apply, finset.smul_sum],
  dsimp [conjugate],
  conv_lhs {
    rw [←finset.univ_map_embedding (mul_right_embedding g⁻¹)],
    simp only [mul_right_embedding],
  },
  simp only [←mul_smul, single_mul_single, mul_inv_rev, mul_one, function.embedding.coe_fn_mk,
    finset.sum_map, inv_inv, inv_mul_cancel_right],
end)

section
variables [inv : invertible (fintype.card G : k)]
include inv

section
local attribute [instance] linear_map_algebra_module
/--
We construct our `k[G]`-linear retraction of `i` as
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/
def equivariant_projection :
  W →ₗ[monoid_algebra k G] V :=
⅟(fintype.card G : k) • (sum_of_conjugates_equivariant π)
end

include h

lemma equivariant_projection_condition (v : V) : (equivariant_projection π) (i v) = v :=
begin
  rw [equivariant_projection, linear_map_algebra_module.smul_apply, sum_of_conjugates_equivariant,
    equivariant_of_linear_of_comm_apply, sum_of_conjugates],
  rw [linear_map.sum_apply],
  simp only [conjugate_i π i h],
  rw [finset.sum_const, finset.card_univ,
    @semimodule.nsmul_eq_smul k _
      (restrict_scalars k (monoid_algebra k G) V) _ _ (fintype.card G) v,
    ←mul_smul, invertible.inv_of_mul_self, one_smul],
end
end
end

-- Now we work over a `[field k]`, and replace the assumption `[invertible (fintype.card G : k)]`
-- with `¬(ring_char k ∣ fintype.card G)`.
variables {k : Type u} [field k] {G : Type u} [fintype G] [group G]
variables {V : Type u} [add_comm_group V] [module (monoid_algebra k G) V]
variables {W : Type u} [add_comm_group W] [module (monoid_algebra k G) W]

lemma monoid_algebra.exists_left_inverse_of_injective
  (not_dvd : ¬(ring_char k ∣ fintype.card G))
  (f : V →ₗ[monoid_algebra k G] W) (hf_inj : f.ker = ⊥) :
  ∃ (g : W →ₗ[monoid_algebra k G] V), g.comp f = linear_map.id :=
begin
  let E := linear_map.exists_left_inverse_of_injective
    (by convert f.restrict_scalars k) (by simp [hf_inj]),
  fsplit,
  haveI : invertible (fintype.card G : k) :=
    invertible_of_ring_char_not_dvd not_dvd,
  exact equivariant_projection (classical.some E),
  { ext v,
    apply equivariant_projection_condition,
    intro v,
    have := classical.some_spec E,
    have := congr_arg linear_map.to_fun this,
    exact congr_fun this v, }
end

lemma monoid_algebra.submodule.exists_is_compl
  (not_dvd : ¬(ring_char k ∣ fintype.card G)) (p : submodule (monoid_algebra k G) V) :
  ∃ q : submodule (monoid_algebra k G) V, is_compl p q :=
let ⟨f, hf⟩ := monoid_algebra.exists_left_inverse_of_injective not_dvd p.subtype p.ker_subtype in
⟨f.ker, linear_map.is_compl_of_proj $ linear_map.ext_iff.1 hf⟩
