import data.monoid_algebra
import ring_theory.algebra

universes u

noncomputable theory
open module

variables {k : Type u} [comm_ring k] {G : Type u} [fintype G] [group G]
-- still need an assumption about the characteristic of k before we can complete the proofs!

variables {W : Type u} [add_comm_group W] [module (monoid_algebra k G) W]
variables (V : submodule (monoid_algebra k G) W)

/-!
We now do the key calculation in Maschke's theorem.

Given `V → W`, an inclusion of `k[G]` modules,,
assume we have some splitting `π` of the inclusion `V → W`,
just as as a `k`-linear map.
(This is available cheaply, by choosing a basis.)

We now construct a splitting of the inclusion as a `k[G]`-linear map,
by the formula
$$ \frac{1}{|G|} \sum_{g \mem G} g • π(g⁻¹ • -). $$

There's a certain amount of work afterwards to get all
the formulations of Maschke's theorem you might like
(possibly requiring setting up some infrastructure about semisimplicity,
or abelian categories, depending on the formulation),
but they should all rely on this calculation.
-/

def restrict_scalars (k : Type u) (W : Type u) : Type u := W
instance add_comm_group_restrict_scalars [add_comm_group W] :
  add_comm_group (restrict_scalars k W) := by assumption
instance module_restrict_scalars :
  module k (restrict_scalars k W) :=
(module.restrict_scalars k (monoid_algebra k G) W : module k W)

variables (π : (restrict_scalars k W) →ₗ[k] (restrict_scalars k V))
include π

def conjugate (g : G) : (restrict_scalars k W) →ₗ[k] (restrict_scalars k V) :=
begin
  -- TODO pre- and post-compose
  sorry,
end

def sum_of_conjugates :
  (restrict_scalars k W) →ₗ[k] (restrict_scalars k V) :=
(finset.univ : finset G).sum (conjugate V π)

def sum_of_conjugates_equivariant :
  W →ₗ[monoid_algebra k G] V :=
-- TODO use a `monoid_algebra.equivariant_of` lemma?
sorry

def retraction_of_retraction_res :
  W →ₗ[monoid_algebra k G] V :=
-- TODO divide by #G
sorry

variables (h : ∀ v : V, π ((submodule.subtype V) v) = v)

lemma conjugate_comp_ι_res_eq_id (g : G) :
  ∀ v : V, (conjugate V π g) ((submodule.subtype V) v) = v :=
begin
  sorry
end

lemma retraction_of_retraction_res_condition :
  ∀ v : V, (retraction_of_retraction_res V π) ((submodule.subtype V) v) = v :=
begin
  sorry,
end



-- /--
-- The inclusion of `V` into `monoid_algebra k G`.
-- -/
-- def ι : V →ₗ[monoid_algebra k G] monoid_algebra k G :=
-- submodule.subtype V

-- /--
-- The inclusion of `V` into `monoid_algebra k G`,
-- (i.e., merely as a `k`-linear map).
-- -/
-- def ι_res : (V.restrict_scalars k) →ₗ[k] (monoid_algebra k G) :=
-- (algebra.restrict_scalars_iso k (monoid_algebra k G)).comp (submodule.subtype (V.restrict_scalars k))
-- .
