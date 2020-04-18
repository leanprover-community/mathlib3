import data.monoid_algebra
import ring_theory.algebra

universes u

noncomputable theory

variables {k : Type u} [comm_ring k] {G : Type u} [fintype G] [group G]
-- still need an assumption about the characteristic of k before we can complete the proofs!

variables (V : submodule (monoid_algebra k G) (monoid_algebra k G))

/-!
We now do the key calculation in Maschke's theorem.

Given `V`, a submodule of `k[G]`,
assume we have some splitting `π` of the inclusion `V → k[G]` as a `k`-linear map.
(This is available cheaply, by choosing a basis.)

We now construct a splitting of the inclusion as a `k[G]`-linear map, by the formula
$$ \frac{1}{|G|} \sum_{g \mem G} g • π(g⁻¹ • -). $$

There's a certain amount of work afterwards to get all
the formulations of Maschke's theorem you might like
(possibly requiring setting up some infrastructure about semisimplicity,
or abelian categories, depending on the formulation),
but they should all rely on this calculation.
-/

variables (π : monoid_algebra k G →ₗ[k] V.restrict_scalars k)
include π

def conjugate (g : G) : monoid_algebra k G →ₗ[k] V.restrict_scalars k :=
begin
  -- TODO pre- and post-compose
  sorry,
end

def sum_of_conjugates :
  monoid_algebra k G →ₗ[k] V.restrict_scalars k :=
(finset.univ : finset G).sum (conjugate V π)

def sum_of_conjugates_equivariant :
  monoid_algebra k G →ₗ[monoid_algebra k G] V :=
-- TODO use a `monoid_algebra.equivariant_of` lemma?
sorry

def retraction_of_retraction_res :
  monoid_algebra k G →ₗ[monoid_algebra k G] V :=
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
