import data.monoid_algebra
import ring_theory.algebra
import algebra.invertible

universes u

def mul_right_embedding {G : Type*} [group G] (g : G) : G ↪ G :=
{ to_fun := λ h, h * g,
  inj' := λ h h', (mul_left_inj g).mp, }

noncomputable def function.embedding.equiv_of_fintype_endomorphism {α : Type*} [fintype α] (e : α ↪ α) : α ≃ α :=
begin
  apply function.embedding.equiv_of_surjective e _,
  apply (fintype.injective_iff_surjective_of_equiv (equiv.refl α)).mp _,
  exact function.embedding.inj e,
end

@[simp]
lemma function.embedding.equiv_of_fintype_endomorphism_to_embedding {α : Type*} [fintype α] (e : α ↪ α) :
  (e.equiv_of_fintype_endomorphism).to_embedding = e :=
by { ext, refl, }

@[simp]
lemma finset.univ_map_equiv_to_embedding {α : Type*} [fintype α] (e : α ≃ α) :
  (finset.univ).map e.to_embedding = finset.univ :=
begin
  ext,
  split,
  { intro h,
    simp, },
  { intro h,
    rw [finset.mem_map],
    use e.symm a,
    simp, },
end

lemma finset.univ_map_embedding {α : Type*} [fintype α] (e : α ↪ α) : (finset.univ).map e = finset.univ :=
begin
  rw ←e.equiv_of_fintype_endomorphism_to_embedding,
  apply finset.univ_map_equiv_to_embedding,
end

section
variables (R : Type*) [comm_ring R] (S : Type*) [ring S] [algebra R S]
  (V : Type*) [add_comm_group V] [module S V]
  (W : Type*) [add_comm_group W] [module S W]

local attribute [instance] linear_map_algebra_module

variables {R S V W}
@[simp]
lemma linear_map_algebra_module.smul_apply (c : R) (f : V →ₗ[S] W) (v : V) :
  (c • f) v = (c • (f v) : module.restrict_scalars R W) :=
begin
  erw [linear_map.map_smul],
  refl,
end

end

noncomputable theory
open module
open monoid_algebra

variables {k : Type u} [comm_ring k] {G : Type u} [fintype G] [group G]

variables {V : Type u} [add_comm_group V] [module (monoid_algebra k G) V]
variables {W : Type u} [add_comm_group W] [module (monoid_algebra k G) W]

/-!
We now do the key calculation in Maschke's theorem.

Given `V → W`, an inclusion of `k[G]` modules,,
assume we have some splitting `π` of the inclusion `V → W`,
just as as a `k`-linear map.
(This is available cheaply, by choosing a basis.)

We now construct a splitting of the inclusion as a `k[G]`-linear map,
by the formula
$$ \frac{1}{|G|} \sum_{g \mem G} g⁻¹ • π(g • -). $$

There may be a certain amount of work afterwards to get
the specific formulation of Maschke's theorem you might be thinking of
(possibly requiring setting up some infrastructure about semisimplicity,
or abelian categories, depending on the formulation),
but they should all rely on this calculation.
-/

variables (π : (restrict_scalars k W) →ₗ[k] (restrict_scalars k V))
include π

/--
We define the conjugate of `π` by `g`, as a `k`-linear map.
-/
def conjugate (g : G) : (restrict_scalars k W) →ₗ[k] (restrict_scalars k V) :=
((group_smul.linear_map k V g⁻¹).comp π).comp (group_smul.linear_map k W g)

/--
The sum of the conjugates of `π` by each element `g : G`, as a `k`-linear map.

(We postpone dividing by the size of the group as long as possible.)
-/
def sum_of_conjugates :
  (restrict_scalars k W) →ₗ[k] (restrict_scalars k V) :=
(finset.univ : finset G).sum (λ g, conjugate π g)

/--
In fact, the sum over `g : G` of the conjugate of `π` by `g` is a `k[G]`-linear map.
-/
def sum_of_conjugates_equivariant :
  W →ₗ[monoid_algebra k G] V :=
monoid_algebra.equivariant_of_linear_of_comm (sum_of_conjugates π) (λ g,
begin
  ext,
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

variables [inv : invertible (fintype.card G : k)]
include inv

section
local attribute [instance] linear_map_algebra_module
/--
We construct our `k[G]`-linear retraction of `i` as
$$ \frac{1}{|G|} \sum_{g \mem G} g⁻¹ • π(g • -). $$
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
    @semimodule.add_monoid_smul_eq_smul k _ (restrict_scalars k V) _ _ (fintype.card G) v,
    ←mul_smul, invertible.inv_of_mul_self, one_smul],
end
