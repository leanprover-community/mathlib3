/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import algebra.module.basic
import algebra.module.linear_map
import algebra.monoid_algebra.basic
import linear_algebra.trace
import linear_algebra.dual
import linear_algebra.free_module.basic

/-!
# Monoid representations

This file introduces monoid representations and their characters and defines a few ways to construct
representations.

## Main definitions

  * representation.representation
  * representation.character
  * representation.tprod
  * representation.lin_hom
  * represensation.dual

## Implementation notes

Representations of a monoid `G` on a `k`-module `V` are implemented as
homomorphisms `G →* (V →ₗ[k] V)`.
-/

open monoid_algebra (lift) (of)
open linear_map

section
variables (k G V : Type*) [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]

/--
A representation of `G` on the `k`-module `V` is an homomorphism `G →* (V →ₗ[k] V)`.
-/
abbreviation representation := G →* (V →ₗ[k] V)

end

namespace representation

section trivial

variables {k G V : Type*} [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]

/--
The trivial representation of `G` on the one-dimensional module `k`.
-/
def trivial : representation k G k := 1

@[simp]
lemma trivial_def (g : G) (v : k) : trivial g v = v := rfl

end trivial

section monoid_algebra

variables {k G V : Type*} [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]
variables (ρ : representation k G V)

/-- The `k`-linear `G`-representation on `k[G]` sending `g : G` to left multiplication by
`g` as an element of `k[G]`. -/
noncomputable def left_regular (k G : Type*) [comm_semiring k] [monoid G] :
  representation k G (monoid_algebra k G) :=
((monoid_algebra.lift k G _).symm (algebra.lmul k (monoid_algebra k G)))

@[simp] lemma left_regular_def (g : G) (v : monoid_algebra k G) :
  left_regular k G g v = finsupp.single g (1 : k) * v := rfl

/--
A `k`-linear representation of `G` on `V` can be thought of as
an algebra map from `monoid_algebra k G` into the `k`-linear endomorphisms of `V`.
-/
noncomputable def as_algebra_hom : monoid_algebra k G →ₐ[k] (module.End k V) :=
(lift k G _) ρ

lemma as_algebra_hom_def : as_algebra_hom ρ = (lift k G _) ρ :=
rfl

@[simp]
lemma as_algebra_hom_single (g : G) (r : k) :
  (as_algebra_hom ρ (finsupp.single g r)) = r • ρ g :=
by simp only [as_algebra_hom_def, monoid_algebra.lift_single]

lemma as_algebra_hom_single_one (g : G):
  (as_algebra_hom ρ (finsupp.single g 1)) = ρ g :=
by simp

lemma as_algebra_hom_of (g : G) :
  (as_algebra_hom ρ (of k G g)) = ρ g :=
by simp only [monoid_algebra.of_apply, as_algebra_hom_single, one_smul]

@[simp] lemma as_algebra_hom_left_regular (x y : monoid_algebra k G) :
  as_algebra_hom (left_regular k G) x y = x * y :=
by simp only [as_algebra_hom_def, left_regular, equiv.apply_symm_apply, algebra.lmul_apply]

/--
If `ρ : representation k G V`, then `ρ.as_module` is a type synonym for `V`,
which we equip with an instance `module (monoid_algebra k G) ρ.as_module`.
You should use `as_module_equiv : ρ.as_module ≃+ V` to translate terms.
-/
@[nolint unused_arguments, derive [add_comm_monoid, module (module.End k V)]]
def as_module (ρ : representation k G V) := V

instance : inhabited ρ.as_module := ⟨0⟩

/--
A `k`-linear representation of `G` on `V` can be thought of as
a module over `monoid_algebra k G`.
-/
noncomputable instance as_module_module : module (monoid_algebra k G) ρ.as_module :=
module.comp_hom V (as_algebra_hom ρ).to_ring_hom

end monoid_algebra

section mul_action
variables (k : Type*) [comm_semiring k] (G : Type*) [monoid G] (H : Type*) [mul_action G H]

/-- A `G`-action on `H` induces a representation `G →* End(k[H])` in the natural way. -/
noncomputable def of_mul_action : representation k G (H →₀ k) :=
{ to_fun := λ g, finsupp.lmap_domain k k ((•) g),
  map_one' := by { ext x y, dsimp, simp },
  map_mul' := λ x y, by { ext z w, simp [mul_smul] }}

variables {k G H}

lemma of_mul_action_def (g : G) : of_mul_action k G H g = finsupp.lmap_domain k k ((•) g) := rfl

end mul_action
section group

variables {k G V : Type*} [comm_semiring k] [group G] [add_comm_monoid V] [module k V]
variables (ρ : representation k G V)

@[simp] lemma of_mul_action_apply {H : Type*} [mul_action G H]
  (g : G) (f : H →₀ k) (h : H) : of_mul_action k G H g f h = f (g⁻¹ • h) :=
begin
  conv_lhs { rw ← smul_inv_smul g h, },
  let h' := g⁻¹ • h,
  change of_mul_action k G H g f (g • h') = f h',
  have hg : function.injective ((•) g : H → H), { intros h₁ h₂, simp, },
  simp only [of_mul_action_def, finsupp.lmap_domain_apply, finsupp.map_domain_apply, hg],
end

lemma of_mul_action_as_module_eq_mul
  (x : monoid_algebra k G) (y : (of_mul_action k G G).as_module) :
  x • y = (x * y : monoid_algebra k G) :=
x.induction_on (λ g, by show as_algebra_hom _ _ _ = _; ext; simp)
  (λ x y hx hy, by simp only [hx, hy, add_mul, add_smul])
  (λ r x hx, by show as_algebra_hom _ _ _ = _; simpa [←hx])

/--
When `G` is a group, a `k`-linear representation of `G` on `V` can be thought of as
a group homomorphism from `G` into the invertible `k`-linear endomorphisms of `V`.
-/
def as_group_hom : G →* units (V →ₗ[k] V) :=
monoid_hom.to_hom_units ρ

lemma as_group_hom_apply (g : G) : ↑(as_group_hom ρ g) = ρ g :=
by simp only [as_group_hom, monoid_hom.coe_to_hom_units]

end group

section tensor_product

variables {k G V W : Type*} [comm_semiring k] [monoid G]
variables [add_comm_monoid V] [module k V] [add_comm_monoid W] [module k W]
variables (ρV : representation k G V) (ρW : representation k G W)

open_locale tensor_product

/--
Given representations of `G` on `V` and `W`, there is a natural representation of `G` on their
tensor product `V ⊗[k] W`.
-/
def tprod : representation k G (V ⊗[k] W) :=
{ to_fun := λ g, tensor_product.map (ρV g) (ρW g),
  map_one' := by simp only [map_one, tensor_product.map_one],
  map_mul' := λ g h, by simp only [map_mul, tensor_product.map_mul] }

local notation ρV ` ⊗ ` ρW := tprod ρV ρW

@[simp]
lemma tprod_apply (g : G) : (ρV ⊗ ρW) g = tensor_product.map (ρV g) (ρW g) := rfl

lemma tprod_one_as_module {V W : Type*} [add_comm_group V] [add_comm_group W] [module k V]
  [module k W] (ρ : representation k G V) (r : monoid_algebra k G) (x : V)
  (y : W) : (r • (x ⊗ₜ y : (ρ.tprod 1).as_module) : (ρ.tprod 1).as_module)
    = (r • x : ρ.as_module) ⊗ₜ y :=
begin
  show as_algebra_hom _ _ _ = as_algebra_hom _ _ _ ⊗ₜ _,
  simp only [as_algebra_hom_def, monoid_algebra.lift_apply,
    tprod_apply, monoid_hom.one_apply, linear_map.finsupp_sum_apply,
    linear_map.smul_apply, tensor_product.map_tmul, linear_map.one_apply],
  erw tensor_product.sum_tmul,
  refl,
end

lemma one_tprod_as_module {V W : Type*} [add_comm_group V] [add_comm_group W] [module k V]
  [module k W] (ρ : representation k G W) (r : monoid_algebra k G) (x : V)
  (y : W) : (r • (x ⊗ₜ y : (tprod 1 ρ).as_module) : (tprod 1 ρ).as_module)
    = x ⊗ₜ (r • y : ρ.as_module) :=
begin
  show as_algebra_hom _ _ _ = _ ⊗ₜ as_algebra_hom _ _ _,
  simp only [as_algebra_hom_def, monoid_algebra.lift_apply,
    tprod_apply, monoid_hom.one_apply, linear_map.finsupp_sum_apply,
    linear_map.smul_apply, tensor_product.map_tmul, linear_map.one_apply],
  erw tensor_product.tmul_sum,
  simp only [tensor_product.tmul_smul],
  refl,
end

end tensor_product

section linear_hom

variables {k G V W : Type*} [comm_semiring k] [group G]
variables [add_comm_monoid V] [module k V] [add_comm_monoid W] [module k W]
variables (ρV : representation k G V) (ρW : representation k G W)

/--
Given representations of `G` on `V` and `W`, there is a natural representation of `G` on the
module `V →ₗ[k] W`, where `G` acts by conjugation.
-/
def lin_hom : representation k G (V →ₗ[k] W) :=
{ to_fun := λ g,
  { to_fun := λ f, (ρW g) ∘ₗ f ∘ₗ (ρV g⁻¹),
    map_add' := λ f₁ f₂, by simp_rw [add_comp, comp_add],
    map_smul' := λ r f, by simp_rw [ring_hom.id_apply, smul_comp, comp_smul]},
  map_one' := linear_map.ext $ λ x,
    by simp_rw [coe_mk, inv_one, map_one, one_apply, one_eq_id, comp_id, id_comp],
  map_mul' := λ g h,  linear_map.ext $ λ x,
    by simp_rw [coe_mul, coe_mk, function.comp_apply, mul_inv_rev, map_mul, mul_eq_comp,
                comp_assoc ]}

@[simp]
lemma lin_hom_apply (g : G) (f : V →ₗ[k] W) : (lin_hom ρV ρW) g f = (ρW g) ∘ₗ f ∘ₗ (ρV g⁻¹) := rfl

/--
The dual of a representation `ρ` of `G` on a module `V`, given by `(dual ρ) g f = f ∘ₗ (ρ g⁻¹)`,
where `f : module.dual k V`.
-/
def dual : representation k G (module.dual k V) :=
{ to_fun := λ g,
  { to_fun := λ f, f ∘ₗ (ρV g⁻¹),
    map_add' := λ f₁ f₂, by simp only [add_comp],
    map_smul' := λ r f,
      by {ext, simp only [coe_comp, function.comp_app, smul_apply, ring_hom.id_apply]} },
  map_one' :=
    by {ext, simp only [coe_comp, function.comp_app, map_one, inv_one, coe_mk, one_apply]},
  map_mul' := λ g h,
    by {ext, simp only [coe_comp, function.comp_app, mul_inv_rev, map_mul, coe_mk, mul_apply]}}

@[simp]
lemma dual_apply (g : G) : (dual ρV) g = module.dual.transpose (ρV g⁻¹) := rfl

lemma dual_tensor_hom_comm (g : G) :
  (dual_tensor_hom k V W) ∘ₗ (tensor_product.map (ρV.dual g) (ρW g)) =
  (lin_hom ρV ρW) g ∘ₗ (dual_tensor_hom k V W) :=
begin
  ext, simp [module.dual.transpose_apply],
end

end linear_hom

end representation
