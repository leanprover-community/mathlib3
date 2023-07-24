/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import algebra.module.basic
import algebra.module.linear_map
import algebra.monoid_algebra.basic
import linear_algebra.dual
import linear_algebra.contraction
import ring_theory.tensor_product

/-!
# Monoid representations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

variables (k : Type*) {G V : Type*} [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]

/--
The trivial representation of `G` on a `k`-module V.
-/
def trivial : representation k G V := 1

@[simp]
lemma trivial_def (g : G) (v : V) : trivial k g v = v := rfl

end trivial

section monoid_algebra

variables {k G V : Type*} [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]
variables (ρ : representation k G V)

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

/--
The additive equivalence from the `module (monoid_algebra k G)` to the original vector space
of the representative.

This is just the identity, but it is helpful for typechecking and keeping track of instances.
-/
def as_module_equiv : ρ.as_module ≃+ V :=
add_equiv.refl _

@[simp]
lemma as_module_equiv_map_smul (r : monoid_algebra k G) (x : ρ.as_module) :
  ρ.as_module_equiv (r • x) = ρ.as_algebra_hom r (ρ.as_module_equiv x) :=
rfl

@[simp]
lemma as_module_equiv_symm_map_smul (r : k) (x : V) :
  ρ.as_module_equiv.symm (r • x) =
    algebra_map k (monoid_algebra k G) r • (ρ.as_module_equiv.symm x) :=
begin
  apply_fun ρ.as_module_equiv,
  simp,
end

@[simp]
lemma as_module_equiv_symm_map_rho (g : G) (x : V) :
  ρ.as_module_equiv.symm (ρ g x) = monoid_algebra.of k G g • (ρ.as_module_equiv.symm x) :=
begin
  apply_fun ρ.as_module_equiv,
  simp,
end

/--
Build a `representation k G M` from a `[module (monoid_algebra k G) M]`.

This version is not always what we want, as it relies on an existing `[module k M]`
instance, along with a `[is_scalar_tower k (monoid_algebra k G) M]` instance.

We remedy this below in `of_module`
(with the tradeoff that the representation is defined
only on a type synonym of the original module.)
-/
noncomputable
def of_module' (M : Type*) [add_comm_monoid M] [module k M] [module (monoid_algebra k G) M]
  [is_scalar_tower k (monoid_algebra k G) M] : representation k G M :=
(monoid_algebra.lift k G (M →ₗ[k] M)).symm (algebra.lsmul k M)

section
variables (k G) (M : Type*) [add_comm_monoid M] [module (monoid_algebra k G) M]

/--
Build a `representation` from a `[module (monoid_algebra k G) M]`.

Note that the representation is built on `restrict_scalars k (monoid_algebra k G) M`,
rather than on `M` itself.
-/
noncomputable
def of_module :
  representation k G (restrict_scalars k (monoid_algebra k G) M) :=
(monoid_algebra.lift k G
  (restrict_scalars k (monoid_algebra k G) M →ₗ[k] restrict_scalars k (monoid_algebra k G) M)).symm
  (restrict_scalars.lsmul k (monoid_algebra k G) M)

/-!
## `of_module` and `as_module` are inverses.

This requires a little care in both directions:
this is a categorical equivalence, not an isomorphism.

See `Rep.equivalence_Module_monoid_algebra` for the full statement.

Starting with `ρ : representation k G V`, converting to a module and back again
we have a `representation k G (restrict_scalars k (monoid_algebra k G) ρ.as_module)`.
To compare these, we use the composition of `restrict_scalars_add_equiv` and `ρ.as_module_equiv`.

Similarly, starting with `module (monoid_algebra k G) M`,
after we convert to a representation and back to a module,
we have `module (monoid_algebra k G) (restrict_scalars k (monoid_algebra k G) M)`.
-/

@[simp] lemma of_module_as_algebra_hom_apply_apply
  (r : monoid_algebra k G) (m : restrict_scalars k (monoid_algebra k G) M) :
  ((((of_module k G M).as_algebra_hom) r) m) =
    (restrict_scalars.add_equiv _ _ _).symm (r • restrict_scalars.add_equiv _ _ _ m) :=
begin
  apply monoid_algebra.induction_on r,
  { intros g,
    simp only [one_smul, monoid_algebra.lift_symm_apply, monoid_algebra.of_apply,
      representation.as_algebra_hom_single, representation.of_module,
      add_equiv.apply_eq_iff_eq, restrict_scalars.lsmul_apply_apply], },
  { intros f g fw gw,
    simp only [fw, gw, map_add, add_smul, linear_map.add_apply], },
  { intros r f w,
    simp only [w, alg_hom.map_smul, linear_map.smul_apply,
      restrict_scalars.add_equiv_symm_map_smul_smul], }
end

@[simp]
lemma of_module_as_module_act (g : G) (x : restrict_scalars k (monoid_algebra k G) ρ.as_module) :
  of_module k G (ρ.as_module) g x =
    (restrict_scalars.add_equiv _ _ _).symm ((ρ.as_module_equiv).symm
      (ρ g (ρ.as_module_equiv (restrict_scalars.add_equiv _ _ _ x)))) :=
begin
  apply_fun restrict_scalars.add_equiv _ _ ρ.as_module using
    (restrict_scalars.add_equiv _ _ _).injective,
  dsimp [of_module, restrict_scalars.lsmul_apply_apply],
  simp,
end

lemma smul_of_module_as_module (r : monoid_algebra k G)
  (m : (of_module k G M).as_module) :
   (restrict_scalars.add_equiv _ _ _) ((of_module k G M).as_module_equiv (r • m)) =
     r • (restrict_scalars.add_equiv _ _ _) ((of_module k G M).as_module_equiv m) :=
by { dsimp, simp only [add_equiv.apply_symm_apply, of_module_as_algebra_hom_apply_apply], }

end

end monoid_algebra

section add_comm_group

variables {k G V : Type*} [comm_ring k] [monoid G] [I : add_comm_group V] [module k V]
variables (ρ : representation k G V)

instance : add_comm_group ρ.as_module := I

end add_comm_group

section mul_action
variables (k : Type*) [comm_semiring k] (G : Type*) [monoid G] (H : Type*) [mul_action G H]

/-- A `G`-action on `H` induces a representation `G →* End(k[H])` in the natural way. -/
noncomputable def of_mul_action : representation k G (H →₀ k) :=
{ to_fun := λ g, finsupp.lmap_domain k k ((•) g),
  map_one' := by { ext x y, dsimp, simp },
  map_mul' := λ x y, by { ext z w, simp [mul_smul] }}

variables {k G H}

lemma of_mul_action_def (g : G) : of_mul_action k G H g = finsupp.lmap_domain k k ((•) g) := rfl

lemma of_mul_action_single (g : G) (x : H) (r : k) :
  of_mul_action k G H g (finsupp.single x r) = finsupp.single (g • x) r :=
finsupp.map_domain_single

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

lemma of_mul_action_self_smul_eq_mul
  (x : monoid_algebra k G) (y : (of_mul_action k G G).as_module) :
  x • y = (x * y : monoid_algebra k G) :=
x.induction_on (λ g, by show as_algebra_hom _ _ _ = _; ext; simp)
  (λ x y hx hy, by simp only [hx, hy, add_mul, add_smul])
  (λ r x hx, by show as_algebra_hom _ _ _ = _; simpa [←hx])

/-- If we equip `k[G]` with the `k`-linear `G`-representation induced by the left regular action of
`G` on itself, the resulting object is isomorphic as a `k[G]`-module to `k[G]` with its natural
`k[G]`-module structure. -/
@[simps] noncomputable def of_mul_action_self_as_module_equiv :
  (of_mul_action k G G).as_module ≃ₗ[monoid_algebra k G] monoid_algebra k G :=
{ map_smul' := of_mul_action_self_smul_eq_mul, ..as_module_equiv _ }

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

lemma smul_tprod_one_as_module (r : monoid_algebra k G) (x : V) (y : W) :
  (r • (x ⊗ₜ y) : (ρV.tprod 1).as_module) = (r • x : ρV.as_module) ⊗ₜ y :=
begin
  show as_algebra_hom _ _ _ = as_algebra_hom _ _ _ ⊗ₜ _,
  simp only [as_algebra_hom_def, monoid_algebra.lift_apply,
    tprod_apply, monoid_hom.one_apply, linear_map.finsupp_sum_apply,
    linear_map.smul_apply, tensor_product.map_tmul, linear_map.one_apply],
  simp only [finsupp.sum, tensor_product.sum_tmul],
  refl,
end

lemma smul_one_tprod_as_module (r : monoid_algebra k G) (x : V) (y : W) :
  (r • (x ⊗ₜ y) : ((1 : representation k G V).tprod ρW).as_module) = x ⊗ₜ (r • y : ρW.as_module) :=
begin
  show as_algebra_hom _ _ _ = _ ⊗ₜ as_algebra_hom _ _ _,
  simp only [as_algebra_hom_def, monoid_algebra.lift_apply,
    tprod_apply, monoid_hom.one_apply, linear_map.finsupp_sum_apply,
    linear_map.smul_apply, tensor_product.map_tmul, linear_map.one_apply],
  simp only [finsupp.sum, tensor_product.tmul_sum, tensor_product.tmul_smul],
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

/--
Given $k$-modules $V, W$, there is a homomorphism $φ : V^* ⊗ W → Hom_k(V, W)$
(implemented by `linear_algebra.contraction.dual_tensor_hom`).
Given representations of $G$ on $V$ and $W$,there are representations of $G$ on  $V^* ⊗ W$ and on
$Hom_k(V, W)$.
This lemma says that $φ$ is $G$-linear.
-/
lemma dual_tensor_hom_comm (g : G) :
  (dual_tensor_hom k V W) ∘ₗ (tensor_product.map (ρV.dual g) (ρW g)) =
  (lin_hom ρV ρW) g ∘ₗ (dual_tensor_hom k V W) :=
begin
  ext, simp [module.dual.transpose_apply],
end

end linear_hom

end representation
