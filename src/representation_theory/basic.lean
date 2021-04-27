/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import linear_algebra.basic
import algebra.monoid_algebra
import algebra.module.submodule

/-!
# Representations
TODO
-/

universes u v w

/-- A `representation k G M` is a `add_comm_monoid M` with a `k`-scalar multiplication
and a `G`-action which commute with each other. -/
class representation (k : Type u) (G : Type v) (M : Type w)
  [semiring k] [monoid G] [add_comm_monoid M]
  [module k M] [distrib_mul_action G M] extends smul_comm_class k G M : Type (max u v w).


namespace representation
variables (k : Type u) (G : Type v) (M : Type w)
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M] [distrib_mul_action G M]

noncomputable instance monoid_algebra_scalar : has_scalar (monoid_algebra k G) M :=
{ smul := λ kG m, finsupp.lift_add_hom (λ g : G, g • (smul_add_hom k M)) kG m }

lemma add_smul' (x y : monoid_algebra k G) (m : M) : (x + y) • m = x • m + y • m :=
begin
  dsimp [(•)],
  simp only [add_monoid_hom.coe_mk, add_monoid_hom.finsupp_sum_apply],
  rw finsupp.sum_add_index,
  simp only [zero_smul, forall_const, smul_zero],
  simp [add_smul, smul_add],
end

lemma zero_smul' (m : M) : (0 : monoid_algebra k G) • m = 0 :=
begin
  dsimp [(•)],
  simp,
end

lemma sum_smul (x : monoid_algebra k G) (f : G → k → monoid_algebra k G) (m : M) :
  (finsupp.sum x f) • m = finsupp.sum x (λ g r, f g r • m) :=
begin
  convert add_monoid_hom.map_finsupp_sum  ⟨λ r, r • m, _, _⟩ x f,
  { exact zero_smul' k G M m, },
  { exact λ x y, add_smul' k G M x y m, },
end

lemma mul_smul' (x y : monoid_algebra k G) (m : M)
  (hsmul : ∀ (m : k) (n : G) (a : M), m • n • a = n • m • a) :
  (x * y) • m = x • y • m :=
begin
  simp only [monoid_algebra.mul_def],
  conv_rhs { rw ← finsupp.sum_single x, rw ← finsupp.sum_single y, rw sum_smul, rw sum_smul, },
  simp only [sum_smul], congr, funext,
  dsimp [(•)],
  simp only [finsupp.smul_sum, add_monoid_hom.coe_mk, zero_smul, finsupp.sum_zero,
    add_monoid_hom.finsupp_sum_apply, finsupp.sum_single_index, smul_zero],
  conv_rhs { rw finsupp.sum, rw finset.smul_sum },
  rw finsupp.sum,
  congr, funext,
  simp [mul_smul, hsmul],
end

/-- Turn the two `smul`s into a `FG`-module -/
noncomputable instance [representation k G M] :
  module (monoid_algebra k G) M :=
{ smul := λ x m, x • m,
  add_smul := λ x y m, add_smul' k G M x y m,
  zero_smul := λ m, zero_smul' k G M m,
  smul_add := λ x y m, add_monoid_hom.map_add _ _ _,
  smul_zero := λ x, add_monoid_hom.map_zero _,
  one_smul := λ m, by simp [(•), monoid_algebra.one_def],
  mul_smul := λ x y m, mul_smul' k G M x y m _inst_6.smul_comm }

end representation

section monoid_algebra_actions
variables (k : Type u) (G : Type v) (M : Type w)
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M] [distrib_mul_action G M]

noncomputable instance monoid_algebra.has_group_scalar : has_scalar G (monoid_algebra k G) :=
{ smul := λ g x, (monoid_algebra.of k G g) * x }

@[simp]
lemma group_smul_apply (g : G) (x : monoid_algebra k G) : g • x = (monoid_algebra.of k G g) • x :=
rfl

noncomputable instance group_monoid_algebra_action : distrib_mul_action G (monoid_algebra k G) :=
{ one_smul := λ x, one_mul _,
  mul_smul := λ g h x, by { simp [← mul_assoc], },
  smul_add := λ g x y, mul_add _ x y,
  smul_zero := λ g, mul_zero _ }

lemma of_smul (g : G) (m : M) : (monoid_algebra.of k G g) • m = g • m :=
begin
  simp [(•)],
end

/-- Inclusion of `k` into `monoid_algebra k G` as a ring homomorphism. -/
noncomputable def of' : k →+* monoid_algebra k G :=
{ to_fun := λ k, finsupp.single 1 k,
  map_one' := monoid_algebra.one_def,
  map_mul' := λ r s, by { simp only [mul_one, monoid_algebra.single_mul_single]},
  map_zero' := finsupp.single_zero,
  map_add' := λ r s, finsupp.single_add }

@[simp] lemma of'_apply (r : k) : of' k G r = finsupp.single 1 r := rfl

lemma of'_smul (r : k) (m : M) : (of' k G r) • m = r • m :=
begin
  simp [(•), of'],
end

/-- Scalar tower stuff -/
instance group_smul_tower [representation k G M] :
  is_scalar_tower G (monoid_algebra k G) M :=
{ smul_assoc := λ g x m,
  begin
    rw ← of_smul k G M g (x • m),
    simp only [group_smul_apply, smul_eq_mul, mul_smul],
  end }

instance semiring_smul_tower [representation k G M] :
  is_scalar_tower k (monoid_algebra k G) M :=
{ smul_assoc := λ x y m,
  begin
    haveI : smul_comm_class k G M := by apply_instance,
    dsimp [(•)],
    simp only [finsupp.smul_sum, add_monoid_hom.coe_mk, add_monoid_hom.finsupp_sum_apply],
    rw finsupp.sum_map_range_index,
    congr, funext,
    rw [mul_smul],
    rw smul_comm x a _,
    exact _inst,
    simp,
  end }

end monoid_algebra_actions

namespace representation
variables (k : Type u) (G : Type v) (M : Type w)
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M]

section as_monoid_hom
variables [distrib_mul_action G M]

variables {G}
/-- A group element acts by an k-linear map in any k-linear representation. -/
def smul.linear_map [representation k G M] (g : G) : M →ₗ[k] M :=
{ to_fun := λ m, g • m,
  map_add' := λ m n, distrib_mul_action.smul_add g _ _,
  map_smul' := λ r m, (smul_comm _ _ _).symm }

@[simp]
lemma smul.linear_map_apply [representation k G M] (g : G) (m : M) :
  (smul.linear_map k M g : M →ₗ[k] M) m = g • m := rfl

variables (k G M)
/--
A k-linear representation of G on M can be thought of as
a multiplicative map from G into the k-linear endomorphisms of M.
-/
def as_monoid_hom [representation k G M] : G →* (M →ₗ[k] M) :=
{ to_fun := λ g, smul.linear_map k M g,
  map_one' := by { ext, simp, },
  map_mul' := λ g g', by { ext, simp [mul_smul], }, }

@[simp]
lemma as_monoid_hom_apply_apply [representation k G M] (g : G) (m : M) :
  (as_monoid_hom k G M) g m = g • m := rfl

end as_monoid_hom

variables {k G M}

/--
We get a k-linear representation of G on M from
a multiplicative map from G into the k-linear endomorphisms of M.
-/
instance of_monoid_hom_aux {p : G →* (M →ₗ[k] M)} : distrib_mul_action G M :=
{ smul := λ g m , p g m,
  one_smul := λ m, by simp only [linear_map.one_apply, monoid_hom.map_one],
  mul_smul := λ g h m, by simp only [linear_map.mul_apply, monoid_hom.map_mul],
  smul_add := λ g m n, by simp only [linear_map.map_add],
  smul_zero := λ g, by simp only [linear_map.map_zero] }

-- def of_monoid_hom {p : G →* (M →ₗ[k] M)} : representation k G M :=

end representation
