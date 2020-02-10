import linear_algebra.tensor_product
import linear_algebra.dual

universes u v

set_option class.instance_max_depth 42

namespace contraction
open tensor_product
open_locale tensor_product

variables (R : Type u) (M N : Type v)
variables [comm_ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]

/--
The natural left-handed pairing between a module and its dual.
-/
def contract_l : (module.dual R M) ⊗ M →ₗ[R] R := (uncurry _ _ _ _).to_fun linear_map.id

/--
The natural right-handed pairing between a module and its dual.
-/
def contract_r : M ⊗ (module.dual R M) →ₗ[R] R := (uncurry _ _ _ _).to_fun linear_map.id.flip

/--
The natural map associating a linear map to the tensor product of two modules.
-/
def dual_tensor_hom : (module.dual R M) ⊗ N →ₗ[R] M →ₗ[R] N :=
  let M' := (module.dual R M) in
  ((uncurry R M' N (M →ₗ[R] N)) : _ → M' ⊗ N →ₗ[R] M →ₗ[R] N) {
  to_fun := λ f, {
    to_fun := λ n, {
      to_fun := λ m, (f m) • n,
      add    := λ m₁ m₂, by { rw linear_map.map_add, apply add_smul, },
      smul   := λ c m, by { rw linear_map.map_smul, apply mul_smul, } },
    add    := λ n₁ n₂, by { ext m, apply smul_add, },
    smul   := λ c n, by { ext m, apply smul_comm, } },
  add    := λ f₁ f₂, by { ext n m, apply add_smul, },
  smul   := λ c f, by { ext n m, apply mul_smul, } }

variables {R M N}

@[simp] lemma contract_l_apply (f : module.dual R M) (m : M) :
  contract_l R M (f ⊗ₜ m) = f m := by apply uncurry_apply

@[simp] lemma contract_r_apply (f : module.dual R M) (m : M) :
  contract_r R M (m ⊗ₜ f) = f m := by apply uncurry_apply

@[simp] lemma dual_tensor_hom_apply (f : module.dual R M) (m : M) (n : N) :
  dual_tensor_hom R M N (f ⊗ₜ n) m = (f m) • n := by {
    dunfold dual_tensor_hom, rw uncurry_apply, refl, }

end contraction
