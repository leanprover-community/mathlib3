/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Zhangir Azerbayev.
-/
import .multilinear
import group_theory.perm.sign


variables (R : Type*) [ring R]
variables (M : Type*) [add_comm_group M] [module R M]
variables (N : Type*) [add_comm_group N] [module R N]
variables (ι : Type*) [decidable_eq ι]
variable (M₀ : Π i : ι, M)

class alternating_map extends multilinear_map R (λ i : ι , M) N :=
(map_alternating {ν : ι → M} {i j : ι} (h : ν i = ν j) (hij : i ≠ j) : to_fun ν = 0)


namespace alternating
variable {f : alternating_map R M N ι}
variable (ν : ι → M)
variables {R M N ι}
open function

instance : has_coe (alternating_map R M N ι) (multilinear_map R (λ i : ι, M) N) :=
⟨λ x , ⟨x.to_fun, x.map_add', x.map_smul'⟩⟩

@[simp] lemma map_add (i : ι) (x y : M) :
  f (update ν i (x + y)) = f (update ν i x) + f (update ν i y) :=
f.to_multilinear_map.map_add' ν i x y

@[simp] lemma map_smul (i : ι) (r : R) (x : M) :
  f (update ν i (r • x)) = r • f (update ν i x) :=
f.to_multilinear_map.map_smul' ν i r x

lemma eq_args {i j : ι} (h : ν i = ν j) (hij : i ≠ j) : f ν = 0 :=
alternating_map.map_alternating h hij

lemma map_add_swap {i j : ι} (hij : i ≠ j):
f ν + f (ν ∘ equiv.swap i j) = 0 :=
begin
  have key : f (function.update (function.update ν i (ν i + ν j)) j (ν i + ν j)) = 0 :=
    by rw eq_args (function.update (function.update ν i (ν i + ν j)) j (ν i + ν j))
    (by rw [function.update_same, function.update_noteq hij,  function.update_same]) hij,
  rw map_add at key,
  rw [function.update_comm hij (ν i + ν j) (ν i) ν, map_add] at key,
  rw eq_args (function.update (function.update ν j (ν i)) i (ν i))
    (by rw [function.update_same, function.update_comm (ne_comm.mp hij) (ν i) (ν i) ν,
    function.update_same]) hij at key,
  rw zero_add at key,
  rw [function.update_comm hij (ν i + ν j) (ν j) ν, map_add] at key,
  rw eq_args (function.update (function.update ν j (ν j)) i (ν j))
  (by rw [function.update_same, function.update_comm (ne_comm.mp hij) (ν j) (ν j) ν,
  function.update_same]) hij at key,
  rw [add_zero, add_comm] at key,
  convert key,
  simp,
  ext x,
    cases classical.em (x = i) with hx hx,
    --case x = i
    rw hx,
    simp only [equiv.swap_apply_left, function.comp_app],
    rw function.update_same,
    --case x ≠ i
    cases classical.em (x = j) with hx1 hx1,
    rw hx1,
    simp only [equiv.swap_apply_left, function.comp_app],
    rw function.update_noteq (ne_comm.mp hij),
    simp,
    --case x ≠ i, x ≠ j,
    simp only [hx, hx1, function.comp_app, function.update_noteq, ne.def, not_false_iff],
    rw equiv.swap_apply_of_ne_of_ne hx hx1,
end

lemma map_swap {i j : ι} (hij : i ≠ j):
f (ν ∘ equiv.swap i j) = - f ν  :=
begin
  apply eq_neg_of_add_eq_zero,
  rw add_comm,
  exact map_add_swap ν hij,
end

variable [fintype ι]

lemma map_perm (σ : equiv.perm ι) :
f ν = (equiv.perm.sign σ : ℤ) • f (ν ∘ σ) :=
begin
  apply equiv.perm.swap_induction_on' σ,
  --Base case
  rw equiv.perm.sign_one,
  simp only [units.coe_one, one_smul, coe_fn_coe_base],
  congr,
  --rw [equiv.perm.sign_one, one_smul], congr,
  --Inductive step
  intros s x y hxy hI,
  have assoc : ν ∘ (s * equiv.swap x y : equiv.perm ι) = (ν ∘ s ∘ equiv.swap x y) := rfl,
  rw [assoc, map_swap (ν ∘ s) hxy, ←neg_one_smul ℤ (f (ν ∘ s))],
  have h1 : (-1 : ℤ) = equiv.perm.sign (equiv.swap x y) := by simp [hxy],
  rw h1,
  rw smul_smul,
  rw ←units.coe_mul,
  rw ←equiv.perm.sign_mul,
  rw mul_assoc,
  rw equiv.swap_mul_self,
  rw mul_one,
  assumption,
end

end alternating
