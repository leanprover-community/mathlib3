/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Topaz.
-/

import .tensor_algebra
import group_theory.perm.sign

/-!
# Exterior Algebras

We construct the exterior algebra of a semimodule `M` over a commutative semiring `R`.

## Notation

The exterior algebra of the `R`-semimodule `M` is denoted as `exterior_algebra R M`.
It is endowed with the structure of an `R`-algebra. Some results only hold at the level of
generality of an `S`-module `M` and the space `exterior_algebra S N`.

Given a linear morphism `f : M → A` from a semimodule `M` to another `R`-algebra `A`, such that
`cond : ∀ m : M, f m * f m = 0`, there is a (unique) lift of `f` to an `R`-algebra morphism,
which is denoted `exterior_algebra.lift R M f cond`.

The canonical linear map `M → exterior_algebra R M` is denoted `exterior_algebra.ι R M`.

The canonical multilinear map `(fin q → M) → exterior_algebra R M` is denoted `wedge R M`.

## Theorems

The main theorems proved ensure that `exterior_algebra R M` satisfies the universal property
of the exterior algebra.
1. `ι_comp_lift` is  fact that the composition of `ι R M` with `lift R M f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift R M f cond` with respect to 1.
3. `wedge_perm` says that for any permutation `σ` of `fin q` and any `ν : fin q → N`, we have that
`wedge S N ν = (equiv.perm.sign σ) • wedge S n (ν ∘ σ)`.

## Implementation details

The exterior algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `exterior_algebra.rel R M` on `tensor_algebra R M`.
  This is the smallest relation which identifies squares of elements of `M` with `0`,
  and which is compatible with addition and multiplication.
2. The exterior algebra is the quotient of the tensor algebra by this relation.

-/

variables (R : Type*) [comm_semiring R]
variables (M : Type*) [add_comm_group M] [semimodule R M]
variables {S : Type*} [field S]
variables {N : Type*} [add_comm_group N] [module S N]
variable {q : ℕ}

namespace exterior_algebra
open tensor_algebra

/--
An inductively defined relation on `tensor_algebra R M` used to define the exterior algebra.
-/
inductive rel : tensor_algebra R M → tensor_algebra R M → Prop
| of (m : M) : rel ((ι R M m) * (ι R M m)) 0
| eq_compat {a} : rel a a
| add_compat_left {a b c} : rel a b → rel (a + c) (b + c)
| add_compat_right {a b c} : rel a b → rel (c + a) (c + b)
| mul_compat_left {a b c} : rel a b → rel (a * c) (b * c)
| mul_compat_right {a b c} : rel a b → rel (c * a) (c * b)

end exterior_algebra

/--
The exterior algebra of an `R`-semimodule `M`.
-/
def exterior_algebra := quot (exterior_algebra.rel R M)

namespace exterior_algebra


instance : semiring (exterior_algebra R M) :=
{ add := quot.map₂ (+) (λ _ _ _, rel.add_compat_right) (λ _ _ _, rel.add_compat_left),
  add_assoc := by {rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw add_assoc, refl},
  zero := quot.mk _ 0,
  zero_add := by {rintros ⟨⟩, change quot.mk _ _ = _, rw zero_add },
  add_zero := by {rintros ⟨⟩, change quot.mk _ _ = _, rw add_zero },
  add_comm := by {rintros ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw add_comm, refl },
  mul := quot.map₂ (*) (λ _ _ _, rel.mul_compat_right) (λ _ _ _, rel.mul_compat_left),
  mul_assoc := by {rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw mul_assoc, refl },
  one := quot.mk _ 1,
  one_mul := by {rintros ⟨⟩, change quot.mk _ _ = _, rw one_mul },
  mul_one := by {rintros ⟨⟩, change quot.mk _ _ = _, rw mul_one },
  zero_mul := by {rintros ⟨⟩, change quot.mk _ _ = _, rw zero_mul },
  mul_zero := by {rintros ⟨⟩, change quot.mk _ _ = _, rw mul_zero },
  left_distrib := by {rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw left_distrib, refl },
  right_distrib := by {rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw right_distrib, refl } }

instance : inhabited (exterior_algebra R M) := ⟨0⟩

instance : has_scalar R (exterior_algebra R M) :=
{ smul := λ r m, quot.lift_on m (λ x, quot.mk _ $ r • x) $
  λ a b h, by {simp_rw algebra.smul_def, exact quot.sound (rel.mul_compat_right h)} }

instance : algebra R (exterior_algebra R M) :=
{ to_fun := λ r, (quot.mk _ $ algebra_map _ _ r),
  map_one' := rfl,
  map_mul' := λ _ _, by {rw ring_hom.map_mul, refl },
  map_zero' := rfl,
  map_add' := λ _ _, by {rw ring_hom.map_add, refl },
  commutes' := begin
    rintros r ⟨⟩,
    change quot.mk _ _ = _,
    rw algebra.commutes r x,
    refl,
  end,
  smul_def' := begin
    rintros r ⟨⟩,
    change quot.mk _ _ = _,
    rw algebra.smul_def,
    refl,
  end }

instance : add_comm_group (exterior_algebra S N) :=
{ add := semiring.add,
  add_assoc := semiring.add_assoc,
  zero := semiring.zero,
  zero_add := semiring.zero_add,
  add_zero := semiring.add_zero,
  neg := λ v, (-1 : S) • v,
  add_left_neg := quot.ind
  begin
    intro a,
    apply quot.sound,
    rw [←one_smul S a, smul_smul, ←add_smul],
    norm_num,
    exact rel.eq_compat,
  end,
  add_comm := semiring.add_comm }


instance : mul_action (units ℤ) (exterior_algebra S N) :=
{ smul := λ u : units ℤ, λ v, (u.val) • v,
  one_smul := mul_action.one_smul,
  mul_smul := λ x y b, mul_action.mul_smul x y b }

/--
The canonical quotient map `tensor_algebra R M → exterior_algebra R M`.
-/
protected def quot : tensor_algebra R M →ₐ[R] exterior_algebra R M :=
  by refine_struct { to_fun := λ m, quot.mk _ m }; tauto

/--
The canonical linear map `M →ₗ[R] exterior_algebra R M`.
-/
def ι : M →ₗ[R] exterior_algebra R M :=
  (exterior_algebra.quot R M).to_linear_map.comp (tensor_algebra.ι R M)

/--
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = 0`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `exterior_algebra R M` to `A`.
-/
def lift {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) :
  exterior_algebra R M →ₐ[R] A :=
{ to_fun := λ a, quot.lift_on a (tensor_algebra.lift R M f) $ λ x y h,
  begin
    induction h,
    { simp only [alg_hom.map_mul,tensor_algebra.ι_comp_lift',cond,alg_hom.map_zero] },
    repeat { simp only [alg_hom.map_add, h_ih] },
    repeat { simp only [alg_hom.map_mul, h_ih] },
    refl
  end,
  map_one' := by {change algebra_map _ _ _ = _, simp},
  map_mul' := begin
    rintros ⟨⟩ ⟨⟩,
    change tensor_algebra.lift _ _ _ _ = _,
    rw alg_hom.map_mul,
  end,
  map_zero' := by {change algebra_map _ _ _ = _, simp},
  map_add' := begin
    rintros ⟨⟩ ⟨⟩,
    change tensor_algebra.lift _ _ _ _ = _,
    rw alg_hom.map_add,
  end,
  commutes' := by tauto }

variables {R M}

@[simp]
theorem ι_comp_lift {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A)
  (cond : ∀ m, f m * f m = 0) : (lift R M f cond).to_linear_map.comp (ι R M) = f :=
  by {ext, refl}

@[simp]
theorem lift_unique {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A)
  (cond : ∀ m : M, f m * f m = 0)
  (g : exterior_algebra R M →ₐ[R] A) : g.to_linear_map.comp (ι R M) = f ↔ g = lift R M f cond :=
begin
  refine ⟨λ hyp, _, λ hyp, by rw [hyp, ι_comp_lift]⟩,
  ext,
  rcases x,
  change (g.comp (exterior_algebra.quot _ _)) _ = tensor_algebra.lift _ _ _ _,
  suffices : g.comp (exterior_algebra.quot R M) = tensor_algebra.lift R M f, by rw this,
  apply tensor_algebra.hom_ext,
  finish,
end

@[simp]
theorem ι_square_zero (m : M) : (ι R M m) * (ι R M m) = 0 := by apply quot.sound (rel.of _)

@[simp]
theorem comp_ι_square_zero {A: Type*} [semiring A] [algebra R A] (g : exterior_algebra R M →ₐ[R] A)
  (m : M) : (g.to_linear_map.comp (ι R M)) m * (g.to_linear_map.comp (ι R M)) m = 0 :=
begin
  change g _ * g _ = 0,
  rw [←alg_hom.map_mul, ι_square_zero, alg_hom.map_zero],
end

@[simp]
theorem lift_comp_ι {A : Type*} [semiring A] [algebra R A] (g : exterior_algebra R M →ₐ[R] A) :
  lift R M (g.to_linear_map.comp (ι R M)) (comp_ι_square_zero _) = g :=
  by {symmetry, rw ←lift_unique}

theorem hom_ext {A : Type*} [semiring A] [algebra R A] {f g : exterior_algebra R M →ₐ[R] A} :
  f.to_linear_map.comp (ι R M) = g.to_linear_map.comp (ι R M) → f = g :=
begin
  intro hyp,
  let h := g.to_linear_map.comp (ι R M),
  have : g = lift R M h (comp_ι_square_zero _), by rw ←lift_unique,
  rw [this, ←lift_unique, hyp],
end

lemma ι_add_mul (x y z : M) : ι R M (x + y) * ι R M z = ι R M x * ι R M z + ι R M y * ι R M z :=
by rw [linear_map.map_add, right_distrib]

lemma ι_mul_add (x y z : M) : ι R M x * ι R M (y + z) = ι R M x * ι R M y + ι R M x * ι R M z :=
by rw [linear_map.map_add, left_distrib]

@[simp]
lemma ι_add_swap (x y : M) : ι R M x * ι R M y + ι R M y * ι R M x = 0 :=
calc ι R M x * ι R M y + ι R M y * ι R M x
  = ι R M x * ι R M y + ι R M y * ι R M y + ι R M y * ι R M x :
    by rw [ι_square_zero, add_zero]
  ...= ι R M x * ι R M y + ι R M y * ι R M y + ι R M y * ι R M x + ι R M x * ι R M x :
    by rw [ι_square_zero x, add_zero]
  ...= ι R M (x + y) * ι R M y + ι R M y * ι R M x + ι R M x * ι R M x :
    by rw ι_add_mul
  ...= ι R M (x + y) * ι R M y + ι R M (x + y) * ι R M x :
    by rw [ι_add_mul x y x, ι_square_zero, zero_add, add_zero]
  ...= ι R M (x + y) * ι R M (x + y) :
    by rw [ι_mul_add (x + y) x y, add_comm]
  ...= 0 :
    by rw ι_square_zero

variables (R M)

/--
The canonical multilinear map from `fin q → M` into `exterior_algebra R M`.
-/
def wedge : multilinear_map R (λ i : fin q, M) (exterior_algebra R M) :=
{ to_fun := λ ν : fin q → M , quot.mk _ (tensor_algebra.mk R M ν),
  map_add' :=
    begin
      intros ν i x y,
      apply quot.sound,
      rw multilinear_map.map_add,
      exact rel.eq_compat
    end,
  map_smul' :=
    begin
      intros ν i r x,
      apply quot.sound,
      rw multilinear_map.map_smul,
      exact rel.eq_compat
    end }

variables {R M}

lemma wedge_split (ν : fin q.succ → M) :
wedge R M ν = ι R M (ν 0) * wedge R M (λ i : fin q, ν i.succ) :=
begin
  apply quot.sound,
  rw tensor_algebra.mk_split,
  exact rel.eq_compat
end

/--
Auxiliary lemma used to prove `wedge_self_adj`.
-/
lemma wedge_self_adj_aux (ν : fin q.succ → M) {j : fin q.succ} (hj : j.val = 1) (hv : ν 0 = ν j):
ι R M (ν 0) * wedge R M (λ i : fin q, ν i.succ) = 0 :=
begin
  induction q with q hq,
  --Base case (we get a contradiction)
  exfalso,
  exact not_lt_of_le (le_of_eq (eq_comm.mp hj)) j.2,
  --Inductive step
  rw wedge_split,
  have hj1 : j = 1 :=
  begin
    ext, exact hj,
  end,
  have fact : ν (0 : fin q.succ).succ = ν 1 := by congr,
  rw fact, rw hj1 at hv, rw hv, rw ←mul_assoc, rw ι_square_zero, rw zero_mul,
end


lemma wedge_self_adj (ν : fin q → M) (i j : fin q) (hij : i.val + 1 = j.val) (hv : ν i = ν j) :
wedge R M ν = 0 :=
begin
  induction q with q hq,
  --Base case (there is nothing to show)
  cases i, exfalso, exact nat.not_lt_zero i_val i_is_lt,
  --Inductive step
  rw wedge_split,
  cases classical.em (i = 0) with hem hem,
  --case i = 0
  rw hem at hv,
  rw hem at hij, norm_num at hij, rw eq_comm at hij,
  exact wedge_self_adj_aux ν hij hv,
  --case i ≠ 0
  have hj : j ≠ 0 :=
  begin
    intro cj, rw cj at hij, simp at hij, assumption,
  end,
  have hij1 : (i.pred hem).val.succ = (j.pred hj).val :=
    by rw [←fin.succ_val, fin.succ_pred, fin.pred_val, ←hij, nat.pred_succ],
  have hv1 : (ν ∘ fin.succ) (i.pred hem) = (ν ∘ fin.succ) (j.pred hj) := by simp [hv],
  rw hq (ν ∘ fin.succ) (i.pred hem) (j.pred hj) hij1 hv1,
  rw mul_zero,
end



lemma wedge_add_swap_adj (ν : fin q → M) {i j : fin q} (hij : i.val + 1 = j.val) :
wedge R M ν + wedge R M (ν ∘ equiv.swap i j) = 0 :=
begin
  have hij1 : i ≠ j :=
  begin
    intro h,
    rw h at hij, exact nat.succ_ne_self j.val hij,
  end,
  have key : wedge R M (function.update (function.update ν i (ν i + ν j)) j (ν i + ν j)) = 0 :=
    by rw wedge_self_adj (function.update (function.update ν i (ν i + ν j)) j (ν i + ν j)) i j hij
    begin
      rw [function.update_same, function.update_noteq hij1,  function.update_same],
    end,
  rw multilinear_map.map_add at key,
  rw function.update_comm hij1 (ν i + ν j) (ν i) ν at key,
  rw multilinear_map.map_add at key,
  rw wedge_self_adj (function.update (function.update ν j (ν i)) i (ν i)) i j hij
    begin
      rw function.update_same,
      rw function.update_comm (ne_comm.mp hij1) (ν i) (ν i) ν,
      rw function.update_same,
    end at key,
  rw zero_add at key,
  rw function.update_comm hij1 (ν i + ν j) (ν j) ν at key,
  rw multilinear_map.map_add at key,
  rw wedge_self_adj (function.update (function.update ν j (ν j)) i (ν j)) i j hij
  begin
    rw function.update_same,
    rw function.update_comm (ne_comm.mp hij1) (ν j) (ν j) ν,
    rw function.update_same,
  end at key,
  rw add_zero at key,
  rw add_comm at key,
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
    rw function.update_noteq (ne_comm.mp hij1),
    simp,
    --case x ≠ i, x ≠ j,
    simp only [hx, hx1, function.comp_app, function.update_noteq, ne.def, not_false_iff],
    rw equiv.swap_apply_of_ne_of_ne hx hx1,
end



lemma wedge_swap_adj (ν : fin q → N) {i j : fin q} (hij : i.val + 1 = j.val) :
wedge S N (ν ∘ equiv.swap i j) = - wedge S N ν  :=
begin
  apply eq_neg_of_add_eq_zero,
  rw add_comm,
  exact wedge_add_swap_adj ν hij,
end


lemma wedge_perm (ν : fin q → N) (σ : equiv.perm (fin q)) :
wedge S N ν = (equiv.perm.sign σ) • wedge S N (ν ∘ σ) :=
begin
  apply equiv.perm.swap_adj_induction_on' σ,
  --Base case
  rw [equiv.perm.sign_one, one_smul], congr,
  --Inductive step
  intros f x y hxy hI,
  have hxy1 : x ≠ y :=
  begin
    intro h, rw h at hxy, exact (nat.succ_ne_self y.val) hxy,
  end,
  have assoc : ν ∘ (f * equiv.swap x y : equiv.perm (fin q)) = (ν ∘ f ∘ equiv.swap x y) := rfl,
  rw [assoc, wedge_swap_adj (ν ∘ f) hxy, ←neg_one_smul ℤ (wedge S N (ν ∘ f))],
  have h1 : (-1 : ℤ) = equiv.perm.sign (equiv.swap x y) := by simp [hxy1],
  rw h1,
  have hack : ∀ z : exterior_algebra S N,
  (equiv.perm.sign (f * equiv.swap x y) : units ℤ) • z =
  (equiv.perm.sign (f * equiv.swap x y) : ℤ) • z := λ z, rfl,
  rw hack,
  rw [smul_smul, ←units.coe_mul, ←equiv.perm.sign_mul, mul_assoc, equiv.swap_mul_self, mul_one],
  assumption,
end

end exterior_algebra
