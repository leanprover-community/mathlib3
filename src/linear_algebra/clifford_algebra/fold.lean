/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.conjugation

/-!
# Recursive computation rules for the Clifford algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides API for a special case `clifford_algebra.foldr` of the universal property
`clifford_algebra.lift` with `A = module.End R N` for some arbitrary module `N`. This specialization
resembles the `list.foldr` operation, allowing a bilinear map to be "folded" along the generators.

For convenience, this file also provides `clifford_algebra.foldl`, implemented via
`clifford_algebra.reverse`

## Main definitions

* `clifford_algebra.foldr`: a computation rule for building linear maps out of the clifford
  algebra starting on the right, analogous to using `list.foldr` on the generators.
* `clifford_algebra.foldl`: a computation rule for building linear maps out of the clifford
  algebra starting on the left, analogous to using `list.foldl` on the generators.

## Main statements

* `clifford_algebra.right_induction`: an induction rule that adds generators from the right.
* `clifford_algebra.left_induction`: an induction rule that adds generators from the left.
-/

universes u1 u2 u3

variables {R M N : Type*}
variables [comm_ring R] [add_comm_group M] [add_comm_group N]
variables [module R M] [module R N]
variables (Q : quadratic_form R M)

namespace clifford_algebra

section foldr

/-- Fold a bilinear map along the generators of a term of the clifford algebra, with the rule
given by `foldr Q f hf n (ι Q m * x) = f m (foldr Q f hf n x)`.

For example, `foldr f hf n (r • ι R u + ι R v * ι R w) = r • f u n + f v (f w n)`. -/
def foldr (f : M →ₗ[R] N →ₗ[R] N) (hf : ∀ m x, f m (f m x) = Q m • x) :
  N →ₗ[R] clifford_algebra Q →ₗ[R] N :=
(clifford_algebra.lift Q ⟨f, λ v, linear_map.ext $ hf v⟩).to_linear_map.flip

@[simp] lemma foldr_ι (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (m : M) :
  foldr Q f hf n (ι Q m) = f m n :=
linear_map.congr_fun (lift_ι_apply _ _ _) n

@[simp] lemma foldr_algebra_map (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (r : R) :
  foldr Q f hf n (algebra_map R _ r) = r • n :=
linear_map.congr_fun (alg_hom.commutes _ r) n

@[simp] lemma foldr_one (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) :
  foldr Q f hf n 1 = n :=
linear_map.congr_fun (alg_hom.map_one _) n

@[simp] lemma foldr_mul (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (a b : clifford_algebra Q) :
  foldr Q f hf n (a * b) = foldr Q f hf (foldr Q f hf n b) a :=
linear_map.congr_fun (alg_hom.map_mul _ _ _) n


/-- This lemma demonstrates the origin of the `foldr` name. -/
lemma foldr_prod_map_ι (l : list M) (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N):
  foldr Q f hf n (l.map $ ι Q).prod = list.foldr (λ m n, f m n) n l :=
begin
  induction l with hd tl ih,
  { rw [list.map_nil, list.prod_nil, list.foldr_nil, foldr_one] },
  { rw [list.map_cons, list.prod_cons, list.foldr_cons, foldr_mul, foldr_ι, ih] },
end

end foldr

section foldl

/-- Fold a bilinear map along the generators of a term of the clifford algebra, with the rule
given by `foldl Q f hf n (ι Q m * x) = f m (foldl Q f hf n x)`.

For example, `foldl f hf n (r • ι R u + ι R v * ι R w) = r • f u n + f v (f w n)`. -/
def foldl (f : M →ₗ[R] N →ₗ[R] N) (hf : ∀ m x, f m (f m x) = Q m • x) :
  N →ₗ[R] clifford_algebra Q →ₗ[R] N :=
linear_map.compl₂ (foldr Q f hf) reverse

@[simp] lemma foldl_reverse (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (x : clifford_algebra Q) :
  foldl Q f hf n (reverse x) = foldr Q f hf n x :=
fun_like.congr_arg (foldr Q f hf n) $ reverse_reverse _

@[simp] lemma foldr_reverse (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (x : clifford_algebra Q) :
  foldr Q f hf n (reverse x) = foldl Q f hf n x := rfl

@[simp] lemma foldl_ι (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (m : M) :
  foldl Q f hf n (ι Q m) = f m n :=
by rw [←foldr_reverse, reverse_ι, foldr_ι]

@[simp] lemma foldl_algebra_map (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (r : R) :
  foldl Q f hf n (algebra_map R _ r) = r • n :=
by rw [←foldr_reverse, reverse.commutes, foldr_algebra_map]

@[simp] lemma foldl_one (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) :
  foldl Q f hf n 1 = n :=
by rw [←foldr_reverse, reverse.map_one, foldr_one]

@[simp] lemma foldl_mul (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (a b : clifford_algebra Q) :
  foldl Q f hf n (a * b) = foldl Q f hf (foldl Q f hf n a) b :=
by rw [←foldr_reverse, ←foldr_reverse, ←foldr_reverse, reverse.map_mul, foldr_mul]

/-- This lemma demonstrates the origin of the `foldl` name. -/
lemma foldl_prod_map_ι (l : list M) (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N):
  foldl Q f hf n (l.map $ ι Q).prod = list.foldl (λ m n, f n m) n l :=
by rw [←foldr_reverse, reverse_prod_map_ι, ←list.map_reverse, foldr_prod_map_ι, list.foldr_reverse]

end foldl

lemma right_induction {P : clifford_algebra Q → Prop}
  (hr : ∀ r : R, P (algebra_map _ _ r))
  (h_add : ∀ x y, P x → P y → P (x + y))
  (h_ι_mul : ∀ m x, P x → P (x * ι Q m)) : ∀ x, P x :=
begin
  /- It would be neat if we could prove this via `foldr` like how we prove
  `clifford_algebra.induction`, but going via the grading seems easier. -/
  intro x,
  have : x ∈ ⊤ := submodule.mem_top,
  rw ←supr_ι_range_eq_top at this,
  apply submodule.supr_induction _ this (λ i x hx, _) _ h_add,
  { refine submodule.pow_induction_on_right _ hr h_add (λ x px m, _) hx,
    rintro ⟨m, rfl⟩,
    exact h_ι_mul _ _ px },
  { simpa only [map_zero] using hr 0}
end

lemma left_induction {P : clifford_algebra Q → Prop}
  (hr : ∀ r : R, P (algebra_map _ _ r))
  (h_add : ∀ x y, P x → P y → P (x + y))
  (h_mul_ι : ∀ x m, P x → P (ι Q m * x)) : ∀ x, P x :=
begin
  refine reverse_involutive.surjective.forall.2 _,
  intro x,
  induction x using clifford_algebra.right_induction with r x y hx hy m x hx,
  { simpa only [reverse.commutes] using hr r },
  { simpa only [map_add] using h_add _ _ hx hy },
  { simpa only [reverse.map_mul, reverse_ι] using h_mul_ι _ _ hx },
end

/-! ### Versions with extra state -/
/-- Auxiliary definition for `clifford_algebra.foldr'` -/
def foldr'_aux (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N) :
  M →ₗ[R] module.End R (clifford_algebra Q × N) :=
begin
  have v_mul := (algebra.lmul R (clifford_algebra Q)).to_linear_map ∘ₗ (ι Q),
  have l := v_mul.compl₂ (linear_map.fst _ _ N),
  exact { to_fun := λ m, (l m).prod (f m),
          map_add' := λ v₂ v₂, linear_map.ext $ λ x, prod.ext
            (linear_map.congr_fun (l.map_add _ _) x) (linear_map.congr_fun (f.map_add _ _) x),
          map_smul' := λ c v, linear_map.ext $ λ x, prod.ext
            (linear_map.congr_fun (l.map_smul _ _) x) (linear_map.congr_fun (f.map_smul _ _) x), },
end

lemma foldr'_aux_apply_apply (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N) (m : M) (x_fx) :
    foldr'_aux Q f m x_fx = (ι Q m * x_fx.1, f m x_fx) := rfl

lemma foldr'_aux_foldr'_aux (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx)
  (v : M) (x_fx) :
  foldr'_aux Q f v (foldr'_aux Q f v x_fx) = Q v • x_fx :=
begin
  cases x_fx with x fx,
  simp only [foldr'_aux_apply_apply],
  rw [←mul_assoc, ι_sq_scalar, ← algebra.smul_def, hf, prod.smul_mk],
end

/-- Fold a bilinear map along the generators of a term of the clifford algebra, with the rule
given by `foldr' Q f hf n (ι Q m * x) = f m (x, foldr' Q f hf n x)`.
Note this is like `clifford_algebra.foldr`, but with an extra `x` argument.
Implement the recursion scheme `F[n0](m * x) = f(m, (x, F[n0](x)))`. -/
def foldr' (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx)
  (n : N) :
  clifford_algebra Q →ₗ[R] N :=
linear_map.snd _ _ _ ∘ₗ foldr Q (foldr'_aux Q f) (foldr'_aux_foldr'_aux Q _ hf) (1, n)

lemma foldr'_algebra_map (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n r) :
  foldr' Q f hf n (algebra_map R _ r) = r • n :=
congr_arg prod.snd (foldr_algebra_map _ _ _ _ _)

lemma foldr'_ι (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) :
  foldr' Q f hf n (ι Q m) = f m (1, n) :=
congr_arg prod.snd (foldr_ι _ _ _ _ _)

lemma foldr'_ι_mul (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) (x) :
  foldr' Q f hf n (ι Q m * x) = f m (x, foldr' Q f hf n x) :=
begin
  dsimp [foldr'],
  rw [foldr_mul, foldr_ι, foldr'_aux_apply_apply],
  refine congr_arg (f m) (prod.mk.eta.symm.trans _),
  congr' 1,
  induction x using clifford_algebra.left_induction with r x y hx hy m x hx,
  { simp_rw [foldr_algebra_map, prod.smul_mk, algebra.algebra_map_eq_smul_one] },
  { rw [map_add, prod.fst_add, hx, hy] },
  { rw [foldr_mul, foldr_ι, foldr'_aux_apply_apply, hx], },
end

end clifford_algebra
