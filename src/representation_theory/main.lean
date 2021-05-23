/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import linear_algebra.pi
import ring_theory.simple_module
import algebra.direct_sum
import linear_algebra.matrix

universes u v w
open_locale direct_sum classical big_operators
open classical linear_map
noncomputable theory
/-!
# Simple Modules



-/

def right_mul_lmap {R : Type*} [semiring R] (r : R) : R →ₗ[R] R :=
{ to_fun := λ s, s * r,
  map_add' := λ _ _, add_mul _ _ _,
  map_smul' := λ t s, mul_assoc _ _ _ }

@[simp] lemma right_mul_lmap_apply  {R : Type*} [semiring R] (r s : R) :
  right_mul_lmap r s = s * r := rfl

def End_equiv_opposite {R M : Type*} [semiring R] [add_comm_monoid M] [module R M] :
  Rᵒᵖ ≃+* module.End R R :=
{ to_fun := λ a, right_mul_lmap (opposite.unop a),
  inv_fun := λ f, opposite.op (f 1),
  left_inv := λ x, by { simp, },
  right_inv := λ x, by { ext, simp, },
  map_mul' := λ x y, by { ext, simp, },
  map_add' := λ x y, by { ext, simp} }

def linear_map.co_lsum_add_equiv (R M : Type*) {ι : Type*} [fintype ι] [decidable_eq ι]
  [semiring R] [add_comm_monoid M] [module R M] (φ : ι → Type*)
  [Π (i : ι), add_comm_monoid (φ i)] [Π (i : ι), module R (φ i)] :
  (Π i, M →ₗ[R] φ i) ≃+ (M →ₗ[R] Π i, φ i) :=
{ to_fun := λ x, linear_map.pi x,
  map_add' := sorry, -- λ x y, by { ext, simp, },
  inv_fun := λ x i,
  { to_fun := λ m, x m i,
    map_add' := λ a b, by { sorry },
    map_smul' := λ s a, by { sorry } },
  left_inv := λ x, by { ext, sorry, },
  right_inv := λ x, by { ext, sorry, } }

def linear_map.co_lsum (R S M : Type*) {ι : Type*} [fintype ι] [decidable_eq ι]
  [semiring R] [add_comm_monoid M] [module R M] (φ : ι → Type*)
  [Π (i : ι), add_comm_monoid (φ i)] [Π (i : ι), module R (φ i)]
  [semiring S] [Π i, module S (φ i)] [Π i, smul_comm_class R S (φ i)] :
  (Π i, M →ₗ[R] φ i) ≃ₗ[S] (M →ₗ[R] Π i, φ i) :=
{ to_fun := λ x, linear_map.pi x,
  map_add' := sorry, -- λ x y, by { ext, simp, },
  map_smul' := sorry, -- λ s x, by { ext, simp, },
  inv_fun := λ x i,
  { to_fun := λ m, x m i,
    map_add' := λ a b, by { sorry },
    map_smul' := λ s a, by { sorry } },
  left_inv := λ x, by { ext, sorry, },
  right_inv := λ x, by { ext, sorry, } }

def linear_map.pi_inv (R M : Type*) {ι : Type*} [fintype ι] [decidable_eq ι]
  [semiring R] [add_comm_monoid M] [module R M] (φ : ι → Type*)
  [Π (i : ι), add_comm_monoid (φ i)] [Π (i : ι), module R (φ i)] :
  (M →ₗ[R] (Π i, φ i)) → Π i, M →ₗ[R] φ i :=
λ f i,
{ to_fun := λ m, f m i,
  map_add' := λ x y, by { simp, },
  map_smul' := λ s x, by { simp, } }

def linear_map.fun_congr_right (R : Type*) {M N : Type*} (n : Type*) [fintype n]
  [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N] (e : M ≃ₗ[R] N) :
  (n → M) ≃ₗ[R] n → N :=
{ to_fun := λ x i, e (x i),
  map_add' := λ x y, by { ext, sorry },
  map_smul' := λ s y, by { ext, sorry },
  inv_fun := λ x i, e.symm (x i),
  left_inv := λ x, by { ext, sorry },
  right_inv := λ x, by { ext, sorry } }

def add_monoid_hom.pi {ι : Type*} (M : Type*) [fintype ι] [decidable_eq ι]
  (φ : ι → Type*) [Π i, add_comm_monoid (φ i)] [add_comm_monoid M] :
  (Π i, M →+ φ i) → (M →+ Π i, φ i) :=
λ x,
{ to_fun := λ m i, x i m,
  map_zero' := sorry,
  map_add' := sorry }


def add_monoid_hom.co_lsum {ι : Type*} (M : Type*) [fintype ι] [decidable_eq ι]
  (φ : ι → Type*) [Π i, add_comm_monoid (φ i)] [add_comm_monoid M] :
  (Π i, M →+ φ i) ≃+ (M →+ Π i, φ i) :=
{ to_fun := λ x, add_monoid_hom.pi _ _ x,
  inv_fun := λ x i,
  { to_fun := λ m, x m i,
    map_zero' := sorry,
    map_add' := sorry },
  left_inv := sorry,
  right_inv := sorry,
  map_add' := sorry }


def add_monoid_hom.fun_congr_right {M N : Type*} (n : Type*) [fintype n]
  [add_comm_monoid M] [add_comm_monoid N] (e : M ≃+ N) :
  (n → M) ≃+ (n → N) :=
{ to_fun := λ x i, e (x i),
  map_add' := λ x y, by { ext, sorry },
  inv_fun := λ x i, e.symm (x i),
  left_inv := λ x, by { ext, sorry },
  right_inv := λ x, by { ext, sorry } }

variables {F A M : Type*} [field F] [ring A] [add_comm_monoid M]
variables [module A M]

instance module.End.module {R M S : Type*}
  [semiring R] [semiring S] [add_comm_monoid M]
  [module R M] [module S M] [smul_comm_class R S M] :
module S (module.End R M) := linear_map.module

instance exist_or_no {n : Type*} [fintype n] {S : Type*} [add_comm_group S] [module A S]
  [is_simple_module A S] : module A (module.End A S) :=
{ smul := λ a f, _,
  one_smul := _,
  mul_smul := _,
  smul_add := _,
  smul_zero := _,
  add_smul := _,
  zero_smul := _ }

@[simp] lemma add_monoid_hom.apply_single {ι M : Type*} [fintype ι] [decidable_eq ι]
  {φ : ι → Type*} [Π i, add_comm_monoid (φ i)] [add_comm_monoid M]
  (f : Π (i : ι), φ i →+ M) (i j : ι) (x : φ i) :
  f j (pi.single i x j) = pi.single i (f i x) j :=
sorry

def linear_map.lsum' (R M ι : Type*) [semiring R] (φ : ι → Type*) [Π (i : ι), add_comm_monoid (φ i)] [Π (i : ι), module R (φ i)] (S : Type*) [add_comm_monoid M] [module R M] [fintype ι] [decidable_eq ι] [semiring S] [module S M] [smul_comm_class R S M] :
  (Π (i : ι), φ i →ₗ[R] M) ≃ₗ[S] (Π (i : ι), φ i) →ₗ[R] M :=
{ to_fun := λ f, ∑ i : ι, (f i).comp (proj i),
  map_add' := sorry,
  map_smul' := sorry,
  inv_fun := λ f i, f.comp (single i),
  left_inv := λ f, by { ext i x, simp, simp only [apply_single, finset.mem_univ, if_true, finset.sum_pi_single'], },
  right_inv := _ }


@[simps] def add_monoid_hom.lsum {ι : Type*} (M : Type*) [fintype ι] [decidable_eq ι]
  (φ : ι → Type*) [Π i, add_comm_monoid (φ i)] [add_comm_monoid M] :
  (Π i, φ i →+ M) ≃+ ((Π i, φ i) →+ M) :=
{ to_fun := λ f, ∑ i : ι, (f i).comp (add_monoid_hom.apply _ i),
  inv_fun := λ f i, f.comp (add_monoid_hom.single _ i),
  left_inv := λ x, by { ext i φi,
    simp only [add_monoid_hom.finset_sum_apply, add_monoid_hom.coe_comp,
    add_monoid_hom.apply_apply, function.comp_app, add_monoid_hom.single_apply,
    add_monoid_hom.apply_single, finset.mem_univ, if_true, finset.sum_pi_single'], },
  right_inv := sorry,
  map_add' := sorry }

@[simp] lemma sum_pi_single'' {ι : Type*} {M : ι → Type*}
  [decidable_eq ι] [Π i, add_comm_monoid (M i)] (i : ι) (f : Π i, M i) (s : finset ι) :
  ∑ j in s, pi.single j (f j) i = if i ∈ s then f i else 0 :=
finset.sum_dite_eq _ _ _

lemma helpful_lemma {n : Type*} [fintype n] {R E : Type*}
  [semiring R] [add_comm_monoid E] [module R E] (f : module.End R (n → E)) (v : n → n → E) (j : n) :
  ∑ i, f (v i) j = f (∑ i, v i) j :=
begin
  simp only [fintype.sum_apply, map_sum],
end

def equiv_to_matrix (n : Type u) [fintype n] (R : Type v) (E : Type w)
  [semiring R] [add_comm_monoid E] [module R E] :
  module.End R (n → E) ≃+* matrix n n (module.End R E) :=
{ to_fun := λ f j i,
  { to_fun := λ e, f (pi.single i e) j,
    map_add' := sorry,
    map_smul' := sorry },
  map_add' := _,
  map_mul' := λ x y,
  begin
    ext j i e,
    rw matrix.mul_eq_mul,
    rw matrix.mul_apply,
    simp only [coe_fn_sum, mul_apply, coe_mk, fintype.sum_apply],
    rw helpful_lemma, congr, ext k,
    simp only [finset.mem_univ, if_true, fintype.sum_apply, sum_pi_single''],
  end,
  inv_fun := λ M,
  { to_fun := λ f j, ∑ i : n, (M j i) (f i),
    map_add' := sorry,
    map_smul' := sorry },
  left_inv := /-λ x,-/
  /-begin
    ext i e j,
    simp only [coe_single, coe_mk, function.comp_app, coe_comp],
    have h4 : ∑ (k : n), x (pi.single k (pi.single i e k)) j = ∑ (k : n), ite (k = i) (x (pi.single k e) j) 0,
    refine finset.sum_congr rfl (λ k hk, _),
    split_ifs,
    { congr, rw h, simp only [pi.single_eq_same], },
    rw pi.single_eq_of_ne h _,
    simp only [pi.zero_apply, pi.single_zero, map_zero],
    rw h4, simp only [finset.mem_univ, if_true, finset.sum_ite_eq'],
  end-/ sorry,
  right_inv := _ }
--((linear_map.fun_congr_right ℕ n (linear_map.co_lsum R ℕ E (λ i : n, E))).trans
  --(lsum R (λ i : n, E) ℕ)).symm
