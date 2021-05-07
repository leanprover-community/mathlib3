/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import representation_theory.pi_map
import linear_algebra.finite_dimensional

open_locale direct_sum classical big_operators
open classical linear_map finite_dimensional
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
variables [algebra F A] [module A M]
variables [finite_dimensional F A]

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

def equiv_to_matrix {n : Type*} [fintype n] {R E : Type*}
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

/- lemma equiv_to_matrix_apply {n : Type*} [fintype n] {R E : Type*}
  [semiring R] [add_comm_monoid E] [module R E] (i j : n)
  (f : module.End R (n → E)) : equiv_to_matrix f i j = 0 :=
begin
  ext x,
  rw equiv_to_matrix,
  simp [lsum, linear_map.co_lsum, linear_map.fun_congr_right],
  dsimp,
end

lemma equiv_to_matrix_mul {n : Type*} [fintype n] {R E : Type*}
  [semiring R] [add_comm_monoid E] [module R E] (x y : module.End R (n → E)) :
  equiv_to_matrix (x * y) = equiv_to_matrix x * equiv_to_matrix y :=
begin
  ext i k B,
  rw matrix.mul_eq_mul,
  rw matrix.mul_apply,
  sorry
end

def equiv_to_matrix' {n : Type*} [fintype n] {R E : Type*}
  [semiring R] [add_comm_monoid E] [module R E] :
  module.End R (n → E) ≃+* matrix n n (module.End R E) :=
{ to_fun := equiv_to_matrix,
  inv_fun := equiv_to_matrix.symm,
  left_inv := λ x, by simp only [linear_equiv.symm_apply_apply],
  right_inv := λ x, by simp only [linear_equiv.apply_symm_apply],
  map_mul' := equiv_to_matrix_mul,
  map_add' := λ x y, by { ext, simp only [linear_equiv.map_add], } } -/

variables (A)

instance submodule.setoid : setoid (submodule A A) :=
{ r := λ n m, nonempty (n ≃ₗ[A] m),
  iseqv := ⟨λ x, ⟨linear_equiv.refl A x⟩, λ x y h, ⟨h.some.symm⟩,
    λ x y z hxy hyz, ⟨hxy.some.trans hyz.some⟩⟩ }

def atom_setoid := subtype.setoid (λ s : submodule A A, is_atom s)
def atom_quot := quotient $ atom_setoid A

def setoid.class {α : Type*} (r : setoid α) (y : α) := {x : α | r.rel x y}

/-

variables {D : Type*} [field D] {n : Type*} [fintype n] [decidable_eq n]

instance matrix_smul : module (matrix n n D) (n → D) :=
{ smul := matrix.mul_vec,
  one_smul := λ v, by simp only [matrix.mul_vec_one],
  mul_smul := λ x y v, by simp only [matrix.mul_vec_mul_vec, matrix.mul_eq_mul],
  smul_add := matrix.mul_vec_add,
  smul_zero := matrix.mul_vec_zero,
  add_smul := matrix.add_mul_vec,
  zero_smul := λ v, by { ext, simp, rw ← matrix.diagonal_zero, rw matrix.mul_vec_diagonal, simp, } }

def dfinsupp.equiv_fun_on_fintype {ι : Type*} {M : ι → Type*} [∀ i, has_zero (M i)] [fintype ι] :
  (Π₀ i, M i) ≃ (Π i, M i) :=
{ to_fun := λ f a, f a,
  inv_fun := λ f, dfinsupp.mk finset.univ (λ x, f x),
  left_inv := λ f, by { ext, simp, congr, },
  right_inv := λ f, by { ext, simp, congr, }, }

def pi.to_dfinsupp_of_fintype {ι : Type*} {M : ι → Type*} [∀ i, has_zero (M i)] [fintype ι] :
  (Π i, M i) ≃ (Π₀ i, M i) := dfinsupp.equiv_fun_on_fintype.symm

def transport_one {α β : Type*} [hα : has_one α] (h : α ≃ β) : has_one β :=
{ one := h hα.one }

def transport_monoid {α β : Type*} [hα : mul_one_class α] (h : α ≃ β) : mul_one_class β :=
{! !}

instance semiring_direct_sum {ι : Type*} {D : ι → Type*} [∀ i, semiring (D i)] :
  semiring (Π₀ (i : ι), D i) := sorry

variables (R : Type*) [comm_ring R] (A : Type*) [comm_ring A] [algebra R A] [algebra R D]

instance boo : algebra R (matrix n n D) := by apply_instance

instance submodule.setoid : setoid (submodule A A) :=
{ r := λ n m, nonempty (n ≃ₗ[A] m),
  iseqv := ⟨λ x, ⟨linear_equiv.refl A x⟩, λ x y h, ⟨h.some.symm⟩,
    λ x y z hxy hyz, ⟨hxy.some.trans hyz.some⟩⟩ }

def atom_setoid := subtype.setoid (λ s : submodule A A, is_atom s)
def atom_quot := quotient $ atom_setoid A

def setoid.class {α : Type*} (r : setoid α) (y : α) := {x : α | r.rel x y}

#check λ s, ((atom_setoid A).class s).

def decompose : A ≃ₗ[A] Π s : atom_quot A, (Π i : (atom_setoid A).class s.out, i.val) := sorry

def decompose' :
  A ≃ₗ[A] Π s : atom_quot A, (⨆ i : (atom_setoid A).class s.out, i.val : submodule A A) := sorry

variables (p : submodule A A) (s : atom_quot A) (a : (atom_setoid A).class s.out)
#check a.val.val
#check supr (λ a : (atom_setoid A).class s.out, a.val.val)
#check Sup ((submodule.setoid A).class p)
#check (submodule.setoid A).class p

def decompose'' [nontrivial A] (s : atom_quot A) :
  (Π i : (atom_setoid A).class s.out, i.val) ≃ₗ[A]
  (⨆ i : (atom_setoid A).class s.out, i.val : submodule A A) :=
begin
  haveI : fintype ((atom_setoid A).class s.out) := sorry,
  convert submodule.prod_equiv_of_independent (λ i : (atom_setoid A).class s.out, i.val.val) _,
  sorry,
end

lemma submodule.mem_coe_supr {ι : Type*} [fintype ι] {s : ι → submodule A A} (x : Π i : ι, s i) :
  ∑ i, (x i).val ∈ supr s :=
begin
  rw submodule.mem_supr,
  intros t ht,
  apply submodule.sum_mem,
  intros i hi,
  exact ht i (x i).2,
end

def decompose''' {ι : Type*} [fintype ι] {s : ι → submodule A A} (h : complete_lattice.independent s) :
  (Π i : ι, s i) ≃ₗ[A] (supr s : submodule A A) :=
{ to_fun := λ x, ⟨∑ i, (x i).val, submodule.mem_coe_supr A x⟩,
  map_add' := λ x y, by { ext, simp [finset.sum_add_distrib] },
  map_smul' := λ a x, by { ext, simp [finset.mul_sum], },
  inv_fun := λ x i, ⟨_, _⟩,
  left_inv := _,
  right_inv := _ }

def decompose'''' {ι : Type*} [fintype ι] {s t : submodule A A} (h : s ⊓ t = ⊥) :
  (s × t) ≃ₗ[A] (s ⊔ t : submodule A A) :=
{ to_fun := λ x, ⟨x.1.val + x.2.val, sorry⟩,
  map_add' := sorry,
  map_smul' := sorry,
  inv_fun := λ x, _,
  left_inv := _,
  right_inv := _ }






lemma lem21a : is_simple_module (matrix n n D) (n → D) := sorry

def lem21b : matrix n n D ≃ₗ[matrix n n D] (⨁ (i : n), n → D) := sorry

lemma thm21a {ι : Type*} {D : ι → Type*} [∀ i, division_ring (D i)] :
  is_semisimple_module (Π (i : ι), matrix n n (D i)) (Π (i : ι), matrix n n (D i)) := sorry

lemma direct_sum_equiv_Sup {ι : Type*} (s : ι → submodule A A) (h : complete_lattice.independent s) :
  (Π i, s i) ≃ ↥(supr s) :=
begin
  sorry
end



lemma thm31 {ι : Type*} (f : ι → submodule A A) :
  is_semisimple_module A A → ∃ (s : set (submodule A A)),
  ∀ n : submodule A A, is_simple_module A n → n ∈ s :=
begin

  sorry
end


instance bruh {ι : Type*} (R : ι → Type*) [∀ i, comm_semiring (R i)]
  {A : ι → Type*} [∀ i, semiring (A i)] [hRA : ∀ i, algebra (R i) (A i)] :
  algebra (Π i, R i) (Π i, A i) :=
{ smul := λ r x i, (r i) • (x i),
  to_fun := λ r i, (hRA i).to_fun (r i),
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry,
  commutes' := sorry,
  smul_def' := sorry }


-/
