/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle, Kyle Miller
-/
import linear_algebra.finite_dimensional
import linear_algebra.projection
import linear_algebra.sesquilinear_form
import ring_theory.finiteness
import linear_algebra.free_module.finite.basic

/-!
# Dual vector spaces

The dual space of an $R$-module $M$ is the $R$-module of $R$-linear maps $M \to R$.

## Main definitions

* Duals and transposes:
  * `module.dual R M` defines the dual space of the `R`-module `M`, as `M →ₗ[R] R`.
  * `module.dual_pairing R M` is the canonical pairing between `dual R M` and `M`.
  * `module.dual.eval R M : M →ₗ[R] dual R (dual R)` is the canonical map to the double dual.
  * `module.dual.transpose` is the linear map from `M →ₗ[R] M'` to `dual R M' →ₗ[R] dual R M`.
  * `linear_map.dual_map` is `module.dual.transpose` of a given linear map, for dot notation.
  * `linear_equiv.dual_map` is for the dual of an equivalence.
* Bases:
  * `basis.to_dual` produces the map `M →ₗ[R] dual R M` associated to a basis for an `R`-module `M`.
  * `basis.to_dual_equiv` is the equivalence `M ≃ₗ[R] dual R M` associated to a finite basis.
  * `basis.dual_basis` is a basis for `dual R M` given a finite basis for `M`.
  * `module.dual_bases e ε` is the proposition that the families `e` of vectors and `ε` of dual
    vectors have the characteristic properties of a basis and a dual.
* Submodules:
  * `submodule.dual_restrict W` is the transpose `dual R M →ₗ[R] dual R W` of the inclusion map.
  * `submodule.dual_annihilator W` is the kernel of `W.dual_restrict`. That is, it is the submodule
    of `dual R M` whose elements all annihilate `W`.
  * `submodule.dual_restrict_comap W'` is the dual annihilator of `W' : submodule R (dual R M)`,
    pulled back along `module.dual.eval R M`.
  * `submodule.dual_copairing W` is the canonical pairing between `W.dual_annihilator` and `M ⧸ W`.
    It is nondegenerate for vector spaces (`subspace.dual_copairing_nondegenerate`).
  * `submodule.dual_pairing W` is the canonical pairing between `dual R M ⧸ W.dual_annihilator`
    and `W`. It is nondegenerate for vector spaces (`subspace.dual_pairing_nondegenerate`).
* Vector spaces:
  * `subspace.dual_lift W` is an arbitrary section (using choice) of `submodule.dual_restrict W`.

## Main results

* Bases:
  * `module.dual_basis.basis` and `module.dual_basis.coe_basis`: if `e` and `ε` form a dual pair,
    then `e` is a basis.
  * `module.dual_basis.coe_dual_basis`: if `e` and `ε` form a dual pair,
    then `ε` is a basis.
* Annihilators:
  * `module.dual_annihilator_gc R M` is the antitone Galois correspondence between
    `submodule.dual_annihilator` and `submodule.dual_coannihilator`.
  * `linear_map.ker_dual_map_eq_dual_annihilator_range` says that
    `f.dual_map.ker = f.range.dual_annihilator`
  * `linear_map.range_dual_map_eq_dual_annihilator_ker_of_subtype_range_surjective` says that
    `f.dual_map.range = f.ker.dual_annihilator`; this is specialized to vector spaces in
    `linear_map.range_dual_map_eq_dual_annihilator_ker`.
  * `submodule.dual_quot_equiv_dual_annihilator` is the equivalence
    `dual R (M ⧸ W) ≃ₗ[R] W.dual_annihilator`
* Vector spaces:
  * `subspace.dual_annihilator_dual_coannihilator_eq` says that the double dual annihilator,
    pulled back ground `module.dual.eval`, is the original submodule.
  * `subspace.dual_annihilator_gci` says that `module.dual_annihilator_gc R M` is an
    antitone Galois coinsertion.
  * `subspace.quot_annihilator_equiv` is the equivalence
    `dual K V ⧸ W.dual_annihilator ≃ₗ[K] dual K W`.
  * `linear_map.dual_pairing_nondegenerate` says that `module.dual_pairing` is nondegenerate.
  * `subspace.is_compl_dual_annihilator` says that the dual annihilator carries complementary
    subspaces to complementary subspaces.
* Finite-dimensional vector spaces:
  * `module.eval_equiv` is the equivalence `V ≃ₗ[K] dual K (dual K V)`
  * `module.map_eval_equiv` is the order isomorphism between subspaces of `V` and
    subspaces of `dual K (dual K V)`.
  * `subspace.quot_dual_equiv_annihilator W` is the equivalence
    `(dual K V ⧸ W.dual_lift.range) ≃ₗ[K] W.dual_annihilator`, where `W.dual_lift.range` is a copy
    of `dual K W` inside `dual K V`.
  * `subspace.quot_equiv_annihilator W` is the equivalence `(V ⧸ W) ≃ₗ[K] W.dual_annihilator`
  * `subspace.dual_quot_distrib W` is an equivalence
    `dual K (V₁ ⧸ W) ≃ₗ[K] dual K V₁ ⧸ W.dual_lift.range` from an arbitrary choice of
    splitting of `V₁`.

## TODO

Erdös-Kaplansky theorem about the dimension of a dual vector space in case of infinite dimension.
-/

noncomputable theory

namespace module

variables (R : Type*) (M : Type*)
variables [comm_semiring R] [add_comm_monoid M] [module R M]

/-- The dual space of an R-module M is the R-module of linear maps `M → R`. -/
@[derive [add_comm_monoid, module R]] def dual := M →ₗ[R] R

instance {S : Type*} [comm_ring S] {N : Type*} [add_comm_group N] [module S N] :
  add_comm_group (dual S N) := linear_map.add_comm_group

instance : linear_map_class (dual R M) R M R :=
linear_map.semilinear_map_class

/-- The canonical pairing of a vector space and its algebraic dual. -/
def dual_pairing (R M) [comm_semiring R] [add_comm_monoid M] [module R M] :
  module.dual R M →ₗ[R] M →ₗ[R] R := linear_map.id

@[simp] lemma dual_pairing_apply (v x) : dual_pairing R M v x = v x := rfl

namespace dual

instance : inhabited (dual R M) := linear_map.inhabited

instance : has_coe_to_fun (dual R M) (λ _, M → R) := ⟨linear_map.to_fun⟩

/-- Maps a module M to the dual of the dual of M. See `module.erange_coe` and
`module.eval_equiv`. -/
def eval : M →ₗ[R] (dual R (dual R M)) := linear_map.flip linear_map.id

@[simp] lemma eval_apply (v : M) (a : dual R M) : eval R M v a = a v := rfl

variables {R M} {M' : Type*} [add_comm_monoid M'] [module R M']

/-- The transposition of linear maps, as a linear map from `M →ₗ[R] M'` to
`dual R M' →ₗ[R] dual R M`. -/
def transpose : (M →ₗ[R] M') →ₗ[R] (dual R M' →ₗ[R] dual R M) :=
(linear_map.llcomp R M M' R).flip

lemma transpose_apply (u : M →ₗ[R] M') (l : dual R M') : transpose u l = l.comp u := rfl

variables {M'' : Type*} [add_comm_monoid M''] [module R M'']

lemma transpose_comp (u : M' →ₗ[R] M'') (v : M →ₗ[R] M') :
  transpose (u.comp v) = (transpose v).comp (transpose u) := rfl

end dual

section prod
variables (M' : Type*) [add_comm_monoid M'] [module R M']

/-- Taking duals distributes over products. -/
@[simps] def dual_prod_dual_equiv_dual :
  (module.dual R M × module.dual R M') ≃ₗ[R] module.dual R (M × M') :=
linear_map.coprod_equiv R

@[simp] lemma dual_prod_dual_equiv_dual_apply (φ : module.dual R M) (ψ : module.dual R M') :
  dual_prod_dual_equiv_dual R M M' (φ, ψ) = φ.coprod ψ := rfl

end prod

end module

section dual_map
open module

variables {R : Type*} [comm_semiring R] {M₁ : Type*} {M₂ : Type*}
variables [add_comm_monoid M₁] [module R M₁] [add_comm_monoid M₂] [module R M₂]

/-- Given a linear map `f : M₁ →ₗ[R] M₂`, `f.dual_map` is the linear map between the dual of
`M₂` and `M₁` such that it maps the functional `φ` to `φ ∘ f`. -/
def linear_map.dual_map (f : M₁ →ₗ[R] M₂) : dual R M₂ →ₗ[R] dual R M₁ :=
module.dual.transpose f

lemma linear_map.dual_map_def (f : M₁ →ₗ[R] M₂) : f.dual_map = module.dual.transpose f := rfl

lemma linear_map.dual_map_apply' (f : M₁ →ₗ[R] M₂) (g : dual R M₂) :
  f.dual_map g = g.comp f := rfl

@[simp] lemma linear_map.dual_map_apply (f : M₁ →ₗ[R] M₂) (g : dual R M₂) (x : M₁) :
  f.dual_map g x = g (f x) := rfl

@[simp] lemma linear_map.dual_map_id :
  (linear_map.id : M₁ →ₗ[R] M₁).dual_map = linear_map.id :=
by { ext, refl }

lemma linear_map.dual_map_comp_dual_map {M₃ : Type*} [add_comm_group M₃] [module R M₃]
  (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
  f.dual_map.comp g.dual_map = (g.comp f).dual_map :=
rfl

/-- If a linear map is surjective, then its dual is injective. -/
lemma linear_map.dual_map_injective_of_surjective {f : M₁ →ₗ[R] M₂} (hf : function.surjective f) :
  function.injective f.dual_map :=
begin
  intros φ ψ h,
  ext x,
  obtain ⟨y, rfl⟩ := hf x,
  exact congr_arg (λ (g : module.dual R M₁), g y) h,
end

/-- The `linear_equiv` version of `linear_map.dual_map`. -/
def linear_equiv.dual_map (f : M₁ ≃ₗ[R] M₂) : dual R M₂ ≃ₗ[R] dual R M₁ :=
{ inv_fun := f.symm.to_linear_map.dual_map,
  left_inv :=
    begin
      intro φ, ext x,
      simp only [linear_map.dual_map_apply, linear_equiv.coe_to_linear_map,
                 linear_map.to_fun_eq_coe, linear_equiv.apply_symm_apply]
    end,
  right_inv :=
    begin
      intro φ, ext x,
      simp only [linear_map.dual_map_apply, linear_equiv.coe_to_linear_map,
                 linear_map.to_fun_eq_coe, linear_equiv.symm_apply_apply]
    end,
  .. f.to_linear_map.dual_map }

@[simp] lemma linear_equiv.dual_map_apply (f : M₁ ≃ₗ[R] M₂) (g : dual R M₂) (x : M₁) :
  f.dual_map g x = g (f x) := rfl

@[simp] lemma linear_equiv.dual_map_refl :
  (linear_equiv.refl R M₁).dual_map = linear_equiv.refl R (dual R M₁) :=
by { ext, refl }

@[simp] lemma linear_equiv.dual_map_symm {f : M₁ ≃ₗ[R] M₂} :
  (linear_equiv.dual_map f).symm = linear_equiv.dual_map f.symm := rfl

lemma linear_equiv.dual_map_trans {M₃ : Type*} [add_comm_group M₃] [module R M₃]
  (f : M₁ ≃ₗ[R] M₂) (g : M₂ ≃ₗ[R] M₃) :
  g.dual_map.trans f.dual_map = (f.trans g).dual_map :=
rfl

end dual_map

namespace basis

universes u v w

open module module.dual submodule linear_map cardinal function
open_locale big_operators

variables {R M K V ι : Type*}

section comm_semiring

variables [comm_semiring R] [add_comm_monoid M] [module R M] [decidable_eq ι]
variables (b : basis ι R M)

/-- The linear map from a vector space equipped with basis to its dual vector space,
taking basis elements to corresponding dual basis elements. -/
def to_dual : M →ₗ[R] module.dual R M :=
b.constr ℕ $ λ v, b.constr ℕ $ λ w, if w = v then (1 : R) else 0

lemma to_dual_apply (i j : ι) :
  b.to_dual (b i) (b j) = if i = j then 1 else 0 :=
by { erw [constr_basis b, constr_basis b], ac_refl }

@[simp] lemma to_dual_total_left (f : ι →₀ R) (i : ι) :
  b.to_dual (finsupp.total ι M R b f) (b i) = f i :=
begin
  rw [finsupp.total_apply, finsupp.sum, linear_map.map_sum, linear_map.sum_apply],
  simp_rw [linear_map.map_smul, linear_map.smul_apply, to_dual_apply, smul_eq_mul,
           mul_boole, finset.sum_ite_eq'],
  split_ifs with h,
  { refl },
  { rw finsupp.not_mem_support_iff.mp h }
end

@[simp] lemma to_dual_total_right (f : ι →₀ R) (i : ι) :
  b.to_dual (b i) (finsupp.total ι M R b f) = f i :=
begin
  rw [finsupp.total_apply, finsupp.sum, linear_map.map_sum],
  simp_rw [linear_map.map_smul, to_dual_apply, smul_eq_mul, mul_boole, finset.sum_ite_eq],
  split_ifs with h,
  { refl },
  { rw finsupp.not_mem_support_iff.mp h }
end

lemma to_dual_apply_left (m : M) (i : ι) : b.to_dual m (b i) = b.repr m i :=
by rw [← b.to_dual_total_left, b.total_repr]

lemma to_dual_apply_right (i : ι) (m : M) : b.to_dual (b i) m = b.repr m i :=
by rw [← b.to_dual_total_right, b.total_repr]

lemma coe_to_dual_self (i : ι) : b.to_dual (b i) = b.coord i :=
by { ext, apply to_dual_apply_right }

/-- `h.to_dual_flip v` is the linear map sending `w` to `h.to_dual w v`. -/
def to_dual_flip (m : M) : (M →ₗ[R] R) := b.to_dual.flip m

lemma to_dual_flip_apply (m₁ m₂ : M) : b.to_dual_flip m₁ m₂ = b.to_dual m₂ m₁ := rfl

lemma to_dual_eq_repr (m : M) (i : ι) : b.to_dual m (b i) = b.repr m i :=
b.to_dual_apply_left m i

lemma to_dual_eq_equiv_fun [fintype ι] (m : M) (i : ι) : b.to_dual m (b i) = b.equiv_fun m i :=
by rw [b.equiv_fun_apply, to_dual_eq_repr]

lemma to_dual_inj (m : M) (a : b.to_dual m = 0) : m = 0 :=
begin
  rw [← mem_bot R, ← b.repr.ker, mem_ker, linear_equiv.coe_coe],
  apply finsupp.ext,
  intro b,
  rw [← to_dual_eq_repr, a],
  refl
end

theorem to_dual_ker : b.to_dual.ker = ⊥ :=
ker_eq_bot'.mpr b.to_dual_inj

theorem to_dual_range [_root_.finite ι] : b.to_dual.range = ⊤ :=
begin
  casesI nonempty_fintype ι,
  refine eq_top_iff'.2 (λ f, _),
  rw linear_map.mem_range,
  let lin_comb : ι →₀ R := finsupp.equiv_fun_on_finite.symm (λ i, f.to_fun (b i)),
  refine ⟨finsupp.total ι M R b lin_comb, b.ext $ λ i, _⟩,
  rw [b.to_dual_eq_repr _ i, repr_total b],
  refl,
end

end comm_semiring

section

variables [comm_semiring R] [add_comm_monoid M] [module R M] [fintype ι]
variables (b : basis ι R M)

@[simp] lemma sum_dual_apply_smul_coord (f : module.dual R M) : ∑ x, f (b x) • b.coord x = f :=
begin
  ext m,
  simp_rw [linear_map.sum_apply, linear_map.smul_apply, smul_eq_mul, mul_comm (f _), ←smul_eq_mul,
    ←f.map_smul, ←f.map_sum, basis.coord_apply, basis.sum_repr],
end

end

section comm_ring

variables [comm_ring R] [add_comm_group M] [module R M] [decidable_eq ι]
variables (b : basis ι R M)

section finite
variables [_root_.finite ι]

/-- A vector space is linearly equivalent to its dual space. -/
@[simps]
def to_dual_equiv : M ≃ₗ[R] dual R M :=
linear_equiv.of_bijective b.to_dual
  ⟨ker_eq_bot.mp b.to_dual_ker, range_eq_top.mp b.to_dual_range⟩

/-- Maps a basis for `V` to a basis for the dual space. -/
def dual_basis : basis ι R (dual R M) := b.map b.to_dual_equiv

-- We use `j = i` to match `basis.repr_self`
lemma dual_basis_apply_self (i j : ι) : b.dual_basis i (b j) = if j = i then 1 else 0 :=
by { convert b.to_dual_apply i j using 2, rw @eq_comm _ j i }

lemma total_dual_basis (f : ι →₀ R) (i : ι) :
  finsupp.total ι (dual R M) R b.dual_basis f (b i) = f i :=
begin
  casesI nonempty_fintype ι,
  rw [finsupp.total_apply, finsupp.sum_fintype, linear_map.sum_apply],
  { simp_rw [linear_map.smul_apply, smul_eq_mul, dual_basis_apply_self, mul_boole,
      finset.sum_ite_eq, if_pos (finset.mem_univ i)] },
  { intro, rw zero_smul },
end

lemma dual_basis_repr (l : dual R M) (i : ι) : b.dual_basis.repr l i = l (b i) :=
by rw [← total_dual_basis b, basis.total_repr b.dual_basis l]

lemma dual_basis_apply (i : ι) (m : M) : b.dual_basis i m = b.repr m i := b.to_dual_apply_right i m

@[simp] lemma coe_dual_basis : ⇑b.dual_basis = b.coord := by { ext i x, apply dual_basis_apply }

@[simp] lemma to_dual_to_dual : b.dual_basis.to_dual.comp b.to_dual = dual.eval R M :=
begin
  refine b.ext (λ i, b.dual_basis.ext (λ j, _)),
  rw [linear_map.comp_apply, to_dual_apply_left, coe_to_dual_self, ← coe_dual_basis,
      dual.eval_apply, basis.repr_self, finsupp.single_apply, dual_basis_apply_self]
end

end finite

lemma dual_basis_equiv_fun [fintype ι] (l : dual R M) (i : ι) :
  b.dual_basis.equiv_fun l i = l (b i) :=
by rw [basis.equiv_fun_apply, dual_basis_repr]

theorem eval_ker {ι : Type*} (b : basis ι R M) :
  (dual.eval R M).ker = ⊥ :=
begin
  rw ker_eq_bot',
  intros m hm,
  simp_rw [linear_map.ext_iff, dual.eval_apply, zero_apply] at hm,
  exact (basis.forall_coord_eq_zero_iff _).mp (λ i, hm (b.coord i))
end

lemma eval_range {ι : Type*} [_root_.finite ι] (b : basis ι R M) : (eval R M).range = ⊤ :=
begin
  classical,
  casesI nonempty_fintype ι,
  rw [← b.to_dual_to_dual, range_comp, b.to_dual_range, submodule.map_top, to_dual_range _],
  apply_instance
end

/-- A module with a basis is linearly equivalent to the dual of its dual space. -/
def eval_equiv  {ι : Type*} [_root_.finite ι] (b : basis ι R M) : M ≃ₗ[R] dual R (dual R M) :=
linear_equiv.of_bijective (eval R M)
  ⟨ker_eq_bot.mp b.eval_ker, range_eq_top.mp b.eval_range⟩

@[simp] lemma eval_equiv_to_linear_map {ι : Type*} [_root_.finite ι] (b : basis ι R M) :
  (b.eval_equiv).to_linear_map = dual.eval R M := rfl

section

open_locale classical

variables [finite R M] [free R M] [nontrivial R]

instance dual_free : free R (dual R M) := free.of_basis (free.choose_basis R M).dual_basis

instance dual_finite : finite R (dual R M) := finite.of_basis (free.choose_basis R M).dual_basis

end

end comm_ring

/-- `simp` normal form version of `total_dual_basis` -/
@[simp] lemma total_coord [comm_ring R] [add_comm_group M] [module R M] [_root_.finite ι]
  (b : basis ι R M) (f : ι →₀ R) (i : ι) :
  finsupp.total ι (dual R M) R b.coord f (b i) = f i :=
by { haveI := classical.dec_eq ι, rw [← coe_dual_basis, total_dual_basis] }

lemma dual_dim_eq [comm_ring K] [add_comm_group V] [module K V] [_root_.finite ι]
  (b : basis ι K V) :
  cardinal.lift (module.rank K V) = module.rank K (dual K V) :=
begin
  classical,
  casesI nonempty_fintype ι,
  have := linear_equiv.lift_dim_eq b.to_dual_equiv,
  simp only [cardinal.lift_umax] at this,
  rw [this, ← cardinal.lift_umax],
  apply cardinal.lift_id,
end

end basis

namespace module

variables {K V : Type*}
variables [field K] [add_comm_group V] [module K V]
open module module.dual submodule linear_map cardinal basis finite_dimensional

section
variables (K) (V)

theorem eval_ker : (eval K V).ker = ⊥ :=
by { classical, exact (basis.of_vector_space K V).eval_ker }

theorem map_eval_injective : (submodule.map (eval K V)).injective :=
begin
  apply submodule.map_injective_of_injective,
  rw ← linear_map.ker_eq_bot,
  apply eval_ker K V, -- elaborates faster than `exact`
end

theorem comap_eval_surjective : (submodule.comap (eval K V)).surjective :=
begin
  apply submodule.comap_surjective_of_injective,
  rw ← linear_map.ker_eq_bot,
  apply eval_ker K V, -- elaborates faster than `exact`
end

end

section
variable (K)

theorem eval_apply_eq_zero_iff (v : V) : (eval K V) v = 0 ↔ v = 0 :=
by simpa only using set_like.ext_iff.mp (eval_ker K V) v

theorem eval_apply_injective : function.injective (eval K V) :=
(injective_iff_map_eq_zero' (eval K V)).mpr (eval_apply_eq_zero_iff K)

theorem forall_dual_apply_eq_zero_iff (v : V) : (∀ (φ : module.dual K V), φ v = 0) ↔ v = 0 :=
by { rw [← eval_apply_eq_zero_iff K v, linear_map.ext_iff], refl }

end

-- TODO(jmc): generalize to rings, once `module.rank` is generalized
theorem dual_dim_eq [finite_dimensional K V] :
  cardinal.lift (module.rank K V) = module.rank K (dual K V) :=
(basis.of_vector_space K V).dual_dim_eq

lemma erange_coe [finite_dimensional K V] : (eval K V).range = ⊤ :=
begin
  letI : is_noetherian K V := is_noetherian.iff_fg.2 infer_instance,
  exact (basis.of_vector_space K V).eval_range
end

variables (K V)

/-- A vector space is linearly equivalent to the dual of its dual space. -/
def eval_equiv [finite_dimensional K V] : V ≃ₗ[K] dual K (dual K V) :=
linear_equiv.of_bijective (eval K V)
  -- 60x faster elaboration than using `ker_eq_bot.mp eval_ker` directly:
  ⟨by { rw ← ker_eq_bot, apply eval_ker K V }, range_eq_top.mp erange_coe⟩

/-- The isomorphism `module.eval_equiv` induces an order isomorphism on subspaces. -/
def map_eval_equiv [finite_dimensional K V] : subspace K V ≃o subspace K (dual K (dual K V)) :=
submodule.order_iso_map_comap (eval_equiv K V)

variables {K V}

@[simp] lemma eval_equiv_to_linear_map [finite_dimensional K V] :
  (eval_equiv K V).to_linear_map = dual.eval K V := rfl

@[simp] lemma map_eval_equiv_apply [finite_dimensional K V] (W : subspace K V) :
  map_eval_equiv K V W = W.map (eval K V) := rfl

@[simp] lemma map_eval_equiv_symm_apply [finite_dimensional K V]
  (W'' : subspace K (dual K (dual K V))) :
  (map_eval_equiv K V).symm W'' = W''.comap (eval K V) := rfl

end module

section dual_bases

open module

variables {R M ι : Type*}
variables [comm_semiring R] [add_comm_monoid M] [module R M] [decidable_eq ι]

/-- Try using `set.to_finite` to dispatch a `set.finite` goal. -/
-- TODO: In Lean 4 we can remove this and use `by { intros; exact Set.toFinite _ }` as a default
-- argument.
meta def use_finite_instance : tactic unit := `[intros, exact set.to_finite _]

/-- `e` and `ε` have characteristic properties of a basis and its dual -/
@[nolint has_nonempty_instance]
structure module.dual_bases (e : ι → M) (ε : ι → (dual R M)) : Prop :=
(eval : ∀ i j : ι, ε i (e j) = if i = j then 1 else 0)
(total : ∀ {m : M}, (∀ i, ε i m = 0) → m = 0)
(finite : ∀ m : M, {i | ε i m ≠ 0}.finite . use_finite_instance)

end dual_bases

namespace module.dual_bases

open module module.dual linear_map function

variables {R M ι : Type*}
variables [comm_ring R] [add_comm_group M] [module R M]
variables {e : ι → M} {ε : ι → dual R M}

/-- The coefficients of `v` on the basis `e` -/
def coeffs [decidable_eq ι] (h : dual_bases e ε) (m : M) : ι →₀ R :=
{ to_fun := λ i, ε i m,
  support := (h.finite m).to_finset,
  mem_support_to_fun := by { intro i, rw [set.finite.mem_to_finset, set.mem_set_of_eq] } }

@[simp] lemma coeffs_apply [decidable_eq ι] (h : dual_bases e ε) (m : M) (i : ι) :
  h.coeffs m i = ε i m := rfl

/-- linear combinations of elements of `e`.
This is a convenient abbreviation for `finsupp.total _ M R e l` -/
def lc {ι} (e : ι → M) (l : ι →₀ R) : M := l.sum (λ (i : ι) (a : R), a • (e i))

lemma lc_def (e : ι → M) (l : ι →₀ R) : lc e l = finsupp.total _ _ _ e l := rfl

open module

variables [decidable_eq ι] (h : dual_bases e ε)
include h

lemma dual_lc (l : ι →₀ R) (i : ι) : ε i (dual_bases.lc e l) = l i :=
begin
  erw linear_map.map_sum,
  simp only [h.eval, map_smul, smul_eq_mul],
  rw finset.sum_eq_single i,
  { simp },
  { intros q q_in q_ne,
    simp [q_ne.symm] },
  { intro p_not_in,
    simp [finsupp.not_mem_support_iff.1 p_not_in] },
end

@[simp]
lemma coeffs_lc (l : ι →₀ R) : h.coeffs (dual_bases.lc e l) = l :=
by { ext i, rw [h.coeffs_apply, h.dual_lc] }

/-- For any m : M n, \sum_{p ∈ Q n} (ε p m) • e p = m -/
@[simp]
lemma lc_coeffs (m : M) : dual_bases.lc e (h.coeffs m) = m :=
begin
  refine eq_of_sub_eq_zero (h.total _),
  intros i,
  simp [-sub_eq_add_neg, linear_map.map_sub, h.dual_lc, sub_eq_zero]
end

/-- `(h : dual_bases e ε).basis` shows the family of vectors `e` forms a basis. -/
@[simps]
def basis : basis ι R M :=
basis.of_repr
{ to_fun := coeffs h,
  inv_fun := lc e,
  left_inv := lc_coeffs h,
  right_inv := coeffs_lc h,
  map_add' := λ v w, by { ext i, exact (ε i).map_add v w },
  map_smul' := λ c v, by { ext i, exact (ε i).map_smul c v } }

@[simp] lemma coe_basis : ⇑h.basis = e :=
by { ext i, rw basis.apply_eq_iff, ext j,
     rw [h.basis_repr_apply, coeffs_apply, h.eval, finsupp.single_apply],
     convert if_congr eq_comm rfl rfl } -- `convert` to get rid of a `decidable_eq` mismatch

lemma mem_of_mem_span {H : set ι} {x : M} (hmem : x ∈ submodule.span R (e '' H)) :
  ∀ i : ι, ε i x ≠ 0 → i ∈ H :=
begin
  intros i hi,
  rcases (finsupp.mem_span_image_iff_total _).mp hmem with ⟨l, supp_l, rfl⟩,
  apply not_imp_comm.mp ((finsupp.mem_supported' _ _).mp supp_l i),
  rwa [← lc_def, h.dual_lc] at hi
end

lemma coe_dual_basis [fintype ι] : ⇑h.basis.dual_basis = ε :=
funext (λ i, h.basis.ext (λ j, by rw [h.basis.dual_basis_apply_self, h.coe_basis, h.eval,
                                      if_congr eq_comm rfl rfl]))

end module.dual_bases

namespace submodule

universes u v w

variables {R : Type u} {M : Type v} [comm_semiring R] [add_comm_monoid M] [module R M]
variable {W : submodule R M}

/-- The `dual_restrict` of a submodule `W` of `M` is the linear map from the
  dual of `M` to the dual of `W` such that the domain of each linear map is
  restricted to `W`. -/
def dual_restrict (W : submodule R M) :
  module.dual R M →ₗ[R] module.dual R W :=
linear_map.dom_restrict' W

lemma dual_restrict_def (W : submodule R M) : W.dual_restrict = W.subtype.dual_map := rfl

@[simp] lemma dual_restrict_apply
  (W : submodule R M) (φ : module.dual R M) (x : W) :
  W.dual_restrict φ x = φ (x : M) := rfl

/-- The `dual_annihilator` of a submodule `W` is the set of linear maps `φ` such
  that `φ w = 0` for all `w ∈ W`. -/
def dual_annihilator {R : Type u} {M : Type v} [comm_semiring R] [add_comm_monoid M]
  [module R M] (W : submodule R M) : submodule R $ module.dual R M :=
W.dual_restrict.ker

@[simp] lemma mem_dual_annihilator (φ : module.dual R M) :
  φ ∈ W.dual_annihilator ↔ ∀ w ∈ W, φ w = 0 :=
begin
  refine linear_map.mem_ker.trans _,
  simp_rw [linear_map.ext_iff, dual_restrict_apply],
  exact ⟨λ h w hw, h ⟨w, hw⟩, λ h w, h w.1 w.2⟩
end

/-- That $\operatorname{ker}(\iota^* : V^* \to W^*) = \operatorname{ann}(W)$.
This is the definition of the dual annihilator of the submodule $W$. -/
lemma dual_restrict_ker_eq_dual_annihilator (W : submodule R M) :
  W.dual_restrict.ker = W.dual_annihilator :=
rfl

/-- The `dual_annihilator` of a submodule of the dual space pulled back along the evaluation map
`module.dual.eval`. -/
def dual_coannihilator (Φ : submodule R (module.dual R M)) : submodule R M :=
Φ.dual_annihilator.comap (module.dual.eval R M)

lemma mem_dual_coannihilator {Φ : submodule R (module.dual R M)} (x : M) :
  x ∈ Φ.dual_coannihilator ↔ ∀ φ ∈ Φ, (φ x : R) = 0 :=
by simp_rw [dual_coannihilator, mem_comap, mem_dual_annihilator, module.dual.eval_apply]

lemma dual_annihilator_gc (R M : Type*) [comm_semiring R] [add_comm_monoid M] [module R M] :
  galois_connection
    (order_dual.to_dual ∘ (dual_annihilator : submodule R M → submodule R (module.dual R M)))
    (dual_coannihilator ∘ order_dual.of_dual) :=
begin
  intros a b,
  induction b using order_dual.rec,
  simp only [function.comp_app, order_dual.to_dual_le_to_dual, order_dual.of_dual_to_dual],
  split;
  { intros h x hx,
    simp only [mem_dual_annihilator, mem_dual_coannihilator],
    intros y hy,
    have := h hy,
    simp only [mem_dual_annihilator, mem_dual_coannihilator] at this,
    exact this x hx },
end

lemma le_dual_annihilator_iff_le_dual_coannihilator
  {U : submodule R (module.dual R M)} {V : submodule R M} :
  U ≤ V.dual_annihilator ↔ V ≤ U.dual_coannihilator :=
(dual_annihilator_gc R M).le_iff_le

@[simp] lemma dual_annihilator_bot : (⊥ : submodule R M).dual_annihilator = ⊤ :=
(dual_annihilator_gc R M).l_bot

@[simp] lemma dual_annihilator_top : (⊤ : submodule R M).dual_annihilator = ⊥ :=
begin
  rw eq_bot_iff,
  intro v,
  simp_rw [mem_dual_annihilator, mem_bot, mem_top, forall_true_left],
  exact λ h, linear_map.ext h,
end

@[simp] lemma dual_coannihilator_bot :
  (⊥ : submodule R (module.dual R M)).dual_coannihilator = ⊤ :=
(dual_annihilator_gc R M).u_top

@[mono] lemma dual_annihilator_anti {U V : submodule R M} (hUV : U ≤ V) :
  V.dual_annihilator ≤ U.dual_annihilator :=
(dual_annihilator_gc R M).monotone_l hUV

@[mono] lemma dual_coannihilator_anti {U V : submodule R (module.dual R M)} (hUV : U ≤ V) :
  V.dual_coannihilator ≤ U.dual_coannihilator :=
(dual_annihilator_gc R M).monotone_u hUV

lemma le_dual_annihilator_dual_coannihilator (U : submodule R M) :
  U ≤ U.dual_annihilator.dual_coannihilator :=
(dual_annihilator_gc R M).le_u_l U

lemma le_dual_coannihilator_dual_annihilator (U : submodule R (module.dual R M)) :
  U ≤ U.dual_coannihilator.dual_annihilator :=
(dual_annihilator_gc R M).l_u_le U

lemma dual_annihilator_dual_coannihilator_dual_annihilator
  (U : submodule R M) :
  U.dual_annihilator.dual_coannihilator.dual_annihilator = U.dual_annihilator :=
(dual_annihilator_gc R M).l_u_l_eq_l U

lemma dual_coannihilator_dual_annihilator_dual_coannihilator
  (U : submodule R (module.dual R M)) :
  U.dual_coannihilator.dual_annihilator.dual_coannihilator = U.dual_coannihilator :=
(dual_annihilator_gc R M).u_l_u_eq_u U

lemma dual_annihilator_sup_eq (U V : submodule R M) :
  (U ⊔ V).dual_annihilator = U.dual_annihilator ⊓ V.dual_annihilator :=
(dual_annihilator_gc R M).l_sup

lemma dual_coannihilator_sup_eq (U V : submodule R (module.dual R M)) :
  (U ⊔ V).dual_coannihilator = U.dual_coannihilator ⊓ V.dual_coannihilator :=
(dual_annihilator_gc R M).u_inf

lemma dual_annihilator_supr_eq {ι : Type*} (U : ι → submodule R M) :
  (⨆ (i : ι), U i).dual_annihilator = ⨅ (i : ι), (U i).dual_annihilator :=
(dual_annihilator_gc R M).l_supr

lemma dual_coannihilator_supr_eq {ι : Type*} (U : ι → submodule R (module.dual R M)) :
  (⨆ (i : ι), U i).dual_coannihilator = ⨅ (i : ι), (U i).dual_coannihilator :=
(dual_annihilator_gc R M).u_infi

/-- See also `subspace.dual_annihilator_inf_eq` for vector subspaces. -/
lemma sup_dual_annihilator_le_inf (U V : submodule R M) :
  U.dual_annihilator ⊔ V.dual_annihilator ≤ (U ⊓ V).dual_annihilator :=
begin
  rw [le_dual_annihilator_iff_le_dual_coannihilator, dual_coannihilator_sup_eq],
  apply' inf_le_inf; exact le_dual_annihilator_dual_coannihilator _,
end

/-- See also `subspace.dual_annihilator_infi_eq` for vector subspaces when `ι` is finite. -/
lemma supr_dual_annihilator_le_infi {ι : Type*} (U : ι → submodule R M) :
  (⨆ (i : ι), (U i).dual_annihilator) ≤ (⨅ (i : ι), U i).dual_annihilator :=
begin
  rw [le_dual_annihilator_iff_le_dual_coannihilator, dual_coannihilator_supr_eq],
  apply' infi_mono,
  exact λ (i : ι), le_dual_annihilator_dual_coannihilator (U i),
end

end submodule

namespace subspace

open submodule linear_map

universes u v w

-- We work in vector spaces because `exists_is_compl` only hold for vector spaces
variables {K : Type u} {V : Type v} [field K] [add_comm_group V] [module K V]

@[simp] lemma dual_coannihilator_top (W : subspace K V) :
  (⊤ : subspace K (module.dual K W)).dual_coannihilator = ⊥ :=
by rw [dual_coannihilator, dual_annihilator_top, comap_bot, module.eval_ker]

lemma dual_annihilator_dual_coannihilator_eq {W : subspace K V} :
  W.dual_annihilator.dual_coannihilator = W :=
begin
  refine le_antisymm _ (le_dual_annihilator_dual_coannihilator _),
  intro v,
  simp only [mem_dual_annihilator, mem_dual_coannihilator],
  contrapose!,
  intro hv,
  obtain ⟨W', hW⟩ := submodule.exists_is_compl W,
  obtain ⟨⟨w, w'⟩, rfl, -⟩ := exists_unique_add_of_is_compl_prod hW v,
  have hw'n : (w' : V) ∉ W := by { contrapose! hv, exact submodule.add_mem W w.2 hv },
  have hw'nz : w' ≠ 0 := by { rintro rfl, exact hw'n (submodule.zero_mem W) },
  rw [ne.def, ← module.forall_dual_apply_eq_zero_iff K w'] at hw'nz,
  push_neg at hw'nz,
  obtain ⟨φ, hφ⟩ := hw'nz,
  existsi ((linear_map.of_is_compl_prod hW).comp (linear_map.inr _ _ _)) φ,
  simp only [coe_comp, coe_inr, function.comp_app, of_is_compl_prod_apply, map_add,
    of_is_compl_left_apply, zero_apply, of_is_compl_right_apply, zero_add, ne.def],
  refine ⟨_, hφ⟩,
  intros v hv,
  apply linear_map.of_is_compl_left_apply hW ⟨v, hv⟩, -- exact elaborates slowly
end

theorem forall_mem_dual_annihilator_apply_eq_zero_iff (W : subspace K V) (v : V) :
  (∀ (φ : module.dual K V), φ ∈ W.dual_annihilator → φ v = 0) ↔ v ∈ W :=
by rw [← set_like.ext_iff.mp dual_annihilator_dual_coannihilator_eq v,
       mem_dual_coannihilator]

/-- `submodule.dual_annihilator` and `submodule.dual_coannihilator` form a Galois coinsertion. -/
def dual_annihilator_gci (K V : Type*) [field K] [add_comm_group V] [module K V] :
  galois_coinsertion
    (order_dual.to_dual ∘ (dual_annihilator : subspace K V → subspace K (module.dual K V)))
    (dual_coannihilator ∘ order_dual.of_dual) :=
{ choice := λ W h, dual_coannihilator W,
  gc := dual_annihilator_gc K V,
  u_l_le := λ W, dual_annihilator_dual_coannihilator_eq.le,
  choice_eq := λ W h, rfl }

lemma dual_annihilator_le_dual_annihilator_iff {W W' : subspace K V} :
  W.dual_annihilator ≤ W'.dual_annihilator ↔ W' ≤ W :=
(dual_annihilator_gci K V).l_le_l_iff

lemma dual_annihilator_inj {W W' : subspace K V} :
  W.dual_annihilator = W'.dual_annihilator ↔ W = W' :=
begin
  split,
  { apply (dual_annihilator_gci K V).l_injective },
  { rintro rfl, refl },
end

/-- Given a subspace `W` of `V` and an element of its dual `φ`, `dual_lift W φ` is
an arbitrary extension of `φ` to an element of the dual of `V`.
That is, `dual_lift W φ` sends `w ∈ W` to `φ x` and `x` in a chosen complement of `W` to `0`. -/
noncomputable def dual_lift (W : subspace K V) :
  module.dual K W →ₗ[K] module.dual K V :=
let h := classical.indefinite_description _ W.exists_is_compl in
  (linear_map.of_is_compl_prod h.2).comp (linear_map.inl _ _ _)

variable {W : subspace K V}

@[simp] lemma dual_lift_of_subtype {φ : module.dual K W} (w : W) :
  W.dual_lift φ (w : V) = φ w :=
by { erw of_is_compl_left_apply _ w, refl }

lemma dual_lift_of_mem {φ : module.dual K W} {w : V} (hw : w ∈ W) :
  W.dual_lift φ w = φ ⟨w, hw⟩ :=
by convert dual_lift_of_subtype ⟨w, hw⟩

@[simp] lemma dual_restrict_comp_dual_lift (W : subspace K V) :
  W.dual_restrict.comp W.dual_lift = 1 :=
by { ext φ x, simp }

lemma dual_restrict_left_inverse (W : subspace K V) :
  function.left_inverse W.dual_restrict W.dual_lift :=
λ x, show W.dual_restrict.comp W.dual_lift x = x,
  by { rw [dual_restrict_comp_dual_lift], refl }

lemma dual_lift_right_inverse (W : subspace K V) :
  function.right_inverse W.dual_lift W.dual_restrict :=
W.dual_restrict_left_inverse

lemma dual_restrict_surjective :
  function.surjective W.dual_restrict :=
W.dual_lift_right_inverse.surjective

lemma dual_lift_injective : function.injective W.dual_lift :=
W.dual_restrict_left_inverse.injective

/-- The quotient by the `dual_annihilator` of a subspace is isomorphic to the
  dual of that subspace. -/
noncomputable def quot_annihilator_equiv (W : subspace K V) :
  (module.dual K V ⧸ W.dual_annihilator) ≃ₗ[K] module.dual K W :=
(quot_equiv_of_eq _ _ W.dual_restrict_ker_eq_dual_annihilator).symm.trans $
  W.dual_restrict.quot_ker_equiv_of_surjective dual_restrict_surjective

@[simp] lemma quot_annihilator_equiv_apply (W : subspace K V) (φ : module.dual K V) :
  W.quot_annihilator_equiv (submodule.quotient.mk φ) = W.dual_restrict φ :=
by { ext, refl }

/-- The natural isomorphism from the dual of a subspace `W` to `W.dual_lift.range`. -/
noncomputable def dual_equiv_dual (W : subspace K V) :
  module.dual K W ≃ₗ[K] W.dual_lift.range :=
linear_equiv.of_injective _ dual_lift_injective

lemma dual_equiv_dual_def (W : subspace K V) :
  W.dual_equiv_dual.to_linear_map = W.dual_lift.range_restrict := rfl

@[simp] lemma dual_equiv_dual_apply (φ : module.dual K W) :
  W.dual_equiv_dual φ = ⟨W.dual_lift φ, mem_range.2 ⟨φ, rfl⟩⟩ := rfl

section

open_locale classical

open finite_dimensional

variables {V₁ : Type*} [add_comm_group V₁] [module K V₁]

instance [H : finite_dimensional K V] : finite_dimensional K (module.dual K V) :=
by apply_instance

variables [finite_dimensional K V] [finite_dimensional K V₁]

lemma dual_annihilator_dual_annihilator_eq (W : subspace K V) :
  W.dual_annihilator.dual_annihilator = module.map_eval_equiv K V W :=
begin
  have : _ = W := subspace.dual_annihilator_dual_coannihilator_eq,
  rw [dual_coannihilator, ← module.map_eval_equiv_symm_apply] at this,
  rwa ← order_iso.symm_apply_eq,
end

-- TODO(kmill): https://github.com/leanprover-community/mathlib/pull/17521#discussion_r1083241963
@[simp] lemma dual_finrank_eq :
  finrank K (module.dual K V) = finrank K V :=
linear_equiv.finrank_eq (basis.of_vector_space K V).to_dual_equiv.symm

/-- The quotient by the dual is isomorphic to its dual annihilator.  -/
noncomputable def quot_dual_equiv_annihilator (W : subspace K V) :
  (module.dual K V ⧸ W.dual_lift.range) ≃ₗ[K] W.dual_annihilator :=
linear_equiv.quot_equiv_of_quot_equiv $
  linear_equiv.trans W.quot_annihilator_equiv W.dual_equiv_dual

/-- The quotient by a subspace is isomorphic to its dual annihilator. -/
noncomputable def quot_equiv_annihilator (W : subspace K V) :
  (V ⧸ W) ≃ₗ[K] W.dual_annihilator :=
begin
  refine _ ≪≫ₗ W.quot_dual_equiv_annihilator,
  refine linear_equiv.quot_equiv_of_equiv _ (basis.of_vector_space K V).to_dual_equiv,
  exact (basis.of_vector_space K W).to_dual_equiv.trans W.dual_equiv_dual
end

open finite_dimensional

@[simp]
lemma finrank_dual_coannihilator_eq {Φ : subspace K (module.dual K V)} :
  finrank K Φ.dual_coannihilator = finrank K Φ.dual_annihilator :=
begin
  rw [submodule.dual_coannihilator, ← module.eval_equiv_to_linear_map],
  exact linear_equiv.finrank_eq (linear_equiv.of_submodule' _ _),
end

lemma finrank_add_finrank_dual_coannihilator_eq
  (W : subspace K (module.dual K V)) :
  finrank K W + finrank K W.dual_coannihilator = finrank K V :=
begin
  rw [finrank_dual_coannihilator_eq, W.quot_equiv_annihilator.finrank_eq.symm, add_comm,
      submodule.finrank_quotient_add_finrank, subspace.dual_finrank_eq],
end

end

end subspace

open module

namespace linear_map
variables {R : Type*} [comm_semiring R] {M₁ : Type*} {M₂ : Type*}
variables [add_comm_monoid M₁] [module R M₁] [add_comm_monoid M₂] [module R M₂]

variable (f : M₁ →ₗ[R] M₂)

lemma ker_dual_map_eq_dual_annihilator_range :
  f.dual_map.ker = f.range.dual_annihilator :=
begin
  ext φ, split; intro hφ,
  { rw mem_ker at hφ,
    rw submodule.mem_dual_annihilator,
    rintro y ⟨x, rfl⟩,
    rw [← dual_map_apply, hφ, zero_apply] },
  { ext x,
    rw dual_map_apply,
    rw submodule.mem_dual_annihilator at hφ,
    exact hφ (f x) ⟨x, rfl⟩ }
end

lemma range_dual_map_le_dual_annihilator_ker :
  f.dual_map.range ≤ f.ker.dual_annihilator :=
begin
  rintro _ ⟨ψ, rfl⟩,
  simp_rw [submodule.mem_dual_annihilator, mem_ker],
  rintro x hx,
  rw [dual_map_apply, hx, map_zero]
end

end linear_map

section comm_ring

variables {R M M' : Type*}
variables [comm_ring R] [add_comm_group M] [module R M] [add_comm_group M'] [module R M']

namespace submodule

/-- Given a submodule, corestrict to the pairing on `M ⧸ W` by
simultaneously restricting to `W.dual_annihilator`.

See `subspace.dual_copairing_nondegenerate`. -/
def dual_copairing (W : submodule R M) :
  W.dual_annihilator →ₗ[R] M ⧸ W →ₗ[R] R :=
linear_map.flip $ W.liftq ((module.dual_pairing R M).dom_restrict W.dual_annihilator).flip
  (by { intros w hw, ext ⟨φ, hφ⟩, exact (mem_dual_annihilator φ).mp hφ w hw })

@[simp] lemma dual_copairing_apply {W : submodule R M} (φ : W.dual_annihilator) (x : M) :
  W.dual_copairing φ (quotient.mk x) = φ x := rfl

/-- Given a submodule, restrict to the pairing on `W` by
simultaneously corestricting to `module.dual R M ⧸ W.dual_annihilator`.
This is `submodule.dual_restrict` factored through the quotient by its kernel (which
is `W.dual_annihilator` by definition).

See `subspace.dual_pairing_nondegenerate`. -/
def dual_pairing (W : submodule R M) :
  module.dual R M ⧸ W.dual_annihilator →ₗ[R] W →ₗ[R] R :=
W.dual_annihilator.liftq W.dual_restrict le_rfl

@[simp] lemma dual_pairing_apply {W : submodule R M} (φ : module.dual R M) (x : W) :
  W.dual_pairing (quotient.mk φ) x = φ x := rfl

/-- That $\operatorname{im}(q^* : (V/W)^* \to V^*) = \operatorname{ann}(W)$. -/
lemma range_dual_map_mkq_eq (W : submodule R M) :
  W.mkq.dual_map.range = W.dual_annihilator :=
begin
  ext φ,
  rw linear_map.mem_range,
  split,
  { rintro ⟨ψ, rfl⟩,
    have := linear_map.mem_range_self W.mkq.dual_map ψ,
    simpa only [ker_mkq] using linear_map.range_dual_map_le_dual_annihilator_ker W.mkq this, },
  { intro hφ,
    existsi W.dual_copairing ⟨φ, hφ⟩,
    ext,
    refl, }
end

/-- Equivalence $(M/W)^* \approx \operatorname{ann}(W)$. That is, there is a one-to-one
correspondence between the dual of `M ⧸ W` and those elements of the dual of `M` that
vanish on `W`.

The inverse of this is `submodule.dual_copairing`. -/
def dual_quot_equiv_dual_annihilator (W : submodule R M) :
  module.dual R (M ⧸ W) ≃ₗ[R] W.dual_annihilator :=
linear_equiv.of_linear
  (W.mkq.dual_map.cod_restrict W.dual_annihilator $
    λ φ, W.range_dual_map_mkq_eq ▸ W.mkq.dual_map.mem_range_self φ)
  W.dual_copairing
  (by { ext, refl}) (by { ext, refl })

@[simp] lemma dual_quot_equiv_dual_annihilator_apply (W : submodule R M)
  (φ : module.dual R (M ⧸ W)) (x : M) :
  dual_quot_equiv_dual_annihilator W φ x = φ (quotient.mk x) := rfl

lemma dual_copairing_eq (W : submodule R M) :
  W.dual_copairing = (dual_quot_equiv_dual_annihilator W).symm.to_linear_map := rfl

@[simp] lemma dual_quot_equiv_dual_annihilator_symm_apply_mk (W : submodule R M)
  (φ : W.dual_annihilator) (x : M) :
  (dual_quot_equiv_dual_annihilator W).symm φ (quotient.mk x) = φ x := rfl

end submodule

namespace linear_map
open submodule

lemma range_dual_map_eq_dual_annihilator_ker_of_surjective
  (f : M →ₗ[R] M') (hf : function.surjective f) :
  f.dual_map.range = f.ker.dual_annihilator :=
begin
  rw ← f.ker.range_dual_map_mkq_eq,
  let f' := linear_map.quot_ker_equiv_of_surjective f hf,
  transitivity linear_map.range (f.dual_map.comp f'.symm.dual_map.to_linear_map),
  { rw linear_map.range_comp_of_range_eq_top,
    apply linear_equiv.range },
  { apply congr_arg,
    ext φ x,
    simp only [linear_map.coe_comp, linear_equiv.coe_to_linear_map, linear_map.dual_map_apply,
      linear_equiv.dual_map_apply, mkq_apply, f', linear_map.quot_ker_equiv_of_surjective,
      linear_equiv.trans_symm, linear_equiv.trans_apply, linear_equiv.of_top_symm_apply,
      linear_map.quot_ker_equiv_range_symm_apply_image, mkq_apply], }
end

-- Note, this can be specialized to the case where `R` is an injective `R`-module, or when
-- `f.coker` is a projective `R`-module.
lemma range_dual_map_eq_dual_annihilator_ker_of_subtype_range_surjective
  (f : M →ₗ[R] M') (hf : function.surjective f.range.subtype.dual_map) :
  f.dual_map.range = f.ker.dual_annihilator :=
begin
  have rr_surj : function.surjective f.range_restrict,
  { rw [← linear_map.range_eq_top, linear_map.range_range_restrict] },
  have := range_dual_map_eq_dual_annihilator_ker_of_surjective f.range_restrict rr_surj,
  convert this using 1,
  { change ((submodule.subtype f.range).comp f.range_restrict).dual_map.range = _,
    rw [← linear_map.dual_map_comp_dual_map, linear_map.range_comp_of_range_eq_top],
    rwa linear_map.range_eq_top, },
  { apply congr_arg,
    exact (linear_map.ker_range_restrict f).symm, },
end

end linear_map

end comm_ring

section vector_space

variables {K : Type*} [field K] {V₁ : Type*} {V₂ : Type*}
variables [add_comm_group V₁] [module K V₁] [add_comm_group V₂] [module K V₂]

namespace linear_map

lemma dual_pairing_nondegenerate : (dual_pairing K V₁).nondegenerate :=
⟨separating_left_iff_ker_eq_bot.mpr ker_id, λ x, (forall_dual_apply_eq_zero_iff K x).mp⟩

lemma dual_map_surjective_of_injective {f : V₁ →ₗ[K] V₂} (hf : function.injective f) :
  function.surjective f.dual_map :=
begin
  intro φ,
  let f' := linear_equiv.of_injective f hf,
  use subspace.dual_lift (range f) (f'.symm.dual_map φ),
  ext x,
  rw [linear_map.dual_map_apply, subspace.dual_lift_of_mem (mem_range_self f x),
    linear_equiv.dual_map_apply],
  congr' 1,
  exact linear_equiv.symm_apply_apply f' x,
end

lemma range_dual_map_eq_dual_annihilator_ker (f : V₁ →ₗ[K] V₂) :
  f.dual_map.range = f.ker.dual_annihilator :=
range_dual_map_eq_dual_annihilator_ker_of_subtype_range_surjective f $
  dual_map_surjective_of_injective (range f).injective_subtype

/-- For vector spaces, `f.dual_map` is surjective if and only if `f` is injective -/
@[simp] lemma dual_map_surjective_iff {f : V₁ →ₗ[K] V₂} :
  function.surjective f.dual_map ↔ function.injective f :=
by rw [← linear_map.range_eq_top, range_dual_map_eq_dual_annihilator_ker,
       ← submodule.dual_annihilator_bot, subspace.dual_annihilator_inj, linear_map.ker_eq_bot]

end linear_map

namespace subspace
open submodule

lemma dual_pairing_eq (W : subspace K V₁) :
  W.dual_pairing = W.quot_annihilator_equiv.to_linear_map :=
by { ext, refl }

lemma dual_pairing_nondegenerate (W : subspace K V₁) : W.dual_pairing.nondegenerate :=
begin
  split,
  { rw [linear_map.separating_left_iff_ker_eq_bot, dual_pairing_eq],
    apply linear_equiv.ker, },
  { intros x h,
    rw ← forall_dual_apply_eq_zero_iff K x,
    intro φ,
    simpa only [submodule.dual_pairing_apply, dual_lift_of_subtype]
      using h (submodule.quotient.mk (W.dual_lift φ)), }
end

lemma dual_copairing_nondegenerate (W : subspace K V₁) : W.dual_copairing.nondegenerate :=
begin
  split,
  { rw [linear_map.separating_left_iff_ker_eq_bot, dual_copairing_eq],
    apply linear_equiv.ker, },
  { rintro ⟨x⟩,
    simp only [quotient.quot_mk_eq_mk, dual_copairing_apply, quotient.mk_eq_zero],
    rw [← forall_mem_dual_annihilator_apply_eq_zero_iff, set_like.forall],
    exact id, }
end

-- Argument from https://math.stackexchange.com/a/2423263/172988
lemma dual_annihilator_inf_eq (W W' : subspace K V₁) :
  (W ⊓ W').dual_annihilator = W.dual_annihilator ⊔ W'.dual_annihilator :=
begin
  refine le_antisymm _ (sup_dual_annihilator_le_inf W W'),
  let F : V₁ →ₗ[K] (V₁ ⧸ W) × (V₁ ⧸ W') := (submodule.mkq W).prod (submodule.mkq W'),
  have : F.ker = W ⊓ W' := by simp only [linear_map.ker_prod, ker_mkq],
  rw [← this, ← linear_map.range_dual_map_eq_dual_annihilator_ker],
  intro φ,
  rw [linear_map.mem_range],
  rintro ⟨x, rfl⟩,
  rw [submodule.mem_sup],
  obtain ⟨⟨a, b⟩, rfl⟩ := (dual_prod_dual_equiv_dual K (V₁ ⧸ W) (V₁ ⧸ W')).surjective x,
  obtain ⟨a', rfl⟩ := (dual_quot_equiv_dual_annihilator W).symm.surjective a,
  obtain ⟨b', rfl⟩ := (dual_quot_equiv_dual_annihilator W').symm.surjective b,
  use [a', a'.property, b', b'.property],
  refl,
end

-- This is also true if `V₁` is finite dimensional since one can restrict `ι` to some subtype
-- for which the infi and supr are the same.
--
-- The obstruction to the `dual_annihilator_inf_eq` argument carrying through is that we need
-- for `module.dual R (Π (i : ι), V ⧸ W i) ≃ₗ[K] Π (i : ι), module.dual R (V ⧸ W i)`, which is not
-- true for infinite `ι`. One would need to add additional hypothesis on `W` (for example, it might
-- be true when the family is inf-closed).
lemma dual_annihilator_infi_eq {ι : Type*} [_root_.finite ι] (W : ι → subspace K V₁) :
  (⨅ (i : ι), W i).dual_annihilator = (⨆ (i : ι), (W i).dual_annihilator) :=
begin
  unfreezingI { revert ι },
  refine finite.induction_empty_option _ _ _,
  { intros α β h hyp W,
    rw [← h.infi_comp, hyp (W ∘ h), ← h.supr_comp], },
  { intro W,
    rw [supr_of_empty', infi_of_empty', Inf_empty, Sup_empty, dual_annihilator_top], },
  { introsI α _ h W,
    rw [infi_option, supr_option, dual_annihilator_inf_eq, h], }
end

/-- For vector spaces, dual annihilators carry direct sum decompositions
to direct sum decompositions. -/
lemma is_compl_dual_annihilator {W W' : subspace K V₁} (h : is_compl W W') :
  is_compl W.dual_annihilator W'.dual_annihilator :=
begin
  rw [is_compl_iff, disjoint_iff, codisjoint_iff] at h ⊢,
  rw [← dual_annihilator_inf_eq, ← dual_annihilator_sup_eq, h.1, h.2,
    dual_annihilator_top, dual_annihilator_bot],
  exact ⟨rfl, rfl⟩
end

/-- For finite-dimensional vector spaces, one can distribute duals over quotients by identifying
`W.dual_lift.range` with `W`. Note that this depends on a choice of splitting of `V₁`. -/
def dual_quot_distrib [finite_dimensional K V₁] (W : subspace K V₁) :
  module.dual K (V₁ ⧸ W) ≃ₗ[K] (module.dual K V₁ ⧸ W.dual_lift.range) :=
W.dual_quot_equiv_dual_annihilator.trans W.quot_dual_equiv_annihilator.symm

end subspace

section finite_dimensional

open finite_dimensional linear_map

variable [finite_dimensional K V₂]

namespace linear_map

-- TODO(kmill) remove finite_dimensional if possible
-- see https://github.com/leanprover-community/mathlib/pull/17521#discussion_r1083242551
@[simp] lemma finrank_range_dual_map_eq_finrank_range (f : V₁ →ₗ[K] V₂) :
  finrank K f.dual_map.range = finrank K f.range :=
begin
  have := submodule.finrank_quotient_add_finrank f.range,
  rw [(subspace.quot_equiv_annihilator f.range).finrank_eq,
      ← ker_dual_map_eq_dual_annihilator_range] at this,
  conv_rhs at this { rw ← subspace.dual_finrank_eq },
  refine add_left_injective (finrank K f.dual_map.ker) _,
  change _ + _ = _ + _,
  rw [finrank_range_add_finrank_ker f.dual_map, add_comm, this],
end

/-- `f.dual_map` is injective if and only if `f` is surjective -/
@[simp] lemma dual_map_injective_iff {f : V₁ →ₗ[K] V₂} :
  function.injective f.dual_map ↔ function.surjective f :=
begin
  refine ⟨_, λ h, dual_map_injective_of_surjective h⟩,
  rw [← range_eq_top, ← ker_eq_bot],
  intro h,
  apply finite_dimensional.eq_top_of_finrank_eq,
  rw ← finrank_eq_zero at h,
  rw [← add_zero (finite_dimensional.finrank K f.range), ← h,
      ← linear_map.finrank_range_dual_map_eq_finrank_range,
      linear_map.finrank_range_add_finrank_ker, subspace.dual_finrank_eq],
end

/-- `f.dual_map` is bijective if and only if `f` is -/
@[simp] lemma dual_map_bijective_iff {f : V₁ →ₗ[K] V₂} :
  function.bijective f.dual_map ↔ function.bijective f :=
by simp_rw [function.bijective, dual_map_surjective_iff, dual_map_injective_iff, and.comm]

end linear_map

end finite_dimensional

end vector_space

namespace tensor_product

variables (R : Type*) (M : Type*) (N : Type*)

variables {ι κ : Type*}
variables [decidable_eq ι] [decidable_eq κ]
variables [fintype ι] [fintype κ]

open_locale big_operators
open_locale tensor_product

local attribute [ext] tensor_product.ext

open tensor_product
open linear_map

section
variables [comm_semiring R] [add_comm_monoid M] [add_comm_monoid N]
variables [module R M] [module R N]

/--
The canonical linear map from `dual M ⊗ dual N` to `dual (M ⊗ N)`,
sending `f ⊗ g` to the composition of `tensor_product.map f g` with
the natural isomorphism `R ⊗ R ≃ R`.
-/
def dual_distrib : (dual R M) ⊗[R] (dual R N) →ₗ[R] dual R (M ⊗[R] N) :=
(comp_right ↑(tensor_product.lid R R)) ∘ₗ hom_tensor_hom_map R M N R R

variables {R M N}

@[simp]
lemma dual_distrib_apply (f : dual R M) (g : dual R N) (m : M) (n : N) :
  dual_distrib R M N (f ⊗ₜ g) (m ⊗ₜ n) = f m * g n :=
rfl

end

variables {R M N}
variables [comm_ring R] [add_comm_group M] [add_comm_group N]
variables [module R M] [module R N]

/--
An inverse to `dual_tensor_dual_map` given bases.
-/
noncomputable
def dual_distrib_inv_of_basis (b : basis ι R M) (c : basis κ R N) :
  dual R (M ⊗[R] N) →ₗ[R] (dual R M) ⊗[R] (dual R N) :=
∑ i j, (ring_lmap_equiv_self R ℕ _).symm (b.dual_basis i ⊗ₜ c.dual_basis j)
    ∘ₗ applyₗ (c j) ∘ₗ applyₗ (b i) ∘ₗ (lcurry R M N R)

@[simp]
lemma dual_distrib_inv_of_basis_apply (b : basis ι R M) (c : basis κ R N)
  (f : dual R (M ⊗[R] N)) : dual_distrib_inv_of_basis b c f =
  ∑ i j, (f (b i ⊗ₜ c j)) • (b.dual_basis i ⊗ₜ c.dual_basis j) :=
by simp [dual_distrib_inv_of_basis]

/--
A linear equivalence between `dual M ⊗ dual N` and `dual (M ⊗ N)` given bases for `M` and `N`.
It sends `f ⊗ g` to the composition of `tensor_product.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simps]
noncomputable def dual_distrib_equiv_of_basis (b : basis ι R M) (c : basis κ R N) :
  (dual R M) ⊗[R] (dual R N) ≃ₗ[R] dual R (M ⊗[R] N) :=
begin
  refine linear_equiv.of_linear
    (dual_distrib R M N) (dual_distrib_inv_of_basis b c) _ _,
  { ext f m n,
    have h : ∀ (r s : R), r • s = s • r := is_commutative.comm,
    simp only [compr₂_apply, mk_apply, comp_apply, id_apply, dual_distrib_inv_of_basis_apply,
      linear_map.map_sum, map_smul, sum_apply, smul_apply, dual_distrib_apply, h (f _) _,
      ← f.map_smul, ←f.map_sum, ←smul_tmul_smul, ←tmul_sum, ←sum_tmul, basis.coe_dual_basis,
      basis.coord_apply, basis.sum_repr] },
  { ext f g,
    simp only [compr₂_apply, mk_apply, comp_apply, id_apply, dual_distrib_inv_of_basis_apply,
      dual_distrib_apply, ←smul_tmul_smul, ←tmul_sum, ←sum_tmul, basis.coe_dual_basis,
      basis.sum_dual_apply_smul_coord] }
end

variables (R M N)
variables [module.finite R M] [module.finite R N] [module.free R M] [module.free R N]
variables [nontrivial R]

open_locale classical

/--
A linear equivalence between `dual M ⊗ dual N` and `dual (M ⊗ N)` when `M` and `N` are finite free
modules. It sends `f ⊗ g` to the composition of `tensor_product.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simp]
noncomputable
def dual_distrib_equiv : (dual R M) ⊗[R] (dual R N) ≃ₗ[R] dual R (M ⊗[R] N) :=
dual_distrib_equiv_of_basis (module.free.choose_basis R M) (module.free.choose_basis R N)

end tensor_product
