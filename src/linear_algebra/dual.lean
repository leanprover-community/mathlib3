/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle
-/
import linear_algebra.finite_dimensional
import linear_algebra.projection

/-!
# Dual vector spaces

The dual space of an R-module M is the R-module of linear maps `M → R`.

## Main definitions

* `dual R M` defines the dual space of M over R.
* Given a basis for a K-vector space `V`, `is_basis.to_dual` produces a map from `V` to `dual K V`.
* Given families of vectors `e` and `ε`, `dual_pair e ε` states that these families have the
  characteristic properties of a basis and a dual.
* `dual_annihilator W` is the submodule of `dual R M` where every element annihilates `W`.

## Main results

* `to_dual_equiv` : the dual space is linearly equivalent to the primal space.
* `dual_pair.is_basis` and `dual_pair.eq_dual`: if `e` and `ε` form a dual pair, `e` is a basis and
  `ε` is its dual basis.
* `quot_equiv_annihilator`: the quotient by a subspace is isomorphic to its dual annihilator.

## Notation

We sometimes use `V'` as local notation for `dual K V`.

## TODO

Erdös-Kaplansky theorem about the dimension of a dual vector space in case of infinite dimension.
-/

noncomputable theory

namespace module

variables (R : Type*) (M : Type*)
variables [comm_ring R] [add_comm_group M] [module R M]

/-- The dual space of an R-module M is the R-module of linear maps `M → R`. -/
@[derive [add_comm_group, module R]] def dual := M →ₗ[R] R

namespace dual

instance : inhabited (dual R M) := by dunfold dual; apply_instance

instance : has_coe_to_fun (dual R M) := ⟨_, linear_map.to_fun⟩

/-- Maps a module M to the dual of the dual of M. See `vector_space.erange_coe` and
`vector_space.eval_equiv`. -/
def eval : M →ₗ[R] (dual R (dual R M)) := linear_map.flip linear_map.id

@[simp] lemma eval_apply (v : M) (a : dual R M) : eval R M v a = a v :=
begin
  dunfold eval,
  rw [linear_map.flip_apply, linear_map.id_apply]
end

variables {R M} {M' : Type*} [add_comm_group M'] [module R M']

/-- The transposition of linear maps, as a linear map from `M →ₗ[R] M'` to
`dual R M' →ₗ[R] dual R M`. -/
def transpose : (M →ₗ[R] M') →ₗ[R] (dual R M' →ₗ[R] dual R M) :=
(linear_map.llcomp R M M' R).flip

lemma transpose_apply (u : M →ₗ[R] M') (l : dual R M') : transpose u l = l.comp u := rfl

variables {M'' : Type*} [add_comm_group M''] [module R M'']

lemma transpose_comp (u : M' →ₗ[R] M'') (v : M →ₗ[R] M') :
  transpose (u.comp v) = (transpose v).comp (transpose u) := rfl

end dual

end module

namespace is_basis

universes u v w

variables {K : Type u} {V : Type v} {ι : Type w}
variables [field K] [add_comm_group V] [vector_space K V]

open vector_space module module.dual submodule linear_map cardinal function

variables [de : decidable_eq ι]
variables (B : ι → V) (h : is_basis K B)

include de h

/-- The linear map from a vector space equipped with basis to its dual vector space,
taking basis elements to corresponding dual basis elements. -/
def to_dual : V →ₗ[K] module.dual K V :=
h.constr $ λ v, h.constr $ λ w, if w = v then 1 else 0

variable {B}

lemma to_dual_apply (i j : ι) :
  h.to_dual B (B i) (B j) = if i = j then 1 else 0 :=
by { erw [constr_basis h, constr_basis h], ac_refl }

@[simp] lemma to_dual_total_left (f : ι →₀ K) (i : ι) :
  h.to_dual B (finsupp.total ι V K B f) (B i) = f i :=
begin
  rw [finsupp.total_apply, finsupp.sum, linear_map.map_sum, linear_map.sum_apply],
  simp_rw [linear_map.map_smul, linear_map.smul_apply, to_dual_apply, smul_eq_mul,
           mul_boole, finset.sum_ite_eq'],
  split_ifs with h,
  { refl },
  { rw finsupp.not_mem_support_iff.mp h }
end

@[simp] lemma to_dual_total_right (f : ι →₀ K) (i : ι) :
  h.to_dual B (B i) (finsupp.total ι V K B f) = f i :=
begin
  rw [finsupp.total_apply, finsupp.sum, linear_map.map_sum],
  simp_rw [linear_map.map_smul, to_dual_apply, smul_eq_mul, mul_boole, finset.sum_ite_eq],
  split_ifs with h,
  { refl },
  { rw finsupp.not_mem_support_iff.mp h }
end

lemma to_dual_apply_left (v : V) (i : ι) : h.to_dual B v (B i) = h.repr v i :=
by rw [← h.to_dual_total_left, h.total_repr]

lemma to_dual_apply_right (i : ι) (v : V) : h.to_dual B (B i) v = h.repr v i :=
by rw [← h.to_dual_total_right, h.total_repr]

variable (B)

/-- `h.to_dual_flip v` is the linear map sending `w` to `h.to_dual w v`. -/
def to_dual_flip (v : V) : (V →ₗ[K] K) := (h.to_dual B).flip v

variable {B}

omit de

/-- `h.coord_fun i` sends vectors to their `i`'th coordinate with respect to the basis `h`. -/
def coord_fun (i : ι) : (V →ₗ[K] K) := (finsupp.lapply i).comp h.repr

lemma coord_fun_eq_repr (v : V) (i : ι) : h.coord_fun i v = h.repr v i := rfl

include de

-- TODO: this lemma should be called something like `to_dual_flip_apply`
lemma to_dual_swap_eq_to_dual (v w : V) : h.to_dual_flip B v w = h.to_dual B w v := rfl

lemma to_dual_eq_repr (v : V) (i : ι) : h.to_dual B v (B i) = h.repr v i :=
h.to_dual_apply_left v i

lemma to_dual_eq_equiv_fun [fintype ι] (v : V) (i : ι) : h.to_dual B v (B i) = h.equiv_fun v i :=
by rw [h.equiv_fun_apply, to_dual_eq_repr]

lemma to_dual_inj (v : V) (a : h.to_dual B v = 0) : v = 0 :=
begin
  rw [← mem_bot K, ← h.repr_ker, mem_ker],
  apply finsupp.ext,
  intro b,
  rw [←to_dual_eq_repr _ _ _, a],
  refl
end

theorem to_dual_ker : (h.to_dual B).ker = ⊥ :=
ker_eq_bot'.mpr h.to_dual_inj

theorem to_dual_range [fin : fintype ι] : (h.to_dual B).range = ⊤ :=
begin
  rw eq_top_iff',
  intro f,
  rw linear_map.mem_range,
  let lin_comb : ι →₀ K := finsupp.on_finset fin.elems (λ i, f.to_fun (B i)) _,
  { use finsupp.total ι V K B lin_comb,
    apply h.ext,
    { intros i,
      rw [h.to_dual_eq_repr _ i, repr_total h],
      { refl },
      { rw [finsupp.mem_supported],
        exact λ _ _, set.mem_univ _ } } },
  { intros a _,
    apply fin.complete }
end

/-- Maps a basis for `V` to a basis for the dual space. -/
def dual_basis : ι → dual K V := λ i, h.to_dual B (B i)

theorem dual_lin_independent : linear_independent K h.dual_basis :=
h.1.map' _ (to_dual_ker _)

@[simp] lemma dual_basis_apply_self (i j : ι) :
  h.dual_basis i (B j) = if i = j then 1 else 0 :=
h.to_dual_apply i j

variable (B)

/-- A vector space is linearly equivalent to its dual space. -/
def to_dual_equiv [fintype ι] : V ≃ₗ[K] (dual K V) :=
linear_equiv.of_bijective (h.to_dual B) h.to_dual_ker h.to_dual_range

variable {B}

theorem dual_basis_is_basis [fintype ι] : is_basis K h.dual_basis :=
(h.to_dual_equiv B).is_basis h

@[simp] lemma total_dual_basis [fintype ι] (f : ι →₀ K) (i : ι) :
  finsupp.total ι (dual K V) K h.dual_basis f (B i) = f i :=
begin
  rw [finsupp.total_apply, finsupp.sum_fintype, linear_map.sum_apply],
  { simp_rw [smul_apply, smul_eq_mul, dual_basis_apply_self, mul_boole,
             finset.sum_ite_eq', if_pos (finset.mem_univ i)] },
  { intro, rw zero_smul },
end

lemma dual_basis_repr [fintype ι] (l : dual K V) (i : ι) :
  h.dual_basis_is_basis.repr l i = l (B i) :=
by rw [← total_dual_basis h, is_basis.total_repr h.dual_basis_is_basis l ]

lemma dual_basis_equiv_fun [fintype ι] (l : dual K V) (i : ι) :
  h.dual_basis_is_basis.equiv_fun l i = l (B i) :=
by rw [is_basis.equiv_fun_apply, dual_basis_repr]

lemma dual_basis_apply [fintype ι] (i : ι) (v : V) : h.dual_basis i v = h.equiv_fun v i :=
h.to_dual_apply_right i v

@[simp] lemma to_dual_to_dual [fintype ι] :
  (h.dual_basis_is_basis.to_dual _).comp (h.to_dual B) = eval K V :=
begin
  refine h.ext (λ i, h.dual_basis_is_basis.ext (λ j, _)),
  suffices : @ite K _ (classical.prop_decidable _) 1 0 = @ite K _ (de j i) 1 0,
    by simpa [h.dual_basis_is_basis.to_dual_apply_left, h.dual_basis_repr, h.to_dual_apply_right],
  split_ifs; refl
end

omit de

theorem dual_dim_eq [fintype ι] :
  cardinal.lift.{v u} (dim K V) = dim K (dual K V) :=
begin
  classical,
  have := linear_equiv.dim_eq_lift (h.to_dual_equiv B),
  simp only [cardinal.lift_umax] at this,
  rw [this, ← cardinal.lift_umax],
  apply cardinal.lift_id,
end

end is_basis

namespace vector_space

universes u v
variables {K : Type u} {V : Type v}
variables [field K] [add_comm_group V] [vector_space K V]
open module module.dual submodule linear_map cardinal is_basis finite_dimensional

theorem eval_ker : (eval K V).ker = ⊥ :=
begin
  classical,
  rw ker_eq_bot',
  intros v h,
  rw linear_map.ext_iff at h,
  by_contradiction H,
  rcases exists_subset_is_basis (linear_independent_singleton H) with ⟨b, hv, hb⟩,
  swap 4, assumption,
  have hv' : v = (coe : b → V) ⟨v, hv (set.mem_singleton v)⟩ := rfl,
  let hx := h (hb.to_dual _ v),
  rw [eval_apply, hv', to_dual_apply, if_pos rfl, zero_apply] at hx,
  exact one_ne_zero hx
end

theorem dual_dim_eq [finite_dimensional K V] :
  cardinal.lift.{v u} (dim K V) = dim K (dual K V) :=
begin
  classical,
  rcases exists_is_basis_fintype (dim_lt_omega K V) with ⟨b, hb, ⟨hf⟩⟩,
  resetI,
  exact hb.dual_dim_eq
end


lemma erange_coe [finite_dimensional K V] : (eval K V).range = ⊤ :=
begin
  classical,
  rcases exists_is_basis_fintype (dim_lt_omega K V) with ⟨b, hb, ⟨hf⟩⟩,
  unfreezingI { rw [← hb.to_dual_to_dual, range_comp, hb.to_dual_range, map_top, to_dual_range _] },
  apply_instance
end

/-- A vector space is linearly equivalent to the dual of its dual space. -/
def eval_equiv [finite_dimensional K V] : V ≃ₗ[K] dual K (dual K V) :=
linear_equiv.of_bijective (eval K V) eval_ker (erange_coe)

end vector_space

section dual_pair

open vector_space module module.dual linear_map function

universes u v w

variables {K : Type u} {V : Type v} {ι : Type w} [decidable_eq ι]
variables [field K] [add_comm_group V] [vector_space K V]

local notation `V'` := dual K V

/-- `e` and `ε` have characteristic properties of a basis and its dual -/
@[nolint has_inhabited_instance]
structure dual_pair (e : ι → V) (ε : ι → V') :=
(eval : ∀ i j : ι, ε i (e j) = if i = j then 1 else 0)
(total : ∀ {v : V}, (∀ i, ε i v = 0) → v = 0)
[finite : ∀ v : V, fintype {i | ε i v ≠ 0}]

end dual_pair

namespace dual_pair

open vector_space module module.dual linear_map function

universes u v w
variables {K : Type u} {V : Type v} {ι : Type w} [dι : decidable_eq ι]
variables [field K] [add_comm_group V] [vector_space K V]
variables {e : ι → V} {ε : ι → dual K V} (h : dual_pair e ε)

include h

/-- The coefficients of `v` on the basis `e` -/
def coeffs (v : V) : ι →₀ K :=
{ to_fun := λ i, ε i v,
  support := by { haveI := h.finite v, exact {i : ι | ε i v ≠ 0}.to_finset },
  mem_support_to_fun := by {intro i, rw set.mem_to_finset, exact iff.rfl } }


@[simp] lemma coeffs_apply (v : V) (i : ι) : h.coeffs v i = ε i v := rfl

omit h
/-- linear combinations of elements of `e`.
This is a convenient abbreviation for `finsupp.total _ V K e l` -/
def lc (e : ι → V) (l : ι →₀ K) : V := l.sum (λ (i : ι) (a : K), a • (e i))

include h

lemma dual_lc (l : ι →₀ K) (i : ι) : ε i (dual_pair.lc e l) = l i :=
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
lemma coeffs_lc (l : ι →₀ K) : h.coeffs (dual_pair.lc e l) = l :=
by { ext i, rw [h.coeffs_apply, h.dual_lc] }

/-- For any v : V n, \sum_{p ∈ Q n} (ε p v) • e p = v -/
lemma decomposition (v : V) : dual_pair.lc e (h.coeffs v) = v :=
begin
  refine eq_of_sub_eq_zero (h.total _),
  intros i,
  simp [-sub_eq_add_neg, linear_map.map_sub, h.dual_lc, sub_eq_zero_iff_eq]
end

lemma mem_of_mem_span {H : set ι} {x : V} (hmem : x ∈ submodule.span K (e '' H)) :
  ∀ i : ι, ε i x ≠ 0 → i ∈ H :=
begin
  intros i hi,
  rcases (finsupp.mem_span_iff_total _).mp hmem with ⟨l, supp_l, sum_l⟩,
  change dual_pair.lc e l = x at sum_l,
  rw finsupp.mem_supported' at supp_l,
  apply classical.by_contradiction,
  intro i_not,
  apply hi,
  rw ← sum_l,
  simpa [h.dual_lc] using supp_l i i_not
end

lemma is_basis : is_basis K e :=
begin
  split,
  { rw linear_independent_iff,
    intros l H,
    change dual_pair.lc e l = 0 at H,
    ext i,
    apply_fun ε i at H,
    simpa [h.dual_lc] using H },
  { rw submodule.eq_top_iff',
    intro v,
    rw [← set.image_univ, finsupp.mem_span_iff_total],
    exact ⟨h.coeffs v, by simp, h.decomposition v⟩ },
end

lemma eq_dual : ε = is_basis.dual_basis h.is_basis :=
begin
  funext i,
  refine h.is_basis.ext (λ _, _),
  erw [is_basis.to_dual_apply, h.eval]
end

end dual_pair

namespace submodule

universes u v w

variables {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
variable {W : submodule R M}

/-- The `dual_restrict` of a submodule `W` of `M` is the linear map from the
  dual of `M` to the dual of `W` such that the domain of each linear map is
  restricted to `W`. -/
def dual_restrict (W : submodule R M) :
  module.dual R M →ₗ[R] module.dual R W :=
linear_map.dom_restrict' W

@[simp] lemma dual_restrict_apply
  (W : submodule R M) (φ : module.dual R M) (x : W) :
  W.dual_restrict φ x = φ (x : M) := rfl

/-- The `dual_annihilator` of a submodule `W` is the set of linear maps `φ` such
  that `φ w = 0` for all `w ∈ W`. -/
def dual_annihilator {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M]
  [module R M] (W : submodule R M) : submodule R $ module.dual R M :=
W.dual_restrict.ker

@[simp] lemma mem_dual_annihilator (φ : module.dual R M) :
  φ ∈ W.dual_annihilator ↔ ∀ w ∈ W, φ w = 0 :=
begin
  refine linear_map.mem_ker.trans _,
  simp_rw [linear_map.ext_iff, dual_restrict_apply],
  exact ⟨λ h w hw, h ⟨w, hw⟩, λ h w, h w.1 w.2⟩
end

lemma dual_restrict_ker_eq_dual_annihilator (W : submodule R M) :
  W.dual_restrict.ker = W.dual_annihilator :=
rfl

end submodule

namespace subspace

open submodule linear_map

universes u v w

-- We work in vector spaces because `exists_is_compl` only hold for vector spaces
variables {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V]

/-- Given a subspace `W` of `V` and an element of its dual `φ`, `dual_lift W φ` is
the natural extension of `φ` to an element of the dual of `V`.
That is, `dual_lift W φ` sends `w ∈ W` to `φ x` and `x` in the complement of `W` to `0`. -/
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
dual_lift_of_subtype ⟨w, hw⟩

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
  W.dual_annihilator.quotient ≃ₗ[K] module.dual K W :=
(quot_equiv_of_eq _ _ W.dual_restrict_ker_eq_dual_annihilator).symm.trans $
  W.dual_restrict.quot_ker_equiv_of_surjective dual_restrict_surjective

/-- The natural isomorphism forom the dual of a subspace `W` to `W.dual_lift.range`. -/
noncomputable def dual_equiv_dual (W : subspace K V) :
  module.dual K W ≃ₗ[K] W.dual_lift.range :=
linear_equiv.of_injective _ $ ker_eq_bot.2 dual_lift_injective

lemma dual_equiv_dual_def (W : subspace K V) :
  W.dual_equiv_dual.to_linear_map = W.dual_lift.range_restrict := rfl

@[simp] lemma dual_equiv_dual_apply (φ : module.dual K W) :
  W.dual_equiv_dual φ = ⟨W.dual_lift φ, mem_range.2 ⟨φ, rfl⟩⟩ := rfl

section

open_locale classical

open finite_dimensional

variables {V₁ : Type*} [add_comm_group V₁] [vector_space K V₁]

instance [H : finite_dimensional K V] : finite_dimensional K (module.dual K V) :=
begin
  refine @linear_equiv.finite_dimensional _ _ _ _ _ _ _ _ _ H,
  have hB := classical.some_spec (exists_is_basis_finite K V),
  haveI := classical.choice hB.2,
  exact is_basis.to_dual_equiv _ hB.1
end

variables [finite_dimensional K V] [finite_dimensional K V₁]

@[simp] lemma dual_findim_eq :
  findim K (module.dual K V) = findim K V :=
begin
  obtain ⟨n, hn, hf⟩ := exists_is_basis_finite K V,
  refine linear_equiv.findim_eq _,
  haveI : fintype n := set.finite.fintype hf,
  refine (hn.to_dual_equiv _).symm,
end

/-- The quotient by the dual is isomorphic to its dual annihilator.  -/
noncomputable def quot_dual_equiv_annihilator (W : subspace K V) :
  W.dual_lift.range.quotient ≃ₗ[K] W.dual_annihilator :=
linear_equiv.quot_equiv_of_quot_equiv $
  linear_equiv.trans W.quot_annihilator_equiv W.dual_equiv_dual

/-- The quotient by a subspace is isomorphic to its dual annihilator. -/
noncomputable def quot_equiv_annihilator (W : subspace K V) :
  W.quotient ≃ₗ[K] W.dual_annihilator :=
begin
  refine linear_equiv.trans _ W.quot_dual_equiv_annihilator,
  refine linear_equiv.quot_equiv_of_equiv _ _,
  { refine linear_equiv.trans _ W.dual_equiv_dual,
    have hB := classical.some_spec (exists_is_basis_finite K W),
    haveI := classical.choice hB.2,
    exact is_basis.to_dual_equiv _ hB.1 },
  { have hB := classical.some_spec (exists_is_basis_finite K V),
    haveI := classical.choice hB.2,
    exact is_basis.to_dual_equiv _ hB.1 },
end

end

end subspace

variables {R : Type*} [comm_ring R] {M₁ : Type*} {M₂ : Type*}
variables [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂]

open module

/-- Given a linear map `f : M₁ →ₗ[R] M₂`, `f.dual_map` is the linear map between the dual of
`M₂` and `M₁` such that it maps the functional `φ` to `φ ∘ f`. -/
def linear_map.dual_map (f : M₁ →ₗ[R] M₂) : dual R M₂ →ₗ[R] dual R M₁ :=
linear_map.lcomp R R f

@[simp] lemma linear_map.dual_map_apply (f : M₁ →ₗ[R] M₂) (g : dual R M₂) (x : M₁) :
  f.dual_map g x = g (f x) :=
linear_map.lcomp_apply f g x

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
  f.dual_map g x = g (f x) :=
linear_map.lcomp_apply f g x

@[simp] lemma linear_equiv.symm_of_dual_map_eq_dual_map_symm {f : M₁ ≃ₗ[R] M₂} :
  (linear_equiv.dual_map f).symm = linear_equiv.dual_map f.symm := rfl

namespace linear_map

variable {f : M₁ →ₗ[R] M₂}

lemma ker_dual_map_eq_range_dual_annihilator :
  f.dual_map.ker = f.range.dual_annihilator :=
begin
  ext φ, split; intro hφ,
  { rw mem_ker at hφ,
    rw submodule.mem_dual_annihilator,
    rintro y ⟨x, _, rfl⟩,
    rw [← dual_map_apply, hφ, zero_apply] },
  { ext x,
    rw dual_map_apply,
    rw submodule.mem_dual_annihilator at hφ,
    exact hφ (f x) ⟨x, (submodule.mem_coe _).mpr submodule.mem_top, rfl⟩ }
end

lemma range_dual_map_le_dual_annihilator_ker :
  f.dual_map.range ≤ f.ker.dual_annihilator :=
begin
  rintro _ ⟨ψ, _, rfl⟩,
  simp_rw [submodule.mem_dual_annihilator, mem_ker],
  rintro x hx,
  rw [dual_map_apply, hx, map_zero]
end

section finite_dimensional

variables {K : Type*} [field K] {V₁ : Type*} {V₂ : Type*}
variables [add_comm_group V₁] [vector_space K V₁] [add_comm_group V₂] [vector_space K V₂]
variables [finite_dimensional K V₂]

open finite_dimensional

lemma findim_range_dual_map_eq_findim_range {f : V₁ →ₗ[K] V₂} :
  findim K f.dual_map.range = findim K f.range :=
begin
  have := submodule.findim_quotient_add_findim f.range,
  rw [(subspace.quot_equiv_annihilator f.range).findim_eq,
      ← ker_dual_map_eq_range_dual_annihilator] at this,
  conv_rhs at this { rw ← subspace.dual_findim_eq },
  refine add_left_injective (findim K f.dual_map.ker) _,
  change _ + _ = _ + _,
  rw [findim_range_add_findim_ker f.dual_map, add_comm, this],
end

lemma range_dual_map_eq_dual_annihilator_ker [finite_dimensional K V₁] {f : V₁ →ₗ[K] V₂} :
  f.dual_map.range = f.ker.dual_annihilator :=
begin
  refine eq_of_le_of_findim_eq range_dual_map_le_dual_annihilator_ker _,
  have := submodule.findim_quotient_add_findim f.ker,
  rw (subspace.quot_equiv_annihilator f.ker).findim_eq at this,
  refine add_left_injective (findim K f.ker) _,
  simp_rw [this, findim_range_dual_map_eq_findim_range],
  exact findim_range_add_findim_ker f,
end

end finite_dimensional

end linear_map
