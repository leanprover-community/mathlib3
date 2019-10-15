/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle

Dual vector spaces, the spaces of linear functionals to the base field, including the dual basis
isomorphism and evaluation isomorphism in the finite-dimensional case.
-/
import linear_algebra.tensor_product
import linear_algebra.finite_dimensional
import tactic.apply_fun
noncomputable theory

namespace module
variables (R : Type*) (M : Type*)
variables [comm_ring R] [add_comm_group M] [module R M]

@[derive [add_comm_group, module R]] def dual := M →ₗ[R] R

namespace dual

instance : has_coe_to_fun (dual R M) := ⟨_, linear_map.to_fun⟩

def eval : M →ₗ[R] (dual R (dual R M)) := linear_map.id.flip

lemma eval_apply (v : M) (a : dual R M) : (eval R M v) a = a v :=
begin
  dunfold eval,
  rw [linear_map.flip_apply, linear_map.id_apply]
end

end dual
end module

namespace is_basis
universes u v w
variables {K : Type u} {V : Type v} {ι : Type w}
variables [discrete_field K] [add_comm_group V] [vector_space K V]
open vector_space module module.dual submodule linear_map cardinal function

instance dual.vector_space : vector_space K (dual K V) := { ..module.dual.inst K V }

variables [de : decidable_eq ι]
variables {B : ι → V} (h : is_basis K B)

include de h

def to_dual : V →ₗ[K] module.dual K V :=
h.constr $ λ v, h.constr $ λ w, if w = v then 1 else 0

lemma to_dual_apply (i j : ι) :
  (h.to_dual (B i)) (B j) = if i = j then 1 else 0 :=
  by erw [constr_basis h, constr_basis h]; ac_refl

def to_dual_flip (v : V) : (V →ₗ[K] K) := (linear_map.flip h.to_dual).to_fun v

omit de h
def eval_finsupp_at (i : ι) : (ι →₀ K) →ₗ[K] K :=
{ to_fun := λ f, f i,
  add := by intros; rw finsupp.add_apply,
  smul := by intros; rw finsupp.smul_apply }
include h

set_option class.instance_max_depth 50

def coord_fun (i : ι) : (V →ₗ[K] K) := (eval_finsupp_at i).comp h.repr

lemma coord_fun_eq_repr (v : V) (i : ι) : h.coord_fun i v = h.repr v i := rfl

include de

lemma to_dual_swap_eq_to_dual (v w : V) : h.to_dual_flip v w = h.to_dual w v := rfl

lemma to_dual_eq_repr (v : V) (i : ι) : (h.to_dual v) (B i) = h.repr v i :=
begin
  rw [←coord_fun_eq_repr, ←to_dual_swap_eq_to_dual],
  apply congr_fun,
  dsimp,
  congr',
  apply h.ext,
  { intros,
    rw [to_dual_swap_eq_to_dual, to_dual_apply],
    { split_ifs with hx,
      { rwa [hx, coord_fun_eq_repr, repr_eq_single, finsupp.single_apply, if_pos rfl] },
      { rw [coord_fun_eq_repr, repr_eq_single, finsupp.single_apply], symmetry, convert if_neg hx } } }
end

lemma to_dual_inj (v : V) (a : h.to_dual v = 0) : v = 0 :=
begin
  rw [← mem_bot K, ← h.repr_ker, mem_ker],
  apply finsupp.ext,
  intro b,
  rw [←to_dual_eq_repr _ _ _, a],
  refl
end

theorem to_dual_ker : h.to_dual.ker = ⊥ :=
ker_eq_bot'.mpr h.to_dual_inj

theorem to_dual_range [fin : fintype ι] : h.to_dual.range = ⊤ :=
begin
  rw eq_top_iff',
  intro f,
  rw linear_map.mem_range,
  let lin_comb : ι →₀ K := finsupp.on_finset fin.elems (λ i, f.to_fun (B i)) _,
  --let emb := embedding.subtype B,
  { use finsupp.total ι V K B lin_comb,
    apply h.ext,
    { intros i,
      rw [h.to_dual_eq_repr _ i, repr_total h],
      { simpa },
      { rw [finsupp.mem_supported],
        exact λ _ _, set.mem_univ _ } } },
  { intros a _,
    apply fin.complete }
end

def dual_basis : ι → dual K V := λ i, h.to_dual (B i)

theorem dual_lin_independent : linear_independent K h.dual_basis :=
begin
  apply linear_independent.image h.1,
  rw to_dual_ker,
  exact disjoint_bot_right
end

def to_dual_equiv [fintype ι] : V ≃ₗ[K] (dual K V) :=
linear_equiv.of_bijective h.to_dual h.to_dual_ker h.to_dual_range

theorem dual_basis_is_basis [fintype ι] : is_basis K h.dual_basis :=
h.to_dual_equiv.is_basis h

@[simp] lemma to_dual_to_dual [fintype ι] :
  (h.dual_basis_is_basis.to_dual).comp h.to_dual = eval K V :=
begin
  apply @is_basis.ext _ _ _ _ _ _ _ _ _ _ _ _ h,
  intros i,
  apply @is_basis.ext _ _ _ _ _ _ _ _ _ _ _ _ h.dual_basis_is_basis,
  intros j,
  dunfold eval,
  rw [linear_map.flip_apply, linear_map.id_apply, linear_map.comp_apply],
  apply eq.trans (to_dual_apply h.dual_basis_is_basis i j),
  { dunfold dual_basis,
    rw to_dual_apply,
    split_ifs with h₁ h₂; try {refl},
    { exfalso, apply h₂ h₁.symm },
    { exfalso, apply ne.symm h₁ (by assumption) } }
end

theorem dual_dim_eq [fintype ι] :
  cardinal.lift.{v u} (dim K V) = dim K (dual K V) :=
begin
  have :=  linear_equiv.dim_eq_lift  h.to_dual_equiv,
  simp only [cardinal.lift_umax] at this,
  rw [this, ← cardinal.lift_umax],
  apply cardinal.lift_id,
end

end is_basis

namespace vector_space

universes u v
variables {K : Type u} {V : Type v}
variables [discrete_field K] [add_comm_group V] [vector_space K V]
open module module.dual submodule linear_map cardinal is_basis

theorem eval_ker : (eval K V).ker = ⊥ :=
begin
  haveI := classical.dec_eq K,
  haveI := classical.dec_eq V,
  haveI := classical.dec_eq (dual K V),
  rw ker_eq_bot',
  intros v h,
  rw linear_map.ext_iff at h,
  by_contradiction H,
  rcases exists_subset_is_basis (linear_independent_singleton H) with ⟨b, hv, hb⟩,
  swap 4, assumption,
  have hv' : v = (λ (i : b), i.val) ⟨v, hv (set.mem_singleton v)⟩ := rfl,
  let hx := h (hb.to_dual v),
  erw [eval_apply, hv', to_dual_apply, if_pos rfl, zero_apply _] at hx,
  exact one_ne_zero hx
end

theorem dual_dim_eq (h : dim K V < omega) :
  cardinal.lift.{v u} (dim K V) = dim K (dual K V) :=
begin
  letI := classical.dec_eq (dual K V),
  letI := classical.dec_eq V,
  rcases exists_is_basis_fintype h with ⟨b, hb, ⟨hf⟩⟩,
  resetI,
  exact hb.dual_dim_eq
end

set_option class.instance_max_depth 70

lemma eval_range (h : dim K V < omega) : (eval K V).range = ⊤ :=
begin
  haveI := classical.dec_eq (dual K V),
  haveI := classical.dec_eq (dual K (dual K V)),
  letI := classical.dec_eq V,
  rcases exists_is_basis_fintype h with ⟨b, hb, ⟨hf⟩⟩,
  resetI,
  rw [← hb.to_dual_to_dual, range_comp, hb.to_dual_range, map_top, to_dual_range _],
  apply_instance
end

def eval_equiv (h : dim K V < omega) : V ≃ₗ[K] dual K (dual K V) :=
linear_equiv.of_bijective (eval K V) eval_ker (eval_range h)

end vector_space

section dual_pair

open vector_space module module.dual linear_map function

universes u v w
variables {K : Type u} {V : Type v} {ι : Type w} [decidable_eq ι]
variables [discrete_field K] [add_comm_group V] [vector_space K V]
          [decidable_eq V] [decidable_eq (ι → V)] [decidable_eq $ dual K V]

local notation `V'` := dual K V

/-- `e` and `ε` have characteristic properties of a basis and its dual -/
structure dual_pair (e : ι → V) (ε : ι → V') :=
(eval : ∀ i j : ι, ε i (e j) = if i = j then 1 else 0)
(total : ∀ {v : V}, (∀ i, ε i v = 0) → v = 0)
[finite : ∀ v : V, fintype {i | ε i v ≠ 0}]

end dual_pair

namespace dual_pair

local attribute [instance, priority 1] classical.prop_decidable

open vector_space module module.dual linear_map function

universes u v w
variables {K : Type u} {V : Type v} {ι : Type w} [dι : decidable_eq ι]
variables [discrete_field K] [add_comm_group V] [vector_space K V]
          [decidable_eq V] [dιv : decidable_eq (ι → V)] [decidable_eq $ dual K V]
variables {e : ι → V} {ε : ι → dual K V} (h : dual_pair e ε)

include dι dιv h

/-- The coefficients of `v` on the basis `e` -/
def coeffs (v : V) : ι →₀ K :=
{ to_fun := λ i, ε i v,
  support := by { haveI := h.finite v, exact {i : ι | ε i v ≠ 0}.to_finset },
  mem_support_to_fun := by {intro i, rw set.mem_to_finset, exact iff.rfl } }

omit h

@[simp]
lemma coeffs_apply (v : V) (i : ι) : h.coeffs v i = ε i v := rfl

private def help_tcs : has_scalar K V := mul_action.to_has_scalar _ _

local attribute [instance] help_tcs

omit dι dιv

/-- linear combinations of elements of `e` -/
def lc (e : ι → V) (l : ι →₀ K) : V := l.sum (λ (i : ι) (a : K), a • (e i))

include dι dιv

include h

@[simp] lemma dual_lc (l : ι →₀ K) (i : ι) : ε i (dual_pair.lc e l) = l i :=
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
  by_contradiction i_not,
  apply hi,
  rw ← sum_l,
  simpa [h.dual_lc] using supp_l i i_not,
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
omit h

lemma eq_dual : ε = is_basis.dual_basis h.is_basis :=
begin
  funext i,
  refine h.is_basis.ext (λ _, _),
  erw [is_basis.to_dual_apply, h.eval]
end

end dual_pair
