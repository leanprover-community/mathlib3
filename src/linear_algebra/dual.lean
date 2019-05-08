/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle

Dual vector spaces, the spaces of linear functionals to the base field, including the dual basis
isomorphism and evaluation isomorphism in the finite-dimensional case.
-/
import linear_algebra.dimension
import linear_algebra.tensor_product
noncomputable theory

namespace module
variables (R : Type*) (M : Type*)
variables [comm_ring R] [add_comm_group M] [module R M]

def dual := M →ₗ[R] R

namespace dual

instance : has_coe_to_fun (dual R M) := ⟨_, linear_map.to_fun⟩

instance : add_comm_group (dual R M) :=
by delta dual; apply_instance

instance : module R (dual R M) :=
by delta dual; apply_instance

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
variables [decidable_eq V] [discrete_field K] [add_comm_group V] [vector_space K V]
variables [decidable_eq (module.dual K V)] [decidable_eq ι]
variables {B : ι → V} (h : is_basis K B)
open vector_space module module.dual submodule linear_map cardinal function

instance dual.vector_space : vector_space K (dual K V) := {..dual.module K V}

include h

def to_dual : V →ₗ[K] module.dual K V :=
h.constr $ λ v, h.constr $ λ w, if w = v then 1 else 0

lemma to_dual_apply (i j : ι) :
  (h.to_dual (B i)) (B j) = if i = j then 1 else 0 :=
  by erw [constr_basis h, constr_basis h]; ac_refl

def to_dual_flip (v : V) : (V →ₗ[K] K) := (linear_map.flip h.to_dual).to_fun v

omit h
def eval_finsupp_at (i : ι) : (ι →₀ K) →ₗ[K] K :=
{ to_fun := λ f, f i,
  add := by intros; rw finsupp.add_apply,
  smul := by intros; rw finsupp.smul_apply }
include h

set_option class.instance_max_depth 50

def coord_fun (i : ι) : (V →ₗ[K] K) := (eval_finsupp_at i).comp h.repr

lemma coord_fun_eq_repr (v : V) (i : ι) : h.coord_fun i v = h.repr v i := rfl

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
      { rwa [coord_fun_eq_repr, repr_eq_single, finsupp.single_apply, if_neg hx] } } },
  { exact classical.dec_eq K }
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
        exact λ _ _, set.mem_univ _ } },
    { exact classical.dec_eq K } },
  { intros a _,
    apply fin.complete }
end

def dual_basis : ι → dual K V := λ i, h.to_dual (B i)

theorem dual_lin_independent : linear_independent K h.dual_basis set.univ :=
begin
  apply linear_independent.image' h.1,
  rw to_dual_ker,
  exact disjoint_bot_right
end

def to_dual_equiv [fintype ι] : V ≃ₗ[K] (dual K V) :=
linear_equiv.of_bijective h.to_dual h.to_dual_ker h.to_dual_range

theorem dual_basis_is_basis [fintype ι] : is_basis K h.dual_basis :=
h.to_dual_equiv.is_basis h

@[simp] lemma to_dual_to_dual [decidable_eq (dual K (dual K V))] [fintype ι] :
  (h.dual_basis_is_basis.to_dual).comp h.to_dual = eval K V :=
begin
  apply @is_basis.ext _ _ _ _ _ _ _ _ (classical.dec_eq (dual K (dual K V))) _ _ _ _ _ _ _ h,
  intros i,
  apply @is_basis.ext _ _ _ _ _ _ _ _ (classical.dec_eq _) _ _ _ _ _ _ _ h.dual_basis_is_basis,
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

theorem dual_dim_eq [decidable_eq V] [decidable_eq (dual K V)] (h : dim K V < omega) :
  cardinal.lift.{v u} (dim K V) = dim K (dual K V) :=
begin
  rcases exists_is_basis_fintype h with ⟨b, hb, ⟨hf⟩⟩,
  resetI,
  exact hb.dual_dim_eq
end

set_option class.instance_max_depth 70

lemma eval_range [decidable_eq V] (h : dim K V < omega) : (eval K V).range = ⊤ :=
begin
  haveI := classical.dec_eq (dual K V),
  haveI := classical.dec_eq (dual K (dual K V)),
  rcases exists_is_basis_fintype h with ⟨b, hb, ⟨hf⟩⟩,
  resetI,
  rw [← hb.to_dual_to_dual, range_comp, hb.to_dual_range, map_top, to_dual_range _],
  delta dual_basis,
  apply_instance
end

def eval_equiv [decidable_eq V] (h : dim K V < omega) : V ≃ₗ[K] dual K (dual K V) :=
linear_equiv.of_bijective (eval K V) eval_ker (eval_range h)

end vector_space
