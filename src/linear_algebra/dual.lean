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

local attribute [instance, priority 0] classical.prop_decidable

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
universes u v
variables {K : Type u} {V : Type v}
variables [discrete_field K] [add_comm_group V] [vector_space K V]
variables {B : set V} (h : is_basis K B)
open vector_space module module.dual submodule linear_map cardinal function

instance dual.vector_space : vector_space K (dual K V) := {..dual.module K V}

include h

def to_dual : V →ₗ[K] module.dual K V :=
h.constr $ λ v, h.constr $ λ w, if w = v then 1 else 0

lemma to_dual_apply (v ∈ B) (w ∈ B) :
  (h.to_dual v) w = if w = v then 1 else 0 :=
by erw [constr_basis h ‹v ∈ B›, constr_basis h ‹w ∈ B›]

def to_dual_flip (v : V) : (V →ₗ[K] K) := (linear_map.flip h.to_dual).to_fun v

omit h
def eval_lc_at (v : V) : (lc K V) →ₗ[K] K :=
{ to_fun := λ f, f v,
  add := by intros; rw finsupp.add_apply,
  smul := by intros; rw finsupp.smul_apply }
include h

def coord_fun (v : V) : (V →ₗ[K] K) := (eval_lc_at v).comp h.repr

lemma coord_fun_eq_repr (v w : V) : h.coord_fun v w = h.repr w v := rfl

lemma to_dual_swap_eq_to_dual (v w : V) : h.to_dual_flip v w = h.to_dual w v := rfl

lemma to_dual_eq_repr (v : V) (b ∈ B) : (h.to_dual v) b = h.repr v b :=
begin
  rw [←coord_fun_eq_repr, ←to_dual_swap_eq_to_dual],
  apply congr_fun,
  dsimp,
  congr',
  apply h.ext,
  intros,
  rw [to_dual_swap_eq_to_dual, to_dual_apply],
  { split_ifs with hx,
    { rwa [hx, coord_fun_eq_repr, repr_eq_single, finsupp.single_apply, if_pos rfl] },
    { rwa [coord_fun_eq_repr, repr_eq_single, finsupp.single_apply, if_neg (ne.symm hx)] } },
  assumption'
end

lemma to_dual_inj (v : V) (a : h.to_dual v = 0) : v = 0 :=
begin
  rw [← mem_bot K, ← h.repr_ker, mem_ker],
  apply finsupp.ext,
  intro b,
  by_cases hb : b ∈ B,
  { rw [←to_dual_eq_repr _ _ _ hb, a],
    refl },
  { dsimp,
    rw ←finsupp.not_mem_support_iff,
    by_contradiction hb,
    have nhb : b ∈ B := set.mem_of_subset_of_mem (h.repr_supported v) hb,
    contradiction }
end

theorem to_dual_ker : h.to_dual.ker = ⊥ :=
ker_eq_bot'.mpr h.to_dual_inj

theorem to_dual_range [fin : fintype B] : h.to_dual.range = ⊤ :=
begin
  rw eq_top_iff',
  intro f,
  rw linear_map.mem_range,
  let lin_comb : B →₀ K := finsupp.on_finset fin.elems (λ b, f.to_fun b) _,
  let emb := embedding.subtype B,
  { use lc.total K V (finsupp.emb_domain emb lin_comb),
    apply h.ext,
    intros x hx,
    rw [h.to_dual_eq_repr _ x hx, repr_total _],
    have emb_x : x = emb ⟨x, hx⟩, from rfl,
    { rw [emb_x, finsupp.emb_domain_apply emb lin_comb _, ← emb_x], simpa },
    { rw [lc.mem_supported, finsupp.support_emb_domain, finset.map_eq_image, finset.coe_image],
      apply subtype.val_image_subset } },
  { intros a _,
    apply fin.complete }
end

def dual_basis : set (dual K V) := h.to_dual '' B

theorem dual_lin_independent : linear_independent K h.dual_basis :=
begin
  apply linear_independent.image h.1,
  rw to_dual_ker,
  exact disjoint_bot_right
end

def to_dual_equiv [fintype B] : V ≃ₗ[K] (dual K V) :=
linear_equiv.of_bijective h.to_dual h.to_dual_ker h.to_dual_range

theorem dual_basis_is_basis [fintype B] : is_basis K h.dual_basis :=
h.to_dual_equiv.is_basis h

@[simp] lemma to_dual_to_dual [fintype B] :
  (h.dual_basis_is_basis.to_dual).comp h.to_dual = eval K V :=
begin
  apply h.ext,
  intros b hb,
  apply h.dual_basis_is_basis.ext,
  intros c hc,
  dunfold eval,
  rw [linear_map.flip_apply, linear_map.id_apply, linear_map.comp_apply,
      to_dual_apply h.dual_basis_is_basis (h.to_dual b) _ c hc],
  { dsimp [dual_basis] at hc,
    rw set.mem_image at hc,
    rcases hc with ⟨b', hb', rfl⟩,
    rw to_dual_apply,
    split_ifs with h₁ h₂; try {refl},
    { have hh : b = b', from (ker_eq_bot.1 h.to_dual_ker h₁).symm, contradiction },
    { subst h_1, contradiction },
    assumption' },
  { dunfold dual_basis,
    exact set.mem_image_of_mem h.to_dual hb }
end

theorem dual_dim_eq [fintype B] :
  cardinal.lift.{v (max u v)} (dim K V) = dim K (dual K V) :=
by { rw linear_equiv.dim_eq_lift h.to_dual_equiv, apply cardinal.lift_id }

end is_basis

namespace vector_space

universes u v
variables {K : Type u} {V : Type v}
variables [discrete_field K] [add_comm_group V] [vector_space K V]
open module module.dual submodule linear_map cardinal is_basis

theorem eval_ker : (eval K V).ker = ⊥ :=
begin
  rw ker_eq_bot',
  intros v h,
  rw linear_map.ext_iff at h,
  by_contradiction H,
  rcases exists_subset_is_basis (linear_independent_singleton H) with ⟨b, hv, hb⟩,
  swap 4, assumption,
  have hv' : v ∈ b := hv (set.mem_singleton v),
  let hx := h (hb.to_dual v),
  erw [eval_apply, to_dual_apply _ _ hv' _ hv', if_pos rfl, zero_apply _] at hx,
  exact one_ne_zero hx
end

theorem dual_dim_eq (h : dim K V < omega) :
  cardinal.lift.{v (max u v)} (dim K V) = dim K (dual K V) :=
begin
  rcases exists_is_basis_fintype h with ⟨b, hb, ⟨hf⟩⟩,
  resetI,
  exact hb.dual_dim_eq
end

set_option class.instance_max_depth 70

lemma eval_range (h : dim K V < omega) : (eval K V).range = ⊤ :=
begin
  rcases exists_is_basis_fintype h with ⟨b, hb, ⟨hf⟩⟩,
  resetI,
  rw [← hb.to_dual_to_dual, range_comp, hb.to_dual_range, map_top, to_dual_range _],
  delta dual_basis,
  apply_instance
end

def eval_equiv (h : dim K V < omega) : V ≃ₗ[K] dual K (dual K V) :=
linear_equiv.of_bijective (eval K V) eval_ker (eval_range h)

end vector_space
