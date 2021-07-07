/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import ring_theory.simple_module
import linear_algebra.matrix
import linear_algebra.direct_sum_module
import algebra.direct_sum

/-!
# Decompositions of Modules
This file talks about decompositions of modules.
-/

universes u v w

open_locale direct_sum classical big_operators
open classical linear_map
noncomputable theory

variables (ι : Type u) (R : Type v) (M : Type w)
variables [semiring R] [add_comm_monoid M] [module R M]

/-- A `decomposition ι R M` for a module `M` is the type of `ι`-indexed decompositions of `M`.
The factors are available as `factors : ι → submodule R M`.
To create a decomposition of `M`, one furthermore must provide data that the
factors satisfy `∀ i : ι, disjoint (factors i) (⨆ (j ≠ i), factors j)` and
that their union is the whole module `M`.
Note: Why not say `set (submodule R M)`? Then one could get rid of explicitly
identifying `ι`. But I think it's better to follow the `basis` design,
which was phased out of exactly the `set` design because of problems with it.
-/
@[nolint has_inhabited_instance]
structure decomposition : Type (max u v w) :=
(factors : ι → submodule R M)
(factors_ind : complete_lattice.independent factors)
(factors_supr : supr factors = ⊤)

/-
variables {ι R M}

/--
bruh

-/
def terrible_map (p : ι → submodule R M) :
  (⨁ i, p i) →ₗ[R] (supr p : submodule R M) :=
(direct_sum.to_module R ι _ (λ i, submodule.of_le (le_supr p i : p i ≤ supr p)))

@[simp] lemma terrible_map_apply (p : ι → submodule R M) (x : ⨁ (i : ι), (p i)) :
  terrible_map p x = ∑ i in x.support, ⟨(x i).1, (le_supr p i : p i ≤ supr p) (x i).2⟩ :=
begin
  simp only [terrible_map, direct_sum.to_module, dfinsupp.sum_add_hom_apply, coe_mk,
    to_add_monoid_hom_coe, dfinsupp.lsum_apply, subtype.val_eq_coe],
  refine finset.sum_congr rfl (λ i hi, _),
  congr,
end

lemma support_mk_support
  (p : ι → submodule R M) (v : ι →₀ M) (hv: ∀ (i : ι), v i ∈ p i) :
  dfinsupp.support (direct_sum.mk (λ i, p i) v.support (λ i, ⟨v i, hv i⟩)) = v.support :=
begin
  simp only [direct_sum.mk, add_monoid_hom.coe_mk],
  ext i, split,
  { intro hi,
    rw dfinsupp.mem_support_iff at hi,
    simp only [dfinsupp.mk_apply, finsupp.mem_support_iff, subtype.coe_mk, dite_not] at hi,
    split_ifs at hi,
    exact h,
    contradiction, },
  intro hi,
  rw dfinsupp.mem_support_iff,
  simp only [dfinsupp.mk_apply, finsupp.mem_support_iff, subtype.coe_mk, dite_not],
  split_ifs,
  simp only [ne.def, submodule.mk_eq_zero],
  rw ← ne.def,
  rwa finsupp.mem_support_iff at hi,
end

end setup

variables {ι : Type u} {R : Type v} {M : Type w}
variables [ring R] [add_comm_group M] [module R M]
lemma terrible_map_ker
  (p : ι → submodule R M) (h : complete_lattice.independent p) : (terrible_map p).ker = ⊥ :=
begin
  rw ker_eq_bot',
  intros x hx,
  ext i,
  simp only [terrible_map_apply, ← set_like.coe_eq_coe, coe_sum, submodule.coe_mk] at hx,
  revert i,
  by_contra,
  push_neg at h,
  cases h with j hj,
  have : j ∈ dfinsupp.support x, { rw dfinsupp.mem_support_iff, exact_mod_cast hj },
  rw ← finset.sum_erase' _ this at hx,
  simp only [submodule.coe_zero, subtype.val_eq_coe, ← neg_eq_iff_add_eq_zero] at hx,
  simp only [← hx, pi.zero_apply, submodule.coe_zero] at hj,
  have := submodule.disjoint_def.mp (complete_lattice.independent_def.mp h j) (x j) (x j).2,
  have h2 : ∑ (k : ι) in (dfinsupp.support x).erase j,
    ↑(x k) ∈ ⨆ (k : ι) (H : k ∈ (dfinsupp.support x).erase j), p k,
  { apply submodule.sum_mem_bsupr,
    intros c hc,
    exact (x c).2, },
  have h3 : (⨆ (k : ι) (H : k ∈ (dfinsupp.support x).erase j), p k : submodule R M) ≤
    ⨆ (k : ι) (H : k ≠ j), p k,
    { refine bsupr_le_bsupr' (λ i hi, finset.ne_of_mem_erase hi), },
  have h4 := h3 h2,
  rw ← submodule.neg_mem_iff at h4,
  rw hx at h4,
  rw hx at hj,
  have h5 := this h4,
  contradiction,
end

lemma terrible_map_range
  (p : ι → submodule R M) (h : complete_lattice.independent p) : (terrible_map p).range = ⊤ :=
begin
  ext,
  cases x with x hx,
  simp only [coe_fn_sum, submodule.mem_top, mem_range,
    lsum_apply, coe_proj, function.comp_app, function.eval_apply,
    iff_true, coe_comp, subtype.val_eq_coe],
  rw submodule.mem_supr' at hx,
  rcases hx with ⟨v, hv, hvs⟩,
  use direct_sum.mk (λ i, p i) v.support (λ i, ⟨v i, hv i⟩),
  simp only [terrible_map_apply, subtype.val_eq_coe],
  rw support_mk_support,
  rw [← set_like.coe_eq_coe, set_like.coe_mk, ← hvs],
  rw @coe_sum ι R M _ _ _ (supr p : submodule R M) _ v.support,
  refine finset.sum_congr rfl (λ i hi, _),
  simp [direct_sum.mk],
  split_ifs,
  exact h_1.symm,
  exact set_like.coe_mk _ _,
end

/--
blah

-/
def submodule.direct_sum_equiv_of_independent
  (p : ι → submodule R M) (h : complete_lattice.independent p) :
  (⨁ i, p i) ≃ₗ[R] (supr p : submodule R M) :=
begin
  letI : add_comm_group (⨁ (i : ι), (p i)) := direct_sum.add_comm_group (λ i, p i),
  convert @linear_equiv.of_bijective R (⨁ i, p i) (supr p : submodule R M) _ _ _ _ _ _ _ _,
  convert terrible_map p,
  dsimp,
  convert terrible_map_ker p h,
  dsimp,
  convert terrible_map_range p h,
end

@[simp] lemma submodule.direct_sum_equiv_of_independent_apply
  (p : ι → submodule R M) (h : complete_lattice.independent p) (x : ⨁ i, p i) :
  submodule.direct_sum_equiv_of_independent p h x = terrible_map p x :=
rfl

variables {R M}

/--
blah

-/
def is_decomposition.equiv (D : decomposition ι R M) : (⨁ i, D.factors i) ≃ₗ[R] M :=
((submodule.direct_sum_equiv_of_independent D.factors D.factors_ind).trans
  (linear_equiv.of_eq _ _ D.factors_supr)).trans (submodule.top_equiv_self)

lemma is_decomposition.equiv_apply (D : decomposition ι R M) (x : ⨁ i, D.factors i) :
  (is_decomposition.equiv D) x = ∑ i in x.support, x i :=
begin
  rw [is_decomposition.equiv],
  rw linear_equiv.trans_apply,
  rw linear_equiv.trans_apply,
  simp [submodule.top_equiv_self],
end

lemma is_decomposition.equiv_symm_single_apply
  (D : decomposition ι R M) (i : ι) (x : M) (hx : x ∈ D.factors i) :
  (is_decomposition.equiv D).symm x = dfinsupp.single i ⟨x, hx⟩ :=
begin
  apply_fun (is_decomposition.equiv D),
  rw [linear_equiv.apply_symm_apply],
  rw is_decomposition.equiv_apply,
  by_cases h : x = 0,
  { rw dfinsupp.support_single_eq_zero,
    rw finset.sum_empty,
    exact h,
    rw ← submodule.coe_eq_zero,
    exact h,  },
  rw dfinsupp.support_single_ne_zero,
  simp only [dite_eq_ite, if_true, dfinsupp.single_eq_same, submodule.coe_mk, eq_self_iff_true,
    finset.sum_singleton],
  rw ← ne.def at h,
  rw ← submodule.coe_mk x hx at h,
  exact_mod_cast h,
  exact linear_equiv.injective _,
end
-/
