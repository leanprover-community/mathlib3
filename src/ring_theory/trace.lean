/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import order.conditionally_complete_lattice
import field_theory.adjoin
import field_theory.simple_extension
import linear_algebra.bilinear_form
import linear_algebra.char_poly.coeff
import ring_theory.algebra_tower
import ring_theory.localization

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the trace is defined specifically for finite field extensions.
The definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the trace for left multiplication (`algebra.lmul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't matter anyway.

## References

 * https://en.wikipedia.org/wiki/Field_trace

-/

universes u v w

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables {A: Type*} [integral_domain A] [algebra A S]
variables [algebra R S] [algebra R T]
variables {K L : Type*} [field K] [field L] [algebra K L]
variables {ι : Type w} [fintype ι] {b : ι → S} (hb : is_basis R b)

open finite_dimensional
open intermediate_field
open linear_map
open matrix

open_locale big_operators
open_locale matrix

section power_basis

open algebra field polynomial

lemma is_scalar_tower.is_algebraic [algebra S T] [is_scalar_tower R S T] {x : S}
  (inj : function.injective (algebra_map S T)) (hx : is_algebraic R (algebra_map S T x)) :
  is_algebraic R x :=
let ⟨p, hp, hpx⟩ := hx in ⟨p, hp, inj
  (by rwa [ring_hom.map_zero, aeval_def, hom_eval₂,
           ← is_scalar_tower.algebra_map_eq])⟩

lemma intermediate_field.is_algebraic (S : intermediate_field K L) {x : S}
  (hx : is_algebraic K (x : L)) : is_algebraic K x :=
is_scalar_tower.is_algebraic (algebra_map S L).injective hx

lemma is_algebraic_algebra_map (x : K) : is_algebraic K (algebra_map K L x) :=
⟨X - C x, X_sub_C_ne_zero _, by rw [alg_hom.map_sub, aeval_X, aeval_C, sub_self]⟩

variables {x : L} (alg : is_algebraic K x)

lemma exists_eq_aeval_gen (alg : is_algebraic K L) {y : L} (hy : y ∈ K⟮x⟯) :
  ∃ f : polynomial K, y = aeval x f :=
begin
  refine adjoin_induction _ hy _ _ _ _ _ _,
  { intros x hx,
    rcases set.mem_singleton_iff.mp hx with rfl,
    exact ⟨X, (aeval_X _).symm⟩ },
  { intros x,
    refine ⟨C x, (aeval_C _ _).symm⟩ },
  { rintros x y ⟨fx, rfl⟩ ⟨fy, rfl⟩,
    exact ⟨fx + fy, (ring_hom.map_add _ _ _).symm⟩ },
  { rintros x ⟨fx, rfl⟩,
    exact ⟨-fx, (ring_hom.map_neg _ _).symm⟩ },
  { rintros x ⟨fx, x_eq⟩,
    by_cases hx0 : x = 0,
    { rw [hx0, inv_zero],
      exact ⟨0, (ring_hom.map_zero _).symm⟩ },
    have hx : is_integral K x := ((is_algebraic_iff_is_integral _).mp (alg x)),
    rw inv_eq_of_root_of_coeff_zero_ne_zero
      (minimal_polynomial.aeval hx) (minimal_polynomial.coeff_zero_ne_zero hx hx0),
    use - (C ((minimal_polynomial hx).coeff 0)⁻¹) * (minimal_polynomial hx).div_X.comp fx,
    rw aeval_def at x_eq,
    rw [div_eq_inv_mul, alg_hom.map_mul, alg_hom.map_neg, aeval_C, neg_mul_eq_neg_mul,
        ring_hom.map_inv, aeval_def, aeval_def, eval₂_comp, ← x_eq] },
  { rintros x y ⟨fx, rfl⟩ ⟨fy, rfl⟩,
    exact ⟨fx * fy, (ring_hom.map_mul _ _ _).symm⟩ },
end

/-- Bundle `power_basis` in a structure to generalize over `algebra.adjoin` and `adjoin`. -/
structure has_power_basis (R S : Type*) [comm_ring R] [ring S] [algebra R S] :=
(dim : ℕ)
(gen : S)
(is_basis : is_basis R (λ (i : fin dim), gen ^ (i : ℕ)))

@[simp] lemma has_power_basis.total_eq (h : has_power_basis A S) (f : fin h.dim →₀ S) :
  finsupp.total _ _ _ (λ (i : fin h.dim), h.gen ^ (i : ℕ)) f =
    aeval h.gen (finsupp.emb_fin_nat f) :=
by simp [aeval_def, eval₂_eq_sum, finsupp.total, linear_map.smul_right, algebra.smul_def]

noncomputable def has_power_basis_of_is_simple_extension
  (K) [field K] [algebra K L] (alg : is_algebraic K L) [is_simple_extension K L] :
  has_power_basis K L :=
{ dim := (is_simple_extension.minimal_polynomial alg).nat_degree,
  gen := is_simple_extension.primitive_element K L,
  is_basis := is_simple_extension.power_basis_is_basis alg }

lemma gen_simple_extension (alg : is_algebraic K L) [is_simple_extension K L] :
  (has_power_basis_of_is_simple_extension _ alg).gen = is_simple_extension.primitive_element K L :=
rfl

@[simp] lemma total_power_basis_eq {n : ℕ} (f : fin n →₀ K) :
  finsupp.total _ _ _ (λ i : fin n, x ^ (i : ℕ)) f =
  aeval x (finsupp.emb_fin_nat f) :=
by simp_rw [aeval_def, eval₂_eq_sum, finsupp.total_apply, finsupp.emb_fin_nat_sum, algebra.smul_def]

lemma linear_independent_power_basis (hx : is_integral K (adjoin_simple.gen K x)) :
  linear_independent K (λ (i : fin (minimal_polynomial hx).nat_degree),
    adjoin_simple.gen K x ^ (i : ℕ)) :=
begin
  rw linear_independent_iff,
  intros p hp,
  rw total_power_basis_eq at hp,
  rw ← finsupp.emb_fin_nat_eq_zero,
  refine minimal_polynomial.eq_zero_of_degree_lt hx _ hp,
  rw degree_eq_nat_degree (minimal_polynomial.ne_zero _),
  exact polynomial.degree_emb_fin_nat_lt _
end

@[simp] lemma mem_span_set_submodule {M : Type*} [add_comm_monoid M] [semimodule R M]
  (S : submodule R M) (x : S) (s : set S) :
  x ∈ submodule.span R s ↔ (x : M) ∈ submodule.span R (coe '' s : set M) :=
show x ∈ submodule.span R s ↔ S.subtype x ∈ submodule.span R (S.subtype '' s),
by { rw [← submodule.map_span S.subtype, submodule.mem_map],
     simp only [S.subtype_inj_iff, exists_eq_right] }

@[simp] lemma intermediate_field.coe_eq (S : intermediate_field K L) :
  (coe : S → L) = algebra_map S L := rfl

lemma nat_degree_lt_nat_degree {p q : polynomial R} (hp : p ≠ 0) (hpq : p.degree < q.degree) :
  p.nat_degree < q.nat_degree :=
begin
  by_cases hq : q = 0, { rw [hq, degree_zero] at hpq, have := not_lt_bot hpq, contradiction },
  rwa [degree_eq_nat_degree hp, degree_eq_nat_degree hq, with_bot.coe_lt_coe] at hpq
end

lemma mem_span_power_basis (alg : is_algebraic K L)
  (hx : is_integral K (adjoin_simple.gen K x)) (y : K⟮x⟯) :
  y ∈ submodule.span K (set.range (λ (i : fin (minimal_polynomial hx).nat_degree),
    adjoin_simple.gen K x ^ (i : ℕ))) :=
begin
  obtain ⟨y, hy⟩ := y,
  have mp_monic := minimal_polynomial.monic hx,
  have mp_ne_zero := minimal_polynomial.ne_zero hx,

  obtain ⟨f, rfl⟩ := exists_eq_aeval_gen alg hy,

  have : aeval x f = algebra_map K⟮x⟯ L
    (eval₂ (algebra_map K K⟮x⟯) (adjoin_simple.gen K x) f),
  { rw [aeval_def, hom_eval₂, ← is_scalar_tower.algebra_map_eq, adjoin_simple.algebra_map_gen] },

  rw [mem_span_set_submodule K⟮x⟯.to_subalgebra.to_submodule, subtype.coe_mk, this,
      ← eval₂_mod_by_monic_eq_self_of_root mp_monic (minimal_polynomial.aeval _),
      eval₂_eq_sum_range],

  change K⟮x⟯.to_subalgebra.to_submodule.subtype
    (∑ (a : ℕ) in _,
      (algebra_map K ↥K⟮x⟯) ((f %ₘ minimal_polynomial hx).coeff a) * (adjoin_simple.gen K x ^ a) : K⟮x⟯) ∈
    submodule.span K (K⟮x⟯.to_subalgebra.to_submodule.subtype ''
      set.range (λ (i : fin (minimal_polynomial hx).nat_degree), adjoin_simple.gen K x ^ ↑i)),
  rw [← submodule.map_span, submodule.mem_map],
  refine ⟨_, _, rfl⟩,
  refine submodule.sum_mem _ (λ i i_mem, _),
  rw finset.mem_range at i_mem,
  rw ← algebra.smul_def,
  refine submodule.smul_mem _ _ (submodule.subset_span ⟨⟨i, _⟩, rfl⟩),
  by_cases hf : f %ₘ minimal_polynomial hx = 0,
  { rw [hf, nat_degree_zero, nat.lt_succ_iff, nat.le_zero_iff] at i_mem,
    rw i_mem,
    rw nat_degree_pos_iff_degree_pos,
    apply minimal_polynomial.degree_pos },
  calc i < (f %ₘ minimal_polynomial hx).nat_degree + 1 : i_mem
  ... ≤ (minimal_polynomial hx).nat_degree : _,
  rw nat.succ_le_iff,
  exact nat_degree_lt_nat_degree hf (degree_mod_by_monic_lt _ mp_monic mp_ne_zero),
end

example : ring K⟮x⟯ := infer_instance
example : algebra K K⟮x⟯ := infer_instance

noncomputable def has_power_basis_adjoin_simple
  (K) [field K] [algebra K L] (alg : is_algebraic K L) (x : L) :
  has_power_basis K K⟮x⟯ :=
let hx : is_integral K (adjoin_simple.gen K x) :=
    (is_algebraic_iff_is_integral _).mp (K⟮x⟯.is_algebraic (alg x)) in
{ dim := (minimal_polynomial hx).nat_degree,
  gen := adjoin_simple.gen K x,
  is_basis := ⟨linear_independent_power_basis _,
               _root_.eq_top_iff.mpr (λ y _, mem_span_power_basis alg _ _)⟩ }

@[simp] lemma gen_adjoin_simple (alg : is_algebraic K L) :
  (has_power_basis_adjoin_simple _ alg x).gen = adjoin_simple.gen K x :=
rfl

lemma findim_eq_dim (h : has_power_basis K L) :
  findim K L = h.dim :=
trans (findim_eq_card_basis h.is_basis) (fintype.card_fin _)

lemma monic_add_of_left {p q : polynomial R} (hp : monic p) (hpq : degree q < degree p) :
  monic (p + q) :=
by rwa [monic, add_comm, leading_coeff_add_of_degree_lt hpq]

lemma monic_add_of_right {p q : polynomial R} (hq : monic q) (hpq : degree p < degree q) :
  monic (p + q) :=
by rwa [monic, leading_coeff_add_of_degree_lt hpq]

lemma degree_sum {s : finset ι} (p : ι → polynomial R) :
  degree (s.sum p) ≤ s.fold (⊔) ⊥ (λ i, degree (p i)) :=
begin
  classical,
  refine s.induction_on _ _,
  { simp },
  intros a s ha ih,
  calc ((insert a s).sum p).degree
      = (p a + s.sum p).degree : by rw finset.sum_insert ha
  ... ≤ max (p a).degree (s.sum p).degree : degree_add_le _ _
  ... ≤ max (p a).degree (s.fold (⊔) ⊥ (λ i, degree (p i))) : max_le_max (refl _) ih
  ... = (insert a s).fold (⊔) ⊥ (λ i, degree (p i)) :
    by rw [finset.fold_insert ha, with_bot.sup_eq_max]
end

/-- `h.minpoly_gen` is a minimal polynomial for `h.gen`.

If `A` is not a field, it might not necessarily be *the* minimal polynomial,
however `minpoly_gen_nat_degree_le` shows its degree is indeed minimal.
-/
noncomputable def minpoly_gen (h : has_power_basis A S) : polynomial A :=
X ^ h.dim -
  ∑ (i : fin h.dim), C (h.is_basis.repr (h.gen ^ h.dim) i) * X ^ (i : ℕ)

lemma degree_sum_fin_lt {n : ℕ} (f : fin n → R) :
  degree (∑ i : fin n, C (f i) * X ^ (i : ℕ)) < n :=
begin
  haveI : is_commutative (with_bot ℕ) max := ⟨max_comm⟩,
  haveI : is_associative (with_bot ℕ) max := ⟨max_assoc⟩,
  calc  (∑ i, C (f i) * X ^ (i : ℕ)).degree
      ≤ finset.univ.fold (⊔) ⊥ (λ i, (C (f i) * X ^ (i : ℕ)).degree) : degree_sum _
  ... = finset.univ.fold max ⊥ (λ i, (C (f i) * X ^ (i : ℕ)).degree) :
    (@finset.fold_hom _ _ _ (⊔) _ _ _ ⊥ finset.univ _ _ _ id (with_bot.sup_eq_max)).symm
  ... < n : (finset.fold_max_lt (n : with_bot ℕ)).mpr ⟨with_bot.bot_lt_some _, _⟩,
  rintros ⟨i, hi⟩ -,
  calc (C (f ⟨i, hi⟩) * X ^ i).degree
      ≤ (C _).degree + (X ^ i).degree : degree_mul_le _ _
  ... ≤ 0 + i : add_le_add degree_C_le (degree_X_pow_le i)
  ... = i : zero_add _
  ... < n : with_bot.some_lt_some.mpr hi,
end

@[simp] lemma nat_degree_minpoly_gen (h : has_power_basis A S) :
  nat_degree (minpoly_gen h) = h.dim :=
begin
  rw [minpoly_gen, sub_eq_add_neg],
  apply nat_degree_eq_of_degree_eq_some,
  -- TODO: find a good lemma to encapsulate the next three lines
  rw [add_comm, ← @degree_X_pow A _ _ h.dim],
  apply degree_add_eq_of_degree_lt,
  rw [degree_neg, @degree_X_pow A _ _ h.dim],
  exact degree_sum_fin_lt _
end

lemma minpoly_gen_monic (h : has_power_basis A S) : monic (minpoly_gen h) :=
begin
  apply monic_add_of_left (monic_pow (monic_X) _),
  rw [degree_neg, degree_X_pow],
  exact degree_sum_fin_lt _
end

lemma aeval_minpoly_gen (h : has_power_basis A S) : aeval h.gen (minpoly_gen h) = 0 :=
begin
  simp_rw [minpoly_gen, alg_hom.map_sub, alg_hom.map_sum, alg_hom.map_mul, alg_hom.map_pow,
           aeval_C, ← smul_def, aeval_X],
  refine sub_eq_zero.mpr ((h.is_basis.total_repr (h.gen ^ h.dim)).symm.trans _),
  rw [finsupp.total_apply, finsupp.sum_fintype],
  intro i, rw zero_smul
end

lemma gen_is_integral (h : has_power_basis A S) : is_integral A h.gen :=
⟨minpoly_gen h, minpoly_gen_monic h, aeval_minpoly_gen h⟩

lemma eval₂_eq_sum_range' (f : R →+* S) {p : polynomial R} {n : ℕ} (hn : p.nat_degree < n) (x : S) :
  eval₂ f x p = ∑ i in finset.range n, f (p.coeff i) * x ^ i :=
begin
  rw [eval₂_eq_sum, p.sum_over_range' _ _ hn],
  intro i,
  rw [f.map_zero, zero_mul]
end

lemma aeval_eq_sum_range' {p : polynomial R} {n : ℕ} (hn : p.nat_degree < n) (x : S) :
  aeval x p = ∑ i in finset.range n, p.coeff i • x ^ i :=
by { simp_rw smul_def, exact eval₂_eq_sum_range' (algebra_map R S) hn x }

lemma dim_le_nat_degree_of_root (h : has_power_basis A S) {p : polynomial A}
  (ne_zero : p ≠ 0) (root : aeval h.gen p = 0) :
  h.dim ≤ p.nat_degree :=
begin
  refine le_of_not_lt (λ hlt, ne_zero _),
  let p_coeff : fin (h.dim) → A := λ i, p.coeff i,
  suffices : ∀ i, p_coeff i = 0,
  { ext i,
    by_cases hi : i < h.dim,
    { exact this ⟨i, hi⟩ },
    exact coeff_eq_zero_of_nat_degree_lt (lt_of_lt_of_le hlt (le_of_not_gt hi)) },
  intro i,
  refine linear_independent_iff'.mp h.is_basis.1 finset.univ _ _ i (finset.mem_univ _),
  rw aeval_eq_sum_range' hlt at root,
  rw finset.sum_fin_eq_sum_range,
  convert root,
  ext i,
  split_ifs with hi,
  { refl },
  { rw [coeff_eq_zero_of_nat_degree_lt (lt_of_lt_of_le hlt (le_of_not_gt hi)),
        zero_smul] }
end

lemma nat_degree_minimal_polynomial (h : has_power_basis K L) :
  h.dim = (minimal_polynomial (gen_is_integral h)).nat_degree :=
begin
  refine le_antisymm
    (dim_le_nat_degree_of_root h (minimal_polynomial.ne_zero _) (minimal_polynomial.aeval _))
    _,
  rw ← nat_degree_minpoly_gen,
  apply nat_degree_le_of_degree_le,
  rw ← degree_eq_nat_degree (minpoly_gen_monic h).ne_zero,
  exact minimal_polynomial.min _ (minpoly_gen_monic h) (aeval_minpoly_gen h)
end

end power_basis

namespace algebra

variables (R S)

/-- The trace of an element `s` of an `R`-algebra is the trace of `(*) s`,
as an `R`-linear map. -/
noncomputable def trace : S →ₗ[R] R := (linear_map.trace R S).comp (lmul R S)

variables {S}

@[simp] lemma trace_apply (s : S) : trace R S s = linear_map.trace R S (lmul R S s) := rfl

lemma trace_eq_zero_of_not_exists_basis
  (h : ¬ ∃ s : finset S, is_basis R (λ x, x : (↑s : set S) → S)) : trace R S = 0 :=
by { ext s, simp [linear_map.trace, h] }

lemma findim_eq_zero_of_not_exists_basis
  (h : ¬ ∃ s : finset L, is_basis K (λ x, x : (↑s : set L) → L)) : findim K L = 0 :=
dif_neg (mt (λ h, @exists_is_basis_finset K L _ _ _ (finite_dimensional_iff_dim_lt_omega.mpr h)) h)

theorem smul_id (r : R) : r • linear_map.id = lsmul R S r := rfl

@[simp] lemma lmul_algebra_map (x : R) : lmul R S (algebra_map R S x) = lsmul R S x :=
linear_map.ext (λ s, by simp [smul_def''])

@[simp] lemma to_matrix_lmul [decidable_eq ι] (x : S) (i j) :
  linear_map.to_matrix hb hb (lmul R S x) i j = hb.repr (x * b j) i :=
by rw [linear_map.to_matrix_apply', lmul_apply]

include hb
/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
lemma trace_algebra_map_of_basis (x : R) :
  trace R S (algebra_map R S x) = fintype.card ι • x :=
begin
  rw [trace_apply, trace_eq_matrix_trace R hb, trace_diag],
  convert finset.sum_const _,
  ext i,
  simp [←smul_id]
end
omit hb

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
@[simp]
lemma trace_algebra_map (x : K) : trace K L (algebra_map K L x) = findim K L • x :=
begin
  by_cases H : ∃ s : finset L, is_basis K (λ x, x : (↑s : set L) → L),
  { rw [trace_algebra_map_of_basis K H.some_spec, findim_eq_card_basis H.some_spec] },
  { simp [trace_eq_zero_of_not_exists_basis K H, findim_eq_zero_of_not_exists_basis H] },
end

lemma linear_equiv.map_sum {R : Type u} {M : Type v} {M₂ : Type w}
  [semiring R] [add_comm_monoid M]
  [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂]
  (f : M ≃ₗ[R] M₂) {ι : Type u_1} {t : finset ι} {g : ι → M} :
  f (t.sum (λ (i : ι), g i)) = t.sum (λ (i : ι), f (g i)) :=
f.to_linear_map.map_sum

section trace_form

variables (S)

/-- The `trace_form` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separable. -/
noncomputable def trace_form : bilin_form R S :=
{ bilin := λ x y, trace R S (x * y),
  bilin_add_left := λ x y z, by rw [add_mul, linear_map.map_add],
  bilin_smul_left := λ x y z, by rw [smul_mul_assoc, linear_map.map_smul, smul_eq_mul],
  bilin_add_right := λ x y z, by rw [mul_add, linear_map.map_add],
  bilin_smul_right := λ x y z, by rw [mul_smul_comm, linear_map.map_smul, smul_eq_mul], }

variables {S}

@[simp] lemma trace_form_apply (x y : S) : trace_form R S x y = trace R S (x * y) := rfl

lemma trace_form_is_sym : sym_bilin_form.is_sym (trace_form R S) :=
λ x y, congr_arg (trace R S) (mul_comm _ _)

lemma trace_form_to_matrix [decidable_eq ι] (i j) :
  bilin_form_equiv_matrix hb (trace_form R S) i j = trace R S (b i * b j) :=
by rw [bilin_form_equiv_matrix_apply, trace_form_apply]

open bilin_form

lemma lmul_mul (x y : S) : lmul R S (x * y) = (lmul R S x).comp (lmul R S y) :=
by { ext z, simp [mul_assoc] }

lemma lmul_one : lmul R S 1 = linear_map.id :=
by { ext z, rw [lmul_apply, one_mul, linear_map.id_apply] }

lemma matrix.trace_apply (A : matrix ι ι S) : matrix.trace ι R S A = ∑ i, A i i := rfl

end trace_form

end algebra

open intermediate_field.adjoin_simple
open algebra

variables [decidable_eq ι] [algebra S T] [is_scalar_tower R S T]

lemma to_matrix_lsmul (x : R) :
  linear_map.to_matrix hb hb (lsmul R S x) = algebra_map _ _ x :=
by { ext i j, simp [linear_map.to_matrix_apply, algebra_map_matrix_apply, eq_comm] }

noncomputable def lmul_matrix : S →ₐ[R] matrix ι ι R :=
{ to_fun := λ x, linear_map.to_matrix hb hb (lmul R S x),
  map_zero' := by rw [linear_map.map_zero, linear_equiv.map_zero],
  map_one' := by rw [lmul_one, linear_map.to_matrix_id],
  map_add' := λ x y, by rw [linear_map.map_add, linear_equiv.map_add],
  map_mul' := λ x y, by rw [lmul_mul, linear_map.to_matrix_comp hb hb, matrix.mul_eq_mul],
  commutes' := λ r, by rw [lmul_algebra_map, to_matrix_lsmul] }

lemma lmul_matrix_apply (x : S) (i j) :
  lmul_matrix hb x i j = linear_map.to_matrix hb hb (lmul R S x) i j := rfl

section

open polynomial

lemma ring_hom.map_matrix.map_mul {n : Type*} [fintype n] [decidable_eq n]
  (M N : matrix n n R) (f : R →+* S) :
  f.map_matrix (M ⬝ N) = f.map_matrix M ⬝ f.map_matrix N :=
by rw [← mul_eq_mul, ring_hom.map_mul, mul_eq_mul]

@[simp] lemma perm_congr_apply {m n : Type*} [fintype m] [decidable_eq m]
  [fintype n] [decidable_eq n] (e : m ≃ n) (p : equiv.perm m) (x) :
  e.perm_congr p x = e (p (e.symm x)) := rfl

@[simp] lemma sign_perm_congr {m n : Type*} [fintype m] [decidable_eq m]
  [fintype n] [decidable_eq n] (e : m ≃ n) (p : equiv.perm m) :
  (e.perm_congr p).sign = p.sign :=
equiv.perm.sign_eq_sign_of_equiv _ _ e.symm (by simp)

lemma det_reindex {m n : Type*} [fintype m] [decidable_eq m]
  [fintype n] [decidable_eq n] (e : m ≃ n) (A : matrix m m R) :
  det (reindex_linear_equiv e e A) = det A :=
begin
  simp only [det, reindex_linear_equiv_apply],
  apply finset.sum_bij' (λ σ _, equiv.perm_congr e.symm σ) _ _ (λ σ _, equiv.perm_congr e σ),
  { intros σ _, ext, simp only [equiv.symm_symm, perm_congr_apply, equiv.apply_symm_apply] },
  { intros σ _, ext, simp only [equiv.symm_symm, perm_congr_apply, equiv.symm_apply_apply] },
  { intros σ _, apply finset.mem_univ },
  { intros σ _, apply finset.mem_univ },

  intros σ _,
  simp_rw [sign_perm_congr, perm_congr_apply, equiv.symm_symm],
  congr,
  apply finset.prod_bij' (λ i _, e.symm i) _ _ (λ i _, e i),
  { intros, simp_rw equiv.apply_symm_apply },
  { intros, simp_rw equiv.symm_apply_apply },
  { intros, apply finset.mem_univ },
  { intros, apply finset.mem_univ },
  { intros, simp_rw equiv.apply_symm_apply },
end

@[simp] lemma reindex_refl_refl {m n : Type*} [fintype m] [decidable_eq m]
  [fintype n] [decidable_eq n] (A : matrix m n R) :
  (reindex_linear_equiv (equiv.refl _) (equiv.refl _) A) = A :=
by { ext, simp only [reindex_linear_equiv_apply, equiv.refl_symm, equiv.refl_apply] }

lemma matrix.card_le_card_of_left_inv' {m n : ℕ}
  {M : matrix (fin m) (fin n) A} {M' : matrix (fin n) (fin m) A}
  (hMM' : M ⬝ M' = 1) :
  m ≤ n :=
have function.left_inverse
  ((M.map (algebra_map A (fraction_ring A))).mul_vec)
  ((M'.map (algebra_map A (fraction_ring A))).mul_vec) :=
λ x, by rw [mul_vec_mul_vec, ← matrix.map_mul, hMM', matrix.map_one, mul_vec_one],
have function.injective ((M'.map (algebra_map A (fraction_ring A))).to_lin') :=
function.left_inverse.injective this,
calc m = findim (fraction_ring A) (fin m → fraction_ring A) : (findim_fin_fun _).symm
   ... ≤ findim (fraction_ring A) (fin n → fraction_ring A) : findim_le_findim_of_injective this
   ... = n : findim_fin_fun _

lemma matrix.card_le_card_of_left_inv {m n : Type*}
  [fintype m] [decidable_eq m] [fintype n] [decidable_eq n]
  {M : matrix m n A} {M' : matrix n m A} (hMM' : M ⬝ M' = 1) :
  fintype.card m ≤ fintype.card n :=
let em := trunc.out (fintype.equiv_fin m), en := trunc.out (fintype.equiv_fin n) in
matrix.card_le_card_of_left_inv' $
calc reindex_linear_equiv em en M ⬝ reindex_linear_equiv en em M'
    = reindex_linear_equiv em em (M ⬝ M') : reindex_mul em en em M M'
... = reindex_linear_equiv em em 1 : by rw hMM'
... = 1 : (reindex_alg_equiv em).map_one

noncomputable def matrix.equiv_of_inv {m n : Type*}
  [fintype m] [decidable_eq m] [fintype n] [decidable_eq n]
   {M : matrix m n A} {M' : matrix n m A}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  m ≃ n :=
classical.choice (fintype.card_eq.mp (le_antisymm
  (matrix.card_le_card_of_left_inv hMM')
  (matrix.card_le_card_of_left_inv hM'M)))

/-- If `A'` is a two-sided inverse for `A` (indexed differently), `det (A ⬝ B ⬝ A') = det B`. -/
lemma det_conjugate_aux {m n : Type*} [fintype m] [decidable_eq m]
  [fintype n] [decidable_eq n] {M : matrix m n A} {M' : matrix n m A} {N : matrix n n A}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  det (M ⬝ N ⬝ M') = det N :=
begin
  -- Although `m` and `n` are different a priori, we will show they have the same cardinality.
  -- This turns the problem into one for square matrices, which is easy.
  let e : m ≃ n := matrix.equiv_of_inv hMM' hM'M,
  have : det (reindex_linear_equiv e (equiv.refl _) M ⬝ N ⬝ reindex_linear_equiv (equiv.refl _) e M') = det N,
  { rw [det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, reindex_mul, reindex_refl_refl, hM'M, det_one, one_mul] },
  convert this,
  rw [← det_reindex e (M ⬝ N ⬝ M'), ← reindex_mul e (equiv.refl n) e, ← reindex_mul e (equiv.refl n) (equiv.refl n), reindex_refl_refl],
end

/-- If `A'` is a two-sided inverse for `A`, `char_poly (A ⬝ B ⬝ A') = char_poly B`. -/
lemma char_poly_conjugate_aux {m n : Type*} [fintype m] [decidable_eq m]
  [fintype n] [decidable_eq n] {M : matrix m n A} {M' : matrix n m A} {N : matrix n n A}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  char_poly (M ⬝ N ⬝ M') = char_poly N :=
have hCACA' : M.map C ⬝ M'.map C = 1 := by rw [← matrix.map_mul, hMM', matrix.map_one],
have hCA'CA : M'.map C ⬝ M.map C = 1 := by rw [← matrix.map_mul, hM'M, matrix.map_one],
calc (X • 1 - C.map_matrix (M ⬝ N ⬝ M')).det
    = (M.map C ⬝ (scalar n X - N.map C) ⬝ M'.map C).det :
    by rw [matrix.mul_sub, matrix.sub_mul, ring_hom.map_matrix_apply, matrix.map_mul,
           matrix.map_mul, coe_scalar, matrix.mul_smul, matrix.mul_one,
           matrix.smul_mul, hCACA']
... = (X • 1 - C.map_matrix N).det : det_conjugate_aux hCACA' hCA'CA

lemma char_poly_conjugate {n : Type*} [fintype n] [decidable_eq n] {M B : matrix n n A}
  (hM : is_unit M.det) :
  char_poly (M⁻¹ ⬝ B ⬝ M) = char_poly B :=
char_poly_conjugate_aux (nonsing_inv_mul _ hM) (mul_nonsing_inv _ hM)

end

variables {M M' : Type*} [add_comm_group M] [module R M] [add_comm_group M'] [module R M']

lemma to_matrix_basis_change {ι' κ κ' : Type*} [fintype ι'] [decidable_eq ι']
  [fintype κ] [decidable_eq κ] [fintype κ'] [decidable_eq κ']
  {b : ι → M} {b' : ι' → M} (hb : is_basis R b) (hb' : is_basis R b')
  {c : κ → M'} {c' : κ' → M'} (hc : is_basis R c) (hc' : is_basis R c')
  (f : M →ₗ[R] M'):
  to_matrix hb hc f = hc.to_matrix c' ⬝ to_matrix hb' hc' f ⬝ hb'.to_matrix b :=
begin
  ext j i,
  calc to_matrix hb hc f j i = hc.repr (f (b i)) j :
       by rw [linear_map.to_matrix_apply, is_basis.equiv_fun_apply]
  ... = ∑ i', (∑ j', hc.repr (c' j') j * hc'.repr (f (b' i')) j') * hb'.repr (b i) i' :
       _
  ... = (hc.to_matrix c' ⬝ to_matrix hb' hc' f ⬝ hb'.to_matrix b) j i :
      by simp only [matrix.mul_apply, is_basis.to_matrix_apply, linear_map.to_matrix_apply,
                    is_basis.equiv_fun_apply],
  conv_lhs { rw ← hb'.total_repr (b i) },
  rw [finsupp.total_apply, f.finsupp_sum, hc.repr.finsupp_sum, finsupp.sum_apply,
      finsupp.sum_fintype, finset.sum_congr rfl],
  { rintros i' -,
    rw [linear_map.map_smul, linear_map.map_smul, finsupp.smul_apply, smul_eq_mul, mul_comm],
    congr,
    conv_lhs { rw ← hc'.total_repr (f (b' i')) },
    rw [finsupp.total_apply, hc.repr.finsupp_sum, finsupp.sum_apply, finsupp.sum_fintype,
        finset.sum_congr rfl],
    { rintros j' -,
      simp [mul_comm] },
    { simp } },
  { simp }
end

@[simp] lemma to_matrix_id' {ι' : Type*} [fintype ι'] [decidable_eq ι']
  {b : ι → M} {b' : ι' → M} (hb : is_basis R b) (hb' : is_basis R b') :
  to_matrix hb hb' id = hb'.to_matrix b :=
by rw [to_matrix_basis_change hb hb' hb' hb', to_matrix_id, matrix.mul_one, hb'.to_matrix_self, matrix.one_mul]

@[simp] lemma is_basis.to_matrix_mul_to_matrix {ι' ι'' : Type*}
  [fintype ι'] [decidable_eq ι'] [fintype ι''] [decidable_eq ι'']
  {b' : ι' → S} (hb' : is_basis R b') {b'' : ι'' → S} (hb'' : is_basis R b'') :
  hb.to_matrix b' ⬝ hb'.to_matrix b'' = hb.to_matrix b'' :=
begin
  apply (matrix.to_lin hb'' hb).injective,
  calc to_lin hb'' hb (hb.to_matrix b' ⬝ hb'.to_matrix b'')
      = to_lin hb'' hb (hb.to_matrix b' ⬝ to_matrix hb' hb' id ⬝ hb'.to_matrix b'') : by simp
  ... = to_lin hb'' hb (hb.to_matrix b'') : by rw [← to_matrix_basis_change hb'' hb' hb hb', to_matrix_id']
end

lemma char_poly_lmul_matrix_basis_invariant {ι' : Type*} [fintype ι'] [decidable_eq ι']
  (hb : is_basis A b) {b' : ι' → S} (hb' : is_basis A b') (x : S) :
  char_poly (lmul_matrix hb x) = char_poly (lmul_matrix hb' x) :=
begin
  change char_poly (to_matrix hb hb (lmul A S x)) = char_poly (to_matrix hb' hb' (lmul A S x)),
  rw [to_matrix_basis_change hb hb' hb hb', char_poly_conjugate_aux];
    rw [is_basis.to_matrix_mul_to_matrix, is_basis.to_matrix_self];
    assumption
end

lemma trace_eq_matrix_trace (x : S) :
  algebra.trace R S x = matrix.trace _ R R (lmul_matrix hb x) :=
by { rw [trace_apply, trace_eq_matrix_trace _ hb], congr }

section

def linear_map.restrict_base (R : Type*) {S M M' : Type*} [comm_semiring R] [semiring S] [algebra R S]
  [add_comm_monoid M] [semimodule R M] [semimodule S M] [is_scalar_tower R S M]
  [add_comm_monoid M'] [semimodule R M'] [semimodule S M'] [is_scalar_tower R S M']
  (l : M →ₗ[S] M') : M →ₗ[R] M' :=
{ map_smul' := λ c x,
    show l (c • x) = c • l x,
    by rw [← is_scalar_tower.algebra_map_smul S c x, l.map_smul, is_scalar_tower.algebra_map_smul],
  .. (l.to_add_monoid_hom) }

@[simp] lemma linear_map.restrict_base_apply
  (R : Type*) {S M M' : Type*} [comm_semiring R] [semiring S] [algebra R S]
  [add_comm_monoid M] [semimodule R M] [semimodule S M] [is_scalar_tower R S M]
  [add_comm_monoid M'] [semimodule R M'] [semimodule S M'] [is_scalar_tower R S M']
  (l : M →ₗ[S] M') (x : M) : l.restrict_base R x = l x := rfl

instance is_scalar_tower.finsupp {α : Type*} : is_scalar_tower R S (α →₀ S) :=
⟨λ r s t, finsupp.ext (λ x, show ((r • s) • t x) = (r • s • t x), by { rw [smul_assoc] })⟩

lemma lmul_matrix_smul {κ : Type*} [fintype κ] [decidable_eq κ] [algebra S T] [is_scalar_tower R S T]
  {b : ι → S} (hb : is_basis R b) {c : κ → T} (hc : is_basis S c) (x) (i j) (k k') :
  lmul_matrix (hb.smul hc) x (i, k) (j, k') = lmul_matrix hb (lmul_matrix hc x k k') i j :=
by simp only [lmul_matrix_apply, linear_map.to_matrix_apply, is_basis.equiv_fun_apply, mul_comm,
              is_basis.smul_repr, finsupp.smul_apply, lmul_apply, id.smul_eq_mul,
              map_smul_eq_smul_map, mul_smul_comm]

lemma lmul_matrix_smul_algebra_map {κ : Type*} [fintype κ] [decidable_eq κ]
  {b : ι → S} (hb : is_basis R b) {c : κ → T} (hc : is_basis S c) (x : S) :
  lmul_matrix (hb.smul hc) (algebra_map _ _ x) = block_diagonal (λ k, lmul_matrix hb x) :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  rw [lmul_matrix_smul, alg_hom.commutes, block_diagonal_apply, algebra_map_matrix_apply],
  split_ifs with h; simp [h],
end

lemma lmul_matrix_smul_algebra_map_eq {κ : Type*} [fintype κ] [decidable_eq κ]
  {b : ι → S} (hb : is_basis R b) {c : κ → T} (hc : is_basis S c) (x : S) (i j k) :
  lmul_matrix (hb.smul hc) (algebra_map _ _ x) (i, k) (j, k) = lmul_matrix hb x i j :=
by rw [lmul_matrix_smul_algebra_map, block_diagonal_apply_eq]

lemma lmul_matrix_smul_algebra_map_ne {κ : Type*} [fintype κ] [decidable_eq κ]
  {b : ι → S} (hb : is_basis R b) {c : κ → T} (hc : is_basis S c) (x : S) (i j) {k k'}
  (h : k ≠ k') : lmul_matrix (hb.smul hc) (algebra_map _ _ x) (i, k) (j, k') = 0 :=
by rw [lmul_matrix_smul_algebra_map, block_diagonal_apply_ne _ _ _ h]

end

lemma trace_comp_of_basis [algebra S T] [is_scalar_tower R S T]
  {ι κ : Type*} [fintype ι] [fintype κ] [decidable_eq ι] [decidable_eq κ] {b : ι → S} {c : κ → T}
  (hb : is_basis R b) (hc : is_basis S c) (x : T) :
  algebra.trace R T x = trace R S (trace S T x) :=
begin
  rw [trace_eq_matrix_trace (hb.smul hc), trace_eq_matrix_trace hb, trace_eq_matrix_trace hc,
      matrix.trace_apply, matrix.trace_apply, matrix.trace_apply,
      ← finset.univ_product_univ, finset.sum_product],
  refine finset.sum_congr rfl (λ i _, _),
  rw [alg_hom.map_sum, finset.sum_apply, finset.sum_apply],
      refine finset.sum_congr rfl (λ j _, _),
  apply lmul_matrix_smul
end

lemma aeval_lmul_matrix (p : polynomial R) (x : S) :
  polynomial.aeval (lmul_matrix hb x) p = lmul_matrix hb (polynomial.aeval x p) :=
p.aeval_alg_hom_apply (lmul_matrix hb) x

lemma lmul_injective : function.injective (lmul R S) :=
λ x x' h, calc x = lmul R S x 1 : by rw [lmul_apply, mul_one]
             ... = lmul R S x' 1 : by rw h
             ... = x' : by rw [lmul_apply, mul_one]

lemma linear_map.injective_iff {V V' : Type*} [add_comm_group V] [add_comm_monoid V']
  [semimodule R V] [semimodule R V']
  (f : V →ₗ[R] V') : function.injective f ↔ ∀ x, f x = 0 → x = 0 :=
f.to_add_monoid_hom.injective_iff

lemma lmul_matrix_injective : function.injective (lmul_matrix hb) :=
λ x x' h, lmul_injective ((linear_map.to_matrix hb hb).injective h)

lemma char_poly_lmul_matrix_power_basis [algebra K S] (h : has_power_basis K S) :
  char_poly (lmul_matrix h.is_basis h.gen) = minimal_polynomial (gen_is_integral h) :=
begin
  apply minimal_polynomial.unique,
  { apply char_poly_monic },
  { have := lmul_matrix_injective h.is_basis,
    apply (lmul_matrix _).injective_iff.mp this,
    rw [← aeval_lmul_matrix, aeval_self_char_poly] },
  { intros q q_monic root_q,
    rw [char_poly_degree_eq_dim, fintype.card_fin,
        polynomial.degree_eq_nat_degree q_monic.ne_zero],
    apply with_bot.some_le_some.mpr,
    exact dim_le_nat_degree_of_root h q_monic.ne_zero root_q }
end

example {α : Type*} {a b c : set α} : c ∩ (a ∩ b) = a ∩ (b ∩ c) := by finish


lemma char_matrix_lmul_matrix_smul {κ : Type*} [fintype κ] [decidable_eq κ]
  {b : ι → S} (hb : is_basis R b) {c : κ → T} (hc : is_basis S c) (x : S) :
  char_matrix (lmul_matrix (hb.smul hc) (algebra_map _ _ x)) =
    block_diagonal (λ _, char_matrix (lmul_matrix hb x)) :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  rw block_diagonal_apply,
  split_ifs with hk,
  { rw (show k = k', from hk),
    by_cases hij : i = j,
    { rw [hij, char_matrix_apply_eq, char_matrix_apply_eq, lmul_matrix_smul_algebra_map_eq] },
    { have : (i, k') ≠ (j, k') := mt prod.fst_eq_iff.mpr hij,
      rw [char_matrix_apply_ne _ this, char_matrix_apply_ne _ hij,
          lmul_matrix_smul_algebra_map_eq] } },
  { have : (i, k) ≠ (j, k') := mt prod.mk.inj_iff.mp (not_and.mpr (λ _, hk)),
    rw [char_matrix_apply_ne _ this, lmul_matrix_smul_algebra_map_ne hb hc _ _ _ hk,
        polynomial.C.map_zero, neg_zero] },
end

lemma char_poly_lmul_matrix_smul [algebra K R] [algebra L R] [is_scalar_tower K L R]
  (h : has_power_basis K L) {c : ι → R} (hc : is_basis L c) :
  char_poly (lmul_matrix (h.is_basis.smul hc) (algebra_map L R h.gen)) =
    (minimal_polynomial (gen_is_integral h))^(fintype.card ι) :=
begin
  rw [← char_poly_lmul_matrix_power_basis h, char_poly, char_poly,
      char_matrix_lmul_matrix_smul, det_block_diagonal, finset.prod_const, finset.card_univ],
end

instance finite_dimensional.tower_top {V : Type*} [add_comm_group V]
  [vector_space K V] [vector_space L V] [is_scalar_tower K L V]
  [finite_dimensional K V] : finite_dimensional L V := sorry

set_option pp.proofs true

lemma minimal_polynomial.eq_of_algebra_map_eq
  [algebra K T] [algebra L T] [is_scalar_tower K L T] [nontrivial T]
  {x : L} {y : T} (hx : is_integral K x) (hy : is_integral K y)
  (h : y = algebra_map L T x) : minimal_polynomial hx = minimal_polynomial hy :=
minimal_polynomial.unique hy (minimal_polynomial.monic hx)
  (by rw [h, ← is_scalar_tower.algebra_map_aeval, minimal_polynomial.aeval hx, ring_hom.map_zero])
  (λ q q_monic root_q, minimal_polynomial.min _ q_monic
    (is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero_field
      (h ▸ root_q : polynomial.aeval (algebra_map L T x) q = 0)))

lemma char_poly_eq_minimal_polynomial_pow (x : L) [finite_dimensional K L]
  {b : ι → L} (hb : is_basis K b) :
  char_poly (lmul_matrix hb x) =
    (minimal_polynomial ((is_algebraic_iff_is_integral K).mp (is_algebraic_of_finite x)))^(findim K⟮x⟯ L) :=
begin
  obtain ⟨c, hc⟩ := exists_is_basis_finset K⟮x⟯ L,
  haveI : decidable_eq (@coe_sort.{(max (u_6+1) 1) (max 1 (u_6+1))+1} (set.{u_6} L) (@set.has_coe_to_sort.{u_6} L)
  (@coe.{u_6+1 (max (u_6+1) 1)} (finset.{u_6} L) (set.{u_6} L)
  (@lift_base.{u_6+1 (max (u_6+1) 1)} (finset.{u_6} L) (set.{u_6} L) (@finset.has_lift.{u_6} L))
  c)) := λ _ _, classical.prop_decidable _,
  rw findim_eq_card_basis hc,
  let h := has_power_basis_adjoin_simple K is_algebraic_of_finite x,
  rw char_poly_lmul_matrix_basis_invariant hb (h.is_basis.smul hc),
  show char_poly (lmul_matrix (h.is_basis.smul hc) (algebra_map _ L h.gen)) =
    minimal_polynomial _ ^ fintype.card (↑c : set _),
  rw [char_poly_lmul_matrix_smul h hc, minimal_polynomial.eq_of_algebra_map_eq (gen_is_integral h) ((is_algebraic_iff_is_integral K).mp (is_algebraic_of_finite x))],
  exact (algebra_map_gen K x).symm
end

/-
lemma repr_primitive_element_pow_of_lt'
  [is_simple_extension K L] (alg : is_algebraic K L) (n : fin (simple_degree alg)) :
  (power_basis_is_basis alg).repr (primitive_element K L ^ (n : ℕ)) = finsupp.single n 1 :=
is_basis.repr_eq_single (power_basis_is_basis alg)

lemma repr_primitive_element_pow_of_lt
  [is_simple_extension K L] (alg : is_algebraic K L) {n : ℕ} (hn : n < simple_degree alg) (i) :
  (power_basis_is_basis alg).repr (primitive_element K L ^ (n : ℕ)) i = if n = i then 1 else 0 :=
by { rw [← fin.coe_mk hn, (repr_primitive_element_pow_of_lt' _ _ alg ⟨n, hn⟩),
         finsupp.single_apply, fin.ext_iff], congr' 1 }

@[simp] lemma finsupp.finset_sum_apply {α α₁ β : Type*} [add_comm_monoid β]
  {s : finset α₁} {g : α₁ → α →₀ β} {a₂ : α} :
  (s.sum g) a₂ = s.sum (λa₁, g a₁ a₂) :=
(finsupp.eval_add_hom a₂ : (α →₀ β) →+ _).map_sum _ _

variables {K L}

lemma repr_primitive_element_pow_simple_degree
  [is_simple_extension K L] (alg : is_algebraic K L) (i) :
  (power_basis_is_basis alg).repr (primitive_element K L ^ simple_degree alg) i =
    - (minimal_polynomial alg).coeff i :=
begin
  unfold simple_degree,
  have : ∀ {p : polynomial K} (hp : p.monic) (x : L),
    x ^ p.nat_degree = polynomial.aeval x p - ∑ i in finset.range p.nat_degree, p.coeff i • x^i,
  { intros p hp x,
    conv_rhs { congr, { rw hp.as_sum } },
    rw [alg_hom.map_add, alg_hom.map_pow, polynomial.aeval_X, add_sub_assoc, alg_hom.map_sum,
        ← finset.sum_sub_distrib],
    convert (add_zero _).symm,
    refine finset.sum_eq_zero (λ i hi, _),
    rw [alg_hom.map_mul, alg_hom.map_pow, polynomial.aeval_C, polynomial.aeval_X, smul_def, sub_self] },

  erw [this (show (minimal_polynomial alg).monic, from minimal_polynomial.monic _),
      minimal_polynomial.aeval],
  rw [zero_sub, linear_map.map_neg, linear_map.map_sum, finsupp.neg_apply, finsupp.finset_sum_apply,
      ← finset.sum_attach, neg_inj],
  convert finset.sum_ite_eq (finset.range (minimal_polynomial alg).nat_degree) i
    (λ i, (minimal_polynomial alg).coeff i) using 1,
  { conv_rhs { rw ← finset.sum_attach },
    apply finset.sum_congr rfl,
    intros j hj,
    rw [linear_map.map_smul, finsupp.smul_apply, smul_eq_mul],
    erw repr_primitive_element_pow_of_lt _ _ alg (finset.mem_range.mp j.2) i,
    rw mul_boole, simp [eq_comm] },
  { exact (if_pos (finset.mem_range.mpr i.2)).symm }
end

lemma linear_equiv_matrix_lmul_primitive_element_pow_of_lt
  [is_simple_extension K L] (alg : is_algebraic K L) {n : ℕ} (i j : fin _) (hn : n + (j : ℕ) < simple_degree alg) :
  linear_equiv_matrix (power_basis_is_basis alg) (power_basis_is_basis alg)
      (lmul K L (primitive_element K L ^ n)) i j =
    if n + (j : ℕ) = i then 1 else 0 :=
by rw [linear_equiv_matrix_apply', lmul_apply, power_basis_apply, ←pow_add, repr_primitive_element_pow_of_lt K L alg hn]

#check nat.sub_le_iff

lemma linear_equiv_matrix_lmul_primitive_element_pow
  [is_simple_extension K L] (alg : is_algebraic K L) {n : ℕ} (i j : fin _) (hn : n < simple_degree alg) :
  linear_equiv_matrix (power_basis_is_basis alg) (power_basis_is_basis alg)
      (lmul K L (primitive_element K L ^ n)) i j =
    if n + (j : ℕ) < simple_degree alg
    then if n + (j : ℕ) = i then 1 else 0
    else sorry :=
begin
  split_ifs with hj hi,
  { rw [linear_equiv_matrix_apply', lmul_apply, power_basis_apply, ←pow_add, repr_primitive_element_pow_of_lt K L alg hj, if_pos hi] },
  { rw [linear_equiv_matrix_apply', lmul_apply, power_basis_apply, ←pow_add, repr_primitive_element_pow_of_lt K L alg hj, if_neg hi] },
  replace hj := nat.sub_le_right_iff_le_add.mpr (le_of_not_gt hj),
  obtain ⟨n', rfl⟩ := nat.exists_eq_add_of_le hj,
  rw [pow_add, lmul_mul, linear_equiv_matrix_comp _ (power_basis_is_basis alg), matrix.mul_apply],
  simp_rw linear_equiv_matrix_lmul_primitive_element_pow_of_lt,
  sorry
end
-/

lemma sum_repr (x : S) : ∑ i, hb.repr x i • b i = x :=
begin
  convert hb.total_repr x using 1,
  rw finsupp.total_apply,
  refine (finset.sum_subset (finset.subset_univ _) (λ i _ hi, _)).symm,
  rw [finsupp.not_mem_support_iff.mp hi, zero_smul]
end

lemma lmul_one : lmul R S 1 = linear_map.id :=
by { ext, simp }

lemma trace_form.nondegenerate [finite_dimensional K L] [is_separable K L] :
  (trace_form K L).nondegenerate :=
begin
  rw bilin_form.nondegenerate_iff_eq_zero,
  intros x hxy,
  have alg : is_algebraic K L := is_algebraic_of_finite,
  have hb := power_basis_is_basis alg,
  haveI := classical.prop_decidable,
  by_contra hx,
  have trace_eq_zero : ∀ (z : L), trace K L z = 0,
  { intro z,
    convert hxy (x⁻¹ * z),
    rw [←mul_assoc, mul_inv_cancel hx, one_mul] },
  have trace_primitive_element : ∀ i < simple_degree alg,
    trace K L (primitive_element K L ^ (i : ℕ)) = (minimal_polynomial alg).coeff (simple_degree alg - i),
  { intro i,
    induction i with i ih,
    { sorry },
    { intro hi,
      rw pow_succ } },

/-
  use x⁻¹ * is_simple_extension.primitive_element K L,
  rw [trace_form_apply, ← mul_assoc, mul_inv_cancel hxy, one_mul, trace_apply,
      linear_map.trace_eq_matrix_trace K hb, matrix.trace_apply],
  simp_rw [linear_equiv_matrix_apply' hb hb],
  -/
end

end trace_form

end algebra

#lint
