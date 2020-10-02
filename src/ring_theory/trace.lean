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
  refine field.adjoin_induction _ hy _ _ _ _ _ _,
  { intros x hx,
    rcases set.mem_insert_iff.mp hx with rfl | ⟨_, ⟨⟩⟩,
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

/-- Bundle `power_basis` in a structure to generalize over `algebra.adjoin` and `field.adjoin`. -/
structure has_power_basis (R S : Type*) [comm_ring R] [ring S] [algebra R S] :=
(dim : ℕ)
(gen : S)
(is_basis : is_basis R (λ (i : fin dim), gen ^ (i : ℕ)))

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
  finsupp.total _ _ _ (λ i : fin n, x  ^(i : ℕ)) f =
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

lemma mem_span_power_basis (alg : is_algebraic K L)
  (hx : is_integral K (adjoin_simple.gen K x)) (y : K⟮x⟯) :
  y ∈ submodule.span K (set.range ((λ (i : fin (minimal_polynomial hx).nat_degree),
    adjoin_simple.gen K x ^ (i : ℕ)))) :=
begin
  obtain ⟨y, hy⟩ := y,
  have mp_monic := minimal_polynomial.monic hx,
  have mp_ne_zero := minimal_polynomial.ne_zero hx,

  obtain ⟨f, rfl⟩ := exists_eq_aeval_gen alg hy,
  rw [aeval_def, ← eval₂_mod_by_monic_eq_self_of_root mp_monic (minimal_polynomial.aeval _),
    eval₂_eq_sum, finsupp.sum],
  refine submodule.sum_mem _ (λ i i_mem, _),
  rw ← algebra.smul_def,
  by_cases hi : i < simple_degree alg,
  { exact submodule.smul_mem _ _ (submodule.subset_span ⟨⟨i, hi⟩, rfl⟩) },
  convert submodule.zero_mem _,
  convert zero_smul _ _,
  refine coeff_eq_zero_of_degree_lt _,
  calc (f %ₘ minimal_polynomial _).degree
      < (minimal_polynomial _).degree : degree_mod_by_monic_lt _ mp_monic mp_ne_zero
  ... ≤ (minimal_polynomial _).nat_degree : degree_le_nat_degree
  ... ≤ i : with_bot.some_le_some.mpr (le_of_not_gt hi),
end

noncomputable def has_power_basis_adjoin_simple
  (K) [field K] [algebra K L] (alg : is_algebraic K L) (x : L) :
  has_power_basis K K⟮x⟯ :=
let hx := ((is_algebraic_iff_is_integral _).mp (alg x)) in
{ dim := (minimal_polynomial ((is_algebraic_iff_is_integral _).mp (alg x))).nat_degree,
  gen := field.adjoin_simple.gen K x,
  is_basis := ⟨linear_independent_power_basis _, _⟩ }

@[simp] lemma gen_adjoin_simple (alg : is_algebraic K L) :
  (has_power_basis_adjoin_simple _ alg x).gen = adjoin_simple.gen K x :=
by rw [has_power_basis_adjoin_simple, gen_simple_extension]

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

@[simp] lemma total_power_basis_eq (h : has_power_basis A S) (f : fin h.dim →₀ S) :
  finsupp.total _ _ _ (λ (i : fin h.dim), h.gen ^ (i : ℕ)) f =
    aeval h.gen (finsupp.emb_fin_nat f) :=
by simp [aeval_def, eval₂_eq_sum, finsupp.total, linear_map.smul_right, algebra.smul_def]

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

section block_matrix

variables {o : Type*} [fintype o] [decidable_eq o]
variables {m n : Type*} [fintype m] [fintype n]

/-- For `M : Π (k : o), matrix m n R`, `block_matrix M` is the
`(o × m)`-by-`(o × n)` matrix with `M k` along the diagonal and `0` elsewhere.

For an `(m × o)`-by-`(n × o)` matrix, see `block_matrix'`.
-/
def block_matrix (M : o → matrix m n R) : matrix (o × m) (o × n) R
| ⟨k, i⟩ ⟨k', j⟩ := if k = k' then M k i j else 0

/-- For `M : Π (k : o), matrix m n R`, `block_matrix M` is the
`(m × o)`-by-`(n × o)` matrix with `M k` along the diagonal and `0` elsewhere.

For an `(o × m)`-by-`(o × n)` matrix, see `block_matrix`.
-/
def block_matrix' (M : o → matrix m n R) : matrix (m × o) (n × o) R
| ⟨i, k⟩ ⟨j, k'⟩ := if k = k' then M k i j else 0

variables (M : o → matrix m n R)

lemma block_matrix_apply_mk (k i k' j) :
  block_matrix M ⟨k, i⟩ ⟨k', j⟩ = if k = k' then M k i j else 0 := rfl

lemma block_matrix_apply : Π (ki kj),
  block_matrix M ki kj = if ki.fst = kj.fst then M ki.fst ki.snd kj.snd else 0
| ⟨k, i⟩ ⟨k', j⟩ := rfl

@[simp] lemma block_matrix_apply_eq (k i j) :
  block_matrix M ⟨k, i⟩ ⟨k, j⟩ = M k i j := if_pos rfl

lemma block_matrix_apply_ne {k k'} (i j) (h : k ≠ k') :
  block_matrix M ⟨k, i⟩ ⟨k', j⟩ = 0 := if_neg h

lemma block_matrix'_eq_block_matrix_swap :
  block_matrix' M = (λ i j, block_matrix M (prod.swap i) (prod.swap j)) :=
by { ext ⟨i, k⟩ ⟨j, k⟩, refl }

lemma block_matrix'_eq_block_matrix_prod_comm :
  block_matrix' M = (λ i j, block_matrix M (equiv.prod_comm _ _ i) (equiv.prod_comm _ _ j)) :=
by { ext ⟨i, k⟩ ⟨j, k⟩, refl }

lemma block_matrix'_apply_mk (k i k' j) :
  block_matrix' M ⟨i, k⟩ ⟨j, k'⟩ = if k = k' then M k i j else 0 := rfl

lemma block_matrix'_apply : Π (ki kj),
  block_matrix' M ki kj = if ki.snd = kj.snd then M ki.snd ki.fst kj.fst else 0
| ⟨k, i⟩ ⟨k', j⟩ := rfl

@[simp] lemma block_matrix'_apply_eq (k i j) :
  block_matrix' M ⟨i, k⟩ ⟨j, k⟩ = M k i j := if_pos rfl

lemma block_matrix'_apply_ne {k k'} (i j) (h : k ≠ k') :
  block_matrix' M ⟨i, k⟩ ⟨j, k'⟩ = 0 := if_neg h

@[simp] lemma finset.univ_pi_univ {m : o → Type*} [Π k, fintype (m k)] :
  finset.univ.pi (λ (k : o), (finset.univ : finset (m k))) = finset.univ :=
eq_top_iff.mpr (λ f _, finset.mem_pi.mpr (λ x _, finset.mem_univ _))

@[simp] lemma finset.univ_product_univ :
  (finset.univ.product finset.univ : finset (o × m)) = finset.univ :=
eq_top_iff.mpr (λ x _, finset.mem_product.mpr ⟨finset.mem_univ _, finset.mem_univ _⟩)

lemma mk_eq_of_preserves_fst {f : o × m → o × n} (hf : ∀ x, (f x).fst = x.fst)
  (k : o) (x : m) :
  (k, (f (k, x)).snd) = f (k, x) :=
by rw [← @prod.mk.eta _ _ (f (k, x)), hf (k, x)]

/- Turn a function returning permutations into a permutation of the product type. -/
def uncurry (σ : o → equiv.perm m) : equiv.perm (o × m) :=
{ to_fun := λ kx, ⟨kx.1, σ kx.1 kx.2⟩,
  inv_fun := λ kx, ⟨kx.1, (σ kx.1)⁻¹ kx.2⟩,
  left_inv := by { rintros ⟨k, x⟩, simp },
  right_inv := by { rintros ⟨k, x⟩, simp } }

@[simp] lemma uncurry_apply_mk (σ : o → equiv.perm m) (k : o) (x : m) :
  uncurry σ (k, x) = (k, σ k x) := rfl

/-- Extends `σ` to `o × m` by keeping everything except `(k, _)` fixed.  -/
def extend (σ : equiv.perm m) (k : o) : equiv.perm (o × m) :=
{ to_fun := λ kx, if k = kx.fst then (k, σ kx.snd) else kx,
  inv_fun := λ kx, if k = kx.fst then (k, σ⁻¹ kx.snd) else kx,
  left_inv := by { rintros ⟨k', x⟩, simp only, split_ifs with h; simp [h] },
  right_inv := by { rintros ⟨k', x⟩, simp only, split_ifs with h; simp [h] } }

@[simp] lemma extend_apply_eq (σ : equiv.perm m) (k : o) (x : m) :
  extend σ k (k, x) = (k, σ x) := if_pos rfl

lemma extend_apply_ne (σ : equiv.perm m) {k k' : o} (h : k ≠ k') (x : m) :
  extend σ k (k', x) = (k', x) := if_neg h

lemma eq_of_extend_apply_ne {σ : equiv.perm m} {k k' : o} {x : m}
  (h : extend σ k (k', x) ≠ (k', x)) : k = k' :=
by { contrapose! h, exact extend_apply_ne _ h _ }

@[simp] lemma fst_extend (σ : equiv.perm m) (k : o) (kx : o × m) :
  (extend σ k kx).fst = kx.fst :=
begin
  simp only [extend, equiv.coe_fn_mk],
  split_ifs,
  { assumption },
  { refl }
end

@[simp] lemma list.prod_to_finset {α M : Type*} [decidable_eq α] [comm_monoid M] (f : α → M)
  {l : list α} (hl : l.nodup) : l.to_finset.prod f = (l.map f).prod :=
begin
  revert hl,
  apply l.rec_on,
  { simp },
  intros a l ih hl,
  obtain ⟨not_mem, hl⟩ := list.nodup_cons.mp hl,
  simp [finset.prod_insert (mt list.mem_to_finset.mp not_mem), ih hl]
end

lemma uncurry_eq_prod_extend (σ : o → equiv.perm m)
  {l : list o} (hl : l.nodup) (mem_l : ∀ k, k ∈ l) :
  uncurry σ = (l.map (λ k, extend (σ k) k)).prod :=
begin
  ext ⟨k, x⟩ : 1,
  suffices : (k ∈ l ∧ (l.map (λ k, extend (σ k) k)).prod (k, x) = (k, σ k x)) ∨
             (k ∉ l ∧ (l.map (λ k, extend (σ k) k)).prod (k, x) = (k, x)),
  { obtain ⟨_, prod_eq⟩ := or.resolve_right this (not_and.mpr (λ h _, h (mem_l k))),
    rw [prod_eq, uncurry_apply_mk] },
  clear mem_l,

  induction l with k' l ih,
  { refine or.inr ⟨list.not_mem_nil _, _⟩,
    rw [list.map_nil, list.prod_nil, equiv.perm.one_apply] },

  rw [list.map_cons, list.prod_cons, equiv.perm.mul_apply],
  rcases ih (list.nodup_cons.mp hl).2 with ⟨mem_l, prod_eq⟩ | ⟨not_mem_l, prod_eq⟩; rw prod_eq,
  { refine or.inl ⟨list.mem_cons_of_mem _ mem_l, _⟩,
    rw extend_apply_ne _ (λ (h : k' = k), (list.nodup_cons.mp hl).1 (h.symm ▸ mem_l)) },
  by_cases hk' : k = k',
  { rw ← hk' at *,
    refine or.inl ⟨list.mem_cons_self k l, _⟩,
    rw extend_apply_eq },
  { refine or.inr ⟨λ h, not_or hk' not_mem_l ((list.mem_cons_iff _ _ _).mp h), _⟩,
    rw extend_apply_ne _ (ne.symm hk') },
end

lemma sign_extend (σ : equiv.perm m) (k : o) [decidable_eq m] :
  (extend σ k).sign = σ.sign :=
equiv.perm.sign_bij (λ (x : o × m) hx, x.snd)
  (λ ⟨k', x⟩ hx hx', by simp [eq_of_extend_apply_ne hx])
  (λ ⟨k₁, x₁⟩ ⟨k₂, x₂⟩ hx₁ hx₂ h,
    by simpa [← eq_of_extend_apply_ne hx₁, ← eq_of_extend_apply_ne hx₂] using h)
  (λ y hy, ⟨(k, y), by simpa, by simp⟩)

lemma sign_uncurry (σ : o → equiv.perm m) [decidable_eq m] :
  (uncurry σ).sign = ∏ k, (σ k).sign :=
begin
  obtain ⟨l, hl, mem_l⟩ := fintype.exists_univ_list o,
  have l_to_finset : l.to_finset = finset.univ,
  { apply eq_top_iff.mpr,
    intros x _,
    exact list.mem_to_finset.mpr (mem_l x) },
  rw [uncurry_eq_prod_extend σ hl mem_l, equiv.perm.sign.map_list_prod,
      list.map_map, ← l_to_finset, list.prod_to_finset _ hl],
  simp_rw ← λ k, sign_extend (σ k) k
end

@[simp, norm_cast] lemma prod_coe (f : o → ℤ) (s : finset o) :
  (↑∏ i in s, f i : R) = ∏ i in s, f i :=
(int.cast_ring_hom R).map_prod _ _

@[simp, norm_cast] lemma units.prod_coe (f : o → units R) (s : finset o) :
  (↑∏ i in s, f i : R) = ∏ i in s, f i :=
(units.coe_hom R).map_prod _ _

@[simp] lemma det_block_matrix [decidable_eq m] (M : o → matrix m m R) :
  (block_matrix M).det = ∏ k, (M k).det :=
begin
  -- Rewrite the determinants as a sum over permutations.
  unfold det,
  -- The right hand side is a product of sums, rewrite it as a sum of products.
  rw finset.prod_sum,
  simp_rw [finset.mem_univ, finset.prod_attach_univ, finset.univ_pi_univ],
  -- We claim that the only permutations contributing to the sum are those that
  -- preserve their first component.
  let preserving_fst : finset (equiv.perm (o × m)) :=
    finset.univ.filter (λ σ, ∀ x, (σ x).fst = x.fst),
  have mem_preserving_fst : ∀ {σ : equiv.perm (o × m)},
    σ ∈ preserving_fst ↔ ∀ x, (σ x).fst = x.fst :=
    λ σ, finset.mem_filter.trans ⟨λ h, h.2, λ h, ⟨finset.mem_univ _, h⟩⟩,
  rw ← finset.sum_subset (finset.subset_univ preserving_fst) _,
  -- And that these are in bijection with `o → equiv.perm m`.
  rw (finset.sum_bij (λ (σ : ∀ (k : o), k ∈ finset.univ → equiv.perm m) _,
                        uncurry (λ k, σ k (finset.mem_univ k))) _ _ _ _).symm,
  { intros σ _,
    rw mem_preserving_fst,
    rintros ⟨k, x⟩,
    simp },
  { intros σ _,
    rw finset.prod_mul_distrib,
    congr,
    { simp [sign_uncurry] },
    rw [← finset.univ_product_univ, finset.prod_product],
    simp },
  { intros σ σ' _ _ eq,
    ext k hk x,
    simp only at eq,
    have : ∀ k x,
      uncurry (λ k, σ k (finset.mem_univ _)) (k, x) = uncurry (λ k, σ' k (finset.mem_univ _)) (k, x) :=
      λ k x, by rw eq,
    simp only [uncurry_apply_mk, prod.mk.inj_iff] at this,
    exact (this k x).2 },
  { intros σ hσ,
    rw mem_preserving_fst at hσ,
    refine ⟨λ k _, ⟨λ x, (σ (k, x)).snd, λ x, (σ⁻¹ (k, x)).snd, _, _⟩, _, _⟩,
    { intro x,
      simp [mk_eq_of_preserves_fst hσ] },
    { intro x,
      have hσ' : ∀ x, (σ⁻¹ x).fst = x.fst,
      { intro x, conv_rhs { rw [← σ.apply_inv_self x, hσ] } },
      simp [mk_eq_of_preserves_fst hσ'] },
    { apply finset.mem_univ },
    { ext ⟨k, x⟩; simp [hσ] } },
  { intros σ _ hσ,
    rw mem_preserving_fst at hσ,
    obtain ⟨⟨k, x⟩, hkx⟩ := not_forall.mp hσ,
    rw [finset.prod_eq_zero (finset.mem_univ (k, x)), mul_zero],
    rw [← @prod.mk.eta _ _ (σ (k, x)), block_matrix_apply_ne],
    exact hkx }
end

.
@[simp] lemma perm_congr_apply (e : n ≃ m) (σ : equiv.perm n) (x : m) :
  equiv.perm_congr e σ x = e (σ (e.symm x)) := rfl

@[simp] lemma sign_perm_congr [decidable_eq m] [decidable_eq n] (e : n ≃ m) (σ : equiv.perm n) :
  (e.perm_congr σ).sign = σ.sign :=
equiv.perm.sign_eq_sign_of_equiv _ _ e.symm (by simp)

@[simp] lemma det_equiv [decidable_eq m] [decidable_eq n] (e : n ≃ m) (M : matrix m m R) :
  matrix.det (λ i j, M (e i) (e j)) = M.det :=
calc  ∑ (σ : equiv.perm n), ↑σ.sign * ∏ (i : n), M (e (σ i)) (e i)
    = ∑ (σ : equiv.perm n), ↑(equiv.perm_congr e σ).sign * ∏ (i : n), M (equiv.perm_congr e σ (e i)) (e i) :
  by simp_rw [sign_perm_congr, perm_congr_apply, e.symm_apply_apply]
... = ∑ (σ : equiv.perm m), ↑σ.sign * ∏ (i : n), M (σ (e i)) (e i) :
  finset.sum_equiv (equiv.perm_congr e) (λ σ, ↑σ.sign * ∏ (i : n), M (σ (e i)) (e i))
... = ∑ (σ : equiv.perm m), ↑σ.sign * ∏ (i : m), M (σ i) i :
  by simp_rw (λ (σ : equiv.perm m), finset.prod_equiv e (λ (i : m), M (σ i) i))

@[simp] lemma det_block_matrix' [decidable_eq m] (M : o → matrix m m R) :
  (block_matrix' M).det = ∏ k, (M k).det :=
by rw [block_matrix'_eq_block_matrix_prod_comm, det_equiv, det_block_matrix]

end block_matrix

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

@[simp] lemma linear_equiv_matrix_lmul [decidable_eq ι] (x : S) (i j) :
  linear_equiv_matrix hb hb (lmul R S x) i j = hb.repr (x * b j) i :=
by rw [linear_equiv_matrix_apply', lmul_apply]

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

open field.adjoin_simple
open algebra

variables [decidable_eq ι] [algebra S T] [is_scalar_tower R S T]

lemma linear_equiv_matrix_lsmul (x : R) :
  linear_equiv_matrix hb hb (lsmul R S x) = algebra_map _ _ x :=
by { ext i j, simp [linear_equiv_matrix_apply, algebra_map_matrix_apply, eq_comm] }

noncomputable def lmul_matrix : S →ₐ[R] matrix ι ι R :=
{ to_fun := λ x, linear_equiv_matrix hb hb (lmul R S x),
  map_zero' := by rw [linear_map.map_zero, linear_equiv.map_zero],
  map_one' := by rw [lmul_one, linear_equiv_matrix_id],
  map_add' := λ x y, by rw [linear_map.map_add, linear_equiv.map_add],
  map_mul' := λ x y, by rw [lmul_mul, linear_equiv_matrix_comp hb hb, matrix.mul_eq_mul],
  commutes' := λ r, by rw [lmul_algebra_map, linear_equiv_matrix_lsmul] }

lemma lmul_matrix_apply (x : S) (i j) :
  lmul_matrix hb x i j = linear_equiv_matrix hb hb (lmul R S x) i j := rfl

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
by simp only [lmul_matrix_apply, linear_equiv_matrix_apply, is_basis.equiv_fun_apply, mul_comm,
              is_basis.smul_repr, finsupp.smul_apply, lmul_apply, id.smul_eq_mul,
              map_smul_eq_smul_map, mul_smul_comm]

lemma lmul_matrix_smul_algebra_map {κ : Type*} [fintype κ] [decidable_eq κ]
  {b : ι → S} (hb : is_basis R b) {c : κ → T} (hc : is_basis S c) (x : S) :
  lmul_matrix (hb.smul hc) (algebra_map _ _ x) = block_matrix' (λ k, lmul_matrix hb x) :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  rw [lmul_matrix_smul, alg_hom.commutes, block_matrix'_apply_mk, algebra_map_matrix_apply],
  split_ifs with h; simp [h],
end

lemma lmul_matrix_smul_algebra_map_eq {κ : Type*} [fintype κ] [decidable_eq κ]
  {b : ι → S} (hb : is_basis R b) {c : κ → T} (hc : is_basis S c) (x : S) (i j k) :
  lmul_matrix (hb.smul hc) (algebra_map _ _ x) (i, k) (j, k) = lmul_matrix hb x i j :=
by rw [lmul_matrix_smul_algebra_map, block_matrix'_apply_eq]

lemma lmul_matrix_smul_algebra_map_ne {κ : Type*} [fintype κ] [decidable_eq κ]
  {b : ι → S} (hb : is_basis R b) {c : κ → T} (hc : is_basis S c) (x : S) (i j) {k k'}
  (h : k ≠ k') : lmul_matrix (hb.smul hc) (algebra_map _ _ x) (i, k) (j, k') = 0 :=
by rw [lmul_matrix_smul_algebra_map, block_matrix'_apply_ne _ _ _ h]

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
λ x x' h, lmul_injective ((linear_equiv_matrix hb hb).injective h)

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

lemma char_matrix_lmul_matrix_smul {κ : Type*} [fintype κ] [decidable_eq κ]
  {b : ι → S} (hb : is_basis R b) {c : κ → T} (hc : is_basis S c) (x : S) :
  char_matrix (lmul_matrix (hb.smul hc) (algebra_map _ _ x)) =
    block_matrix' (λ _, char_matrix (lmul_matrix hb x)) :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  rw block_matrix'_apply_mk,
  split_ifs with hk,
  { rw hk,
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
      char_matrix_lmul_matrix_smul, det_block_matrix', finset.prod_const, finset.card_univ],
end

instance finite_dimensional.tower_top {V : Type*} [add_comm_group V]
  [vector_space K V] [vector_space L V] [is_scalar_tower K L V]
  [finite_dimensional K V] : finite_dimensional L V := sorry

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
  have : char_poly (lmul_matrix hb x) = char_poly (lmul_matrix (h.is_basis.smul hc) x) := sorry,
  rw [this, char_poly_lmul_matrix_smul h hc],
end

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
  rw nondegenerate_iff_eq_zero,
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
