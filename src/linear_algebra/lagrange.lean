/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Wrenna Robson
-/

import algebra.big_operators.basic
import linear_algebra.vandermonde
import ring_theory.polynomial.basic

/-!
# Lagrange interpolation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions
* In everything that follows, `s : finset ι` is a finite set of indexes, with `v : ι → F` an
indexing of the field over some type. We call the image of v on s the interpolation nodes,
though strictly unique nodes are only defined when v is injective on s.
* `lagrange.basis_divisor x y`, with `x y : F`. These are the normalised irreducible factors of
the Lagrange basis polynomials. They evaluate to `1` at `x` and `0` at `y` when `x` and `y`
are distinct.
* `lagrange.basis v i` with `i : ι`: the Lagrange basis polynomial that evaluates to `1` at `v i`
and `0` at `v j` for `i ≠ j`.
* `lagrange.interpolate v r` where `r : ι → F` is a function from the fintype to the field: the
Lagrange interpolant that evaluates to `r i` at `x i` for all `i : ι`. The `r i` are the _values_
associated with the _nodes_`x i`.
* `lagrange.interpolate_at v f`, where `v : ι ↪ F` and `ι` is a fintype, and `f : F → F` is a
function from the field to itself: this is the Lagrange interpolant that evaluates to `f (x i)`
at `x i`, and so approximates the function `f`. This is just a special case of the general
interpolation, where the values are given by a known function `f`.
-/

open_locale polynomial big_operators

section polynomial_determination

namespace polynomial
variables {R : Type*} [comm_ring R] [is_domain R] {f g : R[X]}

section finset
open function fintype
variables (s : finset R)

theorem eq_zero_of_degree_lt_of_eval_finset_eq_zero (degree_f_lt : f.degree < s.card)
  (eval_f : ∀ x ∈ s, f.eval x = 0) : f = 0 :=
begin
  rw ← mem_degree_lt at degree_f_lt,
  simp_rw eval_eq_sum_degree_lt_equiv degree_f_lt at eval_f,
  rw ← degree_lt_equiv_eq_zero_iff_eq_zero degree_f_lt,
  exact matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
    (injective.comp (embedding.subtype _).inj' (equiv_fin_of_card_eq (card_coe _)).symm.injective)
    (λ _, eval_f _ (finset.coe_mem _))
end

theorem eq_of_degree_sub_lt_of_eval_finset_eq (degree_fg_lt : (f - g).degree < s.card)
  (eval_fg : ∀ x ∈ s, f.eval x = g.eval x) : f = g :=
begin
  rw ← sub_eq_zero,
  refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_fg_lt _,
  simp_rw [eval_sub, sub_eq_zero],
  exact eval_fg
end

theorem eq_of_degrees_lt_of_eval_finset_eq (degree_f_lt : f.degree < s.card)
  (degree_g_lt : g.degree < s.card) (eval_fg : ∀ x ∈ s, f.eval x = g.eval x) : f = g :=
begin
  rw ← mem_degree_lt at degree_f_lt degree_g_lt,
  refine eq_of_degree_sub_lt_of_eval_finset_eq _ _ eval_fg,
  rw ← mem_degree_lt, exact submodule.sub_mem _ degree_f_lt degree_g_lt
end

end finset

section indexed
open finset
variables {ι : Type*} {v : ι → R} (s : finset ι)

theorem eq_zero_of_degree_lt_of_eval_index_eq_zero (hvs : set.inj_on v s)
  (degree_f_lt : f.degree < s.card) (eval_f : ∀ i ∈ s, f.eval (v i) = 0) : f = 0 :=
begin
  classical,
  rw ← card_image_of_inj_on hvs at degree_f_lt,
  refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_f_lt _,
  intros x hx,
  rcases mem_image.mp hx with ⟨_, hj, rfl⟩,
  exact eval_f _ hj
end

theorem eq_of_degree_sub_lt_of_eval_index_eq (hvs : set.inj_on v s)
  (degree_fg_lt : (f - g).degree < s.card) (eval_fg : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) :
  f = g :=
begin
  rw ← sub_eq_zero,
  refine eq_zero_of_degree_lt_of_eval_index_eq_zero _ hvs degree_fg_lt _,
  simp_rw [eval_sub, sub_eq_zero],
  exact eval_fg
end

theorem eq_of_degrees_lt_of_eval_index_eq (hvs : set.inj_on v s) (degree_f_lt : f.degree < s.card)
  (degree_g_lt : g.degree < s.card) (eval_fg : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) : f = g :=
begin
  refine eq_of_degree_sub_lt_of_eval_index_eq _ hvs _ eval_fg,
  rw ← mem_degree_lt at degree_f_lt degree_g_lt ⊢,
  exact submodule.sub_mem _ degree_f_lt degree_g_lt
end

end indexed

end polynomial

end polynomial_determination

noncomputable theory

namespace lagrange
open polynomial
variables {F : Type*} [field F]

section basis_divisor
variables {x y : F}
/-- `basis_divisor x y` is the unique linear or constant polynomial such that
when evaluated at `x` it gives `1` and `y` it gives `0` (where when `x = y` it is identically `0`).
Such polynomials are the building blocks for the Lagrange interpolants. -/
def basis_divisor (x y : F) : F[X] := C ((x - y)⁻¹) * (X - C (y))

lemma basis_divisor_self : basis_divisor x x = 0 :=
by simp only [basis_divisor, sub_self, inv_zero, map_zero, zero_mul]

lemma basis_divisor_inj (hxy : basis_divisor x y = 0) : x = y :=
begin
  simp_rw [basis_divisor, mul_eq_zero, X_sub_C_ne_zero, or_false,
            C_eq_zero, inv_eq_zero, sub_eq_zero] at hxy,
  exact hxy
end

@[simp] lemma basis_divisor_eq_zero_iff : basis_divisor x y = 0 ↔ x = y :=
⟨basis_divisor_inj, λ H, H ▸ basis_divisor_self⟩

lemma basis_divisor_ne_zero_iff : basis_divisor x y ≠ 0 ↔ x ≠ y :=
by rw [ne.def, basis_divisor_eq_zero_iff]

lemma degree_basis_divisor_of_ne (hxy : x ≠ y) : (basis_divisor x y).degree = 1 :=
begin
  rw [basis_divisor, degree_mul, degree_X_sub_C, degree_C, zero_add],
  exact inv_ne_zero (sub_ne_zero_of_ne hxy)
end

@[simp] lemma degree_basis_divisor_self : (basis_divisor x x).degree = ⊥ :=
by rw [basis_divisor_self, degree_zero]

lemma nat_degree_basis_divisor_self : (basis_divisor x x).nat_degree = 0 :=
by rw [basis_divisor_self, nat_degree_zero]

lemma nat_degree_basis_divisor_of_ne (hxy : x ≠ y) : (basis_divisor x y).nat_degree = 1 :=
nat_degree_eq_of_degree_eq_some (degree_basis_divisor_of_ne hxy)

@[simp] lemma eval_basis_divisor_right : eval y (basis_divisor x y) = 0 :=
by simp only [basis_divisor, eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero]

lemma eval_basis_divisor_left_of_ne (hxy : x ≠ y) : eval x (basis_divisor x y) = 1 :=
begin
  simp only [basis_divisor, eval_mul, eval_C, eval_sub, eval_X],
  exact inv_mul_cancel (sub_ne_zero_of_ne hxy)
end

end basis_divisor

section basis
open finset
variables {ι : Type*} [decidable_eq ι] {s : finset ι} {v : ι → F} {i j : ι}

/-- Lagrange basis polynomials indexed by `s : finset ι`, defined at nodes `v i` for a
map `v : ι → F`. For `i, j ∈ s`, `basis s v i` evaluates to 0 at `v j` for `i ≠ j`. When
`v` is injective on `s`, `basis s v i` evaluates to 1 at `v i`. -/
protected def basis (s : finset ι) (v : ι → F) (i : ι) : F[X] :=
∏ j in s.erase i, basis_divisor (v i) (v j)

@[simp] theorem basis_empty : lagrange.basis ∅ v i = 1 := rfl

@[simp] theorem basis_singleton (i : ι) : lagrange.basis {i} v i = 1 :=
by rw [lagrange.basis, erase_singleton, prod_empty]

@[simp] theorem basis_pair_left (hij : i ≠ j) :
  lagrange.basis {i, j} v i = basis_divisor (v i) (v j) :=
by simp only [lagrange.basis, hij, erase_insert_eq_erase, erase_eq_of_not_mem,
              mem_singleton, not_false_iff, prod_singleton]

@[simp] theorem basis_pair_right (hij : i ≠ j) :
  lagrange.basis {i, j} v j = basis_divisor (v j) (v i) :=
by { rw pair_comm, exact basis_pair_left hij.symm }

lemma basis_ne_zero (hvs : set.inj_on v s) (hi : i ∈ s) : lagrange.basis s v i ≠ 0 :=
begin
  simp_rw [lagrange.basis, prod_ne_zero_iff, ne.def, mem_erase],
  rintros j ⟨hij, hj⟩,
  rw [basis_divisor_eq_zero_iff, hvs.eq_iff hi hj],
  exact hij.symm
end

@[simp] theorem eval_basis_self (hvs : set.inj_on v s) (hi : i ∈ s) :
  (lagrange.basis s v i).eval (v i) = 1 :=
begin
  rw [lagrange.basis, eval_prod],
  refine prod_eq_one (λ j H, _),
  rw eval_basis_divisor_left_of_ne,
  rcases mem_erase.mp H with ⟨hij, hj⟩,
  exact mt (hvs hi hj) hij.symm
end

@[simp] theorem eval_basis_of_ne (hij : i ≠ j) (hj : j ∈ s) :
  (lagrange.basis s v i).eval (v j) = 0 :=
begin
  simp_rw [lagrange.basis, eval_prod, prod_eq_zero_iff],
  exact ⟨j, ⟨mem_erase.mpr ⟨hij.symm, hj⟩, eval_basis_divisor_right⟩⟩
end

@[simp] theorem nat_degree_basis (hvs : set.inj_on v s) (hi : i ∈ s) :
  (lagrange.basis s v i).nat_degree = s.card - 1 :=
begin
  have H : ∀ j, j ∈ s.erase i → basis_divisor (v i) (v j) ≠ 0,
  { simp_rw [ne.def, mem_erase, basis_divisor_eq_zero_iff],
    exact λ j ⟨hij₁, hj⟩ hij₂, hij₁ (hvs hj hi hij₂.symm) },
  rw [← card_erase_of_mem hi, card_eq_sum_ones],
  convert nat_degree_prod _ _ H using 1,
  refine sum_congr rfl (λ j hj, (nat_degree_basis_divisor_of_ne _).symm),
  rw [ne.def, ← basis_divisor_eq_zero_iff],
  exact H _ hj
end

theorem degree_basis (hvs : set.inj_on v s) (hi : i ∈ s) :
  (lagrange.basis s v i).degree = ↑(s.card - 1) :=
by rw [degree_eq_nat_degree (basis_ne_zero hvs hi), nat_degree_basis hvs hi]

lemma sum_basis (hvs : set.inj_on v s) (hs : s.nonempty) : ∑ j in s, (lagrange.basis s v j) = 1 :=
begin
  refine eq_of_degrees_lt_of_eval_index_eq s hvs (lt_of_le_of_lt (degree_sum_le _ _) _) _ _,
  { rw finset.sup_lt_iff (with_bot.bot_lt_coe s.card),
    intros i hi,
    rw [degree_basis hvs hi, with_bot.coe_lt_coe],
    exact nat.pred_lt (card_ne_zero_of_mem hi) },
  { rw [degree_one, ← with_bot.coe_zero, with_bot.coe_lt_coe],
    exact nonempty.card_pos hs },
  { intros i hi,
    rw [eval_finset_sum, eval_one, ← add_sum_erase _ _ hi,
        eval_basis_self hvs hi, add_right_eq_self],
    refine sum_eq_zero (λ j hj, _),
    rcases mem_erase.mp hj with ⟨hij, hj⟩,
    rw eval_basis_of_ne hij hi }
end

lemma basis_divisor_add_symm {x y : F} (hxy : x ≠ y) : basis_divisor x y + basis_divisor y x = 1 :=
begin
  classical,
  rw [←sum_basis (set.inj_on_of_injective function.injective_id _) ⟨x, mem_insert_self _ {y}⟩,
      sum_insert (not_mem_singleton.mpr hxy), sum_singleton, basis_pair_left hxy,
      basis_pair_right hxy, id, id]
end

end basis

section interpolate
open finset
variables {ι : Type*} [decidable_eq ι] {s t : finset ι} {i j : ι} {v : ι → F} (r r' : ι → F)

/-- Lagrange interpolation: given a finset `s : finset ι`, a nodal map  `v : ι → F` injective on
`s` and a value function `r : ι → F`,  `interpolate s v r` is the unique
polynomial of degree `< s.card` that takes value `r i` on `v i` for all `i` in `s`. -/
@[simps]
def interpolate (s : finset ι) (v : ι → F) : (ι → F) →ₗ[F] F[X] :=
{ to_fun := λ r, ∑ i in s, C (r i) * (lagrange.basis s v i),
  map_add' := λ f g, by simp_rw [← finset.sum_add_distrib, ← add_mul,
                                 ← C_add, pi.add_apply],
  map_smul' := λ c f, by simp_rw [finset.smul_sum, C_mul', smul_smul,
                                  pi.smul_apply, ring_hom.id_apply, smul_eq_mul] }

@[simp] theorem interpolate_empty : interpolate ∅ v r = 0 :=
by rw [interpolate_apply, sum_empty]

@[simp] theorem interpolate_singleton : interpolate {i} v r = C (r i) :=
by rw [interpolate_apply, sum_singleton, basis_singleton, mul_one]

theorem interpolate_one (hvs : set.inj_on v s) (hs : s.nonempty) : interpolate s v 1 = 1 :=
by { simp_rw [interpolate_apply, pi.one_apply, map_one, one_mul], exact sum_basis hvs hs }

theorem eval_interpolate_at_node (hvs : set.inj_on v s) (hi : i ∈ s) :
  eval (v i) (interpolate s v r) = r i :=
begin
  rw [interpolate_apply, eval_finset_sum, ← add_sum_erase _ _ hi],
  simp_rw [eval_mul, eval_C, eval_basis_self hvs hi, mul_one, add_right_eq_self],
  refine sum_eq_zero (λ j H, _),
  rw [eval_basis_of_ne (mem_erase.mp H).1 hi, mul_zero]
end

theorem degree_interpolate_le (hvs : set.inj_on v s) : (interpolate s v r).degree ≤ ↑(s.card - 1) :=
begin
  refine (degree_sum_le _ _).trans _,
  rw finset.sup_le_iff,
  intros i hi,
  rw [degree_mul, degree_basis hvs hi],
  by_cases hr : r i = 0,
  { simpa only [hr, map_zero, degree_zero, with_bot.bot_add] using bot_le },
  { rw [degree_C hr, zero_add, with_bot.coe_le_coe] }
end

theorem degree_interpolate_lt (hvs : set.inj_on v s) : (interpolate s v r).degree < s.card :=
begin
  rcases eq_empty_or_nonempty s with rfl | h,
  { rw [interpolate_empty, degree_zero, card_empty],
    exact with_bot.bot_lt_coe _ },
  { refine lt_of_le_of_lt (degree_interpolate_le _ hvs) _,
    rw with_bot.coe_lt_coe,
    exact nat.sub_lt (nonempty.card_pos h) zero_lt_one }
end

theorem degree_interpolate_erase_lt (hvs : set.inj_on v s) (hi : i ∈ s) :
  (interpolate (s.erase i) v r).degree < ↑(s.card - 1) :=
begin
  rw ← finset.card_erase_of_mem hi,
  exact degree_interpolate_lt _ (set.inj_on.mono (coe_subset.mpr (erase_subset _ _)) hvs),
end

theorem values_eq_on_of_interpolate_eq (hvs : set.inj_on v s)
  (hrr' : interpolate s v r = interpolate s v r') : ∀ i ∈ s, r i = r' i :=
λ _ hi, by rw [← eval_interpolate_at_node r hvs hi, hrr', eval_interpolate_at_node r' hvs hi]

theorem interpolate_eq_of_values_eq_on (hrr' : ∀ i ∈ s, r i = r' i) :
  interpolate s v r = interpolate s v r' :=
sum_congr rfl (λ i hi, (by rw hrr' _ hi))

theorem interpolate_eq_iff_values_eq_on (hvs : set.inj_on v s) :
  interpolate s v r = interpolate s v r' ↔ ∀ i ∈ s, r i = r' i :=
⟨values_eq_on_of_interpolate_eq _ _ hvs, interpolate_eq_of_values_eq_on _ _⟩

theorem eq_interpolate {f : F[X]} (hvs : set.inj_on v s) (degree_f_lt : f.degree < s.card) :
  f = interpolate s v (λ i, f.eval (v i)) :=
eq_of_degrees_lt_of_eval_index_eq _ hvs degree_f_lt (degree_interpolate_lt _ hvs) $
λ i hi, (eval_interpolate_at_node _ hvs hi).symm

theorem eq_interpolate_of_eval_eq {f : F[X]} (hvs : set.inj_on v s)
  (degree_f_lt : f.degree < s.card) (eval_f : ∀ i ∈ s, f.eval (v i) = r i) :
  f = interpolate s v r :=
by { rw eq_interpolate hvs degree_f_lt, exact interpolate_eq_of_values_eq_on _ _ eval_f }

/--
This is the characteristic property of the interpolation: the interpolation is the
unique polynomial of `degree < fintype.card ι` which takes the value of the `r i` on the `v i`.
-/
theorem eq_interpolate_iff {f : F[X]} (hvs : set.inj_on v s) :
  (f.degree < s.card ∧ ∀ i ∈ s, eval (v i) f = r i) ↔ f = interpolate s v r :=
begin
  split; intro h,
  { exact eq_interpolate_of_eval_eq _ hvs h.1 h.2 },
  { rw h, exact ⟨degree_interpolate_lt _ hvs, λ _ hi, eval_interpolate_at_node _ hvs hi⟩ }
end

/-- Lagrange interpolation induces isomorphism between functions from `s`
and polynomials of degree less than `fintype.card ι`.-/
def fun_equiv_degree_lt (hvs : set.inj_on v s) : degree_lt F s.card ≃ₗ[F] (s → F) :=
{ to_fun := λ f i, f.1.eval (v i),
  map_add' := λ f g, funext $ λ v, eval_add,
  map_smul' := λ c f, funext $ by simp,
  inv_fun := λ r, ⟨interpolate s v (λ x, if hx : x ∈ s then r ⟨x, hx⟩ else 0),
                   mem_degree_lt.2 $ degree_interpolate_lt _ hvs⟩,
  left_inv :=
  begin
    rintros ⟨f, hf⟩,
    simp only [subtype.mk_eq_mk, subtype.coe_mk, dite_eq_ite],
    rw mem_degree_lt at hf,
    nth_rewrite_rhs 0 eq_interpolate hvs hf,
    exact interpolate_eq_of_values_eq_on _ _ (λ _ hi, if_pos hi)
  end,
  right_inv :=
  begin
    intro f,
    ext ⟨i, hi⟩,
    simp only [subtype.coe_mk, eval_interpolate_at_node _ hvs hi],
    exact dif_pos hi,
  end }

theorem interpolate_eq_sum_interpolate_insert_sdiff (hvt : set.inj_on v t) (hs : s.nonempty)
  (hst : s ⊆ t) : interpolate t v r =
  ∑ i in s, (interpolate (insert i (t \ s)) v r) * lagrange.basis s v i :=
begin
  symmetry,
  refine eq_interpolate_of_eval_eq _ hvt (lt_of_le_of_lt (degree_sum_le _ _) _) (λ i hi, _),
  { simp_rw [(finset.sup_lt_iff (with_bot.bot_lt_coe t.card)), degree_mul],
    intros i hi,
    have hs : 1 ≤ s.card := nonempty.card_pos ⟨_, hi⟩,
    have hst' : s.card ≤ t.card := card_le_of_subset hst,
    have H : t.card = (1 + (t.card - s.card)) + (s.card - 1),
    { rw [add_assoc, tsub_add_tsub_cancel hst' hs, ← add_tsub_assoc_of_le (hs.trans hst'),
          nat.succ_add_sub_one, zero_add] },
    rw [degree_basis (set.inj_on.mono hst hvt) hi, H, with_bot.coe_add,
        with_bot.add_lt_add_iff_right (@with_bot.coe_ne_bot _ (s.card - 1))],
    convert degree_interpolate_lt _ (hvt.mono (coe_subset.mpr (insert_subset.mpr
      ⟨hst hi, sdiff_subset _ _⟩))),
    rw [card_insert_of_not_mem (not_mem_sdiff_of_mem_right hi), card_sdiff hst, add_comm] },

  { simp_rw [eval_finset_sum, eval_mul],
    by_cases hi' : i ∈ s,
    { rw [← add_sum_erase _ _ hi', eval_basis_self (hvt.mono hst) hi',
          eval_interpolate_at_node _ (hvt.mono (coe_subset.mpr
            (insert_subset.mpr ⟨hi, sdiff_subset _ _⟩))) (mem_insert_self _ _),
          mul_one, add_right_eq_self],
      refine sum_eq_zero (λ j hj, _),
      rcases mem_erase.mp hj with ⟨hij, hj⟩,
      rw [eval_basis_of_ne hij hi', mul_zero] },
    { have H : ∑ j in s, eval (v i) (lagrange.basis s v j) = 1,
      { rw [← eval_finset_sum, sum_basis (hvt.mono hst) hs, eval_one] },
      rw [← mul_one (r i), ← H, mul_sum],
      refine sum_congr rfl (λ j hj, _),
      congr,
      exact eval_interpolate_at_node _ (hvt.mono (insert_subset.mpr ⟨hst hj, sdiff_subset _ _⟩))
                                (mem_insert.mpr (or.inr (mem_sdiff.mpr ⟨hi, hi'⟩))) } }
end

theorem interpolate_eq_add_interpolate_erase (hvs : set.inj_on v s) (hi : i ∈ s) (hj : j ∈ s)
  (hij : i ≠ j) : interpolate s v r = interpolate (s.erase j) v r * basis_divisor (v i) (v j) +
  interpolate (s.erase i) v r * basis_divisor (v j) (v i) :=
begin
  rw [interpolate_eq_sum_interpolate_insert_sdiff _ hvs ⟨i, (mem_insert_self i {j})⟩ _,
      sum_insert (not_mem_singleton.mpr hij), sum_singleton, basis_pair_left hij,
      basis_pair_right hij,
      sdiff_insert_insert_of_mem_of_not_mem hi (not_mem_singleton.mpr hij),
      sdiff_singleton_eq_erase, pair_comm,
      sdiff_insert_insert_of_mem_of_not_mem hj (not_mem_singleton.mpr hij.symm),
      sdiff_singleton_eq_erase],
  { exact insert_subset.mpr ⟨hi, singleton_subset_iff.mpr hj⟩ },
end

end interpolate

section nodal
open finset polynomial
variables {ι : Type*} {s : finset ι} {v : ι → F} {i : ι} (r : ι → F) {x : F}

/--
`nodal s v` is the unique monic polynomial whose roots are the nodes defined by `v` and `s`.

That is, the roots of `nodal s v` are exactly the image of `v` on `s`,
with appropriate multiplicity.

We can use `nodal` to define the barycentric forms of the evaluated interpolant.
-/
def nodal (s : finset ι) (v : ι → F) : F[X] := ∏ i in s, (X - C (v i))

lemma nodal_eq (s : finset ι) (v : ι → F) : nodal s v = ∏ i in s, (X - C (v i)) := rfl

@[simp] lemma nodal_empty : nodal ∅ v = 1 := rfl

lemma degree_nodal : (nodal s v).degree = s.card :=
by simp_rw [nodal, degree_prod, degree_X_sub_C, sum_const, nat.smul_one_eq_coe]

lemma eval_nodal {x : F} : (nodal s v).eval x = ∏ i in s, (x - v i) :=
by simp_rw [nodal, eval_prod, eval_sub, eval_X, eval_C]

lemma eval_nodal_at_node (hi : i ∈ s) : eval (v i) (nodal s v) = 0 :=
by { rw [eval_nodal, prod_eq_zero_iff], exact ⟨i, hi, sub_eq_zero_of_eq rfl⟩ }

lemma eval_nodal_not_at_node (hx : ∀ i ∈ s, x ≠ v i) : eval x (nodal s v) ≠ 0 :=
by { simp_rw [nodal, eval_prod, prod_ne_zero_iff, eval_sub, eval_X, eval_C, sub_ne_zero], exact hx }

lemma nodal_eq_mul_nodal_erase [decidable_eq ι] (hi : i ∈ s) :
  nodal s v = (X - C (v i)) * nodal (s.erase i) v := by simp_rw [nodal, mul_prod_erase _ _ hi]

lemma X_sub_C_dvd_nodal (v : ι → F) (hi : i ∈ s) : (X - C (v i)) ∣ nodal s v :=
⟨_, by { classical, exact nodal_eq_mul_nodal_erase hi }⟩

variable [decidable_eq ι]

lemma nodal_erase_eq_nodal_div (hi : i ∈ s) :
  nodal (s.erase i) v = nodal s v / (X - C (v i)) :=
begin
  rw [nodal_eq_mul_nodal_erase hi, euclidean_domain.mul_div_cancel_left],
  exact X_sub_C_ne_zero _
end

lemma nodal_insert_eq_nodal (hi : i ∉ s) :
  nodal (insert i s) v = (X - C (v i)) * (nodal s v) := by simp_rw [nodal, prod_insert hi]

lemma derivative_nodal : (nodal s v).derivative = ∑ i in s, nodal (s.erase i) v :=
begin
  refine finset.induction_on s _ (λ _ _ hit IH, _),
  { rw [nodal_empty, derivative_one, sum_empty] },
  { rw [nodal_insert_eq_nodal hit, derivative_mul, IH, derivative_sub,
        derivative_X, derivative_C, sub_zero, one_mul, sum_insert hit,
        mul_sum, erase_insert hit, add_right_inj],
    refine sum_congr rfl (λ j hjt, _),
    rw [nodal_erase_eq_nodal_div (mem_insert_of_mem hjt), nodal_insert_eq_nodal hit,
        euclidean_domain.mul_div_assoc _ (X_sub_C_dvd_nodal v hjt),
        nodal_erase_eq_nodal_div hjt] }
end

lemma eval_nodal_derivative_eval_node_eq (hi : i ∈ s) :
  eval (v i) (nodal s v).derivative = eval (v i) (nodal (s.erase i) v) :=
begin
  rw [derivative_nodal, eval_finset_sum, ← add_sum_erase _ _ hi, add_right_eq_self],
  refine sum_eq_zero (λ j hj, _),
  simp_rw [nodal, eval_prod, eval_sub, eval_X, eval_C, prod_eq_zero_iff, mem_erase],
  exact ⟨i, ⟨(mem_erase.mp hj).1.symm, hi⟩, sub_eq_zero_of_eq rfl⟩
end

/-- This defines the nodal weight for a given set of node indexes and node mapping function `v`. -/
def nodal_weight (s : finset ι) (v : ι → F) (i : ι) := ∏ j in s.erase i, (v i - v j)⁻¹

lemma nodal_weight_eq_eval_nodal_erase_inv : nodal_weight s v i =
  (eval (v i) (nodal (s.erase i) v))⁻¹ :=
by rw [eval_nodal, nodal_weight, prod_inv_distrib]

lemma nodal_weight_eq_eval_nodal_derative (hi : i ∈ s) : nodal_weight s v i =
  (eval (v i) (nodal s v).derivative)⁻¹ :=
by rw [eval_nodal_derivative_eval_node_eq hi, nodal_weight_eq_eval_nodal_erase_inv]

lemma nodal_weight_ne_zero (hvs : set.inj_on v s) (hi : i ∈ s) : nodal_weight s v i ≠ 0 :=
begin
  rw [nodal_weight, prod_ne_zero_iff],
  intros j hj,
  rcases mem_erase.mp hj with ⟨hij, hj⟩,
  refine inv_ne_zero (sub_ne_zero_of_ne (mt (hvs.eq_iff hi hj).mp hij.symm)),
end

lemma basis_eq_prod_sub_inv_mul_nodal_div (hi : i ∈ s) :
  lagrange.basis s v i = C (nodal_weight s v i) * ( nodal s v / (X - C (v i)) )  :=
by simp_rw [lagrange.basis, basis_divisor, nodal_weight, prod_mul_distrib,
            map_prod, ← nodal_erase_eq_nodal_div hi, nodal]

lemma eval_basis_not_at_node (hi : i ∈ s) (hxi : x ≠ v i) :
  eval x (lagrange.basis s v i) = (eval x (nodal s v)) * (nodal_weight s v i * (x - v i)⁻¹)  :=
by rw [mul_comm, basis_eq_prod_sub_inv_mul_nodal_div hi, eval_mul, eval_C,
       ← nodal_erase_eq_nodal_div hi, eval_nodal, eval_nodal, mul_assoc, ← mul_prod_erase _ _ hi,
       ← mul_assoc (x - v i)⁻¹, inv_mul_cancel (sub_ne_zero_of_ne hxi), one_mul]

lemma interpolate_eq_nodal_weight_mul_nodal_div_X_sub_C :
  interpolate s v r = ∑ i in s, C (nodal_weight s v i) * (nodal s v / (X - C (v i))) * C (r i) :=
sum_congr rfl (λ j hj, by rw [mul_comm, basis_eq_prod_sub_inv_mul_nodal_div hj])

/-- This is the first barycentric form of the Lagrange interpolant. -/
lemma eval_interpolate_not_at_node (hx : ∀ i ∈ s, x ≠ v i) : eval x (interpolate s v r) =
  eval x (nodal s v) * ∑ i in s, nodal_weight s v i * (x - v i)⁻¹ * r i :=
begin
  simp_rw [interpolate_apply, mul_sum, eval_finset_sum, eval_mul, eval_C],
  refine sum_congr rfl (λ i hi, _),
  rw [← mul_assoc, mul_comm, eval_basis_not_at_node hi (hx _ hi)]
end

lemma sum_nodal_weight_mul_inv_sub_ne_zero (hvs : set.inj_on v s)
  (hx : ∀ i ∈ s, x ≠ v i) (hs : s.nonempty) :
  ∑ i in s, nodal_weight s v i * (x - v i)⁻¹ ≠ 0 :=
@right_ne_zero_of_mul_eq_one  _ _ _ (eval x (nodal s v)) _ $
  by simpa only [pi.one_apply, interpolate_one hvs hs, eval_one, mul_one]
    using (eval_interpolate_not_at_node 1 hx).symm

/-- This is the second barycentric form of the Lagrange interpolant. -/
lemma eval_interpolate_not_at_node' (hvs : set.inj_on v s) (hs : s.nonempty)
  (hx : ∀ i ∈ s, x ≠ v i) : eval x (interpolate s v r) =
  (∑ i in s, nodal_weight s v i * (x - v i)⁻¹ * r i) /
  ∑ i in s, nodal_weight s v i * (x - v i)⁻¹ :=
begin
  rw [← div_one (eval x (interpolate s v r)), ← @eval_one _ _ x, ← interpolate_one hvs hs,
      eval_interpolate_not_at_node r hx, eval_interpolate_not_at_node 1 hx],
  simp only [mul_div_mul_left _ _ (eval_nodal_not_at_node hx), pi.one_apply, mul_one]
end

end nodal

end lagrange
