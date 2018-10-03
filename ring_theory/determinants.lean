/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import tactic.tidy
import group_theory.subgroup
import group_theory.perm
import data.finset
import ring_theory.matrix

universes u v

namespace matrix
open equiv equiv.perm finset
variables {n : Type u} [fintype n] [decidable_eq n] {R : Type v} [comm_ring R]

instance : decidable_pred (function.bijective : (n → n) → Prop) :=
λ _, by unfold function.bijective; apply_instance

instance bij_fintype : fintype {f : n → n // function.bijective f} :=
set_fintype _

definition det (M : matrix n n R) : R :=
univ.sum (λ (σ : perm n), (e σ) * univ.prod (λ (i:n), M (σ i) i))

@[simp] lemma det_diagonal {d : n → R} : det (diagonal d) = univ.prod d :=
begin
  refine (finset.sum_eq_single 1 _ _).trans _,
  { intros σ h1 h2,
    cases not_forall.1 (mt (equiv.ext _ _) h2) with x h3,
    convert ring.mul_zero _,
    apply finset.prod_eq_zero,
    { change x ∈ _, simp },
    exact if_neg h3 },
  simp,
  simp
end

-- @[simp] lemma det_scalar {r : R} : det (scalar r : matrix n n R) = r^(fintype.card n) :=
-- by simp [scalar, fintype.card]

-- @[simp] lemma det_zero (h : nonempty n) : det (0 : matrix n n R) = (0 : R) :=
-- by rw ← scalar_zero; simp [-scalar_zero, zero_pow, fintype.card_pos_iff.mpr h]

-- @[simp] lemma det_one : det (1 : matrix n n R) = (1 : R) :=
-- by rw ← scalar_one; simp [-scalar_one]

lemma det_mul_aux (M N : matrix n n R) (p : n → n) (H : ¬function.bijective p) :
univ.sum (λ σ : perm n, e σ * (univ.prod (λ x, M (σ x) (p x)) * univ.prod (λ x, N (p x) x))) = 0 :=
begin
  have H1 : ¬function.injective p,
    from mt (λ h, and.intro h $ fintype.injective_iff_surjective.1 h) H,
  unfold function.injective at H1, simp only [not_forall] at H1,
  rcases H1 with ⟨i, j, H2, H3⟩,
  have H4 : (univ : finset (perm n)) = univ.filter (λ σ, σ.sign = 1) ∪ univ.filter (λ σ, σ.sign = -1),
  { rw [← finset.filter_or], simp only [int.units_eq_one_or],
    ext k, simp only [finset.mem_univ, finset.mem_filter, true_and] },
  have H5 : (univ : finset (perm n)).filter (λ σ, σ.sign = 1) ∩ univ.filter (λ σ, σ.sign = -1) = ∅,
  { rw [← finset.filter_and], refine finset.eq_empty_of_forall_not_mem (λ _ H, _),
    rw finset.mem_filter at H, exact absurd (H.2.1.symm.trans H.2.2) dec_trivial },
  have H6 : finset.map ⟨λ z, z * swap i j, λ _ _, mul_right_cancel⟩
    (univ.filter (λ σ, σ.sign = -1))
    = univ.filter (λ σ, σ.sign = 1),
  { ext k, split,
    { exact λ H, finset.mem_filter.2 ⟨finset.mem_univ _,
        let ⟨b, hb1, hb2⟩ := finset.mem_map.1 H in
        by rw ← hb2; dsimp only [function.embedding.coe_fn_mk];
        rw [sign_mul, (finset.mem_filter.1 hb1).2, sign_swap H3]; refl⟩ },
    { exact λ H, finset.mem_map.2 ⟨k * swap i j,
        finset.mem_filter.2 ⟨finset.mem_univ _,
          by rw [sign_mul, (finset.mem_filter.1 H).2, sign_swap H3, one_mul]⟩,
        by dsimp only [function.embedding.coe_fn_mk];
        rw [mul_assoc, swap_mul_self, mul_one]⟩ } },
  have H7 : ∀ k, p (swap i j k) = p k,
  { intro k, rw [swap_apply_def], split_ifs; cc },
  rw [H4, finset.sum_union H5],
  refine eq.trans (congr_arg _ (finset.sum_mul_right $ swap i j)) _,
  conv { to_lhs, congr, skip, for (finset.prod _ _) [1] { rw finset.prod_perm (swap i j)}},
  simp [H3, H6, H7]
end

@[simp] lemma det_mul (M N : matrix n n R) :
  det (M * N) = det M * det N :=
begin
  unfold det,
  conv { to_lhs, simp only [mul_val', finset.prod_sum, finset.mul_sum] },
  conv { to_lhs, for (M _ _ * N _ _) [1] { rw @proof_irrel _ x.2 (finset.mem_univ x.1) } },
  rw finset.sum_comm,
  refine (finset.sum_bij (λ (p : Π (a : n), a ∈ univ → n) _, (λ i, p i (finset.mem_univ i) : n → n))
    (λ _ _, finset.mem_univ _) (λ p _, _) _ _).trans _,
  { exact (λ p, finset.sum (univ : finset (perm n))
      (λ σ, e σ * (finset.prod (univ : finset n) (λ x, M (σ x) (p x))
        * finset.prod (univ : finset n) (λ x, N (p x) x)))) },
  { conv { to_lhs, congr, skip, funext,
      rw @finset.prod_attach n R univ _ (λ k, M (x k) (p k _) * N (p k _) k),
      rw finset.prod_mul_distrib } },
  { exact λ _ _ _ _ H, funext (λ i, funext (λ _, have _ := congr_fun H i, this)) },
  { exact λ b _, ⟨λ i _, b i, finset.mem_pi.2 (λ _ _, finset.mem_univ _), rfl⟩ },
  refine (finset.sum_subset (finset.subset_univ (univ.filter function.bijective)) _).symm.trans _,
  { exact λ p _ H, det_mul_aux M N p (mt (λ H2, finset.mem_filter.2 ⟨finset.mem_univ _, H2⟩) H) },
  refine (finset.sum_bij (λ (τ : perm n) (_ : _ ∈ univ) x, τ x)
    (λ τ _, finset.mem_filter.2 ⟨finset.mem_univ _, τ.bijective⟩) _ _ _).symm.trans _,
  { exact (λ τ, e τ * finset.prod (univ : finset n) (λ x, N (τ x) x) *
      finset.sum (univ : finset (perm n))
        (λ σ, e σ * finset.prod (univ : finset n) (λ x, M (σ x) x))) },
  { intros τ _, dsimp only,
    conv { to_lhs, rw [mul_assoc, mul_left_comm, finset.mul_sum],
      congr, skip, rw [univ_sum_mul_right τ⁻¹],
      congr, skip, funext, rw [← mul_assoc, mul_comm (e τ), ← e_mul, inv_mul_cancel_right],
      rw [finset.prod_perm τ],
      simp only [mul_apply, inv_apply_self] },
    conv { to_rhs, congr, skip, funext, rw [← mul_assoc, mul_comm] },
    conv { to_rhs, rw ← finset.mul_sum} },
  { exact λ _ _ _ _ H, perm.ext _ _ (congr_fun H) },
  { exact λ b H, ⟨of_bijective (finset.mem_filter.1 H).2, finset.mem_univ _,
      of_bijective_to_fun (finset.mem_filter.1 H).2⟩ },
  rw [← finset.sum_mul, mul_comm]
end

-- instance : is_monoid_hom (det : matrix n n R → R) :=
-- { map_one := det_one,
--   map_mul := det_mul }

end matrix