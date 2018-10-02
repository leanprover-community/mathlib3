/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import tactic.tidy
import group_theory.subgroup
import group_theory.perm
import data.finset
import ring_theory.matrix

universes u v

lemma finset.prod_mul_right {α} [group α]
  {β} [comm_monoid β] {f : α → β} {s : finset α} (x : α) :
  s.prod f =
  (s.map ⟨λ z, z * x⁻¹, λ _ _, mul_right_cancel⟩).prod (λ z, f (z * x)) :=
finset.prod_bij (λ z _, z * x⁻¹) (λ _ _, by simpa) (λ _ _, by simp)
  (λ _ _ _ _, mul_right_cancel) (λ b H,
    ⟨b * x, by revert H; simp [eq_comm] {contextual:=tt}, by simp⟩)

lemma finset.sum_mul_right {α} [group α]
  {β} [add_comm_monoid β] {f : α → β} {s : finset α} (x : α) :
  s.sum f =
  (s.map ⟨λ z, z * x⁻¹, λ _ _, mul_right_cancel⟩).sum (λ z, f (z * x)) :=
finset.sum_bij (λ z _, z * x⁻¹) (λ _ _, by simpa) (λ _ _, by simp)
  (λ _ _ _ _, mul_right_cancel) (λ b H,
    ⟨b * x, by revert H; simp [eq_comm] {contextual:=tt}, by simp⟩)

lemma finset.univ_sum_mul_right {α} [group α] [fintype α]
  {β} [add_comm_monoid β] {f : α → β} (x : α) :
  finset.univ.sum f =
  finset.univ.sum (λ z, f (z * x)) :=
finset.sum_bij (λ z _, z * x⁻¹) (λ _ _, finset.mem_univ _) (λ _ _, by simp)
  (λ _ _ _ _, mul_right_cancel) (λ b H,
    ⟨b * x, by revert H; simp [eq_comm] {contextual:=tt}, by simp⟩)

lemma finset.prod_perm {α} [fintype α] [decidable_eq α]
  {β} [comm_monoid β] {f : α → β} (σ : equiv.perm α) :
  (finset.univ : finset α).prod f
  = finset.univ.prod (λ z, f (σ z)) :=
eq.symm $ finset.prod_bij (λ z _, σ z) (λ _ _, finset.mem_univ _) (λ _ _, rfl)
  (λ _ _ _ _ H, σ.bijective.1 H) (λ b _, ⟨σ⁻¹ b, finset.mem_univ _, by simp⟩)

instance {α} (H : α → Prop) : subsingleton (decidable_pred H) :=
by apply_instance

@[simp] lemma finset.filter_true {α} (s : finset α) [h : decidable_pred (λ _, true)] :
  @finset.filter α (λ _, true) h s = s :=
by ext; simp

namespace matrix
open equiv
variables {n : Type u} [fintype n] [decidable_eq n] {R : Type v} [comm_ring R]

instance : group (equiv.perm n) := by apply_instance

@[simp] lemma equiv.swap_mul_self (i j : n) : equiv.swap i j * equiv.swap i j = 1 :=
equiv.swap_swap i j

@[simp] lemma equiv.swap_swap_apply (i j k : n) : equiv.swap i j (equiv.swap i j k) = k :=
equiv.swap_core_swap_core k i j

instance : decidable_pred (function.bijective : (n → n) → Prop) :=
λ _, by unfold function.bijective; apply_instance

instance bij_fintype : fintype {f : n → n // function.bijective f} := 
set_fintype _

@[extensionality] theorem equiv.perm.ext (σ τ : equiv.perm n)
  (H : ∀ i, σ i = τ i) : σ = τ :=
equiv.ext _ _ H

@[simp] lemma equiv.perm.sign_mul (σ τ : equiv.perm n) :
  (σ * τ).sign = σ.sign * τ.sign :=
is_group_hom.mul _ _ _

@[simp] lemma equiv.perm.sign_one :
  equiv.perm.sign (1 : equiv.perm n) = 1 :=
is_group_hom.one _

@[simp] lemma equiv.perm.sign_refl :
  equiv.perm.sign (equiv.refl n) = 1 :=
is_group_hom.one equiv.perm.sign

@[simp] lemma equiv.perm.sign_swap' {i j : n} :
  (equiv.swap i j).sign = if i = j then 1 else -1 :=
if H : i = j then by simp [H, equiv.swap_self] else
by simp [equiv.perm.sign_swap H, H]

def e (σ : equiv.perm n) : R := ((σ.sign : ℤ) : R)

@[simp] lemma e_mul (σ τ : equiv.perm n) : (e (σ * τ) : R) = e σ * e τ :=
by unfold e; rw ← int.cast_mul; congr; rw ← units.mul_coe; congr; apply is_group_hom.mul

@[simp] lemma e_swap {i j : n} : (e (equiv.swap i j) : R) = if i = j then 1 else -1 :=
by by_cases H : i = j; simp [e, H]

@[simp] lemma e_one : (e (1 : equiv.perm n) : R) = 1 :=
by unfold e; rw is_group_hom.one (equiv.perm.sign : equiv.perm n → units ℤ); simp

@[simp] lemma e_inv (σ : equiv.perm n): (e σ⁻¹ : R) = e σ :=
by unfold e; rw is_group_hom.inv (equiv.perm.sign : equiv.perm n → units ℤ);
cases int.units_eq_one_or σ.sign with H H; rw H; refl

lemma e_eq_one_or (σ : equiv.perm n) : (e σ : R) = 1 ∨ (e σ : R) = -1 :=
by cases int.units_eq_one_or σ.sign with H H; unfold e; rw H; simp

definition det (M : matrix n n R) : R :=
finset.univ.sum (λ (σ : equiv.perm n),
(e σ) * finset.univ.prod (λ (i:n), M (σ i) i))

@[simp] lemma det_diagonal {d : n → R} : det (diagonal d) = finset.univ.prod d :=
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
  finset.sum (finset.univ : finset (equiv.perm n))
    (λ σ, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
      * finset.prod (finset.univ : finset n) (λ x, N (p x) x))) = 0 :=
begin
  have H1 : ¬function.injective p,
    from mt (λ h, and.intro h $ fintype.injective_iff_surjective.1 h) H,
  unfold function.injective at H1, simp only [not_forall] at H1,
  rcases H1 with ⟨i, j, H2, H3⟩,
  have H4 : (finset.univ : finset (equiv.perm n)) = finset.univ.filter (λ σ, σ.sign = 1) ∪ finset.univ.filter (λ σ, σ.sign = -1),
  { rw [← finset.filter_or], simp only [int.units_eq_one_or],
    ext k, simp only [finset.mem_univ, finset.mem_filter, true_and] },
  have H5 : (finset.univ : finset (equiv.perm n)).filter (λ σ, σ.sign = 1) ∩ finset.univ.filter (λ σ, σ.sign = -1) = ∅,
  { rw [← finset.filter_and], refine finset.eq_empty_of_forall_not_mem (λ _ H, _),
    rw finset.mem_filter at H, exact absurd (H.2.1.symm.trans H.2.2) dec_trivial },
  have H6 : finset.map ⟨λ z, z * equiv.swap i j, λ _ _, mul_right_cancel⟩
    (finset.univ.filter (λ σ, σ.sign = -1))
    = finset.univ.filter (λ σ, σ.sign = 1),
  { ext k, split,
    { exact λ H, finset.mem_filter.2 ⟨finset.mem_univ _,
        let ⟨b, hb1, hb2⟩ := finset.mem_map.1 H in
        by rw ← hb2; dsimp only [function.embedding.coe_fn_mk];
        rw [equiv.perm.sign_mul, (finset.mem_filter.1 hb1).2, equiv.perm.sign_swap H3]; refl⟩ },
    { exact λ H, finset.mem_map.2 ⟨k * equiv.swap i j,
        finset.mem_filter.2 ⟨finset.mem_univ _,
          by rw [equiv.perm.sign_mul, (finset.mem_filter.1 H).2, equiv.perm.sign_swap H3, one_mul]⟩,
        by dsimp only [function.embedding.coe_fn_mk];
        rw [mul_assoc, equiv.swap_mul_self, mul_one]⟩ } },
  have H7 : ∀ k, p (equiv.swap i j k) = p k,
  { intro k, rw [equiv.swap_apply_def], split_ifs; cc },
  rw [H4, finset.sum_union H5],
  refine eq.trans (congr_arg _ (finset.sum_mul_right $ equiv.swap i j)) _,
  conv { to_lhs, congr, skip, for (finset.prod _ _) [1] { rw finset.prod_perm (equiv.swap i j)}},
  simp [H3, H6, H7]
end

@[simp] lemma det_mul (M N : matrix n n R) :
  det (M * N) = det M * det N :=
begin
  unfold det,
  conv { to_lhs, simp only [mul_val', finset.prod_sum, finset.mul_sum] },
  conv { to_lhs, for (M _ _ * N _ _) [1] { rw @proof_irrel _ x.2 (finset.mem_univ x.1) } },
  rw finset.sum_comm,
  refine (finset.sum_bij (λ (p : Π (a : n), a ∈ finset.univ → n) _, (λ i, p i (finset.mem_univ i) : n → n))
    (λ _ _, finset.mem_univ _) (λ p _, _) _ _).trans _,
  { exact (λ p, finset.sum (finset.univ : finset (equiv.perm n))
      (λ σ, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
        * finset.prod (finset.univ : finset n) (λ x, N (p x) x)))) },
  { conv { to_lhs, congr, skip, funext,
      rw @finset.prod_attach n R finset.univ _ (λ k, M (x k) (p k _) * N (p k _) k),
      rw finset.prod_mul_distrib } },
  { exact λ _ _ _ _ H, funext (λ i, funext (λ _, have _ := congr_fun H i, this)) },
  { exact λ b _, ⟨λ i _, b i, finset.mem_pi.2 (λ _ _, finset.mem_univ _), rfl⟩ },
  refine (finset.sum_subset (finset.subset_univ (finset.univ.filter function.bijective)) _).symm.trans _,
  { exact λ p _ H, det_mul_aux M N p (mt (λ H2, finset.mem_filter.2 ⟨finset.mem_univ _, H2⟩) H) },
  refine (finset.sum_bij (λ (τ : equiv.perm n) (_ : _ ∈ finset.univ) x, τ x)
    (λ τ _, finset.mem_filter.2 ⟨finset.mem_univ _, τ.bijective⟩) _ _ _).symm.trans _,
  { exact (λ τ, e τ * finset.prod (finset.univ : finset n) (λ x, N (τ x) x) *
      finset.sum (finset.univ : finset (equiv.perm n))
        (λ σ, e σ * finset.prod (finset.univ : finset n) (λ x, M (σ x) x))) },
  { intros τ _, dsimp only,
    conv { to_lhs, rw [mul_assoc, mul_left_comm, finset.mul_sum],
      congr, skip, rw [finset.univ_sum_mul_right τ⁻¹],
      congr, skip, funext, rw [← mul_assoc, mul_comm (e τ), ← e_mul, inv_mul_cancel_right],
      rw [finset.prod_perm τ],
      simp only [equiv.perm.mul_apply, equiv.perm.inv_apply_self] },
    conv { to_rhs, congr, skip, funext, rw [← mul_assoc, mul_comm] },
    conv { to_rhs, rw ← finset.mul_sum} },
  { exact λ _ _ _ _ H, equiv.perm.ext _ _ (congr_fun H) },
  { exact λ b H, ⟨equiv.of_bijective (finset.mem_filter.1 H).2, finset.mem_univ _,
      equiv.of_bijective_to_fun (finset.mem_filter.1 H).2⟩ },
  rw [← finset.sum_mul, mul_comm]
end

-- instance : is_monoid_hom (det : matrix n n R → R) :=
-- { map_one := det_one,
--   map_mul := det_mul }

end matrix