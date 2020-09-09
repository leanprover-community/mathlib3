import ring_theory.witt_vector.basic
import ring_theory.witt_vector.witt_vector_preps

variables {p : ℕ} [hp : fact p.prime] (n : ℕ) {R : Type*} [comm_ring R]

local notation `𝕎` := witt_vector p -- type as `\bbW`

namespace witt_vector
open mv_polynomial

def init (x : 𝕎 R) (n : ℕ) := mk p (λ k, if k < n then x.coeff k else 0)

def tail (x : 𝕎 R) (n : ℕ) := mk p (λ k, if k < n then 0 else x.coeff k)

include hp

@[simp]
lemma init_init (x : 𝕎 R) (n : ℕ) :
  init (init x n) n = init x n :=
begin
  rw ext_iff,
  intros i,
  simp only [init, coeff_mk],
  split_ifs with hi; refl,
end

lemma init_add (x y : 𝕎 R) (n : ℕ) :
  init (x + y) n = init (init x n + init y n) n :=
begin
  rw ext_iff,
  intros i,
  simp only [init, coeff_mk],
  split_ifs with hi, swap, refl,
  simp only [add_coeff],
  apply eval₂_hom_congr' (ring_hom.ext_int _ _) _ rfl,
  rintro ⟨b, k⟩ h -,
  replace h := witt_add_vars p _ h,
  simp only [finset.mem_range, finset.mem_product, true_and, finset.mem_univ] at h,
  have hk : k < n, by linarith,
  simp only [hk, coeff_mk, if_true],
end

lemma init_mul (x y : 𝕎 R) (n : ℕ) :
  init (x * y) n = init (init x n * init y n) n :=
begin
  rw ext_iff,
  intros i,
  simp only [init, coeff_mk],
  split_ifs with hi, swap, refl,
  simp only [mul_coeff],
  apply eval₂_hom_congr' (ring_hom.ext_int _ _) _ rfl,
  rintro ⟨b, k⟩ h -,
  replace h := witt_mul_vars p _ h,
  simp only [finset.mem_range, finset.mem_product, true_and, finset.mem_univ] at h,
  have hk : k < n, by linarith,
  simp only [hk, coeff_mk, if_true],
end

lemma init_neg (x : 𝕎 R) (n : ℕ) :
  init (-x) n = init (-init x n) n :=
begin
  rw ext_iff,
  intros i,
  simp only [init, coeff_mk],
  split_ifs with hi, swap, refl,
  simp only [neg_coeff],
  apply eval₂_hom_congr' (ring_hom.ext_int _ _) _ rfl,
  rintro ⟨u, k⟩ h -,
  replace h := witt_neg_vars p _ h,
  simp only [finset.mem_range, finset.mem_product, true_and, finset.mem_univ] at h,
  have hk : k < n, by linarith,
  simp only [hk, coeff_mk, if_true],
end

lemma init_sub (x y : 𝕎 R) (n : ℕ) :
  init (x - y) n = init (init x n - init y n) n :=
begin
  simp only [sub_eq_add_neg],
  rw [init_add, init_neg],
  conv_rhs { rw [init_add, init_init] },
end

end witt_vector
