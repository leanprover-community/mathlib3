/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/

import analysis.convex algebra.quadratic_discriminant analysis.complex.exponential
       analysis.specific_limits
import tactic.monotonicity


/-!
# Inner Product Space

Define inner product space over reals and prove its basic properties.

## Implementation notes

## Tags

inner product space, norm

## References
*  [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
*  [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: http://www.lri.fr/~sboldo/elfic/index.html
-/

noncomputable theory

open real set lattice

universes u v w

variables {α : Type u} {F : Type v} {G : Type w}

class has_inner (α : Type*) := (inner : α → α → ℝ)

export has_inner (inner)

/--
An inner product space is a real vector space with an additional operation called inner product.
Inner product spaces over complex vector space will be defined in another file.
-/
class inner_product_space (α : Type*) extends add_comm_group α, vector_space ℝ α, has_inner α :=
(comm      : ∀ x y, inner x y = inner y x)
(nonneg    : ∀ x, 0 ≤ inner x x)
(definite  : ∀ x, inner x x = 0 → x = 0)
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = r * inner x y)

variable [inner_product_space α]

section basic_properties

lemma inner_comm (x y : α) : inner x y = inner y x := inner_product_space.comm x y

lemma inner_self_nonneg {x : α} : 0 ≤ inner x x := inner_product_space.nonneg _

lemma inner_add_left {x y z : α} : inner (x + y) z = inner x z + inner y z :=
inner_product_space.add_left _ _ _

lemma inner_add_right {x y z : α} : inner x (y + z) = inner x y + inner x z :=
by { rw [inner_comm, inner_add_left], simp [inner_comm] }

lemma inner_smul_left {x y : α} {r : ℝ} : inner (r • x) y = r * inner x y :=
inner_product_space.smul_left _ _ _

lemma inner_smul_right {x y : α} {r : ℝ} : inner x (r • y) = r * inner x y :=
by { rw [inner_comm, inner_smul_left, inner_comm] }

@[simp] lemma inner_zero_left {x : α} : inner 0 x = 0 :=
by { rw [← zero_smul ℝ (0:α), inner_smul_left, zero_mul] }

@[simp] lemma inner_zero_right {x : α} : inner x 0 = 0 :=
by { rw [inner_comm, inner_zero_left] }

lemma inner_self_eq_zero (x : α) : inner x x = 0 ↔ x = 0 :=
iff.intro (inner_product_space.definite _) (by { rintro rfl, exact inner_zero_left })

@[simp] lemma inner_neg_left {x y : α} : inner (-x) y = -inner x y :=
by { rw [← neg_one_smul ℝ x, inner_smul_left], simp }

@[simp] lemma inner_neg_right {x y : α} : inner x (-y) = -inner x y :=
by { rw [inner_comm, inner_neg_left, inner_comm] }

@[simp] lemma inner_neg_neg {x y : α} : inner (-x) (-y) = inner x y := by simp

lemma inner_sub_left {x y z : α} : inner (x - y) z = inner x z - inner y z :=
by { simp [sub_eq_add_neg, inner_add_left] }

lemma inner_sub_right {x y z : α} : inner x (y - z) = inner x y - inner x z :=
by { simp [sub_eq_add_neg, inner_add_right] }

/-- Expand `inner (x + y) (x + y)` -/
lemma inner_add_add_self {x y : α} : inner (x + y) (x + y) = inner x x + 2 * inner x y + inner y y :=
by { simpa [inner_add_left, inner_add_right, two_mul] using inner_comm _ _ }

/-- Expand `inner (x - y) (x - y)` -/
lemma inner_sub_sub_self {x y : α} : inner (x - y) (x - y) = inner x x - 2 * inner x y + inner y y :=
by { simp only [inner_sub_left, inner_sub_right, two_mul], simpa using inner_comm _ _ }

/-- Parallelogram law -/
lemma parallelogram_law {x y : α} :
  inner (x + y) (x + y) + inner (x - y) (x - y) = 2 * (inner x x + inner y y) :=
by { simp [inner_add_add_self, inner_sub_sub_self, two_mul] }

/-- Cauchy–Schwarz inequality -/
lemma inner_mul_inner_self_le (x y : α) : inner x y * inner x y ≤ inner x x * inner y y :=
begin
  have : ∀ t, 0 ≤ inner y y * t * t + 2 * inner x y * t + inner x x, from
    assume t, calc
      0 ≤ inner (x+t•y) (x+t•y) : inner_self_nonneg
      ... = inner y y * t * t + 2 * inner x y * t + inner x x :
        by { simp only [inner_add_add_self, inner_smul_right, inner_smul_left], ring },
  have := discriminant_le_zero this, rw discrim at this,
  have h : (2 * inner x y)^2 - 4 * inner y y * inner x x =
                      4 * (inner x y * inner x y - inner x x * inner y y) := by ring,
  rw h at this,
  linarith
end

end basic_properties

section norm

/-- An inner product naturally induces a norm. -/
instance inner_product_space_has_norm : has_norm α := ⟨λx, sqrt (inner x x)⟩

lemma norm_eq_sqrt_inner {x : α} : ∥x∥ = sqrt (inner x x) := rfl

lemma inner_self_eq_norm_square (x : α) : inner x x = ∥x∥ * ∥x∥ := (mul_self_sqrt inner_self_nonneg).symm

/-- Expand the square -/
lemma norm_add_pow_two {x y : α} : ∥x + y∥^2 = ∥x∥^2 + 2 * inner x y + ∥y∥^2 :=
by { repeat {rw [pow_two, ← inner_self_eq_norm_square]}, exact inner_add_add_self }

/-- Same lemma as above but in a different form -/
lemma norm_add_mul_self {x y : α} : ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + 2 * inner x y + ∥y∥ * ∥y∥ :=
by { repeat {rw [← pow_two]}, exact norm_add_pow_two }

/-- Expand the square -/
lemma norm_sub_pow_two {x y : α} : ∥x - y∥^2 = ∥x∥^2 - 2 * inner x y + ∥y∥^2 :=
by { repeat {rw [pow_two, ← inner_self_eq_norm_square]}, exact inner_sub_sub_self }

/-- Same lemma as above but in a different form -/
lemma norm_sub_mul_self {x y : α} : ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ - 2 * inner x y + ∥y∥ * ∥y∥ :=
by { repeat {rw [← pow_two]}, exact norm_sub_pow_two }

/-- Cauchy–Schwarz inequality with norm -/
lemma abs_inner_le_norm (x y : α) : abs (inner x y) ≤ ∥x∥ * ∥y∥ :=
nonneg_le_nonneg_of_squares_le (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
begin
  rw abs_mul_abs_self,
  have : ∥x∥ * ∥y∥ * (∥x∥ * ∥y∥) = inner x x * inner y y,
    simp only [inner_self_eq_norm_square], ring,
  rw this,
  exact inner_mul_inner_self_le _ _
end

lemma parallelogram_law_with_norm {x y : α} :
  ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥) :=
by { simp only [(inner_self_eq_norm_square _).symm], exact parallelogram_law }

/-- An inner product space forms a normed group w.r.t. its associated norm. -/
instance inner_product_space_is_normed_group : normed_group α :=
normed_group.of_core α
{ norm_eq_zero_iff := assume x, iff.intro
    (λ h : sqrt (inner x x) = 0, (inner_self_eq_zero x).1 $ (sqrt_eq_zero inner_self_nonneg).1 h )
    (by {rintro rfl, show sqrt (inner (0:α) 0) = 0, simp }),
  triangle := assume x y,
  begin
    have := calc
      ∥x + y∥ * ∥x + y∥ = inner (x + y) (x + y) : (inner_self_eq_norm_square _).symm
      ... = inner x x + 2 * inner x y + inner y y : inner_add_add_self
      ... ≤ inner x x + 2 * (∥x∥ * ∥y∥) + inner y y :
        by linarith [abs_inner_le_norm x y, le_abs_self (inner x y)]
      ... = (∥x∥ + ∥y∥) * (∥x∥ + ∥y∥) : by { simp only [inner_self_eq_norm_square], ring },
    exact nonneg_le_nonneg_of_squares_le (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this
  end,
  norm_neg := λx, show sqrt (inner (-x) (-x)) = sqrt (inner x x), by simp }

/-- An inner product space forms a normed space over reals w.r.t. its associated norm. -/
instance inner_product_space_is_normed_space : normed_space ℝ α :=
{ norm_smul := assume r x,
  begin
    rw [norm_eq_sqrt_inner, sqrt_eq_iff_mul_self_eq,
        inner_smul_left, inner_smul_right, inner_self_eq_norm_square],
    exact calc
      abs(r) * ∥x∥ * (abs(r) * ∥x∥) = (abs(r) * abs(r)) * (∥x∥ * ∥x∥) : by ring
      ... = r * (r * (∥x∥ * ∥x∥)) : by { rw abs_mul_abs_self, ring },
    exact inner_self_nonneg,
    exact mul_nonneg (abs_nonneg _) (sqrt_nonneg _)
  end }

end norm

section orthogonal

open filter

/--
Existence of minimizers
Let `u` be a point in an inner product space, and let `K` be a nonempty complete convex subset.
Then there exists a unique `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
 -/
theorem exists_norm_eq_infi_of_complete_convex {K : set α} (ne : nonempty K) (h₁ : is_complete K)
  (h₂ : convex K) : ∀ u : α, ∃ v ∈ K, ∥u - v∥ = ⨅ w : K, ∥u - w∥ := assume u,
begin
  let δ := ⨅ w : K, ∥u - w∥,
  have zero_le_δ : 0 ≤ δ,
    apply le_cinfi, intro, exact norm_nonneg _,
  have δ_le : ∀ w : K, δ ≤ ∥u - w∥,
    assume w, apply cinfi_le, use (0:ℝ), rintros _ ⟨_, rfl⟩, exact norm_nonneg _,
  have δ_le' : ∀ w ∈ K, δ ≤ ∥u - w∥ := assume w hw, δ_le ⟨w, hw⟩,
  -- Step 1: since `δ` is the infimum, can find a sequence `w : ℕ → K` in `K`
  -- such that `∥u - w n∥ < δ + 1 / (n + 1)` (which implies `∥u - w n∥ --> δ`);
  -- maybe this should be a separate lemma
  have exists_seq : ∃ w : ℕ → K, ∀ n, ∥u - w n∥ < δ + 1 / (n + 1),
    have hδ : ∀n:ℕ, δ < δ + 1 / (n + 1), from
      λ n, lt_add_of_le_of_pos (le_refl _) nat.one_div_pos_of_nat,
    have h := λ n, exists_lt_of_cinfi_lt ne (hδ n),
    let w : ℕ → K := λ n, classical.some (h n),
    exact ⟨w, λ n, classical.some_spec (h n)⟩,
  rcases exists_seq with ⟨w, hw⟩,
  have norm_tendsto : tendsto (λ n, ∥u - w n∥) at_top (nhds δ),
    have h : tendsto (λ n:ℕ, δ) at_top (nhds δ),
      exact tendsto_const_nhds,
    have h' : tendsto (λ n:ℕ, δ + 1 / (n + 1)) at_top (nhds δ),
      convert tendsto_add h tendsto_one_div_add_at_top_nhds_0_nat, simp only [add_zero],
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h h'
      (by { rw mem_at_top_sets, use 0, assume n hn, exact δ_le _ })
      (by { rw mem_at_top_sets, use 0, assume n hn, exact le_of_lt (hw _) }),
  -- Step 2: Prove that the sequence `w : ℕ → K` is a Cauchy sequence
  have seq_is_cauchy : cauchy_seq (λ n, ((w n):α)),
    rw cauchy_seq_iff_le_tendsto_0, -- splits into three goals
    let b := λ n:ℕ, (8 * δ * (1/(n+1)) + 4 * (1/(n+1)) * (1/(n+1))),
    use (λn, sqrt (b n)),
    split,
    -- first goal :  `∀ (n : ℕ), 0 ≤ sqrt (b n)`
    assume n, exact sqrt_nonneg _,
    split,
    -- second goal : `∀ (n m N : ℕ), N ≤ n → N ≤ m → dist ↑(w n) ↑(w m) ≤ sqrt (b N)`
    assume p q N hp hq,
    let wp := ((w p):α), let wq := ((w q):α),
    let a := u - wq, let b := u - wp,
    let half := 1 / (2:ℝ), let div := 1 / ((N:ℝ) + 1),
    have : 4 * ∥u - half • (wq + wp)∥ * ∥u - half • (wq + wp)∥ + ∥wp - wq∥ * ∥wp - wq∥ =
      2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) :=
    calc
      4 * ∥u - half•(wq + wp)∥ * ∥u - half•(wq + wp)∥ + ∥wp - wq∥ * ∥wp - wq∥
          = (2*∥u - half•(wq + wp)∥) * (2 * ∥u - half•(wq + wp)∥) + ∥wp-wq∥*∥wp-wq∥ : by ring
      ... = (abs((2:ℝ)) * ∥u - half•(wq + wp)∥) * (abs((2:ℝ)) * ∥u - half•(wq+wp)∥) + ∥wp-wq∥*∥wp-wq∥ :
      by { rw abs_of_nonneg, exact add_nonneg zero_le_one zero_le_one }
      ... = ∥(2:ℝ) • (u - half • (wq + wp))∥ * ∥(2:ℝ) • (u - half • (wq + wp))∥ + ∥wp-wq∥ * ∥wp-wq∥ :
        by { rw [norm_smul], refl }
      ... = ∥a + b∥ * ∥a + b∥ + ∥a - b∥ * ∥a - b∥ :
      begin
        rw [smul_sub, smul_smul, mul_one_div_cancel two_ne_zero, ← one_add_one_eq_two, add_smul],
        simp only [one_smul],
        have eq₁ : wp - wq = a - b, show wp - wq = (u - wq) - (u - wp), abel,
        have eq₂ : u + u - (wq + wp) = a + b, show u + u - (wq + wp) = (u - wq) + (u - wp), abel,
        rw [eq₁, eq₂],
      end
      ... = 2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) : parallelogram_law_with_norm,
    have eq : δ ≤ ∥u - half • (wq + wp)∥,
      rw smul_add,
      apply δ_le', apply h₂,
        repeat {exact subtype.mem _},
        repeat {exact le_of_lt one_half_pos},
        exact add_halves 1,
    have eq₁ : 4 * δ * δ ≤ 4 * ∥u - half • (wq + wp)∥ * ∥u - half • (wq + wp)∥,
      mono, mono, norm_num, apply mul_nonneg, norm_num, exact norm_nonneg _,
    have eq₂ : ∥a∥ * ∥a∥ ≤ (δ + div) * (δ + div) :=
      mul_self_le_mul_self (norm_nonneg _)
        (le_trans (le_of_lt $ hw q) (add_le_add_left (nat.one_div_le_one_div hq) _)),
    have eq₂' : ∥b∥ * ∥b∥ ≤ (δ + div) * (δ + div) :=
      mul_self_le_mul_self (norm_nonneg _)
        (le_trans (le_of_lt $ hw p) (add_le_add_left (nat.one_div_le_one_div hp) _)),
    rw dist_eq_norm,
    apply nonneg_le_nonneg_of_squares_le, { exact sqrt_nonneg _ },
    rw mul_self_sqrt,
    exact calc
      ∥wp - wq∥ * ∥wp - wq∥ = 2 * (∥a∥*∥a∥ + ∥b∥*∥b∥) - 4 * ∥u - half • (wq+wp)∥ * ∥u - half • (wq+wp)∥ :
        by { rw ← this, simp }
      ... ≤ 2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) - 4 * δ * δ : sub_le_sub_left eq₁ _
      ... ≤ 2 * ((δ + div) * (δ + div) + (δ + div) * (δ + div)) - 4 * δ * δ :
        sub_le_sub_right (mul_le_mul_of_nonneg_left (add_le_add eq₂ eq₂') (by norm_num)) _
      ... = 8 * δ * div + 4 * div * div : by ring,
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) zero_le_δ) (le_of_lt nat.one_div_pos_of_nat))
      (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt nat.one_div_pos_of_nat)) (le_of_lt nat.one_div_pos_of_nat)),
    -- third goal : `tendsto (λ (n : ℕ), sqrt (b n)) at_top (nhds 0)`
    apply tendsto.comp,
    { convert continuous_sqrt.continuous_at, exact sqrt_zero.symm },
    have eq₁ : tendsto (λ (n : ℕ), 8 * δ * (1 / (n + 1))) at_top (nhds (0:ℝ)),
      convert tendsto_mul (@tendsto_const_nhds _ _ _ (8 * δ) _) tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero],
    have : tendsto (λ (n : ℕ), (4:ℝ) * (1 / (n + 1))) at_top (nhds (0:ℝ)),
      convert tendsto_mul (@tendsto_const_nhds _ _ _ (4:ℝ) _) tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero],
    have eq₂ : tendsto (λ (n : ℕ), (4:ℝ) * (1 / (n + 1)) * (1 / (n + 1))) at_top (nhds (0:ℝ)),
      convert tendsto_mul this tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero],
    convert tendsto_add eq₁ eq₂, simp only [add_zero],
  -- Step 3: By completeness of `K`, let `w : ℕ → K` converge to some `v : K`.
  -- Prove that it satisfies all requirements.
  rcases cauchy_seq_tendsto_of_is_complete h₁ (λ n, _) seq_is_cauchy with ⟨v, hv, w_tendsto⟩,
  use v, use hv,
  have h_cont : continuous (λ v, ∥u - v∥) :=
    continuous.comp continuous_norm (continuous_sub continuous_const continuous_id),
  have : tendsto (λ n, ∥u - w n∥) at_top (nhds ∥u - v∥),
    convert (tendsto.comp h_cont.continuous_at w_tendsto),
  exact tendsto_nhds_unique at_top_ne_bot this norm_tendsto,
  exact subtype.mem _
end

/-- Characterization of minimizers in the above theorem -/
theorem norm_eq_infi_iff_inner_le_zero {K : set α} (ne : nonempty K) (h : convex K) {u : α} {v : α}
  (hv : v ∈ K) : ∥u - v∥ = (⨅ w : K, ∥u - w∥) ↔ ∀ w ∈ K, inner (u - v) (w - v) ≤ 0 :=
iff.intro
begin
  assume eq w hw,
  let δ := ⨅ w : K, ∥u - w∥, let p := inner (u - v) (w - v), let q := ∥w - v∥^2,
  have zero_le_δ : 0 ≤ δ,
    apply le_cinfi, intro, exact norm_nonneg _,
  have δ_le : ∀ w : K, δ ≤ ∥u - w∥,
    assume w, apply cinfi_le, use (0:ℝ), rintros _ ⟨_, rfl⟩, exact norm_nonneg _,
  have δ_le' : ∀ w ∈ K, δ ≤ ∥u - w∥ := assume w hw, δ_le ⟨w, hw⟩,
  have : ∀θ:ℝ, 0 < θ → θ ≤ 1 → 2 * p ≤ θ * q,
    assume θ hθ₁ hθ₂,
    have : ∥u - v∥^2 ≤ ∥u - v∥^2 - 2 * θ * inner (u - v) (w - v) + θ*θ*∥w - v∥^2 :=
    calc
      ∥u - v∥^2 ≤ ∥u - (θ•w + (1-θ)•v)∥^2 :
      begin
        simp only [pow_two], apply mul_self_le_mul_self (norm_nonneg _),
        rw eq, apply δ_le',
        apply (convex_iff K).1 h hw hv,
        repeat { exact subtype.mem _ },
        exact le_of_lt hθ₁, exact hθ₂,
      end
      ... = ∥(u - v) - θ • (w - v)∥^2 :
      begin
        have : u - (θ•w + (1-θ)•v) = (u - v) - θ • (w - v),
          rw [smul_sub, sub_smul, one_smul], simp,
        rw this
      end
      ... = ∥u - v∥^2 - 2 * θ * inner (u - v) (w - v) + θ*θ*∥w - v∥^2 :
      begin
        rw [norm_sub_pow_two, inner_smul_right, norm_smul],
        simp only [pow_two],
        show ∥u-v∥*∥u-v∥-2*(θ*inner(u-v)(w-v))+abs(θ)*∥w-v∥*(abs(θ)*∥w-v∥)=
                ∥u-v∥*∥u-v∥-2*θ*inner(u-v)(w-v)+θ*θ*(∥w-v∥*∥w-v∥),
        rw abs_of_pos hθ₁, ring
      end,
    have eq₁ : ∥u-v∥^2-2*θ*inner(u-v)(w-v)+θ*θ*∥w-v∥^2=∥u-v∥^2+(θ*θ*∥w-v∥^2-2*θ*inner(u-v)(w-v)), abel,
    rw [eq₁, le_add_iff_nonneg_right] at this,
    have eq₂ : θ*θ*∥w-v∥^2-2*θ*inner(u-v)(w-v)=θ*(θ*∥w-v∥^2-2*inner(u-v)(w-v)), ring,
    rw eq₂ at this,
    have := le_of_sub_nonneg (nonneg_of_mul_nonneg_left this hθ₁),
    exact this,
  by_cases hq : q = 0,
  { rw hq at this,
    have : p ≤ 0,
      have := this (1:ℝ) (by norm_num) (by norm_num),
      linarith,
    exact this },
  { have q_pos : 0 < q,
      apply lt_of_le_of_ne, exact pow_two_nonneg _, intro h, exact hq h.symm,
    by_contradiction hp, rw not_le at hp,
    let θ := min (1:ℝ) (p / q),
    have eq₁ : θ*q ≤ p := calc
      θ*q ≤ (p/q) * q : mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_two_nonneg _)
      ... = p : div_mul_cancel _ hq,
    have : 2 * p ≤ p := calc
      2 * p ≤ θ*q : by { refine this θ (lt_min (by norm_num) (div_pos hp q_pos)) (by norm_num) }
      ... ≤ p : eq₁,
    linarith }
end
begin
  assume h,
  apply le_antisymm,
  { apply le_cinfi, assume w,
    apply nonneg_le_nonneg_of_squares_le (norm_nonneg _),
    have := h w w.2,
    exact calc
      ∥u - v∥ * ∥u - v∥ ≤ ∥u - v∥ * ∥u - v∥ - 2 * inner (u - v) ((w:α) - v) : by linarith
      ... ≤ ∥u - v∥^2 - 2 * inner (u - v) ((w:α) - v) + ∥(w:α) - v∥^2 :
        by { rw pow_two, refine le_add_of_nonneg_right _, exact pow_two_nonneg _ }
      ... = ∥(u - v) - (w - v)∥^2 : norm_sub_pow_two.symm
      ... = ∥u - w∥ * ∥u - w∥ :
        by { have : (u - v) - (w - v) = u - w, abel, rw [this, pow_two] } },
  { show (⨅ (w : K), ∥u - w∥) ≤ (λw:K, ∥u - w∥) ⟨v, hv⟩,
      apply cinfi_le, use 0, rintros y ⟨z, rfl⟩, exact norm_nonneg _ }
end

/--
Existence of minimizers.
Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
Then there exists a unique `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
This point `v` is usually called the orthogonal projection of `u` onto `K`.
-/
theorem exists_norm_eq_infi_of_complete_subspace (K : subspace ℝ α) (ne : nonempty K)
  (h : is_complete (↑K : set α)) : ∀ u : α, ∃ v ∈ K, ∥u - v∥ = ⨅ w : (↑K : set α), ∥u - w∥ :=
exists_norm_eq_infi_of_complete_convex ne h (convex_submodule _)

/--
Characterization of minimizers in the above theorem.
Let `u` be a point in an inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `∥u - v∥` if and only if
for all `w ∈ K`, `inner (u - v) w = 0` (i.e., `u - v` is orthogonal to the subspace `K`)
-/
theorem norm_eq_infi_iff_inner_eq_zero (K : subspace ℝ α) (ne : nonempty K) {u : α} {v : α}
  (hv : v ∈ K) : ∥u - v∥ = (⨅ w : (↑K : set α), ∥u - w∥) ↔ ∀ w ∈ K, inner (u - v) w = 0 :=
iff.intro
begin
  assume h,
  have h : ∀ w ∈ K, inner (u - v) (w - v) ≤ 0,
    rw norm_eq_infi_iff_inner_le_zero at h, exact h, exact ne, exact convex_submodule _, exact hv,
  assume w hw,
  have le : inner (u - v) w ≤ 0,
    let w' := w + v,
    have : w' ∈ K := submodule.add_mem _ hw hv,
    have h₁ := h w' this,
    have h₂ : w' - v = w, simp only [add_neg_cancel_right, sub_eq_add_neg],
    rw h₂ at h₁, exact h₁,
  have ge : inner (u - v) w ≥ 0,
    let w'' := -w + v,
    have : w'' ∈ K := submodule.add_mem _ (submodule.neg_mem _ hw) hv,
    have h₁ := h w'' this,
    have h₂ : w'' - v = -w, simp only [neg_inj', add_neg_cancel_right, sub_eq_add_neg],
    rw [h₂, inner_neg_right] at h₁,
    linarith,
    exact le_antisymm le ge
end
begin
  assume h,
  have : ∀ w ∈ K, inner (u - v) (w - v) ≤ 0,
    assume w hw,
    let w' := w - v,
    have : w' ∈ K := submodule.sub_mem _ hw hv,
    have h₁ := h w' this,
    exact le_of_eq h₁,
  rwa norm_eq_infi_iff_inner_le_zero,
    exact ne, exact convex_submodule _, exact hv
end

end orthogonal
