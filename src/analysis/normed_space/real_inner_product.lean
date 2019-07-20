/-
	Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
	Released under Apache 2.0 license as described in the file LICENSE.
	Authors: Zhouhang Zhou
  -/

import analysis.normed_space.basic
import analysis.normed_space.discriminant

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

universes u v w

variables {α : Type u} {F : Type v} {G : Type w}

class has_inner (α : Type*) := (inner : α → α → ℝ)

export has_inner (inner)

/--
An inner product space is a real vector space with an additional operation called inner product.
Inner product spaces over complex vector space will be defined in another file.
-/
class inner_product_space (α : Type*) [add_comm_group α] [vector_space ℝ α] extends has_inner α :=
(comm      : ∀ x y, inner x y = inner y x)
(nonneg    : ∀ x, 0 ≤ inner x x)
(definite  : ∀ x, inner x x = 0 → x = 0)
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = r * inner x y)

variables [add_comm_group α] [vector_space ℝ α] [inner_product_space α]

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
  have := discriminant_le_zero this,
  have h : 2 * inner x y * (2 * inner x y) - 4 * inner y y * inner x x =
                      4 * (inner x y * inner x y - inner x x * inner y y) := by ring,
  rw h at this,
  linarith
end

end basic_properties

section norm
open real

/-- An inner product naturally induces a norm. -/
instance inner_product_space_has_norm : has_norm α := ⟨λx, sqrt (inner x x)⟩

lemma norm_eq_sqrt_inner {x : α} : ∥x∥ = sqrt (inner x x) := rfl

lemma inner_self_eq_norm_square (x : α) : inner x x = ∥x∥ * ∥x∥ := (mul_self_sqrt inner_self_nonneg).symm

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
