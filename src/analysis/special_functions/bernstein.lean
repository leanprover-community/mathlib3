import data.polynomial.bernstein
import topology.instances.real
import topology.algebra.continuous_functions
import topology.algebra.polynomial
import analysis.normed_space.basic
import topology.bounded_continuous_function
import topology.uniform_space.compact_separated
import algebra.floor

open_locale big_operators

noncomputable theory

open_locale classical

instance {α : Type*} [fintype α] : has_coe (set α) (finset α) :=
⟨λ S, S.to_finset⟩

open_locale bounded_continuous_function

example {X : Type*} [topological_space X] : has_norm (X →ᵇ ℝ) := by apply_instance

-- example {X : Type*} [topological_space X] [compact_space X] : has_norm C(X, ℝ) := by apply_instance

/--
The Bernstein polynomials, as continuous functions on ℝ.
-/
def bernstein' (n ν : ℕ) : C(ℝ, ℝ) :=
⟨λ x, polynomial.aeval x (bernstein_polynomial n ν), by continuity⟩

local notation `I` := set.Icc (0 : ℝ) (1 : ℝ) -- there's some orphaned development in `path_connected`.

example : compact_space I := by apply_instance

/--
The Bernstein polynomials, as bounded continuous functions on `[0,1]`.
-/
def bernstein (n ν : ℕ) : I →ᵇ ℝ :=
bounded_continuous_function.mk_of_compact
(λ x, bernstein' n ν x) (by continuity)

@[simp] lemma bernstein_apply (n ν : ℕ) (x : I) :
  bernstein n ν x = n.choose ν * x^ν * (1-x)^(n-ν) :=
begin
  dsimp [bernstein, bernstein', bernstein_polynomial],
  simp,
end

namespace bernstein

def Z {n : ℕ} (k : fin (n+1)) : I := ⟨(k : ℝ) / n, begin sorry, end⟩

lemma probability (n : ℕ) (x : I) :
  ∑ k : fin (n+1), bernstein n k x = 1 :=
sorry

lemma variance (n : ℕ) (x : I) :
  ∑ k : fin (n+1), (x - Z k : ℝ)^2 * bernstein n k x = x * (1-x) / n :=
sorry

end bernstein

open bernstein

/--
The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials,
given by `∑ k, f (k/n) * bernstein n k x`.
-/
def bernstein_approximation (n : ℕ) (f : I →ᵇ ℝ) : I →ᵇ ℝ :=
∑ k : fin (n+1), f (Z k) • bernstein n k

namespace bernstein_approximation

@[simp] lemma apply (n : ℕ) (f : I →ᵇ ℝ) (x : I) :
  bernstein_approximation n f x = ∑ k : fin (n+1), f (Z k) * bernstein n k x :=
begin
  dsimp [bernstein_approximation],
  simp,
end

def δ (f : I →ᵇ ℝ) (ε : ℝ) (h : 0 < ε) : ℝ :=
classical.some (metric.uniform_continuous_iff.mp begin apply compact_space.uniform_continuous_of_continuous f.2.1, end (ε/2) (half_pos h))

lemma uniform_continuity (f : I →ᵇ ℝ) (ε : ℝ) (h : 0 < ε) {a b : I} (w : dist a b < δ f ε h) : dist (f a) (f b) < ε/2 :=
classical.some_spec (classical.some_spec (metric.uniform_continuous_iff.mp begin apply compact_space.uniform_continuous_of_continuous f.2.1, end (ε/2) (half_pos h))) w

def S (f : I →ᵇ ℝ) (ε : ℝ) (h : 0 < ε) (n : ℕ) (x : I) : finset (fin (n+1)) :=
{ k : fin (n+1) | dist (Z k) x < δ f ε h }.to_finset

lemma lt_of_mem_S {f : I →ᵇ ℝ} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : fin (n+1)} (m : k ∈ S f ε h n x) :
  abs (f (Z k) - f x) < ε/2 :=
begin
  apply uniform_continuity f ε h,
  simpa [S] using m,
end

end bernstein_approximation

open bernstein_approximation

lemma norm_le_of_bound {X Y : Type*} [topological_space X] [nonempty X] [normed_group Y]
  {f : X →ᵇ Y} {M : ℝ} (w : ∀ x, ∥f x∥ ≤ M) : ∥f∥ ≤ M :=
begin
  have z : 0 ≤ M := le_trans (norm_nonneg _) (w (nonempty.some ‹_›)),
  apply real.Inf_le _,
  exact ⟨0, λ y p, p.1⟩,
  exact ⟨z, λ x, by { convert w x, exact dist_zero_right _, }⟩,
end

lemma norm_lt_of_bound
  {X Y : Type*} [topological_space X] [compact_space X] [nonempty X] [normed_group Y]
  {f : X →ᵇ Y} {M : ℝ} (h : ∀ x, ∥f x∥ < M) : ∥f∥ < M :=
begin
  have c : continuous (λ x, ∥f x∥), { have := f.2.1, continuity, },
  obtain ⟨x, -, le⟩ :=
    is_compact.exists_forall_ge compact_univ set.univ_nonempty (continuous.continuous_on c),
  exact lt_of_le_of_lt (norm_le_of_bound (λ y, le y trivial)) (h x),
end

instance : nonempty I := sorry

theorem bernstein_approximation_uniform (f : I →ᵇ ℝ) (ε : ℝ) (h : 0 < ε) :
  ∃ n : ℕ, ∥bernstein_approximation n f - f∥ < ε :=
begin
  let δ := δ f ε h,
  let n : ℕ := _, use n,
  apply norm_lt_of_bound,
  intro x,
  let S := S f ε h n x,
  calc
    abs ((bernstein_approximation n f - f) x)
        = abs (bernstein_approximation n f x - f x)
            : rfl
    ... = abs (bernstein_approximation n f x - f x * 1)
            : by rw mul_one
    ... = abs (bernstein_approximation n f x - f x * (∑ k : fin (n+1), bernstein n k x))
            : by rw bernstein.probability
    ... = abs (bernstein_approximation n f x - (∑ k : fin (n+1), f x * bernstein n k x))
            : by rw finset.mul_sum
    ... = abs (∑ k : fin (n+1), (f (Z k) - f x) * bernstein n k x) :
            begin
              dsimp [bernstein_approximation],
              simp only [bounded_continuous_function.coe_sum, finset.sum_apply,
                ←finset.sum_sub_distrib, bounded_continuous_function.coe_smul,
                algebra.id.smul_eq_mul, ←sub_mul],
            end
    ... ≤ ∑ k : fin (n+1), abs (f (Z k) - f x) * bernstein n k x
            : sorry
    ... = ∑ k in S, abs (f (Z k) - f x) * bernstein n k x +
          ∑ k in Sᶜ, abs (f (Z k) - f x) * bernstein n k x
            : (finset.sum_add_sum_compl S).symm
    ... < ∑ k in S, (ε/2) * bernstein n k x +
          ∑ k in Sᶜ, abs (f (Z k) - f x) * bernstein n k x
            : add_lt_add_right sorry _
    ... = (ε/2) * ∑ k in S, bernstein n k x +
          ∑ k in Sᶜ, abs (f (Z k) - f x) * bernstein n k x
            : by rw finset.mul_sum
    ... ≤ (ε/2) * ∑ k : fin (n+1), bernstein n k x +
          ∑ k in Sᶜ, abs (f (Z k) - f x) * bernstein n k x
            : add_le_add_right sorry _
    ... = (ε/2) + ∑ k in Sᶜ, abs (f (Z k) - f x) * bernstein n k x
            : by rw [bernstein.probability, mul_one]
    ... ≤ (ε/2) + ∑ k in Sᶜ, (2 * ∥f∥) * bernstein n k x
            : add_le_add_left sorry _
    ... = (ε/2) + (2 * ∥f∥) * ∑ k in Sᶜ, bernstein n k x
            : by rw finset.mul_sum
    ... ≤ (ε/2) + (2 * ∥f∥) * ∑ k in Sᶜ, (x - Z k)^2 / δ^2 * bernstein n k x
            : add_le_add_left sorry _
    ... ≤ (ε/2) + (2 * ∥f∥) * ∑ k : fin (n+1), (x - Z k)^2 / δ^2 * bernstein n k x
            : add_le_add_left sorry _
    ... = (ε/2) + (2 * ∥f∥) / δ^2 * ∑ k : fin (n+1), (x - Z k)^2 * bernstein n k x
            : sorry
    ... = (ε/2) + (2 * ∥f∥) / δ^2 * x * (1-x) / n
            : by { rw variance, ring, }
    ... ≤ (ε/2) + (2 * ∥f∥) / δ^2 / n
            : add_le_add_left sorry _
    ... < ε : _, -- We postpone this step for a moment, in order to choose `n`.
  swap,
  exact nat_ceil (4 * ∥f∥ / (δ^2 * ε)),
  dsimp [n],
  sorry,
end
