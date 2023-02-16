import data.nat.choose.sum
import order.filter.basic
import measure_theory.integral.interval_integral
import data.zmod.basic
import data.real.basic
import data.polynomial.basic
import measure_theory.constructions.borel_space
import analysis.normed.group.basic
import order.liminf_limsup

universes u v
open_locale measure_theory classical real big_operators
open filter

/-- Let $a_1 , a_2 , a_3 ,\\ldots$ be a sequence of positive real numbers, define $s_n = \\frac{a_1 +a_2 +\\ldots+a_n }{n}$ and $r_n = \\frac{a_{1}^{-1} +a_{2}^{-1} +\\ldots+a_{n}^{-1} }{n}.$ If  $\\lim_{n\\to \\infty} s_n $ and $\\lim_{n\\to \\infty} r_n $ exist, then the product of these limits is not less than $1.$ -/
theorem lim_prod_le_one_of_lim_sum_lim_inv_sum_exists {a : ℕ → ℝ} (h : ∀ (n : ℕ), 0 < a n)
(h1 : tendsto (λ (n : ℕ), (finset.range n).sum (λ (i : ℕ), a i)) at_top (nhds (liminf at_top (λ (n : ℕ), (finset.range n).sum (λ (i : ℕ), a i)))))
(h2 : tendsto (λ (n : ℕ), (finset.range n).sum (λ (i : ℕ), (a i)⁻¹)) at_top (nhds (liminf at_top (λ (n : ℕ), (finset.range n).sum (λ (i : ℕ), (a i)⁻¹))))) :
(liminf at_top (λ (n : ℕ), (finset.range n).sum (λ (i : ℕ), a i)) * liminf at_top (λ (n : ℕ), (finset.range n).sum (λ (i : ℕ), (a i)⁻¹))) ≤ 1 := sorry
