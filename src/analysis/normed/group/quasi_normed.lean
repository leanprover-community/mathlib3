import analysis.special_functions.pow
import analysis.normed.group.basic

variable {G : Type*}

open nnreal finset
open_locale nnreal big_operators

namespace quasinormed_group
/-- Given `p : ℝ≥0`, the `inf_p_norm` of an element `g` in an additive group G endowed with a
"norm-map" `∥ ∥ : G → ℝ`, is the infimum over all expressions of `g` as finite sum of `xᵢ`'s, of the
sum of the `p`th powers of the norms of the `xᵢ`'s.
-/
noncomputable
def inf_p_norm [has_norm G] [add_comm_group G] (p : ℝ≥0) : G → ℝ :=
  λ g, ⨅ S : {S : finset G // (S.1.sum) = g}, (∑ xᵢ in S.1, ∥ xᵢ ∥ ^ p.1)

/-- A quasinormed group is an additive, group endowed with a "norm-map" `∥ ∥ : G → ℝ` for which
there exists a `1 < C` such that the norm satisfies the `C`-triangle inequality
`∥ x + y ∥ ≤ C * (max ∥ x ∥ ∥ y ∥))` and such that `dist x y = inf_p_norm ∥x - y∥` defines a
pseudometric space structure for `p` such that `2 ^ p = C`. This is (a generalization to groups of )
the definition of `Δ-norm` found in Kalton--Peck--Roberts, Chap 1, § 2.-/
@[class]
structure quasinormed_add_comm_group (E : Type*)
  extends has_norm E, add_comm_group E, pseudo_metric_space E :=
(const' : ℝ≥0)
(exp' : ℝ≥0)
(rel_C_p : 2 ^ exp'.1 = const')
(C_lt_one : 1 < const')
(C_triangle : ∀ x y : E, ∥ x + y ∥ ≤ const' * (max ∥ x ∥ ∥ y ∥))
(dist_eq : ∀ x y : E, dist x y = inf_p_norm exp' (x - y))

@[protected]
def C (E : Type) [quasinormed_add_comm_group E] : ℝ≥0 := quasinormed_add_comm_group.const' E

@[protected]
def p (E : Type) [quasinormed_add_comm_group E] : ℝ≥0 := quasinormed_add_comm_group.exp' E


-- lemma inf_p_norm_triangle {E : Type} [quasinormed_add_comm_group E] (x y : E) : true :=
-- begin
--   let := (quasinormed_add_comm_group E),
-- end
-- -- inf_p_norm E.p (x + y ) ≤ inf_p_norm E.p x + inf_p_norm E.p y :=

end quasinormed_group
