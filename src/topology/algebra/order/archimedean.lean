import topology.algebra.order.basic
import algebra.order.archimedean

variables {𝕜 : Type*} [linear_ordered_field 𝕜] [topological_space 𝕜] [order_topology 𝕜]
  [archimedean 𝕜]

lemma rat.dense_range_cast : dense_range (coe : ℚ → 𝕜) :=
dense_of_exists_between $ λ a b h, set.exists_range_iff.2 $ exists_rat_btwn h
