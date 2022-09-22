import analysis.special_functions.pow
import analysis.normed.group.basic
import topology.algebra.filter_basis

universe u

variable {G : Type u}

open nnreal finset topological_space
open_locale nnreal big_operators

namespace quasinormed_add_comm_group
/-- Given `p : ℝ≥0`, the `inf_p_norm` of an element `g` in an additive group G endowed with a
"norm-map" `∥ ∥ : G → ℝ`, is the infimum over all expressions of `g` as finite sum of `xᵢ`'s, of the
sum of the `p`th powers of the norms of the `xᵢ`'s.
-/
noncomputable
def inf_p_norm [has_norm G] [add_comm_group G] (p : ℝ≥0) : G → ℝ :=
  λ g, ⨅ S : {S : finset G // (S.1.sum) = g}, (∑ xᵢ in S.1, ∥ xᵢ ∥ ^ p.1)

@[simp]
lemma zero_inf_p_norm [has_norm G] [add_comm_group G] (p : ℝ≥0) : inf_p_norm p (0 : G)  = 0 := sorry

@[simp]
lemma inf_p_norm_sub [has_norm G] [add_comm_group G] (p : ℝ≥0) (g : G) :
  inf_p_norm p (-g) = inf_p_norm p g := sorry
/-- A quasinormed group is an additive, group endowed with a "norm-map" `∥ ∥ : G → ℝ` for which
there exists a `1 < C` such that the norm satisfies the `C`-triangle inequality
`∥ x + y ∥ ≤ C * (max ∥ x ∥ ∥ y ∥))` and such that `dist x y = inf_p_norm ∥x - y∥` defines a
pseudometric space structure for `p` such that `2 ^ p = C`. This is (a generalization to groups of)
the definition of `Δ-norm` found in Kalton--Peck--Roberts, Chap 1, § 2.

With respect to the approach taken *ibid.* we dot not consider the topology *defined* by the
quasinorm, so in particular we do not show that it is equivalent to that defined by the
`inf_p_norm`. Rather, we define a distance on the space through this `inf_p_norm` and we deduce the
according topology. The approaches are equivalent thanks to Kalton--Peck--Robert, Theorem 1.2
-/
@[class]
structure quasinormed_add_comm_group (E : Type u)
  extends has_norm E, add_comm_group E, metric_space E :=
(const' : ℝ≥0)
(exp' : ℝ≥0)
(rel_C_p : 2 ^ exp'.1 = const')
(C_lt_one : 1 < const')
(C_triangle : ∀ x y : E, ∥ x + y ∥ ≤ const' * (max ∥ x ∥ ∥ y ∥))
(dist_eq : ∀ x y : E, dist x y = inf_p_norm exp' (x - y))

@[protected]
def C (E : Type u) [quasinormed_add_comm_group E] : ℝ≥0 := quasinormed_add_comm_group.const' E

@[protected]
def p (E : Type u) [quasinormed_add_comm_group E] : ℝ≥0 := quasinormed_add_comm_group.exp' E

lemma two_pow_p_eq_C (E : Type u) [quasinormed_add_comm_group E] : 2 ^ (p E).1 = C E :=
  quasinormed_add_comm_group.rel_C_p

instance topological_add_group.to_pseudo_metric_space (G : Type u) [topological_space G]
  [add_comm_group G] [topological_add_group G] [first_countable_topology G] :
  pseudo_metric_space G :=
begin
  choose u₀ h_basis_u h_incl_u using topological_add_group.exists_antitone_basis_nhds_zero G,
  -- let u := add_group_filter_basis_of_comm u₀,
  letI : has_norm G := ⟨λ x, ↑(Sup {n : ℕ | x ∉ u n})⟩,
  letI : has_dist G := ⟨λ x y, inf_p_norm 1 ∥ x - y ∥⟩,
  apply pseudo_metric_space.mk,
  { intro x,
    have : ∀ n : ℕ, (0 : G) ∈ u n,
    { intro,
      replace h_basis_u := ((h_basis_u).1.1 (u n)).mpr ⟨n, by {simp [exists_true_left]}⟩,
      obtain ⟨s, h_incl_s, -, zero_mem_s⟩ := mem_nhds_iff.mp h_basis_u,
      exact h_incl_s zero_mem_s },
    simp only [sub_self, this, not_true, set.set_of_false, cSup_empty, bot_eq_zero', nat.cast_zero,
      zero_inf_p_norm] },
  { intros x y,
    simp only,
    congr,
    ext n,
    sorry, --here it is needed that the `u n` are **balanced**
  },
  { intros x y z,
    simp,

  },
end
-- { dist :=
--   begin
--     choose u₁ h_basis_u₁ h_incl_u₁ using topological_add_group.exists_antitone_basis_nhds_zero E,
--     let norm' : E → ℝ := λ x, ↑(Sup {n : ℕ | x ∉ u₁ n}),
--     haveI : has_norm E := ⟨norm'⟩,
--     use λ x y, inf_p_norm 1 ∥ x - y ∥,
--   end,
--   dist_self :=
--   begin
--     intro x,
--     -- dsimp [dist],
--     simp,
--     rw sub_self,
--     -- have :=
--   end,
--   dist_comm := _,
--   dist_triangle := _,
--   edist := _,
--   edist_dist := _,
--   to_uniform_space := _,
--   uniformity_dist := _,
--   to_bornology := _,
--   cobounded_sets := _ }

instance topological_add_group.to_quasinormed_add_comm_group (E : Type u) [topological_space E]
  [add_comm_group E] [topological_add_group E] [second_countable_topology E] :
  quasinormed_add_comm_group E :=
begin
  -- begin
  -- let u₂ := (topological_space.exists_countable_basis E).some,
  -- have ovvio1 : countable u₂,
  -- { exact set.countable_coe_iff.mpr (topological_space.exists_countable_basis E).some_spec.1 },
  choose u₁ h_basis_u₁ h_incl_u₁ using topological_add_group.exists_antitone_basis_nhds_zero E,
  let norm' : E → ℝ := λ x, ↑(Sup {n : ℕ | x ∉ u₁ n}),
  haveI : has_norm E := ⟨norm'⟩,
  let dist' : E → E → ℝ := λ x y, inf_p_norm 1 ∥ x - y ∥,
  haveI : has_dist E := ⟨dist'⟩,
  haveI : pseudo_metric_space E,
  apply pseudo_metric_space.mk,
  apply quasinormed_add_comm_group.mk,
end

lemma inf_p_norm_triangle {E : Type} [quasinormed_add_comm_group E] (x y : E) :
  inf_p_norm (p E) (x + y) ≤ inf_p_norm (p E) x + inf_p_norm (p E) y :=
begin
  sorry
end

lemma coutable_basis_to_quasinormed_add_comm_group :

end quasinormed_add_comm_group
