import number_theory.dirichlet_character
import data.zmod.algebra
import analysis.normed_space.basic
import topology.algebra.group
import topology.continuous_function.compact

/-- Making `zmod` a discrete topological space. -/
def zmod.topological_space' (d : ℕ) : topological_space (zmod d) := ⊥

local attribute [instance] zmod.topological_space'
open_locale big_operators
instance (α : Type*) [topological_space α] [discrete_topology α] : discrete_topology αᵒᵖ :=
discrete_topology_induced opposite.unop_injective

/-- Like disc_top_units but includes k = 0. -/
lemma disc_top_units' (k : ℕ) : discrete_topology (units (zmod k)) :=
begin
  convert @discrete_topology_induced _ _ _ _ _ (embed_product_injective _),
  apply @prod.discrete_topology _ _ infer_instance infer_instance infer_instance infer_instance,
  any_goals { apply_instance, },
end

open dirichlet_character

lemma dirichlet_character.continuous {R : Type*} [monoid R] [topological_space R]
  {n : ℕ} (χ : dirichlet_character R n) : continuous χ :=
begin
  convert continuous_of_discrete_topology,
  exact disc_top_units' _,
end

lemma dirichlet_character.asso_dirichlet_character_continuous
  {R : Type*} [monoid_with_zero R] [topological_space R] {n : ℕ} (χ : dirichlet_character R n) :
  continuous (asso_dirichlet_character χ) :=
begin
  convert continuous_of_discrete_topology,
  apply_instance,
end

lemma dirichlet_character.asso_dirichlet_character_bounded {R : Type*} [monoid_with_zero R]
  [normed_group R] {n : ℕ} [fact (0 < n)] (χ : dirichlet_character R n) : ∃ M : ℝ,
  ∥ (⟨asso_dirichlet_character χ,
    dirichlet_character.asso_dirichlet_character_continuous χ⟩ : C(zmod n, R)) ∥ < M :=
begin
  refine ⟨(⨆ i : zmod n, ∥asso_dirichlet_character χ i∥) + 1, _⟩,
  apply lt_of_le_of_lt _ (lt_add_one _),
  { convert le_refl _,
    rw continuous_map.norm_eq_supr_norm,
    simp only [continuous_map.coe_mk], },
  { apply_instance, },
end

lemma asso_dirichlet_character_zero_range {R : Type*} [monoid_with_zero R] [normed_group R]
  (χ : dirichlet_character R 0) : (set.range (λ (i : zmod 0), ∥(asso_dirichlet_character χ) i∥)) =
    {∥asso_dirichlet_character χ 0∥, ∥asso_dirichlet_character χ 1∥,
      ∥asso_dirichlet_character χ (-1)∥} :=
begin
  ext,
  simp only [set.mem_insert_iff, set.mem_range, set.mem_singleton_iff],
  refine ⟨λ h, _, λ h, _⟩,
  { cases h with y hy,
    by_cases is_unit y,
    { suffices h' : y = 1 ∨ y = -1,
      { cases h',
        { rw h' at hy,
          right, left, rw ←hy, },
        { rw h' at hy,
          right, right, rw hy, }, },
      { apply int.is_unit_eq_one_or h, }, },
    rw asso_dirichlet_character_eq_zero _ h at hy,
    left, rw ←hy,
    rw asso_dirichlet_character_eq_zero _,
    apply @not_is_unit_zero _ _ infer_instance,
    change nontrivial ℤ, apply_instance, },
  { cases h,
    { refine ⟨0, _⟩, rw h, },
    { cases h,
      { rw h, refine ⟨1, rfl⟩, },
      { rw h, refine ⟨-1, rfl⟩, }, }, },
end

lemma asso_dirichlet_character_zero_range_fin {R : Type*} [monoid_with_zero R] [normed_group R]
  (χ : dirichlet_character R 0) :
  (set.range (λ (i : zmod 0), ∥(asso_dirichlet_character χ) i∥)).finite :=
begin
  rw asso_dirichlet_character_zero_range,
  simp only [set.finite_singleton, set.finite.insert],
end

lemma asso_dirichlet_character_range_fin {R : Type*} [monoid_with_zero R] [normed_group R] {n : ℕ}
  (χ : dirichlet_character R n) :
  (set.range (λ (i : zmod n), ∥(asso_dirichlet_character χ) i∥)).finite :=
begin
  cases n, -- big improvement over by_cases n!
  { apply asso_dirichlet_character_zero_range_fin _, },
  { haveI : fact (0 < n.succ) := fact_iff.2 (nat.succ_pos _),
    exact set.finite_range (λ (i : zmod n.succ), ∥(asso_dirichlet_character χ) i∥), },
end

lemma asso_dirichlet_character_range_bdd_above {R : Type*} [monoid_with_zero R] [normed_group R]
  {n : ℕ} (χ : dirichlet_character R n) :
  bdd_above (set.range (λ (i : zmod n), ∥(asso_dirichlet_character χ) i∥)) :=
set.finite.bdd_above (asso_dirichlet_character_range_fin _)

lemma dirichlet_character.asso_dirichlet_character_bounded_spec
  {R : Type*} [monoid_with_zero R] [normed_group R] {n : ℕ}
  (χ : dirichlet_character R n) : ∃ M : ℝ, (∀ a, ∥asso_dirichlet_character χ a∥ < M) ∧ 0 < M :=
begin
  refine ⟨(⨆ i : zmod n, ∥asso_dirichlet_character χ i∥) + 1, λ a, lt_of_le_of_lt _
    (lt_add_one _), (lt_add_of_le_of_pos _ _)⟩,
  { apply le_cSup (asso_dirichlet_character_range_bdd_above _) (⟨a, rfl⟩), },
  { apply le_csupr_of_le _ _,
    swap 3, { exact 1, },
    { apply norm_nonneg _, },
    { apply asso_dirichlet_character_range_bdd_above, }, },
  { norm_num, },
end

/-- Every Dirichlet character is bounded above. -/
noncomputable abbreviation dirichlet_character.bound {R : Type*} [monoid_with_zero R]
  [normed_group R] {n : ℕ} (χ : dirichlet_character R n) : ℝ :=
classical.some (dirichlet_character.asso_dirichlet_character_bounded_spec χ)

lemma dirichlet_character.lt_bound {R : Type*} [monoid_with_zero R] [normed_group R] {n : ℕ}
  (χ : dirichlet_character R n) (a : zmod n) :
  ∥asso_dirichlet_character χ a∥ < dirichlet_character.bound χ :=
(classical.some_spec (dirichlet_character.asso_dirichlet_character_bounded_spec χ)).1 a

lemma dirichlet_character.bound_pos {R : Type*} [monoid_with_zero R] [normed_group R] {n : ℕ}
  (χ : dirichlet_character R n) : 0 < dirichlet_character.bound χ :=
(classical.some_spec (dirichlet_character.asso_dirichlet_character_bounded_spec χ)).2
