/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/

import topology.algebra.valuation
import topology.algebra.with_zero_topology
import topology.algebra.uniform_field

/-!
# Valued fields and their completions

In this file we study the topology of a field `K` endowed with a valuation (in our application
to adic spaces, `K` will be the valuation field associated to some valuation on a ring, defined in
valuation.basic).

We already know from valuation.topology that one can build a topology on `K` which
makes it a topological ring.

The first goal is to show `K` is a topological *field*, ie inversion is continuous
at every non-zero element.

The next goal is to prove `K` is a *completable* topological field. This gives us
a completion `hat K` which is a topological field. We also prove that `K` is automatically
separated, so the map from `K` to `hat K` is injective.

Then we extend the valuation given on `K` to a valuation on `hat K`.
-/

section move_to_correct_file

open uniform_space
open_locale topological_space

-- Bourbaki GT III §3 no.4 Proposition 7 [I hope]
lemma filter.has_basis.completion_nhds_zero {G ι : Type*}
  [add_group G] [uniform_space G] [uniform_add_group G] {s : ι → set G} {p : ι → Prop}
  (h : (𝓝 (0 : G)).has_basis p s) :
  (𝓝 (0 : completion G)).has_basis p $ λ i, closure $ coe '' (s i) :=
sorry

end move_to_correct_file

open filter set
open_locale topological_space

section division_ring

variables {K : Type*} [division_ring K] {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]

section valuation_topological_division_ring

section inversion_estimate
variables (v : valuation K Γ₀)

-- The following is the main technical lemma ensuring that inversion is continuous
-- in the topology induced by a valuation on a division ring (ie the next instance)
-- and the fact that a valued field is completable
-- [BouAC, VI.5.1 Lemme 1]
lemma valuation.inversion_estimate {x y : K} {γ : Γ₀ˣ} (y_ne : y ≠ 0)
  (h : v (x - y) < min (γ * ((v y) * (v y))) (v y)) :
  v (x⁻¹ - y⁻¹) < γ :=
begin
  have hyp1 : v (x - y) < γ * ((v y) * (v y)),
    from lt_of_lt_of_le h (min_le_left _ _),
  have hyp1' : v (x - y) * ((v y) * (v y))⁻¹ < γ,
    from mul_inv_lt_of_lt_mul₀ hyp1,
  have hyp2 : v (x - y) < v y,
    from lt_of_lt_of_le h (min_le_right _ _),
  have key : v x = v y, from valuation.map_eq_of_sub_lt v hyp2,
  have x_ne : x ≠ 0,
  { intro h,
    apply y_ne,
    rw [h, v.map_zero] at key,
    exact v.zero_iff.1 key.symm },
  have decomp : x⁻¹ - y⁻¹ = x⁻¹ * (y - x) * y⁻¹,
  by rw [mul_sub_left_distrib, sub_mul, mul_assoc,
        show y * y⁻¹ = 1, from mul_inv_cancel y_ne,
        show x⁻¹ * x = 1, from inv_mul_cancel x_ne, mul_one, one_mul],
  calc
    v (x⁻¹ - y⁻¹) = v (x⁻¹ * (y - x) * y⁻¹) : by rw decomp
    ... = (v x⁻¹) * (v $ y - x) * (v y⁻¹) : by repeat { rw valuation.map_mul }
    ... = (v x)⁻¹ * (v $ y - x) * (v y)⁻¹ : by rw [v.map_inv, v.map_inv]
    ... = (v $ y - x) * ((v y) * (v y))⁻¹ : by
      { rw [mul_assoc, mul_comm, key, mul_assoc, mul_inv_rev₀] }
    ... = (v $ y - x) * ((v y) * (v y))⁻¹ : rfl
    ... = (v $ x - y) * ((v y) * (v y))⁻¹ : by rw valuation.map_sub_swap
    ... < γ : hyp1',
end
end inversion_estimate

open valued

/-- The topology coming from a valuation on a division ring makes it a topological division ring
    [BouAC, VI.5.1 middle of Proposition 1] -/
@[priority 100]
instance valued.topological_division_ring [valued K Γ₀] : topological_division_ring K :=
{ continuous_at_inv₀ :=
    begin
      intros x x_ne s s_in,
      cases valued.mem_nhds.mp s_in with γ hs, clear s_in,
      rw [mem_map, valued.mem_nhds],
      change ∃ (γ : Γ₀ˣ), {y : K | (v (y - x) : Γ₀) < γ} ⊆ {x : K | x⁻¹ ∈ s},
      have vx_ne := (valuation.ne_zero_iff $ v).mpr x_ne,
      let γ' := units.mk0 _ vx_ne,
      use min (γ * (γ'*γ')) γ',
      intros y y_in,
      apply hs,
      simp only [mem_set_of_eq] at y_in,
      rw [units.min_coe, units.coe_mul, units.coe_mul] at y_in,
      exact valuation.inversion_estimate _ x_ne y_in
    end,
  ..(by apply_instance : topological_ring K) }

/-- A valued division ring is separated. -/
@[priority 100]
instance valued_ring.separated [valued K Γ₀] : separated_space K :=
begin
  apply valued.separated_of_zero_sep,
  intros x x_ne,
  refine ⟨{k | v k < v x}, _, λ h, lt_irrefl _ h⟩,
  rw valued.mem_nhds,
  have vx_ne := (valuation.ne_zero_iff $ v).mpr x_ne,
  let γ' := units.mk0 _ vx_ne,
  exact ⟨γ', λ y hy, by simpa using hy⟩,
end

section
local attribute [instance] linear_ordered_comm_group_with_zero.topological_space

open valued

lemma valued.continuous_valuation [valued K Γ₀] : continuous (v : K → Γ₀) :=
begin
  rw continuous_iff_continuous_at,
  intro x,
  classical,
  by_cases h : x = 0,
  { rw h,
    change tendsto _ _ (𝓝 (v (0 : K))),
    erw valuation.map_zero,
    rw linear_ordered_comm_group_with_zero.tendsto_zero,
    intro γ,
    rw valued.mem_nhds_zero,
    use [γ, set.subset.refl _] },
  { change tendsto _ _ _,
    have v_ne : (v x : Γ₀) ≠ 0, from (valuation.ne_zero_iff _).mpr h,
    rw linear_ordered_comm_group_with_zero.tendsto_of_ne_zero v_ne,
    apply valued.loc_const v_ne },
end
end

end valuation_topological_division_ring

end division_ring

namespace valued
open uniform_space

variables {K : Type*} [field K] {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]
  [hv: valued K Γ₀]

include hv

local notation `hat ` := completion

/-- A valued field is completable. -/
@[priority 100]
instance completable : completable_top_field K :=
{ nice := begin
    rintros F hF h0,
    have : ∃ (γ₀ : Γ₀ˣ) (M ∈ F), ∀ x ∈ M, (γ₀ : Γ₀) ≤ v x,
    { rcases filter.inf_eq_bot_iff.mp h0 with ⟨U, U_in, M, M_in, H⟩,
      rcases valued.mem_nhds_zero.mp U_in with ⟨γ₀, hU⟩,
      existsi [γ₀, M, M_in],
      intros x xM,
      apply le_of_not_lt _,
      intro hyp,
      have : x ∈ U ∩ M := ⟨hU hyp, xM⟩,
      rwa H at this },
    rcases this with ⟨γ₀, M₀, M₀_in, H₀⟩,
    rw valued.cauchy_iff at hF ⊢,
    refine ⟨hF.1.map _, _⟩,
    replace hF := hF.2,
    intros γ,
    rcases hF (min (γ * γ₀ * γ₀) γ₀) with ⟨M₁, M₁_in, H₁⟩, clear hF,
    use (λ x : K, x⁻¹) '' (M₀ ∩ M₁),
    split,
    { rw mem_map,
      apply mem_of_superset (filter.inter_mem M₀_in M₁_in),
      exact subset_preimage_image _ _ },
    { rintros _ ⟨x, ⟨x_in₀, x_in₁⟩, rfl⟩ _ ⟨y, ⟨y_in₀, y_in₁⟩, rfl⟩,
      simp only [mem_set_of_eq],
      specialize H₁ x x_in₁ y y_in₁,
      replace x_in₀ := H₀ x x_in₀,
      replace y_in₀ := H₀ y y_in₀, clear H₀,
      apply valuation.inversion_estimate,
      { have : (v x : Γ₀) ≠ 0,
        { intro h, rw h at x_in₀, simpa using x_in₀, },
        exact (valuation.ne_zero_iff _).mp this },
      { refine lt_of_lt_of_le H₁ _,
        rw units.min_coe,
        apply min_le_min _ x_in₀,
        rw mul_assoc,
        have : ((γ₀ * γ₀ : Γ₀ˣ) : Γ₀) ≤ v x * v x,
          from calc ↑γ₀ * ↑γ₀ ≤ ↑γ₀ * v x : mul_le_mul_left' x_in₀ ↑γ₀
                          ... ≤ _ : mul_le_mul_right' x_in₀ (v x),
        rw units.coe_mul,
        exact mul_le_mul_left' this γ } }
  end,
  ..valued_ring.separated }

local attribute [instance] linear_ordered_comm_group_with_zero.topological_space

/-- The extension of the valuation of a valued field to the completion of the field. -/
noncomputable def extension : hat K → Γ₀ :=
completion.dense_inducing_coe.extend (v : K → Γ₀)

lemma continuous_extension : continuous (valued.extension : hat K → Γ₀) :=
 begin
  refine completion.dense_inducing_coe.continuous_extend _,
  intro x₀,
  by_cases h : x₀ = coe 0,
  { refine ⟨0, _⟩,
    erw [h, ← completion.dense_inducing_coe.to_inducing.nhds_eq_comap]; try { apply_instance },
    rw linear_ordered_comm_group_with_zero.tendsto_zero,
    intro γ₀,
    rw valued.mem_nhds,
    exact ⟨γ₀, by simp⟩ },
  { have preimage_one : v ⁻¹' {(1 : Γ₀)} ∈ 𝓝 (1 : K),
    { have : (v (1 : K) : Γ₀) ≠ 0, { rw valuation.map_one, exact zero_ne_one.symm },
      convert valued.loc_const this,
      ext x,
      rw [valuation.map_one, mem_preimage, mem_singleton_iff, mem_set_of_eq] },
    obtain ⟨V, V_in, hV⟩ : ∃ V ∈ 𝓝 (1 : hat K), ∀ x : K, (x : hat K) ∈ V → (v x : Γ₀) = 1,
    { rwa [completion.dense_inducing_coe.nhds_eq_comap, mem_comap] at preimage_one },

    have : ∃ V' ∈ (𝓝 (1 : hat K)), (0 : hat K) ∉ V' ∧ ∀ x y ∈ V', x*y⁻¹ ∈ V,
    { have : tendsto (λ p : hat K × hat K, p.1*p.2⁻¹) ((𝓝 1).prod (𝓝 1)) (𝓝 1),
      { rw ← nhds_prod_eq,
        conv {congr, skip, skip, rw ← (one_mul (1 : hat K))},
        refine tendsto.mul continuous_fst.continuous_at
                           (tendsto.comp _ continuous_snd.continuous_at),
        convert continuous_at_inv₀ (zero_ne_one.symm : 1 ≠ (0 : hat K)),
        exact inv_one.symm },
      rcases tendsto_prod_self_iff.mp this V V_in with ⟨U, U_in, hU⟩,
      let hatKstar := ({0}ᶜ : set $ hat K),
      have : hatKstar ∈ 𝓝 (1 : hat K),
      from compl_singleton_mem_nhds zero_ne_one.symm,
      use  [U ∩ hatKstar, filter.inter_mem U_in this],
      split,
      { rintro ⟨h, h'⟩,
        rw mem_compl_singleton_iff at h',
        exact h' rfl },
      { rintros x ⟨hx, _⟩ y ⟨hy, _⟩,
        apply hU ; assumption } },
    rcases this with ⟨V', V'_in, zeroV', hV'⟩,
    have nhds_right : (λ x, x*x₀) '' V' ∈ 𝓝 x₀,
    { have l : function.left_inverse (λ x : hat K, x * x₀⁻¹) (λ x : hat K, x * x₀),
      { intro x,
        simp only [mul_assoc, mul_inv_cancel h, mul_one] },
      have r: function.right_inverse (λ x : hat K, x * x₀⁻¹) (λ x : hat K, x * x₀),
      { intro x,
        simp only [mul_assoc, inv_mul_cancel h, mul_one] },
      have c : continuous  (λ x : hat K, x * x₀⁻¹),
        from continuous_id.mul continuous_const,
      rw image_eq_preimage_of_inverse l r,
      rw ← mul_inv_cancel h at V'_in,
      exact c.continuous_at V'_in },
    have : ∃ (z₀ : K) (y₀ ∈ V'), coe z₀ = y₀*x₀ ∧ z₀ ≠ 0,
    { rcases completion.dense_range_coe.mem_nhds nhds_right with ⟨z₀, y₀, y₀_in, H : y₀ * x₀ = z₀⟩,
      refine ⟨z₀, y₀, y₀_in, ⟨H.symm, _⟩⟩,
      rintro rfl,
      exact mul_ne_zero (ne_of_mem_of_not_mem y₀_in zeroV') h H },
    rcases this with ⟨z₀, y₀, y₀_in, hz₀, z₀_ne⟩,
    have vz₀_ne: (v z₀ : Γ₀) ≠ 0 := by rwa valuation.ne_zero_iff,
    refine ⟨v z₀, _⟩,
    rw [linear_ordered_comm_group_with_zero.tendsto_of_ne_zero vz₀_ne, mem_comap],
    use [(λ x, x*x₀) '' V', nhds_right],
    intros x x_in,
    rcases mem_preimage.1 x_in with ⟨y, y_in, hy⟩, clear x_in,
    change y*x₀ = coe x at hy,
    have : (v (x*z₀⁻¹) : Γ₀) = 1,
    { apply hV,
      have : ((z₀⁻¹ : K) : hat K) = z₀⁻¹,
      from ring_hom.map_inv (completion.coe_ring_hom : K →+* hat K) z₀,
      rw [completion.coe_mul, this, ← hy, hz₀, mul_inv₀, mul_comm y₀⁻¹, ← mul_assoc, mul_assoc y,
          mul_inv_cancel h, mul_one],
      solve_by_elim },
    calc v x = v (x*z₀⁻¹*z₀) : by rw [mul_assoc, inv_mul_cancel z₀_ne, mul_one]
         ... = v (x*z₀⁻¹)*v z₀ : valuation.map_mul _ _ _
         ... = v z₀ : by rw [this, one_mul]  },
end

@[simp, norm_cast]
lemma extension_extends (x : K) : extension (x : hat K) = v x :=
begin
  haveI : t2_space Γ₀ := regular_space.t2_space _,
  refine completion.dense_inducing_coe.extend_eq_of_tendsto _,
  rw ← completion.dense_inducing_coe.nhds_eq_comap,
  exact valued.continuous_valuation.continuous_at,
end

/-- the extension of a valuation on a division ring to its completion. -/
noncomputable def extension_valuation :
  valuation (hat K) Γ₀ :=
{ to_fun := valued.extension,
  map_zero' := by { rw [← v.map_zero, ← valued.extension_extends (0 : K)], refl, },
  map_one' := by { rw [← completion.coe_one, valued.extension_extends (1 : K)],
                   exact valuation.map_one _ },
  map_mul' := λ x y, begin
    apply completion.induction_on₂ x y,
    { have c1 : continuous (λ (x : hat K × hat K), valued.extension (x.1 * x.2)),
        from valued.continuous_extension.comp (continuous_fst.mul continuous_snd),

      have c2 : continuous (λ (x : hat K × hat K), valued.extension x.1 * valued.extension x.2),
        from (valued.continuous_extension.comp continuous_fst).mul
              (valued.continuous_extension.comp continuous_snd),
      exact is_closed_eq c1 c2 },
    { intros x y,
      norm_cast,
      exact valuation.map_mul _ _ _ },
  end,
  map_add_le_max' := λ x y, begin
    rw le_max_iff,
    apply completion.induction_on₂ x y,
    { have cont : continuous (valued.extension : hat K → Γ₀) := valued.continuous_extension,
      exact  (is_closed_le (cont.comp continuous_add) $ cont.comp continuous_fst).union
        (is_closed_le (cont.comp continuous_add) $ cont.comp continuous_snd) },
    { intros x y,
      dsimp,
      norm_cast,
      rw ← le_max_iff,
      exact v.map_add x y, },
  end }

-- Bourbaki CA VI §5 no.3 Proposition 5 (d) [I hope]
lemma closure_v_lt {γ : Γ₀ˣ} :
  closure (coe '' { x : K | v x < (γ : Γ₀) }) = { x : hat K | extension_valuation x < (γ : Γ₀) } :=
begin
  refine le_antisymm (λ x hx, _) (λ x hx, _),
  { -- TODO Golf this ridiculous proof!
    let γ₀ := extension_valuation x,
    change γ₀ < (γ : Γ₀),
    cases eq_or_ne γ₀ 0,
    { simp [h], },
    { have hγ₀ : is_open ({ γ₀ } : set Γ₀),
      { simp only [is_open_iff_mem_nhds, mem_singleton_iff, forall_eq],
        apply (linear_ordered_comm_group_with_zero.has_basis_nhds_of_ne_zero h).mem_of_mem
          true.intro,
        exact unit.star, },
      let u := (extension_valuation : hat K → Γ₀)⁻¹' { γ₀ },
      have hu : x ∈ u, { simp, },
      obtain ⟨-, hy₁, y, hy₂, rfl⟩ :=
        mem_closure_iff.mp hx u (continuous_extension.is_open_preimage _ hγ₀) hu,
      replace hy₁ : v y = γ₀, { rw ← extension_extends y, simp at hy₁, exact hy₁, },
      rw ← hy₁,
      exact hy₂, }, },
  { -- Oh, it's basically the same argument. OK tidy up later.
    sorry, },
end

noncomputable instance valued_completion : valued (hat K) Γ₀ :=
{ v := valued.extension_valuation,
  is_uniform_valuation := λ s,
  begin
    suffices : has_basis (𝓝 (0 : hat K)) (λ _, true) (λ (γ : Γ₀ˣ),
      { x | valued.extension_valuation x < (γ : Γ₀) }),
    { simp only [uniformity_eq_comap_nhds_zero, mem_comap],
      split,
      { rintros ⟨n, hn, hns⟩,
        obtain ⟨γ, -, hγ⟩ := this.mem_iff.mp hn,
        exact ⟨γ, subset.trans (preimage_mono hγ) hns⟩, },
      { rintros ⟨γ, hγ⟩,
        exact ⟨{ x | valued.extension_valuation x < (γ : Γ₀) },
          this.mem_iff.mpr ⟨γ, trivial, subset.rfl⟩, subset.trans subset.rfl hγ⟩, }, },
    simp_rw ← valued.closure_v_lt,
    exact (valued.has_basis_nhds_zero K Γ₀).completion_nhds_zero,
  end }

end valued
