import group_theory.subgroup.basic
import data.real.basic
import topology.order
import topology.algebra.group.basic
import topology.constructions
import topology.instances.real
import linear_algebra.free_module.basic
import linear_algebra.free_module.pid
import analysis.normed.group.basic
import linear_algebra.finite_dimensional
import analysis.normed_space.basic

open_locale classical

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]

section approx

variables {α : Type*} [fintype α] {v : α → E}

noncomputable def floor_approx
  (hv : linear_independent ℝ v)
  (m : submodule.span ℝ (set.range v)) : E :=
begin
  let s := hv.repr m,
  let z := finset.univ.sum (λ j : α, int.floor(s j) • (v j)),
  exact z,
end

lemma linear_independent.repr_sum
  (hv : linear_independent ℝ v) (m : submodule.span ℝ (set.range v)) :
  finset.univ.sum (λ i, ((hv.repr) m) i • v i) = m :=
begin
  have := hv.total_repr m,
  rwa [finsupp.total_apply, finsupp.sum_fintype _ _ _] at this,
  simp only [zero_smul, eq_self_iff_true, implies_true_iff],
end

lemma sub_floor_approx_le (hv : linear_independent ℝ v) (m : submodule.span ℝ (set.range v)) :
  ‖(m : E) - (floor_approx hv m)‖ ≤ finset.univ.sum (λ j : α, ‖v j‖) :=
begin
  calc
    ‖(m : E) - (floor_approx hv m)‖
        = ‖finset.univ.sum (λ i, ((hv.repr) m) i • v i) - (floor_approx hv m)‖
          : by rw ← toto
    ... = ‖finset.univ.sum (λ i, ((hv.repr) m) i • v i) -
            finset.univ.sum (λ j, ⌊((hv.repr) m) j⌋ • v j)‖
          : by rw floor_approx
    ... = ‖finset.univ.sum (λ j, ((hv.repr) m) j • v j - ⌊((hv.repr) m) j⌋ • v j)‖
          : by rw [← finset.sum_sub_distrib]
    ... = ‖finset.univ.sum (λ j, ((hv.repr) m) j • v j - (⌊((hv.repr) m) j⌋ : ℝ) • v j)‖
          : by simp_rw zsmul_eq_smul_cast ℝ _ _
    ... = ‖finset.univ.sum (λ j, (((hv.repr) m) j - (⌊((hv.repr) m) j⌋ : ℝ))• v j)‖
          : by simp_rw ← sub_smul
    ... ≤ finset.univ.sum (λ j, ‖(((hv.repr) m) j - (⌊((hv.repr) m) j⌋ : ℝ))• v j‖)
          : norm_sum_le _ _
    ... ≤ finset.univ.sum (λ j, |((hv.repr) m) j - (⌊((hv.repr) m) j⌋ : ℝ)| * ‖v j‖)
          : by simp_rw [norm_smul, real.norm_eq_abs]
    ... ≤ finset.univ.sum (λ j : α, ‖v j‖) : finset.sum_le_sum _,
  intros j _,
  rw int.self_sub_floor,
  rw int.abs_fract,
  refine le_trans (mul_le_mul_of_nonneg_right (le_of_lt (int.fract_lt_one _)) (norm_nonneg _)) _,
  rw one_mul,
end

lemma floor_approx_mem (hv : linear_independent ℝ v) (m : submodule.span ℝ (set.range v))
  (L : add_subgroup E) (h : ∀ i, v i ∈ L) :
  floor_approx hv m ∈ L := sum_mem (λ j _, zsmul_mem (h j) _)

lemma linear_dependent_of_sub_eq
  (hv : linear_independent ℝ v) (m n : submodule.span ℝ (set.range v))
  (h : (m : E) - floor_approx hv m = (n : E) - floor_approx hv n) :
  ∃ f : α → ℤ, (m - n : E) = finset.univ.sum (λ j, f j • (v j)) :=
begin
  have : ∀ j, ∃ s : ℤ, (hv.repr m j) - (hv.repr n j) = s,
  { suffices : ∀ i,  (λ j, (hv.repr m j - int.floor (hv.repr m j)) -
      (hv.repr n j - int.floor (hv.repr n j))) i = 0,
    { intro j,
      specialize this j,
      rw ← int.fract_eq_fract,
      rw ← sub_eq_zero,
      rw ← int.self_sub_floor,
      rwa ← int.self_sub_floor,
    },
    rw linear_independent_iff' at hv,
    specialize hv finset.univ,
    simp only [finset.mem_univ, forall_true_left] at hv,
    apply hv,
    simp_rw sub_smul,
    simp_rw finset.sum_sub_distrib,
    rw sub_eq_zero,
    simp_rw ← zsmul_eq_smul_cast ℝ _ _,
    simp_rw linear_independent.repr_sum,
    exact h,
  },
  refine ⟨_, _⟩,
  intro j,
  specialize this j,
  use this.some,
  rw ← hv.repr_sum m,
  rw ← hv.repr_sum n,
  rw ← finset.sum_sub_distrib,
  simp_rw ← sub_smul,
  congr,
  ext j,
  have t1 := (this j).some_spec,
  simp_rw zsmul_eq_smul_cast ℝ _ _,
  rw ← t1,
end

end approx

#exit

-- Don't you need E without ℚ (or ℝ) torsion?
variable (L : add_subgroup E)

example :
  ∀ r : ℝ, ((L : set (ι → ℝ)) ∩ metric.ball (0 : ι → ℝ) r).finite
  ↔ discrete_topology L :=
begin
  sorry
end

example (h : discrete_topology L) : countable L :=
begin
  sorry,
end

example (h : discrete_topology L) : module.free ℤ L :=
begin
  rw module.free_def,
  convert module.free_of_finite_type_torsion_free',

end
