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

open_locale classical

variables {E : Type*} [normed_add_comm_group E] [module ℝ E]

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

example (a : ℤ) (b : ℝ) (v : E) : b • v + a • v = (b + a) • v :=
begin
  rw ( _ : a • v = (a : ℝ) • v),
  exact (add_smul b ↑a v).symm,
  exact zsmul_eq_smul_cast ℝ a v,
end


example (hv : linear_independent ℝ v)
  (m : submodule.span ℝ (set.range v)) :
  ‖(floor_approx hv m : E) + (-1 : ℝ) • m‖ ≤ finset.univ.sum (λ j : α, ‖v j‖) :=
begin
  have := hv.total_repr m,
  rw finsupp.total_apply at this,
  rw finsupp.sum_fintype _ _ _ at this,
  rotate,
  apply_instance,
  simp only [zero_smul, eq_self_iff_true, implies_true_iff],
  { rw ← this,
    rw floor_approx,
    show_term { dsimp *, },
    rw finset.smul_sum,
    rw ← finset.sum_add_distrib,
    --
    simp_rw neg_smul,
    simp_rw one_smul,
    simp_rw ← neg_smul,
    have : ∀ x : α, ⌊((hv.repr) m) x⌋ • v x = (⌊((hv.repr) m) x⌋ : ℝ) • v x,
    { intro x,
      exact zsmul_eq_smul_cast ℝ _ _, },
    simp_rw this,
    simp_rw ← add_smul,
    rw norm_sum_le _ _,
    sorry,
  },

end

example (hv : linear_independent ℝ v)
  (m : submodule.span ℝ (set.range v)) :
  ‖(floor_approx hv m : E) + (-1 : ℝ) • m‖ ≤ finset.univ.sum (λ j : α, ‖v j‖) :=
begin
  have : (m : E) = finset.univ.sum (λ (i : α), ((hv.repr) m) i • v i), { sorry, },
  calc
    ‖(floor_approx hv m : E) + (-1 : ℝ) • m‖
        ≤ ‖floor_approx hv m + (-1 : ℝ) • finset.univ.sum (λ i, ((hv.repr) m) i • v i)‖
          : by rw this
    ... ≤ ‖finset.univ.sum (λ j, ⌊((hv.repr) m) j⌋ • v j) +
            (-1 : ℝ) • finset.univ.sum (λ i, ((hv.repr) m) i • v i)‖
          : by rw floor_approx
    ... ≤ ‖finset.univ.sum (λ j, ⌊((hv.repr) m) j⌋ • v j + (-1 : ℝ) • ((hv.repr) m) j • v j)‖
          : by rw [finset.smul_sum, ← finset.sum_add_distrib]
    ... ≤ ‖finset.univ.sum (λ j, ⌊((hv.repr) m) j⌋ • v j + -((hv.repr) m) j • v j)‖
          : by simp_rw [neg_smul, one_smul]
    ... ≤ ‖finset.univ.sum (λ j, (⌊((hv.repr) m) j⌋ : ℝ) • v j + -((hv.repr) m) j • v j)‖
          : by simp_rw zsmul_eq_smul_cast ℝ
    ... ≤ ‖finset.univ.sum (λ j, (↑⌊((hv.repr) m) j⌋ + -((hv.repr) m) j) • v j)‖
          : by sorry
    ... ≤ finset.univ.sum (λ j : α, ‖v j‖) : by sorry,

end

end approx

#exit

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
