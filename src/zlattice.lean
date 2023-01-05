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
import group_theory.finiteness

open_locale classical

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]

section approx

variables {α : Type*} [fintype α] {v : α → E}

-- TODO : write everything in terms of m - floor_approx m (and thus stay in the span)?

noncomputable def floor_approx
  (hv : linear_independent ℝ v)
  (m : submodule.span ℝ (set.range v)) : E :=
begin
  let s := hv.repr m,
  let z := finset.univ.sum (λ j : α, int.floor(s j) • (v j)),
  exact z,
end

lemma linear_independent.repr_sum {R : Type*} [ring R] [module R E]
  (hv : linear_independent R v) (m : submodule.span R (set.range v)) :
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
          : by rw ← linear_independent.repr_sum
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

lemma floor_approx_mem (hv : linear_independent ℝ v) (m : submodule.span ℝ (set.range v)) :
  floor_approx hv m ∈ submodule.span ℤ (set.range v) :=
sum_mem (λ j _, zsmul_mem (submodule.subset_span (set.mem_range_self j)) _)

lemma sub_approx_eq_sub_approx
  (hv : linear_independent ℝ v) (m n : submodule.span ℝ (set.range v)) :
  (m : E) - floor_approx hv m = (n : E) - floor_approx hv n ↔
  (m - n : E) ∈ (submodule.span ℤ (set.range v) : set E) :=
begin
  split,
  { intro h,
    rw sub_eq_sub_iff_sub_eq_sub at h,
    rw h,
    rw set_like.mem_coe,
    refine submodule.sub_mem _ _ _,
    exact floor_approx_mem hv m,
    exact floor_approx_mem hv n,
  },
  { intro h,
    suffices : ∀ j, int.fract (hv.repr m j) = int.fract (hv.repr n j),
    { rw ← hv.repr_sum m,
      rw ← hv.repr_sum n,
      dsimp [floor_approx],
      rw ← finset.sum_sub_distrib,
      rw ← finset.sum_sub_distrib,
      simp_rw zsmul_eq_smul_cast ℝ _ _,
      simp_rw ← sub_smul,
      simp_rw int.self_sub_floor,
      simp_rw this, },
    have hvz : linear_independent ℤ v := hv.restrict_scalars (smul_left_injective ℤ (by norm_num)),
    have eqr : ∀ i, ((hv.repr) (m - n)) i = ↑(((hvz.repr) ⟨m - n, h⟩) i),
    { have t1 := linear_independent.repr_sum hvz ⟨m - n, h⟩,
      have t2 := linear_independent.repr_sum hv (m - n),
      rw subtype.coe_mk at t1,
      rw ( _ : ↑(m - n) = ↑m - ↑n) at t2,
      rw eq_comm at t1,
      rw t1 at t2,
      rw ← sub_eq_zero at t2,
      rw ← finset.sum_sub_distrib at t2,
      simp_rw zsmul_eq_smul_cast ℝ _ _ at t2,
      simp_rw ← sub_smul at t2,
      rw linear_independent_iff' at hv,
      specialize hv finset.univ,
      simp only [finset.mem_univ, forall_true_left] at hv,
      have := (hv _) t2,
      simp_rw sub_eq_zero at this,
      exact this,
      exact (submodule.span ℝ (set.range v)).coe_sub m n, },
    intro j,
    simp_rw int.fract_eq_fract,
    use hvz.repr ⟨m - n, h⟩ j,
    have : ((hv.repr) m j) - ((hv.repr) n j) = hv.repr (m - n) j,
    { rw map_sub, refl, },
    rw this,
    exact eqr j, },
  end

end approx

section fg

example {G : Type*} [group G] (N : subgroup G) [N.normal] (h1 : group.fg N)
  (h2 : group.fg (G ⧸ N)) : group.fg G :=
begin
  rw group.fg_iff at h1 h2 ⊢,
  obtain ⟨S1, HS1⟩ := h1,
  obtain ⟨S2, HS2⟩ := h2,
  let S1p := (coe : N → G) '' S1,
  let s : G ⧸ N → G := λ q, (quot.exists_rep q).some,
  let S2p := s '' S2,
  use S1p ∪ S2p,
  split,
  { ext g,
    split,
    { sorry,


    },
    { intro _,
      suffices : N ≤ subgroup.closure (S1p ∪ S2p),
      { let q := quotient_group.mk' N g,
        let x := s q,
        have t1 : x ∈ subgroup.closure (S1p ∪ S2p), { sorry, },
        have t2 : g ∈ left_coset g N, { sorry, },
        have t3 : left_coset g N ≤ subgroup.closure (S1p ∪ S2p), { sorry, },
        exact t3 t2, },
      { sorry, }}},
  { sorry, }
end

end fg

section lattice_basic

variable (L : add_subgroup E)

example {R M : Type*} [ring R] [add_comm_group M] [module R M] (P : submodule R M)
  (h1 : module.finite R P) (h2 : module.finite R (M ⧸ P)) :
  module.finite R M :=
begin
  rw module.finite_def at h1 h2 ⊢,
  rw submodule.fg_def at h1 h2 ⊢,
  obtain ⟨S1, HS1⟩ := h1,
  obtain ⟨S2, HS2⟩ := h2,
  let S1p := (coe : P → M) '' S1,
  let s : M ⧸ P → M := λ q, (quot.exists_rep q).some,
  let S2p := s '' S2,
  use S1p ∪ S2p,
  split,
  { rw set.finite_union,
    sorry,
  },
  { ext x,
    split,
    { sorry,
    },
    { rintros ⟨x, hx⟩,
    }
  }
end



example (h : discrete_topology L) : add_subgroup.fg L :=
begin
  sorry,
end

end lattice_basic

#exit

-- Don't you need E without ℚ (or ℝ) torsion?


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
