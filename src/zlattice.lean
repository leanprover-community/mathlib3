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

section approx_gen

namespace gen

variables {ι : Type*}

noncomputable def floor_approx (b : basis ι ℝ E) (m : E) : E :=
begin
  let s := b.repr m,
  let k0 : ι →₀ ℤ := s.map_range int.floor int.floor_zero,
  let k : ι →₀ ℝ := k0.map_range coe int.cast_zero,
  exact b.repr.symm k,
end

end gen

end approx_gen

section approx

variables {α : Type*} [fintype α] {v : α → E}

-- TODO : write everything in terms of m - floor_approx m (and thus stay in the span)?
-- TODO : do everything in terms of basis of E?

noncomputable def floor_approx
  (hv : linear_independent ℝ v) (m : submodule.span ℝ (set.range v)) : E :=
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
          : by rw ← linear_independent.repr_sum hv m
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

section lattice_basic

variables [finite_dimensional ℝ E] (L : submodule ℤ E)

example {α: Type*} [lattice α] (x y : α) (h : y ≤ x) : x ⊓ y = y := by refine inf_eq_right.mpr h

example (hd : discrete_topology L) (hs : submodule.span ℝ (L : set E) = ⊤) : submodule.fg L :=
begin
  obtain ⟨b, ⟨hbL, ⟨hbsp, hblin⟩⟩⟩ := exists_linear_independent ℝ (L : set E),
  have : basis b ℝ E, { sorry, },
  refine submodule.fg_of_fg_map_of_fg_inf_ker (submodule.mkq (submodule.span ℤ b)) _ _,
  { suffices : (submodule.map (submodule.span ℤ b).mkq L).carrier.finite,
    { refine ⟨_, _⟩,
      use set.finite.to_finset this,
      rw set.finite.coe_to_finset,
      change submodule.span ℤ ↑(submodule.map (submodule.span ℤ b).mkq L) =
        submodule.map (submodule.span ℤ b).mkq L,
      rw submodule.span_eq, },
    let g : E → E := λ x, x - gen.floor_approx this x,
    
    let f : E ⧸ (submodule.span ℤ b) → E :=
    begin
      intro x,
      let y := (quot.exists_rep x).some,
      use y - gen.floor_approx this y,
    end,
    have hi : function.injective f, { sorry, },
    refine set.finite.of_finite_image _ (hi.inj_on _),

    sorry, },
  { have : L ⊓ linear_map.ker _ = submodule.span ℤ b,
    { rw submodule.ker_mkq (submodule.span ℤ b),
      rw inf_eq_right,
      rwa submodule.span_le, },
    rw this,
    exact submodule.fg_span (linear_independent.finite hblin), }
end

  #exit

  -- have := b.linear_independent,
  -- have := b.mem_span _,
  -- have t1 : ∀ v ∈ L, v ∈ submodule.span ℝ (L : set E), { sorry, },

--   have t2 : ∀ v ∈ L, v ∈ (submodule.span ℝ (set.range ⇑b) : set E),
--   { intros v hv,
--     have t1 : v ∈ submodule.span ℝ (L : set E) := submodule.subset_span hv,
-- --    have t2 := b.mem_span t1,
--     sorry,
--     },
  have : L ≤ (submodule.span ℝ (L : set E)), { sorry, },
  let L0 := submodule.map _ L,
  let f : (submodule.span ℝ (L : set E)) →ₗ[ℤ] (submodule.span ℤ (L : set E)) :=
  { to_fun := sorry,
    -- begin
    --   intro v,
    --   refine floor_approx b.linear_independent _,
    --   have := b.mem_span ⟨v, (t1 v) v.prop⟩,
    --   use v,
    --   exact (t1 v) v.prop,
    --   exact this,
    -- end,
    map_add' := sorry,
    map_smul' := sorry },
  -- make L a submodule of (submodule.span ℝ (L : set E))
  refine submodule.fg_of_fg_map_of_fg_inf_ker f _ _,

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
