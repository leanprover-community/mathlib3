import ring_theory.noetherian
import ring_theory.jacobson

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]

open ideal

lemma exists_mul_sub_mem_of_sub_one_mem_jacobson {I : ideal R} (r : R)
  (h : r - 1 ∈ jacobson I) : ∃ s, r * s - 1 ∈ I :=
begin
  cases mem_jacobson_iff.1 h 1 with s hs,
  use s,
  simpa [sub_mul] using hs
end

lemma is_unit_of_sub_one_mem_jacobson_bot (r : R)
  (h : r - 1 ∈ jacobson (⊥ : ideal R)) : is_unit r :=
begin
  cases exists_mul_sub_mem_of_sub_one_mem_jacobson r h with s hs,
  rw [mem_bot, sub_eq_zero] at hs,
  exact is_unit_of_mul_eq_one _ _ hs
end

namespace submodule

-- Number 2 on stacks
lemma eq_smul_of_le_smul_of_le_jacobson {I J : ideal R} {N : submodule R M}
  (hN : N.fg) (hIN : N ≤ I • N) (hIjac : I ≤ jacobson J) : N = J • N :=
begin
  refine le_antisymm _ (submodule.smul_le.2 (λ _ _ _, submodule.smul_mem _ _)),
  intros n hn,
  cases submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hN hIN with r hr,
  cases exists_mul_sub_mem_of_sub_one_mem_jacobson r (hIjac hr.1) with s hs,
  have : n = (-(r * s - 1) • n),
  { rw [neg_sub, sub_smul, mul_comm, mul_smul, hr.2 n hn, one_smul, smul_zero, sub_zero] },
  rw this,
  exact submodule.smul_mem_smul (submodule.neg_mem _ hs) hn
end

lemma eq_bot_of_le_smul_of_le_jacobson (I : ideal R) (N : submodule R M)
  (hN : N.fg) (hIN : N ≤ I • N) (hIjac : I ≤ jacobson ⊥) : N = ⊥ :=
by rw [eq_smul_of_le_smul_of_le_jacobson hN hIN hIjac, submodule.bot_smul]

lemma smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson {I J : ideal R}
  {N N' : submodule R M} (hN' : N'.fg) (hIJ : I ≤ jacobson J)
  (hNN : N ⊔ N' ≤ N ⊔ I • N') : N ⊔ I • N' = N ⊔ J • N' :=
begin
  have hNN' : N ⊔ N' = N ⊔ I • N',
    from le_antisymm hNN
      (sup_le_sup_left (submodule.smul_le.2 (λ _ _ _, submodule.smul_mem _ _)) _),
  have : (I • N').map N.mkq = N'.map N.mkq,
  { rw ← (submodule.comap_injective_of_surjective
        (linear_map.range_eq_top.1 (submodule.range_mkq N))).eq_iff,
    simpa [linear_map.comap_map_eq, sup_comm, eq_comm] using hNN' },
  have := @submodule.eq_smul_of_le_smul_of_le_jacobson _ _ _ _ _ I J
    (N'.map N.mkq) (fg_map hN')
    (by rw [← map_smul'', this]; exact le_refl _)
    hIJ,
  rw [← map_smul'', ← (submodule.comap_injective_of_surjective
        (linear_map.range_eq_top.1 (submodule.range_mkq N))).eq_iff,
        linear_map.comap_map_eq, linear_map.comap_map_eq, submodule.ker_mkq, sup_comm,
        hNN'] at this,
  rw [this, sup_comm]
end

lemma smul_sup_eq_of_le_smul_of_le_jacobson {I : ideal R}
  {N N' : submodule R M} (hN' : N'.fg) (hIJ : I ≤ jacobson ⊥)
  (hNN : N ⊔ N' ≤ N ⊔ I • N') : N ⊔ I • N' = N :=
by rw [smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson hN' hIJ hNN, bot_smul, sup_bot_eq]

end submodule
