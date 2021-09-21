/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import ring_theory.noetherian
import ring_theory.jacobson
/-!
# Nakayama's lemma

This file contains some alternative statements of Nakayama's Lemma as found in
[Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

## Main statements

* `submodule.eq_smul_of_le_smul_of_le_jacobson` - A version of (2) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).,
  generalising to the Jacobson of any ideal.
* `submodule.eq_bot_of_le_smul_of_le_jacobson_bot` - Statement (2) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

* `submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson` - A version of (4) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).,
  generalising to the Jacobson of any ideal.
* `submodule.smul_sup_eq_of_le_smul_of_le_jacobson_bot` - Statement (4) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

Note that a version of Statement (1) in
[Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV) can be found in
`ring_theory/noetherian` under the name
`submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`

## References
* [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV)

## Tags
Nakayama, Jacobson
-/
variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]

open ideal

namespace submodule

/-- *Nakayama's Lemma** - A slightly more general version of (2) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `eq_bot_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`.  -/
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

/-- *Nakayama's Lemma** - Statement (2) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `eq_smul_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
lemma eq_bot_of_le_smul_of_le_jacobson_bot (I : ideal R) (N : submodule R M)
  (hN : N.fg) (hIN : N ≤ I • N) (hIjac : I ≤ jacobson ⊥) : N = ⊥ :=
by rw [eq_smul_of_le_smul_of_le_jacobson hN hIN hIjac, submodule.bot_smul]

/-- *Nakayama's Lemma** - A slightly more general version of (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_sup_eq_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`.  -/
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
    simpa [comap_map_eq, sup_comm, eq_comm] using hNN' },
  have := @submodule.eq_smul_of_le_smul_of_le_jacobson _ _ _ _ _ I J
    (N'.map N.mkq) (fg_map hN')
    (by rw [← map_smul'', this]; exact le_refl _)
    hIJ,
  rw [← map_smul'', ← (submodule.comap_injective_of_surjective
        (linear_map.range_eq_top.1 (submodule.range_mkq N))).eq_iff,
        comap_map_eq, comap_map_eq, submodule.ker_mkq, sup_comm,
        hNN'] at this,
  rw [this, sup_comm]
end

/-- *Nakayama's Lemma** - Statement (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
lemma smul_sup_le_of_le_smul_of_le_jacobson_bot {I : ideal R}
  {N N' : submodule R M} (hN' : N'.fg) (hIJ : I ≤ jacobson ⊥)
  (hNN : N ⊔ N' ≤ N ⊔ I • N') : I • N' ≤ N :=
by rw [← sup_eq_left, smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson hN' hIJ hNN,
  bot_smul, sup_bot_eq]

end submodule
