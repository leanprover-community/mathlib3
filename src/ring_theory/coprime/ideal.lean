/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import linear_algebra.dfinsupp
import ring_theory.ideal.operations

/-!
# An additional lemma about coprime ideals

This lemma generalises `exists_sum_eq_one_iff_pairwise_coprime` to the case of non-principal ideals.
It is on a separate file due to import requirements.
-/

namespace ideal
variables {ι R : Type*} [comm_semiring R]

/--A finite family of ideals is pairwise coprime (that is, any two of them generate the whole ring)
iff when taking all the possible intersections of all but one of these ideals, the resulting family
of ideals still generate the whole ring.

For example with three ideals : `I ⊔ J = I ⊔ K = J ⊔ K = ⊤ ↔ (I ⊓ J) ⊔ (I ⊓ K) ⊔ (J ⊓ K) = ⊤`.

When ideals are all of the form `I i = R ∙ s i`, this is equivalent to the
`exists_sum_eq_one_iff_pairwise_coprime` lemma.-/
lemma supr_infi_eq_top_iff_pairwise {t : finset ι} (h : t.nonempty) (I : ι → ideal R) :
  (⨆ i ∈ t, ⨅ j (hj : j ∈ t) (ij : j ≠ i), I j) = ⊤ ↔
    (t : set ι).pairwise (λ i j, I i ⊔ I j = ⊤) :=
begin
  haveI : decidable_eq ι := classical.dec_eq ι,
  rw [eq_top_iff_one, submodule.mem_supr_finset_iff_exists_sum],
  refine h.cons_induction _ _; clear' t h,
  { simp only [finset.sum_singleton, finset.coe_singleton, set.pairwise_singleton, iff_true],
    refine λ a, ⟨λ i, if h : i = a then ⟨1, _⟩ else 0, _⟩,
    { rw h, simp only [finset.mem_singleton, ne.def, infi_infi_eq_left, eq_self_iff_true,
        not_true, infi_false]},
    { simp only [dif_pos, dif_ctx_congr, submodule.coe_mk, eq_self_iff_true] } },
  intros a t hat h ih,
  rw [finset.coe_cons,
    set.pairwise_insert_of_symmetric (λ i j (h : I i ⊔ I j = ⊤), sup_comm.trans h)],
  split,
  { rintro ⟨μ, hμ⟩, rw finset.sum_cons at hμ,
    refine ⟨ih.mp ⟨pi.single h.some ⟨μ a, _⟩ + λ i, ⟨μ i, _⟩, _⟩, λ b hb ab, _⟩,
    { have := submodule.coe_mem (μ a), rw mem_infi at this ⊢,
      --for some reason `simp only [mem_infi]` times out
      intro i, specialize this i, rw [mem_infi, mem_infi] at this ⊢,
      intros hi _, apply this (finset.subset_cons _ hi),
      rintro rfl, exact hat hi },
    { have := submodule.coe_mem (μ i), simp only [mem_infi] at this ⊢,
      intros j hj ij, exact this _ (finset.subset_cons _ hj) ij },
    { rw [← @if_pos _ _ h.some_spec R (μ a) 0, ← finset.sum_pi_single',
        ← finset.sum_add_distrib] at hμ,
      convert hμ, ext i, rw [pi.add_apply, submodule.coe_add, submodule.coe_mk],
      by_cases hi : i = h.some,
      { rw [hi, pi.single_eq_same, pi.single_eq_same, submodule.coe_mk] },
      { rw [pi.single_eq_of_ne hi, pi.single_eq_of_ne hi, submodule.coe_zero] } },
    { rw [eq_top_iff_one, submodule.mem_sup],
      rw add_comm at hμ, refine ⟨_, _, _, _, hμ⟩,
      { refine sum_mem _ (λ x hx, _),
        have := submodule.coe_mem (μ x), simp only [mem_infi] at this,
        apply this _ (finset.mem_cons_self _ _), rintro rfl, exact hat hx },
      { have := submodule.coe_mem (μ a), simp only [mem_infi] at this,
        exact this _ (finset.subset_cons _ hb) ab.symm } } },
  { rintro ⟨hs, Hb⟩,
    obtain ⟨μ, hμ⟩ := ih.mpr hs,
    have := sup_infi_eq_top (λ b hb, Hb b hb (ne_of_mem_of_not_mem hb hat).symm),
    rw [eq_top_iff_one, submodule.mem_sup] at this,
    obtain ⟨u, hu, v, hv, huv⟩ := this,
    refine ⟨λ i, if hi : i = a then ⟨v, _⟩ else ⟨u * μ i, _⟩, _⟩,
    { simp only [mem_infi] at hv ⊢,
      intros j hj ij, rw [finset.mem_cons, ← hi] at hj,
      exact hv _ (hj.resolve_left ij) },
    { have := submodule.coe_mem (μ i), simp only [mem_infi] at this ⊢,
      intros j hj ij,
      rcases finset.mem_cons.mp hj with rfl | hj,
      { exact mul_mem_right _ _ hu },
      { exact mul_mem_left _ _ (this _ hj ij) } },
    { rw [finset.sum_cons, dif_pos rfl, add_comm],
      rw ← mul_one u at huv, rw [← huv, ← hμ, finset.mul_sum],
      congr' 1, apply finset.sum_congr rfl, intros j hj,
      rw dif_neg, refl,
      rintro rfl, exact hat hj } }
end

end ideal
