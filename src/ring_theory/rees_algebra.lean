/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import ring_theory.finiteness
import ring_theory.ideal.local_ring
import ring_theory.nakayama

/-!

# Rees algebra

The Rees algebra of an ideal `I` is the subalgebra `R[It]` of `R[X]` defined as `R[It] = ⨁ₙ Iⁿ tⁿ`.
This is used to prove the Artin-Rees lemma, and will potentially enable us to calculate some
blowup in the future.

## Main definition

- `rees_algebra` : The Rees algebra of an ideal `I`, defined as a subalgebra of `R[X]`.
- `adjoin_monomial_eq_rees_algebra` : The Rees algebra is generated by the degree one elements.
- `rees_algebra.fg` : The Rees algebra of a f.g. ideal is of finite type. In particular, this
implies that the rees algebra over a noetherian ring is still noetherian.

-/

universes u v

variables {R M : Type u} [comm_ring R] [add_comm_group M] [module R M] (I : ideal R)

open polynomial
open_locale polynomial big_operators

/-- The Rees algebra of an ideal `I`, defined as the subalgebra of `R[X]` whose `i`-th coefficient
falls in `I ^ n`. -/
def rees_algebra : subalgebra R R[X] :=
{ carrier := { f | ∀ i, f.coeff i ∈ I ^ i },
  mul_mem' := λ f g hf hg i, begin
    rw coeff_mul,
    apply ideal.sum_mem,
    rintros ⟨j, k⟩ e,
    rw [← finset.nat.mem_antidiagonal.mp e, pow_add],
    exact ideal.mul_mem_mul (hf j) (hg k)
  end,
  one_mem' := λ i, begin
    rw coeff_one,
    split_ifs,
    { subst h, simp },
    { simp }
  end,
  add_mem' := λ f g hf hg i, begin
    rw coeff_add,
    exact ideal.add_mem _ (hf i) (hg i)
  end,
  zero_mem' := λ i, ideal.zero_mem _,
  algebra_map_mem' := λ r i, begin
    rw [algebra_map_apply, coeff_C],
    split_ifs,
    { subst h, simp },
    { simp }
  end }

lemma mem_rees_algebra_iff (f : R[X]) :
  f ∈ rees_algebra I ↔ ∀ i, f.coeff i ∈ I ^ i := iff.rfl

lemma rees_algebra.monomial_mem {I : ideal R} {i : ℕ} {r : R} :
  monomial i r ∈ rees_algebra I ↔ r ∈ I ^ i :=
begin
  dsimp [mem_rees_algebra_iff, monomial, monomial_fun],
  simp_rw finsupp.single_apply,
  exact ⟨λ H, by simpa using H i, λ h j,
    by { split_ifs with h', { rwa ← h' }, { exact ideal.zero_mem _ } }⟩,
end

lemma adjoin_monomial_eq_rees_algebra :
  algebra.adjoin R (submodule.map (monomial 1) I : set R[X]) = rees_algebra I :=
begin
  apply le_antisymm,
  { apply algebra.adjoin_le _,
    rintro _ ⟨r, hr, rfl⟩,
    exact rees_algebra.monomial_mem.mpr (by rwa pow_one) },
  { intros p hp,
    rw p.as_sum_support,
    apply subalgebra.sum_mem _ _,
    rintros i -,
    specialize hp i,
    revert hp,
    generalize : p.coeff i = r,
    induction i with i hi generalizing r,
    { intro _, exact subalgebra.algebra_map_mem _ _ },
    { intro h,
      rw pow_succ at h,
      apply submodule.smul_induction_on h,
      { intros r hr s hs,
        rw [nat.succ_eq_one_add, smul_eq_mul, ← monomial_mul_monomial],
        exact subalgebra.mul_mem _ (algebra.subset_adjoin (set.mem_image_of_mem _ hr)) (hi s hs) },
      { intros x y hx hy, rw monomial_add, exact subalgebra.add_mem _ hx hy } } }
end

variables {I}

lemma rees_algebra.fg (hI : I.fg) : (rees_algebra I).fg :=
begin
  classical,
  obtain ⟨s, hs⟩ := hI,
  rw [← adjoin_monomial_eq_rees_algebra, ← hs],
  use s.image (monomial 1),
  rw finset.coe_image,
  change _ = algebra.adjoin R (submodule.map (monomial 1) (submodule.span R ↑s) : set R[X]),
  rw [submodule.map_span, algebra.adjoin_span]
end

instance [is_noetherian_ring R] : algebra.finite_type R (rees_algebra I) :=
⟨(rees_algebra I).fg_top.mpr (rees_algebra.fg $ is_noetherian.noetherian I)⟩

instance [is_noetherian_ring R] : is_noetherian_ring (rees_algebra I) :=
algebra.finite_type.is_noetherian_ring R _
