/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import ring_theory.localization.at_prime
import order.minimal

/-!

# Minimal primes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We provide various results concerning the minimal primes above an ideal

## Main results
- `ideal.minimal_primes`: `I.minimal_primes` is the set of ideals that are minimal primes over `I`.
- `minimal_primes`: `minimal_primes R` is the set of minimal primes of `R`.
- `ideal.exists_minimal_primes_le`: Every prime ideal over `I` contains a minimal prime over `I`.
- `ideal.radical_minimal_primes`: The minimal primes over `I.radical` are precisely
  the minimal primes over `I`.
- `ideal.Inf_minimal_primes`: The intersection of minimal primes over `I` is `I.radical`.
- `ideal.exists_minimal_primes_comap_eq` If `p` is a minimal prime over `f ⁻¹ I`, then it is the
  preimage of some minimal prime over `I`.
- `ideal.minimal_primes_eq_comap`: The minimal primes over `I` are precisely the preimages of
  minimal primes of `R ⧸ I`.


-/


section

variables {R S : Type*} [comm_ring R] [comm_ring S] (I J : ideal R)

/-- `I.minimal_primes` is the set of ideals that are minimal primes over `I`. -/
def ideal.minimal_primes : set (ideal R) :=
minimals (≤) { p | p.is_prime ∧ I ≤ p }

/-- `minimal_primes R` is the set of minimal primes of `R`.
This is defined as `ideal.minimal_primes ⊥`. -/
def minimal_primes (R : Type*) [comm_ring R] : set (ideal R) := ideal.minimal_primes ⊥

variables {I J}

lemma ideal.exists_minimal_primes_le [J.is_prime] (e : I ≤ J) :
  ∃ p ∈ I.minimal_primes, p ≤ J :=
begin
  suffices : ∃ m ∈ { p : (ideal R)ᵒᵈ | ideal.is_prime p ∧ I ≤ order_dual.of_dual p },
    (order_dual.to_dual J) ≤ m ∧
      ∀ z ∈ { p : (ideal R)ᵒᵈ | ideal.is_prime p ∧ I ≤ p }, m ≤ z → z = m,
  { obtain ⟨p, h₁, h₂, h₃⟩ := this,
    simp_rw ← @eq_comm _ p at h₃,
    exact ⟨p, ⟨h₁, λ a b c, (h₃ a b c).le⟩, h₂⟩ },
  apply zorn_nonempty_partial_order₀,
  swap, { refine ⟨show J.is_prime, by apply_instance, e⟩ },
  rintros (c : set (ideal R)) hc hc' J' hJ',
  refine ⟨order_dual.to_dual (Inf c),
    ⟨ideal.Inf_is_prime_of_is_chain ⟨J', hJ'⟩ hc'.symm (λ x hx, (hc hx).1), _⟩, _⟩,
  { rw order_dual.of_dual_to_dual, convert le_Inf _, intros x hx, exact (hc hx).2 },
  { rintro z hz,
    rw order_dual.le_to_dual,
    exact Inf_le hz }
end

@[simp]
lemma ideal.radical_minimal_primes : I.radical.minimal_primes = I.minimal_primes :=
begin
  rw [ideal.minimal_primes, ideal.minimal_primes],
  congr,
  ext p,
  exact ⟨λ ⟨a, b⟩, ⟨a, ideal.le_radical.trans b⟩, λ ⟨a, b⟩, ⟨a, a.radical_le_iff.mpr b⟩⟩,
end

@[simp]
lemma ideal.Inf_minimal_primes :
  Inf I.minimal_primes = I.radical :=
begin
  rw I.radical_eq_Inf,
  apply le_antisymm,
  { intros x hx,
    rw ideal.mem_Inf at hx ⊢,
    rintros J ⟨e, hJ⟩,
    resetI,
    obtain ⟨p, hp, hp'⟩ := ideal.exists_minimal_primes_le e,
    exact hp' (hx hp) },
  { apply Inf_le_Inf _,
    intros I hI,
    exact hI.1.symm },
end

lemma ideal.exists_comap_eq_of_mem_minimal_primes_of_injective {f : R →+* S}
  (hf : function.injective f) (p ∈ minimal_primes R) :
  ∃ p' : ideal S, p'.is_prime ∧ p'.comap f = p :=
begin
  haveI := H.1.1,
  haveI : nontrivial (localization (submonoid.map f p.prime_compl)),
  { refine ⟨⟨1, 0, _⟩⟩,
    convert (is_localization.map_injective_of_injective p.prime_compl (localization.at_prime p)
      (localization $ p.prime_compl.map f) hf).ne one_ne_zero,
    { rw map_one }, { rw map_zero } },
  obtain ⟨M, hM⟩ := ideal.exists_maximal (localization (submonoid.map f p.prime_compl)),
  resetI,
  refine ⟨M.comap (algebra_map S $ localization (submonoid.map f p.prime_compl)),
    infer_instance, _⟩,
  rw [ideal.comap_comap, ← @@is_localization.map_comp _ _ _ _ localization.is_localization _
    p.prime_compl.le_comap_map _ localization.is_localization, ← ideal.comap_comap],
  suffices : _ ≤ p,
  { exact this.antisymm (H.2 ⟨infer_instance, bot_le⟩ this) },
  intros x hx,
  by_contra h,
  apply hM.ne_top,
  apply M.eq_top_of_is_unit_mem hx,
  apply is_unit.map,
  apply is_localization.map_units _ (show p.prime_compl, from ⟨x, h⟩),
  apply_instance
end

lemma ideal.exists_comap_eq_of_mem_minimal_primes {I : ideal S}
  (f : R →+* S) (p ∈ (I.comap f).minimal_primes) :
  ∃ p' : ideal S, p'.is_prime ∧ I ≤ p' ∧ p'.comap f = p :=
begin
  haveI := H.1.1,
  let f' := I^.quotient.mk^.comp f,
  have e : (I^.quotient.mk^.comp f).ker = I.comap f,
  { ext1, exact (submodule.quotient.mk_eq_zero _) },
  have : (I^.quotient.mk^.comp f).ker^.quotient.mk^.ker ≤ p,
  { rw [ideal.mk_ker, e], exact H.1.2 },
  obtain ⟨p', hp₁, hp₂⟩ := ideal.exists_comap_eq_of_mem_minimal_primes_of_injective
    (I^.quotient.mk^.comp f).ker_lift_injective (p.map (I^.quotient.mk^.comp f).ker^.quotient.mk) _,
  { resetI,
    refine ⟨p'.comap I^.quotient.mk, ideal.is_prime.comap _, _, _⟩,
    { exact ideal.mk_ker.symm.trans_le (ideal.comap_mono bot_le) },
    convert congr_arg (ideal.comap (I^.quotient.mk^.comp f).ker^.quotient.mk) hp₂,
    rwa [ideal.comap_map_of_surjective (I^.quotient.mk^.comp f).ker^.quotient.mk
      ideal.quotient.mk_surjective, eq_comm, sup_eq_left] },
  refine ⟨⟨_, bot_le⟩, _⟩,
  { apply ideal.map_is_prime_of_surjective _ this, exact ideal.quotient.mk_surjective },
  { rintro q ⟨hq, -⟩ hq',
    rw ← ideal.map_comap_of_surjective (I^.quotient.mk^.comp f).ker^.quotient.mk
      ideal.quotient.mk_surjective q,
    apply ideal.map_mono,
    resetI,
    apply H.2,
    { refine ⟨infer_instance, (ideal.mk_ker.trans e).symm.trans_le (ideal.comap_mono bot_le)⟩ },
    { refine (ideal.comap_mono hq').trans _, rw ideal.comap_map_of_surjective,
      exacts [sup_le rfl.le this, ideal.quotient.mk_surjective] } }
end

lemma ideal.exists_minimal_primes_comap_eq {I : ideal S}
  (f : R →+* S) (p ∈ (I.comap f).minimal_primes) :
  ∃ p' ∈ I.minimal_primes, ideal.comap f p' = p :=
begin
  obtain ⟨p', h₁, h₂, h₃⟩ := ideal.exists_comap_eq_of_mem_minimal_primes f p H,
  resetI,
  obtain ⟨q, hq, hq'⟩ := ideal.exists_minimal_primes_le h₂,
  refine ⟨q, hq, eq.symm _⟩,
  haveI := hq.1.1,
  have := (ideal.comap_mono hq').trans_eq h₃,
  exact (H.2 ⟨infer_instance, ideal.comap_mono hq.1.2⟩ this).antisymm this
end

lemma ideal.mimimal_primes_comap_of_surjective {f : R →+* S} (hf : function.surjective f)
  {I J : ideal S} (h : J ∈ I.minimal_primes) :
  J.comap f ∈ (I.comap f).minimal_primes :=
begin
  haveI := h.1.1,
  refine ⟨⟨infer_instance, ideal.comap_mono h.1.2⟩, _⟩,
  rintros K ⟨hK, e₁⟩ e₂,
  have : f.ker ≤ K := (ideal.comap_mono bot_le).trans e₁,
  rw [← sup_eq_left.mpr this, ring_hom.ker_eq_comap_bot, ← ideal.comap_map_of_surjective f hf],
  apply ideal.comap_mono _,
  apply h.2 _ _,
  { exactI ⟨ideal.map_is_prime_of_surjective hf this,
      ideal.le_map_of_comap_le_of_surjective f hf e₁⟩ },
  { exact ideal.map_le_of_le_comap e₂ }
end

lemma ideal.comap_minimal_primes_eq_of_surjective {f : R →+* S} (hf : function.surjective f)
  (I : ideal S) :
  (I.comap f).minimal_primes = ideal.comap f '' I.minimal_primes :=
begin
  ext J,
  split,
  { intro H, obtain ⟨p, h, rfl⟩ := ideal.exists_minimal_primes_comap_eq f J H, exact ⟨p, h, rfl⟩ },
  { rintros ⟨J, hJ, rfl⟩, exact ideal.mimimal_primes_comap_of_surjective hf hJ }
end

lemma ideal.minimal_primes_eq_comap :
  I.minimal_primes = ideal.comap I^.quotient.mk '' minimal_primes (R ⧸ I) :=
begin
  rw [minimal_primes, ← ideal.comap_minimal_primes_eq_of_surjective ideal.quotient.mk_surjective,
    ← ring_hom.ker_eq_comap_bot, ideal.mk_ker],
end

lemma ideal.minimal_primes_eq_subsingleton (hI : I.is_primary) :
  I.minimal_primes = {I.radical} :=
begin
  ext J,
  split,
  { exact λ H, let e := H.1.1.radical_le_iff.mpr H.1.2 in
      (H.2 ⟨ideal.is_prime_radical hI, ideal.le_radical⟩ e).antisymm e },
  { rintro (rfl : J = I.radical),
    exact ⟨⟨ideal.is_prime_radical hI, ideal.le_radical⟩, λ _ H _, H.1.radical_le_iff.mpr H.2⟩ }
end

lemma ideal.minimal_primes_eq_subsingleton_self [I.is_prime] :
  I.minimal_primes = {I} :=
begin
  ext J,
  split,
  { exact λ H, (H.2 ⟨infer_instance, rfl.le⟩ H.1.2).antisymm H.1.2 },
  { unfreezingI { rintro (rfl : J = I) }, refine ⟨⟨infer_instance, rfl.le⟩, λ _ h _, h.2⟩ },
end

end
