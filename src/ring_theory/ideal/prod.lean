/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import ring_theory.ideal.operations

universes u v
variables {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (I I' : ideal R) (J J' : ideal S)

namespace ideal

/-- `I × J` as an ideal of `α × β`. -/
def prod : ideal (R × S) :=
{ carrier := { x | x.fst ∈ I ∧ x.snd ∈ J },
  zero_mem' := by simp,
  add_mem' :=
  begin
    rintros ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩,
    refine ⟨ideal.add_mem _ _ _, ideal.add_mem _ _ _⟩;
    simp only [ha₁, ha₂, hb₁, hb₂]
  end,
  smul_mem' :=
  begin
    rintros ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨hb₁, hb₂⟩,
    refine ⟨ideal.mul_mem_left _ _, ideal.mul_mem_left _ _⟩;
    simp only [hb₁, hb₂]
  end }

@[simp] lemma mem_prod {r : R} {s : S} : (⟨r, s⟩ : R × S) ∈ prod I J ↔ r ∈ I ∧ s ∈ J := iff.rfl
@[simp] lemma prod_top_top : prod (⊤ : ideal R) (⊤ : ideal S) = ⊤ := ideal.ext $ by simp

@[simp] lemma map_prod_comm_prod :
  map (ring_equiv.prod_comm R S : R × S →+* S × R) (prod I J) = prod J I :=
begin
  apply ideal.ext,
  rintro ⟨s, r⟩,
  rw mem_map_iff_of_surjective (ring_equiv.prod_comm R S : R × S →+* S × R)
    (ring_equiv.prod_comm R S).surjective,
  refine ⟨_, _⟩,
  { rintro ⟨⟨r', s'⟩, ⟨⟨hr, hs⟩, h⟩⟩,
    simp only [prod.mk.inj_iff, prod.swap_prod_mk, ring_equiv.coe_coe_prod_comm] at h,
    rw [←h.1, ←h.2],
    exact ⟨hs, hr⟩ },
  { rintro ⟨(hs : s ∈ J), (hr : r ∈ I)⟩,
    exact ⟨⟨r, s⟩, ⟨⟨hr, hs⟩, rfl⟩⟩ }
end

/-- Every ideal of the product ring is of the form `I × J`, where `I` and `J` can be explicitly
    given as the image under the projection maps. -/
theorem ideal_prod_eq (I : ideal (R × S)) :
  I = ideal.prod (map (ring_hom.fst R S) I) (map (ring_hom.snd R S) I) :=
begin
  apply ideal.ext,
  rintro ⟨r, s⟩,
  rw [mem_prod, mem_map_iff_of_surjective (ring_hom.fst R S) prod.fst_surjective,
    mem_map_iff_of_surjective (ring_hom.snd R S) prod.snd_surjective],
  refine ⟨λ h, ⟨⟨_, ⟨h, rfl⟩⟩, ⟨_, ⟨h, rfl⟩⟩⟩, _⟩,
  rintro ⟨⟨⟨r, s'⟩, ⟨h₁, rfl⟩⟩, ⟨⟨r', s⟩, ⟨h₂, rfl⟩⟩⟩,
  have hr : (r, s') * (1, 0) ∈ I := ideal.mul_mem_right _ h₁,
  have hs : (r', s) * (0, 1) ∈ I := ideal.mul_mem_right _ h₂,
  simpa using ideal.add_mem _ hr hs
end

@[simp] lemma map_fst_prod (I : ideal R) (J : ideal S) : map (ring_hom.fst R S) (prod I J) = I :=
begin
  ext,
  rw mem_map_iff_of_surjective (ring_hom.fst R S) prod.fst_surjective,
  exact ⟨by { rintro ⟨x, ⟨h, rfl⟩⟩, exact h.1 }, λ h, ⟨⟨x, 0⟩, ⟨⟨h, ideal.zero_mem _⟩, rfl⟩⟩⟩
end

@[simp] lemma map_snd_prod (I : ideal R) (J : ideal S) : map (ring_hom.snd R S) (prod I J) = J :=
begin
  ext,
  rw mem_map_iff_of_surjective (ring_hom.snd R S) prod.snd_surjective,
  exact ⟨by { rintro ⟨x, ⟨h, rfl⟩⟩, exact h.2 }, λ h, ⟨⟨0, x⟩, ⟨⟨ideal.zero_mem _, h⟩, rfl⟩⟩⟩
end

/-- Ideals of `R × S` are in one-to-one correspondence with pairs of ideals of `R` and ideals of
    `S`. -/
def ideal_prod_equiv : ideal (R × S) ≃ ideal R × ideal S :=
{ to_fun := λ I, ⟨map (ring_hom.fst R S) I, map (ring_hom.snd R S) I⟩,
  inv_fun := λ I, prod I.1 I.2,
  left_inv := λ I, (ideal_prod_eq I).symm,
  right_inv := λ ⟨I, J⟩, by simp }

@[simp] lemma ideal_prod_equiv_symm_apply (I : ideal R) (J : ideal S) :
  ideal_prod_equiv.symm ⟨I, J⟩ = prod I J := rfl

lemma prod.ext_iff {I I' : ideal R} {J J' : ideal S} : prod I J = prod I' J' ↔ I = I' ∧ J = J' :=
by simp only [←ideal_prod_equiv_symm_apply, ideal_prod_equiv.symm.injective.eq_iff, prod.mk.inj_iff]

lemma ideal_prod_prime_aux₀ {I : ideal R} {J : ideal S} (h : (ideal.prod I J).is_prime) :
  I = ⊤ ∨ J = ⊤ :=
begin
  unfreezingI { revert h },
  contrapose!,
  simp only [ne_top_iff_one, is_prime],
  push_neg,
  exact λ ⟨hI, hJ⟩ hIJ, ⟨⟨0, 1⟩, ⟨1, 0⟩, by simp, by simp [hJ], by simp [hI]⟩
end

lemma ideal_prod_prime_aux₁ {I : ideal R} (h : (ideal.prod I (⊤ : ideal S)).is_prime) :
  I.is_prime :=
begin
  split,
  { unfreezingI { contrapose! h },
    simp [is_prime, h] },
  { intros x y hxy,
    have : (⟨x, 1⟩ : R × S) * ⟨y, 1⟩ ∈ prod I ⊤,
    { rw [prod.mk_mul_mk, mul_one, mem_prod],
      exact ⟨hxy, trivial⟩ },
    simpa using h.mem_or_mem this }
end

lemma ideal_prod_prime_aux₁' {I : ideal S} (h : (ideal.prod (⊤ : ideal R) I).is_prime) :
  I.is_prime :=
begin
  apply @ideal_prod_prime_aux₁ _ R,
  rw ←map_prod_comm_prod,
  exact map_is_prime_of_equiv _
end

lemma is_prime_ideal_prod_top {I : ideal R} [h : I.is_prime] : (prod I (⊤ : ideal S)).is_prime :=
begin
  split,
  { unfreezingI { rcases h with ⟨h, -⟩, contrapose! h },
    rw [←prod_top_top, prod.ext_iff] at h,
    exact h.1 },
  rintros ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨h₁, h₂⟩,
  cases h.mem_or_mem h₁ with h h,
  { exact or.inl ⟨h, trivial⟩ },
  { exact or.inr ⟨h, trivial⟩ }
end

lemma is_prime_ideal_prod_top' {I : ideal S} [h : I.is_prime] : (prod (⊤ : ideal R) I).is_prime :=
begin
  rw ←map_prod_comm_prod,
  apply map_is_prime_of_equiv _,
  exact is_prime_ideal_prod_top,
end

/-- Classification of prime ideals in product rings: the prime ideals of `R × S` are precisely the
    ideals of the form `p × S` or `R × p`, where `p` is a prime ideal of `R` or `S`. -/
theorem ideal_prod_prime (I : ideal (R × S)) : I.is_prime ↔
  ((∃ p : ideal R, p.is_prime ∧ I = ideal.prod p ⊤) ∨
   (∃ p : ideal S, p.is_prime ∧ I = ideal.prod ⊤ p)) :=
begin
  split,
  { rw ideal_prod_eq I,
    introsI hI,
    rcases ideal_prod_prime_aux₀ hI with (h|h),
    { right,
      rw h at hI ⊢,
      exact ⟨_, ⟨ideal_prod_prime_aux₁' hI, rfl⟩⟩ },
    { left,
      rw h at hI ⊢,
      exact ⟨_, ⟨ideal_prod_prime_aux₁ hI, rfl⟩⟩ } },
  { rintro (⟨p, ⟨h, rfl⟩⟩|⟨p, ⟨h, rfl⟩⟩),
    { exactI is_prime_ideal_prod_top },
    { exactI is_prime_ideal_prod_top' } }
end

end ideal
