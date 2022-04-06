/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import ring_theory.ideal.operations

/-!
# Ideals in product rings

For commutative rings `R` and `S` and ideals `I ≤ R`, `J ≤ S`, we define `ideal.prod I J` as the
product `I × J`, viewed as an ideal of `R × S`. In `ideal_prod_eq` we show that every ideal of
`R × S` is of this form.  Furthermore, we show that every prime ideal of `R × S` is of the form
`p × S` or `R × p`, where `p` is a prime ideal.
-/

universes u v
variables {R : Type u} {S : Type v} [ring R] [ring S] (I I' : ideal R) (J J' : ideal S)

namespace ideal

/-- `I × J` as an ideal of `R × S`. -/
def prod : ideal (R × S) :=
{ carrier := { x | x.fst ∈ I ∧ x.snd ∈ J },
  zero_mem' := by simp,
  add_mem' :=
  begin
    rintros ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩,
    exact ⟨I.add_mem ha₁ hb₁, J.add_mem ha₂ hb₂⟩
  end,
  smul_mem' :=
  begin
    rintros ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨hb₁, hb₂⟩,
    exact ⟨I.mul_mem_left _ hb₁, J.mul_mem_left _ hb₂⟩,
  end }

@[simp] lemma mem_prod {r : R} {s : S} : (⟨r, s⟩ : R × S) ∈ prod I J ↔ r ∈ I ∧ s ∈ J := iff.rfl
@[simp] lemma prod_top_top : prod (⊤ : ideal R) (⊤ : ideal S) = ⊤ := ideal.ext $ by simp

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
  simpa using I.add_mem (I.mul_mem_left (1, 0) h₁) (I.mul_mem_left (0, 1) h₂),
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

@[simp] lemma map_prod_comm_prod :
  map ↑(ring_equiv.prod_comm : R × S ≃+* S × R) (prod I J) = prod J I :=
begin
  refine trans (ideal_prod_eq _) _,
  simp [map_map],
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

lemma is_prime_of_is_prime_prod_top {I : ideal R} (h : (ideal.prod I (⊤ : ideal S)).is_prime) :
  I.is_prime :=
begin
  split,
  { unfreezingI { contrapose! h },
    simp [is_prime_iff, h] },
  { intros x y hxy,
    have : (⟨x, 1⟩ : R × S) * ⟨y, 1⟩ ∈ prod I ⊤,
    { rw [prod.mk_mul_mk, mul_one, mem_prod],
      exact ⟨hxy, trivial⟩ },
    simpa using h.mem_or_mem this }
end

lemma is_prime_of_is_prime_prod_top' {I : ideal S} (h : (ideal.prod (⊤ : ideal R) I).is_prime) :
  I.is_prime :=
begin
  apply @is_prime_of_is_prime_prod_top _ R,
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

lemma ideal_prod_prime_aux {I : ideal R} {J : ideal S} : (ideal.prod I J).is_prime →
  I = ⊤ ∨ J = ⊤ :=
begin
  contrapose!,
  simp only [ne_top_iff_one, is_prime_iff, not_and, not_forall, not_or_distrib],
  exact λ ⟨hI, hJ⟩ hIJ, ⟨⟨0, 1⟩, ⟨1, 0⟩, by simp, by simp [hJ], by simp [hI]⟩
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
    rcases ideal_prod_prime_aux hI with (h|h),
    { right,
      rw h at hI ⊢,
      exact ⟨_, ⟨is_prime_of_is_prime_prod_top' hI, rfl⟩⟩ },
    { left,
      rw h at hI ⊢,
      exact ⟨_, ⟨is_prime_of_is_prime_prod_top hI, rfl⟩⟩ } },
  { rintro (⟨p, ⟨h, rfl⟩⟩|⟨p, ⟨h, rfl⟩⟩),
    { exactI is_prime_ideal_prod_top },
    { exactI is_prime_ideal_prod_top' } }
end

@[simp] private def prime_ideals_equiv_impl :
  { I : ideal R // I.is_prime } ⊕ { J : ideal S // J.is_prime } →
    { K : ideal (R × S) // K.is_prime }
| (sum.inl ⟨I, hI⟩) := ⟨ideal.prod I ⊤, by exactI is_prime_ideal_prod_top⟩
| (sum.inr ⟨J, hJ⟩) := ⟨ideal.prod ⊤ J, by exactI is_prime_ideal_prod_top'⟩

section
variables (R S)

/-- The prime ideals of `R × S` are in bijection with the disjoint union of the prime ideals
    of `R` and the prime ideals of `S`. -/
noncomputable def prime_ideals_equiv : { K : ideal (R × S) // K.is_prime } ≃
  { I : ideal R // I.is_prime } ⊕ { J : ideal S // J.is_prime } :=
equiv.symm $ equiv.of_bijective prime_ideals_equiv_impl
begin
  split,
  { rintros (⟨I, hI⟩|⟨J, hJ⟩) (⟨I',  hI'⟩|⟨J', hJ'⟩) h;
    simp [prod.ext_iff] at h,
    { simp [h] },
    { exact false.elim (hI.ne_top h.1) },
    { exact false.elim (hJ.ne_top h.2) },
    { simp [h] } },
  { rintro ⟨I, hI⟩,
    rcases (ideal_prod_prime I).1 hI with (⟨p, ⟨hp, rfl⟩⟩|⟨p, ⟨hp, rfl⟩⟩),
    { exact ⟨sum.inl ⟨p, hp⟩, rfl⟩ },
    { exact ⟨sum.inr ⟨p, hp⟩, rfl⟩ } }
end

end

@[simp] lemma prime_ideals_equiv_symm_inl (h : I.is_prime) :
  (prime_ideals_equiv R S).symm (sum.inl ⟨I, h⟩) = ⟨prod I ⊤, by exactI is_prime_ideal_prod_top⟩ :=
rfl
@[simp] lemma prime_ideals_equiv_symm_inr (h : J.is_prime) :
  (prime_ideals_equiv R S).symm (sum.inr ⟨J, h⟩) = ⟨prod ⊤ J, by exactI is_prime_ideal_prod_top'⟩ :=
rfl

end ideal
