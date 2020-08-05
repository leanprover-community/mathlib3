/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma
-/
import ring_theory.ideal_operations

/-!
# Jacobson radical

The Jacobson radical of a ring `R` is defined to be the intersection of all maximal ideals of `R`.
This is similar to how the nilradical is equal to the intersection of all prime ideals of `R`.

We can extend the idea of the nilradical to ideals of `R`,
by letting the radical of an ideal `I` be the intersection of prime ideals containing `I`.
Under this extension, the original nilradical is the radical of the zero ideal `⊥`.
Here we define the Jacobson radical of an ideal `I` in a similar way,
as the intersection of maximal ideals containing `I`.

## Main definitions

Let `R` be a commutative ring, and `I` be an ideal of `R`

* `jacobson I` is the jacobson radical, i.e. the infimum of all maximal ideals containing I.

* `is_local I` is the proposition that the jacobson radical of `I` is itself a maximal ideal

## Main statements

* `mem_jacobson_iff` gives a characterization of members of the jacobson of I

* `is_local_of_is_maximal_radical`: if the radical of I is maximal then so is the jacobson radical

## Tags

Jacobson, Jacobson radical, Local Ideal

-/

universes u v

namespace ideal
variables {R : Type u} [comm_ring R]
variables {S : Type v} [comm_ring S]

section jacobson

/-- The Jacobson radical of `I` is the infimum of all maximal ideals containing `I`. -/
def jacobson (I : ideal R) : ideal R :=
Inf {J : ideal R | I ≤ J ∧ is_maximal J}

lemma le_jacobson {I : ideal R} : I ≤ jacobson I :=
λ x hx, mem_Inf.mpr (λ J hJ, hJ.left hx)

lemma radical_le_jacobson {I : ideal R} : radical I ≤ jacobson I :=
le_Inf (λ J hJ, (radical_eq_Inf I).symm ▸ Inf_le ⟨hJ.left, is_maximal.is_prime hJ.right⟩)

lemma eq_radical_of_eq_jacobson {I : ideal R} : jacobson I = I → radical I = I :=
λ h, le_antisymm (le_trans radical_le_jacobson (le_of_eq h)) le_radical

@[simp] lemma jacobson_top : jacobson (⊤ : ideal R) = ⊤ :=
eq_top_iff.2 le_jacobson

@[simp] theorem jacobson_eq_top_iff {I : ideal R} : jacobson I = ⊤ ↔ I = ⊤ :=
⟨λ H, classical.by_contradiction $ λ hi, let ⟨M, hm, him⟩ := exists_le_maximal I hi in
  lt_top_iff_ne_top.1 (lt_of_le_of_lt (show jacobson I ≤ M, from Inf_le ⟨him, hm⟩) $ lt_top_iff_ne_top.2 hm.1) H,
λ H, eq_top_iff.2 $ le_Inf $ λ J ⟨hij, hj⟩, H ▸ hij⟩

lemma jacobson_eq_bot {I : ideal R} : jacobson I = ⊥ → I = ⊥ :=
λ h, eq_bot_iff.mpr (h ▸ le_jacobson)

lemma jacobson_eq_self_of_is_maximal  {I : ideal R} [H : is_maximal I] : I.jacobson = I :=
le_antisymm (Inf_le ⟨le_of_eq rfl, H⟩) le_jacobson

@[priority 100]
instance jacobson.is_maximal {I : ideal R} [H : is_maximal I] : is_maximal (jacobson I) :=
⟨λ htop, H.left (jacobson_eq_top_iff.1 htop),
  λ J hJ, H.right _ (lt_of_le_of_lt le_jacobson hJ)⟩

theorem mem_jacobson_iff {I : ideal R} {x : R} :
  x ∈ jacobson I ↔ ∀ y, ∃ z, x * y * z + z - 1 ∈ I :=
⟨λ hx y, classical.by_cases
  (assume hxy : I ⊔ span {x * y + 1} = ⊤,
    let ⟨p, hpi, q, hq, hpq⟩ := submodule.mem_sup.1 ((eq_top_iff_one _).1 hxy) in
    let ⟨r, hr⟩ := mem_span_singleton.1 hq in
    ⟨r, by rw [← one_mul r, ← mul_assoc, ← add_mul, mul_one, ← hr, ← hpq, ← neg_sub, add_sub_cancel]; exact I.neg_mem hpi⟩)
  (assume hxy : I ⊔ span {x * y + 1} ≠ ⊤,
    let ⟨M, hm1, hm2⟩ := exists_le_maximal _ hxy in
    suffices x ∉ M, from (this $ mem_Inf.1 hx ⟨le_trans le_sup_left hm2, hm1⟩).elim,
    λ hxm, hm1.1 $ (eq_top_iff_one _).2 $ add_sub_cancel' (x * y) 1 ▸ M.sub_mem
      (le_trans le_sup_right hm2 $ mem_span_singleton.2 $ dvd_refl _)
      (M.mul_mem_right hxm)),
λ hx, mem_Inf.2 $ λ M ⟨him, hm⟩, classical.by_contradiction $ λ hxm,
  let ⟨y, hy⟩ := hm.exists_inv hxm, ⟨z, hz⟩ := hx (-y) in
  hm.1 $ (eq_top_iff_one _).2 $ sub_sub_cancel (x * -y * z + z) 1 ▸ M.sub_mem
    (by rw [← one_mul z, ← mul_assoc, ← add_mul, mul_one, mul_neg_eq_neg_mul_symm, neg_add_eq_sub, ← neg_sub,
        neg_mul_eq_neg_mul_symm, neg_mul_eq_mul_neg, mul_comm x y]; exact M.mul_mem_right hy)
    (him hz)⟩

/-- An ideal equals its jacobson radical iff it is the intersection of a set of maximal ideal.
Allowing the set to include ⊤ is equivalent, and is included only to simplify some proofs. -/
theorem eq_jacobson_iff_Inf_maximal {I : ideal R} :
  I.jacobson = I ↔ ∃ M : set (ideal R), (∀ J ∈ M, is_maximal J ∨ J = ⊤) ∧ I = Inf M :=
begin
  use λ hI, ⟨{J : ideal R | I ≤ J ∧ J.is_maximal}, ⟨λ _ hJ, or.inl hJ.right, hI.symm⟩⟩,
  rintros ⟨M, hM, hInf⟩,
  refine le_antisymm _ le_jacobson,
  intros x hx,
  rw hInf,
  erw mem_Inf at ⊢ hx,
  intros I hI,
  cases hM I hI with is_max is_top,
  { refine hx ⟨le_Inf_iff.1 (le_of_eq hInf) I hI, is_max⟩ },
  { rw is_top, exact submodule.mem_top }
end

/-- An ideal `I` equals its jacobson radical if and only if every element outside `I`
also lies outside of a maximal ideal containing `I`. -/
lemma eq_jacobson_iff_not_mem {I : ideal R} :
  I.jacobson = I ↔ ∀ x ∉ I, ∃ M : ideal R, (I ≤ M ∧ M.is_maximal) ∧ x ∉ M :=
begin
  split,
  { intros h x hx,
    erw [← h, mem_Inf] at hx,
    push_neg at hx,
    exact hx },
  { refine λ h, le_antisymm (λ x hx, _) le_jacobson,
    contrapose hx,
    erw mem_Inf,
    push_neg,
    exact h x hx }
end

theorem map_jacobson_of_surjective {f : R →+* S} (hf : function.surjective f) {I : ideal R} :
  ring_hom.ker f ≤ I → map f (I.jacobson) = (map f I).jacobson :=
begin
  intro h,
  rw [ideal.jacobson, ideal.jacobson],
  refine trans (map_Inf hf (λ J hJ, le_trans h hJ.left)) (le_antisymm _ _);
  rw le_Inf_iff,
  { intros J hJ,
    refine Inf_le _,
    rw set.mem_image,
    exact ⟨comap f J, ⟨⟨le_trans le_comap_map (comap_mono hJ.left),
      comap_is_maximal_of_surjective _ hf hJ.right⟩,
      map_comap_of_surjective _ hf J⟩⟩ },
  { intros j hj,
    have : Inf { J : ideal S | map f I ≤ J ∧ J.is_maximal }
      = Inf (insert ⊤ { J : ideal S | map f I ≤ J ∧ J.is_maximal }),
    by rw [Inf_insert, top_inf_eq],
    refine le_trans (le_of_eq this) (Inf_le _),
    rw set.mem_image at hj,
    cases hj with J hJ,
    rw ← hJ.right,
    cases map_eq_top_or_is_maximal_of_surjective f hf hJ.left.right with htop hmax,
    { exact or.inl htop },
    { exact or.inr ⟨map_mono hJ.left.left, hmax⟩ } }
end

theorem comap_jacobson_of_surjective {f : R →+* S} (hf : function.surjective f) {K : ideal S} :
  comap f (K.jacobson) = (comap f K).jacobson :=
begin
  rw [ideal.jacobson, ideal.jacobson],
  refine le_antisymm _ _,
  { rw le_Inf_iff,
    intros J hJ,
    intros x hx,
    rw mem_comap at hx,
    rw mem_Inf at hx,
    cases map_eq_top_or_is_maximal_of_surjective _ hf hJ.right with htop hmax,
    { replace htop := congr_arg (comap f) htop,
      rw comap_map_of_surjective _ hf at htop,
      rw comap_top at htop,
      have : ⊤ ≤ J,
      { rw [← htop, sup_le_iff],
        exact ⟨le_of_eq rfl, le_trans (comap_mono bot_le) hJ.left⟩ },
      exact this submodule.mem_top },
    { replace hx := @hx (map f J)
        ⟨le_trans (le_of_eq (map_comap_of_surjective _ hf K).symm) (map_mono hJ.left), hmax⟩,
      rw mem_map_iff_of_surjective _ hf at hx,
      cases hx with x' hx',
      have : x - x' ∈ J,
      { apply hJ.left,
        rw [mem_comap, ring_hom.map_sub, hx'.right, sub_self],
        exact K.zero_mem },
      have := J.add_mem this hx'.left,
      simpa using this },
  },
  { rw comap_Inf,
    rw le_infi_iff,
    intros J,
    rw le_infi_iff,
    intros hJ,
    refine Inf_le ⟨comap_mono hJ.left, comap_is_maximal_of_surjective _ hf hJ.right⟩ }
end

/-- An ideal `I` of `R` is equal to its jacobson radical if and only if
the jacobson radical of the quotient ring `R/I` is the zero ideal -/
theorem jacobson_eq_iff_jacobson_bot_eq {I : ideal R} :
  I.jacobson = I ↔ jacobson (⊥ : ideal (I.quotient)) = ⊥ :=
begin
  have hf : function.surjective (quotient.mk I) := submodule.quotient.mk_surjective I,
  split,
  { intro h,
    replace h := congr_arg (map (quotient.mk I)) h,
    rw map_jacobson_of_surjective hf (le_of_eq mk_ker) at h,
    simpa using h },
  { intro h,
    replace h := congr_arg (comap (quotient.mk I)) h,
    rw [comap_jacobson_of_surjective hf, ← ker_eq_comap_bot (quotient.mk I)] at h,
    simpa using h }
end

/-- The standard radical and jacobson radical of an ideal `I` of `R` are equal if and only if
the nilradical and jacobson radical of the quotient ring `R/I` coincide -/
theorem radical_eq_jacobson_iff_radical_bot_eq_jacobson_bot {I : ideal R} :
  I.radical = I.jacobson ↔ radical (⊥ : ideal (I.quotient)) = jacobson ⊥ :=
begin
  have hf : function.surjective (quotient.mk I) := submodule.quotient.mk_surjective I,
  split,
  { intro h,
    have := congr_arg (map (quotient.mk I)) h,
    rw [map_radical hf (le_of_eq mk_ker), map_jacobson_of_surjective hf (le_of_eq mk_ker)] at this,
    simpa using this },
  { intro h,
    have := congr_arg (comap (quotient.mk I)) h,
    rw [comap_radical, comap_jacobson_of_surjective hf, ← ker_eq_comap_bot (quotient.mk I)] at this,
    simpa using this }
end

@[mono] lemma jacobson_mono {I J : ideal R} : I ≤ J → I.jacobson ≤ J.jacobson :=
begin
  intros h x hx,
  erw mem_Inf at ⊢ hx,
  exact λ K ⟨hK, hK_max⟩, hx ⟨trans h hK, hK_max⟩
end

end jacobson

section is_local

/-- An ideal `I` is local iff its Jacobson radical is maximal. -/
@[class] def is_local (I : ideal R) : Prop :=
is_maximal (jacobson I)

theorem is_local_of_is_maximal_radical {I : ideal R} (hi : is_maximal (radical I)) : is_local I :=
have radical I = jacobson I,
from le_antisymm (le_Inf $ λ M ⟨him, hm⟩, hm.is_prime.radical_le_iff.2 him)
  (Inf_le ⟨le_radical, hi⟩),
show is_maximal (jacobson I), from this ▸ hi

theorem is_local.le_jacobson {I J : ideal R} (hi : is_local I) (hij : I ≤ J) (hj : J ≠ ⊤) : J ≤ jacobson I :=
let ⟨M, hm, hjm⟩ := exists_le_maximal J hj in
le_trans hjm $ le_of_eq $ eq.symm $ hi.eq_of_le hm.1 $ Inf_le ⟨le_trans hij hjm, hm⟩

theorem is_local.mem_jacobson_or_exists_inv {I : ideal R} (hi : is_local I) (x : R) :
  x ∈ jacobson I ∨ ∃ y, y * x - 1 ∈ I :=
classical.by_cases
  (assume h : I ⊔ span {x} = ⊤,
    let ⟨p, hpi, q, hq, hpq⟩ := submodule.mem_sup.1 ((eq_top_iff_one _).1 h) in
    let ⟨r, hr⟩ := mem_span_singleton.1 hq in
    or.inr ⟨r, by rw [← hpq, mul_comm, ← hr, ← neg_sub, add_sub_cancel]; exact I.neg_mem hpi⟩)
  (assume h : I ⊔ span {x} ≠ ⊤,
    or.inl $ le_trans le_sup_right (hi.le_jacobson le_sup_left h) $ mem_span_singleton.2 $ dvd_refl x)

end is_local

theorem is_primary_of_is_maximal_radical {I : ideal R} (hi : is_maximal (radical I)) : is_primary I :=
have radical I = jacobson I,
from le_antisymm (le_Inf $ λ M ⟨him, hm⟩, hm.is_prime.radical_le_iff.2 him)
  (Inf_le ⟨le_radical, hi⟩),
⟨ne_top_of_lt $ lt_of_le_of_lt le_radical (lt_top_iff_ne_top.2 hi.1),
λ x y hxy, ((is_local_of_is_maximal_radical hi).mem_jacobson_or_exists_inv y).symm.imp
  (λ ⟨z, hz⟩, by rw [← mul_one x, ← sub_sub_cancel (z * y) 1, mul_sub, mul_left_comm]; exact
    I.sub_mem (I.mul_mem_left hxy) (I.mul_mem_left hz))
  (this ▸ id)⟩


end ideal
