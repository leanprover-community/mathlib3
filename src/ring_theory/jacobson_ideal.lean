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

section jacobson

/-- The Jacobson radical of `I` is the infimum of all maximal ideals containing `I`. -/
def jacobson (I : ideal R) : ideal R :=
Inf {J : ideal R | I ≤ J ∧ is_maximal J}

lemma le_jacobson {I : ideal R} : I ≤ jacobson I :=
λ x hx, mem_Inf.mpr (λ J hJ, hJ.left hx)

@[simp] lemma jacobson_top : jacobson (⊤ : ideal R) = ⊤ :=
eq_top_iff.2 le_jacobson

@[simp] theorem jacobson_eq_top_iff {I : ideal R} : jacobson I = ⊤ ↔ I = ⊤ :=
⟨λ H, classical.by_contradiction $ λ hi, let ⟨M, hm, him⟩ := exists_le_maximal I hi in
  lt_top_iff_ne_top.1 (lt_of_le_of_lt (show jacobson I ≤ M, from Inf_le ⟨him, hm⟩) $ lt_top_iff_ne_top.2 hm.1) H,
λ H, eq_top_iff.2 $ le_Inf $ λ J ⟨hij, hj⟩, H ▸ hij⟩

lemma jacobson_eq_bot {I : ideal R} : jacobson I = ⊥ → I = ⊥ :=
λ h, eq_bot_iff.mpr (h ▸ le_jacobson)

lemma jacobson.is_maximal {I : ideal R} : is_maximal I → is_maximal (jacobson I) :=
λ h, ⟨λ htop, h.left (jacobson_eq_top_iff.1 htop),
  λ J hJ, h.right _ (lt_of_le_of_lt le_jacobson hJ)⟩

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
