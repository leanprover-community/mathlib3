/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.mv_polynomial
import ring_theory.ideals
import ring_theory.ideal_operations

universes u v

namespace ideal
section is_jacobson
variables {R : Type u} [comm_ring R] {I : ideal R}

/- Definition of jacobson rings in terms of radical ideals -/
@[class] def is_jacobson (R : Type u) [comm_ring R] :=
    ∀ (I : ideal R), I.radical = I → I.jacobson = I

/- Defining jacobson rings in terms of prime ideals is completely equivalent -/
lemma is_jacobson_iff : is_jacobson R ↔ ∀ P : ideal R, is_prime P → P.jacobson = P :=
begin
  split,
  { exact λ h I hI, h I (is_prime.radical hI) },
  { refine λ h I hI, le_antisymm (λ x hx, _) (λ x hx, mem_Inf.mpr (λ _ hJ, hJ.left hx)),
    erw mem_Inf at hx,
    rw [← hI, radical_eq_Inf I, mem_Inf],
    intros P hP,
    rw set.mem_set_of_eq at hP,
    erw [← h P hP.right, mem_Inf],
    exact λ J hJ, hx ⟨le_trans hP.left hJ.left, hJ.right⟩ }
end

lemma radical_eq_jacobson (H : is_jacobson R) (I : ideal R) : I.radical = I.jacobson :=
le_antisymm (le_Inf (λ J ⟨hJ, hJ_max⟩, (is_prime.radical_le_iff hJ_max.is_prime).mpr hJ))
            ((H I.radical (radical_idem I)) ▸ (jacobson_mono le_radical))

/- Fields have only two ideals, and the condition holds for both of them -/
theorem is_jacobson_field {K : Type u} [field K] : is_jacobson K :=
λ I hI, or.rec_on (eq_bot_or_top I)
(λ h, le_antisymm
  (Inf_le ⟨le_of_eq rfl, (eq.symm h) ▸ bot_is_maximal⟩)
  ((eq.symm h) ▸ bot_le))
(λ h, by rw [h, jacobson_eq_top_iff])

/- I equals its jacobson iff it can be written as an Inf of maximal ideals -/
lemma eq_jacobson_iff_Inf_maximal : jacobson I = I ↔
    ∃ M ⊆ {J : ideal R | I ≤ J ∧ (J.is_maximal ∨ J = ⊤)}, I = Inf M :=
begin
  use λ h, ⟨{J : ideal R | I ≤ J ∧ J.is_maximal}, ⟨(λ _ hJ, ⟨hJ.left, or.inl hJ.right⟩), eq.symm h⟩⟩,
  rintro ⟨M, hM, hInf⟩,
  refine le_antisymm _ le_jacobson,
  intros x hx,
  rw hInf,
  erw mem_Inf at *,
  intros I hI,
  specialize hM hI,
  cases hM.right with is_max is_top,
  { exact hx ⟨hM.left, is_max⟩ },
  { rw is_top, exact submodule.mem_top }
end

-- TODO: Can this be rewritten as a special case of a statement about images?
theorem is_jacobson_iso {S : Type u} [comm_ring S] (e : S ≃+* R)
  : is_jacobson S ↔ is_jacobson R :=
begin
  split, swap,
  replace e := e.symm, -- After this swap both proofs are identical
  all_goals {
    intros h I hI,
    specialize h (comap e.to_ring_hom I),
    rw ← comap_radical at h,
    specialize h (congr_arg _ hI),
    rw ← comap_jacobson at h,
    replace h := congr_arg (map e.to_ring_hom) h,
    rw map_comap_of_surjective (e.to_ring_hom) _ I at h,
    rw map_comap_of_surjective (e.to_ring_hom) _ I.jacobson at h,
    exact h,
    all_goals { apply equiv.surjective e.to_equiv }
  }
end

theorem is_jacobson_quotient [H : is_jacobson R] : is_jacobson (quotient I) :=
begin
  introsI p hp,
  rw eq_jacobson_iff_Inf_maximal,
  let S := {J : ideal R | quotient.comap_mk I p ≤ J ∧ J.is_maximal},
  use quotient.map_mk I '' S,
  split,
  { rintros j ⟨J, hJ, hmap⟩,
    refine ⟨hmap ▸ quotient.le_map_mk_of_comap_mk_le hJ.left, _⟩,
    exact hmap ▸ or.symm (quotient.top_or_maximal_of_maximal hJ.right) },
  { have : quotient.map_mk I ((quotient.comap_mk I p).jacobson) = p, {
      specialize H (quotient.comap_mk I p) (le_antisymm _ le_radical),
      exact (eq.symm (H)) ▸ (quotient.map_mk_comap_mk_left_inverse p),
      {
        rw ← quotient.map_mk_le_iff_le_comap_mk,
        rintros ⟨x⟩ ⟨y, ⟨⟨n, hy⟩, hxy⟩⟩,
        rw [← hxy, ← hp],
        use n,
        rw ← quotient.mk_pow,
        use hy,
      }
    },
    exact this ▸ (quotient.map_mk_Inf (λ J hJ, le_trans (quotient.comap_mk_ge) hJ.left)) }
end

-- lemma is_jacobson_polynomial (H : is_jacobson R) : is_jacobson (polynomial R) := sorry

-- lemma is_jacobson_mv_polynomial (H : is_jacobson R) (n : ℕ) :
--   is_jacobson (mv_polynomial (fin n) R) := nat.rec_on n
-- ((is_jacobson_iso ((mv_polynomial.ring_equiv_of_equiv R (equiv.equiv_pempty $ fin.elim0)).trans
--                     (mv_polynomial.pempty_ring_equiv R))).mpr H)
-- (λ n hn, (is_jacobson_iso (mv_polynomial.fin_succ_equiv R n)).mpr
--                     (@ideal.is_jacobson_polynomial _ _ hn))

end is_jacobson
end ideal
