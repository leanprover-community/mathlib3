/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.mv_polynomial
import ring_theory.ideal.over
import ring_theory.jacobson_ideal
import ring_theory.localization

/-!
# Jacobson Rings
The following conditions are equivalent for a ring `R`:
1. Every radical ideal `I` is equal to its Jacobson radical
2. Every radical ideal `I` can be written as an intersection of maximal ideals
3. Every prime ideal `I` is equal to its Jacobson radical
Any ring satisfying any of these equivalent conditions is said to be Jacobson.
Some particular examples of Jacobson rings are also proven.
`is_jacobson_quotient` says that the quotient of a Jacobson ring is Jacobson.
`is_jacobson_localization` says the localization of a Jacobson ring to a single element is Jacobson.
`is_jacobson_polynomial_iff_is_jacobson` says polynomials over a Jacobson ring form a Jacobson ring.
## Main definitions
Let `R` be a commutative ring. Jacobson Rings are defined using the first of the above conditions
* `is_jacobson R` is the proposition that `R` is a Jacobson ring. It is a class,
  implemented as the predicate that for any ideal, `I.radical = I` implies `I.jacobson = I`.

## Main statements
* `is_jacobson_iff_prime_eq` is the equivalence between conditions 1 and 3 above.
* `is_jacobson_iff_Inf_maximal` is the equivalence between conditions 1 and 2 above.
* `is_jacobson_of_surjective` says that if `R` is a Jacobson ring and `f : R →+* S` is surjective,
  then `S` is also a Jacobson ring
* `is_jacobson_mv_polynomial` says that multi-variate polynomials over a Jacobson ring are Jacobson.
## Tags
Jacobson, Jacobson Ring
-/

namespace ideal

open polynomial

section is_jacobson
variables {R S : Type*} [comm_ring R] [comm_ring S] {I : ideal R}

/-- A ring is a Jacobson ring if for every radical ideal `I`,
 the Jacobson radical of `I` is equal to `I`.
 See `is_jacobson_iff_prime_eq` and `is_jacobson_iff_Inf_maximal` for equivalent definitions. -/
class is_jacobson (R : Type*) [comm_ring R] : Prop :=
(out' : ∀ (I : ideal R), I.radical = I → I.jacobson = I)

theorem is_jacobson_iff {R} [comm_ring R] :
  is_jacobson R ↔ ∀ (I : ideal R), I.radical = I → I.jacobson = I :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

theorem is_jacobson.out {R} [comm_ring R] :
  is_jacobson R → ∀ {I : ideal R}, I.radical = I → I.jacobson = I := is_jacobson_iff.1

/--  A ring is a Jacobson ring if and only if for all prime ideals `P`,
 the Jacobson radical of `P` is equal to `P`. -/
lemma is_jacobson_iff_prime_eq : is_jacobson R ↔ ∀ P : ideal R, is_prime P → P.jacobson = P :=
begin
  refine is_jacobson_iff.trans ⟨λ h I hI, h I (is_prime.radical hI), _⟩,
  refine λ h I hI, le_antisymm (λ x hx, _) (λ x hx, mem_Inf.mpr (λ _ hJ, hJ.left hx)),
  rw [← hI, radical_eq_Inf I, mem_Inf],
  intros P hP,
  rw set.mem_set_of_eq at hP,
  erw mem_Inf at hx,
  erw [← h P hP.right, mem_Inf],
  exact λ J hJ, hx ⟨le_trans hP.left hJ.left, hJ.right⟩
end

/-- A ring `R` is Jacobson if and only if for every prime ideal `I`,
 `I` can be written as the infimum of some collection of maximal ideals.
 Allowing ⊤ in the set `M` of maximal ideals is equivalent, but makes some proofs cleaner. -/
lemma is_jacobson_iff_Inf_maximal : is_jacobson R ↔
  ∀ {I : ideal R}, I.is_prime → ∃ M : set (ideal R), (∀ J ∈ M, is_maximal J ∨ J = ⊤) ∧ I = Inf M :=
⟨λ H I h, eq_jacobson_iff_Inf_maximal.1 (H.out (is_prime.radical h)),
  λ H, is_jacobson_iff_prime_eq.2 (λ P hP, eq_jacobson_iff_Inf_maximal.2 (H hP))⟩

lemma is_jacobson_iff_Inf_maximal' : is_jacobson R ↔
  ∀ {I : ideal R}, I.is_prime → ∃ M : set (ideal R),
  (∀ (J ∈ M) (K : ideal R), J < K → K = ⊤) ∧ I = Inf M :=
⟨λ H I h, eq_jacobson_iff_Inf_maximal'.1 (H.out (is_prime.radical h)),
  λ H, is_jacobson_iff_prime_eq.2 (λ P hP, eq_jacobson_iff_Inf_maximal'.2 (H hP))⟩

lemma radical_eq_jacobson [H : is_jacobson R] (I : ideal R) : I.radical = I.jacobson :=
le_antisymm (le_Inf (λ J ⟨hJ, hJ_max⟩, (is_prime.radical_le_iff hJ_max.is_prime).mpr hJ))
            ((H.out (radical_idem I)) ▸ (jacobson_mono le_radical))

/-- Fields have only two ideals, and the condition holds for both of them.  -/
@[priority 100]
instance is_jacobson_field {K : Type*} [field K] : is_jacobson K :=
⟨λ I hI, or.rec_on (eq_bot_or_top I)
(λ h, le_antisymm
  (Inf_le ⟨le_of_eq rfl, (eq.symm h) ▸ bot_is_maximal⟩)
  ((eq.symm h) ▸ bot_le))
(λ h, by rw [h, jacobson_eq_top_iff])⟩

theorem is_jacobson_of_surjective [H : is_jacobson R] :
  (∃ (f : R →+* S), function.surjective f) → is_jacobson S :=
begin
  rintros ⟨f, hf⟩,
  rw is_jacobson_iff_Inf_maximal,
  intros p hp,
  use map f '' {J : ideal R | comap f p ≤ J ∧ J.is_maximal },
  use λ j ⟨J, hJ, hmap⟩, hmap ▸ or.symm (map_eq_top_or_is_maximal_of_surjective f hf hJ.right),
  have : p = map f ((comap f p).jacobson),
  from (is_jacobson.out' (comap f p) (by rw [← comap_radical, is_prime.radical hp])).symm
    ▸ (map_comap_of_surjective f hf p).symm,
  exact eq.trans this (map_Inf hf (λ J ⟨hJ, _⟩, le_trans (ideal.ker_le_comap f) hJ)),
end

@[priority 100]
instance is_jacobson_quotient [is_jacobson R] : is_jacobson (quotient I) :=
is_jacobson_of_surjective ⟨quotient.mk I, (by rintro ⟨x⟩; use x; refl)⟩

lemma is_jacobson_iso (e : R ≃+* S) : is_jacobson R ↔ is_jacobson S :=
⟨λ h, @is_jacobson_of_surjective _ _ _ _ h ⟨(e : R →+* S), e.surjective⟩,
  λ h, @is_jacobson_of_surjective _ _ _ _ h ⟨(e.symm : S →+* R), e.symm.surjective⟩⟩

lemma is_jacobson_of_is_integral [algebra R S] (hRS : algebra.is_integral R S)
  (hR : is_jacobson R) : is_jacobson S :=
begin
  rw is_jacobson_iff_prime_eq,
  introsI P hP,
  by_cases hP_top : comap (algebra_map R S) P = ⊤,
  { simp [comap_eq_top_iff.1 hP_top] },
  { haveI : nontrivial (comap (algebra_map R S) P).quotient := quotient.nontrivial hP_top,
    rw jacobson_eq_iff_jacobson_quotient_eq_bot,
    refine eq_bot_of_comap_eq_bot (is_integral_quotient_of_is_integral hRS) _,
    rw [eq_bot_iff, ← jacobson_eq_iff_jacobson_quotient_eq_bot.1 ((is_jacobson_iff_prime_eq.1 hR)
      (comap (algebra_map R S) P) (comap_is_prime _ _)), comap_jacobson],
    refine Inf_le_Inf (λ J hJ, _),
    simp only [true_and, set.mem_image, bot_le, set.mem_set_of_eq],
    haveI : J.is_maximal := by simpa using hJ,
    exact exists_ideal_over_maximal_of_is_integral (is_integral_quotient_of_is_integral hRS) J
      (comap_bot_le_of_injective _ algebra_map_quotient_injective) }
end

lemma is_jacobson_of_is_integral' (f : R →+* S) (hf : f.is_integral)
  (hR : is_jacobson R) : is_jacobson S :=
@is_jacobson_of_is_integral _ _ _ _ f.to_algebra hf hR

end is_jacobson


section localization
open localization_map submonoid
variables {R S : Type*} [comm_ring R] [comm_ring S] {I : ideal R}
variables {y : R} (f : away_map y S)

lemma disjoint_powers_iff_not_mem (hI : I.radical = I) :
  disjoint ((submonoid.powers y) : set R) ↑I ↔ y ∉ I.1 :=
begin
  refine ⟨λ h, set.disjoint_left.1 h (mem_powers _), λ h, (disjoint_iff).mpr (eq_bot_iff.mpr _)⟩,
  rintros x ⟨⟨n, rfl⟩, hx'⟩,
  rw [← hI] at hx',
  exact absurd (hI ▸ mem_radical_of_pow_mem hx' : y ∈ I.carrier) h
end

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its comap.
See `le_rel_iso_of_maximal` for the more general relation isomorphism -/
lemma is_maximal_iff_is_maximal_disjoint [H : is_jacobson R] (J : ideal S) :
  J.is_maximal ↔ (comap f.to_map J).is_maximal ∧ y ∉ ideal.comap f.to_map J :=
begin
  split,
  { refine λ h, ⟨_, λ hy, h.ne_top (ideal.eq_top_of_is_unit_mem _ hy
      (map_units f ⟨y, submonoid.mem_powers _⟩))⟩,
    have hJ : J.is_prime := is_maximal.is_prime h,
    rw is_prime_iff_is_prime_disjoint f at hJ,
    have : y ∉ (comap f.to_map J).1 :=
      set.disjoint_left.1 hJ.right (submonoid.mem_powers _),
    erw [← H.out (is_prime.radical hJ.left), mem_Inf] at this,
    push_neg at this,
    rcases this with ⟨I, hI, hI'⟩,
    convert hI.right,
    by_cases hJ : J = map f.to_map I,
    { rw [hJ, comap_map_of_is_prime_disjoint f I (is_maximal.is_prime hI.right)],
      rwa disjoint_powers_iff_not_mem (is_maximal.is_prime hI.right).radical},
    { have hI_p : (map f.to_map I).is_prime,
      { refine is_prime_of_is_prime_disjoint f I hI.right.is_prime _,
        rwa disjoint_powers_iff_not_mem (is_maximal.is_prime hI.right).radical },
      have : J ≤ map f.to_map I := (map_comap f J) ▸ (map_mono hI.left),
      exact absurd (h.1.2 _ (lt_of_le_of_ne this hJ)) hI_p.1 } },
  { refine λ h, ⟨⟨λ hJ, h.1.ne_top (eq_top_iff.2 _), λ I hI, _⟩⟩,
    { rwa [eq_top_iff, ← f.order_embedding.le_iff_le] at hJ },
    { have := congr_arg (map f.to_map) (h.1.1.2 _ ⟨comap_mono (le_of_lt hI), _⟩),
      rwa [map_comap f I, map_top f.to_map] at this,
      refine λ hI', hI.right _,
      rw [← map_comap f I, ← map_comap f J],
      exact map_mono hI' } }
end

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its map.
See `le_rel_iso_of_maximal` for the more general statement, and the reverse of this implication -/
lemma is_maximal_of_is_maximal_disjoint [is_jacobson R] (I : ideal R) (hI : I.is_maximal)
  (hy : y ∉ I) : (map f.to_map I).is_maximal :=
begin
  rw [is_maximal_iff_is_maximal_disjoint f,
    comap_map_of_is_prime_disjoint f I (is_maximal.is_prime hI)
    ((disjoint_powers_iff_not_mem (is_maximal.is_prime hI).radical).2 hy)],
  exact ⟨hI, hy⟩
end

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y` -/
def order_iso_of_maximal [is_jacobson R] :
  {p : ideal S // p.is_maximal} ≃o {p : ideal R // p.is_maximal ∧ y ∉ p} :=
{ to_fun := λ p, ⟨ideal.comap f.to_map p.1, (is_maximal_iff_is_maximal_disjoint f p.1).1 p.2⟩,
  inv_fun := λ p, ⟨ideal.map f.to_map p.1, is_maximal_of_is_maximal_disjoint f p.1 p.2.1 p.2.2⟩,
  left_inv := λ J, subtype.eq (map_comap f J),
  right_inv := λ I, subtype.eq (comap_map_of_is_prime_disjoint f I.1 (is_maximal.is_prime I.2.1)
    ((disjoint_powers_iff_not_mem I.2.1.is_prime.radical).2 I.2.2)),
  map_rel_iff' := λ I I', ⟨λ h, (show I.val ≤ I'.val,
    from (map_comap f I.val) ▸ (map_comap f I'.val) ▸ (ideal.map_mono h)), λ h x hx, h hx⟩ }

/-- If `S` is the localization of the Jacobson ring `R` at the submonoid generated by `y : R`, then
`S` is Jacobson. -/
lemma is_jacobson_localization [H : is_jacobson R]
  (f : away_map y S) : is_jacobson S :=
begin
  rw is_jacobson_iff_prime_eq,
  refine λ P' hP', le_antisymm _ le_jacobson,
  obtain ⟨hP', hPM⟩ := (localization_map.is_prime_iff_is_prime_disjoint f P').mp hP',
  have hP := H.out (is_prime.radical hP'),
  refine le_trans (le_trans (le_of_eq (localization_map.map_comap f P'.jacobson).symm) (map_mono _))
    (le_of_eq (localization_map.map_comap f P')),
  have : Inf { I : ideal R | comap f.to_map P' ≤ I ∧ I.is_maximal ∧ y ∉ I } ≤ comap f.to_map P',
  { intros x hx,
    have hxy : x * y ∈ (comap f.to_map P').jacobson,
    { rw [ideal.jacobson, mem_Inf],
      intros J hJ,
      by_cases y ∈ J,
      { exact J.smul_mem x h },
      { exact (mul_comm y x) ▸ J.smul_mem y ((mem_Inf.1 hx) ⟨hJ.left, ⟨hJ.right, h⟩⟩) } },
    rw hP at hxy,
    cases hP'.mem_or_mem hxy with hxy hxy,
    { exact hxy },
    { exact (hPM ⟨submonoid.mem_powers _, hxy⟩).elim } },
  refine le_trans _ this,
  rw [ideal.jacobson, comap_Inf', Inf_eq_infi],
  refine infi_le_infi_of_subset (λ I hI, ⟨map f.to_map I, ⟨_, _⟩⟩),
  { exact ⟨le_trans (le_of_eq ((localization_map.map_comap f P').symm)) (map_mono hI.1),
    is_maximal_of_is_maximal_disjoint f _ hI.2.1 hI.2.2⟩ },
  { exact localization_map.comap_map_of_is_prime_disjoint f I (is_maximal.is_prime hI.2.1)
    ((disjoint_powers_iff_not_mem hI.2.1.is_prime.radical).2 hI.2.2) }
end

end localization

namespace polynomial
open polynomial

section comm_ring
variables {R S : Type*} [comm_ring R] [integral_domain S]
variables {Rₘ Sₘ : Type*} [comm_ring Rₘ] [comm_ring Sₘ]

/-- If `I` is a prime ideal of `polynomial R` and `pX ∈ I` is a non-constant polynomial,
  then the map `R →+* R[x]/I` descends to an integral map when localizing at `pX.leading_coeff`.
  In particular `X` is integral because it satisfies `pX`, and constants are trivially integral,
  so integrality of the entire extension follows by closure under addition and multiplication. -/
lemma is_integral_localization_map_polynomial_quotient
  (P : ideal (polynomial R)) [P.is_prime] (pX : polynomial R) (hpX : pX ∈ P)
  (ϕ : localization_map (submonoid.powers (pX.map (quotient.mk (P.comap C))).leading_coeff) Rₘ)
  (ϕ' : localization_map ((submonoid.powers (pX.map (quotient.mk (P.comap C))).leading_coeff).map
    (quotient_map P C le_rfl) : submonoid P.quotient) Sₘ) :
  (ϕ.map ((submonoid.powers (pX.map (quotient.mk (P.comap C))).leading_coeff).mem_map_of_mem
      (quotient_map P C le_rfl : (P.comap C : ideal R).quotient →* P.quotient)) ϕ').is_integral :=
begin
  let P' : ideal R := P.comap C,
  let M : submonoid P'.quotient :=
  submonoid.powers (pX.map (quotient.mk (P.comap C))).leading_coeff,
  let φ : P'.quotient →+* P.quotient := quotient_map P C le_rfl,
  let φ' := (ϕ.map (M.mem_map_of_mem (φ : P'.quotient →* P.quotient)) ϕ'),
  have hφ' : φ.comp (quotient.mk P') = (quotient.mk P).comp C := rfl,
  intro p,
  obtain ⟨⟨p', ⟨q, hq⟩⟩, hp⟩ := ϕ'.surj p,
  suffices : φ'.is_integral_elem (ϕ'.to_map p'),
  { obtain ⟨q', hq', rfl⟩ := hq,
    obtain ⟨q'', hq''⟩ := is_unit_iff_exists_inv'.1 (ϕ.map_units ⟨q', hq'⟩),
    refine φ'.is_integral_of_is_integral_mul_unit p (ϕ'.to_map (φ q')) q'' _ (hp.symm ▸ this),
    convert trans (trans (φ'.map_mul _ _).symm (congr_arg φ' hq'')) φ'.map_one using 2,
    rw [← φ'.comp_apply, localization_map.map_comp, ϕ'.to_map.comp_apply, subtype.coe_mk] },
  refine is_integral_of_mem_closure''
    ((ϕ'.to_map.comp (quotient.mk P)) '' (insert X {p | p.degree ≤ 0})) _ _ _,
  { rintros x ⟨p, hp, rfl⟩,
    refine hp.rec_on (λ hy, _) (λ hy, _),
    { refine hy.symm ▸ (φ.is_integral_elem_localization_at_leading_coeff ((quotient.mk P) X)
        (pX.map (quotient.mk P')) _ M ⟨1, pow_one _⟩ _ _),
      rwa [eval₂_map, hφ', ← hom_eval₂, quotient.eq_zero_iff_mem, eval₂_C_X] },
    { rw [set.mem_set_of_eq, degree_le_zero_iff] at hy,
      refine hy.symm ▸ ⟨X - C (ϕ.to_map ((quotient.mk P') (p.coeff 0))), monic_X_sub_C _, _⟩,
      simp only [eval₂_sub, eval₂_C, eval₂_X],
      rw [sub_eq_zero_iff_eq, ← φ'.comp_apply, localization_map.map_comp, ring_hom.comp_apply],
      refl } },
  { obtain ⟨p, rfl⟩ := quotient.mk_surjective p',
    refine polynomial.induction_on p
      (λ r, subring.subset_closure $ set.mem_image_of_mem _ (or.inr degree_C_le))
      (λ _ _ h1 h2, _) (λ n _ hr, _),
    { convert subring.add_mem _ h1 h2,
      rw [ring_hom.map_add, ring_hom.map_add] },
    { rw [pow_succ X n, mul_comm X, ← mul_assoc, ring_hom.map_mul, ϕ'.to_map.map_mul],
      exact subring.mul_mem _ hr (subring.subset_closure (set.mem_image_of_mem _ (or.inl rfl))) } },
end

/-- If `f : R → S` descends to an integral map in the localization at `x`,
  and `R` is a Jacobson ring, then the intersection of all maximal ideals in `S` is trivial -/
lemma jacobson_bot_of_integral_localization {R : Type*} [integral_domain R] [is_jacobson R]
  (φ : R →+* S) (hφ : function.injective φ) (x : R) (hx : x ≠ 0)
  (ϕ : localization_map (submonoid.powers x) Rₘ)
  (ϕ' : localization_map ((submonoid.powers x).map φ : submonoid S) Sₘ)
  (hφ' : (ϕ.map ((submonoid.powers x).mem_map_of_mem (φ : R →* S)) ϕ').is_integral) :
  (⊥ : ideal S).jacobson = ⊥ :=
begin
  have hM : ((submonoid.powers x).map φ : submonoid S) ≤ non_zero_divisors S :=
    map_le_non_zero_divisors_of_injective hφ (powers_le_non_zero_divisors_of_domain hx),
  letI : integral_domain Sₘ := localization_map.integral_domain_of_le_non_zero_divisors ϕ' hM,
  let φ' : Rₘ →+* Sₘ := ϕ.map ((submonoid.powers x).mem_map_of_mem (φ : R →* S)) ϕ',
  suffices : ∀ I : ideal Sₘ, I.is_maximal → (I.comap ϕ'.to_map).is_maximal,
  { have hϕ' : comap ϕ'.to_map ⊥ = ⊥,
    { simpa [ring_hom.injective_iff_ker_eq_bot, ring_hom.ker_eq_comap_bot] using ϕ'.injective hM },
    refine eq_bot_iff.2 (le_trans _ (le_of_eq hϕ')),
    have hSₘ : is_jacobson Sₘ := is_jacobson_of_is_integral' φ' hφ' (is_jacobson_localization ϕ),
    rw [← hSₘ.out radical_bot_of_integral_domain, comap_jacobson],
    exact Inf_le_Inf (λ j hj, ⟨bot_le, let ⟨J, hJ⟩ := hj in hJ.2 ▸ this J hJ.1.2⟩) },
  introsI I hI,
  -- Remainder of the proof is pulling and pushing ideals around the square and the quotient square
  haveI : (I.comap ϕ'.to_map).is_prime := comap_is_prime ϕ'.to_map I,
  haveI : (I.comap φ').is_prime := comap_is_prime φ' I,
  haveI : (⊥ : ideal (I.comap ϕ'.to_map).quotient).is_prime := bot_prime,
  have hcomm: φ'.comp ϕ.to_map = ϕ'.to_map.comp φ := ϕ.map_comp _,
  let f := quotient_map (I.comap ϕ'.to_map) φ le_rfl,
  let g := quotient_map I ϕ'.to_map le_rfl,
  have := is_maximal_comap_of_is_integral_of_is_maximal' φ' hφ' I
    (by convert hI; casesI _inst_4; refl),
  have := ((is_maximal_iff_is_maximal_disjoint ϕ _).1 this).left,
  have : ((I.comap ϕ'.to_map).comap φ).is_maximal,
  { rwa [comap_comap, hcomm, ← comap_comap] at this },
  rw ← bot_quotient_is_maximal_iff at this ⊢,
  refine is_maximal_of_is_integral_of_is_maximal_comap' f _ ⊥
    ((eq_bot_iff.2 (comap_bot_le_of_injective f quotient_map_injective)).symm ▸ this),
  exact f.is_integral_tower_bot_of_is_integral g quotient_map_injective
    ((comp_quotient_map_eq_of_comp_eq hcomm I).symm ▸
    (ring_hom.is_integral_trans _ _ (ring_hom.is_integral_of_surjective _
      (localization_map.surjective_quotient_map_of_maximal_of_localization
      (by rwa [comap_comap, hcomm, ← bot_quotient_is_maximal_iff])))
      (ring_hom.is_integral_quotient_of_is_integral _ hφ'))),
end

/-- Used to bootstrap the proof of `is_jacobson_polynomial_iff_is_jacobson`.
  That theorem is more general and should be used instead of this one. -/
private lemma is_jacobson_polynomial_of_domain (R : Type*) [integral_domain R] [hR : is_jacobson R]
  (P : ideal (polynomial R)) [is_prime P] (hP : ∀ (x : R), C x ∈ P → x = 0) :
  P.jacobson = P :=
begin
  by_cases Pb : (P = ⊥),
  { exact Pb.symm ▸ jacobson_bot_polynomial_of_jacobson_bot
      (hR.out radical_bot_of_integral_domain) },
  { refine jacobson_eq_iff_jacobson_quotient_eq_bot.mpr _,
    haveI : (P.comap (C : R →+* polynomial R)).is_prime := comap_is_prime C P,
    obtain ⟨p, pP, p0⟩ := exists_nonzero_mem_of_ne_bot Pb hP,
    refine jacobson_bot_of_integral_localization (quotient_map P C le_rfl) quotient_map_injective
      _ _ (localization.of (submonoid.powers (p.map (quotient.mk (P.comap C))).leading_coeff))
      (localization.of _) (is_integral_localization_map_polynomial_quotient P _ pP _ _),
    rwa [ne.def, leading_coeff_eq_zero] }
end

lemma is_jacobson_polynomial_of_is_jacobson (hR : is_jacobson R) :
  is_jacobson (polynomial R) :=
begin
  refine is_jacobson_iff_prime_eq.mpr (λ I, _),
  introI hI,
  let R' : subring I.quotient := ((quotient.mk I).comp C).range,
  let i : R →+* R' := ((quotient.mk I).comp C).range_restrict,
  have hi : function.surjective (i : R → R') := ((quotient.mk I).comp C).range_restrict_surjective,
  have hi' : (polynomial.map_ring_hom i : polynomial R →+* polynomial R').ker ≤ I,
  { refine λ f hf, polynomial_mem_ideal_of_coeff_mem_ideal I f (λ n, _),
    replace hf := congr_arg (λ (g : polynomial (((quotient.mk I).comp C).range)), g.coeff n) hf,
    change (polynomial.map ((quotient.mk I).comp C).range_restrict f).coeff n = 0 at hf,
    rw [coeff_map, subtype.ext_iff] at hf,
    rwa [mem_comap, ← quotient.eq_zero_iff_mem, ← ring_hom.comp_apply] },
  haveI : (ideal.map (map_ring_hom i) I).is_prime :=
    map_is_prime_of_surjective (map_surjective i hi) hi',
  suffices : (I.map (polynomial.map_ring_hom i)).jacobson = (I.map (polynomial.map_ring_hom i)),
  { replace this := congr_arg (comap (polynomial.map_ring_hom i)) this,
    rw [← map_jacobson_of_surjective _ hi',
      comap_map_of_surjective _ _, comap_map_of_surjective _ _] at this,
    refine le_antisymm (le_trans (le_sup_left_of_le le_rfl)
      (le_trans (le_of_eq this) (sup_le le_rfl hi'))) le_jacobson,
    all_goals {exact polynomial.map_surjective i hi} },
  exact @is_jacobson_polynomial_of_domain R' _ (is_jacobson_of_surjective ⟨i, hi⟩)
    (map (map_ring_hom i) I) _ (eq_zero_of_polynomial_mem_map_range I),
end

theorem is_jacobson_polynomial_iff_is_jacobson :
  is_jacobson (polynomial R) ↔ is_jacobson R :=
begin
  refine ⟨_, is_jacobson_polynomial_of_is_jacobson⟩,
  introI H,
  exact is_jacobson_of_surjective ⟨eval₂_ring_hom (ring_hom.id _) 1, λ x,
    ⟨C x, by simp only [coe_eval₂_ring_hom, ring_hom.id_apply, eval₂_C]⟩⟩,
end

instance [is_jacobson R] : is_jacobson (polynomial R) :=
is_jacobson_polynomial_iff_is_jacobson.mpr ‹is_jacobson R›

end comm_ring

section integral_domain
variables {R : Type*} [integral_domain R] [is_jacobson R]
variables (P : ideal (polynomial R)) [hP : P.is_maximal]

include P hP

lemma is_maximal_comap_C_of_is_maximal (hP' : ∀ (x : R), C x ∈ P → x = 0) :
  is_maximal (comap C P : ideal R) :=
begin
  haveI hp'_prime : (P.comap C : ideal R).is_prime := comap_is_prime C P,
  obtain ⟨m, hm⟩ := submodule.nonzero_mem_of_bot_lt (bot_lt_of_maximal P polynomial_not_is_field),
  have : (m : polynomial R) ≠ 0, rwa [ne.def, submodule.coe_eq_zero],
  let φ : (P.comap C : ideal R).quotient →+* P.quotient := quotient_map P C le_rfl,
  let M : submonoid (P.comap C : ideal R).quotient :=
    submonoid.powers ((m : polynomial R).map (quotient.mk (P.comap C : ideal R))).leading_coeff,
  rw ← bot_quotient_is_maximal_iff at hP ⊢,
  have hp0 : ((m : polynomial R).map (quotient.mk (P.comap C : ideal R))).leading_coeff ≠ 0 :=
    λ hp0', this $ map_injective (quotient.mk (P.comap C : ideal R))
      ((quotient.mk (P.comap C : ideal R)).injective_iff.2 (λ x hx,
      by rwa [quotient.eq_zero_iff_mem, (by rwa eq_bot_iff : (P.comap C : ideal R) = ⊥)] at hx))
      (by simpa only [leading_coeff_eq_zero, map_zero] using hp0'),
  let ϕ : localization_map M (localization M) := localization.of M,
  have hM : (0 : ((P.comap C : ideal R)).quotient) ∉ M := λ ⟨n, hn⟩, hp0 (pow_eq_zero hn),
  suffices : (⊥ : ideal (localization M)).is_maximal,
  { rw ← ϕ.comap_map_of_is_prime_disjoint ⊥ bot_prime (λ x hx, hM (hx.2 ▸ hx.1)),
    refine ((is_maximal_iff_is_maximal_disjoint ϕ _).mp _).1,
    rwa map_bot },
  let M' : submonoid P.quotient := M.map φ,
  have hM' : (0 : P.quotient) ∉ M' :=
    λ ⟨z, hz⟩, hM (quotient_map_injective (trans hz.2 φ.map_zero.symm) ▸ hz.1),
  letI : integral_domain (localization M') :=
    localization_map.integral_domain_localization (le_non_zero_divisors_of_domain hM'),
  let ϕ' : localization_map (M.map ↑φ : submonoid P.quotient) (localization (M.map ↑φ)) :=
    localization.of (M.map ↑φ),
  suffices : (⊥ : ideal (localization M')).is_maximal,
  { rw le_antisymm bot_le (comap_bot_le_of_injective _ (map_injective_of_injective _
      quotient_map_injective M ϕ ϕ' (le_non_zero_divisors_of_domain hM'))),
    refine is_maximal_comap_of_is_integral_of_is_maximal' _ _ ⊥ this,
    refine is_integral_localization_map_polynomial_quotient P _ (submodule.coe_mem m) ϕ ϕ', },
  rw (map_bot.symm : (⊥ : ideal (localization M')) = map ϕ'.to_map ⊥),
  refine map.is_maximal ϕ'.to_map (localization_map_bijective_of_field hM' _ ϕ') hP,
  rwa [← quotient.maximal_ideal_iff_is_field_quotient, ← bot_quotient_is_maximal_iff],
end

/-- Used to bootstrap the more general `quotient_mk_comp_C_is_integral_of_jacobson` -/
private lemma quotient_mk_comp_C_is_integral_of_jacobson' (hR : is_jacobson R)
  (hP' : ∀ (x : R), C x ∈ P → x = 0) :
  ((quotient.mk P).comp C : R →+* P.quotient).is_integral :=
begin
  refine (is_integral_quotient_map_iff _).mp _,
  let P' : ideal R := P.comap C,
  obtain ⟨pX, hpX, hp0⟩ :=
    exists_nonzero_mem_of_ne_bot (ne_of_lt (bot_lt_of_maximal P polynomial_not_is_field)).symm hP',
  let M : submonoid P'.quotient := submonoid.powers (pX.map (quotient.mk P')).leading_coeff,
  let φ : P'.quotient →+* P.quotient := quotient_map P C le_rfl,
  let ϕ' : localization_map (M.map ↑φ : submonoid P.quotient) (localization (M.map ↑φ)) :=
    localization.of (M.map ↑φ),
  haveI hp'_prime : P'.is_prime := comap_is_prime C P,
  have hM : (0 : P'.quotient) ∉ M := λ ⟨n, hn⟩, hp0 $ leading_coeff_eq_zero.mp (pow_eq_zero hn),
  refine ((quotient_map P C le_rfl).is_integral_tower_bot_of_is_integral
    (localization.of (M.map ↑(quotient_map P C le_rfl) : submonoid P.quotient)).to_map _ _),
  { refine ϕ'.injective (le_non_zero_divisors_of_domain (λ hM', hM _)),
    exact (let ⟨z, zM, z0⟩ := hM' in (quotient_map_injective (trans z0 φ.map_zero.symm)) ▸ zM) },
  { let ϕ : localization_map M (localization M) := localization.of M,
    rw ← (ϕ.map_comp _),
    refine ring_hom.is_integral_trans ϕ.to_map
      (ϕ.map (M.mem_map_of_mem (φ : P'.quotient →* P.quotient)) ϕ') _ _,
    { exact ϕ.to_map.is_integral_of_surjective (localization_map_bijective_of_field hM
        ((quotient.maximal_ideal_iff_is_field_quotient _).mp
        (is_maximal_comap_C_of_is_maximal P hP')) _).2 },
    { exact is_integral_localization_map_polynomial_quotient P pX hpX _ _ } }
end

/-- If `R` is a Jacobson ring, and `P` is a maximal ideal of `polynomial R`,
  then `R → (polynomial R)/P` is an integral map. -/
lemma quotient_mk_comp_C_is_integral_of_jacobson :
  ((quotient.mk P).comp C : R →+* P.quotient).is_integral :=
begin
  let P' : ideal R := P.comap C,
  haveI : P'.is_prime := comap_is_prime C P,
  let f : polynomial R →+* polynomial P'.quotient := polynomial.map_ring_hom (quotient.mk P'),
  have hf : function.surjective f := map_surjective (quotient.mk P') quotient.mk_surjective,
  have hPJ : P = (P.map f).comap f,
  { rw comap_map_of_surjective _ hf,
    refine le_antisymm (le_sup_left_of_le le_rfl) (sup_le le_rfl _),
    refine λ p hp, polynomial_mem_ideal_of_coeff_mem_ideal P p (λ n, quotient.eq_zero_iff_mem.mp _),
    simpa only [coeff_map, coe_map_ring_hom] using (polynomial.ext_iff.mp hp) n },
  refine ring_hom.is_integral_tower_bot_of_is_integral _ _ (injective_quotient_le_comap_map P) _,
  rw ← quotient_mk_maps_eq,
  refine ring_hom.is_integral_trans _ _
    ((quotient.mk P').is_integral_of_surjective quotient.mk_surjective) _,
  apply quotient_mk_comp_C_is_integral_of_jacobson' _ _ (λ x hx, _),
  any_goals { exact ideal.is_jacobson_quotient },
  { exact or.rec_on (map_eq_top_or_is_maximal_of_surjective f hf hP)
    (λ h, absurd (trans (h ▸ hPJ : P = comap f ⊤) comap_top : P = ⊤) hP.ne_top) id },
  { obtain ⟨z, rfl⟩ := quotient.mk_surjective x,
    rwa [quotient.eq_zero_iff_mem, mem_comap, hPJ, mem_comap, coe_map_ring_hom, map_C] }
end

lemma is_maximal_comap_C_of_is_jacobson : (P.comap (C : R →+* polynomial R)).is_maximal :=
begin
  rw [← @mk_ker _ _ P, ring_hom.ker_eq_comap_bot, comap_comap],
  exact is_maximal_comap_of_is_integral_of_is_maximal' _
    (quotient_mk_comp_C_is_integral_of_jacobson P) ⊥ ((bot_quotient_is_maximal_iff _).mpr hP),
end

omit P hP

lemma comp_C_integral_of_surjective_of_jacobson
  {S : Type*} [field S] (f : (polynomial R) →+* S) (hf : function.surjective f) :
  (f.comp C).is_integral :=
begin
  haveI : (f.ker).is_maximal := @comap_is_maximal_of_surjective _ _ _ _ f ⊥ hf bot_is_maximal,
  let g : f.ker.quotient →+* S := ideal.quotient.lift f.ker f (λ _ h, h),
  have hfg : (g.comp (quotient.mk f.ker)) = f := ring_hom_ext' rfl rfl,
  rw [← hfg, ring_hom.comp_assoc],
  refine ring_hom.is_integral_trans _ g (quotient_mk_comp_C_is_integral_of_jacobson f.ker)
    (g.is_integral_of_surjective _), --(quotient.lift_surjective f.ker f _ hf)),
  rw [← hfg] at hf,
  exact function.surjective.of_comp hf,
end

end integral_domain

end polynomial

namespace mv_polynomial
open mv_polynomial ring_hom

lemma is_jacobson_mv_polynomial_fin {R : Type*} [comm_ring R] [H : is_jacobson R] :
  ∀ (n : ℕ), is_jacobson (mv_polynomial (fin n) R)
| 0 := ((is_jacobson_iso ((rename_equiv R
  (equiv.equiv_pempty $ fin.elim0)).to_ring_equiv.trans (pempty_ring_equiv R))).mpr H)
| (n+1) := (is_jacobson_iso (fin_succ_equiv R n).to_ring_equiv).2
  (polynomial.is_jacobson_polynomial_iff_is_jacobson.2 (is_jacobson_mv_polynomial_fin n))

/-- General form of the nullstellensatz for Jacobson rings, since in a Jacobson ring we have
  `Inf {P maximal | P ≥ I} = Inf {P prime | P ≥ I} = I.radical`. Fields are always Jacobson,
  and in that special case this is (most of) the classical Nullstellensatz,
  since `I(V(I))` is the intersection of maximal ideals containing `I`, which is then `I.radical` -/
instance {R : Type*} [comm_ring R] {ι : Type*} [fintype ι] [is_jacobson R] :
  is_jacobson (mv_polynomial ι R) :=
begin
  haveI := classical.dec_eq ι,
  obtain ⟨e⟩ := fintype.equiv_fin ι,
  rw is_jacobson_iso (rename_equiv R e).to_ring_equiv,
  exact is_jacobson_mv_polynomial_fin _
end

variables {n : ℕ}

lemma quotient_mk_comp_C_is_integral_of_jacobson {R : Type*} [integral_domain R] [is_jacobson R]
  (P : ideal (mv_polynomial (fin n) R)) [P.is_maximal] :
  ((quotient.mk P).comp mv_polynomial.C : R →+* P.quotient).is_integral :=
begin
  unfreezingI {induction n with n IH},
  { refine ring_hom.is_integral_of_surjective _ (function.surjective.comp quotient.mk_surjective _),
    exact C_surjective_fin_0 },
  { rw [← fin_succ_equiv_comp_C_eq_C, ← ring_hom.comp_assoc, ← ring_hom.comp_assoc,
      ← quotient_map_comp_mk le_rfl, ring_hom.comp_assoc (polynomial.C),
      ← quotient_map_comp_mk le_rfl, ring_hom.comp_assoc, ring_hom.comp_assoc,
      ← quotient_map_comp_mk le_rfl, ← ring_hom.comp_assoc (quotient.mk _)],
    refine ring_hom.is_integral_trans _ _ _ _,
    { refine ring_hom.is_integral_trans _ _ (is_integral_of_surjective _ quotient.mk_surjective) _,
      refine ring_hom.is_integral_trans _ _ _ _,
      { apply (is_integral_quotient_map_iff _).mpr (IH _),
        apply polynomial.is_maximal_comap_C_of_is_jacobson _,
        { exact mv_polynomial.is_jacobson_mv_polynomial_fin n },
        { apply comap_is_maximal_of_surjective,
          exact (fin_succ_equiv R n).symm.surjective } },
      { refine (is_integral_quotient_map_iff _).mpr _,
        rw ← quotient_map_comp_mk le_rfl,
        refine ring_hom.is_integral_trans _ _ _ ((is_integral_quotient_map_iff _).mpr _),
        { exact ring_hom.is_integral_of_surjective _ quotient.mk_surjective },
        { apply polynomial.quotient_mk_comp_C_is_integral_of_jacobson _,
          { exact mv_polynomial.is_jacobson_mv_polynomial_fin n },
          { exact comap_is_maximal_of_surjective _ (fin_succ_equiv R n).symm.surjective } } } },
    { refine (is_integral_quotient_map_iff _).mpr _,
      refine ring_hom.is_integral_trans _ _ _ (is_integral_of_surjective _ quotient.mk_surjective),
      exact ring_hom.is_integral_of_surjective _ (fin_succ_equiv R n).symm.surjective } }
end

lemma comp_C_integral_of_surjective_of_jacobson {R : Type*} [integral_domain R] [is_jacobson R]
  {σ : Type*} [fintype σ] {S : Type*} [field S] (f : mv_polynomial σ R →+* S)
  (hf : function.surjective f) : (f.comp C).is_integral :=
begin
  haveI := classical.dec_eq σ,
  obtain ⟨e⟩ := fintype.equiv_fin σ,
  let f' : mv_polynomial (fin _) R →+* S :=
    f.comp (rename_equiv R e.symm).to_ring_equiv.to_ring_hom,
  have hf' : function.surjective f' :=
    ((function.surjective.comp hf (rename_equiv R e.symm).surjective)),
  have : (f'.comp C).is_integral,
  { haveI : (f'.ker).is_maximal := @comap_is_maximal_of_surjective _ _ _ _ f' ⊥ hf' bot_is_maximal,
    let g : f'.ker.quotient →+* S := ideal.quotient.lift f'.ker f' (λ _ h, h),
    have hfg : (g.comp (quotient.mk f'.ker)) = f' := ring_hom_ext (λ r, rfl) (λ i, rfl),
    rw [← hfg, ring_hom.comp_assoc],
    refine ring_hom.is_integral_trans _ g (quotient_mk_comp_C_is_integral_of_jacobson f'.ker)
      (g.is_integral_of_surjective _),
    rw ← hfg at hf',
    exact function.surjective.of_comp hf' },
  rw ring_hom.comp_assoc at this,
  convert this,
  refine ring_hom.ext (λ x, _),
  exact ((rename_equiv R e.symm).commutes' x).symm,
end

end mv_polynomial

end ideal
