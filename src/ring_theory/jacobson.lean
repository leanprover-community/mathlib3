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
1. Every radical ideal `I` is equal to its jacobson radical
2. Every radical ideal `I` can be written as an intersection of maximal ideals
3. Every prime ideal `I` is equal to its jacobson radical

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

* `is_jacobson_mv_polynomial` says that multi-variate polynomials over a jacobson ring are jacobson

## Tags

Jacobson, Jacobson Ring

-/

universes u v

namespace ideal
variables {R : Type u} [comm_ring R] {I : ideal R}
variables {S : Type v} [comm_ring S]

section is_jacobson

/-- A ring is a Jacobson ring if for every radical ideal `I`,
 the Jacobson radical of `I` is equal to `I`.
 See `is_jacobson_iff_prime_eq` and `is_jacobson_iff_Inf_maximal` for equivalent definitions. -/
@[class] def is_jacobson (R : Type u) [comm_ring R] :=
    ∀ (I : ideal R), I.radical = I → I.jacobson = I

/--  A ring is a Jacobson ring if and only if for all prime ideals `P`,
 the Jacobson radical of `P` is equal to `P`. -/
lemma is_jacobson_iff_prime_eq : is_jacobson R ↔ ∀ P : ideal R, is_prime P → P.jacobson = P :=
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

/-- A ring `R` is Jacobson if and only if for every prime ideal `I`,
 `I` can be written as the infimum of some collection of maximal ideals.
 Allowing ⊤ in the set `M` of maximal ideals is equivalent, but makes some proofs cleaner. -/
lemma is_jacobson_iff_Inf_maximal : is_jacobson R ↔
  ∀ {I : ideal R}, I.is_prime → ∃ M : set (ideal R), (∀ J ∈ M, is_maximal J ∨ J = ⊤) ∧ I = Inf M :=
⟨λ H I h, eq_jacobson_iff_Inf_maximal.1 (H _ (is_prime.radical h)),
  λ H , is_jacobson_iff_prime_eq.2 (λ P hP, eq_jacobson_iff_Inf_maximal.2 (H hP))⟩

lemma is_jacobson_iff_Inf_maximal' : is_jacobson R ↔
  ∀ {I : ideal R}, I.is_prime → ∃ M : set (ideal R), (∀ (J ∈ M) (K : ideal R), J < K → K = ⊤) ∧ I = Inf M :=
⟨λ H I h, eq_jacobson_iff_Inf_maximal'.1 (H _ (is_prime.radical h)),
  λ H , is_jacobson_iff_prime_eq.2 (λ P hP, eq_jacobson_iff_Inf_maximal'.2 (H hP))⟩

lemma radical_eq_jacobson (H : is_jacobson R) (I : ideal R) : I.radical = I.jacobson :=
le_antisymm (le_Inf (λ J ⟨hJ, hJ_max⟩, (is_prime.radical_le_iff hJ_max.is_prime).mpr hJ))
            ((H I.radical (radical_idem I)) ▸ (jacobson_mono le_radical))

/-- Fields have only two ideals, and the condition holds for both of them -/
@[priority 100]
instance is_jacobson_field {K : Type u} [field K] : is_jacobson K :=
λ I hI, or.rec_on (eq_bot_or_top I)
(λ h, le_antisymm
  (Inf_le ⟨le_of_eq rfl, (eq.symm h) ▸ bot_is_maximal⟩)
  ((eq.symm h) ▸ bot_le))
(λ h, by rw [h, jacobson_eq_top_iff])

theorem is_jacobson_of_surjective [H : is_jacobson R] :
  (∃ (f : R →+* S), function.surjective f) → is_jacobson S :=
begin
  rintros ⟨f, hf⟩,
  rw is_jacobson_iff_Inf_maximal,
  intros p hp,
  use map f '' {J : ideal R | comap f p ≤ J ∧ J.is_maximal },
  use λ j ⟨J, hJ, hmap⟩, hmap ▸ or.symm (map_eq_top_or_is_maximal_of_surjective f hf hJ.right),
  have : p = map f ((comap f p).jacobson),
  from (H (comap f p) (by rw [← comap_radical, is_prime.radical hp])).symm
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
open localization_map
variables {y : R} (f : away_map y S)

lemma disjoint_powers_iff_not_mem {I : ideal R} (hI : I.radical = I) :
  disjoint ((submonoid.powers y) : set R) ↑I ↔ y ∉ I.1 :=
begin
  refine ⟨λ h, set.disjoint_left.1 h (submonoid.mem_powers _), λ h, _⟩,
  rw [disjoint_iff, eq_bot_iff],
  rintros x ⟨hx, hx'⟩,
  obtain ⟨n, hn⟩ := hx,
  rw [← hn, ← hI] at hx',
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
  { refine λ h, ⟨_, λ hy, h.1 (ideal.eq_top_of_is_unit_mem _ hy
      (map_units f ⟨y, submonoid.mem_powers _⟩))⟩,
    have hJ : J.is_prime := is_maximal.is_prime h,
    rw is_prime_iff_is_prime_disjoint f at hJ,
    have : y ∉ (comap f.to_map J).1 :=
      set.disjoint_left.1 hJ.right (submonoid.mem_powers _),
    erw [← H (comap f.to_map J) (is_prime.radical hJ.left), mem_Inf] at this,
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
      exact absurd (h.right _ (lt_of_le_of_ne this hJ)) hI_p.left } },
  { refine λ h, ⟨λ hJ, h.left.left (eq_top_iff.2 _), λ I hI, _⟩,
    { rwa [eq_top_iff, (order_embedding f).map_rel_iff] at hJ },
    { have := congr_arg (map f.to_map) (h.left.right _ ⟨comap_mono (le_of_lt hI), _⟩),
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
  map_rel_iff' := λ I I', ⟨λ h x hx, h hx, λ h, (show I.val ≤ I'.val,
    from (map_comap f I.val) ▸ (map_comap f I'.val) ▸ (ideal.map_mono h))⟩ }

/-- If `S` is the localization of the Jacobson ring `R` at the submonoid generated by `y : R`, then `S` is Jacobson. -/
lemma is_jacobson_localization [H : is_jacobson R]
  (f : away_map y S) : is_jacobson S :=
begin
  rw is_jacobson_iff_prime_eq,
  refine λ P' hP', le_antisymm _ le_jacobson,
  obtain ⟨hP', hPM⟩ := (localization_map.is_prime_iff_is_prime_disjoint f P').mp hP',
  have hP := H (comap f.to_map P') (is_prime.radical hP'),
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
    cases hP'.right hxy with hxy hxy,
    { exact hxy },
    { exfalso,
      refine hPM ⟨submonoid.mem_powers _, hxy⟩ } },
  refine le_trans _ this,
  rw [ideal.jacobson, comap_Inf', Inf_eq_infi],
  refine infi_le_infi_of_subset (λ I hI, ⟨map f.to_map I, ⟨_, _⟩⟩),
  { exact ⟨le_trans (le_of_eq ((localization_map.map_comap f P').symm)) (map_mono hI.1),
    is_maximal_of_is_maximal_disjoint f _ hI.2.1 hI.2.2⟩ },
  { exact localization_map.comap_map_of_is_prime_disjoint f I (is_maximal.is_prime hI.2.1)
    ((disjoint_powers_iff_not_mem hI.2.1.is_prime.radical).2 hI.2.2) }
end

end localization

section polynomial
open polynomial

/-- If `f : R → S` descends to an integral map in the localization at `x`,
  and `R` is a jacobson ring, then the intersection of all maximal ideals in `S` is trivial -/
lemma jacobson_bot_of_integral_localization {R S : Type*} [integral_domain R] [integral_domain S]
  {Rₘ Sₘ : Type*} [comm_ring Rₘ] [comm_ring Sₘ] [is_jacobson R]
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
    rw [← hSₘ ⊥ radical_bot_of_integral_domain, comap_jacobson],
    exact Inf_le_Inf (λ j hj, ⟨bot_le, let ⟨J, hJ⟩ := hj in hJ.2 ▸ this J hJ.1.2⟩) },
  introsI I hI,
  -- Remainder of the proof is pulling and pushing ideals around the square and the quotient square
  haveI : (I.comap ϕ'.to_map).is_prime := comap_is_prime ϕ'.to_map I,
  haveI : (I.comap φ').is_prime := comap_is_prime φ' I,
  haveI : (⊥ : ideal (I.comap ϕ'.to_map).quotient).is_prime := bot_prime,
  have hcomm: φ'.comp ϕ.to_map = ϕ'.to_map.comp φ := ϕ.map_comp _,
  let f := quotient_map (I.comap ϕ'.to_map) φ le_rfl,
  let g := quotient_map I ϕ'.to_map le_rfl,
  have := ((is_maximal_iff_is_maximal_disjoint ϕ _).1
    (is_maximal_comap_of_is_integral_of_is_maximal' φ' hφ' I hI)).left,
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
  That theorem is more general and should be used instead of this one -/
private lemma is_jacobson_polynomial_of_domain (R : Type*) [integral_domain R] [hR : is_jacobson R]
  (P : ideal (polynomial R)) [P.is_prime] (hP : ∀ (x : R), C x ∈ P → x = 0) : P.jacobson = P :=
begin
  by_cases hP : (P = ⊥),
  { exact hP.symm ▸ jacobson_bot_polynomial_of_jacobson_bot (hR ⊥ radical_bot_of_integral_domain) },
  { rw jacobson_eq_iff_jacobson_quotient_eq_bot,
    let P' : ideal R := P.comap C,
    have hP'_inj : function.injective (quotient.mk P') := (quotient.mk P').injective_iff.2
      (λ x hx, by rwa [quotient.eq_zero_iff_mem, (by rwa eq_bot_iff : P' = ⊥)] at hx),
    haveI : P'.is_prime := comap_is_prime C P,
    have : ∃ (p : polynomial R) (hp : p ∈ P), p ≠ 0,
    { contrapose! hP,
      exact eq_bot_iff.2 (λ x hx, (hP x hx).symm ▸ (ideal.zero_mem ⊥)) },
    obtain ⟨pX, hpX, hp0⟩ := this,
    have hp0 : (pX.map (quotient.mk P')) ≠ 0 :=
      λ hp0', hp0 $ map_injective (quotient.mk P') hP'_inj (by simpa using hp0'),
    let φ : P'.quotient →+* P.quotient := quotient_map P C le_rfl,
    have hφ' : φ.comp (quotient.mk P') = (quotient.mk P).comp C := rfl,
    have hφ : function.injective φ := quotient_map_injective,
    let M : submonoid P'.quotient := submonoid.powers (pX.map (quotient.mk P')).leading_coeff,
    let ϕ : localization_map M (localization M) := localization.of M,
    let ϕ' : localization_map (M.map ↑φ) (localization (M.map ↑φ)) := localization.of (M.map ↑φ),
    let φ' : (localization M) →+* (localization (M.map ↑φ)) :=
      (ϕ.map (M.mem_map_of_mem (φ : P'.quotient →* P.quotient)) ϕ'),
    refine jacobson_bot_of_integral_localization φ hφ (pX.map (quotient.mk P')).leading_coeff
       (λ hx, hp0 (leading_coeff_eq_zero.1 hx)) ϕ ϕ' (λ p, _),
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
        exact subring.mul_mem _ hr (subring.subset_closure (set.mem_image_of_mem _ (or.inl rfl))) } } }
end

theorem is_jacobson_polynomial_iff_is_jacobson {R : Type*} [comm_ring R] : is_jacobson (polynomial R) ↔ is_jacobson R :=
begin
  split; introI H,
  { exact is_jacobson_of_surjective ⟨eval₂_ring_hom (ring_hom.id _) 1, λ x, ⟨C x, by simp⟩⟩ },
  { rw is_jacobson_iff_prime_eq,
    intros I hI,
    let R' := ((quotient.mk I).comp C).range,
    let i : R →+* R' := ((quotient.mk I).comp C).range_restrict,
    have hi : function.surjective (i : R → R') := ((quotient.mk I).comp C).surjective_onto_range,
    have hi' : (polynomial.map_ring_hom i : polynomial R →+* polynomial R').ker ≤ I,
    { refine λ f hf, polynomial_mem_ideal_of_coeff_mem_ideal I f (λ n, _),
      rw [mem_comap, ← quotient.eq_zero_iff_mem, ← ring_hom.comp_apply],
      rw [ring_hom.mem_ker, coe_map_ring_hom] at hf,
      replace hf := congr_arg (λ (f : polynomial R'), f.coeff n) hf,
      simp only [coeff_map, coeff_zero] at hf,
      rwa [subtype.ext_iff, ring_hom.coe_range_restrict] at hf },
    haveI hR' : is_jacobson R' := is_jacobson_of_surjective ⟨i, hi⟩,
    let I' : ideal (polynomial R') := I.map (polynomial.map_ring_hom i),
    haveI : I'.is_prime := map_is_prime_of_surjective (polynomial.map_surjective i hi) hi',
    suffices : (I.map (polynomial.map_ring_hom i)).jacobson = (I.map (polynomial.map_ring_hom i)),
    { replace this := congr_arg (comap (polynomial.map_ring_hom i)) this,
      rw [← map_jacobson_of_surjective _ hi',
        comap_map_of_surjective _ _, comap_map_of_surjective _ _] at this,
      refine le_antisymm (le_trans (le_sup_left_of_le le_rfl)
        (le_trans (le_of_eq this) (sup_le le_rfl hi'))) le_jacobson,
      all_goals {exact polynomial.map_surjective i hi} },
    refine is_jacobson_polynomial_of_domain R' I' (eq_zero_of_polynomial_mem_map_range I hi') },
end

instance [is_jacobson R] : is_jacobson (polynomial R) :=
is_jacobson_polynomial_iff_is_jacobson.mpr ‹is_jacobson R›

lemma is_jacobson_mv_polynomial_fin [H : is_jacobson R] :
  ∀ (n : ℕ), is_jacobson (mv_polynomial (fin n) R)
| 0 := ((is_jacobson_iso ((mv_polynomial.ring_equiv_of_equiv R
  (equiv.equiv_pempty $ fin.elim0)).trans (mv_polynomial.pempty_ring_equiv R))).mpr H)
| (n+1) := (is_jacobson_iso (mv_polynomial.fin_succ_equiv R n)).2
  (is_jacobson_polynomial_iff_is_jacobson.2 (is_jacobson_mv_polynomial_fin n))

/-- General form of the nullstellensatz for jacobson rings, since in a jacobson ring we have
  `Inf {P maximal | P ≥ I} = Inf {P prime | P ≥ I} = I.radical`. Fields are always jacobson,
  and in that special case this is (most of) the classical nullstellensatz,
  since `I(V(I))` is the intersection of maximal ideals containing `I`, which is then `I.radical` -/
instance {ι : Type*} [fintype ι] [is_jacobson R] : is_jacobson (mv_polynomial ι R) :=
begin
  haveI := classical.dec_eq ι,
  obtain ⟨e⟩ := fintype.equiv_fin ι,
  rw is_jacobson_iso (mv_polynomial.ring_equiv_of_equiv R e),
  exact is_jacobson_mv_polynomial_fin _
end

end polynomial

end ideal
