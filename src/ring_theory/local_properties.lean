/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import ring_theory.finite_type
import ring_theory.localization.at_prime
import ring_theory.localization.away
import ring_theory.localization.integer
import ring_theory.localization.submodule
import ring_theory.nilpotent
import ring_theory.ring_hom_properties

/-!
# Local properties of commutative rings

In this file, we provide the proofs of various local properties.

## Naming Conventions

* `localization_P` : `P` holds for `S⁻¹R` if `P` holds for `R`.
* `P_of_localization_maximal` : `P` holds for `R` if `P` holds for `Rₘ` for all maximal `m`.
* `P_of_localization_prime` : `P` holds for `R` if `P` holds for `Rₘ` for all prime `m`.
* `P_of_localization_span` : `P` holds for `R` if given a spanning set `{fᵢ}`, `P` holds for all
  `R_{fᵢ}`.

## Main results

The following properties are covered:

* The triviality of an ideal or an element:
  `ideal_eq_bot_of_localization`, `eq_zero_of_localization`
* `is_reduced` : `localization_is_reduced`, `is_reduced_of_localization_maximal`.
* `finite`: `localization_finite`, `finite_of_localization_span`
* `finite_type`: `localization_finite_type`, `finite_type_of_localization_span`

-/

open_locale pointwise classical big_operators

universe u

variables {R S : Type u} [comm_ring R] [comm_ring S] (M : submonoid R)
variables (N : submonoid S) (R' S' : Type u) [comm_ring R'] [comm_ring S'] (f : R →+* S)
variables [algebra R R'] [algebra S S']

section properties

section comm_ring

variable (P : ∀ (R : Type u) [comm_ring R], Prop)

include P

/-- A property `P` of comm rings is said to be preserved by localization
  if `P` holds for `M⁻¹R` whenever `P` holds for `R`. -/
def localization_preserves : Prop :=
  ∀ {R : Type u} [hR : comm_ring R] (M : by exactI submonoid R) (S : Type u) [hS : comm_ring S]
    [by exactI algebra R S] [by exactI is_localization M S], @P R hR → @P S hS

/-- A property `P` of comm rings satisfies `of_localization_maximal` if
  if `P` holds for `R` whenever `P` holds for `Rₘ` for all maximal ideal `m`. -/
def of_localization_maximal : Prop :=
  ∀ (R : Type u) [comm_ring R],
    by exactI (∀ (J : ideal R) (hJ : J.is_maximal), by exactI P (localization.at_prime J)) → P R

end comm_ring

section ring_hom

variable (P : ∀ {R S : Type u} [comm_ring R] [comm_ring S] (f : by exactI R →+* S), Prop)

include P

/-- A property `P` of ring homs is said to be preserved by localization
 if `P` holds for `M⁻¹R →+* M⁻¹S` whenever `P` holds for `R →+* S`. -/
def ring_hom.localization_preserves :=
  ∀ ⦃R S : Type u⦄ [comm_ring R] [comm_ring S] (f : by exactI R →+* S) (M : by exactI submonoid R)
    (R' S' : Type u) [comm_ring R'] [comm_ring S'] [by exactI algebra R R']
    [by exactI algebra S S'] [by exactI is_localization M R']
    [by exactI is_localization (M.map f) S'],
    by exactI (P f → P (is_localization.map S' f (submonoid.le_comap_map M) : R' →+* S'))

/-- A property `P` of ring homs satisfies `ring_hom.of_localization_finite_span`
if `P` holds for `R →+* S` whenever there exists a finite set `{ r }` that spans `R` such that
`P` holds for `Rᵣ →+* Sᵣ`.

Note that this is equivalent to `ring_hom.of_localization_span` via
`ring_hom.of_localization_span_iff_finite`, but this is easier to prove. -/
def ring_hom.of_localization_finite_span :=
  ∀ ⦃R S : Type u⦄ [comm_ring R] [comm_ring S] (f : by exactI R →+* S)
    (s : finset R) (hs : by exactI ideal.span (s : set R) = ⊤)
    (H : by exactI (∀ (r : s), P (localization.away_map f r))), by exactI P f

/-- A property `P` of ring homs satisfies `ring_hom.of_localization_finite_span`
if `P` holds for `R →+* S` whenever there exists a set `{ r }` that spans `R` such that
`P` holds for `Rᵣ →+* Sᵣ`.

Note that this is equivalent to `ring_hom.of_localization_finite_span` via
`ring_hom.of_localization_span_iff_finite`, but this has less restrictions when applying. -/
def ring_hom.of_localization_span :=
  ∀ ⦃R S : Type u⦄ [comm_ring R] [comm_ring S] (f : by exactI R →+* S)
    (s : set R) (hs : by exactI ideal.span s = ⊤)
    (H : by exactI (∀ (r : s), P (localization.away_map f r))), by exactI P f

/-- A property `P` of ring homs satisfies `ring_hom.holds_for_localization_away`
 if `P` holds for each localization map `R →+* Rᵣ`. -/
def ring_hom.holds_for_localization_away : Prop :=
∀ ⦃R : Type u⦄ (S : Type u) [comm_ring R] [comm_ring S] [by exactI algebra R S] (r : R)
  [by exactI is_localization.away r S], by exactI P (algebra_map R S)

/-- A property `P` of ring homs satisfies `ring_hom.of_localization_finite_span_target`
if `P` holds for `R →+* S` whenever there exists a finite set `{ r }` that spans `S` such that
`P` holds for `R →+* Sᵣ`.

Note that this is equivalent to `ring_hom.of_localization_span_target` via
`ring_hom.of_localization_span_target_iff_finite`, but this is easier to prove. -/
def ring_hom.of_localization_finite_span_target : Prop :=
∀ ⦃R S : Type u⦄ [comm_ring R] [comm_ring S] (f : by exactI R →+* S)
  (s : finset S) (hs : by exactI ideal.span (s : set S) = ⊤)
  (H : by exactI (∀ (r : s), P ((algebra_map S (localization.away (r : S))).comp f))),
  by exactI P f

/-- A property `P` of ring homs satisfies `ring_hom.of_localization_span_target`
if `P` holds for `R →+* S` whenever there exists a set `{ r }` that spans `S` such that
`P` holds for `R →+* Sᵣ`.

Note that this is equivalent to `ring_hom.of_localization_finite_span_target` via
`ring_hom.of_localization_span_target_iff_finite`, but this has less restrictions when applying. -/
def ring_hom.of_localization_span_target : Prop :=
∀ ⦃R S : Type u⦄ [comm_ring R] [comm_ring S] (f : by exactI R →+* S)
  (s : set S) (hs : by exactI ideal.span s = ⊤)
  (H : by exactI (∀ (r : s), P ((algebra_map S (localization.away (r : S))).comp f))),
  by exactI P f

/-- A property `P` of ring homs satisfies `of_localization_prime` if
  if `P` holds for `R` whenever `P` holds for `Rₘ` for all prime ideals `p`. -/
def ring_hom.of_localization_prime : Prop :=
∀ ⦃R S : Type u⦄ [comm_ring R] [comm_ring S] (f : by exactI R →+* S),
  by exactI (∀ (J : ideal S) (hJ : J.is_prime),
    by exactI P (localization.local_ring_hom _ J f rfl)) → P f

/-- A property of ring homs is local if it is preserved by localizations and compositions, and for
each `{ r }` that spans `S`, we have `P (R →+* S) ↔ ∀ r, P (R →+* Sᵣ)`. -/
structure ring_hom.property_is_local : Prop :=
(localization_preserves : ring_hom.localization_preserves @P)
(of_localization_span_target : ring_hom.of_localization_span_target @P)
(stable_under_composition : ring_hom.stable_under_composition @P)
(holds_for_localization_away : ring_hom.holds_for_localization_away @P)

lemma ring_hom.of_localization_span_iff_finite :
  ring_hom.of_localization_span @P ↔ ring_hom.of_localization_finite_span @P :=
begin
  delta ring_hom.of_localization_span ring_hom.of_localization_finite_span,
  apply forall₅_congr, -- TODO: Using `refine` here breaks `resetI`.
  introsI,
  split,
  { intros h s, exact h s },
  { intros h s hs hs',
    obtain ⟨s', h₁, h₂⟩ := (ideal.span_eq_top_iff_finite s).mp hs,
    exact h s' h₂ (λ x, hs' ⟨_, h₁ x.prop⟩) }
end

lemma ring_hom.of_localization_span_target_iff_finite :
  ring_hom.of_localization_span_target @P ↔ ring_hom.of_localization_finite_span_target @P :=
begin
  delta ring_hom.of_localization_span_target ring_hom.of_localization_finite_span_target,
  apply forall₅_congr, -- TODO: Using `refine` here breaks `resetI`.
  introsI,
  split,
  { intros h s, exact h s },
  { intros h s hs hs',
    obtain ⟨s', h₁, h₂⟩ := (ideal.span_eq_top_iff_finite s).mp hs,
    exact h s' h₂ (λ x, hs' ⟨_, h₁ x.prop⟩) }
end

variables {P f R' S'}

lemma _root_.ring_hom.property_is_local.respects_iso (hP : ring_hom.property_is_local @P) :
  ring_hom.respects_iso @P :=
begin
  apply hP.stable_under_composition.respects_iso,
  introv,
  resetI,
  letI := e.to_ring_hom.to_algebra,
  apply_with hP.holds_for_localization_away { instances := ff },
  apply is_localization.away_of_is_unit_of_bijective _ is_unit_one,
  exact e.bijective
end

-- Almost all arguments are implicit since this is not intended to use mid-proof.
lemma ring_hom.localization_preserves.away
  (H : ring_hom.localization_preserves @P) (r : R) [is_localization.away r R']
  [is_localization.away (f r) S'] (hf : P f) :
    P (by exactI is_localization.away.map R' S' f r) :=
begin
  resetI,
  haveI : is_localization ((submonoid.powers r).map f) S',
  { rw submonoid.map_powers, assumption },
  exact H f (submonoid.powers r) R' S' hf,
end

lemma ring_hom.property_is_local.of_localization_span (hP : ring_hom.property_is_local @P) :
  ring_hom.of_localization_span @P :=
begin
  introv R hs hs',
  resetI,
  apply_fun (ideal.map f) at hs,
  rw [ideal.map_span, ideal.map_top] at hs,
  apply hP.of_localization_span_target _ _ hs,
  rintro ⟨_, r, hr, rfl⟩,
  have := hs' ⟨r, hr⟩,
  convert hP.stable_under_composition _ _ (hP.holds_for_localization_away (localization.away r) r)
    (hs' ⟨r, hr⟩) using 1,
  exact (is_localization.map_comp _).symm
end

end ring_hom

end properties

section ideal

open_locale non_zero_divisors

/-- Let `I J : ideal R`. If the localization of `I` at each maximal ideal `P` is included in
the localization of `J` at `P`, then `I ≤ J`. -/
lemma ideal.le_of_localization_maximal {I J : ideal R}
  (h : ∀ (P : ideal R) (hP : P.is_maximal),
    ideal.map (algebra_map R (by exactI localization.at_prime P)) I ≤
      ideal.map (algebra_map R (by exactI localization.at_prime P)) J) :
  I ≤ J :=
begin
  intros x hx,
  suffices : J.colon (ideal.span {x}) = ⊤,
  { simpa using submodule.mem_colon.mp
      (show (1 : R) ∈ J.colon (ideal.span {x}), from this.symm ▸ submodule.mem_top)
      x (ideal.mem_span_singleton_self x) },
  refine not.imp_symm (J.colon (ideal.span {x})).exists_le_maximal _,
  push_neg,
  introsI P hP le,
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, eq⟩ := (is_localization.mem_map_algebra_map_iff P.prime_compl _).mp
    (h P hP (ideal.mem_map_of_mem _ hx)),
  rw [← _root_.map_mul, ← sub_eq_zero, ← map_sub] at eq,
  obtain ⟨⟨m, hm⟩, eq⟩ := (is_localization.map_eq_zero_iff P.prime_compl _ _).mp eq,
  refine hs ((hP.is_prime.mem_or_mem (le (ideal.mem_colon_singleton.mpr _))).resolve_right hm),
  simp only [subtype.coe_mk, mul_sub, sub_eq_zero, mul_comm x s, mul_left_comm] at eq,
  simpa only [mul_assoc, eq] using J.mul_mem_left m ha
end

/-- Let `I J : ideal R`. If the localization of `I` at each maximal ideal `P` is equal to
the localization of `J` at `P`, then `I = J`. -/
theorem ideal.eq_of_localization_maximal {I J : ideal R}
  (h : ∀ (P : ideal R) (hP : P.is_maximal),
    ideal.map (algebra_map R (by exactI localization.at_prime P)) I =
      ideal.map (algebra_map R (by exactI localization.at_prime P)) J) :
  I = J :=
le_antisymm
  (ideal.le_of_localization_maximal (λ P hP, (h P hP).le))
  (ideal.le_of_localization_maximal (λ P hP, (h P hP).ge))

/-- An ideal is trivial if its localization at every maximal ideal is trivial. -/
lemma ideal_eq_bot_of_localization' (I : ideal R)
   (h : ∀ (J : ideal R) (hJ : J.is_maximal),
      ideal.map (algebra_map R (by exactI (localization.at_prime J))) I = ⊥) : I = ⊥ :=
ideal.eq_of_localization_maximal (λ P hP, (by simpa using h P hP))

-- TODO: This proof should work for all modules, once we have enough material on submodules of
-- localized modules.
/-- An ideal is trivial if its localization at every maximal ideal is trivial. -/
lemma ideal_eq_bot_of_localization (I : ideal R)
   (h : ∀ (J : ideal R) (hJ : J.is_maximal),
      by exactI is_localization.coe_submodule (localization.at_prime J) I = ⊥) : I = ⊥ :=
ideal_eq_bot_of_localization' _ (λ P hP, (ideal.map_eq_bot_iff_le_ker _).mpr (λ x hx,
  by { rw [ring_hom.mem_ker, ← submodule.mem_bot R, ← h P hP, is_localization.mem_coe_submodule],
       exact ⟨x, hx, rfl⟩ }))

lemma eq_zero_of_localization (r : R)
   (h : ∀ (J : ideal R) (hJ : J.is_maximal),
      by exactI algebra_map R (localization.at_prime J) r = 0) : r = 0 :=
begin
  rw ← ideal.span_singleton_eq_bot,
  apply ideal_eq_bot_of_localization,
  intros J hJ,
  delta is_localization.coe_submodule,
  erw [submodule.map_span, submodule.span_eq_bot],
  rintro _ ⟨_, h', rfl⟩,
  cases set.mem_singleton_iff.mpr h',
  exact h J hJ,
end

end ideal

section reduced

lemma localization_is_reduced : localization_preserves (λ R hR, by exactI is_reduced R) :=
begin
  introv R _ _,
  resetI,
  constructor,
  rintro x ⟨(_|n), e⟩,
  { simpa using congr_arg (*x) e },
  obtain ⟨⟨y, m⟩, hx⟩ := is_localization.surj M x,
  dsimp only at hx,
  let hx' := congr_arg (^ n.succ) hx,
  simp only [mul_pow, e, zero_mul, ← ring_hom.map_pow] at hx',
  rw [← (algebra_map R S).map_zero] at hx',
  obtain ⟨m', hm'⟩ := (is_localization.eq_iff_exists M S).mp hx',
  apply_fun (*m'^n) at hm',
  simp only [mul_assoc, zero_mul, mul_zero] at hm',
  rw [← mul_left_comm, ← pow_succ, ← mul_pow] at hm',
  replace hm' := is_nilpotent.eq_zero ⟨_, hm'.symm⟩,
  rw [← (is_localization.map_units S m).mul_left_inj, hx, zero_mul,
    is_localization.map_eq_zero_iff M],
  exact ⟨m', by rw [← hm', mul_comm]⟩
end

instance [is_reduced R] : is_reduced (localization M) := localization_is_reduced M _ infer_instance

lemma is_reduced_of_localization_maximal :
  of_localization_maximal (λ R hR, by exactI is_reduced R) :=
begin
  introv R h,
  constructor,
  intros x hx,
  apply eq_zero_of_localization,
  intros J hJ,
  specialize h J hJ,
  resetI,
  exact (hx.map $ algebra_map R $ localization.at_prime J).eq_zero,
end

end reduced

section surjective

lemma localization_preserves_surjective :
  ring_hom.localization_preserves (λ R S _ _ f, function.surjective f) :=
begin
  introv R H x,
  resetI,
  obtain ⟨x, ⟨_, s, hs, rfl⟩, rfl⟩ := is_localization.mk'_surjective (M.map f) x,
  obtain ⟨y, rfl⟩ := H x,
  use is_localization.mk' R' y ⟨s, hs⟩,
  rw is_localization.map_mk',
  refl,
end

lemma surjective_of_localization_span :
  ring_hom.of_localization_span (λ R S _ _ f, function.surjective f) :=
begin
  introv R e H,
  rw [← set.range_iff_surjective, set.eq_univ_iff_forall],
  resetI,
  letI := f.to_algebra,
  intro x,
  apply submodule.mem_of_span_eq_top_of_smul_pow_mem (algebra.of_id R S).to_linear_map.range s e,
  intro r,
  obtain ⟨a, e'⟩ := H r (algebra_map _ _ x),
  obtain ⟨b, ⟨_, n, rfl⟩, rfl⟩ := is_localization.mk'_surjective (submonoid.powers (r : R)) a,
  erw is_localization.map_mk' at e',
  rw [eq_comm, is_localization.eq_mk'_iff_mul_eq, subtype.coe_mk, subtype.coe_mk, ← map_mul] at e',
  obtain ⟨⟨_, n', rfl⟩, e''⟩ := (is_localization.eq_iff_exists (submonoid.powers (f r)) _).mp e',
  rw [subtype.coe_mk, mul_comm x, ←mul_assoc, ← map_pow, ← map_mul, ← map_mul, ← pow_add] at e'',
  exact ⟨n' + n, _, e''.symm⟩
end

end surjective

section finite

/-- If `S` is a finite `R`-algebra, then `S' = M⁻¹S` is a finite `R' = M⁻¹R`-algebra. -/
lemma localization_finite : ring_hom.localization_preserves @ring_hom.finite :=
begin
  introv R hf,
  -- Setting up the `algebra` and `is_scalar_tower` instances needed
  resetI,
  letI := f.to_algebra,
  letI := ((algebra_map S S').comp f).to_algebra,
  let f' : R' →+* S' := is_localization.map S' f (submonoid.le_comap_map M),
  letI := f'.to_algebra,
  haveI : is_scalar_tower R R' S' :=
    is_scalar_tower.of_algebra_map_eq' (is_localization.map_comp _).symm,
  let fₐ : S →ₐ[R] S' := alg_hom.mk' (algebra_map S S') (λ c x, ring_hom.map_mul _ _ _),

  -- We claim that if `S` is generated by `T` as an `R`-module,
  -- then `S'` is generated by `T` as an `R'`-module.
  unfreezingI { obtain ⟨T, hT⟩ := hf },
  use T.image (algebra_map S S'),
  rw eq_top_iff,
  rintro x -,

  -- By the hypotheses, for each `x : S'`, we have `x = y / (f r)` for some `y : S` and `r : M`.
  -- Since `S` is generated by `T`, the image of `y` should fall in the span of the image of `T`.
  obtain ⟨y, ⟨_, ⟨r, hr, rfl⟩⟩, rfl⟩ := is_localization.mk'_surjective (M.map f) x,
  rw [is_localization.mk'_eq_mul_mk'_one, mul_comm, finset.coe_image],
  have hy : y ∈ submodule.span R ↑T, by { rw hT, trivial },
  replace hy : algebra_map S S' y ∈ submodule.map fₐ.to_linear_map (submodule.span R T) :=
    submodule.mem_map_of_mem hy,
  rw submodule.map_span fₐ.to_linear_map T at hy,
  have H : submodule.span R ((algebra_map S S') '' T) ≤
    (submodule.span R' ((algebra_map S S') '' T)).restrict_scalars R,
  { rw submodule.span_le, exact submodule.subset_span },

  -- Now, since `y ∈ span T`, and `(f r)⁻¹ ∈ R'`, `x / (f r)` is in `span T` as well.
  convert (submodule.span R' ((algebra_map S S') '' T)).smul_mem
    (is_localization.mk' R' (1 : R) ⟨r, hr⟩) (H hy) using 1,
  rw algebra.smul_def,
  erw is_localization.map_mk',
  rw map_one,
  refl,
end

lemma localization_away_map_finite (r : R) [is_localization.away r R']
  [is_localization.away (f r) S'] (hf : f.finite) :
    (is_localization.away.map R' S' f r).finite :=
localization_finite.away r hf

/--
Let `S` be an `R`-algebra, `M` an submonoid of `R`, and `S' = M⁻¹S`.
If the image of some `x : S` falls in the span of some finite `s ⊆ S'` over `R`,
then there exists some `m : M` such that `m • x` falls in the
span of `finset_integer_multiple _ s` over `R`.
-/
lemma is_localization.smul_mem_finset_integer_multiple_span [algebra R S]
  [algebra R S'] [is_scalar_tower R S S']
  [is_localization (M.map (algebra_map R S)) S'] (x : S)
  (s : finset S') (hx : algebra_map S S' x ∈ submodule.span R (s : set S')) :
    ∃ m : M, m • x ∈ submodule.span R
      (is_localization.finset_integer_multiple (M.map (algebra_map R S)) s : set S) :=
begin
  let g : S →ₐ[R] S' := alg_hom.mk' (algebra_map S S')
    (λ c x, by simp [algebra.algebra_map_eq_smul_one]),

  -- We first obtain the `y' ∈ M` such that `s' = y' • s` is falls in the image of `S` in `S'`.
  let y := is_localization.common_denom_of_finset (M.map (algebra_map R S)) s,
  have hx₁ : (y : S) • ↑s = g '' _ := (is_localization.finset_integer_multiple_image _ s).symm,
  obtain ⟨y', hy', e : algebra_map R S y' = y⟩ := y.prop,
  have : algebra_map R S y' • (s : set S') = y' • s :=
    by simp_rw [algebra.algebra_map_eq_smul_one, smul_assoc, one_smul],
  rw [← e, this] at hx₁,
  replace hx₁ := congr_arg (submodule.span R) hx₁,
  rw submodule.span_smul at hx₁,
  replace hx : _ ∈ y' • submodule.span R (s : set S') := set.smul_mem_smul_set hx,
  rw hx₁ at hx,
  erw [← g.map_smul, ← submodule.map_span (g : S →ₗ[R] S')] at hx,
  -- Since `x` falls in the span of `s` in `S'`, `y' • x : S` falls in the span of `s'` in `S'`.
  -- That is, there exists some `x' : S` in the span of `s'` in `S` and `x' = y' • x` in `S'`.
  -- Thus `a • (y' • x) = a • x' ∈ span s'` in `S` for some `a ∈ M`.
  obtain ⟨x', hx', hx'' : algebra_map _ _ _ = _⟩ := hx,
  obtain ⟨⟨_, a, ha₁, rfl⟩, ha₂⟩ := (is_localization.eq_iff_exists
    (M.map (algebra_map R S)) S').mp hx'',
  use (⟨a, ha₁⟩ : M) * (⟨y', hy'⟩ : M),
  convert (submodule.span R (is_localization.finset_integer_multiple
    (submonoid.map (algebra_map R S) M) s : set S)).smul_mem a hx' using 1,
  convert ha₂.symm,
  { rw [subtype.coe_mk, submonoid.smul_def, submonoid.coe_mul, ← smul_smul],
    exact algebra.smul_def _ _ },
  { exact algebra.smul_def _ _ }
end

/-- If `S` is an `R' = M⁻¹R` algebra, and `x ∈ span R' s`,
then `t • x ∈ span R s` for some `t : M`.-/
lemma multiple_mem_span_of_mem_localization_span [algebra R' S] [algebra R S]
  [is_scalar_tower R R' S] [is_localization M R']
  (s : set S) (x : S) (hx : x ∈ submodule.span R' s) :
    ∃ t : M, t • x ∈ submodule.span R s :=
begin
  classical,
  obtain ⟨s', hss', hs'⟩ := submodule.mem_span_finite_of_mem_span hx,
  rsuffices ⟨t, ht⟩ : ∃ t : M, t • x ∈ submodule.span R (s' : set S),
  { exact ⟨t, submodule.span_mono hss' ht⟩ },
  clear hx hss' s,
  revert x,
  apply s'.induction_on,
  { intros x hx, use 1, simpa using hx },
  rintros a s ha hs x hx,
  simp only [finset.coe_insert, finset.image_insert, finset.coe_image, subtype.coe_mk,
    submodule.mem_span_insert] at hx ⊢,
  rcases hx with ⟨y, z, hz, rfl⟩,
  rcases is_localization.surj M y with ⟨⟨y', s'⟩, e⟩,
  replace e : _ * a = _ * a := (congr_arg (λ x, algebra_map R' S x * a) e : _),
  simp_rw [ring_hom.map_mul, ← is_scalar_tower.algebra_map_apply, mul_comm (algebra_map R' S y),
    mul_assoc, ← algebra.smul_def] at e,
  rcases hs _ hz with ⟨t, ht⟩,
  refine ⟨t*s', t*y', _, (submodule.span R (s : set S)).smul_mem s' ht, _⟩,
  rw [smul_add, ← smul_smul, mul_comm, ← smul_smul, ← smul_smul, ← e],
  refl,
end

/-- If `S` is an `R' = M⁻¹R` algebra, and `x ∈ adjoin R' s`,
then `t • x ∈ adjoin R s` for some `t : M`.-/
lemma multiple_mem_adjoin_of_mem_localization_adjoin [algebra R' S] [algebra R S]
  [is_scalar_tower R R' S] [is_localization M R']
  (s : set S) (x : S) (hx : x ∈ algebra.adjoin R' s) :
    ∃ t : M, t • x ∈ algebra.adjoin R s :=
begin
  change ∃ (t : M), t • x ∈ (algebra.adjoin R s).to_submodule,
  change x ∈ (algebra.adjoin R' s).to_submodule at hx,
  simp_rw [algebra.adjoin_eq_span] at hx ⊢,
  exact multiple_mem_span_of_mem_localization_span M R' _ _ hx
end

lemma finite_of_localization_span : ring_hom.of_localization_span @ring_hom.finite :=
begin
  rw ring_hom.of_localization_span_iff_finite,
  introv R hs H,
  -- We first setup the instances
  resetI,
  letI := f.to_algebra,
  letI := λ (r : s), (localization.away_map f r).to_algebra,
  haveI : ∀ r : s, is_localization ((submonoid.powers (r : R)).map (algebra_map R S))
    (localization.away (f r)),
  { intro r, rw submonoid.map_powers, exact localization.is_localization },
  haveI : ∀ r : s, is_scalar_tower R (localization.away (r : R)) (localization.away (f r)) :=
    λ r, is_scalar_tower.of_algebra_map_eq' (is_localization.map_comp _).symm,

  -- By the hypothesis, we may find a finite generating set for each `Sᵣ`. This set can then be
  -- lifted into `R` by multiplying a sufficiently large power of `r`. I claim that the union of
  -- these generates `S`.
  constructor,
  replace H := λ r, (H r).1,
  choose s₁ s₂ using H,
  let sf := λ (x : s), is_localization.finset_integer_multiple (submonoid.powers (f x)) (s₁ x),
  use s.attach.bUnion sf,
  rw [submodule.span_attach_bUnion, eq_top_iff],

  -- It suffices to show that `r ^ n • x ∈ span T` for each `r : s`, since `{ r ^ n }` spans `R`.
  -- This then follows from the fact that each `x : R` is a linear combination of the generating set
  -- of `Sᵣ`. By multiplying a sufficiently large power of `r`, we can cancel out the `r`s in the
  -- denominators of both the generating set and the coefficients.
  rintro x -,
  apply submodule.mem_of_span_eq_top_of_smul_pow_mem _ (s : set R) hs _ _,
  intro r,
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ := multiple_mem_span_of_mem_localization_span
    (submonoid.powers (r : R)) (localization.away (r : R)) (s₁ r : set (localization.away (f r)))
      (algebra_map S _ x) (by { rw s₂ r, trivial }),
  rw [submonoid.smul_def, algebra.smul_def, is_scalar_tower.algebra_map_apply R S,
    subtype.coe_mk, ← map_mul] at hn₁,
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ := is_localization.smul_mem_finset_integer_multiple_span
    (submonoid.powers (r : R)) (localization.away (f r)) _ (s₁ r) hn₁,
  rw [submonoid.smul_def, ← algebra.smul_def, smul_smul, subtype.coe_mk, ← pow_add] at hn₂,
  simp_rw submonoid.map_powers at hn₂,
  use n₂ + n₁,
  exact le_supr (λ (x : s), submodule.span R (sf x : set S)) r hn₂,
end

end finite

section finite_type

lemma localization_finite_type : ring_hom.localization_preserves @ring_hom.finite_type :=
begin
  introv R hf,
  -- mirrors the proof of `localization_map_finite`
  resetI,
  letI := f.to_algebra,
  letI := ((algebra_map S S').comp f).to_algebra,
  let f' : R' →+* S' := is_localization.map S' f (submonoid.le_comap_map M),
  letI := f'.to_algebra,
  haveI : is_scalar_tower R R' S' :=
    is_scalar_tower.of_algebra_map_eq' (is_localization.map_comp _).symm,
  let fₐ : S →ₐ[R] S' := alg_hom.mk' (algebra_map S S') (λ c x, ring_hom.map_mul _ _ _),

  obtain ⟨T, hT⟩ := id hf,
  use T.image (algebra_map S S'),
  rw eq_top_iff,
  rintro x -,
  obtain ⟨y, ⟨_, ⟨r, hr, rfl⟩⟩, rfl⟩ := is_localization.mk'_surjective (M.map f) x,
  rw [is_localization.mk'_eq_mul_mk'_one, mul_comm, finset.coe_image],
  have hy : y ∈ algebra.adjoin R (T : set S), by { rw hT, trivial },
  replace hy : algebra_map S S' y ∈ (algebra.adjoin R (T : set S)).map fₐ :=
    subalgebra.mem_map.mpr ⟨_, hy, rfl⟩,
  rw fₐ.map_adjoin T at hy,
  have H : algebra.adjoin R ((algebra_map S S') '' T) ≤
    (algebra.adjoin R' ((algebra_map S S') '' T)).restrict_scalars R,
  { rw algebra.adjoin_le_iff, exact algebra.subset_adjoin },
  convert (algebra.adjoin R' ((algebra_map S S') '' T)).smul_mem (H hy)
    (is_localization.mk' R' (1 : R) ⟨r, hr⟩) using 1,
  rw algebra.smul_def,
  erw is_localization.map_mk',
  rw map_one,
  refl,
end

lemma localization_away_map_finite_type (r : R) [is_localization.away r R']
  [is_localization.away (f r) S'] (hf : f.finite_type) :
    (is_localization.away.map R' S' f r).finite_type :=
localization_finite_type.away r hf

variable {S'}

/--
Let `S` be an `R`-algebra, `M` a submonoid of `S`, `S' = M⁻¹S`.
Suppose the image of some `x : S` falls in the adjoin of some finite `s ⊆ S'` over `R`,
and `A` is an `R`-subalgebra of `S` containing both `M` and the numerators of `s`.
Then, there exists some `m : M` such that `m • x` falls in `A`.
-/
lemma is_localization.exists_smul_mem_of_mem_adjoin [algebra R S]
  [algebra R S'] [is_scalar_tower R S S'] (M : submonoid S)
  [is_localization M S'] (x : S) (s : finset S') (A : subalgebra R S)
  (hA₁ : (is_localization.finset_integer_multiple M s : set S) ⊆ A)
  (hA₂ : M ≤ A.to_submonoid)
  (hx : algebra_map S S' x ∈ algebra.adjoin R (s : set S')) :
    ∃ m : M, m • x ∈ A :=
begin
  let g : S →ₐ[R] S' := is_scalar_tower.to_alg_hom R S S',
  let y := is_localization.common_denom_of_finset M s,
  have hx₁ : (y : S) • ↑s = g '' _ := (is_localization.finset_integer_multiple_image _ s).symm,
  obtain ⟨n, hn⟩ := algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin (y : S) (s : set S')
    (A.map g) (by { rw hx₁, exact set.image_subset _ hA₁ }) hx (set.mem_image_of_mem _ (hA₂ y.2)),
  obtain ⟨x', hx', hx''⟩ := hn n (le_of_eq rfl),
  rw [algebra.smul_def, ← _root_.map_mul] at hx'',
  obtain ⟨a, ha₂⟩ := (is_localization.eq_iff_exists M S').mp hx'',
  use a * y ^ n,
  convert A.mul_mem hx' (hA₂ a.prop),
  rw [submonoid.smul_def, smul_eq_mul, submonoid.coe_mul, submonoid.coe_pow, mul_assoc, ←ha₂,
    mul_comm],
end

/--
Let `S` be an `R`-algebra, `M` an submonoid of `R`, and `S' = M⁻¹S`.
If the image of some `x : S` falls in the adjoin of some finite `s ⊆ S'` over `R`,
then there exists some `m : M` such that `m • x` falls in the
adjoin of `finset_integer_multiple _ s` over `R`.
-/
lemma is_localization.lift_mem_adjoin_finset_integer_multiple [algebra R S]
  [algebra R S'] [is_scalar_tower R S S']
  [is_localization (M.map (algebra_map R S)) S'] (x : S)
  (s : finset S') (hx : algebra_map S S' x ∈ algebra.adjoin R (s : set S')) :
    ∃ m : M, m • x ∈ algebra.adjoin R
      (is_localization.finset_integer_multiple (M.map (algebra_map R S)) s : set S) :=
begin
  obtain ⟨⟨_, a, ha, rfl⟩, e⟩ := is_localization.exists_smul_mem_of_mem_adjoin
    (M.map (algebra_map R S)) x s (algebra.adjoin R _) algebra.subset_adjoin _ hx,
  { exact ⟨⟨a, ha⟩, by simpa [submonoid.smul_def] using e⟩ },
{ rintros _ ⟨a, ha, rfl⟩, exact subalgebra.algebra_map_mem _ a }
end

lemma finite_type_of_localization_span : ring_hom.of_localization_span @ring_hom.finite_type :=
begin
  rw ring_hom.of_localization_span_iff_finite,
  introv R hs H,
  -- mirrors the proof of `finite_of_localization_span`
  resetI,
  letI := f.to_algebra,
  letI := λ (r : s), (localization.away_map f r).to_algebra,
  haveI : ∀ r : s, is_localization ((submonoid.powers (r : R)).map (algebra_map R S))
    (localization.away (f r)),
  { intro r, rw submonoid.map_powers, exact localization.is_localization },
  haveI : ∀ r : s, is_scalar_tower R (localization.away (r : R)) (localization.away (f r)) :=
    λ r, is_scalar_tower.of_algebra_map_eq' (is_localization.map_comp _).symm,

  constructor,
  replace H := λ r, (H r).1,
  choose s₁ s₂ using H,
  let sf := λ (x : s), is_localization.finset_integer_multiple (submonoid.powers (f x)) (s₁ x),
  use s.attach.bUnion sf,
  convert (algebra.adjoin_attach_bUnion sf).trans _,
  rw eq_top_iff,
  rintro x -,
  apply (⨆ (x : s), algebra.adjoin R (sf x : set S)).to_submodule
    .mem_of_span_eq_top_of_smul_pow_mem _ hs _ _,
  intro r,
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ := multiple_mem_adjoin_of_mem_localization_adjoin
    (submonoid.powers (r : R)) (localization.away (r : R)) (s₁ r : set (localization.away (f r)))
      (algebra_map S (localization.away (f r)) x) (by { rw s₂ r, trivial }),
  rw [submonoid.smul_def, algebra.smul_def, is_scalar_tower.algebra_map_apply R S,
    subtype.coe_mk, ← map_mul] at hn₁,
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ := is_localization.lift_mem_adjoin_finset_integer_multiple
    (submonoid.powers (r : R)) _ (s₁ r) hn₁,
  rw [submonoid.smul_def, ← algebra.smul_def, smul_smul, subtype.coe_mk, ← pow_add] at hn₂,
  simp_rw submonoid.map_powers at hn₂,
  use n₂ + n₁,
  exact le_supr (λ (x : s), algebra.adjoin R (sf x : set S)) r hn₂
end

end finite_type
