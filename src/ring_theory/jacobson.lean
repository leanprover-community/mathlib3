/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.mv_polynomial
import ring_theory.ideal_operations
import ring_theory.localization
import ring_theory.jacobson_ideal

/-!
# Jacobson Rings

The following conditions are equivalent for a ring `R`:
1. Every radical ideal `I` is equal to its jacobson radical
2. Every radical ideal `I` can be written as an intersection of maximal ideals
3. Every prime ideal `I` is equal to its jacobson radical

Any ring satisfying any of these equivalent conditions is said to be Jacobson.

Some particular examples of Jacobson rings are also proven.
`is_jacobson_quotient` says that the quotient of a jacobson ring is jacobson.
`is_jacobson_localization` says the localization of a jacobson ring to a single element is jacobson.

## Main definitions

Let `R` be a commutative ring. Jacobson Rings are defined using the first of the above conditions

* `is_jacobson R` is the proposition that `R` is a Jacobson ring. It is a class,
  implemented as the predicate that for any ideal, `I.radical = I` implies `I.jacobson = I`.

## Main statements

* `is_jacobson_iff_prime_eq` is the equivalence between conditions 1 and 3 above.

* `is_jacobson_iff_Inf_maximal` is the equivalence between conditions 1 and 2 above.

* `is_jacobson_of_surjective` says that if `R` is a jacobson ring and `f : R →+* S` surjective,
then `S` is also a jacobson ring

## Tags

Jacobson, Jacobson Ring

-/

universes u v

namespace ideal
variables {R : Type u} [comm_ring R] {I : ideal R}
variables {S : Type v} [comm_ring S]

--local attribute [instance] classical.prop_decidable

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

end is_jacobson


section localization
open localization_map
variables {y : R} (f : localization_map (submonoid.closure {y} : submonoid R) S)

lemma disjoint_closure_singleton_iff_not_mem {I : ideal R} (hI : I.radical = I) :
  disjoint ((submonoid.closure {y} : submonoid R) : set R) ↑I ↔ y ∉ I.1 :=
begin
  refine ⟨λ h, set.disjoint_left.1 h (submonoid.subset_closure (by simp)), λ h, _⟩,
  rw disjoint_iff,
  rw eq_bot_iff,
  rintros x ⟨hx, hx'⟩,
  exfalso,
  apply h,
  erw submonoid.mem_closure_singleton at hx,
  cases hx with n hn,
  rw ← hn at hx',
  rw ← hI at hx' ⊢,
  refine mem_radical_of_pow_mem hx',
end

/-- The submonoid generated by the single element `y` -/
abbreviation M (y : R) : submonoid R := (submonoid.closure {y} : submonoid R)

/-- If `R` is a jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This gives the correspondence in the particular case of an ideal and its comap.
See `le_order_iso_of_maximal` for the more general order isomorphism -/
lemma is_maximal_iff_is_maximal_disjoint [H : is_jacobson R] (J : ideal S) :
  J.is_maximal ↔ (comap f.to_map J).is_maximal ∧ disjoint (M y : set R) ↑(ideal.comap f.to_map J) :=
begin
  split,
  { refine λ h, ⟨_, λ m hm, h.1 (ideal.eq_top_of_is_unit_mem _ hm.2 (map_units f ⟨m, hm.left⟩))⟩,
    rw is_jacobson_iff_prime_eq at H,
    have : J.is_prime := is_maximal.is_prime h,
    rw is_prime_iff_is_prime_disjoint f at this,
    specialize H (comap f.to_map J) this.left,
    have : y ∉ (comap f.to_map J).1 :=
      set.disjoint_left.1 this.right (submonoid.subset_closure (by simp)),
    erw [← H, mem_Inf] at this,
    push_neg at this,
    rcases this with ⟨I, hI, hI'⟩,
    suffices : comap f.to_map J = I,
    { rw this,
      exact hI.right },
    have : J ≤ map f.to_map I := (map_comap f J) ▸ (map_mono hI.left),
    cases (classical.em (J = map f.to_map I)) with hJ hJ,
    { rw hJ,
      rw comap_map_of_is_prime_disjoint f I (is_maximal.is_prime hI.right),
      rwa disjoint_closure_singleton_iff_not_mem (is_maximal.is_prime hI.right).radical},
    { exfalso,
      have hI_p : (map f.to_map I).is_prime,
      { refine is_prime_of_is_prime_disjoint f I ⟨is_maximal.is_prime hI.right, _⟩,
        rwa disjoint_closure_singleton_iff_not_mem (is_maximal.is_prime hI.right).radical, },
      refine hI_p.left (h.right _ (lt_of_le_of_ne this hJ)) } },
  { intro h,
    split,
    { refine λ hJ, h.left.left (eq_top_iff.2 _),
      rwa [eq_top_iff, (le_order_embedding f).ord] at hJ },
    { intros I hI,
      have := congr_arg (map f.to_map) (h.left.right _ ⟨comap_mono (le_of_lt hI), _⟩),
      rwa [map_comap f I, map_top f.to_map] at this,
      refine λ hI', hI.right _,
      rw [← map_comap f I, ← map_comap f J],
      exact map_mono hI' } }
end

/-- If `R` is a jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This gives the correspondence in the particular case of an ideal and its map.
See `le_order_iso_of_maximal` for the more general statement, and the reverse of this implication -/
lemma is_maximal_of_is_maximal_disjoint [is_jacobson R] (I : ideal R) :
  I.is_maximal ∧ disjoint (M y : set R) ↑I → (map f.to_map I).is_maximal :=
λ h, by rwa [is_maximal_iff_is_maximal_disjoint f,
  comap_map_of_is_prime_disjoint f I (is_maximal.is_prime h.1) h.2]

/-- If `R` is a jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y` -/
def le_order_iso_of_maximal [is_jacobson R] :
  ((≤) : {p : ideal S // p.is_maximal} → {p : ideal S // p.is_maximal} → Prop) ≃o
  ((≤) : {p : ideal R // p.is_maximal ∧ disjoint (M y : set R) ↑p}
            → {p : ideal R // p.is_maximal ∧ disjoint (M y : set R) ↑p} → Prop) :=
{ to_fun := λ p, ⟨ideal.comap f.to_map p.1, (is_maximal_iff_is_maximal_disjoint f p.1).1 p.2⟩,
  inv_fun := λ p, ⟨ideal.map f.to_map p.1, (is_maximal_of_is_maximal_disjoint f p.1) p.2⟩,
  left_inv := λ J, subtype.eq (map_comap f J),
  right_inv := λ I, subtype.eq (comap_map_of_is_prime_disjoint f
    I.1 (is_maximal.is_prime I.2.1) I.2.2),
  ord' := λ I I', ⟨λ h x hx, h hx, λ h, (show I.val ≤ I'.val,
    from (map_comap f I.val) ▸ (map_comap f I'.val) ▸ (ideal.map_mono h))⟩ }

/-- If `y ∈ R` and `S` is the localization the submonoid generated by `y`, then `S` is jacobson -/
lemma is_jacobson_localization [H : is_jacobson R] (f : localization_map (M y) S) : is_jacobson S :=
begin
  let H' := H,
  rw is_jacobson_iff_prime_eq at H' ⊢,
  intros P' hP',
  let P := comap f.to_map P',
  refine le_antisymm _ le_jacobson,
  rw localization_map.is_prime_iff_is_prime_disjoint f P' at hP',
  cases hP' with hP' hPM,
  have hP : P.jacobson = P := H' _ hP',
  refine le_trans _ (le_of_eq (localization_map.map_comap f P')),
  refine le_trans (le_of_eq (localization_map.map_comap f P'.jacobson).symm) _,
  refine map_mono _,
  show comap f.to_map P'.jacobson ≤ P,
  let M : submonoid R := submonoid.closure {y},
  let I₁ := Inf { I : ideal R | P ≤ I ∧ I.is_maximal ∧ disjoint (M : set R) ↑I },
  let I₂ := Inf { I : ideal R | I.is_maximal ∧ ¬ disjoint (M : set R) ↑I },
  have : I₁ ⊓ I₂ ≤ P.jacobson, {
    refine le_Inf (λ J hJ, _),
    cases (classical.em (disjoint (M : set R) ↑J)),
    { refine inf_le_left_of_le (Inf_le ⟨hJ.1, hJ.2, h⟩) },
    { refine inf_le_right_of_le (Inf_le ⟨hJ.2, h⟩) }
  },
  have : Inf { I : ideal R | P ≤ I ∧ I.is_maximal ∧ disjoint (M : set R) ↑I } ≤ P, {
    intros x hx,
    have hxy : x * y ∈ P.jacobson, {
      refine this ⟨_, _⟩,
      exact (mul_comm y x) ▸ I₁.smul_mem y hx,
      refine I₂.smul_mem x _,
      rw mem_Inf,
      rintros J ⟨hJ_max, hJ⟩,
      rw set.not_disjoint_iff at hJ,
      rcases hJ with ⟨a, ⟨ha, ha'⟩⟩,
      erw submonoid.mem_closure_singleton at ha,
      cases ha with _ hn,
      rw ← hn at ha',
      refine is_prime.mem_of_pow_mem (is_maximal.is_prime hJ_max) _ ha',
    },
    rw hP at hxy,
    cases hP'.right hxy with hxy hxy,
    { exact hxy },
    { exfalso,
      refine hPM ⟨_, hxy⟩,
      erw submonoid.mem_closure_singleton,
      use 1,
      rw pow_one }
  },
  refine le_trans _ this,
  rw [ideal.jacobson, comap_Inf', Inf_eq_infi],
  refine infi_le_infi_of_subset _,
  rintros I ⟨hI, hI'⟩,
  simp,
  refine ⟨map f.to_map I, ⟨_, _⟩⟩,
  { exact ⟨le_trans (le_of_eq ((localization_map.map_comap f P').symm)) (map_mono hI),
      is_maximal_of_is_maximal_disjoint f _ hI'⟩ },
  { exact localization_map.comap_map_of_is_prime_disjoint f I
      (is_maximal.is_prime hI'.left) hI'.right }
end

end localization

end ideal
