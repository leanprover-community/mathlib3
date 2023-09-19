/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.finite_type
import ring_theory.mv_polynomial.tower
import ring_theory.ideal.quotient_operations

/-!
# Finiteness conditions in commutative algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define several notions of finiteness that are common in commutative algebra.

## Main declarations

- `module.finite`, `algebra.finite`, `ring_hom.finite`, `alg_hom.finite`
  all of these express that some object is finitely generated *as module* over some base ring.
- `algebra.finite_type`, `ring_hom.finite_type`, `alg_hom.finite_type`
  all of these express that some object is finitely generated *as algebra* over some base ring.
- `algebra.finite_presentation`, `ring_hom.finite_presentation`, `alg_hom.finite_presentation`
  all of these express that some object is finitely presented *as algebra* over some base ring.

-/

open function (surjective)
open_locale big_operators polynomial

section module_and_algebra

variables (R A B M N : Type*)

/-- An algebra over a commutative semiring is `finite_presentation` if it is the quotient of a
polynomial ring in `n` variables by a finitely generated ideal. -/
def algebra.finite_presentation [comm_semiring R] [semiring A] [algebra R A] : Prop :=
∃ (n : ℕ) (f : mv_polynomial (fin n) R →ₐ[R] A),
  surjective f ∧ f.to_ring_hom.ker.fg

namespace algebra

variables [comm_ring R] [comm_ring A] [algebra R A] [comm_ring B] [algebra R B]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]

namespace finite_type

variables {R A B}

/-- A finitely presented algebra is of finite type. -/
lemma of_finite_presentation : finite_presentation R A → finite_type R A :=
begin
  rintro ⟨n, f, hf⟩,
  apply (finite_type.iff_quotient_mv_polynomial'').2,
  exact ⟨n, f, hf.1⟩
end

end finite_type

namespace finite_presentation

variables {R A B}

/-- An algebra over a Noetherian ring is finitely generated if and only if it is finitely
presented. -/
lemma of_finite_type [is_noetherian_ring R] : finite_type R A ↔ finite_presentation R A :=
begin
  refine ⟨λ h, _, algebra.finite_type.of_finite_presentation⟩,
  obtain ⟨n, f, hf⟩ := algebra.finite_type.iff_quotient_mv_polynomial''.1 h,
  refine ⟨n, f, hf, _⟩,
  have hnoet : is_noetherian_ring (mv_polynomial (fin n) R) := by apply_instance,
  replace hnoet := (is_noetherian_ring_iff.1 hnoet).noetherian,
  exact hnoet f.to_ring_hom.ker,
end

/-- If `e : A ≃ₐ[R] B` and `A` is finitely presented, then so is `B`. -/
lemma equiv (hfp : finite_presentation R A) (e : A ≃ₐ[R] B) : finite_presentation R B :=
begin
  obtain ⟨n, f, hf⟩ := hfp,
  use [n, alg_hom.comp ↑e f],
  split,
  { exact function.surjective.comp e.surjective hf.1 },
  suffices hker : (alg_hom.comp ↑e f).to_ring_hom.ker = f.to_ring_hom.ker,
  { rw hker, exact hf.2 },
  { have hco : (alg_hom.comp ↑e f).to_ring_hom = ring_hom.comp ↑e.to_ring_equiv f.to_ring_hom,
    { have h : (alg_hom.comp ↑e f).to_ring_hom = e.to_alg_hom.to_ring_hom.comp f.to_ring_hom := rfl,
      have h1 : ↑(e.to_ring_equiv) = (e.to_alg_hom).to_ring_hom := rfl,
      rw [h, h1] },
    rw [ring_hom.ker_eq_comap_bot, hco, ← ideal.comap_comap, ← ring_hom.ker_eq_comap_bot,
      ring_hom.ker_coe_equiv (alg_equiv.to_ring_equiv e), ring_hom.ker_eq_comap_bot] }
end

variable (R)

/-- The ring of polynomials in finitely many variables is finitely presented. -/
protected lemma mv_polynomial (ι : Type u_2) [finite ι] :
  finite_presentation R (mv_polynomial ι R) :=
by casesI nonempty_fintype ι; exact
let eqv := (mv_polynomial.rename_equiv R $ fintype.equiv_fin ι).symm in
⟨fintype.card ι, eqv, eqv.surjective,
  ((ring_hom.injective_iff_ker_eq_bot _).1 eqv.injective).symm ▸ submodule.fg_bot⟩

/-- `R` is finitely presented as `R`-algebra. -/
lemma self : finite_presentation R R :=
equiv (finite_presentation.mv_polynomial R pempty) (mv_polynomial.is_empty_alg_equiv R pempty)

/-- `R[X]` is finitely presented as `R`-algebra. -/
lemma polynomial : finite_presentation R R[X] :=
equiv (finite_presentation.mv_polynomial R punit) (mv_polynomial.punit_alg_equiv R)

variable {R}

/-- The quotient of a finitely presented algebra by a finitely generated ideal is finitely
presented. -/
protected lemma quotient {I : ideal A} (h : I.fg) (hfp : finite_presentation R A) :
  finite_presentation R (A ⧸ I) :=
begin
  obtain ⟨n, f, hf⟩ := hfp,
  refine ⟨n, (ideal.quotient.mkₐ R I).comp f, _, _⟩,
  { exact (ideal.quotient.mkₐ_surjective R I).comp hf.1 },
  { refine ideal.fg_ker_comp _ _ hf.2 _ hf.1,
    simp [h] }
end

/-- If `f : A →ₐ[R] B` is surjective with finitely generated kernel and `A` is finitely presented,
then so is `B`. -/
lemma of_surjective {f : A →ₐ[R] B} (hf : function.surjective f) (hker : f.to_ring_hom.ker.fg)
  (hfp : finite_presentation R A) : finite_presentation R B :=
equiv (hfp.quotient hker) (ideal.quotient_ker_alg_equiv_of_surjective hf)

lemma iff : finite_presentation R A ↔
  ∃ n (I : ideal (mv_polynomial (fin n) R)) (e : (_ ⧸ I) ≃ₐ[R] A), I.fg :=
begin
  split,
  { rintros ⟨n, f, hf⟩,
    exact ⟨n, f.to_ring_hom.ker, ideal.quotient_ker_alg_equiv_of_surjective hf.1, hf.2⟩ },
  { rintros ⟨n, I, e, hfg⟩,
    exact equiv ((finite_presentation.mv_polynomial R _).quotient hfg) e }
end

/-- An algebra is finitely presented if and only if it is a quotient of a polynomial ring whose
variables are indexed by a fintype by a finitely generated ideal. -/
lemma iff_quotient_mv_polynomial' : finite_presentation R A ↔ ∃ (ι : Type u_2) (_ : fintype ι)
  (f : mv_polynomial ι R →ₐ[R] A), surjective f ∧ f.to_ring_hom.ker.fg :=
begin
  split,
  { rintro ⟨n, f, hfs, hfk⟩,
    set ulift_var := mv_polynomial.rename_equiv R equiv.ulift,
    refine ⟨ulift (fin n), infer_instance, f.comp ulift_var.to_alg_hom,
      hfs.comp ulift_var.surjective,
      ideal.fg_ker_comp _ _ _ hfk ulift_var.surjective⟩,
    convert submodule.fg_bot,
    exact ring_hom.ker_coe_equiv ulift_var.to_ring_equiv, },
  { rintro ⟨ι, hfintype, f, hf⟩,
    resetI,
    have equiv := mv_polynomial.rename_equiv R (fintype.equiv_fin ι),
    refine ⟨fintype.card ι, f.comp equiv.symm,
      hf.1.comp (alg_equiv.symm equiv).surjective,
      ideal.fg_ker_comp _ f _ hf.2 equiv.symm.surjective⟩,
    convert submodule.fg_bot,
    exact ring_hom.ker_coe_equiv (equiv.symm.to_ring_equiv), }
end

/-- If `A` is a finitely presented `R`-algebra, then `mv_polynomial (fin n) A` is finitely presented
as `R`-algebra. -/
lemma mv_polynomial_of_finite_presentation (hfp : finite_presentation R A) (ι : Type*)
  [finite ι] : finite_presentation R (mv_polynomial ι A) :=
begin
  rw iff_quotient_mv_polynomial' at hfp ⊢,
  classical,
  obtain ⟨ι', _, f, hf_surj, hf_ker⟩ := hfp,
  resetI,
  let g := (mv_polynomial.map_alg_hom f).comp (mv_polynomial.sum_alg_equiv R ι ι').to_alg_hom,
  casesI nonempty_fintype (ι ⊕ ι'),
  refine ⟨ι ⊕ ι', by apply_instance, g,
    (mv_polynomial.map_surjective f.to_ring_hom hf_surj).comp (alg_equiv.surjective _),
    ideal.fg_ker_comp _ _ _ _ (alg_equiv.surjective _)⟩,
  { convert submodule.fg_bot,
    exact ring_hom.ker_coe_equiv (mv_polynomial.sum_alg_equiv R ι ι').to_ring_equiv },
  { rw [alg_hom.to_ring_hom_eq_coe, mv_polynomial.map_alg_hom_coe_ring_hom, mv_polynomial.ker_map],
    exact hf_ker.map mv_polynomial.C, }
end

/-- If `A` is an `R`-algebra and `S` is an `A`-algebra, both finitely presented, then `S` is
  finitely presented as `R`-algebra. -/
lemma trans [algebra A B] [is_scalar_tower R A B] (hfpA : finite_presentation R A)
  (hfpB : finite_presentation A B) : finite_presentation R B :=
begin
  obtain ⟨n, I, e, hfg⟩ := iff.1 hfpB,
  exact equiv ((mv_polynomial_of_finite_presentation hfpA _).quotient hfg) (e.restrict_scalars R)
end

open mv_polynomial

-- We follow the proof of https://stacks.math.columbia.edu/tag/0561
-- TODO: extract out helper lemmas and tidy proof.
lemma of_restrict_scalars_finite_presentation [algebra A B] [is_scalar_tower R A B]
  (hRB : finite_presentation R B) [hRA : finite_type R A] : finite_presentation A B :=
begin
  classical,
  obtain ⟨n, f, hf, s, hs⟩ := hRB,
  let RX := mv_polynomial (fin n) R, let AX := mv_polynomial (fin n) A,
  refine ⟨n, mv_polynomial.aeval (f ∘ X), _, _⟩,
  { rw [← algebra.range_top_iff_surjective, ← algebra.adjoin_range_eq_range_aeval, set.range_comp,
      _root_.eq_top_iff, ← @adjoin_adjoin_of_tower R A B, adjoin_image,
      adjoin_range_X, algebra.map_top, (algebra.range_top_iff_surjective _).mpr hf],
    exact subset_adjoin },
  { obtain ⟨t, ht⟩ := hRA.out,
    have := λ i : t, hf (algebra_map A B i),
    choose t' ht',
    have ht'' : algebra.adjoin R ((algebra_map A AX) '' t ∪ set.range (X : _ → AX)) = ⊤,
    { rw [adjoin_union_eq_adjoin_adjoin, ← subalgebra.restrict_scalars_top R],
      congr' 1,
      swap, { exact subalgebra.is_scalar_tower_mid _ },
      rw [adjoin_algebra_map, ht],
      apply subalgebra.restrict_scalars_injective R,
      rw [← adjoin_restrict_scalars, adjoin_range_X, subalgebra.restrict_scalars_top,
        subalgebra.restrict_scalars_top] },
    let g : t → AX := λ x, C (x : A) - map (algebra_map R A) (t' x),
    refine ⟨s.image (map (algebra_map R A)) ∪ t.attach.image g, _⟩,
    rw [finset.coe_union, finset.coe_image, finset.coe_image, finset.attach_eq_univ,
      finset.coe_univ, set.image_univ],
    let s₀ := _, let I := _, change ideal.span s₀ = I,
    have leI : ideal.span s₀ ≤ I,
    { rw [ideal.span_le],
      rintros _ (⟨x, hx, rfl⟩|⟨⟨x, hx⟩, rfl⟩),
      all_goals
        { dsimp [g], rw [ring_hom.mem_ker, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom] },
      { rw [mv_polynomial.aeval_map_algebra_map, ← aeval_unique],
        have := ideal.subset_span hx,
        rwa hs at this },
      { rw [map_sub, mv_polynomial.aeval_map_algebra_map, ← aeval_unique,
          aeval_C, ht', subtype.coe_mk, sub_self] } },
    apply leI.antisymm,
    intros x hx,
    rw [ring_hom.mem_ker, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom] at hx,
    let s₀ := _, change x ∈ ideal.span s₀,
    have : x ∈ (map (algebra_map R A) : _ →+* AX).srange.to_add_submonoid ⊔
      (ideal.span s₀).to_add_submonoid,
    { have : x ∈ (⊤ : subalgebra R AX) := trivial,
      rw ← ht'' at this,
      apply adjoin_induction this,
      { rintros _ (⟨x, hx, rfl⟩|⟨i, rfl⟩),
        { rw [algebra_map_eq, ← sub_add_cancel (C x) (map (algebra_map R A) (t' ⟨x, hx⟩)),
          add_comm],
          apply add_submonoid.add_mem_sup,
          { exact set.mem_range_self _ },
          { apply ideal.subset_span,
            apply set.mem_union_right,
            exact set.mem_range_self ⟨x, hx⟩ } },
        { apply add_submonoid.mem_sup_left,
          exact ⟨X i, map_X _ _⟩ } },
      { intro r, apply add_submonoid.mem_sup_left, exact ⟨C r, map_C _ _⟩ },
      { intros _ _ h₁ h₂, exact add_mem h₁ h₂ },
      { intros x₁ x₂ h₁ h₂,
        obtain ⟨_, ⟨p₁, rfl⟩, q₁, hq₁, rfl⟩ := add_submonoid.mem_sup.mp h₁,
        obtain ⟨_, ⟨p₂, rfl⟩, q₂, hq₂, rfl⟩ := add_submonoid.mem_sup.mp h₂,
        rw [add_mul, mul_add, add_assoc, ← map_mul],
        apply add_submonoid.add_mem_sup,
        { exact set.mem_range_self _ },
        { refine add_mem (ideal.mul_mem_left _ _ hq₂) (ideal.mul_mem_right _ _ hq₁) } } },
    obtain ⟨_, ⟨p, rfl⟩, q, hq, rfl⟩ := add_submonoid.mem_sup.mp this,
    rw [map_add, aeval_map_algebra_map, ← aeval_unique, (show aeval (f ∘ X) q = 0, from leI hq),
      add_zero] at hx,
    suffices : ideal.span (s : set RX) ≤ (ideal.span s₀).comap (map $ algebra_map R A),
    { refine add_mem _ hq, rw hs at this, exact this hx },
    rw ideal.span_le,
    intros x hx,
    apply ideal.subset_span,
    apply set.mem_union_left,
    exact set.mem_image_of_mem _ hx }
end

/-- This is used to prove the strictly stronger `ker_fg_of_surjective`. Use it instead. -/
-- TODO: extract out helper lemmas and tidy proof.
lemma ker_fg_of_mv_polynomial {n : ℕ} (f : mv_polynomial (fin n) R →ₐ[R] A)
  (hf : function.surjective f) (hfp : finite_presentation R A) : f.to_ring_hom.ker.fg :=
begin
  classical,
  obtain ⟨m, f', hf', s, hs⟩ := hfp,
  let RXn := mv_polynomial (fin n) R, let RXm := mv_polynomial (fin m) R,
  have := λ (i : fin n), hf' (f $ X i),
  choose g hg,
  have := λ (i : fin m), hf (f' $ X i),
  choose h hh,
  let aeval_h : RXm →ₐ[R] RXn := aeval h,
  let g' : fin n → RXn := λ i, X i - aeval_h (g i),
  refine ⟨finset.univ.image g' ∪ s.image aeval_h, _⟩,
  simp only [finset.coe_image, finset.coe_union, finset.coe_univ, set.image_univ],
  have hh' : ∀ x, f (aeval_h x) = f' x,
  { intro x, rw [← f.coe_to_ring_hom, map_aeval], simp_rw [alg_hom.coe_to_ring_hom, hh],
    rw [alg_hom.comp_algebra_map, ← aeval_eq_eval₂_hom, ← aeval_unique] },
  let s' := set.range g' ∪ aeval_h '' s,
  have leI : ideal.span s' ≤ f.to_ring_hom.ker,
  { rw ideal.span_le,
    rintros _ (⟨i, rfl⟩|⟨x, hx, rfl⟩),
    { change f (g' i) = 0, rw [map_sub, ← hg, hh', sub_self], },
    { change f (aeval_h x) = 0,
      rw hh',
      change x ∈ f'.to_ring_hom.ker,
      rw ← hs,
      exact ideal.subset_span hx } },
  apply leI.antisymm,
  intros x hx,
  have : x ∈ aeval_h.range.to_add_submonoid ⊔ (ideal.span s').to_add_submonoid,
  { have : x ∈ adjoin R (set.range X : set RXn) := by { rw [adjoin_range_X], trivial },
    apply adjoin_induction this,
    { rintros _ ⟨i, rfl⟩,
      rw [← sub_add_cancel (X i) (aeval h (g i)), add_comm],
      apply add_submonoid.add_mem_sup,
    { exact set.mem_range_self _ },
    { apply submodule.subset_span,
      apply set.mem_union_left,
      exact set.mem_range_self _ } },
    { intros r, apply add_submonoid.mem_sup_left, exact ⟨C r, aeval_C _ _⟩ },
    { intros _ _ h₁ h₂, exact add_mem h₁ h₂ },
    { intros p₁ p₂ h₁ h₂,
      obtain ⟨_, ⟨x₁, rfl⟩, y₁, hy₁, rfl⟩ := add_submonoid.mem_sup.mp h₁,
      obtain ⟨_, ⟨x₂, rfl⟩, y₂, hy₂, rfl⟩ := add_submonoid.mem_sup.mp h₂,
      rw [mul_add, add_mul, add_assoc, ← map_mul],
      apply add_submonoid.add_mem_sup,
    { exact set.mem_range_self _ },
    { exact add_mem (ideal.mul_mem_right _ _ hy₁) (ideal.mul_mem_left _ _ hy₂) } } },
  obtain ⟨_, ⟨x, rfl⟩, y, hy, rfl⟩ := add_submonoid.mem_sup.mp this,
  refine add_mem _ hy,
  simp only [ring_hom.mem_ker, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom, map_add,
    (show f y = 0, from leI hy), add_zero, hh'] at hx,
  suffices : ideal.span (s : set RXm) ≤ (ideal.span s').comap aeval_h,
  { apply this, rwa hs },
  rw ideal.span_le,
  intros x hx,
  apply submodule.subset_span,
  apply set.mem_union_right,
  exact set.mem_image_of_mem _ hx
end

/-- If `f : A →ₐ[R] B` is a sujection between finitely-presented `R`-algebras, then the kernel of
`f` is finitely generated. -/
lemma ker_fg_of_surjective (f : A →ₐ[R] B) (hf : function.surjective f)
  (hRA : finite_presentation R A) (hRB : finite_presentation R B) : f.to_ring_hom.ker.fg :=
begin
  obtain ⟨n, g, hg, hg'⟩ := hRA,
  convert (ker_fg_of_mv_polynomial (f.comp g) (hf.comp hg) hRB).map g.to_ring_hom,
  simp_rw [ring_hom.ker_eq_comap_bot, alg_hom.to_ring_hom_eq_coe, alg_hom.comp_to_ring_hom],
  rw [← ideal.comap_comap, ideal.map_comap_of_surjective (g : mv_polynomial (fin n) R →+* A) hg],
end

end finite_presentation

end algebra

end module_and_algebra

namespace ring_hom
variables {A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C]

/-- A ring morphism `A →+* B` is of `finite_presentation` if `B` is finitely presented as
`A`-algebra. -/
def finite_presentation (f : A →+* B) : Prop := @algebra.finite_presentation A B _ _ f.to_algebra

namespace finite_type

lemma of_finite_presentation {f : A →+* B} (hf : f.finite_presentation) : f.finite_type :=
@algebra.finite_type.of_finite_presentation A B _ _ f.to_algebra hf

end finite_type

namespace finite_presentation

variables (A)

lemma id : finite_presentation (ring_hom.id A) := algebra.finite_presentation.self A

variables {A}

lemma comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.finite_presentation) (hg : surjective g)
  (hker : g.ker.fg) :  (g.comp f).finite_presentation :=
@algebra.finite_presentation.of_surjective A B C _ _ f.to_algebra _ (g.comp f).to_algebra
{ to_fun := g, commutes' := λ a, rfl, .. g } hg hker hf

lemma of_surjective (f : A →+* B) (hf : surjective f) (hker : f.ker.fg) : f.finite_presentation :=
by { rw ← f.comp_id, exact (id A).comp_surjective hf hker}

lemma of_finite_type [is_noetherian_ring A] {f : A →+* B} : f.finite_type ↔ f.finite_presentation :=
@algebra.finite_presentation.of_finite_type A B _ _ f.to_algebra _

lemma comp {g : B →+* C} {f : A →+* B} (hg : g.finite_presentation) (hf : f.finite_presentation) :
  (g.comp f).finite_presentation :=
@algebra.finite_presentation.trans A B C _ _ f.to_algebra _ (g.comp f).to_algebra g.to_algebra
{ smul_assoc := λ a b c, begin
    simp only [algebra.smul_def, ring_hom.map_mul, mul_assoc],
    refl
  end }
hf hg

lemma of_comp_finite_type (f : A →+* B) {g : B →+* C} (hg : (g.comp f).finite_presentation)
  (hf : f.finite_type) : g.finite_presentation :=
@@algebra.finite_presentation.of_restrict_scalars_finite_presentation _ _ f.to_algebra _
  (g.comp f).to_algebra g.to_algebra
  (@@is_scalar_tower.of_algebra_map_eq' _ _ _ f.to_algebra g.to_algebra (g.comp f).to_algebra rfl)
  hg hf

end finite_presentation

end ring_hom

namespace alg_hom

variables {R A B C : Type*} [comm_ring R]
variables [comm_ring A] [comm_ring B] [comm_ring C]
variables [algebra R A] [algebra R B] [algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is of `finite_presentation` if it is of finite presentation as
ring morphism. In other words, if `B` is finitely presented as `A`-algebra. -/
def finite_presentation (f : A →ₐ[R] B) : Prop := f.to_ring_hom.finite_presentation

namespace finite_type

variables {R A}

lemma of_finite_presentation {f : A →ₐ[R] B} (hf : f.finite_presentation) : f.finite_type :=
ring_hom.finite_type.of_finite_presentation hf

end finite_type

namespace finite_presentation

variables (R A)

lemma id : finite_presentation (alg_hom.id R A) := ring_hom.finite_presentation.id A

variables {R A}

lemma comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.finite_presentation)
  (hf : f.finite_presentation) : (g.comp f).finite_presentation :=
ring_hom.finite_presentation.comp hg hf

lemma comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.finite_presentation)
  (hg : surjective g) (hker : g.to_ring_hom.ker.fg) : (g.comp f).finite_presentation :=
ring_hom.finite_presentation.comp_surjective hf hg hker

lemma of_surjective (f : A →ₐ[R] B) (hf : surjective f) (hker : f.to_ring_hom.ker.fg) :
  f.finite_presentation :=
ring_hom.finite_presentation.of_surjective f hf hker

lemma of_finite_type [is_noetherian_ring A] {f : A →ₐ[R] B} :
  f.finite_type ↔ f.finite_presentation :=
ring_hom.finite_presentation.of_finite_type

lemma of_comp_finite_type (f : A →ₐ[R] B) {g : B →ₐ[R] C} (h : (g.comp f).finite_presentation)
  (h' : f.finite_type) : g.finite_presentation :=
h.of_comp_finite_type _ h'

end finite_presentation

end alg_hom
