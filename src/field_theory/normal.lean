/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import field_theory.minpoly
import field_theory.splitting_field
import field_theory.tower
import ring_theory.power_basis

/-!
# Normal field extensions

In this file we define normal field extensions and prove that for a finite extension, being normal
is the same as being a splitting field (`normal.of_is_splitting_field` and
`normal.exists_is_splitting_field`).

## Main Definitions

- `normal F K` where `K` is a field extension of `F`.
-/

noncomputable theory
open_locale classical
open polynomial is_scalar_tower

variables (F K : Type*) [field F] [field K] [algebra F K]

--TODO(Commelin): refactor normal to extend `is_algebraic`??

/-- Typeclass for normal field extension: `K` is a normal extension of `F` iff the minimal
polynomial of every element `x` in `K` splits in `K`, i.e. every conjugate of `x` is in `K`. -/
@[class] def normal : Prop :=
∀ x : K, is_integral F x ∧ splits (algebra_map F K) (minpoly F x)

instance normal_self : normal F F :=
λ x, ⟨is_integral_algebra_map, by { rw minpoly.eq_X_sub_C', exact splits_X_sub_C _ }⟩

variables {K}

theorem normal.is_integral [h : normal F K] (x : K) : is_integral F x := (h x).1

theorem normal.splits [h : normal F K] (x : K) : splits (algebra_map F K) (minpoly F x) := (h x).2

variables (K)

theorem normal.exists_is_splitting_field [normal F K] [finite_dimensional F K] :
  ∃ p : polynomial F, is_splitting_field F K p :=
begin
  obtain ⟨s, hs⟩ := finite_dimensional.exists_is_basis_finset F K,
  refine ⟨s.prod $ λ x, minpoly F x,
    splits_prod _ $ λ x hx, normal.splits F x,
    subalgebra.to_submodule_injective _⟩,
  rw [algebra.coe_top, eq_top_iff, ← hs.2, submodule.span_le, set.range_subset_iff],
  refine λ x, algebra.subset_adjoin (multiset.mem_to_finset.mpr $
    (mem_roots $ mt (map_eq_zero $ algebra_map F K).1 $
    finset.prod_ne_zero_iff.2 $ λ x hx, _).2 _),
  { exact minpoly.ne_zero (normal.is_integral F x) },
  rw [is_root.def, eval_map, ← aeval_def, alg_hom.map_prod],
  exact finset.prod_eq_zero x.2 (minpoly.aeval _ _)
end

section normal_tower

variables (E : Type*) [field E] [algebra F E] [algebra K E] [is_scalar_tower F K E]

lemma normal.tower_top_of_normal [h : normal F E] : normal K E :=
begin
  intros x,
  cases h x with hx hhx,
  rw algebra_map_eq F K E at hhx,
  exact ⟨is_integral_of_is_scalar_tower x hx, polynomial.splits_of_splits_of_dvd (algebra_map K E)
    (polynomial.map_ne_zero (minpoly.ne_zero hx))
    ((polynomial.splits_map_iff (algebra_map F K) (algebra_map K E)).mpr hhx)
    (minpoly.dvd_map_of_is_scalar_tower F K x)⟩,
end

variables {F} {E} {E' : Type*} [field E'] [algebra F E']

lemma normal.of_alg_equiv [h : normal F E] (f : E ≃ₐ[F] E') : normal F E' :=
begin
  intro x,
  cases h (f.symm x) with hx hhx,
  have H := is_integral_alg_hom f.to_alg_hom hx,
  rw [alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom, alg_equiv.apply_symm_apply] at H,
  use H,
  apply polynomial.splits_of_splits_of_dvd (algebra_map F E') (minpoly.ne_zero hx),
  { rw ← alg_hom.comp_algebra_map f.to_alg_hom,
    exact polynomial.splits_comp_of_splits (algebra_map F E) f.to_alg_hom.to_ring_hom hhx },
  { apply minpoly.dvd _ _,
    rw ← add_equiv.map_eq_zero_iff f.symm.to_add_equiv,
    exact eq.trans (polynomial.aeval_alg_hom_apply f.symm.to_alg_hom x
      (minpoly F (f.symm x))).symm (minpoly.aeval _ _) },
end

lemma alg_equiv.transfer_normal (f : E ≃ₐ[F] E') : normal F E ↔ normal F E' :=
⟨λ h, by exactI normal.of_alg_equiv f, λ h, by exactI normal.of_alg_equiv f.symm⟩

lemma normal.of_is_splitting_field {p : polynomial F} [hFEp : is_splitting_field F E p] :
  normal F E :=
begin
  by_cases hp : p = 0,
  { haveI : is_splitting_field F F p := by { rw hp, exact ⟨splits_zero _, subsingleton.elim _ _⟩ },
    exactI (alg_equiv.transfer_normal ((is_splitting_field.alg_equiv F p).trans
      (is_splitting_field.alg_equiv E p).symm)).mp (normal_self F) },
  intro x,
  haveI hFE : finite_dimensional F E := is_splitting_field.finite_dimensional E p,
  have Hx : is_integral F x := is_integral_of_noetherian hFE x,
  refine ⟨Hx, or.inr _⟩,
  rintros q q_irred ⟨r, hr⟩,
  let D := adjoin_root q,
  let pbED := adjoin_root.power_basis q_irred.ne_zero,
  haveI : finite_dimensional E D := power_basis.finite_dimensional pbED,
  have findimED : finite_dimensional.findim E D = q.nat_degree := power_basis.findim pbED,
  letI : algebra F D := ring_hom.to_algebra ((algebra_map E D).comp (algebra_map F E)),
  haveI : is_scalar_tower F E D := of_algebra_map_eq (λ _, rfl),
  haveI : finite_dimensional F D := finite_dimensional.trans F E D,
  suffices : nonempty (D →ₐ[F] E),
  { cases this with ϕ,
    rw [←with_bot.coe_one, degree_eq_iff_nat_degree_eq q_irred.ne_zero, ←findimED],
    have nat_lemma : ∀ a b c : ℕ, a * b = c → c ≤ a → 0 < c → b = 1,
    { intros a b c h1 h2 h3, nlinarith },
    exact nat_lemma _ _ _ (finite_dimensional.findim_mul_findim F E D)
      (linear_map.findim_le_findim_of_injective (show function.injective ϕ.to_linear_map,
        from ϕ.to_ring_hom.injective)) finite_dimensional.findim_pos, },
  let C := adjoin_root (minpoly F x),
  have Hx_irred := minpoly.irreducible Hx,
  letI : algebra C D := ring_hom.to_algebra (adjoin_root.lift
    (algebra_map F D) (adjoin_root.root q) (by rw [algebra_map_eq F E D, ←eval₂_map, hr,
      adjoin_root.algebra_map_eq, eval₂_mul, adjoin_root.eval₂_root, zero_mul])),
  letI : algebra C E := ring_hom.to_algebra (adjoin_root.lift
    (algebra_map F E) x (minpoly.aeval F x)),
  haveI : is_scalar_tower F C D := of_algebra_map_eq (λ x, adjoin_root.lift_of.symm),
  haveI : is_scalar_tower F C E := of_algebra_map_eq (λ x, adjoin_root.lift_of.symm),
  suffices : nonempty (D →ₐ[C] E),
  { exact nonempty.map (restrict_base F) this },
  let S : set D := ((p.map (algebra_map F E)).roots.map (algebra_map E D)).to_finset,
  suffices : ⊤ ≤ intermediate_field.adjoin C S,
  { refine intermediate_field.alg_hom_mk_adjoin_splits' (top_le_iff.mp this) (λ y hy, _),
    rcases multiset.mem_map.mp (multiset.mem_to_finset.mp hy) with ⟨z, hz1, hz2⟩,
    have Hz : is_integral F z := is_integral_of_noetherian hFE z,
    use (show is_integral C y, from is_integral_of_noetherian (finite_dimensional.right F C D) y),
    apply splits_of_splits_of_dvd (algebra_map C E) (map_ne_zero (minpoly.ne_zero Hz)),
    { rw [splits_map_iff, ←algebra_map_eq F C E],
      exact splits_of_splits_of_dvd _ hp hFEp.splits (minpoly.dvd F z
        (eq.trans (eval₂_eq_eval_map _) ((mem_roots (map_ne_zero hp)).mp hz1))) },
    { apply minpoly.dvd,
      rw [←hz2, aeval_def, eval₂_map, ←algebra_map_eq F C D, algebra_map_eq F E D, ←hom_eval₂,
          ←aeval_def, minpoly.aeval F z, ring_hom.map_zero] } },
  rw [←intermediate_field.to_subalgebra_le_to_subalgebra, intermediate_field.top_to_subalgebra],
  apply ge_trans (intermediate_field.algebra_adjoin_le_adjoin C S),
  suffices : (algebra.adjoin C S).res F = (algebra.adjoin E {adjoin_root.root q}).res F,
  { rw [adjoin_root.adjoin_root_eq_top, subalgebra.res_top, ←@subalgebra.res_top F C] at this,
    exact top_le_iff.mpr (subalgebra.res_inj F this) },
  dsimp only [S],
  rw [←finset.image_to_finset, finset.coe_image],
  apply eq.trans (algebra.adjoin_res_eq_adjoin_res F E C D
    hFEp.adjoin_roots adjoin_root.adjoin_root_eq_top),
  rw [set.image_singleton, ring_hom.algebra_map_to_algebra, adjoin_root.lift_root]
end

end normal_tower

variables {F} {K} (ϕ ψ : K →ₐ[F] K) (χ ω : K ≃ₐ[F] K)
  (E : Type*) [field E] [algebra F E] [algebra E K] [is_scalar_tower F E K]

/-- Restrict algebra homomorphism to image of normal subfield -/
def alg_hom.restrict_normal_aux [h : normal F E] :
  (to_alg_hom F E K).range →ₐ[F] (to_alg_hom F E K).range :=
{ to_fun := λ x, ⟨ϕ x, by
  { suffices : (to_alg_hom F E K).range.map ϕ ≤ _,
    { exact this ⟨x, subtype.mem x, rfl⟩ },
    rintros x ⟨y, ⟨z, -, hy⟩, hx⟩,
    rw [←hx, ←hy],
    exact minpoly.mem_range_of_degree_eq_one E _ (or.resolve_left (h z).2 (minpoly.ne_zero (h z).1)
      (minpoly.irreducible (is_integral_of_is_scalar_tower _
        (is_integral_alg_hom ϕ (is_integral_alg_hom _ (h z).1))))
      (minpoly.dvd E _ (by rw [aeval_map, aeval_alg_hom, aeval_alg_hom, alg_hom.comp_apply,
        alg_hom.comp_apply, minpoly.aeval, alg_hom.map_zero, alg_hom.map_zero]))) }⟩,
  map_zero' := subtype.ext ϕ.map_zero,
  map_one' := subtype.ext ϕ.map_one,
  map_add' := λ x y, subtype.ext (ϕ.map_add x y),
  map_mul' := λ x y, subtype.ext (ϕ.map_mul x y),
  commutes' := λ x, subtype.ext (ϕ.commutes x) }

/-- Restrict algebra homomorphism to normal subfield -/
def alg_hom.restrict_normal [normal F E] : E →ₐ[F] E :=
((alg_hom.alg_equiv.of_injective_field (is_scalar_tower.to_alg_hom F E K)).symm.to_alg_hom.comp
  (ϕ.restrict_normal_aux E)).comp
    (alg_hom.alg_equiv.of_injective_field (is_scalar_tower.to_alg_hom F E K)).to_alg_hom

lemma alg_hom.restrict_normal_commutes [normal F E] (x : E) :
  algebra_map E K (ϕ.restrict_normal E x) = ϕ (algebra_map E K x) :=
subtype.ext_iff.mp (alg_equiv.apply_symm_apply (alg_hom.alg_equiv.of_injective_field
  (is_scalar_tower.to_alg_hom F E K)) (ϕ.restrict_normal_aux E
    ⟨is_scalar_tower.to_alg_hom F E K x, ⟨x, ⟨subsemiring.mem_top x, rfl⟩⟩⟩))

lemma alg_hom.restrict_normal_comp [normal F E] :
  (ϕ.restrict_normal E).comp (ψ.restrict_normal E) = (ϕ.comp ψ).restrict_normal E :=
alg_hom.ext (λ _, (algebra_map E K).injective
  (by simp only [alg_hom.comp_apply, alg_hom.restrict_normal_commutes]))

/-- Restrict algebra isomorphism to a normal subfield -/
def alg_equiv.restrict_normal [h : normal F E] : E ≃ₐ[F] E :=
alg_equiv.of_alg_hom (χ.to_alg_hom.restrict_normal E)
  (χ.symm.to_alg_hom.restrict_normal E)
  (alg_hom.ext $ λ _, (algebra_map E K).injective
    (by simp only [alg_hom.comp_apply, alg_hom.restrict_normal_commutes,
      alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom, alg_hom.id_apply, χ.apply_symm_apply]))
  (alg_hom.ext $ λ _, (algebra_map E K).injective
    (by simp only [alg_hom.comp_apply, alg_hom.restrict_normal_commutes,
      alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom, alg_hom.id_apply, χ.symm_apply_apply]))

lemma alg_equiv.restrict_normal_commutes [normal F E] (x : E) :
  algebra_map E K (χ.restrict_normal E x) = χ (algebra_map E K x) :=
χ.to_alg_hom.restrict_normal_commutes E x

lemma alg_equiv.restrict_normal_trans [normal F E] :
  (χ.trans ω).restrict_normal E = (χ.restrict_normal E).trans (ω.restrict_normal E) :=
alg_equiv.ext (λ _, (algebra_map E K).injective
(by simp only [alg_equiv.trans_apply, alg_equiv.restrict_normal_commutes]))

/-- Restriction to an normal subfield as a group homomorphism -/
def alg_equiv.restrict_normal_hom [normal F E] : (K ≃ₐ[F] K) →* (E ≃ₐ[F] E) :=
monoid_hom.mk' (λ χ, χ.restrict_normal E) (λ ω χ, (χ.restrict_normal_trans ω E))
