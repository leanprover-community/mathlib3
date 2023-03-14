/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Thomas Browning, Patrick Lutz
-/

import field_theory.adjoin
import field_theory.tower
import group_theory.solvable
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

open_locale big_operators
open_locale classical polynomial

open polynomial is_scalar_tower

variables (F K : Type*) [field F] [field K] [algebra F K]

/-- Typeclass for normal field extension: `K` is a normal extension of `F` iff the minimal
polynomial of every element `x` in `K` splits in `K`, i.e. every conjugate of `x` is in `K`. -/
class normal : Prop :=
(is_algebraic' : algebra.is_algebraic F K)
(splits' (x : K) : splits (algebra_map F K) (minpoly F x))

variables {F K}

theorem normal.is_algebraic (h : normal F K) (x : K) : is_algebraic F x := normal.is_algebraic' x

theorem normal.is_integral (h : normal F K) (x : K) : is_integral F x :=
is_algebraic_iff_is_integral.mp (h.is_algebraic x)

theorem normal.splits (h : normal F K) (x : K) :
  splits (algebra_map F K) (minpoly F x) := normal.splits' x

theorem normal_iff : normal F K ↔
  ∀ x : K, is_integral F x ∧ splits (algebra_map F K) (minpoly F x) :=
⟨λ h x, ⟨h.is_integral x, h.splits x⟩, λ h, ⟨λ x, (h x).1.is_algebraic F, λ x, (h x).2⟩⟩

theorem normal.out : normal F K →
  ∀ x : K, is_integral F x ∧ splits (algebra_map F K) (minpoly F x) := normal_iff.1

variables (F K)

instance normal_self : normal F F :=
⟨λ x, is_integral_algebra_map.is_algebraic F, λ x, (minpoly.eq_X_sub_C' x).symm ▸ splits_X_sub_C _⟩

variables {K}

variables (K)

theorem normal.exists_is_splitting_field [h : normal F K] [finite_dimensional F K] :
  ∃ p : F[X], is_splitting_field F K p :=
begin
  let s := basis.of_vector_space F K,
  refine ⟨∏ x, minpoly F (s x),
    splits_prod _ $ λ x hx, h.splits (s x),
    subalgebra.to_submodule.injective _⟩,
  rw [algebra.top_to_submodule, eq_top_iff, ← s.span_eq, submodule.span_le, set.range_subset_iff],
  refine λ x, algebra.subset_adjoin (multiset.mem_to_finset.mpr $
    (mem_roots $ mt (polynomial.map_eq_zero $ algebra_map F K).1 $
    finset.prod_ne_zero_iff.2 $ λ x hx, _).2 _),
  { exact minpoly.ne_zero (h.is_integral (s x)) },
  rw [is_root.def, eval_map, ← aeval_def, alg_hom.map_prod],
  exact finset.prod_eq_zero (finset.mem_univ _) (minpoly.aeval _ _)
end

section normal_tower

variables (E : Type*) [field E] [algebra F E] [algebra K E] [is_scalar_tower F K E]

lemma normal.tower_top_of_normal [h : normal F E] : normal K E :=
normal_iff.2 $ λ x, begin
  cases h.out x with hx hhx,
  rw algebra_map_eq F K E at hhx,
  exact ⟨is_integral_of_is_scalar_tower hx, polynomial.splits_of_splits_of_dvd (algebra_map K E)
    (polynomial.map_ne_zero (minpoly.ne_zero hx))
    ((polynomial.splits_map_iff (algebra_map F K) (algebra_map K E)).mpr hhx)
    (minpoly.dvd_map_of_is_scalar_tower F K x)⟩,
end

lemma alg_hom.normal_bijective [h : normal F E] (ϕ : E →ₐ[F] K) : function.bijective ϕ :=
⟨ϕ.to_ring_hom.injective, λ x, by
{ letI : algebra E K := ϕ.to_ring_hom.to_algebra,
  obtain ⟨h1, h2⟩ := h.out (algebra_map K E x),
  cases minpoly.mem_range_of_degree_eq_one E x (h2.def.resolve_left (minpoly.ne_zero h1)
    (minpoly.irreducible (is_integral_of_is_scalar_tower
      ((is_integral_algebra_map_iff (algebra_map K E).injective).mp h1)))
    (minpoly.dvd E x ((algebra_map K E).injective (by
    { rw [ring_hom.map_zero, aeval_map_algebra_map, ← aeval_algebra_map_apply],
      exact minpoly.aeval F (algebra_map K E x) })))) with y hy,
  exact ⟨y, hy⟩ }⟩

variables {F} {E} {E' : Type*} [field E'] [algebra F E']

lemma normal.of_alg_equiv [h : normal F E] (f : E ≃ₐ[F] E') : normal F E' :=
normal_iff.2 $ λ x, begin
  cases h.out (f.symm x) with hx hhx,
  have H := map_is_integral f.to_alg_hom hx,
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

lemma normal.of_is_splitting_field (p : F[X]) [hFEp : is_splitting_field F E p] :
  normal F E :=
begin
  by_cases hp : p = 0,
  { haveI : is_splitting_field F F p, { rw hp, exact ⟨splits_zero _, subsingleton.elim _ _⟩ },
    exactI (alg_equiv.transfer_normal ((is_splitting_field.alg_equiv F p).trans
      (is_splitting_field.alg_equiv E p).symm)).mp (normal_self F) },
  refine normal_iff.2 (λ x, _),
  haveI hFE : finite_dimensional F E := is_splitting_field.finite_dimensional E p,
  have Hx : is_integral F x := is_integral_of_noetherian (is_noetherian.iff_fg.2 hFE) x,
  refine ⟨Hx, or.inr _⟩,
  rintros q q_irred ⟨r, hr⟩,
  let D := adjoin_root q,
  haveI := fact.mk q_irred,
  let pbED := adjoin_root.power_basis q_irred.ne_zero,
  haveI : finite_dimensional E D := power_basis.finite_dimensional pbED,
  have finrankED : finite_dimensional.finrank E D = q.nat_degree := power_basis.finrank pbED,
  letI : algebra F D := ring_hom.to_algebra ((algebra_map E D).comp (algebra_map F E)),
  haveI : is_scalar_tower F E D := of_algebra_map_eq (λ _, rfl),
  haveI : finite_dimensional F D := finite_dimensional.trans F E D,
  suffices : nonempty (D →ₐ[F] E),
  { cases this with ϕ,
    rw [←with_bot.coe_one, degree_eq_iff_nat_degree_eq q_irred.ne_zero, ←finrankED],
    have nat_lemma : ∀ a b c : ℕ, a * b = c → c ≤ a → 0 < c → b = 1,
    { intros a b c h1 h2 h3, nlinarith },
    exact nat_lemma _ _ _ (finite_dimensional.finrank_mul_finrank F E D)
      (linear_map.finrank_le_finrank_of_injective (show function.injective ϕ.to_linear_map,
        from ϕ.to_ring_hom.injective)) finite_dimensional.finrank_pos, },
  let C := adjoin_root (minpoly F x),
  haveI Hx_irred := fact.mk (minpoly.irreducible Hx),
  letI : algebra C D := ring_hom.to_algebra (adjoin_root.lift
    (algebra_map F D) (adjoin_root.root q) (by rw [algebra_map_eq F E D, ←eval₂_map, hr,
      adjoin_root.algebra_map_eq, eval₂_mul, adjoin_root.eval₂_root, zero_mul])),
  letI : algebra C E := ring_hom.to_algebra (adjoin_root.lift
    (algebra_map F E) x (minpoly.aeval F x)),
  haveI : is_scalar_tower F C D := of_algebra_map_eq (λ x, (adjoin_root.lift_of _).symm),
  haveI : is_scalar_tower F C E := of_algebra_map_eq (λ x, (adjoin_root.lift_of _).symm),
  suffices : nonempty (D →ₐ[C] E),
  { exact nonempty.map (alg_hom.restrict_scalars F) this },
  let S : set D := ((p.map (algebra_map F E)).roots.map (algebra_map E D)).to_finset,
  suffices : ⊤ ≤ intermediate_field.adjoin C S,
  { refine intermediate_field.alg_hom_mk_adjoin_splits' (top_le_iff.mp this) (λ y hy, _),
    rcases multiset.mem_map.mp (multiset.mem_to_finset.mp hy) with ⟨z, hz1, hz2⟩,
    have Hz : is_integral F z := is_integral_of_noetherian (is_noetherian.iff_fg.2 hFE) z,
    use (show is_integral C y, from is_integral_of_noetherian
      (is_noetherian.iff_fg.2 (finite_dimensional.right F C D)) y),
    apply splits_of_splits_of_dvd (algebra_map C E) (map_ne_zero (minpoly.ne_zero Hz)),
    { rw [splits_map_iff, ←algebra_map_eq F C E],
      exact splits_of_splits_of_dvd _ hp hFEp.splits (minpoly.dvd F z
        (eq.trans (eval₂_eq_eval_map _) ((mem_roots (map_ne_zero hp)).mp hz1))) },
    { apply minpoly.dvd,
      rw [←hz2, aeval_def, eval₂_map, ←algebra_map_eq F C D, algebra_map_eq F E D, ←hom_eval₂,
          ←aeval_def, minpoly.aeval F z, ring_hom.map_zero] } },
  rw [←intermediate_field.to_subalgebra_le_to_subalgebra, intermediate_field.top_to_subalgebra],
  apply ge_trans (intermediate_field.algebra_adjoin_le_adjoin C S),
  suffices : (algebra.adjoin C S).restrict_scalars F
           = (algebra.adjoin E {adjoin_root.root q}).restrict_scalars F,
  { rw [adjoin_root.adjoin_root_eq_top, subalgebra.restrict_scalars_top,
      ←@subalgebra.restrict_scalars_top F C] at this,
    exact top_le_iff.mpr (subalgebra.restrict_scalars_injective F this) },
  dsimp only [S],
  rw [←finset.image_to_finset, finset.coe_image],
  apply eq.trans (algebra.adjoin_res_eq_adjoin_res F E C D
    hFEp.adjoin_roots adjoin_root.adjoin_root_eq_top),
  rw [set.image_singleton, ring_hom.algebra_map_to_algebra, adjoin_root.lift_root]
end

instance (p : F[X]) : normal F p.splitting_field := normal.of_is_splitting_field p

end normal_tower

namespace intermediate_field

/-- A compositum of normal extensions is normal -/
instance normal_supr {ι : Type*} (t : ι → intermediate_field F K) [h : ∀ i, normal F (t i)] :
  normal F (⨆ i, t i : intermediate_field F K) :=
begin
  refine ⟨is_algebraic_supr (λ i, (h i).1), λ x, _⟩,
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr'' (λ i, (h i).1) x.2,
  let E : intermediate_field F K := ⨆ i ∈ s, adjoin F ((minpoly F (i.2 : _)).root_set K),
  have hF : normal F E,
  { apply normal.of_is_splitting_field (∏ i in s, minpoly F i.2),
    refine is_splitting_field_supr _ (λ i hi, adjoin_root_set_is_splitting_field _),
    { exact finset.prod_ne_zero_iff.mpr (λ i hi, minpoly.ne_zero ((h i.1).is_integral i.2)) },
    { exact polynomial.splits_comp_of_splits _ (algebra_map (t i.1) K) ((h i.1).splits i.2) } },
  have hE : E ≤ ⨆ i, t i,
  { refine supr_le (λ i, supr_le (λ hi, le_supr_of_le i.1 _)),
    rw [adjoin_le_iff, ←image_root_set ((h i.1).splits i.2) (t i.1).val],
    exact λ _ ⟨a, _, h⟩, h ▸ a.2 },
  have := hF.splits ⟨x, hx⟩,
  rw [minpoly_eq, subtype.coe_mk, ←minpoly_eq] at this,
  exact polynomial.splits_comp_of_splits _ (inclusion hE).to_ring_hom this,
end

variables {F K} {L : Type*} [field L] [algebra F L] [algebra K L] [is_scalar_tower F K L]

@[simp] lemma restrict_scalars_normal {E : intermediate_field K L} :
  normal F (E.restrict_scalars F) ↔ normal F E :=
iff.rfl

end intermediate_field

variables {F} {K} {K₁ K₂ K₃:Type*} [field K₁] [field K₂] [field K₃]
 [algebra F K₁] [algebra F K₂] [algebra F K₃]
 (ϕ : K₁ →ₐ[F] K₂) (χ : K₁ ≃ₐ[F] K₂) (ψ : K₂ →ₐ[F] K₃) (ω : K₂ ≃ₐ[F] K₃)


section restrict

variables (E : Type*) [field E] [algebra F E] [algebra E K₁] [algebra E K₂] [algebra E K₃]
[is_scalar_tower F E K₁] [is_scalar_tower F E K₂] [is_scalar_tower F E K₃]

/-- Restrict algebra homomorphism to image of normal subfield -/
def alg_hom.restrict_normal_aux [h : normal F E] :
  (to_alg_hom F E K₁).range →ₐ[F] (to_alg_hom F E K₂).range :=
{ to_fun := λ x, ⟨ϕ x, by
  { suffices : (to_alg_hom F E K₁).range.map ϕ ≤ _,
    { exact this ⟨x, subtype.mem x, rfl⟩ },
    rintros x ⟨y, ⟨z, hy⟩, hx⟩,
    rw [←hx, ←hy],
    apply minpoly.mem_range_of_degree_eq_one E,
    refine or.resolve_left (h.splits z).def (minpoly.ne_zero (h.is_integral z))
      (minpoly.irreducible _) (minpoly.dvd E _ (by simp [aeval_alg_hom_apply])),
    simp only [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom],
    suffices : is_integral F _,
    { exact is_integral_of_is_scalar_tower this },
    exact map_is_integral ϕ (map_is_integral (to_alg_hom F E K₁) (h.is_integral z)) }⟩,
  map_zero' := subtype.ext ϕ.map_zero,
  map_one' := subtype.ext ϕ.map_one,
  map_add' := λ x y, subtype.ext (ϕ.map_add x y),
  map_mul' := λ x y, subtype.ext (ϕ.map_mul x y),
  commutes' := λ x, subtype.ext (ϕ.commutes x) }

/-- Restrict algebra homomorphism to normal subfield -/
def alg_hom.restrict_normal [normal F E] : E →ₐ[F] E :=
((alg_equiv.of_injective_field (is_scalar_tower.to_alg_hom F E K₂)).symm.to_alg_hom.comp
  (ϕ.restrict_normal_aux E)).comp
    (alg_equiv.of_injective_field (is_scalar_tower.to_alg_hom F E K₁)).to_alg_hom

/-- Restrict algebra homomorphism to normal subfield (`alg_equiv` version) -/
def alg_hom.restrict_normal' [normal F E] : E ≃ₐ[F] E :=
alg_equiv.of_bijective (alg_hom.restrict_normal ϕ E) (alg_hom.normal_bijective F E E _)

@[simp] lemma alg_hom.restrict_normal_commutes [normal F E] (x : E) :
  algebra_map E K₂ (ϕ.restrict_normal E x) = ϕ (algebra_map E K₁ x) :=
subtype.ext_iff.mp (alg_equiv.apply_symm_apply (alg_equiv.of_injective_field
  (is_scalar_tower.to_alg_hom F E K₂)) (ϕ.restrict_normal_aux E
    ⟨is_scalar_tower.to_alg_hom F E K₁ x, x, rfl⟩))

lemma alg_hom.restrict_normal_comp [normal F E] :
  (ψ.restrict_normal E).comp (ϕ.restrict_normal E) = (ψ.comp ϕ).restrict_normal E :=
alg_hom.ext (λ _, (algebra_map E K₃).injective
  (by simp only [alg_hom.comp_apply, alg_hom.restrict_normal_commutes]))

/-- Restrict algebra isomorphism to a normal subfield -/
def alg_equiv.restrict_normal [h : normal F E] : E ≃ₐ[F] E :=
alg_hom.restrict_normal' χ.to_alg_hom E

@[simp] lemma alg_equiv.restrict_normal_commutes [normal F E] (x : E) :
  algebra_map E K₂ (χ.restrict_normal E x) = χ (algebra_map E K₁ x) :=
χ.to_alg_hom.restrict_normal_commutes E x

lemma alg_equiv.restrict_normal_trans [normal F E] :
  (χ.trans ω).restrict_normal E = (χ.restrict_normal E).trans (ω.restrict_normal E) :=
alg_equiv.ext (λ _, (algebra_map E K₃).injective
(by simp only [alg_equiv.trans_apply, alg_equiv.restrict_normal_commutes]))


/-- Restriction to an normal subfield as a group homomorphism -/
def alg_equiv.restrict_normal_hom [normal F E] : (K₁ ≃ₐ[F] K₁) →* (E ≃ₐ[F] E) :=
monoid_hom.mk' (λ χ, χ.restrict_normal E) (λ ω χ, (χ.restrict_normal_trans ω E))

variables (F K₁ E)

/-- If `K₁/E/F` is a tower of fields with `E/F` normal then `normal.alg_hom_equiv_aut` is an
 equivalence. -/
@[simps] def normal.alg_hom_equiv_aut [normal F E] : (E →ₐ[F] K₁) ≃ (E ≃ₐ[F] E) :=
{ to_fun := λ σ, alg_hom.restrict_normal' σ E,
  inv_fun := λ σ, (is_scalar_tower.to_alg_hom F E K₁).comp σ.to_alg_hom,
  left_inv := λ σ, begin
    ext,
    simp[alg_hom.restrict_normal'],
  end,
  right_inv := λ σ, begin
    ext,
    simp only [alg_hom.restrict_normal', alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_of_bijective],
    apply no_zero_smul_divisors.algebra_map_injective E K₁,
    rw alg_hom.restrict_normal_commutes,
    simp,
  end }


end restrict

section lift

variables {F} {K₁ K₂} (E : Type*) [field E] [algebra F E] [algebra K₁ E] [algebra K₂ E]
[is_scalar_tower F K₁ E] [is_scalar_tower F K₂ E]

/-- If `E/Kᵢ/F` are towers of fields with `E/F` normal then we can lift
  an algebra homomorphism `ϕ : K₁ →ₐ[F] K₂` to `ϕ.lift_normal E : E →ₐ[F] E`. -/
noncomputable def alg_hom.lift_normal [h : normal F E] : E →ₐ[F] E :=
@alg_hom.restrict_scalars F K₁ E E _ _ _ _ _ _
  ((is_scalar_tower.to_alg_hom F K₂ E).comp ϕ).to_ring_hom.to_algebra _ _ _ _ $ nonempty.some $
  @intermediate_field.alg_hom_mk_adjoin_splits' _ _ _ _ _ _ _
  ((is_scalar_tower.to_alg_hom F K₂ E).comp ϕ).to_ring_hom.to_algebra _
  (intermediate_field.adjoin_univ _ _)
  (λ x hx, ⟨is_integral_of_is_scalar_tower (h.out x).1,
    splits_of_splits_of_dvd _ (map_ne_zero (minpoly.ne_zero (h.out x).1))
    (by { rw [splits_map_iff, ←is_scalar_tower.algebra_map_eq], exact (h.out x).2 })
    (minpoly.dvd_map_of_is_scalar_tower F K₁ x)⟩)

@[simp] lemma alg_hom.lift_normal_commutes [normal F E] (x : K₁) :
  ϕ.lift_normal E (algebra_map K₁ E x) = algebra_map K₂ E (ϕ x) :=
by apply @alg_hom.commutes K₁ E E _ _ _ _

@[simp] lemma alg_hom.restrict_lift_normal (ϕ : K₁ →ₐ[F] K₁) [normal F K₁] [normal F E] :
  (ϕ.lift_normal E).restrict_normal K₁ = ϕ :=
alg_hom.ext (λ x, (algebra_map K₁ E).injective
  (eq.trans (alg_hom.restrict_normal_commutes _ K₁ x) (ϕ.lift_normal_commutes E x)))

/-- If `E/Kᵢ/F` are towers of fields with `E/F` normal then we can lift
  an algebra isomorphism `ϕ : K₁ ≃ₐ[F] K₂` to `ϕ.lift_normal E : E ≃ₐ[F] E`. -/
noncomputable def alg_equiv.lift_normal [normal F E] : E ≃ₐ[F] E :=
alg_equiv.of_bijective (χ.to_alg_hom.lift_normal E) (alg_hom.normal_bijective F E E _)

@[simp] lemma alg_equiv.lift_normal_commutes [normal F E] (x : K₁) :
  χ.lift_normal E (algebra_map K₁ E x) = algebra_map K₂ E (χ x) :=
χ.to_alg_hom.lift_normal_commutes E x

@[simp] lemma alg_equiv.restrict_lift_normal (χ : K₁ ≃ₐ[F] K₁) [normal F K₁] [normal F E] :
  (χ.lift_normal E).restrict_normal K₁ = χ :=
alg_equiv.ext (λ x, (algebra_map K₁ E).injective
  (eq.trans (alg_equiv.restrict_normal_commutes _ K₁ x) (χ.lift_normal_commutes E x)))

lemma alg_equiv.restrict_normal_hom_surjective [normal F K₁] [normal F E] :
  function.surjective (alg_equiv.restrict_normal_hom K₁ : (E ≃ₐ[F] E) → (K₁ ≃ₐ[F] K₁)) :=
λ χ, ⟨χ.lift_normal E, χ.restrict_lift_normal E⟩

variables (F) (K₁) (E)

lemma is_solvable_of_is_scalar_tower [normal F K₁] [h1 : is_solvable (K₁ ≃ₐ[F] K₁)]
  [h2 : is_solvable (E ≃ₐ[K₁] E)] : is_solvable (E ≃ₐ[F] E) :=
begin
  let f : (E ≃ₐ[K₁] E) →* (E ≃ₐ[F] E) :=
  { to_fun := λ ϕ, alg_equiv.of_alg_hom (ϕ.to_alg_hom.restrict_scalars F)
      (ϕ.symm.to_alg_hom.restrict_scalars F)
      (alg_hom.ext (λ x, ϕ.apply_symm_apply x))
      (alg_hom.ext (λ x, ϕ.symm_apply_apply x)),
    map_one' := alg_equiv.ext (λ _, rfl),
    map_mul' := λ _ _, alg_equiv.ext (λ _, rfl) },
  refine solvable_of_ker_le_range f (alg_equiv.restrict_normal_hom K₁)
    (λ ϕ hϕ, ⟨{commutes' := λ x, _, .. ϕ}, alg_equiv.ext (λ _, rfl)⟩),
  exact (eq.trans (ϕ.restrict_normal_commutes K₁ x).symm (congr_arg _ (alg_equiv.ext_iff.mp hϕ x))),
end

end lift

section normal_closure

open intermediate_field

variables (F K) (L : Type*) [field L] [algebra F L] [algebra K L] [is_scalar_tower F K L]

/-- The normal closure of `K` in `L`. -/
noncomputable! def normal_closure : intermediate_field K L :=
{ algebra_map_mem' := λ r, le_supr (λ f : K →ₐ[F] L, f.field_range)
    (is_scalar_tower.to_alg_hom F K L) ⟨r, rfl⟩,
  .. (⨆ f : K →ₐ[F] L, f.field_range).to_subfield }

namespace normal_closure

lemma restrict_scalars_eq_supr_adjoin [h : normal F L] :
  (normal_closure F K L).restrict_scalars F = ⨆ x : K, adjoin F ((minpoly F x).root_set L) :=
begin
  refine le_antisymm (supr_le _) (supr_le (λ x, adjoin_le_iff.mpr (λ y hy, _))),
  { rintros f _ ⟨x, rfl⟩,
    refine le_supr (λ x, adjoin F ((minpoly F x).root_set L)) x
      (subset_adjoin F ((minpoly F x).root_set L) _),
    rw [mem_root_set_of_ne, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom,
        polynomial.aeval_alg_hom_apply, minpoly.aeval, map_zero],
    exact minpoly.ne_zero ((is_integral_algebra_map_iff (algebra_map K L).injective).mp
      (h.is_integral (algebra_map K L x))) },
  { rw [polynomial.root_set, finset.mem_coe, multiset.mem_to_finset] at hy,
    let g := (alg_hom_adjoin_integral_equiv F ((is_integral_algebra_map_iff
      (algebra_map K L).injective).mp (h.is_integral (algebra_map K L x)))).symm ⟨y, hy⟩,
    refine le_supr (λ f : K →ₐ[F] L, f.field_range)
      ((g.lift_normal L).comp (is_scalar_tower.to_alg_hom F K L))
      ⟨x, (g.lift_normal_commutes L (adjoin_simple.gen F x)).trans _⟩,
    rw [algebra.id.map_eq_id, ring_hom.id_apply],
    apply power_basis.lift_gen },
end

instance normal [h : normal F L] : normal F (normal_closure F K L) :=
let ϕ := algebra_map K L in begin
  rw [←intermediate_field.restrict_scalars_normal, restrict_scalars_eq_supr_adjoin],
  apply intermediate_field.normal_supr F L _,
  intro x,
  apply normal.of_is_splitting_field (minpoly F x),
  exact adjoin_root_set_is_splitting_field ((minpoly.eq_of_algebra_map_eq ϕ.injective
    ((is_integral_algebra_map_iff ϕ.injective).mp (h.is_integral (ϕ x))) rfl).symm ▸ h.splits _),
end

instance is_finite_dimensional [finite_dimensional F K] :
  finite_dimensional F (normal_closure F K L) :=
begin
  haveI : ∀ f : K →ₐ[F] L, finite_dimensional F f.field_range :=
  λ f, f.to_linear_map.finite_dimensional_range,
  apply intermediate_field.finite_dimensional_supr_of_finite,
end

end normal_closure

end normal_closure
