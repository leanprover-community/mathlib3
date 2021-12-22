/-
Copyright (c) 2021 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import algebra.group_action_hom
import data.fin_simplicial_complex
import algebra.monoid_algebra.basic
import algebra.group.cohomology.lemmas
import linear_algebra.basis

/-! Setting up `ℤ[Gⁿ]`, defined as `monoid_algebra ℤ (fin n → G)`.
  Showing it's a free `ℤ[G]`-module for `n ≥ 1.` -/

variables (G : Type*) [group G] (M : Type*) [add_comm_group M] [distrib_mul_action G M]
(n : ℕ)
noncomputable theory

/-- The quotient of `Gⁿ⁺¹` by the left action of `G` -/
abbreviation orbit_quot := quotient (mul_action.orbit_rel G (fin (n + 1) → G))

/- Thank you to this def for solving all my instance clashes -/
def group_ring := monoid_algebra ℤ G

instance : add_comm_group (group_ring G) :=
finsupp.add_comm_group

instance : ring (group_ring G) :=
{ ..monoid_algebra.semiring, ..group_ring.add_comm_group G }

/-- `ℤ[G]`-module instance on an `add_comm_group` `M` with a `distrib_mul_action` of `G`.
  Deliberately not an instance. -/
def distrib_mul_action.to_module {G : Type*} [group G] {M : Type*} [add_comm_group M]
  [h : distrib_mul_action G M] : module (group_ring G) M :=
{ smul := λ g m, finsupp.total G M ℤ (λ h, h • m) g,
    one_smul := λ b, by
    { dsimp,
        erw [finsupp.total_single],
        simp only [one_smul] },
    mul_smul := λ g h m, by
    { refine g.induction_on _ _ _,
      intros g,
      { dsimp,
        simp only [one_gsmul, finsupp.total_single, monoid_algebra.mul_def, one_mul,
          zero_mul, finsupp.single_zero, finsupp.sum_zero, finsupp.sum_single_index,
          linear_map.map_finsupp_sum],
        rw [finsupp.total_apply, finsupp.smul_sum],
        congr,
        ext f n,
        rw [mul_smul, distrib_mul_action.smul_gsmul] },
      { intros g1 g2 hg1 hg2,
        rw add_mul,
        simp only [linear_map.map_add] at *,
        simp only [hg1, hg2] },
      { intros r f hf,
        rw algebra.smul_mul_assoc,
        simp only [linear_map.map_smul] at *,
        simp only [←hf] }},
    smul_add := λ g b c, by
      { simp only [smul_add, finsupp.total_apply, finsupp.sum_add] },
    smul_zero := λ x, by
      simp only [finsupp.total_apply, finsupp.sum_zero, smul_zero],
    add_smul := λ r s x, linear_map.map_add _ _ _,
    zero_smul := λ x, linear_map.map_zero _ }

namespace group_ring

instance {H : Type*} [group H] [mul_action G H] :
  distrib_mul_action G (group_ring H) :=
finsupp.comap_distrib_mul_action

instance : module (group_ring G) (group_ring (fin n → G)) :=
distrib_mul_action.to_module

instance (M : submodule (group_ring G) (group_ring (fin n → G))) :
  has_coe M (group_ring (fin n → G)) :=
{ coe := λ m, m.1 }

def of : G →* group_ring G :=
monoid_algebra.of ℤ G

@[simp] lemma of_apply (g : G) :
  of G g = finsupp.single g (1 : ℤ) := rfl

variables {G n}

lemma smul_def
  (g : group_ring G) (h : group_ring (fin n → G)) :
  g • h = finsupp.total G (group_ring (fin n → G)) ℤ (λ x, x • h) g :=
rfl

lemma gsmul_single_one (g : G) (r : ℤ) :
  (finsupp.single g r : group_ring G) = r • (of G g) :=
by simp only [mul_one, finsupp.smul_single', gsmul_eq_smul, of_apply]

lemma of_smul_of (g : G) (x : fin n → G) :
  of G g • of (fin n → G) x = of (fin n → G) (g • x) :=
begin
  show finsupp.total _ _ _ _ _ = _,
  simp only [of_apply, finsupp.total_single, one_smul, finsupp.comap_smul_single],
end

@[elab_as_eliminator]
lemma induction_on {p : group_ring G → Prop} (f : group_ring G)
  (hM : ∀ g, p (of G g)) (hadd : ∀ f g : group_ring G, p f → p g → p (f + g))
  (hsmul : ∀ (r : ℤ) f, p f → p (r • f)) : p f :=
begin
  refine finsupp.induction_linear f _ (λ f g hf hg, hadd f g hf hg) (λ g r, _),
  { simpa using hsmul 0 (of G 1) (hM 1) },
  { convert hsmul r (of G g) (hM g),
    rw gsmul_single_one, },
end

variables (G)
def dom_one_equiv : group_ring (fin 1 → G) ≃ₗ[group_ring G] group_ring G :=
{ map_smul' := λ x y, by
  { refine x.induction_on _ _ _,
    { dsimp,
      intro g,
      ext,
      rw [smul_def, finsupp.total_single, one_smul],
      simp only [monoid_algebra.single_mul_apply, one_mul, finsupp.equiv_map_domain_apply,
        finsupp.comap_smul_apply],
      congr },
    { intros a b ha hb,
      simp only [add_smul, add_equiv.map_add', ha, hb]},
    { intros r a ha,
      simp only [add_equiv.to_fun_eq_coe, add_equiv.map_gsmul, smul_assoc] at ⊢ ha,
      rw ha }},
  ..finsupp.dom_congr (fin.dom_one_equiv G) }

variables {G}

lemma dom_one_equiv_single {g : fin 1 → G} {m : ℤ} :
  dom_one_equiv G (finsupp.single g m) = finsupp.single (g 0) m :=
begin
  erw [finsupp.dom_congr_apply, finsupp.equiv_map_domain_single],
  refl,
end

/- The hom sending `ℤ[Gⁿ] → ℤ[Gⁿ⁺¹]` sending `(g₁, ..., gₙ) ↦ (r, g₁, ..., gₙ)` -/
def cons (n : ℕ) (r : G) : group_ring (fin n → G) →+ group_ring (fin (n + 1) → G) :=
finsupp.map_domain.add_monoid_hom (@fin.cons n (λ i, G) r)

lemma cons_of {n : ℕ} {r : G} (g : fin n → G) :
  cons n r (of _ g) = of (fin (n + 1) → G) (fin.cons r g) :=
finsupp.map_domain_single

variables (G n)

/-- Helper function; sends `g ∈ Gⁿ⁺¹`, `n ∈ ℤ` to `(n • g₀) • g` as an element of `ℤ[Gⁿ⁺¹] → ℤ[G]` -/
def to_basis_add_hom_aux (g : fin (n + 1) → G) : ℤ →+ ((fin (n + 1) → G) →₀ group_ring G) :=
{ to_fun := λ m, finsupp.single g (finsupp.single (g 0) m),
    map_zero' := by simp only [finsupp.single_zero],
    map_add' := λ x y, by simp only [finsupp.single_add]}

/-- Extends the map sending `g : Gⁿ⁺¹` to `g₀ • ⟦g⟧` -/
def to_basis_add_hom :
  group_ring (fin (n + 1) → G) →+ (orbit_quot G n →₀ group_ring G) :=
(@finsupp.map_domain.add_monoid_hom (fin (n + 1) → G) (orbit_quot G n) (group_ring G) _ quotient.mk').comp
(finsupp.lift_add_hom $ to_basis_add_hom_aux G n)

variables {G n}

lemma to_basis_add_hom_of (g : fin (n + 1) → G) :
  to_basis_add_hom G n (of _ g) = finsupp.single (quotient.mk' g : orbit_quot G n) (of G (g 0)) :=
begin
  unfold to_basis_add_hom,
  simp only [finsupp.lift_add_hom_apply_single, add_monoid_hom.coe_comp,
    function.comp_app, of_apply],
  exact finsupp.map_domain_single,
end


variables (G n)

/-- The `ℤ[G]`-linear map on `ℤ[Gⁿ⁺¹]` sending `g` to `g₀ • ⟦g⟧`; image is a basis
  of the free `ℤ[G]`-module on `Gⁿ⁺¹/G`. -/
noncomputable def to_basis :
  group_ring (fin (n + 1) → G) →ₗ[group_ring G] (orbit_quot G n →₀ group_ring G) :=
{ map_smul' := λ g x,
  begin
    refine x.induction_on _ _ _,
    { intro x,
      refine g.induction_on _ _ _,
      { intro g,
        erw of_smul_of,
        dsimp,
        erw [to_basis_add_hom_of, to_basis_add_hom_of, ←of_apply],
        simp only [smul_eq_mul, smul_def, finsupp.smul_single, of_apply, pi.smul_apply,
          one_mul, int.cast_one, finsupp.total_single, finsupp.comap_smul_single, gsmul_eq_mul],
        congr' 1,
        { exact quotient.sound' (set.mem_range_self _) },
        { erw [monoid_algebra.single_mul_single, one_mul] }},
      { intros a b ha hb,
        simp only [add_smul, *, add_monoid_hom.map_add, add_monoid_hom.to_fun_eq_coe] at * },
      { intros r y hy,
        simp only [add_monoid_hom.to_fun_eq_coe] at *,
        rw [smul_assoc, add_monoid_hom.map_gsmul, hy, smul_assoc] }},
    { intros a b ha hb,
      simp only [*, smul_add, add_monoid_hom.map_add, add_monoid_hom.to_fun_eq_coe] at * },
    { intros r y hy,
      dsimp at ⊢ hy,
      rw [smul_algebra_smul_comm, add_monoid_hom.map_gsmul, hy,
        ←smul_algebra_smul_comm, add_monoid_hom.map_gsmul] }
  end, .. to_basis_add_hom G n }

variables {G n}

/-- Helper function sending `x ∈ Gⁿ⁺¹`, `g ∈ G`, `n ∈ ℤ` to `n • (g • x₀⁻¹ • x)`. -/
def of_basis_aux (x : fin (n + 1) → G) (g : G) : ℤ →+ (group_ring (fin (n + 1) → G)) :=
{ to_fun := finsupp.single_add_hom (g • (x 0)⁻¹ • x),
  map_zero' := finsupp.single_zero,
  map_add' := λ _ _, finsupp.single_add }

variables (G n)

/-- Inverse of `to_basis` from the free `ℤ[G]`-module on `Gⁿ⁺¹/G` to `ℤ[Gⁿ⁺¹]`,
  sending `⟦g⟧ ∈ Gⁿ⁺¹/G` to `g₀⁻¹ • g ∈ ℤ[Gⁿ⁺¹]` -/
def of_basis : (orbit_quot G n →₀ (group_ring G)) →ₗ[group_ring G] group_ring (fin (n + 1) → G) :=
finsupp.lift (group_ring (fin (n + 1) → G)) (group_ring G) (orbit_quot G n)
  (λ y, quotient.lift_on' y (λ x, of _ ((x 0)⁻¹ • x)) $
  begin
    rintros a b ⟨c, rfl⟩,
    dsimp,
    congr' 1,
    ext i,
    simp only [mul_inv_rev, smul_eq_mul, pi.smul_apply, mul_assoc, inv_mul_cancel_left]
  end)

lemma left_inverse (x : group_ring (fin (n + 1) → G)) :
  of_basis G n (to_basis G n x) = x :=
begin
  refine induction_on x _ _ _,
  { intro g,
    erw to_basis_add_hom_of,
    unfold of_basis,
    simp only [quotient.lift_on'_mk', smul_inv_smul, of_smul_of, zero_smul,
      finsupp.sum_single_index, finsupp.lift_apply]},
  { intros f g hf hg,
    simp only [linear_map.map_add, hf, hg]},
  { intros r f hf,
    simp only [linear_map.map_smul_of_tower, hf] }
end

lemma right_inverse (x : orbit_quot G n →₀ group_ring G) :
  to_basis G n (of_basis G n x) = x :=
begin
  refine x.induction_linear _ _ _,
  { simp only [linear_map.map_zero] },
  { intros f g hf hg,
    simp only [linear_map.map_add, hf, hg] },
  { intros a b,
    refine quotient.induction_on' a (λ c, _),
    unfold of_basis,
    simp only [quotient.lift_on'_mk', zero_smul, of_apply, finsupp.sum_single_index,
      linear_map.map_smul, finsupp.lift_apply],
    erw to_basis_add_hom_of,
    simp only [finsupp.smul_single', smul_eq_mul, of_apply, pi.smul_apply, mul_left_inv],
    erw mul_one,
    congr' 1,
    exact quotient.sound' (mul_action.mem_orbit _ _) }
end

/-- An isomorphism of `ℤ[Gⁿ⁺¹]` with the free `ℤ[G]`-module on `Gⁿ⁺¹/G`, given by `to_basis`. -/
def basis : basis (orbit_quot G n) (group_ring G) (group_ring (fin (n + 1) → G)) :=
{ repr :=
  { inv_fun := of_basis G n,
    left_inv := left_inverse G n,
    right_inv := right_inverse G n, ..to_basis G n } }

end group_ring
