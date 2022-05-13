/-
Copyright (c) 2021 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import representation_theory.invariants
import representation_theory.Rep
variables {k G V : Type*} [comm_semiring k] [group G] [add_comm_monoid V] [module k V]
variables (ρ : representation k G V)

open monoid_algebra (lift) (of)

variables (V)
-- not sure if good idea
@[derive [add_comm_monoid]] def with_rep (ρ : representation k G V) := V

instance : module k (with_rep V ρ) :=
by dunfold with_rep; apply_instance

variables {V}

noncomputable instance with_rep.module' : module (monoid_algebra k G) (with_rep V ρ) :=
representation.as_module ρ

variables (k G) (n : ℕ)

noncomputable def lsmul (H : Type*) [group H] [mul_action G H] :
  representation k G (monoid_algebra k H) :=
{ to_fun := λ g, finsupp.lmap_domain k k ((•) g),
  map_one' := by { ext x y, dsimp, simp },
  map_mul' := λ x y, by { ext z w, simp [mul_smul] }}

abbreviation hmm := with_rep (monoid_algebra k (fin n → G)) (lsmul k G _)

/-
/-- The natural `ℤ[G]`-linear isomorphism `ℤ[G¹] ≅ ℤ[G]` -/
def dom_one_equiv : monoid_algebra k (fin 1 → G) ≃ₗ[monoid_algebra k G] monoid_algebra k G :=
mk_equiv (finsupp.dom_congr (fin.dom_one_equiv G)) $ λ g x, finsupp.ext $ λ c,
by { dsimp, simpa [smul_def] }

variables {G}

lemma dom_one_equiv_single {g : fin 1 → G} {m : ℤ} :
  dom_one_equiv G (finsupp.single g m) = finsupp.single (g 0) m :=
begin
  erw [finsupp.dom_congr_apply, finsupp.equiv_map_domain_single],
  refl,
end-/

def cons_one_mul_hom : (fin n → G) →* (fin (n + 1) → G) :=
{ to_fun := @fin.cons n (λ i, G) 1,
  map_one' := by
  { ext,
    refine fin.induction_on x _ _,
    { rw fin.cons_zero,
      refl },
    { intros i ih,
      simp only [fin.cons_succ],
      refl }},
  map_mul' := by
  { intros x y,
    ext i,
    refine fin.induction_on i _ _,
    { rw [fin.cons_zero],
      exact (one_mul _).symm },
    { intros i ih,
      simp only [fin.cons_succ, pi.mul_apply] }}, }

/-- The hom sending `k[Gⁿ] → k[Gⁿ⁺¹]` sending `(g₁, ..., gₙ) ↦ (1, g₁, ..., gₙ)` -/
noncomputable def cons_one (n : ℕ) :
  monoid_algebra k (fin n → G) →ₐ[k] monoid_algebra k (fin (n + 1) → G) :=
monoid_algebra.map_domain_alg_hom k k (cons_one_mul_hom G n)

lemma cons_one_of {n : ℕ} (g : fin n → G) :
  cons_one k G n (of k _ g) = of k (fin (n + 1) → G) (fin.cons 1 g) :=
finsupp.map_domain_single

variables (G n)

/-- The quotient of `Gⁿ⁺¹` by the left action of `G` -/
abbreviation orbit_quot := quotient (mul_action.orbit_rel G (fin (n + 1) → G))

/-- The map sending `g = (g₀, ..., gₙ) ∈ k[Gⁿ⁺¹]` to `g₀ • ⟦g⟧`, as an element of the free
  `k[G]`-module on the set `Gⁿ⁺¹` modulo the left action of `G`. -/
noncomputable def to_basis_aux :
  monoid_algebra k (fin (n + 1) → G) →ₗ[k] (orbit_quot G n →₀ monoid_algebra k G) :=
(@finsupp.lmap_domain (fin (n + 1) → G) (monoid_algebra k G) k
 _ _ _ (orbit_quot G n) quotient.mk').comp
(finsupp.lift (monoid_algebra (monoid_algebra k G) (fin (n + 1) → G))
  k (fin (n + 1) → G) $ λ g, finsupp.single g (finsupp.single (g 0) 1))

variables {G n}

lemma to_basis_of (g : fin (n + 1) → G) :
  to_basis_aux k G n (of k _ g) = finsupp.single (quotient.mk' g : orbit_quot G n) (of k G (g 0)) :=
begin
  simp [to_basis_aux]
end

variables (G n)

/-- The `k[G]`-linear map on `k[Gⁿ⁺¹]` sending `g` to `g₀ • ⟦g⟧` as an element of the free
  `k[G]`-module on the set `Gⁿ⁺¹` modulo the left action of `G`. -/
noncomputable def to_basis :
  hmm k G (n + 1) →ₗ[monoid_algebra k G] (orbit_quot G n →₀ monoid_algebra k G) :=
sorry
/-mk_linear (to_basis_add_hom G n) $ λ x g,
begin
  refine map_smul_of_map_smul_of (to_basis_add_hom G n) _ _ _,
  intros g y,
  simp only [of_smul_of, to_basis_add_hom_of, ←of_apply],
  simp [smul_def, @quotient.sound' _ (mul_action.orbit_rel G _) _ y (set.mem_range_self g)],
end-/

variables {G n}

#exit
/-- Helper function sending `x ∈ Gⁿ⁺¹`, `g ∈ G`, `n ∈ ℤ` to `n • (g • x₀⁻¹ • x)`. -/
def of_basis_aux (x : fin (n + 1) → G) (g : G) : ℤ →+ (group_ring (fin (n + 1) → G)) :=
{ to_fun := finsupp.single_add_hom (g • (x 0)⁻¹ • x),
  map_zero' := finsupp.single_zero,
  map_add' := λ _ _, finsupp.single_add }

variables (G n)

/-- Inverse of `to_basis` from the free `ℤ[G]`-module on `Gⁿ⁺¹/G` to `ℤ[Gⁿ⁺¹]`,
  sending `⟦g⟧ ∈ Gⁿ⁺¹/G` to `g₀⁻¹ • g ∈ ℤ[Gⁿ⁺¹]` -/
def of_basis : (orbit_quot G n →₀ (monoid_algebra k G))
  →ₗ[monoid_algebra k G] group_ring (fin (n + 1) → G) :=
finsupp.lift (group_ring (fin (n + 1) → G)) (monoid_algebra k G) (orbit_quot G n)
  (λ y, quotient.lift_on' y (λ x, of _ ((x 0)⁻¹ • x)) $
  begin
    rintros a b ⟨c, rfl⟩,
    dsimp,
    congr' 1,
    ext i,
    simp [mul_assoc]
  end)

lemma left_inverse (x : group_ring (fin (n + 1) → G)) :
  of_basis G n (to_basis G n x) = x :=
begin
  refine ext ((of_basis G n).comp (to_basis G n)).to_add_monoid_hom
    (add_monoid_hom.id _) _,
  { intro g,
    dsimp,
    erw to_basis_add_hom_of,
    unfold of_basis,
    simpa only [quotient.lift_on'_mk', smul_inv_smul, of_smul_of, zero_smul,
      finsupp.sum_single_index, finsupp.lift_apply] },
end

lemma right_inverse (x : orbit_quot G n →₀ monoid_algebra k G) :
  to_basis G n (of_basis G n x) = x :=
begin
  refine x.induction_linear _ _ _,
  { simp only [linear_map.map_zero] },
  { intros f g hf hg,
    simp only [linear_map.map_add, hf, hg] },
  { intros a b,
    refine quotient.induction_on' a (λ c, _),
    unfold of_basis,
    simp only [quotient.lift_on'_mk', zero_smul, of_apply,
      finsupp.sum_single_index, linear_map.map_smul, finsupp.lift_apply],
    erw to_basis_add_hom_of,
    simp only [finsupp.smul_single', smul_eq_mul, of_apply,
      pi.smul_apply, mul_left_inv],
    erw mul_one,
    congr' 1,
    exact quotient.sound' (mul_action.mem_orbit _ _) }
end

/-- An isomorphism of `ℤ[Gⁿ⁺¹]` with the free `ℤ[G]`-module on the set `Gⁿ⁺¹`
  modulo the left action of `G`, given by `to_basis`. -/
def basis : basis (orbit_quot G n) (monoid_algebra k G) (group_ring (fin (n + 1) → G)) :=
{ repr :=
  { inv_fun := of_basis G n,
    left_inv := left_inverse G n,
    right_inv := right_inverse G n, ..to_basis G n } }

end group_ring
