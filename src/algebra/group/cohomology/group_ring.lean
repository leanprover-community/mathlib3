/-
Copyright (c) 2021 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import algebra.group.cohomology.cochain_succ
import linear_algebra.basis
/-!

# group_ring

What does this do?

-/
variables (G : Type*) [group G] (M : Type*) [add_comm_group M] [distrib_mul_action G M]
(n : ℕ)
noncomputable theory

abbreviation orbit_quot := quotient (mul_action.orbit_rel G (fin (n + 1) → G))

def distrib_mul_action.to_module {G : Type*} [group G] {M : Type*} [add_comm_group M]
  [h : distrib_mul_action G M] : module (monoid_algebra ℤ G) M :=
{ smul := λ g m, finsupp.total G M ℤ (λ h, h • m) g,
    one_smul := λ b, by
    { dsimp,
        erw [finsupp.total_single],
        simp only [one_smul] },
    mul_smul := λ g h m, by
    { refine g.induction_on _ _ _,
      intros g,
      { dsimp,
        simp only [one_gsmul, finsupp.total_single, monoid_algebra.mul_def, one_mul, zero_mul, finsupp.single_zero,
          finsupp.sum_zero, finsupp.sum_single_index, linear_map.map_finsupp_sum],
        rw [finsupp.total_apply, finsupp.smul_sum],
        congr,
        ext f n,
        rw [mul_smul, group_cohomology.cochain_succ.smul_gsmul] },
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

def group_ring := monoid_algebra ℤ G

namespace group_ring

instance : add_comm_group (group_ring G) :=
finsupp.add_comm_group

instance : ring (group_ring G) :=
{ ..monoid_algebra.semiring, ..group_ring.add_comm_group G }

instance {H : Type*} [group H] [mul_action G H] :
  distrib_mul_action G (group_ring H) :=
finsupp.comap_distrib_mul_action

instance : module (group_ring G) (group_ring (fin n → G)) :=
distrib_mul_action.to_module

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

variables (G n)

def to_basis_add_hom_aux (g : fin (n + 1) → G) : ℤ →+ ((fin (n + 1) → G) →₀ group_ring G) :=
{ to_fun := λ m, finsupp.single g (finsupp.single (g 0) m),
    map_zero' := by simp only [finsupp.single_zero],
    map_add' := λ x y, by simp only [finsupp.single_add]}

def to_basis_add_hom :=
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

lemma of_smul_of (g : G) (x : fin n → G) :
  of G g • of (fin n → G) x = of (fin n → G) (g • x) :=
begin
  show finsupp.total _ _ _ _ _ = _,
  simp only [of_apply, finsupp.total_single, one_smul, finsupp.comap_smul_single],
end

variables (G n)

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

def of_basis_aux (x : fin (n + 1) → G) (g : G) : ℤ →+ (group_ring (fin (n + 1) → G)) :=
{ to_fun := finsupp.single_add_hom (g • (x 0)⁻¹ • x),
  map_zero' := finsupp.single_zero,
  map_add' := λ _ _, finsupp.single_add }

variables (G n)

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

def basis : basis (orbit_quot G n) (group_ring G) (group_ring (fin (n + 1) → G)) :=
{ repr :=
  { inv_fun := of_basis G n,
    left_inv := left_inverse G n,
    right_inv := right_inverse G n, ..to_basis G n } }

end group_ring
