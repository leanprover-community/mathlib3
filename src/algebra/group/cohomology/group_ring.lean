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
  Showing it's a free `ℤ[G]`-module for `n ≥ 1.`


Lots of long proofs of map_smul in this whole folder. TODO: see if I can factor out common
lemmas -/

variables (G : Type*) [group G] (M : Type*) [add_comm_group M] [distrib_mul_action G M]
(n : ℕ)
noncomputable theory

/- Thank you to this def for solving all my instance clashes -/
/- Linter asks me not to assume `G` is a group. But it seems misleading to do this as
  this def is basically 'made for' the situation of G being a group, idk. -/
/-- The ring `ℤ[G]`. -/
def group_ring (G : Type*) := monoid_algebra ℤ G

namespace group_ring

instance (G : Type*) : inhabited (group_ring G) :=
by unfold group_ring; apply_instance
instance (G : Type*) : add_comm_group (group_ring G) :=
finsupp.add_comm_group

instance : ring (group_ring G) :=
{ ..monoid_algebra.semiring, ..group_ring.add_comm_group G }

/-- The natural inclusion `G → ℤ[G]`. -/
def of : G →* group_ring G :=
monoid_algebra.of ℤ G

variables {G}

@[simp] lemma of_apply (g : G) :
  of G g = finsupp.single g (1 : ℤ) := rfl

lemma zsmul_single_one (g : G) (r : ℤ) :
  (finsupp.single g r : group_ring G) = r • (of G g) :=
by simp only [mul_one, finsupp.smul_single', zsmul_eq_smul, of_apply]

@[elab_as_eliminator]
lemma induction_on {p : group_ring G → Prop} (f : group_ring G)
  (hM : ∀ g, p (of G g)) (hadd : ∀ f g : group_ring G, p f → p g → p (f + g))
  (hsmul : ∀ (r : ℤ) f, p f → p (r • f)) : p f :=
monoid_algebra.induction_on _ hM hadd hsmul

lemma ext {P : Type*} [add_comm_group P] (f : group_ring G →+ P)
  (g : group_ring G →+ P) (H : ∀ x, f (of G x) = g (of G x)) {x} :
  f x = g x :=
begin
  congr,
  refine finsupp.add_hom_ext _,
  intros,
  rw ←finsupp.smul_single_one,
  simp only [add_monoid_hom.map_zsmul, ←of_apply, H],
end

variables (G)

/-- `ℤ[G]`-module instance on an `add_comm_group` `M` with a `distrib_mul_action` of `G`.
  Deliberately not an instance. -/
def to_module {G : Type*} [group G] {M : Type*} [add_comm_group M]
  [H : distrib_mul_action G M] : module (group_ring G) M :=
{ smul := λ g m, finsupp.total G M ℤ (λ h, h • m) g,
  one_smul := λ b, by
  { dsimp,
    erw [finsupp.total_single],
    simp only [one_smul] },
  mul_smul := λ g h m, by
  { refine g.induction_on _ _ _,
    { intros g,
      dsimp,
      simp only [one_zsmul, finsupp.total_single, monoid_algebra.mul_def, one_mul,
        zero_mul, finsupp.single_zero, finsupp.sum_zero, finsupp.sum_single_index,
        linear_map.map_finsupp_sum],
      rw [finsupp.total_apply, finsupp.smul_sum],
      congr,
      ext f n,
      rw [mul_smul, distrib_mul_action.smul_zsmul] },
    { intros x y hx hy,
      rw add_mul,
      simp only [linear_map.map_add] at *,
      simp only [hx, hy] },
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

instance {H : Type*} [mul_action G H] :
  distrib_mul_action G (group_ring H) :=
finsupp.comap_distrib_mul_action

instance : module (group_ring G) (group_ring (fin n → G)) :=
group_ring.to_module

instance (M : submodule (group_ring G) (group_ring (fin n → G))) :
  has_coe M (group_ring (fin n → G)) :=
{ coe := λ m, m.1 }

variables {G n}

lemma smul_def
  (g : group_ring G) (h : group_ring (fin n → G)) :
  g • h = finsupp.total G (group_ring (fin n → G)) ℤ (λ x, x • h) g :=
rfl

lemma of_smul_of (g : G) (x : fin n → G) :
  of G g • of (fin n → G) x = of (fin n → G) (g • x) :=
show finsupp.total _ _ _ _ _ = _, by simp

/-- Makes a `ℤ[G]`-linear map from a `G`-linear hom of additive groups. -/
def mk_linear {P : Type*} {P' : Type*} [add_comm_group P] [add_comm_group P']
  [module (group_ring G) P] [module (group_ring G) P'] (f : P →+ P')
  (H : ∀ g x, f (of G g • x) = of G g • f x) : P →ₗ[group_ring G] P' :=
{ map_smul' := λ z,
  begin
  refine z.induction_on (by exact H) _ _,
  { intros a b ha hb x,
    dsimp at ⊢ ha hb,
    simp only [add_smul, f.map_add, ha, hb] },
  { intros r a ha x,
    dsimp at ⊢ ha,
    simp only [smul_assoc, f.map_zsmul, ha] }
  end, ..f }

@[simp] lemma mk_linear_apply {P : Type*} {P' : Type*} [add_comm_group P] [add_comm_group P']
  [module (group_ring G) P] [module (group_ring G) P'] (f : P →+ P')
  {H : ∀ g x, f (of G g • x) = of G g • f x} {x : P} :
  mk_linear f H x = f x := rfl

/-- Makes a `ℤ[G]`-linear isomorphism from a `G`-linear isomorphism of additive groups. -/
def mk_equiv {P : Type*} {P' : Type*} [add_comm_group P] [add_comm_group P']
  [module (group_ring G) P] [module (group_ring G) P'] (f : P ≃+ P')
  (H : ∀ g x, f (of G g • x) = of G g • f x) : P ≃ₗ[group_ring G] P' :=
{ ..f, ..mk_linear f.to_add_monoid_hom H }

@[simp] lemma mk_equiv_apply {P : Type*} {P' : Type*} [add_comm_group P] [add_comm_group P']
  [module (group_ring G) P] [module (group_ring G) P'] (f : P ≃+ P')
  {H : ∀ g x, f (of G g • x) = of G g • f x} {x : P} :
  mk_equiv f H x = f x := rfl

lemma map_smul_of_map_of_smul_of {P : Type*} [add_comm_group P] [module (group_ring G) P] {n : ℕ}
  (f : group_ring (fin n → G) →+ P)
  (H : ∀ (g : G) (x : fin n → G), f (of G g • of _ x) = of G g • f (of _ x)) (g : group_ring G)
  (x : group_ring (fin n → G)) : f (g • x) = g • f x :=
begin
  convert (mk_linear f _).map_smul g x,
  intros a b,
  refine b.induction_on (by exact H a) _ _,
  { intros s t hs ht,
    simp only [smul_add, f.map_add, hs, ht] },
  { intros r s hs,
    simp only [smul_algebra_smul_comm, f.map_zsmul, hs] }
end

variables (G)

/-- The natural `ℤ[G]`-linear isomorphism `ℤ[G¹] ≅ ℤ[G]` -/
def dom_one_equiv : group_ring (fin 1 → G) ≃ₗ[group_ring G] group_ring G :=
mk_equiv (finsupp.dom_congr (fin.dom_one_equiv G)) $ λ g x, finsupp.ext $ λ c,
by { dsimp, simpa [smul_def] }

variables {G}

lemma dom_one_equiv_single {g : fin 1 → G} {m : ℤ} :
  dom_one_equiv G (finsupp.single g m) = finsupp.single (g 0) m :=
begin
  erw [finsupp.dom_congr_apply, finsupp.equiv_map_domain_single],
  refl,
end

/-- The hom sending `ℤ[Gⁿ] → ℤ[Gⁿ⁺¹]` sending `(g₁, ..., gₙ) ↦ (r, g₁, ..., gₙ)` -/
def cons {G : Type*} (n : ℕ) (r : G) : group_ring (fin n → G) →+ group_ring (fin (n + 1) → G) :=
finsupp.map_domain.add_monoid_hom (@fin.cons n (λ i, G) r)

lemma cons_of {n : ℕ} {r : G} (g : fin n → G) :
  cons n r (of _ g) = of (fin (n + 1) → G) (fin.cons r g) :=
finsupp.map_domain_single

variables (G n)

/-- The quotient of `Gⁿ⁺¹` by the left action of `G` -/
abbreviation orbit_quot := quotient (mul_action.orbit_rel G (fin (n + 1) → G))

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
mk_linear (to_basis_add_hom G n) $ λ x g,
begin
  refine map_smul_of_map_of_smul_of (to_basis_add_hom G n) _ _ _,
  intros g y,
  simp only [of_smul_of, to_basis_add_hom_of, ←of_apply],
  simp [smul_def, @quotient.sound' _ (mul_action.orbit_rel G _) _ y (set.mem_range_self g)],
end

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
    simp [mul_assoc]
  end)

lemma left_inverse (x : group_ring (fin (n + 1) → G)) :
  of_basis G n (to_basis G n x) = x :=
begin
  refine ext ((of_basis G n).comp (to_basis G n)).to_add_monoid_hom (add_monoid_hom.id _) _,
  { intro g,
    dsimp,
    erw to_basis_add_hom_of,
    unfold of_basis,
    simpa only [quotient.lift_on'_mk', smul_inv_smul, of_smul_of, zero_smul,
      finsupp.sum_single_index, finsupp.lift_apply] },
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
