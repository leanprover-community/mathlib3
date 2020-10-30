/-
Copyright (c) 2018 Kevin Buzzard and Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot.

This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
-/
import group_theory.coset

universes u v

namespace quotient_group

variables {G : Type u} [group G] (N : subgroup G) [nN : N.normal] {H : Type v} [group H]
include nN

@[to_additive quotient_add_group.add_group]
instance : group (quotient N) :=
{ one := (1 : G),
  mul := quotient.map₂' (*)
  (λ a₁ b₁ hab₁ a₂ b₂ hab₂,
    ((N.mul_mem_cancel_right (N.inv_mem hab₂)).1
        (by rw [mul_inv_rev, mul_inv_rev, ← mul_assoc (a₂⁻¹ * a₁⁻¹),
          mul_assoc _ b₂, ← mul_assoc b₂, mul_inv_self, one_mul, mul_assoc (a₂⁻¹)];
          exact nN.conj_mem _ hab₁ _))),
  mul_assoc := λ a b c, quotient.induction_on₃' a b c
    (λ a b c, congr_arg mk (mul_assoc a b c)),
  one_mul := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (one_mul a)),
  mul_one := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (mul_one a)),
  inv := λ a, quotient.lift_on' a (λ a, ((a⁻¹ : G) : quotient N))
    (λ a b hab, quotient.sound' begin
      show a⁻¹⁻¹ * b⁻¹ ∈ N,
      rw ← mul_inv_rev,
      exact N.inv_mem (nN.mem_comm hab)
    end),
  mul_left_inv := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (mul_left_inv a)) }

/-- The group homomorphism from `G` to `G/N`. -/
@[to_additive quotient_add_group.mk' "The additive group homomorphism from `G` to `G/N`."]
def mk' : G →* quotient N := monoid_hom.mk' (quotient_group.mk) (λ _ _, rfl)

@[simp, to_additive quotient_add_group.ker_mk]
lemma ker_mk :
  monoid_hom.ker (quotient_group.mk' N : G →* quotient_group.quotient N) = N :=
begin
  ext g,
  rw [monoid_hom.mem_ker, eq_comm],
  show (((1 : G) : quotient_group.quotient N)) = g ↔ _,
  rw [quotient_group.eq, one_inv, one_mul],
end

-- for commutative groups we don't need normality assumption
omit nN

@[to_additive quotient_add_group.add_comm_group]
instance {G : Type*} [comm_group G] (N : subgroup G) : comm_group (quotient N) :=
{ mul_comm := λ a b, quotient.induction_on₂' a b
    (λ a b, congr_arg mk (mul_comm a b)),
  .. @quotient_group.quotient.group _ _ N N.normal_of_comm }

include nN

local notation ` Q ` := quotient N

@[simp, to_additive quotient_add_group.coe_zero]
lemma coe_one : ((1 : G) : Q) = 1 := rfl

@[simp, to_additive quotient_add_group.coe_add]
lemma coe_mul (a b : G) : ((a * b : G) : Q) = a * b := rfl

@[simp, to_additive quotient_add_group.coe_neg]
lemma coe_inv (a : G) : ((a⁻¹ : G) : Q) = a⁻¹ := rfl

@[simp] lemma coe_pow (a : G) (n : ℕ) : ((a ^ n : G) : Q) = a ^ n :=
(mk' N).map_pow a n

@[simp] lemma coe_gpow (a : G) (n : ℤ) : ((a ^ n : G) : Q) = a ^ n :=
(mk' N).map_gpow a n

/-- A group homomorphism `φ : G →* H` with `N ⊆ ker(φ)` descends (i.e. `lift`s) to a
group homomorphism `G/N →* H`. -/
@[to_additive quotient_add_group.lift "An `add_group` homomorphism `φ : G →+ H` with `N ⊆ ker(φ)`
descends (i.e. `lift`s) to a group homomorphism `G/N →* H`."]
def lift (φ : G →* H) (HN : ∀x∈N, φ x = 1) : Q →* H :=
monoid_hom.mk'
  (λ q : Q, q.lift_on' φ $ assume a b (hab : a⁻¹ * b ∈ N),
  (calc φ a = φ a * 1           : (mul_one _).symm
  ...       = φ a * φ (a⁻¹ * b) : HN (a⁻¹ * b) hab ▸ rfl
  ...       = φ (a * (a⁻¹ * b)) : (is_mul_hom.map_mul φ a (a⁻¹ * b)).symm
  ...       = φ b               : by rw mul_inv_cancel_left))
  (λ q r, quotient.induction_on₂' q r $ is_mul_hom.map_mul φ)

@[simp, to_additive quotient_add_group.lift_mk]
lemma lift_mk {φ : G →* H} (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN (g : Q) = φ g := rfl

@[simp, to_additive quotient_add_group.lift_mk']
lemma lift_mk' {φ : G →* H} (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN (mk g : Q) = φ g := rfl

@[simp, to_additive quotient_add_group.lift_quot_mk]
lemma lift_quot_mk {φ : G →* H} (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN (quot.mk _ g : Q) = φ g := rfl

/-- A group homomorphism `f : G →* H` induces a map `G/N →* H/M` if `N ⊆ f⁻¹(M)`. -/
@[to_additive quotient_add_group.map "An `add_group` homomorphism `f : G →+ H` induces a map
`G/N →+ H/M` if `N ⊆ f⁻¹(M)`."]
def map (M : subgroup H) [M.normal] (f : G →* H) (h : N ≤ M.comap f) :
  quotient N →* quotient M :=
begin
  refine quotient_group.lift N ((mk' M).comp f) _,
  assume x hx,
  refine quotient_group.eq.2 _,
  rw [mul_one, subgroup.inv_mem_iff],
  exact h hx,
end

omit nN
variables (φ : G →* H)

open function monoid_hom

/-- The induced map from the quotient by the kernel to the codomain. -/
@[to_additive quotient_add_group.ker_lift "The induced map from the quotient by the kernel to the
codomain."]
def ker_lift : quotient (ker φ) →* H :=
lift _ φ $ λ g, φ.mem_ker.mp

@[simp, to_additive quotient_add_group.ker_lift_mk]
lemma ker_lift_mk (g : G) : (ker_lift φ) g = φ g :=
lift_mk _ _ _

@[simp, to_additive quotient_add_group.ker_lift_mk']
lemma ker_lift_mk' (g : G) : (ker_lift φ) (mk g) = φ g :=
lift_mk' _ _ _

@[to_additive quotient_add_group.injective_ker_lift]
lemma ker_lift_injective : injective (ker_lift φ) :=
assume a b, quotient.induction_on₂' a b $
  assume a b (h : φ a = φ b), quotient.sound' $
show a⁻¹ * b ∈ ker φ, by rw [mem_ker,
  is_mul_hom.map_mul φ, ← h, is_group_hom.map_inv φ, inv_mul_self]

-- Note that ker φ isn't definitionally ker (to_range φ)
-- so there is a bit of annoying code duplication here

/-- The induced map from the quotient by the kernel to the range. -/
@[to_additive quotient_add_group.range_ker_lift "The induced map from the quotient by the kernel to
the range."]
def range_ker_lift : quotient (ker φ) →* φ.range :=
lift _ (to_range φ) $ λ g hg, (mem_ker _).mp $ by rwa to_range_ker

@[to_additive quotient_add_group.range_ker_lift_injective]
lemma range_ker_lift_injective : injective (range_ker_lift φ) :=
assume a b, quotient.induction_on₂' a b $
  assume a b (h : to_range φ a = to_range φ b), quotient.sound' $
show a⁻¹ * b ∈ ker φ, by rw [←to_range_ker, mem_ker,
  is_mul_hom.map_mul (to_range φ), ← h, is_group_hom.map_inv (to_range φ), inv_mul_self]

@[to_additive quotient_add_group.range_ker_lift_surjective]
lemma range_ker_lift_surjective : surjective (range_ker_lift φ) :=
begin
  rintro ⟨_, g, rfl⟩,
  use mk g,
  refl,
end

/-- The first isomorphism theorem (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/
@[to_additive quotient_add_group.quotient_ker_equiv_range "The first isomorphism theorem
(a definition): the canonical isomorphism between `G/(ker φ)` to `range φ`."]
noncomputable def quotient_ker_equiv_range : (quotient (ker φ)) ≃* range φ :=
mul_equiv.of_bijective (range_ker_lift φ) ⟨range_ker_lift_injective φ, range_ker_lift_surjective φ⟩

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a surjection `φ : G →* H`. -/
@[to_additive quotient_add_group.quotient_ker_equiv_of_surjective "The canonical isomorphism
`G/(ker φ) ≃+ H` induced by a surjection `φ : G →+ H`."]
noncomputable def quotient_ker_equiv_of_surjective (hφ : function.surjective φ) :
  (quotient (ker φ)) ≃* H :=
mul_equiv.of_bijective (ker_lift φ) ⟨ker_lift_injective φ, λ h, begin
  rcases hφ h with ⟨g, rfl⟩,
  use mk g,
  refl
end⟩

end quotient_group
