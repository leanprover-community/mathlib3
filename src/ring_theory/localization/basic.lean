/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import algebra.algebra.basic
import data.equiv.ring
import group_theory.monoid_localization
import ring_theory.ideal.basic
import ring_theory.non_zero_divisors
import tactic.ring_exp

/-!
# Localizations of commutative rings

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R`, `f x = f y` iff there exists `c ∈ M` such that `x * c = y * c`.

In the following, let `R, P` be commutative rings, `S, Q` be `R`- and `P`-algebras
and `M, T` be submonoids of `R` and `P` respectively, e.g.:
```
variables (R S P Q : Type*) [comm_ring R] [comm_ring S] [comm_ring P] [comm_ring Q]
variables [algebra R S] [algebra P Q] (M : submonoid R) (T : submonoid P)
```

## Main definitions

 * `is_localization (M : submonoid R) (S : Type*)` is a typeclass expressing that `S` is a
   localization of `R` at `M`, i.e. the canonical map `algebra_map R S : R →+* S` is a
   localization map (satisfying the above properties).
 * `is_localization.mk' S` is a surjection sending `(x, y) : R × M` to `f x * (f y)⁻¹`
 * `is_localization.lift` is the ring homomorphism from `S` induced by a homomorphism from `R`
   which maps elements of `M` to invertible elements of the codomain.
 * `is_localization.map S Q` is the ring homomorphism from `S` to `Q` which maps elements
   of `M` to elements of `T`
 * `is_localization.ring_equiv_of_ring_equiv`: if `R` and `P` are isomorphic by an isomorphism
   sending `M` to `T`, then `S` and `Q` are isomorphic
 * `is_localization.alg_equiv`: if `Q` is another localization of `R` at `M`, then `S` and `Q`
   are isomorphic as `R`-algebras

## Main results

 * `localization M S`, a construction of the localization as a quotient type, defined in
   `group_theory.monoid_localization`, has `comm_ring`, `algebra R` and `is_localization M`
   instances if `R` is a ring. `localization.away`, `localization.at_prime` and `fraction_ring`
   are abbreviations for `localization`s and have their corresponding `is_localization` instances

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A previous version of this file used a fully bundled type of ring localization maps,
then used a type synonym `f.codomain` for `f : localization_map M S` to instantiate the
`R`-algebra structure on `S`. This results in defining ad-hoc copies for everything already
defined on `S`. By making `is_localization` a predicate on the `algebra_map R S`,
we can ensure the localization map commutes nicely with other `algebra_map`s.

To prove most lemmas about a localization map `algebra_map R S` in this file we invoke the
corresponding proof for the underlying `comm_monoid` localization map
`is_localization.to_localization_map M S`, which can be found in `group_theory.monoid_localization`
and the namespace `submonoid.localization_map`.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → localization M` equals the surjection
`localization_map.mk'` induced by the map `algebra_map : R →+* localization M`.
The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `localization_map.mk'` induced by any localization map.

The proof that "a `comm_ring` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[field K]` instead of just `[comm_ring K]`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/
variables {R : Type*} [comm_ring R] (M : submonoid R) (S : Type*) [comm_ring S]
variables [algebra R S] {P : Type*} [comm_ring P]

open function
open_locale big_operators

/-- The typeclass `is_localization (M : submodule R) S` where `S` is an `R`-algebra
expresses that `S` is isomorphic to the localization of `R` at `M`. -/
class is_localization : Prop :=
(map_units [] : ∀ y : M, is_unit (algebra_map R S y))
(surj [] : ∀ z : S, ∃ x : R × M, z * algebra_map R S x.2 = algebra_map R S x.1)
(eq_iff_exists [] : ∀ {x y}, algebra_map R S x = algebra_map R S y ↔ ∃ c : M, x * c = y * c)

variables {M S}

namespace is_localization

section is_localization

variables [is_localization M S]

section

variables (M)

lemma of_le (N : submonoid R) (h₁ : M ≤ N)
  (h₂ : ∀ r ∈ N, is_unit (algebra_map R S r)) : is_localization N S :=
{ map_units := λ r, h₂ r r.2,
  surj := λ s, by { obtain ⟨⟨x, y, hy⟩, H⟩ := is_localization.surj M s, exact ⟨⟨x, y, h₁ hy⟩, H⟩ },
  eq_iff_exists := λ x y, begin
    split,
    { rw is_localization.eq_iff_exists M,
      rintro ⟨c, hc⟩,
      exact ⟨⟨c, h₁ c.2⟩, hc⟩ },
    { rintro ⟨c, h⟩,
      simpa only [set_like.coe_mk, map_mul, (h₂ c c.2).mul_left_inj] using
        congr_arg (algebra_map R S) h }
  end }

variables (S)

/-- `is_localization.to_localization_map M S` shows `S` is the monoid localization of `R` at `M`. -/
@[simps]
def to_localization_map : submonoid.localization_map M S :=
{ to_fun := algebra_map R S,
  map_units' := is_localization.map_units _,
  surj' := is_localization.surj _,
  eq_iff_exists' := λ _ _, is_localization.eq_iff_exists _ _,
  .. algebra_map R S }

@[simp]
lemma to_localization_map_to_map :
  (to_localization_map M S).to_map = (algebra_map R S : R →* S) := rfl

lemma to_localization_map_to_map_apply (x) :
  (to_localization_map M S).to_map x = algebra_map R S x := rfl

end

variables (M)

/-- Given a localization map `f : M →* N`, a section function sending `z : N` to some
`(x, y) : M × S` such that `f x * (f y)⁻¹ = z`. -/
noncomputable def sec (z : S) : R × M :=
classical.some $ is_localization.surj _ z

@[simp] lemma to_localization_map_sec : (to_localization_map M S).sec = sec M := rfl

/-- Given `z : S`, `is_localization.sec M z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x` (so this lemma is true by definition). -/
lemma sec_spec (z : S) :
  z * algebra_map R S (is_localization.sec M z).2 =
    algebra_map R S (is_localization.sec M z).1 :=
classical.some_spec $ is_localization.surj _ z

/-- Given `z : S`, `is_localization.sec M z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x`, so this lemma is just an application of `S`'s commutativity. -/
lemma sec_spec' (z : S) :
  algebra_map R S (is_localization.sec M z).1 =
    algebra_map R S (is_localization.sec M z).2 * z :=
by rw [mul_comm, sec_spec]

variables {R M}

lemma map_right_cancel {x y} {c : M} (h : algebra_map R S (c * x) = algebra_map R S (c * y)) :
  algebra_map R S x = algebra_map R S y :=
(to_localization_map M S).map_right_cancel h

lemma map_left_cancel {x y} {c : M} (h : algebra_map R S (x * c) = algebra_map R S (y * c)) :
  algebra_map R S x = algebra_map R S y :=
(to_localization_map M S).map_left_cancel h

lemma eq_zero_of_fst_eq_zero {z x} {y : M}
  (h : z * algebra_map R S y = algebra_map R S x) (hx : x = 0) : z = 0 :=
by { rw [hx, (algebra_map R S).map_zero] at h,
     exact (is_unit.mul_left_eq_zero (is_localization.map_units S y)).1 h}

variables (M S)

lemma map_eq_zero_iff (r : R) :
  algebra_map R S r = 0 ↔ ∃ m : M, r * m = 0 :=
begin
  split,
  intro h,
  { obtain ⟨m, hm⟩ := (is_localization.eq_iff_exists M S).mp
      ((algebra_map R S).map_zero.trans h.symm),
    exact ⟨m, by simpa using hm.symm⟩ },
  { rintro ⟨m, hm⟩,
    rw [← (is_localization.map_units S m).mul_left_inj, zero_mul, ← ring_hom.map_mul, hm,
      ring_hom.map_zero] }
end

variables {M}

/-- `is_localization.mk' S` is the surjection sending `(x, y) : R × M` to
`f x * (f y)⁻¹`. -/
noncomputable def mk' (x : R) (y : M) : S :=
(to_localization_map M S).mk' x y

@[simp] lemma mk'_sec (z : S) :
  mk' S (is_localization.sec M z).1 (is_localization.sec M z).2 = z :=
(to_localization_map M S).mk'_sec _

lemma mk'_mul (x₁ x₂ : R) (y₁ y₂ : M) :
  mk' S (x₁ * x₂) (y₁ * y₂) = mk' S x₁ y₁ * mk' S x₂ y₂ :=
(to_localization_map M S).mk'_mul _ _ _ _

lemma mk'_one (x) : mk' S x (1 : M) = algebra_map R S x :=
(to_localization_map M S).mk'_one _

@[simp]
lemma mk'_spec (x) (y : M) :
  mk' S x y * algebra_map R S y = algebra_map R S x :=
(to_localization_map M S).mk'_spec _ _

@[simp]
lemma mk'_spec' (x) (y : M) :
  algebra_map R S y * mk' S x y = algebra_map R S x :=
(to_localization_map M S).mk'_spec' _ _

@[simp]
lemma mk'_spec_mk (x) (y : R) (hy : y ∈ M) :
  mk' S x ⟨y, hy⟩ * algebra_map R S y = algebra_map R S x :=
mk'_spec S x ⟨y, hy⟩

@[simp]
lemma mk'_spec'_mk (x) (y : R) (hy : y ∈ M) :
  algebra_map R S y * mk' S x ⟨y, hy⟩ = algebra_map R S x :=
mk'_spec' S x ⟨y, hy⟩

variables {S}

theorem eq_mk'_iff_mul_eq {x} {y : M} {z} :
  z = mk' S x y ↔ z * algebra_map R S y = algebra_map R S x :=
(to_localization_map M S).eq_mk'_iff_mul_eq

theorem mk'_eq_iff_eq_mul {x} {y : M} {z} :
  mk' S x y = z ↔ algebra_map R S x = z * algebra_map R S y :=
(to_localization_map M S).mk'_eq_iff_eq_mul

variables (M)

lemma mk'_surjective (z : S) : ∃ x (y : M), mk' S x y = z :=
let ⟨r, hr⟩ := is_localization.surj _ z in ⟨r.1, r.2, (eq_mk'_iff_mul_eq.2 hr).symm⟩

variables (S)

include M

/-- The localization of a `fintype` is a `fintype`. Cannot be an instance. -/
noncomputable def fintype' [fintype R] : fintype S :=
have _ := classical.prop_decidable, by exactI
fintype.of_surjective (function.uncurry $ is_localization.mk' S)
                      (λ a, prod.exists'.mpr $ is_localization.mk'_surjective M a)

omit M

variables {M S}

lemma mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : M} :
  mk' S x₁ y₁ = mk' S x₂ y₂ ↔ algebra_map R S (x₁ * y₂) = algebra_map R S (x₂ * y₁) :=
(to_localization_map M S).mk'_eq_iff_eq

lemma mk'_mem_iff {x} {y : M} {I : ideal S} : mk' S x y ∈ I ↔ algebra_map R S x ∈ I :=
begin
  split;
  intro h,
  { rw [← mk'_spec S x y, mul_comm],
    exact I.mul_mem_left ((algebra_map R S) y) h },
  { rw ← mk'_spec S x y at h,
    obtain ⟨b, hb⟩ := is_unit_iff_exists_inv.1 (map_units S y),
    have := I.mul_mem_left b h,
    rwa [mul_comm, mul_assoc, hb, mul_one] at this }
end

protected lemma eq {a₁ b₁} {a₂ b₂ : M} :
  mk' S a₁ a₂ = mk' S b₁ b₂ ↔ ∃ c : M, a₁ * b₂ * c = b₁ * a₂ * c :=
(to_localization_map M S).eq

lemma mk'_eq_zero_iff (x : R) (s : M) :
  mk' S x s = 0 ↔ ∃ (m : M), x * m = 0 :=
by rw [← (map_units S s).mul_left_inj, mk'_spec, zero_mul, map_eq_zero_iff M]

@[simp] lemma mk'_zero (s : M) : is_localization.mk' S 0 s = 0 :=
by rw [eq_comm, is_localization.eq_mk'_iff_mul_eq, zero_mul, map_zero]

lemma ne_zero_of_mk'_ne_zero {x : R} {y : M} (hxy : is_localization.mk' S x y ≠ 0) : x ≠ 0 :=
begin
  rintro rfl,
  exact hxy (is_localization.mk'_zero _)
end

section ext

variables [algebra R P] [is_localization M P]

lemma eq_iff_eq {x y} :
  algebra_map R S x = algebra_map R S y ↔ algebra_map R P x = algebra_map R P y :=
(to_localization_map M S).eq_iff_eq (to_localization_map M P)

lemma mk'_eq_iff_mk'_eq {x₁ x₂}
  {y₁ y₂ : M} : mk' S x₁ y₁ = mk' S x₂ y₂ ↔ mk' P x₁ y₁ = mk' P x₂ y₂ :=
(to_localization_map M S).mk'_eq_iff_mk'_eq (to_localization_map M P)

lemma mk'_eq_of_eq {a₁ b₁ : R} {a₂ b₂ : M} (H : b₁ * a₂ = a₁ * b₂) :
  mk' S a₁ a₂ = mk' S b₁ b₂ :=
(to_localization_map M S).mk'_eq_of_eq H

variables (S)

@[simp] lemma mk'_self {x : R} (hx : x ∈ M) : mk' S x ⟨x, hx⟩ = 1 :=
(to_localization_map M S).mk'_self _ hx

@[simp] lemma mk'_self' {x : M} : mk' S (x : R) x = 1 :=
(to_localization_map M S).mk'_self' _

lemma mk'_self'' {x : M} : mk' S x.1 x = 1 :=
mk'_self' _

end ext

lemma mul_mk'_eq_mk'_of_mul (x y : R) (z : M) :
  (algebra_map R S) x * mk' S y z = mk' S (x * y) z :=
(to_localization_map M S).mul_mk'_eq_mk'_of_mul _ _ _

lemma mk'_eq_mul_mk'_one (x : R) (y : M) :
  mk' S x y = (algebra_map R S) x * mk' S 1 y :=
((to_localization_map M S).mul_mk'_one_eq_mk' _ _).symm

@[simp] lemma mk'_mul_cancel_left (x : R) (y : M) :
  mk' S (y * x : R) y = (algebra_map R S) x :=
(to_localization_map M S).mk'_mul_cancel_left _ _

lemma mk'_mul_cancel_right (x : R) (y : M) :
  mk' S (x * y) y = (algebra_map R S) x :=
(to_localization_map M S).mk'_mul_cancel_right _ _

@[simp] lemma mk'_mul_mk'_eq_one (x y : M) :
  mk' S (x : R) y * mk' S (y : R) x = 1 :=
by rw [←mk'_mul, mul_comm]; exact mk'_self _ _

lemma mk'_mul_mk'_eq_one' (x : R) (y : M) (h : x ∈ M) :
  mk' S x y * mk' S (y : R) ⟨x, h⟩ = 1 :=
mk'_mul_mk'_eq_one ⟨x, h⟩ _

section

variables (M)

lemma is_unit_comp (j : S →+* P) (y : M) :
  is_unit (j.comp (algebra_map R S) y) :=
(to_localization_map M S).is_unit_comp j.to_monoid_hom _

end

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →+* P` such that `g(M) ⊆ units P`, `f x = f y → g x = g y` for all `x y : R`. -/
lemma eq_of_eq {g : R →+* P} (hg : ∀ y : M, is_unit (g y)) {x y}
  (h : (algebra_map R S) x = (algebra_map R S) y) :
  g x = g y :=
@submonoid.localization_map.eq_of_eq _ _ _ _ _ _ _
  (to_localization_map M S) g.to_monoid_hom hg _ _ h

lemma mk'_add (x₁ x₂ : R) (y₁ y₂ : M) :
  mk' S (x₁ * y₂ + x₂ * y₁) (y₁ * y₂) = mk' S x₁ y₁ + mk' S x₂ y₂ :=
mk'_eq_iff_eq_mul.2 $ eq.symm
begin
  rw [mul_comm (_ + _), mul_add, mul_mk'_eq_mk'_of_mul, ←eq_sub_iff_add_eq, mk'_eq_iff_eq_mul,
      mul_comm _ ((algebra_map R S) _), mul_sub, eq_sub_iff_add_eq, ←eq_sub_iff_add_eq', ←mul_assoc,
      ←(algebra_map R S).map_mul, mul_mk'_eq_mk'_of_mul, mk'_eq_iff_eq_mul],
  simp only [(algebra_map R S).map_add, submonoid.coe_mul, (algebra_map R S).map_mul],
  ring_exp,
end

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →+* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` sending `z : S` to `g x * (g y)⁻¹`, where `(x, y) : R × M` are such that
`z = f x * (f y)⁻¹`. -/
noncomputable def lift {g : R →+* P} (hg : ∀ y : M, is_unit (g y)) : S →+* P :=
ring_hom.mk' (@submonoid.localization_map.lift _ _ _ _ _ _ _
  (to_localization_map M S) g.to_monoid_hom hg) $
begin
  intros x y,
  rw [(to_localization_map M S).lift_spec, mul_comm, add_mul, ←sub_eq_iff_eq_add, eq_comm,
      (to_localization_map M S).lift_spec_mul, mul_comm _ (_ - _), sub_mul, eq_sub_iff_add_eq',
      ←eq_sub_iff_add_eq, mul_assoc, (to_localization_map M S).lift_spec_mul],
  show g _ * (g _ * g _) = g _ * (g _ * g _ - g _ * g _),
  simp only [← g.map_sub, ← g.map_mul, to_localization_map_sec],
  apply eq_of_eq hg,
  rw [(algebra_map R S).map_mul, sec_spec', mul_sub, (algebra_map R S).map_sub],
  simp only [ring_hom.map_mul, sec_spec'],
  ring,
  assumption
end

variables {g : R →+* P} (hg : ∀ y : M, is_unit (g y))

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : R, y ∈ M`. -/
lemma lift_mk' (x y) :
  lift hg (mk' S x y) = g x * ↑(is_unit.lift_right (g.to_monoid_hom.mrestrict M) hg y)⁻¹ :=
(to_localization_map M S).lift_mk' _ _ _

lemma lift_mk'_spec (x v) (y : M) :
  lift hg (mk' S x y) = v ↔ g x = g y * v :=
(to_localization_map M S).lift_mk'_spec _ _ _ _

@[simp] lemma lift_eq (x : R) :
  lift hg ((algebra_map R S) x) = g x :=
(to_localization_map M S).lift_eq _ _

lemma lift_eq_iff {x y : R × M} :
  lift hg (mk' S x.1 x.2) = lift hg (mk' S y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) :=
(to_localization_map M S).lift_eq_iff _

@[simp] lemma lift_comp : (lift hg).comp (algebra_map R S) = g :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ (to_localization_map M S).lift_comp _

@[simp] lemma lift_of_comp (j : S →+* P) :
  lift (is_unit_comp M j) = j :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ (to_localization_map M S).lift_of_comp j.to_monoid_hom

variables (M)
/-- See note [partially-applied ext lemmas] -/
lemma monoid_hom_ext ⦃j k : S →* P⦄
  (h : j.comp (algebra_map R S : R →* S) = k.comp (algebra_map R S)) : j = k :=
submonoid.localization_map.epic_of_localization_map (to_localization_map M S) $
  monoid_hom.congr_fun h

/-- See note [partially-applied ext lemmas] -/
lemma ring_hom_ext ⦃j k : S →+* P⦄
  (h : j.comp (algebra_map R S) = k.comp (algebra_map R S)) : j = k :=
ring_hom.coe_monoid_hom_injective $ monoid_hom_ext M $ monoid_hom.ext $ ring_hom.congr_fun h

/-- To show `j` and `k` agree on the whole localization, it suffices to show they agree
on the image of the base ring, if they preserve `1` and `*`. -/
protected lemma ext (j k : S → P) (hj1 : j 1 = 1) (hk1 : k 1 = 1)
  (hjm : ∀ a b, j (a * b) = j a * j b) (hkm : ∀ a b, k (a * b) = k a * k b)
  (h : ∀ a, j (algebra_map R S a) = k (algebra_map R S a)) : j = k :=
monoid_hom.mk.inj (monoid_hom_ext M $ monoid_hom.ext h : (⟨j, hj1, hjm⟩ : S →* P) = ⟨k, hk1, hkm⟩)

variables {M}

lemma lift_unique {j : S →+* P}
  (hj : ∀ x, j ((algebra_map R S) x) = g x) : lift hg = j :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ @submonoid.localization_map.lift_unique
  _ _ _ _ _ _ _ (to_localization_map M S) g.to_monoid_hom hg j.to_monoid_hom hj

@[simp] lemma lift_id (x) : lift (map_units S : ∀ y : M, is_unit _) x = x :=
(to_localization_map M S).lift_id _

lemma lift_surjective_iff :
  surjective (lift hg : S → P) ↔ ∀ v : P, ∃ x : R × M, v * g x.2 = g x.1 :=
(to_localization_map M S).lift_surjective_iff hg

lemma lift_injective_iff :
  injective (lift hg : S → P) ↔ ∀ x y, algebra_map R S x = algebra_map R S y ↔ g x = g y :=
(to_localization_map M S).lift_injective_iff hg

section map

variables {T : submonoid P} {Q : Type*} [comm_ring Q] (hy : M ≤ T.comap g)
variables [algebra P Q] [is_localization T Q]

section

variables (Q)

/-- Map a homomorphism `g : R →+* P` to `S →+* Q`, where `S` and `Q` are
localizations of `R` and `P` at `M` and `T` respectively,
such that `g(M) ⊆ T`.

We send `z : S` to `algebra_map P Q (g x) * (algebra_map P Q (g y))⁻¹`, where
`(x, y) : R × M` are such that `z = f x * (f y)⁻¹`. -/
noncomputable def map (g : R →+* P) (hy : M ≤ T.comap g) : S →+* Q :=
@lift R _ M _ _ _ _ _ _ ((algebra_map P Q).comp g) (λ y, map_units _ ⟨g y, hy y.2⟩)

end

lemma map_eq (x) :
  map Q g hy ((algebra_map R S) x) = algebra_map P Q (g x) :=
lift_eq (λ y, map_units _ ⟨g y, hy y.2⟩) x

@[simp] lemma map_comp :
  (map Q g hy).comp (algebra_map R S) = (algebra_map P Q).comp g :=
lift_comp $ λ y, map_units _ ⟨g y, hy y.2⟩

lemma map_mk' (x) (y : M) :
  map Q g hy (mk' S x y) = mk' Q (g x) ⟨g y, hy y.2⟩ :=
@submonoid.localization_map.map_mk' _ _ _ _ _ _ _ (to_localization_map M S)
g.to_monoid_hom _ (λ y, hy y.2) _ _ (to_localization_map T Q) _ _

@[simp] lemma map_id (z : S) (h : M ≤ M.comap (ring_hom.id R) := le_refl M) :
  map S (ring_hom.id _) h z = z :=
lift_id _

lemma map_unique (j : S →+* Q)
  (hj : ∀ x : R, j (algebra_map R S x) = algebra_map P Q (g x)) : map Q g hy = j :=
lift_unique (λ y, map_units _ ⟨g y, hy y.2⟩) hj

/-- If `comm_ring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
lemma map_comp_map {A : Type*} [comm_ring A] {U : submonoid A} {W} [comm_ring W]
  [algebra A W] [is_localization U W] {l : P →+* A} (hl : T ≤ U.comap l) :
  (map W l hl).comp (map Q g hy : S →+* _) = map W (l.comp g) (λ x hx, hl (hy hx)) :=
ring_hom.ext $ λ x, @submonoid.localization_map.map_map _ _ _ _ _ P _ (to_localization_map M S) g _
_ _ _ _ _ _ _ _ _ (to_localization_map U W) l _ x

/-- If `comm_ring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
lemma map_map {A : Type*} [comm_ring A] {U : submonoid A} {W} [comm_ring W]
  [algebra A W] [is_localization U W] {l : P →+* A} (hl : T ≤ U.comap l) (x : S) :
  map W l hl (map Q g hy x) = map W (l.comp g) (λ x hx, hl (hy hx)) x :=
by rw ←map_comp_map hy hl; refl

lemma map_smul (x : S) (z : R) :
  map Q g hy (z • x : S) = g z • map Q g hy x :=
by rw [algebra.smul_def, algebra.smul_def, ring_hom.map_mul, map_eq]

section

variables (S Q)

/-- If `S`, `Q` are localizations of `R` and `P` at submonoids `M, T` respectively, an
isomorphism `j : R ≃+* P` such that `j(M) = T` induces an isomorphism of localizations
`S ≃+* Q`. -/
@[simps]
noncomputable def ring_equiv_of_ring_equiv (h : R ≃+* P) (H : M.map h.to_monoid_hom = T) :
  S ≃+* Q :=
have H' : T.map h.symm.to_monoid_hom = M,
by { rw [← M.map_id, ← H, submonoid.map_map], congr, ext, apply h.symm_apply_apply },
{ to_fun := map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H)),
  inv_fun := map S (h.symm : P →+* R) (T.le_comap_of_map_le (le_of_eq H')),
  left_inv := λ x, by { rw [map_map, map_unique _ (ring_hom.id _), ring_hom.id_apply],
                        intro x, convert congr_arg (algebra_map R S) (h.symm_apply_apply x).symm },
  right_inv := λ x, by { rw [map_map, map_unique _ (ring_hom.id _), ring_hom.id_apply],
                         intro x, convert congr_arg (algebra_map P Q) (h.apply_symm_apply x).symm },
  .. map Q (h : R →+* P) _ }

end

lemma ring_equiv_of_ring_equiv_eq_map {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) :
  (ring_equiv_of_ring_equiv S Q j H : S →+* Q) =
    map Q (j : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) := rfl

@[simp] lemma ring_equiv_of_ring_equiv_eq {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) (x) :
  ring_equiv_of_ring_equiv S Q j H ((algebra_map R S) x) = algebra_map P Q (j x) :=
map_eq _ _

lemma ring_equiv_of_ring_equiv_mk' {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) (x : R) (y : M) :
  ring_equiv_of_ring_equiv S Q j H (mk' S x y) =
    mk' Q (j x) ⟨j y, show j y ∈ T, from H ▸ set.mem_image_of_mem j y.2⟩ :=
map_mk' _ _ _

end map

section alg_equiv

variables {Q : Type*} [comm_ring Q] [algebra R Q] [is_localization M Q]

section

variables (M S Q)

/-- If `S`, `Q` are localizations of `R` at the submonoid `M` respectively,
there is an isomorphism of localizations `S ≃ₐ[R] Q`. -/
@[simps]
noncomputable def alg_equiv : S ≃ₐ[R] Q :=
{ commutes' := ring_equiv_of_ring_equiv_eq _,
  .. ring_equiv_of_ring_equiv S Q (ring_equiv.refl R) M.map_id }

end

@[simp]
lemma alg_equiv_mk' (x : R) (y : M) : alg_equiv M S Q (mk' S x y) = mk' Q x y:=
map_mk' _ _ _

@[simp]
lemma alg_equiv_symm_mk' (x : R) (y : M) : (alg_equiv M S Q).symm (mk' Q x y) = mk' S x y:=
map_mk' _ _ _

end alg_equiv

end is_localization

section

variables (M)

lemma is_localization_of_alg_equiv [algebra R P] [is_localization M S] (h : S ≃ₐ[R] P) :
  is_localization M P :=
begin
  constructor,
  { intro y,
    convert (is_localization.map_units S y).map h.to_alg_hom.to_ring_hom.to_monoid_hom,
    exact (h.commutes y).symm },
  { intro y,
    obtain ⟨⟨x, s⟩, e⟩ := is_localization.surj M (h.symm y),
    apply_fun h at e,
    simp only [h.map_mul, h.apply_symm_apply, h.commutes] at e,
    exact ⟨⟨x, s⟩, e⟩ },
  { intros x y,
    rw [← h.symm.to_equiv.injective.eq_iff, ← is_localization.eq_iff_exists M S,
      ← h.symm.commutes, ← h.symm.commutes],
    refl }
end

lemma is_localization_iff_of_alg_equiv [algebra R P] (h : S ≃ₐ[R] P) :
  is_localization M S ↔ is_localization M P :=
⟨λ _, by exactI is_localization_of_alg_equiv M h,
  λ _, by exactI is_localization_of_alg_equiv M h.symm⟩

lemma is_localization_iff_of_ring_equiv (h : S ≃+* P) :
  is_localization M S ↔
    @@is_localization _ M P _ (h.to_ring_hom.comp $ algebra_map R S).to_algebra :=
begin
  letI := (h.to_ring_hom.comp $ algebra_map R S).to_algebra,
  exact is_localization_iff_of_alg_equiv M { commutes' := λ _, rfl, ..h },
end

variable (S)

lemma is_localization_of_base_ring_equiv [is_localization M S] (h : R ≃+* P) :
  @@is_localization _ (M.map h.to_monoid_hom) S _
    ((algebra_map R S).comp h.symm.to_ring_hom).to_algebra :=
begin
  constructor,
  { rintros ⟨_, ⟨y, hy, rfl⟩⟩,
    convert is_localization.map_units S ⟨y, hy⟩,
    dsimp only [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply],
    exact congr_arg _ (h.symm_apply_apply _) },
  { intro y,
    obtain ⟨⟨x, s⟩, e⟩ := is_localization.surj M y,
    refine ⟨⟨h x, _, _, s.prop, rfl⟩, _⟩,
    dsimp only [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply] at ⊢ e,
    convert e; exact h.symm_apply_apply _ },
  { intros x y,
    rw [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply, ring_hom.comp_apply,
      is_localization.eq_iff_exists M S],
    simp_rw ← h.to_equiv.apply_eq_iff_eq,
    change (∃ (c : M), h (h.symm x * c) = h (h.symm y * c)) ↔ _,
    simp only [ring_equiv.apply_symm_apply, ring_equiv.map_mul],
    exact ⟨λ ⟨c, e⟩, ⟨⟨_, _, c.prop, rfl⟩, e⟩, λ ⟨⟨_, c, h, e₁⟩, e₂⟩, ⟨⟨_, h⟩, e₁.symm ▸ e₂⟩⟩ }
end

lemma is_localization_iff_of_base_ring_equiv (h : R ≃+* P) :
  is_localization M S ↔ @@is_localization _ (M.map h.to_monoid_hom) S _
    ((algebra_map R S).comp h.symm.to_ring_hom).to_algebra :=
begin
  refine ⟨λ _, by exactI is_localization_of_base_ring_equiv _ _ h, _⟩,
  letI := ((algebra_map R S).comp h.symm.to_ring_hom).to_algebra,
  intro H,
  convert @@is_localization_of_base_ring_equiv _ _ _ _ _ _ H h.symm,
  { erw [submonoid.map_equiv_eq_comap_symm, submonoid.comap_map_eq_of_injective],
    exact h.to_equiv.injective },
  rw [ring_hom.algebra_map_to_algebra, ring_hom.comp_assoc],
  simp only [ring_hom.comp_id, ring_equiv.symm_symm, ring_equiv.symm_to_ring_hom_comp_to_ring_hom],
  apply algebra.algebra_ext,
  intro r,
  rw ring_hom.algebra_map_to_algebra
end

end

variables (M S)

include M

lemma non_zero_divisors_le_comap [is_localization M S] :
    non_zero_divisors R ≤ (non_zero_divisors S).comap (algebra_map R S)  :=
begin
  rintros a ha b (e : b * algebra_map R S a = 0),
  obtain ⟨x, s, rfl⟩ := mk'_surjective M b,
  rw [← @mk'_one R _ M, ← mk'_mul, ← (algebra_map R S).map_zero, ← @mk'_one R _ M,
    is_localization.eq] at e,
  obtain ⟨c, e⟩ := e,
  rw [zero_mul, zero_mul, submonoid.coe_one, mul_one, mul_comm x a, mul_assoc, mul_comm] at e,
  rw mk'_eq_zero_iff,
  exact ⟨c, ha _ e⟩
end

lemma map_non_zero_divisors_le [is_localization M S] :
    (non_zero_divisors R).map (algebra_map R S).to_monoid_hom ≤ non_zero_divisors S  :=
submonoid.map_le_iff_le_comap.mpr (non_zero_divisors_le_comap M S)

end is_localization

namespace localization

open is_localization

/-! ### Constructing a localization at a given submonoid -/

variables {M}

section

instance [subsingleton R] : unique (localization M) :=
⟨⟨1⟩, begin intro a, induction a, induction default, congr, refl, refl end⟩

/-- Addition in a ring localization is defined as `⟨a, b⟩ + ⟨c, d⟩ = ⟨b * c + d * a, b * d⟩`.

Should not be confused with `add_localization.add`, which is defined as
`⟨a, b⟩ + ⟨c, d⟩ = ⟨a + c, b + d⟩`.
-/
@[irreducible] protected def add (z w : localization M) : localization M :=
localization.lift_on₂ z w
  (λ a b c d, mk ((b : R) * c + d * a) (b * d)) $
λ a a' b b' c c' d d' h1 h2, mk_eq_mk_iff.2
begin
  rw r_eq_r' at h1 h2 ⊢,
  cases h1 with t₅ ht₅,
  cases h2 with t₆ ht₆,
  use t₆ * t₅,
  calc ((b : R) * c + d * a) * (b' * d') * (t₆ * t₅) =
      (c * d' * t₆) * (b * b' * t₅) + (a * b' * t₅) * (d * d' * t₆) : by ring
      ... = (b' * c' + d' * a') * (b * d) * (t₆ * t₅) : by rw [ht₆, ht₅]; ring
end

instance : has_add (localization M) := ⟨localization.add⟩

lemma add_mk (a b c d) : (mk a b : localization M) + mk c d = mk (b * c + d * a) (b * d) :=
by { unfold has_add.add localization.add, apply lift_on₂_mk }

lemma add_mk_self (a b c) : (mk a b : localization M) + mk c b = mk (a + c) b :=
begin
  rw [add_mk, mk_eq_mk_iff, r_eq_r'],
  refine (r' M).symm ⟨1, _⟩,
  simp only [submonoid.coe_one, submonoid.coe_mul],
  ring
end

/-- Negation in a ring localization is defined as `-⟨a, b⟩ = ⟨-a, b⟩`. -/
@[irreducible] protected def neg (z : localization M) : localization M :=
localization.lift_on z (λ a b, mk (-a) b) $
  λ a b c d h, mk_eq_mk_iff.2
begin
  rw r_eq_r' at h ⊢,
  cases h with t ht,
  use t,
  rw [neg_mul, neg_mul, ht],
  ring_nf,
end

instance : has_neg (localization M) := ⟨localization.neg⟩

lemma neg_mk (a b) : -(mk a b : localization M) = mk (-a) b :=
by { unfold has_neg.neg localization.neg, apply lift_on_mk }

/-- The zero element in a ring localization is defined as `⟨0, 1⟩`.

Should not be confused with `add_localization.zero` which is `⟨0, 0⟩`. -/
@[irreducible] protected def zero : localization M :=
mk 0 1

instance : has_zero (localization M) := ⟨localization.zero⟩

lemma mk_zero (b) : (mk 0 b : localization M) = 0 :=
calc mk 0 b = mk 0 1 : mk_eq_mk_iff.mpr (r_of_eq (by simp))
... = 0 : by  unfold has_zero.zero localization.zero

lemma lift_on_zero {p : Type*} (f : ∀ (a : R) (b : M), p) (H) : lift_on 0 f H = f 0 1 :=
by rw [← mk_zero 1, lift_on_mk]

private meta def tac := `[
{ intros,
  simp only [add_mk, localization.mk_mul, neg_mk, ← mk_zero 1],
  refine mk_eq_mk_iff.mpr (r_of_eq _),
  simp only [submonoid.coe_mul, prod.fst_mul, prod.snd_mul],
  ring }]

instance : comm_ring (localization M) :=
{ zero := 0,
  one  := 1,
  add  := (+),
  mul  := (*),
  npow := localization.npow _,
  nsmul := (•),
  nsmul_zero' := λ x, localization.induction_on x
    (λ x, by simp only [smul_mk, zero_nsmul, mk_zero]),
  nsmul_succ' := λ n x, localization.induction_on x
    (λ x, by simp only [smul_mk, succ_nsmul, add_mk_self]),
  zsmul := (•),
  zsmul_zero' := λ x, localization.induction_on x
    (λ x, by simp only [smul_mk, zero_zsmul, mk_zero]),
  zsmul_succ' := λ n x, localization.induction_on x
    (λ x, by simp [smul_mk, add_mk_self, -mk_eq_monoid_of_mk', add_comm (n : ℤ) 1, add_smul]),
  zsmul_neg' := λ n x, localization.induction_on x
    (λ x, by { rw [smul_mk, smul_mk, neg_mk, ← neg_smul], refl }),
  add_assoc      := λ m n k, localization.induction_on₃ m n k (by tac),
  zero_add       := λ y, localization.induction_on y (by tac),
  add_zero       := λ y, localization.induction_on y (by tac),
  neg            := has_neg.neg,
  sub            := λ x y, x + -y,
  sub_eq_add_neg := λ x y, rfl,
  add_left_neg   := λ y, by exact localization.induction_on y (by tac),
  add_comm       := λ y z, localization.induction_on₂ z y (by tac),
  left_distrib   := λ m n k, localization.induction_on₃ m n k (by tac),
  right_distrib  := λ m n k, localization.induction_on₃ m n k (by tac),
   ..localization.comm_monoid M }

instance {S : Type*} [monoid S] [distrib_mul_action S R] [is_scalar_tower S R R] :
  distrib_mul_action S (localization M) :=
{ smul_zero := λ s, by simp only [←localization.mk_zero 1, localization.smul_mk, smul_zero],
  smul_add := λ s x y, localization.induction_on₂ x y $
    prod.rec $ by exact λ r₁ x₁, prod.rec $ by exact λ r₂ x₂,
      by simp only [localization.smul_mk, localization.add_mk, smul_add, mul_comm _ (s • _),
                    mul_comm _ r₁, mul_comm _ r₂, smul_mul_assoc] }

instance {S : Type*} [semiring S] [mul_semiring_action S R] [is_scalar_tower S R R] :
  mul_semiring_action S (localization M) :=
{ ..localization.mul_distrib_mul_action }

instance {S : Type*} [semiring S] [module S R] [is_scalar_tower S R R] :
  module S (localization M) :=
{ zero_smul := localization.ind $ prod.rec $
    by { intros, simp only [localization.smul_mk, zero_smul, mk_zero] },
  add_smul := λ s₁ s₂, localization.ind $ prod.rec $
    by { intros, simp only [localization.smul_mk, add_smul, add_mk_self] },
  ..localization.distrib_mul_action }

instance {S : Type*} [comm_semiring S] [algebra S R] : algebra S (localization M) :=
{ to_ring_hom :=
  ring_hom.comp
  { to_fun := (monoid_of M).to_map,
    map_zero' := by rw [← mk_zero (1 : M), mk_one_eq_monoid_of_mk],
    map_add' := λ x y,
      by simp only [← mk_one_eq_monoid_of_mk, add_mk, submonoid.coe_one, one_mul, add_comm],
    .. localization.monoid_of M } (algebra_map S R),
  smul_def' := λ s, localization.ind $ prod.rec $ begin
    intros r x,
    dsimp,
    simp only [←mk_one_eq_monoid_of_mk, mk_mul, localization.smul_mk, one_mul, algebra.smul_def],
  end,
  commutes' := λ s, localization.ind $ prod.rec $ begin
    intros r x,
    dsimp,
    simp only [←mk_one_eq_monoid_of_mk, mk_mul, localization.smul_mk, one_mul, mul_one,
               algebra.commutes],
  end }

instance : is_localization M (localization M) :=
{ map_units := (localization.monoid_of M).map_units,
  surj := (localization.monoid_of M).surj,
  eq_iff_exists := λ _ _, (localization.monoid_of M).eq_iff_exists }

end

@[simp] lemma to_localization_map_eq_monoid_of :
  to_localization_map M (localization M) = monoid_of M := rfl

lemma monoid_of_eq_algebra_map (x) :
  (monoid_of M).to_map x = algebra_map R (localization M) x :=
rfl

lemma mk_one_eq_algebra_map (x) : mk x 1 = algebra_map R (localization M) x := rfl

lemma mk_eq_mk'_apply (x y) : mk x y = is_localization.mk' (localization M) x y :=
by rw [mk_eq_monoid_of_mk'_apply, mk', to_localization_map_eq_monoid_of]

@[simp] lemma mk_eq_mk' : (mk : R → M → localization M) = is_localization.mk' (localization M) :=
mk_eq_monoid_of_mk'

variables [is_localization M S]

section

variables (M S)

/-- The localization of `R` at `M` as a quotient type is isomorphic to any other localization. -/
@[simps]
noncomputable def alg_equiv : localization M ≃ₐ[R] S :=
is_localization.alg_equiv M _ _

/-- The localization of a singleton is a singleton. Cannot be an instance due to metavariables. -/
noncomputable def _root_.is_localization.unique (R Rₘ) [comm_ring R] [comm_ring Rₘ]
  (M : submonoid R) [subsingleton R] [algebra R Rₘ] [is_localization M Rₘ] : unique Rₘ :=
have inhabited Rₘ := ⟨1⟩,
by exactI (alg_equiv M Rₘ).symm.injective.unique

end

@[simp] lemma alg_equiv_mk' (x : R) (y : M) :
  alg_equiv M S (mk' (localization M) x y) = mk' S x y :=
alg_equiv_mk' _ _

@[simp] lemma alg_equiv_symm_mk' (x : R) (y : M) :
  (alg_equiv M S).symm (mk' S x y) = mk' (localization M) x y :=
alg_equiv_symm_mk' _ _

lemma alg_equiv_mk (x y) :
  alg_equiv M S (mk x y) = mk' S x y :=
by rw [mk_eq_mk', alg_equiv_mk']

lemma alg_equiv_symm_mk (x : R) (y : M) :
  (alg_equiv M S).symm (mk' S x y) = mk x y :=
by rw [mk_eq_mk', alg_equiv_symm_mk']

end localization

namespace is_localization

variables {R M} (S) {K : Type*} [is_localization M S]

lemma to_map_eq_zero_iff {x : R} (hM : M ≤ non_zero_divisors R) :
  algebra_map R S x = 0 ↔ x = 0 :=
begin
  rw ← (algebra_map R S).map_zero,
  split; intro h,
  { cases (eq_iff_exists M S).mp h with c hc,
    rw zero_mul at hc,
    exact hM c.2 x hc },
  { rw h },
end

protected lemma injective (hM : M ≤ non_zero_divisors R) :
  injective (algebra_map R S) :=
begin
  rw ring_hom.injective_iff (algebra_map R S),
  intros a ha,
  rwa to_map_eq_zero_iff S hM at ha
end

protected lemma to_map_ne_zero_of_mem_non_zero_divisors [nontrivial R]
  (hM : M ≤ non_zero_divisors R) {x : R} (hx : x ∈ non_zero_divisors R) : algebra_map R S x ≠ 0 :=
show (algebra_map R S).to_monoid_with_zero_hom x ≠ 0,
from map_ne_zero_of_mem_non_zero_divisors (algebra_map R S) (is_localization.injective S hM) hx

variables (S M) (Q : Type*) [comm_ring Q] {g : R →+* P} [algebra P Q]

/-- Injectivity of a map descends to the map induced on localizations. -/
lemma map_injective_of_injective
  (hg : function.injective g) [is_localization (M.map g : submonoid P) Q]
  (hM : (M.map g : submonoid P) ≤ non_zero_divisors P) :
  function.injective (map Q g M.le_comap_map : S → Q) :=
begin
  rintros x y hxy,
  obtain ⟨a, b, rfl⟩ := mk'_surjective M x,
  obtain ⟨c, d, rfl⟩ := mk'_surjective M y,
  rw [map_mk' _ a b, map_mk' _ c d, mk'_eq_iff_eq] at hxy,
  refine mk'_eq_iff_eq.2 (congr_arg (algebra_map _ _) (hg _)),
  convert is_localization.injective _ hM hxy; simp,
end

variables {S Q M}

variables (A : Type*) [comm_ring A] [is_domain A]

/-- A `comm_ring` `S` which is the localization of an integral domain `R` at a subset of
non-zero elements is an integral domain.
See note [reducible non-instances]. -/
@[reducible]
theorem is_domain_of_le_non_zero_divisors
  [algebra A S] {M : submonoid A} [is_localization M S]
  (hM : M ≤ non_zero_divisors A) : is_domain S :=
{ eq_zero_or_eq_zero_of_mul_eq_zero :=
    begin
      intros z w h,
      cases surj M z with x hx,
      cases surj M w with y hy,
      have : z * w * algebra_map A S y.2 * algebra_map A S x.2 =
        algebra_map A S x.1 * algebra_map A S y.1,
      by rw [mul_assoc z, hy, ←hx]; ac_refl,
      rw [h, zero_mul, zero_mul, ← (algebra_map A S).map_mul] at this,
      cases eq_zero_or_eq_zero_of_mul_eq_zero ((to_map_eq_zero_iff S hM).mp this.symm) with H H,
      { exact or.inl (eq_zero_of_fst_eq_zero hx H) },
      { exact or.inr (eq_zero_of_fst_eq_zero hy H) },
    end,
  exists_pair_ne := ⟨(algebra_map A S) 0, (algebra_map A S) 1,
                     λ h, zero_ne_one (is_localization.injective S hM h)⟩, }

variables {A}

/-- The localization at of an integral domain to a set of non-zero elements is an integral domain.
See note [reducible non-instances]. -/
@[reducible]
theorem is_domain_localization {M : submonoid A} (hM : M ≤ non_zero_divisors A) :
  is_domain (localization M) :=
is_domain_of_le_non_zero_divisors _ hM

end is_localization

open is_localization

/-- If `R` is a field, then localizing at a submonoid not containing `0` adds no new elements. -/
lemma localization_map_bijective_of_field
  {R Rₘ : Type*} [comm_ring R] [comm_ring Rₘ]
  {M : submonoid R} (hM : (0 : R) ∉ M) (hR : is_field R)
  [algebra R Rₘ] [is_localization M Rₘ] : function.bijective (algebra_map R Rₘ) :=
begin
  letI := hR.to_field R,
  replace hM := le_non_zero_divisors_of_no_zero_divisors hM,
  refine ⟨is_localization.injective _ hM, λ x, _⟩,
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := mk'_surjective M x,
  obtain ⟨n, hn⟩ := hR.mul_inv_cancel (non_zero_divisors.ne_zero $ hM hm),
  exact ⟨r * n, by erw [eq_mk'_iff_mul_eq, ← ring_hom.map_mul, mul_assoc, mul_comm n, hn, mul_one]⟩
end

section algebra

variables {R S} {Rₘ Sₘ : Type*} [comm_ring Rₘ] [comm_ring Sₘ]
variables [algebra R Rₘ] [is_localization M Rₘ]
variables [algebra S Sₘ] [is_localization (algebra.algebra_map_submonoid S M) Sₘ]

section

variables (S M)

/-- Definition of the natural algebra induced by the localization of an algebra.
Given an algebra `R → S`, a submonoid `R` of `M`, and a localization `Rₘ` for `M`,
let `Sₘ` be the localization of `S` to the image of `M` under `algebra_map R S`.
Then this is the natural algebra structure on `Rₘ → Sₘ`, such that the entire square commutes,
where `localization_map.map_comp` gives the commutativity of the underlying maps -/
noncomputable def localization_algebra : algebra Rₘ Sₘ :=
(map Sₘ (algebra_map R S)
    (show _ ≤ (algebra.algebra_map_submonoid S M).comap _, from M.le_comap_map)
  : Rₘ →+* Sₘ).to_algebra

end

lemma algebra_map_mk' (r : R) (m : M) :
  (@algebra_map Rₘ Sₘ _ _ (localization_algebra M S)) (mk' Rₘ r m) =
    mk' Sₘ (algebra_map R S r) ⟨algebra_map R S m, algebra.mem_algebra_map_submonoid_of_mem m⟩ :=
map_mk' _ _ _

variables (Rₘ Sₘ)

/-- Injectivity of the underlying `algebra_map` descends to the algebra induced by localization. -/
lemma localization_algebra_injective (hRS : function.injective (algebra_map R S))
  (hM : algebra.algebra_map_submonoid S M ≤ non_zero_divisors S) :
  function.injective (@algebra_map Rₘ Sₘ _ _ (localization_algebra M S)) :=
is_localization.map_injective_of_injective M Rₘ Sₘ hRS hM

end algebra
