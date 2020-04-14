/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import group_theory.congruence
import algebra.associated
import algebra.punit_instances

/-!
# Localizations of commutative monoids

Localizing a commutative ring at one of its submonoids does not rely on the ring's addition, so
we can generalize localizations to commutative monoids.

We characterize the localization of a commutative monoid `M` at a submonoid `S` up to
isomorphism; that is, a commutative monoid `N` is the localization of `M` at `S` iff we can find a
monoid homomorphism `f : M →* N` satisfying 3 properties:
1. For all `y ∈ S`, `f y` is a unit;
2. For all `z : N`, there exists `(x, y) : M × S` such that `z * f y = f x`;
3. For all `x, y : M`, `f x = f y` iff there exists `c ∈ S` such that `x * c = y * c`.

We also define the quotient of `M × S` by the unique congruence relation (equivalence relation
preserving a binary operation) `r` such that for any other congruence relation `s` on `M × S`
satisfying '`∀ y ∈ S`, `(1, 1) ∼ (y, y)` under `s`', we have that `(x₁, y₁) ∼ (x₂, y₂)` by `s`
whenever `(x₁, y₁) ∼ (x₂, y₂)` by `r`. We show this relation is equivalent to the standard
localization relation.
This defines the localization as a quotient type, but the majority of subsequent lemmas in the file
are given in terms of localizations up to isomorphism, using maps which satisfy the characteristic
predicate.

Given such a localization map `f : M →* N`, we can define the surjection
`monoid_localization.mk` sending `(x, y) : M × S` to `f x * (f y)⁻¹`, and
`monoid_localization.lift`, the homomorphism from `N` induced by a homomorphism from `M` which maps
elements of `S` to invertible elements of the codomain. Similarly, given commutative monoids
`P, Q`, a submonoid `T` of `P` and a localization map for `T` from `P` to `Q`, then a homomorphism
`g : M →* P` such that `g(S) ⊆ T` induces a homomorphism of localizations,
`monoid_localization.map`, from `N` to `Q`.

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

The infimum form of the localization congruence relation is chosen as 'canonical' here, since it
shortens some proofs.

## Tags
localization, monoid localization, quotient monoid, congruence relation, characteristic predicate,
commutative monoid
-/

namespace add_submonoid
variables {M : Type*} [add_comm_monoid M] (S : add_submonoid M) (N : Type*) [add_comm_monoid N]

/-- The type of add_monoid homomorphisms satisfying the characteristic predicate: if `f : M →+ N`
    satisfies this predicate, then `N` is isomorphic to the localization of `M` at `S`. -/
@[nolint has_inhabited_instance] structure localization_map :=
(to_fun : M →+ N)
(map_add_units : ∀ y : S, is_add_unit (to_fun y))
(surj : ∀ z : N, ∃ x : M × S, z + to_fun x.2 = to_fun x.1)
(eq_iff_exists : ∀ x y, to_fun x = to_fun y ↔ ∃ c : S, x + c = y + c)

end add_submonoid

variables {M : Type*} [comm_monoid M] (S : submonoid M) (N : Type*) [comm_monoid N]
          {P : Type*} [comm_monoid P]

namespace submonoid

/-- The type of monoid homomorphisms satisfying the characteristic predicate: if `f : M →* N`
    satisfies this predicate, then `N` is isomorphic to the localization of `M` at `S`. -/
@[nolint has_inhabited_instance] structure localization_map :=
(to_fun : M →* N)
(map_units : ∀ y : S, is_unit (to_fun y))
(surj : ∀ z : N, ∃ x : M × S, z * to_fun x.2 = to_fun x.1)
(eq_iff_exists : ∀ x y, to_fun x = to_fun y ↔ ∃ c : S, x * c = y * c)

attribute [to_additive add_submonoid.localization_map] submonoid.localization_map

namespace localization

/-- The congruence relation on `M × S`, `M` a `comm_monoid` and `S` a submonoid of `M`, whose
    quotient is the localization of `M` at `S`, defined as the unique congruence relation on
    `M × S` such that for any other congruence relation `s` on `M × S` where for all `y ∈ S`,
    `(1, 1) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies
    `(x₁, y₁) ∼ (x₂, y₂)` by `s`. -/
@[to_additive "The congruence relation on `M × S`, `M` an `add_comm_monoid` and `S` an `add_submonoid` of `M`, whose quotient is the localization of `M` at `S`, defined as the unique congruence relation on `M × S` such that for any other congruence relation `s` on `M × S` where for all `y ∈ S`, `(0, 0) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies `(x₁, y₁) ∼ (x₂, y₂)` by `s`."]
def r (S : submonoid M) : con (M × S) :=
Inf {c | ∀ y : S, c 1 (y, y)}

/-- An alternate form of the congruence relation on `M × S`, `M` a `comm_monoid` and `S` a
    submonoid of `M`, whose quotient is the localization of `M` at `S`. Its equivalence to `r` can
    be useful for proofs. -/
@[to_additive "An alternate form of the congruence relation on `M × S`, `M` a `comm_monoid` and `S` a submonoid of `M`, whose quotient is the localization of `M` at `S`. Its equivalence to `r` can be useful for proofs."]
def r' : con (M × S) :=
begin
  refine { r := λ a b : M × S, ∃ c : S, a.1 * b.2 * c = b.1 * a.2 * c,
    iseqv := ⟨λ a, ⟨1, rfl⟩, λ a b ⟨c, hc⟩, ⟨c, hc.symm⟩, _⟩,
    .. },
  { rintros a b c ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩,
    use b.2 * t₁ * t₂,
    simp only [submonoid.coe_mul],
    calc a.1 * c.2 * (b.2 * t₁ * t₂) = a.1 * b.2 * t₁ * c.2 * t₂ : by ac_refl
    ... = b.1 * c.2 * t₂ * a.2 * t₁ : by { rw ht₁, ac_refl }
    ... = c.1 * a.2 * (b.2 * t₁ * t₂) : by { rw ht₂, ac_refl } },
  { rintros a b c d ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩,
    use t₁ * t₂,
    calc (a.1 * c.1) * (b.2 * d.2) * (t₁ * t₂) = (a.1 * b.2 * t₁) * (c.1 * d.2 * t₂) :
      by ac_refl
    ... = (b.1 * d.1) * (a.2 * c.2) * (t₁ * t₂) : by { rw [ht₁, ht₂], ac_refl } }
end

/-- The congruence relation used to localize a `comm_monoid` at a submonoid can be expressed
    equivalently as an infimum (see `localization.r`) or explicitly
    (see `localization.r'`). -/
@[to_additive "The additive congruence relation used to localize an `add_comm_monoid` at a submonoid can be expressed equivalently as an infimum (see `localization.r`) or explicitly (see `localization.r'`)."]
theorem r_eq_r' : r S = r' S :=
le_antisymm (Inf_le $ λ _, ⟨1, by simp⟩) $
  le_Inf $ λ b H ⟨p, q⟩ y ⟨t, ht⟩,
    begin
      rw [← mul_one (p, q), ← mul_one y],
      refine b.trans (b.mul (b.refl _) (H (y.2 * t))) _,
      convert b.symm (b.mul (b.refl y) (H (q * t))); simp only [],
      rw [prod.mk_mul_mk, submonoid.coe_mul, ← mul_assoc, ht, mul_left_comm, mul_assoc],
      refl
    end

variables {S}

@[to_additive]
lemma r_iff_exists {x y : M × S} : r S x y ↔ ∃ c : S, x.1 * y.2 * c = y.1 * x.2 * c :=
by rw r_eq_r' S; refl

end localization

/-- The localization of a `comm_monoid` at one of its submonoids (as a quotient type). -/
@[to_additive "The localization of an `add_comm_monoid` at one of its submonoids (as a quotient type)."]
def localization := (localization.r S).quotient

@[to_additive] instance localization.inhabited :
  inhabited (localization S) :=
con.quotient.inhabited

namespace localization_map

variables {S N}

@[to_additive, ext] lemma ext {f g : localization_map S N} (h : ∀ x, f.1 x = g.1 x) : f = g :=
by cases f; cases g; simp only []; exact monoid_hom.ext h

attribute [ext] add_submonoid.localization_map.ext

@[to_additive] lemma ext_iff {f g : localization_map S N} : f = g ↔ ∀ x, f.1 x = g.1 x :=
⟨λ h x, h ▸ rfl, ext⟩

@[to_additive] lemma to_fun_inj {f g : localization_map S N} (h : f.1 = g.1) : f = g :=
ext $ monoid_hom.ext_iff.1 h

variables (S)

/-- Given a map `f : M →* N`, a section function sending `z : N` to some
    `(x, y) : M × S` such that `f x * (f y)⁻¹ = z` if there always exists such an element. -/
@[to_additive "Given a map `f : M →+ N`, a section function sending `z : N` to some `(x, y) : M × S` such that `f x - f y = z` if there always exists such an element."]
noncomputable def sec (f : M →* N) :=
@classical.epsilon (N → M × S) ⟨λ z, 1⟩ (λ g, ∀ z, z * f (g z).2 = f (g z).1)

variables {S}

@[to_additive] lemma sec_spec {f : M →* N}
  (h : ∀ z : N, ∃ x : M × S, z * f x.2 = f x.1) (z : N) :
  z * f (sec S f z).2 = f (sec S f z).1 :=
@classical.epsilon_spec (N → M × S) (λ g, ∀ z, z * f (g z).2 = f (g z).1)
  ⟨λ y, classical.some $ h y, λ y, classical.some_spec $ h y⟩ z

@[to_additive] lemma sec_spec' {f : M →* N}
  (h : ∀ z : N, ∃ x : M × S, z * f x.2 = f x.1) (z : N) :
  f (sec S f z).1 = f (sec S f z).2 * z :=
by rw [mul_comm, sec_spec h]

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
    `w : M, z : N` and `y ∈ S`, we have `w * (f y)⁻¹ = z ↔ w = f y * z`. -/
@[to_additive "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that `f(S) ⊆ add_units N`, for all `w : M, z : N` and `y ∈ S`, we have `w - f y = z ↔ w = f y + z`."]
lemma mul_inv_left {f : M →* N} (h : ∀ y : S, is_unit (f y))
  (y : S) (w z) : w * ↑(is_unit.lift_right (f.restrict S) h y)⁻¹ = z ↔ w = f y * z :=
by rw mul_comm; convert units.inv_mul_eq_iff_eq_mul _;
  exact (is_unit.coe_lift_right (f.restrict S) h _).symm

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
    `w : M, z : N` and `y ∈ S`, we have `z = w * (f y)⁻¹ ↔ z * f y = w`. -/
@[to_additive "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that `f(S) ⊆ add_units N`, for all `w : M, z : N` and `y ∈ S`, we have `z = w - f y ↔ z + f y = w`."]
lemma mul_inv_right {f : M →* N} (h : ∀ y : S, is_unit (f y))
  (y : S) (w z) : z = w * ↑(is_unit.lift_right (f.restrict S) h y)⁻¹ ↔ z * f y = w :=
by rw [eq_comm, mul_inv_left h, mul_comm, eq_comm]

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that
    `f(S) ⊆ units N`, for all `x₁ x₂ : M` and `y₁, y₂ ∈ S`, we have
    `f x₁ * (f y₁)⁻¹ = f x₂ * (f y₂)⁻¹ ↔ f (x₁ * y₂) = f (x₂ * y₁)`. -/
@[to_additive "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that `f(S) ⊆ add_units N`, for all `x₁ x₂ : M` and `y₁, y₂ ∈ S`, we have `f x₁ - f y₁ = f x₂ - f y₂ ↔ f (x₁ + y₂) = f (x₂ + y₁)`."]
lemma mul_inv {f : M →* N} (h : ∀ y : S, is_unit (f y)) {x₁ x₂} {y₁ y₂ : S} :
  f x₁ * ↑(is_unit.lift_right (f.restrict S) h y₁)⁻¹ =
    f x₂ * ↑(is_unit.lift_right (f.restrict S) h y₂)⁻¹ ↔ f (x₁ * y₂) = f (x₂ * y₁) :=
by rw [mul_inv_right h, mul_assoc, mul_comm _ (f y₂), ←mul_assoc, mul_inv_left h, mul_comm x₂,
  f.map_mul, f.map_mul]

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
    `y, z ∈ S`, we have `(f y)⁻¹ = (f z)⁻¹ → f y = f z`. -/
@[to_additive "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that `f(S) ⊆ add_units N`, for all `y, z ∈ S`, we have `- (f y) = - (f z) → f y = f z`."]
lemma inv_inj {f : M →* N} (hf : ∀ y : S, is_unit (f y)) {y z}
  (h : (is_unit.lift_right (f.restrict S) hf y)⁻¹ = (is_unit.lift_right (f.restrict S) hf z)⁻¹) :
  f y = f z :=
by rw [←mul_one (f y), eq_comm, ←mul_inv_left hf y (f z) 1, h];
  convert units.inv_mul _; exact (is_unit.coe_lift_right (f.restrict S) hf _).symm

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
    `y ∈ S`, `(f y)⁻¹` is unique. -/
@[to_additive "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that `f(S) ⊆ add_units N`, for all `y ∈ S`, `- (f y)` is unique."]
lemma inv_unique {f : M →* N} (h : ∀ y : S, is_unit (f y)) {y : S}
  {z} (H : f y * z = 1) : ↑(is_unit.lift_right (f.restrict S) h y)⁻¹ = z :=
by rw [←one_mul ↑(_)⁻¹, mul_inv_left, ←H]

variables (f : localization_map S N)
/-- Given a localization map `f : M →* N`, the surjection sending `(x, y) : M × S` to
    `f x * (f y)⁻¹`. -/
@[to_additive "Given a localization map `f : M →+ N`, the surjection sending `(x, y) : M × S` to `f x - f y`."]
noncomputable def mk' (f : localization_map S N) (x : M) (y : S) : N :=
f.1 x * ↑(is_unit.lift_right (f.1.restrict S) f.2 y)⁻¹

@[to_additive] lemma mk'_mul (x₁ x₂ : M) (y₁ y₂ : S) :
  f.mk' (x₁ * x₂) (y₁ * y₂) = f.mk' x₁ y₁ * f.mk' x₂ y₂ :=
(mul_inv_left f.2 _ _ _).2 $ show _ = _ * (_ * _ * (_ * _)), by
  rw [←mul_assoc, ←mul_assoc, mul_inv_right f.2, mul_assoc, mul_assoc, mul_comm _ (f.1 x₂),
      ←mul_assoc, ←mul_assoc, mul_inv_right f.2, submonoid.coe_mul, f.1.map_mul, f.1.map_mul];
  ac_refl

@[to_additive] lemma mk'_one (x) : f.mk' x (1 : S) = f.1 x :=
by rw [mk', monoid_hom.map_one]; exact mul_one (f.1 x)

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, for all `z : N` we have that if
    `x : M, y ∈ S` are such that `z * f y = f x`, then `f x * (f y)⁻¹ = z`. -/
@[simp, to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, for all `z : N` we have that if `x : M, y ∈ S` are such that `z + f y = f x`, then `f x - f y = z`."]
lemma mk'_sec (z : N) : f.mk' (sec S f.1 z).1 (sec S f.1 z).2 = z :=
show _ * _ = _, by rw [←sec_spec f.3, mul_inv_left, mul_comm]

@[to_additive] lemma mk'_surjective (z : N) : ∃ x (y : S), f.mk' x y = z :=
⟨(sec S f.1 z).1, (sec S f.1 z).2, f.mk'_sec z⟩

@[to_additive] lemma mk'_spec (x) (y : S) :
  f.mk' x y * f.1 y = f.1 x :=
show _ * _ * _ = _, by rw [mul_assoc, mul_comm _ (f.1 y), ←mul_assoc, mul_inv_left, mul_comm]

@[to_additive] lemma mk'_spec' (x) (y : S) :
  f.1 y * f.mk' x y = f.1 x :=
by rw [mul_comm, mk'_spec]

@[to_additive] theorem eq_mk'_iff_mul_eq {x} {y : S} {z} :
  z = f.mk' x y ↔ z * f.1 y = f.1 x :=
⟨λ H, by rw [H, mk'_spec], λ H, by erw [mul_inv_right, H]; refl⟩

@[to_additive] theorem mk'_eq_iff_eq_mul {x} {y : S} {z} :
  f.mk' x y = z ↔ f.1 x = z * f.1 y :=
by rw [eq_comm, eq_mk'_iff_mul_eq, eq_comm]

@[to_additive] lemma mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : S} :
  f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ f.1 (x₁ * y₂) = f.1 (x₂ * y₁) :=
⟨λ H, by rw [f.1.map_mul, f.mk'_eq_iff_eq_mul.1 H, mul_assoc,
  mul_comm (f.1 _), ←mul_assoc, mk'_spec, f.1.map_mul],
 λ H, by rw [mk'_eq_iff_eq_mul, mk', mul_assoc, mul_comm _ (f.1 y₁), ←mul_assoc,
  ←f.1.map_mul, ←H, f.1.map_mul, mul_inv_right f.2]⟩

@[to_additive] protected lemma eq {a₁ b₁} {a₂ b₂ : S} :
  f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ ∃ c : S, a₁ * b₂ * c = b₁ * a₂ * c :=
f.mk'_eq_iff_eq.trans $ f.4 _ _

@[to_additive] protected lemma eq' {a₁ b₁} {a₂ b₂ : S} :
  f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ localization.r S (a₁, a₂) (b₁, b₂) :=
by rw [f.eq, localization.r_iff_exists]

@[to_additive] lemma eq_iff_eq (g : localization_map S P) {x y} :
  f.1 x = f.1 y ↔ g.1 x = g.1 y :=
(f.4 _ _).trans (g.4 _ _).symm

@[to_additive] lemma mk'_eq_iff_mk'_eq (g : localization_map S P) {x₁ x₂}
  {y₁ y₂ : S} : f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ g.mk' x₁ y₁ = g.mk' x₂ y₂ :=
f.eq'.trans g.eq'.symm

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, for all `x₁ : M` and `y₁ ∈ S`,
    if `x₂ : M, y₂ ∈ S` are such that `f x₁ * (f y₁)⁻¹ * f y₂ = f x₂`, then there exists `c ∈ S`
    such that `x₁ * y₂ * c = x₂ * y₁ * c`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, for all `x₁ : M` and `y₁ ∈ S`, if `x₂ : M, y₂ ∈ S` are such that `(f x₁ - f y₁) + f y₂ = f x₂`, then there exists `c ∈ S` such that `x₁ + y₂ + c = x₂ + y₁ + c`."]
lemma exists_of_sec_mk' (x) (y : S) :
  ∃ c : S, x * (sec S f.1 $ f.mk' x y).2 * c = (sec S f.1 $ f.mk' x y).1 * y * c :=
(f.4 _ _).1 $ f.mk'_eq_iff_eq.1 $ (mk'_sec _ _).symm

@[to_additive] lemma mk'_eq_of_eq {a₁ b₁ : M} {a₂ b₂ : S} (H : b₁ * a₂ = a₁ * b₂) :
  f.mk' a₁ a₂ = f.mk' b₁ b₂ :=
f.mk'_eq_iff_eq.2 $ H ▸ rfl

@[simp, to_additive] lemma mk'_self (y : S) :
  f.mk' (y : M) y = 1 :=
show _ * _ = _, by rw [mul_inv_left, mul_one]

@[simp, to_additive] lemma mk'_self' (x) (H : x ∈ S) :
  f.mk' x ⟨x, H⟩ = 1 :=
by convert mk'_self _ _; refl

@[to_additive] lemma mul_mk'_eq_mk'_of_mul (x₁ x₂) (y : S) :
  f.1 x₁ * f.mk' x₂ y = f.mk' (x₁ * x₂) y :=
by rw [←mk'_one, ←mk'_mul, one_mul]

@[to_additive] lemma mk'_mul_eq_mk'_of_mul (x₁ x₂) (y : S) :
  f.mk' x₂ y * f.1 x₁ = f.mk' (x₁ * x₂) y :=
by rw [mul_comm, mul_mk'_eq_mk'_of_mul]

@[to_additive] lemma mul_mk'_one_eq_mk' (x) (y : S) :
  f.1 x * f.mk' 1 y = f.mk' x y :=
by rw [mul_mk'_eq_mk'_of_mul, mul_one]

@[to_additive] lemma mk'_mul_cancel_right (x : M) (y : S) :
  f.mk' (x * y) y = f.1 x :=
by rw [←mul_mk'_one_eq_mk', f.1.map_mul, mul_assoc, mul_mk'_one_eq_mk', mk'_self, mul_one]

@[to_additive] lemma mk'_mul_cancel_left (x) (y : S) :
  f.mk' ((y : M) * x) y = f.1 x :=
by rw [mul_comm, mk'_mul_cancel_right]

@[to_additive] lemma is_unit_comp (j : N →* P) (y : S) :
  is_unit (j.comp f.1 y) :=
⟨units.map j $ is_unit.lift_right (f.1.restrict S) f.2 y,
  show j _ = j _, from congr_arg j $ (is_unit.coe_lift_right (f.1.restrict S) f.2 _).symm⟩

variables {g : M →* P}

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M` and a map of `comm_monoid`s
    `g : M →* P` such that `g(S) ⊆ units P`, `f x = f y → g x = g y` for all `x y : M`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M` and a map of `add_comm_monoid`s `g : M →+ P` such that `g(S) ⊆ add_units P`, `f x = f y → g x = g y` for all `x y : M`."]
lemma eq_of_eq (hg : ∀ y : S, is_unit (g y)) {x y} (h : f.1 x = f.1 y) :
  g x = g y :=
begin
  obtain ⟨c, hc⟩ := (f.4 _ _).1 h,
  rw [←mul_one (g x), ←is_unit.mul_lift_right_inv (g.restrict S) hg c],
  show _ * (g c * _) = _,
  rw [←mul_assoc, ←g.map_mul, hc, mul_inv_left hg, g.map_mul, mul_comm],
end

/-- Given `comm_monoid`s `M, P`, localization maps `f : M →* N, k : P →* Q` for submonoids
    `S, T` respectively, and `g : M →* P` such that `g(S) ⊆ T`, `f x = f y` implies
    `k (g x) = k (g y)`. -/
@[to_additive "Given `add_comm_monoid`s `M, P`, localization maps `f : M →+ N, k : P →+ Q` for submonoids `S, T` respectively, and `g : M →+ P` such that `g(S) ⊆ T`, `f x = f y` implies `k (g x) = k (g y)`."]
lemma comp_eq_of_eq {T : submonoid P} {Q : Type*} [comm_monoid Q]
  (hg : ∀ y : S, g y ∈ T) (k : localization_map T Q)
  {x y} (h : f.1 x = f.1 y) : k.1 (g x) = k.1 (g y) :=
f.eq_of_eq (λ y : S, show is_unit (k.1.comp g y), from k.2 ⟨g y, hg y⟩) h

variables (hg : ∀ y : S, is_unit (g y))

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M` and a map of `comm_monoid`s
    `g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
    `N` to `P` sending `z : N` to `g x * (g y)⁻¹`, where `(x, y) : M × S` are such that
    `z = f x * (f y)⁻¹`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M` and a map of `add_comm_monoid`s `g : M →+ P` such that `g y` is invertible for all `y : S`, the homomorphism induced from `N` to `P` sending `z : N` to `g x - g y`, where `(x, y) : M × S` are such that `z = f x - f y`."]
noncomputable def lift : N →* P :=
{ to_fun := λ z, g (sec S f.1 z).1 * ↑(is_unit.lift_right (g.restrict S) hg (sec S f.1 z).2)⁻¹,
  map_one' := by rw [mul_inv_left, mul_one]; exact f.eq_of_eq hg (by rw [←sec_spec f.3, one_mul]),
  map_mul' := λ x y, by rw [mul_inv_left hg, ←mul_assoc, ←mul_assoc, mul_inv_right hg,
    mul_comm _ (g (sec S f.1 y).1), ←mul_assoc, ←mul_assoc, mul_inv_right hg];
    repeat { rw ←g.map_mul };
    exact f.eq_of_eq hg (by repeat { rw f.1.map_mul <|> rw sec_spec' f.3 }; ac_refl) }

variables {S g}

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M` and a map of `comm_monoid`s
    `g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
    `N` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : M, y ∈ S`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M` and a map of `add_comm_monoid`s `g : M →+ P` such that `g y` is invertible for all `y : S`, the homomorphism induced from `N` to `P` maps `f x - f y` to `g x - g y` for all `x : M, y ∈ S`."]
lemma lift_mk' (x y) :
  f.lift hg (f.mk' x y) = g x * ↑(is_unit.lift_right (g.restrict S) hg y)⁻¹ :=
(mul_inv hg).2 $ f.eq_of_eq hg $ by
  rw [f.1.map_mul, f.1.map_mul, sec_spec' f.3, mul_assoc, f.mk'_spec, mul_comm]

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
    `g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v : P`, we have
    `f.lift hg z = v ↔ g x = g y * v`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, if an `add_comm_monoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N, v : P`, we have `f.lift hg z = v ↔ g x = g y + v`, where `x : M, y ∈ S` are such that `z + f y = f x`."]
lemma lift_spec (z v) :
  f.lift hg z = v ↔ g (sec S f.1 z).1 = g (sec S f.1 z).2 * v :=
mul_inv_left hg _ _ v

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
    `g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v w : P`, we have
    `f.lift hg z * w = v ↔ g x * w = g y * v`, where `x : M, y ∈ S` are such that
    `z * f y = f x`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, if an `add_comm_monoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N, v w : P`, we have `f.lift hg z + w = v ↔ g x + w = g y + v`, where `x : M, y ∈ S` are such that `z + f y = f x`."]
lemma lift_spec_mul (z w v) :
  f.lift hg z * w = v ↔ g (sec S f.1 z).1 * w = g (sec S f.1 z).2 * v :=
begin
  rw mul_comm,
  show _ * (_ * _) = _ ↔ _,
  rw [←mul_assoc, mul_inv_left hg, mul_comm],
end

@[to_additive] lemma lift_mk'_spec (x v) (y : S) :
  f.lift hg (f.mk' x y) = v ↔ g x = g y * v :=
by rw f.lift_mk' hg; exact mul_inv_left hg _ _ _

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
    `g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
    `f.lift hg z * g y = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, if an `add_comm_monoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N`, we have `f.lift hg z + g y = g x`, where `x : M, y ∈ S` are such that `z + f y = f x`."]
lemma lift_mul_right (z) :
  f.lift hg z * g (sec S f.1 z).2 = g (sec S f.1 z).1 :=
show _ * _ * _ = _, by erw [mul_assoc, is_unit.lift_right_inv_mul, mul_one]

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
    `g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
    `g y * f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, if an `add_comm_monoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N`, we have `g y + f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z + f y = f x`."]
lemma lift_mul_left (z) :
  g (sec S f.1 z).2 * f.lift hg z = g (sec S f.1 z).1 :=
by rw [mul_comm, lift_mul_right]

@[simp, to_additive] lemma lift_eq (x : M) :
  f.lift hg (f.1 x) = g x :=
by rw [lift_spec, ←g.map_mul]; exact f.eq_of_eq hg (by rw [sec_spec' f.3, f.1.map_mul])

@[to_additive] lemma lift_eq_iff {x y : M × S} :
  f.lift hg (f.mk' x.1 x.2) = f.lift hg (f.mk' y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) :=
by rw [lift_mk', lift_mk', mul_inv hg]

@[simp, to_additive] lemma  lift_comp : (f.lift hg).comp f.1 = g :=
by ext; exact f.lift_eq hg _

@[simp, to_additive] lemma lift_of_comp (j : N →* P) :
  f.lift (f.is_unit_comp j) = j :=
begin
  ext,
  rw lift_spec,
  show j _ = j _ * _,
  erw [←j.map_mul, sec_spec' f.3],
end

@[to_additive] lemma epic_of_localization_map {j k : N →* P}
  (h : ∀ a, j.comp f.1 a = k.comp f.1 a) : j = k :=
begin
  rw [←f.lift_of_comp j, ←f.lift_of_comp k],
  congr' 1,
  ext,
  exact h x,
end

@[to_additive] lemma lift_unique {j : N →* P}
  (hj : ∀ x, j (f.1 x) = g x) : f.lift hg = j :=
begin
  ext,
  rw [lift_spec, ←hj, ←hj, ←j.map_mul],
  apply congr_arg,
  rw ←sec_spec' f.3,
end

@[simp, to_additive] lemma lift_id (x) : f.lift f.2 x = x :=
monoid_hom.ext_iff.1 (f.lift_of_comp $ monoid_hom.id N) x

/-- Given two localization maps `f : M →* N, k : M →* P` for a submonoid `S ⊆ M`,
    the hom from `P` to `N` induced by `f` is left inverse to the hom from `N` to `P`
    induced by `k`. -/
@[simp, to_additive] lemma lift_left_inverse {k : localization_map S P} (z : N) :
  k.lift f.2 (f.lift k.2 z) = z :=
begin
  rw lift_spec,
  cases f.3 z with x hx,
  conv_rhs {congr, skip, rw f.eq_mk'_iff_mul_eq.2 hx},
  rw [mk', ←mul_assoc, mul_inv_right f.2, ←f.1.map_mul, ←f.1.map_mul],
  apply k.eq_of_eq f.2,
  rw [k.1.map_mul, k.1.map_mul, ←sec_spec k.3, mul_assoc, lift_spec_mul],
  repeat { rw ←k.1.map_mul },
  apply f.eq_of_eq k.2,
  repeat { rw f.1.map_mul },
  rw [sec_spec' f.3, ←hx],
  ac_refl,
end

@[to_additive] lemma lift_surjective_iff :
  function.surjective (f.lift hg) ↔ ∀ v : P, ∃ x : M × S, v * g x.2 = g x.1 :=
begin
  split,
    { intros H v,
      obtain ⟨z, hz⟩ := H v,
      obtain ⟨x, hx⟩ := f.3 z,
      use x,
      rw [←hz, f.eq_mk'_iff_mul_eq.2 hx, lift_mk', mul_assoc, mul_comm _ (g ↑x.2)],
      erw [is_unit.mul_lift_right_inv (g.restrict S) hg, mul_one] },
  { intros H v,
    obtain ⟨x, hx⟩ := H v,
    use f.mk' x.1 x.2,
    rw [lift_mk', mul_inv_left hg, mul_comm, ←hx] }
end

@[to_additive] lemma lift_injective_iff :
  function.injective (f.lift hg) ↔ ∀ x y, f.1 x = f.1 y ↔ g x = g y :=
begin
  split,
    { intros H x y,
      split,
        { exact f.eq_of_eq hg },
      { intro h,
        rw [←f.lift_eq hg, ←f.lift_eq hg] at h,
        exact H h }},
  { intros H z w h,
    obtain ⟨x, hx⟩ := f.3 z,
    obtain ⟨y, hy⟩ := f.3 w,
    rw [←f.mk'_sec z, ←f.mk'_sec w],
    exact (mul_inv f.2).2 ((H _ _).2 $ (mul_inv hg).1 h) }
end

variables {T : submonoid P} (hy : ∀ y : S, g y ∈ T) {Q : Type*} [comm_monoid Q]
          (k : localization_map T Q)

/-- Given a `comm_monoid` homomorphism `g : M →* P` where for submonoids `S ⊆ M, T ⊆ P` we have
    `g(S) ⊆ T`, the induced monoid homomorphism from the localization of `M` at `S` to the
    localization of `P` at `T`: if `f : M →* N` and `k : P →* Q` are localization maps for `S` and
    `T` respectively, we send `z : N` to `k (g x) * (k (g y))⁻¹`, where `(x, y) : M × S` are such
    that `z = f x * (f y)⁻¹`. -/
@[to_additive "Given a `add_comm_monoid` homomorphism `g : M →+ P` where for submonoids `S ⊆ M, T ⊆ P` we have `g(S) ⊆ T`, the induced add_monoid homomorphism from the localization of `M` at `S` to the localization of `P` at `T`: if `f : M →+ N` and `k : P →+ Q` are localization maps for `S` and `T` respectively, we send `z : N` to `k (g x) - k (g y)`, where `(x, y) : M × S` are such that `z = f x - f y`."]
noncomputable def map : N →* Q :=
@lift _ _ _ _ _ _ _ f (k.1.comp g) $ λ y, k.2 ⟨g y, hy y⟩

variables {k}

@[to_additive] lemma map_eq (x) :
  f.map hy k (f.1 x) = k.1 (g x) := f.lift_eq (λ y, k.2 ⟨g y, hy y⟩) x

@[simp, to_additive] lemma map_comp :
  (f.map hy k).comp f.1 = k.1.comp g := f.lift_comp $ λ y, k.2 ⟨g y, hy y⟩

@[to_additive] lemma map_mk' (x) (y : S) :
  f.map hy k (f.mk' x y) = k.mk' (g x) ⟨g y, hy y⟩ :=
begin
  rw [map, lift_mk', mul_inv_left],
  { show k.1 (g x) = k.1 (g y) * _,
    rw mul_mk'_eq_mk'_of_mul,
    exact (k.mk'_mul_cancel_left (g x) ⟨(g y), hy y⟩).symm },
end

/-- Given localization maps `f : M →* N, k : P →* Q` for submonoids `S, T` respectively, if a
    `comm_monoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
    `u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) * u` where `x : M, y ∈ S` are such that
    `z * f y = f x`. -/
@[to_additive "Given localization maps `f : M →+ N, k : P →+ Q` for submonoids `S, T` respectively, if an `add_comm_monoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`, `u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) + u` where `x : M, y ∈ S` are such that `z + f y = f x`."]
lemma map_spec (z u) :
  f.map hy k z = u ↔ k.1 (g (sec S f.1 z).1) = k.1 (g (sec S f.1 z).2) * u :=
f.lift_spec (λ y, k.2 ⟨g y, hy y⟩) _ _

/-- Given localization maps `f : M →* N, k : P →* Q` for submonoids `S, T` respectively, if a
    `comm_monoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
    we have `f.map hy k z * k (g y) = k (g x)` where `x : M, y ∈ S` are such that
    `z * f y = f x`. -/
@[to_additive "Given localization maps `f : M →+ N, k : P →+ Q` for submonoids `S, T` respectively, if an `add_comm_monoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`, we have `f.map hy k z + k (g y) = k (g x)` where `x : M, y ∈ S` are such that `z + f y = f x`."]
lemma map_mul_right (z) :
  f.map hy k z * (k.1 (g (sec S f.1 z).2)) = k.1 (g (sec S f.1 z).1) :=
f.lift_mul_right (λ y, k.2 ⟨g y, hy y⟩) _

/-- Given localization maps `f : M →* N, k : P →* Q` for submonoids `S, T` respectively, if a
    `comm_monoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
    we have `k (g y) * f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that
    `z * f y = f x`. -/
@[to_additive "Given localization maps `f : M →+ N, k : P →+ Q` for submonoids `S, T` respectively, if an `add_comm_monoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`, we have `k (g y) + f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that `z + f y = f x`."]
lemma map_mul_left (z) :
  k.1 (g (sec S f.1 z).2) * f.map hy k z = k.1 (g (sec S f.1 z).1) :=
by rw [mul_comm, f.map_mul_right]

@[simp, to_additive] lemma map_id (z : N) :
  f.map (λ y, show monoid_hom.id M y ∈ S, from y.2) f z = z :=
f.lift_id z

/-- If `comm_monoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
    of the induced maps equals the map of localizations induced by `l ∘ g`. -/
@[to_additive "If `add_comm_monoid` homs `g : M →+ P, l : P →+ A` induce maps of localizations, the composition of the induced maps equals the map of localizations induced by `l ∘ g`."]
lemma map_comp_map {A : Type*} [comm_monoid A] {U : submonoid A} {R} [comm_monoid R]
  (j : localization_map U R) {l : P →* A} (hl : ∀ w : T, l w ∈ U) :
  (k.map hl j).comp (f.map hy k) = f.map (λ x, show l.comp g x ∈ U, from hl ⟨g x, hy x⟩) j :=
begin
  ext z,
  show j.1 _ * _ = j.1 (l _) * _,
  { rw [mul_inv_left, ←mul_assoc, mul_inv_right],
    show j.1 _ * j.1 (l (g _)) = j.1 (l _) * _,
    rw [←j.1.map_mul, ←j.1.map_mul, ←l.map_mul, ←l.map_mul],
    exact k.comp_eq_of_eq hl j
      (by rw [k.1.map_mul, k.1.map_mul, sec_spec' k.3, mul_assoc, map_mul_right]) },
end

/-- If `comm_monoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
    of the induced maps equals the map of localizations induced by `l ∘ g`. -/
@[to_additive "If `add_comm_monoid` homs `g : M →+ P, l : P →+ A` induce maps of localizations, the composition of the induced maps equals the map of localizations induced by `l ∘ g`."]
lemma map_map {A : Type*} [comm_monoid A] {U : submonoid A} {R} [comm_monoid R]
  (j : localization_map U R) {l : P →* A} (hl : ∀ w : T, l w ∈ U) (x) :
  k.map hl j (f.map hy k x) = f.map (λ x, show l.comp g x ∈ U, from hl ⟨g x, hy x⟩) j x :=
by rw ←f.map_comp_map hy j hl; refl

variables {g}

/-- If `f : M →* N` and `k : M →* R` are localization maps for a submonoid `S`, we get an
    isomorphism of `N` and `R`. -/
@[to_additive "If `f : M →+ N` and `k : M →+ R` are localization maps for a submonoid `S`, we get an isomorphism of `N` and `R`."]
noncomputable def mul_equiv_of_localizations
  (k : localization_map S P) : N ≃* P :=
⟨f.lift k.2, k.lift f.2, f.lift_left_inverse, k.lift_left_inverse, monoid_hom.map_mul _⟩

@[to_additive, simp] lemma mul_equiv_of_localizations_apply
  {k : localization_map S P} {x} : f.mul_equiv_of_localizations k x = f.lift k.2 x := rfl

@[to_additive, simp] lemma mul_equiv_of_localizations_symm_apply
  {k : localization_map S P} {x} : (f.mul_equiv_of_localizations k).symm x = k.lift f.2 x := rfl

/-- If `f : M →* N` is a localization map for a submonoid `S` and `k : N ≃* P` is an isomorphism
    of `comm_monoid`s, `k ∘ f` is a localization map for `M` at `S`. -/
@[to_additive "If `f : M →+ N` is a localization map for a submonoid `S` and `k : N ≃+ P` is an isomorphism of `add_comm_monoid`s, `k ∘ f` is a localization map for `M` at `S`."]
def to_mul_equiv (k : N ≃* P) :
  localization_map S P :=
{ to_fun := k.to_monoid_hom.comp f.1,
  map_units := λ y, is_unit_comp f k.to_monoid_hom y,
  surj := λ v, let ⟨z, hz⟩ := k.to_equiv.surjective v in
    let ⟨x, hx⟩ := f.3 z in ⟨x, show v * k _ = k _, by rw [←hx, k.map_mul, ←hz]; refl⟩,
  eq_iff_exists := λ x y, (k.to_equiv.apply_eq_iff_eq _ _).trans $ f.4 _ _ }

@[to_additive, simp] lemma to_mul_equiv_apply {k : N ≃* P} (x) :
  (f.to_mul_equiv k).1 x = k (f.1 x) := rfl

@[to_additive, simp] lemma to_mul_equiv_eq {k : N ≃* P} :
  (f.to_mul_equiv k).1 = k.to_monoid_hom.comp f.1 := rfl

@[to_additive] lemma symm_to_mul_equiv_apply {k : N ≃* P} (x) :
  k.symm ((f.to_mul_equiv k).1 x) = f.1 x := k.symm_apply_apply (f.1 x)

@[to_additive] lemma comp_mul_equiv_symm_map_apply {k : P ≃* N} (x) :
  k ((f.to_mul_equiv k.symm).1 x) = f.1 x := k.apply_symm_apply (f.1 x)

@[to_additive] lemma to_mul_equiv_eq_iff_eq {k : N ≃* P} {x y} :
  (f.to_mul_equiv k).1 x = y ↔ f.1 x = k.symm y :=
k.to_equiv.eq_symm_apply.symm

@[to_additive] lemma mul_equiv_of_to_mul_equiv (k : localization_map S P) :
  f.to_mul_equiv (f.mul_equiv_of_localizations k) = k :=
to_fun_inj $ f.lift_comp k.2

@[to_additive] lemma mul_equiv_of_to_mul_equiv_apply {k : localization_map S P} {x} :
  (f.to_mul_equiv (f.mul_equiv_of_localizations k)).1 x = k.1 x :=
ext_iff.1 (f.mul_equiv_of_to_mul_equiv k) x

@[to_additive] lemma to_mul_equiv_of_mul_equiv (k : N ≃* P) :
  f.mul_equiv_of_localizations (f.to_mul_equiv k) = k :=
mul_equiv.ext $ monoid_hom.ext_iff.1 $ f.lift_of_comp k.to_monoid_hom

@[to_additive] lemma to_mul_equiv_of_mul_equiv_apply {k : N ≃* P} (x) :
  f.mul_equiv_of_localizations (f.to_mul_equiv k) x = k x :=
by rw to_mul_equiv_of_mul_equiv

@[simp, to_additive] lemma to_mul_equiv_id :
  f.to_mul_equiv (mul_equiv.refl N) = f :=
by ext; refl

@[to_additive] lemma to_mul_equiv_comp {k : N ≃* P} {j : P ≃* Q} :
  (f.to_mul_equiv (k.trans j)).1 = j.to_monoid_hom.comp (f.to_mul_equiv k).1 :=
by ext; refl

/-- Given `comm_monoid`s `M, P` and submonoids `S ⊆ M, T ⊆ P`, if `f : M →* N` is a localization
    map for `S` and `k : P ≃* M` is an isomorphism of `comm_monoid`s such that `k(T) = S`, `f ∘ k`
    is a localization map for `T`. -/
@[to_additive "Given `comm_monoid`s `M, P` and submonoids `S ⊆ M, T ⊆ P`, if `f : M →* N` is a localization map for `S` and `k : P ≃* M` is an isomorphism of `comm_monoid`s such that `k(T) = S`, `f ∘ k` is a localization map for `T`."]
def of_mul_equiv {k : P ≃* M} (H : T.map k.to_monoid_hom = S) :
  localization_map T N :=
let H' : S.comap k.to_monoid_hom = T :=
  H ▸ (submonoid.ext' $ T.1.preimage_image_eq k.to_equiv.injective) in
{ to_fun := f.1.comp k.to_monoid_hom,
  map_units := λ y, let ⟨z, hz⟩ := f.2 ⟨k y, H ▸ set.mem_image_of_mem k y.2⟩ in ⟨z, hz⟩,
  surj := λ z, let ⟨x, hx⟩ := f.3 z in let ⟨v, hv⟩ := k.to_equiv.surjective x.1 in
    let ⟨w, hw⟩ := k.to_equiv.surjective x.2 in ⟨(v, ⟨w, H' ▸ show k w ∈ S, from hw.symm ▸ x.2.2⟩),
    show z * f.1 (k.to_equiv w) = f.1 (k.to_equiv v), by erw [hv, hw, hx]; refl⟩,
  eq_iff_exists := λ x y, show f.1 _ = f.1 _ ↔ _, by erw f.4;
    exact ⟨λ ⟨c, hc⟩, let ⟨d, hd⟩ := k.to_equiv.surjective c in
    ⟨⟨d, H' ▸ show k d ∈ S, from hd.symm ▸ c.2⟩, by erw [←hd, ←k.map_mul, ←k.map_mul] at hc;
      exact k.to_equiv.injective hc⟩, λ ⟨c, hc⟩, ⟨⟨k c, H ▸ set.mem_image_of_mem k c.2⟩,
    by erw ←k.map_mul; rw [hc, k.map_mul]; refl⟩⟩ }

@[to_additive, simp] lemma of_mul_equiv_apply {k : P ≃* M} (H : T.map k.to_monoid_hom = S) (x) :
  (f.of_mul_equiv H).1 x = f.1 (k x) := rfl

@[to_additive, simp] lemma of_mul_equiv_eq {k : P ≃* M} (H : T.map k.to_monoid_hom = S) :
  (f.of_mul_equiv H).1 = f.1.comp k.to_monoid_hom := rfl

@[to_additive] lemma symm_of_mul_equiv_apply {k : P ≃* M}
  (H : T.map k.to_monoid_hom = S) (x) :
  (f.of_mul_equiv H).1 (k.symm x) = f.1 x := congr_arg f.1 $ k.apply_symm_apply x

@[to_additive, simp] lemma comp_mul_equiv_symm_comap_apply {k : M ≃* P}
  (H : T.map k.symm.to_monoid_hom = S) (x) :
  (f.of_mul_equiv H).1 (k x) = f.1 x := congr_arg f.1 $ k.symm_apply_apply x

/-- A special case of `f ∘ id = f`, `f` a localization map. -/
@[simp, to_additive "A special case of `f ∘ id = f`, `f` a localization map."]
lemma of_mul_equiv_id :
  f.of_mul_equiv (show S.map (mul_equiv.refl M).to_monoid_hom = S, from
    submonoid.ext $ λ x, ⟨λ ⟨y, hy, h⟩, h ▸ hy, λ h, ⟨x, h, rfl⟩⟩) = f :=
by ext; refl

/-- Given localization maps `f : M →* N, k : P →* U` for submonoids `S, T` respectively, an
    isomorphism `j : M ≃* P` such that `j(S) = T` induces an isomorphism of localizations
    `N ≃* U`. -/
@[to_additive "Given localization maps `f : M →+ N, k : P →+ U` for submonoids `S, T` respectively, an isomorphism `j : M ≃+ P` such that `j(S) = T` induces an isomorphism of localizations `N ≃+ U`."]
noncomputable def mul_equiv_of_mul_equiv
  (k : localization_map T Q) {j : M ≃* P} (H : S.map j.to_monoid_hom = T) :
  N ≃* Q :=
f.mul_equiv_of_localizations $ k.of_mul_equiv H

@[to_additive, simp] lemma mul_equiv_of_mul_equiv_eq_map_apply
  {k : localization_map T Q} {j : M ≃* P} (H : S.map j.to_monoid_hom = T) (x) :
  f.mul_equiv_of_mul_equiv k H x =
    f.map (λ y : S, show j.to_monoid_hom y ∈ T, from H ▸ set.mem_image_of_mem j y.2) k x := rfl

@[to_additive, simp] lemma mul_equiv_of_mul_equiv_eq_map
  {k : localization_map T Q} {j : M ≃* P} (H : S.map j.to_monoid_hom = T) :
  (f.mul_equiv_of_mul_equiv k H).to_monoid_hom =
    f.map (λ y : S, show j.to_monoid_hom y ∈ T, from H ▸ set.mem_image_of_mem j y.2) k := rfl

@[to_additive, simp] lemma mul_equiv_of_mul_equiv_eq {k : localization_map T Q}
  {j : M ≃* P} (H : S.map j.to_monoid_hom = T) (x) :
  f.mul_equiv_of_mul_equiv k H (f.1 x) = k.1 (j x) :=
f.map_eq (λ y : S, H ▸ set.mem_image_of_mem j y.2) _

@[to_additive] lemma mul_equiv_of_mul_equiv_mk' {k : localization_map T Q}
  {j : M ≃* P} (H : S.map j.to_monoid_hom = T) (x y) :
  f.mul_equiv_of_mul_equiv k H (f.mk' x y) = k.mk' (j x) ⟨j y, H ▸ set.mem_image_of_mem j y.2⟩ :=
f.map_mk' (λ y : S, H ▸ set.mem_image_of_mem j y.2) _ _

@[to_additive, simp] lemma to_mul_equiv_of_mul_equiv_of_mul_equiv_apply
  {k : localization_map T Q} {j : M ≃* P} (H : S.map j.to_monoid_hom = T) (x) :
  (f.to_mul_equiv (f.mul_equiv_of_mul_equiv k H)).1 x = k.1 (j x) :=
ext_iff.1 (f.mul_equiv_of_to_mul_equiv (k.of_mul_equiv H)) x

@[to_additive, simp] lemma to_mul_equiv_of_mul_equiv_of_mul_equiv
  {k : localization_map T Q} {j : M ≃* P} (H : S.map j.to_monoid_hom = T) :
  (f.to_mul_equiv (f.mul_equiv_of_mul_equiv k H)).1 = k.1.comp j.to_monoid_hom :=
monoid_hom.ext $ f.to_mul_equiv_of_mul_equiv_of_mul_equiv_apply H

end localization_map
end submonoid