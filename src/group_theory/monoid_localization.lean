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
lattice.Inf {c | ∀ y : S, c 1 (y, y)}

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
le_antisymm (lattice.Inf_le $ λ _, ⟨1, by simp⟩) $
  lattice.le_Inf $ λ b H ⟨p, q⟩ y ⟨t, ht⟩,
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

variables (S) {N}

/-- Given a map `f : M →* N`, a section function sending `z : N` to some
    `(x, y) : M × S` such that `f x * (f y)⁻¹ = z` if there always exists such an element. -/
@[to_additive "Given a map `f : M →+ N`, a section function sending `z : N` to some `(x, y) : M × S` such that `f x - f y = z` if there always exists such an element."]
noncomputable def sec (f : M →* N) :=
@classical.epsilon (N → M × S) ⟨λ z, 1⟩ (λ g, ∀ z, z * f (g z).2 = f (g z).1)

variables {S}

@[simp, to_additive] lemma sec_spec {f : M →* N}
  (h : ∀ z : N, ∃ x : M × S, z * f x.2 = f x.1) (z : N) :
  z * f (sec S f z).2 = f (sec S f z).1 :=
@classical.epsilon_spec (N → M × S) (λ g, ∀ z, z * f (g z).2 = f (g z).1)
  ⟨λ y, classical.some $ h y, λ y, classical.some_spec $ h y⟩ z

@[simp, to_additive] lemma sec_spec' {f : M →* N}
  (h : ∀ z : N, ∃ x : M × S, z * f x.2 = f x.1) (z : N) :
  f (sec S f z).1 = f (sec S f z).2 * z :=
by rw [mul_comm, sec_spec h]

@[simp, to_additive] lemma mul_inv_left {f : M →* N} (h : ∀ y : S, is_unit (f y))
  (y : S) (w z) : w * ↑(is_unit.lift_right (f.restrict S) h y)⁻¹ = z ↔ w = f y * z :=
by rw mul_comm; convert units.inv_mul_eq_iff_eq_mul _;
  exact (is_unit.coe_lift_right (f.restrict S) h _).symm

@[simp, to_additive] lemma mul_inv_right {f : M →* N} (h : ∀ y : S, is_unit (f y))
  (y : S) (w z) : z = w * ↑(is_unit.lift_right (f.restrict S) h y)⁻¹ ↔ z * f y = w :=
by rw [eq_comm, mul_inv_left h, mul_comm, eq_comm]

@[simp, to_additive] lemma mul_inv {f : M →* N} (h : ∀ y : S, is_unit (f y)) {x₁ x₂} {y₁ y₂ : S} :
  f x₁ * ↑(is_unit.lift_right (f.restrict S) h y₁)⁻¹ =
    f x₂ * ↑(is_unit.lift_right (f.restrict S) h y₂)⁻¹ ↔ f (x₁ * y₂) = f (x₂ * y₁) :=
by rw [mul_inv_right h, mul_assoc, mul_comm _ (f y₂), ←mul_assoc, mul_inv_left h, mul_comm x₂,
  f.map_mul, f.map_mul]

@[to_additive] lemma inv_inj {f : M →* N} (hf : ∀ y : S, is_unit (f y)) {y z}
  (h : (is_unit.lift_right (f.restrict S) hf y)⁻¹ = (is_unit.lift_right (f.restrict S) hf z)⁻¹) :
  f y = f z :=
by rw [←mul_one (f y), eq_comm, ←mul_inv_left hf y (f z) 1, h];
  convert units.inv_mul _; exact (is_unit.coe_lift_right (f.restrict S) hf _).symm

@[to_additive] lemma inv_unique {f : M →* N} (h : ∀ y : S, is_unit (f y)) {y : S}
  {z} (H : f y * z = 1) : ↑(is_unit.lift_right (f.restrict S) h y)⁻¹ = z :=
by rw [←one_mul ↑(_)⁻¹, mul_inv_left, ←H]

variables (f : localization_map S N)
/-- Given a localization map `f : M →* N`, the surjection sending `(x, y) : M × S` to
    `f x * (f y)⁻¹`. -/
@[to_additive "Given a localization map `f : M →+ N`, the surjection sending `(x, y) : M × S` to `f x - f y`."]
noncomputable def mk' (f : localization_map S N) (x : M) (y : S) : N :=
f.1 x * ↑(is_unit.lift_right (f.1.restrict S) f.2 y)⁻¹

@[simp, to_additive] lemma mk'_mul (x₁ x₂ : M) (y₁ y₂ : S) :
  f.mk' (x₁ * x₂) (y₁ * y₂) = f.mk' x₁ y₁ * f.mk' x₂ y₂ :=
(mul_inv_left f.2 _ _ _).2 $ show _ = _ * (_ * _ * (_ * _)), by
  rw [←mul_assoc, ←mul_assoc, mul_inv_right f.2, mul_assoc, mul_assoc, mul_comm _ (f.1 x₂),
      ←mul_assoc, ←mul_assoc, mul_inv_right f.2, submonoid.coe_mul, f.1.map_mul, f.1.map_mul];
  ac_refl

@[to_additive] lemma mk'_one (x) : f.mk' x (1 : S) = f.1 x :=
by rw [mk', monoid_hom.map_one]; simp

@[simp, to_additive] lemma mk'_sec (z : N) : f.mk' (sec S f.1 z).1 (sec S f.1 z).2 = z :=
show _ * _ = _, by rw [←sec_spec f.3, mul_inv_left, mul_comm]

@[to_additive] lemma mk'_surjective (z : N) : ∃ x (y : S), f.mk' x y = z :=
⟨(sec S f.1 z).1, (sec S f.1 z).2, f.mk'_sec z⟩

@[to_additive] lemma mk'_spec (x) (y : S) :
  f.mk' x y * f.1 y = f.1 x :=
show _ * _ * _ = _, by rw [mul_assoc, mul_comm _ (f.1 y), ←mul_assoc, mul_inv_left, mul_comm]

@[to_additive] lemma mk'_spec' (x) (y : S) :
  f.1 y * f.mk' x y = f.1 x :=
by rw [mul_comm, mk'_spec]

@[simp, to_additive] theorem eq_mk'_iff_mul_eq {x} {y : S} {z} :
  z = f.mk' x y ↔ z * f.1 y = f.1 x :=
⟨λ H, by rw [H, mk'_spec], λ H, by erw [mul_inv_right, H]; refl⟩

@[simp, to_additive] theorem mk'_eq_iff_eq_mul {x} {y : S} {z} :
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

@[to_additive] lemma exists_of_sec_mk' (x) (y : S) :
  ∃ c : S, x * (sec S f.1 $ f.mk' x y).2 * c = (sec S f.1 $ f.mk' x y).1 * y * c :=
(f.4 _ _).1 $ f.mk'_eq_iff_eq.1 $ (mk'_sec _ _).symm

@[to_additive] lemma exists_of_sec (x) :
  ∃ c : S, x * (sec S f.1 $ f.1 x).2 * c = (sec S f.1 $ f.1 x).1 * c :=
(f.4 _ _).1 $ by rw f.1.map_mul; exact sec_spec f.3 _

@[to_additive] lemma mk'_eq_of_eq {a₁ b₁ : M} {a₂ b₂ : S} (H : b₁ * a₂ = a₁ * b₂) :
  f.mk' a₁ a₂ = f.mk' b₁ b₂ :=
f.mk'_eq_iff_eq.2 $ H ▸ rfl

@[simp, to_additive] lemma mk'_self (y : S) :
  f.mk' (y : M) y = 1 :=
show _ * _ = _, by rw [mul_inv_left, mul_one]

@[simp, to_additive] lemma mk'_self' (x) (H : x ∈ S) :
  f.mk' x ⟨x, H⟩ = 1 :=
by convert mk'_self _ _; refl

@[simp, to_additive] lemma mul_mk'_eq_mk'_of_mul (x₁ x₂) (y : S) :
  f.1 x₁ * f.mk' x₂ y = f.mk' (x₁ * x₂) y :=
by rw [←mk'_one, ←mk'_mul, one_mul]

@[simp, to_additive] lemma mk'_mul_eq_mk'_of_mul (x₁ x₂) (y : S) :
  f.mk' x₂ y * f.1 x₁ = f.mk' (x₁ * x₂) y :=
by rw [mul_comm, mul_mk'_eq_mk'_of_mul]

@[simp, to_additive] lemma mul_mk'_one_eq_mk' (x) (y : S) :
  f.1 x * f.mk' 1 y = f.mk' x y :=
by rw [mul_mk'_eq_mk'_of_mul, mul_one]

@[simp, to_additive] lemma mk'_mul_cancel_right (x : M) (y : S) :
  f.mk' (x * y) y = f.1 x :=
by rw [←mul_mk'_one_eq_mk', f.1.map_mul, mul_assoc, mul_mk'_one_eq_mk', mk'_self, mul_one]

@[simp, to_additive] lemma mk'_mul_cancel_left (x) (y : S) :
  f.mk' ((y : M) * x) y = f.1 x :=
by rw [mul_comm, mk'_mul_cancel_right]

end localization_map
end submonoid