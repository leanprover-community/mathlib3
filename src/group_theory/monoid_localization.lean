/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import group_theory.congruence
import algebra.associated

/-!
# Localizations of commutative monoids

Localizing a commutative ring at one of its submonoids does not rely on the ring's addition, so
we can generalize localizations to commutative monoids.

We characterize the localization of a commutative monoid `X` at a submonoid `Y` up to
isomorphism; that is, a commutative monoid `Z` is the localization of `X` at `Y` iff we can find a
monoid homomorphism `f : X →* Z` satisfying 3 properties:
1. For all `y ∈ Y`, there exists `z : Z` such that `f y * z = 1`;
2. For all `z : Z`, there exists `(x, y) : X × Y` such that `z * f y = f x`;
3. For all `x, y : X`, `f x = f y` iff there exists `c ∈ Y` such that `x * c = y * c`.

We also define the quotient of `X × Y` by the unique congruence relation (equivalence relation
preserving a binary operation) `r` such that for any other congruence relation `s` on `X × Y`
satisfying '`∀ y ∈ Y`, `(1, 1) ∼ (y, y)` under `s`', we have that `(x₁, y₁) ∼ (x₂, y₂)` by `s`
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

We use `classical.epsilon` where possible; like `classical.some`, it reduces the number of
arguments to functions, but shortens proofs in comparison to `classical.some`.

## Tags
localization, monoid localization, quotient monoid, congruence relation, characteristic predicate,
commutative monoid
-/
variables {X : Type*} [comm_monoid X] (Y : submonoid X) {Z : Type*} [comm_monoid Z]
          {V : Type*} [comm_monoid V] (f : X →* Z)

namespace submonoid

/-- The characteristic predicate: if `f` satisfies `is_localization_map`, then `Z` is isomorphic
    to the localization of `X` at `Y`. -/
@[to_additive "The characteristic predicate: if `f` satisfies `is_localization_map`, then `Z` is isomorphic to the localization of `X` at `Y`."]
def is_localization_map :=
(∀ y : Y, ∃ z, f y * z = 1) ∧ (∀ z : Z, ∃ x : X × Y, z * f x.2 = f x.1) ∧
∀ x y, f x = f y ↔ ∃ c : Y, x * c = y * c

variables {f} (Z)

/-- Given a proof that there exists some homomorphism from `X` to `Z` satsifying
    `is_localization_map Y`, produces such a homomorphism. -/
@[to_additive "Given a proof that there exists some homomorphism from `X` to `Z` satsifying `is_localization_map Y`, produces such a homomorphism."]
noncomputable def localization_map :=
@classical.epsilon (X →* Z) ⟨monoid_hom.one⟩ (λ f, Y.is_localization_map f)

/-- A predicate characterizing `comm_monoid`s `Z` isomorphic to the localization of `X` at `Y`,
    requiring only a proof that there exists some homomorphism `f : X →* Z` satisfying
    `is_localization_map Y f`. -/
@[to_additive "A predicate characterizing `add_comm_monoid`s `Z` isomorphic to the localization of `X` at `Y`, requiring only a proof that there exists some homomorphism `f : X →+ Z` satisfying `is_localization_map Y f`."]
def is_localization := ∃ f : X →* Z, Y.is_localization_map f

namespace monoid_localization

/-- The congruence relation on `X × Y`, `X` a `comm_monoid` and `Y` a submonoid of `X`, whose
    quotient is the localization of `X` at `Y`, defined as the unique congruence relation on
    `X × Y` such that for any other congruence relation `s` on `X × Y` where for all `y ∈ Y`,
    `(1, 1) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies
    `(x₁, y₁) ∼ (x₂, y₂)` by `s`. -/
@[to_additive "The congruence relation on `X × Y`, `X` an `add_comm_monoid` and `Y` an `add_submonoid` of `X`, whose quotient is the localization of `X` at `Y`, defined as the unique congruence relation on `X × Y` such that for any other congruence relation `s` on `X × Y` where for all `y ∈ Y`, `(0, 0) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies `(x₁, y₁) ∼ (x₂, y₂)` by `s`."]
def r (Y : submonoid X) : con (X × Y) :=
lattice.Inf {c | ∀ y : Y, c 1 (y, y)}

/-- An alternate form of the congruence relation on `X × Y`, `X` a `comm_monoid` and `Y` a
    submonoid of `X`, whose quotient is the localization of `X` at `Y`. Its equivalence to `r` can
    be useful for proofs. -/
@[to_additive "An alternate form of the congruence relation on `X × Y`, `X` a `comm_monoid` and `Y` a submonoid of `X`, whose quotient is the localization of `X` at `Y`. Its equivalence to `r` can be useful for proofs."]
def r' : con (X × Y) :=
begin
  refine { r := λ a b : X × Y, ∃ c : Y, a.1 * b.2 * c = b.1 * a.2 * c,
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
    equivalently as an infimum (see `monoid_localization.r`) or explicitly
    (see `monoid_localization.r'`). -/
@[to_additive "The additive congruence relation used to localize an `add_comm_monoid` at a submonoid can be expressed equivalently as an infimum (see `monoid_localization.r`) or explicitly (see `monoid_localization.r'`)."]
theorem r_eq_r' : r Y = r' Y :=
le_antisymm (lattice.Inf_le $ λ _, ⟨1, by simp⟩) $
  lattice.le_Inf $ λ b H ⟨p, q⟩ y ⟨t, ht⟩,
    begin
      rw [← mul_one (p, q), ← mul_one y],
      refine b.trans (b.mul (b.refl _) (H (y.2 * t))) _,
      convert b.symm (b.mul (b.refl y) (H (q * t))); simp only [],
      rw [prod.mk_mul_mk, submonoid.coe_mul, ← mul_assoc, ht, mul_left_comm, mul_assoc],
      refl
    end

end monoid_localization

/-- The localization of a `comm_monoid` at one of its submonoids (as a quotient type). -/
@[to_additive "The localization of an `add_comm_monoid` at one of its submonoids (as a quotient type)."]
def monoid_localization := (monoid_localization.r Y).quotient

namespace monoid_localization

variables {Y}

@[to_additive]
lemma r_iff_exists {x y : X × Y} : r Y x y ↔ ∃ c : Y, x.1 * y.2 * c = y.1 * x.2 * c :=
by rw r_eq_r' Y; refl

variables (Y) {Z} (f)

/-- Given a localization map `f : X →* Z`, a section function sending `z : Z` to some
    `(x, y) : X × Y` such that `f x * (f y)⁻¹ = z`. -/
@[to_additive "Given a localization map `f : X →+ Z`, a section function sending `z : Z` to some `(x, y) : X × Y` such that `f x - f y = z`."]
noncomputable def sec :=
@classical.epsilon (Z → X × Y) ⟨λ z, 1⟩ (λ g, ∀ z, z * f (g z).2 = f (g z).1)

/-- Given a map `f : X →* Z` such that `f y` is invertible for all `y ∈ Y`, produces a
    homomorphism sending `y ∈ Y` to `(f y)⁻¹`. -/
@[to_additive "Given a map `f : X →+ Z` such that `f y` is invertible for all `y ∈ Y`, produces a homomorphism sending `y ∈ Y` to `-(f y)`."]
noncomputable def inv :=
@classical.epsilon (Y →* Z) ⟨monoid_hom.one⟩ (λ g, ∀ y : Y, f y * g y = 1)

variables {Y f}

@[simp, to_additive] lemma inv_mul (inv : Y → Z) (h : ∀ y : Y, f y * inv y = 1) (x y : Y) :
  inv (x * y) = inv x * inv y :=
begin
  rw [←one_mul (inv _), ←h, ←mul_one (f x), ←h, ←mul_assoc, ←f.map_mul,
      ←submonoid.coe_mul, mul_comm],
  assoc_rw mul_comm (inv _) (f _),
  rw [h, one_mul, mul_comm],
end

@[simp, to_additive] lemma inv_spec_right (h : ∀ y : Y, ∃ z : Z, f y * z = 1) (y : Y) :
  f y * inv Y f y = 1 :=
@classical.epsilon_spec (Y →* Z) (λ g, ∀ y : Y, f y * g y = 1)
  ⟨⟨λ y, classical.some $ h y, by simpa using classical.some_spec (h 1),
   inv_mul (λ y, classical.some $ h y) $ λ y, classical.some_spec $ h y⟩,
   λ y, classical.some_spec $ h y⟩ y

@[simp, to_additive] lemma inv_spec_left (h : ∀ y : Y, ∃ z : Z, f y * z = 1) (y : Y) :
  inv Y f y * f y = 1 :=
by rw [mul_comm, inv_spec_right h]

@[simp, to_additive] lemma mul_inv_left (h : ∀ y : Y, ∃ z : Z, f y * z = 1) (y : Y) (w z) :
  w * inv Y f y = z ↔ w = f y * z :=
⟨λ H, by rw [←mul_one w, ←inv_spec_left h y, ←H]; ac_refl,
 λ H, by rw [←one_mul z, ←inv_spec_left h y, H]; ac_refl⟩

@[simp, to_additive] lemma mul_inv_right (h : ∀ y : Y, ∃ z : Z, f y * z = 1) (y : Y) (w z) :
  z = w * inv Y f y ↔ z * f y = w :=
by rw [eq_comm, mul_inv_left h, mul_comm, eq_comm]

@[simp, to_additive] lemma mul_inv (h : ∀ y : Y, ∃ z, f y * z = 1) {x₁ x₂} {y₁ y₂ : Y} :
  f x₁ * inv Y f y₁ = f x₂ * inv Y f y₂ ↔ f (x₁ * y₂) = f (x₂ * y₁) :=
by rw [mul_inv_left h, ←mul_assoc, mul_inv_right h, mul_comm x₂, f.map_mul, f.map_mul]

@[to_additive] lemma inv_inj (hf : ∀ y : Y, ∃ z, f y * z = 1) {y z}
  (h : inv Y f y = inv Y f z) : f y = f z :=
by rw [←mul_one (f y), ←inv_spec_right hf z, ←h, ←mul_assoc, mul_comm (f y), mul_assoc,
       inv_spec_right hf, mul_one]

@[to_additive] lemma inv_unique (h : ∀ y : Y, ∃ z, f y * z = 1) {y : Y} {z} (H : f y * z = 1) :
  inv Y f y = z :=
by rw [←mul_one z, ←inv_spec_right h y, ←mul_assoc, mul_comm z, H, one_mul]

variables (f)

/-- Given a localization map `f : X →* Z`, the surjection sending `(x, y) : X × Y` to
    `f x * (f y)⁻¹`. -/
@[to_additive "Given a localization map `f : X →+ Z`, the surjection sending `(x, y) : X × Y` to `f x - f y`."]
noncomputable def mk (x : X) (y : Y) : Z := f x * inv Y f y

/-- Given a localization map `f : X →* Z`, the surjection sending `(x, y) : X × Y` to
    `f x * (f y)⁻¹` as a `monoid_hom`. -/
@[to_additive "Given a localization map `f : X →+ Z`, the surjection sending `(x, y) : X × Y` to `f x - f y` as an `add_monoid_hom`."]
noncomputable def mk_hom : X × Y →* Z :=
(f.comp prod.monoid_hom.fst).mul $ (inv Y f).comp prod.monoid_hom.snd

variables {f}

@[simp, to_additive] lemma mk_mul (x₁ x₂ : X) (y₁ y₂ : Y) :
  mk f (x₁ * x₂) (y₁ * y₂) = mk f x₁ y₁ * mk f x₂ y₂ :=
(mk_hom f).map_mul (x₁, y₁) (x₂, y₂)

@[to_additive] lemma mk_one (x) : mk f x (1 : Y) = f x := by rw [mk, (inv Y f).map_one, mul_one]

@[to_additive] lemma localization_map_spec (h : is_localization Y Z) :
  Y.is_localization_map (Y.localization_map Z) :=
classical.epsilon_spec h

variables (hf : Y.is_localization_map f)
include hf

@[simp, to_additive] lemma sec_spec (z : Z) :
  z * f (sec Y f z).2 = f (sec Y f z).1 :=
@classical.epsilon_spec (Z → X × Y) (λ g, ∀ z, z * f (g z).2 = f (g z).1)
  ⟨λ y, classical.some $ hf.2.1 y, λ y, classical.some_spec $ hf.2.1 y⟩ z

@[simp, to_additive] lemma sec_spec' (z : Z) :
  f (sec Y f z).1 = f (sec Y f z).2 * z :=
by rw [mul_comm, sec_spec hf]

@[simp, to_additive] lemma mk_sec (z : Z) :  mk f (sec Y f z).1 (sec Y f z).2 = z :=
show _ * _ = _, by rw [←sec_spec hf, mul_assoc, inv_spec_right hf.1, mul_one]

@[to_additive] lemma mk_surjective (z : Z) : ∃ x (y : Y), mk f x y = z :=
⟨(sec Y f z).1, (sec Y f z).2, mk_sec hf z⟩

@[simp, to_additive] lemma mk_spec (x) (y : Y) :
  mk f x y * f y = f x :=
show _ * _ * _ = _, by rw [mul_assoc, inv_spec_left hf.1, mul_one]

@[simp, to_additive] lemma mk_spec' (x) (y : Y) :
  f y * mk f x y = f x :=
by rw [mul_comm, mk_spec hf]

@[simp, to_additive] theorem eq_mk_iff_mul_eq {x} {y : Y} {z} :
  z = mk f x y ↔ z * f y = f x :=
⟨λ H, by rw [H, mk_spec hf], λ H, by rw [←mul_one z, ←inv_spec_right hf.1 y, ←mul_assoc, H]; refl⟩

@[simp, to_additive] theorem mk_eq_iff_eq_mul {x} {y : Y} {z} :
  mk f x y = z ↔ f x = z * f y :=
by rw [eq_comm, eq_mk_iff_mul_eq hf, eq_comm]

@[to_additive] lemma mk_eq_iff_eq {x₁ x₂} {y₁ y₂ : Y} :
  mk f x₁ y₁ = mk f x₂ y₂ ↔ f (x₁ * y₂) = f (x₂ * y₁) :=
⟨λ H, by rw [f.map_mul, (mk_eq_iff_eq_mul hf).1 H, mul_assoc,
  mul_comm (f _), ←mul_assoc, mk_spec hf, f.map_mul],
 λ H, by rw [mk_eq_iff_eq_mul hf, mk, mul_assoc, mul_comm (inv Y f _),
   ←mul_assoc, ←f.map_mul, ←H, f.map_mul, mul_assoc, inv_spec_right hf.1, mul_one]⟩

@[to_additive] protected lemma eq {a₁ b₁} {a₂ b₂ : Y} :
  mk f a₁ a₂ = mk f b₁ b₂ ↔ ∃ c : Y, a₁ * b₂ * c = b₁ * a₂ * c :=
(mk_eq_iff_eq hf).trans $ hf.2.2 _ _

@[to_additive] protected lemma eq' {a₁ b₁} {a₂ b₂ : Y} :
  mk f a₁ a₂ = mk f b₁ b₂ ↔ r Y (a₁, a₂) (b₁, b₂) :=
by rw [monoid_localization.eq hf, r_iff_exists]

@[to_additive] lemma eq_iff_eq {g : X →* V} (hg : Y.is_localization_map g) {x y} :
  f x = f y ↔ g x = g y :=
(hf.2.2 _ _).trans (hg.2.2 _ _).symm

@[to_additive] lemma mk_eq_iff_mk_eq {g : X →* V}
  (hg : Y.is_localization_map g) {x₁ x₂} {y₁ y₂ : Y} :
  mk f x₁ y₁ = mk f x₂ y₂ ↔ mk g x₁ y₁ = mk g x₂ y₂ :=
(monoid_localization.eq' hf).trans (monoid_localization.eq' hg).symm

@[to_additive] lemma exists_of_sec_mk (x) (y : Y) :
  ∃ c : Y, x * (sec Y f $ mk f x y).2 * c = (sec Y f $ mk f x y).1 * y * c :=
(hf.2.2 _ _).1 $ (mk_eq_iff_eq hf).1 $ (mk_sec hf _).symm

@[to_additive] lemma exists_of_sec (x) :
  ∃ c : Y, x * (sec Y f $ f x).2 * c = (sec Y f $ f x).1 * c :=
(hf.2.2 _ _).1 $ by rw f.map_mul; exact sec_spec hf _

@[to_additive] lemma mk_eq_of_eq {a₁ b₁ : X} {a₂ b₂ : Y} (H : b₁ * a₂ = a₁ * b₂) :
  mk f a₁ a₂ = mk f b₁ b₂ :=
(mk_eq_iff_eq hf).2 $ H ▸ rfl

@[simp, to_additive] lemma mk_self (y : Y) :
  mk f (y : X) y = 1 := inv_spec_right hf.1 y

@[simp, to_additive] lemma mk_self' (x) (H : x ∈ Y) :
  mk f x ⟨x, H⟩ = 1 :=
by convert mk_self hf _; refl

omit hf

@[simp, to_additive] lemma mul_mk_eq_mk_of_mul (x₁ x₂) (y : Y) :
  f x₁ * mk f x₂ y = mk f (x₁ * x₂) y :=
by rw [←mk_one, ←mk_mul, one_mul]

@[simp, to_additive] lemma mk_mul_eq_mk_of_mul (x₁ x₂) (y : Y) :
  mk f x₂ y * f x₁ = mk f (x₁ * x₂) y :=
by rw [mul_comm, mul_mk_eq_mk_of_mul]

@[simp, to_additive] lemma mul_mk_one_eq_mk (x) (y : Y) :
  f x * mk f 1 y = mk f x y :=
by rw [mul_mk_eq_mk_of_mul, mul_one]

include hf

@[simp, to_additive] lemma mk_mul_cancel_right (x : X) (y : Y) :
  mk f (x * y) y = f x :=
by rw [←mul_mk_one_eq_mk, f.map_mul, mul_assoc, mul_mk_one_eq_mk, mk_self hf, mul_one]

@[simp, to_additive] lemma mk_mul_cancel_left (x) (y : Y) :
  mk f ((y : X) * x) y = f x :=
by rw [mul_comm, mk_mul_cancel_right hf]

end monoid_localization
end submonoid