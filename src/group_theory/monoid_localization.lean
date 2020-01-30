/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import group_theory.congruence
import algebra.associated
import tactic.abel

/-

# Localizations of commutative monoids

The standard congruence relation (an equivalence relation preserving a binary operation) used to
define commutative ring localizations does not rely on the ring's addition. For a commutative
monoid `X` and submonoid `Y`, this relation can be expressed as
`∀ (x₁, y₁) (x₂, y₂) : X × Y, x ∼ y ↔ ∃ c ∈ Y, c * x₁ * y₂ = c * x₂ * y₁`, or, equivalently, as the
unique congruence relation `r` on `X × Y` such that for any other congruence relation `r'` on
`X × Y` where for all `y ∈ Y`, `(1, 1) ∼ (y, y)` under `r'`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by
`r'` implies `(x₁, y₁) ∼ (x₂, y₂)` by `r`.

The first half of the file contains basic lemmas about the localization of `X` at `Y` - the
commutative monoid we get when we quotient `X × Y` by this congruence relation - and some
associated monoid homomorphisms: the quotient map, `localization.mk`, the quotient map restricted
to `X × {1}`, `localization.monoid.of`, and the quotient map restricted to `Y × {1}`,
`localization.monoid.to_units`, whose image is contained in the unit group of the localization of
`X` at `Y`.
Subsequently we prove basic lemmas about `localization.monoid.lift'` (constructive version) and
`localization.monoid.lift` (classical version): given a `comm_monoid` homomorphism `f : X → Z`
mapping elements of a submonoid `Y` to invertible elements of `Z`, these are the homomorphism
from the localization of `X` at `Y` sending `⟦(x, y)⟧` to `f(x) * f(y)⁻¹`. If `f(Y)` is contained
in a submonoid `W` of `Z`, we can also define the map from the localization of `X` at `Y`
to the localization of `Z` at `W` induced by `(of W) ∘ f`, where `of W` is the natural map from `Z`
to the localization of `Z` at `W`. This is called `localization.monoid.map`.

## Implementation notes

The infimum form of the localization congruence relation is chosen as 'canonical' here, since it
shortens many proofs.

The `private def` `r'.rel` and the lemmas `r'.add, r'.transitive` are to enable the use of the
`abel` tactic for both the additive and multiplicative proofs that the 'usual' localization
congruence relation is a congruence relation.

There is only a multiplicative version for any lemma or definition relying on a unit group of a
`comm_monoid`; additive versions would require additive unit groups.

## Tags
localization, monoid localization, quotient monoid, congruence relation

-/
variables {X : Type*}

namespace submonoid

/-- The congruence relation on `X × Y`, `X` a `comm_monoid` and `Y` a submonoid of `X`, whose
    quotient is the localization of `X` at `Y`, defined as the unique congruence relation on
    `X × Y` such that for any other congruence relation `s` on `X × Y` where for all `y ∈ Y`,
    `(1, 1) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `s` implies
    `(x₁, y₁) ∼ (x₂, y₂)` by `r`. -/
@[to_additive "The congruence relation on `X × Y`, `X` an `add_comm_monoid` and `Y` an `add_submonoid` of `X`, whose quotient is the localization of `X` at `Y`, defined as the unique congruence relation on `X × Y` such that for any other congruence relation `s` on `X × Y` where for all `y ∈ Y`, `(0, 0) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `s` implies `(x₁, y₁) ∼ (x₂, y₂)` by `r`."]
def r [comm_monoid X] (Y : submonoid X) : con (X × Y) :=
lattice.Inf {c | ∀ y : Y, c 1 (y, y)}

end submonoid

namespace add_submonoid

variables [add_comm_monoid X]

/-- An alternate form of the `add_monoid` localization relation, stated here for readability of the
    next few lemmas. -/
private def r'.rel (Y : add_submonoid X) (a b : X × Y) :=
∃ c : Y, (c : X) + (a.1 + b.2) = c + (b.1 + a.2)

lemma r'.transitive {Y : add_submonoid X} : transitive (r'.rel Y) :=
λ a b c ⟨m, hm⟩ ⟨n, hn⟩, ⟨n + m + b.2,
  calc
    ↑n + ↑m + ↑b.2 + (a.1 + ↑c.2)
      = ↑n + (↑m + (b.1 + ↑a.2)) + ↑c.2 : by rw ←hm; abel
  ... = ↑m + (↑n + (c.1 + ↑b.2)) + ↑a.2 : by rw ←hn; abel
  ... = ↑n + ↑m + ↑b.2 + (c.1 + ↑a.2) : by abel⟩

lemma r'.add {Y : add_submonoid X} {a b c d} :
  r'.rel Y a b → r'.rel Y c d → r'.rel Y (a + c) (b + d) :=
λ ⟨m, hm⟩ ⟨n, hn⟩, ⟨m + n,
  calc
    ↑m + ↑n + (a.1 + c.1 + (↑b.2 + ↑d.2))
      = ↑n + c.1 + (↑m + (b.1 + ↑a.2)) + ↑d.2 : by rw ←hm; abel
  ... = (↑m + (b.1 + ↑a.2)) + (↑n + (d.1 + ↑c.2)) : by rw ←hn; abel
  ... = ↑m + ↑n + (b.1 + d.1 + (↑a.2 + ↑c.2)) : by abel⟩

/-- An alternate form of the congruence relation on `X × Y`, `X` an `add_comm_monoid` and `Y` an
    `add_submonoid` of `X`, whose quotient is the localization of `X` at `Y`. Its equivalence to
    `r` can be useful for proofs. -/
def r' (Y : add_submonoid X) : add_con (X × Y) :=
{ r := λ a b, ∃ c : Y, (c : X) + (a.1 + b.2) = c + (b.1 + a.2),
  iseqv := ⟨λ _, ⟨0, rfl⟩, λ _ _ ⟨c, hc⟩, ⟨c, hc.symm⟩, r'.transitive⟩,
  add' := λ a b c d, r'.add }

end add_submonoid

variables [comm_monoid X] (Y : submonoid X) {Z : Type*} [comm_monoid Z]

namespace submonoid

/-- An alternate form of the congruence relation on `X × Y`, `X` a `comm_monoid` and `Y` a
    submonoid of `X`, whose quotient is the localization of `X` at `Y`. Its equivalence to `r` can
    be useful for proofs. -/
def r' : con (X × Y) :=
{ r := λ a b, ∃ c : Y, (c : X) * (a.1 * b.2) = c * (b.1 * a.2),
  iseqv := ⟨λ _, ⟨1, rfl⟩, λ _ _ ⟨c, hc⟩, ⟨c, hc.symm⟩,
    @add_submonoid.r'.transitive (additive X) _ $ submonoid.to_add_submonoid Y⟩,
  mul' := @add_submonoid.r'.add (additive X) _ $ submonoid.to_add_submonoid Y }

attribute [to_additive add_submonoid.r'] submonoid.r'

/-- The congruence relation used to localize a `comm_monoid` at a submonoid can be expressed
    equivalently as an infimum (see `submonoid.r`) or explicitly (see `submonoid.r'`). -/
@[to_additive "The additive congruence relation used to localize an `add_comm_monoid` at a submonoid can be expressed equivalently as an infimum (see `add_submonoid.r`) or explicitly (see `add_submonoid.r'`)."]
theorem r_eq_r' : Y.r = Y.r' :=
le_antisymm (lattice.Inf_le $ λ _, ⟨1, by norm_num⟩) $
  lattice.le_Inf $ λ b H x y ⟨t, ht⟩,
    begin
      rw [show x = (1 * x.1, 1 * x.2), by simp, show y = (1 * y.1, 1 * y.2), by simp],
      refine b.trans
       (show b _ ((t : X) * y.2 * x.1, t * y.2 * x.2), from
         b.mul (H (t * y.2)) $ b.refl (x.1, x.2)) _,
      rw [mul_assoc, mul_comm _ x.1, ht, mul_comm y.1, mul_assoc, mul_comm y.2,
          ←mul_assoc, ←mul_assoc],
      exact b.mul (b.symm $ H $ t * x.2) (b.refl (y.1, y.2))
    end

end submonoid

variables (X)

/-- The localization of a `comm_monoid` at one of its submonoids. -/
@[to_additive add_monoid_localization "The localization of an `add_comm_monoid` at one of its submonoids."]
def monoid_localization := Y.r.quotient

variables {X Y}

namespace monoid_localization

/-- For all `y` in `Y`, a submonoid of a `comm_monoid` `X`, `(1, 1) ∼ (y, y)` under the relation
    defining the localization of `X` at `Y`. -/
@[to_additive "For all `y` in `Y`, a submonoid of an `add_comm_monoid` `X`, `(0, 0) ∼ (y, y)` under the relation defining the localization of `X` at `Y`."]
lemma one_rel (y : Y) : Y.r 1 (y, y) := by rw Y.r_eq_r'; use 1; norm_num

/-- Given a `comm_monoid` `X` and submonoid `Y`, `mk` sends `x : X`, `y ∈ Y` to the equivalence
    class of `(x, y)` in the localization of `X` at `Y`. -/
@[to_additive "Given an `add_comm_monoid` `X` and submonoid `Y`, `mk` sends `x : X`, `y ∈ Y` to the equivalence class of `(x, y)` in the localization of `X` at `Y`."]
def mk (x : X) (y : Y) : monoid_localization X Y := Y.r.mk' (x, y)

@[elab_as_eliminator, to_additive]
theorem ind {p : monoid_localization X Y → Prop}
  (H : ∀ (y : X × Y), p (mk y.1 y.2)) (x) : p x :=
by rcases x; convert H x; exact prod.mk.eta.symm

@[elab_as_eliminator, to_additive]
theorem induction_on {p : monoid_localization X Y → Prop} (x)
  (H : ∀ (y : X × Y), p (mk y.1 y.2)) : p x := ind H x

@[to_additive] lemma exists_rep (x) : ∃ y : X × Y, mk y.1 y.2 = x :=
induction_on x $ λ y, ⟨y, rfl⟩

@[to_additive] instance : has_mul (monoid_localization X Y) := Y.r.has_mul

@[to_additive] instance : comm_monoid (monoid_localization X Y) :=
Y.r.comm_monoid

@[to_additive] instance : inhabited (monoid_localization X Y) := ⟨1⟩

@[to_additive] protected lemma eq {a₁ b₁} {a₂ b₂ : Y} :
  mk a₁ a₂ = mk b₁ b₂ ↔ ∀ c : con (X × Y), (∀ y : Y, c 1 (y, y)) → c (a₁, a₂) (b₁, b₂) :=
Y.r.eq.trans $ iff.rfl

@[to_additive] protected lemma eq' {a₁ b₁} {a₂ b₂ : Y} :
  mk a₁ a₂ = mk b₁ b₂ ↔ ∃ c : Y, (c : X) * (a₁ * b₂) = c * (b₁ * a₂) :=
⟨λ h, let ⟨w, hw⟩ := show Y.r' (a₁, a₂) (b₁, b₂), by rw [←Y.r_eq_r', ←con.eq]; exact h in ⟨w, hw⟩,
 λ ⟨w, hw⟩, by erw [Y.r.eq, Y.r_eq_r']; exact ⟨w, hw⟩⟩

@[to_additive] lemma mk_eq_of_eq {a₁ b₁} {a₂ b₂ : Y} (h : (a₂ : X) * b₁ = b₂ * a₁) :
  mk a₁ a₂ = mk b₁ b₂ :=
monoid_localization.eq'.2 $ ⟨1, by rw [mul_comm b₁, h, mul_comm a₁]⟩

@[simp, to_additive] lemma mk_self' (x : Y) : mk (x : X) x = 1 :=
monoid_localization.eq.2 $ λ c h, c.symm $ h x

@[simp, to_additive] lemma mk_self {x} (hx : x ∈ Y) : mk x ⟨x, hx⟩ = 1 :=
mk_self' ⟨x, hx⟩

@[simp, to_additive] lemma mk_mul_mk (x y) (s t : Y) :
  mk x s * mk y t = mk (x * y) (s * t) := rfl

/-- Definition of the function on the localization of a `comm_monoid` at a submonoid induced by a
    function that is constant on the equivalence classes of the localization relation. -/
@[simp, to_additive "Definition of the function on the localization of an `add_comm_monoid` at an `add_submonoid` induced by a function that is constant on the equivalence classes of the localization relation."]
lemma lift_on_beta {β} (f : (X × Y) → β) (H : ∀ a b, Y.r a b → f a = f b) (x y) :
con.lift_on (mk x y) f H = f (x, y) := rfl

/-- Natural homomorphism sending `x : X`, `X` a `comm_monoid`, to the equivalence class of
    `(x, 1)` in the localization of `X` at a submonoid. For a `comm_ring` localization, this is
    a ring homomorphism named `localization.of`. -/
@[to_additive "Natural homomorphism sending `x : X`, `X` an `add_comm_monoid`, to the equivalence class of `(x, 0)` in the localization of `X` at a submonoid."]
def of (Y) : X →* monoid_localization X Y :=
Y.r.mk'.comp ⟨λ x, (x, 1), refl 1, λ _ _, by simp only [prod.mk_mul_mk, one_mul]⟩

@[to_additive] lemma of_ker_iff {x y} : con.ker (of Y) x y ↔ Y.r (x, 1) (y, 1) :=
con.eq _

@[to_additive] lemma of_eq_mk (x) : of Y x = mk x 1 := rfl

@[simp, to_additive] lemma of_mul_mk (x y v) : of Y x * mk y v = mk (x * y) v :=
by rw [of_eq_mk, mk_mul_mk, one_mul]

@[to_additive] lemma mk_eq_mul_mk_one (x y) : mk x y = of Y x * mk 1 y :=
by rw [of_mul_mk, mul_one]

@[simp, to_additive] lemma mk_mul_cancel_right (x : X) (y : Y) :
  mk (x * y) y = of Y x :=
by rw [mk_eq_mul_mk_one, (of Y).map_mul, mul_assoc, ←mk_eq_mul_mk_one, mk_self', mul_one]

@[simp, to_additive] lemma mk_mul_cancel_left (x : X) (y : Y) :
  mk ((y : X) * x) y = of Y x :=
by rw [mul_comm, mk_mul_cancel_right]

/-- Natural homomorphism sending `y ∈ Y`, `Y` a submonoid of a `comm_monoid` `X`, to the units of
    the localization of `X` at `Y`. -/
def to_units (Y : submonoid X) : Y →* units (monoid_localization X Y) :=
⟨λ y, ⟨mk y 1, mk 1 y, by simp, by simp⟩, by simp; refl,
 λ _ _, by ext; convert (of Y).map_mul _ _⟩

@[simp] lemma to_units_mk (y) : (to_units Y y : monoid_localization X Y) = mk y 1 := rfl

@[simp] lemma mk_is_unit (y : Y) : is_unit (mk (y : X) (1 : Y)) :=
is_unit_unit $ to_units Y y

@[simp] lemma mk_is_unit' (x) (hx : x ∈ Y) : is_unit (mk x (1 : Y)) :=
is_unit_unit $ to_units Y ⟨x, hx⟩

lemma to_units_inv (y) : mk 1 y = ↑(to_units Y y)⁻¹ := rfl

@[simp] lemma of_is_unit (y : Y) : is_unit (of Y y) :=
is_unit_unit $ to_units Y y

@[simp] lemma of_is_unit' (x) (hx : x ∈ Y) : is_unit (of Y x) :=
is_unit_unit $ to_units Y ⟨x, hx⟩

lemma to_units_map_inv (g : monoid_localization X Y →* Z) (y) :
  g ↑(to_units Y y)⁻¹ = ↑(units.map g (to_units Y y))⁻¹ :=
by rw [←units.coe_map, (units.map g).map_inv]

lemma mk_eq (x y) : mk x y = of Y x * ↑(to_units Y y)⁻¹ :=
by rw ←to_units_inv; simp only [of_eq_mk, mk_mul_mk, mul_one, one_mul]

variables {f : X →* Z}

lemma is_unit_of_of_comp {W : submonoid Z} (hf : ∀ y : Y, f y ∈ W) {y : Y} :
  is_unit (of W (f y)) :=
⟨to_units W ⟨f y, hf y⟩, rfl⟩

variables {g : Y → units Z}

lemma units_restrict_mul (H : ∀ y : Y, f y = g y) {x y} : g (x * y) = g x * g y :=
by ext; rw [units.coe_mul, ←H _, ←H _, ←H _]; apply f.map_mul

variables (f)

/-- Given a `comm_monoid` homomorphism `f : X → Z` mapping elements of a submonoid `Y` to
    invertible elements of `Z`, the induced homomorphism from `Y` to the units of `Z`. -/
def units_restrict (H : ∀ y : Y, f y = g y) : Y →* units Z :=
⟨g, units.ext $ (H 1) ▸ f.map_one, λ _ _, units_restrict_mul H⟩

variables (g)

/-- Given a `comm_monoid` homomorphism `f : X → Z` mapping elements of a submonoid `Y` to
    invertible elements of `Z`, the homomorphism from `X × Y` to `Z` sending `(x, y)` to
    `f(x) * f(y)⁻¹`; this induces a homomorphism from the localization of `X` at `Y`
    (constructive version). -/
def aux (H : ∀ y : Y, f y = g y) : X × Y →* Z :=
(f.comp prod.monoid_hom.fst).mul $
  (units.coe_hom Z).comp ((units_restrict f H).comp prod.monoid_hom.snd).inv

variables {g}

/-- Given a `comm_monoid` homomorphism `f : X → Z` mapping elements of a submonoid `Y` to
    invertible elements of `Z`, the homomorphism from `X × Y` to `Z` sending `(x, y)` to
    `f(x) * f(y)⁻¹` is constant on the equivalence classes of the localization of `X` at `Y`. -/
lemma r_le_ker_aux (H : ∀ y : Y, f y = g y) :
  Y.r ≤ con.ker (aux f g H) :=
con.Inf_le _ _ (λ y, show f (1 : Y) * ↑(g 1)⁻¹ = f y * ↑(g y)⁻¹, by
  rw [H 1, H y]; simp [units.mul_inv])

/-- Given a `comm_monoid` homomorphism `f : X → Z` mapping elements of a submonoid `Y` to
    invertible elements of `Z`, the homomorphism from the localization of `X` at `Y` sending
    `⟦(x, y)⟧` to `f(x) * f(y)⁻¹`. -/
def lift' (g : Y → units Z) (H : ∀ y : Y, f y = g y) : monoid_localization X Y →* Z :=
Y.r.lift (aux f g H) $ r_le_ker_aux f H

/-- Given a `comm_monoid` homomorphism `f : X → Z` mapping elements of a submonoid `Y` to
    invertible elements of `Z`, the homomorphism from the localization of `X` at `Y` sending
    `⟦(x, y)⟧` to `f(x) * f(y)⁻¹`, where `f(y)⁻¹` is chosen nonconstructively. -/
noncomputable def lift (H : ∀ y : Y, is_unit (f y)) : monoid_localization X Y →* Z :=
lift' f _ $ λ _, classical.some_spec $ H _

variables {f}

@[simp] lemma lift'_mk (H : ∀ y : Y, f y = g y) (x y) :
  lift' f _ H (mk x y) = f x * ↑(g y)⁻¹ := rfl

@[simp] lemma lift_mk (H : ∀ y : Y, is_unit (f y)) (x y) :
  lift f H (mk x y) = f x * ↑(classical.some (H y))⁻¹ := rfl

@[simp] lemma lift'_of (H : ∀ y : Y, f y = g y) (x : X) :
  lift' f _ H (of Y x) = f x :=
show f x * ↑(g 1)⁻¹ = _, by
  rw [inv_eq_one.2 (show g 1 = 1, from units.ext $ (H 1) ▸ f.map_one), units.coe_one, mul_one]

@[simp] lemma lift_of (H : ∀ y : Y, is_unit (f y)) (x : X) :
  lift f H (of Y x) = f x := lift'_of _ _

lemma lift'_eq_iff (H : ∀ y : Y, f y = g y) {x y : X × Y} :
  lift' f g H (mk x.1 x.2) = lift' f g H (mk y.1 y.2) ↔ f (y.2 * x.1) = f (y.1 * x.2) :=
by rw [lift'_mk, lift'_mk, units.eq_mul_inv_iff_mul_eq, mul_comm, ←mul_assoc,
       units.mul_inv_eq_iff_eq_mul, ←H _, ←H _, ←f.map_mul, ←f.map_mul]

lemma lift_eq_iff (H : ∀ y : Y, is_unit (f y)) {x y : X × Y} :
  lift f H (mk x.1 x.2) = lift f H (mk y.1 y.2) ↔ f (y.2 * x.1) = f (y.1 * x.2) :=
lift'_eq_iff _

lemma mk_eq_iff_of_eq {x y : X × Y} :
  mk x.1 x.2 = mk y.1 y.2 ↔ of Y (y.2 * x.1) = of Y (y.1 * x.2) :=
by rw [mk_eq, mk_eq, ←lift'_mk, ←lift'_mk];
  exact lift'_eq_iff (λ (w : Y), rfl)

lemma lift'_comp_of (H : ∀ y : Y, f y = g y) :
  (lift' f _ H).comp (of Y) = f :=
by ext; exact lift'_of H _

@[simp] lemma lift_comp_of (H : ∀ y : Y, is_unit (f y)) :
  (lift f H).comp (of Y) = f := lift'_comp_of _

@[simp] lemma lift'_apply_of (f' : monoid_localization X Y →* Z)
  (H : ∀ y : Y, f'.comp (of Y) y = g y) : lift' (f'.comp (of Y)) _ H = f' :=
begin
  ext x,
  apply induction_on x,
  intros,
  rw [lift'_mk, ←units.mul_right_inj (g y.2), mul_assoc, units.inv_mul, ←H y.2,
      mul_one, mk_eq_mul_mk_one],
  show f' _ = f' (mk _ _ * _) * f' (mk _ _),
  rw [←f'.map_mul, mk_mul_mk, mk_mul_mk],
  simp only [mul_one, mk_mul_cancel_right, one_mul],
end

@[simp] lemma lift_apply_of (g : monoid_localization X Y →* Z) :
  lift (g.comp $ of Y) (λ y, is_unit_unit $ units.map g $ to_units Y y) = g :=
lift'_apply_of _ _

lemma  funext (f g : monoid_localization X Y →* Z)
  (h : ∀ a, f.comp (of Y) a = g.comp (of Y) a) : f = g :=
begin
  rw [←lift_apply_of f, ←lift_apply_of g],
  congr' 1,
  ext,
  convert h x,
end

variables {W : submonoid Z} (f)

/-- Given a `comm_monoid` homomorphism `f : X → Z` where for submonoids `Y ⊆ X, W ⊆ Z` we have
    `f(Y) ⊆ W`, the monoid homomorphism from the localization of `X` at `Y` to the localization of
    `Z` at `W` induced by the natural map from `Z` to the localization of `Z` at
    `W` composed with `f`. -/
def map (hf : ∀ y : Y, f y ∈ W) : monoid_localization X Y →* monoid_localization Z W :=
lift' ((of W).comp f) ((to_units W).comp $ (f.comp Y.subtype).subtype_mk W hf) $ λ y, rfl

variables {f}

lemma map_eq (hf : ∀ y : Y, f y ∈ W) :
  map f hf = lift ((of W).comp f) (λ y, ⟨to_units W ⟨f y, hf y⟩, rfl⟩) :=
by rw map; congr; ext; erw ←classical.some_spec (is_unit_of_of_comp hf); refl

@[simp] lemma map_of (hf : ∀ y : Y, f y ∈ W) (x) :
  map f hf (of Y x) = of W (f x) := lift'_of _ _

@[simp] lemma map_comp_of (hf : ∀ y : Y, f y ∈ W) :
  (map f hf).comp (of Y) = (of W).comp f := lift'_comp_of _

lemma map_mk (hf : ∀ y : Y, f y ∈ W) (x y) :
  map f hf (mk x y) = mk (f x) ⟨f y, hf y⟩ :=
(lift'_mk _ _ _).trans (mk_eq _ _).symm

@[simp] lemma map_id (x : monoid_localization X Y) :
  map (monoid_hom.id X) (λ (y : Y), y.2) x = x :=
induction_on x $ λ ⟨w, z⟩, by rw map_mk; exact congr_arg _ (subtype.eq' rfl)

lemma map_comp_map {A} [comm_monoid A] {V} {g : Z →* A}
  (hf : ∀ y : Y, f y ∈ W) (hg : ∀ w : W, g w ∈ V) :
  (map g hg).comp (map f hf) = map (g.comp f) (λ y, hg ⟨f y, hf y⟩) :=
funext _ _ $ λ x, by simp only [map_of, monoid_hom.comp_apply]

lemma map_map {A} [comm_monoid A] {V} {g : Z →* A}
  (hf : ∀ y : Y, f y ∈ W) (hg : ∀ w : W, g w ∈ V) (x) :
  map g hg (map f hf x) = map (g.comp f) (λ y : Y, hg ⟨f y, hf y⟩) x :=
by rw ←map_comp_map hf hg; refl

lemma map_ext (g : X →* Z) (hf : ∀ y : Y, f y ∈ W) (hg : ∀ y : Y, g y ∈ W)
  (h : f = g) (x) : map f hf x = map g hg x :=
induction_on x $ λ _, by {rw [map_mk, map_mk], congr; rw h; refl}

end monoid_localization
