/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import group_theory.monoid_localization.localization_map

/-!
# Localizations of commutative monoids

We define the quotient of `M × S` by the unique congruence relation (equivalence relation
preserving a binary operation) `r` such that for any other congruence relation `s` on `M × S`
satisfying '`∀ y ∈ S`, `(1, 1) ∼ (y, y)` under `s`', we have that `(x₁, y₁) ∼ (x₂, y₂)` by `s`
whenever `(x₁, y₁) ∼ (x₂, y₂)` by `r`. We show this relation is equivalent to the standard
localization relation.

## Implementation notes

The infimum form of the localization congruence relation is chosen as 'canonical' here, since it
shortens some proofs.

To reason about the localization as a quotient type, use `mk_eq_monoid_of_mk'` and associated
lemmas. These show the quotient map `mk : M → S → localization S` equals the
surjection `localization_map.mk'` induced by the map
`monoid_of : localization_map S (localization S)` (where `of` establishes the
localization as a quotient type satisfies the characteristic predicate). The lemma
`mk_eq_monoid_of_mk'` hence gives you access to the results in the rest of the file, which are
about the `localization_map.mk'` induced by any localization map.

## Tags
quotient monoid, congruence relation
-/

section comm_monoid

variables {M : Type*} [comm_monoid M] (S : submonoid M) {N : Type*} [comm_monoid N]
          {P : Type*} [comm_monoid P]


namespace localization
run_cmd to_additive.map_namespace `localization `add_localization

/-- The congruence relation on `M × S`, `M` a `comm_monoid` and `S` a submonoid of `M`, whose
quotient is the localization of `M` at `S`, defined as the unique congruence relation on
`M × S` such that for any other congruence relation `s` on `M × S` where for all `y ∈ S`,
`(1, 1) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies
`(x₁, y₁) ∼ (x₂, y₂)` by `s`. -/
@[to_additive "The congruence relation on `M × S`, `M` an `add_comm_monoid` and `S`
an `add_submonoid` of `M`, whose quotient is the localization of `M` at `S`, defined as the unique
congruence relation on `M × S` such that for any other congruence relation `s` on `M × S` where
for all `y ∈ S`, `(0, 0) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies
`(x₁, y₁) ∼ (x₂, y₂)` by `s`."]
def r (S : submonoid M) : con (M × S) :=
Inf {c | ∀ y : S, c 1 (y, y)}

/-- An alternate form of the congruence relation on `M × S`, `M` a `comm_monoid` and `S` a
submonoid of `M`, whose quotient is the localization of `M` at `S`. -/
@[to_additive "An alternate form of the congruence relation on `M × S`, `M` a `comm_monoid` and
`S` a submonoid of `M`, whose quotient is the localization of `M` at `S`."]
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
@[to_additive "The additive congruence relation used to localize an `add_comm_monoid` at a
submonoid can be expressed equivalently as an infimum (see `add_localization.r`) or
explicitly (see `add_localization.r'`)."]
theorem r_eq_r' : r S = r' S :=
le_antisymm (Inf_le $ λ _, ⟨1, by simp⟩) $
  le_Inf $ λ b H ⟨p, q⟩ y ⟨t, ht⟩,
    begin
      rw [← mul_one (p, q), ← mul_one y],
      refine b.trans (b.mul (b.refl _) (H (y.2 * t))) _,
      convert b.symm (b.mul (b.refl y) (H (q * t))) using 1,
      rw [prod.mk_mul_mk, submonoid.coe_mul, ← mul_assoc, ht, mul_left_comm, mul_assoc],
      refl
    end

variables {S}

@[to_additive]
lemma r_iff_exists {x y : M × S} : r S x y ↔ ∃ c : S, x.1 * y.2 * c = y.1 * x.2 * c :=
by rw r_eq_r' S; refl

end localization

@[to_additive add_submonoid.localization_map.eq']
protected  lemma localization_map.eq' (f : submonoid.localization_map S N) {a₁ b₁} {a₂ b₂ : S} :
  f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ localization.r S (a₁, a₂) (b₁, b₂) :=
by rw [f.eq, localization.r_iff_exists]

/-- The localization of a `comm_monoid` at one of its submonoids (as a quotient type). -/
@[to_additive add_localization "The localization of an `add_comm_monoid` at one
of its submonoids (as a quotient type)."]
def localization := (localization.r S).quotient

namespace localization

@[to_additive] instance inhabited :
  inhabited (localization S) :=
con.quotient.inhabited

/-- Multiplication in a localization is defined as `⟨a, b⟩ * ⟨c, d⟩ = ⟨a * c, b * d⟩`. -/
@[to_additive "Addition in an `add_localization` is defined as `⟨a, b⟩ + ⟨c, d⟩ = ⟨a + c, b + d⟩`.

Should not be confused with the ring localization counterpart `localization.add`, which maps
`⟨a, b⟩ + ⟨c, d⟩` to `⟨d * a + b * c, b * d⟩`.", irreducible]
protected def mul : localization S → localization S → localization S :=
(r S).comm_monoid.mul

@[to_additive] instance : has_mul (localization S) :=
⟨localization.mul S⟩

/-- The identity element of a localization is defined as `⟨1, 1⟩`. -/
@[to_additive "The identity element of an `add_localization` is defined as `⟨0, 0⟩`.

Should not be confused with the ring localization counterpart `localization.zero`,
which is defined as `⟨0, 1⟩`.", irreducible] protected def one : localization S :=
(r S).comm_monoid.one

@[to_additive] instance : has_one (localization S) :=
⟨localization.one S⟩

/-- Exponentiation in a localization is defined as `⟨a, b⟩ ^ n = ⟨a ^ n, b ^ n⟩`.

This is a separate `irreducible` def to ensure the elaborator doesn't waste its time
trying to unify some huge recursive definition with itself, but unfolded one step less.
-/
@[to_additive
"Multiplication with a natural in an `add_localization` is defined as `n • ⟨a, b⟩ = ⟨n • a, n • b⟩`.

This is a separate `irreducible` def to ensure the elaborator doesn't waste its time
trying to unify some huge recursive definition with itself, but unfolded one step less.",
irreducible]
protected def npow : ℕ → localization S → localization S :=
(r S).comm_monoid.npow

local attribute [semireducible] localization.mul localization.one localization.npow

@[to_additive] instance : comm_monoid (localization S) :=
{ mul := (*),
  one := 1,
  mul_assoc :=
    show ∀ (x y z : localization S), x * y * z = x * (y * z), from (r S).comm_monoid.mul_assoc,
  mul_comm := show ∀ (x y : localization S), x * y = y * x, from (r S).comm_monoid.mul_comm,
  mul_one := show ∀ (x : localization S), x * 1 = x, from (r S).comm_monoid.mul_one,
  one_mul := show ∀ (x : localization S), 1 * x = x, from (r S).comm_monoid.one_mul,
  npow := localization.npow S,
  npow_zero' := show ∀ (x : localization S), localization.npow S 0 x = 1, from pow_zero,
  npow_succ' := show ∀ (n : ℕ) (x : localization S),
    localization.npow S n.succ x = x * localization.npow S n x, from λ n x, pow_succ x n }

variables {S}

/-- Given a `comm_monoid` `M` and submonoid `S`, `mk` sends `x : M`, `y ∈ S` to the equivalence
class of `(x, y)` in the localization of `M` at `S`. -/
@[to_additive "Given an `add_comm_monoid` `M` and submonoid `S`, `mk` sends `x : M`, `y ∈ S` to
the equivalence class of `(x, y)` in the localization of `M` at `S`."]
def mk (x : M) (y : S) : localization S := (r S).mk' (x, y)

@[to_additive] theorem mk_eq_mk_iff {a c : M} {b d : S} :
  mk a b = mk c d ↔ r S ⟨a, b⟩ ⟨c, d⟩ :=
(r S).eq

universes u

/-- Dependent recursion principle for localizations: given elements `f a b : p (mk a b)`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d` (wih the correct coercions),
then `f` is defined on the whole `localization S`. -/
@[elab_as_eliminator, to_additive
"Dependent recursion principle for `add_localizations`: given elements `f a b : p (mk a b)`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d` (wih the correct coercions),
then `f` is defined on the whole `add_localization S`."]
def rec {p : localization S → Sort u}
  (f : ∀ (a : M) (b : S), p (mk a b))
  (H : ∀ {a c : M} {b d : S} (h : r S (a, b) (c, d)),
    (eq.rec (f a b) (mk_eq_mk_iff.mpr h) : p (mk c d)) = f c d)
  (x) : p x :=
quot.rec (λ y, eq.rec (f y.1 y.2) (prod.mk.eta : (y.1, y.2) = y))
  (λ y z h, by { cases y, cases z, exact H h }) x

attribute [irreducible] localization

@[to_additive] lemma mk_mul (a c : M) (b d : S) : mk a b * mk c d = mk (a * c) (b * d) := rfl
@[to_additive] lemma mk_one : mk 1 (1 : S) = 1 := rfl
@[to_additive] lemma mk_pow (n : ℕ) (a : M) (b : S) : (mk a b) ^ n = mk (a ^ n) (b ^ n) := rfl

@[simp, to_additive] lemma rec_mk {p : localization S → Sort u}
  (f : ∀ (a : M) (b : S), p (mk a b)) (H) (a : M) (b : S) :
  (rec f H (mk a b) : p (mk a b)) = f a b :=
rfl

/-- Non-dependent recursion principle for localizations: given elements `f a b : p`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d`,
then `f` is defined on the whole `localization S`. -/
@[elab_as_eliminator, to_additive
"Non-dependent recursion principle for `add_localizations`: given elements `f a b : p`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d`,
then `f` is defined on the whole `localization S`."]
def lift_on {p : Sort u} (x : localization S) (f : M → S → p)
  (H : ∀ {a c : M} {b d : S} (h : r S (a, b) (c, d)), f a b = f c d) : p :=
rec f (λ a c b d h, by rw [eq_rec_constant, H h]) x

@[to_additive] lemma lift_on_mk {p : Sort u}
  (f : ∀ (a : M) (b : S), p) (H) (a : M) (b : S) :
  lift_on (mk a b) f H = f a b :=
rfl

@[elab_as_eliminator, to_additive]
theorem ind {p : localization S → Prop}
  (H : ∀ (y : M × S), p (mk y.1 y.2)) (x) : p x :=
rec (λ a b, H (a, b)) (λ _ _ _ _ _, rfl) x

@[elab_as_eliminator, to_additive]
theorem induction_on {p : localization S → Prop} (x)
  (H : ∀ (y : M × S), p (mk y.1 y.2)) : p x := ind H x

/-- Non-dependent recursion principle for localizations: given elements `f x y : p`
for all `x` and `y`, such that `r S x x'` and `r S y y'` implies `f x y = f x' y'`,
then `f` is defined on the whole `localization S`. -/
@[elab_as_eliminator, to_additive
"Non-dependent recursion principle for localizations: given elements `f x y : p`
for all `x` and `y`, such that `r S x x'` and `r S y y'` implies `f x y = f x' y'`,
then `f` is defined on the whole `localization S`."]
def lift_on₂ {p : Sort u} (x y : localization S) (f : M → S → M → S → p)
  (H : ∀ {a a' b b' c c' d d'} (hx : r S (a, b) (a', b')) (hy : r S (c, d) (c', d')),
    f a b c d = f a' b' c' d') :
  p :=
lift_on x (λ a b, lift_on y (f a b) (λ c c' d d' hy, H ((r S).refl _) hy))
  (λ a a' b b' hx, induction_on y (λ ⟨c, d⟩, H hx ((r S).refl _)))

@[to_additive] lemma lift_on₂_mk {p : Sort*}
  (f : M → S → M → S → p) (H) (a c : M) (b d : S) :
  lift_on₂ (mk a b) (mk c d) f H = f a b c d :=
rfl

@[elab_as_eliminator, to_additive]
theorem induction_on₂ {p : localization S → localization S → Prop} (x y)
  (H : ∀ (x y : M × S), p (mk x.1 x.2) (mk y.1 y.2)) : p x y :=
induction_on x $ λ x, induction_on y $ H x

@[elab_as_eliminator, to_additive]
theorem induction_on₃
  {p : localization S → localization S → localization S → Prop} (x y z)
  (H : ∀ (x y z : M × S), p (mk x.1 x.2) (mk y.1 y.2) (mk z.1 z.2)) : p x y z :=
induction_on₂ x y $ λ x y, induction_on z $ H x y

@[to_additive] lemma one_rel (y : S) : r S 1 (y, y) := λ b hb, hb y

@[to_additive] theorem r_of_eq {x y : M × S} (h : y.1 * x.2 = x.1 * y.2) : r S x y :=
r_iff_exists.2 ⟨1, by rw h⟩

@[to_additive] lemma mk_self (a : S) : mk (a : M) a = 1 :=
by { symmetry, rw [← mk_one, mk_eq_mk_iff], exact one_rel a }

section scalar

variables {R R₁ R₂ : Type*}

/-- Scalar multiplication in a monoid localization is defined as `c • ⟨a, b⟩ = ⟨c • a, b⟩`. -/
@[irreducible] protected def smul [has_scalar R M] [is_scalar_tower R M M]
  (c : R) (z : localization S) : localization S :=
localization.lift_on z (λ a b, mk (c • a) b) $
  λ a a' b b' h, mk_eq_mk_iff.2
begin
  cases b with b hb,
  cases b' with b' hb',
  rw r_eq_r' at h ⊢,
  cases h with t ht,
  use t,
  simp only [smul_mul_assoc, ht]
end

instance [has_scalar R M] [is_scalar_tower R M M] :
  has_scalar R (localization S) :=
{ smul := localization.smul }

lemma smul_mk [has_scalar R M] [is_scalar_tower R M M] (c : R) (a b) :
  c • (mk a b : localization S) = mk (c • a) b :=
by { unfold has_scalar.smul localization.smul, apply lift_on_mk }

instance [has_scalar R₁ M] [has_scalar R₂ M] [is_scalar_tower R₁ M M] [is_scalar_tower R₂ M M]
  [smul_comm_class R₁ R₂ M] : smul_comm_class R₁ R₂ (localization S) :=
{ smul_comm := λ s t, localization.ind $ prod.rec $ by exact λ r x,
    by simp only [smul_mk, smul_comm s t r] }

instance [has_scalar R₁ M] [has_scalar R₂ M] [is_scalar_tower R₁ M M] [is_scalar_tower R₂ M M]
  [has_scalar R₁ R₂] [is_scalar_tower R₁ R₂ M] : is_scalar_tower R₁ R₂ (localization S) :=
{ smul_assoc := λ s t, localization.ind $ prod.rec $ by exact λ r x,
    by simp only [smul_mk, smul_assoc s t r] }

instance smul_comm_class_right {R : Type*} [has_scalar R M] [is_scalar_tower R M M] :
  smul_comm_class R (localization S) (localization S) :=
{ smul_comm := λ s, localization.ind $ prod.rec $ by exact λ r₁ x₁,
                    localization.ind $ prod.rec $ by exact λ r₂ x₂,
    by simp only [smul_mk, smul_eq_mul, mk_mul, mul_comm r₁, smul_mul_assoc] }

instance is_scalar_tower_right {R : Type*} [has_scalar R M] [is_scalar_tower R M M] :
  is_scalar_tower R (localization S) (localization S) :=
{ smul_assoc := λ s, localization.ind $ prod.rec $ by exact λ r₁ x₁,
                     localization.ind $ prod.rec $ by exact λ r₂ x₂,
    by simp only [smul_mk, smul_eq_mul, mk_mul, smul_mul_assoc] }

instance [has_scalar R M] [has_scalar Rᵐᵒᵖ M]  [is_scalar_tower R M M] [is_scalar_tower Rᵐᵒᵖ M M]
  [is_central_scalar R M] : is_central_scalar R (localization S) :=
{ op_smul_eq_smul := λ s, localization.ind $ prod.rec $ by exact λ r x,
    by simp only [smul_mk, op_smul_eq_smul] }

instance [monoid R] [mul_action R M] [is_scalar_tower R M M] : mul_action R (localization S) :=
{ one_smul := localization.ind $ prod.rec $
    by { intros, simp only [localization.smul_mk, one_smul] },
  mul_smul := λ s₁ s₂, localization.ind $ prod.rec $
    by { intros, simp only [localization.smul_mk, mul_smul] } }

instance [monoid R] [mul_distrib_mul_action R M] [is_scalar_tower R M M] :
  mul_distrib_mul_action R (localization S) :=
{ smul_one := λ s, by simp only [←localization.mk_one, localization.smul_mk, smul_one],
  smul_mul := λ s x y, localization.induction_on₂ x y $
    prod.rec $ by exact λ r₁ x₁, prod.rec $ by exact λ r₂ x₂,
      by simp only [localization.smul_mk, localization.mk_mul, smul_mul']}

end scalar

variables (S)

/-- Natural hom sending `x : M`, `M` a `comm_monoid`, to the equivalence class of
`(x, 1)` in the localization of `M` at a submonoid. -/
@[to_additive "Natural homomorphism sending `x : M`, `M` an `add_comm_monoid`, to the equivalence
class of `(x, 0)` in the localization of `M` at a submonoid."]
def monoid_of : submonoid.localization_map S (localization S) :=
{ to_fun := λ x, mk x 1,
  map_one' := mk_one,
  map_mul' := λ x y, by rw [mk_mul, mul_one],
  map_units' := λ y, is_unit_iff_exists_inv.2 ⟨mk 1 y, by rw [mk_mul, mul_one, one_mul, mk_self]⟩,
  surj' := λ z, induction_on z $ λ x, ⟨x,
    by rw [mk_mul, mul_comm x.fst, ← mk_mul, mk_self, one_mul]⟩,
  eq_iff_exists' := λ x y, mk_eq_mk_iff.trans $ r_iff_exists.trans $
    show (∃ (c : S), x * 1 * c = y * 1 * c) ↔ _, by rw [mul_one, mul_one],
  ..(r S).mk'.comp $ monoid_hom.inl M S }

variables {S}

@[to_additive] lemma mk_one_eq_monoid_of_mk (x) : mk x 1 = (monoid_of S).to_map x := rfl

@[to_additive] lemma mk_eq_monoid_of_mk'_apply (x y) : mk x y = (monoid_of S).mk' x y :=
show _ = _ * _, from (submonoid.localization_map.mul_inv_right (monoid_of S).map_units _ _ _).2 $
begin
  rw [←mk_one_eq_monoid_of_mk, ←mk_one_eq_monoid_of_mk,
      show mk x y * mk y 1 = mk (x * y) (1 * y), by rw [mul_comm 1 y, mk_mul],
      show mk x 1 = mk (x * 1) ((1 : S) * 1), by rw [mul_one, mul_one]],
  exact mk_eq_mk_iff.2 (con.symm _ $ (localization.r S).mul
    (con.refl _ (x, 1)) $ one_rel _),
end

@[simp, to_additive] lemma mk_eq_monoid_of_mk' : mk = (monoid_of S).mk' :=
funext $ λ _, funext $ λ _, mk_eq_monoid_of_mk'_apply _ _

@[simp, to_additive] lemma lift_on_mk' {p : Sort u}
  (f : ∀ (a : M) (b : S), p) (H) (a : M) (b : S) :
  lift_on ((monoid_of S).mk' a b) f H = f a b :=
by rw [← mk_eq_monoid_of_mk', lift_on_mk]

@[simp, to_additive] lemma lift_on₂_mk' {p : Sort*}
  (f : M → S → M → S → p) (H) (a c : M) (b d : S) :
  lift_on₂ ((monoid_of S).mk' a b) ((monoid_of S).mk' c d) f H = f a b c d :=
by rw [← mk_eq_monoid_of_mk', lift_on₂_mk]

variables (f : submonoid.localization_map S N)
/-- Given a localization map `f : M →* N` for a submonoid `S`, we get an isomorphism between
the localization of `M` at `S` as a quotient type and `N`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S`, we get an isomorphism
between the localization of `M` at `S` as a quotient type and `N`."]
noncomputable def mul_equiv_of_quotient (f : submonoid.localization_map S N) :
  localization S ≃* N :=
(monoid_of S).mul_equiv_of_localizations f

variables {f}

@[simp, to_additive] lemma mul_equiv_of_quotient_apply (x) :
  mul_equiv_of_quotient f x = (monoid_of S).lift f.map_units x := rfl

@[simp, to_additive] lemma mul_equiv_of_quotient_mk' (x y) :
  mul_equiv_of_quotient f ((monoid_of S).mk' x y) = f.mk' x y :=
(monoid_of S).lift_mk' _ _ _

@[to_additive] lemma mul_equiv_of_quotient_mk (x y) :
  mul_equiv_of_quotient f (mk x y) = f.mk' x y :=
by rw mk_eq_monoid_of_mk'_apply; exact mul_equiv_of_quotient_mk' _ _

@[simp, to_additive] lemma mul_equiv_of_quotient_monoid_of (x) :
  mul_equiv_of_quotient f ((monoid_of S).to_map x) = f.to_map x :=
(monoid_of S).lift_eq _ _

@[simp, to_additive] lemma mul_equiv_of_quotient_symm_mk' (x y) :
  (mul_equiv_of_quotient f).symm (f.mk' x y) = (monoid_of S).mk' x y :=
f.lift_mk' _ _ _

@[to_additive] lemma mul_equiv_of_quotient_symm_mk (x y) :
  (mul_equiv_of_quotient f).symm (f.mk' x y) = mk x y :=
by rw mk_eq_monoid_of_mk'_apply; exact mul_equiv_of_quotient_symm_mk' _ _

@[simp, to_additive] lemma mul_equiv_of_quotient_symm_monoid_of (x) :
  (mul_equiv_of_quotient f).symm (f.to_map x) = (monoid_of S).to_map x :=
f.lift_eq _ _

end localization

end comm_monoid

section comm_monoid_with_zero

namespace localization

variables {M : Type*} [comm_monoid_with_zero M] (S : submonoid M)

local attribute [semireducible] localization

/-- The zero element in a localization is defined as `(0, 1)`.

Should not be confused with `add_localization.zero` which is `(0, 0)`. -/
@[irreducible] protected def zero : localization S :=
mk 0 1

instance : has_zero (localization S) :=⟨localization.zero S⟩

local attribute [semireducible] localization.zero localization.mul

instance : comm_monoid_with_zero (localization S) :=
by refine_struct
{ zero := 0, .. localization.comm_monoid S };
  exact λ x, localization.induction_on x $ by
  { intros,
    refine mk_eq_mk_iff.mpr (r_of_eq _),
    simp only [zero_mul, mul_zero] }

attribute [irreducible] localization

variables {S}

lemma mk_zero (x : S) : mk 0 (x : S) = 0 :=
calc mk 0 x = mk 0 1  : mk_eq_mk_iff.mpr (r_of_eq (by simp))
        ... = 0       : rfl

lemma lift_on_zero {p : Type*} (f : ∀ (x : M) (y : S), p) (H) : lift_on 0 f H = f 0 1 :=
by rw [← mk_zero 1, lift_on_mk]

end localization

end comm_monoid_with_zero
