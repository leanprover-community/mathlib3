/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import group_theory.monoid_localization
import ring_theory.localization.basic

/-!
# Localized Module

Given a commutative ring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can localize
`M` by `S`. This gives us a `localization S`-module.

## Main definitions

* `localized_module.r` : the equivalence relation defining this localization, namely
  `(m, s) ≈ (m', s')` if and only if if there is some `u : S` such that `u • s' • m = u • s • m'`.
* `localized_module M S` : the localized module by `S`.
* `localized_module.mk`  : the canonical map sending `(m, s) : M × S ↦ m/s : localized_module M S`
* `localized_module.lift_on` : any well defined function `f : M × S → α` respecting `r` descents to
  a function `localized_module M S → α`
* `localized_module.lift_on₂` : any well defined function `f : M × S → M × S → α` respecting `r`
  descents to a function `localized_module M S → localized_module M S`
* `localized_module.mk_add_mk` : in the localized module
  `mk m s + mk m' s' = mk (s' • m + s • m') (s * s')`
* `localized_module.mk_smul_mk` : in the localized module, for any `r : R`, `s t : S`, `m : M`,
  we have `mk r s • mk m t = mk (r • m) (s * t)` where `mk r s : localization S` is localized ring
  by `S`.
* `localized_module.is_module` : `localized_module M S` is a `localization S`-module.

-/


namespace localized_module

universes u v

variables {R : Type u} [comm_semiring R] (S : submonoid R)
variables (M : Type v) [add_comm_monoid M] [module R M]

/--The equivalence relation on `M × S` where `(m1, s1) ≈ (m2, s2)` if and only if
for some (u : S), u * (s2 • m1 - s1 • m2) = 0-/
def r (p1 p2 : M × S) : Prop :=
match p1, p2 with
| ⟨m1, s1⟩, ⟨m2, s2⟩ := ∃ (u : S), u • s1 • m2 = u • s2 • m1
end

lemma r.is_equiv : is_equiv _ (r S M) :=
{ refl := λ ⟨m, s⟩, ⟨1, by rw [one_smul]⟩,
  trans := λ ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m3, s3⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩, begin
    use u1 * u2 * s2,
    rw calc (u1 * u2 * s2) • s1 • m3
        = (u1 * u2 * s2 * s1) • m3 : by simp only [mul_smul]
    ... = (u1 * s1 * (u2 * s2)) • m3 : by congr' 1; ext; simp only [submonoid.coe_mul]; ring
    ... = (u1 * s1) • u2 • s2 • m3 : by simp only [mul_smul]
    ... = (u1 * s1) • u2 • s3 • m2 : by rw [hu2]
    ... = (u1 * s1 * (u2 * s3)) • m2 : by simp only [mul_smul]
    ... = (u2 * s3 * (u1 * s1)) • m2 : by congr' 1; ext; simp only [submonoid.coe_mul]; ring
    ... = (u2 * s3) • u1 • s1 • m2 : by simp only [mul_smul]
    ... = (u2 * s3) • u1 • s2 • m1 : by rw [hu1]
    ... = ((u2 * s3) * u1 * s2) • m1 : by simp only [mul_smul],
    rw [← mul_smul],
    congr' 1,
    ext,
    simp only [submonoid.coe_mul],
    ring
  end,
  symm := λ ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨u, hu⟩, ⟨u, hu.symm⟩ }


instance r.setoid : setoid (M × S) :=
{ r := r S M,
  iseqv := ⟨(r.is_equiv S M).refl, (r.is_equiv S M).symm, (r.is_equiv S M).trans⟩ }

/--
If `S` is a multiplicative subset of a ring `R` and `M` an `R`-module, then
we can localize `M` by `S`.
-/
@[nolint has_inhabited_instance]
def _root_.localized_module : Type (max u v) := quotient (r.setoid S M)

section
variables {M S}

/--The canonical map sending `(m, s) ↦ m/s`-/
def mk (m : M) (s : S) : localized_module S M :=
quotient.mk ⟨m, s⟩

lemma mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔ ∃ (u : S), u • s • m' = u • s' • m :=
quotient.eq

@[elab_as_eliminator]
lemma induction_on {β : localized_module S M → Prop} (h : ∀ (m : M) (s : S), β (mk m s)) :
  ∀ (x : localized_module S M), β x :=
by { rintro ⟨⟨m, s⟩⟩, exact h m s }

@[elab_as_eliminator]
lemma induction_on₂ {β : localized_module S M → localized_module S M → Prop}
  (h : ∀ (m m' : M) (s s' : S), β (mk m s) (mk m' s')) : ∀ x y, β x y :=
by { rintro ⟨⟨m, s⟩⟩ ⟨⟨m', s'⟩⟩, exact h m m' s s' }

/--If `f : M × S → α` respects the equivalence relation `localized_module.r`, then
`f` descents to a map `localized_module M S → α`.
-/
def lift_on {α : Type*} (x : localized_module S M) (f : M × S → α)
  (wd : ∀ (p p' : M × S) (h1 : p ≈ p'), f p = f p') : α :=
quotient.lift_on x f wd

lemma lift_on_mk {α : Type*} {f : M × S → α}
  (wd : ∀ (p p' : M × S) (h1 : p ≈ p'), f p = f p')
  (m : M) (s : S) :
  lift_on (mk m s) f wd = f ⟨m, s⟩ :=
by convert quotient.lift_on_mk f wd ⟨m, s⟩

/--If `f : M × S → M × S → α` respects the equivalence relation `localized_module.r`, then
`f` descents to a map `localized_module M S → localized_module M S → α`.
-/
def lift_on₂ {α : Type*} (x y : localized_module S M) (f : (M × S) → (M × S) → α)
  (wd : ∀ (p q p' q' : M × S) (h1 : p ≈ p') (h2 : q ≈ q'), f p q = f p' q') : α :=
quotient.lift_on₂ x y f wd

lemma lift_on₂_mk {α : Type*} (f : (M × S) → (M × S) → α)
  (wd : ∀ (p q p' q' : M × S) (h1 : p ≈ p') (h2 : q ≈ q'), f p q = f p' q')
  (m m' : M) (s s' : S) :
  lift_on₂ (mk m s) (mk m' s') f wd = f ⟨m, s⟩ ⟨m', s'⟩ :=
by convert quotient.lift_on₂_mk f wd _ _

instance : has_zero (localized_module S M) := ⟨mk 0 1⟩
lemma zero_mk (s : S) : mk (0 : M) s = 0 :=
mk_eq.mpr ⟨1, by rw [one_smul, smul_zero, smul_zero, one_smul]⟩

instance : has_add (localized_module S M) :=
{ add := λ p1 p2, lift_on₂ p1 p2 (λ x y, mk (y.2 • x.1 + x.2 • y.1) (x.2 * y.2)) $
    λ ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m1', s1'⟩ ⟨m2', s2'⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩, mk_eq.mpr ⟨u1 * u2, begin
      calc (u1 * u2) • (s1 * s2) • (s2' • m1' + s1' • m2')
          = (u1 * u2) • (s1 * s2) • s2' • m1' + (u1 * u2) • (s1 * s2) • s1' • m2'
          : by simp only [smul_add]
      ... = (u1 * u2 * (s1 * s2) * s2') • m1' + (u1 * u2 * (s1 * s2) * s1') • m2'
          : by simp only [mul_smul]
      ... = ((u2 * s2 * s2') * (u1 * s1)) • m1' + (u1 * u2 * (s1 * s2) * s1') • m2'
          : by congr' 2; ext; simp only [submonoid.coe_mul]; ring
      ... = (u2 * s2 * s2') • u1 • s1 • m1' + (u1 * u2 * (s1 * s2) * s1') • m2'
          : by simp only [mul_smul]
      ... = (u2 * s2 * s2') • u1 • s1' • m1 + (u1 * u2 * (s1 * s2) * s1') • m2' : by rw [hu1]
      ... = ((u2 * s2 * s2') * u1 * s1') • m1 + (u1 * u2 * (s1 * s2) * s1') • m2'
          : by simp only [mul_smul]
      ... = ((u1 * u2) * (s1' * s2') * s2) • m1 + (u1 * u2 * (s1 * s2) * s1') • m2'
          : by congr' 2; ext; simp only [submonoid.coe_mul]; ring
      ... = (u1 * u2) • (s1' • s2') • s2 • m1 + (u1 * u2 * (s1 * s2) * s1') • m2'
          : by congr' 1; simp [mul_smul]
      ... = (u1 * u2) • (s1' • s2') • s2 • m1 + ((u1 * s1 * s1') * (u2 * s2)) • m2'
          : by congr' 2; ext; simp only [submonoid.coe_mul]; ring
      ... = (u1 * u2) • (s1' • s2') • s2 • m1 + (u1 * s1 * s1') • u2 • s2 • m2'
          : by simp [mul_smul]
      ... = (u1 * u2) • (s1' • s2') • s2 • m1 + (u1 * s1 * s1') • u2 • s2' • m2 : by rw [hu2]
      ... = (u1 * u2) • (s1' • s2') • s2 • m1 + ((u1 * s1 * s1') * (u2 * s2')) • m2
          : by simp [mul_smul]
      ... = (u1 * u2) • (s1' • s2') • s2 • m1 + ((u1 * u2) * (s1' * s2') * s1) • m2
          : by congr' 2; ext; simp only [submonoid.coe_mul]; ring
      ... = (u1 * u2) • (s1' • s2') • s2 • m1 + (u1 * u2) • (s1' • s2') • s1 • m2
          : by simp [mul_smul]
      ... = (u1 * u2) • (s1' * s2') • (s2 • m1 + s1 • m2) : by simp [smul_add],
    end⟩ }

lemma mk_add_mk {m1 m2 : M} {s1 s2 : S} :
  mk m1 s1 + mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2) :=
mk_eq.mpr $ ⟨1, by dsimp only; rw [one_smul]⟩

lemma add_assoc' (x y z : localized_module S M) :
  x + y + z = x + (y + z) :=
begin
  induction x using localized_module.induction_on with mx sx,
  induction y using localized_module.induction_on with my sy,
  induction z using localized_module.induction_on with mz sz,
  simp [mk_add_mk],
  refine mk_eq.mpr ⟨1, _⟩,
  rw [one_smul, one_smul],
  congr' 1,
  { rw [mul_assoc] },
  { rw [mul_comm, add_assoc, mul_smul, mul_smul, ←mul_smul sx sz, mul_comm, mul_smul], },
end

lemma add_comm' (x y : localized_module S M) :
  x + y = y + x :=
localized_module.induction_on₂ (λ m m' s s', by rw [mk_add_mk, mk_add_mk, add_comm, mul_comm]) x y

lemma zero_add' (x : localized_module S M) : 0 + x = x :=
induction_on (λ m s, by rw [← zero_mk s, mk_add_mk, smul_zero, zero_add, mk_eq];
  exact ⟨1, by rw [one_smul, mul_smul, one_smul]⟩) x

lemma add_zero' (x : localized_module S M) : x + 0 = x :=
induction_on (λ m s, by rw [← zero_mk s, mk_add_mk, smul_zero, add_zero, mk_eq];
  exact ⟨1, by rw [one_smul, mul_smul, one_smul]⟩) x

instance has_nat_scalar : has_scalar ℕ (localized_module S M) :=
{ smul := λ n, nat.rec_on n (λ x, 0) (λ m f x, x + f x) }

lemma nsmul_zero' (x : localized_module S M) : (0 : ℕ) • x = 0 :=
localized_module.induction_on (λ _ _, rfl) x
lemma nsmul_succ' (n : ℕ) (x : localized_module S M) :
  n.succ • x = x + n • x :=
localized_module.induction_on (λ _ _, rfl) x

instance : add_comm_monoid (localized_module S M) :=
{ add := (+),
  add_assoc := add_assoc',
  zero := 0,
  zero_add := zero_add',
  add_zero := add_zero',
  nsmul := (•),
  nsmul_zero' := nsmul_zero',
  nsmul_succ' := nsmul_succ',
  add_comm := add_comm' }

instance : has_scalar (localization S) (localized_module S M) :=
{ smul := λ f x, localization.lift_on f (λ r s, lift_on x (λ p, mk (r • p.1) (s * p.2))
    begin
      rintros ⟨m1, t1⟩ ⟨m2, t2⟩ ⟨u, h⟩,
      refine mk_eq.mpr ⟨u, _⟩,
      dsimp only,
      calc u • (s * t1) • r • m2
          = ((u : R) * (s * t1) * r) • m2 : by simp only [mul_smul]; congr
      ... = ((s : R) * r * (u * t1)) • m2 : by congr' 1; ring
      ... = ((s : R) * r) • u • t1 • m2 : by simp only [mul_smul]; congr
      ... = ((s : R) * r) • u • t2 • m1 : by rw [h]
      ... = ((s : R) * r * (u * t2)) • m1 : by simp only [mul_smul]; congr
      ... = ((u : R) * (s * t2) * r) • m1 : by congr' 1; ring
      ... = u • (s * t2) • r • m1 : by simp only [mul_smul]; congr,
    end) begin
      induction x using localized_module.induction_on with m t,
      rintros r r' s s' h,
      dsimp only,
      rw [lift_on_mk, lift_on_mk],
      rw localization.r_iff_exists at h,
      rcases h with ⟨u, eq1⟩,
      rw mk_eq,
      simp only at eq1 ⊢,
      refine ⟨u, _⟩,
      calc u • (s * t) • r' • m
          = ((u : R) * (s * t) * r') • m : by simp only [mul_smul]; congr
      ... = ((t : R) * (r' * s * u)) • m : by congr' 1; ring
      ... = ((t : R) * (r * s' * u)) • m : by rw [eq1]
      ... = ((u : R) * (s' * t) * r) • m : by congr' 1; ring
      ... = u • (s' * t) • r • m : by simp only [mul_smul]; congr,
    end }

lemma mk_smul_mk (r : R) (m : M) (s t : S) :
  localization.mk r s • mk m t = mk (r • m) (s * t) :=
begin
  unfold has_scalar.smul,
  rw [localization.lift_on_mk, lift_on_mk],
end

lemma one_smul' (m : localized_module S M) :
  (1 : localization S) • m = m :=
begin
  induction m using localized_module.induction_on with m s,
  rw [← localization.mk_one, mk_smul_mk, one_smul, one_mul],
end

lemma mul_smul' (x y : localization S) (m : localized_module S M) :
  (x * y) • m = x • y • m :=
begin
  induction x using localization.induction_on with data,
  induction y using localization.induction_on with data',
  rcases ⟨data, data'⟩ with ⟨⟨r, s⟩, ⟨r', s'⟩⟩,

  induction m using localized_module.induction_on with m t,
  rw [localization.mk_mul, mk_smul_mk, mk_smul_mk, mk_smul_mk, mul_smul, mul_assoc],
end

lemma smul_add' (x : localization S) (y z : localized_module S M) :
  x • (y + z) = x • y + x • z :=
begin
  induction x using localization.induction_on with data,
  rcases data with ⟨r, u⟩,
  induction y using localized_module.induction_on with m s,
  induction z using localized_module.induction_on with n t,
  dsimp only,
  rw [mk_smul_mk, mk_smul_mk, mk_add_mk, mk_smul_mk, mk_add_mk],
  refine mk_eq.mpr _,
  refine ⟨1, _⟩,
  rw [one_smul, one_smul],
  calc (u * (s * t)) • ((u * t) • r • m + (u * s) • r • n)
      = (u * (s * t)) • (u * t) • r • m + (u * (s * t)) • (u * s) • r • n : by rw [smul_add]
  ... = ((u : R) * (s * t) * (u * t) * r) • m + ((u : R) * (s * t) * (u * s) * r) • n
      : by simp only [mul_smul]; congr
  ... = ((u : R) * s * (u * t) * r * t) • m + ((u : R) * s * (u * t) * r * s) • n
      : by congr' 2; ring
  ... = ((u : R) * s * (u * t)) • r • t • m + (u * s * (u * t)) • r • s • n
      : by simp only [mul_smul]; congr
  ... = (u * s * (u * t)) • r • (t • m + s • n) : by simp [smul_add]; congr,
end

lemma smul_zero' (x : localization S) :
  x • (0 : localized_module S M) = 0 :=
begin
  induction x using localization.induction_on with data,
  rcases data with ⟨r, s⟩,
  rw [←zero_mk s, mk_smul_mk, smul_zero, zero_mk, zero_mk],
end

lemma add_smul' (x y : localization S) (z : localized_module S M) :
  (x + y) • z = x • z + y • z :=
begin
  induction x using localization.induction_on with datax,
  induction y using localization.induction_on with datay,
  induction z using localized_module.induction_on with m t,
  rcases ⟨datax, datay⟩ with ⟨⟨r, s⟩, ⟨r', s'⟩⟩,
  rw [localization.add_mk, mk_smul_mk, mk_smul_mk, mk_smul_mk, mk_add_mk],
  refine mk_eq.mpr ⟨1, _⟩,
  rw [one_smul, one_smul],
  dsimp only,
  calc (s * s' * t) • ((s' * t) • r • m + (s * t) • r' • m)
      = (s * s' * t) • (s' * t) • r • m + (s * s' * t) • (s * t) • r' • m : by rw [smul_add]
  ... = ((s : R) * s' * t * (s' * t) * r) • m + ((s : R) * s' * t * (s * t) * r') • m
      : by simp only [mul_smul]; congr
  ... = ((s : R) * t * (s' * t) * s * r') • m + ((s : R) * t * (s' * t) * s' * r) • m
      : by rw add_comm; congr' 2; ring
  ... = (((s : R) * t * (s' * t) * s * r') + ((s : R) * t * (s' * t) * s' * r)) • m
      : by rw add_smul
  ... = ((s : R) * t * (s' * t) * (s * r' + s' * r)) • m : by congr' 2 ; ring
  ... = (s * t * (s' * t)) • ((s : R) * r' + (s' : R) * r) • m : by simp only [mul_smul]; congr
  ... = (s * t * (s' * t)) • ((s : R) * r' + (s' : R) * r) • m : by simp [add_smul]; congr,
end

lemma zero_smul' (x : localized_module S M) :
  (0 : localization S) • x = 0 :=
begin
  induction x using localized_module.induction_on with m s,
  rw [← localization.mk_zero s, mk_smul_mk, zero_smul, zero_mk],
end

instance is_module : module (localization S) (localized_module S M) :=
{ smul := (•),
  one_smul := one_smul',
  mul_smul := mul_smul',
  smul_add := smul_add',
  smul_zero := smul_zero',
  add_smul := add_smul',
  zero_smul := zero_smul' }

end

end localized_module
