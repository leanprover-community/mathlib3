/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/

import group_theory.monoid_localization
import ring_theory.localization.basic
import algebra.algebra.restrict_scalars

/-!
# Localized Module

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

## Future work

 * Redefine `localization` for monoids and rings to coincide with `localized_module`.
-/


namespace localized_module

universes u v

variables {R : Type u} [comm_semiring R] (S : submonoid R)
variables (M : Type v) [add_comm_monoid M] [module R M]

/--The equivalence relation on `M × S` where `(m1, s1) ≈ (m2, s2)` if and only if
for some (u : S), u * (s2 • m1 - s1 • m2) = 0-/
def r (a b : M × S) : Prop :=
∃ (u : S), u • b.2 • a.1 = u • a.2 • b.1

lemma r.is_equiv : is_equiv _ (r S M) :=
{ refl := λ ⟨m, s⟩, ⟨1, by rw [one_smul]⟩,
  trans := λ ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m3, s3⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩, begin
    use u1 * u2 * s2,
    -- Put everything in the same shape, sorting the terms using `simp`
    have hu1' := congr_arg ((•) (u2 * s3)) hu1.symm,
    have hu2' := congr_arg ((•) (u1 * s1)) hu2.symm,
    simp only [← mul_smul, smul_assoc, mul_assoc, mul_comm, mul_left_comm] at ⊢ hu1' hu2',
    rw [hu2', hu1']
  end,
  symm := λ ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨u, hu⟩, ⟨u, hu.symm⟩ }

instance r.setoid : setoid (M × S) :=
{ r := r S M,
  iseqv := ⟨(r.is_equiv S M).refl, (r.is_equiv S M).symm, (r.is_equiv S M).trans⟩ }

-- TODO: change `localization` to use `r'` instead of `r` so that the two types are also defeq,
-- `localization S = localized_module S R`.
example {R} [comm_semiring R] (S : submonoid R) : ⇑(localization.r' S) = localized_module.r S R :=
rfl

/--
If `S` is a multiplicative subset of a ring `R` and `M` an `R`-module, then
we can localize `M` by `S`.
-/
@[nolint has_nonempty_instance]
def _root_.localized_module : Type (max u v) := quotient (r.setoid S M)

section
variables {M S}

/--The canonical map sending `(m, s) ↦ m/s`-/
def mk (m : M) (s : S) : localized_module S M :=
quotient.mk ⟨m, s⟩

lemma mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔ ∃ (u : S), u • s' • m = u • s • m' :=
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
@[simp] lemma zero_mk (s : S) : mk (0 : M) s = 0 :=
mk_eq.mpr ⟨1, by rw [one_smul, smul_zero, smul_zero, one_smul]⟩

instance : has_add (localized_module S M) :=
{ add := λ p1 p2, lift_on₂ p1 p2 (λ x y, mk (y.2 • x.1 + x.2 • y.1) (x.2 * y.2)) $
    λ ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m1', s1'⟩ ⟨m2', s2'⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩, mk_eq.mpr ⟨u1 * u2, begin
      -- Put everything in the same shape, sorting the terms using `simp`
      have hu1' := congr_arg ((•) (u2 * s2 * s2')) hu1,
      have hu2' := congr_arg ((•) (u1 * s1 * s1')) hu2,
      simp only [smul_add, ← mul_smul, smul_assoc, mul_assoc, mul_comm, mul_left_comm]
        at ⊢ hu1' hu2',
      rw [hu1', hu2']
    end⟩ }

lemma mk_add_mk {m1 m2 : M} {s1 s2 : S} :
  mk m1 s1 + mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2) :=
mk_eq.mpr $ ⟨1, by dsimp only; rw [one_smul]⟩

private lemma add_assoc' (x y z : localized_module S M) :
  x + y + z = x + (y + z) :=
begin
  induction x using localized_module.induction_on with mx sx,
  induction y using localized_module.induction_on with my sy,
  induction z using localized_module.induction_on with mz sz,
  simp only [mk_add_mk, smul_add],
  refine mk_eq.mpr ⟨1, _⟩,
  rw [one_smul, one_smul],
  congr' 1,
  { rw [mul_assoc] },
  { rw [eq_comm, mul_comm, add_assoc, mul_smul, mul_smul, ←mul_smul sx sz, mul_comm, mul_smul], },
end

private lemma add_comm' (x y : localized_module S M) :
  x + y = y + x :=
localized_module.induction_on₂ (λ m m' s s', by rw [mk_add_mk, mk_add_mk, add_comm, mul_comm]) x y

private lemma zero_add' (x : localized_module S M) : 0 + x = x :=
induction_on (λ m s, by rw [← zero_mk s, mk_add_mk, smul_zero, zero_add, mk_eq];
  exact ⟨1, by rw [one_smul, mul_smul, one_smul]⟩) x

private lemma add_zero' (x : localized_module S M) : x + 0 = x :=
induction_on (λ m s, by rw [← zero_mk s, mk_add_mk, smul_zero, add_zero, mk_eq];
  exact ⟨1, by rw [one_smul, mul_smul, one_smul]⟩) x

instance has_nat_smul : has_smul ℕ (localized_module S M) :=
{ smul := λ n, nsmul_rec n }

private lemma nsmul_zero' (x : localized_module S M) : (0 : ℕ) • x = 0 :=
localized_module.induction_on (λ _ _, rfl) x
private lemma nsmul_succ' (n : ℕ) (x : localized_module S M) :
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

instance {M : Type*} [add_comm_group M] [module R M] :
  add_comm_group (localized_module S M) :=
{ neg := λ p, lift_on p (λ x, localized_module.mk (-x.1) x.2)
    (λ ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨u, hu⟩, by { rw mk_eq, exact ⟨u, by simpa⟩ }),
  add_left_neg := λ p, begin
    obtain ⟨⟨m, s⟩, rfl : mk m s = p⟩ := quotient.exists_rep p,
    change (mk m s).lift_on (λ x, mk (-x.1) x.2)
      (λ ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨u, hu⟩, by { rw mk_eq, exact ⟨u, by simpa⟩ }) + mk m s = 0,
    rw [lift_on_mk, mk_add_mk],
    simp
  end,
  ..(show add_comm_monoid (localized_module S M), by apply_instance) }

lemma mk_neg {M : Type*} [add_comm_group M] [module R M] {m : M} {s : S} :
  mk (-m) s = - mk m s := rfl

instance {A : Type*} [semiring A] [algebra R A] {S : submonoid R} :
  semiring (localized_module S A) :=
{ mul := λ m₁ m₂, lift_on₂ m₁ m₂ (λ x₁ x₂, localized_module.mk (x₁.1 * x₂.1) (x₁.2 * x₂.2))
    (begin
      rintros ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨b₁, t₁⟩ ⟨b₂, t₂⟩ ⟨u₁, e₁⟩ ⟨u₂, e₂⟩,
      rw mk_eq,
      use u₁ * u₂,
      dsimp only at ⊢ e₁ e₂,
      rw eq_comm,
      transitivity (u₁ • t₁ • a₁) • u₂ • t₂ • a₂,
      rw [e₁, e₂], swap, rw eq_comm,
      all_goals { rw [smul_smul, mul_mul_mul_comm, ← smul_eq_mul, ← smul_eq_mul A,
        smul_smul_smul_comm, mul_smul, mul_smul] }
    end),
  left_distrib := begin
    intros x₁ x₂ x₃,
    obtain ⟨⟨a₁, s₁⟩, rfl : mk a₁ s₁ = x₁⟩ := quotient.exists_rep x₁,
    obtain ⟨⟨a₂, s₂⟩, rfl : mk a₂ s₂ = x₂⟩ := quotient.exists_rep x₂,
    obtain ⟨⟨a₃, s₃⟩, rfl : mk a₃ s₃ = x₃⟩ := quotient.exists_rep x₃,
    apply mk_eq.mpr _,
    use 1,
    simp only [one_mul, smul_add, mul_add, mul_smul_comm, smul_smul, ← mul_assoc, mul_right_comm]
  end,
  right_distrib := begin
    intros x₁ x₂ x₃,
    obtain ⟨⟨a₁, s₁⟩, rfl : mk a₁ s₁ = x₁⟩ := quotient.exists_rep x₁,
    obtain ⟨⟨a₂, s₂⟩, rfl : mk a₂ s₂ = x₂⟩ := quotient.exists_rep x₂,
    obtain ⟨⟨a₃, s₃⟩, rfl : mk a₃ s₃ = x₃⟩ := quotient.exists_rep x₃,
    apply mk_eq.mpr _,
    use 1,
    simp only [one_mul, smul_add, add_mul, smul_smul, ← mul_assoc, smul_mul_assoc, mul_right_comm],
  end,
  zero_mul := begin
    intros x,
    obtain ⟨⟨a, s⟩, rfl : mk a s = x⟩ := quotient.exists_rep x,
    exact mk_eq.mpr ⟨1, by simp only [zero_mul, smul_zero]⟩,
  end,
  mul_zero := begin
    intros x,
    obtain ⟨⟨a, s⟩, rfl : mk a s = x⟩ := quotient.exists_rep x,
    exact mk_eq.mpr ⟨1, by simp only [mul_zero, smul_zero]⟩,
  end,
  mul_assoc := begin
    intros x₁ x₂ x₃,
    obtain ⟨⟨a₁, s₁⟩, rfl : mk a₁ s₁ = x₁⟩ := quotient.exists_rep x₁,
    obtain ⟨⟨a₂, s₂⟩, rfl : mk a₂ s₂ = x₂⟩ := quotient.exists_rep x₂,
    obtain ⟨⟨a₃, s₃⟩, rfl : mk a₃ s₃ = x₃⟩ := quotient.exists_rep x₃,
    apply mk_eq.mpr _,
    use 1,
    simp only [one_mul, smul_smul, ← mul_assoc, mul_right_comm],
  end,
  one := mk 1 (1 : S),
  one_mul := begin
    intros x,
    obtain ⟨⟨a, s⟩, rfl : mk a s = x⟩ := quotient.exists_rep x,
    exact mk_eq.mpr ⟨1, by simp only [one_mul, one_smul]⟩,
  end,
  mul_one := begin
    intros x,
    obtain ⟨⟨a, s⟩, rfl : mk a s = x⟩ := quotient.exists_rep x,
    exact mk_eq.mpr ⟨1, by simp only [mul_one, one_smul]⟩,
  end,
  ..(show add_comm_monoid (localized_module S A), by apply_instance) }

instance {A : Type*} [comm_semiring A] [algebra R A] {S : submonoid R} :
  comm_semiring (localized_module S A) :=
{ mul_comm := begin
    intros x₁ x₂,
    obtain ⟨⟨a₁, s₁⟩, rfl : mk a₁ s₁ = x₁⟩ := quotient.exists_rep x₁,
    obtain ⟨⟨a₂, s₂⟩, rfl : mk a₂ s₂ = x₂⟩ := quotient.exists_rep x₂,
    exact mk_eq.mpr ⟨1, by simp only [one_smul, mul_comm]⟩
  end,
  ..(show semiring (localized_module S A), by apply_instance) }

instance {A : Type*} [ring A] [algebra R A] {S : submonoid R} :
  ring (localized_module S A) :=
{ ..(show add_comm_group (localized_module S A), by apply_instance),
  ..(show monoid (localized_module S A), by apply_instance),
  ..(show distrib (localized_module S A), by apply_instance) }

instance {A : Type*} [comm_ring A] [algebra R A] {S : submonoid R} :
  comm_ring (localized_module S A) :=
{ mul_comm := begin
    intros x₁ x₂,
    obtain ⟨⟨a₁, s₁⟩, rfl : mk a₁ s₁ = x₁⟩ := quotient.exists_rep x₁,
    obtain ⟨⟨a₂, s₂⟩, rfl : mk a₂ s₂ = x₂⟩ := quotient.exists_rep x₂,
    exact mk_eq.mpr ⟨1, by simp only [one_smul, mul_comm]⟩
  end,
  ..(show ring (localized_module S A), by apply_instance) }

lemma mk_mul_mk {A : Type*} [semiring A] [algebra R A] {a₁ a₂ : A} {s₁ s₂ : S} :
  mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₁ * s₂) :=
rfl

instance : has_smul (localization S) (localized_module S M) :=
{ smul := λ f x, localization.lift_on f (λ r s, lift_on x (λ p, mk (r • p.1) (s * p.2))
    begin
      rintros ⟨m1, t1⟩ ⟨m2, t2⟩ ⟨u, h⟩,
      refine mk_eq.mpr ⟨u, _⟩,
      have h' := congr_arg ((•) (s • r)) h,
      simp only [← mul_smul, smul_assoc, mul_comm, mul_left_comm, submonoid.smul_def,
        submonoid.coe_mul] at ⊢ h',
      rw h',
    end) begin
      induction x using localized_module.induction_on with m t,
      rintros r r' s s' h,
      simp only [lift_on_mk, lift_on_mk, mk_eq],
      obtain ⟨u, eq1⟩ := localization.r_iff_exists.mp h,
      use u,
      have eq1' := congr_arg (• (t • m)) eq1,
      simp only [← mul_smul, smul_assoc, submonoid.smul_def, submonoid.coe_mul] at ⊢ eq1',
      ring_nf at ⊢ eq1',
      rw eq1'
    end }

lemma mk_smul_mk (r : R) (m : M) (s t : S) :
  localization.mk r s • mk m t = mk (r • m) (s * t) :=
begin
  unfold has_smul.smul,
  rw [localization.lift_on_mk, lift_on_mk],
end

private lemma one_smul' (m : localized_module S M) :
  (1 : localization S) • m = m :=
begin
  induction m using localized_module.induction_on with m s,
  rw [← localization.mk_one, mk_smul_mk, one_smul, one_mul],
end

private lemma mul_smul' (x y : localization S) (m : localized_module S M) :
  (x * y) • m = x • y • m :=
begin
  induction x using localization.induction_on with data,
  induction y using localization.induction_on with data',
  rcases ⟨data, data'⟩ with ⟨⟨r, s⟩, ⟨r', s'⟩⟩,

  induction m using localized_module.induction_on with m t,
  rw [localization.mk_mul, mk_smul_mk, mk_smul_mk, mk_smul_mk, mul_smul, mul_assoc],
end

private lemma smul_add' (x : localization S) (y z : localized_module S M) :
  x • (y + z) = x • y + x • z :=
begin
  induction x using localization.induction_on with data,
  rcases data with ⟨r, u⟩,
  induction y using localized_module.induction_on with m s,
  induction z using localized_module.induction_on with n t,
  rw [mk_smul_mk, mk_smul_mk, mk_add_mk, mk_smul_mk, mk_add_mk, mk_eq],
  use 1,
  simp only [one_smul, smul_add, ← mul_smul, submonoid.smul_def, submonoid.coe_mul],
  ring_nf
end

private lemma smul_zero' (x : localization S) :
  x • (0 : localized_module S M) = 0 :=
begin
  induction x using localization.induction_on with data,
  rcases data with ⟨r, s⟩,
  rw [←zero_mk s, mk_smul_mk, smul_zero, zero_mk, zero_mk],
end

private lemma add_smul' (x y : localization S) (z : localized_module S M) :
  (x + y) • z = x • z + y • z :=
begin
  induction x using localization.induction_on with datax,
  induction y using localization.induction_on with datay,
  induction z using localized_module.induction_on with m t,
  rcases ⟨datax, datay⟩ with ⟨⟨r, s⟩, ⟨r', s'⟩⟩,
  rw [localization.add_mk, mk_smul_mk, mk_smul_mk, mk_smul_mk, mk_add_mk, mk_eq],
  use 1,
  simp only [one_smul, add_smul, smul_add, ← mul_smul, submonoid.smul_def, submonoid.coe_mul,
    submonoid.coe_one],
  rw add_comm, -- Commutativity of addition in the module is not applied by `ring`.
  ring_nf,
end

private lemma zero_smul' (x : localized_module S M) :
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

@[simp] lemma mk_cancel_common_left (s' s : S) (m : M) : mk (s' • m) (s' * s) = mk m s :=
mk_eq.mpr ⟨1, by { simp only [mul_smul, one_smul], rw smul_comm }⟩

@[simp] lemma mk_cancel (s : S) (m : M) : mk (s • m) s = mk m 1 :=
mk_eq.mpr ⟨1, by simp⟩

@[simp] lemma mk_cancel_common_right (s s' : S) (m : M) : mk (s' • m) (s * s') = mk m s :=
mk_eq.mpr ⟨1, by simp [mul_smul]⟩

instance is_module' : module R (localized_module S M) :=
{ ..module.comp_hom (localized_module S M) $ (algebra_map R (localization S)) }

lemma smul'_mk (r : R) (s : S) (m : M) : r • mk m s = mk (r • m) s :=
by erw [mk_smul_mk r m 1 s, one_mul]

instance {A : Type*} [semiring A] [algebra R A] :
  algebra (localization S) (localized_module S A) :=
algebra.of_module
begin
  intros r x₁ x₂,
  obtain ⟨y, s, rfl : is_localization.mk' _ y s = r⟩ := is_localization.mk'_surjective S r,
  obtain ⟨⟨a₁, s₁⟩, rfl : mk a₁ s₁ = x₁⟩ := quotient.exists_rep x₁,
  obtain ⟨⟨a₂, s₂⟩, rfl : mk a₂ s₂ = x₂⟩ := quotient.exists_rep x₂,
  rw [mk_mul_mk, ← localization.mk_eq_mk', mk_smul_mk, mk_smul_mk, mk_mul_mk,
    mul_assoc, smul_mul_assoc],
end
begin
  intros r x₁ x₂,
  obtain ⟨y, s, rfl : is_localization.mk' _ y s = r⟩ := is_localization.mk'_surjective S r,
  obtain ⟨⟨a₁, s₁⟩, rfl : mk a₁ s₁ = x₁⟩ := quotient.exists_rep x₁,
  obtain ⟨⟨a₂, s₂⟩, rfl : mk a₂ s₂ = x₂⟩ := quotient.exists_rep x₂,
  rw [mk_mul_mk, ← localization.mk_eq_mk', mk_smul_mk, mk_smul_mk, mk_mul_mk,
    mul_left_comm, mul_smul_comm]
end

lemma algebra_map_mk {A : Type*} [semiring A] [algebra R A] (a : R) (s : S) :
  algebra_map _ _ (localization.mk a s) = mk (algebra_map R A a) s :=
begin
  rw [algebra.algebra_map_eq_smul_one],
  change _ • mk _ _ = _,
  rw [mk_smul_mk, algebra.algebra_map_eq_smul_one, mul_one]
end

instance : is_scalar_tower R (localization S) (localized_module S M) :=
restrict_scalars.is_scalar_tower R (localization S) (localized_module S M)

instance algebra' {A : Type*} [semiring A] [algebra R A] :
  algebra R (localized_module S A) :=
{ commutes' := begin
    intros r x,
    obtain ⟨⟨a, s⟩, rfl : mk a s = x⟩ := quotient.exists_rep x,
    dsimp,
    rw [← localization.mk_one_eq_algebra_map, algebra_map_mk, mk_mul_mk, mk_mul_mk, mul_comm,
      algebra.commutes],
  end,
  smul_def' := begin
    intros r x,
    obtain ⟨⟨a, s⟩, rfl : mk a s = x⟩ := quotient.exists_rep x,
    dsimp,
    rw [← localization.mk_one_eq_algebra_map, algebra_map_mk, mk_mul_mk, smul'_mk,
      algebra.smul_def, one_mul],
  end,
  ..(algebra_map (localization S) (localized_module S A)).comp (algebra_map R $ localization S),
  ..(show module R (localized_module S A), by apply_instance) }
section

variables (S M)

/-- The function `m ↦ m / 1` as an `R`-linear map.
-/
@[simps]
def mk_linear_map : M →ₗ[R] localized_module S M :=
{ to_fun := λ m, mk m 1,
  map_add' := λ x y, by simp [mk_add_mk],
  map_smul' := λ r x, (smul'_mk _ _ _).symm }

end

/--
For any `s : S`, there is an `R`-linear map given by `a/b ↦ a/(b*s)`.
-/
@[simps]
def div_by (s : S) : localized_module S M →ₗ[R] localized_module S M :=
{ to_fun := λ p, p.lift_on (λ p, mk p.1 (s * p.2)) $ λ ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩, mk_eq.mpr ⟨c,
  begin
    rw [mul_smul, mul_smul, smul_comm c, eq1, smul_comm s];
    apply_instance,
  end⟩,
  map_add' := λ x y, x.induction_on₂
    (begin
      intros m₁ m₂ t₁ t₂,
      simp only [mk_add_mk, localized_module.lift_on_mk, mul_smul, ←smul_add, mul_assoc,
        mk_cancel_common_left s],
      rw show s * (t₁ * t₂) = t₁ * (s * t₂), by { ext, simp only [submonoid.coe_mul], ring },
    end) y,
  map_smul' := λ r x, x.induction_on $ by { intros, simp [localized_module.lift_on_mk, smul'_mk] } }

lemma div_by_mul_by (s : S) (p : localized_module S M) :
  div_by s (algebra_map R (module.End R (localized_module S M)) s p) = p :=
p.induction_on
begin
  intros m t,
  simp only [localized_module.lift_on_mk, module.algebra_map_End_apply, smul'_mk, div_by_apply],
  erw mk_cancel_common_left s t,
end

lemma mul_by_div_by (s : S) (p : localized_module S M) :
  algebra_map R (module.End R (localized_module S M)) s (div_by s p) = p :=
p.induction_on
begin
  intros m t,
  simp only [localized_module.lift_on_mk, div_by_apply, module.algebra_map_End_apply, smul'_mk],
  erw mk_cancel_common_left s t,
end

end

end localized_module

section is_localized_module

universes u v

variables {R : Type*} [comm_ring R] (S : submonoid R)
variables {M M' M'' : Type*} [add_comm_monoid M] [add_comm_monoid M'] [add_comm_monoid M'']
variables [module R M] [module R M'] [module R M''] (f : M →ₗ[R] M') (g : M →ₗ[R] M'')

/--
The characteristic predicate for localized module.
`is_localized_module S f` describes that `f : M ⟶ M'` is the localization map identifying `M'` as
`localized_module S M`.
-/
class is_localized_module : Prop :=
(map_units [] : ∀ (x : S), is_unit (algebra_map R (module.End R M') x))
(surj [] : ∀ y : M', ∃ (x : M × S), x.2 • y = f x.1)
(eq_iff_exists [] : ∀ {x₁ x₂}, f x₁ = f x₂ ↔ ∃ c : S, c • x₂ = c • x₁)

namespace localized_module

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `localized_module S M → M''`.
-/
noncomputable def lift' (g : M →ₗ[R] M'')
  (h : ∀ (x : S), is_unit ((algebra_map R (module.End R M'')) x)) :
  (localized_module S M) → M'' :=
λ m, m.lift_on (λ p, (h $ p.2).unit⁻¹ $ g p.1) $ λ ⟨m, s⟩ ⟨m', s'⟩ ⟨c, eq1⟩,
begin
  generalize_proofs h1 h2,
  erw [module.End_algebra_map_is_unit_inv_apply_eq_iff, ←h2.unit⁻¹.1.map_smul], symmetry,
  erw [module.End_algebra_map_is_unit_inv_apply_eq_iff], dsimp,
  have : c • s • g m' = c • s' • g m,
  { erw [←g.map_smul, ←g.map_smul, ←g.map_smul, ←g.map_smul, eq1], refl, },
  have : function.injective (h c).unit.inv,
  { rw function.injective_iff_has_left_inverse, refine ⟨(h c).unit, _⟩,
    intros x,
    change ((h c).unit.1 * (h c).unit.inv) x = x,
    simp only [units.inv_eq_coe_inv, is_unit.mul_coe_inv, linear_map.one_apply], },
  apply_fun (h c).unit.inv,
  erw [units.inv_eq_coe_inv, module.End_algebra_map_is_unit_inv_apply_eq_iff,
    ←(h c).unit⁻¹.1.map_smul], symmetry,
  erw [module.End_algebra_map_is_unit_inv_apply_eq_iff,
    ←g.map_smul, ←g.map_smul, ←g.map_smul, ←g.map_smul, eq1], refl,
end

lemma lift'_mk (g : M →ₗ[R] M'')
  (h : ∀ (x : S), is_unit ((algebra_map R (module.End R M'')) x)) (m : M) (s : S) :
  localized_module.lift' S g h (localized_module.mk m s) =
  (h s).unit⁻¹.1 (g m) := rfl

lemma lift'_add (g : M →ₗ[R] M'')
  (h : ∀ (x : S), is_unit ((algebra_map R (module.End R M'')) x)) (x y) :
  localized_module.lift' S g h (x + y) =
  localized_module.lift' S g h x + localized_module.lift' S g h y :=
localized_module.induction_on₂ begin
  intros a a' b b',
  erw [localized_module.lift'_mk, localized_module.lift'_mk, localized_module.lift'_mk],
  dsimp, generalize_proofs h1 h2 h3,
  erw [map_add, module.End_algebra_map_is_unit_inv_apply_eq_iff,
    smul_add, ←h2.unit⁻¹.1.map_smul, ←h3.unit⁻¹.1.map_smul],
  congr' 1; symmetry,
  erw [module.End_algebra_map_is_unit_inv_apply_eq_iff, mul_smul, ←map_smul], refl,
  erw [module.End_algebra_map_is_unit_inv_apply_eq_iff, mul_comm, mul_smul, ←map_smul], refl,
end x y

lemma lift'_smul (g : M →ₗ[R] M'')
  (h : ∀ (x : S), is_unit ((algebra_map R (module.End R M'')) x))
  (r : R) (m) :
  r • localized_module.lift' S g h m = localized_module.lift' S g h (r • m) :=
m.induction_on begin
  intros a b,
  rw [localized_module.lift'_mk, localized_module.smul'_mk, localized_module.lift'_mk],
    generalize_proofs h1 h2,
    erw [←h1.unit⁻¹.1.map_smul, ←g.map_smul],
end

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `localized_module S M → M''`.
-/
noncomputable def lift (g : M →ₗ[R] M'')
  (h : ∀ (x : S), is_unit ((algebra_map R (module.End R M'')) x)) :
  (localized_module S M) →ₗ[R] M'' :=
{ to_fun := localized_module.lift' S g h,
  map_add' := localized_module.lift'_add S g h,
  map_smul' := λ r x, by rw [localized_module.lift'_smul, ring_hom.id_apply] }

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
`lift g m s = s⁻¹ • g m`.
-/
lemma lift_mk (g : M →ₗ[R] M'')
  (h : ∀ (x : S), is_unit ((algebra_map R (module.End R M'')) x))
  (m : M) (s : S) :
  localized_module.lift S g h (localized_module.mk m s) = (h s).unit⁻¹.1 (g m) := rfl

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `lift g ∘ mk_linear_map = g`.
-/
lemma lift_comp (g : M →ₗ[R] M'')
  (h : ∀ (x : S), is_unit ((algebra_map R (module.End R M'')) x)) :
  (lift S g h).comp (mk_linear_map S M) = g :=
begin
  ext x, dsimp, rw localized_module.lift_mk,
  erw [module.End_algebra_map_is_unit_inv_apply_eq_iff, one_smul],
end

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible and
`l` is another linear map `localized_module S M ⟶ M''` such that `l ∘ mk_linear_map = g` then
`l = lift g`
-/
lemma lift_unique (g : M →ₗ[R] M'')
  (h : ∀ (x : S), is_unit ((algebra_map R (module.End R M'')) x))
  (l : localized_module S M →ₗ[R] M'')
  (hl : l.comp (localized_module.mk_linear_map S M) = g) :
  localized_module.lift S g h = l :=
begin
  ext x, induction x using localized_module.induction_on with m s,
  rw [localized_module.lift_mk],
  erw [module.End_algebra_map_is_unit_inv_apply_eq_iff, ←hl, linear_map.coe_comp, function.comp_app,
    localized_module.mk_linear_map_apply, ←l.map_smul, localized_module.smul'_mk],
  congr' 1, rw localized_module.mk_eq,
  refine ⟨1, _⟩, simp only [one_smul], refl,
end

end localized_module

instance localized_module_is_localized_module :
  is_localized_module S (localized_module.mk_linear_map S M) :=
{ map_units := λ s, ⟨⟨algebra_map R (module.End R (localized_module S M)) s,
    localized_module.div_by s,
    fun_like.ext _ _ $ localized_module.mul_by_div_by s,
    fun_like.ext _ _ $ localized_module.div_by_mul_by s⟩,
    fun_like.ext _ _ $ λ p, p.induction_on $ by { intros, refl }⟩,
  surj := λ p, p.induction_on
    begin
      intros m t,
      refine ⟨⟨m, t⟩, _⟩,
      erw [localized_module.smul'_mk, localized_module.mk_linear_map_apply, submonoid.coe_subtype,
        localized_module.mk_cancel t ],
    end,
  eq_iff_exists := λ m1 m2,
  { mp := λ eq1, by simpa only [eq_comm, one_smul] using localized_module.mk_eq.mp eq1,
    mpr := λ ⟨c, eq1⟩,
      localized_module.mk_eq.mpr ⟨c, by simpa only [eq_comm, one_smul] using eq1⟩ } }

namespace is_localized_module

variable [is_localized_module S f]

/--
If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is a canonical map
`localized_module S M ⟶ M'`.
-/
noncomputable def from_localized_module' : localized_module S M → M' :=
λ p, p.lift_on (λ x, (is_localized_module.map_units f x.2).unit⁻¹ (f x.1))
begin
  rintros ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩,
  dsimp,
  generalize_proofs h1 h2,
  erw [module.End_algebra_map_is_unit_inv_apply_eq_iff, ←h2.unit⁻¹.1.map_smul,
    module.End_algebra_map_is_unit_inv_apply_eq_iff', ←linear_map.map_smul, ←linear_map.map_smul],
  exact (is_localized_module.eq_iff_exists S f).mpr ⟨c, eq1⟩,
end

@[simp] lemma from_localized_module'_mk (m : M) (s : S) :
  from_localized_module' S f (localized_module.mk m s) =
  (is_localized_module.map_units f s).unit⁻¹ (f m) :=
rfl

lemma from_localized_module'_add (x y : localized_module S M) :
  from_localized_module' S f (x + y) =
  from_localized_module' S f x + from_localized_module' S f y :=
localized_module.induction_on₂ begin
  intros a a' b b',
  simp only [localized_module.mk_add_mk, from_localized_module'_mk],
  generalize_proofs h1 h2 h3,
  erw [module.End_algebra_map_is_unit_inv_apply_eq_iff, smul_add, ←h2.unit⁻¹.1.map_smul,
    ←h3.unit⁻¹.1.map_smul, map_add],
  congr' 1,
  all_goals { erw [module.End_algebra_map_is_unit_inv_apply_eq_iff'] },
  { dsimp, erw [mul_smul, f.map_smul], refl, },
  { dsimp, erw [mul_comm, f.map_smul, mul_smul], refl, },
end x y

lemma from_localized_module'_smul (r : R) (x : localized_module S M) :
  r • from_localized_module' S f x = from_localized_module' S f (r • x) :=
localized_module.induction_on begin
  intros a b,
  rw [from_localized_module'_mk, localized_module.smul'_mk, from_localized_module'_mk],
  generalize_proofs h1, erw [f.map_smul, h1.unit⁻¹.1.map_smul], refl,
end x

/--
If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is a canonical map
`localized_module S M ⟶ M'`.
-/
noncomputable def from_localized_module : localized_module S M →ₗ[R] M' :=
{ to_fun := from_localized_module' S f,
  map_add' := from_localized_module'_add S f,
  map_smul' := λ r x, by rw [from_localized_module'_smul, ring_hom.id_apply] }

lemma from_localized_module_mk (m : M) (s : S) :
  from_localized_module S f (localized_module.mk m s) =
  (is_localized_module.map_units f s).unit⁻¹ (f m) :=
rfl

lemma from_localized_module.inj : function.injective $ from_localized_module S f :=
λ x y eq1,
begin
  induction x using localized_module.induction_on with a b,
  induction y using localized_module.induction_on with a' b',
  simp only [from_localized_module_mk] at eq1,
  generalize_proofs h1 h2 at eq1,
  erw [module.End_algebra_map_is_unit_inv_apply_eq_iff, ←linear_map.map_smul,
    module.End_algebra_map_is_unit_inv_apply_eq_iff'] at eq1,
  erw [localized_module.mk_eq, ←is_localized_module.eq_iff_exists S f, f.map_smul, f.map_smul, eq1],
  refl,
end

lemma from_localized_module.surj : function.surjective $ from_localized_module S f :=
λ x, let ⟨⟨m, s⟩, eq1⟩ := is_localized_module.surj S f x in ⟨localized_module.mk m s,
by { rw [from_localized_module_mk, module.End_algebra_map_is_unit_inv_apply_eq_iff, ←eq1], refl }⟩

lemma from_localized_module.bij : function.bijective $ from_localized_module S f :=
⟨from_localized_module.inj _ _, from_localized_module.surj _ _⟩

/--
If `(M', f : M ⟶ M')` satisfies universal property of localized module, then `M'` is isomorphic to
`localized_module S M` as an `R`-module.
-/
@[simps] noncomputable def iso : localized_module S M ≃ₗ[R] M' :=
{ ..from_localized_module S f,
  ..equiv.of_bijective (from_localized_module S f) $ from_localized_module.bij _ _}

lemma iso_apply_mk (m : M) (s : S) :
  iso S f (localized_module.mk m s) = (is_localized_module.map_units f s).unit⁻¹ (f m) :=
rfl

lemma iso_symm_apply_aux (m : M') :
  (iso S f).symm m = localized_module.mk (is_localized_module.surj S f m).some.1
    (is_localized_module.surj S f m).some.2 :=
begin
  generalize_proofs _ h2,
  apply_fun (iso S f) using linear_equiv.injective _,
  rw [linear_equiv.apply_symm_apply],
  simp only [iso_apply, linear_map.to_fun_eq_coe, from_localized_module_mk],
  erw [module.End_algebra_map_is_unit_inv_apply_eq_iff', h2.some_spec],
end

lemma iso_symm_apply' (m : M') (a : M) (b : S) (eq1 : b • m = f a) :
  (iso S f).symm m = localized_module.mk a b :=
(iso_symm_apply_aux S f m).trans $ localized_module.mk_eq.mpr $
begin
  generalize_proofs h1,
  erw [←is_localized_module.eq_iff_exists S f, f.map_smul, f.map_smul, ←h1.some_spec, ←mul_smul,
    mul_comm, mul_smul, eq1],
end

lemma iso_symm_comp : (iso S f).symm.to_linear_map.comp f = localized_module.mk_linear_map S M :=
begin
  ext m, rw [linear_map.comp_apply, localized_module.mk_linear_map_apply],
  change (iso S f).symm _ = _, rw [iso_symm_apply'], exact one_smul _ _,
end

/--
If `M'` is a localized module and `g` is a linear map `M' → M''` such that all scalar multiplication
by `s : S` is invertible, then there is a linear map `M' → M''`.
-/
noncomputable def lift (g : M →ₗ[R] M'')
  (h : ∀ (x : S), is_unit ((algebra_map R (module.End R M'')) x)) :
  M' →ₗ[R] M'' :=
(localized_module.lift S g h).comp (iso S f).symm.to_linear_map

lemma lift_comp (g : M →ₗ[R] M'')
  (h : ∀ (x : S), is_unit ((algebra_map R (module.End R M'')) x)) :
  (lift S f g h).comp f = g :=
begin
  dunfold is_localized_module.lift,
  rw [linear_map.comp_assoc],
  convert localized_module.lift_comp S g h,
  exact iso_symm_comp _ _,
end

lemma lift_unique (g : M →ₗ[R] M'')
  (h : ∀ (x : S), is_unit ((algebra_map R (module.End R M'')) x))
  (l : M' →ₗ[R] M'') (hl : l.comp f = g) :
  lift S f g h = l :=
begin
  dunfold is_localized_module.lift,
  rw [localized_module.lift_unique S g h (l.comp (iso S f).to_linear_map), linear_map.comp_assoc,
    show (iso S f).to_linear_map.comp (iso S f).symm.to_linear_map = linear_map.id, from _,
    linear_map.comp_id],
  { rw [linear_equiv.comp_to_linear_map_symm_eq, linear_map.id_comp], },
  { rw [linear_map.comp_assoc, ←hl], congr' 1, ext x,
    erw [from_localized_module_mk, module.End_algebra_map_is_unit_inv_apply_eq_iff, one_smul], },
end

/--
Universal property from localized module:
If `(M', f : M ⟶ M')` is a localized module then it satisfies the following universal property:
For every `R`-module `M''` which every `s : S`-scalar multiplication is invertible and for every
`R`-linear map `g : M ⟶ M''`, there is a unique `R`-linear map `l : M' ⟶ M''` such that
`l ∘ f = g`.
```
M -----f----> M'
|           /
|g       /
|     /   l
v   /
M''
```
-/
lemma is_universal :
  ∀ (g : M →ₗ[R] M'') (map_unit : ∀ (x : S), is_unit ((algebra_map R (module.End R M'')) x)),
    ∃! (l : M' →ₗ[R] M''), l.comp f = g :=
λ g h, ⟨lift S f g h, lift_comp S f g h, λ l hl, (lift_unique S f g h l hl).symm⟩

lemma ring_hom_ext (map_unit : ∀ (x : S), is_unit ((algebra_map R (module.End R M'')) x))
  ⦃j k : M' →ₗ[R] M''⦄ (h : j.comp f = k.comp f) : j = k :=
by { rw [←lift_unique S f (k.comp f) map_unit j h, lift_unique], refl }

/--
If `(M', f)` and `(M'', g)` both satisfy universal property of localized module, then `M', M''`
are isomorphic as `R`-module
-/
noncomputable def linear_equiv [is_localized_module S g] : M' ≃ₗ[R] M'' :=
(iso S f).symm.trans (iso S g)

variable {S}

lemma smul_injective (s : S) : function.injective (λ m : M', s • m) :=
((module.End_is_unit_iff _).mp (is_localized_module.map_units f s)).injective

lemma smul_inj (s : S) (m₁ m₂ : M') : s • m₁ = s • m₂ ↔ m₁ = m₂ :=
(smul_injective f s).eq_iff

/-- `mk' f m s` is the fraction `m/s` with respect to the localization map `f`. -/
noncomputable
def mk' (m : M) (s : S) : M' := from_localized_module S f (localized_module.mk m s)

lemma mk'_smul (r : R) (m : M) (s : S) : mk' f (r • m) s = r • mk' f m s :=
by { delta mk', rw [← localized_module.smul'_mk, linear_map.map_smul] }

lemma mk'_add_mk' (m₁ m₂ : M) (s₁ s₂ : S) :
  mk' f m₁ s₁ + mk' f m₂ s₂ = mk' f (s₂ • m₁ + s₁ • m₂) (s₁ * s₂)  :=
by { delta mk', rw [← map_add, localized_module.mk_add_mk] }

@[simp] lemma mk'_zero (s : S) :
  mk' f 0 s = 0 :=
by rw [← zero_smul R (0 : M), mk'_smul, zero_smul]

variable (S)

@[simp] lemma mk'_one (m : M) :
  mk' f m (1 : S) = f m :=
by { delta mk', rw [from_localized_module_mk, module.End_algebra_map_is_unit_inv_apply_eq_iff,
  submonoid.coe_one, one_smul] }

variable {S}

@[simp] lemma mk'_cancel (m : M) (s : S) :
  mk' f (s • m) s = f m :=
by { delta mk', rw [localized_module.mk_cancel, ← mk'_one S f], refl }

@[simp] lemma mk'_cancel' (m : M) (s : S) :
  s • mk' f m s = f m :=
by rw [submonoid.smul_def, ← mk'_smul, ← submonoid.smul_def, mk'_cancel]

@[simp] lemma mk'_cancel_left (m : M) (s₁ s₂ : S) :
  mk' f (s₁ • m) (s₁ * s₂) = mk' f m s₂ :=
by { delta mk', rw localized_module.mk_cancel_common_left }

@[simp] lemma mk'_cancel_right (m : M) (s₁ s₂ : S) :
  mk' f (s₂ • m) (s₁ * s₂) = mk' f m s₁ :=
by { delta mk', rw localized_module.mk_cancel_common_right }

lemma mk'_add (m₁ m₂ : M) (s : S) : mk' f (m₁ + m₂) s = mk' f m₁ s + mk' f m₂ s :=
by { rw [mk'_add_mk', ← smul_add, mk'_cancel_left] }

lemma mk'_eq_mk'_iff (m₁ m₂ : M) (s₁ s₂ : S) :
  mk' f m₁ s₁ = mk' f m₂ s₂ ↔ ∃ s : S, s • s₁ • m₂ = s • s₂ • m₁ :=
begin
  delta mk',
  rw [(from_localized_module.inj S f).eq_iff, localized_module.mk_eq],
  simp_rw eq_comm
end

lemma mk'_neg {M M' : Type*} [add_comm_group M] [add_comm_group M'] [module R M]
  [module R M'] (f : M →ₗ[R] M') [is_localized_module S f] (m : M) (s : S) :
  mk' f (-m) s = - mk' f m s :=
by { delta mk', rw [localized_module.mk_neg, map_neg] }

lemma mk'_sub {M M' : Type*} [add_comm_group M] [add_comm_group M'] [module R M]
  [module R M'] (f : M →ₗ[R] M') [is_localized_module S f] (m₁ m₂ : M) (s : S) :
  mk' f (m₁ - m₂) s = mk' f m₁ s - mk' f m₂ s :=
by rw [sub_eq_add_neg, sub_eq_add_neg, mk'_add, mk'_neg]

lemma mk'_sub_mk' {M M' : Type*} [add_comm_group M] [add_comm_group M'] [module R M]
  [module R M'] (f : M →ₗ[R] M') [is_localized_module S f] (m₁ m₂ : M) (s₁ s₂ : S) :
  mk' f m₁ s₁ - mk' f m₂ s₂ = mk' f (s₂ • m₁ - s₁ • m₂) (s₁ * s₂) :=
by rw [sub_eq_add_neg, ← mk'_neg, mk'_add_mk', smul_neg, ← sub_eq_add_neg]

lemma mk'_mul_mk'_of_map_mul {M M' : Type*} [semiring M] [semiring M'] [module R M]
  [algebra R M'] (f : M →ₗ[R] M') (hf : ∀ m₁ m₂, f (m₁ * m₂) = f m₁ * f m₂)
  [is_localized_module S f] (m₁ m₂ : M) (s₁ s₂ : S) :
  mk' f m₁ s₁ * mk' f m₂ s₂ = mk' f (m₁ * m₂) (s₁ * s₂) :=
begin
  symmetry,
  apply (module.End_algebra_map_is_unit_inv_apply_eq_iff _ _ _).mpr,
  simp_rw [submonoid.coe_mul, ← smul_eq_mul],
  rw [smul_smul_smul_comm, ← mk'_smul, ← mk'_smul],
  simp_rw [← submonoid.smul_def, mk'_cancel, smul_eq_mul, hf],
end

lemma mk'_mul_mk' {M M' : Type*} [semiring M] [semiring M'] [algebra R M]
  [algebra R M'] (f : M →ₐ[R] M')
  [is_localized_module S f.to_linear_map] (m₁ m₂ : M) (s₁ s₂ : S) :
  mk' f.to_linear_map m₁ s₁ * mk' f.to_linear_map m₂ s₂ =
    mk' f.to_linear_map (m₁ * m₂) (s₁ * s₂) :=
mk'_mul_mk'_of_map_mul f.to_linear_map f.map_mul m₁ m₂ s₁ s₂

variables {f}

@[simp] lemma mk'_eq_iff {m : M} {s : S} {m' : M'} :
  mk' f m s = m' ↔ f m = s • m' :=
by rw [← smul_inj f s, submonoid.smul_def, ← mk'_smul, ← submonoid.smul_def, mk'_cancel]

@[simp] lemma mk'_eq_zero {m : M} (s : S) :
  mk' f m s = 0 ↔ f m = 0 :=
by rw [mk'_eq_iff, smul_zero]

variable (f)

lemma mk'_eq_zero' {m : M} (s : S) :
  mk' f m s = 0 ↔ ∃ s' : S, s' • m = 0 :=
by simp_rw [← mk'_zero f (1 : S), mk'_eq_mk'_iff, smul_zero, one_smul, eq_comm]

lemma mk_eq_mk' (s : S) (m : M) :
  localized_module.mk m s = mk' (localized_module.mk_linear_map S M) m s :=
by rw [eq_comm, mk'_eq_iff, submonoid.smul_def, localized_module.smul'_mk,
  ← submonoid.smul_def, localized_module.mk_cancel, localized_module.mk_linear_map_apply]

variable (S)

lemma eq_zero_iff {m : M} :
  f m = 0 ↔ ∃ s' : S, s' • m = 0 :=
(mk'_eq_zero (1 : S)).symm.trans (mk'_eq_zero' f _)

lemma mk'_surjective : function.surjective (function.uncurry $ mk' f : M × S → M') :=
begin
  intro x,
  obtain ⟨⟨m, s⟩, e : s • x = f m⟩ := is_localized_module.surj S f x,
  exact ⟨⟨m, s⟩, mk'_eq_iff.mpr e.symm⟩
end

section algebra

lemma mk_of_algebra {R S S' : Type*} [comm_ring R] [comm_ring S] [comm_ring S']
  [algebra R S] [algebra R S'] (M : submonoid R) (f : S →ₐ[R] S')
  (h₁ : ∀ x ∈ M, is_unit (algebra_map R S' x))
  (h₂ : ∀ y, ∃ (x : S × M), x.2 • y = f x.1)
  (h₃ : ∀ x, f x = 0 → ∃ m : M, m • x = 0) :
  is_localized_module M f.to_linear_map :=
begin
  replace h₃ := λ x, iff.intro (h₃ x) (λ ⟨⟨m, hm⟩, e⟩, (h₁ m hm).mul_left_cancel $
    by { rw ← algebra.smul_def, simpa [submonoid.smul_def] using f.congr_arg e }),
  constructor,
  { intro x,
    rw module.End_is_unit_iff,
    split,
    { rintros a b (e : x • a = x • b), simp_rw [submonoid.smul_def, algebra.smul_def] at e,
      exact (h₁ x x.2).mul_left_cancel e },
    { intro a, refine ⟨((h₁ x x.2).unit⁻¹ : _) * a, _⟩, change (x : R) • (_ * a) = _,
      rw [algebra.smul_def, ← mul_assoc, is_unit.mul_coe_inv, one_mul] } },
  { exact h₂ },
  { intros, dsimp, rw [eq_comm, ← sub_eq_zero, ← map_sub, h₃], simp_rw [smul_sub, sub_eq_zero] },
end

end algebra

end is_localized_module

end is_localized_module
