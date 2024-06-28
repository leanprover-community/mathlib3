/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Filippo A. E. Nuccio
-/
import algebra.big_operators.finprod
import ring_theory.integral_closure
import ring_theory.localization.integer
import ring_theory.localization.submodule
import ring_theory.noetherian
import ring_theory.principal_ideal_domain
import tactic.field_simp

/-!
# Fractional ideals

This file defines fractional ideals of an integral domain and proves basic facts about them.

## Main definitions
Let `S` be a submonoid of an integral domain `R`, `P` the localization of `R` at `S`, and `f` the
natural ring hom from `R` to `P`.
 * `is_fractional` defines which `R`-submodules of `P` are fractional ideals
 * `fractional_ideal S P` is the type of fractional ideals in `P`
 * `has_coe_t (ideal R) (fractional_ideal S P)` instance
 * `comm_semiring (fractional_ideal S P)` instance:
   the typical ideal operations generalized to fractional ideals
 * `lattice (fractional_ideal S P)` instance
 * `map` is the pushforward of a fractional ideal along an algebra morphism

Let `K` be the localization of `R` at `R⁰ = R \ {0}` (i.e. the field of fractions).
 * `fractional_ideal R⁰ K` is the type of fractional ideals in the field of fractions
 * `has_div (fractional_ideal R⁰ K)` instance:
   the ideal quotient `I / J` (typically written $I : J$, but a `:` operator cannot be defined)

## Main statements

  * `mul_left_mono` and `mul_right_mono` state that ideal multiplication is monotone
  * `prod_one_self_div_eq` states that `1 / I` is the inverse of `I` if one exists
  * `is_noetherian` states that every fractional ideal of a noetherian integral domain is noetherian

## Implementation notes

Fractional ideals are considered equal when they contain the same elements,
independent of the denominator `a : R` such that `a I ⊆ R`.
Thus, we define `fractional_ideal` to be the subtype of the predicate `is_fractional`,
instead of having `fractional_ideal` be a structure of which `a` is a field.

Most definitions in this file specialize operations from submodules to fractional ideals,
proving that the result of this operation is fractional if the input is fractional.
Exceptions to this rule are defining `(+) := (⊔)` and `⊥ := 0`,
in order to re-use their respective proof terms.
We can still use `simp` to show `↑I + ↑J = ↑(I + J)` and `↑⊥ = ↑0`.

Many results in fact do not need that `P` is a localization, only that `P` is an
`R`-algebra. We omit the `is_localization` parameter whenever this is practical.
Similarly, we don't assume that the localization is a field until we need it to
define ideal quotients. When this assumption is needed, we replace `S` with `R⁰`,
making the localization a field.

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/

open is_localization
open_locale pointwise

open_locale non_zero_divisors

section defs

variables {R : Type*} [comm_ring R] {S : submonoid R} {P : Type*} [comm_ring P]
variables [algebra R P]

variables (S)

/-- A submodule `I` is a fractional ideal with respect to a submonoid `S`
  if `a I ⊆ R` for some `a ∈ S`. -/
def is_fractional (I : submodule R P) :=
∃ a ∈ S, ∀ b ∈ I, is_integer R (a • b)

variables (S P)

/-- The fractional ideals of a domain `R` with respect to a submonoid `S`
  are ideals of `R` divided by some `a ∈ S`.

  More precisely, let `P` be a localization of `R` at some submonoid `S`,
  then a fractional ideal `I ⊆ P` is an `R`-submodule of `P`,
  such that there is an `a ∈ S` with `a I ⊆ R`.
-/
def fractional_ideal :=
{I : submodule R P // is_fractional S I}

end defs

namespace fractional_ideal

open set
open submodule

variables {R : Type*} [comm_ring R] {S : submonoid R} {P : Type*} [comm_ring P]
variables [algebra R P] [loc : is_localization S P]

/-- Map a fractional ideal `I` to a submodule by forgetting that `∃ a, a I ⊆ R`.

This coercion is typically called `coe_to_submodule` in lemma names
(or `coe` when the coercion is clear from the context),
not to be confused with `is_localization.coe_submodule : ideal R → submodule R P`
(which we use to define `coe : ideal R → fractional_ideal S P`).
-/
instance : has_coe (fractional_ideal S P) (submodule R P) := ⟨λ I, I.val⟩

protected lemma is_fractional (I : fractional_ideal S P) :
  is_fractional S (I : submodule R P) :=
I.prop

section set_like

instance : set_like (fractional_ideal S P) P :=
{ coe := λ I, ↑(I : submodule R P),
  coe_injective' := set_like.coe_injective.comp subtype.coe_injective }

@[simp] lemma mem_coe {I : fractional_ideal S P} {x : P} :
  x ∈ (I : submodule R P) ↔ x ∈ I :=
iff.rfl

@[ext] lemma ext {I J : fractional_ideal S P} : (∀ x, x ∈ I ↔ x ∈ J) → I = J := set_like.ext

/-- Copy of a `fractional_ideal` with a new underlying set equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (p : fractional_ideal S P) (s : set P) (hs : s = ↑p) : fractional_ideal S P :=
⟨submodule.copy p s hs, by { convert p.is_fractional, ext, simp only [hs], refl }⟩

@[simp] lemma coe_copy (p : fractional_ideal S P) (s : set P) (hs : s = ↑p) :
  ↑(p.copy s hs) = s :=
rfl

lemma coe_eq (p : fractional_ideal S P) (s : set P) (hs : s = ↑p) : p.copy s hs = p :=
set_like.coe_injective hs

end set_like

@[simp] lemma val_eq_coe (I : fractional_ideal S P) : I.val = I := rfl

@[simp, norm_cast] lemma coe_mk (I : submodule R P) (hI : is_fractional S I) :
  (subtype.mk I hI : submodule R P) = I := rfl

/-! Transfer instances from `submodule R P` to `fractional_ideal S P`. -/
instance (I : fractional_ideal S P) : add_comm_group I := submodule.add_comm_group ↑I
instance (I : fractional_ideal S P) : module R I := submodule.module ↑I

lemma coe_to_submodule_injective :
  function.injective (coe : fractional_ideal S P → submodule R P) :=
subtype.coe_injective

lemma coe_to_submodule_inj {I J : fractional_ideal S P} : (I : submodule R P) = J ↔ I = J :=
coe_to_submodule_injective.eq_iff

lemma is_fractional_of_le_one (I : submodule R P) (h : I ≤ 1) : is_fractional S I :=
begin
  use [1, S.one_mem],
  intros b hb,
  rw one_smul,
  obtain ⟨b', b'_mem, rfl⟩ := h hb,
  exact set.mem_range_self b',
end

lemma is_fractional_of_le {I : submodule R P} {J : fractional_ideal S P} (hIJ : I ≤ J) :
  is_fractional S I :=
begin
  obtain ⟨a, a_mem, ha⟩ := J.is_fractional,
  use [a, a_mem],
  intros b b_mem,
  exact ha b (hIJ b_mem)
end

/-- Map an ideal `I` to a fractional ideal by forgetting `I` is integral.

This is a bundled version of `is_localization.coe_submodule : ideal R → submodule R P`,
which is not to be confused with the `coe : fractional_ideal S P → submodule R P`,
also called `coe_to_submodule` in theorem names.

This map is available as a ring hom, called `fractional_ideal.coe_ideal_hom`.
-/
-- Is a `coe_t` rather than `coe` to speed up failing inference, see library note [use has_coe_t]
instance : has_coe_t (ideal R) (fractional_ideal S P) :=
⟨λ I, ⟨coe_submodule P I,
  is_fractional_of_le_one _ $ by simpa using coe_submodule_mono P (le_top : I ≤ ⊤)⟩⟩

@[simp, norm_cast] lemma coe_coe_ideal (I : ideal R) :
  ((I : fractional_ideal S P) : submodule R P) = coe_submodule P I := rfl

variables (S)

@[simp] lemma mem_coe_ideal {x : P} {I : ideal R} :
  x ∈ (I : fractional_ideal S P) ↔ ∃ x', x' ∈ I ∧ algebra_map R P x' = x :=
mem_coe_submodule _ _

lemma mem_coe_ideal_of_mem {x : R} {I : ideal R} (hx : x ∈ I) :
  algebra_map R P x ∈ (I : fractional_ideal S P) :=
(mem_coe_ideal S).mpr ⟨x, hx, rfl⟩

lemma coe_ideal_le_coe_ideal' [is_localization S P] (h : S ≤ non_zero_divisors R)
  {I J : ideal R} : (I : fractional_ideal S P) ≤ J ↔ I ≤ J :=
coe_submodule_le_coe_submodule h

@[simp] lemma coe_ideal_le_coe_ideal (K : Type*) [comm_ring K] [algebra R K] [is_fraction_ring R K]
  {I J : ideal R} : (I : fractional_ideal R⁰ K) ≤ J ↔ I ≤ J :=
is_fraction_ring.coe_submodule_le_coe_submodule

instance : has_zero (fractional_ideal S P) := ⟨(0 : ideal R)⟩

@[simp] lemma mem_zero_iff {x : P} : x ∈ (0 : fractional_ideal S P) ↔ x = 0 :=
⟨(λ ⟨x', x'_mem_zero, x'_eq_x⟩,
   have x'_eq_zero : x' = 0 := x'_mem_zero,
   by simp [x'_eq_x.symm, x'_eq_zero]),
 (λ hx, ⟨0, rfl, by simp [hx]⟩)⟩

variables {S}

@[simp, norm_cast] lemma coe_zero : ↑(0 : fractional_ideal S P) = (⊥ : submodule R P) :=
submodule.ext $ λ _, mem_zero_iff S

@[simp, norm_cast] lemma coe_ideal_bot : ((⊥ : ideal R) : fractional_ideal S P) = 0 := rfl

variables (P)

include loc

@[simp] lemma exists_mem_to_map_eq {x : R} {I : ideal R} (h : S ≤ non_zero_divisors R) :
  (∃ x', x' ∈ I ∧ algebra_map R P x' = algebra_map R P x) ↔ x ∈ I :=
⟨λ ⟨x', hx', eq⟩, is_localization.injective _ h eq ▸ hx', λ h, ⟨x, h, rfl⟩⟩

variables {P}

lemma coe_ideal_injective' (h : S ≤ non_zero_divisors R) :
  function.injective (coe : ideal R → fractional_ideal S P) :=
λ _ _ h', ((coe_ideal_le_coe_ideal' S h).mp h'.le).antisymm ((coe_ideal_le_coe_ideal' S h).mp h'.ge)

lemma coe_ideal_inj' (h : S ≤ non_zero_divisors R) {I J : ideal R} :
  (I : fractional_ideal S P) = J ↔ I = J :=
(coe_ideal_injective' h).eq_iff

@[simp] lemma coe_ideal_eq_zero' {I : ideal R} (h : S ≤ non_zero_divisors R) :
  (I : fractional_ideal S P) = 0 ↔ I = (⊥ : ideal R) :=
coe_ideal_inj' h

lemma coe_ideal_ne_zero' {I : ideal R} (h : S ≤ non_zero_divisors R) :
  (I : fractional_ideal S P) ≠ 0 ↔ I ≠ (⊥ : ideal R) :=
not_iff_not.mpr $ coe_ideal_eq_zero' h

omit loc

lemma coe_to_submodule_eq_bot {I : fractional_ideal S P} :
  (I : submodule R P) = ⊥ ↔ I = 0 :=
⟨λ h, coe_to_submodule_injective (by simp [h]),
 λ h, by simp [h]⟩

lemma coe_to_submodule_ne_bot {I : fractional_ideal S P} :
  ↑I ≠ (⊥ : submodule R P) ↔ I ≠ 0 :=
not_iff_not.mpr coe_to_submodule_eq_bot

instance : inhabited (fractional_ideal S P) := ⟨0⟩

instance : has_one (fractional_ideal S P) :=
⟨(⊤ : ideal R)⟩

variables (S)

@[simp, norm_cast] lemma coe_ideal_top : ((⊤ : ideal R) : fractional_ideal S P) = 1 := rfl

lemma mem_one_iff {x : P} : x ∈ (1 : fractional_ideal S P) ↔ ∃ x' : R, algebra_map R P x' = x :=
iff.intro (λ ⟨x', _, h⟩, ⟨x', h⟩) (λ ⟨x', h⟩, ⟨x', ⟨⟩, h⟩)

lemma coe_mem_one (x : R) : algebra_map R P x ∈ (1 : fractional_ideal S P) :=
(mem_one_iff S).mpr ⟨x, rfl⟩

lemma one_mem_one : (1 : P) ∈ (1 : fractional_ideal S P) :=
(mem_one_iff S).mpr ⟨1, ring_hom.map_one _⟩

variables {S}

/-- `(1 : fractional_ideal S P)` is defined as the R-submodule `f(R) ≤ P`.

However, this is not definitionally equal to `1 : submodule R P`,
which is proved in the actual `simp` lemma `coe_one`. -/
lemma coe_one_eq_coe_submodule_top :
  ↑(1 : fractional_ideal S P) = coe_submodule P (⊤ : ideal R) :=
rfl

@[simp, norm_cast] lemma coe_one :
  (↑(1 : fractional_ideal S P) : submodule R P) = 1 :=
by rw [coe_one_eq_coe_submodule_top, coe_submodule_top]

section lattice

/-!
### `lattice` section

Defines the order on fractional ideals as inclusion of their underlying sets,
and ports the lattice structure on submodules to fractional ideals.
-/

@[simp] lemma coe_le_coe {I J : fractional_ideal S P} :
  (I : submodule R P) ≤ (J : submodule R P) ↔ I ≤ J :=
iff.rfl

lemma zero_le (I : fractional_ideal S P) : 0 ≤ I :=
begin
  intros x hx,
  convert submodule.zero_mem _,
  simpa using hx
end

instance order_bot : order_bot (fractional_ideal S P) :=
{ bot := 0,
  bot_le := zero_le }

@[simp] lemma bot_eq_zero : (⊥ : fractional_ideal S P) = 0 :=
rfl

@[simp] lemma le_zero_iff {I : fractional_ideal S P} : I ≤ 0 ↔ I = 0 :=
le_bot_iff

lemma eq_zero_iff {I : fractional_ideal S P} : I = 0 ↔ (∀ x ∈ I, x = (0 : P)) :=
⟨ (λ h x hx, by simpa [h, mem_zero_iff] using hx),
  (λ h, le_bot_iff.mp (λ x hx, (mem_zero_iff S).mpr (h x hx))) ⟩

lemma _root_.is_fractional.sup {I J : submodule R P} :
  is_fractional S I → is_fractional S J → is_fractional S (I ⊔ J)
| ⟨aI, haI, hI⟩ ⟨aJ, haJ, hJ⟩ := ⟨aI * aJ, S.mul_mem haI haJ, λ b hb, begin
  rcases mem_sup.mp hb with ⟨bI, hbI, bJ, hbJ, rfl⟩,
  rw smul_add,
  apply is_integer_add,
  { rw [mul_smul, smul_comm],
    exact is_integer_smul (hI bI hbI), },
  { rw mul_smul,
    exact is_integer_smul (hJ bJ hbJ) }
end⟩

lemma _root_.is_fractional.inf_right {I : submodule R P} :
  is_fractional S I → ∀ J, is_fractional S (I ⊓ J)
| ⟨aI, haI, hI⟩ J := ⟨aI, haI, λ b hb, begin
  rcases mem_inf.mp hb with ⟨hbI, hbJ⟩,
  exact hI b hbI
end⟩

instance : has_inf (fractional_ideal S P) := ⟨λ I J, ⟨I ⊓ J, I.is_fractional.inf_right J⟩⟩

@[simp, norm_cast]
lemma coe_inf (I J : fractional_ideal S P) : ↑(I ⊓ J) = (I ⊓ J : submodule R P) := rfl

instance : has_sup (fractional_ideal S P) := ⟨λ I J, ⟨I ⊔ J, I.is_fractional.sup J.is_fractional⟩⟩

@[norm_cast]
lemma coe_sup (I J : fractional_ideal S P) : ↑(I ⊔ J) = (I ⊔ J : submodule R P) := rfl

instance lattice : lattice (fractional_ideal S P) :=
function.injective.lattice _ subtype.coe_injective coe_sup coe_inf

instance : semilattice_sup (fractional_ideal S P) :=
{ ..fractional_ideal.lattice }

end lattice

section semiring

instance : has_add (fractional_ideal S P) := ⟨(⊔)⟩

@[simp]
lemma sup_eq_add (I J : fractional_ideal S P) : I ⊔ J = I + J := rfl

@[simp, norm_cast]
lemma coe_add (I J : fractional_ideal S P) : (↑(I + J) : submodule R P) = I + J := rfl

@[simp, norm_cast]
lemma coe_ideal_sup (I J : ideal R) : ↑(I ⊔ J) = (I + J : fractional_ideal S P) :=
coe_to_submodule_injective $ coe_submodule_sup _ _ _

lemma _root_.is_fractional.nsmul {I : submodule R P} :
  Π n : ℕ, is_fractional S I → is_fractional S (n • I : submodule R P)
| 0 _ := begin
    rw [zero_smul],
    convert ((0 : ideal R) : fractional_ideal S P).is_fractional,
    simp,
  end
| (n + 1) h := begin
  rw succ_nsmul,
  exact h.sup (_root_.is_fractional.nsmul n h)
end

instance : has_smul ℕ (fractional_ideal S P) :=
{ smul := λ n I, ⟨n • I, I.is_fractional.nsmul n⟩}

@[norm_cast]
lemma coe_nsmul (n : ℕ) (I : fractional_ideal S P) : (↑(n • I) : submodule R P) = n • I := rfl

lemma _root_.is_fractional.mul {I J : submodule R P} :
  is_fractional S I → is_fractional S J → is_fractional S (I * J : submodule R P)
| ⟨aI, haI, hI⟩ ⟨aJ, haJ, hJ⟩ := ⟨aI * aJ, S.mul_mem haI haJ, λ b hb, begin
  apply submodule.mul_induction_on hb,
  { intros m hm n hn,
    obtain ⟨n', hn'⟩ := hJ n hn,
    rw [mul_smul, mul_comm m, ← smul_mul_assoc, ← hn', ← algebra.smul_def],
    apply hI,
    exact submodule.smul_mem _ _ hm },
  { intros x y hx hy,
    rw smul_add,
    apply is_integer_add hx hy },
end⟩

lemma _root_.is_fractional.pow {I : submodule R P} (h : is_fractional S I) :
  ∀ n : ℕ, is_fractional S (I ^ n : submodule R P)
| 0 := is_fractional_of_le_one _ (pow_zero _).le
| (n + 1) := (pow_succ I n).symm ▸ h.mul (_root_.is_fractional.pow n)

/-- `fractional_ideal.mul` is the product of two fractional ideals,
used to define the `has_mul` instance.

This is only an auxiliary definition: the preferred way of writing `I.mul J` is `I * J`.

Elaborated terms involving `fractional_ideal` tend to grow quite large,
so by making definitions irreducible, we hope to avoid deep unfolds.
-/
@[irreducible]
def mul (I J : fractional_ideal S P) : fractional_ideal S P :=
⟨I * J, I.is_fractional.mul J.is_fractional⟩

-- local attribute [semireducible] mul

instance : has_mul (fractional_ideal S P) := ⟨λ I J, mul I J⟩

@[simp] lemma mul_eq_mul (I J : fractional_ideal S P) : mul I J = I * J := rfl

lemma mul_def (I J : fractional_ideal S P) : I * J = ⟨I * J, I.is_fractional.mul J.is_fractional⟩ :=
by simp only [← mul_eq_mul, mul]

@[simp, norm_cast]
lemma coe_mul (I J : fractional_ideal S P) : (↑(I * J) : submodule R P) = I * J :=
by { simp only [mul_def], refl }

@[simp, norm_cast]
lemma coe_ideal_mul (I J : ideal R) : (↑(I * J) : fractional_ideal S P) = I * J :=
begin
  simp only [mul_def],
  exact coe_to_submodule_injective (coe_submodule_mul _ _ _)
end

lemma mul_left_mono (I : fractional_ideal S P) : monotone ((*) I) :=
begin
  intros J J' h,
  simp only [mul_def],
  exact mul_le.mpr (λ x hx y hy, mul_mem_mul hx (h hy))
end

lemma mul_right_mono (I : fractional_ideal S P) : monotone (λ J, J * I) :=
begin
  intros J J' h,
  simp only [mul_def],
  exact mul_le.mpr (λ x hx y hy, mul_mem_mul (h hx) hy)
end

lemma mul_mem_mul {I J : fractional_ideal S P} {i j : P} (hi : i ∈ I) (hj : j ∈ J) :
  i * j ∈ I * J :=
by { simp only [mul_def], exact submodule.mul_mem_mul hi hj }

lemma mul_le {I J K : fractional_ideal S P} :
  I * J ≤ K ↔ (∀ (i ∈ I) (j ∈ J), i * j ∈ K) :=
by { simp only [mul_def], exact submodule.mul_le }

instance : has_pow (fractional_ideal S P) ℕ := ⟨λ I n, ⟨I^n, I.is_fractional.pow n⟩⟩

@[simp, norm_cast]
lemma coe_pow (I : fractional_ideal S P) (n : ℕ) : ↑(I ^ n) = (I ^ n : submodule R P) := rfl

@[elab_as_eliminator] protected theorem mul_induction_on
  {I J : fractional_ideal S P}
  {C : P → Prop} {r : P} (hr : r ∈ I * J)
  (hm : ∀ (i ∈ I) (j ∈ J), C (i * j))
  (ha : ∀ x y, C x → C y → C (x + y)) : C r :=
begin
  simp only [mul_def] at hr,
  exact submodule.mul_induction_on hr hm ha
end

instance : has_nat_cast (fractional_ideal S P) := ⟨nat.unary_cast⟩

lemma coe_nat_cast (n : ℕ) : ((n : fractional_ideal S P) : submodule R P) = n :=
show ↑n.unary_cast = ↑n, by induction n; simp [*, nat.unary_cast]

instance : comm_semiring (fractional_ideal S P) :=
function.injective.comm_semiring coe subtype.coe_injective
  coe_zero coe_one coe_add coe_mul (λ _ _, coe_nsmul _ _) coe_pow coe_nat_cast

variables (S P)
/-- `fractional_ideal.submodule.has_coe` as a bundled `ring_hom`. -/
@[simps] def coe_submodule_hom : fractional_ideal S P →+* submodule R P :=
⟨coe, coe_one, coe_mul, coe_zero, coe_add⟩
variables {S P}

section order

lemma add_le_add_left {I J : fractional_ideal S P} (hIJ : I ≤ J) (J' : fractional_ideal S P) :
  J' + I ≤ J' + J :=
sup_le_sup_left hIJ J'

lemma mul_le_mul_left {I J : fractional_ideal S P} (hIJ : I ≤ J) (J' : fractional_ideal S P) :
  J' * I ≤ J' * J :=
mul_le.mpr (λ k hk j hj, mul_mem_mul hk (hIJ hj))

lemma le_self_mul_self {I : fractional_ideal S P} (hI: 1 ≤ I) : I ≤ I * I :=
begin
  convert mul_left_mono I hI,
  exact (mul_one I).symm
end

lemma mul_self_le_self {I : fractional_ideal S P} (hI: I ≤ 1) : I * I ≤ I :=
begin
  convert mul_left_mono I hI,
  exact (mul_one I).symm
end

lemma coe_ideal_le_one {I : ideal R} : (I : fractional_ideal S P) ≤ 1 :=
λ x hx, let ⟨y, _, hy⟩ := (mem_coe_ideal S).mp hx in (mem_one_iff S).mpr ⟨y, hy⟩

lemma le_one_iff_exists_coe_ideal {J : fractional_ideal S P} :
  J ≤ (1 : fractional_ideal S P) ↔ ∃ (I : ideal R), ↑I = J :=
begin
  split,
  { intro hJ,
    refine ⟨⟨{x : R | algebra_map R P x ∈ J}, _, _, _⟩, _⟩,
    { intros a b ha hb,
      rw [mem_set_of_eq, ring_hom.map_add],
      exact J.val.add_mem ha hb },
    { rw [mem_set_of_eq, ring_hom.map_zero],
      exact J.val.zero_mem },
    { intros c x hx,
      rw [smul_eq_mul, mem_set_of_eq, ring_hom.map_mul, ← algebra.smul_def],
      exact J.val.smul_mem c hx },
    { ext x,
      split,
      { rintros ⟨y, hy, eq_y⟩,
        rwa ← eq_y },
      { intro hx,
        obtain ⟨y, eq_x⟩ := (mem_one_iff S).mp (hJ hx),
        rw ← eq_x at *,
        exact ⟨y, hx, rfl⟩ } } },
  { rintro ⟨I, hI⟩,
    rw ← hI,
    apply coe_ideal_le_one },
end

@[simp] lemma one_le {I : fractional_ideal S P} :
  1 ≤ I ↔ (1 : P) ∈ I :=
by rw [← coe_le_coe, coe_one, submodule.one_le, mem_coe]

variables (S P)

/-- `coe_ideal_hom (S : submonoid R) P` is `coe : ideal R → fractional_ideal S P` as a ring hom -/
@[simps]
def coe_ideal_hom : ideal R →+* fractional_ideal S P :=
{ to_fun := coe,
  map_add' := coe_ideal_sup,
  map_mul' := coe_ideal_mul,
  map_one' := by rw [ideal.one_eq_top, coe_ideal_top],
  map_zero' := coe_ideal_bot }

lemma coe_ideal_pow (I : ideal R) (n : ℕ) : (↑(I^n) : fractional_ideal S P) = I^n :=
(coe_ideal_hom S P).map_pow _ n

open_locale big_operators
lemma coe_ideal_finprod [is_localization S P] {α : Sort*} {f : α → ideal R}
  (hS : S ≤ non_zero_divisors R) :
  ((∏ᶠ a : α, f a : ideal R) : fractional_ideal S P) = ∏ᶠ a : α, (f a : fractional_ideal S P) :=
monoid_hom.map_finprod_of_injective (coe_ideal_hom S P).to_monoid_hom (coe_ideal_injective' hS) f

end order

variables {P' : Type*} [comm_ring P'] [algebra R P'] [loc' : is_localization S P']
variables {P'' : Type*} [comm_ring P''] [algebra R P''] [loc'' : is_localization S P'']

lemma _root_.is_fractional.map (g : P →ₐ[R] P') {I : submodule R P} :
  is_fractional S I → is_fractional S (submodule.map g.to_linear_map I)
| ⟨a, a_nonzero, hI⟩ := ⟨a, a_nonzero, λ b hb, begin
  obtain ⟨b', b'_mem, hb'⟩ := submodule.mem_map.mp hb,
  obtain ⟨x, hx⟩ := hI b' b'_mem,
  use x,
  erw [←g.commutes, hx, g.map_smul, hb']
end⟩

/-- `I.map g` is the pushforward of the fractional ideal `I` along the algebra morphism `g` -/
def map (g : P →ₐ[R] P') :
  fractional_ideal S P → fractional_ideal S P' :=
λ I, ⟨submodule.map g.to_linear_map I, I.is_fractional.map g⟩

@[simp, norm_cast] lemma coe_map (g : P →ₐ[R] P') (I : fractional_ideal S P) :
  ↑(map g I) = submodule.map g.to_linear_map I := rfl

@[simp] lemma mem_map {I : fractional_ideal S P} {g : P →ₐ[R] P'}
  {y : P'} : y ∈ I.map g ↔ ∃ x, x ∈ I ∧ g x = y :=
submodule.mem_map

variables (I J : fractional_ideal S P) (g : P →ₐ[R] P')

@[simp] lemma map_id : I.map (alg_hom.id _ _) = I :=
coe_to_submodule_injective (submodule.map_id I)

@[simp] lemma map_comp (g' : P' →ₐ[R] P'') :
  I.map (g'.comp g) = (I.map g).map g' :=
coe_to_submodule_injective (submodule.map_comp g.to_linear_map g'.to_linear_map I)

@[simp, norm_cast] lemma map_coe_ideal (I : ideal R) :
  (I : fractional_ideal S P).map g = I :=
begin
  ext x,
  simp only [mem_coe_ideal],
  split,
  { rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩,
    exact ⟨y, hy, (g.commutes y).symm⟩ },
  { rintro ⟨y, hy, rfl⟩,
    exact ⟨_, ⟨y, hy, rfl⟩, g.commutes y⟩ },
end

@[simp] lemma map_one :
  (1 : fractional_ideal S P).map g = 1 :=
map_coe_ideal g ⊤

@[simp] lemma map_zero :
  (0 : fractional_ideal S P).map g = 0 :=
map_coe_ideal g 0

@[simp] lemma map_add : (I + J).map g = I.map g + J.map g :=
coe_to_submodule_injective (submodule.map_sup _ _ _)

@[simp] lemma map_mul : (I * J).map g = I.map g * J.map g :=
begin
  simp only [mul_def],
  exact coe_to_submodule_injective (submodule.map_mul _ _ _)
end

@[simp] lemma map_map_symm (g : P ≃ₐ[R] P') :
  (I.map (g : P →ₐ[R] P')).map (g.symm : P' →ₐ[R] P) = I :=
by rw [←map_comp, g.symm_comp, map_id]

@[simp] lemma map_symm_map (I : fractional_ideal S P') (g : P ≃ₐ[R] P') :
  (I.map (g.symm : P' →ₐ[R] P)).map (g : P →ₐ[R] P') = I :=
by rw [←map_comp, g.comp_symm, map_id]

lemma map_mem_map {f : P →ₐ[R] P'} (h : function.injective f) {x : P} {I : fractional_ideal S P} :
  f x ∈ map f I ↔ x ∈ I :=
mem_map.trans ⟨λ ⟨x', hx', x'_eq⟩, h x'_eq ▸ hx', λ h, ⟨x, h, rfl⟩⟩

lemma map_injective (f : P →ₐ[R] P') (h : function.injective f) :
  function.injective (map f : fractional_ideal S P → fractional_ideal S P') :=
λ I J hIJ, ext (λ x, (map_mem_map h).symm.trans (hIJ.symm ▸ map_mem_map h))

/-- If `g` is an equivalence, `map g` is an isomorphism -/
def map_equiv (g : P ≃ₐ[R] P') :
  fractional_ideal S P ≃+* fractional_ideal S P' :=
{ to_fun := map g,
  inv_fun := map g.symm,
  map_add' := λ I J, map_add I J _,
  map_mul' := λ I J, map_mul I J _,
  left_inv := λ I, by { rw [←map_comp, alg_equiv.symm_comp, map_id] },
  right_inv := λ I, by { rw [←map_comp, alg_equiv.comp_symm, map_id] } }

@[simp] lemma coe_fun_map_equiv (g : P ≃ₐ[R] P') :
  (map_equiv g : fractional_ideal S P → fractional_ideal S P') = map g :=
rfl

@[simp] lemma map_equiv_apply (g : P ≃ₐ[R] P') (I : fractional_ideal S P) :
  map_equiv g I = map ↑g I := rfl

@[simp] lemma map_equiv_symm (g : P ≃ₐ[R] P') :
  ((map_equiv g).symm : fractional_ideal S P' ≃+* _) = map_equiv g.symm := rfl

@[simp] lemma map_equiv_refl :
  map_equiv alg_equiv.refl = ring_equiv.refl (fractional_ideal S P) :=
ring_equiv.ext (λ x, by simp)

lemma is_fractional_span_iff {s : set P} :
  is_fractional S (span R s) ↔ ∃ a ∈ S, ∀ (b : P), b ∈ s → is_integer R (a • b) :=
⟨λ ⟨a, a_mem, h⟩, ⟨a, a_mem, λ b hb, h b (subset_span hb)⟩,
 λ ⟨a, a_mem, h⟩, ⟨a, a_mem, λ b hb, span_induction hb
   h
   (by { rw smul_zero, exact is_integer_zero })
   (λ x y hx hy, by { rw smul_add, exact is_integer_add hx hy })
   (λ s x hx, by { rw smul_comm, exact is_integer_smul hx })⟩⟩

include loc

lemma _root_.is_fractional_of_fg {I : submodule R P} (hI : I.fg) :
  is_fractional S I :=
begin
  rcases hI with ⟨I, rfl⟩,
  rcases exist_integer_multiples_of_finset S I with ⟨⟨s, hs1⟩, hs⟩,
  rw is_fractional_span_iff,
  exact ⟨s, hs1, hs⟩,
end

lemma _root_.is_fractional_unit (I : (submodule R P)ˣ) : is_fractional S (I : submodule R P) :=
is_fractional_of_fg $ fg_unit I

lemma _root_.is_fractional_of_is_unit {I : submodule R P} (hI : is_unit I) : is_fractional S I :=
is_fractional_of_fg $ fg_of_is_unit hI

/-- The group of invertible fractional `R`-ideals in `P` is isomorphic to
  the group of invertible `R`-submodules of `P`. -/
def unit_equiv : (fractional_ideal S P)ˣ ≃* (submodule R P)ˣ :=
{ to_fun := λ I, by use [I, ↑I⁻¹];
    simp only [coe_coe, ← fractional_ideal.coe_mul, I.mul_inv, I.inv_mul, fractional_ideal.coe_one],
  inv_fun := λ I, begin
    use [⟨I, is_fractional_unit I⟩, ⟨_, is_fractional_unit I⁻¹⟩];
    apply subtype.ext;
    simp only [fractional_ideal.coe_mul, fractional_ideal.coe_mk,
               I.mul_inv, I.inv_mul, fractional_ideal.coe_one],
  end,
  left_inv := λ I, by { ext1, ext1, refl },
  right_inv := λ I, by { ext1, refl },
  map_mul' := λ I J, begin
    ext1, simp only [coe_coe, fractional_ideal.coe_mul, units.coe_mul, units.coe_mk],
  end }

omit loc

lemma mem_span_mul_finite_of_mem_mul {I J : fractional_ideal S P} {x : P} (hx : x ∈ I * J) :
  ∃ (T T' : finset P), (T : set P) ⊆ I ∧ (T' : set P) ⊆ J ∧ x ∈ span R (T * T' : set P) :=
submodule.mem_span_mul_finite_of_mem_mul (by simpa using mem_coe.mpr hx)

variables (S)

lemma coe_ideal_fg (inj : function.injective (algebra_map R P)) (I : ideal R) :
  fg ((I : fractional_ideal S P) : submodule R P) ↔ I.fg :=
coe_submodule_fg _ inj _

variables {S}

lemma fg_unit (I : (fractional_ideal S P)ˣ) :
  fg (I : submodule R P) :=
submodule.fg_unit $ units.map (coe_submodule_hom S P).to_monoid_hom I

lemma fg_of_is_unit (I : fractional_ideal S P) (h : is_unit I) :
  fg (I : submodule R P) :=
fg_unit h.unit

lemma _root_.ideal.fg_of_is_unit (inj : function.injective (algebra_map R P))
  (I : ideal R) (h : is_unit (I : fractional_ideal S P)) :
  I.fg :=
by { rw ← coe_ideal_fg S inj I, exact fg_of_is_unit I h }

variables (S P P')

include loc loc'

@[irreducible]
noncomputable def canonical_equiv :
  fractional_ideal S P ≃+* fractional_ideal S P' :=
submodule.map_equiv
  { commutes' := λ r, ring_equiv_of_ring_equiv_eq _ _,
    ..ring_equiv_of_ring_equiv P P' (ring_equiv.refl R)
      (show S.map _ = S, by rw [ring_equiv.to_monoid_hom_refl, submonoid.map_id]) }


/-- `canonical_equiv f f'` is the canonical equivalence between the fractional
ideals in `P` and in `P'` -/
@[irreducible]
noncomputable def canonical_equiv :
  fractional_ideal S P ≃+* fractional_ideal S P' :=
map_equiv
  { commutes' := λ r, ring_equiv_of_ring_equiv_eq _ _,
    ..ring_equiv_of_ring_equiv P P' (ring_equiv.refl R)
      (show S.map _ = S, by rw [ring_equiv.to_monoid_hom_refl, submonoid.map_id]) }

@[simp] lemma mem_canonical_equiv_apply {I : fractional_ideal S P} {x : P'} :
  x ∈ canonical_equiv S P P' I ↔
    ∃ y ∈ I, is_localization.map P' (ring_hom.id R)
      (λ y (hy : y ∈ S), show ring_hom.id R y ∈ S, from hy) (y : P) = x :=
begin
  rw [canonical_equiv, map_equiv_apply, mem_map],
  exact ⟨λ ⟨y, mem, eq⟩, ⟨y, mem, eq⟩, λ ⟨y, mem, eq⟩, ⟨y, mem, eq⟩⟩
end

@[simp] lemma canonical_equiv_symm :
  (canonical_equiv S P P').symm = canonical_equiv S P' P :=
ring_equiv.ext $ λ I, set_like.ext_iff.mpr $ λ x,
by { rw [mem_canonical_equiv_apply, canonical_equiv, map_equiv_symm, map_equiv,
         ring_equiv.coe_mk, mem_map],
    exact ⟨λ ⟨y, mem, eq⟩, ⟨y, mem, eq⟩, λ ⟨y, mem, eq⟩, ⟨y, mem, eq⟩⟩ }

lemma canonical_equiv_flip (I) :
  canonical_equiv S P P' (canonical_equiv S P' P I) = I :=
by rw [←canonical_equiv_symm, ring_equiv.symm_apply_apply]

@[simp]
lemma canonical_equiv_canonical_equiv (P'' : Type*) [comm_ring P''] [algebra R P'']
  [is_localization S P''] (I : fractional_ideal S P) :
  canonical_equiv S P' P'' (canonical_equiv S P P' I) = canonical_equiv S P P'' I :=
begin
  ext,
  simp only [is_localization.map_map, ring_hom_inv_pair.comp_eq₂, mem_canonical_equiv_apply,
      exists_prop, exists_exists_and_eq_and],
  refl
end

lemma canonical_equiv_trans_canonical_equiv (P'' : Type*) [comm_ring P'']
  [algebra R P''] [is_localization S P''] :
  (canonical_equiv S P P').trans (canonical_equiv S P' P'') = canonical_equiv S P P'' :=
ring_equiv.ext (canonical_equiv_canonical_equiv S P P' P'')

@[simp]
lemma canonical_equiv_coe_ideal (I : ideal R) :
  canonical_equiv S P P' I = I :=
by { ext, simp [is_localization.map_eq] }

omit loc'

@[simp]
lemma canonical_equiv_self : canonical_equiv S P P = ring_equiv.refl _ :=
begin
  rw ← canonical_equiv_trans_canonical_equiv S P P,
  convert (canonical_equiv S P P).symm_trans_self,
  exact (canonical_equiv_symm S P P).symm
end

end semiring

section is_fraction_ring

/-!
### `is_fraction_ring` section

This section concerns fractional ideals in the field of fractions,
i.e. the type `fractional_ideal R⁰ K` where `is_fraction_ring R K`.
-/

variables {K K' : Type*} [field K] [field K']
variables [algebra R K] [is_fraction_ring R K] [algebra R K'] [is_fraction_ring R K']
variables {I J : fractional_ideal R⁰ K} (h : K →ₐ[R] K')

/-- Nonzero fractional ideals contain a nonzero integer. -/
lemma exists_ne_zero_mem_is_integer [nontrivial R] (hI : I ≠ 0) :
  ∃ x ≠ (0 : R), algebra_map R K x ∈ I :=
begin
  obtain ⟨y, y_mem, y_not_mem⟩ := set_like.exists_of_lt
    (by simpa only using bot_lt_iff_ne_bot.mpr hI),
  have y_ne_zero : y ≠ 0 := by simpa using y_not_mem,
  obtain ⟨z, ⟨x, hx⟩⟩ := exists_integer_multiple R⁰ y,
  refine ⟨x, _, _⟩,
  { rw [ne.def, ← @is_fraction_ring.to_map_eq_zero_iff R _ K, hx, algebra.smul_def],
    exact mul_ne_zero (is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors z.2) y_ne_zero },
  { rw hx,
    exact smul_mem _ _ y_mem }
end

lemma map_ne_zero [nontrivial R] (hI : I ≠ 0) : I.map h ≠ 0 :=
begin
  obtain ⟨x, x_ne_zero, hx⟩ := exists_ne_zero_mem_is_integer hI,
  contrapose! x_ne_zero with map_eq_zero,
  refine is_fraction_ring.to_map_eq_zero_iff.mp (eq_zero_iff.mp map_eq_zero _ (mem_map.mpr _)),
  exact ⟨algebra_map R K x, hx, h.commutes x⟩,
end

@[simp] lemma map_eq_zero_iff [nontrivial R] : I.map h = 0 ↔ I = 0 :=
⟨imp_of_not_imp_not _ _ (map_ne_zero _), λ hI, hI.symm ▸ map_zero h⟩

lemma coe_ideal_injective : function.injective (coe : ideal R → fractional_ideal R⁰ K) :=
coe_ideal_injective' le_rfl

lemma coe_ideal_inj {I J : ideal R} :
  (I : fractional_ideal R⁰ K) = (J : fractional_ideal R⁰ K) ↔ I = J :=
coe_ideal_inj' le_rfl

@[simp] lemma coe_ideal_eq_zero {I : ideal R} : (I : fractional_ideal R⁰ K) = 0 ↔ I = ⊥ :=
coe_ideal_eq_zero' le_rfl

lemma coe_ideal_ne_zero {I : ideal R} : (I : fractional_ideal R⁰ K) ≠ 0 ↔ I ≠ ⊥ :=
coe_ideal_ne_zero' le_rfl

@[simp] lemma coe_ideal_eq_one {I : ideal R} : (I : fractional_ideal R⁰ K) = 1 ↔ I = 1 :=
by simpa only [ideal.one_eq_top] using coe_ideal_inj

lemma coe_ideal_ne_one {I : ideal R} : (I : fractional_ideal R⁰ K) ≠ 1 ↔ I ≠ 1 :=
not_iff_not.mpr coe_ideal_eq_one

end is_fraction_ring

section quotient

/-!
### `quotient` section

This section defines the ideal quotient of fractional ideals.

In this section we need that each non-zero `y : R` has an inverse in
the localization, i.e. that the localization is a field. We satisfy this
assumption by taking `S = non_zero_divisors R`, `R`'s localization at which
is a field because `R` is a domain.
-/

open_locale classical

variables {R₁ : Type*} [comm_ring R₁] {K : Type*} [field K]
variables [algebra R₁ K] [frac : is_fraction_ring R₁ K]

instance : nontrivial (fractional_ideal R₁⁰ K) :=
⟨⟨0, 1, λ h,
  have this : (1 : K) ∈ (0 : fractional_ideal R₁⁰ K) :=
    by { rw ← (algebra_map R₁ K).map_one, simpa only [h] using coe_mem_one R₁⁰ 1 },
  one_ne_zero ((mem_zero_iff _).mp this)⟩⟩

lemma ne_zero_of_mul_eq_one (I J : fractional_ideal R₁⁰ K) (h : I * J = 1) : I ≠ 0 :=
λ hI, zero_ne_one' (fractional_ideal R₁⁰ K) (by { convert h, simp [hI], })

variables [is_domain R₁]

include frac

lemma _root_.is_fractional.div_of_nonzero {I J : submodule R₁ K} :
  is_fractional R₁⁰ I → is_fractional R₁⁰ J → J ≠ 0 → is_fractional R₁⁰ (I / J)
| ⟨aI, haI, hI⟩ ⟨aJ, haJ, hJ⟩ h := begin
  obtain ⟨y, mem_J, not_mem_zero⟩ := set_like.exists_of_lt
    (by simpa only using bot_lt_iff_ne_bot.mpr h),
  obtain ⟨y', hy'⟩ := hJ y mem_J,
  use (aI * y'),
  split,
  { apply (non_zero_divisors R₁).mul_mem haI (mem_non_zero_divisors_iff_ne_zero.mpr _),
    intro y'_eq_zero,
    have : algebra_map R₁ K aJ * y = 0,
    { rw [← algebra.smul_def, ←hy', y'_eq_zero, ring_hom.map_zero] },
    have y_zero := (mul_eq_zero.mp this).resolve_left
      (mt ((injective_iff_map_eq_zero (algebra_map R₁ K)).1 (is_fraction_ring.injective _ _) _)
          (mem_non_zero_divisors_iff_ne_zero.mp haJ)),
    apply not_mem_zero,
    simpa only using (mem_zero_iff R₁⁰).mpr y_zero, },
  intros b hb,
  convert hI _ (hb _ (submodule.smul_mem _ aJ mem_J)) using 1,
  rw [← hy', mul_comm b, ← algebra.smul_def, mul_smul]
end

lemma fractional_div_of_nonzero {I J : fractional_ideal R₁⁰ K} (h : J ≠ 0) :
  is_fractional R₁⁰ (I / J : submodule R₁ K) :=
I.is_fractional.div_of_nonzero J.is_fractional $ λ H, h $
  coe_to_submodule_injective $ H.trans coe_zero.symm

noncomputable instance : has_div (fractional_ideal R₁⁰ K) :=
⟨ λ I J, if h : J = 0 then 0 else ⟨I / J, fractional_div_of_nonzero h⟩ ⟩

variables {I J : fractional_ideal R₁⁰ K} [ J ≠ 0 ]

@[simp] lemma div_zero {I : fractional_ideal R₁⁰ K} :
  I / 0 = 0 :=
dif_pos rfl

lemma div_nonzero {I J : fractional_ideal R₁⁰ K} (h : J ≠ 0) :
  (I / J) = ⟨I / J, fractional_div_of_nonzero h⟩ :=
dif_neg h

@[simp] lemma coe_div {I J : fractional_ideal R₁⁰ K} (hJ : J ≠ 0) :
  (↑(I / J) : submodule R₁ K) = ↑I / (↑J : submodule R₁ K) :=
congr_arg _ (dif_neg hJ)

lemma mem_div_iff_of_nonzero {I J : fractional_ideal R₁⁰ K} (h : J ≠ 0) {x} :
  x ∈ I / J ↔ ∀ y ∈ J, x * y ∈ I :=
by { rw div_nonzero h, exact submodule.mem_div_iff_forall_mul_mem }

lemma mul_one_div_le_one {I : fractional_ideal R₁⁰ K} : I * (1 / I) ≤ 1 :=
begin
  by_cases hI : I = 0,
  { rw [hI, div_zero, mul_zero],
    exact zero_le 1 },
  { rw [← coe_le_coe, coe_mul, coe_div hI, coe_one],
    apply submodule.mul_one_div_le_one },
end

lemma le_self_mul_one_div {I : fractional_ideal R₁⁰ K} (hI : I ≤ (1 : fractional_ideal R₁⁰ K)) :
  I ≤ I * (1 / I) :=
begin
  by_cases hI_nz : I = 0,
  { rw [hI_nz, div_zero, mul_zero], exact zero_le 0 },
  { rw [← coe_le_coe, coe_mul, coe_div hI_nz, coe_one],
    rw [← coe_le_coe, coe_one] at hI,
    exact submodule.le_self_mul_one_div hI },
end

lemma le_div_iff_of_nonzero {I J J' : fractional_ideal R₁⁰ K} (hJ' : J' ≠ 0) :
  I ≤ J / J' ↔ ∀ (x ∈ I) (y ∈ J'), x * y ∈ J :=
⟨ λ h x hx, (mem_div_iff_of_nonzero hJ').mp (h hx),
  λ h x hx, (mem_div_iff_of_nonzero hJ').mpr (h x hx) ⟩

lemma le_div_iff_mul_le {I J J' : fractional_ideal R₁⁰ K} (hJ' : J' ≠ 0) :
  I ≤ J / J' ↔ I * J' ≤ J :=
begin
  rw div_nonzero hJ',
  convert submodule.le_div_iff_mul_le using 1,
  rw [← coe_mul, coe_le_coe]
end

@[simp] lemma div_one {I : fractional_ideal R₁⁰ K} : I / 1 = I :=
begin
  rw [div_nonzero (one_ne_zero' (fractional_ideal R₁⁰ K))],
  ext,
  split; intro h,
  { simpa using mem_div_iff_forall_mul_mem.mp h 1
      ((algebra_map R₁ K).map_one ▸ coe_mem_one R₁⁰ 1) },
  { apply mem_div_iff_forall_mul_mem.mpr,
    rintros y ⟨y', _, rfl⟩,
    rw mul_comm,
    convert submodule.smul_mem _ y' h,
    exact (algebra.smul_def _ _).symm }
end

theorem eq_one_div_of_mul_eq_one_right (I J : fractional_ideal R₁⁰ K) (h : I * J = 1) :
  J = 1 / I :=
begin
  have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J h,
  suffices h' : I * (1 / I) = 1,
  { exact (congr_arg units.inv $
      @units.ext _ _ (units.mk_of_mul_eq_one _ _ h) (units.mk_of_mul_eq_one _ _ h') rfl) },
  apply le_antisymm,
  { apply mul_le.mpr _,
    intros x hx y hy,
    rw mul_comm,
    exact (mem_div_iff_of_nonzero hI).mp hy x hx },
  rw ← h,
  apply mul_left_mono I,
  apply (le_div_iff_of_nonzero hI).mpr _,
  intros y hy x hx,
  rw mul_comm,
  exact mul_mem_mul hx hy,
end

theorem mul_div_self_cancel_iff {I : fractional_ideal R₁⁰ K} :
  I * (1 / I) = 1 ↔ ∃ J, I * J = 1 :=
⟨λ h, ⟨(1 / I), h⟩, λ ⟨J, hJ⟩, by rwa [← eq_one_div_of_mul_eq_one_right I J hJ]⟩

variables {K' : Type*} [field K'] [algebra R₁ K'] [is_fraction_ring R₁ K']

@[simp] lemma map_div (I J : fractional_ideal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
  (I / J).map (h : K →ₐ[R₁] K') = I.map h / J.map h :=
begin
  by_cases H : J = 0,
  { rw [H, div_zero, map_zero, div_zero] },
  { apply coe_to_submodule_injective,
    simp [div_nonzero H, div_nonzero (map_ne_zero _ H), submodule.map_div] }
end

@[simp] lemma map_one_div (I : fractional_ideal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
  (1 / I).map (h : K →ₐ[R₁] K') = 1 / I.map h :=
by rw [map_div, map_one]

end quotient

section field

variables {R₁ K L : Type*} [comm_ring R₁] [field K] [field L]
variables [algebra R₁ K] [is_fraction_ring R₁ K] [algebra K L] [is_fraction_ring K L]

lemma eq_zero_or_one (I : fractional_ideal K⁰ L) : I = 0 ∨ I = 1 :=
begin
  rw or_iff_not_imp_left,
  intro hI,
  simp_rw [@set_like.ext_iff _ _ _ I 1, mem_one_iff],
  intro x,
  split,
  { intro x_mem,
    obtain ⟨n, d, rfl⟩ := is_localization.mk'_surjective K⁰ x,
    refine ⟨n / d, _⟩,
    rw [map_div₀, is_fraction_ring.mk'_eq_div] },
  { rintro ⟨x, rfl⟩,
    obtain ⟨y, y_ne, y_mem⟩ := exists_ne_zero_mem_is_integer hI,
    rw [← div_mul_cancel x y_ne, ring_hom.map_mul, ← algebra.smul_def],
    exact submodule.smul_mem I _ y_mem }
end

lemma eq_zero_or_one_of_is_field (hF : is_field R₁) (I : fractional_ideal R₁⁰ K) : I = 0 ∨ I = 1 :=
by letI : field R₁ := hF.to_field; exact eq_zero_or_one I

end field

section principal_ideal_ring

variables {R₁ : Type*} [comm_ring R₁] {K : Type*} [field K]
variables [algebra R₁ K] [is_fraction_ring R₁ K]

open_locale classical

variables (R₁)

/-- `fractional_ideal.span_finset R₁ s f` is the fractional ideal of `R₁` generated by `f '' s`. -/
@[simps] def span_finset {ι : Type*} (s : finset ι) (f : ι → K) : fractional_ideal R₁⁰ K :=
⟨submodule.span R₁ (f '' s), begin
  obtain ⟨a', ha'⟩ := is_localization.exist_integer_multiples R₁⁰ s f,
  refine ⟨a', a'.2, λ x hx, submodule.span_induction hx _ _ _ _⟩,
  { rintro _ ⟨i, hi, rfl⟩, exact ha' i hi },
  { rw smul_zero, exact is_localization.is_integer_zero },
  { intros x y hx hy, rw smul_add, exact is_localization.is_integer_add hx hy },
  { intros c x hx, rw smul_comm, exact is_localization.is_integer_smul hx }
end⟩

variables {R₁}

@[simp] lemma span_finset_eq_zero {ι : Type*} {s : finset ι} {f : ι → K} :
  span_finset R₁ s f = 0 ↔ ∀ j ∈ s, f j = 0 :=
by simp only [← coe_to_submodule_inj, span_finset_coe, coe_zero, submodule.span_eq_bot,
  set.mem_image, finset.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

lemma span_finset_ne_zero {ι : Type*} {s : finset ι} {f : ι → K} :
  span_finset R₁ s f ≠ 0 ↔ ∃ j ∈ s, f j ≠ 0 :=
by simp

open submodule.is_principal

include loc

lemma is_fractional_span_singleton (x : P) : is_fractional S (span R {x} : submodule R P) :=
let ⟨a, ha⟩ := exists_integer_multiple S x in
is_fractional_span_iff.mpr ⟨a, a.2, λ x' hx', (set.mem_singleton_iff.mp hx').symm ▸ ha⟩

variables (S)

/-- `span_singleton x` is the fractional ideal generated by `x` if `0 ∉ S` -/
@[irreducible]
def span_singleton (x : P) : fractional_ideal S P :=
⟨span R {x}, is_fractional_span_singleton x⟩

-- local attribute [semireducible] span_singleton

@[simp] lemma coe_span_singleton (x : P) :
  (span_singleton S x : submodule R P) = span R {x} :=
by { rw span_singleton, refl }

@[simp] lemma mem_span_singleton {x y : P} :
  x ∈ span_singleton S y ↔ ∃ (z : R), z • y = x :=
by { rw span_singleton, exact submodule.mem_span_singleton }

lemma mem_span_singleton_self (x : P) :
  x ∈ span_singleton S x :=
(mem_span_singleton S).mpr ⟨1, one_smul _ _⟩

variables {S}

@[simp] lemma span_singleton_le_iff_mem {x : P} {I : fractional_ideal S P} :
  span_singleton S x ≤ I ↔ x ∈ I :=
by rw [← coe_le_coe, coe_span_singleton, submodule.span_singleton_le_iff_mem x ↑I, mem_coe]

lemma span_singleton_eq_span_singleton [no_zero_smul_divisors R P] {x y : P} :
  span_singleton S x = span_singleton S y ↔ ∃ z : Rˣ, z • x = y :=
by { rw [← submodule.span_singleton_eq_span_singleton, span_singleton, span_singleton],
  exact subtype.mk_eq_mk }

lemma eq_span_singleton_of_principal (I : fractional_ideal S P)
  [is_principal (I : submodule R P)] :
  I = span_singleton S (generator (I : submodule R P)) :=
by { rw span_singleton, exact coe_to_submodule_injective (span_singleton_generator ↑I).symm }

lemma is_principal_iff (I : fractional_ideal S P) :
  is_principal (I : submodule R P) ↔ ∃ x, I = span_singleton S x :=
⟨λ h, ⟨@generator _ _ _ _ _ ↑I h, @eq_span_singleton_of_principal _ _ _ _ _ _ _ I h⟩,
 λ ⟨x, hx⟩, { principal := ⟨x, trans (congr_arg _ hx) (coe_span_singleton _ x)⟩ } ⟩

@[simp] lemma span_singleton_zero : span_singleton S (0 : P) = 0 :=
by { ext, simp [submodule.mem_span_singleton, eq_comm] }

lemma span_singleton_eq_zero_iff {y : P} : span_singleton S y = 0 ↔ y = 0 :=
⟨λ h, span_eq_bot.mp (by simpa using congr_arg subtype.val h : span R {y} = ⊥) y (mem_singleton y),
 λ h, by simp [h] ⟩

lemma span_singleton_ne_zero_iff {y : P} : span_singleton S y ≠ 0 ↔ y ≠ 0 :=
not_congr span_singleton_eq_zero_iff

@[simp] lemma span_singleton_one : span_singleton S (1 : P) = 1 :=
begin
  ext,
  refine (mem_span_singleton S).trans ((exists_congr _).trans (mem_one_iff S).symm),
  intro x',
  rw [algebra.smul_def, mul_one]
end

@[simp]
lemma span_singleton_mul_span_singleton (x y : P) :
  span_singleton S x * span_singleton S y = span_singleton S (x * y) :=
begin
  apply coe_to_submodule_injective,
  simp only [coe_mul, coe_span_singleton, span_mul_span, singleton_mul_singleton],
end

@[simp]
lemma span_singleton_pow (x : P) (n : ℕ) : span_singleton S x ^ n = span_singleton S (x ^ n) :=
begin
  induction n with n hn,
  { rw [pow_zero, pow_zero, span_singleton_one] },
  { rw [pow_succ, hn, span_singleton_mul_span_singleton, pow_succ] }
end

@[simp]
lemma coe_ideal_span_singleton (x : R) :
  (↑(ideal.span {x} : ideal R) : fractional_ideal S P) = span_singleton S (algebra_map R P x) :=
begin
  ext y,
  refine (mem_coe_ideal S).trans (iff.trans _ (mem_span_singleton S).symm),
  split,
  { rintros ⟨y', hy', rfl⟩,
    obtain ⟨x', rfl⟩ := submodule.mem_span_singleton.mp hy',
    use x',
    rw [smul_eq_mul, ring_hom.map_mul, algebra.smul_def] },
  { rintros ⟨y', rfl⟩,
    refine ⟨y' * x, submodule.mem_span_singleton.mpr ⟨y', rfl⟩, _⟩,
    rw [ring_hom.map_mul, algebra.smul_def] }
end

@[simp]
lemma canonical_equiv_span_singleton {P'} [comm_ring P'] [algebra R P'] [is_localization S P']
  (x : P) :
  canonical_equiv S P P' (span_singleton S x) =
    span_singleton S (is_localization.map P' (ring_hom.id R)
      (λ y (hy : y ∈ S), show ring_hom.id R y ∈ S, from hy) x) :=
begin
  apply set_like.ext_iff.mpr,
  intro y,
  split; intro h,
  { rw mem_span_singleton,
    obtain ⟨x', hx', rfl⟩ := (mem_canonical_equiv_apply _ _ _).mp h,
    obtain ⟨z, rfl⟩ := (mem_span_singleton _).mp hx',
    use z,
    rw is_localization.map_smul,
    refl },
  { rw mem_canonical_equiv_apply,
    obtain ⟨z, rfl⟩ := (mem_span_singleton _).mp h,
    use z • x,
    use (mem_span_singleton _).mpr ⟨z, rfl⟩,
    simp [is_localization.map_smul] }
end

lemma mem_singleton_mul {x y : P} {I : fractional_ideal S P} :
  y ∈ span_singleton S x * I ↔ ∃ y' ∈ I, y = x * y' :=
begin
  split,
  { intro h,
    apply fractional_ideal.mul_induction_on h,
    { intros x' hx' y' hy',
      obtain ⟨a, ha⟩ := (mem_span_singleton S).mp hx',
      use [a • y', submodule.smul_mem I a hy'],
      rw [←ha, algebra.mul_smul_comm, algebra.smul_mul_assoc] },
    { rintros _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩,
      exact ⟨y + y', submodule.add_mem I hy hy', (mul_add _ _ _).symm⟩ } },
  { rintros ⟨y', hy', rfl⟩,
    exact mul_mem_mul ((mem_span_singleton S).mpr ⟨1, one_smul _ _⟩) hy' }
end

omit loc

variables (K)

lemma mk'_mul_coe_ideal_eq_coe_ideal {I J : ideal R₁} {x y : R₁} (hy : y ∈ R₁⁰) :
  span_singleton R₁⁰ (is_localization.mk' K x ⟨y, hy⟩) * I = (J : fractional_ideal R₁⁰ K) ↔
  ideal.span {x} * I = ideal.span {y} * J :=
begin
  have : span_singleton R₁⁰ (is_localization.mk' _ (1 : R₁) ⟨y, hy⟩) *
           span_singleton R₁⁰ (algebra_map R₁ K y) = 1,
  { rw [span_singleton_mul_span_singleton, mul_comm, ← is_localization.mk'_eq_mul_mk'_one,
        is_localization.mk'_self, span_singleton_one] },
  let y' : (fractional_ideal R₁⁰ K)ˣ := units.mk_of_mul_eq_one _ _ this,
  have coe_y' : ↑y' = span_singleton R₁⁰ (is_localization.mk' K (1 : R₁) ⟨y, hy⟩) := rfl,
  refine iff.trans _ (y'.mul_right_inj.trans coe_ideal_inj),
  rw [coe_y', coe_ideal_mul, coe_ideal_span_singleton, coe_ideal_mul, coe_ideal_span_singleton,
    ←mul_assoc, span_singleton_mul_span_singleton, ←mul_assoc, span_singleton_mul_span_singleton,
    mul_comm (mk' _ _ _), ← is_localization.mk'_eq_mul_mk'_one,
    mul_comm (mk' _ _ _), ← is_localization.mk'_eq_mul_mk'_one,
    is_localization.mk'_self, span_singleton_one, one_mul],
end

variables {K}

lemma span_singleton_mul_coe_ideal_eq_coe_ideal {I J : ideal R₁} {z : K} :
  span_singleton R₁⁰ z * (I : fractional_ideal R₁⁰ K) = J ↔
  ideal.span {((is_localization.sec R₁⁰ z).1 : R₁)} * I =
    ideal.span {(is_localization.sec R₁⁰ z).2} * J :=
-- `erw` to deal with the distinction between `y` and `⟨y.1, y.2⟩`
by erw [← mk'_mul_coe_ideal_eq_coe_ideal K (is_localization.sec R₁⁰ z).2.prop,
        is_localization.mk'_sec K z]

variables [is_domain R₁]

lemma one_div_span_singleton (x : K) :
  1 / span_singleton R₁⁰ x = span_singleton R₁⁰ (x⁻¹) :=
if h : x = 0 then by simp [h] else (eq_one_div_of_mul_eq_one_right _ _ (by simp [h])).symm

@[simp] lemma div_span_singleton (J : fractional_ideal R₁⁰ K) (d : K) :
  J / span_singleton R₁⁰ d = span_singleton R₁⁰ (d⁻¹) * J :=
begin
  rw ← one_div_span_singleton,
  by_cases hd : d = 0,
  { simp only [hd, span_singleton_zero, div_zero, zero_mul] },
  have h_spand : span_singleton R₁⁰ d ≠ 0 := mt span_singleton_eq_zero_iff.mp hd,
  apply le_antisymm,
  { intros x hx,
    rw [← mem_coe, coe_div h_spand, submodule.mem_div_iff_forall_mul_mem] at hx,
    specialize hx d (mem_span_singleton_self R₁⁰ d),
    have h_xd : x = d⁻¹ * (x * d), { field_simp },
    rw [← mem_coe, coe_mul, one_div_span_singleton, h_xd],
    exact submodule.mul_mem_mul (mem_span_singleton_self R₁⁰ _) hx },
  { rw [le_div_iff_mul_le h_spand, mul_assoc, mul_left_comm, one_div_span_singleton,
    span_singleton_mul_span_singleton, inv_mul_cancel hd, span_singleton_one, mul_one],
    exact le_refl J },
end

lemma exists_eq_span_singleton_mul (I : fractional_ideal R₁⁰ K) :
  ∃ (a : R₁) (aI : ideal R₁), a ≠ 0 ∧ I = span_singleton R₁⁰ (algebra_map R₁ K a)⁻¹ * aI :=
begin
  obtain ⟨a_inv, nonzero, ha⟩ := I.is_fractional,
  have nonzero := mem_non_zero_divisors_iff_ne_zero.mp nonzero,
  have map_a_nonzero : algebra_map R₁ K a_inv ≠ 0 :=
    mt is_fraction_ring.to_map_eq_zero_iff.mp nonzero,
  refine ⟨a_inv,
          submodule.comap (algebra.linear_map R₁ K)
            ↑(span_singleton R₁⁰ (algebra_map R₁ K a_inv) * I),
          nonzero,
          ext (λ x, iff.trans ⟨_, _⟩ mem_singleton_mul.symm)⟩,
  { intro hx,
    obtain ⟨x', hx'⟩ := ha x hx,
    rw algebra.smul_def at hx',
    refine ⟨algebra_map R₁ K x', (mem_coe_ideal _).mpr ⟨x', mem_singleton_mul.mpr _, rfl⟩, _⟩,
    { exact ⟨x, hx, hx'⟩ },
    { rw [hx', ← mul_assoc, inv_mul_cancel map_a_nonzero, one_mul] } },
  { rintros ⟨y, hy, rfl⟩,
    obtain ⟨x', hx', rfl⟩ := (mem_coe_ideal _).mp hy,
    obtain ⟨y', hy', hx'⟩ := mem_singleton_mul.mp hx',
    rw algebra.linear_map_apply at hx',
    rwa [hx', ←mul_assoc, inv_mul_cancel map_a_nonzero, one_mul] }
end

instance is_principal {R} [comm_ring R] [is_domain R] [is_principal_ideal_ring R]
  [algebra R K] [is_fraction_ring R K]
  (I : fractional_ideal R⁰ K) : (I : submodule R K).is_principal :=
begin
  obtain ⟨a, aI, -, ha⟩ := exists_eq_span_singleton_mul I,
  use (algebra_map R K a)⁻¹ * algebra_map R K (generator aI),
  suffices : I = span_singleton R⁰ ((algebra_map R K a)⁻¹ * algebra_map R K (generator aI)),
  { rw span_singleton at this, exact congr_arg subtype.val this },
  conv_lhs { rw [ha, ←span_singleton_generator aI] },
  rw [ideal.submodule_span_eq, coe_ideal_span_singleton (generator aI),
      span_singleton_mul_span_singleton]
end

include loc

lemma le_span_singleton_mul_iff {x : P} {I J : fractional_ideal S P} :
  I ≤ span_singleton S x * J ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI :=
show (∀ {zI} (hzI : zI ∈ I), zI ∈ span_singleton _ x * J) ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI,
by simp only [mem_singleton_mul, eq_comm]

lemma span_singleton_mul_le_iff {x : P} {I J : fractional_ideal S P} :
  span_singleton _ x * I ≤ J ↔ ∀ z ∈ I, x * z ∈ J :=
begin
  simp only [mul_le, mem_singleton_mul, mem_span_singleton],
  split,
  { intros h zI hzI,
    exact h x ⟨1, one_smul _ _⟩ zI hzI },
  { rintros h _ ⟨z, rfl⟩ zI hzI,
    rw [algebra.smul_mul_assoc],
    exact submodule.smul_mem J.1 _ (h zI hzI) },
end

lemma eq_span_singleton_mul {x : P} {I J : fractional_ideal S P} :
  I = span_singleton _ x * J ↔ (∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI) ∧ ∀ z ∈ J, x * z ∈ I :=
by simp only [le_antisymm_iff, le_span_singleton_mul_iff, span_singleton_mul_le_iff]

end principal_ideal_ring

variables {R₁ : Type*} [comm_ring R₁]
variables {K : Type*} [field K] [algebra R₁ K] [frac : is_fraction_ring R₁ K]

local attribute [instance] classical.prop_decidable

lemma is_noetherian_zero : is_noetherian R₁ (0 : fractional_ideal R₁⁰ K) :=
is_noetherian_submodule.mpr (λ I (hI : I ≤ (0 : fractional_ideal R₁⁰ K)),
  by { rw coe_zero at hI, rw le_bot_iff.mp hI, exact fg_bot })

lemma is_noetherian_iff {I : fractional_ideal R₁⁰ K} :
  is_noetherian R₁ I ↔ ∀ J ≤ I, (J : submodule R₁ K).fg :=
is_noetherian_submodule.trans ⟨λ h J hJ, h _ hJ, λ h J hJ, h ⟨J, is_fractional_of_le hJ⟩ hJ⟩

lemma is_noetherian_coe_ideal [_root_.is_noetherian_ring R₁] (I : ideal R₁) :
  is_noetherian R₁ (I : fractional_ideal R₁⁰ K) :=
begin
  rw is_noetherian_iff,
  intros J hJ,
  obtain ⟨J, rfl⟩ := le_one_iff_exists_coe_ideal.mp (le_trans hJ coe_ideal_le_one),
  exact (is_noetherian.noetherian J).map _,
end

include frac
variables [is_domain R₁]

lemma is_noetherian_span_singleton_inv_to_map_mul (x : R₁) {I : fractional_ideal R₁⁰ K}
  (hI : is_noetherian R₁ I) :
  is_noetherian R₁ (span_singleton R₁⁰ (algebra_map R₁ K x)⁻¹ * I : fractional_ideal R₁⁰ K) :=
begin
  by_cases hx : x = 0,
  { rw [hx, ring_hom.map_zero, _root_.inv_zero, span_singleton_zero, zero_mul],
    exact is_noetherian_zero },
  have h_gx : algebra_map R₁ K x ≠ 0,
  from mt ((injective_iff_map_eq_zero (algebra_map R₁ K)).mp
    (is_fraction_ring.injective _ _) x) hx,
  have h_spanx : span_singleton R₁⁰ (algebra_map R₁ K x) ≠ 0,
    from span_singleton_ne_zero_iff.mpr h_gx,

  rw is_noetherian_iff at ⊢ hI,
  intros J hJ,
  rw [← div_span_singleton, le_div_iff_mul_le h_spanx] at hJ,
  obtain ⟨s, hs⟩ := hI _ hJ,
  use s * {(algebra_map R₁ K x)⁻¹},
  rw [finset.coe_mul, finset.coe_singleton, ← span_mul_span, hs, ← coe_span_singleton R₁⁰,
      ← coe_mul, mul_assoc, span_singleton_mul_span_singleton, mul_inv_cancel h_gx,
      span_singleton_one, mul_one],
end

/-- Every fractional ideal of a noetherian integral domain is noetherian. -/
theorem is_noetherian [_root_.is_noetherian_ring R₁] (I : fractional_ideal R₁⁰ K) :
  is_noetherian R₁ I :=
begin
  obtain ⟨d, J, h_nzd, rfl⟩ := exists_eq_span_singleton_mul I,
  apply is_noetherian_span_singleton_inv_to_map_mul,
  apply is_noetherian_coe_ideal
end

section adjoin

include loc
omit frac

variables {R P} (S) (x : P) (hx : is_integral R x)

/-- `A[x]` is a fractional ideal for every integral `x`. -/
lemma is_fractional_adjoin_integral :
  is_fractional S (algebra.adjoin R ({x} : set P)).to_submodule :=
is_fractional_of_fg (fg_adjoin_singleton_of_integral x hx)

/-- `fractional_ideal.adjoin_integral (S : submonoid R) x hx` is `R[x]` as a fractional ideal,
where `hx` is a proof that `x : P` is integral over `R`. -/
@[simps]
def adjoin_integral : fractional_ideal S P :=
⟨_, is_fractional_adjoin_integral S x hx⟩

lemma mem_adjoin_integral_self :
  x ∈ adjoin_integral S x hx :=
algebra.subset_adjoin (set.mem_singleton x)

end adjoin

end fractional_ideal
