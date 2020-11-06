/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import ring_theory.localization
import ring_theory.principal_ideal_domain
import algebra.algebra.operations

/-!
# Fractional ideals

This file defines fractional ideals of an integral domain and proves basic facts about them.

## Main definitions
Let `S` be a submonoid of an integral domain `R`, `P` the localization of `R` at `S`, and `f` the
natural ring hom from `R` to `P`.
 * `is_fractional` defines which `R`-submodules of `P` are fractional ideals
 * `fractional_ideal f` is the type of fractional ideals in `P`
 * `has_coe (ideal R) (fractional_ideal f)` instance
 * `comm_semiring (fractional_ideal f)` instance:
   the typical ideal operations generalized to fractional ideals
 * `lattice (fractional_ideal f)` instance
 * `map` is the pushforward of a fractional ideal along an algebra morphism

Let `K` be the localization of `R` at `R \ {0}` and `g` the natural ring hom from `R` to `K`.
 * `has_div (fractional_ideal g)` instance:
   the ideal quotient `I / J` (typically written $I : J$, but a `:` operator cannot be defined)

## Main statements

  * `mul_left_mono` and `mul_right_mono` state that ideal multiplication is monotone
  * `right_inverse_eq` states that `1 / I` is the inverse of `I` if one exists

## Implementation notes

Fractional ideals are considered equal when they contain the same elements,
independent of the denominator `a : R` such that `a I ⊆ R`.
Thus, we define `fractional_ideal` to be the subtype of the predicate `is_fractional`,
instead of having `fractional_ideal` be a structure of which `a` is a field.

Most definitions in this file specialize operations from submodules to fractional ideals,
proving that the result of this operation is fractional if the input is fractional.
Exceptions to this rule are defining `(+) := (⊔)` and `⊥ := 0`,
in order to re-use their respective proof terms.
We can still use `simp` to show `I.1 + J.1 = (I + J).1` and `⊥.1 = 0.1`.

In `ring_theory.localization`, we define a copy of the localization map `f`'s codomain `P`
(`f.codomain`) so that the `R`-algebra instance on `P` can 'know' the map needed to induce
the `R`-algebra structure.

We don't assume that the localization is a field until we need it to define ideal quotients.
When this assumption is needed, we replace `S` with `non_zero_divisors R`, making the localization
a field.

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/

open localization_map

namespace ring

section defs

variables {R : Type*} [integral_domain R] {S : submonoid R} {P : Type*} [comm_ring P]
  (f : localization_map S P)

/-- A submodule `I` is a fractional ideal if `a I ⊆ R` for some `a ≠ 0`. -/
def is_fractional (I : submodule R f.codomain) :=
∃ a ∈ S, ∀ b ∈ I, f.is_integer (f.to_map a * b)

/-- The fractional ideals of a domain `R` are ideals of `R` divided by some `a ∈ R`.

  More precisely, let `P` be a localization of `R` at some submonoid `S`,
  then a fractional ideal `I ⊆ P` is an `R`-submodule of `P`,
  such that there is a no nzero `a : R` with `a I ⊆ R`.
-/
def fractional_ideal :=
{I : submodule R f.codomain // is_fractional f I}

end defs

namespace fractional_ideal

open set
open submodule

variables {R : Type*} [integral_domain R] {S : submonoid R} {P : Type*} [comm_ring P]
  {f : localization_map S P}

instance : has_coe (fractional_ideal f) (submodule R f.codomain) := ⟨λ I, I.val⟩

@[simp] lemma val_eq_coe (I : fractional_ideal f) : I.val = I := rfl

@[simp] lemma coe_mk (I : submodule R f.codomain) (hI : is_fractional f I) :
  (subtype.mk I hI : submodule R f.codomain) = I := rfl

instance : has_mem P (fractional_ideal f) := ⟨λ x I, x ∈ (I : submodule R f.codomain)⟩

/-- Fractional ideals are equal if their submodules are equal.

  Combined with `submodule.ext` this gives that fractional ideals are equal if
  they have the same elements.
-/
@[ext]
lemma ext {I J : fractional_ideal f} : (I : submodule R f.codomain) = J → I = J :=
subtype.ext_iff_val.mpr

lemma fractional_of_subset_one (I : submodule R f.codomain)
  (h : I ≤ (submodule.span R {1})) :
  is_fractional f I :=
begin
  use [1, S.one_mem],
  intros b hb,
  rw [f.to_map.map_one, one_mul],
  rw ←submodule.one_eq_span at h,
  obtain ⟨b', b'_mem, b'_eq_b⟩ := h hb,
  rw (show b = f.to_map b', from b'_eq_b.symm),
  exact set.mem_range_self b',
end

instance coe_to_fractional_ideal : has_coe (ideal R) (fractional_ideal f) :=
⟨ λ I, ⟨f.coe_submodule I, fractional_of_subset_one _ $ λ x ⟨y, hy, h⟩,
  submodule.mem_span_singleton.2 ⟨y, by rw ←h; exact mul_one _⟩⟩ ⟩

@[simp] lemma coe_coe_ideal (I : ideal R) :
  ((I : fractional_ideal f) : submodule R f.codomain) = f.coe_submodule I := rfl

@[simp] lemma mem_coe {x : f.codomain} {I : ideal R} :
  x ∈ (I : fractional_ideal f) ↔ ∃ (x' ∈ I), f.to_map x' = x :=
⟨ λ ⟨x', hx', hx⟩, ⟨x', hx', hx⟩,
  λ ⟨x', hx', hx⟩, ⟨x', hx', hx⟩ ⟩

instance : has_zero (fractional_ideal f) := ⟨(0 : ideal R)⟩

@[simp] lemma mem_zero_iff {x : P} : x ∈ (0 : fractional_ideal f) ↔ x = 0 :=
⟨ (λ ⟨x', x'_mem_zero, x'_eq_x⟩,
    have x'_eq_zero : x' = 0 := x'_mem_zero,
    by simp [x'_eq_x.symm, x'_eq_zero]),
  (λ hx, ⟨0, rfl, by simp [hx]⟩) ⟩

@[simp] lemma coe_zero : ↑(0 : fractional_ideal f) = (⊥ : submodule R f.codomain) :=
submodule.ext $ λ _, mem_zero_iff

lemma coe_ne_bot_iff_nonzero {I : fractional_ideal f} :
  ↑I ≠ (⊥ : submodule R f.codomain) ↔ I ≠ 0 :=
⟨ λ h h', h (by simp [h']),
  λ h h', h (ext (by simp [h'])) ⟩

instance : inhabited (fractional_ideal f) := ⟨0⟩

instance : has_one (fractional_ideal f) :=
⟨(1 : ideal R)⟩

lemma mem_one_iff {x : P} : x ∈ (1 : fractional_ideal f) ↔ ∃ x' : R, f.to_map x' = x :=
iff.intro (λ ⟨x', _, h⟩, ⟨x', h⟩) (λ ⟨x', h⟩, ⟨x', ⟨x', set.mem_univ _, rfl⟩, h⟩)

lemma coe_mem_one (x : R) : f.to_map x ∈ (1 : fractional_ideal f) :=
mem_one_iff.mpr ⟨x, rfl⟩

lemma one_mem_one : (1 : P) ∈ (1 : fractional_ideal f) :=
mem_one_iff.mpr ⟨1, f.to_map.map_one⟩

@[simp] lemma coe_one : ↑(1 : fractional_ideal f) = f.coe_submodule 1 := rfl

section lattice

/-!
### `lattice` section

Defines the order on fractional ideals as inclusion of their underlying sets,
and ports the lattice structure on submodules to fractional ideals.
-/

instance : partial_order (fractional_ideal f) :=
{ le := λ I J, I.1 ≤ J.1,
  le_refl := λ I, le_refl I.1,
  le_antisymm := λ ⟨I, hI⟩ ⟨J, hJ⟩ hIJ hJI, by { congr, exact le_antisymm hIJ hJI },
  le_trans := λ _ _ _ hIJ hJK, le_trans hIJ hJK }

lemma le_iff {I J : fractional_ideal f} : I ≤ J ↔ (∀ x ∈ I, x ∈ J) := iff.refl _

lemma zero_le (I : fractional_ideal f) : 0 ≤ I :=
begin
  intros x hx,
  convert submodule.zero_mem _,
  simpa using hx
end

instance order_bot : order_bot (fractional_ideal f) :=
{ bot := 0,
  bot_le := zero_le,
  ..fractional_ideal.partial_order }

@[simp] lemma bot_eq_zero : (⊥ : fractional_ideal f) = 0 :=
rfl

lemma eq_zero_iff {I : fractional_ideal f} : I = 0 ↔ (∀ x ∈ I, x = (0 : P)) :=
⟨ (λ h x hx, by simpa [h, mem_zero_iff] using hx),
  (λ h, le_bot_iff.mp (λ x hx, mem_zero_iff.mpr (h x hx))) ⟩

lemma fractional_sup (I J : fractional_ideal f) : is_fractional f (I.1 ⊔ J.1) :=
begin
  rcases I.2 with ⟨aI, haI, hI⟩,
  rcases J.2 with ⟨aJ, haJ, hJ⟩,
  use aI * aJ,
  use S.mul_mem haI haJ,
  intros b hb,
  rcases mem_sup.mp hb with
    ⟨bI, hbI, bJ, hbJ, hbIJ⟩,
  rw [←hbIJ, mul_add],
  apply is_integer_add,
  { rw [mul_comm aI, f.to_map.map_mul, mul_assoc],
    apply is_integer_smul (hI bI hbI), },
  { rw [f.to_map.map_mul, mul_assoc],
    apply is_integer_smul (hJ bJ hbJ) }
end

lemma fractional_inf (I J : fractional_ideal f) : is_fractional f (I.1 ⊓ J.1) :=
begin
  rcases I.2 with ⟨aI, haI, hI⟩,
  use aI,
  use haI,
  intros b hb,
  rcases mem_inf.mp hb with ⟨hbI, hbJ⟩,
  exact (hI b hbI)
end

instance lattice : lattice (fractional_ideal f) :=
{ inf := λ I J, ⟨I.1 ⊓ J.1, fractional_inf I J⟩,
  sup := λ I J, ⟨I.1 ⊔ J.1, fractional_sup I J⟩,
  inf_le_left := λ I J, show I.1 ⊓ J.1 ≤ I.1, from inf_le_left,
  inf_le_right := λ I J, show I.1 ⊓ J.1 ≤ J.1, from inf_le_right,
  le_inf := λ I J K hIJ hIK, show I.1 ≤ (J.1 ⊓ K.1), from le_inf hIJ hIK,
  le_sup_left := λ I J, show I.1 ≤ I.1 ⊔ J.1, from le_sup_left,
  le_sup_right := λ I J, show J.1 ≤ I.1 ⊔ J.1, from le_sup_right,
  sup_le := λ I J K hIK hJK, show (I.1 ⊔ J.1) ≤ K.1, from sup_le hIK hJK,
  ..fractional_ideal.partial_order }

instance : semilattice_sup_bot (fractional_ideal f) :=
{ ..fractional_ideal.order_bot, ..fractional_ideal.lattice }

end lattice

section semiring

instance : has_add (fractional_ideal f) := ⟨(⊔)⟩

@[simp]
lemma sup_eq_add (I J : fractional_ideal f) : I ⊔ J = I + J := rfl

@[simp]
lemma coe_add (I J : fractional_ideal f) : (↑(I + J) : submodule R f.codomain) = I + J := rfl

lemma fractional_mul (I J : fractional_ideal f) : is_fractional f (I.1 * J.1) :=
begin
  rcases I with ⟨I, aI, haI, hI⟩,
  rcases J with ⟨I, aJ, haJ, hJ⟩,
  use aI * aJ,
  use S.mul_mem haI haJ,
  intros b hb,
  apply submodule.mul_induction_on hb,
  { intros m hm n hn,
    obtain ⟨n', hn'⟩ := hJ n hn,
    rw [f.to_map.map_mul, mul_comm m, ←mul_assoc, mul_assoc _ _ n],
    erw ←hn', rw mul_assoc,
    apply hI,
    exact submodule.smul_mem _ _ hm },
  { rw [mul_zero],
    exact ⟨0, f.to_map.map_zero⟩ },
  { intros x y hx hy,
    rw [mul_add],
    apply is_integer_add hx hy },
  { intros r x hx,
    show f.is_integer (_ * (f.to_map r * x)),
    rw [←mul_assoc, ←f.to_map.map_mul, mul_comm _ r, f.to_map.map_mul, mul_assoc],
    apply is_integer_smul hx },
end

instance : has_mul (fractional_ideal f) := ⟨λ I J, ⟨I.1 * J.1, fractional_mul I J⟩⟩

@[simp]
lemma coe_mul (I J : fractional_ideal f) : (↑(I * J) : submodule R f.codomain) = I * J := rfl

lemma mul_left_mono (I : fractional_ideal f) : monotone ((*) I) :=
λ J J' h, mul_le.mpr (λ x hx y hy, mul_mem_mul hx (h hy))

lemma mul_right_mono (I : fractional_ideal f) : monotone (λ J, J * I) :=
λ J J' h, mul_le.mpr (λ x hx y hy, mul_mem_mul (h hx) hy)

instance add_comm_monoid : add_comm_monoid (fractional_ideal f) :=
{ add_assoc := λ I J K, sup_assoc,
  add_comm := λ I J, sup_comm,
  add_zero := λ I, sup_bot_eq,
  zero_add := λ I, bot_sup_eq,
  ..fractional_ideal.has_zero,
  ..fractional_ideal.has_add }

instance comm_monoid : comm_monoid (fractional_ideal f) :=
{ mul_assoc := λ I J K, ext (submodule.mul_assoc _ _ _),
  mul_comm := λ I J, ext (submodule.mul_comm _ _),
  mul_one := λ I, begin
    ext,
    split; intro h,
    { apply mul_le.mpr _ h,
      rintros x hx y ⟨y', y'_mem_R, y'_eq_y⟩,
      rw [←y'_eq_y, mul_comm],
      exact submodule.smul_mem _ _ hx },
    { have : x * 1 ∈ (I * 1) := mul_mem_mul h one_mem_one,
      rwa [mul_one] at this }
  end,
  one_mul := λ I, begin
    ext,
    split; intro h,
    { apply mul_le.mpr _ h,
      rintros x ⟨x', x'_mem_R, x'_eq_x⟩ y hy,
      rw ←x'_eq_x,
      exact submodule.smul_mem _ _ hy },
    { have : 1 * x ∈ (1 * I) := mul_mem_mul one_mem_one h,
      rwa [one_mul] at this }
  end,
  ..fractional_ideal.has_mul,
  ..fractional_ideal.has_one }

instance comm_semiring : comm_semiring (fractional_ideal f) :=
{ mul_zero := λ I, eq_zero_iff.mpr (λ x hx, submodule.mul_induction_on hx
    (λ x hx y hy, by simp [mem_zero_iff.mp hy])
    rfl
    (λ x y hx hy, by simp [hx, hy])
    (λ r x hx, by simp [hx])),
  zero_mul := λ I, eq_zero_iff.mpr (λ x hx, submodule.mul_induction_on hx
    (λ x hx y hy, by simp [mem_zero_iff.mp hx])
    rfl
    (λ x y hx hy, by simp [hx, hy])
    (λ r x hx, by simp [hx])),
  left_distrib := λ I J K, ext (mul_add _ _ _),
  right_distrib := λ I J K, ext (add_mul _ _ _),
  ..fractional_ideal.add_comm_monoid,
  ..fractional_ideal.comm_monoid }

variables {P' : Type*} [comm_ring P'] {f' : localization_map S P'}
variables {P'' : Type*} [comm_ring P''] {f'' : localization_map S P''}

lemma fractional_map (g : f.codomain →ₐ[R] f'.codomain) (I : fractional_ideal f) :
  is_fractional f' (submodule.map g.to_linear_map I.1) :=
begin
  rcases I with ⟨I, a, a_nonzero, hI⟩,
  use [a, a_nonzero],
  intros b hb,
  obtain ⟨b', b'_mem, hb'⟩ := submodule.mem_map.mp hb,
  obtain ⟨x, hx⟩ := hI b' b'_mem,
  use x,
  erw [←g.commutes, hx, g.map_smul, hb'],
  refl
end

/-- `I.map g` is the pushforward of the fractional ideal `I` along the algebra morphism `g` -/
def map (g : f.codomain →ₐ[R] f'.codomain) :
  fractional_ideal f → fractional_ideal f' :=
λ I, ⟨submodule.map g.to_linear_map I.1, fractional_map g I⟩

@[simp] lemma coe_map (g : f.codomain →ₐ[R] f'.codomain) (I : fractional_ideal f) :
  ↑(map g I) = submodule.map g.to_linear_map I := rfl

@[simp] lemma mem_map {I : fractional_ideal f} {g : f.codomain →ₐ[R] f'.codomain}
  {y : f'.codomain} : y ∈ I.map g ↔ ∃ x, x ∈ I ∧ g x = y :=
submodule.mem_map

variables (I J : fractional_ideal f) (g : f.codomain →ₐ[R] f'.codomain)

@[simp] lemma map_id : I.map (alg_hom.id _ _) = I :=
ext (submodule.map_id I.1)

@[simp] lemma map_comp (g' : f'.codomain →ₐ[R] f''.codomain) :
  I.map (g'.comp g) = (I.map g).map g' :=
ext (submodule.map_comp g.to_linear_map g'.to_linear_map I.1)

@[simp] lemma map_coe_ideal (I : ideal R) :
  (I : fractional_ideal f).map g = I :=
begin
  ext x,
  simp only [coe_coe_ideal, mem_coe_submodule],
  split,
  { rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩,
    exact ⟨y, hy, (g.commutes y).symm⟩ },
  { rintro ⟨y, hy, rfl⟩,
    exact ⟨_, ⟨y, hy, rfl⟩, g.commutes y⟩ },
end

@[simp] lemma map_one :
(1 : fractional_ideal f).map g = 1 :=
map_coe_ideal g 1

@[simp] lemma map_zero :
  (0 : fractional_ideal f).map g = 0 :=
map_coe_ideal g 0

@[simp] lemma map_add : (I + J).map g = I.map g + J.map g :=
ext (submodule.map_sup _ _ _)

@[simp] lemma map_mul : (I * J).map g = I.map g * J.map g :=
ext (submodule.map_mul _ _ _)

@[simp] lemma map_map_symm (g : f.codomain ≃ₐ[R] f'.codomain) :
  (I.map (g : f.codomain →ₐ[R] f'.codomain)).map (g.symm : f'.codomain →ₐ[R] f.codomain) = I :=
by rw [←map_comp, g.symm_comp, map_id]

@[simp] lemma map_symm_map (I : fractional_ideal f') (g : f.codomain ≃ₐ[R] f'.codomain) :
  (I.map (g.symm : f'.codomain →ₐ[R] f.codomain)).map (g : f.codomain →ₐ[R] f'.codomain) = I :=
by rw [←map_comp, g.comp_symm, map_id]

/-- If `g` is an equivalence, `map g` is an isomorphism -/
def map_equiv (g : f.codomain ≃ₐ[R] f'.codomain) :
  fractional_ideal f ≃+* fractional_ideal f' :=
{ to_fun := map g,
  inv_fun := map g.symm,
  map_add' := λ I J, map_add I J _,
  map_mul' := λ I J, map_mul I J _,
  left_inv := λ I, by { rw [←map_comp, alg_equiv.symm_comp, map_id] },
  right_inv := λ I, by { rw [←map_comp, alg_equiv.comp_symm, map_id] } }

@[simp] lemma map_equiv_apply (g : f.codomain ≃ₐ[R] f'.codomain) :
  map_equiv g I = map ↑g I := rfl

@[simp] lemma map_equiv_refl :
  map_equiv alg_equiv.refl = ring_equiv.refl (fractional_ideal f) :=
ring_equiv.ext (λ x, by simp)

lemma fractional_of_fg {I : submodule R f.codomain} (hI : I.fg) :
  is_fractional f I :=
begin
  cases hI with T hT,
  rcases localization_map.exist_integer_multiples_of_finset f T with ⟨⟨s, hs1⟩, hs⟩,
  use [s, hs1],
  intros b hb,
  rw ←hT at hb,
  apply span_induction hb,
  exact hs,
  {
    simp,
    use 0,
    simp,
  },
  {
    rintros x y hx hy,
    rw mul_add,
    apply is_integer_add hx,
    assumption,
  },
  {
    rintros a x hx,
    rw algebra.mul_smul_comm,
    apply is_integer_smul hx,
  },
end

/-- `canonical_equiv f f'` is the canonical equivalence between the fractional
ideals in `f.codomain` and in `f'.codomain` -/
noncomputable def canonical_equiv (f f' : localization_map S P) :
  fractional_ideal f ≃+* fractional_ideal f' :=
map_equiv
  { commutes' := λ r, ring_equiv_of_ring_equiv_eq _ _ _,
    ..ring_equiv_of_ring_equiv f f' (ring_equiv.refl R)
      (by rw [ring_equiv.to_monoid_hom_refl, submonoid.map_id]) }

end semiring

section fraction_map

/-!
### `fraction_map` section

This section concerns fractional ideals in the field of fractions,
i.e. the type `fractional_ideal g` when `g` is a `fraction_map R K`.
-/

variables {K K' : Type*} [field K] [field K'] {g : fraction_map R K} {g' : fraction_map R K'}
variables {I J : fractional_ideal g} (h : g.codomain →ₐ[R] g'.codomain)

/-- Nonzero fractional ideals contain a nonzero integer. -/
lemma exists_ne_zero_mem_is_integer (hI : I ≠ 0) :
  ∃ x ≠ (0 : R), g.to_map x ∈ I :=
begin
  obtain ⟨y, y_mem, y_not_mem⟩ := submodule.exists_of_lt (bot_lt_iff_ne_bot.mpr hI),
  have y_ne_zero : y ≠ 0 := by simpa using y_not_mem,
  obtain ⟨z, ⟨x, hx⟩⟩ := g.exists_integer_multiple y,
  refine ⟨x, _, _⟩,
  { rw [ne.def, ← g.to_map_eq_zero_iff, hx],
    exact mul_ne_zero (g.to_map_ne_zero_of_mem_non_zero_divisors _) y_ne_zero },
  { rw hx,
    exact smul_mem _ _ y_mem }
end

lemma map_ne_zero (hI : I ≠ 0) : I.map h ≠ 0 :=
begin
  obtain ⟨x, x_ne_zero, hx⟩ := exists_ne_zero_mem_is_integer hI,
  contrapose! x_ne_zero with map_eq_zero,
  refine g'.to_map_eq_zero_iff.mp (eq_zero_iff.mp map_eq_zero _ (mem_map.mpr _)),
  exact ⟨g.to_map x, hx, h.commutes x⟩,
end

@[simp] lemma map_eq_zero_iff : I.map h = 0 ↔ I = 0 :=
⟨imp_of_not_imp_not _ _ (map_ne_zero _),
 λ hI, hI.symm ▸ map_zero h⟩

end fraction_map

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

variables {K : Type*} [field K] {g : fraction_map R K}

instance : nontrivial (fractional_ideal g) :=
⟨⟨0, 1, λ h,
  have this : (1 : K) ∈ (0 : fractional_ideal g) :=
    by rw ←g.to_map.map_one; convert coe_mem_one _,
  one_ne_zero (mem_zero_iff.mp this) ⟩⟩

lemma fractional_div_of_nonzero {I J : fractional_ideal g} (h : J ≠ 0) :
  is_fractional g (I.1 / J.1) :=
begin
  rcases I with ⟨I, aI, haI, hI⟩,
  rcases J with ⟨J, aJ, haJ, hJ⟩,
  obtain ⟨y, mem_J, not_mem_zero⟩ := exists_of_lt (bot_lt_iff_ne_bot.mpr h),
  obtain ⟨y', hy'⟩ := hJ y mem_J,
  use (aI * y'),
  split,
  { apply (non_zero_divisors R).mul_mem haI (mem_non_zero_divisors_iff_ne_zero.mpr _),
    intro y'_eq_zero,
    have : g.to_map aJ * y = 0 := by rw [←hy', y'_eq_zero, g.to_map.map_zero],
    obtain aJ_zero | y_zero := mul_eq_zero.mp this,
    { have : aJ = 0 := g.to_map.injective_iff.1 g.injective _ aJ_zero,
      have : aJ ≠ 0 := mem_non_zero_divisors_iff_ne_zero.mp haJ,
      contradiction },
    { exact not_mem_zero (mem_zero_iff.mpr y_zero) } },
  intros b hb,
  rw [g.to_map.map_mul, mul_assoc, mul_comm _ b, hy'],
  exact hI _ (hb _ (submodule.smul_mem _ aJ mem_J)),
end

noncomputable instance fractional_ideal_has_div :
  has_div (fractional_ideal g) :=
⟨ λ I J, if h : J = 0 then 0 else ⟨I.1 / J.1, fractional_div_of_nonzero h⟩ ⟩

noncomputable instance : has_inv (fractional_ideal g) := ⟨λ I, 1 / I⟩

lemma inv_eq {I : fractional_ideal g} : I⁻¹ = 1 / I := rfl

@[simp] lemma div_zero {I : fractional_ideal g} :
  I / 0 = 0 :=
dif_pos rfl

lemma div_nonzero {I J : fractional_ideal g} (h : J ≠ 0) :
  (I / J) = ⟨I.1 / J.1, fractional_div_of_nonzero h⟩ :=
dif_neg h

lemma inv_zero : (0 : fractional_ideal g)⁻¹ = 0 :=
div_zero

lemma inv_nonzero {I : fractional_ideal g} (h : I ≠ 0) :
  I⁻¹ = ⟨(1 : fractional_ideal g) / I, fractional_div_of_nonzero h⟩ :=
div_nonzero h

lemma coe_inv_of_nonzero {I : fractional_ideal g} (h : I ≠ 0) :
  (↑(I⁻¹) : submodule R g.codomain) = g.coe_submodule 1 / I :=
by { rw inv_nonzero h, refl }

@[simp] lemma div_one {I : fractional_ideal g} : I / 1 = I :=
begin
  rw [div_nonzero (@one_ne_zero (fractional_ideal g) _ _)],
  ext,
  split; intro h,
  { convert mem_div_iff_forall_mul_mem.mp h 1
      (g.to_map.map_one ▸ coe_mem_one 1), simp },
  { apply mem_div_iff_forall_mul_mem.mpr,
    rintros y ⟨y', _, y_eq_y'⟩,
    rw [mul_comm],
    convert submodule.smul_mem _ y' h,
    rw ←y_eq_y',
    refl }
end

lemma ne_zero_of_mul_eq_one (I J : fractional_ideal g) (h : I * J = 1) : I ≠ 0 :=
λ hI, @zero_ne_one (fractional_ideal g) _ _ (by { convert h, simp [hI], })

/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq (I J : fractional_ideal g) (h : I * J = 1) :
  J = I⁻¹ :=
begin
  have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J h,
  suffices h' : I * (1 / I) = 1,
  { exact (congr_arg units.inv $
      @units.ext _ _ (units.mk_of_mul_eq_one _ _ h) (units.mk_of_mul_eq_one _ _ h') rfl) },
  rw [div_nonzero hI],
  apply le_antisymm,
  { apply submodule.mul_le.mpr _,
    intros x hx y hy,
    rw [mul_comm],
    exact mem_div_iff_forall_mul_mem.mp hy x hx },
  rw [←h],
  apply mul_left_mono I,
  apply submodule.le_div_iff.mpr _,
  intros y hy x hx,
  rw [mul_comm],
  exact mul_mem_mul hx hy
end

theorem mul_inv_cancel_iff {I : fractional_ideal g} :
  I * I⁻¹ = 1 ↔ ∃ J, I * J = 1 :=
⟨λ h, ⟨I⁻¹, h⟩, λ ⟨J, hJ⟩, by rwa [←right_inverse_eq I J hJ]⟩

variables {K' : Type*} [field K'] {g' : fraction_map R K'}

@[simp] lemma map_div (I J : fractional_ideal g) (h : g.codomain ≃ₐ[R] g'.codomain) :
  (I / J).map (h : g.codomain →ₐ[R] g'.codomain) = I.map h / J.map h :=
begin
  by_cases H : J = 0,
  { rw [H, div_zero, map_zero, div_zero] },
  { ext x,
    simp [div_nonzero H, div_nonzero (map_ne_zero _ H), submodule.map_div] }
end

@[simp] lemma map_inv (I : fractional_ideal g) (h : g.codomain ≃ₐ[R] g'.codomain) :
  (I⁻¹).map (h : g.codomain →ₐ[R] g'.codomain) = (I.map h)⁻¹ :=
by rw [inv_eq, map_div, map_one, inv_eq]

end quotient

section principal_ideal_ring

variables {K : Type*} [field K] {g : fraction_map R K}

open_locale classical

open submodule submodule.is_principal

lemma span_fractional_iff {s : set f.codomain} :
  is_fractional f (span R s) ↔ ∃ a ∈ S, ∀ (b : P), b ∈ s → f.is_integer (f.to_map a * b) :=
⟨ λ ⟨a, a_mem, h⟩, ⟨a, a_mem, λ b hb, h b (subset_span hb)⟩,
  λ ⟨a, a_mem, h⟩, ⟨a, a_mem, λ b hb, span_induction hb
    h
    (is_integer_smul ⟨0, f.to_map.map_zero⟩)
    (λ x y hx hy, by { rw mul_add, exact is_integer_add hx hy })
    (λ s x hx, by { rw algebra.mul_smul_comm, exact is_integer_smul hx }) ⟩ ⟩

lemma span_singleton_fractional (x : f.codomain) : is_fractional f (span R {x}) :=
let ⟨a, ha⟩ := f.exists_integer_multiple x in
span_fractional_iff.mpr ⟨ a.1, a.2, λ x hx, (mem_singleton_iff.mp hx).symm ▸ ha⟩

/-- `span_singleton x` is the fractional ideal generated by `x` if `0 ∉ S` -/
def span_singleton (x : f.codomain) : fractional_ideal f :=
⟨span R {x}, span_singleton_fractional x⟩

@[simp] lemma coe_span_singleton (x : f.codomain) :
  (span_singleton x : submodule R f.codomain) = span R {x} := rfl

lemma eq_span_singleton_of_principal (I : fractional_ideal f) [is_principal I.1] :
  I = span_singleton (generator I.1) :=
ext (span_singleton_generator I.1).symm

lemma is_principal_iff (I : fractional_ideal f) :
  is_principal I.1 ↔ ∃ x, I = span_singleton x :=
⟨ λ h, ⟨@generator _ _ _ _ _ I.1 h, @eq_span_singleton_of_principal _ _ _ _ _ _ I h⟩,
  λ ⟨x, hx⟩, { principal := ⟨x, trans (congr_arg _ hx) (coe_span_singleton x)⟩ } ⟩

@[simp] lemma span_singleton_zero : span_singleton (0 : f.codomain) = 0 :=
by { ext, simp [submodule.mem_span_singleton, eq_comm] }

lemma span_singleton_eq_zero_iff {y : f.codomain} : span_singleton y = 0 ↔ y = 0 :=
⟨ λ h, span_eq_bot.mp (by simpa using congr_arg subtype.val h : span R {y} = ⊥) y (mem_singleton y),
  λ h, by simp [h] ⟩

@[simp] lemma span_singleton_one : span_singleton (1 : f.codomain) = 1 :=
begin
  ext,
  refine mem_span_singleton.trans ((exists_congr _).trans mem_one_iff.symm),
  intro x',
  refine eq.congr (mul_one _) rfl,
end

@[simp]
lemma span_singleton_mul_span_singleton (x y : f.codomain) :
  span_singleton x * span_singleton y = span_singleton (x * y) :=
begin
  ext,
  simp_rw [coe_mul, coe_span_singleton, span_mul_span, singleton.is_mul_hom.map_mul]
end

@[simp]
lemma coe_ideal_span_singleton (x : R) :
  (↑(span R {x} : ideal R) : fractional_ideal f) = span_singleton (f.to_map x) :=
begin
  ext y,
  refine mem_coe.trans (iff.trans _ mem_span_singleton.symm),
  split,
  { rintros ⟨y', hy', rfl⟩,
    obtain ⟨x', rfl⟩ := mem_span_singleton.mp hy',
    use x',
    rw [smul_eq_mul, f.to_map.map_mul],
    refl },
  { rintros ⟨y', rfl⟩,
    exact ⟨y' * x, mem_span_singleton.mpr ⟨y', rfl⟩, f.to_map.map_mul _ _⟩ }
end

lemma mem_singleton_mul {x y : f.codomain} {I : fractional_ideal f} :
  y ∈ span_singleton x * I ↔ ∃ y' ∈ I, y = x * y' :=
begin
  split,
  { intro h,
    apply submodule.mul_induction_on h,
    { intros x' hx' y' hy',
      obtain ⟨a, ha⟩ := mem_span_singleton.mp hx',
      use [a • y', I.1.smul_mem a hy'],
      rw [←ha, algebra.mul_smul_comm, algebra.smul_mul_assoc] },
    { exact ⟨0, I.1.zero_mem, (mul_zero x).symm⟩ },
    { rintros _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩,
      exact ⟨y + y', I.1.add_mem hy hy', (mul_add _ _ _).symm⟩ },
    { rintros r _ ⟨y', hy', rfl⟩,
      exact ⟨r • y', I.1.smul_mem r hy', (algebra.mul_smul_comm _ _ _).symm ⟩ } },
  { rintros ⟨y', hy', rfl⟩,
    exact mul_mem_mul (mem_span_singleton.mpr ⟨1, one_smul _ _⟩) hy' }
end

lemma mul_generator_self_inv (I : fractional_ideal g)
  [submodule.is_principal I.1] (h : I ≠ 0) :
  I * span_singleton (generator I.1)⁻¹ = 1 :=
begin
  -- Rewrite only the `I` that appears alone.
  conv_lhs { congr, rw eq_span_singleton_of_principal I },
  rw [span_singleton_mul_span_singleton, mul_inv_cancel, span_singleton_one],
  intro generator_I_eq_zero,
  apply h,
  rw [eq_span_singleton_of_principal I, generator_I_eq_zero, span_singleton_zero]
end

lemma exists_eq_span_singleton_mul (I : fractional_ideal g) :
  ∃ (a : K) (aI : ideal R), I = span_singleton a * aI :=
begin
  obtain ⟨a_inv, nonzero, ha⟩ := I.2,
  have nonzero := mem_non_zero_divisors_iff_ne_zero.mp nonzero,
  have map_a_nonzero := mt g.to_map_eq_zero_iff.mp nonzero,
  use (g.to_map a_inv)⁻¹,
  use (span_singleton (g.to_map a_inv) * I).1.comap g.lin_coe,
  ext,
  refine iff.trans _ mem_singleton_mul.symm,
  split,
  { intro hx,
    obtain ⟨x', hx'⟩ := ha x hx,
    refine ⟨g.to_map x', mem_coe.mpr ⟨x', (mem_singleton_mul.mpr ⟨x, hx, hx'⟩), rfl⟩, _⟩,
    erw [hx', ←mul_assoc, inv_mul_cancel map_a_nonzero, one_mul] },
  { rintros ⟨y, hy, rfl⟩,
    obtain ⟨x', hx', rfl⟩ := mem_coe.mp hy,
    obtain ⟨y', hy', hx'⟩ := mem_singleton_mul.mp hx',
    rw lin_coe_apply at hx',
    erw [hx', ←mul_assoc, inv_mul_cancel map_a_nonzero, one_mul],
    exact hy' }
end

instance is_principal {R} [integral_domain R] [is_principal_ideal_ring R] {f : fraction_map R K}
  (I : fractional_ideal f) : (I : submodule R f.codomain).is_principal :=
⟨ begin
  obtain ⟨a, aI, ha⟩ := exists_eq_span_singleton_mul I,
  have := a * f.to_map (generator aI),
  use a * f.to_map (generator aI),
  suffices : I = span_singleton (a * f.to_map (generator aI)),
  { exact congr_arg subtype.val this },
  conv_lhs { rw [ha, ←span_singleton_generator aI] },
  rw [coe_ideal_span_singleton (generator aI), span_singleton_mul_span_singleton]
end ⟩

end principal_ideal_ring

end fractional_ideal

end ring

open_locale classical -- to deal with union of two finsets!

universes u v

variables (B : Type u) [semiring B]
variables (M : Type v) [add_comm_monoid M] [semimodule B M]

open submodule

lemma submodule.mem_span_finite_of_mem_span (S : set M) (x : M) (hx : x ∈ span B S) :
  ∃ T : set M, T ⊆ S ∧ T.finite ∧ x ∈ span B T :=
begin
  apply span_induction hx;
  clear hx x,
  {
    rintros x hx,
    use {x},
    split,
    {
      rw set.singleton_subset_iff,
      assumption,
    },
    simp,
    apply submodule.mem_span_singleton_self,
  },
  {
    use ⊥,
    simp,
  },
  {
    rintros x y hx hy,
    rcases hx with ⟨X, hX, hx⟩,
    rcases hy with ⟨Y, hY, hy⟩,
    use X ∪ Y,
    split,
    {
      have hS := set.union_subset_union hX hY,
      rw set.union_self S at hS,
      assumption,
    },
    split,
    {
      refine set.finite.union _ _,
      cases hx,
      assumption,
      cases hy,
      assumption,
    },
    rw span_union X Y,
    rw mem_sup,
    use x,
    split,
    cases hx,
    assumption,
    use y,
    split,
    cases hy,
    assumption,
    refl,
  },
  rintros a x h,
  rcases h with ⟨T, hT, h1, h2⟩,
  use T,
  split,
  assumption,
  split,
  assumption,
  refine smul_mem _ _ h2,
end

lemma submodule.mem_span_mul_finite_of_mem_span_mul [comm_semiring B] [semiring M] [algebra B M] (S : set M) (S' : set M) (x : M) (hx : x ∈ span B S * span B S') :
  ∃ T : set M, T ⊆ S ∧ T.finite ∧ ∃ T' : set M, T' ⊆ S' ∧ T'.finite ∧ x ∈ span B T * span B T' :=
begin
  sorry,
end
