/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bryan Gin-ge Chen
-/
import order.heyting.basic

/-!
# (Generalized) Boolean algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A Boolean algebra is a bounded distributive lattice with a complement operator. Boolean algebras
generalize the (classical) logic of propositions and the lattice of subsets of a set.

Generalized Boolean algebras may be less familiar, but they are essentially Boolean algebras which
do not necessarily have a top element (`⊤`) (and hence not all elements may have complements). One
example in mathlib is `finset α`, the type of all finite subsets of an arbitrary
(not-necessarily-finite) type `α`.

`generalized_boolean_algebra α` is defined to be a distributive lattice with bottom (`⊥`) admitting
a *relative* complement operator, written using "set difference" notation as `x \ y` (`sdiff x y`).
For convenience, the `boolean_algebra` type class is defined to extend `generalized_boolean_algebra`
so that it is also bundled with a `\` operator.

(A terminological point: `x \ y` is the complement of `y` relative to the interval `[⊥, x]`. We do
not yet have relative complements for arbitrary intervals, as we do not even have lattice
intervals.)

## Main declarations

* `generalized_boolean_algebra`: a type class for generalized Boolean algebras
* `boolean_algebra`: a type class for Boolean algebras.
* `Prop.boolean_algebra`: the Boolean algebra instance on `Prop`

## Implementation notes

The `sup_inf_sdiff` and `inf_inf_sdiff` axioms for the relative complement operator in
`generalized_boolean_algebra` are taken from
[Wikipedia](https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations).

[Stone's paper introducing generalized Boolean algebras][Stone1935] does not define a relative
complement operator `a \ b` for all `a`, `b`. Instead, the postulates there amount to an assumption
that for all `a, b : α` where `a ≤ b`, the equations `x ⊔ a = b` and `x ⊓ a = ⊥` have a solution
`x`. `disjoint.sdiff_unique` proves that this `x` is in fact `b \ a`.

## References

* <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations>
* [*Postulates for Boolean Algebras and Generalized Boolean Algebras*, M.H. Stone][Stone1935]
* [*Lattice Theory: Foundation*, George Grätzer][Gratzer2011]

## Tags

generalized Boolean algebras, Boolean algebras, lattices, sdiff, compl
-/
set_option old_structure_cmd true

open function order_dual

universes u v
variables {α : Type u} {β : Type*} {w x y z : α}

/-!
### Generalized Boolean algebras

Some of the lemmas in this section are from:

* [*Lattice Theory: Foundation*, George Grätzer][Gratzer2011]
* <https://ncatlab.org/nlab/show/relative+complement>
* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

-/

/-- A generalized Boolean algebra is a distributive lattice with `⊥` and a relative complement
operation `\` (called `sdiff`, after "set difference") satisfying `(a ⊓ b) ⊔ (a \ b) = a` and
`(a ⊓ b) ⊓ (a \ b) = ⊥`, i.e. `a \ b` is the complement of `b` in `a`.

This is a generalization of Boolean algebras which applies to `finset α` for arbitrary
(not-necessarily-`fintype`) `α`. -/
class generalized_boolean_algebra (α : Type u) extends distrib_lattice α, has_sdiff α, has_bot α :=
(sup_inf_sdiff : ∀a b:α, (a ⊓ b) ⊔ (a \ b) = a)
(inf_inf_sdiff : ∀a b:α, (a ⊓ b) ⊓ (a \ b) = ⊥)

-- We might want a `is_compl_of` predicate (for relative complements) generalizing `is_compl`,
-- however we'd need another type class for lattices with bot, and all the API for that.

section generalized_boolean_algebra
variables [generalized_boolean_algebra α]

@[simp] theorem sup_inf_sdiff (x y : α) : (x ⊓ y) ⊔ (x \ y) = x :=
generalized_boolean_algebra.sup_inf_sdiff _ _
@[simp] theorem inf_inf_sdiff (x y : α) : (x ⊓ y) ⊓ (x \ y) = ⊥ :=
generalized_boolean_algebra.inf_inf_sdiff _ _

@[simp] theorem sup_sdiff_inf (x y : α) : (x \ y) ⊔ (x ⊓ y) = x :=
by rw [sup_comm, sup_inf_sdiff]
@[simp] theorem inf_sdiff_inf (x y : α) : (x \ y) ⊓ (x ⊓ y) = ⊥ :=
by rw [inf_comm, inf_inf_sdiff]

@[priority 100]  -- see Note [lower instance priority]
instance generalized_boolean_algebra.to_order_bot : order_bot α :=
{ bot_le := λ a, by { rw [←inf_inf_sdiff a a, inf_assoc], exact inf_le_left },
  ..generalized_boolean_algebra.to_has_bot α }

theorem disjoint_inf_sdiff : disjoint (x ⊓ y) (x \ y) :=
disjoint_iff_inf_le.mpr (inf_inf_sdiff x y).le

-- TODO: in distributive lattices, relative complements are unique when they exist
theorem sdiff_unique (s : (x ⊓ y) ⊔ z = x) (i : (x ⊓ y) ⊓ z = ⊥) : x \ y = z :=
begin
  conv_rhs at s { rw [←sup_inf_sdiff x y, sup_comm] },
  rw sup_comm at s,
  conv_rhs at i { rw [←inf_inf_sdiff x y, inf_comm] },
  rw inf_comm at i,
  exact (eq_of_inf_eq_sup_eq i s).symm,
end

-- Use `sdiff_le`
private lemma sdiff_le' : x \ y ≤ x :=
calc x \ y ≤ (x ⊓ y) ⊔ (x \ y) : le_sup_right
       ... = x                 : sup_inf_sdiff x y

-- Use `sdiff_sup_self`
private lemma sdiff_sup_self' : y \ x ⊔ x = y ⊔ x :=
calc y \ x ⊔ x = y \ x ⊔ (x ⊔ x ⊓ y) : by rw sup_inf_self
           ... = (y ⊓ x) ⊔ y \ x ⊔ x : by ac_refl
           ... = y ⊔ x                   : by rw sup_inf_sdiff


@[simp] lemma sdiff_inf_sdiff : x \ y ⊓ (y \ x) = ⊥ :=
eq.symm $
  calc ⊥ = (x ⊓ y) ⊓ (x \ y)                           : by rw inf_inf_sdiff
     ... = (x ⊓ (y ⊓ x ⊔ y \ x)) ⊓ (x \ y)             : by rw sup_inf_sdiff
     ... = (x ⊓ (y ⊓ x) ⊔ x ⊓ (y \ x)) ⊓ (x \ y)       : by rw inf_sup_left
     ... = (y ⊓ (x ⊓ x) ⊔ x ⊓ (y \ x)) ⊓ (x \ y)       : by ac_refl
     ... = (y ⊓ x ⊔ x ⊓ (y \ x)) ⊓ (x \ y)             : by rw inf_idem
     ... = (x ⊓ y ⊓ (x \ y)) ⊔ (x ⊓ (y \ x) ⊓ (x \ y)) : by rw [inf_sup_right, @inf_comm _ _ x y]
     ... = x ⊓ (y \ x) ⊓ (x \ y)                       : by rw [inf_inf_sdiff, bot_sup_eq]
     ... = x ⊓ (x \ y) ⊓ (y \ x)                       : by ac_refl
     ... = (x \ y) ⊓ (y \ x)                           : by rw inf_of_le_right sdiff_le'

lemma disjoint_sdiff_sdiff : disjoint (x \ y) (y \ x) := disjoint_iff_inf_le.mpr sdiff_inf_sdiff.le

@[simp] theorem inf_sdiff_self_right : x ⊓ (y \ x) = ⊥ :=
calc x ⊓ (y \ x) = ((x ⊓ y) ⊔ (x \ y)) ⊓ (y \ x)         : by rw sup_inf_sdiff
             ... = (x ⊓ y) ⊓ (y \ x) ⊔ (x \ y) ⊓ (y \ x) : by rw inf_sup_right
             ... = ⊥         : by rw [@inf_comm _ _ x y, inf_inf_sdiff, sdiff_inf_sdiff, bot_sup_eq]
@[simp] theorem inf_sdiff_self_left : (y \ x) ⊓ x = ⊥ := by rw [inf_comm, inf_sdiff_self_right]

@[priority 100] -- see Note [lower instance priority]
instance generalized_boolean_algebra.to_generalized_coheyting_algebra :
  generalized_coheyting_algebra α :=
{ sdiff := (\),
  sdiff_le_iff := λ y x z, ⟨λ h, le_of_inf_le_sup_le
    (le_of_eq
      (calc y ⊓ (y \ x) = y \ x                         : inf_of_le_right sdiff_le'
                    ... = (x ⊓ (y \ x)) ⊔ (z ⊓ (y \ x))
                        : by rw [inf_eq_right.2 h, inf_sdiff_self_right, bot_sup_eq]
                    ... = (x ⊔ z) ⊓ (y \ x)             : inf_sup_right.symm))
    (calc y ⊔ y \ x = y                 : sup_of_le_left sdiff_le'
                ... ≤ y ⊔ (x ⊔ z)       : le_sup_left
                ... = ((y \ x) ⊔ x) ⊔ z : by rw [←sup_assoc, ←@sdiff_sup_self' _ x y]
                ... = x ⊔ z ⊔ y \ x     : by ac_refl),
   λ h, le_of_inf_le_sup_le
    (calc y \ x ⊓ x = ⊥     : inf_sdiff_self_left
                ... ≤ z ⊓ x : bot_le)
    (calc y \ x ⊔ x = y ⊔ x       : sdiff_sup_self'
                ... ≤ (x ⊔ z) ⊔ x : sup_le_sup_right h x
                ... ≤ z ⊔ x       : by rw [sup_assoc, sup_comm, sup_assoc, sup_idem])⟩,
  ..‹generalized_boolean_algebra α›, ..generalized_boolean_algebra.to_order_bot }

theorem disjoint_sdiff_self_left : disjoint (y \ x) x :=
disjoint_iff_inf_le.mpr inf_sdiff_self_left.le
theorem disjoint_sdiff_self_right : disjoint x (y \ x) :=
disjoint_iff_inf_le.mpr inf_sdiff_self_right.le

lemma le_sdiff : x ≤ y \ z ↔ x ≤ y ∧ disjoint x z :=
⟨λ h, ⟨h.trans sdiff_le, disjoint_sdiff_self_left.mono_left h⟩, λ h,
  by { rw ←h.2.sdiff_eq_left, exact sdiff_le_sdiff_right h.1 }⟩

@[simp] lemma sdiff_eq_left : x \ y = x ↔ disjoint x y :=
⟨λ h, disjoint_sdiff_self_left.mono_left h.ge, disjoint.sdiff_eq_left⟩

/- TODO: we could make an alternative constructor for `generalized_boolean_algebra` using
`disjoint x (y \ x)` and `x ⊔ (y \ x) = y` as axioms. -/
theorem disjoint.sdiff_eq_of_sup_eq (hi : disjoint x z) (hs : x ⊔ z = y) : y \ x = z :=
have h : y ⊓ x = x := inf_eq_right.2 $ le_sup_left.trans hs.le,
sdiff_unique (by rw [h, hs]) (by rw [h, hi.eq_bot])

protected theorem disjoint.sdiff_unique (hd : disjoint x z) (hz : z ≤ y) (hs : y ≤ x ⊔ z) :
  y \ x = z :=
sdiff_unique
  (begin
    rw ←inf_eq_right at hs,
    rwa [sup_inf_right, inf_sup_right, @sup_comm _ _ x, inf_sup_self, inf_comm, @sup_comm _ _ z,
      hs, sup_eq_left],
  end)
  (by rw [inf_assoc, hd.eq_bot, inf_bot_eq])

-- cf. `is_compl.disjoint_left_iff` and `is_compl.disjoint_right_iff`
lemma disjoint_sdiff_iff_le (hz : z ≤ y) (hx : x ≤ y) : disjoint z (y \ x) ↔ z ≤ x :=
⟨λ H, le_of_inf_le_sup_le
    (le_trans H.le_bot bot_le)
    (begin
      rw sup_sdiff_cancel_right hx,
      refine le_trans (sup_le_sup_left sdiff_le z) _,
      rw sup_eq_right.2 hz,
    end),
 λ H, disjoint_sdiff_self_right.mono_left H⟩

-- cf. `is_compl.le_left_iff` and `is_compl.le_right_iff`
lemma le_iff_disjoint_sdiff (hz : z ≤ y) (hx : x ≤ y) : z ≤ x ↔ disjoint z (y \ x) :=
(disjoint_sdiff_iff_le hz hx).symm

-- cf. `is_compl.inf_left_eq_bot_iff` and `is_compl.inf_right_eq_bot_iff`
lemma inf_sdiff_eq_bot_iff (hz : z ≤ y) (hx : x ≤ y) : z ⊓ (y \ x) = ⊥ ↔ z ≤ x :=
by { rw ←disjoint_iff, exact disjoint_sdiff_iff_le hz hx }

-- cf. `is_compl.left_le_iff` and `is_compl.right_le_iff`
lemma le_iff_eq_sup_sdiff (hz : z ≤ y) (hx : x ≤ y) : x ≤ z ↔ y = z ⊔ (y \ x) :=
⟨λ H,
  begin
    apply le_antisymm,
    { conv_lhs { rw ←sup_inf_sdiff y x, },
      apply sup_le_sup_right,
      rwa inf_eq_right.2 hx, },
    { apply le_trans,
      { apply sup_le_sup_right hz, },
      { rw sup_sdiff_left, } }
  end,
 λ H,
  begin
    conv_lhs at H { rw ←sup_sdiff_cancel_right hx, },
    refine le_of_inf_le_sup_le _ H.le,
    rw inf_sdiff_self_right,
    exact bot_le,
  end⟩

-- cf. `is_compl.sup_inf`
lemma sdiff_sup : y \ (x ⊔ z) = (y \ x) ⊓ (y \ z) :=
sdiff_unique
  (calc y ⊓ (x ⊔ z) ⊔ y \ x ⊓ (y \ z) =
        (y ⊓ (x ⊔ z) ⊔ y \ x) ⊓ (y ⊓ (x ⊔ z) ⊔ (y \ z))         : by rw sup_inf_left
  ... = (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ (y \ z))     : by rw @inf_sup_left _ _ y
  ... = (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ (y \ z))) : by ac_refl
  ... = (y ⊓ z ⊔ y) ⊓ (y ⊓ x ⊔ y)                             : by rw [sup_inf_sdiff, sup_inf_sdiff]
  ... = (y ⊔ y ⊓ z) ⊓ (y ⊔ y ⊓ x)                               : by ac_refl
  ... = y                                            : by rw [sup_inf_self, sup_inf_self, inf_idem])
  (calc y ⊓ (x ⊔ z) ⊓ ((y \ x) ⊓ (y \ z)) =
        (y ⊓ x ⊔ y ⊓ z) ⊓ ((y \ x) ⊓ (y \ z))                             : by rw inf_sup_left
  ... = ((y ⊓ x) ⊓ ((y \ x) ⊓ (y \ z))) ⊔ ((y ⊓ z) ⊓ ((y \ x) ⊓ (y \ z))) : by rw inf_sup_right
  ... = ((y ⊓ x) ⊓ (y \ x) ⊓ (y \ z)) ⊔ ((y \ x) ⊓ ((y \ z) ⊓ (y ⊓ z)))   : by ac_refl
  ... = ⊥ : by rw [inf_inf_sdiff, bot_inf_eq, bot_sup_eq, @inf_comm _ _ (y \ z), inf_inf_sdiff,
              inf_bot_eq])

lemma sdiff_eq_sdiff_iff_inf_eq_inf : y \ x = y \ z ↔ y ⊓ x = y ⊓ z :=
⟨λ h, eq_of_inf_eq_sup_eq
  (by rw [inf_inf_sdiff, h, inf_inf_sdiff])
  (by rw [sup_inf_sdiff, h, sup_inf_sdiff]),
 λ h, by rw [←sdiff_inf_self_right, ←sdiff_inf_self_right z y, inf_comm, h, inf_comm]⟩

theorem sdiff_eq_self_iff_disjoint : x \ y = x ↔ disjoint y x :=
calc x \ y = x ↔ x \ y = x \ ⊥ : by rw sdiff_bot
           ... ↔ x ⊓ y = x ⊓ ⊥ : sdiff_eq_sdiff_iff_inf_eq_inf
           ... ↔ disjoint y x  : by rw [inf_bot_eq, inf_comm, disjoint_iff]

theorem sdiff_eq_self_iff_disjoint' : x \ y = x ↔ disjoint x y :=
by rw [sdiff_eq_self_iff_disjoint, disjoint.comm]

lemma sdiff_lt (hx : y ≤ x) (hy : y ≠ ⊥) :
  x \ y < x :=
begin
  refine sdiff_le.lt_of_ne (λ h, hy _),
  rw [sdiff_eq_self_iff_disjoint', disjoint_iff] at h,
  rw [←h, inf_eq_right.mpr hx],
end

@[simp] lemma le_sdiff_iff : x ≤ y \ x ↔ x = ⊥ :=
⟨λ h, disjoint_self.1 (disjoint_sdiff_self_right.mono_right h), λ h, h.le.trans bot_le⟩

lemma sdiff_lt_sdiff_right (h : x < y) (hz : z ≤ x) : x \ z < y \ z :=
(sdiff_le_sdiff_right h.le).lt_of_not_le $ λ h', h.not_le $
  le_sdiff_sup.trans $ sup_le_of_le_sdiff_right h' hz

lemma sup_inf_inf_sdiff : (x ⊓ y) ⊓ z ⊔ (y \ z) = (x ⊓ y) ⊔ (y \ z) :=
calc (x ⊓ y) ⊓ z ⊔ (y \ z) = x ⊓ (y ⊓ z) ⊔ (y \ z) : by rw inf_assoc
                       ... = (x ⊔ (y \ z)) ⊓ y     : by rw [sup_inf_right, sup_inf_sdiff]
                       ... = (x ⊓ y) ⊔ (y \ z)     : by rw [inf_sup_right, inf_sdiff_left]

lemma sdiff_sdiff_right : x \ (y \ z) = (x \ y) ⊔ (x ⊓ y ⊓ z) :=
begin
  rw [sup_comm, inf_comm, ←inf_assoc, sup_inf_inf_sdiff],
  apply sdiff_unique,
  { calc x ⊓ (y \ z) ⊔ (z ⊓ x ⊔ x \ y) =
          (x ⊔ (z ⊓ x ⊔ x \ y)) ⊓ (y \ z ⊔ (z ⊓ x ⊔ x \ y)) : by rw sup_inf_right
    ... = (x ⊔ x ⊓ z ⊔ x \ y) ⊓ (y \ z ⊔ (x ⊓ z ⊔ x \ y))   : by ac_refl
    ... = x ⊓ (y \ z ⊔ x ⊓ z ⊔ x \ y)             : by rw [sup_inf_self, sup_sdiff_left, ←sup_assoc]
    ... = x ⊓ (y \ z ⊓ (z ⊔ y) ⊔ x ⊓ (z ⊔ y) ⊔ x \ y) :
                          by rw [sup_inf_left, sdiff_sup_self', inf_sup_right, @sup_comm _ _ y]
    ... = x ⊓ (y \ z ⊔ (x ⊓ z ⊔ x ⊓ y) ⊔ x \ y) :
                                                by rw [inf_sdiff_sup_right, @inf_sup_left _ _ x z y]
    ... = x ⊓ (y \ z ⊔ (x ⊓ z ⊔ (x ⊓ y ⊔ x \ y)))           : by ac_refl
    ... = x ⊓ (y \ z ⊔ (x ⊔ x ⊓ z))                   : by rw [sup_inf_sdiff, @sup_comm _ _ (x ⊓ z)]
    ... = x                                        : by rw [sup_inf_self, sup_comm, inf_sup_self] },
  { calc x ⊓ (y \ z) ⊓ (z ⊓ x ⊔ x \ y) =
          x ⊓ (y \ z) ⊓ (z ⊓ x) ⊔ x ⊓ (y \ z) ⊓ (x \ y) : by rw inf_sup_left
    ... = x ⊓ (y \ z ⊓ z ⊓ x) ⊔ x ⊓ (y \ z) ⊓ (x \ y)   : by ac_refl
    ... = x ⊓ (y \ z) ⊓ (x \ y) :    by rw [inf_sdiff_self_left, bot_inf_eq, inf_bot_eq, bot_sup_eq]
    ... = x ⊓ (y \ z ⊓ y) ⊓ (x \ y)                     : by conv_lhs { rw ←inf_sdiff_left }
    ... = x ⊓ (y \ z ⊓ (y ⊓ (x \ y)))                   : by ac_refl
    ... = ⊥                                 : by rw [inf_sdiff_self_right, inf_bot_eq, inf_bot_eq] }
end

lemma sdiff_sdiff_right' : x \ (y \ z) = (x \ y) ⊔ (x ⊓ z) :=
calc  x \ (y \ z) = (x \ y) ⊔ (x ⊓ y ⊓ z) : sdiff_sdiff_right
              ... = z ⊓ x ⊓ y ⊔ (x \ y)   : by ac_refl
              ... = (x \ y) ⊔ (x ⊓ z)     : by rw [sup_inf_inf_sdiff, sup_comm, inf_comm]

lemma sdiff_sdiff_eq_sdiff_sup (h : z ≤ x) : x \ (y \ z) = x \ y ⊔ z :=
by rw [sdiff_sdiff_right', inf_eq_right.2 h]

@[simp] lemma sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y :=
by rw [sdiff_sdiff_right, inf_idem, sdiff_self, bot_sup_eq]

lemma sdiff_sdiff_eq_self (h : y ≤ x) : x \ (x \ y) = y :=
by rw [sdiff_sdiff_right_self, inf_of_le_right h]

lemma sdiff_eq_symm (hy : y ≤ x) (h : x \ y = z) : x \ z = y := by rw [←h, sdiff_sdiff_eq_self hy]
lemma sdiff_eq_comm (hy : y ≤ x) (hz : z ≤ x) : x \ y = z ↔ x \ z = y :=
⟨sdiff_eq_symm hy, sdiff_eq_symm hz⟩

lemma eq_of_sdiff_eq_sdiff (hxz : x ≤ z) (hyz : y ≤ z) (h : z \ x = z \ y) : x = y :=
by rw [←sdiff_sdiff_eq_self hxz, h, sdiff_sdiff_eq_self hyz]

lemma sdiff_sdiff_left' : (x \ y) \ z = (x \ y) ⊓ (x \ z) :=
by rw [sdiff_sdiff_left, sdiff_sup]

lemma sdiff_sdiff_sup_sdiff : z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) :=
calc z \ (x \ y ⊔ y \ x) = (z \ x ⊔ z ⊓ x ⊓ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) :
                                             by rw [sdiff_sup, sdiff_sdiff_right, sdiff_sdiff_right]
... = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) : by rw [sup_inf_left, sup_comm, sup_inf_sdiff]
... = z ⊓ (z \ x ⊔ y) ⊓ (z ⊓ (z \ y ⊔ x)) :
                                          by rw [sup_inf_left, @sup_comm _ _ (z \ y), sup_inf_sdiff]
... = z ⊓ z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x)     : by ac_refl
... = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x)         : by rw inf_idem

lemma sdiff_sdiff_sup_sdiff' : z \ (x \ y ⊔ y \ x) = z ⊓ x ⊓ y ⊔ ((z \ x) ⊓ (z \ y)) :=
calc z \ (x \ y ⊔ y \ x) =
      z \ (x \ y) ⊓ (z \ (y \ x))               : sdiff_sup
... = (z \ x ⊔ z ⊓ x ⊓ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) : by rw [sdiff_sdiff_right, sdiff_sdiff_right]
... = (z \ x ⊔ z ⊓ y ⊓ x) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) : by ac_refl
... = (z \ x) ⊓ (z \ y) ⊔ z ⊓ y ⊓ x             : sup_inf_right.symm
... = z ⊓ x ⊓ y ⊔ ((z \ x) ⊓ (z \ y))           : by ac_refl

lemma inf_sdiff : (x ⊓ y) \ z = (x \ z) ⊓ (y \ z) :=
sdiff_unique
  (calc (x ⊓ y) ⊓ z ⊔ ((x \ z) ⊓ (y \ z)) =
        ((x ⊓ y) ⊓ z ⊔ (x \ z)) ⊓ ((x ⊓ y) ⊓ z ⊔ (y \ z)) : by rw [sup_inf_left]
  ... = (x ⊓ y ⊓ (z ⊔ x) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) :
                     by rw [sup_inf_right, sup_sdiff_self_right, inf_sup_right, inf_sdiff_sup_right]
  ... = (y ⊓ (x ⊓ (x ⊔ z)) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) : by ac_refl
  ... = ((y ⊓ x) ⊔ (x \ z)) ⊓ ((x ⊓ y) ⊔ (y \ z))         : by rw [inf_sup_self, sup_inf_inf_sdiff]
  ... = (x ⊓ y) ⊔ ((x \ z) ⊓ (y \ z))                     : by rw [@inf_comm _ _ y, sup_inf_left]
  ... = x ⊓ y                                        : sup_eq_left.2 (inf_le_inf sdiff_le sdiff_le))
  (calc (x ⊓ y) ⊓ z ⊓ ((x \ z) ⊓ (y \ z)) =
        x ⊓ y ⊓ (z ⊓ (x \ z)) ⊓ (y \ z) : by ac_refl
  ... = ⊥                               : by rw [inf_sdiff_self_right, inf_bot_eq, bot_inf_eq])

lemma inf_sdiff_assoc : (x ⊓ y) \ z = x ⊓ (y \ z) :=
sdiff_unique
  (calc x ⊓ y ⊓ z ⊔ x ⊓ (y \ z) = x ⊓ (y ⊓ z) ⊔ x ⊓ (y \ z) : by rw inf_assoc
                            ... = x ⊓ ((y ⊓ z) ⊔ y \ z)     : inf_sup_left.symm
                            ... = x ⊓ y                     : by rw sup_inf_sdiff)
  (calc x ⊓ y ⊓ z ⊓ (x ⊓ (y \ z)) = x ⊓ x ⊓ ((y ⊓ z) ⊓ (y \ z)) : by ac_refl
                              ... = ⊥                           : by rw [inf_inf_sdiff, inf_bot_eq])

lemma inf_sdiff_right_comm : x \ z ⊓ y = (x ⊓ y) \ z :=
by rw [@inf_comm _ _ x, inf_comm, inf_sdiff_assoc]

lemma inf_sdiff_distrib_left (a b c : α) : a ⊓ b \ c = (a ⊓ b) \ (a ⊓ c) :=
by rw [sdiff_inf, sdiff_eq_bot_iff.2 inf_le_left, bot_sup_eq, inf_sdiff_assoc]

lemma inf_sdiff_distrib_right (a b c : α) : a \ b ⊓ c = (a ⊓ c) \ (b ⊓ c) :=
by simp_rw [@inf_comm _ _ _ c, inf_sdiff_distrib_left]

lemma sup_eq_sdiff_sup_sdiff_sup_inf : x ⊔ y = (x \ y) ⊔ (y \ x) ⊔ (x ⊓ y) :=
eq.symm $
  calc (x \ y) ⊔ (y \ x) ⊔ (x ⊓ y) =
        ((x \ y) ⊔ (y \ x) ⊔ x) ⊓ ((x \ y) ⊔ (y \ x) ⊔ y)   : by rw sup_inf_left
  ... = ((x \ y) ⊔ x ⊔ (y \ x)) ⊓ ((x \ y) ⊔ ((y \ x) ⊔ y)) : by ac_refl
  ... = (x ⊔ (y \ x)) ⊓ ((x \ y) ⊔ y)                     : by rw [sup_sdiff_right, sup_sdiff_right]
  ... = x ⊔ y                          : by rw [sup_sdiff_self_right, sup_sdiff_self_left, inf_idem]

lemma sup_lt_of_lt_sdiff_left (h : y < z \ x) (hxz : x ≤ z) : x ⊔ y < z :=
begin
  rw ←sup_sdiff_cancel_right hxz,
  refine (sup_le_sup_left h.le _).lt_of_not_le (λ h', h.not_le _),
  rw ←sdiff_idem,
  exact (sdiff_le_sdiff_of_sup_le_sup_left h').trans sdiff_le,
end

lemma sup_lt_of_lt_sdiff_right (h : x < z \ y) (hyz : y ≤ z) : x ⊔ y < z :=
begin
  rw ←sdiff_sup_cancel hyz,
  refine (sup_le_sup_right h.le _).lt_of_not_le (λ h', h.not_le _),
  rw ←sdiff_idem,
  exact (sdiff_le_sdiff_of_sup_le_sup_right h').trans sdiff_le,
end

instance pi.generalized_boolean_algebra {α : Type u} {β : Type v} [generalized_boolean_algebra β] :
  generalized_boolean_algebra (α → β) :=
by pi_instance

end generalized_boolean_algebra

/-!
### Boolean algebras
-/
/-- A Boolean algebra is a bounded distributive lattice with a complement operator `ᶜ` such that
`x ⊓ xᶜ = ⊥` and `x ⊔ xᶜ = ⊤`. For convenience, it must also provide a set difference operation `\`
and a Heyting implication `⇨` satisfying `x \ y = x ⊓ yᶜ` and `x ⇨ y = y ⊔ xᶜ`.

This is a generalization of (classical) logic of propositions, or the powerset lattice.

Since `bounded_order`, `order_bot`, and `order_top` are mixins that require `has_le`
to be present at define-time, the `extends` mechanism does not work with them.
Instead, we extend using the underlying `has_bot` and `has_top` data typeclasses, and replicate the
order axioms of those classes here. A "forgetful" instance back to `bounded_order` is provided.
-/
class boolean_algebra (α : Type u) extends distrib_lattice α, has_compl α, has_sdiff α, has_himp α,
  has_top α, has_bot α :=
(inf_compl_le_bot : ∀x:α, x ⊓ xᶜ ≤ ⊥)
(top_le_sup_compl : ∀x:α, ⊤ ≤ x ⊔ xᶜ)
(le_top : ∀ a : α, a ≤ ⊤)
(bot_le : ∀ a : α, ⊥ ≤ a)
(sdiff := λ x y, x ⊓ yᶜ)
(himp := λ x y, y ⊔ xᶜ)
(sdiff_eq : ∀ x y : α, x \ y = x ⊓ yᶜ . obviously)
(himp_eq : ∀ x y : α, x ⇨ y = y ⊔ xᶜ . obviously)

@[priority 100] -- see Note [lower instance priority]
instance boolean_algebra.to_bounded_order [h : boolean_algebra α] : bounded_order α :=
{ ..h }

/-- A bounded generalized boolean algebra is a boolean algebra. -/
@[reducible] -- See note [reducible non instances]
def generalized_boolean_algebra.to_boolean_algebra [generalized_boolean_algebra α] [order_top α] :
  boolean_algebra α :=
{ compl := λ a, ⊤ \ a,
  inf_compl_le_bot := λ _, disjoint_sdiff_self_right.le_bot,
  top_le_sup_compl := λ _, le_sup_sdiff,
  sdiff_eq := λ _ _, by { rw [←inf_sdiff_assoc, inf_top_eq], refl },
  ..‹generalized_boolean_algebra α›, ..generalized_boolean_algebra.to_order_bot, ..‹order_top α› }

section boolean_algebra
variables [boolean_algebra α]

@[simp] lemma inf_compl_eq_bot' : x ⊓ xᶜ = ⊥ := bot_unique $ boolean_algebra.inf_compl_le_bot x
@[simp] lemma sup_compl_eq_top : x ⊔ xᶜ = ⊤ := top_unique $ boolean_algebra.top_le_sup_compl x
@[simp] lemma compl_sup_eq_top : xᶜ ⊔ x = ⊤ := sup_comm.trans sup_compl_eq_top

lemma is_compl_compl : is_compl x xᶜ := is_compl.of_eq inf_compl_eq_bot' sup_compl_eq_top

lemma sdiff_eq : x \ y = x ⊓ yᶜ := boolean_algebra.sdiff_eq x y
lemma himp_eq : x ⇨ y = y ⊔ xᶜ := boolean_algebra.himp_eq x y

@[priority 100]
instance boolean_algebra.to_complemented_lattice : complemented_lattice α :=
⟨λ x, ⟨xᶜ, is_compl_compl⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance boolean_algebra.to_generalized_boolean_algebra : generalized_boolean_algebra α :=
{ sup_inf_sdiff := λ a b, by rw [sdiff_eq, ←inf_sup_left, sup_compl_eq_top, inf_top_eq],
  inf_inf_sdiff := λ a b, by { rw [sdiff_eq, ←inf_inf_distrib_left, inf_compl_eq_bot', inf_bot_eq],
    congr },
  ..‹boolean_algebra α› }

@[priority 100] -- See note [lower instance priority]
instance boolean_algebra.to_biheyting_algebra : biheyting_algebra α :=
{ hnot := compl,
  le_himp_iff := λ a b c, by rw [himp_eq, is_compl_compl.le_sup_right_iff_inf_left_le],
  himp_bot := λ _, himp_eq.trans bot_sup_eq,
  top_sdiff := λ a, by rw [sdiff_eq, top_inf_eq],
  ..‹boolean_algebra α›, ..generalized_boolean_algebra.to_generalized_coheyting_algebra }

@[simp] lemma hnot_eq_compl : ￢x = xᶜ := rfl

@[simp] lemma top_sdiff : ⊤ \ x = xᶜ := top_sdiff' _

theorem eq_compl_iff_is_compl : x = yᶜ ↔ is_compl x y :=
⟨λ h, by { rw h, exact is_compl_compl.symm }, is_compl.eq_compl⟩

theorem compl_eq_iff_is_compl : xᶜ = y ↔ is_compl x y :=
⟨λ h, by { rw ←h, exact is_compl_compl }, is_compl.compl_eq⟩

theorem compl_eq_comm : xᶜ = y ↔ yᶜ = x :=
by rw [eq_comm, compl_eq_iff_is_compl, eq_compl_iff_is_compl]

theorem eq_compl_comm : x = yᶜ ↔ y = xᶜ :=
by rw [eq_comm, compl_eq_iff_is_compl, eq_compl_iff_is_compl]

@[simp] theorem compl_compl (x : α) : xᶜᶜ = x := (@is_compl_compl _ x _).symm.compl_eq

theorem compl_comp_compl : compl ∘ compl = @id α := funext compl_compl

@[simp] theorem compl_involutive : function.involutive (compl : α → α) := compl_compl

theorem compl_bijective : function.bijective (compl : α → α) :=
compl_involutive.bijective

theorem compl_surjective : function.surjective (compl : α → α) :=
compl_involutive.surjective

theorem compl_injective : function.injective (compl : α → α) :=
compl_involutive.injective

@[simp] theorem compl_inj_iff : xᶜ = yᶜ ↔ x = y :=
compl_injective.eq_iff

theorem is_compl.compl_eq_iff (h : is_compl x y) : zᶜ = y ↔ z = x :=
h.compl_eq ▸ compl_inj_iff

@[simp] theorem compl_eq_top : xᶜ = ⊤ ↔ x = ⊥ :=
is_compl_bot_top.compl_eq_iff

@[simp] theorem compl_eq_bot : xᶜ = ⊥ ↔ x = ⊤ :=
is_compl_top_bot.compl_eq_iff

@[simp] theorem compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ := hnot_inf_distrib _ _

@[simp] theorem compl_le_compl_iff_le : yᶜ ≤ xᶜ ↔ x ≤ y :=
⟨assume h, by have h := compl_le_compl h; simp at h; assumption,
  compl_le_compl⟩

theorem compl_le_of_compl_le (h : yᶜ ≤ x) : xᶜ ≤ y :=
by simpa only [compl_compl] using compl_le_compl h

theorem compl_le_iff_compl_le : xᶜ ≤ y ↔ yᶜ ≤ x :=
⟨compl_le_of_compl_le, compl_le_of_compl_le⟩

@[simp] lemma sdiff_compl : x \ yᶜ = x ⊓ y := by rw [sdiff_eq, compl_compl]

instance : boolean_algebra αᵒᵈ :=
{ compl := λ a, to_dual (of_dual a)ᶜ,
  sdiff := λ a b, to_dual (of_dual b ⇨ of_dual a),
  himp := λ a b, to_dual (of_dual b \ of_dual a),
  inf_compl_le_bot := λ a, (@codisjoint_hnot_right _ _ (of_dual a)).top_le,
  top_le_sup_compl := λ a, (@disjoint_compl_right _ _ (of_dual a)).le_bot,
  sdiff_eq := λ _ _, himp_eq,
  himp_eq := λ _ _, sdiff_eq,
  ..order_dual.distrib_lattice α, ..order_dual.bounded_order α }

@[simp] lemma sup_inf_inf_compl : (x ⊓ y) ⊔ (x ⊓ yᶜ) = x :=
by rw [← sdiff_eq, sup_inf_sdiff _ _]

@[simp] lemma compl_sdiff : (x \ y)ᶜ = x ⇨ y :=
by rw [sdiff_eq, himp_eq, compl_inf, compl_compl, sup_comm]

@[simp] lemma compl_himp : (x ⇨ y)ᶜ = x \ y := @compl_sdiff αᵒᵈ _ _ _

@[simp] lemma compl_sdiff_compl : xᶜ \ yᶜ = y \ x := by rw [sdiff_compl, sdiff_eq, inf_comm]
@[simp] lemma compl_himp_compl : xᶜ ⇨ yᶜ = y ⇨ x := @compl_sdiff_compl αᵒᵈ _ _ _

lemma disjoint_compl_left_iff : disjoint xᶜ y ↔ y ≤ x :=
by rw [←le_compl_iff_disjoint_left, compl_compl]

lemma disjoint_compl_right_iff : disjoint x yᶜ ↔ x ≤ y :=
by rw [←le_compl_iff_disjoint_right, compl_compl]

end boolean_algebra

instance Prop.boolean_algebra : boolean_algebra Prop :=
{ compl := not,
  himp_eq := λ p q, propext imp_iff_or_not,
  inf_compl_le_bot := λ p ⟨Hp, Hpc⟩, Hpc Hp,
  top_le_sup_compl := λ p H, classical.em p,
  .. Prop.heyting_algebra, ..generalized_heyting_algebra.to_distrib_lattice }

instance pi.boolean_algebra {ι : Type u} {α : ι → Type v} [∀ i, boolean_algebra (α i)] :
  boolean_algebra (Π i, α i) :=
{ sdiff_eq := λ x y, funext $ λ i, sdiff_eq,
  himp_eq := λ x y, funext $ λ i, himp_eq,
  inf_compl_le_bot := λ _ _, boolean_algebra.inf_compl_le_bot _,
  top_le_sup_compl := λ _ _, boolean_algebra.top_le_sup_compl _,
  .. pi.has_sdiff,
  .. pi.heyting_algebra,
  .. pi.distrib_lattice }

instance : boolean_algebra bool :=
{ sup := bor,
  le_sup_left := bool.left_le_bor,
  le_sup_right := bool.right_le_bor,
  sup_le := λ _ _ _, bool.bor_le,
  inf := band,
  inf_le_left := bool.band_le_left,
  inf_le_right := bool.band_le_right,
  le_inf := λ _ _ _, bool.le_band,
  le_sup_inf := dec_trivial,
  compl := bnot,
  inf_compl_le_bot := λ a, a.band_bnot_self.le,
  top_le_sup_compl := λ a, a.bor_bnot_self.ge,
  ..bool.linear_order, ..bool.bounded_order }

@[simp] lemma bool.sup_eq_bor : (⊔) = bor := rfl
@[simp] lemma bool.inf_eq_band : (⊓) = band := rfl
@[simp] lemma bool.compl_eq_bnot : has_compl.compl = bnot := rfl

section lift

/-- Pullback a `generalized_boolean_algebra` along an injection. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.generalized_boolean_algebra [has_sup α] [has_inf α] [has_bot α]
  [has_sdiff α] [generalized_boolean_algebra β] (f : α → β) (hf : injective f)
  (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
  (map_bot : f ⊥ = ⊥) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
  generalized_boolean_algebra α :=
{ sup_inf_sdiff := λ a b, hf $ by erw [map_sup, map_sdiff, map_inf, sup_inf_sdiff],
  inf_inf_sdiff := λ a b, hf $ by erw [map_inf, map_sdiff, map_inf, inf_inf_sdiff, map_bot],
  ..hf.generalized_coheyting_algebra f map_sup map_inf map_bot map_sdiff,
  ..hf.distrib_lattice f map_sup map_inf }

/-- Pullback a `boolean_algebra` along an injection. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.boolean_algebra [has_sup α] [has_inf α] [has_top α] [has_bot α]
  [has_compl α] [has_sdiff α] [boolean_algebra β] (f : α → β) (hf : injective f)
  (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
  (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f aᶜ = (f a)ᶜ)
  (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
  boolean_algebra α :=
{ compl := compl,
  top := ⊤,
  le_top := λ a, (@le_top β _ _ _).trans map_top.ge,
  bot_le := λ a, map_bot.le.trans bot_le,
  inf_compl_le_bot := λ a, ((map_inf _ _).trans $ by rw [map_compl, inf_compl_eq_bot, map_bot]).le,
  top_le_sup_compl := λ a, ((map_sup _ _).trans $ by rw [map_compl, sup_compl_eq_top, map_top]).ge,
  sdiff_eq := λ a b, hf $ (map_sdiff _ _).trans $ sdiff_eq.trans $
    by { convert (map_inf _ _).symm, exact (map_compl _).symm },
  ..hf.generalized_boolean_algebra f map_sup map_inf map_bot map_sdiff }

end lift

instance : boolean_algebra punit :=
by refine_struct
{ ..punit.biheyting_algebra };
    intros; trivial <|> exact subsingleton.elim _ _
