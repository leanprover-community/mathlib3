/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bryan Gin-ge Chen
-/
import order.bounded_order
/-!
# (Generalized) Boolean algebras

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

* `has_compl`: a type class for the complement operator
* `generalized_boolean_algebra`: a type class for generalized Boolean algebras
* `boolean_algebra.core`: a type class with the minimal assumptions for a Boolean algebras
* `boolean_algebra`: the main type class for Boolean algebras; it extends both
  `generalized_boolean_algebra` and `boolean_algebra.core`. An instance of `boolean_algebra` can be
  obtained from one of `boolean_algebra.core` using `boolean_algebra.of_core`.
* `Prop.boolean_algebra`: the Boolean algebra instance on `Prop`

## Implementation notes

The `sup_inf_sdiff` and `inf_inf_sdiff` axioms for the relative complement operator in
`generalized_boolean_algebra` are taken from
[Wikipedia](https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations).

[Stone's paper introducing generalized Boolean algebras][Stone1935] does not define a relative
complement operator `a \ b` for all `a`, `b`. Instead, the postulates there amount to an assumption
that for all `a, b : α` where `a ≤ b`, the equations `x ⊔ a = b` and `x ⊓ a = ⊥` have a solution
`x`. `disjoint.sdiff_unique` proves that this `x` is in fact `b \ a`.

## Notations

* `xᶜ` is notation for `compl x`
* `x \ y` is notation for `sdiff x y`.

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

export has_sdiff (sdiff)

/-- A generalized Boolean algebra is a distributive lattice with `⊥` and a relative complement
operation `\` (called `sdiff`, after "set difference") satisfying `(a ⊓ b) ⊔ (a \ b) = a` and
`(a ⊓ b) ⊓ (a \ b) = b`, i.e. `a \ b` is the complement of `b` in `a`.

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

theorem disjoint_inf_sdiff : disjoint (x ⊓ y) (x \ y) := (inf_inf_sdiff x y).le

-- TODO: in distributive lattices, relative complements are unique when they exist
theorem sdiff_unique (s : (x ⊓ y) ⊔ z = x) (i : (x ⊓ y) ⊓ z = ⊥) : x \ y = z :=
begin
  conv_rhs at s { rw [←sup_inf_sdiff x y, sup_comm] },
  rw sup_comm at s,
  conv_rhs at i { rw [←inf_inf_sdiff x y, inf_comm] },
  rw inf_comm at i,
  exact (eq_of_inf_eq_sup_eq i s).symm,
end

lemma sdiff_le : x \ y ≤ x :=
calc x \ y ≤ (x ⊓ y) ⊔ (x \ y) : le_sup_right
       ... = x                 : sup_inf_sdiff x y

@[simp] lemma bot_sdiff : ⊥ \ x = ⊥ := le_bot_iff.1 sdiff_le

lemma inf_sdiff_right : x ⊓ (x \ y) = x \ y := by rw [inf_of_le_right (@sdiff_le _ x y _)]
lemma inf_sdiff_left : (x \ y) ⊓ x = x \ y := by rw [inf_comm, inf_sdiff_right]

-- cf. `is_compl_top_bot`
@[simp] lemma sdiff_self : x \ x = ⊥ :=
by rw [←inf_inf_sdiff, inf_idem, inf_of_le_right (@sdiff_le _ x x _)]

@[simp] theorem sup_sdiff_self_right : x ⊔ (y \ x) = x ⊔ y :=
calc x ⊔ (y \ x) = (x ⊔ (x ⊓ y)) ⊔ (y \ x) : by rw sup_inf_self
             ... = x ⊔ ((y ⊓ x) ⊔ (y \ x)) : by ac_refl
             ... = x ⊔ y                   : by rw sup_inf_sdiff

@[simp] theorem sup_sdiff_self_left : (y \ x) ⊔ x = y ⊔ x :=
by rw [sup_comm, sup_sdiff_self_right, sup_comm]

lemma sup_sdiff_symm : x ⊔ (y \ x) = y ⊔ (x \ y) :=
by rw [sup_sdiff_self_right, sup_sdiff_self_right, sup_comm]

lemma sup_sdiff_cancel_right (h : x ≤ y) : x ⊔ (y \ x) = y :=
by conv_rhs { rw [←sup_inf_sdiff y x, inf_eq_right.2 h] }

lemma sdiff_sup_cancel (h : y ≤ x) : x \ y ⊔ y = x := by rw [sup_comm, sup_sdiff_cancel_right h]

lemma sup_le_of_le_sdiff_left (h : y ≤ z \ x) (hxz : x ≤ z) : x ⊔ y ≤ z :=
(sup_le_sup_left h x).trans (sup_sdiff_cancel_right hxz).le

lemma sup_le_of_le_sdiff_right (h : x ≤ z \ y) (hyz : y ≤ z) : x ⊔ y ≤ z :=
(sup_le_sup_right h y).trans (sdiff_sup_cancel hyz).le

@[simp] lemma sup_sdiff_left : x ⊔ (x \ y) = x := by { rw sup_eq_left, exact sdiff_le }
lemma sup_sdiff_right : (x \ y) ⊔ x = x := by rw [sup_comm, sup_sdiff_left]

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
     ... = (x \ y) ⊓ (y \ x)                           : by rw inf_sdiff_right

lemma disjoint_sdiff_sdiff : disjoint (x \ y) (y \ x) := sdiff_inf_sdiff.le

theorem le_sup_sdiff : y ≤ x ⊔ (y \ x) :=
by { rw [sup_sdiff_self_right], exact le_sup_right }

theorem le_sdiff_sup : y ≤ (y \ x) ⊔ x :=
by { rw [sup_comm], exact le_sup_sdiff }

@[simp] theorem inf_sdiff_self_right : x ⊓ (y \ x) = ⊥ :=
calc x ⊓ (y \ x) = ((x ⊓ y) ⊔ (x \ y)) ⊓ (y \ x)         : by rw sup_inf_sdiff
             ... = (x ⊓ y) ⊓ (y \ x) ⊔ (x \ y) ⊓ (y \ x) : by rw inf_sup_right
             ... = ⊥         : by rw [@inf_comm _ _ x y, inf_inf_sdiff, sdiff_inf_sdiff, bot_sup_eq]
@[simp] theorem inf_sdiff_self_left : (y \ x) ⊓ x = ⊥ := by rw [inf_comm, inf_sdiff_self_right]

theorem disjoint_sdiff_self_left : disjoint (y \ x) x := inf_sdiff_self_left.le
theorem disjoint_sdiff_self_right : disjoint x (y \ x) := inf_sdiff_self_right.le

lemma disjoint.disjoint_sdiff_left (h : disjoint x y) : disjoint (x \ z) y := h.mono_left sdiff_le
lemma disjoint.disjoint_sdiff_right (h : disjoint x y) : disjoint x (y \ z) := h.mono_right sdiff_le

/- TODO: we could make an alternative constructor for `generalized_boolean_algebra` using
`disjoint x (y \ x)` and `x ⊔ (y \ x) = y` as axioms. -/
theorem disjoint.sdiff_eq_of_sup_eq (hi : disjoint x z) (hs : x ⊔ z = y) : y \ x = z :=
have h : y ⊓ x = x := inf_eq_right.2 $ le_sup_left.trans hs.le,
sdiff_unique (by rw [h, hs]) (by rw [h, hi.eq_bot])

lemma disjoint.sup_sdiff_cancel_left (h : disjoint x y) : (x ⊔ y) \ x = y :=
h.sdiff_eq_of_sup_eq rfl
lemma disjoint.sup_sdiff_cancel_right (h : disjoint x y) : (x ⊔ y) \ y = x :=
h.symm.sdiff_eq_of_sup_eq sup_comm

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
    (le_trans H bot_le)
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

-- cf. `set.union_diff_cancel'`
lemma sup_sdiff_cancel' (hx : x ≤ z) (hz : z ≤ y) : z ⊔ (y \ x) = y :=
((le_iff_eq_sup_sdiff hz (hx.trans hz)).1 hx).symm

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

-- cf. `is_compl.inf_sup`
lemma sdiff_inf : y \ (x ⊓ z) = y \ x ⊔ y \ z :=
sdiff_unique
  (calc y ⊓ (x ⊓ z) ⊔ (y \ x ⊔ y \ z) =
        (z ⊓ (y ⊓ x)) ⊔ (y \ x ⊔ y \ z)                     : by ac_refl
  ... = (z ⊔ (y \ x ⊔ y \ z)) ⊓ ((y ⊓ x) ⊔ (y \ x ⊔ y \ z)) : by rw sup_inf_right
  ... = (y \ x ⊔ (y \ z ⊔ z)) ⊓ (y ⊓ x ⊔ (y \ x ⊔ y \ z))   : by ac_refl
  ... = (y ⊔ z) ⊓ ((y ⊓ x) ⊔ (y \ x ⊔ y \ z)) :
                                            by rw [sup_sdiff_self_left, ←sup_assoc, sup_sdiff_right]
  ... = (y ⊔ z) ⊓ y                              : by rw [←sup_assoc, sup_inf_sdiff, sup_sdiff_left]
  ... = y                                                   : by rw [inf_comm, inf_sup_self])
  (calc y ⊓ (x ⊓ z) ⊓ ((y \ x) ⊔ (y \ z)) =
        (y ⊓ (x ⊓ z) ⊓ (y \ x)) ⊔ (y ⊓ (x ⊓ z) ⊓ (y \ z)) : by rw inf_sup_left
  ... = z ⊓ (y ⊓ x ⊓ (y \ x)) ⊔ z ⊓ (y ⊓ x) ⊓ (y \ z)     : by ac_refl
  ... = z ⊓ (y ⊓ x) ⊓ (y \ z)                        : by rw [inf_inf_sdiff, inf_bot_eq, bot_sup_eq]
  ... = x ⊓ ((y ⊓ z) ⊓ (y \ z))                           : by ac_refl
  ... = ⊥                                                 : by rw [inf_inf_sdiff, inf_bot_eq])

@[simp] lemma sdiff_inf_self_right : y \ (x ⊓ y) = y \ x :=
by rw [sdiff_inf, sdiff_self, sup_bot_eq]
@[simp] lemma sdiff_inf_self_left : y \ (y ⊓ x) = y \ x := by rw [inf_comm, sdiff_inf_self_right]

lemma sdiff_eq_sdiff_iff_inf_eq_inf : y \ x = y \ z ↔ y ⊓ x = y ⊓ z :=
⟨λ h, eq_of_inf_eq_sup_eq
  (by rw [inf_inf_sdiff, h, inf_inf_sdiff])
  (by rw [sup_inf_sdiff, h, sup_inf_sdiff]),
 λ h, by rw [←sdiff_inf_self_right, ←@sdiff_inf_self_right _ z y, inf_comm, h, inf_comm]⟩

theorem disjoint.sdiff_eq_left (h : disjoint x y) : x \ y = x :=
by conv_rhs { rw [←sup_inf_sdiff x y, h.eq_bot, bot_sup_eq] }
theorem disjoint.sdiff_eq_right (h : disjoint x y) : y \ x = y := h.symm.sdiff_eq_left

-- cf. `is_compl_bot_top`
@[simp] theorem sdiff_bot : x \ ⊥ = x := disjoint_bot_right.sdiff_eq_left

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

-- cf. `is_compl.antitone`
lemma sdiff_le_sdiff_left (h : z ≤ x) : w \ x ≤ w \ z :=
le_of_inf_le_sup_le
  (calc (w \ x) ⊓ (w ⊓ z) ≤ (w \ x) ⊓ (w ⊓ x) : inf_le_inf le_rfl (inf_le_inf le_rfl h)
              ... = ⊥                         : by rw [inf_comm, inf_inf_sdiff]
              ... ≤ (w \ z) ⊓ (w ⊓ z)         : bot_le)
  (calc w \ x ⊔ (w ⊓ z) ≤ w \ x ⊔ (w ⊓ x)   : sup_le_sup le_rfl (inf_le_inf le_rfl h)
                    ... ≤ w                 : by rw [sup_comm, sup_inf_sdiff]
                    ... = (w \ z) ⊔ (w ⊓ z) : by rw [sup_comm, sup_inf_sdiff])

lemma sdiff_le_iff : y \ x ≤ z ↔ y ≤ x ⊔ z :=
⟨λ h, le_of_inf_le_sup_le
  (le_of_eq
    (calc y ⊓ (y \ x) = y \ x                         : inf_sdiff_right
                  ... = (x ⊓ (y \ x)) ⊔ (z ⊓ (y \ x)) :
                                          by rw [inf_eq_right.2 h, inf_sdiff_self_right, bot_sup_eq]
                  ... = (x ⊔ z) ⊓ (y \ x)             : inf_sup_right.symm))
  (calc y ⊔ y \ x = y                 : sup_sdiff_left
              ... ≤ y ⊔ (x ⊔ z)       : le_sup_left
              ... = ((y \ x) ⊔ x) ⊔ z : by rw [←sup_assoc, ←@sup_sdiff_self_left _ x y]
              ... = x ⊔ z ⊔ y \ x     : by ac_refl),
 λ h, le_of_inf_le_sup_le
  (calc y \ x ⊓ x = ⊥     : inf_sdiff_self_left
              ... ≤ z ⊓ x : bot_le)
  (calc y \ x ⊔ x = y ⊔ x       : sup_sdiff_self_left
              ... ≤ (x ⊔ z) ⊔ x : sup_le_sup_right h x
              ... ≤ z ⊔ x       : by rw [sup_assoc, sup_comm, sup_assoc, sup_idem])⟩

lemma sdiff_sdiff_le : x \ (x \ y) ≤ y := sdiff_le_iff.2 le_sdiff_sup

@[simp] lemma le_sdiff_iff : x ≤ y \ x ↔ x = ⊥ :=
⟨λ h, disjoint_self.1 (disjoint_sdiff_self_right.mono_right h), λ h, h.le.trans bot_le⟩

@[simp] lemma sdiff_eq_bot_iff : y \ x = ⊥ ↔ y ≤ x :=
by rw [←le_bot_iff, sdiff_le_iff, sup_bot_eq]

lemma sdiff_le_comm : x \ y ≤ z ↔ x \ z ≤ y :=
by rw [sdiff_le_iff, sup_comm, sdiff_le_iff]

lemma sdiff_le_sdiff_right (h : w ≤ y) : w \ x ≤ y \ x :=
le_of_inf_le_sup_le
  (calc (w \ x) ⊓ (w ⊓ x) = ⊥                 : by rw [inf_comm, inf_inf_sdiff]
                      ... ≤ (y \ x) ⊓ (w ⊓ x) : bot_le)
  (calc w \ x ⊔ (w ⊓ x) = w                       : by rw [sup_comm, sup_inf_sdiff]
                    ... ≤ (y ⊓ (y \ x)) ⊔ w       : le_sup_right
                    ... = (y ⊓ (y \ x)) ⊔ (y ⊓ w) : by rw inf_eq_right.2 h
                    ... = y ⊓ ((y \ x) ⊔ w)       : by rw inf_sup_left
                    ... = ((y \ x) ⊔ (y ⊓ x)) ⊓ ((y \ x) ⊔ w) :
                                                by rw [@sup_comm _ _ (y \ x) (y ⊓ x), sup_inf_sdiff]
                    ... = (y \ x) ⊔ ((y ⊓ x) ⊓ w) : by rw ←sup_inf_left
                    ... = (y \ x) ⊔ ((w ⊓ y) ⊓ x) : by ac_refl
                    ... = (y \ x) ⊔ (w ⊓ x)       : by rw inf_eq_left.2 h)

theorem sdiff_le_sdiff (h₁ : w ≤ y) (h₂ : z ≤ x) : w \ x ≤ y \ z :=
calc w \ x ≤ w \ z : sdiff_le_sdiff_left h₂
       ... ≤ y \ z : sdiff_le_sdiff_right h₁

lemma sdiff_lt_sdiff_right (h : x < y) (hz : z ≤ x) : x \ z < y \ z :=
(sdiff_le_sdiff_right h.le).lt_of_not_le $ λ h', h.not_le $
  le_sdiff_sup.trans $ sup_le_of_le_sdiff_right h' hz

lemma sup_inf_inf_sdiff : (x ⊓ y) ⊓ z ⊔ (y \ z) = (x ⊓ y) ⊔ (y \ z) :=
calc (x ⊓ y) ⊓ z ⊔ (y \ z) = x ⊓ (y ⊓ z) ⊔ (y \ z) : by rw inf_assoc
                       ... = (x ⊔ (y \ z)) ⊓ y     : by rw [sup_inf_right, sup_inf_sdiff]
                       ... = (x ⊓ y) ⊔ (y \ z)     : by rw [inf_sup_right, inf_sdiff_left]

@[simp] lemma inf_sdiff_sup_left : (x \ z) ⊓ (x ⊔ y) = x \ z :=
by rw [inf_sup_left, inf_sdiff_left, sup_inf_self]
@[simp] lemma inf_sdiff_sup_right : (x \ z) ⊓ (y ⊔ x) = x \ z :=
by rw [sup_comm, inf_sdiff_sup_left]

lemma sdiff_sdiff_right : x \ (y \ z) = (x \ y) ⊔ (x ⊓ y ⊓ z) :=
begin
  rw [sup_comm, inf_comm, ←inf_assoc, sup_inf_inf_sdiff],
  apply sdiff_unique,
  { calc x ⊓ (y \ z) ⊔ (z ⊓ x ⊔ x \ y) =
          (x ⊔ (z ⊓ x ⊔ x \ y)) ⊓ (y \ z ⊔ (z ⊓ x ⊔ x \ y)) : by rw sup_inf_right
    ... = (x ⊔ x ⊓ z ⊔ x \ y) ⊓ (y \ z ⊔ (x ⊓ z ⊔ x \ y))   : by ac_refl
    ... = x ⊓ (y \ z ⊔ x ⊓ z ⊔ x \ y)             : by rw [sup_inf_self, sup_sdiff_left, ←sup_assoc]
    ... = x ⊓ (y \ z ⊓ (z ⊔ y) ⊔ x ⊓ (z ⊔ y) ⊔ x \ y) :
                           by rw [sup_inf_left, sup_sdiff_self_left, inf_sup_right, @sup_comm _ _ y]
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

lemma sdiff_sdiff_left : (x \ y) \ z = x \ (y ⊔ z) :=
begin
  rw sdiff_sup,
  apply sdiff_unique,
  { rw [←inf_sup_left, sup_sdiff_self_right, inf_sdiff_sup_right] },
  { rw [inf_assoc, @inf_comm _ _ z, inf_assoc, inf_sdiff_self_left, inf_bot_eq, inf_bot_eq] }
end

lemma sdiff_sdiff_left' : (x \ y) \ z = (x \ y) ⊓ (x \ z) :=
by rw [sdiff_sdiff_left, sdiff_sup]

lemma sdiff_sdiff_comm : (x \ y) \ z = (x \ z) \ y :=
by rw [sdiff_sdiff_left, sup_comm, sdiff_sdiff_left]

@[simp] lemma sdiff_idem : x \ y \ y = x \ y := by rw [sdiff_sdiff_left, sup_idem]

@[simp] lemma sdiff_sdiff_self : x \ y \ x = ⊥ := by rw [sdiff_sdiff_comm, sdiff_self, bot_sdiff]

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

lemma sup_sdiff : (x ⊔ y) \ z = (x \ z) ⊔ (y \ z) :=
sdiff_unique
  (calc (x ⊔ y) ⊓ z ⊔ (x \ z ⊔ y \ z) =
        (x ⊓ z ⊔ y ⊓ z) ⊔ (x \ z ⊔ y \ z) : by rw inf_sup_right
  ... = x ⊓ z ⊔ x \ z ⊔ y \ z ⊔ y ⊓ z     : by ac_refl
  ... = x ⊔ (y ⊓ z ⊔ y \ z)               : by rw [sup_inf_sdiff, sup_assoc, @sup_comm _ _ (y \ z)]
  ... = x ⊔ y                             : by rw sup_inf_sdiff)
  (calc (x ⊔ y) ⊓ z ⊓ (x \ z ⊔ y \ z) =
        (x ⊓ z ⊔ y ⊓ z) ⊓ (x \ z ⊔ y \ z)                       : by rw inf_sup_right
  ... = (x ⊓ z ⊔ y ⊓ z) ⊓ (x \ z) ⊔ ((x ⊓ z ⊔ y ⊓ z) ⊓ (y \ z)) :
                                                           by rw [@inf_sup_left _ _ (x ⊓ z ⊔ y ⊓ z)]
  ... = (y ⊓ z ⊓ (x \ z)) ⊔ ((x ⊓ z ⊔ y ⊓ z) ⊓ (y \ z)) :
                                                    by rw [inf_sup_right, inf_inf_sdiff, bot_sup_eq]
  ... = (x ⊓ z ⊔ y ⊓ z) ⊓ (y \ z)  : by rw [inf_assoc, inf_sdiff_self_right, inf_bot_eq, bot_sup_eq]
  ... = x ⊓ z ⊓ (y \ z)                           : by rw [inf_sup_right, inf_inf_sdiff, sup_bot_eq]
  ... = ⊥                                     : by rw [inf_assoc, inf_sdiff_self_right, inf_bot_eq])

lemma sup_sdiff_right_self : (x ⊔ y) \ y = x \ y :=
by rw [sup_sdiff, sdiff_self, sup_bot_eq]

lemma sup_sdiff_left_self : (x ⊔ y) \ x = y \ x :=
by rw [sup_comm, sup_sdiff_right_self]

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

lemma sdiff_sup_sdiff_cancel (hyx : y ≤ x) (hzy : z ≤ y) : x \ y ⊔ y \ z = x \ z :=
by rw [←sup_sdiff_inf (x \ z) y, sdiff_sdiff_left, sup_eq_right.2 hzy, inf_sdiff_right_comm,
  inf_eq_right.2 hyx]

lemma sup_eq_sdiff_sup_sdiff_sup_inf : x ⊔ y = (x \ y) ⊔ (y \ x) ⊔ (x ⊓ y) :=
eq.symm $
  calc (x \ y) ⊔ (y \ x) ⊔ (x ⊓ y) =
        ((x \ y) ⊔ (y \ x) ⊔ x) ⊓ ((x \ y) ⊔ (y \ x) ⊔ y)   : by rw sup_inf_left
  ... = ((x \ y) ⊔ x ⊔ (y \ x)) ⊓ ((x \ y) ⊔ ((y \ x) ⊔ y)) : by ac_refl
  ... = (x ⊔ (y \ x)) ⊓ ((x \ y) ⊔ y)                     : by rw [sup_sdiff_right, sup_sdiff_right]
  ... = x ⊔ y                          : by rw [sup_sdiff_self_right, sup_sdiff_self_left, inf_idem]

lemma sdiff_le_sdiff_of_sup_le_sup_left (h : z ⊔ x ≤ z ⊔ y) : x \ z ≤ y \ z :=
begin
  rw [←sup_sdiff_left_self, ←@sup_sdiff_left_self _ _ y],
  exact sdiff_le_sdiff_right h,
end

lemma sdiff_le_sdiff_of_sup_le_sup_right (h : x ⊔ z ≤ y ⊔ z) : x \ z ≤ y \ z :=
begin
  rw [←sup_sdiff_right_self, ←@sup_sdiff_right_self _ y],
  exact sdiff_le_sdiff_right h,
end

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


/-- Set / lattice complement -/
@[notation_class] class has_compl (α : Type*) := (compl : α → α)

export has_compl (compl)

postfix `ᶜ`:(max+1) := compl

/-- This class contains the core axioms of a Boolean algebra. The `boolean_algebra` class extends
both this class and `generalized_boolean_algebra`, see Note [forgetful inheritance].

Since `bounded_order`, `order_bot`, and `order_top` are mixins that require `has_le`
to be present at define-time, the `extends` mechanism does not work with them.
Instead, we extend using the underlying `has_bot` and `has_top` data typeclasses, and replicate the
order axioms of those classes here. A "forgetful" instance back to `bounded_order` is provided.
-/
class boolean_algebra.core (α : Type u) extends distrib_lattice α, has_compl α,
  has_top α, has_bot α :=
(inf_compl_le_bot : ∀x:α, x ⊓ xᶜ ≤ ⊥)
(top_le_sup_compl : ∀x:α, ⊤ ≤ x ⊔ xᶜ)
(le_top : ∀ a : α, a ≤ ⊤)
(bot_le : ∀ a : α, ⊥ ≤ a)

@[priority 100]  -- see Note [lower instance priority]
instance boolean_algebra.core.to_bounded_order [h : boolean_algebra.core α] : bounded_order α :=
{ ..h }

section boolean_algebra_core
variables [boolean_algebra.core α]

@[simp] theorem inf_compl_eq_bot : x ⊓ xᶜ = ⊥ :=
bot_unique $ boolean_algebra.core.inf_compl_le_bot x

@[simp] theorem compl_inf_eq_bot : xᶜ ⊓ x = ⊥ :=
eq.trans inf_comm inf_compl_eq_bot

@[simp] theorem sup_compl_eq_top : x ⊔ xᶜ = ⊤ :=
top_unique $ boolean_algebra.core.top_le_sup_compl x

@[simp] theorem compl_sup_eq_top : xᶜ ⊔ x = ⊤ :=
eq.trans sup_comm sup_compl_eq_top

theorem is_compl_compl : is_compl x xᶜ :=
is_compl.of_eq inf_compl_eq_bot sup_compl_eq_top

theorem is_compl.eq_compl (h : is_compl x y) : x = yᶜ :=
h.left_unique is_compl_compl.symm

theorem is_compl.compl_eq (h : is_compl x y) : xᶜ = y :=
(h.right_unique is_compl_compl).symm

theorem eq_compl_iff_is_compl : x = yᶜ ↔ is_compl x y :=
⟨λ h, by { rw h, exact is_compl_compl.symm }, is_compl.eq_compl⟩

theorem compl_eq_iff_is_compl : xᶜ = y ↔ is_compl x y :=
⟨λ h, by { rw ←h, exact is_compl_compl }, is_compl.compl_eq⟩

theorem disjoint_compl_right : disjoint x xᶜ := is_compl_compl.disjoint
theorem disjoint_compl_left : disjoint xᶜ x := disjoint_compl_right.symm

theorem compl_unique (i : x ⊓ y = ⊥) (s : x ⊔ y = ⊤) : xᶜ = y :=
(is_compl.of_eq i s).compl_eq

@[simp] theorem compl_top : ⊤ᶜ = (⊥:α) :=
is_compl_top_bot.compl_eq

@[simp] theorem compl_bot : ⊥ᶜ = (⊤:α) :=
is_compl_bot_top.compl_eq

@[simp] theorem compl_compl (x : α) : xᶜᶜ = x :=
is_compl_compl.symm.compl_eq

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

@[simp] theorem compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ :=
(is_compl_compl.inf_sup is_compl_compl).compl_eq

@[simp] theorem compl_sup : (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ :=
(is_compl_compl.sup_inf is_compl_compl).compl_eq

theorem compl_le_compl (h : y ≤ x) : xᶜ ≤ yᶜ :=
is_compl_compl.antitone is_compl_compl h

@[simp] theorem compl_le_compl_iff_le : yᶜ ≤ xᶜ ↔ x ≤ y :=
⟨assume h, by have h := compl_le_compl h; simp at h; assumption,
  compl_le_compl⟩

theorem le_compl_of_le_compl (h : y ≤ xᶜ) : x ≤ yᶜ :=
by simpa only [compl_compl] using compl_le_compl h

theorem compl_le_of_compl_le (h : yᶜ ≤ x) : xᶜ ≤ y :=
by simpa only [compl_compl] using compl_le_compl h

theorem le_compl_iff_le_compl : y ≤ xᶜ ↔ x ≤ yᶜ :=
⟨le_compl_of_le_compl, le_compl_of_le_compl⟩

theorem compl_le_iff_compl_le : xᶜ ≤ y ↔ yᶜ ≤ x :=
⟨compl_le_of_compl_le, compl_le_of_compl_le⟩

namespace boolean_algebra

@[priority 100]
instance : is_complemented α := ⟨λ x, ⟨xᶜ, is_compl_compl⟩⟩

end boolean_algebra

end boolean_algebra_core

/-- A Boolean algebra is a bounded distributive lattice with
a complement operator `ᶜ` such that `x ⊓ xᶜ = ⊥` and `x ⊔ xᶜ = ⊤`.
For convenience, it must also provide a set difference operation `\`
satisfying `x \ y = x ⊓ yᶜ`.

This is a generalization of (classical) logic of propositions, or
the powerset lattice. -/
-- Lean complains about metavariables in the type if the universe is not specified
class boolean_algebra (α : Type u) extends generalized_boolean_algebra α, boolean_algebra.core α :=
(sdiff_eq : ∀x y:α, x \ y = x ⊓ yᶜ)
-- TODO: is there a way to automatically fill in the proofs of sup_inf_sdiff and inf_inf_sdiff given
-- everything in `boolean_algebra.core` and `sdiff_eq`? The following doesn't work:
-- (sup_inf_sdiff := λ a b, by rw [sdiff_eq, ←inf_sup_left, sup_compl_eq_top, inf_top_eq])


section of_core

/-- Create a `has_sdiff` instance from a `boolean_algebra.core` instance, defining `x \ y` to
be `x ⊓ yᶜ`.

For some types, it may be more convenient to create the `boolean_algebra` instance by hand in order
to have a simpler `sdiff` operation.

See note [reducible non-instances]. -/
@[reducible]
def boolean_algebra.core.sdiff [boolean_algebra.core α] : has_sdiff α := ⟨λ x y, x ⊓ yᶜ⟩

local attribute [instance] boolean_algebra.core.sdiff

lemma boolean_algebra.core.sdiff_eq [boolean_algebra.core α] (a b : α) :
  a \ b = a ⊓ bᶜ := rfl

/-- Create a `boolean_algebra` instance from a `boolean_algebra.core` instance, defining `x \ y` to
be `x ⊓ yᶜ`.

For some types, it may be more convenient to create the `boolean_algebra` instance by hand in order
to have a simpler `sdiff` operation. -/
def boolean_algebra.of_core (B : boolean_algebra.core α) :
  boolean_algebra α :=
{ sdiff := λ x y, x ⊓ yᶜ,
  sdiff_eq := λ _ _, rfl,
  sup_inf_sdiff := λ a b, by rw [←inf_sup_left, sup_compl_eq_top, inf_top_eq],
  inf_inf_sdiff := λ a b, by { rw [inf_left_right_swap, boolean_algebra.core.sdiff_eq,
    @inf_assoc _ _ _ _ b, compl_inf_eq_bot, inf_bot_eq, bot_inf_eq], congr },
  ..B }

end of_core

section boolean_algebra
variables [boolean_algebra α]

--TODO@Yaël: Once we have co-Heyting algebras, we won't need to go through `boolean_algebra.of_core`
instance : boolean_algebra αᵒᵈ :=
boolean_algebra.of_core
{ compl := λ a, to_dual (of_dual a)ᶜ,
  inf_compl_le_bot := λ _, sup_compl_eq_top.ge,
  top_le_sup_compl := λ _, inf_compl_eq_bot.ge,
  ..order_dual.distrib_lattice α, ..order_dual.bounded_order α }

@[simp] lemma of_dual_compl (a : αᵒᵈ) : of_dual aᶜ = (of_dual a)ᶜ := rfl
@[simp] lemma to_dual_compl (a : α) : to_dual aᶜ = (to_dual a)ᶜ := rfl

theorem sdiff_eq : x \ y = x ⊓ yᶜ := boolean_algebra.sdiff_eq x y

@[simp] theorem sdiff_compl : x \ yᶜ = x ⊓ y := by rw [sdiff_eq, compl_compl]

@[simp] theorem top_sdiff : ⊤ \ x = xᶜ := by rw [sdiff_eq, top_inf_eq]
@[simp] theorem sdiff_top : x \ ⊤ = ⊥ := by rw [sdiff_eq, compl_top, inf_bot_eq]

@[simp] lemma sup_inf_inf_compl : (x ⊓ y) ⊔ (x ⊓ yᶜ) = x :=
by rw [← sdiff_eq, sup_inf_sdiff _ _]

@[simp] lemma compl_sdiff : (x \ y)ᶜ = xᶜ ⊔ y :=
by rw [sdiff_eq, compl_inf, compl_compl]

end boolean_algebra

instance Prop.boolean_algebra : boolean_algebra Prop :=
boolean_algebra.of_core
{ compl := not,
  inf_compl_le_bot := λ p ⟨Hp, Hpc⟩, Hpc Hp,
  top_le_sup_compl := λ p H, classical.em p,
  .. Prop.distrib_lattice,
  .. Prop.bounded_order }

instance pi.has_sdiff {ι : Type u} {α : ι → Type v} [∀ i, has_sdiff (α i)] :
  has_sdiff (Π i, α i) :=
⟨λ x y i, x i \ y i⟩

lemma pi.sdiff_def {ι : Type u} {α : ι → Type v} [∀ i, has_sdiff (α i)] (x y : Π i, α i) :
  (x \ y) = λ i, x i \ y i := rfl

@[simp]
lemma pi.sdiff_apply {ι : Type u} {α : ι → Type v} [∀ i, has_sdiff (α i)] (x y : Π i, α i) (i : ι) :
  (x \ y) i = x i \ y i := rfl

instance pi.has_compl {ι : Type u} {α : ι → Type v} [∀ i, has_compl (α i)] :
  has_compl (Π i, α i) :=
⟨λ x i, (x i)ᶜ⟩

lemma pi.compl_def {ι : Type u} {α : ι → Type v} [∀ i, has_compl (α i)] (x : Π i, α i) :
  xᶜ = λ i, (x i)ᶜ := rfl

@[simp]
lemma pi.compl_apply {ι : Type u} {α : ι → Type v} [∀ i, has_compl (α i)] (x : Π i, α i) (i : ι)  :
  xᶜ i = (x i)ᶜ := rfl

instance pi.boolean_algebra {ι : Type u} {α : ι → Type v} [∀ i, boolean_algebra (α i)] :
  boolean_algebra (Π i, α i) :=
{ sdiff_eq := λ x y, funext $ λ i, sdiff_eq,
  sup_inf_sdiff := λ x y, funext $ λ i, sup_inf_sdiff (x i) (y i),
  inf_inf_sdiff := λ x y, funext $ λ i, inf_inf_sdiff (x i) (y i),
  inf_compl_le_bot := λ _ _, boolean_algebra.inf_compl_le_bot _,
  top_le_sup_compl := λ _ _, boolean_algebra.top_le_sup_compl _,
  .. pi.has_sdiff,
  .. pi.has_compl,
  .. pi.bounded_order,
  .. pi.distrib_lattice }

instance : boolean_algebra bool := boolean_algebra.of_core
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

section lift

/-- Pullback a `generalized_boolean_algebra` along an injection. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.generalized_boolean_algebra [has_sup α] [has_inf α] [has_bot α]
  [has_sdiff α] [generalized_boolean_algebra β] (f : α → β) (hf : injective f)
  (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
  (map_bot : f ⊥ = ⊥) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
  generalized_boolean_algebra α :=
{ sdiff := (\),
  bot := ⊥,
  sup_inf_sdiff := λ a b, hf $ (map_sup _ _).trans begin
    rw map_sdiff,
    convert sup_inf_sdiff _ _,
    exact map_inf _ _,
  end,
  inf_inf_sdiff := λ a b, hf $ (map_inf _ _).trans begin
    rw map_sdiff,
    convert inf_inf_sdiff _ _,
    exact map_inf _ _,
  end,
  le_sup_inf := λ a b c, (map_inf _ _).le.trans $ by { convert le_sup_inf, exact map_sup _ _,
    exact map_sup _ _, convert map_sup _ _, exact (map_inf _ _).symm },
  ..hf.lattice f map_sup map_inf }

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
