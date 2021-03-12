/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bryan Gin-ge Chen
-/
import order.bounded_lattice
/-!
# (Generalized) Boolean algebras

A Boolean algebra is a bounded distributive lattice with a complement operator. Boolean algebras
generalize the (classical) logic of propositions and the lattice of subsets of a set.

A generalized Boolean algebra less familiar, but it is essentially a Boolean algebra which does not
necessarily have a top element (`⊤`) (and hence not all elements may have complements). It is
defined here as a distributive lattice with bottom (`⊥`) admitting a *relative* complement operator,
written using "set difference" notation as `x \ y`.

For convenience, the `boolean_algebra` type class is defined to extend `generalized_boolean_algebra`
so that it is also bundled with a `\` operator.

## Main declarations

* `has_compl`: a type class for the complement operator
* `generalized_boolean_algebra`: a type class for generalized Boolean algebras
* `boolean_algebra.core`: a type class with the minimal assumptions for a Boolean algebras
* `boolean_algebra`: the main type class for Boolean algebras; it extends both
  `generalized_boolean_algebra` and `boolean_algebra.core`. An instance of `boolean_algebra` can be
  obtained from one of `boolean_algebra.core` using `boolean_algebra.of_core`.
* `boolean_algebra_Prop`: the Boolean algebra instance on `Prop`

## Notations

* `xᶜ` is notation for `compl x`
* `x \ y` is notation for `sdiff x y`.

## Tags

generalized Boolean algebras, Boolean algebras, lattices, sdiff, compl

-/
set_option old_structure_cmd true

universes u v
variables {α : Type u} {w x y z : α}

/-!
### Generalized Boolean algebras

Sectionally complemented
-/

export has_sdiff (sdiff)

/-- A generalized Boolean algebra is a distributive lattice with `⊥`
and a set difference operation `\` satisfying `(a ⊓ b) ⊔ (a \ b) = a`
and `(a ⊓ b) ⊓ (a \ b) = b`, i.e. `a \ b` is the complement of `b` in
`a`.

This is a generalization of Boolean algebras which applies to `finset α`
for arbitrary (not-necessarily-`fintype`) `α`. -/
class generalized_boolean_algebra (α : Type u) extends semilattice_sup_bot α, semilattice_inf_bot α,
  distrib_lattice α, has_sdiff α :=
(sup_inf_sdiff : ∀a b:α, (a ⊓ b) ⊔ (a \ b) = a)
(inf_inf_sdiff : ∀a b:α, (a ⊓ b) ⊓ (a \ b) = ⊥)

-- We might want a `is_compl_of` predicate generalizing `is_compl`,
-- however we'd need another type class for lattices with bot, and all the API for that.

section generalized_boolean_algebra
variables [generalized_boolean_algebra α]

@[simp] theorem sup_inf_sdiff (x y : α) : (x ⊓ y) ⊔ (x \ y) = x :=
generalized_boolean_algebra.sup_inf_sdiff _ _
@[simp] theorem inf_inf_sdiff (x y : α) : (x ⊓ y) ⊓ (x \ y) = ⊥ :=
generalized_boolean_algebra.inf_inf_sdiff _ _

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

theorem sdiff_symm (hy : y ≤ x) (hz : z ≤ x) (H : x \ y = z) : x \ z = y :=
have hyi : x ⊓ y = y := inf_eq_right.2 hy,
have hzi : x ⊓ z = z := inf_eq_right.2 hz,
eq_of_inf_eq_sup_eq
  (begin
    have ixy := inf_inf_sdiff x y,
    rw [H, hyi] at ixy,
    have ixz := inf_inf_sdiff x z,
    rwa [hzi, inf_comm, ←ixy] at ixz,
  end)
  (begin
    have sxz := sup_inf_sdiff x z,
    rw [hzi, sup_comm] at sxz,
    rw sxz,
    symmetry,
    have sxy := sup_inf_sdiff x y,
    rwa [H, hyi] at sxy,
  end)

lemma sdiff_le : x \ y ≤ x :=
calc x \ y ≤ (x ⊓ y) ⊔ (x \ y) : le_sup_right
       ... = x                 : sup_inf_sdiff x y

@[simp] lemma bot_sdiff : ⊥ \ x = ⊥ := le_bot_iff.1 sdiff_le

lemma inf_sdiff_right : x ⊓ (x \ y) = x \ y := by rw [inf_of_le_right (@sdiff_le _ x y _)]
lemma inf_sdiff_left : (x \ y) ⊓ x = x \ y := by rw [inf_comm, inf_sdiff_right]

-- cf. `is_compl_top_bot`
@[simp] lemma sdiff_self : x \ x = ⊥ :=
by rw [←inf_inf_sdiff, inf_idem, inf_of_le_right (@sdiff_le _ x x _)]

@[simp] theorem sup_sdiff_same_right : x ⊔ (y \ x) = x ⊔ y :=
calc x ⊔ (y \ x) = (x ⊔ (x ⊓ y)) ⊔ (y \ x) : by rw sup_inf_self
             ... = x ⊔ ((y ⊓ x) ⊔ (y \ x)) : by ac_refl
             ... = x ⊔ y                   : by rw sup_inf_sdiff

@[simp] theorem sup_sdiff_same_left : (y \ x) ⊔ x = y ⊔ x :=
by rw [sup_comm, sup_sdiff_same_right, sup_comm]

/--
Grätzer 2011, I.6.1
-/
lemma sup_sdiff_of_le (h : x ≤ y) : x ⊔ (y \ x) = y :=
by conv_rhs { rw [←sup_inf_sdiff y x, inf_eq_right.2 h] }

@[simp] lemma sup_sdiff_left : x ⊔ (x \ y) = x := by { rw [sup_eq_left], exact sdiff_le }
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

/--
Cf. <https://ncatlab.org/nlab/show/relative+complement>
-/
theorem le_sup_sdiff : y ≤ x ⊔ (y \ x) :=
by { rw [sup_sdiff_same_right], exact le_sup_right }

@[simp] theorem inf_sdiff_same_right : x ⊓ (y \ x) = ⊥ :=
calc x ⊓ (y \ x) = ((x ⊓ y) ⊔ (x \ y)) ⊓ (y \ x)         : by rw sup_inf_sdiff
             ... = (x ⊓ y) ⊓ (y \ x) ⊔ (x \ y) ⊓ (y \ x) : by rw inf_sup_right
             ... = ⊥         : by rw [@inf_comm _ _ x y, inf_inf_sdiff, sdiff_inf_sdiff, bot_sup_eq]
@[simp] theorem inf_sdiff_same_left : (y \ x) ⊓ x = ⊥ := by rw [inf_comm, inf_sdiff_same_right]

theorem disjoint_sdiff : disjoint x (y \ x) := inf_sdiff_same_right.le

/-- <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations> -/
theorem exist_rel_complements (h : x ≤ y) : ∃ z, x ⊓ z = ⊥ ∧ x ⊔ z = y :=
⟨y \ x, ⟨inf_sdiff_same_right, sup_sdiff_of_le h⟩⟩

/-- <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations>

Could potentially make an alternative constructor with this as an axiom if we had a typeclasses for
distributive lattices with bot? -/
theorem disjoint.sdiff_eq_of_sup_eq (hi : disjoint x z) (hs : x ⊔ z = y) : y \ x = z :=
have h : y ⊓ x = x := inf_eq_right.2 $ le_sup_left.trans hs.le,
sdiff_unique (by rw [h, hs]) (by rw [h, hi.eq_bot])

/-- Cf. <https://ncatlab.org/nlab/show/relative+complement> -/
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
      rw sup_sdiff_of_le hx,
      refine le_trans (sup_le_sup_left sdiff_le z) _,
      rw sup_eq_right.2 hz,
    end),
 λ H, disjoint_sdiff.mono_left H⟩

-- cf. `is_compl.le_left_iff` and `is_compl.le_right_iff`
lemma le_iff_disjoint_sdiff (hz : z ≤ y) (hx : x ≤ y) : z ≤ x ↔ disjoint z (y \ x) :=
(disjoint_sdiff_iff_le hz hx).symm

-- cf. `is_compl.inf_left_eq_bot_iff` and `is_compl.inf_right_eq_bot_iff`
lemma inf_sdiff_eq_bot_iff (hz : z ≤ y) (hx : x ≤ y) : z ≤ x ↔ z ⊓ (y \ x) = ⊥ :=
by { rw ←disjoint_iff, exact le_iff_disjoint_sdiff hz hx }

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
    conv_lhs at H { rw ←sup_sdiff_of_le hx, },
    refine le_of_inf_le_sup_le _ H.le,
    rw inf_sdiff_same_right,
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

-- cf. `is_compl.inf_sup`
lemma sdiff_inf : y \ (x ⊓ z) = y \ x ⊔ y \ z :=
sdiff_unique
  (calc y ⊓ (x ⊓ z) ⊔ (y \ x ⊔ y \ z) =
        (z ⊓ (y ⊓ x)) ⊔ (y \ x ⊔ y \ z)                     : by ac_refl
  ... = (z ⊔ (y \ x ⊔ y \ z)) ⊓ ((y ⊓ x) ⊔ (y \ x ⊔ y \ z)) : by rw sup_inf_right
  ... = (y \ x ⊔ (y \ z ⊔ z)) ⊓ (y ⊓ x ⊔ (y \ x ⊔ y \ z))   : by ac_refl
  ... = (y ⊔ z) ⊓ ((y ⊓ x) ⊔ (y \ x ⊔ y \ z)) :
                                            by rw [sup_sdiff_same_left, ←sup_assoc, sup_sdiff_right]
  ... = (y ⊔ z) ⊓ y                              : by rw [←sup_assoc, sup_inf_sdiff, sup_sdiff_left]
  ... = y                                                          : by rw [inf_comm, inf_sup_self])
  (calc y ⊓ (x ⊓ z) ⊓ ((y \ x) ⊔ (y \ z)) =
        (y ⊓ (x ⊓ z) ⊓ (y \ x)) ⊔ (y ⊓ (x ⊓ z) ⊓ (y \ z)) : by rw inf_sup_left
  ... = z ⊓ (y ⊓ x ⊓ (y \ x)) ⊔ z ⊓ (y ⊓ x) ⊓ (y \ z)     : by ac_refl
  ... = z ⊓ (y ⊓ x) ⊓ (y \ z)                        : by rw [inf_inf_sdiff, inf_bot_eq, bot_sup_eq]
  ... = x ⊓ ((y ⊓ z) ⊓ (y \ z))                           : by ac_refl
  ... = ⊥                                                 : by rw [inf_inf_sdiff, inf_bot_eq])

@[simp] lemma sdiff_inf_same_right : y \ (x ⊓ y) = y \ x :=
by rw [sdiff_inf, sdiff_self, sup_bot_eq]
@[simp] lemma sdiff_inf_same_left : y \ (y ⊓ x) = y \ x := by rw [inf_comm, sdiff_inf_same_right]

theorem disjoint.sdiff_eq_left (h : disjoint x y) : x \ y = x :=
by conv_rhs { rw [←sup_inf_sdiff x y, h.eq_bot, bot_sup_eq] }
theorem disjoint.sdiff_eq_right (h : disjoint x y) : y \ x = y := h.symm.sdiff_eq_left

-- cf. `is_compl_bot_top`
@[simp] theorem sdiff_bot : x \ ⊥ = x := disjoint_bot_right.sdiff_eq_left

-- cf. `is_compl.antimono`
lemma sdiff_le_sdiff_same (h : z ≤ x) : w \ x ≤ w \ z :=
le_of_inf_le_sup_le
  (calc (w \ x) ⊓ (w ⊓ z) ≤ (w \ x) ⊓ (w ⊓ x) : inf_le_inf le_rfl (inf_le_inf le_rfl h)
              ... = ⊥                         : by rw [inf_comm, inf_inf_sdiff]
              ... ≤ (w \ z) ⊓ (w ⊓ z)         : bot_le)
  (calc w \ x ⊔ (w ⊓ z) ≤ w \ x ⊔ (w ⊓ x)   : sup_le_sup le_rfl (inf_le_inf le_rfl h)
                    ... ≤ w                 : by rw [sup_comm, sup_inf_sdiff]
                    ... = (w \ z) ⊔ (w ⊓ z) : by rw [sup_comm, sup_inf_sdiff])

lemma sdiff_le_same_sdiff (h : w ≤ y) : w \ x ≤ y \ x :=
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
calc w \ x ≤ w \ z : sdiff_le_sdiff_same h₂
       ... ≤ y \ z : sdiff_le_same_sdiff h₁

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
  { rw [sup_inf_right, ←sup_assoc, @inf_comm _ _ z, sup_inf_self, sup_sdiff_left, ←sup_assoc,
      sup_inf_left, sup_sdiff_same_left, inf_sup_right, @sup_comm _ _ y, inf_sdiff_sup_right,
      @inf_sup_left _ _ x z y, sup_assoc, sup_assoc, sup_inf_sdiff, @sup_comm _ _ (x ⊓ z),
      sup_inf_self, sup_comm, inf_sup_self], },
  { rw [inf_sup_left, inf_assoc, ←@inf_assoc _ _ (y \ z), inf_sdiff_same_left, bot_inf_eq,
      inf_bot_eq, bot_sup_eq, ←inf_sdiff_left, inf_assoc, inf_assoc, inf_sdiff_same_right,
      inf_bot_eq, inf_bot_eq], }
end

@[simp] lemma sdiff_sdiff_right_same : x \ (x \ y) = x ⊓ y :=
by rw [sdiff_sdiff_right, inf_idem, sdiff_self, bot_sup_eq]

lemma sdiff_sdiff_eq_self (h : y ≤ x) : x \ (x \ y) = y :=
by rw [sdiff_sdiff_right_same, inf_of_le_right h]

lemma sdiff_sdiff_left : (x \ y) \ z = x \ (y ⊔ z) :=
begin
  rw sdiff_sup,
  apply sdiff_unique,
  { rw [←inf_sup_left, sup_sdiff_same_right, inf_sdiff_sup_right] },
  { rw [inf_assoc, @inf_comm _ _ z, inf_assoc, inf_sdiff_same_left, inf_bot_eq, inf_bot_eq] }
end

@[simp] lemma sdiff_idem : x \ y \ y = x \ y := by rw [sdiff_sdiff_left, sup_idem]

lemma sdiff_sdiff_sup_sdiff : z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) :=
begin
  rw [sdiff_sup, sdiff_sdiff_right, sdiff_sdiff_right,
    sup_inf_left, sup_comm, sup_inf_sdiff,
    sup_inf_left,  @sup_comm _ _ (z \ y), sup_inf_sdiff,
    inf_assoc, ←@inf_assoc _ _ (z \ x ⊔ y), @inf_comm _ _ _ z, ←inf_assoc, ←inf_assoc, inf_idem],
end

lemma sdiff_sdiff_sup_sdiff' : z \ (x \ y ⊔ y \ x) = z ⊓ x ⊓ y ⊔ ((z \ x) ⊓ (z \ y)):=
begin
  rw [sdiff_sup, sdiff_sdiff_right, sdiff_sdiff_right, inf_assoc, @inf_comm _ _ x, ←inf_assoc,
    ←sup_inf_right, sup_comm],
end

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
  ... = (x ⊓ z ⊔ y ⊓ z) ⊓ (y \ z)  : by rw [inf_assoc, inf_sdiff_same_right, inf_bot_eq, bot_sup_eq]
  ... = x ⊓ z ⊓ (y \ z)                           : by rw [inf_sup_right, inf_inf_sdiff, sup_bot_eq]
  ... = ⊥                                     : by rw [inf_assoc, inf_sdiff_same_right, inf_bot_eq])

lemma inf_sdiff : (x ⊓ y) \ z = (x \ z) ⊓ (y \ z) :=
sdiff_unique
  (calc (x ⊓ y) ⊓ z ⊔ ((x \ z) ⊓ (y \ z)) =
        ((x ⊓ y) ⊓ z ⊔ (x \ z)) ⊓ ((x ⊓ y) ⊓ z ⊔ (y \ z)) : by rw [sup_inf_left]
  ... = (x ⊓ y ⊓ (z ⊔ x) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) :
                     by rw [sup_inf_right, sup_sdiff_same_right, inf_sup_right, inf_sdiff_sup_right]
  ... = (y ⊓ (x ⊓ (x ⊔ z)) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) : by ac_refl
  ... = ((y ⊓ x) ⊔ (x \ z)) ⊓ ((x ⊓ y) ⊔ (y \ z))         : by rw [inf_sup_self, sup_inf_inf_sdiff]
  ... = (x ⊓ y) ⊔ ((x \ z) ⊓ (y \ z))                     : by rw [@inf_comm _ _ y, sup_inf_left]
  ... = x ⊓ y                                        : sup_eq_left.2 (inf_le_inf sdiff_le sdiff_le))
  (calc (x ⊓ y) ⊓ z ⊓ ((x \ z) ⊓ (y \ z)) =
        x ⊓ y ⊓ (z ⊓ (x \ z)) ⊓ (y \ z) : by ac_refl
  ... = ⊥                               : by rw [inf_sdiff_same_right, inf_bot_eq, bot_inf_eq])

instance pi.generalized_boolean_algebra {α : Type u} {β : Type v} [generalized_boolean_algebra β] :
  generalized_boolean_algebra (α → β) :=
by pi_instance

end generalized_boolean_algebra

/-!
### Boolean algebras
-/


/-- Set / lattice complement -/
class has_compl (α : Type*) := (compl : α → α)

export has_compl (compl)

postfix `ᶜ`:(max+1) := compl

/-- This class contains the core axioms of a Boolean algebra. The `boolean_algebra` class extends
both this class and `generalized_boolean_algebra`, see Note [forgetful inheritance]. -/
class boolean_algebra.core (α : Type u) extends bounded_distrib_lattice α, has_compl α :=
(inf_compl_le_bot : ∀x:α, x ⊓ xᶜ ≤ ⊥)
(top_le_sup_compl : ∀x:α, ⊤ ≤ x ⊔ xᶜ)

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

theorem is_compl.compl_eq (h : is_compl x y) : xᶜ = y :=
(h.right_unique is_compl_compl).symm

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

theorem compl_injective : function.injective (compl : α → α) :=
function.involutive.injective compl_compl

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
is_compl_compl.antimono is_compl_compl h

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

/-- Create a `boolean_algebra` instance from a `boolean_algebra.core` instance, defining `x \ y` to
be `x ⊓ yᶜ`.

For some types, it may be more convenient to create the `boolean_algebra` instance by hand in order
to have a simpler `sdiff` operation. -/
def boolean_algebra.of_core (B : boolean_algebra.core α) :
  boolean_algebra α :=
{ sdiff := λ x y, x ⊓ yᶜ,
  sdiff_eq := λ _ _, rfl,
  sup_inf_sdiff := λ a b, by rw [←inf_sup_left, sup_compl_eq_top, inf_top_eq],
  inf_inf_sdiff := λ a b, by rw [inf_left_right_swap, @inf_assoc _ _ a, compl_inf_eq_bot,
    inf_bot_eq, bot_inf_eq],
  ..B }

section boolean_algebra
variables [boolean_algebra α]

theorem sdiff_eq : x \ y = x ⊓ yᶜ := boolean_algebra.sdiff_eq x y

theorem top_sdiff : ⊤ \ x = xᶜ := by rw [sdiff_eq, top_inf_eq]
@[simp] theorem sdiff_top : x \ ⊤ = ⊥ := by rw [sdiff_eq, compl_top, inf_bot_eq]

end boolean_algebra

instance boolean_algebra_Prop : boolean_algebra Prop :=
boolean_algebra.of_core
{ compl := not,
  inf_compl_le_bot := λ p ⟨Hp, Hpc⟩, Hpc Hp,
  top_le_sup_compl := λ p H, classical.em p,
  .. bounded_distrib_lattice_Prop }

instance pi.boolean_algebra {α : Type u} {β : Type v} [boolean_algebra β] :
  boolean_algebra (α → β) :=
by pi_instance
