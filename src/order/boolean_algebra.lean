/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.bounded_lattice
/-!
# (Generalized) Boolean algebras

A generalized Boolean algebra is a distributive lattice admitting a relative complement operator,
written using "set difference" notation `x \ y`.

A Boolean algebra is a bounded distributive lattice with a complement operator. Boolean algebras
generalize the (classical) logic of propositions and the lattice of subsets of a set.

For convenience, the `boolean_algebra` type class is also bundled with a set difference operator
`sdiff`, written `\`.

## Main declarations

* `has_compl`: a type class for the complement operator
* `boolean_algebra`: a type class for Boolean algebras
* `boolean_algebra_Prop`: the Boolean algebra instance on `Prop`

## Notations

* `xᶜ` is notation for `compl x`
* `x \ y` is notation for `sdiff x y`.

## Tags

Boolean algebras, lattices

-/
set_option old_structure_cmd true

universes u v
variables {α : Type u} {w x y z : α}

/-!
### Generalized Boolean algebras

Sectionally complemented
-/

/-- A generalized Boolean algebra is a distributive lattice with `⊥`
and a set difference operation `\` satisfying `(a ⊓ b) ⊔ (a \ b) = a`
and `(a ⊓ b) ⊓ (a \ b) = b`, i.e. `a \ b` is the complement of `b` in
`a`.

This is a generalization of Boolean algebras which applies to `finset α`
for arbitrary (not-necessarily-`fintype`) `α`. -/
class generalized_boolean_algebra α extends distrib_lattice α, order_bot α, has_sdiff α :=
(sup_inf_sdiff : ∀a b:α, (a ⊓ b) ⊔ (a \ b) = a)
(inf_inf_sdiff : ∀a b:α, (a ⊓ b) ⊓ (a \ b) = ⊥)

-- We might want a `is_compl_of` predicate generalizing `is_compl`,
-- however we'd need another type class for lattices with bot, and all the API for that.

section generalized_boolean_algebra
variables [generalized_boolean_algebra α]

namespace generalized_boolean_algebra

@[priority 100]
instance : semilattice_sup_bot α := { .. (infer_instance : generalized_boolean_algebra α) }
@[priority 100]
instance : semilattice_inf_bot α := { .. (infer_instance : generalized_boolean_algebra α) }

end generalized_boolean_algebra

theorem sup_inf_sdiff (x y : α) : (x ⊓ y) ⊔ (x \ y) = x :=
generalized_boolean_algebra.sup_inf_sdiff _ _
theorem inf_inf_sdiff (x y : α) : (x ⊓ y) ⊓ (x \ y) = ⊥ :=
generalized_boolean_algebra.inf_inf_sdiff _ _

theorem disjoint_inf_sdiff : disjoint (x ⊓ y) (x \ y) := (inf_inf_sdiff x y).le

-- TODO: in distributive lattices, relative complements are unique when they exist
theorem sdiff_unique (s : (x ⊓ y) ⊔ z = x) (i : (x ⊓ y) ⊓ z = ⊥) : x \ y = z :=
begin
  conv_rhs at s { rw [←sup_inf_sdiff x y, sup_comm] },
  conv_rhs at i { rw [←inf_inf_sdiff x y, inf_comm] },
  rw [sup_comm] at s,
  rw [inf_comm] at i,
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

lemma inf_sdiff_right : x ⊓ (x \ y) = x \ y := by rw [inf_of_le_right (@sdiff_le _ x y _)]
lemma inf_sdiff_left : (x \ y) ⊓ x = x \ y := by rw [inf_comm, inf_sdiff_right]

lemma sdiff_self : x \ x = ⊥ :=
by rw [←inf_inf_sdiff x x, inf_idem, inf_of_le_right (@sdiff_le _ x x _)]
-- lemma is_compl_top_bot [bounded_lattice α] : is_compl (⊤ : α) ⊥ :=
-- is_compl.of_eq inf_bot_eq top_sup_eq

theorem sup_sdiff_same_right : x ⊔ (y \ x) = x ⊔ y :=
calc x ⊔ (y \ x) = (x ⊔ (x ⊓ y)) ⊔ (y \ x) : by rw sup_inf_self
             ... = x ⊔ ((y ⊓ x) ⊔ (y \ x)) : by rw [sup_assoc, inf_comm]
             ... = x ⊔ y                   : by rw sup_inf_sdiff

theorem sup_sdiff_same_left : (y \ x) ⊔ x = y ⊔ x :=
by rw [sup_comm, sup_sdiff_same_right, sup_comm]

/--
Grätzer 2011, I.6.1
-/
lemma sup_sdiff_of_le (h : x ≤ y) : x ⊔ (y \ x) = y :=
by conv_rhs { rw [←sup_inf_sdiff y x, inf_eq_right.2 h] }

lemma sup_sdiff_left : x ⊔ (x \ y) = x := by { rw [sup_eq_left], exact sdiff_le }
lemma sup_sdiff_right : (x \ y) ⊔ x = x := by rw [sup_comm, sup_sdiff_left]

lemma sdiff_inf_sdiff : x \ y ⊓ (y \ x) = ⊥ :=
eq.symm $
  calc ⊥ = (x ⊓ y) ⊓ (x \ y)                           : by rw inf_inf_sdiff
     ... = (x ⊓ (y ⊓ x ⊔ y \ x)) ⊓ (x \ y)             : by rw sup_inf_sdiff
     ... = (x ⊓ (y ⊓ x) ⊔ x ⊓ (y \ x)) ⊓ (x \ y)       : by rw inf_sup_left
     ... = (y ⊓ x ⊔ x ⊓ (y \ x)) ⊓ (x \ y) :
                                    by conv_lhs { congr, congr, rw [inf_comm, inf_assoc, inf_idem] }
     ... = (x ⊓ y ⊓ (x \ y)) ⊔ (x ⊓ (y \ x) ⊓ (x \ y)) : by rw [inf_sup_right, @inf_comm _ _ x y]
     ... = x ⊓ (y \ x) ⊓ (x \ y)                       : by rw [inf_inf_sdiff, bot_sup_eq]
     ... = x ⊓ (x \ y) ⊓ (y \ x)              : by rw [inf_assoc, @inf_comm _ _ (y \ x), ←inf_assoc]
     ... = (x \ y) ⊓ (y \ x)                           : by rw [inf_sdiff_right]

lemma disjoint_sdiff_sdiff : disjoint (x \ y) (y \ x) := sdiff_inf_sdiff.le

/--
Cf. <https://ncatlab.org/nlab/show/relative+complement>
-/
theorem le_sup_sdiff : y ≤ x ⊔ (y \ x) :=
by { rw [sup_sdiff_same_right], exact le_sup_right }

theorem inf_sdiff_same_right : x ⊓ (y \ x) = ⊥ :=
calc x ⊓ (y \ x) = ((x ⊓ y) ⊔ (x \ y)) ⊓ (y \ x)         : by rw [sup_inf_sdiff]
             ... = (x ⊓ y) ⊓ (y \ x) ⊔ (x \ y) ⊓ (y \ x) : by rw [inf_sup_right]
             ... = ⊥         : by rw [@inf_comm _ _ x y, inf_inf_sdiff, sdiff_inf_sdiff, bot_sup_eq]
theorem inf_sdiff_same_left : (y \ x) ⊓ x = ⊥ := by rw [inf_comm, inf_sdiff_same_right]

theorem disjoint_sdiff : disjoint x (y \ x) := inf_sdiff_same_right.le

/-- <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations> -/
theorem exist_rel_complements (h : x ≤ y) : ∃ z, x ⊓ z = ⊥ ∧ x ⊔ z = y :=
⟨y \ x, ⟨inf_sdiff_same_right, sup_sdiff_of_le h⟩⟩

/-- <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations>

Could potentially make an alternative constructor with this as an axiom if we had a typeclasses for
distributive lattices with bot? -/
theorem unique_rel_complement (h : x ≤ y) (hi : x ⊓ z = ⊥) (hs : x ⊔ z = y) : y \ x = z :=
sdiff_unique (by rw [inf_eq_right.2 h, hs]) (by rw [inf_eq_right.2 h, hi])

theorem of_ncatlab (hz : z ≤ y) (hs : y ≤ x ⊔ z) (hd : disjoint x z) : y \ x = z :=
sdiff_unique
  (begin
    rw [←inf_eq_right] at hs,
    rwa [sup_inf_right, inf_sup_right, @sup_comm _ _ x, inf_sup_self, inf_comm, @sup_comm _ _ z,
      hs, sup_eq_left],
  end)
  (by rw [inf_assoc, hd.eq_bot, inf_bot_eq])

-- cf. `is_compl.le_left_iff` and `is_compl.le_right_iff`
lemma le_iff_disjoint_sdiff (hz : z ≤ y) (hx : x ≤ y) : z ≤ x ↔ disjoint z (y \ x) :=
⟨λ H, disjoint_sdiff.mono_left H,
  λ H, le_of_inf_le_sup_le
    (le_trans H bot_le)
    (begin
      rw [sup_sdiff_of_le hx],
      apply le_trans,
      apply sup_le_sup_left,
      apply sdiff_le,
      rw sup_eq_right.2 hz,
    end)⟩
-- lemma inf_left_eq_bot_iff (h : is_compl y z) : x ⊓ y = ⊥ ↔ x ≤ z :=
-- inf_eq_bot_iff_le_compl h.sup_eq_top h.inf_eq_bot

-- lemma inf_right_eq_bot_iff (h : is_compl y z) : x ⊓ z = ⊥ ↔ x ≤ y :=
-- h.symm.inf_left_eq_bot_iff

-- lemma disjoint_left_iff (h : is_compl y z) : disjoint x y ↔ x ≤ z :=
-- disjoint_iff.trans h.inf_left_eq_bot_iff

-- lemma disjoint_right_iff (h : is_compl y z) : disjoint x z ↔ x ≤ y :=
-- h.symm.disjoint_left_iff

-- cf. `is_compl.left_le_iff` and `is_compl.right_le_iff`
lemma le_iff_eq_sup_disjoint (hz : z ≤ y) (hx : x ≤ y) : x ≤ z ↔ y = z ⊔ (y \ x) :=
⟨λ H,
  begin
    apply le_antisymm,
    { conv_lhs { rw [←sup_inf_sdiff y x] },
      apply sup_le_sup_right,
      rw inf_eq_right.2 hx,
      exact H, },
    { apply le_trans,
      { apply sup_le_sup_right hz, },
      { rw sup_sdiff_left, } }
  end,
 λ H,
  begin
    conv_lhs at H { rw [←sup_sdiff_of_le hx], },
    refine le_of_inf_le_sup_le _ H.le,
    rw inf_sdiff_same_right,
    exact bot_le,
  end⟩

lemma sdiff_sup : y \ (x ⊔ z) = (y \ x) ⊓ (y \ z) :=
sdiff_unique
  (calc y ⊓ (x ⊔ z) ⊔ y \ x ⊓ (y \ z) =
        (y ⊓ (x ⊔ z) ⊔ y \ x) ⊓ (y ⊓ (x ⊔ z) ⊔ (y \ z))     : by rw sup_inf_left
  ... = (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ (y \ z)) : by rw @inf_sup_left _ _ y
  ... = (y ⊓ z ⊔ y ⊓ x ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ (y \ z)) : by rw @sup_comm _ _ (y ⊓ x)
  ... = (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ (y \ z))) :
                                    by rw [@sup_assoc _ _ (y ⊓ z), @sup_assoc _ _ (y ⊓ x)]
  ... = (y ⊓ z ⊔ y) ⊓ (y ⊓ x ⊔ y) : by rw [sup_inf_sdiff, sup_inf_sdiff]
  ... = (y ⊔ y ⊓ z) ⊓ (y ⊔ y ⊓ x) : by rw [sup_comm, @sup_comm _ _ (y ⊓ x)]
  ... = y                         : by rw [sup_inf_self, sup_inf_self, inf_idem])
   (calc y ⊓ (x ⊔ z) ⊓ ((y \ x) ⊓ (y \ z)) =
         (y ⊓ x ⊔ y ⊓ z) ⊓ ((y \ x) ⊓ (y \ z)) : by rw inf_sup_left
  ... = ((y ⊓ x) ⊓ ((y \ x) ⊓ (y \ z))) ⊔ (((y \ x) ⊓ (y \ z)) ⊓ (y ⊓ z)) :
                                                        by rw [inf_sup_right, @inf_comm _ _ (y ⊓ z)]
  ... = ((y ⊓ x) ⊓ (y \ x) ⊓ (y \ z)) ⊔ ((y \ x) ⊓ ((y \ z) ⊓ (y ⊓ z))) :
                                                        by rw [←inf_assoc, ←@inf_assoc _ _ (y \ x)]
  ... = ⊥ : by rw [inf_inf_sdiff, bot_inf_eq, bot_sup_eq, @inf_comm _ _ (y \ z), inf_inf_sdiff,
              inf_bot_eq])
-- lemma sup_inf {x' y'} (h : is_compl x y) (h' : is_compl x' y') :
--   is_compl (x ⊔ x') (y ⊓ y') :=
-- of_eq
--   (by rw [inf_sup_right, ← inf_assoc, h.inf_eq_bot, bot_inf_eq, bot_sup_eq, inf_left_comm,
--     h'.inf_eq_bot, inf_bot_eq])
--   (by rw [sup_inf_left, @sup_comm _ _ x, sup_assoc, h.sup_eq_top, sup_top_eq, top_inf_eq,
--     sup_assoc, sup_left_comm, h'.sup_eq_top, sup_top_eq])

lemma sdiff_inf : y \ (x ⊓ z) = y \ x ⊔ y \ z :=
sdiff_unique
  (calc y ⊓ (x ⊓ z) ⊔ (y \ x ⊔ y \ z) =
    (z ⊓ (y ⊓ x)) ⊔ (y \ x ⊔ y \ z) : by rw [←inf_assoc, inf_comm]
  ... = (z ⊔ (y \ x ⊔ y \ z)) ⊓ ((y ⊓ x) ⊔ (y \ x ⊔ y \ z)) : by rw [sup_inf_right]
  ... = (y ⊔ z) ⊓ ((y ⊓ x) ⊔ (y \ x ⊔ y \ z)) :
                       by rw [sup_comm, sup_assoc, sup_sdiff_same_left, ←sup_assoc, sup_sdiff_right]
  ... = (y ⊔ z) ⊓ y : by rw [←sup_assoc, sup_inf_sdiff, sup_sdiff_left]
  ... = y                         : by rw [inf_comm, inf_sup_self])
  (calc y ⊓ (x ⊓ z) ⊓ ((y \ x) ⊔ (y \ z)) =
        (y ⊓ (x ⊓ z) ⊓ (y \ x)) ⊔ (y ⊓ (x ⊓ z) ⊓ (y \ z)) : by rw [inf_sup_left]
  ... = (y ⊓ (x ⊓ z) ⊓ (y \ z)) :
             by rw [←inf_assoc, @inf_comm _ _ _ z, inf_assoc, inf_inf_sdiff, inf_bot_eq, bot_sup_eq]
  ... = (x ⊓ ((y ⊓ z) ⊓ (y \ z))) :
             by rw [@inf_comm _ _ y, @inf_assoc _ _ x, @inf_comm _ _ z, inf_assoc]
  ... = ⊥ : by rw [inf_inf_sdiff, inf_bot_eq])
-- lemma inf_sup {x' y'} (h : is_compl x y) (h' : is_compl x' y') :
--   is_compl (x ⊓ x') (y ⊔ y') :=
-- (h.symm.sup_inf h'.symm).symm

lemma sdiff_inf_same_right : y \ (x ⊓ y) = y \ x := by rw [sdiff_inf, sdiff_self, sup_bot_eq]
lemma sdiff_inf_same_left : y \ (y ⊓ x) = y \ x := by rw [inf_comm, sdiff_inf_same_right]

theorem sdiff_eq_left (h : x ⊓ y = ⊥) : x \ y = x :=
by conv_rhs { rw [←sup_inf_sdiff x y, h, bot_sup_eq] }

@[simp] theorem sdiff_bot : x \ ⊥ = x := sdiff_eq_left inf_bot_eq
-- lemma is_compl_bot_top [bounded_lattice α] : is_compl (⊥ : α) ⊤ :=
-- is_compl.of_eq bot_inf_eq sup_top_eq

lemma sdiff_le_sdiff_same (h : z ≤ x) : w \ x ≤ w \ z :=
le_of_inf_le_sup_le
  (calc (w \ x) ⊓ (w ⊓ z) ≤ (w \ x) ⊓ (w ⊓ x) : inf_le_inf le_rfl (inf_le_inf le_rfl h)
              ... = ⊥                         : by rw [inf_comm, inf_inf_sdiff]
              ... ≤ (w \ z) ⊓ (w ⊓ z)         : bot_le)
  (calc w \ x ⊔ (w ⊓ z) ≤ w \ x ⊔ (w ⊓ x)   : sup_le_sup le_rfl (inf_le_inf le_rfl h)
                    ... ≤ w                 : by rw [sup_comm, sup_inf_sdiff]
                    ... = (w \ z) ⊔ (w ⊓ z) : by rw [sup_comm, sup_inf_sdiff])
-- lemma antimono {x' y'} (h : is_compl x y) (h' : is_compl x' y') (hx : x ≤ x') :
--   y' ≤ y :=
-- h'.right_le_iff.2 $ le_trans h.symm.top_le_sup (sup_le_sup_left hx _)

lemma sdiff_le_same_sdiff (h : w ≤ y) : w \ x ≤ y \ x :=
le_of_inf_le_sup_le
  (calc (w \ x) ⊓ (w ⊓ x) = ⊥                 : by rw [inf_comm, inf_inf_sdiff]
                      ... ≤ (y \ x) ⊓ (w ⊓ x) : bot_le)
  (calc w \ x ⊔ (w ⊓ x) = w                       : by rw [sup_comm, sup_inf_sdiff]
                    ... ≤ (y ⊓ (y \ x)) ⊔ w       : le_sup_right
                    ... = (y ⊓ (y \ x)) ⊔ (y ⊓ w) : by rw [inf_eq_right.2 h]
                    ... = y ⊓ ((y \ x) ⊔ w)       : by rw [inf_sup_left]
                    ... = ((y \ x) ⊔ (y ⊓ x)) ⊓ ((y \ x) ⊔ w) :
                                                by rw [@sup_comm _ _ (y \ x) (y ⊓ x), sup_inf_sdiff]
                    ... = (y \ x) ⊔ ((y ⊓ x) ⊓ w) : by rw [←sup_inf_left]
                    ... = (y \ x) ⊔ ((w ⊓ y) ⊓ x) : by rw [inf_comm, inf_assoc]
                    ... = (y \ x) ⊔ (w ⊓ x)       : by rw [inf_eq_left.2 h])

theorem sdiff_le_sdiff (h₁ : w ≤ y) (h₂ : z ≤ x) : w \ x ≤ y \ z :=
calc w \ x ≤ w \ z : sdiff_le_sdiff_same h₂
       ... ≤ y \ z : sdiff_le_same_sdiff h₁
-- le_of_inf_le_sup_le
  -- (show w \ x ⊓ (x ⊔ z) ≤ y \ z ⊓ (x ⊔ z), from sorry)
  -- (show w \ x ⊔ (x ⊔ z) ≤ y \ z ⊔ (x ⊔ z), from sorry)
-- by rw [sdiff_eq, sdiff_eq]; from inf_le_inf h₁ (compl_le_compl h₂)

lemma mccuan1c : x \ (y \ z) = (x \ y) ⊔ (x ⊓ y ⊓ z) :=
eq.symm $
calc (x \ y) ⊔ (x ⊓ y ⊓ z) = z ⊓ (x ⊓ y) ⊔ (x \ y) : by rw [sup_comm, inf_comm]
... = (z ⊔ (x \ y)) ⊓ ((x ⊓ y) ⊔ (x \ y)) : by rw [sup_inf_right]
... = (z ⊔ (x \ y)) ⊓ x : by rw [sup_inf_sdiff]
... = (z ⊓ x) ⊔ (x \ y) : by rw [inf_sup_right, inf_sdiff_left]
... = _ : sorry

lemma sdiff_sdiff : x \ (x \ y) = x ⊓ y := by rw [mccuan1c, inf_idem, sdiff_self, bot_sup_eq]

lemma sdiff_sdiff_eq_self (h : y ≤ x) : x \ (x \ y) = y := by rw [sdiff_sdiff, inf_of_le_right h]

lemma mccuan1b : (x \ y) \ z = x \ (y ⊔ z) := sorry

@[simp] lemma sdiff_idem_right : x \ y \ y = x \ y := by rw [mccuan1b, sup_idem]
-- by rw [sdiff_eq, sdiff_eq, inf_assoc, inf_idem]

lemma sdiff_sdiff_sup_sdiff : z \ (x \ y ⊔ y \ x) = (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := sorry

-- mccuan1a
lemma sup_sdiff : (x ⊔ y) \ z = (x \ z) ⊔ (y \ z) :=
sdiff_unique
  (calc (x ⊔ y) ⊓ z ⊔ (x \ z ⊔ y \ z) = (x ⊓ z ⊔ y ⊓ z) ⊔ (x \ z ⊔ y \ z) : by rw [inf_sup_right]
                                  ... = x ⊓ z ⊔ x \ z ⊔ y \ z ⊔ y ⊓ z :
                                    by rw [sup_assoc, @sup_comm _ _ (y ⊓ z), ←sup_assoc, ←sup_assoc]
                                  ... = x ⊔ (y ⊓ z ⊔ y \ z) :
                                            by rw [sup_inf_sdiff, sup_assoc, @sup_comm _ _ (y \ z)]
                                  ... = x ⊔ y : by rw [sup_inf_sdiff])
  (calc (x ⊔ y) ⊓ z ⊓ (x \ z ⊔ y \ z) = (x ⊓ z ⊔ y ⊓ z) ⊓ (x \ z ⊔ y \ z) : by rw [inf_sup_right]
                                  ... = (x ⊓ z ⊔ y ⊓ z) ⊓ (x \ z) ⊔ ((x ⊓ z ⊔ y ⊓ z) ⊓ (y \ z)) :
                                                           by rw [@inf_sup_left _ _ (x ⊓ z ⊔ y ⊓ z)]
                                  ... = (y ⊓ z ⊓ (x \ z)) ⊔ ((x ⊓ z ⊔ y ⊓ z) ⊓ (y \ z)) :
                                                    by rw [inf_sup_right, inf_inf_sdiff, bot_sup_eq]
                                  ... = (x ⊓ z ⊔ y ⊓ z) ⊓ (y \ z) :
                                     by rw [inf_assoc, inf_sdiff_same_right, inf_bot_eq, bot_sup_eq]
                                  ... = x ⊓ z ⊓ (y \ z) :
                                                    by rw [inf_sup_right, inf_inf_sdiff, sup_bot_eq]
                                  ... = ⊥ : by rw [inf_assoc, inf_sdiff_same_right, inf_bot_eq])

lemma inf_sdiff : (x ⊓ y) \ z = (x \ z) ⊓ (y \ z) :=
sdiff_unique
  (calc (x ⊓ y) ⊓ z ⊔ ((x \ z) ⊓ (y \ z)) = ((x ⊓ y) ⊓ z ⊔ (x \ z)) ⊓ ((x ⊓ y) ⊓ z ⊔ (y \ z)) :
          by rw [sup_inf_left]
          ... = ((x ⊓ y ⊓ (z ⊔ x)) ⊔ ((x \ z) ⊓ (z ⊔ x))) ⊓ ((x ⊓ y) ⊓ z ⊔ (y \ z)) :
                      by rw [sup_inf_right, sup_sdiff_same_right, inf_sup_right]
                                  ... = x ⊓ y : sorry)
  (calc (x ⊓ y) ⊓ z ⊓ ((x \ z) ⊓ (y \ z)) = x ⊓ y ⊓ (z ⊓ (x \ z)) ⊓ (y \ z) :
                                                          by rw [←inf_assoc, @inf_assoc _ _ (x ⊓ y)]
                                      ... = ⊥ :
                                               by rw [inf_sdiff_same_right, inf_bot_eq, bot_inf_eq])

end generalized_boolean_algebra

/-!
### Boolean algebras
-/


/-- Set / lattice complement -/
class has_compl (α : Type*) := (compl : α → α)

export has_compl (compl)

postfix `ᶜ`:(max+1) := compl

/-- A Boolean algebra is a bounded distributive lattice with
a complement operator `ᶜ` such that `x ⊓ xᶜ = ⊥` and `x ⊔ xᶜ = ⊤`.
For convenience, it must also provide a set difference operation `\`
satisfying `x \ y = x ⊓ yᶜ`.

This is a generalization of (classical) logic of propositions, or
the powerset lattice. -/
class boolean_algebra α extends bounded_distrib_lattice α, has_compl α, has_sdiff α :=
(inf_compl_le_bot : ∀x:α, x ⊓ xᶜ ≤ ⊥)
(top_le_sup_compl : ∀x:α, ⊤ ≤ x ⊔ xᶜ)
(sdiff_eq : ∀x y:α, x \ y = x ⊓ yᶜ)

section boolean_algebra
variables [boolean_algebra α]

@[simp] theorem inf_compl_eq_bot : x ⊓ xᶜ = ⊥ :=
bot_unique $ boolean_algebra.inf_compl_le_bot x

@[simp] theorem compl_inf_eq_bot : xᶜ ⊓ x = ⊥ :=
eq.trans inf_comm inf_compl_eq_bot

@[simp] theorem sup_compl_eq_top : x ⊔ xᶜ = ⊤ :=
top_unique $ boolean_algebra.top_le_sup_compl x

@[simp] theorem compl_sup_eq_top : xᶜ ⊔ x = ⊤ :=
eq.trans sup_comm sup_compl_eq_top

theorem is_compl_compl : is_compl x xᶜ :=
is_compl.of_eq inf_compl_eq_bot sup_compl_eq_top

theorem is_compl.compl_eq (h : is_compl x y) : xᶜ = y :=
(h.right_unique is_compl_compl).symm

theorem disjoint_compl_right : disjoint x xᶜ := is_compl_compl.disjoint
theorem disjoint_compl_left : disjoint xᶜ x := disjoint_compl_right.symm

theorem sdiff_eq : x \ y = x ⊓ yᶜ :=
boolean_algebra.sdiff_eq x y

theorem top_sdiff : ⊤ \ x = xᶜ := by rw [sdiff_eq, top_inf_eq]

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
instance : generalized_boolean_algebra α :=
{ sup_inf_sdiff := λ a b, by rw [sdiff_eq, ←inf_sup_left, sup_compl_eq_top, inf_top_eq],
  inf_inf_sdiff := λ a b, by rw [_root_.sdiff_eq, inf_left_right_swap, @inf_assoc _ _ a,
      compl_inf_eq_bot, inf_bot_eq, bot_inf_eq],
  ..(infer_instance : boolean_algebra α) }

@[priority 100]
instance : is_complemented α := ⟨λ x, ⟨xᶜ, is_compl_compl⟩⟩

end boolean_algebra

end boolean_algebra

instance boolean_algebra_Prop : boolean_algebra Prop :=
{ compl := not,
  sdiff := λ p q, p ∧ ¬ q,
  sdiff_eq := λ _ _, rfl,
  inf_compl_le_bot := λ p ⟨Hp, Hpc⟩, Hpc Hp,
  top_le_sup_compl := λ p H, classical.em p,
  .. bounded_distrib_lattice_Prop }

instance pi.boolean_algebra {α : Type u} {β : Type v} [boolean_algebra β] :
  boolean_algebra (α → β) :=
by pi_instance
