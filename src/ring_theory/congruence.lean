/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import algebra.group_ring_action.basic
import algebra.hom.ring
import algebra.ring.inj_surj
import group_theory.congruence

/-!
# Congruence relations on rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines congruence relations on rings, which extend `con` and `add_con` on monoids and
additive monoids.

Most of the time you likely want to use the `ideal.quotient` API that is built on top of this.

## Main Definitions

* `ring_con R`: the type of congruence relations respecting `+` and `*`.
* `ring_con_gen r`: the inductively defined smallest ring congruence relation containing a given
  binary relation.

## TODO

* Use this for `ring_quot` too.
* Copy across more API from `con` and `add_con` in `group_theory/congruence.lean`
-/

/-- A congruence relation on a type with an addition and multiplication is an equivalence relation
which preserves both. -/
/- Note: we can't extend both `add_con R` and `mul_con R` in Lean 3 due to interactions between old-
and new-style structures. We can revisit this in Lean 4. (After and not during the port!) -/
structure ring_con (R : Type*) [has_add R] [has_mul R] extends setoid R :=
(add' : ∀ {w x y z}, r w x → r y z → r (w + y) (x + z))
(mul' : ∀ {w x y z}, r w x → r y z → r (w * y) (x * z))

variables {α R : Type*}

/-- The inductively defined smallest ring congruence relation containing a given binary
    relation. -/
inductive ring_con_gen.rel [has_add R] [has_mul R] (r : R → R → Prop) : R → R → Prop
| of : Π x y, r x y → ring_con_gen.rel x y
| refl : Π x, ring_con_gen.rel x x
| symm : Π {x y}, ring_con_gen.rel x y → ring_con_gen.rel y x
| trans : Π {x y z}, ring_con_gen.rel x y → ring_con_gen.rel y z → ring_con_gen.rel x z
| add : Π {w x y z}, ring_con_gen.rel w x → ring_con_gen.rel y z → ring_con_gen.rel (w + y) (x + z)
| mul : Π {w x y z}, ring_con_gen.rel w x → ring_con_gen.rel y z → ring_con_gen.rel (w * y) (x * z)

/-- The inductively defined smallest ring congruence relation containing a given binary
    relation. -/
def ring_con_gen [has_add R] [has_mul R] (r : R → R → Prop) : ring_con R :=
{ r := ring_con_gen.rel r,
  iseqv := ⟨ring_con_gen.rel.refl, @ring_con_gen.rel.symm _ _ _ _, @ring_con_gen.rel.trans _ _ _ _⟩,
  add' := λ _ _ _ _, ring_con_gen.rel.add,
  mul' := λ _ _ _ _, ring_con_gen.rel.mul }

namespace ring_con

section basic
variables [has_add R] [has_mul R] (c : ring_con R)

/-- Every `ring_con` is also an `add_con` -/
def to_add_con : add_con R := { ..c }

/-- Every `ring_con` is also a `con` -/
def to_con : con R := { ..c }

/-- A coercion from a congruence relation to its underlying binary relation. -/
instance : has_coe_to_fun (ring_con R) (λ _, R → R → Prop) := ⟨λ c, c.r⟩

@[simp] lemma rel_eq_coe : c.r = c := rfl

protected lemma refl (x) : c x x := c.refl' x
protected lemma symm {x y} : c x y → c y x := c.symm'
protected lemma trans {x y z} : c x y → c y z → c x z := c.trans'
protected lemma add {w x y z} : c w x → c y z → c (w + y) (x + z) := c.add'
protected lemma mul {w x y z} : c w x → c y z → c (w * y) (x * z) := c.mul'

@[simp] lemma rel_mk {s : setoid R} {ha hm a b} : ring_con.mk s ha hm a b ↔ setoid.r a b := iff.rfl

instance : inhabited (ring_con R) := ⟨ring_con_gen empty_relation⟩

/-- The map sending a congruence relation to its underlying binary relation is injective. -/
lemma ext' {c d : ring_con R} (H : c.r = d.r) : c = d :=
by { rcases c with ⟨⟨⟩⟩, rcases d with ⟨⟨⟩⟩, cases H, congr, }

/-- Extensionality rule for congruence relations. -/
lemma ext {c d : ring_con R} (H : ∀ x y, c x y ↔ d x y) : c = d :=
ext' $ by ext; apply H

end basic

section quotient

section basic
variables [has_add R] [has_mul R] (c : ring_con R)
/-- Defining the quotient by a congruence relation of a type with addition and multiplication. -/
protected def quotient := quotient c.to_setoid

/-- Coercion from a type with addition and multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
instance : has_coe_t R c.quotient := ⟨@quotient.mk _ c.to_setoid⟩

/-- The quotient by a decidable congruence relation has decidable equality. -/
-- Lower the priority since it unifies with any quotient type.
@[priority 500] instance [d : ∀ a b, decidable (c a b)] : decidable_eq c.quotient :=
@quotient.decidable_eq R c.to_setoid d

@[simp] lemma quot_mk_eq_coe (x : R) : quot.mk c x = (x : c.quotient) := rfl

/-- Two elements are related by a congruence relation `c` iff they are represented by the same
element of the quotient by `c`. -/
@[simp] protected lemma eq {a b : R} : (a : c.quotient) = b ↔ c a b := quotient.eq'

end basic

/-! ### Basic notation

The basic algebraic notation, `0`, `1`, `+`, `*`, `-`, `^`, descend naturally under the quotient
-/
section data

section add_mul
variables [has_add R] [has_mul R] (c : ring_con R)
instance : has_add c.quotient := c.to_add_con.has_add
@[simp, norm_cast] lemma coe_add (x y : R) : (↑(x + y) : c.quotient) = ↑x + ↑y := rfl
instance : has_mul c.quotient := c.to_con.has_mul
@[simp, norm_cast] lemma coe_mul (x y : R) : (↑(x * y) : c.quotient) = ↑x * ↑y := rfl
end add_mul

section zero
variables [add_zero_class R] [has_mul R] (c : ring_con R)
instance : has_zero c.quotient := c.to_add_con^.quotient.has_zero
@[simp, norm_cast] lemma coe_zero : (↑(0 : R) : c.quotient) = 0 := rfl
end zero

section one
variables [has_add R] [mul_one_class R] (c : ring_con R)
instance : has_one c.quotient := c.to_con^.quotient.has_one
@[simp, norm_cast] lemma coe_one : (↑(1 : R) : c.quotient) = 1 := rfl
end one

section smul
variables [has_add R] [mul_one_class R] [has_smul α R] [is_scalar_tower α R R] (c : ring_con R)
instance : has_smul α c.quotient := c.to_con.has_smul
@[simp, norm_cast] lemma coe_smul (a : α) (x : R) : (↑(a • x) : c.quotient) = a • x := rfl
end smul

section neg_sub_zsmul
variables [add_group R] [has_mul R] (c : ring_con R)
instance : has_neg c.quotient := c.to_add_con^.has_neg
@[simp, norm_cast] lemma coe_neg (x : R) : (↑(-x) : c.quotient) = -x := rfl
instance : has_sub c.quotient := c.to_add_con^.has_sub
@[simp, norm_cast] lemma coe_sub (x y : R) : (↑(x - y) : c.quotient) = x - y := rfl
instance has_zsmul : has_smul ℤ c.quotient := c.to_add_con^.quotient.has_zsmul
@[simp, norm_cast] lemma coe_zsmul (z : ℤ) (x : R) : (↑(z • x) : c.quotient) = z • x := rfl
end neg_sub_zsmul

section nsmul
variables [add_monoid R] [has_mul R] (c : ring_con R)
instance has_nsmul : has_smul ℕ c.quotient := c.to_add_con^.quotient.has_nsmul
@[simp, norm_cast] lemma coe_nsmul (n : ℕ) (x : R) : (↑(n • x) : c.quotient) = n • x := rfl
end nsmul

section pow
variables [has_add R] [monoid R] (c : ring_con R)
instance : has_pow c.quotient ℕ := c.to_con^.nat.has_pow
@[simp, norm_cast] lemma coe_pow (x : R) (n : ℕ) : (↑(x ^ n) : c.quotient) = x ^ n := rfl
end pow

section nat_cast
variables [add_monoid_with_one R] [has_mul R] (c : ring_con R)
instance : has_nat_cast c.quotient := ⟨λ n, ↑(n : R)⟩
@[simp, norm_cast] lemma coe_nat_cast (n : ℕ) : (↑(n : R) : c.quotient) = n := rfl
end nat_cast

section int_cast
variables [add_group_with_one R] [has_mul R] (c : ring_con R)
instance : has_int_cast c.quotient := ⟨λ z, ↑(z : R)⟩
@[simp, norm_cast] lemma coe_int_cast (n : ℕ) : (↑(n : R) : c.quotient) = n := rfl
end int_cast

instance [inhabited R] [has_add R] [has_mul R] (c : ring_con R) : inhabited c.quotient :=
⟨↑(default : R)⟩

end data

/-! ### Algebraic structure

The operations above on the quotient by `c : ring_con R` preseverse the algebraic structure of `R`.
-/

section algebraic

instance [non_unital_non_assoc_semiring R] (c : ring_con R) :
  non_unital_non_assoc_semiring c.quotient :=
function.surjective.non_unital_non_assoc_semiring _ quotient.surjective_quotient_mk'
  rfl (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [non_assoc_semiring R] (c : ring_con R) :
  non_assoc_semiring c.quotient :=
function.surjective.non_assoc_semiring _ quotient.surjective_quotient_mk'
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl)

instance [non_unital_semiring R] (c : ring_con R) :
  non_unital_semiring c.quotient :=
function.surjective.non_unital_semiring _ quotient.surjective_quotient_mk'
  rfl (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [semiring R] (c : ring_con R) :
  semiring c.quotient :=
function.surjective.semiring _ quotient.surjective_quotient_mk'
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl)

instance [comm_semiring R] (c : ring_con R) :
  comm_semiring c.quotient :=
function.surjective.comm_semiring _ quotient.surjective_quotient_mk'
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl)

instance [non_unital_non_assoc_ring R] (c : ring_con R) :
  non_unital_non_assoc_ring c.quotient :=
function.surjective.non_unital_non_assoc_ring _ quotient.surjective_quotient_mk'
  rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [non_assoc_ring R] (c : ring_con R) :
  non_assoc_ring c.quotient :=
function.surjective.non_assoc_ring _ quotient.surjective_quotient_mk'
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl)
  (λ _, rfl)

instance [non_unital_ring R] (c : ring_con R) :
  non_unital_ring c.quotient :=
function.surjective.non_unital_ring _ quotient.surjective_quotient_mk'
  rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [ring R] (c : ring_con R) :
  ring c.quotient :=
function.surjective.ring _ quotient.surjective_quotient_mk'
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)
  (λ _, rfl) (λ _, rfl)

instance [comm_ring R] (c : ring_con R) :
  comm_ring c.quotient :=
function.surjective.comm_ring _ quotient.surjective_quotient_mk'
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)
  (λ _, rfl) (λ _, rfl)

instance [monoid α] [non_assoc_semiring R] [distrib_mul_action α R] [is_scalar_tower α R R]
  (c : ring_con R) :
  distrib_mul_action α c.quotient :=
{ smul := (•),
  smul_zero := λ r, congr_arg quotient.mk' $ smul_zero _,
  smul_add := λ r, quotient.ind₂' $ by exact λ m₁ m₂, congr_arg quotient.mk' $ smul_add _ _ _,
  .. c.to_con.mul_action }

instance [monoid α] [semiring R] [mul_semiring_action α R] [is_scalar_tower α R R]
  (c : ring_con R) :
  mul_semiring_action α c.quotient :=
{ smul := (•),
  .. c^.quotient.distrib_mul_action,
  .. c.to_con.mul_distrib_mul_action }

end algebraic

/-- The natural homomorphism from a ring to its quotient by a congruence relation. -/
def mk' [non_assoc_semiring R] (c : ring_con R) : R →+* c.quotient :=
{ to_fun := quotient.mk', map_zero' := rfl, map_one' := rfl,
  map_add' :=  λ _ _, rfl, map_mul' := λ _ _, rfl }

end quotient

/-! ### Lattice structure

The API in this section is copied from `group_theory/congruence.lean`
-/

section lattice
variables [has_add R] [has_mul R]

/-- For congruence relations `c, d` on a type `M` with multiplication and addition, `c ≤ d` iff
`∀ x y ∈ M`, `x` is related to `y` by `d` if `x` is related to `y` by `c`. -/
instance : has_le (ring_con R) := ⟨λ c d, ∀ ⦃x y⦄, c x y → d x y⟩

/-- Definition of `≤` for congruence relations. -/
theorem le_def {c d : ring_con R} : c ≤ d ↔ ∀ {x y}, c x y → d x y := iff.rfl

/-- The infimum of a set of congruence relations on a given type with multiplication and
addition. -/
instance : has_Inf (ring_con R) :=
⟨λ S,
  { r := λ x y, ∀ c : ring_con R, c ∈ S → c x y,
    iseqv := ⟨λ x c hc, c.refl x, λ _ _ h c hc, c.symm $ h c hc,
              λ _ _ _ h1 h2 c hc, c.trans (h1 c hc) $ h2 c hc⟩,
    add' := λ _ _ _ _ h1 h2 c hc, c.add (h1 c hc) $ h2 c hc,
    mul' := λ _ _ _ _ h1 h2 c hc, c.mul (h1 c hc) $ h2 c hc }⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying equivalence relation. -/
lemma Inf_to_setoid (S : set (ring_con R)) : (Inf S).to_setoid = Inf (to_setoid '' S) :=
setoid.ext' $ λ x y, ⟨λ h r ⟨c, hS, hr⟩, by rw ←hr; exact h c hS,
  λ h c hS, h c.to_setoid ⟨c, hS, rfl⟩⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying binary relation. -/
lemma Inf_def (S : set (ring_con R)) :
  ⇑(Inf S) = Inf (@set.image (ring_con R) (R → R → Prop) coe_fn S) :=
by { ext, simp only [Inf_image, infi_apply, infi_Prop_eq], refl }

instance : partial_order (ring_con R) :=
{ le := (≤),
  lt := λ c d, c ≤ d ∧ ¬d ≤ c,
  le_refl := λ c _ _, id,
  le_trans := λ c1 c2 c3 h1 h2 x y h, h2 $ h1 h,
  lt_iff_le_not_le := λ _ _, iff.rfl,
  le_antisymm := λ c d hc hd, ext $ λ x y, ⟨λ h, hc h, λ h, hd h⟩ }

/-- The complete lattice of congruence relations on a given type with multiplication and
addition. -/
instance : complete_lattice (ring_con R) :=
{ inf := λ c d,
  { to_setoid := (c.to_setoid ⊓ d.to_setoid),
    mul' := λ _ _ _ _ h1 h2, ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩,
    add' := λ _ _ _ _ h1 h2, ⟨c.add h1.1 h2.1, d.add h1.2 h2.2⟩ },
  inf_le_left := λ _ _ _ _ h, h.1,
  inf_le_right := λ _ _ _ _ h, h.2,
  le_inf := λ _ _ _ hb hc _ _ h, ⟨hb h, hc h⟩,
  top := { mul' := λ _ _ _ _ _ _, trivial,
           add' := λ _ _ _ _ _ _, trivial,
           ..(⊤ : setoid R) },
  le_top := λ _ _ _ h, trivial,
  bot := { mul' := λ _ _ _ _, congr_arg2 _,
           add' := λ _ _ _ _, congr_arg2 _,
           ..(⊥ : setoid R) },
  bot_le := λ c x y h, h ▸ c.refl x,
  .. complete_lattice_of_Inf (ring_con R) $ assume s,
    ⟨λ r hr x y h, (h : ∀ r ∈ s, (r : ring_con R) x y) r hr, λ r hr x y h r' hr', hr hr' h⟩ }

/-- The infimum of two congruence relations equals the infimum of the underlying binary
operations. -/
lemma inf_def {c d : ring_con R} : (c ⊓ d).r = c.r ⊓ d.r := rfl

/-- Definition of the infimum of two congruence relations. -/
theorem inf_iff_and {c d : ring_con R} {x y} : (c ⊓ d) x y ↔ c x y ∧ d x y := iff.rfl

/-- The inductively defined smallest congruence relation containing a binary relation `r` equals
    the infimum of the set of congruence relations containing `r`. -/
theorem ring_con_gen_eq (r : R → R → Prop) :
  ring_con_gen r = Inf {s : ring_con R | ∀ x y, r x y → s x y} :=
le_antisymm
  (λ x y H, ring_con_gen.rel.rec_on H
    (λ _ _ h _ hs, hs _ _ h)
    (ring_con.refl _)
    (λ _ _ _, ring_con.symm _)
    (λ _ _ _ _ _, ring_con.trans _)
    (λ w x y z _ _ h1 h2 c hc, c.add (h1 c hc) $ h2 c hc)
    (λ w x y z _ _ h1 h2 c hc, c.mul (h1 c hc) $ h2 c hc))
  (Inf_le (λ _ _, ring_con_gen.rel.of _ _))

/-- The smallest congruence relation containing a binary relation `r` is contained in any
    congruence relation containing `r`. -/
theorem ring_con_gen_le {r : R → R → Prop} {c : ring_con R}
  (h : ∀ x y, r x y → @setoid.r _ c.to_setoid x y) :
  ring_con_gen r ≤ c :=
by rw ring_con_gen_eq; exact Inf_le h

/-- Given binary relations `r, s` with `r` contained in `s`, the smallest congruence relation
    containing `s` contains the smallest congruence relation containing `r`. -/
theorem ring_con_gen_mono {r s : R → R → Prop} (h : ∀ x y, r x y → s x y) :
  ring_con_gen r ≤ ring_con_gen s :=
ring_con_gen_le $ λ x y hr, ring_con_gen.rel.of _ _ $ h x y hr

/-- Congruence relations equal the smallest congruence relation in which they are contained. -/
lemma ring_con_gen_of_ring_con (c : ring_con R) : ring_con_gen c = c :=
le_antisymm (by rw ring_con_gen_eq; exact Inf_le (λ _ _, id)) ring_con_gen.rel.of

/-- The map sending a binary relation to the smallest congruence relation in which it is
    contained is idempotent. -/
lemma ring_con_gen_idem (r : R → R → Prop) :
  ring_con_gen (ring_con_gen r) = ring_con_gen r :=
ring_con_gen_of_ring_con _

/-- The supremum of congruence relations `c, d` equals the smallest congruence relation containing
    the binary relation '`x` is related to `y` by `c` or `d`'. -/
lemma sup_eq_ring_con_gen (c d : ring_con R) :
  c ⊔ d = ring_con_gen (λ x y, c x y ∨ d x y) :=
begin
  rw ring_con_gen_eq,
  apply congr_arg Inf,
  simp only [le_def, or_imp_distrib, ← forall_and_distrib]
end

/-- The supremum of two congruence relations equals the smallest congruence relation containing
    the supremum of the underlying binary operations. -/
lemma sup_def {c d : ring_con R} : c ⊔ d = ring_con_gen (c.r ⊔ d.r) :=
by rw sup_eq_ring_con_gen; refl

/-- The supremum of a set of congruence relations `S` equals the smallest congruence relation
    containing the binary relation 'there exists `c ∈ S` such that `x` is related to `y` by
    `c`'. -/
lemma Sup_eq_ring_con_gen (S : set (ring_con R)) :
  Sup S = ring_con_gen (λ x y, ∃ c : ring_con R, c ∈ S ∧ c x y) :=
begin
  rw ring_con_gen_eq,
  apply congr_arg Inf,
  ext,
  exact ⟨λ h _ _ ⟨r, hr⟩, h hr.1 hr.2,
         λ h r hS _ _ hr, h _ _ ⟨r, hS, hr⟩⟩,
end

/-- The supremum of a set of congruence relations is the same as the smallest congruence relation
    containing the supremum of the set's image under the map to the underlying binary relation. -/
lemma Sup_def {S : set (ring_con R)} :
  Sup S = ring_con_gen (Sup (@set.image (ring_con R) (R → R → Prop) coe_fn S)) :=
begin
  rw [Sup_eq_ring_con_gen, Sup_image],
  congr' with x y,
  simp only [Sup_image, supr_apply, supr_Prop_eq, exists_prop, rel_eq_coe]
end

variables (R)

/-- There is a Galois insertion of congruence relations on a type with multiplication and addition
`R` into binary relations on `R`. -/
protected def gi :
  @galois_insertion (R → R → Prop) (ring_con R) _ _ ring_con_gen coe_fn :=
{ choice := λ r h, ring_con_gen r,
  gc := λ r c,
    ⟨λ H _ _ h, H $ ring_con_gen.rel.of _ _ h,
     λ H, ring_con_gen_of_ring_con c ▸ ring_con_gen_mono H⟩,
  le_l_u := λ x, (ring_con_gen_of_ring_con x).symm ▸ le_refl x,
  choice_eq := λ _ _, rfl }

end lattice

end ring_con
