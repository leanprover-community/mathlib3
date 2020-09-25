/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import algebra
import data.zmod.basic
import data.equiv.mul_add

/-!
# Racks and Quandles

This file defines racks and quandles, algebraic structures for sets
that bijectively act on themselves with a self-distributivity
property.  If `R` is a rack and `op : R → (R ≃ R)` is the self-action,
then the self-distributivity is, equivalently, that
```
op (op x y) = op x * op y * (op x)⁻¹
```
where multiplication is composition in `R ≃ R` as a group.
Quandles are racks such that `op x x = x` for all `x`.

One example of a quandle is the action of a Lie algebra on itself,
defined by `op x y = Ad (exp x) y`.

Quandles and racks were independently developed by multiple
mathematicians.  David Joyce introduced quandles in his thesis to
define an algebraic invariant of knot and link complements that is
analogous to the fundamental group of the exterior, and he showed that
the quandle associated to an oriented knot is invariant up to
orientation-reversed mirror image.  Racks were used by Fenn and Rourke
for framed codimension-2 knots and links.

The name "rack" came from wordplay by Conway and Wraith for the "wrack
and ruin" of forgetting everything but the conjugation operation for a
group.

## Main definitions

* `rack`
* `quandle`
* `quandle.conj` defines a quandle of a group acting on itself by conjugation.
* `rack_hom` is homomorphisms of racks and quandles.
* `rack.envel_group` gives the universal group the rack maps to as a conjugation quandle.
* `rack.opp` gives the rack with the action replaced by its inverse.

## Main statements
* `rack.envel_group` is universal (`to_envel_group.univ` and `to_envel_group.univ_uniq`)

## Notation
* `x ◃ y` is local notation for `rack.op x y`
* `x ◃⁻¹ y` is local notation for `rack.inv_op x y`

## Todo

* If g is the Lie algebra of a Lie group G, then (x ◃ y) = Ad (exp x) x forms a quandle
* If X is a symmetric space, then each point has a corresponding involution that acts on X, forming a quandle.
* Alexander quandle with `a ◃ b = t * b + (1 - t) * b`, with `a` and `b` elements of a module over Z[t,t⁻¹].
* If G is a group, H a subgroup, and z in H, then there is a quandle `(G/H;z)` defined by
  `yH ◃ Hx = yzy⁻¹xH`.  Every homogeneous quandle (i.e., a quandle Q whose automorphism group acts
  transitively on Q as a set) is isomorphic to such a quandle.
  There is a generalization to this arbitrary quandles in [Joyce's paper (Theorem 7.2)][Joyce1982].

## Tags

rack, quandle
-/

universes u v

/--
A *rack* is an automorphic set (a set with an action on itself) that is self-distributive.
The `x ◃ y` and `x ◃⁻¹ y` notation is right associative.

There is a weaker notion of a *shelf*, which would be from having `op' : α → α → α`.
-/
class rack (α : Type*) :=
(op' : α → (α ≃ α))
(self_distrib' : ∀ {x y z : α}, op' x (op' y z) = op' (op' x y) (op' x z))

/--
The rack operation.  Has notation `◃`.
-/
abbreviation rack.op {R : Type*} [rack R] (x y : R) : R := rack.op' x y
/--
The inverse of the rack operation. Has notation `◃⁻¹`.
-/
abbreviation rack.inv_op {R : Type*} [rack R] (x y : R) : R := (rack.op' x).symm y

local infixr ` ◃ ` : 65 := rack.op
local infixr ` ◃⁻¹ ` : 65 := rack.inv_op

namespace rack
variables {R : Type*} [rack R]

@[simp] lemma normalize_op (x y : R) : op' x y = x ◃ y := rfl
@[simp] lemma normalize_inv_op (x y : R) : (op' x).symm y = x ◃⁻¹ y := rfl
@[simp] lemma normalize_inv_op' (x y : R) : (op' x)⁻¹ y = x ◃⁻¹ y := rfl

@[simp] lemma left_inv (x y : R) : x ◃⁻¹ x ◃ y = y := (op' x).symm_apply_eq.mpr rfl
@[simp] lemma right_inv (x y : R) : x ◃ x ◃⁻¹ y = y := (op' x).eq_symm_apply.mp rfl

lemma self_distrib {x y z : R} : x ◃ y ◃ z = (x ◃ y) ◃ (x ◃ z) :=
rack.self_distrib'

lemma left_cancel (x : R) {y y' : R} : x ◃ y = x ◃ y' ↔ y = y' :=
by { split, apply (op' x).injective, rintro rfl, refl }

lemma left_cancel_inv (x : R) {y y' : R} : x ◃⁻¹ y = x ◃⁻¹ y' ↔ y = y' :=
by { split, apply (op' x).symm.injective, rintro rfl, refl }

lemma self_distrib_inv {x y z : R} : x ◃⁻¹ y ◃⁻¹ z = (x ◃⁻¹ y) ◃⁻¹ (x ◃⁻¹ z) :=
begin
  rw [←left_cancel (x ◃⁻¹ y), right_inv, ←left_cancel x, right_inv, self_distrib],
  repeat {rw right_inv },
end

/--
The *adjoint action* of a rack on itself is `op'`, and the adjoint
action of `x ◃ y` is the conjugate of the action of `y` by the action
of `x`. It is another way to understand the self-distributivity axiom.

This is used in the natural rack homomorphism `to_conj` from `R` to
`conj (R ≃ R)` defined by `op'`.
-/
lemma ad_conj {R : Type*} [rack R] (x y : R) :
  op' (x ◃ y) = op' x * op' y * (op' x)⁻¹ :=
begin
  apply @mul_right_cancel _ _ _ (op' x), ext z,
  simp only [inv_mul_cancel_right],
  apply self_distrib.symm,
end

/--
The opposite rack, swapping the roles of `◃` and `◃⁻¹`.
-/
@[nolint has_inhabited_instance]
def opp (R : Type*) := R

instance opp.rack : rack (opp R) :=
{ op' := λ (x : R), (op' x).symm,
  self_distrib' := λ (x y z : R), self_distrib_inv }


@[simp]
lemma self_op_op_eq {x y : R} : (x ◃ x) ◃ y = x ◃ y :=
by { rw [←right_inv x y, ←self_distrib] }

@[simp]
lemma self_op_inv_op_inv_eq {x y : R} : (x ◃⁻¹ x) ◃⁻¹ y = x ◃⁻¹ y :=
@self_op_op_eq (opp R) _ x y

@[simp]
lemma self_op_op_inv_eq {x y : R} : (x ◃ x) ◃⁻¹ y = x ◃⁻¹ y :=
by { rw ←left_cancel (x ◃ x), rw right_inv, rw self_op_op_eq, rw right_inv }

@[simp]
lemma self_op_inv_op_eq {x y : R} : (x ◃⁻¹ x) ◃ y = x ◃ y :=
@self_op_op_inv_eq (opp R) _ x y

lemma self_op_eq_iff_eq {x y : R} : x ◃ x = y ◃ y ↔ x = y :=
begin
  split, swap, rintro rfl, refl,
  intro h,
  transitivity (x ◃ x) ◃⁻¹ (x ◃ x),
  rw [←left_cancel (x ◃ x), right_inv, self_op_op_eq],
  rw [h, ←left_cancel (y ◃ y), right_inv, self_op_op_eq],
end

lemma self_op_inv_eq_iff_eq {x y : R} : x ◃⁻¹ x = y ◃⁻¹ y ↔ x = y :=
@self_op_eq_iff_eq (opp R) _ x y

/--
The map `x ↦ x ◃ x` is a bijection.  (This has applications for the
regular isotopy version of the Reidemeister I move for knot diagrams.)
-/
def self_apply_equiv (R : Type*) [rack R] : R ≃ R :=
{ to_fun := λ x, x ◃ x,
  inv_fun := λ x, x ◃⁻¹ x,
  left_inv := λ x, by simp,
  right_inv := λ x, by simp }

/--
An involutory rack is one for which `rack.op R x` is an involution for every x.
-/
def is_involutory (R : Type*) [rack R] : Prop := ∀ x : R, function.involutive (op' x)

lemma involutory_op_inv_eq_op {R : Type*} [rack R] (h : is_involutory R) (x y : R) :
  x ◃⁻¹ y = x ◃ y :=
begin
  rw [←left_cancel x, right_inv],
  exact((h x).left_inverse y).symm,
end

/--
An abelian rack is one for which the mediality axiom holds.
-/
def is_abelian (R : Type*) [rack R] : Prop :=
∀ (x y z w : R), (x ◃ y) ◃ (z ◃ w) = (x ◃ z) ◃ (y ◃ w)

/--
Associative racks are uninteresting.
-/
lemma assoc_iff_id {R : Type*} [rack R] {x y z : R} :
  x ◃ y ◃ z = (x ◃ y) ◃ z ↔ x ◃ z = z :=
by { rw self_distrib, rw left_cancel }

end rack

/--
The type of homomorphisms between racks.
This is also the notion of a quandle homomorphism.
-/
@[ext]
structure rack_hom (R₁ : Type*) (R₂ : Type*) [rack R₁] [rack R₂] :=
(to_fun : R₁ → R₂)
(map_op' : ∀ {x y : R₁}, to_fun (x ◃ y) = to_fun x ◃ to_fun y)

namespace rack_hom

attribute [simp] rack_hom.map_op'

instance (R₁ : Type*) (R₂ : Type*) [rack R₁] [rack R₂] : has_coe_to_fun (rack_hom R₁ R₂) :=
⟨_, rack_hom.to_fun⟩

@[simp]
lemma map_op {R₁ : Type*} {R₂ : Type*} [rack R₁] [rack R₂] (f : rack_hom R₁ R₂)
  (x y : R₁) : f (x ◃ y) = f x ◃ f y :=
rack_hom.map_op' f

/-- The identity homomorphism -/
def id (R : Type*) [rack R] : rack_hom R R :=
{ to_fun := id,
  map_op' := by simp }

instance inhabited (R : Type*) [rack R] : inhabited (rack_hom R R) :=
⟨id R⟩

variables {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [rack R₁] [rack R₂] [rack R₃]

/-- The composition of rack/quandle homomorphisms -/
def comp (g : rack_hom R₂ R₃) (f : rack_hom R₁ R₂) : rack_hom R₁ R₃ :=
{ to_fun := g.to_fun ∘ f.to_fun,
  map_op' := by simp }

@[simp]
lemma comp_apply (g : rack_hom R₂ R₃) (f : rack_hom R₁ R₂) (x : R₁) :
  (g.comp f) x = g (f x) := rfl

end rack_hom


/--
A quandle is a rack such that each automorphism fixes its corresponding element.
-/
class quandle (α : Type*) extends rack α :=
(fix' : ∀ {x : α}, op' x x = x)

namespace quandle
open rack
variables {Q : Type*} [quandle Q]

@[simp]
lemma fix {x : Q} : x ◃ x = x :=
quandle.fix'

lemma fix_inv {x : Q} : x ◃⁻¹ x = x :=
by { rw ←left_cancel x, simp }

instance opp.quandle : quandle (opp Q) :=
{ fix' := λ x, fix_inv }

/--
The conjugation quandle of a group.  Each element of the group acts by
the corresponding inner automorphism.
-/
@[nolint has_inhabited_instance]
def conj (G : Type*) := G

@[simp] lemma conj_conj_inv {G : Type*} [group G] (g h : G) : g * (g⁻¹ * h * g) * g⁻¹ = h :=
mul_inv_eq_of_eq_mul (mul_eq_of_eq_inv_mul (mul_assoc _ _ _))

@[simp] lemma conj_inv_conj {G : Type*} [group G] (g h : G) : g⁻¹ * (g * h * g⁻¹) * g = h :=
mul_eq_of_eq_mul_inv (inv_mul_eq_of_eq_mul (mul_assoc _ _ _))

instance conj.quandle (G : Type*) [group G] : quandle (conj G) :=
{ op' := (λ x, (@mul_aut.conj G _ x).to_equiv),
  self_distrib' := λ x y z, by simp,
  fix' := λ x, by simp }

@[simp]
lemma conj_op_eq_conj {G : Type*} [group G] (x y : conj G) :
  x ◃ y = ((x : G) * (y : G) * (x : G)⁻¹ : G) := rfl

lemma conj_swap {G : Type*} [group G] (x y : conj G) :
  x ◃ y = y ↔ y ◃ x = x :=
begin
  dsimp, split,
  repeat { intro h, conv_rhs { rw eq_mul_inv_of_mul_eq (eq_mul_inv_of_mul_eq h) }, simp, },
end

/--
`conj` is functorial
-/
def conj.map {G : Type*} {H : Type*} [group G] [group H] (f : G →* H) : rack_hom (conj G) (conj H) :=
{ to_fun := f,
  map_op' := by simp }

instance {G : Type*} {H : Type*} [group G] [group H] : has_lift (G →* H) (rack_hom (conj G) (conj H)) :=
{ lift := conj.map }

/--
The dihedral quandle. This is the conjugation quandle of the dihedral group restrict to flips.

Used for Fox n-colorings of knots.
-/
@[nolint has_inhabited_instance]
def dihedral (n : ℕ) := zmod n

/--
The operation for the dihedral quandle.  It does not need to be an equivalence
because it is an involution (see `dihedral_op.inv`).
-/
def dihedral_op (n : ℕ) (a : zmod n) : zmod n → zmod n :=
λ b, 2 * a - b

lemma dihedral_op.inv (n : ℕ) (a : zmod n) : function.involutive (dihedral_op n a) :=
by { intro b, dsimp [dihedral_op], ring }

instance (n : ℕ) : quandle (dihedral n) :=
{ op' := λ a, function.involutive.to_equiv _ (dihedral_op.inv n a),
  self_distrib' := λ x y z, begin
    dsimp [function.involutive.to_equiv, dihedral_op], ring,
  end,
  fix' := λ x, begin
    dsimp [op', function.involutive.to_equiv, dihedral_op], ring,
  end }


end quandle

namespace rack

/--
This is the natural rack homomorphism to the conjugation quandle of the group `R ≃ R`
that acts on the rack.
-/
def to_conj (R : Type*) [rack R] : rack_hom R (quandle.conj (R ≃ R)) :=
{ to_fun := op',
  map_op' := ad_conj }


section envel_group

/-!
## Universal enveloping group of a rack

Joyce, for quandles, called this AdConj.
-/

/--
Free generators of the enveloping group.
-/
inductive pre_envel_group (R : Type u) : Type u
| unit : pre_envel_group
| incl (x : R) : pre_envel_group
| mul (a b : pre_envel_group) : pre_envel_group
| inv (a : pre_envel_group) : pre_envel_group

instance pre_envel_group.inhabited (R : Type u) : inhabited (pre_envel_group R) :=
⟨pre_envel_group.unit⟩

open pre_envel_group

/--
Relations for the enveloping group.
-/
inductive pre_envel_group_rel' (R : Type u) [rack R] : pre_envel_group R → pre_envel_group R → Type u
| refl {a : pre_envel_group R} : pre_envel_group_rel' a a
| symm {a b : pre_envel_group R} (hab : pre_envel_group_rel' a b) : pre_envel_group_rel' b a
| trans {a b c : pre_envel_group R}
  (hab : pre_envel_group_rel' a b) (hbc : pre_envel_group_rel' b c) : pre_envel_group_rel' a c
| congr_mul {a b a' b' : pre_envel_group R}
  (ha : pre_envel_group_rel' a a') (hb : pre_envel_group_rel' b b') :
  pre_envel_group_rel' (mul a b) (mul a' b')
| congr_inv {a a' : pre_envel_group R} (ha : pre_envel_group_rel' a a') :
  pre_envel_group_rel' (inv a) (inv a')
| assoc (a b c : pre_envel_group R) : pre_envel_group_rel' (mul (mul a b) c) (mul a (mul b c))
| one_mul (a : pre_envel_group R) : pre_envel_group_rel' (mul unit a) a
| mul_one (a : pre_envel_group R) : pre_envel_group_rel' (mul a unit) a
| mul_left_inv (a : pre_envel_group R) : pre_envel_group_rel' (mul (inv a) a) unit
| op_incl (x y : R) :
  pre_envel_group_rel' (mul (mul (incl x) (incl y)) (inv (incl x))) (incl (x ◃ y))

instance pre_envel_group_rel'.inhabited (R : Type u) [rack R] :
  inhabited (pre_envel_group_rel' R unit unit) :=
⟨pre_envel_group_rel'.refl⟩

/--
The above relation as a `Prop`.
-/
inductive pre_envel_group_rel (R : Type u) [rack R] : pre_envel_group R → pre_envel_group R → Prop
| rel {a b : pre_envel_group R} (r : pre_envel_group_rel' R a b) : pre_envel_group_rel a b

/--
A quick way to convert a `pre_envel_group_rel'` to a `pre_envel_group_rel`.
-/
lemma pre_envel_group_rel'.rel {R : Type u} [rack R] {a b : pre_envel_group R} :
  pre_envel_group_rel' R a b → pre_envel_group_rel R a b :=
pre_envel_group_rel.rel

@[refl]
lemma pre_envel_group_rel.refl {R : Type u} [rack R] {a : pre_envel_group R} :
  pre_envel_group_rel R a a :=
pre_envel_group_rel.rel pre_envel_group_rel'.refl

@[symm]
lemma pre_envel_group_rel.symm {R : Type u} [rack R] {a b : pre_envel_group R} :
  pre_envel_group_rel R a b → pre_envel_group_rel R b a
| ⟨r⟩ := r.symm.rel

@[trans]
lemma pre_envel_group_rel.trans {R : Type u} [rack R] {a b c : pre_envel_group R} :
  pre_envel_group_rel R a b → pre_envel_group_rel R b c → pre_envel_group_rel R a c
| ⟨rab⟩ ⟨rbc⟩ := (rab.trans rbc).rel

instance pre_envel_group.setoid (R : Type*) [rack R] : setoid (pre_envel_group R) :=
{ r := pre_envel_group_rel R,
  iseqv := begin
    split, apply pre_envel_group_rel.refl,
    split, apply pre_envel_group_rel.symm,
    apply pre_envel_group_rel.trans
  end }

/--
The universal enveloping group for the rack R.
-/
def envel_group (R : Type*) [rack R] := quotient (pre_envel_group.setoid R)

instance (R : Type*) [rack R] : group (envel_group R) :=
{ mul := λ a b, quotient.lift_on₂ a b
                  (λ a b, ⟦pre_envel_group.mul a b⟧)
                  (λ a b a' b' ⟨ha⟩ ⟨hb⟩,
                    quotient.sound (pre_envel_group_rel'.congr_mul ha hb).rel),
  one := ⟦unit⟧,
  inv := λ a, quotient.lift_on a
                (λ a, ⟦pre_envel_group.inv a⟧)
                (λ a a' ⟨ha⟩,
                  quotient.sound (pre_envel_group_rel'.congr_inv ha).rel),
  mul_assoc := λ a b c,
    quotient.induction_on₃ a b c (λ a b c, quotient.sound (pre_envel_group_rel'.assoc a b c).rel),
  one_mul := λ a,
    quotient.induction_on a (λ a, quotient.sound (pre_envel_group_rel'.one_mul a).rel),
  mul_one := λ a,
    quotient.induction_on a (λ a, quotient.sound (pre_envel_group_rel'.mul_one a).rel),
  mul_left_inv := λ a,
    quotient.induction_on a (λ a, quotient.sound (pre_envel_group_rel'.mul_left_inv a).rel) }

instance envel_group.inhabited (R : Type*) [rack R] : inhabited (envel_group R) := ⟨1⟩

/--
The canonical homomorphism from a rack to its enveloping group.
Satisfies universal properties given by `to_envel_group.map` and `to_envel_group.univ`.
-/
def to_envel_group (R : Type*) [rack R] : rack_hom R (quandle.conj (envel_group R)) :=
{ to_fun := λ x, ⟦incl x⟧,
  map_op' := λ x y, quotient.sound (pre_envel_group_rel'.op_incl x y).symm.rel }

/--
The preliminary definition of the induced map from the enveloping group.
See `to_envel_group.map`.
-/
def to_envel_group.map_aux {R : Type*} [rack R] {G : Type*} [group G]
  (f : rack_hom R (quandle.conj G)) : pre_envel_group R → G
| unit := 1
| (incl x) := f x
| (mul a b) := to_envel_group.map_aux a * to_envel_group.map_aux b
| (inv a) := (to_envel_group.map_aux a)⁻¹

namespace to_envel_group.map_aux
open pre_envel_group_rel'

/--
Show that `to_envel_group.map_aux` sends equivalent expressions to equal terms.
-/
lemma well_def {R : Type*} [rack R] {G : Type*} [group G] (f : rack_hom R (quandle.conj G)) :
  Π {a b : pre_envel_group R}, pre_envel_group_rel' R a b →
  to_envel_group.map_aux f a = to_envel_group.map_aux f b
| a b refl := rfl
| a b (symm h) := (well_def h).symm
| a b (trans hac hcb) := eq.trans (well_def hac) (well_def hcb)
| _ _ (congr_mul ha hb) := by { dsimp [to_envel_group.map_aux], rw well_def ha, rw well_def hb, }
| _ _ (congr_inv ha) := by { dsimp [to_envel_group.map_aux], rw well_def ha }
| _ _ (assoc a b c) := by { apply mul_assoc }
| _ _ (one_mul a) := by { dsimp [to_envel_group.map_aux], simp, }
| _ _ (mul_one a) := by { dsimp [to_envel_group.map_aux], simp, }
| _ _ (mul_left_inv a) := by { dsimp [to_envel_group.map_aux], simp, }
| _ _ (op_incl x y) := by { dsimp [to_envel_group.map_aux], simp, }

end to_envel_group.map_aux

/--
Given a map from a rack to a group, lift it to being a map from the enveloping group.
-/
def to_envel_group.map {R : Type*} [rack R] {G : Type*} [group G]
  (f : rack_hom R (quandle.conj G)) : envel_group R →* G :=
{ to_fun := λ x, quotient.lift_on x (to_envel_group.map_aux f)
                   (λ a b ⟨hab⟩, to_envel_group.map_aux.well_def f hab),
  map_one' := begin
    change quotient.lift_on ⟦unit⟧ (to_envel_group.map_aux f) _ = 1,
    simp [to_envel_group.map_aux],
  end,
  map_mul' := λ x y, quotient.induction_on₂ x y (λ x y, begin
    change quotient.lift_on ⟦mul x y⟧ (to_envel_group.map_aux f) _ = _,
    simp [to_envel_group.map_aux],
  end) }

/--
Given a homomorphism from a rack to a group, it factors through the enveloping group.
-/
lemma to_envel_group.univ (R : Type*) [rack R] (G : Type*) [group G]
  (f : rack_hom R (quandle.conj G)) :
  (quandle.conj.map (to_envel_group.map f)).comp (to_envel_group R) = f :=
by { ext, refl }

/--
The homomorphism `to_envel_group.map f` is the unique map that fits into the commutative
triangle in `to_envel_group.univ`.
-/
lemma to_envel_group.univ_uniq (R : Type*) [rack R] (G : Type*) [group G]
  (f : rack_hom R (quandle.conj G))
  (g : envel_group R →* G) (h : f = (quandle.conj.map g).comp (to_envel_group R)) :
  g = to_envel_group.map f :=
begin
  subst f, ext, refine quotient.ind (λ x, _) x,
  induction x,
  convert g.map_one, refl,
  dunfold to_envel_group.map, simp [to_envel_group.map_aux, to_envel_group],
  have hm : ⟦x_a.mul x_b⟧ = @has_mul.mul (envel_group R) _ ⟦x_a⟧ ⟦x_b⟧ := rfl,
  rw hm, simpa [x_ih_a, x_ih_b],
  have hm : ⟦x_a.inv⟧ = @has_inv.inv (envel_group R) _ ⟦x_a⟧ := rfl,
  rw hm, simp [x_ih],
end

/--
The induced group homomorphism from the enveloping group into bijections of the rack,
using `rack.to_conj`. Satisfies the property `envel_action_prop`.

This gives the rack `R` the structure of an augmented rack over `envel_group R`.
-/
def envel_action {R : Type*} [rack R] : envel_group R →* (R ≃ R) :=
to_envel_group.map (to_conj R)

@[simp]
lemma envel_action_prop {R : Type*} [rack R] (x y : R) :
  envel_action (to_envel_group R x) y = x ◃ y := rfl

end envel_group

end rack
