/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston
-/

import algebra.group
import tactic.norm_cast

/-!
# Properties and homomorphisms of semirings and rings

This file proves simple properties of semirings, rings and domains and their unit groups. It also
defines homomorphisms of semirings and rings, both unbundled (e.g. `is_semiring_hom f`)
and bundled (e.g. `ring_hom a β`, a.k.a. `α →+* β`). The unbundled ones are deprecated
and the plan is to slowly remove them from mathlib.

## Main definitions

is_semiring_hom (deprecated), is_ring_hom (deprecated), ring_hom, nonzero_comm_semiring,
nonzero_comm_ring, domain

## Notations

→+* for bundled ring homs (also use for semiring homs)

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical
notation is to use the bundled hom as a function via this coercion.

There is no `semiring_hom` -- the idea is that `ring_hom` is used.
The constructor for a `ring_hom` between semirings needs a proof of `map_zero`, `map_one` and
`map_add` as well as `map_mul`; a separate constructor `ring_hom.mk'` will construct ring homs
between rings from monoid homs given only a proof that addition is preserved.


Throughout the section on `ring_hom` implicit `{}` brackets are often used instead of type class `[]` brackets.
This is done when the instances can be inferred because they are implicit arguments to the type `ring_hom`.
When they can be inferred from the type it is faster to use this method than to use type class inference.

## Tags

is_ring_hom, is_semiring_hom, ring_hom, semiring_hom, semiring, comm_semiring, ring, comm_ring,
domain, integral_domain, nonzero_comm_semiring, nonzero_comm_ring, units
-/
universes u v w
variable {α : Type u}

section
variable [semiring α]

theorem mul_two (n : α) : n * 2 = n + n :=
(left_distrib n 1 1).trans (by simp)

theorem bit0_eq_two_mul (n : α) : bit0 n = 2 * n :=
(two_mul _).symm

@[simp] lemma mul_ite {α} [semiring α] (P : Prop) [decidable P] (a : α) :
  a * (if P then 1 else 0) = if P then a else 0 :=
by split_ifs; simp

@[simp] lemma ite_mul {α} [semiring α] (P : Prop) [decidable P] (a : α) :
  (if P then 1 else 0) * a = if P then a else 0 :=
by split_ifs; simp

variable (α)

/-- Either zero and one are nonequal in a semiring, or the semiring is the zero ring. -/
lemma zero_ne_one_or_forall_eq_0 : (0 : α) ≠ 1 ∨ (∀a:α, a = 0) :=
by haveI := classical.dec;
   refine not_or_of_imp (λ h a, _); simpa using congr_arg ((*) a) h.symm

/-- If zero equals one in a semiring, the semiring is the zero ring. -/
lemma eq_zero_of_zero_eq_one (h : (0 : α) = 1) : (∀a:α, a = 0) :=
(zero_ne_one_or_forall_eq_0 α).neg_resolve_left h

/-- If zero equals one in a semiring, all elements of that semiring are equal. -/
theorem subsingleton_of_zero_eq_one (h : (0 : α) = 1) : subsingleton α :=
⟨λa b, by rw [eq_zero_of_zero_eq_one α h a, eq_zero_of_zero_eq_one α h b]⟩

end

namespace units
variables [ring α] {a b : α}

/-- Each element of the group of units of a ring has an additive inverse. -/
instance : has_neg (units α) := ⟨λu, ⟨-↑u, -↑u⁻¹, by simp, by simp⟩ ⟩

/-- Representing an element of a ring's unit group as an element of the ring commutes with
    mapping this element to its additive inverse. -/
@[simp] protected theorem coe_neg (u : units α) : (↑-u : α) = -u := rfl

/-- Mapping an element of a ring's unit group to its inverse commutes with mapping this element
    to its additive inverse. -/
@[simp] protected theorem neg_inv (u : units α) : (-u)⁻¹ = -u⁻¹ := rfl

/-- An element of a ring's unit group equals the additive inverse of its additive inverse. -/
@[simp] protected theorem neg_neg (u : units α) : - -u = u :=
units.ext $ neg_neg _

/-- Multiplication of elements of a ring's unit group commutes with mapping the first
    argument to its additive inverse. -/
@[simp] protected theorem neg_mul (u₁ u₂ : units α) : -u₁ * u₂ = -(u₁ * u₂) :=
units.ext $ neg_mul_eq_neg_mul_symm _ _

/-- Multiplication of elements of a ring's unit group commutes with mapping the second argument
    to its additive inverse. -/
@[simp] protected theorem mul_neg (u₁ u₂ : units α) : u₁ * -u₂ = -(u₁ * u₂) :=
units.ext $ (neg_mul_eq_mul_neg _ _).symm

/-- Multiplication of the additive inverses of two elements of a ring's unit group equals
    multiplication of the two original elements. -/
@[simp] protected theorem neg_mul_neg (u₁ u₂ : units α) : -u₁ * -u₂ = u₁ * u₂ := by simp

/-- The additive inverse of an element of a ring's unit group equals the additive inverse of
    one times the original element. -/
protected theorem neg_eq_neg_one_mul (u : units α) : -u = -1 * u := by simp

end units

instance [semiring α] : semiring (with_zero α) :=
{ left_distrib := λ a b c, begin
    cases a with a, {refl},
    cases b with b; cases c with c; try {refl},
    exact congr_arg some (left_distrib _ _ _)
  end,
  right_distrib := λ a b c, begin
    cases c with c,
    { change (a + b) * 0 = a * 0 + b * 0, simp },
    cases a with a; cases b with b; try {refl},
    exact congr_arg some (right_distrib _ _ _)
  end,
  ..with_zero.add_comm_monoid,
  ..with_zero.mul_zero_class,
  ..with_zero.monoid }

attribute [refl] dvd_refl
attribute [trans] dvd.trans

/-- Predicate for semiring homomorphisms (deprecated -- use the bundled `ring_hom` version). -/
class is_semiring_hom {α : Type u} {β : Type v} [semiring α] [semiring β] (f : α → β) : Prop :=
(map_zero : f 0 = 0)
(map_one : f 1 = 1)
(map_add : ∀ {x y}, f (x + y) = f x + f y)
(map_mul : ∀ {x y}, f (x * y) = f x * f y)

namespace is_semiring_hom

variables {β : Type v} [semiring α] [semiring β]
variables (f : α → β) [is_semiring_hom f] {x y : α}

/-- The identity map is a semiring homomorphism. -/
instance id : is_semiring_hom (@id α) := by refine {..}; intros; refl

/-- The composition of two semiring homomorphisms is a semiring homomorphism. -/
@[priority 10] -- see Note [low priority instance on morphisms]
instance comp {γ} [semiring γ] (g : β → γ) [is_semiring_hom g] :
  is_semiring_hom (g ∘ f) :=
{ map_zero := by simp [map_zero f]; exact map_zero g,
  map_one := by simp [map_one f]; exact map_one g,
  map_add := λ x y, by simp [map_add f]; rw map_add g; refl,
  map_mul := λ x y, by simp [map_mul f]; rw map_mul g; refl }

/-- A semiring homomorphism is an additive monoid homomorphism. -/
@[priority 100] -- see Note [lower instance priority]
instance : is_add_monoid_hom f :=
{ ..‹is_semiring_hom f› }

/-- A semiring homomorphism is a monoid homomorphism. -/
@[priority 100] -- see Note [lower instance priority]
instance : is_monoid_hom f :=
{ ..‹is_semiring_hom f› }

end is_semiring_hom

section
  variables [ring α] (a b c d e : α)

/-- An element of a ring multiplied by the additive inverse of one is the element's additive
    inverse. -/
  lemma mul_neg_one (a : α) : a * -1 = -a := by simp

/-- The additive inverse of one multiplied by an element of a ring is the element's additive
    inverse. -/
  lemma neg_one_mul (a : α) : -1 * a = -a := by simp

/-- An iff statement following from right distributivity in rings and the definition
    of subtraction. -/
  theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
  calc
    a * e + c = b * e + d ↔ a * e + c = d + b * e : by simp
      ... ↔ a * e + c - b * e = d : iff.intro (λ h, begin simp [h] end) (λ h,
                                                    begin simp [h.symm] end)
      ... ↔ (a - b) * e + c = d   : begin simp [@sub_eq_add_neg α, @right_distrib α] end

/-- A simplification of one side of an equation exploiting right distributivity in rings
    and the definition of subtraction. -/
  theorem sub_mul_add_eq_of_mul_add_eq_mul_add : a * e + c = b * e + d → (a - b) * e + c = d :=
  assume h,
  calc
    (a - b) * e + c = (a * e + c) - b * e : begin simp [@sub_eq_add_neg α, @right_distrib α] end
                ... = d                   : begin rw h, simp [@add_sub_cancel α] end

/-- If the product of two elements of a ring is nonzero, both elements are nonzero. -/
  theorem ne_zero_and_ne_zero_of_mul_ne_zero {a b : α} (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  begin
    split,
    { intro ha, apply h, simp [ha] },
    { intro hb, apply h, simp [hb] }
  end

end

/-- Given an element a of a commutative semiring, there exists another element whose product
    with zero equals a iff a equals zero. -/
@[simp] lemma zero_dvd_iff [comm_semiring α] {a : α} : 0 ∣ a ↔ a = 0 :=
⟨eq_zero_of_zero_dvd, λ h, by rw h⟩

section comm_ring
  variable [comm_ring α]

/-- Representation of a difference of two squares in a commutative ring as a product. -/
  theorem mul_self_sub_mul_self (a b : α) : a * a - b * b = (a + b) * (a - b) :=
  by rw [add_mul, mul_sub, mul_sub, mul_comm a b, sub_add_sub_cancel]

/-- An element a of a commutative ring divides the additive inverse of an element b iff a
    divides b. -/
  @[simp] lemma dvd_neg (a b : α) : (a ∣ -b) ↔ (a ∣ b) :=
  ⟨dvd_of_dvd_neg, dvd_neg_of_dvd⟩

/-- The additive inverse of an element a of a commutative ring divides another element b iff a
    divides b. -/
  @[simp] lemma neg_dvd (a b : α) : (-a ∣ b) ↔ (a ∣ b) :=
  ⟨dvd_of_neg_dvd, neg_dvd_of_dvd⟩

/-- If an element a divides another element c in a commutative ring, a divides the sum of another
    element b with c iff a divides b. -/
  theorem dvd_add_left {a b c : α} (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  (dvd_add_iff_left h).symm

/-- If an element a divides another element b in a commutative ring, a divides the sum of b and
    another element c iff a divides c. -/
  theorem dvd_add_right {a b c : α} (h : a ∣ b) : a ∣ b + c ↔ a ∣ c :=
  (dvd_add_iff_right h).symm

/-- An element a divides the sum a + b if and only if a divides b.-/
@[simp] lemma dvd_add_self_left {a b : α} :
  a ∣ a + b ↔ a ∣ b :=
dvd_add_right (dvd_refl a)

/-- An element a divides the sum b + a if and only if a divides b.-/
@[simp] lemma dvd_add_self_right {a b : α} :
  a ∣ b + a ↔ a ∣ b :=
dvd_add_left (dvd_refl a)

/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
lemma Vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
  ∃ y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c :=
begin
  have : c = b * x - x * x, { apply eq_of_sub_eq_zero, simpa using h },
  use b - x, simp [left_distrib, mul_comm, this],
end

end comm_ring

/-- Predicate for ring homomorphisms (deprecated -- use the bundled `ring_hom` version). -/
class is_ring_hom {α : Type u} {β : Type v} [ring α] [ring β] (f : α → β) : Prop :=
(map_one : f 1 = 1)
(map_mul : ∀ {x y}, f (x * y) = f x * f y)
(map_add : ∀ {x y}, f (x + y) = f x + f y)

namespace is_ring_hom

variables {β : Type v} [ring α] [ring β]

/-- A map of rings that is a semiring homomorphism is also a ring homomorphism. -/
lemma of_semiring (f : α → β) [H : is_semiring_hom f] : is_ring_hom f := {..H}

variables (f : α → β) [is_ring_hom f] {x y : α}

/-- Ring homomorphisms map zero to zero. -/
lemma map_zero : f 0 = 0 :=
calc f 0 = f (0 + 0) - f 0 : by rw [map_add f]; simp
     ... = 0 : by simp

/-- Ring homomorphisms preserve additive inverses. -/
lemma map_neg : f (-x) = -f x :=
calc f (-x) = f (-x + x) - f x : by rw [map_add f]; simp
        ... = -f x : by simp [map_zero f]

/-- Ring homomorphisms preserve subtraction. -/
lemma map_sub : f (x - y) = f x - f y :=
by simp [map_add f, map_neg f]

/-- The identity map is a ring homomorphism. -/
instance id : is_ring_hom (@id α) := by refine {..}; intros; refl

/-- The composition of two ring homomorphisms is a ring homomorphism. -/
@[priority 10] -- see Note [low priority instance on morphisms]
instance comp {γ} [ring γ] (g : β → γ) [is_ring_hom g] :
  is_ring_hom (g ∘ f) :=
{ map_add := λ x y, by simp [map_add f]; rw map_add g; refl,
  map_mul := λ x y, by simp [map_mul f]; rw map_mul g; refl,
  map_one := by simp [map_one f]; exact map_one g }

/-- A ring homomorphism is also a semiring homomorphism. -/
@[priority 100] -- see Note [lower instance priority]
instance : is_semiring_hom f :=
{ map_zero := map_zero f, ..‹is_ring_hom f› }

@[priority 100] -- see Note [lower instance priority]
instance : is_add_group_hom f := { }

end is_ring_hom

set_option old_structure_cmd true

section prio
set_option default_priority 100 -- see Note [default priority]
/-- Bundled semiring homomorphisms; use this for bundled ring homomorphisms too. -/
structure ring_hom (α : Type*) (β : Type*) [semiring α] [semiring β]
  extends monoid_hom α β, add_monoid_hom α β
end prio

infixr ` →+* `:25 := ring_hom

instance {α : Type*} {β : Type*} {rα : semiring α} {rβ : semiring β} : has_coe_to_fun (α →+* β) :=
⟨_, ring_hom.to_fun⟩

instance {α : Type*} {β : Type*} {rα : semiring α} {rβ : semiring β} : has_coe (α →+* β) (α →* β) :=
⟨ring_hom.to_monoid_hom⟩

instance {α : Type*} {β : Type*} {rα : semiring α} {rβ : semiring β} : has_coe (α →+* β) (α →+ β) :=
⟨ring_hom.to_add_monoid_hom⟩

@[squash_cast] lemma coe_monoid_hom {α : Type*} {β : Type*} {rα : semiring α} {rβ : semiring β} (f : α →+* β) (a : α) :
  ((f : α →* β) : α → β) a = (f : α → β) a := rfl
@[squash_cast] lemma coe_add_monoid_hom {α : Type*} {β : Type*} {rα : semiring α} {rβ : semiring β} (f : α →+* β) (a : α) :
  ((f : α →+ β) : α → β) a = (f : α → β) a := rfl

namespace ring_hom

variables {β : Type v} {γ : Type w} [rα : semiring α] [rβ : semiring β]

include rα rβ

/-- Interpret `f : α → β` with `is_semiring_hom f` as a ring homomorphism. -/
def of (f : α → β) [is_semiring_hom f] : α →+* β :=
{ to_fun := f,
  .. monoid_hom.of f,
  .. add_monoid_hom.of f }

@[simp] lemma coe_of (f : α → β) [is_semiring_hom f] : ⇑(of f) = f := rfl

variables (f : α →+* β) {x y : α} {rα rβ}

theorem coe_inj ⦃f g : α →+* β⦄ (h : (f : α → β) = g) : f = g :=
by cases f; cases g; cases h; refl

@[ext] theorem ext ⦃f g : α →+* β⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj (funext h)

theorem ext_iff {f g : α →+* β} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

/-- Ring homomorphisms map zero to zero. -/
@[simp] lemma map_zero (f : α →+* β) : f 0 = 0 := f.map_zero'

/-- Ring homomorphisms map one to one. -/
@[simp] lemma map_one (f : α →+* β) : f 1 = 1 := f.map_one'

/-- Ring homomorphisms preserve addition. -/
@[simp] lemma map_add (f : α →+* β) (a b : α) : f (a + b) = f a + f b := f.map_add' a b

/-- Ring homomorphisms preserve multiplication. -/
@[simp] lemma map_mul (f : α →+* β) (a b : α) : f (a * b) = f a * f b := f.map_mul' a b

instance (f : α →+* β) : is_semiring_hom f :=
{ map_zero := f.map_zero,
  map_one := f.map_one,
  map_add := f.map_add,
  map_mul := f.map_mul }

omit rα rβ

instance {α γ} [ring α] [ring γ] (g : α →+* γ) : is_ring_hom g :=
is_ring_hom.of_semiring g

/-- The identity ring homomorphism from a semiring to itself. -/
def id (α : Type*) [semiring α] : α →+* α :=
by refine {to_fun := id, ..}; intros; refl

include rα

@[simp] lemma id_apply : ring_hom.id α x = x := rfl

variable {rγ : semiring γ}
include rβ rγ

/-- Composition of ring homomorphisms is a ring homomorphism. -/
def comp (hnp : β →+* γ) (hmn : α →+* β) : α →+* γ :=
{ to_fun := hnp ∘ hmn,
  map_zero' := by simp,
  map_one' := by simp,
  map_add' := λ x y, by simp,
  map_mul' := λ x y, by simp}

/-- Composition of semiring homomorphisms is associative. -/
lemma comp_assoc {δ} {rδ: semiring δ} (f : α →+* β) (g : β →+* γ) (h : γ →+* δ) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp] lemma coe_comp (hnp : β →+* γ) (hmn : α →+* β) : (hnp.comp hmn : α → γ) = hnp ∘ hmn := rfl

@[simp] lemma comp_apply (hnp : β →+* γ) (hmn : α →+* β) (x : α) : (hnp.comp hmn : α → γ) x =
  (hnp (hmn x)) := rfl

omit rα rβ rγ

/-- Ring homomorphisms preserve additive inverse. -/
@[simp] theorem map_neg {α β} [ring α] [ring β] (f : α →+* β) (x : α) : f (-x) = -(f x) :=
eq_neg_of_add_eq_zero $ by rw [←f.map_add, neg_add_self, f.map_zero]

/-- Ring homomorphisms preserve subtraction. -/
@[simp] theorem map_sub {α β} [ring α] [ring β] (f : α →+* β) (x y : α) :
  f (x - y) = (f x) - (f y) := by simp

/-- A ring homomorphism is injective iff its kernel is trivial. -/
theorem injective_iff {α β} [ring α] [ring β] (f : α →+* β) :
  function.injective f ↔ (∀ a, f a = 0 → a = 0) :=
add_monoid_hom.injective_iff f.to_add_monoid_hom
include rα

/-- Makes a ring homomorphism from a monoid homomorphism of rings which preserves addition. -/
def mk' {γ} [ring γ] (f : α →* γ) (map_add : ∀ a b : α, f (a + b) = f a + f b) : α →+* γ :=
{ to_fun := f,
  map_zero' := add_self_iff_eq_zero.1 $ by rw [←map_add, add_zero],
  map_one' := f.map_one,
  map_mul' := f.map_mul,
  map_add' := map_add }

end ring_hom

section prio
set_option default_priority 100 -- see Note [default priority]
/-- Predicate for commutative semirings in which zero does not equal one. -/
class nonzero_comm_semiring (α : Type*) extends comm_semiring α, zero_ne_one_class α

/-- Predicate for commutative rings in which zero does not equal one. -/
class nonzero_comm_ring (α : Type*) extends comm_ring α, zero_ne_one_class α
end prio

/-- A nonzero commutative ring is a nonzero commutative semiring. -/
@[priority 100] -- see Note [lower instance priority]
instance nonzero_comm_ring.to_nonzero_comm_semiring {α : Type*} [I : nonzero_comm_ring α] :
  nonzero_comm_semiring α :=
{ zero_ne_one := by convert zero_ne_one,
  ..show comm_semiring α, by apply_instance }

/-- An integral domain is a nonzero commutative ring. -/
@[priority 100] -- see Note [lower instance priority]
instance integral_domain.to_nonzero_comm_ring (α : Type*) [id : integral_domain α] :
  nonzero_comm_ring α :=
{ ..id }

/-- An element of the unit group of a nonzero commutative semiring represented as an element
    of the semiring is nonzero. -/
lemma units.coe_ne_zero [nonzero_comm_semiring α] (u : units α) : (u : α) ≠ 0 :=
λ h : u.1 = 0, by simpa [h, zero_ne_one] using u.3

/-- Makes a nonzero commutative ring from a commutative ring containing at least two distinct
    elements. -/
def nonzero_comm_ring.of_ne [comm_ring α] {x y : α} (h : x ≠ y) : nonzero_comm_ring α :=
{ one := 1,
  zero := 0,
  zero_ne_one := λ h01, h $ by rw [← one_mul x, ← one_mul y, ← h01, zero_mul, zero_mul],
  ..show comm_ring α, by apply_instance }

/-- Makes a nonzero commutative semiring from a commutative semiring containing at least two
    distinct elements. -/
def nonzero_comm_semiring.of_ne [comm_semiring α] {x y : α} (h : x ≠ y) : nonzero_comm_semiring α :=
{ one := 1,
  zero := 0,
  zero_ne_one := λ h01, h $ by rw [← one_mul x, ← one_mul y, ← h01, zero_mul, zero_mul],
  ..show comm_semiring α, by apply_instance }

/-- this is needed for compatibility between Lean 3.4.2 and Lean 3.5.1c -/
def has_div_of_division_ring [division_ring α] : has_div α := division_ring_has_div

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A domain is a ring with no zero divisors, i.e. satisfying
  the condition `a * b = 0 ↔ a = 0 ∨ b = 0`. Alternatively, a domain
  is an integral domain without assuming commutativity of multiplication. -/
class domain (α : Type u) extends ring α, no_zero_divisors α, zero_ne_one_class α
end prio

section domain
  variable [domain α]

/-- Simplification theorems for the definition of a domain. -/
  @[simp] theorem mul_eq_zero {a b : α} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero, λo,
    or.elim o (λh, by rw h; apply zero_mul) (λh, by rw h; apply mul_zero)⟩

  @[simp] theorem zero_eq_mul {a b : α} : 0 = a * b ↔ a = 0 ∨ b = 0 :=
  by rw [eq_comm, mul_eq_zero]

  lemma mul_self_eq_zero {α} [domain α] {x : α} : x * x = 0 ↔ x = 0 := by simp
  lemma zero_eq_mul_self {α} [domain α] {x : α} : 0 = x * x ↔ x = 0 := by simp

/-- The product of two nonzero elements of a domain is nonzero. -/
  theorem mul_ne_zero' {a b : α} (h₁ : a ≠ 0) (h₂ : b ≠ 0) : a * b ≠ 0 :=
  λ h, or.elim (eq_zero_or_eq_zero_of_mul_eq_zero h) h₁ h₂

/-- Right multiplication by a nonzero element in a domain is injective. -/
  theorem domain.mul_right_inj {a b c : α} (ha : a ≠ 0) : b * a = c * a ↔ b = c :=
  by rw [← sub_eq_zero, ← mul_sub_right_distrib, mul_eq_zero];
     simp [ha]; exact sub_eq_zero

/-- Left multiplication by a nonzero element in a domain is injective. -/
  theorem domain.mul_left_inj {a b c : α} (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  by rw [← sub_eq_zero, ← mul_sub_left_distrib, mul_eq_zero];
     simp [ha]; exact sub_eq_zero

/-- An element of a domain fixed by right multiplication by an element other than one must
    be zero. -/
  theorem eq_zero_of_mul_eq_self_right' {a b : α} (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
  by apply (mul_eq_zero.1 _).resolve_right (sub_ne_zero.2 h₁);
     rw [mul_sub_left_distrib, mul_one, sub_eq_zero, h₂]

/-- An element of a domain fixed by left multiplication by an element other than one must
    be zero. -/
  theorem eq_zero_of_mul_eq_self_left' {a b : α} (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
  by apply (mul_eq_zero.1 _).resolve_left (sub_ne_zero.2 h₁);
     rw [mul_sub_right_distrib, one_mul, sub_eq_zero, h₂]

/-- For elements a, b of a domain, if a*b is nonzero, so is b*a. -/
  theorem mul_ne_zero_comm' {a b : α} (h : a * b ≠ 0) : b * a ≠ 0 :=
  mul_ne_zero' (ne_zero_of_mul_ne_zero_left h) (ne_zero_of_mul_ne_zero_right h)

end domain

/- integral domains -/

section
  variables [s : integral_domain α] (a b c d e : α)
  include s

/-- An integral domain is a domain. -/
  @[priority 100] -- see Note [lower instance priority]
  instance integral_domain.to_domain : domain α := {..s}

/-- Right multiplcation by a nonzero element of an integral domain is injective. -/
  theorem eq_of_mul_eq_mul_right_of_ne_zero {a b c : α} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
  have b * a - c * a = 0, by simp [h],
  have (b - c) * a = 0, by rw [mul_sub_right_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right ha,
  eq_of_sub_eq_zero this

/-- Left multiplication by a nonzero element of an integral domain is injective. -/
  theorem eq_of_mul_eq_mul_left_of_ne_zero {a b c : α} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have a * b - a * c = 0, by simp [h],
  have a * (b - c) = 0, by rw [mul_sub_left_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_left ha,
  eq_of_sub_eq_zero this

/-- Given two elements b, c of an integral domain and a nonzero element a, a*b divides a*c iff
    b divides c. -/
  theorem mul_dvd_mul_iff_left {a b c : α} (ha : a ≠ 0) : a * b ∣ a * c ↔ b ∣ c :=
  exists_congr $ λ d, by rw [mul_assoc, domain.mul_left_inj ha]

/-- Given two elements a, b of an integral domain and a nonzero element c, a*c divides b*c iff
    a divides b. -/
  theorem mul_dvd_mul_iff_right {a b c : α} (hc : c ≠ 0) : a * c ∣ b * c ↔ a ∣ b :=
  exists_congr $ λ d, by rw [mul_right_comm, domain.mul_right_inj hc]

/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
    one's additive inverse. -/
  lemma units.inv_eq_self_iff (u : units α) : u⁻¹ = u ↔ u = 1 ∨ u = -1 :=
  by conv {to_lhs, rw [inv_eq_iff_mul_eq_one, ← mul_one (1 : units α), units.ext_iff, units.coe_mul,
    units.coe_mul, mul_self_eq_mul_self_iff, ← units.ext_iff, ← units.coe_neg, ← units.ext_iff] }

end

/- units in various rings -/

namespace units

section comm_semiring
variables [comm_semiring α] (a b : α) (u : units α)

/-- Elements of the unit group of a commutative semiring represented as elements of the semiring
    divide any element of the semiring. -/
@[simp] lemma coe_dvd : ↑u ∣ a := ⟨↑u⁻¹ * a, by simp⟩

/-- In a commutative semiring, an element a divides an element b iff a divides all
    associates of b. -/
@[simp] lemma dvd_coe_mul : a ∣ b * u ↔ a ∣ b :=
iff.intro
  (assume ⟨c, eq⟩, ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← eq, units.mul_inv_cancel_right]⟩)
  (assume ⟨c, eq⟩, eq.symm ▸ dvd_mul_of_dvd_left (dvd_mul_right _ _) _)

/-- An element of a commutative semiring divides a unit iff the element divides one. -/
@[simp] lemma dvd_coe : a ∣ ↑u ↔ a ∣ 1 :=
suffices a ∣ 1 * ↑u ↔ a ∣ 1, by simpa,
dvd_coe_mul _ _ _

/-- In a commutative semiring, an element a divides an element b iff all associates of a divide b.-/
@[simp] lemma coe_mul_dvd : a * u ∣ b ↔ a ∣ b :=
iff.intro
  (assume ⟨c, eq⟩, ⟨c * ↑u, eq.symm ▸ by ac_refl⟩)
  (assume h, suffices a * ↑u ∣ b * 1, by simpa, mul_dvd_mul h (coe_dvd _ _))

end comm_semiring

section domain
variables [domain α]

/-- Every unit in a domain is nonzero. -/
@[simp] theorem ne_zero : ∀(u : units α), (↑u : α) ≠ 0
| ⟨u, v, (huv : 0 * v = 1), hvu⟩ rfl := by simpa using huv

end domain

end units
