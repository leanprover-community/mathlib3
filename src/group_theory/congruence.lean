/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import group_theory.submonoid data.setoid algebra.pi_instances data.equiv.algebra

/-!
# Congruence relations

This file defines multiplicative and additive congruence relations, first by extending
equivalence relations, or `setoid`s, and then as the inductive congruence closure of a
binary operation.

It also proves basic properties of the quotient of a type by a congruence relation, and the
complete lattice of congruence relations on a type.

## Implementation notes

The inductive definition of a congruence relation could be a nested inductive type, defined using
the equivalence closure of a binary relation `eqv_gen`, but the recursor generated does not work.
A nested inductive definition could conceivably shorten proofs, because they would allow invocation
of the corresponding lemmas about `eqv_gen`.

The lemmas `refl`, `symm` and `trans` are not tagged with `@[refl]`, `@[symm]`, and `@[trans]`
respectively as these tags do not work on a structure coerced to a binary relation.

There is a coercion from elements of a type to the element's equivalence class under a
congruence relation.

## Tags

congruence, congruence relation
-/

variables (M : Type*) {N : Type*} {P : Type*}

set_option old_structure_cmd true

/-- A congruence relation on a type with an addition is an equivalence relation which
    preserves addition. -/
structure add_con (M : Type*) [has_add M] extends setoid M :=
(add' : ∀ {w x y z}, r w x → r y z → r (w + y) (x + z))

/-- A congruence relation on a type with a multiplication is an equivalence relation which
    preserves multiplication. -/
@[to_additive add_con] structure con [has_mul M] extends setoid M :=
(mul' : ∀ {w x y z}, r w x → r y z → r (w * y) (x * z))

variables {M}

/-- The inductively defined additive congruence closure of a binary relation. -/
inductive add_con_gen.rel [has_add M] (r : M → M → Prop) : M → M → Prop
| of {} : Π x y, r x y → add_con_gen.rel x y
| refl {} : Π x, add_con_gen.rel x x
| symm {} : Π x y, add_con_gen.rel x y → add_con_gen.rel y x
| trans {} : Π x y z, add_con_gen.rel x y → add_con_gen.rel y z → add_con_gen.rel x z
| add {} : Π w x y z, add_con_gen.rel w x → add_con_gen.rel y z → add_con_gen.rel (w + y) (x + z)

/-- The inductively defined multiplicative congruence closure of a binary relation. -/
@[to_additive add_con_gen.rel]
inductive con_gen.rel [has_mul M] (r : M → M → Prop) : M → M → Prop
| of {} : Π x y, r x y → con_gen.rel x y
| refl {} : Π x, con_gen.rel x x
| symm {} : Π x y, con_gen.rel x y → con_gen.rel y x
| trans {} : Π x y z, con_gen.rel x y → con_gen.rel y z → con_gen.rel x z
| mul {} : Π w x y z, con_gen.rel w x → con_gen.rel y z → con_gen.rel (w * y) (x * z)

/-- The inductively defined multiplicative congruence closure of a binary relation. -/
@[to_additive add_con_gen "The inductively defined additive congruence closure of a binary relation."]
def con_gen [has_mul M] (r : M → M → Prop) : con M :=
⟨con_gen.rel r, ⟨con_gen.rel.refl, con_gen.rel.symm, con_gen.rel.trans⟩, con_gen.rel.mul⟩

variables {M}

namespace con

section
variables [has_mul M] [has_mul N] [has_mul P] (c : con M)

/-- A coercion from a congruence relation to its underlying binary relation. -/
@[to_additive "A coercion from an additive congruence relation to its underlying binary relation."]
instance : has_coe_to_fun (con M) := ⟨_, λ c, λ x y, c.r x y⟩

/-- Congruence relations are reflexive. -/
@[to_additive "Additive congruence relations are reflexive."]
lemma refl (x) : c.1 x x := c.2.1 x

/-- Congruence relations are symmetric. -/
@[to_additive "Additive congruence relations are symmetric."]
lemma symm : ∀ {x y}, c x y → c.1 y x := λ _ _ h, c.2.2.1 h

/-- Congruence relations are transitive. -/
@[to_additive "Additive congruence relations are transitive."]
lemma trans : ∀ {x y z}, c x y → c y z → c.1 x z :=
λ _ _ _ hx, c.2.2.2 hx

/-- Multiplicative congruence relations preserve multiplication. -/
@[to_additive "Additive congruence relations preserve addition."]
lemma mul : ∀ {w x y z}, c w x → c y z → c (w * y) (x * z) :=
λ _ _ _ _ h1 h2, c.3 h1 h2

/-- Given a type `M` with a multiplication, a congruence relation `c` on `M`, and elements of `M`
    `x, y`, `(x, y) ∈ M × M` iff `x` is related to `y` by `c`. -/
@[to_additive "Given a type `M` with an addition, `x, y ∈ M`, and an additive congruence relation `c` on `M`, `(x, y) ∈ M × M` iff `x` is related to `y` by `c`."]
instance : has_mem (M × M) (con M) := ⟨λ x c, c x.1 x.2⟩

variables {c}

/-- The map sending a congruence relation to its underlying binary relation is injective. -/
@[to_additive "The map sending an additive congruence relation to its underlying binary relation is injective."]
lemma ext' {c d : con M} (H : c.r = d.r) : c = d :=
by cases c; cases d; simpa using H

/-- Extensionality rule for congruence relations. -/
@[ext, to_additive "Extensionality rule for additive congruence relations."]
lemma ext {c d : con M} (H : ∀ x y, c x y ↔ d x y) : c = d :=
ext' $ by ext; apply H

attribute [ext] add_con.ext

/-- The map sending a congruence relation to its underlying equivalence relation is injective. -/
@[to_additive "The map sending an additive congruence relation to its underlying equivalence relation is injective."]
lemma to_setoid_inj {c d : con M} (H : c.to_setoid = d.to_setoid) : c = d :=
ext $ setoid.ext_iff.1 H

/-- Iff version of extensionality rule for congruence relations. -/
@[to_additive "Iff version of extensionality rule for additive congruence relations."]
lemma ext_iff {c d : con M} : (∀ x y, c x y ↔ d x y) ↔ c = d :=
⟨ext, λ h _ _, h ▸ iff.rfl⟩

/-- Two congruence relations are equal iff their underlying binary relations are equal. -/
@[to_additive "Two additive congruence relations are equal iff their underlying binary relations are equal."]
lemma ext'_iff {c d : con M} : c.r = d.r ↔ c = d :=
⟨ext', λ h, h ▸ rfl⟩

/-- The kernel of a multiplication-preserving function as a congruence relation. -/
@[to_additive "The kernel of an addition-preserving function as an additive congruence relation."]
def mul_ker (f : M → P) (h : ∀ x y, f (x * y) = f x * f y) : con M :=
{ r := λ x y, f x = f y,
  iseqv := ⟨λ _, rfl, λ _ _, eq.symm, λ _ _ _, eq.trans⟩,
  mul' := λ _ _ _ _ h1 h2, by rw [h, h1, h2, h] }

/-- Given types with multiplications `M, N`, the product of two congruence relations `c` on `M` and
    `d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁` is related to `y₁`
    by `c` and `x₂` is related to `y₂` by `d`. -/
@[to_additive prod "Given types with additions `M, N`, the product of two congruence relations `c` on `M` and `d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁` is related to `y₁` by `c` and `x₂` is related to `y₂` by `d`."]
protected def prod (c : con M) (d : con N) : con (M × N) :=
{ mul' := λ _ _ _ _ h1 h2, ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩, ..c.to_setoid.prod d.to_setoid }

/-- The product of an indexed collection of congruence relations. -/
@[to_additive "The product of an indexed collection of additive congruence relations."]
def pi {ι : Type*} {f : ι → Type*} [Π i, has_mul (f i)]
  (C : Π i, con (f i)) : con (Π i, f i) :=
{ mul' := λ _ _ _ _ h1 h2 i, (C i).mul (h1 i) (h2 i), ..@pi_setoid _ _ $ λ i, (C i).to_setoid }

variables (c)

@[simp, to_additive] lemma coe_eq : c.to_setoid.r = c := rfl

-- Quotients

/-- Defining the quotient by a congruence relation of a type with a multiplication. -/
@[to_additive "Defining the quotient by an additive congruence relation of a type with an addition."]
protected def quotient := quotient $ c.to_setoid

/-- Coercion from a type with a multiplication to its quotient by a congruence relation. -/
@[to_additive "Coercion from a type with an addition to its quotient by an additive congruence relation", priority 0]
instance : has_coe M c.quotient := ⟨@quotient.mk _ c.to_setoid⟩

/-- The quotient of a type with decidable equality by a congruence relation also has
    decidable equality. -/
@[to_additive "The quotient of a type with decidable equality by an additive congruence relation also has decidable equality."]
instance [d : ∀ a b, decidable (c a b)] : decidable_eq c.quotient :=
@quotient.decidable_eq M c.to_setoid d

/-- The function on the quotient by a congruence relation `c` induced by a function that is
    constant on `c`'s equivalence classes. -/
@[elab_as_eliminator, to_additive "The function on the quotient by a congruence relation `c` induced by a function that is constant on `c`'s equivalence classes."]
protected def lift_on {β} {c : con M} (q : c.quotient) (f : M → β)
  (h : ∀ a b, c a b → f a = f b) : β := quotient.lift_on' q f h

variables {c}

/-- The inductive principle used to prove propositions about the elements of a quotient by a
    congruence relation. -/
@[elab_as_eliminator, to_additive "The inductive principle used to prove propositions about the elements of a quotient by an additive congruence relation."]
protected lemma induction_on {C : c.quotient → Prop} (q : c.quotient) (H : ∀ x : M, C x) : C q :=
quotient.induction_on' q H

/-- A version of `con.induction_on` for predicates which take two arguments. -/
@[elab_as_eliminator, to_additive "A version of `add_con.induction_on` for predicates which take two arguments."]
protected lemma induction_on₂ {d : con N} {C : c.quotient → d.quotient → Prop}
  (p : c.quotient) (q : d.quotient) (H : ∀ (x : M) (y : N), C x y) : C p q :=
quotient.induction_on₂' p q H

variables (c)

/-- Two elements are related by a congruence relation `c` iff they are represented by the same
    element of the quotient by `c`. -/
@[simp, to_additive "Two elements are related by an additive congruence relation `c` iff they are represented by the same element of the quotient by `c`."]
protected lemma eq (a b : M) : (a : c.quotient) = b ↔ c a b :=
quotient.eq'

/-- The multiplication induced on the quotient by a congruence relation on a type with a
    multiplication. -/
@[to_additive "The addition induced on the quotient by an additive congruence relation on a type with a addition."]
instance has_mul : has_mul c.quotient :=
⟨λ x y, quotient.lift_on₂' x y (λ w z, ((w * z : M) : c.quotient))
     $ λ _ _ _ _ h1 h2, (c.eq _ _).2 $ c.mul h1 h2⟩

/-- The kernel of the quotient map induced by a congruence relation `c` equals `c`. -/
@[simp, to_additive "The kernel of the quotient map induced by an additive congruence relation `c` equals `c`."]
lemma mul_ker_mk_eq : mul_ker (coe : M → c.quotient) (λ x y, rfl) = c :=
ext $ λ x y, quotient.eq'

variables {c}

/-- The coercion to the quotient of a congruence relation commutes with multiplication (by
    definition). -/
@[simp, to_additive "The coercion to the quotient of an additive congruence relation commutes with addition (by definition)."]
lemma coe_mul (x y : M) : (x : c.quotient) * (y : c.quotient) = ((x * y : M) : c.quotient) := rfl

/-- Definition of the function on the quotient by a congruence relation `c` induced by a function
    that is constant on `c`'s equivalence classes. -/
@[simp, to_additive "Definition of the function on the quotient by an additive congruence relation `c` induced by a function that is constant on `c`'s equivalence classes."]
protected lemma lift_on_beta {β} (c : con M) (f : M → β)
  (h : ∀ a b, c a b → f a = f b) (x : M) :
  quotient.lift_on' (x : c.quotient) f h = f x := rfl

/-- Makes an isomorphism of quotients by two congruence relations, given that the relations are
    equal. -/
@[to_additive "Makes an additive isomorphism of quotients by two additive congruence relations, given that the relations are equal."]
protected def congr {c d : con M} (h : c = d) :  c.quotient ≃* d.quotient :=
{ map_mul' := λ x y, by rcases x; rcases y; refl,
  ..quotient.congr (equiv.refl M) $ by apply ext_iff.2 h }

-- The complete lattice of congruence relations on a type

open lattice

/-- For congruence relations `c, d` on a type `M` with a multiplication, `c ≤ d` iff `∀ x y ∈ M`,
    `x` is related to `y` by `d` if `x` is related to `y` by `c`. -/
@[to_additive "For additive congruence relations `c, d` on a type `M` with an addition, `c ≤ d` iff `∀ x y ∈ M`, `x` is related to `y` by `d` if `x` is related to `y` by `c`."]
instance : has_le (con M) := ⟨λ c d, c.to_setoid ≤ d.to_setoid⟩

/-- Definition of `≤` for congruence relations. -/
@[to_additive "Definition of `≤` for additive congruence relations."]
theorem le_def {c d : con M} : c ≤ d ↔ ∀ {x y}, c x y → d x y := iff.rfl

/-- The infimum of a set of congruence relations on a given type with a multiplication. -/
@[to_additive "The infimum of a set of additive congruence relations on a given type with an addition."]
instance : has_Inf (con M) :=
⟨λ S, ⟨λ x y, ∀ c : con M, c ∈ S → c x y,
⟨λ x c hc, c.refl x, λ _ _ h c hc, c.symm $ h c hc,
 λ _ _ _ h1 h2 c hc, c.trans (h1 c hc) $ h2 c hc⟩,
 λ _ _ _ _ h1 h2 c hc, c.mul (h1 c hc) $ h2 c hc⟩⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying equivalence relation. -/
@[to_additive "The infimum of a set of additive congruence relations is the same as the infimum of the set's image under the map to the underlying equivalence relation."]
lemma Inf_to_setoid (S : set (con M)) : (Inf S).to_setoid = Inf (to_setoid '' S) :=
setoid.ext' $ λ x y, ⟨λ h r ⟨c, hS, hr⟩, by rw ←hr; exact h c hS,
  λ h c hS, h c.to_setoid ⟨c, hS, rfl⟩⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying binary relation. -/
@[to_additive "The infimum of a set of additive congruence relations is the same as the infimum of the set's image under the map to the underlying binary relation."]
lemma Inf_def (S : set (con M)) : (Inf S).r = Inf (r '' S) :=
by { ext, simp only [Inf_image, infi_apply, infi_Prop_eq], refl }

/-- If a congruence relation `c` is contained in every element of a set `s` of congruence relations
    on the same type, `c` is contained in the infimum of `s`. -/
@[to_additive "If an additive congruence relation `c` is contained in every element of a set `s` of additive congruence relations on the same type, `c` is contained in the infimum of `s`."]
lemma le_Inf (s : set (con M)) (c) : (∀d ∈ s, c ≤ d) → c ≤ Inf s :=
λ h _ _ hc r hr, h r hr _ _ hc

/-- The infimum of a set of congruence relations on a given type is contained in every element
    of the set. -/
@[to_additive "The infimum of a set of additive congruence relations on a given type is contained in every element of the set."]
lemma Inf_le (s : set (con M)) (c) : c ∈ s → Inf s ≤ c :=
λ hc _ _ h, h c hc

/-- The complete lattice of congruence relations on a given type with a multiplication. -/
@[to_additive "The complete lattice of additive congruence relations on a given type with an addition."]
instance : complete_lattice (con M) :=
{ sup := λ c d, Inf { x | c ≤ x ∧ d ≤ x},
  le := (≤),
  lt := λ c d, c ≤ d ∧ ¬d ≤ c,
  le_refl := λ c _ _, id,
  le_trans := λ c1 c2 c3 h1 h2 x y h, h2 x y $ h1 x y h,
  lt_iff_le_not_le := λ _ _, iff.rfl,
  le_antisymm := λ c d hc hd, ext $ λ x y, ⟨hc x y, hd x y⟩,
  le_sup_left := λ _ _ _ _ h r hr, hr.1 _ _ h,
  le_sup_right := λ _ _ _ _ h r hr, hr.2 _ _ h,
  sup_le := λ _ _ c h1 h2, Inf_le _ c ⟨h1, h2⟩,
  inf := λ c d, ⟨(c.to_setoid ⊓ d.to_setoid).1, (c.to_setoid ⊓ d.to_setoid).2,
                  λ _ _ _ _ h1 h2, ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩⟩,
  inf_le_left := λ _ _ _ _ h, h.1,
  inf_le_right := λ _ _ _ _ h, h.2,
  le_inf := λ _ _ _ hb hc _ _ h, ⟨hb _ _ h, hc _ _ h⟩,
  top := { mul' := by tauto, ..setoid.complete_lattice.top},
  le_top := λ _ _ _ h, trivial,
  bot := { mul' := λ _ _ _ _ h1 h2, h1 ▸ h2 ▸ rfl, ..setoid.complete_lattice.bot},
  bot_le := λ c x y h, h ▸ c.refl x,
  Sup := λ tt, Inf {t | ∀t'∈tt, t' ≤ t},
  Inf := has_Inf.Inf,
  le_Sup := λ _ _ hs, le_Inf _ _ $ λ c' hc', hc' _ hs,
  Sup_le := λ _ _ hs, Inf_le _ _ hs,
  Inf_le := λ  _ _, Inf_le _ _,
  le_Inf := λ _ _, le_Inf _ _ }

/-- The infimum of two congruence relations equals the infimum of the underlying binary operations. -/
@[to_additive "The infimum of two additive congruence relations equals the infimum of the underlying binary operations."]
lemma inf_def {c d : con M} : (c ⊓ d).r = c.r ⊓ d.r := rfl

/-- Definition of the infimum of two congruence relations. -/
@[to_additive "Definition of the infimum of two additive congruence relations."]
theorem inf_iff_and {c d : con M} {x y} : (c ⊓ d) x y ↔ c x y ∧ d x y := iff.rfl

/-- The inductively defined congruence closure of a binary relation `r` equals the infimum of the
    set of congruence relations containing `r`. -/
@[to_additive add_con_gen_eq "The inductively defined additive congruence closure of a binary relation `r` equals the infimum of the set of additive congruence relations containing `r`."]
theorem con_gen_eq (r : M → M → Prop) :
  con_gen r = Inf {s : con M | ∀ x y, r x y → s.r x y} :=
ext $ λ x y,
  ⟨λ H, con_gen.rel.rec_on H (λ _ _ h _ hs, hs _ _ h) (refl _) (λ _ _ _, symm _)
    (λ _ _ _ _ _, trans _)
    $ λ w x y z _ _ h1 h2 c hc, c.mul (h1 c hc) $ h2 c hc,
  Inf_le _ _ (λ _ _, con_gen.rel.of _ _) _ _⟩

/-- The congruence closure of a binary relation `r` is contained in any congruence relation
    containing `r`. -/
@[to_additive add_con_gen_le "The additive congruence closure of a binary relation `r` is contained in any additive congruence relation containing `r`."]
theorem con_gen_le {r : M → M → Prop} {c : con M} (h : ∀ x y, r x y → c.r x y) :
  con_gen r ≤ c :=
by rw con_gen_eq; exact Inf_le _ _ h

/-- Congruence closure of binary relations is monotonic. -/
@[to_additive add_con_gen_mono "Additive congruence closure of binary relations is monotonic."]
theorem con_gen_mono {r s : M → M → Prop} (h : ∀ x y, r x y → s x y) :
  con_gen r ≤ con_gen s :=
con_gen_le $ λ x y hr, con_gen.rel.of _ _ $ h x y hr

/-- Congruence relations equal their congruence closure. -/
@[simp, to_additive add_con_gen_of_add_con "Additive congruence relations equal their additive congruence closure."]
lemma con_gen_of_con (c : con M) : con_gen c.r = c :=
le_antisymm (by rw con_gen_eq; exact Inf_le _ c (λ _ _, id)) con_gen.rel.of

/-- Congruence closure of binary relations is idempotent. -/
@[simp, to_additive add_con_gen_idem "Additive congruence closure of binary relations is idempotent."]
lemma con_gen_idem (r : M → M → Prop) :
  con_gen (con_gen r).r = con_gen r :=
con_gen_of_con _

/-- The supremum of congruence relations `c, d` equals the congruence closure of the binary relation
    '`x` is related to `y` by `c` or `d`'. -/
@[to_additive sup_eq_add_con_gen "The supremum of additive congruence relations `c, d` equals the congruence closure of the binary relation '`x` is related to `y` by `c` or `d`'."]
lemma sup_eq_con_gen (c d : con M) :
  c ⊔ d = con_gen (λ x y, c x y ∨ d x y) :=
begin
  rw con_gen_eq,
  apply congr_arg Inf,
  ext,
  exact ⟨λ h _ _ H, or.elim H (h.1 _ _) (h.2 _ _),
         λ H, ⟨λ _ _ h, H _ _ $ or.inl h, λ _ _ h, H _ _ $ or.inr h⟩⟩,
end

/-- The supremum of two congruence relations equals the congruence closure of the supremum of the
    underlying binary operations. -/
@[to_additive "The supremum of two additive congruence relations equals the additive congruence closure of the supremum of the underlying binary operations."]
lemma sup_def {c d : con M} : c ⊔ d = con_gen (c.r ⊔ d.r) :=
by rw sup_eq_con_gen; refl

/-- The supremum of a set of congruence relations `S` equals the congruence closure of the
    binary relation 'there exists `c ∈ S` such that `x` is related to `y` by `c`'. -/
@[to_additive Sup_eq_add_con_gen "The supremum of a set of additive congruence relations S equals the additive congruence closure of the binary relation 'there exists `c ∈ S` such that `x` is related to `y` by `c`'."]
lemma Sup_eq_con_gen (S : set (con M)) :
  Sup S = con_gen (λ x y, ∃ c : con M, c ∈ S ∧ c x y) :=
begin
  rw con_gen_eq,
  apply congr_arg Inf,
  ext,
  exact ⟨λ h _ _ ⟨r, hr⟩, h r hr.1 _ _ hr.2,
         λ h r hS _ _ hr, h _ _ ⟨r, hS, hr⟩⟩,
end

/-- The supremum of a set of congruence relations is the same as the congruence closure of the
    supremum of the set's image under the map to the underlying binary relation. -/
@[to_additive "The supremum of a set of additive congruence relations is the same as the additive congruence closure of the supremum of the set's image under the map to the underlying binary relation."]
lemma Sup_def {S : set (con M)} : Sup S = con_gen (Sup (r '' S)) :=
begin
  rw Sup_eq_con_gen,
  congr,
  ext x y,
  erw [Sup_image, supr_apply, supr_apply, supr_Prop_eq],
  simp only [Sup_image, supr_Prop_eq, supr_apply, supr_Prop_eq, exists_prop],
  refl,
end

variables (M)

/-- There is a Galois insertion of congruence relations on a type with a multiplication `M` into
    binary relations on `M`, with congruence closure the lower adjoint. -/
@[to_additive "There is a Galois insertion of additive congruence relations on a type with an addition `M` into binary relations on `M`, with additive congruence closure the lower adjoint."]
protected def gi : @galois_insertion (M → M → Prop) (con M) _ _ con_gen r :=
{ choice := λ r h, con_gen r,
 gc := λ r c, ⟨λ H _ _ h, H _ _ $ con_gen.rel.of _ _ h, λ H, con_gen_of_con c ▸ con_gen_mono H⟩,
  le_l_u := λ x, (con_gen_of_con x).symm ▸ le_refl x,
  choice_eq := λ _ _, rfl }

end
end con