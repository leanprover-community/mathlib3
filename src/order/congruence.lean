/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.group.prod
import group_theory.sublattice.operations
import data.setoid.basic
import order.hom.lattice

/-!
# Lattice congruences

This file defines lattice congruences: equivalence relations that preserve a binary operation,
which in this case is multiplication or addition. The principal definition is a `structure`
extending a `setoid` (an equivalence relation), and the inductive definition of the smallest
lattice congruence containing a binary relation is also given (see `lattice_con_gen`).

The file also proves basic properties of the quotient of a type by a lattice congruence, and the
complete lattice of lattice congruences on a type. We then establish an order-preserving bijection
between the set of lattice congruences containing a lattice congruence `c` and the set of
lattice congruences on the quotient by `c`.

The selattice_cond half of the file lattice_concerns lattice congruences on lattices, in which case the
quotient by the lattice congruence is also a lattice. There are results about the universal
property of quotients of lattices, and the isomorphism theorems for lattices.

## Implementation notes

The inductive definition of a lattice congruence could be a nested inductive type, defined using
the equivalence closure of a binary relation `eqv_gen`, but the recursor generated does not work.
A nested inductive definition could lattice_conceivably shorten proofs, because they would allow invocation
of the corresponding lemmas about `eqv_gen`.

The lemmas `refl`, `symm` and `trans` are not tagged with `@[refl]`, `@[symm]`, and `@[trans]`
respectively as these tags do not work on a structure coerced to a binary relation.

There is a coercion from elements of a type to the element's equivalence class under a
lattice congruence.

A lattice congruence on a lattice `α` can be thought of as a sublattice of `α × α` for which
membership is an equivalence relation, but whilst this fact is established in the file, it is not
used, since this perspective adds more layers of definitional unfolding.

## Tags

congruence, lattice congruence, quotient, quotient by lattice congruence, lattice,
quotient lattice, isomorphism theorems
-/

variables {α β γ : Type*}

open function setoid

/-- A lattice congruence on a type with a multiplication is an equivalence relation which
    preserves multiplication. -/
structure lattice_con (α : Type*) [lattice α] extends setoid α :=
(sup' {a b c d : α} : r a b → r c d → r (a ⊔ c) (b ⊔ d))
(inf' {a b c d : α} : r a b → r c d → r (a ⊓ c) (b ⊓ d))

/-- The equivalence relation underlying a lattice lattice congruence. -/
add_decl_doc lattice_con.to_setoid

variables {α}

/-- The smallest lattice lattice congruence containing a given binary relation. -/
inductive lattice_con_gen.rel [lattice α] (r : α → α → Prop) : α → α → Prop
| of (a b : α) : r a b → lattice_con_gen.rel a b
| refl (a : α) : lattice_con_gen.rel a a
| symm (a b : α) : lattice_con_gen.rel a b → lattice_con_gen.rel b a
| trans (a b c : α) : lattice_con_gen.rel a b → lattice_con_gen.rel b c → lattice_con_gen.rel a c
| sup (a b c d : α) : lattice_con_gen.rel a b → lattice_con_gen.rel c d →
    lattice_con_gen.rel (a ⊔ c) (b ⊔ d)
| inf (a b c d : α) : lattice_con_gen.rel a b → lattice_con_gen.rel c d →
    lattice_con_gen.rel (a ⊓ c) (b ⊓ d)

/-- The smallest lattice congruence containing a given binary relation. -/
def lattice_con_gen [lattice α] (r : α → α → Prop) : lattice_con α :=
⟨⟨lattice_con_gen.rel r, lattice_con_gen.rel.refl, lattice_con_gen.rel.symm,
  lattice_con_gen.rel.trans⟩, lattice_con_gen.rel.sup, lattice_con_gen.rel.inf⟩

namespace lattice_con

section
variables [lattice α] [lattice β] [lattice γ] (r : lattice_con α)

instance : inhabited (lattice_con α) := ⟨lattice_con_gen ⊥⟩

/-- Coercion from lattice congruences to their underlying binary relation. -/
instance : has_coe_to_fun (lattice_con α) (λ _, α → α → Prop) :=
⟨λ r, λ a b, @setoid.r _ r.to_setoid a b⟩

@[simp] lemma rel_eq_coe (r : lattice_con α) : r.r = r := rfl

/-- Lattice congruences are reflexive. -/
protected lemma refl (a) : r a a := r.to_setoid.refl' a

/-- Lattice congruences are symmetric. -/
protected lemma symm : ∀ {a b}, r a b → r b a := λ _ _ h, r.to_setoid.symm' h

/-- Lattice congruences are transitive. -/
protected lemma trans : ∀ {a b c}, r a b → r b c → r a c :=
λ _ _ _ h, r.to_setoid.trans' h

/-- Lattice congruence preserve multiplication. -/
protected lemma sup {a b c d} (hab : r a b) (hcd : r c d) : r (a ⊔ c) (b ⊔ d) := r.sup' hab hcd

@[simp] lemma rel_mk {s : setoid α} {hsup hinf a b} :
  lattice_con.mk s hsup hinf a b ↔ r a b :=
iff.rfl

/-- Given a type `α` with a multiplication, a lattice congruence `c` on `α`, and elements of `α`
    `a, b`, `(a, b) ∈ α × α` iff `a` is related to `b` by `c`. -/
instance : has_mem (α × α) (lattice_con α) := ⟨λ a c, r a.1 a.2⟩

variables {r}

lemma coe_injective {r s : lattice_con α} (H : (r : α → α → Prop) = s) : r = s :=
by { obtain ⟨⟨⟩⟩ := r, obtain ⟨⟨⟩⟩ := s, congr' }

lemma ext {r s : lattice_con α} (h : ∀ a b, r a b ↔ s a b) : r = s :=
coe_injective $ by { ext, exact h _ _ }

/-- The map sending a lattice congruence to its underlying equivalence relation is injective. -/
lemma to_setoid_inj {c d : lattice_con α} (H : r.to_setoid = d.to_setoid) : c = d :=
ext $ ext_iff.1 H

/-- Iff version of extensionality rule for lattice congruences. -/
lemma ext_iff {c d : lattice_con α} : (∀ a b, r a b ↔ d a b) ↔ c = d :=
⟨ext, λ h _ _, h ▸ iff.rfl⟩

/-- Two lattice congruences are equal iff their underlying binary relations are equal. -/
lemma coe_injective_iff {c d : lattice_con α} : c.r = d.r ↔ c = d :=
⟨coe_injective, λ h, h ▸ rfl⟩

/-- The kernel of a multiplication-preserving function as a lattice congruence. -/
def lattice_ker (f : α → γ) (hsup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
  (hinf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) : lattice_con α :=
{ to_setoid := setoid.ker f,
  sup' := λ a b c d (hab : f a = f b) (hcd : f c = f d), (hsup _ _).trans $ by rw [hab, hcd, hsup],
  inf' := λ a b c d (hab : f a = f b) (hcd : f c = f d), (hinf _ _).trans $ by rw [hab, hcd, hinf] }

/-- Given types with multiplications `α, β`, the product of two lattice congruences `c` on `α` and
    `d` on `β`: `(x₁, x₂), (y₁, y₂) ∈ α × β` are related by `c.prod d` iff `x₁` is related to `y₁`
    by `c` and `x₂` is related to `y₂` by `d`. -/
protected def prod (c : lattice_con α) (d : lattice_con β) : lattice_con (α × β) :=
{ mul' := λ _ _ _ _ h1 h2, ⟨r.sup h1.1 h2.1, d.mul h1.2 h2.2⟩, ..r.to_setoid.prod d.to_setoid }

/-- The product of an indexed collection of lattice congruences. -/
def pi {ι : Type*} {α : ι → Type*} [Π i, lattice (α i)] (r : Π i, lattice_con (α i)) :
  lattice_con (Π i, α i) :=
{ sup' := λ _ _ _ _ h1 h2 i, (r i).sup (h1 i) (h2 i),
  ..@pi_setoid _ _ $ λ i, (C i).to_setoid }

variables (r)

/-! ### Quotients -/

/-- Defining the quotient by a lattice congruence of a type with a multiplication. -/
protected def quotient := quotient $ r.to_setoid

/-- Coercion from a type with a multiplication to its quotient by a lattice congruence.

See Note [use has_coe_t]. -/
@[priority 0]
instance : has_coe_t α r.quotient := ⟨@quotient.mk _ r.to_setoid⟩

/-- The quotient by a decidable lattice congruence has decidable equality. -/
@[priority 500] -- Lower the priority since it unifies with any quotient type.
instance [d : ∀ a b, decidable (r a b)] : decidable_eq r.quotient :=
@quotient.decidable_eq α r.to_setoid d

@[simp] lemma quot_mk_eq_coe {α : Type*} [lattice α] (c : lattice_con α) (a : α) :
  quot.mk r a = (a : r.quotient) :=
rfl

/-- The function on the quotient by a lattice congruence `c` induced by a function that is constant
on `c`'s equivalence classes. -/
@[elab_as_eliminator]
protected def lift_on {β} {c : lattice_con α} (q : r.quotient) (f : α → β)
  (h : ∀ a b, r a b → f a = f b) : β := quotient.lift_on' q f h

/-- The binary function on the quotient by a lattice congruence `c` induced by a binary function
that is constant on `c`'s equivalence classes. -/
@[elab_as_eliminator]
protected def lift_on₂ {β} {c : lattice_con α} (q r : r.quotient) (f : α → α → β)
  (h : ∀ a₁ a₂ b₁ b₂, c a₁ b₁ → c a₂ b₂ → f a₁ a₂ = f b₁ b₂) : β := quotient.lift_on₂' q r f h

/-- A version of `quotient.hrec_on₂'` for quotients by `lattice_con`. -/
protected def hrec_on₂ {cM : lattice_con α} {cN : lattice_con β} {φ : cM.quotient → cN.quotient → Sort*}
  (a : cM.quotient) (b : cN.quotient)
  (f : Π (a : α) (b : β), φ a b) (h : ∀ a b x' y', cM a x' → cN b y' → f a b == f x' y') :
  φ a b :=
quotient.hrec_on₂' a b f h

@[simp] lemma hrec_on₂_coe {cM : lattice_con α} {cN : lattice_con β}
  {φ : cM.quotient → cN.quotient → Sort*} (a : α) (b : β)
  (f : Π (a : α) (b : β), φ a b) (h : ∀ a b x' y', cM a x' → cN b y' → f a b == f x' y') :
  lattice_con.hrec_on₂ ↑a ↑b f h = f a b :=
rfl

variables {r}

/-- The inductive principle used to prove propositions about the elements of a quotient by a
lattice congruence. -/
@[elab_as_eliminator]
protected lemma induction_on {C : r.quotient → Prop} (q : r.quotient) (H : ∀ a : α, C a) : C q :=
quotient.induction_on' q H

/-- A version of `lattice_con.induction_on` for predicates which take two arguments. -/
@[elab_as_eliminator]
protected lemma induction_on₂ {d : lattice_con β} {C : r.quotient → d.quotient → Prop}
  (p : r.quotient) (q : d.quotient) (H : ∀ (a : α) (b : β), C a b) : C p q :=
quotient.induction_on₂' p q H

variables (r)

/-- Two elements are related by a lattice congruence `c` iff they are represented by the same
    element of the quotient by `c`. -/
@[simp]
protected lemma eq {a b : α} : (a : r.quotient) = b ↔ r a b :=
quotient.eq'

/-- The multiplication induced on the quotient by a lattice congruence on a type with a
multiplication. -/
instance lattice : lattice r.quotient :=
⟨λ a b, quotient.lift_on₂' a b (λ w c, ((w * c : α) : r.quotient))
     $ λ _ _ _ _ h1 h2, c.eq.2 $ r.sup h1 h2⟩

/-- The kernel of the quotient map induced by a lattice congruence `c` equals `c`. -/
@[simp]
lemma lattice_ker_mk_eq : lattice_ker (coe : α → r.quotient) (λ a b, rfl) = c :=
ext $ λ a b, quotient.eq'

variables {c}

/-- The coercion to the quotient of a lattice congruence commutes with multiplication (by
definition). -/
@[simp]
lemma coe_mul (a b : α) : (↑(a * b) : r.quotient) = ↑x * ↑y := rfl

/-- Definition of the function on the quotient by a lattice congruence `c` induced by a function
that is constant on `c`'s equivalence classes. -/
@[simp]
protected lemma lift_on_coe {β} (c : lattice_con α) (f : α → β)
  (h : ∀ a b, r a b → f a = f b) (a : α) :
  lattice_con.lift_on (a : r.quotient) f h = f a := rfl

/-- Makes an isomorphism of quotients by two lattice congruences, given that the relations are
equal. -/
protected def congr {c d : lattice_con α} (h : c = d) :  r.quotient ≃* d.quotient :=
{ map_mul' := λ a b, by rcases a; rcases b; refl,
  ..quotient.congr (equiv.refl α) $ by apply ext_iff.2 h }

/-! ### The complete lattice of lattice congruences on a type -/

/-- For lattice congruences `c, d` on a type `α` with a multiplication, `c ≤ d` iff `∀ a b ∈ α`,
    `a` is related to `b` by `d` if `a` is related to `b` by `c`. -/
instance : has_le (lattice_con α) := ⟨λ c d, ∀ ⦃a b⦄, r a b → d a b⟩

/-- Definition of `≤` for lattice congruences. -/
lemma le_def {c d : lattice_con α} : c ≤ d ↔ ∀ {a b}, r a b → d a b := iff.rfl

/-- The infimum of a set of lattice congruences on a given type with a multiplication. -/
instance : has_Inf (lattice_con α) :=
⟨λ S, ⟨⟨λ a b, ∀ c : lattice_con α, c ∈ S → r a b,
⟨λ a c hc, c.refl a, λ _ _ h c hc, c.symm $ h c hc,
 λ _ _ _ h1 h2 c hc, c.trans (h1 c hc) $ h2 c hc⟩⟩,
 λ _ _ _ _ h1 h2 c hc, r.sup (h1 c hc) $ h2 c hc⟩⟩

/-- The infimum of a set of lattice congruences is the same as the infimum of the set's image
    under the map to the underlying equivalence relation. -/
lemma Inf_to_setoid (S : set (lattice_con α)) : (Inf S).to_setoid = Inf (to_setoid '' S) :=
setoid.coe_injective $ λ a b, ⟨λ h r ⟨c, hS, hr⟩, by rw ←hr; exact h c hS,
  λ h c hS, h r.to_setoid ⟨c, hS, rfl⟩⟩

/-- The infimum of a set of lattice congruences is the same as the infimum of the set's image
    under the map to the underlying binary relation. -/
lemma Inf_def (S : set (lattice_con α)) : ⇑(Inf S) = Inf (@set.image (lattice_con α) (α → α → Prop) coe_fn S) :=
by { ext, simp only [Inf_image, infi_apply, infi_Prop_eq], refl }

instance : partial_order (lattice_con α) :=
{ le := (≤),
  lt := λ c d, c ≤ d ∧ ¬d ≤ c,
  le_refl := λ c _ _, id,
  le_trans := λ c1 c2 c3 h1 h2 a b h, h2 $ h1 h,
  lt_iff_le_not_le := λ _ _, iff.rfl,
  le_antisymm := λ c d hc hd, ext $ λ a b, ⟨λ h, hc h, λ h, hd h⟩ }

/-- The complete lattice of lattice congruences on a given type with a multiplication. -/
instance : complete_lattice (lattice_con α) :=
{ inf := λ c d, ⟨(r.to_setoid ⊓ d.to_setoid), λ _ _ _ _ h1 h2, ⟨r.sup h1.1 h2.1, d.mul h1.2 h2.2⟩⟩,
  inf_le_left := λ _ _ _ _ h, h.1,
  inf_le_right := λ _ _ _ _ h, h.2,
  le_inf := λ _ _ _ hb hc _ _ h, ⟨hb h, hc h⟩,
  top := { mul' := by tauto, ..setoid.complete_lattice.top},
  le_top := λ _ _ _ h, trivial,
  bot := { mul' := λ _ _ _ _ h1 h2, h1 ▸ h2 ▸ rfl, ..setoid.complete_lattice.bot},
  bot_le := λ r a b h, h ▸ c.refl a,
  .. complete_lattice_of_Inf (lattice_con α) $ assume s,
    ⟨λ r hr a b h, (h : ∀ r ∈ s, (r : lattice_con α) a b) r hr, λ r hr a b h r' hr', hr hr' h⟩ }

/-- The infimum of two lattice congruences equals the infimum of the underlying binary operations.
-/
lemma inf_def {c d : lattice_con α} : (c ⊓ d).r = c.r ⊓ d.r := rfl

/-- Definition of the infimum of two lattice congruences. -/
lemma inf_iff_and {c d : lattice_con α} {a b} : (c ⊓ d) a b ↔ r a b ∧ d a b := iff.rfl

/-- The inductively defined smallest lattice congruence containing a binary relation `r`
equals the infimum of the set of lattice congruences containing `r`. -/
lemma lattice_con_gen_eq (r : α → α → Prop) :
  lattice_con_gen r = Inf {s : lattice_con α | ∀ a b, r a b → s a b} :=
le_antisymm
  (λ a b H, lattice_con_gen.rel.rec_on H (λ _ _ h _ hs, hs _ _ h) (lattice_con.refl _) (λ _ _ _, lattice_con.symm _)
    (λ _ _ _ _ _, lattice_con.trans _)
    $ λ a b c d _ _ h1 h2 c hc, r.sup (h1 c hc) $ h2 c hc)
  (Inf_le (λ _ _, lattice_con_gen.rel.of _ _))

/-- The smallest lattice congruence containing a binary relation `r` is contained in
any lattice congruence containing `r`. -/
lemma lattice_con_gen_le {r : α → α → Prop} {c : lattice_con α} (h : ∀ a b, r a b → @setoid.r _ r.to_setoid a b) :
  lattice_con_gen r ≤ c :=
by rw lattice_con_gen_eq; exact Inf_le h

/-- Given binary relations `r, s` with `r` contained in `s`, the smallest lattice congruence
containing `s` contains the smallest lattice congruence containing `r`. -/
lemma lattice_con_gen_mono {r s : α → α → Prop} (h : ∀ a b, r a b → s a b) :
  lattice_con_gen r ≤ lattice_con_gen s :=
lattice_con_gen_le $ λ a b hr, lattice_con_gen.rel.of _ _ $ h a b hr

/-- Lattice congruences equal the smallest lattice congruence in which they are contained. -/
@[simp]
lemma lattice_con_gen_of_lattice_con (c : lattice_con α) : lattice_con_gen c = c :=
le_antisymm (by rw lattice_con_gen_eq; exact Inf_le (λ _ _, id)) lattice_con_gen.rel.of

/-- The map sending a binary relation to the smallest lattice congruence in which it is contained is
idempotent. -/
@[simp]
lemma lattice_con_gen_idem (r : α → α → Prop) :
  lattice_con_gen (lattice_con_gen r) = lattice_con_gen r :=
lattice_con_gen_of_lattice_con _

/-- The supremum of lattice congruences `c, d` equals the smallest lattice congruence containing the
binary relation '`a` is related to `b` by `c` or `d`'. -/
lemma sup_eq_lattice_con_gen (c d : lattice_con α) :
  c ⊔ d = lattice_con_gen (λ a b, r a b ∨ d a b) :=
begin
  rw lattice_con_gen_eq,
  apply congr_arg Inf,
  simp only [le_def, or_imp_distrib, ← forall_and_distrib]
end

/-- The supremum of two lattice congruences equals the smallest lattice congruence containing
    the supremum of the underlying binary operations. -/
lemma sup_def {c d : lattice_con α} : c ⊔ d = lattice_con_gen (c.r ⊔ d.r) :=
by rw sup_eq_lattice_con_gen; refl

/-- The supremum of a set of lattice congruences `S` equals the smallest lattice congruence
containing the binary relation 'there exists `c ∈ S` such that `a` is related to `b` by `c`'. -/
lemma Sup_eq_lattice_con_gen (S : set (lattice_con α)) :
  Sup S = lattice_con_gen (λ a b, ∃ c : lattice_con α, c ∈ S ∧ r a b) :=
begin
  rw lattice_con_gen_eq,
  apply congr_arg Inf,
  ext,
  exact ⟨λ h _ _ ⟨r, hr⟩, h hr.1 hr.2,
         λ h r hS _ _ hr, h _ _ ⟨r, hS, hr⟩⟩,
end

/-- The supremum of a set of lattice congruences is the same as the smallest lattice congruence
    containing the supremum of the set's image under the map to the underlying binary relation. -/
lemma Sup_def {S : set (lattice_con α)} :
  Sup S = lattice_con_gen (Sup (@set.image (lattice_con α) (α → α → Prop) coe_fn S)) :=
begin
  rw [Sup_eq_lattice_con_gen, Sup_image],
  congr' with a b,
  simp only [Sup_image, supr_apply, supr_Prop_eq, exists_prop, rel_eq_coe]
end

variables (α)

/-- There is a Galois insertion of lattice congruences on a type with a multiplication `α` into
    binary relations on `α`. -/
protected def gi :
  @galois_insertion (α → α → Prop) (lattice_con α) _ _ lattice_con_gen coe_fn :=
{ choice := λ r h, lattice_con_gen r,
  gc := λ r c, ⟨λ H _ _ h, H $ lattice_con_gen.rel.of _ _ h, λ H, lattice_con_gen_of_lattice_con c ▸ lattice_con_gen_mono H⟩,
  le_l_u := λ a, (lattice_con_gen_of_lattice_con a).symm ▸ le_refl a,
  choice_eq := λ _ _, rfl }

variables {α} (c)


/-- Given a function `f`, the smallest lattice congruence containing the binary relation on `f`'s
image defined by '`a ≈ b` iff the elements of `f⁻¹(a)` are related to the elements of `f⁻¹(b)` by a
lattice congruence `c`.' -/
def map_gen (f : α → β) : lattice_con β :=
lattice_con_gen $ λ a b, ∃ a b, f a = a ∧ f b = b ∧ r a b

/-- Given a surjective lattice-preserving function `f` whose kernel is contained in a lattice
congruence `c`, the lattice congruence on `f`'s codomain defined by '`a ≈ b` iff the elements of
`f⁻¹(a)` are related to the elements of `f⁻¹(b)` by `c`.' -/
def map_of_surjective (f : α → β) (H : ∀ a b, f (a * b) = f a * f b) (h : lattice_ker f H ≤ c)
  (hf : surjective f) : lattice_con β :=
{ mul' := λ a b c d ⟨a, b, hw, hx, h1⟩ ⟨p, q, hy, hz, h2⟩,
    ⟨a * p, b * q, by rw [H, hw, hy], by rw [H, hx, hz], r.sup h1 h2⟩,
  ..r.to_setoid.map_of_surjective f h hf }

/-- A specialization of 'the smallest lattice congruence containing a lattice congruence `c` equals
`c`'. -/
lemma map_of_surjective_eq_map_gen {c : lattice_con α} {f : α → β} (H : ∀ a b, f (a * b) = f a * f b)
  (h : lattice_ker f H ≤ c) (hf : surjective f) :
  c.map_gen f = c.map_of_surjective f H h hf :=
by rw ←lattice_con_gen_of_lattice_con (c.map_of_surjective f H h hf); refl

/-- Given types with multiplications `α, β` and a lattice congruence `c` on `β`, a multiplication-preserving map `f : α → β` induces a lattice congruence on `f`'s domain defined by
'`a ≈ b` iff `f(a)` is related to `f(b)` by `c`.' -/
def comap (f : α → β) (H : ∀ a b, f (a * b) = f a * f b) (c : lattice_con β) : lattice_con α :=
{ mul' := λ a b c d h1 h2, show c (f (w * b)) (f (a * c)), by rw [H, H]; exact r.sup h1 h2,
  ..r.to_setoid.comap f }

@[simp] lemma comap_rel {f : α → β} (H : ∀ a b, f (a * b) = f a * f b)
  {c : lattice_con β} {a b : α} :
  comap f H r a b ↔ c (f a) (f b) :=
iff.rfl

section
open _root_.quotient

/-- Given a lattice congruence `c` on a type `α` with a multiplication, the order-preserving
bijection between the set of lattice congruences containing `c` and the lattice congruences on the
quotient of `α` by `c`. -/
def correspondence : {d // c ≤ d} ≃o (lattice_con r.quotient) :=
{ to_fun := λ d, d.1.map_of_surjective coe _
    (by rw lattice_ker_mk_eq; exact d.2) $ @exists_rep _ r.to_setoid,
  inv_fun := λ d, ⟨comap (coe : α → r.quotient) (λ a b, rfl) d, λ _ _ h,
    show d _ _, by rw c.eq.2 h; exact d.refl _ ⟩,
  left_inv := λ d, subtype.ext_iff_val.2 $ ext $ λ _ _,
    ⟨λ h, let ⟨a, b, hx, hy, H⟩ := h in
      d.1.trans (d.1.symm $ d.2 $ c.eq.1 hx) $ d.1.trans H $ d.2 $ c.eq.1 hy,
     λ h, ⟨_, _, rfl, rfl, h⟩⟩,
  right_inv := λ d, let Hm : lattice_ker (coe : α → r.quotient) (λ a b, rfl) ≤
        comap (coe : α → r.quotient) (λ a b, rfl) d :=
      λ a b h, show d _ _, by rw lattice_ker_mk_eq at h; exact c.eq.2 h ▸ d.refl _ in
    ext $ λ a b, ⟨λ h, let ⟨a, b, hx, hy, H⟩ := h in hx ▸ hy ▸ H,
      lattice_con.induction_on₂ a b $ λ w c h, ⟨w, c, rfl, rfl, h⟩⟩,
  map_rel_iff' := λ s t, ⟨λ h _ _ hs, let ⟨a, b, hx, hy, ht⟩ := h ⟨_, _, rfl, rfl, hs⟩ in
      t.1.trans (t.1.symm $ t.2 $ eq_rel.1 hx) $ t.1.trans ht $ t.2 $ eq_rel.1 hy,
      λ h _ _ hs, let ⟨a, b, hx, hy, Hs⟩ := hs in ⟨a, b, hx, hy, h Hs⟩⟩ }

end

end

section mul_one_class

variables {α} [mul_one_class α] [mul_one_class β] [mul_one_class γ] (c : lattice_con α)

/-- The quotient of a lattice by a lattice congruence is a lattice. -/
instance mul_one_class : mul_one_class r.quotient :=
{ one := ((1 : α) : r.quotient),
  mul := (*),
  mul_one := λ a, quotient.induction_on' a $ λ _, congr_arg coe $ mul_one _,
  one_mul := λ a, quotient.induction_on' a $ λ _, congr_arg coe $ one_mul _ }

variables {c}

/-- The 1 of the quotient of a lattice by a lattice congruence is the equivalence class of the
lattice's 1. -/
@[simp] lemma coe_one : ((1 : α) : r.quotient) = 1 := rfl

variables (α c)

/-- The sublattice of `α × α` defined by a lattice congruence on a lattice `α`. -/
protected def sublattice : sublattice (α × α) :=
{ carrier := { a | r a.1 a.2 },
  one_mem' := c.iseqv.1 1,
  mul_mem' := λ _ _, r.sup }

variables {α c}

/-- The lattice congruence on a lattice `α` from a sublattice of `α × α` for which membership is an
equivalence relation. -/
def of_sublattice (β : sublattice (α × α)) (H : equivalence (λ a b, (a, b) ∈ β)) : lattice_con α :=
{ r := λ a b, (a, b) ∈ β,
  iseqv := H,
  mul' := λ _ _ _ _, β.mul_mem }

/-- Coercion from a lattice congruence `c` on a lattice `α` to the sublattice of `α × α` whose
elements are `(a, b)` such that `a` is related to `b` by `c`. -/
instance to_sublattice : has_coe (lattice_con α) (sublattice (α × α)) := ⟨λ c, c.sublattice α⟩

lemma mem_coe {c : lattice_con α} {a b} : (a, b) ∈ (↑c : sublattice (α × α)) ↔ (a, b) ∈ c := iff.rfl

lemma to_sublattice_inj (c d : lattice_con α) (H : (c : sublattice (α × α)) = d) : c = d :=
ext $ λ a b, show (a, b) ∈ (c : sublattice (α × α)) ↔ (a, b) ∈ ↑d, by rw H

lemma le_iff {c d : lattice_con α} : c ≤ d ↔ (c : sublattice (α × α)) ≤ d :=
⟨λ h a H, h H, λ h a b hc, h $ show (a, b) ∈ c, from hc⟩

/-- The kernel of a lattice homomorphism as a lattice congruence. -/
def ker (f : α →* γ) : lattice_con α := lattice_ker f f.3

/-- The definition of the lattice congruence defined by a lattice homomorphism's kernel. -/
@[simp] lemma ker_rel (f : α →* γ) {a b} : ker f a b ↔ f a = f b := iff.rfl

/-- There exists an element of the quotient of a lattice by a lattice congruence (namely 1). -/
instance quotient.inhabited : inhabited r.quotient := ⟨((1 : α) : r.quotient)⟩

variables (c)

/-- The natural homomorphism from a lattice to its quotient by a lattice congruence. -/
def mk' : α →* r.quotient := ⟨coe, rfl, λ _ _, rfl⟩

variables (a b : α)

/-- The kernel of the natural homomorphism from a lattice to its quotient by a lattice congruence `c`
equals `c`. -/
@[simp] lemma mk'_ker : ker c.mk' = c := ext $ λ _ _, c.eq

variables {c}

/-- The natural homomorphism from a lattice to its quotient by a lattice congruence is surjective. -/
lemma mk'_surjective : surjective c.mk' := quotient.surjective_quotient_mk'

@[simp] lemma coe_mk' : (c.mk' : α → r.quotient) = coe := rfl

/-- The elements related to `a ∈ α`, `α` a lattice, by the kernel of a lattice homomorphism are
those in the preimage of `f(a)` under `f`. -/
lemma ker_apply_eq_preimage {f : α →* γ} (a) : (ker f) a = f ⁻¹' {f a} :=
set.ext $ λ a,
  ⟨λ h, set.mem_preimage.2 $ set.mem_singleton_iff.2 h.symm,
   λ h, (set.mem_singleton_iff.1 $ set.mem_preimage.1 h).symm⟩

/-- Given a lattice homomorphism `f : β → α` and a lattice congruence `c` on `α`, the lattice
congruence induced on `β` by `f` equals the kernel of `c`'s quotient homomorphism composed with
`f`. -/
lemma comap_eq {f : β →* α} : comap f f.map_mul c = ker (c.mk'.comp f) :=
ext $ λ a b, show c _ _ ↔ c.mk' _ = c.mk' _, by rw ←c.eq; refl

variables (c) (f : α →* γ)

/-- The homomorphism on the quotient of a lattice by a lattice congruence `c` induced by a
homomorphism constant on `c`'s equivalence classes. -/
def lift (H : c ≤ ker f) : r.quotient →* γ :=
{ to_fun := λ a, lattice_con.lift_on a f $ λ _ _ h, H h,
  map_one' := by rw ←f.map_one; refl,
  map_mul' := λ a b, lattice_con.induction_on₂ a b $ λ m n, f.map_mul m n ▸ rfl }

variables {c f}

/-- The diagram describing the universal property for quotients of lattices commutes. -/
lemma lift_mk' (H : c ≤ ker f) (a) : c.lift f H (c.mk' a) = f a := rfl

/-- The diagram describing the universal property for quotients of lattices commutes. -/
@[simp] lemma lift_coe (H : c ≤ ker f) (a : α) : c.lift f H a = f a := rfl

/-- The diagram describing the universal property for quotients of lattices commutes. -/
@[simp] lemma lift_comp_mk' (H : c ≤ ker f) : (c.lift f H).comp c.mk' = f := by ext; refl

/-- Given a homomorphism `f` from the quotient of a lattice by a lattice congruence, `f` equals the
homomorphism on the quotient induced by `f` composed with the natural map from the lattice to
the quotient. -/
@[simp]
lemma lift_apply_mk' (f : r.quotient →* γ) :
  c.lift (f.comp c.mk') (λ a b h, show f ↑x = f ↑y, by rw c.eq.2 h) = f :=
by ext; rcases a; refl

/-- Homomorphisms on the quotient of a lattice by a lattice congruence are equal if they are equal on
elements that are coercions from the lattice. -/
lemma lift_funext (f g : r.quotient →* γ) (h : ∀ a : α, f a = g a) : f = g :=
begin
  rw [←lift_apply_mk' f, ←lift_apply_mk' g],
  congr' 1,
  exact lattice_hom.ext_iff.2 h,
end

/-- The uniqueness part of the universal property for quotients of lattices. -/
lemma lift_unique (H : c ≤ ker f) (g : r.quotient →* γ)
  (Hg : g.comp c.mk' = f) : g = c.lift f H :=
lift_funext g (c.lift f H) $ λ a, by { subst f, refl }

/-- Given a lattice congruence `c` on a lattice and a homomorphism `f` constant on `c`'s equivalence
classes, `f` has the same image as the homomorphism that `f` induces on the  quotient. -/
lemma lift_range (H : c ≤ ker f) : (c.lift f H).mrange = f.mrange :=
sublattice.ext $ λ a, ⟨by rintros ⟨⟨b⟩, hy⟩; exact ⟨b, hy⟩, λ ⟨b, hy⟩, ⟨↑y, hy⟩⟩

/-- Surjective lattice homomorphisms constant on a lattice congruence `c`'s equivalence classes
    induce a surjective homomorphism on `c`'s quotient. -/
lemma lift_surjective_of_surjective (h : c ≤ ker f) (hf : surjective f) :
  surjective (c.lift f h) :=
λ b, exists.elim (hf b) $ λ w hw, ⟨w, (lift_mk' h w).symm ▸ hw⟩

variables (c f)

/-- Given a lattice homomorphism `f` from `α` to `γ`, the kernel of `f` is the unique congruence
relation on `α` whose induced map from the quotient of `α` to `γ` is injective. -/
lemma ker_eq_lift_of_injective (H : c ≤ ker f) (h : injective (c.lift f H)) : ker f = c :=
to_setoid_inj $ ker_eq_lift_of_injective f H h

variables {c}

/-- The homomorphism induced on the quotient of a lattice by the kernel of a lattice homomorphism. -/
def ker_lift : (ker f).quotient →* γ := (ker f).lift f $ λ _ _, id

variables {f}

/-- The diagram described by the universal property for quotients of lattices, when the congruence
    relation is the kernel of the homomorphism, commutes. -/
@[simp] lemma ker_lift_mk (a : α) :  ker_lift f a = f a := rfl

/-- Given a lattice homomorphism `f`, the induced homomorphism on the quotient by `f`'s kernel has
    the same image as `f`. -/
@[simp]
lemma ker_lift_range_eq : (ker_lift f).mrange = f.mrange :=
lift_range $ λ _ _, id

/-- A lattice homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
lemma ker_lift_injective (f : α →* γ) : injective (ker_lift f) :=
λ a b, quotient.induction_on₂' a b $ λ _ _, (ker f).eq.2

/-- Given lattice congruences `c, d` on a lattice such that `d` contains `c`, `d`'s quotient map
induces a homomorphism from the quotient by `c` to the quotient by `d`. -/
def map (c d : lattice_con α) (h : c ≤ d) : r.quotient →* d.quotient :=
c.lift d.mk' $ λ a b hc, show (ker d.mk') a b, from
  (mk'_ker d).symm ▸ h hc

/-- Given lattice congruences `c, d` on a lattice such that `d` contains `c`, the definition of the
homomorphism from the quotient by `c` to the quotient by `d` induced by `d`'s quotient  map. -/
lemma map_apply {c d : lattice_con α} (h : c ≤ d) (a) :
  c.map d h a = c.lift d.mk' (λ a b hc, d.eq.2 $ h hc) a := rfl

variables (c)

/-- The first isomorphism theorem for lattices. -/
noncomputable def quotient_ker_equiv_range (f : α →* γ) : (ker f).quotient ≃* f.mrange :=
{ map_mul' := lattice_hom.map_mul _,
  ..equiv.of_bijective
      ((@mul_equiv.to_lattice_hom (ker_lift f).mrange _ _ _
        $ mul_equiv.sublattice_congr ker_lift_range_eq).comp (ker_lift f).mrange_restrict) $
      (equiv.bijective _).comp
        ⟨λ a b h, ker_lift_injective f $ by rcases a; rcases b; injections,
         λ ⟨w, c, hz⟩, ⟨c, by rcases hz; rcases _x; refl⟩⟩ }

/-- The first isomorphism theorem for lattices in the case of a homomorphism with right inverse. -/
def quotient_ker_equiv_of_right_inverse (f : α →* γ) (g : γ → α)
  (hf : function.right_inverse g f) :
  (ker f).quotient ≃* γ :=
{ to_fun := ker_lift f,
  inv_fun := coe ∘ g,
  left_inv := λ a, ker_lift_injective _ (by rw [function.comp_app, ker_lift_mk, hf]),
  right_inv := hf,
  .. ker_lift f }

/-- The first isomorphism theorem for lattices in the case of a surjective homomorphism.

For a `computable` version, see `lattice_con.quotient_ker_equiv_of_right_inverse`.
-/
noncomputable def quotient_ker_equiv_of_surjective (f : α →* γ) (hf : surjective f) :
  (ker f).quotient ≃* γ :=
quotient_ker_equiv_of_right_inverse _ _ hf.has_right_inverse.some_spec

/-- The selattice_cond isomorphism theorem for lattices. -/
noncomputable def comap_quotient_equiv (f : β →* α) :
  (comap f f.map_mul c).quotient ≃* (c.mk'.comp f).mrange :=
(lattice_con.congr comap_eq).trans $ quotient_ker_equiv_range $ c.mk'.comp f

/-- The third isomorphism theorem for lattices. -/
def quotient_quotient_equiv_quotient (c d : lattice_con α) (h : c ≤ d) :
  (ker (c.map d h)).quotient ≃* d.quotient :=
{ map_mul' := λ a b, lattice_con.induction_on₂ a b $ λ w c, lattice_con.induction_on₂ w c $ λ a b,
    show _ = d.mk' a * d.mk' b, by rw ←d.mk'.map_mul; refl,
  ..quotient_quotient_equiv_quotient r.to_setoid d.to_setoid h }

end mul_one_class

section lattices

/-- Lattice lattice congruences preserve natural powers. -/
protected lemma pow {α : Type*} [lattice α] (c : lattice_con α) :
  ∀ (n : ℕ) {a b}, r a b → c (w ^ n) (a ^ n)
| 0 a b h := by simpa using c.refl _
| (nat.succ n) a b h := by simpa [pow_succ] using r.sup h (pow n h)

instance {α : Type*} [mul_one_class α] (c : lattice_con α) : has_one r.quotient :=
{ one := ((1 : α) : r.quotient) }

instance _root_.add_lattice_con.quotient.has_nsmul
  {α : Type*} [add_lattice α] (c : add_lattice_con α) : has_scalar ℕ r.quotient :=
{ smul := λ n a, quotient.lift_on' a (λ w, ((n • w : α) : r.quotient))
     $ λ a b h, c.eq.2 $ c.nsmul n h}

instance {α : Type*} [lattice α] (c : lattice_con α) : has_pow r.quotient ℕ :=
{ pow := λ a n, quotient.lift_on' a (λ w, ((w ^ n : α) : r.quotient))
     $ λ a b h, c.eq.2 $ c.pow n h}

/-- The quotient of a semigroup by a lattice congruence is a semigroup. -/
instance semigroup {α : Type*} [semigroup α] (c : lattice_con α) : semigroup r.quotient :=
function.surjective.semigroup _ quotient.surjective_quotient_mk' (λ _ _, rfl)

/-- The quotient of a commutative semigroup by a lattice congruence is a semigroup. -/
instance comm_semigroup {α : Type*} [comm_semigroup α] (c : lattice_con α) : comm_semigroup r.quotient :=
function.surjective.comm_semigroup _ quotient.surjective_quotient_mk' (λ _ _, rfl)

/-- The quotient of a lattice by a lattice congruence is a lattice. -/
instance lattice {α : Type*} [lattice α] (c : lattice_con α) : lattice r.quotient :=
function.surjective.lattice_pow _ quotient.surjective_quotient_mk' rfl (λ _ _, rfl) (λ _ _, rfl)

/-- The quotient of a `comm_lattice` by a lattice congruence is a `comm_lattice`. -/
instance comm_lattice {α : Type*} [comm_lattice α] (c : lattice_con α) :
  comm_lattice r.quotient :=
{ ..c.comm_semigroup, ..c.lattice}

end lattices

section groups

variables {α} [group α] [group β] [group γ] (c : lattice_con α)

/-- Lattice lattice congruences preserve inversion. -/
protected lemma inv : ∀ {a b}, r a b → c w⁻¹ x⁻¹ :=
λ a b h, by simpa using c.symm (r.sup (r.sup (c.refl x⁻¹) h) (c.refl y⁻¹))

/-- Lattice lattice congruences preserve division. -/
protected lemma div : ∀ {a b c d}, r a b → r b c → c (w / b) (a / c) :=
λ a b c d h1 h2, by simpa only [div_eq_mul_inv] using r.sup h1 (c.inv h2)

/-- Lattice lattice congruences preserve integer powers. -/
protected lemma zpow : ∀ (n : ℤ) {a b}, r a b → c (w ^ n) (a ^ n)
| (int.of_nat n) a b h := by simpa only [zpow_of_nat] using c.pow _ h
| -[1+ n] a b h := by simpa only [zpow_neg_succ_of_nat] using c.inv (c.pow _ h)

/-- The inversion induced on the quotient by a lattice congruence on a type with a inversion. -/
instance has_inv : has_inv r.quotient :=
⟨λ a, quotient.lift_on' a (λ w, ((w⁻¹ : α) : r.quotient))
     $ λ a b h, c.eq.2 $ c.inv h⟩

/-- The division induced on the quotient by a lattice congruence on a type with a division. -/
instance has_div : has_div r.quotient :=
⟨λ a b, quotient.lift_on₂' a b (λ w c, ((w / c : α) : r.quotient))
     $ λ _ _ _ _ h1 h2, c.eq.2 $ c.div h1 h2⟩

/-- The integer scaling induced on the quotient by a lattice congruence on a type with a
    subtraction. -/
instance _root_.add_lattice_con.quotient.has_zsmul
  {α : Type*} [add_group α] (c : add_lattice_con α) : has_scalar ℤ r.quotient :=
⟨λ r a, quotient.lift_on' a (λ w, ((c • w : α) : r.quotient))
     $ λ a b h, c.eq.2 $ c.zsmul c h⟩

/-- The integer power induced on the quotient by a lattice congruence on a type with a division. -/
instance has_zpow : has_pow r.quotient ℤ :=
⟨λ a c, quotient.lift_on' a (λ w, ((w ^ c : α) : r.quotient))
     $ λ a b h, c.eq.2 $ c.zpow c h⟩

/-- The quotient of a group by a lattice congruence is a group. -/
instance group : group r.quotient :=
function.surjective.group_pow _ quotient.surjective_quotient_mk' rfl
  (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

end groups

section units
variables [lattice α] {c : lattice_con α}

/-- In order to define a function `(lattice_con.quotient c)ˣ → α` on the units of `lattice_con.quotient c`,
where `c : lattice_con α` is a lattice congruence on a lattice, it suffices to define a function `f`
that takes elements `a b : α` with proofs of `c (a * b) 1` and `c (b * a) 1`, and returns an element
of `α` provided that `f a b _ _ = f x' y' _ _` whenever `r a x'` and `r b y'`. -/
def lift_on_units (u : units r.quotient)
  (f : Π (a b : α), c (a * b) 1 → c (b * a) 1 → α)
  (Hf : ∀ a b hxy hyx x' y' hxy' hyx', r a x' → r b y' → f a b hxy hyx = f x' y' hxy' hyx') :
  α :=
begin
  refine @lattice_con.hrec_on₂ α α _ _ c c (λ a b, a * b = 1 → b * a = 1 → α)
    (u : r.quotient) (↑u⁻¹ : r.quotient)
    (λ (a b : α) (hxy : (a * b : r.quotient) = 1) (hyx : (b * a : r.quotient) = 1),
    f a b (c.eq.1 hxy) (c.eq.1 hyx)) (λ a b x' y' hx hy, _) u.3 u.4,
  ext1, { rw [c.eq.2 hx, c.eq.2 hy] },
  rintro Hxy Hxy' -,
  ext1, { rw [c.eq.2 hx, c.eq.2 hy] },
  rintro Hyx Hyx' -,
  exact heq_of_eq (Hf _ _ _ _ _ _ _ _ hx hy)
end

/-- In order to define a function `(lattice_con.quotient c)ˣ → α` on the units of `lattice_con.quotient c`,
where `c : lattice_con α` is a lattice congruence on a lattice, it suffices to define a function `f`
that takes elements `a b : α` with proofs of `c (a * b) 1` and `c (b * a) 1`, and returns an element
of `α` provided that `f a b _ _ = f x' y' _ _` whenever `r a x'` and `r b y'`. -/
add_decl_doc add_lattice_con.lift_on_add_units

@[simp] lemma lift_on_units_mk (f : Π (a b : α), c (a * b) 1 → c (b * a) 1 → α)
  (Hf : ∀ a b hxy hyx x' y' hxy' hyx', r a x' → r b y' → f a b hxy hyx = f x' y' hxy' hyx')
  (a b : α) (hxy hyx) :
  lift_on_units ⟨(a : r.quotient), b, hxy, hyx⟩ f Hf = f a b (c.eq.1 hxy) (c.eq.1 hyx) :=
rfl

@[elab_as_eliminator]
lemma induction_on_units {p : units r.quotient → Prop} (u : units r.quotient)
  (H : ∀ (a b : α) (hxy : c (a * b) 1) (hyx : c (b * a) 1), p ⟨a, b, c.eq.2 hxy, c.eq.2 hyx⟩) :
  p u :=
begin
  rcases u with ⟨⟨a⟩, ⟨b⟩, h₁, h₂⟩,
  exact H a b (c.eq.1 h₁) (c.eq.1 h₂)
end

end units

end lattice_con
