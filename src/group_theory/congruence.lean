/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import group_theory.submonoid algebra.pi_instances data.equiv.algebra 

/-!
# Congruence relations

## Implementation notes

## Tags

-/
variables {M : Type*} {N : Type*} {P : Type*}

set_option old_structure_cmd true

namespace mul_equiv

-- group_theory.submonoid doesn't import data.equiv.algebra and vice versa. 

/-- Makes the identity multiplicative isomorphism from a proof two submonoids are equal. -/
@[to_additive add_submonoid_congr] 
def submonoid_congr [monoid M] {A B : submonoid M} (h : A = B) : A ≃* B :=
{ map_mul' := λ x y, rfl, ..equiv.set_congr $ submonoid.ext'_iff.2 h }

end mul_equiv

variables (M)

/-- Defining congruence relations as equivalence relations which preserve multiplication. -/
structure con [has_mul M] extends setoid M :=
(mul' : ∀ {w x y z}, r w x → r y z → r (w * y) (x * z))

/-- Defining congruence relations on additive monoids as equivalence relations which 
    preserve addition. -/
structure add_con (M : Type*) [has_add M] extends setoid M :=
(add' : ∀ {w x y z}, r w x → r y z → r (w + y) (x + z))

attribute [to_additive add_con] con
variables {M} 

/-- The inductively defined additive congruence closure of a binary relation. -/
inductive add_con_gen.rel [has_add M] (r : M → M → Prop) : M → M → Prop
| of {} : Π x y, r x y → add_con_gen.rel x y
| refl {} : Π x, add_con_gen.rel x x
| symm {} : Π x y, add_con_gen.rel x y → add_con_gen.rel y x
| trans {} : Π x y z, add_con_gen.rel x y → add_con_gen.rel y z → add_con_gen.rel x z
| add {} : Π w x y z, add_con_gen.rel w x → add_con_gen.rel y z → add_con_gen.rel (w + y) (x + z)

/-- The inductively defined multiplicative congruence closure of a binary relation. -/
@[to_additive add_con_gen.rel] inductive con_gen.rel [has_mul M] (r : M → M → Prop) : M → M → Prop
| of {} : Π x y, r x y → con_gen.rel x y
| refl {} : Π x, con_gen.rel x x
| symm {} : Π x y, con_gen.rel x y → con_gen.rel y x
| trans {} : Π x y z, con_gen.rel x y → con_gen.rel y z → con_gen.rel x z
| mul {} : Π w x y z, con_gen.rel w x → con_gen.rel y z → con_gen.rel (w * y) (x * z)

/-- The inductively defined multiplicative congruence closure of a binary relation. -/
@[to_additive add_con_gen] def con_gen [has_mul M] (r : M → M → Prop) : con M :=
⟨con_gen.rel r, ⟨λ _, con_gen.rel.refl _, λ _ _ h, con_gen.rel.symm _ _ h, 
  λ _ _ _ h1 h2, con_gen.rel.trans _ _ _ h1 h2⟩, con_gen.rel.mul⟩

variables {M} (c : con M)
namespace con

section
variables [has_mul M] [has_mul N] [has_mul P]

/-- A coercion from a congruence relation to its underlying binary relation. -/
@[to_additive]
instance : has_coe_to_fun (con M) := ⟨_, λ c, λ x y, c.r x y⟩

/-- Congruence relations are reflexive. -/
@[simp, refl, to_additive] lemma refl (x) : c.1 x x := c.2.1 x
/-- Congruence relations are symmetric. -/
@[simp, symm, to_additive] lemma symm : ∀ {x y}, c x y → c.1 y x := λ _ _ h, c.2.2.1 h
/-- Congruence relations are transitive. -/
@[simp, trans, to_additive] lemma trans : ∀ {x y z}, c x y → c y z → c.1 x z := 
λ  _ _ _ hx hy, c.2.2.2 hx hy
/-- Multiplicative congruence relations preserve multiplication. -/
@[simp, to_additive] lemma mul : ∀ {w x y z}, c w x → c y z → c (w*y) (x*z) :=
λ _ _ _ _ h1 h2, c.3 h1 h2

/-- For x, y ∈ M, for a congruence relation r on M we define 
    (x, y) ∈ M × M ↔ x is related to y by r. -/
@[to_additive] instance : has_mem (M × M) (con M) := ⟨λ x r, r x.1 x.2⟩

variables {c} 

/-- The map sending a congruence relation to its underlying binary relation is injective. -/
@[to_additive] lemma r_inj {c d : con M} (H : c.r = d.r) : c = d :=
by cases c; cases d; simpa using H

/-- Extensionality rule for congruence relations. -/
@[extensionality, to_additive] lemma ext {c d : con M} (H : ∀ x y, c x y ↔ d x y) :
  c = d := r_inj $ by ext x y; exact H x y

/-- Iff version of extensionality rule for congruence relations. -/
@[to_additive] lemma ext_iff {c d : con M} : (∀ x y, c x y ↔ d x y) ↔ c = d :=
⟨λ h, ext h, λ h x y, h ▸ iff.rfl⟩

/-- The product of two congruence relations c on M, d on N defined as 
    (x₁, x₂) and (y₁, y₂) ∈ M × N are related by c × d ↔ c x₁ y₁ and d x₂ y₂. -/
@[to_additive prod] protected def prod (c : con M) (d : con N) : con (M × N) :=
{ r := λ x y, c x.1 y.1 ∧ d x.2 y.2,
  iseqv := ⟨λ x, ⟨c.refl x.1, d.refl x.2⟩, λ _ _ h, ⟨c.symm h.1, d.symm h.2⟩,
            λ _ _ _ h1 h2, ⟨c.trans h1.1 h2.1, d.trans h1.2 h2.2⟩⟩,
  mul' := λ _ _ _ _ h1 h2, ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩ }

/-- The product of an indexed collection of congruence relations. -/
@[to_additive] def pi {ι : Type*} {f : ι → Type*} [Π i, has_mul (f i)] 
  (C : Π i, con (f i)) : con (Π i, f i) :=
{ r := λ x y, ∀ i, (C i) (x i) (y i),
  iseqv := ⟨λ x i, (C i).refl (x i), λ _ _ h i, (C i).symm (h i),
              λ _ _ _ h1 h2 i, (C i).trans (h1 i) (h2 i)⟩,
  mul' := λ _ _ _ _ h1 h2 i, (C i).mul (h1 i) (h2 i) }

variables (c)

@[simp, to_additive] lemma setoid_eq : c.to_setoid.r = c := rfl

/-- Defining the quotient of a type by a congruence relation. -/
@[to_additive] protected def quotient := quotient $ c.to_setoid

/-- Coercion from a type to its quotient under a congruence relation. -/
@[to_additive, priority 0] instance : has_coe M (c.quotient) := ⟨@quotient.mk _ c.to_setoid⟩

/-- The quotient of a type with decidable equality under a congruence relation also has
    decidable equality. -/
@[to_additive] instance [d : ∀ a b, decidable (c a b)] : decidable_eq c.quotient :=
@quotient.decidable_eq M c.to_setoid d

/-- Defines a function on the quotient of M by a congruence relation c, given a function 
    on M that is constant on c's equivalence classes. -/
@[elab_as_eliminator, reducible, to_additive]
protected def lift_on {β} {c : con M} (q : c.quotient) (f : M → β)
  (h : ∀ a b, c a b → f a = f b) : β := quotient.lift_on' q f h

variables {c}

/-- A proposition is true for all elements of a quotient of M by a congruence relation if it is
    for all x ∈ M, it is true for the image of x under the coercion to the quotient. -/
@[elab_as_eliminator, to_additive]
lemma ind {C : c.quotient → Prop} (H : ∀ x : M, C x) : ∀ q, C q :=
quotient.ind' H

/-- A proposition is true for an element of a quotient of M by a congruence relation if
    for all x ∈ M, it is true for the image of x under the coercion to the quotient. -/
@[elab_as_eliminator, to_additive]
lemma induction_on {C : c.quotient → Prop} (q : c.quotient) (H : ∀ x : M, C x) : C q :=
quotient.induction_on' q H

/-- A version of con.induction_on which takes two arguments (which needn't be from quotients 
    on the same type). -/
@[elab_as_eliminator, to_additive]
lemma induction_on₂ {d : con N} {C : c.quotient → d.quotient → Prop}
  (p : c.quotient) (q : d.quotient) (H : ∀ (x : M) (y : N), C x y) : C p q :=
quotient.induction_on₂' p q H

variables (c)

/-- Two elements are related by a congruence relation ↔ they are mapped to the same element
   of the quotient type. -/
@[simp, to_additive] protected lemma eq (a b : M) : (a : c.quotient) = b ↔ c a b :=
quotient.eq'

/-- Defining multiplication on the quotient of a type by a congruence relation. -/
@[to_additive] instance has_mul : has_mul c.quotient :=
⟨λ x y, quotient.lift_on₂' x y (λ w z, (((w*z) : M) : c.quotient))
         $ λ _ _ _ _ h1 h2, (c.eq _ _).2 $ c.mul h1 h2⟩

variables {c} 

/-- The coercion to the quotient by a congruence relation commutes with multiplication by definition. -/
@[simp, to_additive] lemma coe_mul (x y : M) : 
  (x : c.quotient) * (y : c.quotient) = ((x * y : M) : c.quotient)  := rfl

/-- Stating the definition of the function on the quotient of M by a congruence relation c
    induced by a function on M that is constant on c's equivalence classes. -/
@[simp, to_additive] lemma lift_on_beta {β} (c : con M) (f : M → β)
  (h : ∀ a b, c a b → f a = f b) (x : M) :
  con.lift_on (x : c.quotient) f h = f x := rfl 

/-- Makes a multiplicative isomorphism between the quotients of M by 2 congruence relations, given 
    that the relations are equal. -/
@[to_additive] protected def congr {c d : con M} (h : c = d) :  c.quotient ≃* d.quotient :=
{ map_mul' := λ x y, by rcases x; rcases y; refl,
  ..quotient.congr (equiv.refl M) $ by apply ext_iff.2 h }

open lattice 

/-- For congruence relations c d, c ≤ d iff ∀ x y ∈ M, x is related to y by d if x is
    related to y by c. -/
@[to_additive] instance : has_le (con M) := ⟨λ c d, c.to_setoid ≤ d.to_setoid⟩

/-- Stating the definition of ≤ for congruence relations. -/
@[to_additive] theorem le_def {c d : con M} : c ≤ d ↔ ∀ {x y}, c x y → d x y := iff.rfl

/-- The infimum of a set of congruence relations on a given type. -/
@[to_additive] instance : has_Inf (con M) :=
⟨λ S, ⟨λ x y, ∀ c : con M, c ∈ S → c x y, 
⟨λ x c hc, c.refl x, λ _ _ h c hc, c.symm $ h c hc, 
 λ _ _ _ h1 h2 c hc, c.trans (h1 c hc) $ h2 c hc⟩,
 λ _ _ _ _ h1 h2 c hc, c.mul (h1 c hc) $ h2 c hc⟩⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying equivalence relation. -/
@[to_additive] lemma Inf_to_setoid (S : set (con M)) : (Inf S).to_setoid = Inf (to_setoid '' S) :=
setoid.ext' $ λ x y, ⟨λ h r ⟨c, hS, hr⟩, by rw ←hr; exact h c hS, 
  λ h c hS, h c.to_setoid ⟨c, hS, rfl⟩⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image 
    under the map to the underlying binary relation. -/
@[to_additive] lemma Inf_def (S : set (con M)) : (Inf S).r = Inf (r '' S) :=
begin
  show (Inf S).to_setoid.rel = _,
  rw [Inf_to_setoid S, setoid.Inf_def], 
  congr' 1, ext, 
  exact ⟨λ ⟨r, ⟨r', hS, hr'⟩, hr⟩, ⟨r', hS, by rw [←hr, ←hr']; refl⟩,
         λ ⟨r, hS, hr⟩, ⟨r.to_setoid, set.mem_image_of_mem _ hS, hr⟩⟩,
end 

/-- If a congruence relation c is contained in every element of a set s of congruence relations,
    c is contained in the infimum of s. -/
@[to_additive] lemma le_Inf (s : set (con M)) (c) : (∀d ∈ s, c ≤ d) → c ≤ Inf s :=
λ h _ _ hc r hr, h r hr _ _ hc

/-- The infimum of a set of congruence relations on a given type is contained in every element
    of the set. -/
@[to_additive] lemma Inf_le (s : set (con M)) (c) : c ∈ s → Inf s ≤ c :=
λ hc _ _ h, h c hc 

/-- The inductively defined congruence closure of a binary relation r equals the infimum of the 
    set of congruence relations containing r. -/
@[to_additive add_con_gen_eq] theorem con_gen_eq (r : M → M → Prop) : 
  con_gen r = Inf {s : con M | ∀ x y, r x y → s.r x y} :=
ext $ λ x y, 
  ⟨λ H, con_gen.rel.rec_on H (λ _ _ h _ hs, hs _ _ h) (refl _) (λ _ _ _ h, symm _ h) 
    (λ _ _ _ _ _ h1 h2, trans _ h1 h2) 
    $ λ w x y z _ _ h1 h2 c hc, c.mul (h1 c hc) $ h2 c hc, 
  Inf_le _ _ (λ _ _, con_gen.rel.of _ _) _ _⟩

/-- The congruence closure of a binary relation r is contained in any congruence relation containing
    r. -/
@[to_additive add_con_gen_le] 
theorem con_gen_le {r : M → M → Prop} {c : con M} (h : ∀ x y, r x y → c.r x y) : 
  con_gen r ≤ c :=
by rw con_gen_eq; exact Inf_le _ _ h

/-- Congruence closure of binary relations is monotonic. -/
@[to_additive add_con_gen_mono] 
theorem con_gen_mono {r s : M → M → Prop} (h : ∀ x y, r x y → s x y) : 
  con_gen r ≤ con_gen s :=
con_gen_le $ λ x y hr, con_gen.rel.of _ _ $ h x y hr

/-- The complete lattice of congruence relations on a given type. -/
@[to_additive] instance : complete_lattice (con M) :=
{ sup := λ c d, Inf { x | c ≤ x ∧ d ≤ x},
  le := (≤),
  lt := λ c d, c ≤ d ∧ ¬d ≤ c,
  le_refl := λ c x y h, h,
  le_trans := λ c1 c2 c3 h1 h2 x y h, h2 x y $ h1 x y h,
  lt_iff_le_not_le := λ _ _, iff.rfl,
  le_antisymm := λ c d hc hd, ext $ λ x y, ⟨hc x y, hd x y⟩
  le_sup_left := λ _ _ _ _ h r hr, hr.1 _ _ h,
  le_sup_right := λ _ _ _ _ h r hr, hr.2 _ _ h,
  sup_le := λ _ _ c h1 h2, Inf_le _ c ⟨h1, h2⟩,
  inf := λ c d, ⟨(c.to_setoid ⊓ d.to_setoid).1, (c.to_setoid ⊓ d.to_setoid).2, 
                  λ _ _ _ _ h1 h2, ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩⟩,
  inf_le_left := λ _ _ _ _ h, h.1,
  inf_le_right := λ _ _ _ _ h, h.2,
  le_inf := λ _ _ _ hb hc _ _ h, ⟨hb _ _ h, hc _ _ h⟩,
  top := { mul' := λ _ _ _ _ h1 h2, trivial, ..setoid.complete_lattice.top},
  le_top := λ c x y h, trivial,
  bot := { mul' := λ _ _ _ _ h1 h2, h1 ▸ h2 ▸ rfl, ..setoid.complete_lattice.bot},
  bot_le := λ c x y h, h ▸ c.refl x,
  Sup := λ tt, Inf {t | ∀t'∈tt, t' ≤ t},
  Inf := has_Inf.Inf,
  le_Sup := λ _ _ hs, le_Inf _ _ $ λ c' hc', hc' _ hs,
  Sup_le := λ _ _ hs, Inf_le _ _ hs,
  Inf_le := λ  _ _, Inf_le _ _,
  le_Inf := λ _ _, le_Inf _ _ }

/-- The infimum of 2 congruence relations equals the infimum of the underlying binary operations. -/
@[to_additive] lemma inf_def {c d : con M} : (c ⊓ d).r = c.r ⊓ d.r := rfl 

/-- The supremum of 2 congruence relations equals the congruence closure of the infimum of the 
    underlying binary operations. -/
@[to_additive] lemma sup_def {c d : con M} : c ⊔ d = con_gen (c.r ⊔ d.r) :=
by rw sup_eq_con_gen; refl

/-- Stating the definition of the infimum of two congruence relations. -/
@[to_additive] theorem inf_iff_and {c d : con M} {x y} : (c ⊓ d) x y ↔ c x y ∧ d x y := iff.rfl

/-- Congruence relations equal their congruence closure. -/
@[simp, to_additive add_con_gen_of_add_con] 
lemma con_gen_of_con (c : con M) : con_gen c.r = c :=
le_antisymm (by rw con_gen_eq; exact Inf_le _ c (λ x y h, h)) con_gen.rel.of

/-- Congruence closure of binary relations is idempotent. -/
@[simp, to_additive add_con_gen_idem] 
lemma con_gen_idem (r : M → M → Prop) : 
  con_gen (con_gen r).r = con_gen r :=
con_gen_of_con _ 

variables (M)

/-- There is a Galois insertion of congruence relations on α into binary relations 
    on α, with congruence closure the lower adjoint. -/
@[to_additive] def con.gi : @galois_insertion (M → M → Prop) (con M) _ _ con_gen r :=
{ choice := λ r h, con_gen r,
 gc := λ r c, ⟨λ H _ _ h, H _ _ $ con_gen.rel.of _ _ h, λ H, con_gen_of_con c ▸ con_gen_mono H⟩,
  le_l_u := λ x, (con_gen_of_con x).symm ▸ le_refl x,
  choice_eq := λ _ _, rfl} 

variables {M}

/-- The supremum of congruence relations c, d equals the congruence closure of the binary relation
    'x is related to y by c or d'. -/
@[to_additive sup_eq_add_con_gen] 
lemma sup_eq_con_gen (c d : con M) : 
  c ⊔ d = con_gen (λ x y, c x y ∨ d x y) :=
by rw con_gen_eq; apply congr_arg Inf; ext; exact 
  ⟨λ h _ _ H, or.elim H (λ hl, h.1 _ _ hl) $ λ hr, h.2 _ _ hr, 
   λ H, ⟨λ _ _ h, H _ _ $ or.inl h, λ _ _ h, H _ _ $ or.inr h⟩⟩

/-- The supremum of a set of congruence relations S equals the congruence closure of the 
    binary relation '∃ c ∈ S such that x is related to y by c'. -/
@[to_additive Sup_eq_add_con_gen] 
lemma Sup_eq_con_gen (S : set (con M)) : 
  Sup S = con_gen (λ x y, ∃ c : con M, c∈S ∧ c x y) :=
by rw con_gen_eq; apply congr_arg Inf; ext;
   exact ⟨λ h _ _ ⟨r, hr⟩, h r hr.1 _ _ hr.2, λ h r hS _ _ hr, h _ _ ⟨r, hS, hr⟩⟩

/-- The supremum of a set of congruence relations is the same as the congruence closure of the
    supremum of the set's image under the map to the underlying binary relation. -/
@[to_additive] lemma Sup_def {S : set (con M)} : Sup S = con_gen (Sup (r '' S)) := 
begin
  rw Sup_eq_con_gen, 
  congr,
  ext x y,
  erw [Sup_image, supr_apply, supr_apply, supr_Prop_eq], 
  split,
    rintro ⟨r, h, hr⟩, 
    use r,
    rw [supr_apply, supr_apply, supr_Prop_eq], 
    exact ⟨h, hr⟩,
  rintro ⟨r, h⟩, 
  obtain ⟨h, hr⟩ := by rw [supr_apply, supr_apply, supr_Prop_eq] at h; exact h,
  exact ⟨r, h, hr⟩,
end 

variables (c)

/-- Given a congruence relation c on M, the natural map from congruence relations containing
    c to congruence relations on the quotient of M by c. -/
@[to_additive to_add_con] def to_con (d : {d // c ≤ d}) : con c.quotient :=
{ mul' := λ w x y z, quotient.induction_on₂' w x $ 
    λ _ _, quotient.induction_on₂' y z $ λ _ _ h1 h2, d.1.mul h1 h2, 
  ..c.to_setoid.to_quotient (⟨d.1.to_setoid, d.2⟩ : {d : setoid M // c.to_setoid ≤ d}) }

/-- Given an congruence relation c on M and a map f to the quotient of M by c, an
    congruence relation d on the quotient induces an congruence relation on f's domain defined
    by x ≈ y ↔ f(x) is related to f(y) by d. -/
@[to_additive of_add_con] def of_con (f : N → c.quotient) (d : con c.quotient) : con N :=
{ r := λ x y, d (f x) (f y),
  iseqv := ⟨λ x, d.refl _, λ _ _ h, d.symm h, λ _ _ _ h1 h2, d.trans h1 h2⟩,
  mul' := λ _ _ _ _ h1 h2, d.mul h1 h2}

/-- Given an congruence relation c on M, the order-preserving bijection between the set of 
    congruence relations containing c and the congruence relations on the quotient of M by c. -/
@[to_additive] def correspondence : ((≤) : {d // c ≤ d} → {d // c ≤ d} → Prop) ≃o
  ((≤) : con c.quotient → con c.quotient → Prop) :=
{ to_fun := λ d, c.to_con d,
  inv_fun := λ d, subtype.mk (c.of_con quotient.mk' d) $ 
    λ x y h, show d x y, from (c.eq _ _).2 h ▸ d.refl x,
  left_inv := λ d, by rw subtype.ext; ext; refl,
  right_inv := λ d, by ext; rcases x; rcases y; refl,
  ord := λ a b,
    ⟨λ hle x y, con.induction_on₂ x y $
       λ w z h, by apply hle w z h,
     λ H p q h, by apply H (p : _) (q : _) h⟩ }

end 

variables (M) [monoid M] [monoid N] [monoid P]

/-- The submonoid of M × M defined by a congruence relation on a monoid M. -/
@[to_additive add_submonoid] protected def submonoid : submonoid (M × M) :=
{ carrier := { x | c x.1 x.2 },
  one_mem' := c.iseqv.1 1,
  mul_mem' := λ _ _ hx hy, c.mul hx hy }

variables {M}

/-- Makes a congruence relation on a monoid M from a submonoid of M × M which is 
    also an equivalence relation. -/
@[to_additive of_add_submonoid] 
def of_submonoid (N : submonoid (M × M)) (H : equivalence (λ x y, (x, y) ∈ N)) : con M :=
{ r := λ x y, (x, y) ∈ N,
  iseqv := H,
  mul' := λ _ _ _ _ h1 h2, N.mul_mem h1 h2 }

/-- The kernel of a monoid homomorphism as a congruence relation. -/
@[to_additive] def ker (f : M →* P) : con M :=
{ r := λ x y, f x = f y,
  iseqv := ⟨λ _, rfl, λ _ _ h, h.symm, λ _ _ _ hx hy, eq.trans hx hy⟩,
  mul' := λ _ _ _ _ h1 h2, by rw [f.map_mul, h1, h2, f.map_mul] }

/-- Stating the definition of the congruence relation defined by a monoid homomorphism's kernel. -/
@[to_additive] lemma ker_rel (f : M →* P) {x y} : con.ker f x y ↔ f x = f y := iff.rfl

/-- Restriction of a congruence relation to a submonoid. -/
@[to_additive] def subtype (A : submonoid M) : con A :=
⟨λ x y, c x y, ⟨λ x, c.refl x, λ x y h, c.symm h, λ x y z h1 h2, c.trans h1 h2⟩,
 λ w x y z h1 h2, c.mul h1 h2⟩

variables {c} 

/-- Stating the definition of the restriction of a congruence relation to a submonoid. -/
@[simp, to_additive] lemma subtype_apply {A : submonoid M} {x y} : c.subtype A x y ↔ c x y := iff.rfl

/-- There exists an element of the quotient of a monoid by a congruence relation (namely 1). -/
@[to_additive] instance : inhabited c.quotient := ⟨((1 : M) : c.quotient)⟩

variables (c)

/-- The quotient of a monoid by a congruence relation is a monoid. -/
@[to_additive add_monoid] instance monoid : monoid c.quotient :=
{ one := ((1 : M) : c.quotient),
  mul := (*),
  mul_assoc := λ x y z, quotient.induction_on₃' x y z
               $ λ _ _ _, congr_arg coe $ mul_assoc _ _ _,
  mul_one := λ x, quotient.induction_on' x $ λ _, congr_arg coe $ mul_one _,
  one_mul := λ x, quotient.induction_on' x $ λ _, congr_arg coe $ one_mul _ }

/-- The natural homomorphism from a monoid to its quotient by a congruence relation. -/
@[to_additive] def mk' : M →* c.quotient := ⟨coe, rfl, λ _ _, rfl⟩

variables (x y : M)

/-- The kernel of the natural homomorphism from a monoid to its quotient by a congruence relation is the
    original relation. -/
@[simp, to_additive] lemma mk'_ker : con.ker c.mk' = c := ext $ λ _ _, c.eq _ _

variables {c}

/-- The natural homomorphism from a monoid to its quotient by a congruence relation is surjective. -/
@[to_additive] lemma mk'_surjective : function.surjective c.mk' :=
by apply ind; exact λ x, ⟨x, rfl⟩

@[simp, to_additive] lemma mk'_one : c.mk' 1 = 1 := rfl
@[simp, to_additive] lemma mk'_mul : c.mk' (x * y) = c.mk' x * c.mk' y := rfl
@[simp] lemma mk'_pow : ∀ n : ℕ, c.mk' (x ^ n) = (c.mk' x) ^ n
| 0 := c.mk'.map_one
| (m + 1) := by rw [pow_succ, c.mk'.map_mul, mk'_pow m]; refl
@[simp, to_additive] lemma comp_mk'_apply (g : c.quotient →* P) {x} : g.comp c.mk' x = g x := rfl

@[simp, to_additive] lemma coe_one : ((1 : M) : c.quotient) = 1 := rfl

lemma coe_pow : ∀ n : ℕ, (x ^ n : c.quotient) = (x : c.quotient) ^ n
| 0            := pow_zero _
| (nat.succ n) := by rw pow_succ _

@[to_additive] lemma ker_apply_eq_preimage {f : M →* P} (x) : (con.ker f) x = f ⁻¹' {f x} :=
set.ext $ λ x,
  ⟨λ h, set.mem_preimage.2 (set.mem_singleton_iff.2 h.symm),
   λ h, (set.mem_singleton_iff.1 (set.mem_preimage.1 h)).symm⟩

@[to_additive to_add_submonoid] 
instance to_submonoid : has_coe (con M) (submonoid (M × M)) := ⟨λ c, c.submonoid M⟩

@[to_additive] lemma le_iff {c d : con M} : c ≤ d ↔ (c : submonoid (M × M)) ≤ d := 
⟨λ h x hx, h x.1 x.2 hx, λ h x y hc, h $ show (x, y) ∈ c, from hc⟩ 

@[to_additive] lemma mem_coe {c : con M} {x y} :
  (x, y) ∈ (↑c : submonoid (M × M)) ↔ (x, y) ∈ c := iff.rfl

@[to_additive to_add_submonoid_inj] 
theorem to_submonoid_inj (c d : con M) (H : (c : submonoid (M × M)) = d) : c = d :=
ext $ λ x y, show (x,y) ∈ (c : submonoid (M × M)) ↔ (x,y) ∈ ↑d, by rw H

variables (c) (f : M →* P)

@[to_additive] def lift (H : ∀ x y, c x y → f x = f y) : c.quotient →* P :=
{ to_fun := λ x, con.lift_on x f $ λ a b h, H a b h,
  map_one' := by rw ←f.map_one; refl,
  map_mul' := λ x y, con.induction_on₂ x y $ λ m n, f.map_mul m n ▸ rfl}

@[to_additive] def ker_lift (f : M →* P) : (con.ker f).quotient →* P :=
(con.ker f).lift f $ λ x y h, h

variables {c f}

@[simp, to_additive] lemma lift_mk' (H : ∀ x y, c x y → f x = f y) (m) :
  c.lift f H (c.mk' m) = f m := rfl

@[simp, to_additive] lemma lift_coe (H : ∀ x y, c x y → f x = f y) (m : M) :
  c.lift f H m = f m := rfl

@[simp, to_additive] theorem lift_comp_mk' (H : ∀ x y, c x y → f x = f y) :
  (c.lift f H).comp c.mk' = f := by ext; refl

@[simp, to_additive] lemma lift_apply_mk' (f : c.quotient →* P) :
  c.lift (f.comp c.mk') (λ x y h, by simp [(c.eq _ _).2 h]) = f :=
by ext; rcases x; refl

@[to_additive] lemma lift_funext (f g : c.quotient →* P) (h : ∀ a : M, f a = g a) : f = g :=
by { rw [←lift_apply_mk' f, ← lift_apply_mk' g], congr' 1, ext, apply h x }

@[to_additive] theorem lift_unique (H : ∀ x y, c x y → f x = f y) (g : c.quotient →* P)
  (Hg : g.comp c.mk' = f) : g = c.lift f H :=
lift_funext g (c.lift f H) $ λ x, by rw [lift_coe H, ←con.comp_mk'_apply, Hg]

@[to_additive] theorem lift_range (H : ∀ x y, c x y → f x = f y) : (c.lift f H).range = f.range :=
submonoid.ext $ λ x,
  ⟨λ ⟨y, hy⟩, by revert hy; rcases y; exact
     (λ hy, ⟨y, hy.1, by rw [hy.2.symm, (lift_coe H _).symm]; refl⟩),
   λ ⟨y, hy⟩, ⟨↑y, hy.1, by rw ←hy.2; refl⟩⟩

@[simp, to_additive] lemma ker_lift_mk {x : M} :  ker_lift f x = f x := rfl

@[to_additive] lemma ker_lift_range_eq : (ker_lift f).range = f.range :=
lift_range $ λ x y h, h

@[to_additive] lemma injective_ker_lift (f : M →* P) : function.injective (ker_lift f) :=
λ x y, con.induction_on₂ x y $ λ _ _ h, ((con.ker f).eq _ _).2 $ by rwa ker_lift_mk at h

@[to_additive] def map (c d : con M) (h : c ≤ d) : c.quotient →* d.quotient :=
c.lift d.mk' $ λ x y hc, show (con.ker d.mk') x y, from
  (mk'_ker d).symm ▸ h x y hc

@[simp, to_additive] lemma map_apply {c d : con M} (h : c ≤ d) (x) :
  c.map d h x = c.lift d.mk' (λ x y hc, (d.eq x y).2 $ h x y hc) x := rfl

@[to_additive] lemma ker_eq_of_equiv (h : c.quotient ≃* P) (f : M →* P) 
  (H : ∀ x y, c x y → f x = f y) 
  (hf : h.to_monoid_hom = c.lift f H) : con.ker f = c :=
le_antisymm (λ x y hk, by change f x = f y at hk;
    rw [←lift_coe H, ←lift_coe H, ←hf] at hk;
    exact (c.eq _ _).1 (h.to_equiv.injective hk)) $
  λ _ _ h, H _ _ h
 
variables (c)

@[to_additive] 
noncomputable def quotient_ker_equiv_range (f : M →* P) : (con.ker f).quotient ≃* f.range :=
{ map_mul' := monoid_hom.map_mul _,
  ..@equiv.of_bijective _ _
      ((@mul_equiv.to_monoid_hom (ker_lift f).range _ _ _ 
        (mul_equiv.submonoid_congr ker_lift_range_eq)).comp (ker_lift f).range_mk) $
      function.bijective_comp (equiv.bijective _)
        ⟨λ x y h, injective_ker_lift f $ by rcases x; rcases y; injections, 
         λ ⟨w, z, hzm, hz⟩, ⟨z, by rcases hz; rcases _x; refl⟩⟩ }

@[to_additive] lemma lift_surjective_of_surjective (hf : function.surjective f) : 
  function.surjective (ker_lift f) :=
λ y, exists.elim (hf y) $ λ w hw, ⟨w, hw⟩

@[to_additive] 
noncomputable def quotient_ker_equiv_of_surjective (f : M →* P) (hf : function.surjective f) :
  (con.ker f).quotient ≃* P :=
{ map_mul' := monoid_hom.map_mul _,
  ..(@equiv.of_bijective _ _ (ker_lift f) ⟨injective_ker_lift f, lift_surjective_of_surjective hf⟩) }

@[to_additive] lemma subtype_eq (A : submonoid M) : c.subtype A = con.ker (c.mk'.comp A.subtype) :=
con.ext $ λ x y,
  ⟨λ h, show ((x : M) : c.quotient) = (y : M), from (c.eq _ _).2 $ subtype_apply.2 h,
   λ h, by rw [subtype_apply, ←mk'_ker c]; simpa using h⟩

@[to_additive add_submonoid_quotient_equiv] 
noncomputable def submonoid_quotient_equiv (A : submonoid M) :
  (c.subtype A).quotient ≃* (c.mk'.comp A.subtype).range :=
mul_equiv.trans (con.congr $ subtype_eq c A) $ quotient_ker_equiv_range (c.mk'.comp A.subtype)

@[to_additive] 
lemma surjective_of_con_lift (d : con M) (h : c ≤ d) : function.surjective (c.map d h) :=
λ x, by rcases x; exact ⟨x, rfl⟩

@[to_additive] 
noncomputable def quotient_quotient_equiv_quotient (c d : con M) (h : c ≤ d) :
  (con.ker (c.map d h)).quotient ≃* d.quotient :=
quotient_ker_equiv_of_surjective _ $ surjective_of_con_lift c d h

end con 
