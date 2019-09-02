/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import group_theory.submonoid order.order_iso algebra.pi_instances data.equiv.algebra tactic.default

variables {M : Type*} {N : Type*} {P : Type*} [monoid M] [monoid N] [monoid P]

set_option old_structure_cmd true

namespace mul_equiv
--not sure where to put this; would need to import group_theory.submonoid to put it in data.equiv.algebra and vice versa.
/-- Makes the natural isomorphism between two equal submonoids. -/
def submonoid_congr {A B : submonoid M} (h : A = B) : A ≃* B :=
{ map_mul' := λ x y, rfl,
  ..equiv.set_congr $ submonoid.ext'_iff.2 h }

end mul_equiv

namespace setoid

def r' (r : setoid M) := @setoid.r _ r
lemma ext' {r s : setoid M} (H : ∀ a b, r.r' a b ↔ s.r' a b) : r = s := ext H

def to_set (r : setoid M) : set (M × M) := {x : M × M | @setoid.r _ r x.1 x.2}
def of_set (r : set (M × M)) (H : equivalence (λ x y, (x, y) ∈ r)) : setoid M :=
⟨λ x y, (x, y) ∈ r, H⟩

instance : has_le (setoid M) := ⟨λ r s, ∀ x y, r.r' x y → s.r' x y⟩
instance : has_mem (M × M) (setoid M) := ⟨λ x r, x ∈ r.to_set⟩

lemma le_def (r s : setoid M) : r ≤ s ↔ (∀ x y, r.r' x y → s.r' x y) := iff.rfl

lemma mem_def (r : setoid M) {x y} : (x, y) ∈ r ↔ (x, y) ∈ r.to_set := iff.rfl
lemma mem_rel (r : setoid M) {x y} : (x, y) ∈ r ↔ r.r' x y := iff.rfl

@[simp, refl] lemma refl' (r : setoid M) (x) : r.r' x x := r.2.1 x
@[simp, symm] lemma symm' (r : setoid M) : 
  ∀ {x y}, r.r' x y → r.r' y x := λ _ _ h, r.2.2.1 h
@[simp, trans] lemma trans' (r : setoid M) : ∀ {x y z}, r.r' x y → r.r' y z → r.r' x z := 
λ  _ _ _ hx hy, r.2.2.2 hx hy
variables (M)
def diag : setoid M :=
⟨(=), ⟨λ x, rfl, λ x y h, h.symm, λ _ _ _ h1 h2, h1.trans h2⟩⟩

def top : setoid M := 
⟨λ _ _, true, ⟨λ x, trivial, λ _ _ h, h, λ _ _ _ h1 h2, h1⟩⟩

end setoid
variables (M)
structure con extends setoid M :=
(mul' : ∀ {w x y z}, r w x → r y z → r (w * y) (x * z))

/-- Defining congruence relations on additive monoids as equivalence relations which 
    preserve addition. -/
structure add_con (M : Type*) [add_monoid M] extends setoid M :=
(add' : ∀ {w x y z}, r w x → r y z → r (w + y) (x + z))

attribute [to_additive add_con] con
attribute [to_additive add_con.r] con.r
attribute [to_additive add_con.cases_on] con.cases_on
attribute [to_additive add_con.has_sizeof_inst] con.has_sizeof_inst
attribute [to_additive add_con.mk] con.mk
attribute [to_additive add_con.mk.inj] con.mk.inj
attribute [to_additive add_con.mk.inj_arrow] con.mk.inj_arrow
attribute [to_additive add_con.mk.inj_eq] con.mk.inj_eq
attribute [to_additive add_con.mk.sizeof_spec] con.mk.sizeof_spec
attribute [to_additive add_con.iseqv] con.iseqv
attribute [to_additive add_con.no_confusion] con.no_confusion
attribute [to_additive add_con.no_confusion_type] con.no_confusion_type
attribute [to_additive add_con.add'] con.mul'
attribute [to_additive add_con.rec] con.rec
attribute [to_additive add_con.rec_on] con.rec_on
attribute [to_additive add_con.sizeof] con.sizeof
attribute [to_additive add_con.to_setoid] con.to_setoid
variables {M}
namespace con



@[to_additive]
instance : has_coe_to_fun (con M) := ⟨_, λ c, λ m n, c.r m n⟩

@[simp, refl, to_additive] lemma refl (c : con M) (x) : c.1 x x := c.2.1 x
@[simp, symm, to_additive] lemma symm (c : con M) : ∀ {x y}, c x y → c.1 y x := λ _ _ h, c.2.2.1 h
@[simp, trans, to_additive] lemma trans (c : con M) : ∀ {x y z}, c x y → c y z → c.1 x z := 
λ  _ _ _ hx hy, c.2.2.2 hx hy
@[simp, to_additive] lemma mul (c : con M) : ∀ {w x y z}, c w x → c y z → c (w*y) (x*z) :=
λ _ _ _ _ h1 h2, c.3 h1 h2

instance : has_mem (M × M) (con M) := ⟨λ x r, x ∈ r.to_setoid.to_set⟩
lemma mem_def (r : con M) {x y} : (x, y) ∈ r ↔ (x, y) ∈ r.to_setoid.to_set := iff.rfl
lemma mem_rel (r : con M) {x y} : (x, y) ∈ r ↔ r.to_setoid.r' x y := iff.rfl
/-- Two congruence relations are equal if their underlying functions are equal. -/
@[to_additive] lemma r_inj {c d : con M} (H : c.r = d.r) : c = d :=
by cases c; cases d; simp * at *
run_cmd tactic.add_doc_string `add_con.r_inj'
  "Two congruence relations are equal if their underlying functions are equal."

/-- Two congruence relations are equal if their underlying functions are equal for all arguments. -/
@[extensionality, to_additive] lemma ext {c d : con M} (H : ∀ x y, c x y ↔ d x y) :
  c = d := r_inj $ by ext x y; exact H x y
run_cmd tactic.add_doc_string `add_con.ext'
  "Two congruence relations are equal if their underlying functions are equal."
    
/-- Two congruence relations are equal iff their underlying functions are equal for all arguments. -/
@[to_additive] lemma ext_iff {c d : con M} : (∀ x y, c x y ↔ d x y) ↔ c = d :=
⟨λ h, ext h, λ h x y, h ▸ iff.rfl⟩
run_cmd tactic.add_doc_string `add_con.ext_iff'
  "Two congruence relations are equal iff their underlying functions are equal."
    
variables (M)

/-- The submonoid of M × M defined by a congruence relation on a monoid M. -/
@[to_additive add_con.add_submonoid] protected def submonoid (c : con M) : submonoid (M × M) :=
{ carrier := { x | c x.1 x.2 },
  one_mem' := c.iseqv.1 1,
  mul_mem' := λ _ _ hx hy, c.mul hx hy }
run_cmd tactic.add_doc_string `add_submonoid.add_submonoid'
  "The submonoid of M × M defined by a congruence relation on an additive monoid M."

def diag : con M :=
{ mul' := λ _ _ _ _ h1 h2, h1 ▸ h2 ▸ rfl, ..setoid.diag M }

variables {M}

/-- Makes a congruence relation on a monoid M from a submonoid of M × M which is 
    also an equivalence relation. -/
@[to_additive of_add_submonoid] 
def of_submonoid (N : submonoid (M × M)) (H : equivalence (λ x y, (x, y) ∈ N)) : con M :=
{ r := λ x y, (x, y) ∈ N,
  iseqv := H,
  mul' := λ _ _ _ _ h1 h2, N.mul_mem h1 h2 }
run_cmd tactic.add_doc_string `add_con.of_add_submonoid'
  "Makes a congruence relation on an additive monoid M from a submonoid of M × M which is also an equivalence relation."

/-- The kernel of a monoid homomorphism as a congruence relation. -/
@[to_additive] def ker (f : M →* P) : con M :=
{ r := λ x y, f x = f y,
  iseqv := ⟨λ _, rfl, λ _ _ h, h.symm, λ _ _ _ hx hy, eq.trans hx hy⟩,
  mul' := λ _ _ _ _ h1 h2, by rw [f.map_mul, h1, h2, f.map_mul] }
run_cmd tactic.add_doc_string `add_con.ker'
  "Two congruence relations are equal if their underlying functions are equal."

end con

namespace monoid_hom

theorem injective_iff_ker_diag (f : M →* P) :
  function.injective f ↔ con.ker f = con.diag M :=
⟨λ hf, con.ext $ λ x y, ⟨λ h, hf h, λ h, h ▸ rfl⟩,
 λ hf x y h, show con.diag M x y, by rw ←hf; exact h⟩

theorem ker_eq_ker' {G} {H} [group G] [group H] (f : G →* H) {x} :
  (∃ y, y ∈ con.ker f ∧ x = (y : G × G).1 * y.2⁻¹) ↔ f x = 1 :=
⟨λ ⟨y, hm, hxy⟩, by
  rw [hxy, f.map_mul, f.map_inv, show f y.1 = f y.2, from hm, mul_right_inv],
 λ hx, ⟨(x,1), show f x = f 1, from f.map_one.symm ▸ hx, by simp only [mul_one, one_inv]⟩⟩

end monoid_hom

namespace con

variables {M}

protected def prod (c : con M) (d : con N) : con (M × N) :=
{ r := λ x y, c x.1 y.1 ∧ d x.2 y.2,
  iseqv := ⟨λ x, ⟨c.refl x.1, d.refl x.2⟩, λ _ _ h, ⟨c.symm h.1, d.symm h.2⟩,
            λ _ _ _ h1 h2, ⟨c.trans h1.1 h2.1, d.trans h1.2 h2.2⟩⟩,
  mul' := λ _ _ _ _ h1 h2, ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩ }

def pi {ι : Type*} {f : ι → Type*} [Π i, monoid (f i)] 
  (C : Π i, con (f i)) : con (Π i, f i) :=
{ r := λ x y, ∀ i, (C i) (x i) (y i),
  iseqv := ⟨λ x i, (C i).refl (x i), λ _ _ h i, (C i).symm (h i),
              λ _ _ _ h1 h2 i, (C i).trans (h1 i) (h2 i)⟩,
  mul' := λ _ _ _ _ h1 h2 i, (C i).mul (h1 i) (h2 i) }

lemma ker_rel (f : M →* P) {x y} : con.ker f x y ↔ f x = f y := iff.rfl

variable (c : con M)

def subtype (A : submonoid M) : con A :=
⟨λ x y, c x y, ⟨λ x, c.refl x, λ x y h, c.symm h, λ x y z h1 h2, c.trans h1 h2⟩,
 λ w x y z h1 h2, c.mul h1 h2⟩

@[simp] lemma subtype_apply {A : submonoid M} {x y} : c.subtype A x y ↔ c x y := iff.rfl

@[simp] lemma setoid_eq : c.to_setoid.r = c := rfl

protected def quotient := quotient $ c.to_setoid

instance : has_coe M (c.quotient) := ⟨@quotient.mk _ c.to_setoid⟩

instance [d : ∀ a b, decidable (c a b)] : decidable_eq c.quotient :=
@quotient.decidable_eq M c.to_setoid d

@[elab_as_eliminator, reducible]
protected def lift_on' {β} {c : con M} (q : c.quotient) (f : M → β)
  (h : ∀ a b, c a b → f a = f b) : β := quotient.lift_on' q f h

@[elab_as_eliminator, reducible]
protected def lift_on₂' {β} {c : con M} {d : con N} (q₁ : c.quotient) (q₂ : d.quotient)
  (f : M → N → β) (h : ∀ a₁ a₂ b₁ b₂, c a₁ b₁ → d a₂ b₂ → f a₁ a₂ = f b₁ b₂) : β :=
quotient.lift_on₂' q₁ q₂ f h

variables {c}

@[elab_as_eliminator]
lemma ind {C : c.quotient → Prop} (H : ∀ x : M, C x) : ∀ q, C q :=
quotient.ind' H

@[elab_as_eliminator]
lemma ind₂ {d : con N} {C : c.quotient → d.quotient → Prop}
  (H : ∀ (x : M) (y : N), C x y) : ∀ p q, C p q :=
quotient.ind₂' H

@[elab_as_eliminator]
lemma induction_on {C : c.quotient → Prop} (q : c.quotient) (H : ∀ x : M, C x) : C q :=
quotient.induction_on' q H

@[elab_as_eliminator]
lemma induction_on₂ {d : con N} {C : c.quotient → d.quotient → Prop}
  (p : c.quotient) (q : d.quotient) (H : ∀ (x : M) (y : N), C x y) : C p q :=
quotient.induction_on₂' p q H

instance : inhabited c.quotient := ⟨((1 : M) : c.quotient)⟩

variables (c)

@[simp] protected lemma eq (a b : M) : (a : c.quotient) = b ↔ c a b :=
quotient.eq'

instance monoid : monoid c.quotient :=
{ one := ((1 : M) : c.quotient),
  mul := λ x y, quotient.lift_on₂' x y (λ w z, (((w*z) : M) : c.quotient))
         $ λ _ _ _ _ h1 h2, (c.eq _ _).2 $ c.mul h1 h2,
  mul_assoc := λ x y z, quotient.induction_on₃' x y z
               $ λ _ _ _, congr_arg coe $ mul_assoc _ _ _,
  mul_one := λ x, quotient.induction_on' x $ λ _, congr_arg coe $ mul_one _,
  one_mul := λ x, quotient.induction_on' x $ λ _, congr_arg coe $ one_mul _ }

def mk' : M →* c.quotient := ⟨coe, rfl, λ _ _, rfl⟩

variables (x y : M)

@[simp] lemma mk'_ker : con.ker c.mk' = c := ext $ λ _ _, c.eq _ _

lemma mk'_surjective : function.surjective c.mk' :=
by apply ind; exact λ x, ⟨x, rfl⟩

@[simp] lemma mk'_one : c.mk' 1 = 1 := rfl
@[simp] lemma mk'_mul : c.mk' (x * y) = c.mk' x * c.mk' y := rfl
@[simp] lemma mk'_pow : ∀ n : ℕ, c.mk' (x ^ n) = (c.mk' x) ^ n
| 0 := c.mk'.map_one
| (m + 1) := by rw [pow_succ, c.mk'.map_mul, mk'_pow m]; refl
@[simp] lemma comp_mk'_apply (g : c.quotient →* P) {x} : g.comp c.mk' x = g x := rfl

@[simp] lemma coe_one : ((1 : M) : c.quotient) = 1 := rfl
@[simp] lemma coe_mul : (x : c.quotient) * (y : c.quotient) = ((x * y : M) : c.quotient)  := rfl
lemma coe_pow : ∀ n : ℕ, (x ^ n : c.quotient) = (x : c.quotient) ^ n
| 0            := pow_zero _
| (nat.succ n) := by rw pow_succ _

@[simp] lemma lift_on_beta {β} (c : con M) (f : M → β)
  (h : ∀ a b, c a b → f a = f b) (x : M) :
con.lift_on' (x : c.quotient) f h = f x := rfl

variable {f : M →* P}

lemma ker_apply_eq_preimage (m) : (con.ker f) m = f ⁻¹' {f m} :=
set.ext $ λ x,
  ⟨λ h, set.mem_preimage.2 (set.mem_singleton_iff.2 h.symm),
   λ h, (set.mem_singleton_iff.1 (set.mem_preimage.1 h)).symm⟩

protected def congr {c d : con M} (h : c = d) :  c.quotient ≃* d.quotient :=
{ map_mul' := λ x y, by rcases x; rcases y; refl,
  ..quotient.congr (equiv.refl M) $ by apply ext_iff.2 h }

open lattice
end con
namespace setoid


--instance con.to_submonoid : has_coe (con M) (submonoid (M × M)) := ⟨λ c, c.submonoid M⟩

--lemma con.le_def' {c d : con M} : c ≤ d ↔ (c : submonoid (M × M)) ≤ d := iff.rfl

--instance : has_mem (M × M) (con M) := ⟨λ x c, x ∈ (↑c : set (M × M))⟩

--@[simp] lemma mem_coe {c : con M} {x y} :
--  (x, y) ∈ (↑c : submonoid (M × M)) ↔ (x, y) ∈ c := iff.rfl

theorem to_set_inj {r s : setoid M} (H : r.to_set = s.to_set) : r = s :=
ext' $ λ x y, by rw [←mem_rel, ←mem_rel, mem_def, H]; refl

--theorem to_submonoid_inj (c d : con M) (H : (c : submonoid (M × M)) = d) : c = d :=
--ext $ λ x y, show (x,y) ∈ (c : submonoid (M × M)) ↔ (x,y) ∈ ↑d, by rw H
open lattice

instance : partial_order (setoid M) :=
{ le := (≤),
  lt := λ r s, r ≤ s ∧ ¬s ≤ r,
  le_refl := λ r x y h, h,
  le_trans := λ _ _ _ hr hs x y h, hs x y $ hr x y h,
  lt_iff_le_not_le := λ _ _, iff.rfl,
  le_antisymm := λ r s h1 h2, setoid.ext' $ λ x y, ⟨h1 x y, h2 x y⟩ }

instance : has_bot (setoid M) := ⟨diag M⟩

instance : order_bot (setoid M) :=
{ bot := has_bot.bot (setoid M),
  bot_le := λ r, (le_def _ _).2 $ λ x y h, h ▸ r.2.1 x, ..setoid.partial_order }

instance : has_top (setoid M) := ⟨setoid.top M⟩

instance : order_top (setoid M) :=
{ top := has_top.top (setoid M),
  le_top := λ r, (le_def _ _).2 $ λ x y h, trivial,
  ..setoid.partial_order }

instance : has_inf (setoid M) :=
⟨λ r s, ⟨λ x y, r.r' x y ∧ s.r' x y, ⟨λ x, ⟨r.refl' x, s.refl' x⟩, 
 λ x y h, ⟨r.symm' h.1, s.symm' h.2⟩, 
 λ _ _ _ h1 h2, ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩⟩

instance : has_Inf (setoid M) :=
⟨λ S, ⟨λ x y, (∀ r ∈ S, r' r x y), 
⟨λ x r hr, r.refl' x, λ x y h r hr, r.symm' $ h r hr, 
 λ _ _ _ h1 h2 r hr, r.trans' (h1 r hr) $ h2 r hr⟩⟩⟩

lemma Inf_le' (S : set (setoid M)) (r∈S) : Inf S ≤ r :=
(le_def _ _).2 $ λ _ _ h, h r H

lemma le_Inf' (S : set (setoid (M))) (r) : (∀ s∈S, r ≤ s) → r ≤ Inf S :=
λ H, (le_def _ _).2 $ λ x y h s hs, (le_def _ _).1 (H s hs) x y h

instance : has_sup (setoid M) := ⟨λ r s, Inf { x | r ≤ x ∧ s ≤ x}⟩

instance : complete_lattice (setoid M) :=
{ sup := has_sup.sup,
  le_sup_left := λ r s, le_Inf' _ r $ λ _ hx, hx.1,
  le_sup_right := λ r s, le_Inf' _ s $ λ _ hx, hx.2,
  sup_le := λ r s t h1 h2, Inf_le' _ t ⟨h1, h2⟩,
  inf := has_inf.inf,
  inf_le_left := λ _ _ _ _ h, h.1,
  inf_le_right := λ _ _ _ _ h, h.2,
  le_inf := λ _ _ _ h1 h2 x y h, ⟨h1 x y h, h2 x y h⟩,
  Sup := λ tt, Inf {t | ∀ t'∈tt, t' ≤ t},
  Inf := has_Inf.Inf,
  le_Sup := λ _ _ hs, le_Inf' _ _ $ λ r hr, hr _ hs,
  Sup_le := λ _ _ hs, Inf_le' _ _ hs,
  Inf_le := Inf_le',
  le_Inf := le_Inf',
  ..setoid.partial_order,
  ..setoid.lattice.order_top, ..setoid.lattice.order_bot}

end setoid 

namespace con
open lattice 

instance : has_le (con M) := ⟨λ c d, c.to_setoid ≤ d.to_setoid⟩

instance : partial_order (con M) :=
{ le := (≤),
  lt := λ c d, c ≤ d ∧ ¬d ≤ c,
  le_refl := λ c x y h, h,
  le_trans := λ c1 c2 c3 h1 h2 x y h, h2 x y $ h1 x y h,
  lt_iff_le_not_le := λ _ _, iff.rfl,
  le_antisymm := λ c d hc hd, ext $ λ x y, ⟨hc x y, hd x y⟩}

instance : order_top (con M) :=
{ top := { mul' := λ _ _ _ _ h1 h2, trivial, ..setoid.lattice.complete_lattice.top},
  le_top := λ c x y h, trivial,
  ..con.partial_order}

instance : order_bot (con M) :=
{ bot := diag M,
  bot_le := λ c x y h, h ▸ c.refl x,
  ..con.partial_order}

instance : has_Inf (con M) :=
⟨λ S, ⟨λ x y, (∀ c : con M, c ∈ S → c x y), 
⟨λ x c hc, c.refl x, λ x y h c hc, c.symm $ h c hc, 
 λ _ _ _ h1 h2 c hc, c.trans (h1 c hc) $ h2 c hc⟩,
 λ _ _ _ _ h1 h2 c hc, c.mul (h1 c hc) $ h2 c hc⟩⟩

lemma Inf_eq (S : set (con M)) : (Inf S).to_setoid = Inf (to_setoid '' S) := sorry 

instance : has_inf (con M) :=
⟨λ c d, ⟨(c.to_setoid ⊓ d.to_setoid).1, (c.to_setoid ⊓ d.to_setoid).2, 
λ _ _ _ _ h1 h2, ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩⟩⟩

/-
instance : has_inf (con M) :=
⟨λ c d, ⟨λ x y, c x y ∧ d x y, 
⟨λ x, ⟨c.refl x, d.refl x⟩, λ _ _ h, ⟨c.symm h.1, d.symm h.2⟩, 
 λ _ _ _ h1 h2, ⟨c.trans h1.1 h2.1, d.trans h1.2 h2.2⟩⟩, 
 λ _ _ _ _ h1 h2, ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩⟩⟩-/

instance : has_sup (con M) := ⟨λ c d, Inf { x | c ≤ x ∧ d ≤ x}⟩ 
 
instance : complete_lattice (con M) :=
{ sup := has_sup.sup,
  le_sup_left := sorry ,
  le_sup_right := sorry,
  sup_le := sorry,
  inf := has_inf.inf,
  inf_le_left := sorry,
  inf_le_right := sorry,
  le_inf := sorry,
  Sup := λ tt, Inf {t | ∀t'∈tt, t' ≤ t},
  Inf := has_Inf.Inf,
  le_Sup := sorry,
  Sup_le := sorry,
  Inf_le := sorry,
  le_Inf := sorry,
  ..con.partial_order,
  ..con.lattice.order_top, ..con.lattice.order_bot }

variables (c : con M) (f : M →* P)

def lift (H : ∀ x y, c x y → f x = f y) : c.quotient →* P :=
{ to_fun := λ x, con.lift_on' x f $ λ a b h, H a b h,
  map_one' := by rw ←f.map_one; refl,
  map_mul' := λ x y, con.induction_on₂ x y $
                λ m n, by simp only [f.map_mul, con.lift_on_beta, con.coe_mul]}

def ker_lift (f : M →* P) : (con.ker f).quotient →* P :=
(con.ker f).lift f $ λ x y h, h

variables {c f}

@[simp] lemma lift_mk' (H : ∀ x y, c x y → f x = f y) (m) :
  c.lift f H (c.mk' m) = f m := rfl

@[simp] lemma lift_coe (H : ∀ x y, c x y → f x = f y) (m : M) :
  c.lift f H m = f m := rfl

@[simp] theorem lift_comp_mk' (H : ∀ x y, c x y → f x = f y) :
  (c.lift f H).comp c.mk' = f := by ext; refl

@[simp] lemma lift_apply_mk' (f : c.quotient →* P) :
  c.lift (f.comp c.mk') (λ x y h, by simp [(c.eq _ _).2 h]) = f :=
by ext; rcases x; refl

lemma lift_funext (f g : c.quotient →* P) (h : ∀ a : M, f a = g a) : f = g :=
by { rw [←lift_apply_mk' f, ← lift_apply_mk' g], congr' 1, ext, apply h x }

theorem lift_unique (H : ∀ x y, c x y → f x = f y) (g : c.quotient →* P)
  (Hg : g.comp c.mk' = f) : g = c.lift f H :=
lift_funext g (c.lift f H) $ λ x, by rw [lift_coe H, ←con.comp_mk'_apply, Hg]

theorem lift_range (H : ∀ x y, c x y → f x = f y) : (c.lift f H).range = f.range :=
submonoid.ext $ λ x,
  ⟨λ ⟨y, hy⟩, by revert hy; rcases y; exact
     (λ hy, ⟨y, hy.1, by rw [hy.2.symm, (lift_coe H _).symm]; refl⟩),
   λ ⟨y, hy⟩, ⟨↑y, hy.1, by rw ←hy.2; refl⟩⟩

@[simp] lemma ker_lift_mk {x : M} :  ker_lift f x = f x := rfl

lemma ker_lift_range_eq : (ker_lift f).range = f.range :=
lift_range $ λ x y h, h

lemma injective_ker_lift (f : M →* P) : function.injective (ker_lift f) :=
λ x y, con.induction_on₂ x y $ λ _ _ h, ((con.ker f).eq _ _).2 $ by rwa ker_lift_mk at h

def map (c d : con M) (h : c ≤ d) : c.quotient →* d.quotient :=
c.lift d.mk' $ λ x y hc, show (con.ker d.mk') x y, from
  (mk'_ker d).symm ▸ (h x y hc)

@[simp] lemma map_apply {c d : con M} (h : c ≤ d) (x) :
  c.map d h x = c.lift d.mk' (λ x y hc, (d.eq x y).2 $ h x y hc) x := rfl

variables (c)

lemma rel {x y} (h : @setoid.r M c.to_setoid x y) : c x y := h

def to_con (d : {d // c ≤ d}) : con c.quotient :=
{ r := λ x y, con.lift_on₂' x y d.1 $ λ p q r s hp hq, iff_iff_eq.1
         ⟨λ h', d.1.trans (d.1.symm (d.2 p r $ rel c hp)) $ d.1.trans h' (d.2 q s $ rel c hq),
          λ h', d.1.trans (d.2 p r $ rel c hp) (d.1.trans h' $ d.1.symm (d.2 q s $ rel c hq))⟩,
  iseqv := ⟨λ x, quotient.induction_on' x $ λ y, d.1.refl y,
              λ x y, quotient.induction_on₂' x y $ λ _ _ h', d.1.symm h',
              λ x y z, quotient.induction_on₃' x y z $ λ _ _ _ h1 h2, d.1.trans h1 h2⟩,
  mul' := λ w x y z, quotient.induction_on₂' w x $
             λ _ _, quotient.induction_on₂' y z $ λ _ _ h1 h2, d.1.mul h1 h2 }

def of_con (d : con c.quotient) : con M :=
{ r := λ x y, d ↑x ↑y,
  iseqv := ⟨λ x, d.refl ↑x, λ _ _ h, d.symm h, λ _ _ _ h1 h2, d.trans h1 h2⟩,
  mul' := by intros; rw [←coe_mul, ←coe_mul]; exact d.mul a a_1 }

lemma le_of_con (d : con c.quotient) : c ≤ c.of_con d :=
λ x y h, show d x y, from ((c.eq _ _).2 h) ▸ d.refl x

theorem left_inverse (d : {d // c ≤ d}) : c.of_con (c.to_con d) = d.1 :=
by ext; refl

theorem right_inverse (d : con c.quotient) : c.to_con ⟨(c.of_con d), (c.le_of_con d)⟩ = d :=
by ext; rcases x; rcases y; refl

variables {f c}

lemma ker_eq_of_equiv (h : c.quotient ≃* P) (f : M →* P) (H : ∀ x y, c x y → f x = f y) 
  (hh : h.to_monoid_hom = c.lift f H) : con.ker f = c :=
le_antisymm (λ x y hk, by change f x = f y at hk;
    rw [←lift_coe H, ←lift_coe H, ←hh] at hk;
    exact (c.eq _ _).1 (h.to_equiv.injective hk)) $
  λ _ _ h, H _ _ h
 
variables (c)

noncomputable def quotient_ker_equiv_range (f : M →* P) : (con.ker f).quotient ≃* f.range :=
{ map_mul' := monoid_hom.map_mul _,
  ..@equiv.of_bijective _ _
      ((@mul_equiv.to_monoid_hom (ker_lift f).range _ _ _ 
        (mul_equiv.submonoid_congr ker_lift_range_eq)).comp (ker_lift f).range_mk) $
      function.bijective_comp (equiv.bijective _)
        ⟨λ x y h, injective_ker_lift f $ by rcases x; rcases y; injections, 
         λ ⟨w, z, hzm, hz⟩, ⟨z, by rcases hz; rcases _x; refl⟩⟩ }

lemma lift_surjective_of_surjective (hf : function.surjective f) : function.surjective (ker_lift f) :=
λ y, exists.elim (hf y) $ λ w hw, ⟨w, hw⟩

noncomputable def quotient_ker_equiv_of_surjective (f : M →* P) (hf : function.surjective f) :
  (con.ker f).quotient ≃* P :=
{ map_mul' := monoid_hom.map_mul _,
  ..(@equiv.of_bijective _ _ (ker_lift f) ⟨injective_ker_lift f, lift_surjective_of_surjective hf⟩) }

lemma subtype_eq (A : submonoid M) : c.subtype A = con.ker (c.mk'.comp A.subtype) :=
con.ext $ λ x y,
  ⟨λ h, show ((x : M) : c.quotient) = (y : M), from (c.eq _ _).2 $ c.subtype_apply.2 h,
   λ h, by rw [subtype_apply, ←mk'_ker c]; simpa using h⟩

noncomputable def submonoid_quotient_equiv (A : submonoid M) :
  (c.subtype A).quotient ≃* (c.mk'.comp A.subtype).range :=
mul_equiv.trans (con.congr $ subtype_eq c A) $ quotient_ker_equiv_range (c.mk'.comp A.subtype)

lemma surjective_of_con_lift (d : con M) (h : c ≤ d) : function.surjective (c.map d h) :=
λ x, by rcases x; exact ⟨x, rfl⟩

noncomputable def quotient_quotient_equiv_quotient (c d : con M) (h : c ≤ d) :
  (con.ker (c.map d h)).quotient ≃* d.quotient :=
quotient_ker_equiv_of_surjective _ $ surjective_of_con_lift c d h

def correspondence : ((≤) : {d // c ≤ d} → {d // c ≤ d} → Prop) ≃o
((≤) : con c.quotient → con c.quotient → Prop) :=
{ to_fun := λ d, c.to_con d,
  inv_fun := λ d, subtype.mk (c.of_con d) (c.le_of_con d),
  left_inv := λ d, by simp [c.left_inverse d],
  right_inv := λ d, by simp [c.right_inverse d],
  ord := λ a b,
    ⟨λ hle x y, con.induction_on₂ x y $
       λ w z h, by apply hle w z h,
     λ H p q h, by apply H (p : _) (q : _) h⟩ }

end con

def setoid.to_con (r : setoid M) := lattice.Inf {c : con M | r ≤ c.to_setoid}

lemma con.left_inv (c : con M) : c.to_setoid.to_con = c :=
begin
apply le_antisymm,
sorry, sorry,
end 

#exit
def con.gi : @galois_insertion (setoid M) (con M) _ _ setoid.to_con con.to_setoid :=
{ choice := λ r h, setoid.to_con r,
  gc := λ r s, by {split, intros h x y hr,
  have : s x y := h x y (setoid.le_Inf' (con.to_setoid '' {c : con M | r ≤ c.to_setoid}) r 
  (λ s ⟨c, hm, hc⟩, hc ▸ hm) x y hr),
  intros h x y hr, },
  le_l_u := _,
  choice_eq := _ }
