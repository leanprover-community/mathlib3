/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import logic.relator

/-!
# Quotients -- extends the core library
-/

variables {α : Sort*} {β : Sort*}

namespace setoid

lemma ext {α : Sort*} :
  ∀{s t : setoid α}, (∀a b, @setoid.r α s a b ↔ @setoid.r α t a b) → s = t
| ⟨r, _⟩ ⟨p, _⟩ eq :=
  have r = p, from funext $ assume a, funext $ assume b, propext $ eq a b,
  by subst this

end setoid

namespace quot
variables {ra : α → α → Prop} {rb : β → β → Prop} {φ : quot ra → quot rb → Sort*}
local notation `⟦`:max a `⟧` := quot.mk _ a

instance [inhabited α] : inhabited (quot ra) := ⟨⟦default _⟧⟩

protected def hrec_on₂ (qa : quot ra) (qb : quot rb) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
  (ca : ∀ {b a₁ a₂}, ra a₁ a₂ → f a₁ b == f a₂ b)
  (cb : ∀ {a b₁ b₂}, rb b₁ b₂ → f a b₁ == f a b₂) : φ qa qb :=
quot.hrec_on qa (λ a, quot.hrec_on qb (f a) (λ b₁ b₂ pb, cb pb)) $ λ a₁ a₂ pa,
  quot.induction_on qb $ λ b,
    calc @quot.hrec_on _ _ (φ _) ⟦b⟧ (f a₁) (@cb _)
          == f a₁ b                                     : by simp
      ... == f a₂ b                                     : ca pa
      ... == @quot.hrec_on _ _ (φ _) ⟦b⟧ (f a₂) (@cb _) : by simp

/-- Map a function `f : α → β` such that `ra x y` implies `rb (f x) (f y)`
to a map `quot ra → quot rb`. -/
protected def map (f : α → β) (h : (ra ⇒ rb) f f) : quot ra → quot rb :=
quot.lift (λ x, ⟦f x⟧) $ assume x y (h₁ : ra x y), quot.sound $ h h₁

/-- If `ra` is a subrelation of `ra'`, then we have a natural map `quot ra → quot ra'`. -/
protected def map_right {ra' : α → α → Prop} (h : ∀a₁ a₂, ra a₁ a₂ → ra' a₁ a₂) :
  quot ra → quot ra' :=
quot.map id h

end quot

namespace quotient
variables [sa : setoid α] [sb : setoid β]
variables {φ : quotient sa → quotient sb → Sort*}

instance [inhabited α] : inhabited (quotient sa) := ⟨⟦default _⟧⟩

protected def hrec_on₂ (qa : quotient sa) (qb : quotient sb) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
  (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ == f a₂ b₂) : φ qa qb :=
quot.hrec_on₂ qa qb f
  (λ _ _ _ p, c _ _ _ _ p (setoid.refl _))
  (λ _ _ _ p, c _ _ _ _ (setoid.refl _) p)

/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `quotient sa → quotient sb`. Useful to define unary operations on quotients. -/
protected def map (f : α → β) (h : ((≈) ⇒ (≈)) f f) : quotient sa → quotient sb :=
quot.map f @h

variables {γ : Sort*} [sc : setoid γ]

/-- Map a function `f : α → β → γ` that sends equivalent elements to equivalent elements
to a function `f : quotient sa → quotient sb → quotient sc`.
Useful to define binary operations on quotients. -/
protected def map₂ (f : α → β → γ) (h : ((≈) ⇒ (≈) ⇒ (≈)) f f) :
  quotient sa → quotient sb → quotient sc :=
quotient.lift₂ (λ x y, ⟦f x y⟧) (λ x₁ y₁ x₂ y₂ h₁ h₂, quot.sound $ h h₁ h₂)

/-- A version of `quotient.map₂` using curly braces and unification. -/
protected def map₂' {α : Sort*} {β : Sort*} {γ : Sort*}
  {sa : setoid α} {sb : setoid β} {sc : setoid γ}
  (f : α → β → γ) (h : ((≈) ⇒ (≈) ⇒ (≈)) f f) :
  quotient sa → quotient sb → quotient sc :=
quotient.map₂ f h

end quotient

@[simp] theorem quotient.eq [r : setoid α] {x y : α} : ⟦x⟧ = ⟦y⟧ ↔ x ≈ y :=
⟨quotient.exact, quotient.sound⟩

theorem forall_quotient_iff {α : Type*} [r : setoid α] {p : quotient r → Prop} :
  (∀a:quotient r, p a) ↔ (∀a:α, p ⟦a⟧) :=
⟨assume h x, h _, assume h a, a.induction_on h⟩

@[simp] lemma quotient.lift_beta [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b)
  (x : α) :
  quotient.lift f h (quotient.mk x) = f x := rfl

@[simp] lemma quotient.lift_on_beta [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b)
  (x : α) :
  quotient.lift_on (quotient.mk x) f h = f x := rfl

/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
noncomputable def quot.out {r : α → α → Prop} (q : quot r) : α :=
classical.some (quot.exists_rep q)

/-- Unwrap the VM representation of a quotient to obtain an element of the equivalence class.
  Computable but unsound. -/
meta def quot.unquot {r : α → α → Prop} : quot r → α := unchecked_cast

@[simp] theorem quot.out_eq {r : α → α → Prop} (q : quot r) : quot.mk r q.out = q :=
classical.some_spec (quot.exists_rep q)

/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
noncomputable def quotient.out [s : setoid α] : quotient s → α := quot.out

@[simp] theorem quotient.out_eq [s : setoid α] (q : quotient s) : ⟦q.out⟧ = q := q.out_eq

theorem quotient.mk_out [s : setoid α] (a : α) : ⟦a⟧.out ≈ a :=
quotient.exact (quotient.out_eq _)

instance pi_setoid {ι : Sort*} {α : ι → Sort*} [∀ i, setoid (α i)] : setoid (Π i, α i) :=
{ r := λ a b, ∀ i, a i ≈ b i,
  iseqv := ⟨
    λ a i, setoid.refl _,
    λ a b h i, setoid.symm (h _),
    λ a b c h₁ h₂ i, setoid.trans (h₁ _) (h₂ _)⟩ }

noncomputable def quotient.choice {ι : Type*} {α : ι → Type*} [S : ∀ i, setoid (α i)]
  (f : ∀ i, quotient (S i)) : @quotient (Π i, α i) (by apply_instance) :=
⟦λ i, (f i).out⟧

theorem quotient.choice_eq {ι : Type*} {α : ι → Type*} [∀ i, setoid (α i)]
  (f : ∀ i, α i) : quotient.choice (λ i, ⟦f i⟧) = ⟦f⟧ :=
quotient.sound $ λ i, quotient.mk_out _

lemma nonempty_quotient_iff (s : setoid α) : nonempty (quotient s) ↔ nonempty α :=
⟨assume ⟨a⟩, quotient.induction_on a nonempty.intro, assume ⟨a⟩, ⟨⟦a⟧⟩⟩

/-- `trunc α` is the quotient of `α` by the always-true relation. This
  is related to the propositional truncation in HoTT, and is similar
  in effect to `nonempty α`, but unlike `nonempty α`, `trunc α` is data,
  so the VM representation is the same as `α`, and so this can be used to
  maintain computability. -/
def {u} trunc (α : Sort u) : Sort u := @quot α (λ _ _, true)

theorem true_equivalence : @equivalence α (λ _ _, true) :=
⟨λ _, trivial, λ _ _ _, trivial, λ _ _ _ _ _, trivial⟩

namespace trunc

/-- Constructor for `trunc α` -/
def mk (a : α) : trunc α := quot.mk _ a

instance [inhabited α] : inhabited (trunc α) := ⟨mk (default _)⟩

/-- Any constant function lifts to a function out of the truncation -/
def lift (f : α → β) (c : ∀ a b : α, f a = f b) : trunc α → β :=
quot.lift f (λ a b _, c a b)

theorem ind {β : trunc α → Prop} : (∀ a : α, β (mk a)) → ∀ q : trunc α, β q := quot.ind

protected theorem lift_beta (f : α → β) (c) (a : α) : lift f c (mk a) = f a := rfl

@[reducible, elab_as_eliminator]
protected def lift_on (q : trunc α) (f : α → β)
  (c : ∀ a b : α, f a = f b) : β := lift f c q

@[elab_as_eliminator]
protected theorem induction_on {β : trunc α → Prop} (q : trunc α)
  (h : ∀ a, β (mk a)) : β q := ind h q

theorem exists_rep (q : trunc α) : ∃ a : α, mk a = q := quot.exists_rep q

attribute [elab_as_eliminator]
protected theorem induction_on₂ {C : trunc α → trunc β → Prop} (q₁ : trunc α) (q₂ : trunc β)
  (h : ∀ a b, C (mk a) (mk b)) : C q₁ q₂ :=
trunc.induction_on q₁ $ λ a₁, trunc.induction_on q₂ (h a₁)

protected theorem eq (a b : trunc α) : a = b :=
trunc.induction_on₂ a b (λ x y, quot.sound trivial)

instance : subsingleton (trunc α) := ⟨trunc.eq⟩

def bind (q : trunc α) (f : α → trunc β) : trunc β :=
trunc.lift_on q f (λ a b, trunc.eq _ _)

def map (f : α → β) (q : trunc α) : trunc β := bind q (trunc.mk ∘ f)

instance : monad trunc :=
{ pure := @trunc.mk,
  bind := @trunc.bind }

instance : is_lawful_monad trunc :=
{ id_map := λ α q, trunc.eq _ _,
  pure_bind := λ α β q f, rfl,
  bind_assoc := λ α β γ x f g, trunc.eq _ _ }

variable {C : trunc α → Sort*}

@[reducible, elab_as_eliminator]
protected def rec
   (f : Π a, C (mk a)) (h : ∀ (a b : α), (eq.rec (f a) (trunc.eq (mk a) (mk b)) : C (mk b)) = f b)
   (q : trunc α) : C q :=
quot.rec f (λ a b _, h a b) q

@[reducible, elab_as_eliminator]
protected def rec_on (q : trunc α) (f : Π a, C (mk a))
  (h : ∀ (a b : α), (eq.rec (f a) (trunc.eq (mk a) (mk b)) : C (mk b)) = f b) : C q :=
trunc.rec f h q

@[reducible, elab_as_eliminator]
protected def rec_on_subsingleton
   [∀ a, subsingleton (C (mk a))] (q : trunc α) (f : Π a, C (mk a)) : C q :=
trunc.rec f (λ a b, subsingleton.elim _ (f b)) q

/-- Noncomputably extract a representative of `trunc α` (using the axiom of choice). -/
noncomputable def out : trunc α → α := quot.out

@[simp] theorem out_eq (q : trunc α) : mk q.out = q := trunc.eq _ _

end trunc

theorem nonempty_of_trunc (q : trunc α) : nonempty α :=
let ⟨a, _⟩ := q.exists_rep in ⟨a⟩

namespace quotient
variables {γ : Sort*} {φ : Sort*}
  {s₁ : setoid α} {s₂ : setoid β} {s₃ : setoid γ}

/- Versions of quotient definitions and lemmas ending in `'` use unification instead
of typeclass inference for inferring the `setoid` argument. This is useful when there are
several different quotient relations on a type, for example quotient groups, rings and modules -/

protected def mk' (a : α) : quotient s₁ := quot.mk s₁.1 a

@[elab_as_eliminator, reducible]
protected def lift_on' (q : quotient s₁) (f : α → φ)
  (h : ∀ a b, @setoid.r α s₁ a b → f a = f b) : φ := quotient.lift_on q f h

@[elab_as_eliminator, reducible]
protected def lift_on₂' (q₁ : quotient s₁) (q₂ : quotient s₂) (f : α → β → γ)
  (h : ∀ a₁ a₂ b₁ b₂, @setoid.r α s₁ a₁ b₁ → @setoid.r β s₂ a₂ b₂ → f a₁ a₂ = f b₁ b₂) : γ :=
quotient.lift_on₂ q₁ q₂ f h

@[elab_as_eliminator]
protected lemma ind' {p : quotient s₁ → Prop}
  (h : ∀ a, p (quotient.mk' a)) (q : quotient s₁) : p q :=
quotient.ind h q

@[elab_as_eliminator]
protected lemma ind₂' {p : quotient s₁ → quotient s₂ → Prop}
  (h : ∀ a₁ a₂, p (quotient.mk' a₁) (quotient.mk' a₂))
  (q₁ : quotient s₁) (q₂ : quotient s₂) : p q₁ q₂ :=
quotient.ind₂ h q₁ q₂

@[elab_as_eliminator]
protected lemma induction_on' {p : quotient s₁ → Prop} (q : quotient s₁)
  (h : ∀ a, p (quotient.mk' a)) : p q := quotient.induction_on q h

@[elab_as_eliminator]
protected lemma induction_on₂' {p : quotient s₁ → quotient s₂ → Prop} (q₁ : quotient s₁)
  (q₂ : quotient s₂) (h : ∀ a₁ a₂, p (quotient.mk' a₁) (quotient.mk' a₂)) : p q₁ q₂ :=
quotient.induction_on₂ q₁ q₂ h

@[elab_as_eliminator]
protected lemma induction_on₃' {p : quotient s₁ → quotient s₂ → quotient s₃ → Prop}
  (q₁ : quotient s₁) (q₂ : quotient s₂) (q₃ : quotient s₃)
  (h : ∀ a₁ a₂ a₃, p (quotient.mk' a₁) (quotient.mk' a₂) (quotient.mk' a₃)) : p q₁ q₂ q₃ :=
quotient.induction_on₃ q₁ q₂ q₃ h

lemma exact' {a b : α} :
  (quotient.mk' a : quotient s₁) = quotient.mk' b → @setoid.r _ s₁ a b :=
quotient.exact

lemma sound' {a b : α} : @setoid.r _ s₁ a b → @quotient.mk' α s₁ a = quotient.mk' b :=
quotient.sound

@[simp]
protected lemma eq' {a b : α} : @quotient.mk' α s₁ a = quotient.mk' b ↔ @setoid.r _ s₁ a b :=
quotient.eq

noncomputable def out' (a : quotient s₁) : α := quotient.out a

@[simp] theorem out_eq' (q : quotient s₁) : quotient.mk' q.out' = q := q.out_eq

theorem mk_out' (a : α) : @setoid.r α s₁ (quotient.mk' a : quotient s₁).out' a :=
quotient.exact (quotient.out_eq _)
end quotient
