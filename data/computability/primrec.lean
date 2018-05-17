/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

The primitive recursive functions are the least collection of functions
nat -> nat which are closed under projections (using the mkpair
pairing function), composition, zero, successor, and primitive recursion
(i.e. nat.rec where the motive is C n := nat).

We can extend this definition to a large class of basic types by
using canonical encodings of types as natural numbers (Gödel numbering),
which we implement through the type class `encodable`. (More precisely,
we need that the composition of encode with decode yields a
primitive recursive function, so we have the `primcodable` type class
for this.)
-/
import data.denumerable tactic.basic

open denumerable encodable

local notation `-(` n `, ` m `)-` := nat.mkpair n m
local postfix `ₗ`:80 := λ n, (nat.unpair n).1
local postfix `ᵣ`:80 := λ n, (nat.unpair n).2

namespace nat

def elim {C : Sort*} : C → (ℕ → C → C) → ℕ → C := @nat.rec (λ _, C)

@[simp] theorem elim_zero {C} (a f) : @nat.elim C a f 0 = a := rfl
@[simp] theorem elim_succ {C} (a f n) :
  @nat.elim C a f (succ n) = f n (nat.elim a f n) := rfl

def cases {C : Sort*} (a : C) (f : ℕ → C) : ℕ → C := nat.elim a (λ n _, f n)

@[simp] theorem cases_zero {C} (a f) : @nat.cases C a f 0 = a := rfl
@[simp] theorem cases_succ {C} (a f n) : @nat.cases C a f (succ n) = f n := rfl

@[simp, reducible] def unpaired {α} (f : ℕ → ℕ → α) (n : ℕ) : α := f (n ₗ) (n ᵣ)

/-- The primitive recursive functions `ℕ → ℕ`. -/
inductive primrec : (ℕ → ℕ) → Prop
| zero : primrec (λ n, 0)
| succ : primrec succ
| left : primrec (λ n, n ₗ)
| right : primrec (λ n, n ᵣ)
| pair {f g} : primrec f → primrec g → primrec (λ n, -(f n, g n)-)
| comp {f g} : primrec f → primrec g → primrec (f ∘ g)
| prec {f g} : primrec f → primrec g → primrec (unpaired (λ z n,
   n.elim (f z) (λ y IH, g -(z, -(y, IH)-)-)))

namespace primrec

theorem of_eq {f g : ℕ → ℕ} (hg : primrec g) (H : ∀ n, f n = g n) : primrec f :=
(funext H : f = g).symm ▸ hg

theorem const : ∀ (n : ℕ), primrec (λ _, n)
| 0 := zero
| (n+1) := succ.comp (const n)

protected theorem id : primrec id :=
(left.pair right).of_eq $ λ n, by simp

theorem prec1 {f} (m : ℕ) (hf : primrec f) : primrec (λ n,
   n.elim m (λ y IH, f -(y, IH)-)) :=
((prec (const m) (hf.comp right)).comp 
  (zero.pair primrec.id)).of_eq $
λ n, by simp; dsimp; rw [unpair_mkpair]

theorem cases1 {f} (m : ℕ) (hf : primrec f) : primrec (nat.cases m f) :=
(prec1 m (hf.comp left)).of_eq $ by simp [cases]

theorem cases {f g} (hf : primrec f) (hg : primrec g) :
  primrec (unpaired (λ z n, n.cases (f z) (λ y, g -(z, y)-))) :=
(prec hf (hg.comp (pair left (left.comp right)))).of_eq $ by simp [cases]

protected theorem swap : primrec (unpaired (function.swap mkpair)) :=
(pair right left).of_eq $ λ n, by simp

theorem swap' {f} (hf : primrec (unpaired f)) : primrec (unpaired (function.swap f)) :=
(hf.comp primrec.swap).of_eq $ λ n, by simp

theorem pred : primrec pred :=
(cases1 0 primrec.id).of_eq $ λ n, by cases n; simp *

theorem add : primrec (unpaired (+)) :=
(prec primrec.id ((succ.comp right).comp right)).of_eq $
λ p, by simp; induction p.unpair.2; simp [*, -add_comm, add_succ]

theorem sub : primrec (unpaired has_sub.sub) :=
(prec primrec.id ((pred.comp right).comp right)).of_eq $
λ p, by simp; induction p.unpair.2; simp [*, -add_comm, sub_succ]

theorem mul : primrec (unpaired (*)) :=
(prec zero (add.comp (pair left (right.comp right)))).of_eq $
λ p, by simp; induction p.unpair.2; simp [*, mul_succ]

theorem pow : primrec (unpaired (^)) :=
(prec (const 1) (mul.comp (pair (right.comp right) left))).of_eq $
λ p, by simp; induction p.unpair.2; simp [*, pow_succ]

end primrec

end nat

/-- A `primcodable` type is an `encodable` type for which
  the encode/decode functions are primitive recursive. -/
class primcodable (α : Type*) extends encodable α :=
(prim : nat.primrec (λ n, encodable.encode (decode n)))

namespace primcodable
open nat.primrec

@[priority 0] instance of_denumerable (α) [denumerable α] : primcodable α :=
⟨succ.of_eq $ by simp⟩

def of_equiv (α) {β} [primcodable α] (e : β ≃ α) : primcodable β :=
{ prim := (primcodable.prim α).of_eq $ λ n,
    show (option.cases_on (option.map e.symm (decode α n))
      0 (λ a, nat.succ (encode (e a))) : ℕ) = encode (decode α n),
    by cases decode α n; dsimp [option.map, option.bind]; simp,
  ..encodable.of_equiv α e }

instance empty : primcodable empty :=
⟨zero⟩

instance unit : primcodable punit :=
⟨(cases1 1 zero).of_eq $ λ n, by cases n; simp⟩

instance option {α : Type*} [h : primcodable α] : primcodable (option α) :=
⟨(cases1 1 ((cases1 0 (succ.comp succ)).comp (primcodable.prim α))).of_eq $
  λ n, by cases n; simp; cases decode α n; refl⟩

instance bool : primcodable bool :=
⟨(cases1 1 (cases1 2 zero)).of_eq $
λ n, begin
  cases n, {refl}, cases n, {refl},
  rw decode_ge_two, {refl},
  exact dec_trivial
end⟩

end primcodable

/-- `primrec f` means `f` is primitive recursive (after
  encoding its input and output as natural numbers). -/
def primrec {α β} [primcodable α] [primcodable β] (f : α → β) : Prop :=
nat.primrec (λ n, encode ((decode α n).map f))

namespace primrec
variables {α : Type*} {β : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable σ]
open nat.primrec

protected theorem encode : primrec (@encode α _) :=
(primcodable.prim α).of_eq $ λ n, by cases decode α n; refl

protected theorem decode : primrec (decode α) :=
succ.comp (primcodable.prim α)

theorem dom_denumerable {α β} [denumerable α] [primcodable β]
  {f : α → β} : primrec f ↔ nat.primrec (λ n, encode (f (of_nat α n))) :=
⟨λ h, (pred.comp h).of_eq $ λ n, by simp; refl,
 λ h, (succ.comp h).of_eq $ λ n, by simp; refl⟩

theorem nat_iff {f : ℕ → ℕ} : primrec f ↔ nat.primrec f :=
dom_denumerable

theorem encdec : primrec (λ n, encode (decode α n)) :=
nat_iff.2 (primcodable.prim α)

theorem option_some : primrec (@some α) :=
((cases1 0 (succ.comp succ)).comp (primcodable.prim α)).of_eq $
λ n, by dsimp; cases decode α n; simp

theorem of_eq {f g : α → σ} (hg : primrec g) (H : ∀ n, f n = g n) : primrec f :=
(funext H : f = g).symm ▸ hg

theorem const (x : σ) : primrec (λ a : α, x) :=
((cases1 0 (const (encode x).succ)).comp (primcodable.prim α)).of_eq $
λ n, by simp; cases decode α n; refl

protected theorem id : primrec (@id α) :=
(primcodable.prim α).of_eq $ by simp

theorem comp {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {f : β → γ} {g : α → β} (hf : primrec f) (hg : primrec g) :
  primrec (f ∘ g) :=
((cases1 0 (hf.comp $ pred.comp hg)).comp (primcodable.prim α)).of_eq $
λ n, begin
  simp; cases decode α n, {refl},
  change _ = encode _,
  simp [encodek],
  change _ = encode (option.map f (decode β (encode _))),
  simp [encodek], refl
end

theorem succ : primrec nat.succ := nat_iff.2 nat.primrec.succ

theorem pred : primrec nat.pred := nat_iff.2 nat.primrec.pred

theorem encode_iff {f : α → σ} : primrec (λ a, encode (f a)) ↔ primrec f :=
⟨λ h, nat.primrec.of_eq h $ λ n, by cases decode α n; refl,
 primrec.encode.comp⟩

theorem of_nat_iff {α β} [denumerable α] [primcodable β]
  {f : α → β} : primrec f ↔ primrec (λ n, f (of_nat α n)) :=
dom_denumerable.trans $ nat_iff.symm.trans encode_iff

theorem option_some_iff {f : α → σ} : primrec (λ a, some (f a)) ↔ primrec f :=
⟨λ h, encode_iff.1 $ pred.comp $ encode_iff.2 h, option_some.comp⟩

end primrec

namespace primcodable
open nat.primrec

instance prod {α β} [primcodable α] [primcodable β] : primcodable (α × β) :=
⟨((cases zero ((cases zero succ).comp
  (pair right ((primcodable.prim β).comp left)))).comp
  (pair right ((primcodable.prim α).comp left))).of_eq $
λ n, begin
  simp [nat.unpaired],
  cases decode α n.unpair.1; simp, {refl},
  dsimp [option.bind],
  cases decode β n.unpair.2; simp, {refl},
  refl
end⟩

end primcodable

namespace primrec
variables {α : Type*} {σ : Type*} [primcodable α] [primcodable σ]
open nat.primrec

theorem fst {α β} [primcodable α] [primcodable β] :
  primrec (@prod.fst α β) :=
((cases zero ((cases zero (nat.primrec.succ.comp left)).comp
  (pair right ((primcodable.prim β).comp left)))).comp
  (pair right ((primcodable.prim α).comp left))).of_eq $
λ n, begin
  simp,
  cases decode α n.unpair.1; simp, {refl},
  dsimp [option.bind, (∘)],
  cases decode β n.unpair.2; simp, {refl},
  refl
end

theorem snd {α β} [primcodable α] [primcodable β] :
  primrec (@prod.snd α β) :=
((cases zero ((cases zero (nat.primrec.succ.comp right)).comp
  (pair right ((primcodable.prim β).comp left)))).comp
  (pair right ((primcodable.prim α).comp left))).of_eq $
λ n, begin
  simp,
  cases decode α n.unpair.1; simp, {refl},
  dsimp [option.bind, (∘)],
  cases decode β n.unpair.2; simp, {refl},
  refl
end

theorem pair {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {f : α → β} {g : α → γ} (hf : primrec f) (hg : primrec g) :
  primrec (λ a, (f a, g a)) :=
((cases1 0 (nat.primrec.succ.comp $
  pair (nat.primrec.pred.comp hf) (nat.primrec.pred.comp hg))).comp
  (primcodable.prim α)).of_eq $
λ n, by simp; cases decode α n; simp [encodek]; refl

theorem unpair : primrec nat.unpair :=
suffices primrec (λ n, (n ₗ, n ᵣ)), by simpa,
pair (nat_iff.2 nat.primrec.left) (nat_iff.2 nat.primrec.right)

theorem list_nth : ∀ (l : list α), primrec l.nth
| []     := dom_denumerable.2 zero
| (a::l) := dom_denumerable.2 $
  (cases1 (encode a).succ $ dom_denumerable.1 $ list_nth l).of_eq $
  λ n, by cases n; simp

end primrec

/-- `primrec₂ f` means `f` is a binary primitive recursive function.
  This is technically unnecessary since we can always curry all
  the arguments together, but there are enough natural two-arg
  functions that it is convenient to express this directly. -/
def primrec₂ {α β σ} [primcodable α] [primcodable β] [primcodable σ] (f : α → β → σ) :=
primrec (λ p : α × β, f p.1 p.2)

/-- `primrec_pred p` means `p : α → Prop` is a (decidable)
  primitive recursive predicate, which is to say that
  `to_bool ∘ p : α → bool` is primitive recursive. -/
def primrec_pred {α} [primcodable α] (p : α → Prop)
  [decidable_pred p] := primrec (λ a, to_bool (p a))

/-- `primrec_rel p` means `p : α → β → Prop` is a (decidable)
  primitive recursive relation, which is to say that
  `to_bool ∘ p : α → β → bool` is primitive recursive. -/
def primrec_rel {α β} [primcodable α] [primcodable β]
  (s : α → β → Prop) [∀ a b, decidable (s a b)] :=
primrec₂ (λ a b, to_bool (s a b))

namespace primrec₂
variables {α : Type*} {β : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable σ]

theorem of_eq {f g : α → β → σ} (hg : primrec₂ g) (H : ∀ a b, f a b = g a b) : primrec₂ f :=
(by funext a b; apply H : f = g).symm ▸ hg

theorem const (x : σ) : primrec₂ (λ (a : α) (b : β), x) := primrec.const _

protected theorem pair : primrec₂ (@prod.mk α β) :=
primrec.pair primrec.fst primrec.snd

theorem left : primrec₂ (λ (a : α) (b : β), a) := primrec.fst

theorem right : primrec₂ (λ (a : α) (b : β), b) := primrec.snd

theorem mkpair : primrec₂ nat.mkpair :=
by simp [primrec₂, primrec, option.bind]; constructor

theorem unpaired {f : ℕ → ℕ → α} : primrec (nat.unpaired f) ↔ primrec₂ f :=
⟨λ h, by simpa [(∘)] using h.comp mkpair,
 λ h, h.comp primrec.unpair⟩

theorem unpaired' {f : ℕ → ℕ → ℕ} : nat.primrec (nat.unpaired f) ↔ primrec₂ f :=
primrec.nat_iff.symm.trans unpaired

theorem encode_iff {f : α → β → σ} : primrec₂ (λ a b, encode (f a b)) ↔ primrec₂ f :=
primrec.encode_iff

theorem option_some_iff {f : α → β → σ} : primrec₂ (λ a b, some (f a b)) ↔ primrec₂ f :=
primrec.option_some_iff

theorem of_nat_iff {α β σ}
  [denumerable α] [denumerable β] [primcodable σ]
  {f : α → β → σ} : primrec₂ f ↔ primrec₂ (λ m n : ℕ,
    f (of_nat α m) (of_nat β n)) :=
(primrec.of_nat_iff.trans $ by simp).trans unpaired

theorem uncurry {f : α → β → σ} : primrec (function.uncurry f) ↔ primrec₂ f :=
by rw [show function.uncurry f = λ (p : α × β), f p.1 p.2,
       from funext $ λ ⟨a, b⟩, rfl]; refl

theorem curry {f : α × β → σ} : primrec₂ (function.curry f) ↔ primrec f :=
by rw [← uncurry, function.uncurry_curry]

end primrec₂

section comp
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] [primcodable σ]

theorem primrec.comp₂ {f : γ → σ} {g : α → β → γ}
  (hf : primrec f) (hg : primrec₂ g) :
  primrec₂ (λ a b, f (g a b)) := hf.comp hg

theorem primrec₂.comp
  {f : β → γ → σ} {g : α → β} {h : α → γ}
  (hf : primrec₂ f) (hg : primrec g) (hh : primrec h) :
  primrec (λ a, f (g a) (h a)) :=
primrec.comp hf (primrec.pair hg hh)

theorem primrec₂.comp₂
  {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ}
  (hf : primrec₂ f) (hg : primrec₂ g) (hh : primrec₂ h) :
  primrec₂ (λ a b, f (g a b) (h a b)) :=
primrec.comp hf (primrec.pair hg hh)

theorem primrec_pred.comp
  {p : β → Prop} [decidable_pred p] {f : α → β} :
  primrec_pred p → primrec f →
  primrec_pred (λ a, p (f a)) := primrec.comp

theorem primrec_rel.comp
  {R : β → γ → Prop} [∀ a b, decidable (R a b)] {f : α → β} {g : α → γ} :
  primrec_rel R → primrec f → primrec g →
  primrec_pred (λ a, R (f a) (g a)) := primrec₂.comp

theorem primrec_rel.comp₂
  {R : γ → δ → Prop} [∀ a b, decidable (R a b)] {f : α → β → γ} {g : α → β → δ} :
  primrec_rel R → primrec₂ f → primrec₂ g →
  primrec_rel (λ a b, R (f a b) (g a b)) := primrec_rel.comp

end comp

theorem primrec_pred.of_eq {α} [primcodable α]
  {p q : α → Prop} [decidable_pred p] [decidable_pred q]
  (hq : primrec_pred q) (H : ∀ a, p a ↔ q a) : primrec_pred p :=
primrec.of_eq hq (λ a, to_bool_congr (H a))

theorem primrec_rel.of_eq {α β} [primcodable α] [primcodable β]
  {r s : α → β → Prop} [∀ a b, decidable (r a b)] [∀ a b, decidable (s a b)]
  (hs : primrec_rel s) (H : ∀ a b, r a b ↔ s a b) : primrec_rel r :=
primrec₂.of_eq hs (λ a b, to_bool_congr (H a b))

namespace primrec₂
variables {α : Type*} {β : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable σ]
open nat.primrec

theorem swap {f : α → β → σ} (h : primrec₂ f) : primrec₂ (function.swap f) :=
h.comp₂ primrec₂.right primrec₂.left

theorem nat_iff {f : α → β → σ} : primrec₂ f ↔
  nat.primrec (nat.unpaired $ λ m n : ℕ,
    encode $ (decode α m).bind $ λ a, (decode β n).map (f a)) :=
have ∀ (a : option α) (b : option β),
  option.map (λ (p : α × β), f p.1 p.2)
    (option.bind a (λ (a : α), option.map (prod.mk a) b)) =
  option.bind a (λ a, option.map (f a) b),
by intros; cases a; [refl, {cases b; refl}],
by simp [primrec₂, primrec, this]

theorem nat_iff' {f : α → β → σ} : primrec₂ f ↔ primrec₂ (λ m n : ℕ,
  option.bind (decode α m) (λ a, option.map (f a) (decode β n))) :=
nat_iff.trans $ unpaired'.trans encode_iff

end primrec₂

namespace primrec
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] [primcodable σ]

theorem nat_elim {f : α → β} {g : α → ℕ × β → β}
  (hf : primrec f) (hg : primrec₂ g) :
  primrec₂ (λ a (n : ℕ), n.elim (f a) (λ n IH, g a (n, IH))) :=
primrec₂.nat_iff.2 $ ((nat.primrec.cases nat.primrec.zero $
    (nat.primrec.prec hf $ nat.primrec.comp hg $ nat.primrec.left.pair $
      (nat.primrec.left.comp nat.primrec.right).pair $
      nat.primrec.pred.comp $ nat.primrec.right.comp nat.primrec.right).comp $
    nat.primrec.right.pair $
      nat.primrec.right.comp nat.primrec.left).comp $
  nat.primrec.id.pair $ (primcodable.prim α).comp nat.primrec.left).of_eq $
λ n, begin
  simp,
  cases decode α n.unpair.1 with a, {refl},
  simp [(∘), encodek, option.map, option.bind],
  symmetry,
  induction n.unpair.2 with m; simp [(∘), encodek, option.bind],
  simp [ih],
  repeat {simp [encodek, option.map, option.bind]}
end

theorem nat_elim' {f : α → ℕ} {g : α → β} {h : α → ℕ × β → β}
  (hf : primrec f) (hg : primrec g) (hh : primrec₂ h) :
  primrec (λ a, (f a).elim (g a) (λ n IH, h a (n, IH))) :=
(nat_elim hg hh).comp primrec.id hf

theorem nat_elim1 {f : ℕ → α → α} (a : α) (hf : primrec₂ f) :
  primrec (nat.elim a f) :=
nat_elim' primrec.id (const a) $ comp₂ hf primrec₂.right

theorem nat_cases' {f : α → β} {g : α → ℕ → β}
  (hf : primrec f) (hg : primrec₂ g) :
  primrec₂ (λ a, nat.cases (f a) (g a)) :=
nat_elim hf $ hg.comp₂ primrec₂.left $
  comp₂ fst primrec₂.right

theorem nat_cases {f : α → ℕ} {g : α → β} {h : α → ℕ → β}
  (hf : primrec f) (hg : primrec g) (hh : primrec₂ h) :
  primrec (λ a, (f a).cases (g a) (h a)) :=
(nat_cases' hg hh).comp primrec.id hf

theorem nat_cases1 {f : ℕ → α} (a : α) (hf : primrec f) :
  primrec (nat.cases a f) :=
nat_cases primrec.id (const a) (comp₂ hf primrec₂.right)

theorem option_cases {o : α → option β} {f : α → σ} {g : α → β → σ}
  (ho : primrec o) (hf : primrec f) (hg : primrec₂ g) :
  @primrec _ σ _ _ (λ a, option.cases_on (o a) (f a) (g a)) :=
encode_iff.1 $
(nat_cases (encode_iff.2 ho) (encode_iff.2 hf) $
  pred.comp₂ $ primrec₂.encode_iff.2 $
  (primrec₂.nat_iff'.1 hg).comp₂
    ((@primrec.encode α _).comp₂ primrec₂.left)
    primrec₂.right).of_eq $
λ a, begin
  cases o a with b; simp [encodek]; refl
end

theorem option_bind {f : α → option β} {g : α → β → option σ}
  (hf : primrec f) (hg : primrec₂ g) :
  primrec (λ a, (f a).bind (g a)) :=
(option_cases hf (const none) hg).of_eq $
λ a, by cases f a; refl

theorem option_bind1 {f : α → option σ} (hf : primrec f) :
  primrec (λ o, option.bind o f) :=
option_bind primrec.id (hf.comp₂ primrec₂.right)

theorem option_map {f : α → option β} {g : α → β → σ}
  (hf : primrec f) (hg : primrec₂ g) : primrec (λ a, (f a).map (g a)) :=
option_bind hf (option_some.comp₂ hg)

theorem option_map1 {f : α → σ} (hf : primrec f) : primrec (option.map f) :=
option_map primrec.id (hf.comp₂ primrec₂.right)

theorem option_iget [inhabited α] : primrec (@option.iget α _) :=
(option_cases primrec.id (const $ default α) primrec₂.right).of_eq $
λ o, by cases o; refl

theorem bind_decode_iff {f : α → β → option σ} : primrec₂ (λ a n,
  (decode β n).bind (f a)) ↔ primrec₂ f :=
⟨λ h, by simpa [encodek] using
   h.comp primrec₂.left ((@primrec.encode β _).comp primrec₂.right),
 λ h, option_bind (primrec.decode.comp snd) $
   h.comp (fst.comp primrec₂.left) primrec₂.right⟩

theorem map_decode_iff {f : α → β → σ} : primrec₂ (λ a n,
  (decode β n).map (f a)) ↔ primrec₂ f :=
bind_decode_iff.trans primrec₂.option_some_iff

theorem nat_add : primrec₂ ((+) : ℕ → ℕ → ℕ) :=
primrec₂.unpaired'.1 nat.primrec.add

theorem nat_sub : primrec₂ (has_sub.sub : ℕ → ℕ → ℕ) :=
primrec₂.unpaired'.1 nat.primrec.sub

theorem nat_mul : primrec₂ ((*) : ℕ → ℕ → ℕ) :=
primrec₂.unpaired'.1 nat.primrec.mul

theorem cond {c : α → bool} {f : α → σ} {g : α → σ}
  (hc : primrec c) (hf : primrec f) (hg : primrec g) :
  primrec (λ a, cond (c a) (f a) (g a)) :=
(nat_cases (encode_iff.2 hc) hg (hf.comp₂ primrec₂.left)).of_eq $
λ a, by cases c a; refl

theorem ite {c : α → Prop} [decidable_pred c] {f : α → σ} {g : α → σ}
  (hc : primrec_pred c) (hf : primrec f) (hg : primrec g) :
  primrec (λ a, if c a then f a else g a) :=
by simpa using cond hc hf hg

theorem list_inth [inhabited α] (l : list α) : primrec l.inth :=
option_iget.comp (list_nth _)

theorem nat_le : primrec_rel ((≤) : ℕ → ℕ → Prop) :=
(nat_cases nat_sub (const tt) (primrec₂.const ff)).of_eq $
λ p, begin
  dsimp [function.swap],
  cases e : p.1 - p.2 with n,
  { simp [nat.sub_eq_zero_iff_le.1 e] },
  { simp [not_le.2 (nat.lt_of_sub_eq_succ e)] }
end

theorem dom_bool (f : bool → α) : primrec f :=
(cond primrec.id (const (f tt)) (const (f ff))).of_eq $
λ b, by cases b; refl

theorem dom_bool₂ (f : bool → bool → α) : primrec₂ f :=
(cond fst
  ((dom_bool (f tt)).comp snd)
  ((dom_bool (f ff)).comp snd)).of_eq $
λ ⟨a, b⟩, by cases a; refl

protected theorem bnot : primrec bnot := dom_bool _
protected theorem band : primrec₂ band := dom_bool₂ _
protected theorem bor : primrec₂ bor := dom_bool₂ _

protected theorem not {p : α → Prop} [decidable_pred p]
  (hp : primrec_pred p) : primrec_pred (λ a, ¬ p a) :=
(primrec.bnot.comp hp).of_eq $ λ n, by simp

protected theorem and {p q : α → Prop}
  [decidable_pred p] [decidable_pred q]
  (hp : primrec_pred p) (hq : primrec_pred q) :
  primrec_pred (λ a, p a ∧ q a) :=
(primrec.band.comp hp hq).of_eq $ λ n, by simp

protected theorem or {p q : α → Prop}
  [decidable_pred p] [decidable_pred q]
  (hp : primrec_pred p) (hq : primrec_pred q) :
  primrec_pred (λ a, p a ∨ q a) :=
(primrec.bor.comp hp hq).of_eq $ λ n, by simp

protected theorem eq [decidable_eq α] : primrec_rel (@eq α) :=
have primrec_rel (λ a b : ℕ, a = b), from
  (primrec.and nat_le nat_le.swap).of_eq $
  λ a, by simp [le_antisymm_iff],
(this.comp₂
  (primrec.encode.comp₂ primrec₂.left)
  (primrec.encode.comp₂ primrec₂.right)).of_eq $
λ a b, encode_injective.eq_iff.symm

theorem list_find_index {p : α → β → Prop}
  [∀ a b, decidable (p a b)] (hp : primrec_rel p) :
  ∀ (l : list β), primrec (λ a, l.find_index (p a))
| [] := const 0
| (a::l) := ite (hp.comp primrec.id (const a)) (const 0)
  (succ.comp (list_find_index l))

theorem list_index_of [decidable_eq α] (l : list α) :
  primrec (λ a, l.index_of a) := list_find_index primrec.eq l

theorem dom_fintype [fintype α] (f : α → σ) : primrec f :=
let ⟨l, nd, m⟩ := fintype.exists_univ_list α in
option_some_iff.1 $ begin
  haveI := decidable_eq_of_encodable α,
  refine ((list_nth (l.map f)).comp (list_index_of l)).of_eq (λ a, _),
  simp [(∘)],
  rw [list.nth_le_nth (list.index_of_lt_length.2 (m _)),
      list.index_of_nth_le]; refl
end

theorem nat_bodd_div2 : primrec nat.bodd_div2 :=
(nat_elim' primrec.id (const (ff, 0))
  (primrec.comp₂
    ((cond fst
      (pair (const ff) (succ.comp snd))
      (pair (const tt) snd)).comp snd)
    primrec₂.right)).of_eq $
λ n, begin
  simp [-nat.bodd_div2_eq], symmetry,
  induction n with n IH, {refl},
  simp [-nat.bodd_div2_eq, nat.bodd_div2, *],
  rcases nat.bodd_div2 n with ⟨_|_, m⟩; simp [nat.bodd_div2]
end

theorem nat_bodd : primrec nat.bodd := fst.comp nat_bodd_div2
theorem nat_div2 : primrec nat.div2 := snd.comp nat_bodd_div2

theorem nat_bit0 : primrec (@bit0 ℕ _) :=
nat_add.comp primrec.id primrec.id

theorem nat_bit1 : primrec (@bit1 ℕ _ _) :=
nat_add.comp nat_bit0 (const 1)

theorem nat_bit : primrec₂ nat.bit :=
(cond primrec.fst
  (nat_bit1.comp primrec.snd)
  (nat_bit0.comp primrec.snd)).of_eq $
λ n, by cases n.1; refl

theorem nat_div_mod : primrec₂ (λ n k : ℕ, (n / k, n % k)) :=
let f (a : ℕ × ℕ) : ℕ × ℕ := a.1.elim (0, 0) (λ _ IH,
  if nat.succ IH.2 = a.2
  then (nat.succ IH.1, 0)
  else (IH.1, nat.succ IH.2)) in
have hf : primrec f, from
nat_elim' fst (const (0, 0)) $
  ((ite ((@primrec.eq ℕ _ _).comp (succ.comp $ snd.comp snd) fst)
      (pair (succ.comp $ fst.comp snd) (const 0))
      (pair (fst.comp snd) (succ.comp $ snd.comp snd)))
    .comp₂ (primrec₂.pair.comp₂
    (snd.comp₂ primrec₂.left)
    (snd.comp₂ primrec₂.right))),
suffices ∀ k n, (n / k, n % k) = f (n, k),
from hf.of_eq $ λ ⟨m, n⟩, by simp [this],
λ k n, begin
  have : (f (n, k)).2 + k * (f (n, k)).1 = n
    ∧ (0 < k → (f (n, k)).2 < k)
    ∧ (k = 0 → (f (n, k)).1 = 0),
  { induction n with n IH, {exact ⟨rfl, id, λ _, rfl⟩},
    rw [λ n:ℕ, show f (n.succ, k) =
      _root_.ite ((f (n, k)).2.succ = k)
      (nat.succ (f (n, k)).1, 0)
      ((f (n, k)).1, (f (n, k)).2.succ), from rfl],
    by_cases h : (f (n, k)).2.succ = k; simp [h],
    { have := congr_arg nat.succ IH.1,
      refine ⟨_, λ k0, nat.no_confusion (h.trans k0)⟩,
      rwa [← nat.succ_add, h, add_comm, ← nat.mul_succ] at this },
    { exact ⟨by rw [nat.succ_add, IH.1],
        λ k0, lt_of_le_of_ne (IH.2.1 k0) h, IH.2.2⟩ } },
  revert this, cases f (n, k) with D M,
  simp, intros h₁ h₂ h₃,
  cases nat.eq_zero_or_pos k,
  { simp [h, h₃ h] at h₁ ⊢, simp [h₁] },
  { exact (nat.div_mod_unique h).2 ⟨h₁, h₂ h⟩ }
end

theorem nat_div : primrec₂ ((/) : ℕ → ℕ → ℕ) := fst.comp₂ nat_div_mod
theorem nat_mod : primrec₂ ((%) : ℕ → ℕ → ℕ) := snd.comp₂ nat_div_mod

end primrec

namespace primcodable
variables {α : Type*} {β : Type*}
variables [primcodable α] [primcodable β]
open primrec

instance sum : primcodable (α ⊕ β) :=
⟨primrec.nat_iff.1 $
(encode_iff.2 (cond nat_bodd
  (((@primrec.decode β _).comp nat_div2).option_map $
     nat_bit.comp₂ (primrec₂.const tt)
       (primrec.encode.comp₂ primrec₂.right))
  (((@primrec.decode α _).comp nat_div2).option_map $
     nat_bit.comp₂ (primrec₂.const ff)
       (primrec.encode.comp₂ primrec₂.right)))).of_eq $
λ n, show encode (decode_sum n) = _, begin
  simp [decode_sum],
  cases nat.bodd n; simp [decode_sum],
  { cases decode α n.div2; refl },
  { cases decode β n.div2; refl }
end⟩

end primcodable