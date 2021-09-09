/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.equiv.list
import logic.function.iterate

/-!
# The primitive recursive functions

The primitive recursive functions are the least collection of functions
`nat → nat` which are closed under projections (using the mkpair
pairing function), composition, zero, successor, and primitive recursion
(i.e. nat.rec where the motive is C n := nat).

We can extend this definition to a large class of basic types by
using canonical encodings of types as natural numbers (Gödel numbering),
which we implement through the type class `encodable`. (More precisely,
we need that the composition of encode with decode yields a
primitive recursive function, so we have the `primcodable` type class
for this.)

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

open denumerable encodable function

namespace nat

def elim {C : Sort*} : C → (ℕ → C → C) → ℕ → C := @nat.rec (λ _, C)

@[simp] theorem elim_zero {C} (a f) : @nat.elim C a f 0 = a := rfl
@[simp] theorem elim_succ {C} (a f n) :
  @nat.elim C a f (succ n) = f n (nat.elim a f n) := rfl

def cases {C : Sort*} (a : C) (f : ℕ → C) : ℕ → C := nat.elim a (λ n _, f n)

@[simp] theorem cases_zero {C} (a f) : @nat.cases C a f 0 = a := rfl
@[simp] theorem cases_succ {C} (a f n) : @nat.cases C a f (succ n) = f n := rfl

@[simp, reducible] def unpaired {α} (f : ℕ → ℕ → α) (n : ℕ) : α :=
f n.unpair.1 n.unpair.2

/-- The primitive recursive functions `ℕ → ℕ`. -/
inductive primrec : (ℕ → ℕ) → Prop
| zero : primrec (λ n, 0)
| succ : primrec succ
| left : primrec (λ n, n.unpair.1)
| right : primrec (λ n, n.unpair.2)
| pair {f g} : primrec f → primrec g → primrec (λ n, mkpair (f n) (g n))
| comp {f g} : primrec f → primrec g → primrec (λ n, f (g n))
| prec {f g} : primrec f → primrec g → primrec (unpaired (λ z n,
   n.elim (f z) (λ y IH, g $ mkpair z $ mkpair y IH)))

namespace primrec

theorem of_eq {f g : ℕ → ℕ} (hf : primrec f) (H : ∀ n, f n = g n) : primrec g :=
(funext H : f = g) ▸ hf

theorem const : ∀ (n : ℕ), primrec (λ _, n)
| 0 := zero
| (n+1) := succ.comp (const n)

protected theorem id : primrec id :=
(left.pair right).of_eq $ λ n, by simp

theorem prec1 {f} (m : ℕ) (hf : primrec f) : primrec (λ n,
   n.elim m (λ y IH, f $ mkpair y IH)) :=
((prec (const m) (hf.comp right)).comp
  (zero.pair primrec.id)).of_eq $
λ n, by simp; dsimp; rw [unpair_mkpair]

theorem cases1 {f} (m : ℕ) (hf : primrec f) : primrec (nat.cases m f) :=
(prec1 m (hf.comp left)).of_eq $ by simp [cases]

theorem cases {f g} (hf : primrec f) (hg : primrec g) :
  primrec (unpaired (λ z n, n.cases (f z) (λ y, g $ mkpair z y))) :=
(prec hf (hg.comp (pair left (left.comp right)))).of_eq $ by simp [cases]

protected theorem swap : primrec (unpaired (swap mkpair)) :=
(pair right left).of_eq $ λ n, by simp

theorem swap' {f} (hf : primrec (unpaired f)) : primrec (unpaired (swap f)) :=
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
λ p, by simp; induction p.unpair.2; simp [*, mul_succ, add_comm]

theorem pow : primrec (unpaired (^)) :=
(prec (const 1) (mul.comp (pair (right.comp right) left))).of_eq $
λ p, by simp; induction p.unpair.2; simp [*, pow_succ']

end primrec

end nat

/-- A `primcodable` type is an `encodable` type for which
  the encode/decode functions are primitive recursive. -/
class primcodable (α : Type*) extends encodable α :=
(prim [] : nat.primrec (λ n, encodable.encode (decode n)))

namespace primcodable
open nat.primrec

@[priority 10] instance of_denumerable (α) [denumerable α] : primcodable α :=
⟨succ.of_eq $ by simp⟩

def of_equiv (α) {β} [primcodable α] (e : β ≃ α) : primcodable β :=
{ prim := (primcodable.prim α).of_eq $ λ n,
    show encode (decode α n) =
      (option.cases_on (option.map e.symm (decode α n))
        0 (λ a, nat.succ (encode (e a))) : ℕ),
    by cases decode α n; dsimp; simp,
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
λ n, by cases decode α n; simp

theorem of_eq {f g : α → σ} (hf : primrec f) (H : ∀ n, f n = g n) : primrec g :=
(funext H : f = g) ▸ hf

theorem const (x : σ) : primrec (λ a : α, x) :=
((cases1 0 (const (encode x).succ)).comp (primcodable.prim α)).of_eq $
λ n, by cases decode α n; refl

protected theorem id : primrec (@id α) :=
(primcodable.prim α).of_eq $ by simp

theorem comp {f : β → σ} {g : α → β}
  (hf : primrec f) (hg : primrec g) : primrec (λ a, f (g a)) :=
((cases1 0 (hf.comp $ pred.comp hg)).comp (primcodable.prim α)).of_eq $
λ n, begin
  cases decode α n, {refl},
  simp [encodek]
end

theorem succ : primrec nat.succ := nat_iff.2 nat.primrec.succ

theorem pred : primrec nat.pred := nat_iff.2 nat.primrec.pred

theorem encode_iff {f : α → σ} : primrec (λ a, encode (f a)) ↔ primrec f :=
⟨λ h, nat.primrec.of_eq h $ λ n, by cases decode α n; refl,
 primrec.encode.comp⟩

theorem of_nat_iff {α β} [denumerable α] [primcodable β]
  {f : α → β} : primrec f ↔ primrec (λ n, f (of_nat α n)) :=
dom_denumerable.trans $ nat_iff.symm.trans encode_iff

protected theorem of_nat (α) [denumerable α] : primrec (of_nat α) :=
of_nat_iff.1 primrec.id

theorem option_some_iff {f : α → σ} : primrec (λ a, some (f a)) ↔ primrec f :=
⟨λ h, encode_iff.1 $ pred.comp $ encode_iff.2 h, option_some.comp⟩

theorem of_equiv {β} {e : β ≃ α} :
  by haveI := primcodable.of_equiv α e; exact
  primrec e :=
by letI : primcodable β := primcodable.of_equiv α e; exact encode_iff.1 primrec.encode

theorem of_equiv_symm {β} {e : β ≃ α} :
  by haveI := primcodable.of_equiv α e; exact
  primrec e.symm :=
by letI := primcodable.of_equiv α e; exact
encode_iff.1
  (show primrec (λ a, encode (e (e.symm a))), by simp [primrec.encode])

theorem of_equiv_iff {β} (e : β ≃ α)
  {f : σ → β} :
  by haveI := primcodable.of_equiv α e; exact
  primrec (λ a, e (f a)) ↔ primrec f :=
by letI := primcodable.of_equiv α e; exact
⟨λ h, (of_equiv_symm.comp h).of_eq (λ a, by simp), of_equiv.comp⟩

theorem of_equiv_symm_iff {β} (e : β ≃ α)
  {f : σ → α} :
  by haveI := primcodable.of_equiv α e; exact
  primrec (λ a, e.symm (f a)) ↔ primrec f :=
by letI := primcodable.of_equiv α e; exact
⟨λ h, (of_equiv.comp h).of_eq (λ a, by simp), of_equiv_symm.comp⟩

end primrec

namespace primcodable
open nat.primrec

instance prod {α β} [primcodable α] [primcodable β] : primcodable (α × β) :=
⟨((cases zero ((cases zero succ).comp
  (pair right ((primcodable.prim β).comp left)))).comp
  (pair right ((primcodable.prim α).comp left))).of_eq $
λ n, begin
  simp [nat.unpaired],
  cases decode α n.unpair.1, { simp },
  cases decode β n.unpair.2; simp
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
  cases decode α n.unpair.1; simp,
  cases decode β n.unpair.2; simp
end

theorem snd {α β} [primcodable α] [primcodable β] :
  primrec (@prod.snd α β) :=
((cases zero ((cases zero (nat.primrec.succ.comp right)).comp
  (pair right ((primcodable.prim β).comp left)))).comp
  (pair right ((primcodable.prim α).comp left))).of_eq $
λ n, begin
  simp,
  cases decode α n.unpair.1; simp,
  cases decode β n.unpair.2; simp
end

theorem pair {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {f : α → β} {g : α → γ} (hf : primrec f) (hg : primrec g) :
  primrec (λ a, (f a, g a)) :=
((cases1 0 (nat.primrec.succ.comp $
  pair (nat.primrec.pred.comp hf) (nat.primrec.pred.comp hg))).comp
  (primcodable.prim α)).of_eq $
λ n, by cases decode α n; simp [encodek]; refl

theorem unpair : primrec nat.unpair :=
(pair (nat_iff.2 nat.primrec.left) (nat_iff.2 nat.primrec.right)).of_eq $
λ n, by simp

theorem list_nth₁ : ∀ (l : list α), primrec l.nth
| []     := dom_denumerable.2 zero
| (a::l) := dom_denumerable.2 $
  (cases1 (encode a).succ $ dom_denumerable.1 $ list_nth₁ l).of_eq $
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

theorem of_eq {f g : α → β → σ} (hg : primrec₂ f) (H : ∀ a b, f a b = g a b) : primrec₂ g :=
(by funext a b; apply H : f = g) ▸ hg

theorem const (x : σ) : primrec₂ (λ (a : α) (b : β), x) := primrec.const _

protected theorem pair : primrec₂ (@prod.mk α β) :=
primrec.pair primrec.fst primrec.snd

theorem left : primrec₂ (λ (a : α) (b : β), a) := primrec.fst

theorem right : primrec₂ (λ (a : α) (b : β), b) := primrec.snd

theorem mkpair : primrec₂ nat.mkpair :=
by simp [primrec₂, primrec]; constructor

theorem unpaired {f : ℕ → ℕ → α} : primrec (nat.unpaired f) ↔ primrec₂ f :=
⟨λ h, by simpa using h.comp mkpair,
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
  primrec (λ a, f (g a) (h a)) := hf.comp (hg.pair hh)

theorem primrec₂.comp₂
  {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ}
  (hf : primrec₂ f) (hg : primrec₂ g) (hh : primrec₂ h) :
  primrec₂ (λ a b, f (g a b) (h a b)) := hf.comp hg hh

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
  (hp : primrec_pred p) (H : ∀ a, p a ↔ q a) : primrec_pred q :=
primrec.of_eq hp (λ a, to_bool_congr (H a))

theorem primrec_rel.of_eq {α β} [primcodable α] [primcodable β]
  {r s : α → β → Prop} [∀ a b, decidable (r a b)] [∀ a b, decidable (s a b)]
  (hr : primrec_rel r) (H : ∀ a b, r a b ↔ s a b) : primrec_rel s :=
primrec₂.of_eq hr (λ a b, to_bool_congr (H a b))

namespace primrec₂
variables {α : Type*} {β : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable σ]
open nat.primrec

theorem swap {f : α → β → σ} (h : primrec₂ f) : primrec₂ (swap f) :=
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

theorem to₂ {f : α × β → σ} (hf : primrec f) : primrec₂ (λ a b, f (a, b)) :=
hf.of_eq $ λ ⟨a, b⟩, rfl

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
  simp [encodek],
  induction n.unpair.2 with m; simp [encodek],
  simp [ih, encodek]
end

theorem nat_elim' {f : α → ℕ} {g : α → β} {h : α → ℕ × β → β}
  (hf : primrec f) (hg : primrec g) (hh : primrec₂ h) :
  primrec (λ a, (f a).elim (g a) (λ n IH, h a (n, IH))) :=
(nat_elim hg hh).comp primrec.id hf

theorem nat_elim₁ {f : ℕ → α → α} (a : α) (hf : primrec₂ f) :
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

theorem nat_cases₁ {f : ℕ → α} (a : α) (hf : primrec f) :
  primrec (nat.cases a f) :=
nat_cases primrec.id (const a) (comp₂ hf primrec₂.right)

theorem nat_iterate {f : α → ℕ} {g : α → β} {h : α → β → β}
  (hf : primrec f) (hg : primrec g) (hh : primrec₂ h) :
  primrec (λ a, (h a)^[f a] (g a)) :=
(nat_elim' hf hg (hh.comp₂ primrec₂.left $ snd.comp₂ primrec₂.right)).of_eq $
λ a, by induction f a; simp [*, function.iterate_succ']

theorem option_cases {o : α → option β} {f : α → σ} {g : α → β → σ}
  (ho : primrec o) (hf : primrec f) (hg : primrec₂ g) :
  @primrec _ σ _ _ (λ a, option.cases_on (o a) (f a) (g a)) :=
encode_iff.1 $
(nat_cases (encode_iff.2 ho) (encode_iff.2 hf) $
  pred.comp₂ $ primrec₂.encode_iff.2 $
  (primrec₂.nat_iff'.1 hg).comp₂
    ((@primrec.encode α _).comp fst).to₂
    primrec₂.right).of_eq $
λ a, by cases o a with b; simp [encodek]; refl

theorem option_bind {f : α → option β} {g : α → β → option σ}
  (hf : primrec f) (hg : primrec₂ g) :
  primrec (λ a, (f a).bind (g a)) :=
(option_cases hf (const none) hg).of_eq $
λ a, by cases f a; refl

theorem option_bind₁ {f : α → option σ} (hf : primrec f) :
  primrec (λ o, option.bind o f) :=
option_bind primrec.id (hf.comp snd).to₂

theorem option_map {f : α → option β} {g : α → β → σ}
  (hf : primrec f) (hg : primrec₂ g) : primrec (λ a, (f a).map (g a)) :=
option_bind hf (option_some.comp₂ hg)

theorem option_map₁ {f : α → σ} (hf : primrec f) : primrec (option.map f) :=
option_map primrec.id (hf.comp snd).to₂

theorem option_iget [inhabited α] : primrec (@option.iget α _) :=
(option_cases primrec.id (const $ default α) primrec₂.right).of_eq $
λ o, by cases o; refl

theorem option_is_some : primrec (@option.is_some α) :=
(option_cases primrec.id (const ff) (const tt).to₂).of_eq $
λ o, by cases o; refl

theorem option_get_or_else : primrec₂ (@option.get_or_else α) :=
primrec.of_eq (option_cases primrec₂.left primrec₂.right primrec₂.right) $
λ ⟨o, a⟩, by cases o; refl

theorem bind_decode_iff {f : α → β → option σ} : primrec₂ (λ a n,
  (decode β n).bind (f a)) ↔ primrec₂ f :=
⟨λ h, by simpa [encodek] using
   h.comp fst ((@primrec.encode β _).comp snd),
 λ h, option_bind (primrec.decode.comp snd) $
   h.comp (fst.comp fst) snd⟩

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
(nat_cases (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq $
λ a, by cases c a; refl

theorem ite {c : α → Prop} [decidable_pred c] {f : α → σ} {g : α → σ}
  (hc : primrec_pred c) (hf : primrec f) (hg : primrec g) :
  primrec (λ a, if c a then f a else g a) :=
by simpa using cond hc hf hg

theorem nat_le : primrec_rel ((≤) : ℕ → ℕ → Prop) :=
(nat_cases nat_sub (const tt) (const ff).to₂).of_eq $
λ p, begin
  dsimp [swap],
  cases e : p.1 - p.2 with n,
  { simp [nat.sub_eq_zero_iff_le.1 e] },
  { simp [not_le.2 (nat.lt_of_sub_eq_succ e)] }
end

theorem nat_min : primrec₂ (@min ℕ _) := ite nat_le fst snd
theorem nat_max : primrec₂ (@max ℕ _) := ite (nat_le.comp primrec.snd primrec.fst) fst snd

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
λ a b, encode_injective.eq_iff

theorem nat_lt : primrec_rel ((<) : ℕ → ℕ → Prop) :=
(nat_le.comp snd fst).not.of_eq $ λ p, by simp

theorem option_guard {p : α → β → Prop}
  [∀ a b, decidable (p a b)] (hp : primrec_rel p)
  {f : α → β} (hf : primrec f) :
  primrec (λ a, option.guard (p a) (f a)) :=
ite (hp.comp primrec.id hf) (option_some_iff.2 hf) (const none)

theorem option_orelse :
  primrec₂ ((<|>) : option α → option α → option α) :=
(option_cases fst snd (fst.comp fst).to₂).of_eq $
λ ⟨o₁, o₂⟩, by cases o₁; cases o₂; refl

protected theorem decode₂ : primrec (decode₂ α) :=
option_bind primrec.decode $
option_guard ((@primrec.eq _ _ nat.decidable_eq).comp
  (encode_iff.2 snd) (fst.comp fst)) snd

theorem list_find_index₁ {p : α → β → Prop}
  [∀ a b, decidable (p a b)] (hp : primrec_rel p) :
  ∀ (l : list β), primrec (λ a, l.find_index (p a))
| [] := const 0
| (a::l) := ite (hp.comp primrec.id (const a)) (const 0)
  (succ.comp (list_find_index₁ l))

theorem list_index_of₁ [decidable_eq α] (l : list α) :
  primrec (λ a, l.index_of a) := list_find_index₁ primrec.eq l

theorem dom_fintype [fintype α] (f : α → σ) : primrec f :=
let ⟨l, nd, m⟩ := fintype.exists_univ_list α in
option_some_iff.1 $ begin
  haveI := decidable_eq_of_encodable α,
  refine ((list_nth₁ (l.map f)).comp (list_index_of₁ l)).of_eq (λ a, _),
  rw [list.nth_map, list.nth_le_nth (list.index_of_lt_length.2 (m _)),
      list.index_of_nth_le]; refl
end

theorem nat_bodd_div2 : primrec nat.bodd_div2 :=
(nat_elim' primrec.id (const (ff, 0))
  (((cond fst
      (pair (const ff) (succ.comp snd))
      (pair (const tt) snd)).comp snd).comp snd).to₂).of_eq $
λ n, begin
  simp [-nat.bodd_div2_eq],
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
    .comp (pair (snd.comp fst) (snd.comp snd))).to₂,
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

section
variables {α : Type*} {β : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable σ]

variable (H : nat.primrec (λ n, encodable.encode (decode (list β) n)))
include H
open primrec

private def prim : primcodable (list β) := ⟨H⟩

private lemma list_cases'
  {f : α → list β} {g : α → σ} {h : α → β × list β → σ}
  (hf : by haveI := prim H; exact primrec f) (hg : primrec g)
  (hh : by haveI := prim H; exact primrec₂ h) :
  @primrec _ σ _ _ (λ a, list.cases_on (f a) (g a) (λ b l, h a (b, l))) :=
by letI := prim H; exact
have @primrec _ (option σ) _ _ (λ a,
  (decode (option (β × list β)) (encode (f a))).map
  (λ o, option.cases_on o (g a) (h a))), from
((@map_decode_iff _ (option (β × list β)) _ _ _ _ _).2 $
    to₂ $ option_cases snd (hg.comp fst)
  (hh.comp₂ (fst.comp₂ primrec₂.left) primrec₂.right))
    .comp primrec.id (encode_iff.2 hf),
option_some_iff.1 $ this.of_eq $
λ a, by cases f a with b l; simp [encodek]; refl

private lemma list_foldl'
  {f : α → list β} {g : α → σ} {h : α → σ × β → σ}
  (hf : by haveI := prim H; exact primrec f) (hg : primrec g)
  (hh : by haveI := prim H; exact primrec₂ h) :
  primrec (λ a, (f a).foldl (λ s b, h a (s, b)) (g a)) :=
by letI := prim H; exact
let G (a : α) (IH : σ × list β) : σ × list β :=
  list.cases_on IH.2 IH (λ b l, (h a (IH.1, b), l)) in
let F (a : α) (n : ℕ) := (G a)^[n] (g a, f a) in
have primrec (λ a, (F a (encode (f a))).1), from
fst.comp $ nat_iterate (encode_iff.2 hf) (pair hg hf) $
  list_cases' H (snd.comp snd) snd $ to₂ $ pair
    (hh.comp (fst.comp fst) $
      pair ((fst.comp snd).comp fst) (fst.comp snd))
    (snd.comp snd),
this.of_eq $ λ a, begin
  have : ∀ n, F a n =
    ((list.take n (f a)).foldl (λ s b, h a (s, b)) (g a),
      list.drop n (f a)),
  { intro, simp [F],
    generalize : f a = l, generalize : g a = x,
    induction n with n IH generalizing l x, {refl},
    simp, cases l with b l; simp [IH] },
  rw [this, list.take_all_of_le (length_le_encode _)]
end

private lemma list_cons' : by haveI := prim H; exact primrec₂ (@list.cons β) :=
by letI := prim H; exact
encode_iff.1 (succ.comp $
primrec₂.mkpair.comp (encode_iff.2 fst) (encode_iff.2 snd))

private lemma list_reverse' : by haveI := prim H; exact
  primrec (@list.reverse β) :=
by letI := prim H; exact
(list_foldl' H primrec.id (const []) $ to₂ $
   ((list_cons' H).comp snd fst).comp snd).of_eq
(suffices ∀ l r, list.foldl (λ (s : list β) (b : β), b :: s) r l = list.reverse_core l r,
from λ l, this l [],
λ l, by induction l; simp [*, list.reverse_core])

end

namespace primcodable
variables {α : Type*} {β : Type*}
variables [primcodable α] [primcodable β]
open primrec

instance sum : primcodable (α ⊕ β) :=
⟨primrec.nat_iff.1 $
(encode_iff.2 (cond nat_bodd
  (((@primrec.decode β _).comp nat_div2).option_map $ to₂ $
     nat_bit.comp (const tt) (primrec.encode.comp snd))
  (((@primrec.decode α _).comp nat_div2).option_map $ to₂ $
     nat_bit.comp (const ff) (primrec.encode.comp snd)))).of_eq $
λ n, show _ = encode (decode_sum n), begin
  simp [decode_sum],
  cases nat.bodd n; simp [decode_sum],
  { cases decode α n.div2; refl },
  { cases decode β n.div2; refl }
end⟩

instance list : primcodable (list α) := ⟨
by letI H := primcodable.prim (list ℕ); exact
have primrec₂ (λ (a : α) (o : option (list ℕ)),
  o.map (list.cons (encode a))), from
option_map snd $
  (list_cons' H).comp ((@primrec.encode α _).comp (fst.comp fst)) snd,
have primrec (λ n, (of_nat (list ℕ) n).reverse.foldl
  (λ o m, (decode α m).bind (λ a, o.map (list.cons (encode a))))
   (some [])), from
list_foldl' H
  ((list_reverse' H).comp (primrec.of_nat (list ℕ)))
  (const (some []))
  (primrec.comp₂ (bind_decode_iff.2 $ primrec₂.swap this) primrec₂.right),
nat_iff.1 $ (encode_iff.2 this).of_eq $ λ n, begin
  rw list.foldl_reverse,
  apply nat.case_strong_induction_on n, { simp },
  intros n IH, simp,
  cases decode α n.unpair.1 with a, {refl},
  simp,
  suffices : ∀ (o : option (list ℕ)) p (_ : encode o = encode p),
    encode (option.map (list.cons (encode a)) o) =
    encode (option.map (list.cons a) p),
  from this _ _ (IH _ (nat.unpair_right_le n)),
  intros o p IH,
  cases o; cases p; injection IH with h,
  exact congr_arg (λ k, (nat.mkpair (encode a) k).succ.succ) h
end⟩

end primcodable

namespace primrec
variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ]

theorem sum_inl : primrec (@sum.inl α β) :=
encode_iff.1 $ nat_bit0.comp primrec.encode

theorem sum_inr : primrec (@sum.inr α β) :=
encode_iff.1 $ nat_bit1.comp primrec.encode

theorem sum_cases
  {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ → σ}
  (hf : primrec f) (hg : primrec₂ g) (hh : primrec₂ h) :
  @primrec _ σ _ _ (λ a, sum.cases_on (f a) (g a) (h a)) :=
option_some_iff.1 $
(cond (nat_bodd.comp $ encode_iff.2 hf)
  (option_map (primrec.decode.comp $ nat_div2.comp $ encode_iff.2 hf) hh)
  (option_map (primrec.decode.comp $ nat_div2.comp $ encode_iff.2 hf) hg)).of_eq $
λ a, by cases f a with b c;
  simp [nat.div2_bit, nat.bodd_bit, encodek]; refl

theorem list_cons : primrec₂ (@list.cons α) :=
list_cons' (primcodable.prim _)

theorem list_cases
  {f : α → list β} {g : α → σ} {h : α → β × list β → σ} :
  primrec f → primrec g → primrec₂ h →
  @primrec _ σ _ _ (λ a, list.cases_on (f a) (g a) (λ b l, h a (b, l))) :=
list_cases' (primcodable.prim _)

theorem list_foldl
  {f : α → list β} {g : α → σ} {h : α → σ × β → σ} :
  primrec f → primrec g → primrec₂ h →
  primrec (λ a, (f a).foldl (λ s b, h a (s, b)) (g a)) :=
list_foldl' (primcodable.prim _)

theorem list_reverse : primrec (@list.reverse α) :=
list_reverse' (primcodable.prim _)

theorem list_foldr
  {f : α → list β} {g : α → σ} {h : α → β × σ → σ}
  (hf : primrec f) (hg : primrec g) (hh : primrec₂ h) :
  primrec (λ a, (f a).foldr (λ b s, h a (b, s)) (g a)) :=
(list_foldl (list_reverse.comp hf) hg $ to₂ $
  hh.comp fst $ (pair snd fst).comp snd).of_eq $
λ a, by simp [list.foldl_reverse]

theorem list_head' : primrec (@list.head' α) :=
(list_cases primrec.id (const none)
  (option_some_iff.2 $ (fst.comp snd)).to₂).of_eq $
λ l, by cases l; refl

theorem list_head [inhabited α] : primrec (@list.head α _) :=
(option_iget.comp list_head').of_eq $
λ l, l.head_eq_head'.symm

theorem list_tail : primrec (@list.tail α) :=
(list_cases primrec.id (const []) (snd.comp snd).to₂).of_eq $
λ l, by cases l; refl

theorem list_rec
  {f : α → list β} {g : α → σ} {h : α → β × list β × σ → σ}
  (hf : primrec f) (hg : primrec g) (hh : primrec₂ h) :
  @primrec _ σ _ _ (λ a,
    list.rec_on (f a) (g a) (λ b l IH, h a (b, l, IH))) :=
let F (a : α) := (f a).foldr
  (λ (b : β) (s : list β × σ), (b :: s.1, h a (b, s))) ([], g a) in
have primrec F, from
list_foldr hf (pair (const []) hg) $ to₂ $
  pair ((list_cons.comp fst (fst.comp snd)).comp snd) hh,
(snd.comp this).of_eq $ λ a, begin
  suffices : F a = (f a,
    list.rec_on (f a) (g a) (λ b l IH, h a (b, l, IH))), {rw this},
  simp [F], induction f a with b l IH; simp *
end

theorem list_nth : primrec₂ (@list.nth α) :=
let F (l : list α) (n : ℕ) :=
l.foldl (λ (s : ℕ ⊕ α) (a : α),
  sum.cases_on s
    (@nat.cases (ℕ ⊕ α) (sum.inr a) sum.inl) sum.inr)
  (sum.inl n) in
have hF : primrec₂ F, from
list_foldl fst (sum_inl.comp snd) ((sum_cases fst
  (nat_cases snd
    (sum_inr.comp $ snd.comp fst)
    (sum_inl.comp snd).to₂).to₂
  (sum_inr.comp snd).to₂).comp snd).to₂,
have @primrec _ (option α) _ _ (λ p : list α × ℕ,
  sum.cases_on (F p.1 p.2) (λ _, none) some), from
sum_cases hF (const none).to₂ (option_some.comp snd).to₂,
this.to₂.of_eq $ λ l n, begin
  dsimp, symmetry,
  induction l with a l IH generalizing n, {refl},
  cases n with n,
  { rw [(_ : F (a :: l) 0 = sum.inr a)], {refl},
    clear IH, dsimp [F],
    induction l with b l IH; simp * },
  { apply IH }
end

theorem list_inth [inhabited α] : primrec₂ (@list.inth α _) :=
option_iget.comp₂ list_nth

theorem list_append : primrec₂ ((++) : list α → list α → list α) :=
(list_foldr fst snd $ to₂ $ comp (@list_cons α _) snd).to₂.of_eq $
λ l₁ l₂, by induction l₁; simp *

theorem list_concat : primrec₂ (λ l (a:α), l ++ [a]) :=
list_append.comp fst (list_cons.comp snd (const []))

theorem list_map
  {f : α → list β} {g : α → β → σ}
  (hf : primrec f) (hg : primrec₂ g) :
  primrec (λ a, (f a).map (g a)) :=
(list_foldr hf (const []) $ to₂ $ list_cons.comp
  (hg.comp fst (fst.comp snd)) (snd.comp snd)).of_eq $
λ a, by induction f a; simp *

theorem list_range : primrec list.range :=
(nat_elim' primrec.id (const [])
  ((list_concat.comp snd fst).comp snd).to₂).of_eq $
λ n, by simp; induction n; simp [*, list.range_succ]; refl

theorem list_join : primrec (@list.join α) :=
(list_foldr primrec.id (const []) $ to₂ $
  comp (@list_append α _) snd).of_eq $
λ l, by dsimp; induction l; simp *

theorem list_length : primrec (@list.length α) :=
(list_foldr (@primrec.id (list α) _) (const 0) $ to₂ $
  (succ.comp $ snd.comp snd).to₂).of_eq $
λ l, by dsimp; induction l; simp [*, -add_comm]

theorem list_find_index {f : α → list β} {p : α → β → Prop}
  [∀ a b, decidable (p a b)]
  (hf : primrec f) (hp : primrec_rel p) :
  primrec (λ a, (f a).find_index (p a)) :=
(list_foldr hf (const 0) $ to₂ $
  ite (hp.comp fst $ fst.comp snd) (const 0)
    (succ.comp $ snd.comp snd)).of_eq $
λ a, eq.symm $ by dsimp; induction f a with b l;
  [refl, simp [*, list.find_index]]

theorem list_index_of [decidable_eq α] : primrec₂ (@list.index_of α _) :=
to₂ $ list_find_index snd $ primrec.eq.comp₂ (fst.comp fst).to₂ snd.to₂

theorem nat_strong_rec
  (f : α → ℕ → σ) {g : α → list σ → option σ} (hg : primrec₂ g)
  (H : ∀ a n, g a ((list.range n).map (f a)) = some (f a n)) : primrec₂ f :=
suffices primrec₂ (λ a n, (list.range n).map (f a)), from
  primrec₂.option_some_iff.1 $
  (list_nth.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq $
  λ a n, by simp [list.nth_range (nat.lt_succ_self n)]; refl,
primrec₂.option_some_iff.1 $
(nat_elim (const (some [])) (to₂ $
  option_bind (snd.comp snd) $ to₂ $
  option_map
    (hg.comp (fst.comp fst) snd)
    (to₂ $ list_concat.comp (snd.comp fst) snd))).of_eq $
λ a n, begin
  simp, induction n with n IH, {refl},
  simp [IH, H, list.range_succ]
end

end primrec

namespace primcodable
variables {α : Type*} {β : Type*}
variables [primcodable α] [primcodable β]
open primrec

def subtype {p : α → Prop} [decidable_pred p]
  (hp : primrec_pred p) : primcodable (subtype p) :=
⟨have primrec (λ n, (decode α n).bind (λ a, option.guard p a)),
 from option_bind primrec.decode (option_guard (hp.comp snd) snd),
 nat_iff.1 $ (encode_iff.2 this).of_eq $ λ n,
 show _ = encode ((decode α n).bind (λ a, _)), begin
   cases decode α n with a, {refl},
   dsimp [option.guard],
   by_cases h : p a; simp [h]; refl
 end⟩

instance fin {n} : primcodable (fin n) :=
@of_equiv _ _
  (subtype $ nat_lt.comp primrec.id (const n))
  (equiv.fin_equiv_subtype _)

instance vector {n} : primcodable (vector α n) :=
subtype ((@primrec.eq _ _ nat.decidable_eq).comp list_length (const _))

instance fin_arrow {n} : primcodable (fin n → α) :=
of_equiv _ (equiv.vector_equiv_fin _ _).symm

instance array {n} : primcodable (array n α) :=
of_equiv _ (equiv.array_equiv_fin _ _)

section ulower
local attribute [instance, priority 100]
  encodable.decidable_range_encode encodable.decidable_eq_of_encodable

instance ulower : primcodable (ulower α) :=
have primrec_pred (λ n, encodable.decode₂ α n ≠ none),
from primrec.not (primrec.eq.comp (primrec.option_bind primrec.decode
  (primrec.ite (primrec.eq.comp (primrec.encode.comp primrec.snd) primrec.fst)
    (primrec.option_some.comp primrec.snd) (primrec.const _))) (primrec.const _)),
primcodable.subtype $
  primrec_pred.of_eq this (λ n, decode₂_ne_none_iff)

end ulower

end primcodable

namespace primrec
variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ]

theorem subtype_val {p : α → Prop} [decidable_pred p]
  {hp : primrec_pred p} :
  by haveI := primcodable.subtype hp; exact
  primrec (@subtype.val α p) :=
begin
  letI := primcodable.subtype hp,
  refine (primcodable.prim (subtype p)).of_eq (λ n, _),
  rcases decode (subtype p) n with _|⟨a,h⟩; refl
end

theorem subtype_val_iff {p : β → Prop} [decidable_pred p]
  {hp : primrec_pred p} {f : α → subtype p} :
  by haveI := primcodable.subtype hp; exact
  primrec (λ a, (f a).1) ↔ primrec f :=
begin
  letI := primcodable.subtype hp,
  refine ⟨λ h, _, λ hf, subtype_val.comp hf⟩,
  refine nat.primrec.of_eq h (λ n, _),
  cases decode α n with a, {refl},
  simp, cases f a; refl
end

theorem subtype_mk {p : β → Prop} [decidable_pred p] {hp : primrec_pred p}
  {f : α → β} {h : ∀ a, p (f a)} (hf : primrec f) :
  by haveI := primcodable.subtype hp; exact
  primrec (λ a, @subtype.mk β p (f a) (h a)) :=
subtype_val_iff.1 hf

theorem option_get {f : α → option β} {h : ∀ a, (f a).is_some} :
  primrec f → primrec (λ a, option.get (h a)) :=
begin
  intro hf,
  refine (nat.primrec.pred.comp hf).of_eq (λ n, _),
  generalize hx : decode α n = x,
  cases x; simp
end

theorem ulower_down : primrec (ulower.down : α → ulower α) :=
by letI : ∀ a, decidable (a ∈ set.range (encode : α → ℕ)) := decidable_range_encode _; exact
subtype_mk primrec.encode

theorem ulower_up : primrec (ulower.up : ulower α → α) :=
by letI : ∀ a, decidable (a ∈ set.range (encode : α → ℕ)) := decidable_range_encode _; exact
option_get (primrec.decode₂.comp subtype_val)

theorem fin_val_iff {n} {f : α → fin n} :
  primrec (λ a, (f a).1) ↔ primrec f :=
begin
  let : primcodable {a//id a<n}, swap,
  exactI (iff.trans (by refl) subtype_val_iff).trans (of_equiv_iff _)
end

theorem fin_val {n} : primrec (coe : fin n → ℕ) := fin_val_iff.2 primrec.id

theorem fin_succ {n} : primrec (@fin.succ n) :=
fin_val_iff.1 $ by simp [succ.comp fin_val]

theorem vector_to_list {n} : primrec (@vector.to_list α n) := subtype_val

theorem vector_to_list_iff {n} {f : α → vector β n} :
  primrec (λ a, (f a).to_list) ↔ primrec f := subtype_val_iff

theorem vector_cons {n} : primrec₂ (@vector.cons α n) :=
vector_to_list_iff.1 $ by simp; exact
list_cons.comp fst (vector_to_list_iff.2 snd)

theorem vector_length {n} : primrec (@vector.length α n) := const _

theorem vector_head {n} : primrec (@vector.head α n) :=
option_some_iff.1 $
(list_head'.comp vector_to_list).of_eq $ λ ⟨a::l, h⟩, rfl

theorem vector_tail {n} : primrec (@vector.tail α n) :=
vector_to_list_iff.1 $ (list_tail.comp vector_to_list).of_eq $
λ ⟨l, h⟩, by cases l; refl

theorem vector_nth {n} : primrec₂ (@vector.nth α n) :=
option_some_iff.1 $
(list_nth.comp (vector_to_list.comp fst) (fin_val.comp snd)).of_eq $
λ a, by simp [vector.nth_eq_nth_le]; rw [← list.nth_le_nth]

theorem list_of_fn : ∀ {n} {f : fin n → α → σ},
  (∀ i, primrec (f i)) → primrec (λ a, list.of_fn (λ i, f i a))
| 0     f hf := const []
| (n+1) f hf := by simp [list.of_fn_succ]; exact
  list_cons.comp (hf 0) (list_of_fn (λ i, hf i.succ))

theorem vector_of_fn {n} {f : fin n → α → σ}
  (hf : ∀ i, primrec (f i)) : primrec (λ a, vector.of_fn (λ i, f i a)) :=
vector_to_list_iff.1 $ by simp [list_of_fn hf]

theorem vector_nth' {n} : primrec (@vector.nth α n) := of_equiv_symm

theorem vector_of_fn' {n} : primrec (@vector.of_fn α n) := of_equiv

theorem fin_app {n} : primrec₂ (@id (fin n → σ)) :=
(vector_nth.comp (vector_of_fn'.comp fst) snd).of_eq $
λ ⟨v, i⟩, by simp

theorem fin_curry₁ {n} {f : fin n → α → σ} : primrec₂ f ↔ ∀ i, primrec (f i) :=
⟨λ h i, h.comp (const i) primrec.id,
 λ h, (vector_nth.comp ((vector_of_fn h).comp snd) fst).of_eq $ λ a, by simp⟩

theorem fin_curry {n} {f : α → fin n → σ} : primrec f ↔ primrec₂ f :=
⟨λ h, fin_app.comp (h.comp fst) snd,
 λ h, (vector_nth'.comp (vector_of_fn (λ i,
    show primrec (λ a, f a i), from
    h.comp primrec.id (const i)))).of_eq $
  λ a, by funext i; simp⟩

end primrec

namespace nat
open vector

/-- An alternative inductive definition of `primrec` which
  does not use the pairing function on ℕ, and so has to
  work with n-ary functions on ℕ instead of unary functions.
  We prove that this is equivalent to the regular notion
  in `to_prim` and `of_prim`. -/
inductive primrec' : ∀ {n}, (vector ℕ n → ℕ) → Prop
| zero : @primrec' 0 (λ _, 0)
| succ : @primrec' 1 (λ v, succ v.head)
| nth {n} (i : fin n) : primrec' (λ v, v.nth i)
| comp {m n f} (g : fin n → vector ℕ m → ℕ) :
  primrec' f → (∀ i, primrec' (g i)) →
  primrec' (λ a, f (of_fn (λ i, g i a)))
| prec {n f g} : @primrec' n f → @primrec' (n+2) g →
  primrec' (λ v : vector ℕ (n+1),
    v.head.elim (f v.tail) (λ y IH, g (y ::ᵥ IH ::ᵥ v.tail)))

end nat

namespace nat.primrec'
open vector primrec nat (primrec') nat.primrec'
hide ite

theorem to_prim {n f} (pf : @primrec' n f) : primrec f :=
begin
  induction pf,
  case nat.primrec'.zero { exact const 0 },
  case nat.primrec'.succ { exact primrec.succ.comp vector_head },
  case nat.primrec'.nth : n i {
    exact vector_nth.comp primrec.id (const i) },
  case nat.primrec'.comp : m n f g _ _ hf hg {
    exact hf.comp (vector_of_fn (λ i, hg i)) },
  case nat.primrec'.prec : n f g _ _ hf hg {
    exact nat_elim' vector_head (hf.comp vector_tail) (hg.comp $
      vector_cons.comp (fst.comp snd) $
      vector_cons.comp (snd.comp snd) $
      (@vector_tail _ _ (n+1)).comp fst).to₂ },
end

theorem of_eq {n} {f g : vector ℕ n → ℕ}
  (hf : primrec' f) (H : ∀ i, f i = g i) : primrec' g :=
(funext H : f = g) ▸ hf

theorem const {n} : ∀ m, @primrec' n (λ v, m)
| 0     := zero.comp fin.elim0 (λ i, i.elim0)
| (m+1) := succ.comp _ (λ i, const m)

theorem head {n : ℕ} : @primrec' n.succ head :=
(nth 0).of_eq $ λ v, by simp [nth_zero]

theorem tail {n f} (hf : @primrec' n f) : @primrec' n.succ (λ v, f v.tail) :=
(hf.comp _ (λ i, @nth _ i.succ)).of_eq $
λ v, by rw [← of_fn_nth v.tail]; congr; funext i; simp

def vec {n m} (f : vector ℕ n → vector ℕ m) :=
∀ i, primrec' (λ v, (f v).nth i)

protected theorem nil {n} : @vec n 0 (λ _, nil) := λ i, i.elim0

protected theorem cons {n m f g}
  (hf : @primrec' n f) (hg : @vec n m g) :
  vec (λ v, (f v ::ᵥ g v)) :=
λ i, fin.cases (by simp *) (λ i, by simp [hg i]) i

theorem idv {n} : @vec n n id := nth

theorem comp' {n m f g}
  (hf : @primrec' m f) (hg : @vec n m g) :
  primrec' (λ v, f (g v)) :=
(hf.comp _ hg).of_eq $ λ v, by simp

theorem comp₁ (f : ℕ → ℕ) (hf : @primrec' 1 (λ v, f v.head))
  {n g} (hg : @primrec' n g) : primrec' (λ v, f (g v)) :=
hf.comp _ (λ i, hg)

theorem comp₂ (f : ℕ → ℕ → ℕ)
  (hf : @primrec' 2 (λ v, f v.head v.tail.head))
  {n g h} (hg : @primrec' n g) (hh : @primrec' n h) :
  primrec' (λ v, f (g v) (h v)) :=
by simpa using hf.comp' (hg.cons $ hh.cons primrec'.nil)

theorem prec' {n f g h}
  (hf : @primrec' n f) (hg : @primrec' n g) (hh : @primrec' (n+2) h) :
  @primrec' n (λ v, (f v).elim (g v)
    (λ (y IH : ℕ), h (y ::ᵥ IH ::ᵥ v))) :=
by simpa using comp' (prec hg hh) (hf.cons idv)

theorem pred : @primrec' 1 (λ v, v.head.pred) :=
(prec' head (const 0) head).of_eq $
λ v, by simp; cases v.head; refl

theorem add : @primrec' 2 (λ v, v.head + v.tail.head) :=
(prec head (succ.comp₁ _ (tail head))).of_eq $
λ v, by simp; induction v.head; simp [*, nat.succ_add]

theorem sub : @primrec' 2 (λ v, v.head - v.tail.head) :=
begin
  suffices, simpa using comp₂ (λ a b, b - a) this (tail head) head,
  refine (prec head (pred.comp₁ _ (tail head))).of_eq (λ v, _),
  simp, induction v.head; simp [*, nat.sub_succ]
end

theorem mul : @primrec' 2 (λ v, v.head * v.tail.head) :=
(prec (const 0) (tail (add.comp₂ _ (tail head) (head)))).of_eq $
λ v, by simp; induction v.head; simp [*, nat.succ_mul]; rw add_comm

theorem if_lt {n a b f g}
  (ha : @primrec' n a) (hb : @primrec' n b)
  (hf : @primrec' n f) (hg : @primrec' n g) :
  @primrec' n (λ v, if a v < b v then f v else g v) :=
(prec' (sub.comp₂ _ hb ha) hg (tail $ tail hf)).of_eq $
λ v, begin
  cases e : b v - a v,
  { simp [not_lt.2 (nat.le_of_sub_eq_zero e)] },
  { simp [nat.lt_of_sub_eq_succ e] }
end

theorem mkpair : @primrec' 2 (λ v, v.head.mkpair v.tail.head) :=
if_lt head (tail head)
  (add.comp₂ _ (tail $ mul.comp₂ _ head head) head)
  (add.comp₂ _ (add.comp₂ _
    (mul.comp₂ _ head head) head) (tail head))

protected theorem encode : ∀ {n}, @primrec' n encode
| 0     := (const 0).of_eq (λ v, by rw v.eq_nil; refl)
| (n+1) := (succ.comp₁ _ (mkpair.comp₂ _ head (tail encode)))
  .of_eq $ λ ⟨a::l, e⟩, rfl

theorem sqrt : @primrec' 1 (λ v, v.head.sqrt) :=
begin
  suffices H : ∀ n : ℕ, n.sqrt = n.elim 0 (λ x y,
    if x.succ < y.succ*y.succ then y else y.succ),
  { simp [H],
    have := @prec' 1 _ _ (λ v,
      by have x := v.head; have y := v.tail.head; from
      if x.succ < y.succ*y.succ then y else y.succ) head (const 0) _,
    { convert this, funext, congr, funext x y, congr; simp },
    have x1 := succ.comp₁ _ head,
    have y1 := succ.comp₁ _ (tail head),
    exact if_lt x1 (mul.comp₂ _ y1 y1) (tail head) y1 },
  intro, symmetry,
  induction n with n IH, {simp},
  dsimp, rw IH, split_ifs,
  { exact le_antisymm (nat.sqrt_le_sqrt (nat.le_succ _))
      (nat.lt_succ_iff.1 $ nat.sqrt_lt.2 h) },
  { exact nat.eq_sqrt.2 ⟨not_lt.1 h, nat.sqrt_lt.1 $
      nat.lt_succ_iff.2 $ nat.sqrt_succ_le_succ_sqrt _⟩ },
end

theorem unpair₁ {n f} (hf : @primrec' n f) :
  @primrec' n (λ v, (f v).unpair.1) :=
begin
  have s := sqrt.comp₁ _ hf,
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s),
  refine (if_lt fss s fss s).of_eq (λ v, _),
  simp [nat.unpair], split_ifs; refl
end

theorem unpair₂ {n f} (hf : @primrec' n f) :
  @primrec' n (λ v, (f v).unpair.2) :=
begin
  have s := sqrt.comp₁ _ hf,
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s),
  refine (if_lt fss s s (sub.comp₂ _ fss s)).of_eq (λ v, _),
  simp [nat.unpair], split_ifs; refl
end

theorem of_prim : ∀ {n f}, primrec f → @primrec' n f :=
suffices ∀ f, nat.primrec f → @primrec' 1 (λ v, f v.head), from
λ n f hf, (pred.comp₁ _ $ (this _ hf).comp₁
  (λ m, encodable.encode $ (decode (vector ℕ n) m).map f)
    primrec'.encode).of_eq (λ i, by simp [encodek]),
λ f hf, begin
  induction hf,
  case nat.primrec.zero { exact const 0 },
  case nat.primrec.succ { exact succ },
  case nat.primrec.left { exact unpair₁ head },
  case nat.primrec.right { exact unpair₂ head },
  case nat.primrec.pair : f g _ _ hf hg {
    exact mkpair.comp₂ _ hf hg },
  case nat.primrec.comp : f g _ _ hf hg {
    exact hf.comp₁ _ hg },
  case nat.primrec.prec : f g _ _ hf hg {
    simpa using prec' (unpair₂ head)
      (hf.comp₁ _ (unpair₁ head))
      (hg.comp₁ _ $ mkpair.comp₂ _ (unpair₁ $ tail $ tail head)
        (mkpair.comp₂ _ head (tail head))) },
end

theorem prim_iff {n f} : @primrec' n f ↔ primrec f := ⟨to_prim, of_prim⟩

theorem prim_iff₁ {f : ℕ → ℕ} :
  @primrec' 1 (λ v, f v.head) ↔ primrec f :=
prim_iff.trans ⟨
  λ h, (h.comp $ vector_of_fn $ λ i, primrec.id).of_eq (λ v, by simp),
  λ h, h.comp vector_head⟩

theorem prim_iff₂ {f : ℕ → ℕ → ℕ} :
  @primrec' 2 (λ v, f v.head v.tail.head) ↔ primrec₂ f :=
prim_iff.trans ⟨
  λ h, (h.comp $ vector_cons.comp fst $
    vector_cons.comp snd (primrec.const nil)).of_eq (λ v, by simp),
  λ h, h.comp vector_head (vector_head.comp vector_tail)⟩

theorem vec_iff {m n f} :
  @vec m n f ↔ primrec f :=
⟨λ h, by simpa using vector_of_fn (λ i, to_prim (h i)),
 λ h i, of_prim $ vector_nth.comp h (primrec.const i)⟩

end nat.primrec'

theorem primrec.nat_sqrt : primrec nat.sqrt :=
nat.primrec'.prim_iff₁.1 nat.primrec'.sqrt
