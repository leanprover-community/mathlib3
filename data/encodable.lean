/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Type class for encodable Types.
Note that every encodable Type is countable.
-/
import data.finset data.list data.list.perm data.list.sort data.equiv data.nat.basic
open option list nat function

class encodable (α : Type*) :=
(encode : α → nat) (decode : nat → option α) (encodek : ∀ a, decode (encode a) = some a)

@[simp] lemma succ_ne_zero {n : ℕ} : succ n ≠ 0 :=
assume h, nat.no_confusion h

section encodable
variables {α : Type*} {β : Type*}

open encodable

/-
def countable_of_encodable {α : Type*} : encodable α → countable α :=
assume e : encodable α,
have injective encode, from
  λ (a₁ a₂ : α) (h : encode a₁ = encode a₂),
    have decode α (encode a₁) = decode α (encode a₂), by rewrite h,
    by rewrite [*encodek at this]; injection this; assumption,
exists.intro encode this

def encodable_finType* [instance] {α : Type*} [h₁ : finType* α] [h₂ : decidable_eq α] :
  encodable α :=
encodable.mk
  (λ a, find a (elements_of α))
  (λ n, nth (elements_of α) n)
  (λ a, find_nth (finType*.complete a))
-/

instance encodable_nat : encodable nat :=
encodable.mk (λ a, a) (λ n, some n) (λ a, rfl)

instance encodable_option {α : Type*} [h : encodable α] : encodable (option α) :=
encodable.mk
  (λ o, match o with
        | some a := succ (encode a)
        | none := 0
        end)
  (λ n, if n = 0 then some none else some (decode α (pred n)))
  (λ o, by cases o; simp [encodable_option._match_1, encodek])

section sum
variables [h₁ : encodable α] [h₂ : encodable β]
include h₁ h₂

-- TODO: should be private, but simplifier does not support private equation lemmas
protected def encode_sum : sum α β → nat
| (sum.inl a) := 2 * encode a
| (sum.inr b) := 2 * encode b + 1

-- TODO: should be private, but simplifier does not support private equation lemmas
protected def decode_sum (n : nat) : option (sum α β) :=
if n % 2 = 0 then
   match decode α (n / 2) with
   | some a := some (sum.inl a)
   | none   := none
   end
else
   match decode β ((n - 1) / 2) with
   | some b := some (sum.inr b)
   | none   := none
   end

open decidable
private theorem decode_encode_sum : ∀ s : sum α β, decode_sum (encode_sum s) = some s
| (sum.inl a) :=
  have aux : 2 > (0:nat), from dec_trivial,
  begin
    simp [encode_sum, decode_sum, encodek, -mul_comm],
    rw [nat.mul_div_cancel_left _ aux, encodek],
    refl
  end
| (sum.inr b) :=
  have aux₁ : 2 > (0:nat),     from dec_trivial,
  have aux₂ : 1 % 2 = (1:nat), from dec_trivial,
  have aux₃ : 1 ≠ (0:nat),     from dec_trivial,
  by simp [encode_sum, decode_sum, *, nat.add_sub_cancel_left, encodek]

instance encodable_sum : encodable (sum α β) :=
encodable.mk
  (λ s, encode_sum s)
  (λ n, decode_sum n)
  (λ s, decode_encode_sum s)
end sum

section prod
variables [h₁ : encodable α] [h₂ : encodable β]
include h₁ h₂

-- TODO: should be private, but simplifier does not support private equation lemmas
protected def encode_prod : α × β → nat
| (a, b) := mkpair (encode a) (encode b)

-- TODO: should be private, but simplifier does not support private equation lemmas
protected def decode_prod (n : nat) : option (α × β) :=
match unpair n with
| (n₁, n₂) :=
  match decode α n₁ with
  | some a :=
    match decode β n₂ with
    | some b := some (a, b)
    | none   := none
    end
  | none   := none
  end
end

private theorem decode_encode_prod : ∀ p : α × β, decode_prod (encode_prod p) = some p
| (a, b) := by simp [encode_prod, decode_prod, unpair_mkpair, encodek]

instance encodable_product : encodable (α × β) :=
encodable.mk
  encode_prod
  decode_prod
  decode_encode_prod
end prod

section list
variables [h : encodable α]
include h

private def encode_list_core : list α → nat
| []     := 0
| (a::l) := mkpair (encode a) (encode_list_core l)

private theorem encode_list_core_cons (a : α) (l : list α) :
  encode_list_core (a::l) = mkpair (encode a) (encode_list_core l) :=
rfl

private def encode_list (l : list α) : nat :=
mkpair (length l) (encode_list_core l)

private def decode_list_core : nat → nat → option (list α)
| 0        v  := some []
| (succ n) v  :=
  match unpair v with
  | (v₁, v₂) :=
    match decode α v₁ with
    | some a :=
      match decode_list_core n v₂ with
      | some l := some (a::l)
      | none   := none
      end
    | none   := none
    end
  end

private theorem decode_list_core_succ (n v : nat) :
  decode_list_core (succ n) v =
    match unpair v with
    | (v₁, v₂) :=
      match decode α v₁ with
      | some a :=
        match decode_list_core n v₂ with
        | some l := some (a::l)
        | none   := none
        end
      | none   := none
      end
    end
:= rfl

private def decode_list (n : nat) : option (list α) :=
match unpair n with
| (l, v) := decode_list_core l v
end

private theorem decode_encode_list_core :
  ∀ l : list α, decode_list_core (length l) (encode_list_core l) = some l
| []     := rfl
| (a::l) :=
  begin
    simp [encode_list_core_cons, length_cons, add_one (length l), decode_list_core_succ,
      unpair_mkpair, encodek, decode_encode_list_core l],
    rw [unpair_mkpair], -- TODO: check why the simplifier does not rewrite this!
    simp,
    rewrite [decode_encode_list_core l],
    rewrite [encodable.encodek],
  end

private theorem decode_encode_list (l : list α) : decode_list (encode_list l) = some l :=
begin
  simp [encode_list, decode_list],
  rewrite [unpair_mkpair],
  apply decode_encode_list_core
end

instance encodable_list : encodable (list α) :=
encodable.mk
  encode_list
  decode_list
  decode_encode_list
end list

section finset
variable [encA : encodable α]
include encA

private def enle (a b : α) : Prop := encode a ≤ encode b

private lemma enle.refl (a : α) : enle a a :=
le_refl _

private lemma enle.trans (a b c : α) : enle a b → enle b c → enle a c :=
assume h₁ h₂, le_trans h₁ h₂

private lemma enle.total (a b : α) : enle a b ∨ enle b a :=
le_total _ _

private lemma enle.antisymm (a b : α) : enle a b → enle b a → a = b :=
assume h₁ h₂,
have encode a = encode b, from le_antisymm h₁ h₂,
have decode α (encode a) = decode α (encode b), by rewrite this,
have some a = some b, by rewrite [encodek, encodek] at this; exact this,
option.no_confusion this (λ e, e)

private def decidable_enle (a b : α) : decidable (enle a b) :=
show decidable (encode a ≤ encode b), by apply_instance

local attribute [instance] decidable_enle

variables [decA : decidable_eq α]
include decA

private def ensort (l : list α) : list α :=
insertion_sort enle l

open subtype list.perm

private lemma sorted_eq_of_perm {l₁ l₂ : list α} (h : l₁ ~ l₂) : ensort l₁ = ensort l₂ :=
eq_of_sorted_of_perm _ enle.trans enle.antisymm
  (perm.trans (perm_insertion_sort _ _) $ perm.trans h (perm_insertion_sort _ _).symm)
  (sorted_insertion_sort _ enle.total enle.trans _)
  (sorted_insertion_sort _ enle.total enle.trans _)

private def encode_finset (s : finset α) : nat :=
quot.lift_on s
  (λ l, encode (ensort l.val))
  (λ l₁ l₂ p,
    have l₁.val ~ l₂.val,               from p,
    have ensort l₁.val = ensort l₂.val, from sorted_eq_of_perm this,
    by dsimp; rewrite this)

private def decode_finset (n : nat) : option (finset α) :=
match decode (list α) n with
| some l₁ := some (finset.to_finset l₁)
| none    := none
end

private theorem decode_encode_finset (s : finset α) : decode_finset (encode_finset s) = some s :=
quot.induction_on s (λ⟨l, nd⟩,
  begin
    simp [encode_finset],
    show decode_finset (encode (ensort l)) = some (quot.mk setoid.r ⟨l, nd⟩),
    simp [decode_finset, encodek],
    apply congr_arg some,
    apply quot.sound,
    show erase_dup (ensort l) ~ l, from
      have nodup (ensort l), from nodup_of_perm_of_nodup (perm.symm $ perm_insertion_sort _ _) nd,
      calc erase_dup (ensort l) = ensort l : erase_dup_eq_of_nodup this
                ...             ~ l        : perm_insertion_sort _ _
  end)

instance encodable_finset : encodable (finset α) :=
encodable.mk
  encode_finset
  decode_finset
  decode_encode_finset
end finset

section subtype
open subtype decidable
variable {P : α → Prop}
variable [encA : encodable α]
variable [decP : decidable_pred P]

include encA
-- TODO: should be private, but simplifier does not support private equation lemmas
protected def encode_subtype : {a : α // P a} → nat
| ⟨v, h⟩ := encode v

include decP
-- TODO: should be private, but simplifier does not support private equation lemmas
protected def decode_subtype (v : nat) : option {a : α // P a} :=
match decode α v with
| some a := if h : P a then some ⟨a, h⟩ else none
| none   := none
end

private lemma decode_encode_subtype : ∀ s : {a : α // P a}, decode_subtype (encode_subtype s) = some s
| ⟨v, h⟩ := by simp [encode_subtype, decode_subtype, encodek, h]

instance encodable_subtype : encodable {a : α // P a} :=
encodable.mk
  encode_subtype
  decode_subtype
  decode_encode_subtype
end subtype

def encodable_of_left_injection [h₁ : encodable α]
  (f : β → α) (finv : α → option β) (linv : ∀ b, finv (f b) = some b) : encodable β :=
encodable.mk
  (λ b, encode (f b))
  (λ n,
    match decode α n with
    | some a := finv a
    | none   := none
    end)
  (λ b, by simp [encodable.encodek, encodable_of_left_injection._match_1, linv])

section
open equiv

def encodable_of_equiv [h : encodable α] : α ≃ β → encodable β
| (mk f g l r) :=
  encodable_of_left_injection g (λ a, some (f a))
    (λ b, by rewrite r; reflexivity)
end

end encodable

/-
Choice function for encodable types and decidable predicates.
We provide the following API

choose      {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] : (∃ x, p x) → α :=
choose_spec {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] (ex : ∃ x, p x) : p (choose ex) :=
-/

namespace encodable
section find_a
parameters {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p]
include c d

open encodable

def pn (n : nat) : Prop :=
match decode α n with
| some a := p a
| none   := false
end

private lemma pn_of_some {a : α} {n : ℕ} (h : decode α n = some a) : pn n ↔ p a :=
by simp [pn, h]

private def decidable_pn : decidable_pred pn :=
assume n,
begin
  cases h : decode α n,
  { simp [pn, h],
    exact decidable.is_false id },
  { simp [pn_of_some h],
    apply_instance }
end
local attribute [instance] decidable_pn

private def ex_pn_of_ex : (∃ a, p a) → (∃ n, pn n)
| ⟨w, (pw : p w)⟩ := ⟨encode w, by simp [pn, encodek, *]⟩

private lemma decode_ne_none_of_pn {n : nat} (h : pn n) : decode α n ≠ none :=
begin
  cases h' : decode α n,
  { simp [pn, h'] at h, contradiction },
  { contradiction }
end

private def choose' (h : ∃ x, p x) : {a:α // p a} :=
let n := nat.find $ ex_pn_of_ex $ h in
begin
  cases h' : decode α n,
  { exact absurd h' (@decode_ne_none_of_pn α p c d n $ nat.find_spec _) },
  { have : pn n, from nat.find_spec _,
    exact ⟨a, by simp [pn_of_some h'] at this; assumption⟩ }
end

def choose : (∃ x, p x) → α := subtype.val ∘ choose'

lemma choose_spec (h : ∃ x, p x) : p (choose h) := subtype.property _

end find_a

theorem axiom_of_choice {α : Type*} {β : α → Type*} {R : Π x, β x → Prop}
  [c : Π a, encodable (β a)] [d : ∀ x y, decidable (R x y)] :
  (∀x, ∃y, R x y) → ∃f:Πa, β a, ∀x, R x (f x) :=
assume H,
have ∀x, R x (choose (H x)), from assume x, choose_spec (H x),
exists.intro _ this

theorem skolem {α : Type*} {β : α → Type*} {P : Π x, β x → Prop}
  [c : Π a, encodable (β a)] [d : ∀ x y, decidable (P x y)] :
  (∀x, ∃y, P x y) ↔ ∃f:Πa, β a, (∀x, P x (f x)) :=
iff.intro
  (assume : (∀ x, ∃y, P x y), axiom_of_choice this)
  (assume : (∃ f:Πa, β a, (∀x, P x (f x))),
   assume x, let ⟨(fw : ∀x, β x), Hw⟩ := this in exists.intro (fw x) (Hw x))

end encodable

namespace quot
section
open setoid encodable
parameter {α : Type*}
parameter {s : setoid α}
parameter [decR : ∀ a b : α, decidable (a ≈ b)]
parameter [encA : encodable α]
include decR
include encA

-- Choose equivalence class representative
def rep (q : quotient s) : α :=
choose (exists_rep q)

theorem rep_spec (q : quotient s) : ⟦rep q⟧ = q :=
choose_spec (exists_rep q)

private def encode_quot (q : quotient s) : nat :=
encode (rep q)

private def decode_quot (n : nat) : option (quotient s) :=
match decode α n with
| some a := some ⟦ a ⟧
| none   := none
end

private lemma decode_encode_quot (q : quotient s) : decode_quot (encode_quot q) = some q :=
quot.induction_on q $ λ l,
  begin
    dsimp [encode_quot, decode_quot],
    simp [encodek],
    exact congr_arg some (rep_spec _)
  end

def encodable_quotient : encodable (quotient s) :=
encodable.mk
  encode_quot
  decode_quot
  decode_encode_quot
end

end quot
