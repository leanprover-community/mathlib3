/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro

Type class for encodable Types.
Note that every encodable Type is countable.
-/
import data.fintype data.list data.list.perm data.list.sort
       data.equiv data.nat.basic logic.function
open option list nat function

/-- An encodable type is a "constructively countable" type. This is where
  we have an explicit injection `encode : α → nat` and a partial inverse
  `decode : nat → option α`. This makes the range of `encode` decidable,
  although it is not decidable if `α` is finite or not. -/
class encodable (α : Type*) :=
(encode : α → nat) (decode : nat → option α) (encodek : ∀ a, decode (encode a) = some a)

section encodable
variables {α : Type*} {β : Type*}
universe u
open encodable

section
variables [encodable α]

theorem encode_injective : function.injective (@encode α _)
| x y e := option.some.inj $ by rw [← encodek, e, encodek]

/- lower priority of instance below because we don't want to use encodability
   to prove that e.g. equality of nat is decidable. Example of a problem:

   lemma H (e : ℕ) : finset.range (nat.succ e) = insert e (finset.range e) :=
   begin
   exact finset.range_succ
   end

  fails with this priority not set to zero
-/
@[priority 0] instance decidable_eq_of_encodable : decidable_eq α
| a b := decidable_of_iff _ encode_injective.eq_iff
end

def encodable_of_left_injection [h₁ : encodable α]
  (f : β → α) (finv : α → option β) (linv : ∀ b, finv (f b) = some b) : encodable β :=
⟨λ b, encode (f b),
 λ n, (decode α n).bind finv,
 λ b, by simp [encodable.encodek, option.bind, linv]⟩

def encodable_of_equiv (α) [h : encodable α] : β ≃ α → encodable β
| ⟨f, g, l, r⟩ :=
  encodable_of_left_injection f (λ b, some (g b)) (λ b, by rw l; refl)

instance encodable_nat : encodable nat :=
⟨id, some, λ a, rfl⟩

instance encodable_empty : encodable empty :=
⟨λ a, a.rec _, λ n, none, λ a, a.rec _⟩

instance encodable_unit : encodable punit.{u+1} :=
⟨λ_, 0, λn, if n = 0 then some punit.star else none, λ⟨⟩, by simp⟩

instance encodable_option {α : Type*} [h : encodable α] : encodable (option α) :=
⟨λ o, match o with
      | some a := succ (encode a)
      | none := 0
      end,
 λ n, if n = 0 then some none else some (decode α (pred n)),
 λ o, by cases o; simp [encodable_option._match_1, encodek, nat.succ_ne_zero]⟩

section sum
variables [encodable α] [encodable β]

private def encode_sum : sum α β → nat
| (sum.inl a) := bit ff $ encode a
| (sum.inr b) := bit tt $ encode b

private def decode_sum (n : nat) : option (sum α β) :=
match bodd_div2 n with
| (ff, m) := match decode α m with
  | some a := some (sum.inl a)
  | none   := none
  end
| (tt, m) := match decode β m with
  | some b := some (sum.inr b)
  | none   := none
  end
end

instance encodable_sum : encodable (sum α β) :=
⟨encode_sum, decode_sum, λ s,
  by cases s; simp [encode_sum, decode_sum];
     rw [bodd_bit, div2_bit, decode_sum, encodek]; refl⟩
end sum

instance encodable_bool: encodable bool :=
encodable_of_equiv (unit ⊕ unit) equiv.bool_equiv_unit_sum_unit

section sigma
variables {γ : α → Type*} [encodable α] [∀ a, encodable (γ a)]

private def encode_sigma : sigma γ → nat
| ⟨a, b⟩ := mkpair (encode a) (encode b)

private def decode_sigma (n : nat) : option (sigma γ) :=
let (n₁, n₂) := unpair n in
(decode α n₁).bind $ λ a, (decode (γ a) n₂).map $ sigma.mk a

instance encodable_sigma : encodable (sigma γ) :=
⟨encode_sigma, decode_sigma, λ ⟨a, b⟩,
  by simp [encode_sigma, decode_sigma, option.bind, option.map, unpair_mkpair, encodek]⟩
end sigma

instance encodable_product [encodable α] [encodable β] : encodable (α × β) :=
encodable_of_equiv _ (equiv.sigma_equiv_prod α β).symm

section list
variable [encodable α]

private def encode_list : list α → nat
| []     := 0
| (a::l) := succ (mkpair (encode_list l) (encode a))

private def decode_list : nat → option (list α)
| 0        := some []
| (succ v) := match unpair v, unpair_le v with
  | (v₂, v₁), h :=
    have v₂ < succ v, from lt_succ_of_le h,
    (::) <$> decode α v₁ <*> decode_list v₂
  end

instance encodable_list : encodable (list α) :=
⟨encode_list, decode_list, λ l,
  by induction l with a l IH; simp [encode_list, decode_list, unpair_mkpair, encodek, *]⟩
end list

section finset
variables [encodable α]

private def enle (a b : α) : Prop := encode a ≤ encode b

private lemma enle.refl (a : α) : enle a a := le_refl _

private lemma enle.trans (a b c : α) : enle a b → enle b c → enle a c := le_trans

private lemma enle.total (a b : α) : enle a b ∨ enle b a := le_total _ _

private lemma enle.antisymm (a b : α) (h₁ : enle a b) (h₂ : enle b a) : a = b :=
encode_injective (le_antisymm h₁ h₂)

private def decidable_enle (a b : α) : decidable (enle a b) :=
by unfold enle; apply_instance

local attribute [instance] decidable_enle

private def ensort (l : list α) : list α :=
insertion_sort enle l

open subtype list.perm

private lemma sorted_eq_of_perm {l₁ l₂ : list α} (h : l₁ ~ l₂) : ensort l₁ = ensort l₂ :=
eq_of_sorted_of_perm enle.trans enle.antisymm
  (perm.trans (perm_insertion_sort _ _) $ perm.trans h (perm_insertion_sort _ _).symm)
  (sorted_insertion_sort _ enle.total enle.trans _)
  (sorted_insertion_sort _ enle.total enle.trans _)

private def encode_multiset (s : multiset α) : nat :=
encode $ quot.lift_on s
  (λ l, ensort l)
  (λ l₁ l₂ p, sorted_eq_of_perm p)

private def decode_multiset (n : nat) : option (multiset α) :=
coe <$> decode (list α) n

instance encodable_multiset : encodable (multiset α) :=
⟨encode_multiset, decode_multiset, λ s, quot.induction_on s $ λ l,
show coe <$> decode (list α) (encode (ensort l)) = some ↑l,
by rw [encodek, ← show (ensort l:multiset α) = l,
       from quotient.sound (perm_insertion_sort _ _)]; refl⟩

end finset

def encodable_of_list [decidable_eq α] (l : list α) (H : ∀ x, x ∈ l) : encodable α :=
⟨λ a, index_of a l, l.nth, λ a, index_of_nth (H _)⟩

def trunc_encodable_of_fintype (α : Type*) [decidable_eq α] [fintype α] : trunc (encodable α) :=
@@quot.rec_on_subsingleton _
  (λ s : multiset α, (∀ x:α, x ∈ s) → trunc (encodable α)) _
  finset.univ.1
  (λ l H, trunc.mk $ encodable_of_list l H)
  finset.mem_univ

section subtype
open subtype decidable
variable {P : α → Prop}
variable [encA : encodable α]
variable [decP : decidable_pred P]

include encA
private def encode_subtype : {a : α // P a} → nat
| ⟨v, h⟩ := encode v

include decP
private def decode_subtype (v : nat) : option {a : α // P a} :=
match decode α v with
| some a := if h : P a then some ⟨a, h⟩ else none
| none   := none
end

instance encodable_subtype : encodable {a : α // P a} :=
⟨encode_subtype, decode_subtype,
 λ ⟨v, h⟩, by simp [encode_subtype, decode_subtype, encodek, h]⟩
end subtype

instance bool.encodable : encodable bool := encodable_of_equiv _ equiv.bool_equiv_unit_sum_unit

instance int.encodable : encodable ℤ :=
encodable_of_equiv _ equiv.int_equiv_nat

instance encodable_finset [encodable α] : encodable (finset α) :=
encodable_of_equiv {s : multiset α // s.nodup}
  ⟨λ ⟨a, b⟩, ⟨a, b⟩, λ⟨a, b⟩, ⟨a, b⟩, λ ⟨a, b⟩, rfl, λ⟨a, b⟩, rfl⟩

instance encodable_ulift [encodable α] : encodable (ulift α) :=
encodable_of_equiv _ equiv.ulift

instance encodable_plift [encodable α] : encodable (plift α) :=
encodable_of_equiv _ equiv.plift

noncomputable def encodable_of_inj [encodable β] (f : α → β) (hf : injective f) : encodable α :=
encodable_of_left_injection f (partial_inv f) (λ x, (partial_inv_of_injective hf _ _).2 rfl)

end encodable

/-
Choice function for encodable types and decidable predicates.
We provide the following API

choose      {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] : (∃ x, p x) → α :=
choose_spec {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] (ex : ∃ x, p x) : p (choose ex) :=
-/

namespace encodable
section find_a
variables {α : Type*} (p : α → Prop) [encodable α] [decidable_pred p]

private def good : option α → Prop
| (some a) := p a
| none     := false

private def decidable_good : decidable_pred (good p)
| n := by cases n; unfold good; apply_instance
local attribute [instance] decidable_good

open encodable
variable {p}

def choose_x (h : ∃ x, p x) : {a:α // p a} :=
have ∃ n, good p (decode α n), from
let ⟨w, pw⟩ := h in ⟨encode w, by simp [good, encodek, pw]⟩,
match _, nat.find_spec this : ∀ o, good p o → {a // p a} with
| some a, h := ⟨a, h⟩
end

def choose (h : ∃ x, p x) : α := (choose_x h).1

lemma choose_spec (h : ∃ x, p x) : p (choose h) := (choose_x h).2

end find_a

theorem axiom_of_choice {α : Type*} {β : α → Type*} {R : Π x, β x → Prop}
  [Π a, encodable (β a)] [∀ x y, decidable (R x y)]
  (H : ∀x, ∃y, R x y) : ∃f:Πa, β a, ∀x, R x (f x) :=
⟨λ x, choose (H x), λ x, choose_spec (H x)⟩

theorem skolem {α : Type*} {β : α → Type*} {P : Π x, β x → Prop}
  [c : Π a, encodable (β a)] [d : ∀ x y, decidable (P x y)] :
  (∀x, ∃y, P x y) ↔ ∃f : Π a, β a, (∀x, P x (f x)) :=
⟨axiom_of_choice, λ ⟨f, H⟩ x, ⟨_, H x⟩⟩

end encodable

namespace quot
open encodable
variables {α : Type*} {s : setoid α} [@decidable_rel α (≈)] [encodable α]

-- Choose equivalence class representative
def rep (q : quotient s) : α :=
choose (exists_rep q)

theorem rep_spec (q : quotient s) : ⟦rep q⟧ = q :=
choose_spec (exists_rep q)

def encodable_quotient : encodable (quotient s) :=
⟨λ q, encode (rep q),
 λ n, quotient.mk <$> decode α n,
 λ q, quot.induction_on q $ λ l,
   by rw encodek; exact congr_arg some (rep_spec _)⟩

end quot
