/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Denumerable (countably infinite) types, as a typeclass extending
encodable. This is used to provide explicit encode/decode functions
from nat, where the functions are known inverses of each other.
-/
import data.equiv.encodable data.sigma
open nat

/-- A denumerable type is one which is (constructively) bijective with ℕ.
  Although we already have a name for this property, namely `α ≃ ℕ`,
  we are here interested in using it as a typeclass. -/
class denumerable (α : Type*) extends encodable α :=
(decode_inv : ∀ n, ∃ a ∈ decode n, encode a = n)

namespace denumerable

section
variables {α : Type*} {β : Type*} [denumerable α] [denumerable β]
open encodable

@[simp] theorem decode_is_some (α) [denumerable α] (n : ℕ) :
  (decode α n).is_some :=
option.is_some_iff_exists.2 $
(decode_inv α n).imp $ λ a, Exists.fst

def of_nat (α) [f : denumerable α] (n : ℕ) : α :=
option.get (decode_is_some α n)

@[simp] theorem decode_eq_of_nat (α) [denumerable α] (n : ℕ) :
  decode α n = some (of_nat α n) :=
option.eq_some_of_is_some _

@[simp] theorem of_nat_of_decode {n b}
  (h : decode α n = some b) : of_nat α n = b :=
option.some.inj $ (decode_eq_of_nat _ _).symm.trans h

@[simp] theorem encode_of_nat (n) : encode (of_nat α n) = n :=
let ⟨a, h, e⟩ := decode_inv α n in
by rwa [of_nat_of_decode h]

@[simp] theorem of_nat_encode (a) : of_nat α (encode a) = a :=
of_nat_of_decode (encodek _)

def eqv (α) [denumerable α] : α ≃ ℕ :=
⟨encode, of_nat α, of_nat_encode, encode_of_nat⟩

def mk' {α} (e : α ≃ ℕ) : denumerable α :=
{ encode := e,
  decode := some ∘ e.symm,
  encodek := λ a, congr_arg some (e.inverse_apply_apply _),
  decode_inv := λ n, ⟨_, rfl, e.apply_inverse_apply _⟩ }

def of_equiv (α) {β} [denumerable α] (e : β ≃ α) : denumerable β :=
{ decode_inv := λ n, by simp,
  ..encodable.of_equiv _ e }

@[simp] theorem of_equiv_of_nat (α) {β} [denumerable α] (e : β ≃ α)
  (n) : @of_nat β (of_equiv _ e) n = e.symm (of_nat α n) :=
by apply of_nat_of_decode; show option.map _ _ = _; simp

def equiv₂ (α β) [denumerable α] [denumerable β] : α ≃ β := (eqv α).trans (eqv β).symm

instance nat : denumerable nat := ⟨λ n, ⟨_, rfl, rfl⟩⟩

@[simp] theorem of_nat_nat (n) : of_nat ℕ n = n := rfl

instance option : denumerable (option α) := ⟨λ n, by cases n; simp⟩

instance sum : denumerable (α ⊕ β) :=
⟨λ n, begin
  suffices : ∃ a ∈ @decode_sum α β _ _ n,
    encode_sum a = bit (bodd n) (div2 n), {simpa [bit_decomp]},
  simp [decode_sum]; cases bodd n; simp [decode_sum, bit, encode_sum]
end⟩

section sigma
variables {γ : α → Type*} [∀ a, denumerable (γ a)]

instance sigma : denumerable (sigma γ) :=
⟨λ n, by simp [decode_sigma]; exact ⟨_, _, ⟨rfl, heq.rfl⟩, by simp⟩⟩

@[simp] theorem sigma_of_nat_val (n : ℕ) :
  of_nat (sigma γ) n = ⟨of_nat α (unpair n).1, of_nat (γ _) (unpair n).2⟩ :=
option.some.inj $
by rw [← decode_eq_of_nat, decode_sigma_val]; simp; refl

end sigma

instance prod : denumerable (α × β) :=
of_equiv _ (equiv.sigma_equiv_prod α β).symm

@[simp] theorem prod_of_nat_val (n : ℕ) :
  of_nat (α × β) n = (of_nat α (unpair n).1, of_nat β (unpair n).2) :=
by simp; refl

@[simp] theorem prod_nat_of_nat : of_nat (ℕ × ℕ) = unpair :=
by funext; simp

instance int : denumerable ℤ := of_equiv _ equiv.int_equiv_nat

instance ulift : denumerable (ulift α) := of_equiv _ equiv.ulift

instance plift : denumerable (plift α) := of_equiv _ equiv.plift

def pair : (α × α) ≃ α := equiv₂ _ _

end
end denumerable
