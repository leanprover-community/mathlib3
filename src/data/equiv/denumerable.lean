/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Denumerable (countably infinite) types, as a typeclass extending
encodable. This is used to provide explicit encode/decode functions
from nat, where the functions are known inverses of each other.
-/
import data.equiv.encodable data.sigma data.fintype data.list.min_max
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
  encodek := λ a, congr_arg some (e.symm_apply_apply _),
  decode_inv := λ n, ⟨_, rfl, e.apply_symm_apply _⟩ }

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

namespace nat.subtype
open function encodable lattice

variables {s : set ℕ} [decidable_pred s] [infinite s]

lemma exists_succ (x : s) : ∃ n, x.1 + n + 1 ∈ s :=
classical.by_contradiction $ λ h,
have ∀ (a : ℕ) (ha : a ∈ s), a < x.val.succ,
  from λ a ha, lt_of_not_ge (λ hax, h ⟨a - (x.1 + 1),
    by rwa [add_right_comm, nat.add_sub_cancel' hax]⟩),
infinite.not_fintype
  ⟨(((multiset.range x.1.succ).filter (∈ s)).pmap
      (λ (y : ℕ) (hy : y ∈ s), subtype.mk y hy)
      (by simp [-multiset.range_succ])).to_finset,
    by simpa [subtype.ext, multiset.mem_filter, -multiset.range_succ]⟩

def succ (x : s) : s :=
have h : ∃ m, x.1 + m + 1 ∈ s, from exists_succ x,
⟨x.1 + nat.find h + 1, nat.find_spec h⟩

lemma succ_le_of_lt {x y : s} (h : y < x) : succ y ≤ x :=
have hx : ∃ m, y.1 + m + 1 ∈ s, from exists_succ _,
let ⟨k, hk⟩ := nat.exists_eq_add_of_lt h in
have nat.find hx ≤ k, from nat.find_min' _ (hk ▸ x.2),
show y.1 + nat.find hx + 1 ≤ x.1,
by rw hk; exact add_le_add_right (add_le_add_left this _) _

lemma le_succ_of_forall_lt_le {x y : s} (h : ∀ z < x, z ≤ y) : x ≤ succ y :=
have hx : ∃ m, y.1 + m + 1 ∈ s, from exists_succ _,
show x.1 ≤ y.1 + nat.find hx + 1,
from le_of_not_gt $ λ hxy,
have y.1 + nat.find hx + 1 ≤ y.1 := h ⟨_, nat.find_spec hx⟩ hxy,
not_lt_of_le this $
  calc y.1 ≤ y.1 + nat.find hx : le_add_of_nonneg_right (nat.zero_le _)
  ... < y.1 + nat.find hx + 1 : nat.lt_succ_self _

lemma lt_succ_self (x : s) :  x < succ x :=
calc x.1 ≤ x.1 + _ : le_add_right (le_refl _)
... < succ x : nat.lt_succ_self (x.1 + _)

def of_nat (s : set ℕ) [decidable_pred s] [infinite s] : ℕ → s
| 0     := ⊥
| (n+1) := succ (of_nat n)

lemma of_nat_strict_mono : strict_mono (of_nat s) :=
nat.strict_mono_of_lt_succ _ (λ a, by rw of_nat; exact lt_succ_self _)

open list

lemma of_nat_surjective_aux : ∀ {x : ℕ} (hx : x ∈ s), ∃ n, of_nat s n = ⟨x, hx⟩
| x := λ hx, let t : list s := ((list.range x).filter (λ y, y ∈ s)).pmap
  (λ (y : ℕ) (hy : y ∈ s), ⟨y, hy⟩) (by simp) in
have hmt : ∀ {y : s}, y ∈ t ↔ y < ⟨x, hx⟩,
  by simp [list.mem_filter, subtype.ext, t]; intros; refl,
if ht : t = [] then ⟨0, le_antisymm (@bot_le s _ _)
  (le_of_not_gt (λ h, list.not_mem_nil ⊥ $
    by rw [← ht, hmt]; exact h))⟩
else by letI : inhabited s := ⟨⊥⟩;
  exact have wf : (maximum t).1 < x, by simpa [hmt] using list.mem_maximum ht,
  let ⟨a, ha⟩ := of_nat_surjective_aux (list.maximum t).2 in
  ⟨a + 1, le_antisymm
    (by rw of_nat; exact succ_le_of_lt (by rw ha; exact wf)) $
    by rw of_nat; exact le_succ_of_forall_lt_le
      (λ z hz, by rw ha; exact list.le_maximum_of_mem (hmt.2 hz))⟩

lemma of_nat_surjective : surjective (of_nat s) :=
λ ⟨x, hx⟩, of_nat_surjective_aux hx

def denumerable (s : set ℕ) [decidable_pred s] [infinite s] : denumerable s :=
have li : left_inverse (of_nat s) (λ x : s, nat.find (of_nat_surjective x)),
  from λ x, nat.find_spec (of_nat_surjective x),
denumerable.of_equiv ℕ
{ to_fun := λ x, nat.find (of_nat_surjective x),
  inv_fun := of_nat s,
  left_inv := li,
  right_inv := right_inverse_of_injective_of_left_inverse
    (strict_mono.injective of_nat_strict_mono) li }

end nat.subtype

namespace denumerable
open encodable

def of_encodable_of_infinite (α : Type*) [encodable α] [infinite α] : denumerable α :=
begin
  letI := @decidable_range_encode α _;
  letI : infinite (set.range (@encode α _)) :=
    infinite.of_injective _ (equiv.set.range _ encode_injective).injective,
  letI := nat.subtype.denumerable (set.range (@encode α _)),
  exact denumerable.of_equiv (set.range (@encode α _))
    (equiv_range_encode α)
end

end denumerable
