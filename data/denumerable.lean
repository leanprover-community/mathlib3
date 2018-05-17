/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Denumerable (countably infinite) types, as a typeclass extending
encodable. This is used to provide explicit encode/decode functions
from nat, where the functions are known inverses of each other.
-/
import data.encodable order.basic
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
{ decode_inv := λ n, by simp [option.bind],
  ..encodable.of_equiv _ e }

@[simp] theorem of_equiv_of_nat (α) {β} [denumerable α] (e : β ≃ α)
  (n) : @of_nat β (of_equiv _ e) n = e.symm (of_nat α n) :=
by apply of_nat_of_decode; show option.map _ _ = _; simp; refl

def equiv₂ (α β) [denumerable α] [denumerable β] : α ≃ β := (eqv α).trans (eqv β).symm

instance nat : denumerable nat := ⟨λ n, ⟨_, rfl, rfl⟩⟩

@[simp] theorem of_nat_nat (n) : of_nat ℕ n = n := rfl

instance option : denumerable (option α) := ⟨λ n, by cases n; simp⟩

instance sum : denumerable (α ⊕ β) :=
⟨λ n, begin
  suffices : ∃ a ∈ @decode_sum α β _ _ n,
    encode_sum a = bit (bodd n) (div2 n), {simpa [bit_decomp]},
  simp [decode_sum]; cases bodd n; simp [decode_sum],
  { refine or.inl ⟨_, rfl, _⟩, simp [encode_sum] },
  { refine or.inr ⟨_, rfl, _⟩, simp [encode_sum] }
end⟩

section sigma
variables {γ : α → Type*} [∀ a, denumerable (γ a)]

instance sigma : denumerable (sigma γ) :=
⟨λ n, by simp [decode_sigma]; exact ⟨_, _, rfl, by simp⟩⟩

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

theorem denumerable_list_aux : ∀ n : ℕ,
  ∃ a ∈ @decode_list α _ n, encode_list a = n
| 0        := ⟨_, rfl, rfl⟩
| (succ v) := begin
  cases e : unpair v with v₂ v₁,
  have h := unpair_le v,
  rw e at h,
  rcases have v₂ < succ v, from lt_succ_of_le h,
    denumerable_list_aux v₂ with ⟨a, h₁, h₂⟩,
  simp at h₁,
  simp [decode_list, e, h₂, h₁, encode_list, mkpair_unpair' e]
end

instance denumerable_list : denumerable (list α) := ⟨denumerable_list_aux⟩

section multiset

def lower : list ℕ → ℕ → list ℕ
| []       n := []
| (m :: l) n := (m - n) :: lower l m

def raise : list ℕ → ℕ → list ℕ
| []       n := []
| (m :: l) n := (m + n) :: raise l (m + n)

lemma lower_raise : ∀ l n, lower (raise l n) n = l
| []       n := rfl
| (m :: l) n := by simp [raise, lower, nat.add_sub_cancel, lower_raise]

lemma raise_lower : ∀ {l n}, list.sorted (≤) (n :: l) → raise (lower l n) n = l
| []       n h := rfl
| (m :: l) n h :=
  have n ≤ m, from list.rel_of_sorted_cons h _ (l.mem_cons_self _),
  by simp [raise, lower, nat.add_sub_cancel' this,
           raise_lower (list.sorted_of_sorted_cons h)]

lemma raise_chain : ∀ l n, list.chain (≤) n (raise l n)
| []       n := list.chain.nil _ _
| (m :: l) n := list.chain.cons (nat.le_add_left _ _) (raise_chain _ _)

lemma raise_sorted : ∀ l n, list.sorted (≤) (raise l n)
| []       n := list.sorted_nil
| (m :: l) n := (list.chain_iff_pairwise (@le_trans _ _)).1 (raise_chain _ _)

/- Warning: this is not the same encoding as used in `encodable` -/
instance multiset : denumerable (multiset α) := mk' ⟨
  λ s : multiset α, encode $ lower ((s.map encode).sort (≤)) 0,
  λ n, multiset.map (of_nat α) (raise (of_nat (list ℕ) n) 0),
  λ s, by have := raise_lower
      (list.sorted_cons.2 ⟨λ n _, zero_le n, (s.map encode).sort_sorted _⟩);
    simp [-multiset.coe_map, this],
  λ n, by simp [-multiset.coe_map, list.merge_sort_eq_self _ (raise_sorted _ _), lower_raise]⟩

end multiset

section finset

def lower' : list ℕ → ℕ → list ℕ
| []       n := []
| (m :: l) n := (m - n) :: lower' l (m + 1)

def raise' : list ℕ → ℕ → list ℕ
| []       n := []
| (m :: l) n := (m + n) :: raise' l (m + n + 1)

lemma lower_raise' : ∀ l n, lower' (raise' l n) n = l
| []       n := rfl
| (m :: l) n := by simp [raise', lower', nat.add_sub_cancel, lower_raise']

lemma raise_lower' : ∀ {l n}, (∀ m ∈ l, n ≤ m) → list.sorted (<) l → raise' (lower' l n) n = l
| []       n h₁ h₂ := rfl
| (m :: l) n h₁ h₂ :=
  have n ≤ m, from h₁ _ (l.mem_cons_self _),
  by simp [raise', lower', nat.add_sub_cancel' this, raise_lower'
    (list.rel_of_sorted_cons h₂ : ∀ a ∈ l, m < a) (list.sorted_of_sorted_cons h₂)]

lemma raise'_chain : ∀ l {m n}, m < n → list.chain (<) m (raise' l n)
| []       m n h := list.chain.nil _ _
| (a :: l) m n h := list.chain.cons
  (lt_of_lt_of_le h (nat.le_add_left _ _)) (raise'_chain _ (lt_succ_self _))

lemma raise'_sorted : ∀ l n, list.sorted (<) (raise' l n)
| []       n := list.sorted_nil
| (m :: l) n := (list.chain_iff_pairwise (@lt_trans _ _)).1
  (raise'_chain _ (lt_succ_self _))

def raise'_finset (l : list ℕ) (n : ℕ) : finset ℕ :=
⟨raise' l n, (raise'_sorted _ _).imp (@ne_of_lt _ _)⟩

/- Warning: this is not the same encoding as used in `encodable` -/
instance finset : denumerable (finset α) := mk' ⟨
  λ s : finset α, encode $ lower' ((s.map (eqv α).to_embedding).sort (≤)) 0,
  λ n, finset.map (eqv α).symm.to_embedding (raise'_finset (of_nat (list ℕ) n) 0),
  λ s, finset.eq_of_veq $ by simp [-multiset.coe_map, raise'_finset,
    raise_lower' (λ n _, zero_le n) (finset.sort_sorted_lt _)],
  λ n, by simp [-multiset.coe_map, finset.map, raise'_finset, finset.sort,
    list.merge_sort_eq_self (≤) ((raise'_sorted _ _).imp (@le_of_lt _ _)),
    lower_raise']⟩

end finset

instance int : denumerable ℤ := of_equiv _ equiv.int_equiv_nat

instance ulift : denumerable (ulift α) := of_equiv _ equiv.ulift

instance plift : denumerable (plift α) := of_equiv _ equiv.plift

def pair : (α × α) ≃ α := equiv₂ _ _

end
end denumerable
