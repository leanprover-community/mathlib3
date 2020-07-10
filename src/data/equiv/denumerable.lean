/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Denumerable (countably infinite) types, as a typeclass extending
encodable. This is used to provide explicit encode/decode functions
from nat, where the functions are known inverses of each other.
-/
import data.equiv.encodable
import data.sigma
import data.fintype.basic
import data.list.min_max
open nat

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A denumerable type is one which is (constructively) bijective with ℕ.
  Although we already have a name for this property, namely `α ≃ ℕ`,
  we are here interested in using it as a typeclass. -/
class denumerable (α : Type*) extends encodable α :=
(decode_inv : ∀ n, ∃ a ∈ decode n, encode a = n)
end prio

namespace denumerable

section
variables {α : Type*} {β : Type*} [denumerable α] [denumerable β]
open encodable

theorem decode_is_some (α) [denumerable α] (n : ℕ) :
  (decode α n).is_some :=
option.is_some_iff_exists.2 $
(decode_inv n).imp $ λ a, Exists.fst

def of_nat (α) [f : denumerable α] (n : ℕ) : α :=
option.get (decode_is_some α n)

@[simp, priority 900]
theorem decode_eq_of_nat (α) [denumerable α] (n : ℕ) :
  decode α n = some (of_nat α n) :=
option.eq_some_of_is_some _

@[simp] theorem of_nat_of_decode {n b}
  (h : decode α n = some b) : of_nat α n = b :=
option.some.inj $ (decode_eq_of_nat _ _).symm.trans h

@[simp] theorem encode_of_nat (n) : encode (of_nat α n) = n :=
let ⟨a, h, e⟩ := decode_inv n in
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

instance int : denumerable ℤ := denumerable.mk' equiv.int_equiv_nat

instance pnat : denumerable ℕ+ := denumerable.mk' equiv.pnat_equiv_nat

instance ulift : denumerable (ulift α) := of_equiv _ equiv.ulift

instance plift : denumerable (plift α) := of_equiv _ equiv.plift

def pair : α × α ≃ α := equiv₂ _ _

end
end denumerable

namespace nat.subtype
open function encodable

variables {s : set ℕ} [infinite s]

section classical
open_locale classical

lemma exists_succ (x : s) : ∃ n, x.1 + n + 1 ∈ s :=
classical.by_contradiction $ λ h,
have ∀ (a : ℕ) (ha : a ∈ s), a < x.val.succ,
  from λ a ha, lt_of_not_ge (λ hax, h ⟨a - (x.1 + 1),
    by rwa [add_right_comm, nat.add_sub_cancel' hax]⟩),
infinite.not_fintype
  ⟨(((multiset.range x.1.succ).filter (∈ s)).pmap
      (λ (y : ℕ) (hy : y ∈ s), subtype.mk y hy)
      (by simp [-multiset.range_succ])).to_finset,
    by simpa [subtype.ext_iff_val, multiset.mem_filter, -multiset.range_succ]⟩

end classical

variable [decidable_pred s]

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

lemma lt_succ_self (x : s) : x < succ x :=
calc x.1 ≤ x.1 + _ : le_add_right (le_refl _)
... < succ x : nat.lt_succ_self (x.1 + _)

lemma lt_succ_iff_le {x y : s} : x < succ y ↔ x ≤ y :=
⟨λ h, le_of_not_gt (λ h', not_le_of_gt h (succ_le_of_lt h')),
  λ h, lt_of_le_of_lt h (lt_succ_self _)⟩

def of_nat (s : set ℕ) [decidable_pred s] [infinite s] : ℕ → s
| 0     := ⊥
| (n+1) := succ (of_nat n)

lemma of_nat_surjective_aux : ∀ {x : ℕ} (hx : x ∈ s), ∃ n, of_nat s n = ⟨x, hx⟩
| x := λ hx, let t : list s := ((list.range x).filter (λ y, y ∈ s)).pmap
  (λ (y : ℕ) (hy : y ∈ s), ⟨y, hy⟩) (by simp) in
have hmt : ∀ {y : s}, y ∈ t ↔ y < ⟨x, hx⟩,
  by simp [list.mem_filter, subtype.ext_iff_val, t]; intros; refl,
have wf : ∀ m : s, list.maximum t = m → m.1 < x,
  from λ m hmax, by simpa [hmt] using list.maximum_mem hmax,
begin
  cases hmax : list.maximum t with m,
  { exact ⟨0, le_antisymm (@bot_le s _ _)
      (le_of_not_gt (λ h, list.not_mem_nil (⊥ : s) $
        by rw [← list.maximum_eq_none.1 hmax, hmt]; exact h))⟩ },
  { cases of_nat_surjective_aux m.2 with a ha,
    exact ⟨a + 1, le_antisymm
      (by rw of_nat; exact succ_le_of_lt (by rw ha; exact wf _ hmax)) $
      by rw of_nat; exact le_succ_of_forall_lt_le
        (λ z hz, by rw ha; cases m; exact list.le_maximum_of_mem (hmt.2 hz) hmax)⟩ }
end
using_well_founded {dec_tac := `[tauto]}

lemma of_nat_surjective : surjective (of_nat s) :=
λ ⟨x, hx⟩, of_nat_surjective_aux hx

private def to_fun_aux (x : s) : ℕ :=
(list.range x).countp s

private lemma to_fun_aux_eq (x : s) :
  to_fun_aux x = ((finset.range x).filter s).card :=
by rw [to_fun_aux, list.countp_eq_length_filter]; refl

open finset

private lemma right_inverse_aux : ∀ n, to_fun_aux (of_nat s n) = n
| 0 := begin
  rw [to_fun_aux_eq, card_eq_zero, eq_empty_iff_forall_not_mem],
  assume n,
  rw [mem_filter, of_nat, mem_range],
  assume h,
  exact not_lt_of_le bot_le (show (⟨n, h.2⟩ : s) < ⊥, from h.1)
end
| (n+1) := have ih : to_fun_aux (of_nat s n) = n, from right_inverse_aux n,
have h₁ : (of_nat s n : ℕ) ∉ (range (of_nat s n)).filter s, by simp,
have h₂ : (range (succ (of_nat s n))).filter s =
    insert (of_nat s n) ((range (of_nat s n)).filter s),
  begin
    simp only [finset.ext_iff, mem_insert, mem_range, mem_filter],
    assume m,
    exact ⟨λ h, by simp only [h.2, and_true]; exact or.symm
        (lt_or_eq_of_le ((@lt_succ_iff_le _ _ _ ⟨m, h.2⟩ _).1 h.1)),
      λ h, h.elim (λ h, h.symm ▸ ⟨lt_succ_self _, subtype.property _⟩)
        (λ h, ⟨lt_of_le_of_lt (le_of_lt h.1) (lt_succ_self _), h.2⟩)⟩
  end,
begin
  clear_aux_decl,
  simp only [to_fun_aux_eq, of_nat, range_succ] at *,
  conv {to_rhs, rw [← ih, ← card_insert_of_not_mem h₁, ← h₂] },
end

def denumerable (s : set ℕ) [decidable_pred s] [infinite s] : denumerable s :=
denumerable.of_equiv ℕ
{ to_fun := to_fun_aux,
  inv_fun := of_nat s,
  left_inv := left_inverse_of_surjective_of_right_inverse
    of_nat_surjective right_inverse_aux,
  right_inv := right_inverse_aux }

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
