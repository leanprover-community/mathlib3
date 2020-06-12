/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Additional equiv and encodable instances for lists, finsets, and fintypes.
-/
import data.equiv.denumerable

open nat list

namespace encodable
variables {α : Type*}

section list
variable [encodable α]

def encode_list : list α → ℕ
| []     := 0
| (a::l) := succ (mkpair (encode a) (encode_list l))

def decode_list : ℕ → option (list α)
| 0        := some []
| (succ v) := match unpair v, unpair_le_right v with
  | (v₁, v₂), h :=
    have v₂ < succ v, from lt_succ_of_le h,
    (::) <$> decode α v₁ <*> decode_list v₂
  end

instance list : encodable (list α) :=
⟨encode_list, decode_list, λ l,
  by induction l with a l IH; simp [encode_list, decode_list, unpair_mkpair, encodek, *]⟩

@[simp] theorem encode_list_nil : encode (@nil α) = 0 := rfl
@[simp] theorem encode_list_cons (a : α) (l : list α) :
  encode (a :: l) = succ (mkpair (encode a) (encode l)) := rfl

@[simp] theorem decode_list_zero : decode (list α) 0 = some [] := rfl

@[simp] theorem decode_list_succ (v : ℕ) :
  decode (list α) (succ v) =
  (::) <$> decode α v.unpair.1 <*> decode (list α) v.unpair.2 :=
show decode_list (succ v) = _, begin
  cases e : unpair v with v₁ v₂,
  simp [decode_list, e], refl
end

theorem length_le_encode : ∀ (l : list α), length l ≤ encode l
| [] := _root_.zero_le _
| (a :: l) := succ_le_succ $
  le_trans (length_le_encode l) (le_mkpair_right _ _)

end list

section finset
variables [encodable α]

private def enle : α → α → Prop := encode ⁻¹'o (≤)

private lemma enle.is_linear_order : is_linear_order α enle :=
(order_embedding.preimage ⟨encode, encode_injective⟩ (≤)).is_linear_order

private def decidable_enle (a b : α) : decidable (enle a b) :=
by unfold enle order.preimage; apply_instance

local attribute [instance] enle.is_linear_order decidable_enle

def encode_multiset (s : multiset α) : ℕ :=
encode (s.sort enle)

def decode_multiset (n : ℕ) : option (multiset α) :=
coe <$> decode (list α) n

instance multiset : encodable (multiset α) :=
⟨encode_multiset, decode_multiset,
 λ s, by simp [encode_multiset, decode_multiset, encodek]⟩

end finset

def encodable_of_list [decidable_eq α] (l : list α) (H : ∀ x, x ∈ l) : encodable α :=
⟨λ a, index_of a l, l.nth, λ a, index_of_nth (H _)⟩

def trunc_encodable_of_fintype (α : Type*) [decidable_eq α] [fintype α] : trunc (encodable α) :=
@@quot.rec_on_subsingleton _
  (λ s : multiset α, (∀ x:α, x ∈ s) → trunc (encodable α)) _
  finset.univ.1
  (λ l H, trunc.mk $ encodable_of_list l H)
  finset.mem_univ

instance vector [encodable α] {n} : encodable (vector α n) :=
encodable.subtype

instance fin_arrow [encodable α] {n} : encodable (fin n → α) :=
of_equiv _ (equiv.vector_equiv_fin _ _).symm

instance fin_pi (n) (π : fin n → Type*) [∀i, encodable (π i)] : encodable (Πi, π i) :=
of_equiv _ (equiv.pi_equiv_subtype_sigma (fin n) π)

instance array [encodable α] {n} : encodable (array n α) :=
of_equiv _ (equiv.array_equiv_fin _ _)

instance finset [encodable α] : encodable (finset α) :=
by haveI := decidable_eq_of_encodable α; exact
 of_equiv {s : multiset α // s.nodup}
  ⟨λ ⟨a, b⟩, ⟨a, b⟩, λ⟨a, b⟩, ⟨a, b⟩, λ ⟨a, b⟩, rfl, λ⟨a, b⟩, rfl⟩

def fintype_arrow (α : Type*) (β : Type*) [fintype α] [decidable_eq α] [encodable β] :
  trunc (encodable (α → β)) :=
(fintype.equiv_fin α).map $
  λf, encodable.of_equiv (fin (fintype.card α) → β) $
  equiv.arrow_congr f (equiv.refl _)

def fintype_pi (α : Type*) (π : α → Type*) [fintype α] [decidable_eq α] [∀a, encodable (π a)] :
  trunc (encodable (Πa, π a)) :=
(encodable.trunc_encodable_of_fintype α).bind $ λa,
  (@fintype_arrow α (Σa, π a) _ _ (@encodable.sigma _ _ a _)).bind $ λf,
  trunc.mk $ @encodable.of_equiv _ _ (@encodable.subtype _ _ f _) (equiv.pi_equiv_subtype_sigma α π)

/-- The elements of a `fintype` as a sorted list. -/
def sorted_univ (α) [fintype α] [encodable α] : list α :=
finset.univ.sort (encodable.encode' α ⁻¹'o (≤))

theorem mem_sorted_univ {α} [fintype α] [encodable α] (x : α) : x ∈ sorted_univ α :=
(finset.mem_sort _).2 (finset.mem_univ _)

theorem length_sorted_univ {α} [fintype α] [encodable α] :
  (sorted_univ α).length = fintype.card α :=
finset.length_sort _

theorem sorted_univ_nodup {α} [fintype α] [encodable α] : (sorted_univ α).nodup :=
finset.sort_nodup _ _

/-- An encodable `fintype` is equivalent a `fin`.-/
def fintype_equiv_fin {α} [fintype α] [encodable α] :
  α ≃ fin (fintype.card α) :=
begin
  haveI : decidable_eq α := encodable.decidable_eq_of_encodable _,
  transitivity,
  { exact fintype.equiv_fin_of_forall_mem_list mem_sorted_univ (@sorted_univ_nodup α _ _) },
  exact equiv.cast (congr_arg _ (@length_sorted_univ α _ _))
end

instance fintype_arrow_of_encodable {α β : Type*} [encodable α] [fintype α] [encodable β] :
  encodable (α → β) :=
of_equiv (fin (fintype.card α) → β) $ equiv.arrow_congr fintype_equiv_fin (equiv.refl _)

end encodable

namespace denumerable
variables {α : Type*} {β : Type*} [denumerable α] [denumerable β]
open encodable

section list

theorem denumerable_list_aux : ∀ n : ℕ,
  ∃ a ∈ @decode_list α _ n, encode_list a = n
| 0        := ⟨_, rfl, rfl⟩
| (succ v) := begin
  cases e : unpair v with v₁ v₂,
  have h := unpair_le_right v,
  rw e at h,
  rcases have v₂ < succ v, from lt_succ_of_le h,
    denumerable_list_aux v₂ with ⟨a, h₁, h₂⟩,
  simp at h₁,
  simp [decode_list, e, h₂, h₁, encode_list, mkpair_unpair' e]
end

instance denumerable_list : denumerable (list α) := ⟨denumerable_list_aux⟩

@[simp] theorem list_of_nat_zero : of_nat (list α) 0 = [] := rfl

@[simp] theorem list_of_nat_succ (v : ℕ) :
  of_nat (list α) (succ v) =
  of_nat α v.unpair.1 :: of_nat (list α) v.unpair.2 :=
of_nat_of_decode $ show decode_list (succ v) = _,
begin
  cases e : unpair v with v₁ v₂,
  simp [decode_list, e],
  rw [show decode_list v₂ = decode (list α) v₂,
      from rfl, decode_eq_of_nat]; refl
end

end list

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
  by simp [raise, lower, nat.sub_add_cancel this,
           raise_lower (list.sorted_of_sorted_cons h)]

lemma raise_chain : ∀ l n, list.chain (≤) n (raise l n)
| []       n := list.chain.nil
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
  by simp [raise', lower', nat.sub_add_cancel this, raise_lower'
    (list.rel_of_sorted_cons h₂ : ∀ a ∈ l, m < a) (list.sorted_of_sorted_cons h₂)]

lemma raise'_chain : ∀ l {m n}, m < n → list.chain (<) m (raise' l n)
| []       m n h := list.chain.nil
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

end denumerable

namespace equiv

/-- The type lists on unit is canonically equivalent to the natural numbers. -/
def list_unit_equiv : list unit ≃ ℕ :=
{ to_fun := list.length,
  inv_fun := list.repeat (),
  left_inv := λ u, list.injective_length (by simp),
  right_inv := λ n, list.length_repeat () n }

def list_nat_equiv_nat : list ℕ ≃ ℕ := denumerable.eqv _

def list_equiv_self_of_equiv_nat {α : Type} (e : α ≃ ℕ) : list α ≃ α :=
calc list α ≃ list ℕ : list_equiv_of_equiv e
        ... ≃ ℕ      : list_nat_equiv_nat
        ... ≃ α      : e.symm
end equiv
