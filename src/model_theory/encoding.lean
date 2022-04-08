/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import model_theory.syntax
import set_theory.cardinal_ordinal
import computability.encoding

/-! # Encodings and Cardinality of First-Order Syntax

## Main Definitions
* Terms can be encoded as lists with `first_order.language.term.list_encode` and
`first_order.language.term.list_decode`.

## Main Results
* `first_order.language.term.card_le` shows that the number of terms in `L.term α` is at most
`# (α ⊕ Σ i, L.functions i) + ω`.

## TODO
* An encoding for formulas
* `fin_encoding`s for terms and formulas, based on the `encoding`s
* Computability facts about these `fin_encoding`s, to set up a computability approach to
incompleteness

-/

universes u v w u' v'

namespace first_order
namespace language

variables {L : language.{u v}}
variables {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variables {α : Type u'} {β : Type v'}
open_locale first_order cardinal
open computability list Structure cardinal fin

namespace term

/-- Encodes a term as a list of variables and function symbols. -/
def list_encode : L.term α → list (α ⊕ (Σ i, L.functions i))
| (var i) := [sum.inl i]
| (func f ts) := ((sum.inr (⟨_, f⟩ : Σ i, L.functions i)) ::
    ((list.fin_range _).bind (λ i, (ts i).list_encode)))

/-- Decodes a list of variables and function symbols as a list of terms. -/
def list_decode [inhabited (L.term α)] :
  list (α ⊕ (Σ i, L.functions i)) → list (L.term α)
| [] := []
| ((sum.inl a) :: l) := var a :: list_decode l
| ((sum.inr ⟨n, f⟩) :: l) := func f (λ i, ((list_decode l).nth i).iget) :: ((list_decode l).drop n)

@[simp] theorem list_decode_encode_list [inhabited (L.term α)] (l : list (L.term α)) :
  list_decode (l.bind list_encode) = l :=
begin
  suffices h : ∀ (t : L.term α) (l : list (α ⊕ (Σ i, L.functions i))),
    list_decode (t.list_encode ++ l) = t :: list_decode l,
  { induction l with t l lih,
    { refl },
    { rw [cons_bind, h t (l.bind list_encode), lih] } },
  { intro t,
    induction t with a n f ts ih; intro l,
    { rw [list_encode, singleton_append, list_decode] },
    { rw [list_encode, cons_append, list_decode],
      have h : list_decode ((fin_range n).bind (λ (i : fin n), (ts i).list_encode) ++ l) =
        (fin_range n).map ts ++ list_decode l,
      { induction (fin_range n) with i l' l'ih,
        { refl },
        { rw [cons_bind, append_assoc, ih, map_cons, l'ih, cons_append] } },
      have h' : n ≤ (list_decode ((fin_range n).bind (λ (i : fin n),
        (ts i).list_encode) ++ l)).length,
      { rw [h, length_append, length_map, length_fin_range],
        exact le_self_add, },
      refine congr (congr rfl (congr rfl (funext (λ i, _)))) _,
      { rw [nth_le_nth (lt_of_lt_of_le i.is_lt h'), option.iget_some, nth_le_of_eq h, nth_le_append,
          nth_le_map, nth_le_fin_range, fin.eta],
        { rw [length_fin_range],
          exact i.is_lt },
        { rw [length_map, length_fin_range],
          exact i.is_lt } },
      { rw [h, drop_left'],
        rw [length_map, length_fin_range] } } }
end

/-- An encoding of terms as lists. -/
@[simps] protected def encoding [inhabited (L.term α)] : encoding (L.term α) :=
{ Γ := (α ⊕ (Σ i, L.functions i)),
  encode := list_encode,
  decode := λ l, (list_decode l).head',
  decode_encode := λ t, begin
    have h := list_decode_encode_list [t],
    rw [bind_singleton] at h,
    rw [h, head'],
  end }

lemma list_encode_injective :
  function.injective (list_encode : L.term α → list (α ⊕ (Σ i, L.functions i))) :=
begin
  casesI is_empty_or_nonempty (L.term α) with he hne,
  { exact he.elim },
  { inhabit (L.term α),
    exact term.encoding.encode_injective }
end

theorem card_le : # (L.term α) ≤ # (α ⊕ (Σ i, L.functions i)) + ω :=
begin
  have h := (mk_le_of_injective list_encode_injective),
  refine h.trans _,
  casesI fintype_or_infinite (α ⊕ (Σ i, L.functions i)) with ft inf,
  { haveI := fintype.encodable (α ⊕ (Σ i, L.functions i)),
    exact le_add_left (encodable_iff.1 ⟨encodable.list⟩) },
  { rw mk_list_eq_mk,
    exact le_self_add }
end

instance [encodable α] [encodable ((Σ i, L.functions i))] [inhabited (L.term α)] :
  encodable (L.term α) :=
encodable.of_left_injection list_encode (λ l, (list_decode l).head')
  (λ t, by rw [← bind_singleton list_encode, list_decode_encode_list, head'])

lemma card_le_omega [h1 : nonempty (encodable α)] [h2 : L.countable_functions] :
  # (L.term α) ≤ ω :=
begin
  refine (card_le.trans _),
  rw [add_le_omega, mk_sum, add_le_omega, lift_le_omega, lift_le_omega, ← encodable_iff],
  exact ⟨⟨h1, L.card_functions_le_omega⟩, refl _⟩,
end

instance small [small.{u} α] :
  small.{u} (L.term α) :=
small_of_injective list_encode_injective

end term

namespace bounded_formula

variables (L) (α)

/-- A type of symbols used to encode formulas as lists. -/
inductive list_symbols : Type (max u v u')
| f (n : ℕ)
| e (n : ℕ) (t₁ t₂ : L.term (α ⊕ fin n))
| r (k n : ℕ) (R : L.relations n) (ts : fin n → L.term (α ⊕ fin k))
| i
| a

open list_symbols

instance : inhabited (list_symbols L α) := ⟨a⟩

variables {L} {α}

/-- Encodes a bounded formula as a list of symbols. -/
def list_encode : ∀ {n : ℕ}, L.bounded_formula α n →
  list (list_symbols L α)
| n falsum := [list_symbols.f n]
| n (equal t₁ t₂) := [list_symbols.e n t₁ t₂]
| n (rel R ts) := [list_symbols.r _ _ R ts]
| n (imp φ₁ φ₂) := list_symbols.i :: φ₁.list_encode ++ φ₂.list_encode
| n (all φ) := list_symbols.a :: φ.list_encode

/-- Applies the `forall` quantifier to an element of `(Σ n, L.bounded_formula α n)`,
or returns `default` if not possible. -/
def sigma_all : (Σ n, L.bounded_formula α n) → Σ n, L.bounded_formula α n
| ⟨(n + 1), φ⟩ := ⟨n, φ.all⟩
| _ := default

/-- Applies `imp` to two elements of `(Σ n, L.bounded_formula α n)`,
or returns `default` if not possible. -/
def sigma_imp :
  (Σ n, L.bounded_formula α n) → (Σ n, L.bounded_formula α n) → (Σ n, L.bounded_formula α n)
| ⟨m, φ⟩ ⟨n, ψ⟩ := if h : m = n then ⟨m, φ.imp (eq.mp (by rw h) ψ)⟩ else default

/-- Decodes a list of symbols as a list of formulas. -/
def list_decode :
  list (list_symbols L α) → (Σ n, L.bounded_formula α n) × list (list_symbols L α)
| (f n :: l) := ⟨⟨n, falsum⟩, l⟩
| (e n t₁ t₂ :: l) := ⟨⟨n, equal t₁ t₂⟩, l⟩
| (r k n R ts :: l) := ⟨⟨k, rel R ts⟩, l⟩
| (i :: l) := if h : (list_decode l).2.sizeof < 1 + 1 + l.sizeof
  then ⟨sigma_imp (list_decode l).1 (list_decode (list_decode l).2).1,
    (list_decode (list_decode l).2).2⟩
  else ⟨default, []⟩
| (a :: l) := ⟨sigma_all (list_decode l).1, (list_decode l).2⟩
| _ := ⟨default, []⟩

lemma list_decode_sizeof (l : list (list_symbols L α)) : (list_decode l).2.sizeof ≤ l.sizeof :=
begin
  suffices h : ∀ n (l : list (list_symbols L α)),
    l.sizeof ≤ n → (list_decode l).2.sizeof ≤ l.sizeof,
  { exact h _ l le_rfl },
  intro n,
  induction n with n ih; intros l h,
  { cases l,
    { simp [list_decode, list.sizeof] },
    { contrapose! h,
      rw [list.sizeof, add_assoc, add_comm],
      exact nat.succ_pos' } },
  { cases l with s t,
    { simp [list_decode, list.sizeof] },
    { rw [list.sizeof, add_assoc, add_comm, add_le_add_iff_right 1] at h,
      cases s,
      { simp [list_decode, list.sizeof] },
      { simp [list_decode, list.sizeof] },
      { simp [list_decode, list.sizeof] },
      { have h' := ih t ((nat.le_add_left _ _).trans h),
        rw [list_decode, list.sizeof, if_pos (lt_of_le_of_lt h' _)],
        { exact trans (ih (list_decode t).snd (h'.trans (trans (nat.le_add_left _ _) h)))
            (h'.trans (nat.le_add_left _ _)), },
        { simp only [lt_add_iff_pos_left, nat.succ_pos'] } },
      { simp [list_decode, list.sizeof],
        exact (ih t ((nat.le_add_left _ _).trans h)).trans (nat.le_add_left _ _) } } }
end

lemma list_decode_imp (l : list (list_symbols L α)) :
  list_decode (i :: l) = ⟨sigma_imp (list_decode l).1 (list_decode (list_decode l).2).1,
    (list_decode (list_decode l).2).2⟩ :=
begin
  rw [list_decode, if_pos],
  rw [add_comm, ← add_assoc, nat.lt_succ_iff],
  exact trans (list_decode_sizeof _) (nat.le_succ _),
end

@[simp] theorem list_decode_encode_list (l : list (Σ n, L.bounded_formula α n)) :
  list_decode (l.bind (λ φ, φ.2.list_encode)) = ⟨l.head, l.tail.bind (λ φ, φ.2.list_encode)⟩ :=
begin
  suffices h : ∀ (φ : (Σ n, L.bounded_formula α n)) (l : list (list_symbols L α)),
    list_decode (list_encode φ.2 ++ l) = ⟨φ, l⟩,
  { induction l with φ l lih,
    { simp [list_decode] },
    { rw [cons_bind, h φ _],
      refl } },
  { rintro ⟨n, φ⟩,
    induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih; intro l,
    { rw [list_encode, singleton_append, list_decode] },
    { rw [list_encode, singleton_append, list_decode] },
    { rw [list_encode, singleton_append, list_decode] },
    { rw [list_encode, append_assoc, cons_append, list_decode_imp, ih1, ih2, sigma_imp,
        dif_pos rfl],
      refl, },
    { rw [list_encode, cons_append, list_decode, ih, sigma_all] } }
end

end bounded_formula

end language
end first_order
