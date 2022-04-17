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
def list_encode : L.term α → list (α ⊕ Σ i, L.functions i)
| (var i) := [sum.inl i]
| (func f ts) := ((sum.inr (⟨_, f⟩ : Σ i, L.functions i)) ::
    ((list.fin_range _).bind (λ i, (ts i).list_encode)))

/-- Decodes a list of variables and function symbols as a list of terms. -/
def list_decode [inhabited (L.term α)] :
  list (α ⊕ Σ i, L.functions i) → list (L.term α)
| [] := []
| ((sum.inl a) :: l) := var a :: list_decode l
| ((sum.inr ⟨n, f⟩) :: l) := func f (λ i, ((list_decode l).nth i).iget) :: ((list_decode l).drop n)

@[simp] theorem list_decode_encode_list [inhabited (L.term α)] (l : list (L.term α)) :
  list_decode (l.bind list_encode) = l :=
begin
  suffices h : ∀ (t : L.term α) (l : list (α ⊕ Σ i, L.functions i)),
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
{ Γ := α ⊕ Σ i, L.functions i,
  encode := list_encode,
  decode := λ l, (list_decode l).head',
  decode_encode := λ t, begin
    have h := list_decode_encode_list [t],
    rw [bind_singleton] at h,
    rw [h, head'],
  end }

lemma list_encode_injective :
  function.injective (list_encode : L.term α → list (α ⊕ Σ i, L.functions i)) :=
begin
  casesI is_empty_or_nonempty (L.term α) with he hne,
  { exact he.elim },
  { inhabit (L.term α),
    exact term.encoding.encode_injective }
end

theorem card_le : # (L.term α) ≤ # (α ⊕ Σ i, L.functions i) + ω :=
begin
  have h := (mk_le_of_injective list_encode_injective),
  refine h.trans _,
  casesI fintype_or_infinite (α ⊕ Σ i, L.functions i) with ft inf,
  { haveI := fintype.to_encodable (α ⊕ Σ i, L.functions i),
    exact le_add_left mk_le_omega },
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

end language
end first_order
