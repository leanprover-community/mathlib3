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
* `primcodable` instances for terms and formulas, based on the `encoding`s
* Computability facts about term and formula operations, to set up a computability approach to
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
def list_decode :
  list (α ⊕ Σ i, L.functions i) → list (option (L.term α))
| [] := []
| ((sum.inl a) :: l) := some (var a) :: list_decode l
| ((sum.inr ⟨n, f⟩) :: l) :=
  if h : ∀ (i : fin n), ((list_decode l).nth i).join.is_some
  then func f (λ i, option.get (h i)) :: ((list_decode l).drop n)
  else [none]

theorem list_decode_encode_list (l : list (L.term α)) :
  list_decode (l.bind list_encode) = l.map option.some :=
begin
  suffices h : ∀ (t : L.term α) (l : list (α ⊕ Σ i, L.functions i)),
    list_decode (t.list_encode ++ l) = some t :: list_decode l,
  { induction l with t l lih,
    { refl },
    { rw [cons_bind, h t (l.bind list_encode), lih, list.map] } },
  { intro t,
    induction t with a n f ts ih; intro l,
    { rw [list_encode, singleton_append, list_decode] },
    { rw [list_encode, cons_append, list_decode],
      have h : list_decode ((fin_range n).bind (λ (i : fin n), (ts i).list_encode) ++ l) =
        (fin_range n).map (option.some ∘ ts) ++ list_decode l,
      { induction (fin_range n) with i l' l'ih,
        { refl },
        { rw [cons_bind, append_assoc, ih, map_cons, l'ih, cons_append] } },
      have h' : ∀ i, (list_decode ((fin_range n).bind (λ (i : fin n), (ts i).list_encode) ++ l)).nth ↑i = some (some (ts i)),
      { intro i,
        rw [h, nth_append, nth_map],
        { simp only [option.map_eq_some', function.comp_app, nth_eq_some],
          refine ⟨i, ⟨lt_of_lt_of_le i.2 (ge_of_eq (length_fin_range _)), _⟩, rfl⟩,
          rw [nth_le_fin_range, fin.eta] },
        { refine lt_of_lt_of_le i.2 _,
          simp } },
      refine (dif_pos (λ i, option.is_some_iff_exists.2 ⟨ts i, _⟩)).trans _,
      { rw [option.join_eq_some, h'] },
      refine congr (congr rfl (congr rfl (congr rfl (funext (λ i, option.get_of_mem _ _))))) _,
      { simp [h'] },
      { rw [h, drop_left'],
        rw [length_map, length_fin_range] } } }
end

/-- An encoding of terms as lists. -/
@[simps] protected def encoding : encoding (L.term α) :=
{ Γ := α ⊕ Σ i, L.functions i,
  encode := list_encode,
  decode := λ l, (list_decode l).head'.join,
  decode_encode := λ t, begin
    have h := list_decode_encode_list [t],
    rw [bind_singleton] at h,
    simp only [h, option.join, head', list.map, option.some_bind, id.def],
  end }

lemma list_encode_injective :
  function.injective (list_encode : L.term α → list (α ⊕ Σ i, L.functions i)) :=
term.encoding.encode_injective

theorem card_le : # (L.term α) ≤ max ω (# (α ⊕ Σ i, L.functions i)) :=
lift_le.1 (trans term.encoding.card_le_card_list (lift_le.2 (mk_list_le_max _)))

instance [encodable α] [encodable ((Σ i, L.functions i))] :
  encodable (L.term α) :=
encodable.of_left_injection list_encode (λ l, (list_decode l).head'.join)
  (λ t, begin
    rw [← bind_singleton list_encode, list_decode_encode_list],
    simp only [option.join, head', list.map, option.some_bind, id.def],
  end)

lemma card_le_omega [h1 : nonempty (encodable α)] [h2 : L.countable_functions] :
  # (L.term α) ≤ ω :=
begin
  refine (card_le.trans _),
  rw [max_le_iff],
  simp only [le_refl, mk_sum, add_le_omega, lift_le_omega, true_and],
  exact ⟨encodable_iff.1 h1, L.card_functions_le_omega⟩,
end

instance small [small.{u} α] :
  small.{u} (L.term α) :=
small_of_injective list_encode_injective

end term

end language
end first_order
