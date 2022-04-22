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
* `first_order.language.term.encoding` encodes terms as lists.
* `first_order.language.bounded_formula.encoding` encodes bounded formulas as lists.

## Main Results
* `first_order.language.term.card_le` shows that the number of terms in `L.term α` is at most
`# (α ⊕ Σ i, L.functions i) + ω`.

## TODO
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

/-- Encodes a bounded formula as a list of symbols. -/
def list_encode : ∀ {n : ℕ}, L.bounded_formula α n →
  list ((Σ k, L.term (α ⊕ fin k)) ⊕ (Σ n, L.relations n) ⊕ ℕ)
| n falsum := [sum.inr (sum.inr (n + 3))]
| n (equal t₁ t₂) := [sum.inr (sum.inr 0), sum.inl ⟨_, t₁⟩, sum.inl ⟨_, t₂⟩]
| n (rel R ts) := [sum.inr (sum.inl ⟨_, R⟩), sum.inr (sum.inr n)] ++
  ((list.fin_range _).map (λ i, sum.inl ⟨n, (ts i)⟩))
| n (imp φ₁ φ₂) := (sum.inr (sum.inr 1)) :: φ₁.list_encode ++ φ₂.list_encode
| n (all φ) := (sum.inr (sum.inr 2)) :: φ.list_encode

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

lemma _root_.list.drop_sizeof_le [has_sizeof α] (l : list α) : ∀ (n : ℕ), (l.drop n).sizeof ≤ l.sizeof :=
begin
  induction l with _ _ lih; intro n,
  { rw [drop_nil] },
  { induction n with n nih,
    { refl, },
    { exact trans (lih _) le_add_self } }
end

/-- Decodes a list of symbols as a list of formulas. -/
@[simp] def list_decode :
  Π (l : list ((Σ k, L.term (α ⊕ fin k)) ⊕ (Σ n, L.relations n) ⊕ ℕ)),
    (Σ n, L.bounded_formula α n) ×
    { l' : list ((Σ k, L.term (α ⊕ fin k)) ⊕ (Σ n, L.relations n) ⊕ ℕ) // l'.sizeof ≤ max 1 l.sizeof }
| ((sum.inr (sum.inr (n + 3))) :: l) := ⟨⟨n, falsum⟩, l, le_max_of_le_right le_add_self⟩
| ((sum.inr (sum.inr 0)) :: (sum.inl ⟨n₁, t₁⟩) :: sum.inl ⟨n₂, t₂⟩ :: l) :=
    ⟨if h : n₁ = n₂ then ⟨n₁, equal t₁ (eq.mp (by rw h) t₂)⟩ else default, l, begin
      simp only [list.sizeof, ← add_assoc],
      exact le_max_of_le_right le_add_self,
    end⟩
| (sum.inr (sum.inl ⟨n, R⟩) :: (sum.inr (sum.inr k)) :: l) := ⟨
    if h : ∀ (i : fin n), ((l.map sum.get_left).nth i).join.is_some
    then if h' : ∀ i, (option.get (h i)).1 = k
      then ⟨k, bounded_formula.rel R (λ i, eq.mp (by rw h' i) (option.get (h i)).2)⟩
      else default
    else default,
    l.drop n, le_max_of_le_right (le_add_left (le_add_left (list.drop_sizeof_le _ _)))⟩
| ((sum.inr (sum.inr 1)) :: l) :=
  have (↑((list_decode l).2) : list ((Σ k, L.term (α ⊕ fin k)) ⊕ (Σ n, L.relations n) ⊕ ℕ)).sizeof
    < 1 + (1 + (1 + 1)) + l.sizeof, from begin
      refine lt_of_le_of_lt (list_decode l).2.2 (max_lt _ (nat.lt_add_of_pos_left dec_trivial)),
      rw [add_assoc, add_comm, nat.lt_succ_iff, add_assoc],
      exact le_self_add,
    end,
  ⟨sigma_imp (list_decode l).1 (list_decode (list_decode l).2).1,
    (list_decode (list_decode l).2).2, le_max_of_le_right (trans (list_decode _).2.2 (max_le
      (le_add_right le_self_add) (trans (list_decode _).2.2
      (max_le (le_add_right le_self_add) le_add_self))))⟩
| ((sum.inr (sum.inr 2)) :: l) := ⟨sigma_all (list_decode l).1, (list_decode l).2,
  (list_decode l).2.2.trans (max_le_max le_rfl le_add_self)⟩
| _ := ⟨default, [], le_max_left _ _⟩

@[simp] theorem list_decode_encode_list (l : list (Σ n, L.bounded_formula α n)) :
  (list_decode (l.bind (λ φ, φ.2.list_encode))).1 = l.head :=
begin
  suffices h : ∀ (φ : (Σ n, L.bounded_formula α n)) l,
    (list_decode (list_encode φ.2 ++ l)).1 = φ ∧ (list_decode (list_encode φ.2 ++ l)).2.1 = l,
  { induction l with φ l lih,
    { rw [list.nil_bind],
      simp [list_decode], },
    { rw [cons_bind, (h φ _).1, head_cons] } },
  { rintro ⟨n, φ⟩,
    induction φ with _ _ _ _ _ _ _ ts _ _ _ ih1 ih2 _ _ ih; intro l,
    { rw [list_encode, singleton_append, list_decode],
      simp only [eq_self_iff_true, heq_iff_eq, and_self], },
    { rw [list_encode, cons_append, cons_append, cons_append, list_decode, dif_pos],
      { simp only [eq_mp_eq_cast, cast_eq, eq_self_iff_true, heq_iff_eq, and_self, nil_append], },
      { simp only [eq_self_iff_true, heq_iff_eq, and_self], } },
    { rw [list_encode, cons_append, cons_append, singleton_append, cons_append, list_decode],
      { have h : ∀ (i : fin φ_l), ((list.map sum.get_left (list.map (λ (i : fin φ_l),
          sum.inl (⟨(⟨φ_n, rel φ_R ts⟩ : Σ n, L.bounded_formula α n).fst, ts i⟩ :
            Σ n, L.term (α ⊕ fin n))) (fin_range φ_l) ++ l)).nth ↑i).join = some ⟨_, ts i⟩,
        { intro i,
          simp only [option.join, map_append, map_map, option.bind_eq_some, id.def, exists_eq_right,
            nth_eq_some, length_append, length_map, length_fin_range],
          refine ⟨lt_of_lt_of_le i.2 le_self_add, _⟩,
          rw [nth_le_append, nth_le_map],
          { simp only [sum.get_left, nth_le_fin_range, fin.eta, function.comp_app, eq_self_iff_true,
            heq_iff_eq, and_self] },
          { exact lt_of_lt_of_le i.is_lt (ge_of_eq (length_fin_range _)) },
          { rw [length_map, length_fin_range],
            exact i.2 } },
        rw dif_pos, swap,
        { exact λ i, option.is_some_iff_exists.2 ⟨⟨_, ts i⟩, h i⟩ },
        rw dif_pos, swap,
        { intro i,
          obtain ⟨h1, h2⟩ := option.eq_some_iff_get_eq.1 (h i),
          rw h2 },
        simp only [eq_self_iff_true, heq_iff_eq, true_and],
        refine ⟨funext (λ i, _), _⟩,
        { obtain ⟨h1, h2⟩ := option.eq_some_iff_get_eq.1 (h i),
          rw [eq_mp_eq_cast, cast_eq_iff_heq],
          exact (sigma.ext_iff.1 ((sigma.eta (option.get h1)).trans h2)).2 },
        rw [list.drop_append_eq_append_drop, length_map, length_fin_range, nat.sub_self, drop,
          drop_eq_nil_of_le, nil_append],
        rw [length_map, length_fin_range], }, },
    { rw [list_encode, append_assoc, cons_append, list_decode],
      simp only [subtype.val_eq_coe] at *,
      rw [(ih1 _).1, (ih1 _).2, (ih2 _).1, (ih2 _).2, sigma_imp, dif_pos rfl],
      exact ⟨rfl, rfl⟩, },
    { rw [list_encode, cons_append, list_decode],
      simp only,
      simp only [subtype.val_eq_coe] at *,
      rw [(ih _).1, (ih _).2, sigma_all],
      exact ⟨rfl, rfl⟩ } }
end

/-- An encoding of bounded formulas as lists. -/
@[simps] protected def encoding : encoding (Σ n, L.bounded_formula α n) :=
{ Γ := (Σ k, L.term (α ⊕ fin k)) ⊕ (Σ n, L.relations n) ⊕ ℕ,
  encode := λ φ, φ.2.list_encode,
  decode := λ l, (list_decode l).1,
  decode_encode := λ φ, begin
    have h := list_decode_encode_list [φ],
    rw [bind_singleton] at h,
    rw h,
    refl,
  end }

lemma list_encode_sigma_injective :
  function.injective (λ (φ : Σ n, L.bounded_formula α n), φ.2.list_encode) :=
bounded_formula.encoding.encode_injective

end bounded_formula

end language
end first_order
