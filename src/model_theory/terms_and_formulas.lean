/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import data.equiv.fin
import data.finset.basic
import model_theory.basic
import set_theory.cardinal_ordinal

/-!
# Basics on First-Order Structures
This file defines first-order languages and structures in a style inspired by the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions
* A `first_order.language.term` is defined so that `L.term α` is the type of `L`-terms with free
  variables indexed by `α`.
* A `first_order.language.formula` is defined so that `L.formula α` is the type of `L`-formulas with
  free variables indexed by `α`.
* A `first_order.language.sentence` is a formula with no free variables.
* A `first_order.language.Theory` is a set of sentences.
* `first_order.language.Theory.is_satisfiable` indicates that a theory has a nonempty model.
* Given a theory `T`, `first_order.language.Theory.semantically_equivalent` defines an equivalence
relation `T.semantically_equivalent` on formulas of a particular signature, indicating that the
formulas have the same realization in models of `T`. (This is more often known as logical
equivalence once it is known that this is equivalent to the proof-theoretic definition.)

## Main Results
* `first_order.language.term.card_le` shows that the number of terms in `L.term α` is at most
`# (α ⊕ Σ i, L.functions i) + ω`.

## Implementation Notes
* Formulas use a modified version of de Bruijn variables. Specifically, a `L.bounded_formula α n`
is a formula with some variables indexed by a type `α`, which cannot be quantified over, and some
indexed by `fin n`, which can. For any `φ : L.bounded_formula α (n + 1)`, we define the formula
`∀' φ : L.bounded_formula α n` by universally quantifying over the variable indexed by
`n : fin (n + 1)`.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/

universes u v w u' v'

namespace first_order
namespace language

variables (L : language.{u v}) {L' : language}
variables {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variables {α : Type u'} {β : Type v'}
open_locale first_order cardinal
open Structure cardinal fin

/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive term (α : Type u') : Type (max u u')
| var {} : ∀ (a : α), term
| func {} : ∀ {l : ℕ} (f : L.functions l) (ts : fin l → term), term
export term

variable {L}

namespace term

open list

/-- Relabels a term's variables along a particular function. -/
@[simp] def relabel (g : α → β) : L.term α → L.term β
| (var i) := var (g i)
| (func f ts) := func f (λ i, (ts i).relabel)

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

lemma list_encode_injective :
  function.injective (list_encode : L.term α → list (α ⊕ (Σ i, L.functions i))) :=
begin
  cases is_empty_or_nonempty (L.term α) with he hne,
  { exact he.elim },
  { resetI,
    inhabit (L.term α),
    intros t1 t2 h,
    have h' : (list_decode ([t1].bind (list_encode))) = (list_decode ([t2].bind (list_encode))),
    { rw [bind_singleton, h, bind_singleton] },
    rw [list_decode_encode_list, list_decode_encode_list] at h',
    exact head_eq_of_cons_eq h' }
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

instance inhabited_of_var [inhabited α] : inhabited (L.term α) :=
⟨var default⟩

end term

/-- The representation of a constant symbol as a term. -/
def constants.term (c : L.constants) : (L.term α) :=
func c default

namespace term

instance inhabited_of_constant [inhabited L.constants] : inhabited (L.term α) :=
⟨(default : L.constants).term⟩

/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
@[simp] def realize (v : α → M) :
  ∀ (t : L.term α), M
| (var k)         := v k
| (func f ts)     := fun_map f (λ i, (ts i).realize)

@[simp] lemma realize_relabel {t : L.term α} {g : α → β} {v : β → M} :
  (t.relabel g).realize v = t.realize (v ∘ g) :=
begin
  induction t with _ n f ts ih,
  { refl, },
  { simp [ih] }
end

/-- Raises all of the `fin`-indexed variables of a term greater than or equal to `m` by `n'`. -/
def lift_at {n : ℕ} (n' m : ℕ) : L.term (α ⊕ fin n) → L.term (α ⊕ fin (n + n')) :=
relabel (sum.map id (λ i, if ↑i < m then fin.cast_add n' i else fin.add_nat n' i))

@[simp] lemma realize_lift_at {n n' m : ℕ} {t : L.term (α ⊕ fin n)}
  {v : (α ⊕ fin (n + n')) → M} :
  (t.lift_at n' m).realize v = t.realize (v ∘
    (sum.map id (λ i, if ↑i < m then fin.cast_add n' i else fin.add_nat n' i))) :=
realize_relabel

@[simp] lemma realize_constants {c : L.constants} {v : α → M} :
  c.term.realize v = c :=
fun_map_eq_coe_constants

lemma realize_con {A : set M} {a : A} {v : α → M} :
  (L.con a).term.realize v = a := rfl

end term

localized "prefix `&`:max := first_order.language.term.var ∘ sum.inr" in first_order

namespace Lhom

/-- Maps a term's symbols along a language map. -/
@[simp] def on_term (φ : L →ᴸ L') : L.term α → L'.term α
| (var i) := var i
| (func f ts) := func (φ.on_function f) (λ i, on_term (ts i))

@[simp] lemma id_on_term :
  ((Lhom.id L).on_term : L.term α → L.term α) = id :=
begin
  ext t,
  induction t with _ _ _ _ ih,
  { refl },
  { simp_rw [on_term, ih],
    refl, },
end

@[simp] lemma comp_on_term {L'' : language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
  ((φ.comp ψ).on_term : L.term α → L''.term α) = φ.on_term ∘ ψ.on_term :=
begin
  ext t,
  induction t with _ _ _ _ ih,
  { refl },
  { simp_rw [on_term, ih],
    refl, },
end

@[simp] lemma realize_on_term [L'.Structure M] (φ : L →ᴸ L') [φ.is_expansion_on M]
  (t : L.term α) (v : α → M) :
  (φ.on_term t).realize v = t.realize v :=
begin
  induction t with _ n f ts ih,
  { refl },
  { simp only [term.realize, Lhom.on_term, Lhom.is_expansion_on.map_on_function, ih] }
end

end Lhom

/-- Maps a term's symbols along a language equivalence. -/
@[simps] def Lequiv.on_term (φ : L ≃ᴸ L') : L.term α ≃ L'.term α :=
{ to_fun := φ.to_Lhom.on_term,
  inv_fun := φ.inv_Lhom.on_term,
  left_inv := by rw [function.left_inverse_iff_comp, ← Lhom.comp_on_term, φ.left_inv,
    Lhom.id_on_term],
  right_inv := by rw [function.right_inverse_iff_comp, ← Lhom.comp_on_term, φ.right_inv,
    Lhom.id_on_term] }

@[simp] lemma hom.realize_term (g : M →[L] N) {t : L.term α} {v : α → M} :
  t.realize (g ∘ v) = g (t.realize v) :=
begin
  induction t,
  { refl },
  { rw [term.realize, term.realize, g.map_fun],
    refine congr rfl _,
    ext x,
    simp [t_ih x], },
end

@[simp] lemma embedding.realize_term {v : α → M}
  (t : L.term α) (g : M ↪[L] N) :
  t.realize (g ∘ v) = g (t.realize v) :=
g.to_hom.realize_term

@[simp] lemma equiv.realize_term {v : α → M}
  (t : L.term α) (g : M ≃[L] N) :
  t.realize (g ∘ v) = g (t.realize v) :=
g.to_hom.realize_term

variables (L) (α)
/-- `bounded_formula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive bounded_formula : ℕ → Type (max u v u')
| falsum {} {n} : bounded_formula n
| equal {n} (t₁ t₂ : L.term (α ⊕ fin n)) : bounded_formula n
| rel {n l : ℕ} (R : L.relations l) (ts : fin l → L.term (α ⊕ fin n)) : bounded_formula n
| imp {n} (f₁ f₂ : bounded_formula n) : bounded_formula n
| all {n} (f : bounded_formula (n+1)) : bounded_formula n

/-- `formula α` is the type of formulas with all free variables indexed by `α`. -/
@[reducible] def formula := L.bounded_formula α 0

/-- A sentence is a formula with no free variables. -/
@[reducible] def sentence := L.formula empty

/-- A theory is a set of sentences. -/
@[reducible] def Theory := set L.sentence

variables {L} {α} {n : ℕ}

/-- Applies a relation to terms as a bounded formula. -/
def relations.bounded_formula {l : ℕ} (R : L.relations n) (ts : fin n → L.term (α ⊕ fin l)) :
  L.bounded_formula α l := bounded_formula.rel R ts

/-- The equality of two terms as a bounded formula. -/
def term.bd_equal (t₁ t₂ : L.term (α ⊕ fin n)) : (L.bounded_formula α n) :=
bounded_formula.equal t₁ t₂

/-- Applies a relation to terms as a bounded formula. -/
def relations.formula (R : L.relations n) (ts : fin n → L.term α) :
  L.formula α := R.bounded_formula (λ i, (ts i).relabel sum.inl)

/-- The equality of two terms as a first-order formula. -/
def term.equal (t₁ t₂ : L.term α) : (L.formula α) :=
(t₁.relabel sum.inl).bd_equal (t₂.relabel sum.inl)

namespace bounded_formula

instance : inhabited (L.bounded_formula α n) :=
⟨falsum⟩

instance : has_bot (L.bounded_formula α n) := ⟨falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[pattern] protected def not (φ : L.bounded_formula α n) : L.bounded_formula α n := φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
@[pattern] protected def ex (φ : L.bounded_formula α (n + 1)) : L.bounded_formula α n :=
  φ.not.all.not

instance : has_top (L.bounded_formula α n) := ⟨bounded_formula.not ⊥⟩

instance : has_inf (L.bounded_formula α n) := ⟨λ f g, (f.imp g.not).not⟩

instance : has_sup (L.bounded_formula α n) := ⟨λ f g, f.not.imp g⟩

/-- The biimplication between two bounded formulas. -/
protected def iff (φ ψ : L.bounded_formula α n) := φ.imp ψ ⊓ ψ.imp φ

/-- Casts `L.bounded_formula α m` as `L.bounded_formula α n`, where `m ≤ n`. -/
def cast_le : ∀ {m n : ℕ} (h : m ≤ n), L.bounded_formula α m → L.bounded_formula α n
| m n h falsum := falsum
| m n h (equal t₁ t₂) := (t₁.relabel (sum.map id (fin.cast_le h))).bd_equal
    (t₂.relabel (sum.map id (fin.cast_le h)))
| m n h (rel R ts) := R.bounded_formula (term.relabel (sum.map id (fin.cast_le h)) ∘ ts)
| m n h (imp f₁ f₂) := (f₁.cast_le h).imp (f₂.cast_le h)
| m n h (all f) := (f.cast_le (add_le_add_right h 1)).all

/-- A function to help relabel the variables in bounded formulas. -/
def relabel_aux (g : α → (β ⊕ fin n)) (k : ℕ) :
  α ⊕ fin k → β ⊕ fin (n + k) :=
(sum.map id fin_sum_fin_equiv) ∘ (equiv.sum_assoc _ _ _) ∘ (sum.map g id)

@[simp] lemma sum_elim_comp_relabel_aux {m : ℕ} {g : α → (β ⊕ fin n)}
  {v : β → M} {xs : fin (n + m) → M} :
  sum.elim v xs ∘ relabel_aux g m =
    sum.elim (sum.elim v (xs ∘ cast_add m) ∘ g) (xs ∘ nat_add n) :=
begin
  ext x,
  cases x,
  { simp only [bounded_formula.relabel_aux, function.comp_app, sum.map_inl, sum.elim_inl],
    cases g x with l r;
    simp },
  { simp [bounded_formula.relabel_aux] }
end

/-- Relabels a bounded formula's variables along a particular function. -/
def relabel (g : α → (β ⊕ fin n)) :
  ∀ {k : ℕ}, L.bounded_formula α k → L.bounded_formula β (n + k)
| k falsum := falsum
| k (equal t₁ t₂) := (t₁.relabel (relabel_aux g k)).bd_equal (t₂.relabel (relabel_aux g k))
| k (rel R ts) := R.bounded_formula (term.relabel (relabel_aux g k) ∘ ts)
| k (imp f₁ f₂) := f₁.relabel.imp f₂.relabel
| k (all f) := f.relabel.all

/-- Places universal quantifiers on all extra variables of a bounded formula. -/
def alls : ∀ {n}, L.bounded_formula α n → L.formula α
| 0 φ := φ
| (n + 1) φ := φ.all.alls

/-- Places existential quantifiers on all extra variables of a bounded formula. -/
def exs : ∀ {n}, L.bounded_formula α n → L.formula α
| 0 φ := φ
| (n + 1) φ := φ.ex.exs

/-- Raises all of the `fin`-indexed variables of a formula greater than or equal to `m` by `n'`. -/
def lift_at : ∀ {n : ℕ} (n' m : ℕ), L.bounded_formula α n → L.bounded_formula α (n + n')
| n n' m falsum := falsum
| n n' m (equal t₁ t₂) := (t₁.lift_at n' m).bd_equal (t₂.lift_at n' m)
| n n' m (rel R ts) := R.bounded_formula (term.lift_at n' m ∘ ts)
| n n' m (imp f₁ f₂) := (f₁.lift_at n' m).imp (f₂.lift_at n' m)
| n n' m (all f) := ((f.lift_at n' m).cast_le (by rw [add_assoc, add_comm 1, ← add_assoc])).all

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
def realize :
  ∀ {l} (f : L.bounded_formula α l) (v : α → M) (xs : fin l → M), Prop
| _ falsum        v xs := false
| _ (equal t₁ t₂) v xs := t₁.realize (sum.elim v xs) = t₂.realize (sum.elim v xs)
| _ (rel R ts)    v xs := rel_map R (λ i, (ts i).realize (sum.elim v xs))
| _ (imp f₁ f₂)   v xs := realize f₁ v xs → realize f₂ v xs
| _ (all f)       v xs := ∀(x : M), realize f v (snoc xs x)

variables {l : ℕ} {φ ψ : L.bounded_formula α l} {θ : L.bounded_formula α l.succ}
variables {v : α → M} {xs : fin l → M}

@[simp] lemma realize_bot :
  (⊥ : L.bounded_formula α l).realize v xs ↔ false :=
iff.rfl

@[simp] lemma realize_not :
  φ.not.realize v xs ↔ ¬ φ.realize v xs :=
iff.rfl

@[simp] lemma realize_bd_equal (t₁ t₂ : L.term (α ⊕ fin l)) :
  (t₁.bd_equal t₂).realize v xs ↔
    (t₁.realize (sum.elim v xs) = t₂.realize (sum.elim v xs)) :=
iff.rfl

@[simp] lemma realize_top :
  (⊤ : L.bounded_formula α l).realize v xs ↔ true :=
by simp [has_top.top]

@[simp] lemma realize_inf : (φ ⊓ ψ).realize v xs ↔ (φ.realize v xs ∧ ψ.realize v xs) :=
by simp [has_inf.inf, realize]

@[simp] lemma realize_imp : (φ.imp ψ).realize v xs ↔ (φ.realize v xs → ψ.realize v xs) :=
by simp only [realize]

@[simp] lemma realize_rel {k : ℕ} {R : L.relations k} {ts : fin k → L.term _} :
  (R.bounded_formula ts).realize v xs ↔ rel_map R (λ i, (ts i).realize (sum.elim v xs)) :=
iff.rfl

@[simp] lemma realize_sup : (φ ⊔ ψ).realize v xs ↔ (φ.realize v xs ∨ ψ.realize v xs) :=
begin
  simp only [realize, has_sup.sup, realize_not, eq_iff_iff],
  tauto,
end

@[simp] lemma realize_all : (all θ).realize v xs ↔ ∀ (a : M), (θ.realize v (fin.snoc xs a)) :=
iff.rfl

@[simp] lemma realize_ex : θ.ex.realize v xs ↔ ∃ (a : M), (θ.realize v (fin.snoc xs a)) :=
begin
  rw [bounded_formula.ex, realize_not, realize_all, not_forall],
  simp_rw [realize_not, not_not],
end

@[simp] lemma realize_iff : (φ.iff ψ).realize v xs ↔ (φ.realize v xs ↔ ψ.realize v xs) :=
by simp only [bounded_formula.iff, realize_inf, realize_imp, and_imp, ← iff_def]

lemma realize_cast_le_of_eq {m n : ℕ} (h : m = n) {h' : m ≤ n} {φ : L.bounded_formula α m}
  {v : α → M} {xs : fin n → M} :
  (φ.cast_le h').realize v xs ↔ φ.realize v (xs ∘ fin.cast h) :=
begin
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 k _ ih3 generalizing n xs h h',
  { simp [cast_le, realize] },
  { simp only [cast_le, realize, realize_bd_equal, term.realize_relabel, sum.elim_comp_map,
      function.comp.right_id, cast_le_of_eq h], },
  { simp only [cast_le, realize, realize_rel, term.realize_relabel, sum.elim_comp_map,
      function.comp.right_id, cast_le_of_eq h] },
  { simp only [cast_le, realize, ih1 h, ih2 h], },
  { simp only [cast_le, realize, ih3 (nat.succ_inj'.2 h)],
    refine forall_congr (λ x, iff_eq_eq.mpr (congr rfl (funext (last_cases _ (λ i, _))))),
    { rw [function.comp_app, snoc_last, cast_last, snoc_last] },
    { rw [function.comp_app, snoc_cast_succ, cast_cast_succ, snoc_cast_succ] } }
end

lemma realize_relabel {m n : ℕ}
  {φ : L.bounded_formula α n} {g : α → (β ⊕ fin m)} {v : β → M} {xs : fin (m + n) → M} :
  (φ.relabel g).realize v xs ↔
    φ.realize (sum.elim v (xs ∘ (fin.cast_add n)) ∘ g) (xs ∘ (fin.nat_add m)) :=
begin
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 n' _ ih3,
  { refl },
  { simp [realize, relabel] },
  { simp [realize, relabel] },
  { simp [realize, relabel, ih1, ih2] },
  { simp only [ih3, realize, relabel],
    refine forall_congr (λ a, (iff_eq_eq.mpr (congr (congr rfl (congr (congr rfl (congr rfl
      (funext (λ i, (dif_pos _).trans rfl)))) rfl)) _))),
    { ext i,
      by_cases h : i.val < n',
      { exact (dif_pos (nat.add_lt_add_left h m)).trans (dif_pos h).symm },
      { exact (dif_neg (λ h', h (nat.lt_of_add_lt_add_left h'))).trans (dif_neg h).symm } } }
end

lemma realize_lift_at {n n' m : ℕ} {φ : L.bounded_formula α n}
  {v : α → M} {xs : fin (n + n') → M} (hmn : m + n' ≤ n + 1) :
  (φ.lift_at n' m).realize v xs ↔ φ.realize v (xs ∘
    (λ i, if ↑i < m then fin.cast_add n' i else fin.add_nat n' i)) :=
begin
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 k _ ih3,
  { simp [lift_at, realize] },
  { simp only [lift_at, realize, realize_bd_equal, realize_lift_at, sum.elim_comp_map,
      function.comp.right_id] },
  { simp only [lift_at, realize, realize_rel, realize_lift_at, sum.elim_comp_map,
      function.comp.right_id] },
  { simp only [lift_at, realize, ih1 hmn, ih2 hmn], },
  { have h : k + 1 + n' = k + n'+ 1,
    { rw [add_assoc, add_comm 1 n', ← add_assoc], },
    simp only [lift_at, realize, realize_cast_le_of_eq h, ih3 (hmn.trans k.succ.le_succ)],
    refine forall_congr (λ x, iff_eq_eq.mpr (congr rfl (funext (fin.last_cases _ (λ i, _))))),
    { simp only [function.comp_app, coe_last, snoc_last],
      by_cases (k < m),
      { rw if_pos h,
        refine (congr rfl (ext _)).trans (snoc_last _ _),
        simp only [coe_cast, coe_cast_add, coe_last, self_eq_add_right],
        refine le_antisymm (le_of_add_le_add_left ((hmn.trans (nat.succ_le_of_lt h)).trans _))
          n'.zero_le,
        rw add_zero },
      { rw if_neg h,
        refine (congr rfl (ext _)).trans (snoc_last _ _),
        simp } },
    { simp only [function.comp_app, fin.snoc_cast_succ],
      refine (congr rfl (ext _)).trans (snoc_cast_succ _ _ _),
      simp only [cast_refl, coe_cast_succ, order_iso.coe_refl, id.def],
      split_ifs;
      simp } }
end

lemma realize_lift_at_one {n m : ℕ} {φ : L.bounded_formula α n}
  {v : α → M} {xs : fin (n + 1) → M} (hmn : m ≤ n) :
  (φ.lift_at 1 m).realize v xs ↔ φ.realize v (xs ∘
    (λ i, if ↑i < m then cast_succ i else i.succ)) :=
by simp_rw [realize_lift_at (add_le_add_right hmn 1), cast_succ, add_nat_one]

@[simp] lemma realize_lift_at_one_self {n : ℕ} {φ : L.bounded_formula α n}
  {v : α → M} {xs : fin (n + 1) → M} :
  (φ.lift_at 1 n).realize v xs ↔ φ.realize v (xs ∘ cast_succ) :=
begin
  rw [realize_lift_at_one (refl n), iff_eq_eq],
  refine congr rfl (congr rfl (funext (λ i, _))),
  rw [if_pos i.is_lt],
end

lemma realize_all_lift_at_one_self [nonempty M] {n : ℕ} {φ : L.bounded_formula α n}
  {v : α → M} {xs : fin n → M} :
  (φ.lift_at 1 n).all.realize v xs ↔ φ.realize v xs :=
begin
  inhabit M,
  simp only [realize_all, realize_lift_at_one_self],
  refine ⟨λ h, _, λ h a, _⟩,
  { refine (congr rfl (funext (λ i, _))).mp (h default),
    simp, },
  { refine (congr rfl (funext (λ i, _))).mp h,
    simp }
end

/-- An atomic formula is either equality or a relation symbol applied to terms.
  Note that `⊥` and `⊤` are not considered atomic in this convention. -/
inductive is_atomic : L.bounded_formula α n → Prop
| equal (t₁ t₂ : L.term (α ⊕ fin n)) : is_atomic (bd_equal t₁ t₂)
| rel {l : ℕ} (R : L.relations l) (ts : fin l → L.term (α ⊕ fin n)) :
    is_atomic (R.bounded_formula ts)

lemma not_all_is_atomic (φ : L.bounded_formula α (n + 1)) :
  ¬ φ.all.is_atomic :=
λ con, by cases con

lemma not_ex_is_atomic (φ : L.bounded_formula α (n + 1)) :
  ¬ φ.ex.is_atomic :=
λ con, by cases con

lemma is_atomic.relabel {m : ℕ} {φ : L.bounded_formula α m} (h : φ.is_atomic)
  (f : α → β ⊕ (fin n)) :
  (φ.relabel f).is_atomic :=
is_atomic.rec_on h (λ _ _, is_atomic.equal _ _) (λ _ _ _, is_atomic.rel _ _)

lemma is_atomic.lift_at {k m : ℕ} (h : is_atomic φ) : (φ.lift_at k m).is_atomic :=
is_atomic.rec_on h (λ _ _, is_atomic.equal _ _) (λ _ _ _, is_atomic.rel _ _)

lemma is_atomic.cast_le {h : l ≤ n} (hφ : is_atomic φ) :
  (φ.cast_le h).is_atomic :=
is_atomic.rec_on hφ (λ _ _, is_atomic.equal _ _) (λ _ _ _, is_atomic.rel _ _)

/-- A quantifier-free formula is a formula defined without quantifiers. These are all equivalent
to boolean combinations of atomic formulas. -/
inductive is_qf : L.bounded_formula α n → Prop
| falsum : is_qf falsum
| of_is_atomic {φ} (h : is_atomic φ) : is_qf φ
| imp {φ₁ φ₂} (h₁ : is_qf φ₁) (h₂ : is_qf φ₂) : is_qf (φ₁.imp φ₂)

lemma is_atomic.is_qf {φ : L.bounded_formula α n} : is_atomic φ → is_qf φ :=
is_qf.of_is_atomic

lemma is_qf_bot : is_qf (⊥ : L.bounded_formula α n) :=
is_qf.falsum

lemma is_qf.not {φ : L.bounded_formula α n} (h : is_qf φ) :
  is_qf φ.not :=
h.imp is_qf_bot

lemma is_qf.relabel {m : ℕ} {φ : L.bounded_formula α m} (h : φ.is_qf)
  (f : α → β ⊕ (fin n)) :
  (φ.relabel f).is_qf :=
is_qf.rec_on h is_qf_bot (λ _ h, (h.relabel f).is_qf) (λ _ _ _ _ h1 h2, h1.imp h2)

lemma is_qf.lift_at {k m : ℕ} (h : is_qf φ) : (φ.lift_at k m).is_qf :=
is_qf.rec_on h is_qf_bot (λ _ ih, ih.lift_at.is_qf) (λ _ _ _ _ ih1 ih2, ih1.imp ih2)

lemma is_qf.cast_le {h : l ≤ n} (hφ : is_qf φ) :
  (φ.cast_le h).is_qf :=
is_qf.rec_on hφ is_qf_bot (λ _ ih, ih.cast_le.is_qf) (λ _ _ _ _ ih1 ih2, ih1.imp ih2)

lemma not_all_is_qf (φ : L.bounded_formula α (n + 1)) :
  ¬ φ.all.is_qf :=
λ con, begin
  cases con with _ con,
  exact (φ.not_all_is_atomic con),
end

lemma not_ex_is_qf (φ : L.bounded_formula α (n + 1)) :
  ¬ φ.ex.is_qf :=
λ con, begin
  cases con with _ con _ _ con,
  { exact (φ.not_ex_is_atomic con) },
  { exact not_all_is_qf _ con }
end

/-- Indicates that a bounded formula is in prenex normal form - that is, it consists of quantifiers
  applied to a quantifier-free formula. -/
inductive is_prenex : ∀ {n}, L.bounded_formula α n → Prop
| of_is_qf {n} {φ : L.bounded_formula α n} (h : is_qf φ) : is_prenex φ
| all {n} {φ : L.bounded_formula α (n + 1)} (h : is_prenex φ) : is_prenex φ.all
| ex {n} {φ : L.bounded_formula α (n + 1)} (h : is_prenex φ) : is_prenex φ.ex

lemma is_qf.is_prenex {φ : L.bounded_formula α n} : is_qf φ → is_prenex φ :=
is_prenex.of_is_qf

lemma is_atomic.is_prenex {φ : L.bounded_formula α n} (h : is_atomic φ) : is_prenex φ :=
h.is_qf.is_prenex

lemma is_prenex.induction_on_all_not {P : ∀ {n}, L.bounded_formula α n → Prop}
  {φ : L.bounded_formula α n}
  (h : is_prenex φ)
  (hq : ∀ {m} {ψ : L.bounded_formula α m}, ψ.is_qf → P ψ)
  (ha : ∀ {m} {ψ : L.bounded_formula α (m + 1)}, P ψ → P ψ.all)
  (hn : ∀ {m} {ψ : L.bounded_formula α m}, P ψ → P ψ.not) :
  P φ :=
is_prenex.rec_on h (λ _ _, hq) (λ _ _ _, ha) (λ _ _ _ ih, hn (ha (hn ih)))

lemma is_prenex.relabel {m : ℕ} {φ : L.bounded_formula α m} (h : φ.is_prenex)
  (f : α → β ⊕ (fin n)) :
  (φ.relabel f).is_prenex :=
is_prenex.rec_on h (λ _ _ h, (h.relabel f).is_prenex) (λ _ _ _ h, h.all) (λ _ _ _ h, h.ex)

lemma is_prenex.cast_le (hφ : is_prenex φ) :
  ∀ {n} {h : l ≤ n}, (φ.cast_le h).is_prenex :=
is_prenex.rec_on hφ
  (λ _ _ ih _ _, ih.cast_le.is_prenex)
  (λ _ _ _ ih _ _, ih.all)
  (λ _ _ _ ih _ _, ih.ex)

lemma is_prenex.lift_at {k m : ℕ} (h : is_prenex φ) : (φ.lift_at k m).is_prenex :=
is_prenex.rec_on h
  (λ _ _ ih, ih.lift_at.is_prenex)
  (λ _ _ _ ih, ih.cast_le.all)
  (λ _ _ _ ih, ih.cast_le.ex)

/-- An auxiliary operation to `first_order.language.bounded_formula.to_prenex`.
  If `φ` is quantifier-free and `ψ` is in prenex normal form, then `φ.to_prenex_imp_right ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def to_prenex_imp_right :
  ∀ {n}, L.bounded_formula α n → L.bounded_formula α n → L.bounded_formula α n
| n φ (bounded_formula.ex ψ) := ((φ.lift_at 1 n).to_prenex_imp_right ψ).ex
| n φ (all ψ) := ((φ.lift_at 1 n).to_prenex_imp_right ψ).all
| n φ ψ := φ.imp ψ

lemma is_qf.to_prenex_imp_right {φ : L.bounded_formula α n} :
  Π {ψ : L.bounded_formula α n}, is_qf ψ → (φ.to_prenex_imp_right ψ = φ.imp ψ)
| _ is_qf.falsum := rfl
| _ (is_qf.of_is_atomic (is_atomic.equal _ _)) := rfl
| _ (is_qf.of_is_atomic (is_atomic.rel _ _)) := rfl
| _ (is_qf.imp is_qf.falsum _) := rfl
| _ (is_qf.imp (is_qf.of_is_atomic (is_atomic.equal _ _)) _) := rfl
| _ (is_qf.imp (is_qf.of_is_atomic (is_atomic.rel _ _)) _) := rfl
| _ (is_qf.imp (is_qf.imp _ _) _) := rfl

lemma is_prenex_to_prenex_imp_right {φ ψ : L.bounded_formula α n}
  (hφ : is_qf φ) (hψ : is_prenex ψ) :
  is_prenex (φ.to_prenex_imp_right ψ) :=
begin
  induction hψ with _ _ hψ _ _ _ ih1 _ _ _ ih2,
  { rw hψ.to_prenex_imp_right,
    exact (hφ.imp hψ).is_prenex },
  { exact (ih1 hφ.lift_at).all },
  { exact (ih2 hφ.lift_at).ex }
end

/-- An auxiliary operation to `first_order.language.bounded_formula.to_prenex`.
  If `φ` and `ψ` are in prenex normal form, then `φ.to_prenex_imp ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def to_prenex_imp :
  ∀ {n}, L.bounded_formula α n → L.bounded_formula α n → L.bounded_formula α n
| n (bounded_formula.ex φ) ψ := (φ.to_prenex_imp (ψ.lift_at 1 n)).all
| n (all φ) ψ := (φ.to_prenex_imp (ψ.lift_at 1 n)).ex
| _ φ ψ := φ.to_prenex_imp_right ψ

lemma is_qf.to_prenex_imp : Π {φ ψ : L.bounded_formula α n}, φ.is_qf →
  φ.to_prenex_imp ψ = φ.to_prenex_imp_right ψ
| _ _ is_qf.falsum := rfl
| _ _ (is_qf.of_is_atomic (is_atomic.equal _ _)) := rfl
| _ _ (is_qf.of_is_atomic (is_atomic.rel _ _)) := rfl
| _ _ (is_qf.imp is_qf.falsum _) := rfl
| _ _ (is_qf.imp (is_qf.of_is_atomic (is_atomic.equal _ _)) _) := rfl
| _ _ (is_qf.imp (is_qf.of_is_atomic (is_atomic.rel _ _)) _) := rfl
| _ _ (is_qf.imp (is_qf.imp _ _) _) := rfl

lemma is_prenex_to_prenex_imp {φ ψ : L.bounded_formula α n}
  (hφ : is_prenex φ) (hψ : is_prenex ψ) :
  is_prenex (φ.to_prenex_imp ψ) :=
begin
  induction hφ with _ _ hφ _ _ _ ih1 _ _ _ ih2,
  { rw hφ.to_prenex_imp,
    exact is_prenex_to_prenex_imp_right hφ hψ },
  { exact (ih1 hψ.lift_at).ex },
  { exact (ih2 hψ.lift_at).all }
end

/-- For any bounded formula `φ`, `φ.to_prenex` is a semantically-equivalent formula in prenex normal
  form. -/
def to_prenex : ∀ {n}, L.bounded_formula α n → L.bounded_formula α n
| _ falsum        := ⊥
| _ (equal t₁ t₂) := t₁.bd_equal t₂
| _ (rel R ts)    := rel R ts
| _ (imp f₁ f₂)   := f₁.to_prenex.to_prenex_imp f₂.to_prenex
| _ (all f)       := f.to_prenex.all

lemma to_prenex_is_prenex (φ : L.bounded_formula α n) :
  φ.to_prenex.is_prenex :=
bounded_formula.rec_on φ
  (λ _, is_qf_bot.is_prenex)
  (λ _ _ _, (is_atomic.equal _ _).is_prenex)
  (λ _ _ _ _, (is_atomic.rel _ _).is_prenex)
  (λ _ _ _ h1 h2, is_prenex_to_prenex_imp h1 h2)
  (λ _ _, is_prenex.all)

variables [nonempty M]

lemma realize_to_prenex_imp_right {φ ψ : L.bounded_formula α n}
  (hφ : is_qf φ) (hψ : is_prenex ψ) {v : α → M} {xs : fin n → M} :
  (φ.to_prenex_imp_right ψ).realize v xs ↔ (φ.imp ψ).realize v xs :=
begin
  revert φ,
  induction hψ with _ _ hψ _ _ hψ ih _ _ hψ ih; intros φ hφ,
  { rw hψ.to_prenex_imp_right },
  { refine trans (forall_congr (λ _, ih hφ.lift_at)) _,
    simp only [realize_imp, realize_lift_at_one_self, snoc_comp_cast_succ, realize_all],
    exact ⟨λ h1 a h2, h1 h2 a, λ h1 h2 a, h1 a h2⟩, },
  { rw [to_prenex_imp_right, realize_ex],
    refine trans (exists_congr (λ _, ih hφ.lift_at)) _,
    simp only [realize_imp, realize_lift_at_one_self, snoc_comp_cast_succ, realize_ex],
    refine ⟨_, λ h', _⟩,
    { rintro ⟨a, ha⟩ h,
      exact ⟨a, ha h⟩ },
    { by_cases φ.realize v xs,
      { obtain ⟨a, ha⟩ := h' h,
        exact ⟨a, λ _, ha⟩ },
      { inhabit M,
        exact ⟨default, λ h'', (h h'').elim⟩ } } }
end

lemma realize_to_prenex_imp {φ ψ : L.bounded_formula α n}
  (hφ : is_prenex φ) (hψ : is_prenex ψ) {v : α → M} {xs : fin n → M} :
  (φ.to_prenex_imp ψ).realize v xs ↔ (φ.imp ψ).realize v xs :=
begin
  revert ψ,
  induction hφ with _ _ hφ _ _ hφ ih _ _ hφ ih; intros ψ hψ,
  { rw [hφ.to_prenex_imp],
    exact realize_to_prenex_imp_right hφ hψ, },
  { rw [to_prenex_imp, realize_ex],
    refine trans (exists_congr (λ _, ih hψ.lift_at)) _,
    simp only [realize_imp, realize_lift_at_one_self, snoc_comp_cast_succ, realize_all],
    refine ⟨_, λ h', _⟩,
    { rintro ⟨a, ha⟩ h,
      exact ha (h a) },
    { by_cases ψ.realize v xs,
      { inhabit M,
        exact ⟨default, λ h'', h⟩ },
      { obtain ⟨a, ha⟩ := not_forall.1 (h ∘ h'),
        exact ⟨a, λ h, (ha h).elim⟩ } } },
  { refine trans (forall_congr (λ _, ih hψ.lift_at)) _,
    simp, },
end

@[simp] lemma realize_to_prenex (φ : L.bounded_formula α n) {v : α → M} :
  ∀ {xs : fin n → M}, φ.to_prenex.realize v xs ↔ φ.realize v xs :=
begin
  refine bounded_formula.rec_on φ
    (λ _ _, iff.rfl)
    (λ _ _ _ _, iff.rfl)
    (λ _ _ _ _ _, iff.rfl)
    (λ _ f1 f2 h1 h2 _, _)
    (λ _ f h xs, _),
  { rw [to_prenex, realize_to_prenex_imp f1.to_prenex_is_prenex f2.to_prenex_is_prenex,
      realize_imp, realize_imp, h1, h2],
    apply_instance },
  { rw [realize_all, to_prenex, realize_all],
    exact forall_congr (λ a, h) },
end

end bounded_formula

namespace Lhom
open bounded_formula

/-- Maps a bounded formula's symbols along a language map. -/
@[simp] def on_bounded_formula (g : L →ᴸ L') :
  ∀ {k : ℕ}, L.bounded_formula α k → L'.bounded_formula α k
| k falsum := falsum
| k (equal t₁ t₂) := (g.on_term t₁).bd_equal (g.on_term t₂)
| k (rel R ts) := (g.on_relation R).bounded_formula (g.on_term ∘ ts)
| k (imp f₁ f₂) := (on_bounded_formula f₁).imp (on_bounded_formula f₂)
| k (all f) := (on_bounded_formula f).all

@[simp] lemma id_on_bounded_formula :
  ((Lhom.id L).on_bounded_formula : L.bounded_formula α n → L.bounded_formula α n) = id :=
begin
  ext f,
  induction f with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { rw [on_bounded_formula, Lhom.id_on_term, id.def, id.def, id.def, bd_equal] },
  { rw [on_bounded_formula, Lhom.id_on_term],
    refl, },
  { rw [on_bounded_formula, ih1, ih2, id.def, id.def, id.def] },
  { rw [on_bounded_formula, ih3, id.def, id.def] }
end

@[simp] lemma comp_on_bounded_formula {L'' : language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
  ((φ.comp ψ).on_bounded_formula : L.bounded_formula α n → L''.bounded_formula α n) =
    φ.on_bounded_formula ∘ ψ.on_bounded_formula :=
begin
  ext f,
  induction f with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp only [on_bounded_formula, comp_on_term, function.comp_app],
    refl, },
  { simp only [on_bounded_formula, comp_on_relation, comp_on_term, function.comp_app],
    refl },
  { simp only [on_bounded_formula, function.comp_app, ih1, ih2, eq_self_iff_true, and_self], },
  { simp only [ih3, on_bounded_formula, function.comp_app] }
end

/-- Maps a formula's symbols along a language map. -/
def on_formula (g : L →ᴸ L') : L.formula α → L'.formula α :=
g.on_bounded_formula

/-- Maps a sentence's symbols along a language map. -/
def on_sentence (g : L →ᴸ L') : L.sentence → L'.sentence :=
g.on_formula

/-- Maps a theory's symbols along a language map. -/
def on_Theory (g : L →ᴸ L') (T : L.Theory) : L'.Theory :=
g.on_sentence '' T

@[simp] lemma mem_on_Theory {g : L →ᴸ L'} {T : L.Theory} {φ : L'.sentence} :
  φ ∈ g.on_Theory T ↔ ∃ φ₀, φ₀ ∈ T ∧ g.on_sentence φ₀ = φ :=
set.mem_image _ _ _

@[simp] lemma realize_on_bounded_formula [L'.Structure M] (φ : L →ᴸ L') [φ.is_expansion_on M]
  {n : ℕ} (ψ : L.bounded_formula α n) {v : α → M} {xs : fin n → M} :
  (φ.on_bounded_formula ψ).realize v xs ↔ ψ.realize v xs :=
begin
  induction ψ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp only [on_bounded_formula, realize_bd_equal, realize_on_term],
    refl, },
  { simp only [on_bounded_formula, realize_rel, realize_on_term, is_expansion_on.map_on_relation],
    refl, },
  { simp only [on_bounded_formula, ih1, ih2, realize_imp], },
  { simp only [on_bounded_formula, ih3, realize_all], },
end

end Lhom

namespace Lequiv

/-- Maps a bounded formula's symbols along a language equivalence. -/
@[simps] def on_bounded_formula (φ : L ≃ᴸ L') :
  L.bounded_formula α n ≃ L'.bounded_formula α n :=
{ to_fun := φ.to_Lhom.on_bounded_formula,
  inv_fun := φ.inv_Lhom.on_bounded_formula,
  left_inv := by rw [function.left_inverse_iff_comp, ← Lhom.comp_on_bounded_formula, φ.left_inv,
    Lhom.id_on_bounded_formula],
  right_inv := by rw [function.right_inverse_iff_comp, ← Lhom.comp_on_bounded_formula, φ.right_inv,
    Lhom.id_on_bounded_formula] }

lemma on_bounded_formula_symm (φ : L ≃ᴸ L') :
  (φ.on_bounded_formula.symm : L'.bounded_formula α n ≃ L.bounded_formula α n) =
    φ.symm.on_bounded_formula :=
rfl

/-- Maps a formula's symbols along a language equivalence. -/
def on_formula (φ : L ≃ᴸ L') :
  L.formula α ≃ L'.formula α :=
φ.on_bounded_formula

@[simp] lemma on_formula_apply (φ : L ≃ᴸ L') :
  (φ.on_formula : L.formula α → L'.formula α) = φ.to_Lhom.on_formula :=
rfl

@[simp] lemma on_formula_symm (φ : L ≃ᴸ L') :
  (φ.on_formula.symm : L'.formula α ≃ L.formula α) = φ.symm.on_formula :=
rfl

/-- Maps a sentence's symbols along a language equivalence. -/
@[simps] def on_sentence (φ : L ≃ᴸ L') :
  L.sentence ≃ L'.sentence :=
φ.on_formula

end Lequiv

attribute [protected] bounded_formula.falsum bounded_formula.equal bounded_formula.rel
attribute [protected] bounded_formula.imp bounded_formula.all

localized "infix ` =' `:88 := first_order.language.term.bd_equal" in first_order
  -- input \~- or \simeq
localized "infixr ` ⟹ `:62 := first_order.language.bounded_formula.imp" in first_order
  -- input \==>
localized "prefix `∀'`:110 := first_order.language.bounded_formula.all" in first_order
localized "prefix `∼`:max := first_order.language.bounded_formula.not" in first_order
  -- input \~, the ASCII character ~ has too low precedence
localized "infix ` ⇔ `:61 := first_order.language.bounded_formula.iff" in first_order -- input \<=>
localized "prefix `∃'`:110 := first_order.language.bounded_formula.ex" in first_order -- input \ex

namespace formula

/-- Relabels a formula's variables along a particular function. -/
def relabel (g : α → β) : L.formula α → L.formula β :=
@bounded_formula.relabel _ _ _ 0 (sum.inl ∘ g) 0

/-- The graph of a function as a first-order formula. -/
def graph (f : L.functions n) : L.formula (fin (n + 1)) :=
equal (var 0) (func f (λ i, var i.succ))

/-- The negation of a formula. -/
protected def not (φ : L.formula α) : L.formula α := φ.not

/-- The implication between formulas, as a formula. -/
protected def imp : L.formula α → L.formula α → L.formula α := bounded_formula.imp

/-- The biimplication between formulas, as a formula. -/
protected def iff (φ ψ : L.formula α) : L.formula α := φ.iff ψ

/-- A formula can be evaluated as true or false by giving values to each free variable. -/
def realize (φ : L.formula α) (v : α → M) : Prop :=
φ.realize v default

variables {M} {φ ψ : L.formula α} {v : α → M}

@[simp] lemma realize_not :
  (φ.not).realize v ↔ ¬ φ.realize v :=
iff.rfl

@[simp] lemma realize_bot :
  (⊥ : L.formula α).realize v ↔ false :=
iff.rfl

@[simp] lemma realize_top :
  (⊤ : L.formula α).realize v ↔ true :=
bounded_formula.realize_top

@[simp] lemma realize_inf : (φ ⊓ ψ).realize v ↔ (φ.realize v ∧ ψ.realize v) :=
bounded_formula.realize_inf

@[simp] lemma realize_imp : (φ.imp ψ).realize v ↔ (φ.realize v → ψ.realize v) :=
bounded_formula.realize_imp

@[simp] lemma realize_rel {k : ℕ} {R : L.relations k} {ts : fin k → L.term α} :
  (R.formula ts).realize v ↔ rel_map R (λ i, (ts i).realize v) :=
bounded_formula.realize_rel.trans (by simp)

@[simp] lemma realize_sup : (φ ⊔ ψ).realize v ↔ (φ.realize v ∨ ψ.realize v) :=
bounded_formula.realize_sup

@[simp] lemma realize_iff : (φ.iff ψ).realize v ↔ (φ.realize v ↔ ψ.realize v) :=
bounded_formula.realize_iff

@[simp] lemma realize_relabel {φ : L.formula α} {g : α → β} {v : β → M} :
  (φ.relabel g).realize v ↔ φ.realize (v ∘ g) :=
begin
  rw [realize, realize, relabel, bounded_formula.realize_relabel,
    iff_eq_eq],
  refine congr (congr rfl _) (funext fin_zero_elim),
  ext,
  simp,
end

@[simp]
lemma realize_equal {t₁ t₂ : L.term α} {x : α → M} :
  (t₁.equal t₂).realize x ↔ t₁.realize x = t₂.realize x :=
by simp [term.equal, realize]

@[simp]
lemma realize_graph {f : L.functions n} {x : fin n → M} {y : M} :
  (formula.graph f).realize (fin.cons y x : _ → M) ↔ fun_map f x = y :=
begin
  simp only [formula.graph, term.realize, realize_equal, fin.cons_zero, fin.cons_succ],
  rw eq_comm,
end

lemma is_atomic_graph (f : L.functions n) : (graph f).is_atomic :=
bounded_formula.is_atomic.equal _ _

end formula

@[simp] lemma Lhom.realize_on_formula [L'.Structure M] (φ : L →ᴸ L') [φ.is_expansion_on M]
  (ψ : L.formula α) {v : α → M} :
  (φ.on_formula ψ).realize v ↔ ψ.realize v :=
φ.realize_on_bounded_formula ψ

@[simp] lemma Lhom.set_of_realize_on_formula [L'.Structure M] (φ : L →ᴸ L') [φ.is_expansion_on M]
  (ψ : L.formula α) :
  (set_of (φ.on_formula ψ).realize : set (α → M)) = set_of ψ.realize :=
by { ext, simp }

variable (M)

/-- A sentence can be evaluated as true or false in a structure. -/
def sentence.realize (φ : L.sentence) : Prop :=
φ.realize (default : _ → M)

infix ` ⊨ `:51 := sentence.realize -- input using \|= or \vDash, but not using \models

@[simp] lemma Lhom.realize_on_sentence [L'.Structure M] (φ : L →ᴸ L') [φ.is_expansion_on M]
  (ψ : L.sentence) :
  M ⊨ φ.on_sentence ψ ↔ M ⊨ ψ :=
φ.realize_on_formula ψ

/-- A model of a theory is a structure in which every sentence is realized as true. -/
class Theory.model (T : L.Theory) : Prop :=
(realize_of_mem : ∀ φ ∈ T, M ⊨ φ)

infix ` ⊨ `:51 := Theory.model -- input using \|= or \vDash, but not using \models

variables {M} (T : L.Theory)

lemma Theory.realize_sentence_of_mem [M ⊨ T] {φ : L.sentence} (h : φ ∈ T) :
  M ⊨ φ :=
Theory.model.realize_of_mem φ h

@[simp] lemma Lhom.on_Theory_model [L'.Structure M] (φ : L →ᴸ L') [φ.is_expansion_on M]
  (T : L.Theory) :
  M ⊨ φ.on_Theory T ↔ M ⊨ T :=
begin
  split; introI,
  { exact ⟨λ ψ hψ, (φ.realize_on_sentence M _).1
      ((φ.on_Theory T).realize_sentence_of_mem (set.mem_image_of_mem φ.on_sentence hψ))⟩ },
  { refine ⟨λ ψ hψ, _⟩,
    obtain ⟨ψ₀, hψ₀, rfl⟩ := Lhom.mem_on_Theory.1 hψ,
    exact (φ.realize_on_sentence M _).2 (T.realize_sentence_of_mem hψ₀) },
end

variables {M} {T}

lemma Theory.model.mono {T' : L.Theory} (h : M ⊨ T') (hs : T ⊆ T') :
  M ⊨ T :=
⟨λ φ hφ, T'.realize_sentence_of_mem (hs hφ)⟩

namespace bounded_formula

@[simp] lemma realize_alls {φ : L.bounded_formula α n} {v : α → M} :
  φ.alls.realize v ↔
    ∀ (xs : fin n → M), (φ.realize v xs) :=
begin
  induction n with n ih,
  { exact unique.forall_iff.symm },
  { simp only [alls, ih, realize],
    exact ⟨λ h xs, (fin.snoc_init_self xs) ▸ h _ _, λ h xs x, h (fin.snoc xs x)⟩ }
end

@[simp] lemma realize_exs {φ : L.bounded_formula α n} {v : α → M} :
  φ.exs.realize v ↔ ∃ (xs : fin n → M), (φ.realize v xs) :=
begin
  induction n with n ih,
  { exact unique.exists_iff.symm },
  { simp only [bounded_formula.exs, ih, realize_ex],
    split,
    { rintros ⟨xs, x, h⟩,
      exact ⟨_, h⟩ },
    { rintros ⟨xs, h⟩,
      rw ← fin.snoc_init_self xs at h,
      exact ⟨_, _, h⟩ } }
end

end bounded_formula

@[simp] lemma equiv.realize_bounded_formula (g : M ≃[L] N) (φ : L.bounded_formula α n)
  {v : α → M} {xs : fin n → M} :
  φ.realize (g ∘ v) (g ∘ xs) ↔ φ.realize v xs :=
begin
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp only [bounded_formula.realize, ← sum.comp_elim, equiv.realize_term, g.injective.eq_iff] },
  { simp only [bounded_formula.realize, ← sum.comp_elim, equiv.realize_term, g.map_rel], },
  { rw [bounded_formula.realize, ih1, ih2, bounded_formula.realize] },
  { rw [bounded_formula.realize, bounded_formula.realize],
    split,
    { intros h a,
      have h' := h (g a),
      rw [← fin.comp_snoc, ih3] at h',
      exact h' },
    { intros h a,
      have h' := h (g.symm a),
      rw [← ih3, fin.comp_snoc, g.apply_symm_apply] at h',
      exact h' }}
end

@[simp] lemma equiv.realize_formula (g : M ≃[L] N) (φ : L.formula α) {v : α → M}  :
  φ.realize (g ∘ v) ↔ φ.realize v :=
begin
  rw [formula.realize, formula.realize, ← g.realize_bounded_formula φ,
    iff_eq_eq],
  exact congr rfl (funext fin_zero_elim),
end

namespace Theory
variable (T)

/-- A theory is satisfiable if a structure models it. -/
def is_satisfiable : Prop :=
∃ (M : Type (max u v)) [nonempty M] [str : L.Structure M], @Theory.model L M str T

/-- A theory is finitely satisfiable if all of its finite subtheories are satisfiable. -/
def is_finitely_satisfiable : Prop :=
∀ (T0 : finset L.sentence), (T0 : L.Theory) ⊆ T → (T0 : L.Theory).is_satisfiable

variables {T} {T' : L.Theory}

/-- Given that a theory is satisfiable, selects a model using choice. -/
def is_satisfiable.some_model (h : T.is_satisfiable) : Type* := classical.some h

instance is_satisfiable.nonempty_some_model (h : T.is_satisfiable) :
  nonempty (h.some_model) :=
classical.some (classical.some_spec h)

noncomputable instance is_satisfiable.inhabited_some_model (h : T.is_satisfiable) :
  inhabited (h.some_model) := classical.inhabited_of_nonempty'

noncomputable instance is_satisfiable.some_model_structure (h : T.is_satisfiable) :
  L.Structure (h.some_model) :=
classical.some (classical.some_spec (classical.some_spec h))

instance is_satisfiable.some_model_models (h : T.is_satisfiable) :
  h.some_model ⊨ T :=
classical.some_spec (classical.some_spec (classical.some_spec h))

lemma model.is_satisfiable (M : Type (max u v)) [n : nonempty M]
  [S : L.Structure M] (h : T.model M) : T.is_satisfiable :=
⟨M, n, S, h⟩

lemma is_satisfiable.mono (h : T'.is_satisfiable) (hs : T ⊆ T') :
  T.is_satisfiable :=
⟨h.some_model, h.nonempty_some_model, h.some_model_structure,
  h.some_model_models.mono hs⟩

lemma is_satisfiable.is_finitely_satisfiable (h : T.is_satisfiable) :
  T.is_finitely_satisfiable :=
λ _, h.mono

variable (T)

/-- A theory models a (bounded) formula when any of its nonempty models realizes that formula on all
  inputs.-/
def models_bounded_formula (φ : L.bounded_formula α n) : Prop :=
  ∀ (M : Type (max u v)) [nonempty M] [str : L.Structure M] (v : α → M) (xs : fin n → M),
    @Theory.model L M str T → @bounded_formula.realize L M str α n φ v xs

infix ` ⊨ `:51 := models_bounded_formula -- input using \|= or \vDash, but not using \models

variable {T}

lemma models_formula_iff {φ : L.formula α} :
  T ⊨ φ ↔ ∀ (M : Type (max u v)) [nonempty M] [str : L.Structure M] (v : α → M),
    @Theory.model L M str T → @formula.realize L M str α φ v :=
forall_congr (λ M, forall_congr (λ ne, forall_congr (λ str, forall_congr (λ v, unique.forall_iff))))

lemma models_sentence_iff {φ : L.sentence} :
  T ⊨ φ ↔ ∀ (M : Type (max u v)) [nonempty M] [str : L.Structure M],
    @Theory.model L M str T → @sentence.realize L M str φ :=
begin
  rw [models_formula_iff],
  exact forall_congr (λ M, forall_congr (λ ne, forall_congr (λ str, unique.forall_iff)))
end

/-- Two (bounded) formulas are semantically equivalent over a theory `T` when they have the same
interpretation in every model of `T`. (This is also known as logical equivalence, which also has a
proof-theoretic definition.) -/
def semantically_equivalent (T : L.Theory) (φ ψ : L.bounded_formula α n) : Prop :=
T ⊨ φ.iff ψ

@[refl] lemma semantically_equivalent.refl (φ : L.bounded_formula α n) :
  T.semantically_equivalent φ φ :=
λ M ne str v xs hM, by rw bounded_formula.realize_iff

instance : is_refl (L.bounded_formula α n) T.semantically_equivalent :=
⟨semantically_equivalent.refl⟩

@[symm] lemma semantically_equivalent.symm {φ ψ : L.bounded_formula α n}
  (h : T.semantically_equivalent φ ψ) :
  T.semantically_equivalent ψ φ :=
λ M ne str v xs hM, begin
  haveI := ne,
  rw [bounded_formula.realize_iff, iff.comm, ← bounded_formula.realize_iff],
  exact h M v xs hM,
end

@[trans] lemma semantically_equivalent.trans {φ ψ θ : L.bounded_formula α n}
  (h1 : T.semantically_equivalent φ ψ) (h2 : T.semantically_equivalent ψ θ) :
  T.semantically_equivalent φ θ :=
λ M ne str v xs hM, begin
  haveI := ne,
  have h1' := h1 M v xs hM,
  have h2' := h2 M v xs hM,
  rw [bounded_formula.realize_iff] at *,
  exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩,
end

lemma semantically_equivalent.realize_bd_iff {φ ψ : L.bounded_formula α n}
  {M : Type (max u v)} [ne : nonempty M] [str : L.Structure M] (hM : T.model M)
  (h : T.semantically_equivalent φ ψ) {v : α → M} {xs : (fin n → M)} :
  φ.realize v xs ↔ ψ.realize v xs :=
bounded_formula.realize_iff.1 (h M v xs hM)

lemma semantically_equivalent.some_model_realize_bd_iff {φ ψ : L.bounded_formula α n}
  (hsat : T.is_satisfiable) (h : T.semantically_equivalent φ ψ)
  {v : α → (hsat.some_model)} {xs : (fin n → (hsat.some_model))} :
  φ.realize v xs ↔ ψ.realize v xs :=
h.realize_bd_iff hsat.some_model_models

lemma semantically_equivalent.realize_iff {φ ψ : L.formula α}
  {M : Type (max u v)} [ne : nonempty M] [str : L.Structure M] (hM : T.model M)
  (h : T.semantically_equivalent φ ψ) {v : α → M} :
  φ.realize v ↔ ψ.realize v :=
h.realize_bd_iff hM

lemma semantically_equivalent.some_model_realize_iff {φ ψ : L.formula α}
  (hsat : T.is_satisfiable) (h : T.semantically_equivalent φ ψ) {v : α → (hsat.some_model)} :
  φ.realize v ↔ ψ.realize v :=
h.realize_iff hsat.some_model_models

/-- Semantic equivalence forms an equivalence relation on formulas. -/
def semantically_equivalent_setoid (T : L.Theory) : setoid (L.bounded_formula α n) :=
{ r := semantically_equivalent T,
  iseqv := ⟨λ _, refl _, λ a b h, h.symm, λ _ _ _ h1 h2, h1.trans h2⟩ }

protected lemma semantically_equivalent.all {φ ψ : L.bounded_formula α (n + 1)}
  (h : T.semantically_equivalent φ ψ) : T.semantically_equivalent φ.all ψ.all :=
begin
  rw [semantically_equivalent, models_bounded_formula],
  introsI M ne str v xs hM,
  simp [h.realize_bd_iff hM],
end

protected lemma semantically_equivalent.ex {φ ψ : L.bounded_formula α (n + 1)}
  (h : T.semantically_equivalent φ ψ) : T.semantically_equivalent φ.ex ψ.ex :=
begin
  rw [semantically_equivalent, models_bounded_formula],
  introsI M ne str v xs hM,
  simp [h.realize_bd_iff hM],
end

protected lemma semantically_equivalent.not {φ ψ : L.bounded_formula α n}
  (h : T.semantically_equivalent φ ψ) : T.semantically_equivalent φ.not ψ.not :=
begin
  rw [semantically_equivalent, models_bounded_formula],
  introsI M ne str v xs hM,
  simp [h.realize_bd_iff hM],
end

protected lemma semantically_equivalent.imp {φ ψ φ' ψ' : L.bounded_formula α n}
  (h : T.semantically_equivalent φ ψ) (h' : T.semantically_equivalent φ' ψ') :
  T.semantically_equivalent (φ.imp φ') (ψ.imp ψ') :=
begin
  rw [semantically_equivalent, models_bounded_formula],
  introsI M ne str v xs hM,
  simp [h.realize_bd_iff hM, h'.realize_bd_iff hM],
end

end Theory

namespace bounded_formula
variables (φ ψ : L.bounded_formula α n)

lemma semantically_equivalent_not_not :
  T.semantically_equivalent φ φ.not.not :=
λ M ne str v xs hM, by simp

lemma imp_semantically_equivalent_not_sup :
  T.semantically_equivalent (φ.imp ψ) (φ.not ⊔ ψ) :=
λ M ne str v xs hM, by simp [imp_iff_not_or]

lemma sup_semantically_equivalent_not_inf_not :
  T.semantically_equivalent (φ ⊔ ψ) (φ.not ⊓ ψ.not).not :=
λ M ne str v xs hM, by simp [imp_iff_not_or]

lemma inf_semantically_equivalent_not_sup_not :
  T.semantically_equivalent (φ ⊓ ψ) (φ.not ⊔ ψ.not).not :=
λ M ne str v xs hM, by simp [and_iff_not_or_not]

lemma all_semantically_equivalent_not_ex_not (φ : L.bounded_formula α (n + 1)) :
  T.semantically_equivalent φ.all φ.not.ex.not :=
λ M ne str v xs hM, by simp

lemma ex_semantically_equivalent_not_all_not (φ : L.bounded_formula α (n + 1)) :
  T.semantically_equivalent φ.ex φ.not.all.not :=
λ M ne str v xs hM, by simp

lemma semantically_equivalent_all_lift_at :
  T.semantically_equivalent φ (φ.lift_at 1 n).all :=
λ M ne str v xs hM, by { resetI, rw [realize_iff, realize_all_lift_at_one_self] }

end bounded_formula

namespace formula
variables (φ ψ : L.formula α)

lemma semantically_equivalent_not_not :
  T.semantically_equivalent φ φ.not.not :=
φ.semantically_equivalent_not_not

lemma imp_semantically_equivalent_not_sup :
  T.semantically_equivalent (φ.imp ψ) (φ.not ⊔ ψ) :=
φ.imp_semantically_equivalent_not_sup ψ

lemma sup_semantically_equivalent_not_inf_not :
  T.semantically_equivalent (φ ⊔ ψ) (φ.not ⊓ ψ.not).not :=
φ.sup_semantically_equivalent_not_inf_not ψ

lemma inf_semantically_equivalent_not_sup_not :
  T.semantically_equivalent (φ ⊓ ψ) (φ.not ⊔ ψ.not).not :=
φ.inf_semantically_equivalent_not_sup_not ψ
end formula

namespace bounded_formula

lemma is_qf.induction_on_sup_not {P : L.bounded_formula α n → Prop} {φ : L.bounded_formula α n}
  (h : is_qf φ)
  (hf : P (⊥ : L.bounded_formula α n))
  (ha : ∀ (ψ : L.bounded_formula α n), is_atomic ψ → P ψ)
  (hsup : ∀ {φ₁ φ₂} (h₁ : P φ₁) (h₂ : P φ₂), P (φ₁ ⊔ φ₂))
  (hnot : ∀ {φ} (h : P φ), P φ.not)
  (hse : ∀ {φ₁ φ₂ : L.bounded_formula α n}
    (h : Theory.semantically_equivalent ∅ φ₁ φ₂), P φ₁ ↔ P φ₂) :
  P φ :=
is_qf.rec_on h hf ha (λ φ₁ φ₂ _ _ h1 h2,
  (hse (φ₁.imp_semantically_equivalent_not_sup φ₂)).2 (hsup (hnot h1) h2))

lemma is_qf.induction_on_inf_not {P : L.bounded_formula α n → Prop} {φ : L.bounded_formula α n}
  (h : is_qf φ)
  (hf : P (⊥ : L.bounded_formula α n))
  (ha : ∀ (ψ : L.bounded_formula α n), is_atomic ψ → P ψ)
  (hinf : ∀ {φ₁ φ₂} (h₁ : P φ₁) (h₂ : P φ₂), P (φ₁ ⊓ φ₂))
  (hnot : ∀ {φ} (h : P φ), P φ.not)
  (hse : ∀ {φ₁ φ₂ : L.bounded_formula α n}
    (h : Theory.semantically_equivalent ∅ φ₁ φ₂), P φ₁ ↔ P φ₂) :
  P φ :=
h.induction_on_sup_not hf ha (λ φ₁ φ₂ h1 h2,
  ((hse (φ₁.sup_semantically_equivalent_not_inf_not φ₂)).2 (hnot (hinf (hnot h1) (hnot h2)))))
  (λ _, hnot) (λ _ _, hse)

lemma semantically_equivalent_to_prenex (φ : L.bounded_formula α n) :
  (∅ : L.Theory).semantically_equivalent φ φ.to_prenex :=
λ M nM str v xs hM, begin
  resetI,
  simp,
end

lemma induction_on_all_ex {P : Π {m}, L.bounded_formula α m → Prop} (φ : L.bounded_formula α n)
  (hqf : ∀ {m} {ψ : L.bounded_formula α m}, is_qf ψ → P ψ)
  (hall : ∀ {m} {ψ  : L.bounded_formula α (m + 1)} (h : P ψ), P ψ.all)
  (hex : ∀ {m} {φ : L.bounded_formula α (m + 1)} (h : P φ), P φ.ex)
  (hse : ∀ {m} {φ₁ φ₂ : L.bounded_formula α m}
    (h : Theory.semantically_equivalent ∅ φ₁ φ₂), P φ₁ ↔ P φ₂) :
  P φ :=
begin
  suffices h' : ∀ {m} {φ : L.bounded_formula α m}, φ.is_prenex → P φ,
  { exact (hse φ.semantically_equivalent_to_prenex).2 (h' φ.to_prenex_is_prenex) },
  intros m φ hφ,
  induction hφ with _ _ hφ _ _ _ hφ _ _ _ hφ,
  { exact hqf hφ },
  { exact hall hφ, },
  { exact hex hφ, },
end

lemma induction_on_exists_not {P : Π {m}, L.bounded_formula α m → Prop} (φ : L.bounded_formula α n)
  (hqf : ∀ {m} {ψ : L.bounded_formula α m}, is_qf ψ → P ψ)
  (hnot : ∀ {m} {φ : L.bounded_formula α m} (h : P φ), P φ.not)
  (hex : ∀ {m} {φ : L.bounded_formula α (m + 1)} (h : P φ), P φ.ex)
  (hse : ∀ {m} {φ₁ φ₂ : L.bounded_formula α m}
    (h : Theory.semantically_equivalent ∅ φ₁ φ₂), P φ₁ ↔ P φ₂) :
  P φ :=
φ.induction_on_all_ex
  (λ _ _, hqf)
  (λ _ φ hφ, (hse φ.all_semantically_equivalent_not_ex_not).2 (hnot (hex (hnot hφ))))
  (λ _ _, hex) (λ _ _ _, hse)

end bounded_formula

end language
end first_order
