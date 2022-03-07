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
This file defines first-order languages and structures in the style of the
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

variables (L : language.{u v})
variables {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variables {α : Type u'} {β : Type v'}
open_locale first_order cardinal
open Structure cardinal

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

instance inhabited_of_constant [inhabited L.constants] : inhabited (L.term α) :=
⟨func (default : L.constants) default⟩

instance : has_coe L.constants (L.term α) :=
⟨λ c, func c default⟩

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

end term

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
protected def not (φ : L.bounded_formula α n) : L.bounded_formula α n := φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
protected def ex (φ : L.bounded_formula α (n + 1)) : L.bounded_formula α n :=
  φ.not.all.not

instance : has_top (L.bounded_formula α n) := ⟨bounded_formula.not ⊥⟩

instance : has_inf (L.bounded_formula α n) := ⟨λ f g, (f.imp g.not).not⟩

instance : has_sup (L.bounded_formula α n) := ⟨λ f g, f.not.imp g⟩

/-- The biimplication between two bounded formulas. -/
protected def iff (φ ψ : L.bounded_formula α n) := φ.imp ψ ⊓ ψ.imp φ

/-- A function to help relabel the variables in bounded formulas. -/
def relabel_aux (g : α → (β ⊕ fin n)) (k : ℕ) :
  α ⊕ fin k → β ⊕ fin (n + k) :=
(sum.map id fin_sum_fin_equiv) ∘ (equiv.sum_assoc _ _ _) ∘ (sum.map g id)

@[simp] lemma sum_elim_comp_relabel_aux {m : ℕ} {g : α → (β ⊕ fin n)}
  {v : β → M} {xs : fin (n + m) → M} :
  sum.elim v xs ∘ relabel_aux g m =
    sum.elim (sum.elim v (xs ∘ (fin.cast_add m)) ∘ g) (xs ∘ (fin.nat_add n)) :=
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

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
def realize :
  ∀ {l} (f : L.bounded_formula α l) (v : α → M) (xs : fin l → M), Prop
| _ falsum        v xs := false
| _ (equal t₁ t₂) v xs := t₁.realize (sum.elim v xs) = t₂.realize (sum.elim v xs)
| _ (rel R ts)    v xs := rel_map R (λ i, (ts i).realize (sum.elim v xs))
| _ (imp f₁ f₂)   v xs := realize f₁ v xs → realize f₂ v xs
| _ (all f)       v xs := ∀(x : M), realize f v (fin.snoc xs x)

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

end bounded_formula

attribute [protected] bounded_formula.falsum bounded_formula.equal bounded_formula.rel
attribute [protected] bounded_formula.imp bounded_formula.all

namespace formula

/-- Relabels a formula's variables along a particular function. -/
def relabel (g : α → β) : L.formula α → L.formula β :=
bounded_formula.relabel (sum.inl ∘ g)

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

end formula

variable (M)

/-- A sentence can be evaluated as true or false in a structure. -/
@[reducible] def realize_sentence (φ : L.sentence) : Prop :=
φ.realize (default : _ → M)

infix ` ⊨ `:51 := realize_sentence -- input using \|= or \vDash, but not using \models

/-- A model of a theory is a structure in which every sentence is realized as true. -/
@[reducible] def Theory.model (T : L.Theory) : Prop :=
∀ φ ∈ T, realize_sentence M φ

infix ` ⊨ `:51 := Theory.model -- input using \|= or \vDash, but not using \models

variable {M}

lemma Theory.model.mono {T T' : L.Theory} (h : T'.model M) (hs : T ⊆ T') :
  T.model M :=
λ φ hφ, h φ (hs hφ)

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
variable (T : L.Theory)

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

lemma is_satisfiable.some_model_models (h : T.is_satisfiable) :
  T.model h.some_model :=
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

/-- A theory models a (bounded) formula when any of its nonempty models realizes that formula on all
  inputs.-/
def models_bounded_formula (T : L.Theory) (φ : L.bounded_formula α n) : Prop :=
  ∀ (M : Type (max u v)) [nonempty M] [str : L.Structure M] (v : α → M) (xs : fin n → M),
    @Theory.model L M str T → @bounded_formula.realize L M str α n φ v xs

infix ` ⊨ `:51 := models_bounded_formula -- input using \|= or \vDash, but not using \models

lemma models_formula_iff {T : L.Theory} {φ : L.formula α} :
  T ⊨ φ ↔ ∀ (M : Type (max u v)) [nonempty M] [str : L.Structure M] (v : α → M),
    @Theory.model L M str T → @formula.realize L M str α φ v :=
forall_congr (λ M, forall_congr (λ ne, forall_congr (λ str, forall_congr (λ v, unique.forall_iff))))

lemma models_sentence_iff {T : L.Theory} {φ : L.sentence} :
  T ⊨ φ ↔ ∀ (M : Type (max u v)) [nonempty M] [str : L.Structure M],
    @Theory.model L M str T → @realize_sentence L M str φ :=
begin
  rw [models_formula_iff],
  exact forall_congr (λ M, forall_congr (λ ne, forall_congr (λ str, unique.forall_iff)))
end

/-- Two (bounded) formulas are semantically equivalent over a theory `T` when they have the same
interpretation in every model of `T`. (This is also known as logical equivalence, which also has a
proof-theoretic definition.) -/
def semantically_equivalent (T : L.Theory) (φ ψ : L.bounded_formula α n) : Prop :=
T ⊨ φ.iff ψ

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
  iseqv := ⟨λ φ M ne str v xs hM, by simp,
    λ φ ψ h M ne str v xs hM, begin
      haveI := ne,
      rw [bounded_formula.realize_iff, iff.comm, ← bounded_formula.realize_iff],
      exact h M v xs hM,
    end, λ φ ψ θ h1 h2 M ne str v xs hM, begin
      haveI := ne,
      have h1' := h1 M v xs hM,
      have h2' := h2 M v xs hM,
      rw [bounded_formula.realize_iff] at *,
      exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩,
    end⟩ }

end Theory

namespace bounded_formula
variables {T : L.Theory} (φ ψ : L.bounded_formula α n)

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

end bounded_formula

namespace formula
variables {T : L.Theory} (φ ψ : L.formula α)

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

end language
end first_order
