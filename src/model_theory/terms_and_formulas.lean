/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import data.equiv.fin
import model_theory.basic

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
* A `first_order.language.theory` is a set of sentences.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/

universes u v

namespace first_order
namespace language

variables {L : language.{u v}} {M N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
open_locale first_order
open Structure

variable (L)
/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive term (α : Type) : Type u
| var {} : ∀ (a : α), term
| func {} : ∀ {l : ℕ} (f : L.functions l) (ts : fin l → term), term
export term

variable {L}

/-- Relabels a term's variables along a particular function. -/
@[simp] def term.relabel {α β : Type} (g : α → β) : L.term α → L.term β
| (var i) := var (g i)
| (func f ts) := func f (λ i, (ts i).relabel)

instance {α : Type} [inhabited α] : inhabited (L.term α) :=
⟨var default⟩

instance {α} : has_coe L.const (L.term α) :=
⟨λ c, func c fin_zero_elim⟩

/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
@[simp] def realize_term {α : Type} (v : α → M) :
  ∀ (t : L.term α), M
| (var k)         := v k
| (func f ts)     := fun_map f (λ i, realize_term (ts i))

@[simp] lemma realize_term_relabel {α β : Type} (g : α → β) (v : β → M) (t : L.term α) :
  realize_term v (t.relabel g) = realize_term (v ∘ g) t :=
begin
  induction t with _ n f ts ih,
  { refl, },
  { simp [ih] }
end

@[simp] lemma hom.realize_term {α : Type} (v : α → M)
  (t : L.term α) (g : M →[L] N) :
  realize_term (g ∘ v) t = g (realize_term v t) :=
begin
  induction t,
  { refl },
  { rw [realize_term, realize_term, g.map_fun],
    refine congr rfl _,
    ext x,
    simp [t_ih x], },
end

@[simp] lemma embedding.realize_term {α : Type}  (v : α → M)
  (t : L.term α) (g : M ↪[L] N) :
  realize_term (g ∘ v) t = g (realize_term v t) :=
g.to_hom.realize_term v t

@[simp] lemma equiv.realize_term {α : Type}  (v : α → M)
  (t : L.term α) (g : M ≃[L] N) :
  realize_term (g ∘ v) t = g (realize_term v t) :=
g.to_hom.realize_term v t

variable (L)
/-- `bounded_formula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive bounded_formula (α : Type) : ℕ → Type (max u v)
| bd_falsum {} {n} : bounded_formula n
| bd_equal {n} (t₁ t₂ : L.term (α ⊕ fin n)) : bounded_formula n
| bd_rel {n l : ℕ} (R : L.relations l) (ts : fin l → L.term (α ⊕ fin n)) : bounded_formula n
| bd_imp {n} (f₁ f₂ : bounded_formula n) : bounded_formula n
| bd_all {n} (f : bounded_formula (nat.succ n)) : bounded_formula n

export bounded_formula

instance {α : Type} {n : ℕ} : inhabited (L.bounded_formula α n) :=
⟨bd_falsum⟩

/-- `formula α` is the type of formulas with all free variables indexed by `α`. -/
@[reducible] def formula (α : Type) := L.bounded_formula α 0

/-- `partitioned_formula α β` is the type of formulas with all free variables indexed by `α` or `β`.
-/
@[reducible] def partitioned_formula (α : Type) (β : Type) := L.formula (α ⊕ β)

/-- A sentence is a formula with no free variables. -/
@[reducible] def sentence           := L.formula pempty

/-- A theory is a set of sentences. -/
@[reducible] def theory := set L.sentence

variables {L} {α : Type}

section formula
variable {n : ℕ}

namespace bounded_formula

@[simps] instance : has_bot (L.bounded_formula α n) := ⟨bd_falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[reducible] def bd_not (φ : L.bounded_formula α n) : L.bounded_formula α n :=
  bd_imp φ ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
@[reducible] def bd_exists (φ : L.bounded_formula α n.succ) : L.bounded_formula α n :=
  bd_not (bd_all (bd_not φ))

@[simps] instance : has_top (L.bounded_formula α n) := ⟨bd_not bd_falsum⟩

@[simps] instance : has_inf (L.bounded_formula α n) := ⟨λ f g, bd_not (bd_imp f (bd_not g))⟩

@[simps] instance : has_sup (L.bounded_formula α n) := ⟨λ f g, bd_imp (bd_not f) g⟩

/-- A function to help relabel the variables in bounded formulas. -/
def relabel_aux {n : ℕ} {α β : Type} (g : α → (β ⊕ fin n)) (k : ℕ) :
  α ⊕ fin k → β ⊕ fin (n + k) :=
(sum.map id fin_sum_fin_equiv) ∘ (equiv.sum_assoc _ _ _) ∘ (sum.map g id)

/-- Relabels a bounded formula's variables along a particular function. -/
def relabel {α β : Type} (g : α → (β ⊕ fin n)) :
  ∀ {k : ℕ}, L.bounded_formula α k → L.bounded_formula β (n + k)
| k bd_falsum := bd_falsum
| k (bd_equal t₁ t₂) := bd_equal (t₁.relabel (relabel_aux g k)) (t₂.relabel (relabel_aux g k))
| k (bd_rel R ts) := bd_rel R (term.relabel (relabel_aux g k) ∘ ts)
| k (bd_imp f₁ f₂) := bd_imp f₁.relabel f₂.relabel
| k (bd_all f) := bd_all f.relabel

/-- Places universal quantifiers on all extra variables of a bounded formula. -/
def close_with_forall : L.bounded_formula α n → L.formula α :=
nat.rec_on n id (λ n f φ, (f φ.bd_all))

/-- Places existential quantifiers on all extra variables of a bounded formula. -/
def close_with_exists : L.bounded_formula α n → L.formula α :=
nat.rec_on n id (λ n f φ, (f φ.bd_exists))

end bounded_formula

namespace formula

/-- Relabels a formula's variables along a particular function. -/
def relabel {α β : Type} (g : α → β) : L.formula α → L.formula β :=
bounded_formula.relabel (sum.inl ∘ g)

/-- The equality of two terms as a first-order formula. -/
def equal (t₁ t₂ : L.term α) : (L.formula α) :=
bd_equal (t₁.relabel sum.inl) (t₂.relabel sum.inl)

/-- The graph of a function as a first-order formula. -/
def graph (f : L.functions n) : L.formula (fin (n + 1)) :=
equal (var 0) (func f (λ i, var i.succ))

/-- The negation of a formula. -/
def not (φ : L.formula α) : L.formula α := bd_not φ

end formula

namespace partitioned_formula
variables {β : Type}

/-- Given a partitioned formula, swaps the two variable tuples. -/
def swap (φ : L.partitioned_formula α β) : L.partitioned_formula β α :=
φ.relabel sum.swap

/-- Given a partitioned formula, recasts the right variable tuple as extra variables in a
  bounded formula. -/
def to_bounded_formula_right (φ : L.partitioned_formula α (fin n)) : L.bounded_formula α n :=
bounded_formula.relabel id φ

/-- Given a partitioned formula, recasts the left variable tuple as extra variables in a
  bounded formula. -/
def to_bounded_formula_left (φ : L.partitioned_formula (fin n) α) : L.bounded_formula α n :=
φ.swap.to_bounded_formula_right

/-- Given a partitioned formula, places existential quantifiers over the right variable tuple. -/
def exists_right (φ : L.partitioned_formula α (fin n)) : L.formula α :=
φ.to_bounded_formula_right.close_with_exists

/-- Given a partitioned formula, places existential quantifiers over the left variable tuple. -/
def exists_left (φ : L.partitioned_formula (fin n) α) : L.formula α :=
φ.to_bounded_formula_left.close_with_exists

/-- Given a partitioned formula, places universal quantifiers over the right variable tuple. -/
def forall_right (φ : L.partitioned_formula α (fin n)) : L.formula α :=
φ.to_bounded_formula_right.close_with_forall

/-- Given a partitioned formula, places universal quantifiers over the left variable tuple. -/
def forall_left (φ : L.partitioned_formula (fin n) α) : L.formula α :=
φ.to_bounded_formula_left.close_with_forall

end partitioned_formula
end formula

variable {L}

instance nonempty_bounded_formula {α : Type} (n : ℕ) : nonempty $ L.bounded_formula α n :=
  nonempty.intro (by constructor)

variables (M)

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
@[simp] def realize_bounded_formula :
  ∀ {l} (f : L.bounded_formula α l) (v : α → M) (xs : fin l → M), Prop
| _ bd_falsum  v     xs := false
| _ (bd_equal t₁ t₂) v xs := realize_term (sum.elim v xs) t₁ = realize_term (sum.elim v xs) t₂
| _ (bd_rel R ts)   v   xs := rel_map R (λ i, realize_term (sum.elim v xs) (ts i))
| _ (bd_imp f₁ f₂)  v xs := realize_bounded_formula f₁ v xs → realize_bounded_formula f₂ v xs
| _ (bd_all f)     v   xs := ∀(x : M), realize_bounded_formula f v (fin.snoc xs x)

namespace bounded_formula

variables {M} {l : ℕ} (φ ψ : L.bounded_formula α l) (θ : L.bounded_formula α l.succ)
variables (v : α → M) (xs : fin l → M)

@[simp] lemma realize_bd_not :
  realize_bounded_formula M (φ.bd_not) v xs = ¬ realize_bounded_formula M φ v xs :=
rfl

lemma realize_bd_inf : realize_bounded_formula M (φ ⊓ ψ) v xs =
    (realize_bounded_formula M φ v xs ∧ realize_bounded_formula M ψ v xs) :=
by simp

lemma realize_bd_imp : realize_bounded_formula M (φ.bd_imp ψ) v xs =
    (realize_bounded_formula M φ v xs → realize_bounded_formula M ψ v xs) :=
by simp only [realize_bounded_formula]

lemma realize_bd_sup : realize_bounded_formula M (φ ⊔ ψ) v xs =
    (realize_bounded_formula M φ v xs ∨ realize_bounded_formula M ψ v xs) :=
begin
  simp only [realize_bounded_formula, bounded_formula.has_sup_sup, realize_bd_not, eq_iff_iff],
  tauto,
end

lemma realize_bd_all : realize_bounded_formula M (bd_all θ) v xs =
    ∀ (a : M), (realize_bounded_formula M θ v (fin.snoc xs a)) :=
rfl

lemma realize_bd_exists : realize_bounded_formula M θ.bd_exists v xs =
    ∃ (a : M), (realize_bounded_formula M θ v (fin.snoc xs a)) :=
begin
  rw [bd_exists, realize_bd_not, realize_bd_all, not_forall],
  simp_rw [realize_bd_not, not_not],
end

end bounded_formula

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
@[reducible] def realize_formula (f : L.formula α) (v : α → M) : Prop :=
realize_bounded_formula M f v fin_zero_elim

namespace formula

variables {M} (φ ψ : L.formula α) (v : α → M)

@[simp] lemma realize_not :
  realize_formula M (φ.not) v = ¬ realize_formula M φ v :=
rfl

lemma realize_inf : realize_formula M (φ ⊓ ψ) v =
    (realize_formula M φ v ∧ realize_formula M ψ v) :=
realize_bd_inf _ _ _ _

lemma realize_imp : realize_formula M (φ.bd_imp ψ) v =
    (realize_formula M φ v → realize_formula M ψ v) :=
realize_bd_imp _ _ _ _

lemma realize_sup : realize_formula M (φ ⊔ ψ) v =
    (realize_formula M φ v ∨ realize_formula M ψ v) :=
realize_bd_sup _ _ _ _

end formula

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
@[reducible] def realize_partitioned_formula {β : Type} (f : L.partitioned_formula α β)
  (v : α → M) (w : β → M) : Prop :=
realize_formula M f (sum.elim v w)

/-- A sentence can be evaluated as true or false in a structure. -/
@[reducible] def realize_sentence (φ : L.sentence) : Prop :=
realize_formula M φ pempty.elim

variable {M}

namespace bounded_formula

@[simp] lemma realize_close_with_forall {n : ℕ} (φ : L.bounded_formula α n) (v : α → M) :
  realize_formula M (close_with_forall φ) v =
    ∀ (xs : fin n → M), (realize_bounded_formula M φ v xs) :=
begin
  rw [close_with_forall],
  induction n with n ih,
  { simp only [id.def, eq_iff_iff],
    rw realize_formula,
    exact ⟨λ h x, (funext fin_zero_elim : fin_zero_elim = x) ▸ h, λ h, h _⟩ },
  { simp only [ih, realize_bounded_formula, eq_iff_iff],
    exact ⟨λ h xs, (fin.snoc_init_self xs) ▸ h _ _, λ h xs x, h (fin.snoc xs x)⟩ }
end

@[simp] lemma realize_close_with_exists {n : ℕ} (φ : L.bounded_formula α n) (v : α → M) :
  realize_formula M (close_with_exists φ) v =
    ∃ (xs : fin n → M), (realize_bounded_formula M φ v xs) :=
begin
  rw [close_with_exists],
  induction n with n ih,
  { simp only [id.def, eq_iff_iff],
    rw realize_formula,
    refine ⟨λ h, ⟨fin_zero_elim, h⟩, _⟩,
    rintro ⟨w, h⟩,
    exact (funext fin_zero_elim : w = fin_zero_elim) ▸ h, },
  { simp only [ih, realize_bd_exists, eq_iff_iff],
    split,
    { rintros ⟨xs, x, h⟩,
      exact ⟨_, h⟩ },
    { rintros ⟨xs, h⟩,
      rw ← fin.snoc_init_self xs at h,
      exact ⟨_, _, h⟩ } }
end

lemma realize_relabel {α β : Type} {m n : ℕ}
  (g : α → (β ⊕ fin m)) (v : β → M) (xs : fin (m + n) → M) (φ : L.bounded_formula α n) :
  realize_bounded_formula M (φ.relabel g) v xs ↔
    realize_bounded_formula M φ (sum.elim v (xs ∘ (fin.cast_add n)) ∘ g) (xs ∘ (fin.nat_add m)) :=
begin
  have h : ∀ (n : ℕ) (xs : fin (m + n) → M), sum.elim v xs ∘ bounded_formula.relabel_aux g n =
    sum.elim (sum.elim v (xs ∘ (fin.cast_add n)) ∘ g) (xs ∘ (fin.nat_add m)),
  { intros m xs',
    ext x,
    cases x,
    { simp only [bounded_formula.relabel_aux, function.comp_app, sum.map_inl, sum.elim_inl],
      cases g x with l r;
      simp },
    { simp [bounded_formula.relabel_aux] } },
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 n' _ ih3,
  { refl },
  { simp [realize_bounded_formula, bounded_formula.relabel, h _ xs] },
  { simp [realize_bounded_formula, bounded_formula.relabel, h _ xs] },
  { simp [realize_bounded_formula, bounded_formula.relabel, ih1, ih2] },
  { simp only [ih3, realize_bounded_formula, bounded_formula.relabel],
    refine forall_congr (λ a, (iff_eq_eq.mpr (congr (congr rfl (congr (congr rfl (congr rfl
      (funext (λ i, (dif_pos _).trans rfl)))) rfl)) _))),
    { ext i,
      by_cases h : i.val < n',
      { exact (dif_pos (nat.add_lt_add_left h m)).trans (dif_pos h).symm },
      { exact (dif_neg (λ h', h (nat.lt_of_add_lt_add_left h'))).trans (dif_neg h).symm } } }
end

end bounded_formula

@[simp] lemma equiv.realize_bounded_formula {α : Type} {n : ℕ}  (v : α → M)
  (xs : fin n → M) (φ : L.bounded_formula α n) (g : M ≃[L] N) :
  realize_bounded_formula N φ (g ∘ v) (g ∘ xs) ↔ realize_bounded_formula M φ v xs :=
begin
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp only [realize_bounded_formula, ← sum.comp_elim, equiv.realize_term, g.injective.eq_iff] },
  { simp only [realize_bounded_formula, ← sum.comp_elim, equiv.realize_term, g.map_rel], },
  { rw [realize_bounded_formula, ih1, ih2, realize_bounded_formula] },
  { rw [realize_bounded_formula, realize_bounded_formula],
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

@[simp] lemma realize_formula_relabel {α β : Type}
  (g : α → β) (v : β → M) (φ : L.formula α) :
  realize_formula M (φ.relabel g) v ↔ realize_formula M φ (v ∘ g) :=
begin
  rw [realize_formula, realize_formula, formula.relabel, bounded_formula.realize_relabel,
    iff_eq_eq],
  refine congr (congr rfl _) (funext fin_zero_elim),
  ext,
  simp,
end

@[simp] lemma realize_formula_equiv {α : Type}  (v : α → M) (φ : L.formula α)
  (g : M ≃[L] N) :
  realize_formula N φ (g ∘ v) ↔ realize_formula M φ v :=
begin
  rw [realize_formula, realize_formula, ← equiv.realize_bounded_formula v fin_zero_elim φ g,
    iff_eq_eq],
  exact congr rfl (funext fin_zero_elim),
end

@[simp]
lemma realize_equal {α : Type*} (t₁ t₂ : L.term α) (x : α → M) :
  realize_formula M (formula.equal t₁ t₂) x ↔ realize_term x t₁ = realize_term x t₂ :=
by simp [formula.equal, realize_formula]

@[simp]
lemma realize_graph {l : ℕ} (f : L.functions l) (x : fin l → M) (y : M) :
  realize_formula M (formula.graph f) (fin.cons y x) ↔ fun_map f x = y :=
begin
  simp only [formula.graph, realize_term, realize_equal, fin.cons_zero, fin.cons_succ],
  rw eq_comm,
end

namespace partitioned_formula

@[simp] lemma realize_swap {β : Type} (φ : L.partitioned_formula α β) (x : α → M) (y : β → M) :
  realize_partitioned_formula M φ.swap y x ↔ realize_partitioned_formula M φ x y :=
begin
  rw [swap, realize_partitioned_formula, realize_partitioned_formula, realize_formula_relabel,
    iff_eq_eq],
  refine congr rfl (funext (λ i, sum.cases_on i _ _));
  simp,
end

@[simp] lemma realize_to_bounded_formula_right {n : ℕ} (φ : L.partitioned_formula α (fin n))
  (x : α → M) (y : (fin n) → M) :
  realize_bounded_formula M φ.to_bounded_formula_right x y ↔ realize_partitioned_formula M φ x y :=
begin
  rw [realize_partitioned_formula, to_bounded_formula_right, bounded_formula.realize_relabel,
    realize_formula, iff_eq_eq],
  refine congr (congr rfl (funext (λ i, _))) (funext fin_zero_elim),
  cases i,
  { simp },
  { simp only [function.comp.right_id, sum.elim_inr, function.comp_app, function.id_def],
    refine congr rfl _,
    simp [fin.ext_iff] }
end

@[simp] lemma realize_to_bounded_formula_left {n : ℕ} (φ : L.partitioned_formula (fin n) α)
  (x : α → M) (y : (fin n) → M) :
  realize_bounded_formula M φ.to_bounded_formula_left x y ↔ realize_partitioned_formula M φ y x :=
by simp [to_bounded_formula_left]

@[simp] lemma realize_forall_left {n : ℕ}
  (φ : L.partitioned_formula (fin n) α) (x : α → M) :
  realize_formula M φ.forall_left x ↔ ∀ (y : fin n → M), realize_partitioned_formula M φ y x :=
by simp only [forall_left, realize_close_with_forall, realize_to_bounded_formula_left]

@[simp] lemma realize_exists_left {n : ℕ}
  (φ : L.partitioned_formula (fin n) α) (x : α → M) :
  realize_formula M φ.exists_left x ↔ ∃ (y : fin n → M), realize_partitioned_formula M φ y x :=
by simp only [exists_left, realize_close_with_exists, realize_to_bounded_formula_left]

@[simp] lemma realize_forall_right {n : ℕ}
  (φ : L.partitioned_formula α (fin n)) (x : α → M) :
  realize_formula M φ.forall_right x ↔ ∀ (y : fin n → M), realize_partitioned_formula M φ x y :=
by simp only [forall_right, realize_close_with_forall, realize_to_bounded_formula_right]

@[simp] lemma realize_exists_right {n : ℕ}
  (φ : L.partitioned_formula α (fin n)) (x : α → M) :
  realize_formula M φ.exists_right x ↔ ∃ (y : fin n → M), realize_partitioned_formula M φ x y :=
by simp only [exists_right, realize_close_with_exists, realize_to_bounded_formula_right]


end partitioned_formula

end language
end first_order
