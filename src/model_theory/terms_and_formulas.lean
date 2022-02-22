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

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/

universes u v w w'

namespace first_order
namespace language

variables {L : language.{u v}} {M N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variables {α : Type w} {β : Type w'}
open_locale first_order cardinal
open Structure

variables (L) (α)
/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive term : Type (max u w)
| var {} : ∀ (a : α), term
| func {} : ∀ {l : ℕ} (f : L.functions l) (ts : fin l → term), term
export term

variables {L} {α}

/-- Relabels a term's variables along a particular function. -/
@[simp] def term.relabel (g : α → β) : L.term α → L.term β
| (var i) := var (g i)
| (func f ts) := func f (λ i, (ts i).relabel)

@[simp] def term.to_list : L.term α → list (((Σ i, L.functions i) ⊕ α) ⊕ ℕ)
| (var i) := [sum.inl (sum.inr i)]
| (func f ts) := (sum.inl (sum.inl (⟨_, f⟩ : Σ i, L.functions i))) ::
    (((list.fin_range _).map (λ i, sum.inr (ts i).to_list.length)) ++
      ((list.fin_range _).map (λ i, (ts i).to_list)).join)

lemma term.to_list_injective :
  function.injective (term.to_list : L.term α → list (((Σ i, L.functions i) ⊕ α) ⊕ ℕ)) :=
begin
  intro t₁,
  induction t₁ with a n f ts ih; intros t₂ h,
  { cases t₂,
    { rw sum.inr_injective (sum.inl_injective (list.head_eq_of_cons_eq h)) },
    { exact (sum.inr_ne_inl (sum.inl_injective (list.head_eq_of_cons_eq h))).elim } },
  { cases t₂ with a' n' f' ts',
    { exact (sum.inl_ne_inr (sum.inl_injective (list.head_eq_of_cons_eq h))).elim},
    { obtain ⟨rfl, rfl⟩ := sum.inl_injective (list.head_eq_of_cons_eq h),
      refine congr rfl (funext (λ i, ih i _)),
      simp only [term.to_list] at h,
      have h' := list.append_inj_left h.2 (by simp only [list.length_map]),
      have h'' := (list.eq_iff_join_eq ((list.fin_range n).map (λ i, (ts i).to_list))
          ((list.fin_range n).map (λ i, (ts' i).to_list))).2 ⟨_, _⟩,
      { rw list.map_eq_map_iff at h'',
        rw h'' i (list.mem_fin_range i), },
      { rw h' at h,
        exact list.append_left_cancel h.2 },
      { rw list.map_eq_map_iff at h',
          rw [list.map_map, list.map_map, list.map_eq_map_iff],
          intros x hx,
          simp only [sum.inr.inj (h' x hx), function.comp_app] } } }
end

lemma card_term_le : # (L.term α) ≤ # ((Σ i, L.functions i) ⊕ α) + ω :=
begin
  refine (function.embedding.cardinal_le ⟨term.to_list, term.to_list_injective⟩).trans _,
  rw cardinal.mk_list_eq_mk,
  simp,
end

instance [inhabited α] : inhabited (L.term α) :=
⟨var default⟩

instance : has_coe L.const (L.term α) :=
⟨λ c, func c fin_zero_elim⟩

/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
@[simp] def realize_term (v : α → M) :
  ∀ (t : L.term α), M
| (var k)         := v k
| (func f ts)     := fun_map f (λ i, realize_term (ts i))

@[simp] lemma realize_term_relabel (g : α → β) (v : β → M) (t : L.term α) :
  realize_term v (t.relabel g) = realize_term (v ∘ g) t :=
begin
  induction t with _ n f ts ih,
  { refl, },
  { simp [ih] }
end

@[simp] lemma hom.realize_term (v : α → M)
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

@[simp] lemma embedding.realize_term (v : α → M)
  (t : L.term α) (g : M ↪[L] N) :
  realize_term (g ∘ v) t = g (realize_term v t) :=
g.to_hom.realize_term v t

@[simp] lemma equiv.realize_term (v : α → M)
  (t : L.term α) (g : M ≃[L] N) :
  realize_term (g ∘ v) t = g (realize_term v t) :=
g.to_hom.realize_term v t

variables (L) (α)

/-- `bounded_formula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive bounded_formula : ℕ → Type (max u v w)
| bd_falsum {} {n} : bounded_formula n
| bd_equal {n} (t₁ t₂ : L.term (α ⊕ fin n)) : bounded_formula n
| bd_rel {n l : ℕ} (R : L.relations l) (ts : fin l → L.term (α ⊕ fin n)) : bounded_formula n
| bd_imp {n} (f₁ f₂ : bounded_formula n) : bounded_formula n
| bd_all {n} (f : bounded_formula (n+1)) : bounded_formula n

export bounded_formula

instance {α : Type*} {n : ℕ} : inhabited (L.bounded_formula α n) :=
⟨bd_falsum⟩

/-- `formula α` is the type of formulas with all free variables indexed by `α`. -/
@[reducible] def formula := L.bounded_formula α 0

variable {α}

/-- A sentence is a formula with no free variables. -/
@[reducible] def sentence           := L.formula empty

/-- A theory is a set of sentences. -/
@[reducible] def Theory := set L.sentence

variables {L}

section formula
variable {n : ℕ}

namespace bounded_formula

@[simp] def to_list : ∀ {k : ℕ}, L.bounded_formula α k →
  list ((((Σ i, L.term (α ⊕ fin i)) ⊕ (Σ i, (L.relations i))) ⊕ ℕ) ⊕ ℕ)
| k bd_falsum := [sum.inl (sum.inr 0)]
| k (bd_equal t₁ t₂) := [sum.inl (sum.inr 1), (sum.inl (sum.inl (sum.inl ⟨_, t₁⟩))),
    (sum.inl (sum.inl (sum.inl ⟨_, t₂⟩)))]
| k (bd_rel R ts) := sum.inl (sum.inl (sum.inr ⟨_, R⟩)) ::
    ((list.fin_range _).map (sum.inl ∘ sum.inl ∘ sum.inl ∘ sigma.mk _ ∘ ts))
| k (bd_imp f₁ f₂) := (sum.inl (sum.inr 2)) :: (sum.inr f₁.to_list.length) ::
    (f₁.to_list ++ f₂.to_list)
| k (bd_all f) := sum.inl (sum.inr 3) :: f.to_list

lemma to_list_injective {k : ℕ} :
  function.injective (to_list : L.bounded_formula α k → list _) :=
begin
  intro f₁,
  induction f₁ with _ _ _ _ _ _ _ _ _ _ _ i1 i2 _ _ i3; intros f₂ h,
  { cases f₂,
    { refl },
    { exact (nat.zero_ne_one (sum.inr_injective (sum.inl_injective
        (list.head_eq_of_cons_eq h)))).elim },
    { exact (sum.inr_ne_inl (sum.inl_injective (list.head_eq_of_cons_eq h))).elim },
    { exact (ne_of_lt dec_trivial (sum.inr_injective (sum.inl_injective
        (list.head_eq_of_cons_eq h)))).elim },
    { exact (ne_of_lt dec_trivial (sum.inr_injective (sum.inl_injective
        (list.head_eq_of_cons_eq h)))).elim } },
  { cases f₂,
    { exact (nat.zero_ne_one (sum.inr_injective (sum.inl_injective
        (list.head_eq_of_cons_eq h).symm))).elim },
    { simp only [to_list, eq_self_iff_true, heq_iff_eq, true_and, and_true] at h,
      rw [h.1, h.2] },
    { exact (sum.inr_ne_inl (sum.inl_injective (list.head_eq_of_cons_eq h))).elim },
    { exact (ne_of_lt dec_trivial (sum.inr_injective (sum.inl_injective
        (list.head_eq_of_cons_eq h)))).elim },
    { exact (ne_of_lt dec_trivial (sum.inr_injective (sum.inl_injective
        (list.head_eq_of_cons_eq h)))).elim } },
  { cases f₂,
    { exact (sum.inl_ne_inr (sum.inl_injective (list.head_eq_of_cons_eq h))).elim },
    { exact (sum.inl_ne_inr (sum.inl_injective (list.head_eq_of_cons_eq h))).elim },
    { simp only [to_list] at h,
      obtain ⟨⟨rfl, rfl⟩, h⟩ := h,
      rw list.map_eq_map_iff at h,
      refine congr rfl (funext (λ i, _)),
      have h := sum.inl_injective (sum.inl_injective (sum.inl_injective
        (h i (list.mem_fin_range i)))),
      have h := sigma_mk_injective h,
      exact h, },
    { exact (sum.inl_ne_inr (sum.inl_injective (list.head_eq_of_cons_eq h))).elim },
    { exact (sum.inl_ne_inr (sum.inl_injective (list.head_eq_of_cons_eq h))).elim } },
  { cases f₂,
    { exact (ne_of_gt dec_trivial (sum.inr_injective (sum.inl_injective
        (list.head_eq_of_cons_eq h)))).elim },
    { exact (ne_of_gt dec_trivial (sum.inr_injective (sum.inl_injective
        (list.head_eq_of_cons_eq h)))).elim },
    { exact (sum.inr_ne_inl (sum.inl_injective (list.head_eq_of_cons_eq h))).elim },
    { simp only [to_list, list.cons_append, list.singleton_append, eq_self_iff_true,
        true_and] at h,
      rw [i2 (list.append_inj_right h.2 h.1), i1 (list.append_inj_left h.2 h.1)], },
    { exact (ne_of_lt dec_trivial (sum.inr_injective (sum.inl_injective
        (list.head_eq_of_cons_eq h)))).elim } },
  { cases f₂,
    { exact (ne_of_gt dec_trivial (sum.inr_injective (sum.inl_injective
      (list.head_eq_of_cons_eq h)))).elim },
    { exact (ne_of_gt dec_trivial (sum.inr_injective (sum.inl_injective
        (list.head_eq_of_cons_eq h)))).elim },
    { exact (sum.inr_ne_inl (sum.inl_injective (list.head_eq_of_cons_eq h))).elim },
    { exact (ne_of_gt dec_trivial (sum.inr_injective (sum.inl_injective
        (list.head_eq_of_cons_eq h)))).elim },
    { rw i3 (list.tail_eq_of_cons_eq h) } },
end

instance : has_bot (L.bounded_formula α n) := ⟨bd_falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
def bd_not (φ : L.bounded_formula α n) : L.bounded_formula α n := bd_imp φ ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
def bd_exists (φ : L.bounded_formula α (n + 1)) : L.bounded_formula α n :=
  bd_not (bd_all (bd_not φ))

instance : has_top (L.bounded_formula α n) := ⟨bd_not ⊥⟩

instance : has_inf (L.bounded_formula α n) := ⟨λ f g, bd_not (bd_imp f (bd_not g))⟩

instance : has_sup (L.bounded_formula α n) := ⟨λ f g, bd_imp (bd_not f) g⟩

/-- The biimplication between two bounded formulas. -/
def bd_iff (φ ψ : L.bounded_formula α n) := φ.bd_imp ψ ⊓ ψ.bd_imp φ

/-- A function to help relabel the variables in bounded formulas. -/
def relabel_aux {n : ℕ} (g : α → (β ⊕ fin n)) (k : ℕ) :
  α ⊕ fin k → β ⊕ fin (n + k) :=
(sum.map id fin_sum_fin_equiv) ∘ (equiv.sum_assoc _ _ _) ∘ (sum.map g id)

/-- Relabels a bounded formula's variables along a particular function. -/
def relabel (g : α → (β ⊕ fin n)) :
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
def relabel (g : α → β) : L.formula α → L.formula β :=
bounded_formula.relabel (sum.inl ∘ g)

/-- The equality of two terms as a first-order formula. -/
def equal (t₁ t₂ : L.term α) : (L.formula α) :=
bd_equal (t₁.relabel sum.inl) (t₂.relabel sum.inl)

/-- The graph of a function as a first-order formula. -/
def graph (f : L.functions n) : L.formula (fin (n + 1)) :=
equal (var 0) (func f (λ i, var i.succ))

/-- The negation of a formula. -/
def not (φ : L.formula α) : L.formula α := bd_not φ

/-- The implication between formulas, as a formula. -/
def imp : L.formula α → L.formula α → L.formula α := bd_imp

/-- The biimplication between formulas, as a formula. -/
def iff (φ ψ : L.formula α) : L.formula α := bd_iff φ ψ

end formula
end formula

variable {L}

instance nonempty_bounded_formula (n : ℕ) : nonempty $ L.bounded_formula α n :=
nonempty.intro (by constructor)

variables (M)

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
def realize_bounded_formula :
  ∀ {l} (f : L.bounded_formula α l) (v : α → M) (xs : fin l → M), Prop
| _ bd_falsum  v     xs := false
| _ (bd_equal t₁ t₂) v xs := realize_term (sum.elim v xs) t₁ = realize_term (sum.elim v xs) t₂
| _ (bd_rel R ts)   v   xs := rel_map R (λ i, realize_term (sum.elim v xs) (ts i))
| _ (bd_imp f₁ f₂)  v xs := realize_bounded_formula f₁ v xs → realize_bounded_formula f₂ v xs
| _ (bd_all f)     v   xs := ∀(x : M), realize_bounded_formula f v (fin.snoc xs x)

namespace bounded_formula

variables {M} {l : ℕ} (φ ψ : L.bounded_formula α l) (θ : L.bounded_formula α l.succ)
variables (v : α → M) (xs : fin l → M)

@[simp] lemma realize_bot :
  realize_bounded_formula M (⊥ : L.bounded_formula α l) v xs = false :=
rfl

@[simp] lemma realize_bd_not :
  realize_bounded_formula M (φ.bd_not) v xs = ¬ realize_bounded_formula M φ v xs :=
rfl

@[simp] lemma realize_bd_equal (t₁ t₂ : L.term (α ⊕ fin l)) :
  realize_bounded_formula M (bd_equal t₁ t₂) v xs =
    (realize_term (sum.elim v xs) t₁ = realize_term (sum.elim v xs) t₂) :=
rfl

@[simp] lemma realize_top :
  realize_bounded_formula M (⊤ : L.bounded_formula α l) v xs = true :=
by simp [has_top.top]

@[simp] lemma realize_inf : realize_bounded_formula M (φ ⊓ ψ) v xs =
    (realize_bounded_formula M φ v xs ∧ realize_bounded_formula M ψ v xs) :=
by simp [has_inf.inf, realize_bounded_formula]

@[simp] lemma realize_bd_imp : realize_bounded_formula M (φ.bd_imp ψ) v xs =
    (realize_bounded_formula M φ v xs → realize_bounded_formula M ψ v xs) :=
by simp only [realize_bounded_formula]

@[simp] lemma realize_sup : realize_bounded_formula M (φ ⊔ ψ) v xs =
    (realize_bounded_formula M φ v xs ∨ realize_bounded_formula M ψ v xs) :=
begin
  simp only [realize_bounded_formula, has_sup.sup, realize_bd_not, eq_iff_iff],
  tauto,
end

@[simp] lemma realize_bd_all : realize_bounded_formula M (bd_all θ) v xs =
    ∀ (a : M), (realize_bounded_formula M θ v (fin.snoc xs a)) :=
rfl

@[simp] lemma realize_bd_exists : realize_bounded_formula M θ.bd_exists v xs =
    ∃ (a : M), (realize_bounded_formula M θ v (fin.snoc xs a)) :=
begin
  rw [bd_exists, realize_bd_not, realize_bd_all, not_forall],
  simp_rw [realize_bd_not, not_not],
end

@[simp] lemma realize_bd_iff : realize_bounded_formula M (φ.bd_iff ψ) v xs =
  (realize_bounded_formula M φ v xs ↔ realize_bounded_formula M ψ v xs) :=
begin
  rw [bd_iff, iff_def],
  simp,
end

end bounded_formula

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
def realize_formula (f : L.formula α) (v : α → M) : Prop :=
realize_bounded_formula M f v fin_zero_elim

namespace formula

variables {M} (φ ψ : L.formula α) (v : α → M)

@[simp] lemma realize_not :
  realize_formula M (φ.not) v = ¬ realize_formula M φ v :=
rfl

@[simp] lemma realize_bot :
  realize_formula M (⊥ : L.formula α) v = false :=
rfl

@[simp] lemma realize_top :
  realize_formula M (⊤ : L.formula α) v = true :=
bounded_formula.realize_top _ _

@[simp] lemma realize_inf : realize_formula M (φ ⊓ ψ) v =
    (realize_formula M φ v ∧ realize_formula M ψ v) :=
realize_inf _ _ _ _

@[simp] lemma realize_imp : realize_formula M (φ.imp ψ) v =
    (realize_formula M φ v → realize_formula M ψ v) :=
bounded_formula.realize_bd_imp _ _ _ _

@[simp] lemma realize_sup : realize_formula M (φ ⊔ ψ) v =
    (realize_formula M φ v ∨ realize_formula M ψ v) :=
realize_sup _ _ _ _

@[simp] lemma realize_bd_iff : realize_formula M (φ.iff ψ) v=
  (realize_formula M φ v ↔ realize_formula M ψ v) :=
bounded_formula.realize_bd_iff _ _ _ _

end formula

/-- A sentence can be evaluated as true or false in a structure. -/
@[reducible] def realize_sentence (φ : L.sentence) : Prop :=
realize_formula M φ empty.elim

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

lemma realize_relabel {m n : ℕ}
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

@[simp] lemma equiv.realize_bounded_formula {n : ℕ}  (v : α → M)
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

@[simp] lemma realize_formula_relabel
  (g : α → β) (v : β → M) (φ : L.formula α) :
  realize_formula M (φ.relabel g) v ↔ realize_formula M φ (v ∘ g) :=
begin
  rw [realize_formula, realize_formula, formula.relabel, bounded_formula.realize_relabel,
    iff_eq_eq],
  refine congr (congr rfl _) (funext fin_zero_elim),
  ext,
  simp,
end

@[simp] lemma realize_formula_equiv (v : α → M) (φ : L.formula α)
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

namespace Theory

/-- A theory is satisfiable if a structure models it. -/
def is_satisfiable (T : L.Theory) : Prop :=
∃ (M : Type (max u v)) [nonempty M] [str : L.Structure M], @Theory.model L M str T

/-- A theory is finitely satisfiable if all of its finite subtheories are satisfiable. -/
def is_finitely_satisfiable (T : L.Theory) : Prop :=
∀ (T0 : finset L.sentence), (T0 : L.Theory) ⊆ T → (T0 : L.Theory).is_satisfiable

/-- Given that a theory is satisfiable, selects a model using choice. -/
def is_satisfiable.some_model {T : L.Theory} (h : T.is_satisfiable) : Type* := classical.some h

instance is_satisfiable.nonempty_some_model {T : L.Theory} (h : T.is_satisfiable) :
  nonempty (h.some_model) :=
classical.some (classical.some_spec h)

noncomputable instance is_satisfiable.inhabited_some_model {T : L.Theory} (h : T.is_satisfiable) :
  inhabited (h.some_model) := classical.inhabited_of_nonempty'

noncomputable instance is_satisfiable.some_model_structure {T : L.Theory} (h : T.is_satisfiable) :
  L.Structure (h.some_model) :=
classical.some (classical.some_spec (classical.some_spec h))

lemma is_satisfiable.some_model_models {T : L.Theory} (h : T.is_satisfiable) :
  T.model h.some_model :=
classical.some_spec (classical.some_spec (classical.some_spec h))

lemma model.is_satisfiable {T : L.Theory} (M : Type (max u v)) [n : nonempty M]
  [S : L.Structure M] (h : T.model M) : T.is_satisfiable :=
⟨M, n, S, h⟩

lemma is_satisfiable.mono {T T' : L.Theory} (h : T'.is_satisfiable) (hs : T ⊆ T') :
  T.is_satisfiable :=
⟨h.some_model, h.nonempty_some_model, h.some_model_structure,
  h.some_model_models.mono hs⟩

lemma is_satisfiable.is_finitely_satisfiable {T : L.Theory} (h : T.is_satisfiable) :
  T.is_finitely_satisfiable :=
λ _, h.mono

/-- A theory models a (bounded) formula when any of its nonempty models realizes that formula on all
  inputs.-/
def models_bounded_formula {n : ℕ} (T : L.Theory) (φ : L.bounded_formula α n) : Prop :=
  ∀ (M : Type (max u v)) [nonempty M] [str : L.Structure M] (v : α → M) (xs : fin n → M),
    @Theory.model L M str T → @realize_bounded_formula L M str α n φ v xs

infix ` ⊨ `:51 := models_bounded_formula -- input using \|= or \vDash, but not using \models

lemma models_formula_iff (T : L.Theory) (φ : L.formula α) :
  T ⊨ φ ↔ ∀ (M : Type (max u v)) [nonempty M] [str : L.Structure M] (v : α → M),
    @Theory.model L M str T → @realize_formula L M str α φ v :=
begin
  refine forall_congr (λ M, forall_congr (λ ne, forall_congr (λ str, forall_congr
    (λ v, ⟨λ h, h fin_zero_elim, λ h xs, _⟩)))),
  rw subsingleton.elim xs fin_zero_elim,
  exact h,
end

lemma models_sentence_iff (T : L.Theory) (φ : L.sentence) :
  T ⊨ φ ↔ ∀ (M : Type (max u v)) [nonempty M] [str : L.Structure M],
    @Theory.model L M str T → @realize_sentence L M str φ :=
begin
  rw [models_formula_iff],
  refine forall_congr (λ M, forall_congr (λ ne, forall_congr (λ str, _))),
  refine ⟨λ h, h empty.elim, λ h v, _⟩,
  rw subsingleton.elim v empty.elim,
  exact h,
end

variable {n : ℕ}

section bounded_formula
open bounded_formula

/-- Two (bounded) formulas are semantically equivalent over a theory `T` when they have the same
interpretation in every model of `T`. (This is also known as logical equivalence, which also has a
proof-theoretic definition.) -/
def semantically_equivalent (T : L.Theory) (φ ψ : L.bounded_formula α n) : Prop :=
T ⊨ (φ.bd_iff ψ)

lemma semantically_equivalent.realize_bd_eq {T : L.Theory} {φ ψ : L.bounded_formula α n}
  {M : Type (max u v)} [ne : nonempty M] [str : L.Structure M] (hM : T.model M)
  (h : T.semantically_equivalent φ ψ) :
  realize_bounded_formula M φ = realize_bounded_formula M ψ :=
funext (λ v, funext (λ xs, begin
  have h' := h M v xs hM,
  simp only [realize_bd_iff] at h',
  exact iff_eq_eq.mp ⟨h'.1, h'.2⟩,
end))

lemma semantically_equivalent.some_model_realize_bd_eq {T : L.Theory} {φ ψ : L.bounded_formula α n}
  (hsat : T.is_satisfiable) (h : T.semantically_equivalent φ ψ) :
  realize_bounded_formula (hsat.some_model) φ = realize_bounded_formula (hsat.some_model) ψ :=
h.realize_bd_eq hsat.some_model_models

lemma semantically_equivalent.realize_eq {T : L.Theory} {φ ψ : L.formula α}
  {M : Type (max u v)} [ne : nonempty M] [str : L.Structure M] (hM : T.model M)
  (h : T.semantically_equivalent φ ψ) :
  realize_formula M φ = realize_formula M ψ :=
begin
  ext,
  rw [realize_formula, h.realize_bd_eq hM, ← realize_formula],
end

lemma semantically_equivalent.some_model_realize_eq {T : L.Theory} {φ ψ : L.formula α}
  (hsat : T.is_satisfiable) (h : T.semantically_equivalent φ ψ) :
  realize_formula (hsat.some_model) φ = realize_formula (hsat.some_model) ψ :=
h.realize_eq hsat.some_model_models

/-- Semantic equivalence forms an equivalence relation on formulas. -/
def semantically_equivalent_setoid (T : L.Theory) : setoid (L.bounded_formula α n) :=
{ r := semantically_equivalent T,
  iseqv := ⟨λ φ M ne str v xs hM, by simp,
    λ φ ψ h M ne str v xs hM, begin
      haveI := ne,
      rw [realize_bd_iff, iff.comm, ← realize_bd_iff],
      exact h M v xs hM,
    end, λ φ ψ θ h1 h2 M ne str v xs hM, begin
      haveI := ne,
      have h1' := h1 M v xs hM,
      have h2' := h2 M v xs hM,
      rw [realize_bd_iff] at *,
      exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩,
    end⟩ }

lemma semantically_equivalent_bd_not_bd_not {T : L.Theory} {φ : L.bounded_formula α n} :
  T.semantically_equivalent φ (bd_not (bd_not φ)) :=
λ M ne str v xs hM, by simp

lemma imp_semantically_equivalent_bd_not_sup {T : L.Theory} {φ ψ : L.bounded_formula α n} :
  T.semantically_equivalent (bd_imp φ ψ) (bd_not φ ⊔ ψ) :=
λ M ne str v xs hM, by simp [imp_iff_not_or]

lemma sup_semantically_equivalent_bd_not_inf_bd_not {T : L.Theory} {φ ψ : L.bounded_formula α n} :
  T.semantically_equivalent (φ ⊔ ψ) (bd_not ((bd_not φ) ⊓ (bd_not ψ))) :=
λ M ne str v xs hM, by simp [imp_iff_not_or]

lemma inf_semantically_equivalent_bd_not_sup_bd_not {T : L.Theory} {φ ψ : L.bounded_formula α n} :
  T.semantically_equivalent (φ ⊓ ψ) (bd_not ((bd_not φ) ⊔ (bd_not ψ))) :=
λ M ne str v xs hM, by simp [and_iff_not_or_not]

end bounded_formula

section formula
open formula

lemma semantically_equivalent_not_not {T : L.Theory} {φ : L.formula α} :
  T.semantically_equivalent φ (not (not φ)) :=
semantically_equivalent_bd_not_bd_not

lemma imp_semantically_equivalent_not_sup {T : L.Theory} {φ ψ : L.formula α} :
  T.semantically_equivalent (bd_imp φ ψ) (bd_not φ ⊔ ψ) :=
imp_semantically_equivalent_bd_not_sup

lemma sup_semantically_equivalent_not_inf_not {T : L.Theory} {φ ψ : L.formula α} :
  T.semantically_equivalent (φ ⊔ ψ) (not ((not φ) ⊓ (not ψ))) :=
sup_semantically_equivalent_bd_not_inf_bd_not

lemma inf_semantically_equivalent_not_sup_not {T : L.Theory} {φ ψ : L.formula α} :
  T.semantically_equivalent (φ ⊓ ψ) (not ((not φ) ⊔ (not ψ))) :=
inf_semantically_equivalent_bd_not_sup_bd_not

end formula
end Theory

end language
end first_order
