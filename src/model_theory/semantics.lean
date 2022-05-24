/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import data.finset.basic
import model_theory.syntax

/-!
# Basics on First-Order Semantics
This file defines the interpretations of first-order terms, formulas, sentences, and theories
in a style inspired by the [Flypitch project](https://flypitch.github.io/).

## Main Definitions
* `first_order.language.term.realize` is defined so that `t.realize v` is the term `t` evaluated at
variables `v`.
* `first_order.language.bounded_formula.realize` is defined so that `φ.realize v xs` is the bounded
formula `φ` evaluated at tuples of variables `v` and `xs`.
* `first_order.language.formula.realize` is defined so that `φ.realize v` is the formula `φ`
evaluated at variables `v`.
* `first_order.language.sentence.realize` is defined so that `φ.realize M` is the sentence `φ`
evaluated in the structure `M`. Also denoted `M ⊨ φ`.
* `first_order.language.Theory.model` is defined so that `T.model M` is true if and only if every
sentence of `T` is realized in `M`. Also denoted `T ⊨ φ`.

## Main Results
* `first_order.language.bounded_formula.realize_to_prenex` shows that the prenex normal form of a
formula has the same realization as the original formula.
* Several results in this file show that syntactic constructions such as `relabel`, `cast_le`,
`lift_at`, `subst`, and the actions of language maps commute with realization of terms, formulas,
sentences, and theories.

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

variables {L : language.{u v}} {L' : language}
variables {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variables {α : Type u'} {β : Type v'}
open_locale first_order cardinal
open Structure cardinal fin

namespace term

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

@[simp] lemma realize_lift_at {n n' m : ℕ} {t : L.term (α ⊕ fin n)}
  {v : (α ⊕ fin (n + n')) → M} :
  (t.lift_at n' m).realize v = t.realize (v ∘
    (sum.map id (λ i, if ↑i < m then fin.cast_add n' i else fin.add_nat n' i))) :=
realize_relabel

@[simp] lemma realize_constants {c : L.constants} {v : α → M} :
  c.term.realize v = c :=
fun_map_eq_coe_constants

@[simp] lemma realize_functions_apply₁ {f : L.functions 1} {t : L.term α} {v : α → M} :
  (f.apply₁ t).realize v = fun_map f ![t.realize v] :=
begin
  rw [functions.apply₁, term.realize],
  refine congr rfl (funext (λ i, _)),
  simp only [matrix.cons_val_fin_one],
end

@[simp] lemma realize_functions_apply₂ {f : L.functions 2} {t₁ t₂ : L.term α} {v : α → M} :
  (f.apply₂ t₁ t₂).realize v = fun_map f ![t₁.realize v, t₂.realize v] :=
begin
  rw [functions.apply₂, term.realize],
  refine congr rfl (funext (fin.cases _ _)),
  { simp only [matrix.cons_val_zero], },
  { simp only [matrix.cons_val_succ, matrix.cons_val_fin_one, forall_const] }
end

lemma realize_con {A : set M} {a : A} {v : α → M} :
  (L.con a).term.realize v = a := rfl

@[simp] lemma realize_subst {t : L.term α} {tf : α → L.term β} {v : β → M} :
  (t.subst tf).realize v = t.realize (λ a, (tf a).realize v) :=
begin
  induction t with _ _ _ _ ih,
  { refl },
  { simp [ih] }
end

@[simp] lemma realize_restrict_var [decidable_eq α] {t : L.term α} {s : set α}
  (h : ↑t.var_finset ⊆ s) {v : α → M} :
  (t.restrict_var (set.inclusion h)).realize (v ∘ coe) = t.realize v :=
begin
  induction t with _ _ _ _ ih,
  { refl },
  { simp_rw [var_finset, finset.coe_bUnion, set.Union_subset_iff] at h,
    exact congr rfl (funext (λ i, ih i (h i (finset.mem_univ i)))) },
end

@[simp] lemma realize_restrict_var_left [decidable_eq α] {γ : Type*}
  {t : L.term (α ⊕ γ)} {s : set α}
  (h : ↑t.var_finset_left ⊆ s) {v : α → M} {xs : γ → M} :
  (t.restrict_var_left (set.inclusion h)).realize (sum.elim (v ∘ coe) xs) =
    t.realize (sum.elim v xs) :=
begin
  induction t with a _ _ _ ih,
  { cases a;
    refl },
  { simp_rw [var_finset_left, finset.coe_bUnion, set.Union_subset_iff] at h,
    exact congr rfl (funext (λ i, ih i (h i (finset.mem_univ i)))) },
end

end term

namespace Lhom

@[simp] lemma realize_on_term [L'.Structure M] (φ : L →ᴸ L') [φ.is_expansion_on M]
  (t : L.term α) (v : α → M) :
  (φ.on_term t).realize v = t.realize v :=
begin
  induction t with _ n f ts ih,
  { refl },
  { simp only [term.realize, Lhom.on_term, Lhom.is_expansion_on.map_on_function, ih] }
end

end Lhom

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

variables {L} {α} {n : ℕ}

namespace bounded_formula
open term

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
def realize :
  ∀ {l} (f : L.bounded_formula α l) (v : α → M) (xs : fin l → M), Prop
| _ falsum                        v xs := false
| _ (bounded_formula.equal t₁ t₂) v xs := t₁.realize (sum.elim v xs) = t₂.realize (sum.elim v xs)
| _ (bounded_formula.rel R ts)    v xs := rel_map R (λ i, (ts i).realize (sum.elim v xs))
| _ (bounded_formula.imp f₁ f₂)   v xs := realize f₁ v xs → realize f₂ v xs
| _ (bounded_formula.all f)       v xs := ∀(x : M), realize f v (snoc xs x)

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

@[simp] lemma realize_foldr_inf (l : list (L.bounded_formula α n))
  (v : α → M) (xs : fin n → M) :
  (l.foldr (⊓) ⊤).realize v xs ↔ ∀ φ ∈ l, bounded_formula.realize φ v xs :=
begin
  induction l with φ l ih,
  { simp },
  { simp [ih] }
end

@[simp] lemma realize_imp : (φ.imp ψ).realize v xs ↔ (φ.realize v xs → ψ.realize v xs) :=
by simp only [realize]

@[simp] lemma realize_rel {k : ℕ} {R : L.relations k} {ts : fin k → L.term _} :
  (R.bounded_formula ts).realize v xs ↔ rel_map R (λ i, (ts i).realize (sum.elim v xs)) :=
iff.rfl

@[simp] lemma realize_rel₁ {R : L.relations 1} {t : L.term _} :
  (R.bounded_formula₁ t).realize v xs ↔ rel_map R ![t.realize (sum.elim v xs)] :=
begin
  rw [relations.bounded_formula₁, realize_rel, iff_eq_eq],
  refine congr rfl (funext (λ _, _)),
  simp only [matrix.cons_val_fin_one],
end

@[simp] lemma realize_rel₂ {R : L.relations 2} {t₁ t₂ : L.term _} :
  (R.bounded_formula₂ t₁ t₂).realize v xs ↔
    rel_map R ![t₁.realize (sum.elim v xs), t₂.realize (sum.elim v xs)] :=
begin
  rw [relations.bounded_formula₂, realize_rel, iff_eq_eq],
  refine congr rfl (funext (fin.cases _ _)),
  { simp only [matrix.cons_val_zero]},
  { simp only [matrix.cons_val_succ, matrix.cons_val_fin_one, forall_const] }
end

@[simp] lemma realize_sup : (φ ⊔ ψ).realize v xs ↔ (φ.realize v xs ∨ ψ.realize v xs) :=
begin
  simp only [realize, has_sup.sup, realize_not, eq_iff_iff],
  tauto,
end

@[simp] lemma realize_foldr_sup (l : list (L.bounded_formula α n))
  (v : α → M) (xs : fin n → M) :
  (l.foldr (⊔) ⊥).realize v xs ↔ ∃ φ ∈ l, bounded_formula.realize φ v xs :=
begin
  induction l with φ l ih,
  { simp },
  { simp_rw [list.foldr_cons, realize_sup, ih, exists_prop, list.mem_cons_iff,
      or_and_distrib_right, exists_or_distrib, exists_eq_left] }
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

@[simp] lemma realize_subst_aux {tf : α → L.term β} {v : β → M} {xs : fin n → M} :
  (λ x, term.realize (sum.elim v xs) (sum.elim (term.relabel sum.inl ∘ tf) (var ∘ sum.inr) x)) =
    sum.elim (λ (a : α), term.realize v (tf a)) xs :=
funext (λ x, sum.cases_on x (λ x,
  by simp only [sum.elim_inl, term.realize_relabel, sum.elim_comp_inl]) (λ x, rfl))

lemma realize_subst {φ : L.bounded_formula α n} {tf : α → L.term β} {v : β → M} {xs : fin n → M} :
  (φ.subst tf).realize v xs ↔ φ.realize (λ a, (tf a).realize v) xs :=
begin
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih,
  { refl },
  { simp only [subst, bounded_formula.realize, realize_subst, realize_subst_aux] },
  { simp only [subst, bounded_formula.realize, realize_subst, realize_subst_aux] },
  { simp only [subst, realize_imp, ih1, ih2] },
  { simp only [ih, subst, realize_all] }
end

@[simp] lemma realize_restrict_free_var [decidable_eq α] {n : ℕ} {φ : L.bounded_formula α n}
  {s : set α} (h : ↑φ.free_var_finset ⊆ s) {v : α → M} {xs : fin n → M} :
  (φ.restrict_free_var (set.inclusion h)).realize (v ∘ coe) xs ↔
    φ.realize v xs :=
begin
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp [restrict_free_var, realize] },
  { simp [restrict_free_var, realize] },
  { simp [restrict_free_var, realize, ih1, ih2] },
  { simp [restrict_free_var, realize, ih3] },
end

variables [nonempty M]

lemma realize_all_lift_at_one_self {n : ℕ} {φ : L.bounded_formula α n}
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

attribute [protected] bounded_formula.falsum bounded_formula.equal bounded_formula.rel
attribute [protected] bounded_formula.imp bounded_formula.all

namespace Lhom
open bounded_formula

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

attribute [protected] bounded_formula.falsum bounded_formula.equal bounded_formula.rel
attribute [protected] bounded_formula.imp bounded_formula.all

namespace formula

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

@[simp] lemma realize_rel₁ {R : L.relations 1} {t : L.term _} :
  (R.formula₁ t).realize v ↔ rel_map R ![t.realize v] :=
begin
  rw [relations.formula₁, realize_rel, iff_eq_eq],
  refine congr rfl (funext (λ _, _)),
  simp only [matrix.cons_val_fin_one],
end

@[simp] lemma realize_rel₂ {R : L.relations 2} {t₁ t₂ : L.term _} :
  (R.formula₂ t₁ t₂).realize v ↔
    rel_map R ![t₁.realize v, t₂.realize v] :=
begin
  rw [relations.formula₂, realize_rel, iff_eq_eq],
  refine congr rfl (funext (fin.cases _ _)),
  { simp only [matrix.cons_val_zero]},
  { simp only [matrix.cons_val_succ, matrix.cons_val_fin_one, forall_const] }
end

@[simp] lemma realize_sup : (φ ⊔ ψ).realize v ↔ (φ.realize v ∨ ψ.realize v) :=
bounded_formula.realize_sup

@[simp] lemma realize_iff : (φ.iff ψ).realize v ↔ (φ.realize v ↔ ψ.realize v) :=
bounded_formula.realize_iff

@[simp] lemma realize_relabel {φ : L.formula α} {g : α → β} {v : β → M} :
  (φ.relabel g).realize v ↔ φ.realize (v ∘ g) :=
begin
  rw [realize, realize, relabel, bounded_formula.realize_relabel,
    iff_eq_eq, fin.cast_add_zero],
  exact congr rfl (funext fin_zero_elim),
end

lemma realize_relabel_sum_inr (φ : L.formula (fin n)) {v : empty → M} {x : fin n → M} :
  (bounded_formula.relabel sum.inr φ).realize v x ↔ φ.realize x :=
by rw [bounded_formula.realize_relabel, formula.realize, sum.elim_comp_inr, fin.cast_add_zero,
    cast_refl, order_iso.coe_refl, function.comp.right_id,
    subsingleton.elim (x ∘ (nat_add n : fin 0 → fin n)) default]

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

@[simp] lemma sentence.realize_not {φ : L.sentence} :
  M ⊨ φ.not ↔ ¬ M ⊨ φ :=
iff.rfl

@[simp] lemma Lhom.realize_on_sentence [L'.Structure M] (φ : L →ᴸ L') [φ.is_expansion_on M]
  (ψ : L.sentence) :
  M ⊨ φ.on_sentence ψ ↔ M ⊨ ψ :=
φ.realize_on_formula ψ

variables (L)

/-- The complete theory of a structure `M` is the set of all sentences `M` satisfies. -/
def complete_theory : L.Theory := { φ | M ⊨ φ }

variables {L}

/-- A model of a theory is a structure in which every sentence is realized as true. -/
class Theory.model (T : L.Theory) : Prop :=
(realize_of_mem : ∀ φ ∈ T, M ⊨ φ)

infix ` ⊨ `:51 := Theory.model -- input using \|= or \vDash, but not using \models

variables {M} (T : L.Theory)

@[simp] lemma Theory.model_iff : M ⊨ T ↔ ∀ φ ∈ T, M ⊨ φ := ⟨λ h, h.realize_of_mem, λ h, ⟨h⟩⟩

lemma Theory.realize_sentence_of_mem [M ⊨ T] {φ : L.sentence} (h : φ ∈ T) :
  M ⊨ φ :=
Theory.model.realize_of_mem φ h

@[simp] lemma Lhom.on_Theory_model [L'.Structure M] (φ : L →ᴸ L') [φ.is_expansion_on M]
  (T : L.Theory) :
  M ⊨ φ.on_Theory T ↔ M ⊨ T :=
by simp [Theory.model_iff, Lhom.on_Theory]

variables {M} {T}

instance model_empty : M ⊨ (∅ : L.Theory) := ⟨λ φ hφ, (set.not_mem_empty φ hφ).elim⟩

namespace Theory

lemma model.mono {T' : L.Theory} (h : M ⊨ T') (hs : T ⊆ T') :
  M ⊨ T :=
⟨λ φ hφ, T'.realize_sentence_of_mem (hs hφ)⟩

lemma model.union {T' : L.Theory} (h : M ⊨ T) (h' : M ⊨ T') :
  M ⊨ T ∪ T' :=
begin
  simp only [model_iff, set.mem_union_eq] at *,
  exact λ φ hφ, hφ.elim (h _) (h' _),
end

@[simp] lemma model_union_iff {T' : L.Theory} :
  M ⊨ T ∪ T' ↔ M ⊨ T ∧ M ⊨ T' :=
⟨λ h, ⟨h.mono (T.subset_union_left T'), h.mono (T.subset_union_right T')⟩, λ h, h.1.union h.2⟩

lemma model_singleton_iff {φ : L.sentence} :
  M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ :=
by simp

theorem model_iff_subset_complete_theory :
  M ⊨ T ↔ T ⊆ L.complete_theory M :=
T.model_iff

end Theory

instance model_complete_theory : M ⊨ L.complete_theory M :=
Theory.model_iff_subset_complete_theory.2 (subset_refl _)

variables (M N)

theorem realize_iff_of_model_complete_theory [N ⊨ L.complete_theory M] (φ : L.sentence) :
  N ⊨ φ ↔ M ⊨ φ :=
begin
  refine ⟨λ h, _, Theory.realize_sentence_of_mem (L.complete_theory M)⟩,
  contrapose! h,
  rw [← sentence.realize_not] at *,
  exact Theory.realize_sentence_of_mem (L.complete_theory M) h,
end

variables {M N}

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

namespace equiv

@[simp] lemma realize_bounded_formula (g : M ≃[L] N) (φ : L.bounded_formula α n)
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

@[simp] lemma realize_formula (g : M ≃[L] N) (φ : L.formula α) {v : α → M} :
  φ.realize (g ∘ v) ↔ φ.realize v :=
by rw [formula.realize, formula.realize, ← g.realize_bounded_formula φ,
    iff_eq_eq, unique.eq_default (g ∘ default)]

lemma realize_sentence (g : M ≃[L] N) (φ : L.sentence) :
  M ⊨ φ ↔ N ⊨ φ :=
by rw [sentence.realize, sentence.realize, ← g.realize_formula, unique.eq_default (g ∘ default)]

lemma Theory_model (g : M ≃[L] N) [M ⊨ T] : N ⊨ T :=
⟨λ φ hφ, (g.realize_sentence φ).1 (Theory.realize_sentence_of_mem T hφ)⟩

end equiv

namespace relations
open bounded_formula

variable {r : L.relations 2}

@[simp]
lemma realize_reflexive :
  M ⊨ r.reflexive ↔ reflexive (λ (x y : M), rel_map r ![x,y]) :=
forall_congr (λ _, realize_rel₂)

@[simp]
lemma realize_irreflexive :
  M ⊨ r.irreflexive ↔ irreflexive (λ (x y : M), rel_map r ![x,y]) :=
forall_congr (λ _, not_congr realize_rel₂)

@[simp]
lemma realize_symmetric :
  M ⊨ r.symmetric ↔ symmetric (λ (x y : M), rel_map r ![x,y]) :=
forall_congr (λ _, forall_congr (λ _, imp_congr realize_rel₂ realize_rel₂))

@[simp]
lemma realize_antisymmetric :
  M ⊨ r.antisymmetric ↔ anti_symmetric (λ (x y : M), rel_map r ![x,y]) :=
forall_congr (λ _, forall_congr (λ _, imp_congr realize_rel₂ (imp_congr realize_rel₂ iff.rfl)))

@[simp]
lemma realize_transitive :
  M ⊨ r.transitive ↔ transitive (λ (x y : M), rel_map r ![x,y]) :=
forall_congr (λ _, forall_congr (λ _, forall_congr
  (λ _, imp_congr realize_rel₂ (imp_congr realize_rel₂ realize_rel₂))))

@[simp]
lemma realize_total :
  M ⊨ r.total ↔ total (λ (x y : M), rel_map r ![x,y]) :=
forall_congr (λ _, forall_congr (λ _, realize_sup.trans (or_congr realize_rel₂ realize_rel₂)))

end relations

section cardinality

variable (L)

@[simp] lemma sentence.realize_card_ge (n) : M ⊨ (sentence.card_ge L n) ↔ ↑n ≤ (# M) :=
begin
  rw [← lift_mk_fin, ← lift_le, lift_lift, lift_mk_le, sentence.card_ge, sentence.realize,
    bounded_formula.realize_exs],
  simp_rw [bounded_formula.realize_foldr_inf],
  simp only [function.comp_app, list.mem_map, prod.exists, ne.def, list.mem_product,
    list.mem_fin_range, forall_exists_index, and_imp, list.mem_filter, true_and],
  refine ⟨_, λ xs, ⟨xs.some, _⟩⟩,
  { rintro ⟨xs, h⟩,
    refine ⟨⟨xs, λ i j ij, _⟩⟩,
    contrapose! ij,
    have hij := h _ i j ij rfl,
    simp only [bounded_formula.realize_not, term.realize, bounded_formula.realize_bd_equal,
      sum.elim_inr] at hij,
    exact hij },
  { rintro _ i j ij rfl,
    simp [ij] }
end

@[simp] lemma model_infinite_theory_iff : M ⊨ L.infinite_theory ↔ infinite M :=
by simp [infinite_theory, infinite_iff, omega_le]

instance model_infinite_theory [h : infinite M] :
  M ⊨ L.infinite_theory :=
L.model_infinite_theory_iff.2 h

@[simp] lemma model_nonempty_theory_iff :
  M ⊨ L.nonempty_theory ↔ nonempty M :=
by simp only [nonempty_theory, Theory.model_iff, set.mem_singleton_iff, forall_eq,
    sentence.realize_card_ge, nat.cast_one, one_le_iff_ne_zero, mk_ne_zero_iff]

instance model_nonempty [h : nonempty M] :
  M ⊨ L.nonempty_theory :=
L.model_nonempty_theory_iff.2 h

lemma model_distinct_constants_theory {M : Type w} [L[[α]].Structure M] (s : set α) :
  M ⊨ L.distinct_constants_theory s ↔ set.inj_on (λ (i : α), (L.con i : M)) s :=
begin
  simp only [distinct_constants_theory, set.compl_eq_compl, Theory.model_iff, set.mem_image,
    set.mem_inter_eq, set.mem_prod, set.mem_compl_eq, prod.exists, forall_exists_index, and_imp],
  refine ⟨λ h a as b bs ab, _, _⟩,
  { contrapose! ab,
    have h' := h _ a b as bs ab rfl,
    simp only [sentence.realize, formula.realize_not, formula.realize_equal,
      term.realize_constants] at h',
    exact h', },
  { rintros h φ a b as bs ab rfl,
    simp only [sentence.realize, formula.realize_not, formula.realize_equal,
      term.realize_constants],
    exact λ contra, ab (h as bs contra) }
end

lemma card_le_of_model_distinct_constants_theory (s : set α) (M : Type w) [L[[α]].Structure M]
  [h : M ⊨ L.distinct_constants_theory s] :
  cardinal.lift.{w} (# s) ≤ cardinal.lift.{u'} (# M) :=
lift_mk_le'.2 ⟨⟨_, set.inj_on_iff_injective.1 ((L.model_distinct_constants_theory s).1 h)⟩⟩

end cardinality

end language
end first_order
