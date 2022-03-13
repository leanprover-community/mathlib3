/-
Copyright (c) 2022 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import model_theory.terms_and_formulas

/-!
# The language of rings

## Main Definitions
* A `first_order.language.ring.L` defines the language of rings,
  which consists of 0,1,-,+,*.
-/
universes u v u'

namespace first_order
namespace language
namespace ring

/-- The constant symbols in ring.L -/
inductive consts : Type*
| zero : consts
| one : consts

/-- The unary function symbols in ring.L-/
inductive unaries : Type*
| neg : unaries

/-- The binary function symbols in ring.L-/
inductive binaries : Type*
| add : binaries
| mul : binaries

/-- All function symbols in ring.langauge-/
def functions : ℕ → Type*
| 0 := consts
| 1 := unaries
| 2 := binaries
| (n + 3) := pempty

instance : inhabited consts := ⟨ consts.zero ⟩
instance : inhabited unaries := ⟨ unaries.neg ⟩
instance : inhabited binaries := ⟨ binaries.add ⟩
instance : inhabited (functions 0) := ⟨ consts.zero ⟩

/-- The language of rings -/
def L : language.{u v} :=
{ functions := functions,
  relations := λ n, pempty }

variable {α : Type u'}

@[simp] instance : has_zero (L.term α) := ⟨ @func L _ 0 consts.zero fin_zero_elim ⟩

@[simp] instance : has_one (L.term α) := ⟨ @func L _ 0 consts.one fin_zero_elim ⟩

@[simp] instance : has_neg (L.term α) := ⟨ λ x, @func L _ 1 unaries.neg (λ _, x) ⟩

@[simp] instance : has_add (L.term α) :=
⟨ λ x y, @func L _ 2 binaries.add (λ i, match i with | ⟨0, _⟩ := x | ⟨n+1, _⟩ := y end) ⟩

@[simp] instance : has_mul (L.term α) :=
⟨ λ x y, @func L _ 2 binaries.mul (λ i, match i with | ⟨0, _⟩ := x | ⟨n+1, _⟩ := y end) ⟩

instance : has_pow (L.term α) ℕ := ⟨ λ t n, npow_rec n t ⟩

@[simp] lemma pow_zero (t : L.term α) : t ^ 0 = 1 := rfl
@[simp] lemma pow_succ {n} (t : L.term α) : t ^ (n + 1) = t * t ^ n := rfl

lemma fin_zero_elim_uniq (f : fin 0 → α) : f = fin_zero_elim := subsingleton.elim _ _

lemma fin_one_eta (f : fin 1 → α) : (λ (_ : fin 1), f 0) = f :=
funext (λ x, by {simp [unique.eq_default x] })

lemma not_succ_succ_lt_two {n : ℕ} (h : n.succ.succ < 2) : false :=
by {apply nat.not_lt_zero n, repeat {rw nat.succ_lt_succ_iff at h}, exact h }

/-- Part of the definition of ring_term_rec -/
@[simp] def term_rec_functions {C : L.term α → Sort*} (h0 : C 0)
  (h1 : C 1) (hn : Π {t}, C t → C (- t)) (ha : Π {s t}, C s → C t → C (s + t))
  (hm : Π {s t}, C s → C t → C (s * t)) :
  Π {l : ℕ} (f : functions l) (ts : fin l → L.term α),
  (Π (i : fin l), C (ts i)) → C (func f ts)
| 0 consts.zero ts h := cast (by {rw [fin_zero_elim_uniq ts], refl} ) h0
| 0 consts.one ts h := cast (by {rw [fin_zero_elim_uniq ts], refl}) h1
| 1 unaries.neg ts h := cast (by {simp only [has_neg.neg], congr, apply fin_one_eta}) $ hn $ h 0
| 2 binaries.add ts h := cast (
  by {simp only [has_add.add], congr, funext x, cases x with val hval, cases val, refl, cases val,
    refl, exfalso, exact not_succ_succ_lt_two hval } : C (ts 0 + ts 1) = C _)
    $ ha (h 0) (h 1)
| 2 binaries.mul ts h := cast (
  by {simp only [has_mul.mul], congr, funext x, cases x with val hval, cases val, refl, cases val,
    refl, exfalso, exact not_succ_succ_lt_two hval } : C (ts 0 * ts 1) = C _)
  $ hm (h 0) (h 1)
| (n + 3) f ts h := pempty.elim f

/-- An interface for mapping out of term α (basically term.rec) -/
@[simp] def term_rec {C : L.term α → Sort*} (hv : Π (x : α), C (var x)) (h0 : C 0) (h1 : C 1)
  (hn : Π {t}, C t → C (- t)) (ha : Π {s t}, C s → C t → C (s + t))
  (hm : Π {s t}, C s → C t → C (s * t)) : Π (t : L.term α), C t :=
term.rec hv (λ _, term_rec_functions h0 h1 (λ _, hn) (λ _ _, ha) (λ _ _, hm))

end ring
end language
end first_order
