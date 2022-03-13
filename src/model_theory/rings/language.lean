import model_theory.terms_and_formulas

namespace first_order
namespace language
namespace ring

universes u v u'

-----------------
-- inductive consts' : Type*
-- | zero : consts'

-- def functions' : ℕ → Type*
-- | 0 := consts'
-- | (n+1) := pempty

-- /-- The language of rings -/
-- @[reducible] def L' : language.{u v} :=
-- { functions := functions',
--   relations := λ n, pempty }

-- variable {α : Type u'}

-- @[simps] instance : has_zero (L'.term α) := ⟨ @func L' _ 0 consts'.zero fin_zero_elim ⟩

-- example {C : L'.term α → Sort*} {x0 : C 0} (ts : fin 0 → L'.term α) :
--   C $ @func L' _ 0 consts'.zero ts :=
-- cast (by {have h : ts = fin_zero_elim, simp, simp [h] } ) x0

-----------------

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

/-- To make a map out of `ring.functions`, omitting the empty case -/
def functions_rec {C : Π {n}, functions n → Sort*} (h0 : @C 0 consts.zero) (h1 : @C 0 consts.one)
  (hn : @C 1 unaries.neg) (ha : @C 2 binaries.add) (hm : @C 2 binaries.mul) :
  Π {n} (f : functions n), C f
| 0 consts.zero := h0
| 0 consts.one := h1
| 1 unaries.neg := hn
| 2 binaries.add := ha
| 2 binaries.mul := hm
| (n + 3) f := pempty.elim f

instance : inhabited consts := ⟨ consts.zero ⟩
instance : inhabited unaries := ⟨ unaries.neg ⟩
instance : inhabited binaries := ⟨ binaries.add ⟩

/-- The type `bool` is equivalent to the type of constant symbols -/
def bool_equiv_ring_consts : _root_.equiv bool consts :=
{ to_fun := λ x, match x with | ff := consts.zero | tt := consts.one end,
  inv_fun := λ c, match c with | consts.zero := ff | consts.one := tt end,
  left_inv := λ x, match x with | ff := rfl | tt := rfl end,
  right_inv := λ c, match c with | consts.zero := rfl | consts.one := rfl end }

/-- The language of rings -/
def L : language.{u v} :=
{ functions := functions,
  relations := λ n, pempty }

variable (α : Type u')

-- The terms in the language of rings, which will have instances of 0,1,-,+,*
-- @[reducible] def term := L.term α

-- The formuals in the language of rings
-- @[reducible] def formula := L.bounded_formula α

variable {α}

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

-- set_option pp.all true
/-- Part of the definition of ring_term_rec -/
@[simp] def term_rec_functions {C : L.term α → Sort*} (h0 : C 0)
  (h1 : C 1) (hn : Π {t}, C t → C (- t)) (ha : Π {s t}, C s → C t → C (s + t))
  (hm : Π {s t}, C s → C t → C (s * t)) :
  Π {l : ℕ} (f : functions l) (ts : fin l → L.term α),
  (Π (i : fin l), C (ts i)) → C (func f ts)
| 0 consts.zero ts h := cast (by {rw [fin_zero_elim_uniq ts], refl} ) h0
| 0 consts.one ts h := cast (by {rw [fin_zero_elim_uniq ts], refl}) h1
| 1 unaries.neg ts h := sorry
| 2 binaries.add ts h := sorry
| 2 binaries.mul ts h := sorry
| (n + 3) f ts h := pempty.elim f

/-- An interface for mapping out of term α (basically term.rec) -/
def term_rec {C : term α → Sort*} (hv : Π (x : α), C (var x)) (h0 : C 0) (h1 : C 1)
  (hn : Π {t}, C t → C (- t)) (ha : Π {s t}, C s → C t → C (s + t))
  (hm : Π {s t}, C s → C t → C (s * t)) : Π (t : term α), C t :=
term.rec hv (term_rec_functions h0 h1 hn ha hm)
-- | (var x) := hv x
-- | (func f d) := _





end ring
end language
end first_order
