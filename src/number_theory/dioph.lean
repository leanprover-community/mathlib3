/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fin.fin2
import data.pfun
import data.vector3
import number_theory.pell_matiyasevic

/-!
# Diophantine functions and Matiyasevic's theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Hilbert's tenth problem asked whether there exists an algorithm which for a given integer polynomial
determines whether this polynomial has integer solutions. It was answered in the negative in 1970,
the final step being completed by Matiyasevic who showed that the power function is Diophantine.

Here a function is called Diophantine if its graph is Diophantine as a set. A subset `S ⊆ ℕ ^ α` in
turn is called Diophantine if there exists an integer polynomial on `α ⊕ β` such that `v ∈ S` iff
there exists `t : ℕ^β` with `p (v, t) = 0`.

## Main definitions

* `is_poly`: a predicate stating that a function is a multivariate integer polynomial.
* `poly`: the type of multivariate integer polynomial functions.
* `dioph`: a predicate stating that a set is Diophantine, i.e. a set `S ⊆ ℕ^α` is
  Diophantine if there exists a polynomial on `α ⊕ β` such that `v ∈ S` iff there
  exists `t : ℕ^β` with `p (v, t) = 0`.
* `dioph_fn`: a predicate on a function stating that it is Diophantine in the sense that its graph
  is Diophantine as a set.

## Main statements

* `pell_dioph` states that solutions to Pell's equation form a Diophantine set.
* `pow_dioph` states that the power function is Diophantine, a version of Matiyasevic's theorem.

## References

* [M. Carneiro, _A Lean formalization of Matiyasevic's theorem_][carneiro2018matiyasevic]
* [M. Davis, _Hilbert's tenth problem is unsolvable_][MR317916]

## Tags

Matiyasevic's theorem, Hilbert's tenth problem

## TODO

* Finish the solution of Hilbert's tenth problem.
* Connect `poly` to `mv_polynomial`
-/

open fin2 function nat sum

local infixr ` ::ₒ `:67 := option.elim
local infixr ` ⊗ `:65 := sum.elim

universe u

/-!
### Multivariate integer polynomials

Note that this duplicates `mv_polynomial`.
-/

section polynomials
variables {α β γ : Type*}

/-- A predicate asserting that a function is a multivariate integer polynomial.
  (We are being a bit lazy here by allowing many representations for multiplication,
  rather than only allowing monomials and addition, but the definition is equivalent
  and this is easier to use.) -/
inductive is_poly : ((α → ℕ) → ℤ) → Prop
| proj : ∀ i, is_poly (λ x : α → ℕ, x i)
| const : Π (n : ℤ), is_poly (λ x : α → ℕ, n)
| sub : Π {f g : (α → ℕ) → ℤ}, is_poly f → is_poly g → is_poly (λ x, f x - g x)
| mul : Π {f g : (α → ℕ) → ℤ}, is_poly f → is_poly g → is_poly (λ x, f x * g x)

lemma is_poly.neg {f : (α → ℕ) → ℤ} : is_poly f → is_poly (-f) :=
by { rw ←zero_sub, exact (is_poly.const 0).sub }

lemma is_poly.add {f g : (α → ℕ) → ℤ} (hf : is_poly f) (hg : is_poly g) : is_poly (f + g) :=
by { rw ←sub_neg_eq_add, exact hf.sub hg.neg }

/-- The type of multivariate integer polynomials -/
def poly (α : Type u) := {f : (α → ℕ) → ℤ // is_poly f}

namespace poly
section

instance fun_like : fun_like (poly α) (α → ℕ) (λ _, ℤ) := ⟨subtype.val, subtype.val_injective⟩

/-- Helper instance for when there are too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (poly α) (λ _, (α → ℕ) → ℤ) := fun_like.has_coe_to_fun

/-- The underlying function of a `poly` is a polynomial -/
protected lemma is_poly (f : poly α) : is_poly f := f.2

/-- Extensionality for `poly α` -/
@[ext] lemma ext {f g : poly α} : (∀ x, f x = g x) →  f = g := fun_like.ext _ _

/-- The `i`th projection function, `x_i`. -/
def proj (i) : poly α := ⟨_, is_poly.proj i⟩
@[simp] lemma proj_apply (i : α) (x) : proj i x = x i := rfl

/-- The constant function with value `n : ℤ`. -/
def const (n) : poly α := ⟨_, is_poly.const n⟩
@[simp] lemma const_apply (n) (x : α → ℕ) : const n x = n := rfl

instance : has_zero (poly α) := ⟨const 0⟩
instance : has_one (poly α) := ⟨const 1⟩
instance : has_neg (poly α) := ⟨λ f, ⟨-f, f.2.neg⟩⟩
instance : has_add (poly α) := ⟨λ f g, ⟨f + g, f.2.add g.2⟩⟩
instance : has_sub (poly α) := ⟨λ f g, ⟨f - g, f.2.sub g.2⟩⟩
instance : has_mul (poly α) := ⟨λ f g, ⟨f * g, f.2.mul g.2⟩⟩

@[simp] lemma coe_zero : ⇑(0 : poly α) = const 0 := rfl
@[simp] lemma coe_one : ⇑(1 : poly α) = const 1 := rfl
@[simp] lemma coe_neg (f : poly α) : ⇑(-f) = -f := rfl
@[simp] lemma coe_add (f g : poly α) : ⇑(f + g) = f + g := rfl
@[simp] lemma coe_sub (f g : poly α) : ⇑(f - g) = f - g := rfl
@[simp] lemma coe_mul (f g : poly α) : ⇑(f * g) = f * g := rfl

@[simp] lemma zero_apply (x) : (0 : poly α) x = 0 := rfl
@[simp] lemma one_apply (x) : (1 : poly α) x = 1 := rfl
@[simp] lemma neg_apply (f : poly α) (x) : (-f) x = -f x := rfl
@[simp] lemma add_apply (f g : poly α) (x : α → ℕ) : (f + g) x = f x + g x := rfl
@[simp] lemma sub_apply (f g : poly α) (x : α → ℕ) : (f - g) x = f x - g x := rfl
@[simp] lemma mul_apply (f g : poly α) (x : α → ℕ) : (f * g) x = f x * g x := rfl

instance (α : Type*) : inhabited (poly α) := ⟨0⟩

instance : add_comm_group (poly α) := by refine_struct
{ add   := ((+) : poly α → poly α → poly α),
  neg   := (has_neg.neg : poly α → poly α),
  sub   := (has_sub.sub),
  zero  := 0,
  zsmul := @zsmul_rec _ ⟨(0 : poly α)⟩ ⟨(+)⟩ ⟨has_neg.neg⟩,
  nsmul := @nsmul_rec _ ⟨(0 : poly α)⟩ ⟨(+)⟩ };
intros; try { refl }; refine ext (λ _, _);
simp [sub_eq_add_neg, add_comm, add_assoc]

instance : add_group_with_one (poly α) :=
{ one := 1,
  nat_cast := λ n, poly.const n,
  int_cast := poly.const,
  .. poly.add_comm_group }

instance : comm_ring (poly α) := by refine_struct
{ add   := ((+) : poly α → poly α → poly α),
  zero  := 0,
  mul   := (*),
  one   := 1,
  npow  := @npow_rec _ ⟨(1 : poly α)⟩ ⟨(*)⟩,
  .. poly.add_group_with_one, .. poly.add_comm_group };
intros; try { refl }; refine ext (λ _, _);
simp [sub_eq_add_neg, mul_add, mul_left_comm, mul_comm, add_comm, add_assoc]

lemma induction {C : poly α → Prop}
  (H1 : ∀i, C (proj i)) (H2 : ∀n, C (const n))
  (H3 : ∀f g, C f → C g → C (f - g))
  (H4 : ∀f g, C f → C g → C (f * g)) (f : poly α) : C f :=
begin
  cases f with f pf,
  induction pf with i n f g pf pg ihf ihg f g pf pg ihf ihg,
  apply H1, apply H2, apply H3 _ _ ihf ihg, apply H4 _ _ ihf ihg
end

/-- The sum of squares of a list of polynomials. This is relevant for
  Diophantine equations, because it means that a list of equations
  can be encoded as a single equation: `x = 0 ∧ y = 0 ∧ z = 0` is
  equivalent to `x^2 + y^2 + z^2 = 0`. -/
def sumsq : list (poly α) → poly α
| []      := 0
| (p::ps) := p*p + sumsq ps

lemma sumsq_nonneg (x : α → ℕ) : ∀ l, 0 ≤ sumsq l x
| []      := le_refl 0
| (p::ps) := by rw sumsq; simp [-add_comm];
                exact add_nonneg (mul_self_nonneg _) (sumsq_nonneg ps)

lemma sumsq_eq_zero (x) : ∀ l, sumsq l x = 0 ↔ l.all₂ (λ a : poly α, a x = 0)
| []      := eq_self_iff_true _
| (p::ps) := by rw [list.all₂_cons, ← sumsq_eq_zero ps]; rw sumsq; simp [-add_comm]; exact
  ⟨λ (h : p x * p x + sumsq ps x = 0),
   have p x = 0, from eq_zero_of_mul_self_eq_zero $ le_antisymm
     (by rw ← h; have t := add_le_add_left (sumsq_nonneg x ps) (p x * p x); rwa [add_zero] at t)
     (mul_self_nonneg _),
   ⟨this, by simp [this] at h; exact h⟩,
  λ ⟨h1, h2⟩, by rw [h1, h2]; refl⟩

end

/-- Map the index set of variables, replacing `x_i` with `x_(f i)`. -/
def map {α β} (f : α → β) (g : poly α) : poly β :=
⟨λ v, g $ v ∘ f, g.induction
  (λ i, by simp; apply is_poly.proj)
  (λ n, by simp; apply is_poly.const)
  (λ f g pf pg, by simp; apply is_poly.sub pf pg)
  (λ f g pf pg, by simp; apply is_poly.mul pf pg)⟩
@[simp] lemma map_apply {α β} (f : α → β) (g : poly α) (v) : map f g v = g (v ∘ f) := rfl

end poly
end polynomials

/-! ### Diophantine sets -/

/-- A set `S ⊆ ℕ^α` is Diophantine if there exists a polynomial on
  `α ⊕ β` such that `v ∈ S` iff there exists `t : ℕ^β` with `p (v, t) = 0`. -/
def dioph {α : Type u} (S : set (α → ℕ)) : Prop :=
∃ {β : Type u} (p : poly (α ⊕ β)), ∀ v, S v ↔ ∃ t, p (v ⊗ t) = 0

namespace dioph
section
variables {α β γ : Type u} {S S' : set (α → ℕ)}

lemma ext (d : dioph S) (H : ∀ v, v ∈  S ↔ v ∈ S') : dioph S' := by rwa ←set.ext H

lemma of_no_dummies (S : set (α → ℕ)) (p : poly α) (h : ∀ v, S v ↔ p v = 0) : dioph S :=
⟨pempty, p.map inl, λ v, (h v).trans ⟨λ h, ⟨pempty.rec _, h⟩, λ ⟨t, ht⟩, ht⟩⟩

lemma inject_dummies_lem (f : β → γ) (g : γ → option β) (inv : ∀ x, g (f x) = some x)
  (p : poly (α ⊕ β)) (v : α → ℕ) :
  (∃ t, p (v ⊗ t) = 0) ↔ ∃ t, p.map (inl ⊗ inr ∘ f) (v ⊗ t) = 0 :=
begin
  dsimp, refine ⟨λ t, _, λ t, _⟩; cases t with t ht,
  { have : (v ⊗ (0 ::ₒ t) ∘ g) ∘ (inl ⊗ inr ∘ f) = v ⊗ t :=
    funext (λ s, by cases s with a b; dsimp [(∘)]; try {rw inv}; refl),
    exact ⟨(0 ::ₒ t) ∘ g, by rwa this⟩ },
  { have : v ⊗ t ∘ f = (v ⊗ t) ∘ (inl ⊗ inr ∘ f) :=
    funext (λ s, by cases s with a b; refl),
    exact ⟨t ∘ f, by rwa this⟩ }
end

lemma inject_dummies (f : β → γ) (g : γ → option β) (inv : ∀ x, g (f x) = some x) (p : poly (α ⊕ β))
  (h : ∀ v, S v ↔ ∃ t, p (v ⊗ t) = 0) :
  ∃ q : poly (α ⊕ γ), ∀ v, S v ↔ ∃ t, q (v ⊗ t) = 0 :=
⟨p.map (inl ⊗ (inr ∘ f)), λ v, (h v).trans $ inject_dummies_lem f g inv _ _⟩

variables (β)

lemma reindex_dioph (f : α → β) : Π (d : dioph S), dioph {v | v ∘ f ∈ S}
| ⟨γ, p, pe⟩ := ⟨γ, p.map ((inl ∘ f) ⊗ inr), λ v, (pe _).trans $ exists_congr $ λ t,
  suffices v ∘ f ⊗ t = (v ⊗ t) ∘ (inl ∘ f ⊗ inr), by simp [this],
  funext $ λ s, by cases s with a b; refl⟩

variables {β}

lemma dioph_list.all₂ (l : list (set $ α → ℕ)) (d : l.all₂ dioph) :
  dioph {v | l.all₂ (λ S : set (α → ℕ), v ∈ S)} :=
suffices ∃ β (pl : list (poly (α ⊕ β))), ∀ v,
  list.all₂ (λ S : set _, S v) l ↔ ∃ t, list.all₂ (λ p : poly (α ⊕ β), p (v ⊗ t) = 0) pl,
from let ⟨β, pl, h⟩ := this
  in ⟨β, poly.sumsq pl, λ v, (h v).trans $ exists_congr $ λ t, (poly.sumsq_eq_zero _ _).symm⟩,
begin
  induction l with S l IH,
  exact ⟨ulift empty, [], λ v, by simp; exact ⟨λ ⟨t⟩, empty.rec _ t, trivial⟩⟩,
  simp at d,
  exact let ⟨⟨β, p, pe⟩, dl⟩ := d, ⟨γ, pl, ple⟩ := IH dl in
  ⟨β ⊕ γ, p.map (inl ⊗ inr ∘ inl) :: pl.map (λ q, q.map (inl ⊗ (inr ∘ inr))), λ v,
    by simp; exact iff.trans (and_congr (pe v) (ple v))
    ⟨λ ⟨⟨m, hm⟩, ⟨n, hn⟩⟩,
      ⟨m ⊗ n, by rw [
        show (v ⊗ m ⊗ n) ∘ (inl ⊗ inr ∘ inl) = v ⊗ m,
        from funext $ λ s, by cases s with a b; refl]; exact hm,
      by { refine list.all₂.imp (λ q hq, _) hn, dsimp [(∘)],
           rw [show (λ (x : α ⊕ γ), (v ⊗ m ⊗ n) ((inl ⊗ λ (x : γ), inr (inr x)) x)) = v ⊗ n,
               from funext $ λ s, by cases s with a b; refl]; exact hq }⟩,
    λ ⟨t, hl, hr⟩,
      ⟨⟨t ∘ inl, by rwa [
        show (v ⊗ t) ∘ (inl ⊗ inr ∘ inl) = v ⊗ t ∘ inl,
        from funext $ λ s, by cases s with a b; refl] at hl⟩,
      ⟨t ∘ inr, by
      { refine list.all₂.imp (λ q hq, _) hr, dsimp [(∘)] at hq,
        rwa [show (λ (x : α ⊕ γ), (v ⊗ t) ((inl ⊗ λ (x : γ), inr (inr x)) x)) = v ⊗ t ∘ inr,
             from funext $ λ s, by cases s with a b; refl] at hq }⟩⟩⟩⟩
end

lemma inter (d : dioph S) (d' : dioph S') : dioph (S ∩ S') := dioph_list.all₂ [S, S'] ⟨d, d'⟩

lemma union : ∀ (d : dioph S) (d' : dioph S'), dioph (S ∪ S')
| ⟨β, p, pe⟩ ⟨γ, q, qe⟩ := ⟨β ⊕ γ, p.map (inl ⊗ inr ∘ inl) * q.map (inl ⊗ inr ∘ inr), λ v,
  begin
    refine iff.trans (or_congr ((pe v).trans _) ((qe v).trans _))
      (exists_or_distrib.symm.trans (exists_congr $ λ t,
      (@mul_eq_zero _ _ _ (p ((v ⊗ t) ∘ (inl ⊗ inr ∘ inl)))
        (q ((v ⊗ t) ∘ (inl ⊗ inr ∘ inr)))).symm)),
    exact inject_dummies_lem _ (some ⊗ (λ _, none)) (λ x, rfl) _ _,
    exact inject_dummies_lem _ ((λ _, none) ⊗ some) (λ x, rfl) _ _,
  end⟩

/-- A partial function is Diophantine if its graph is Diophantine. -/
def dioph_pfun (f : (α → ℕ) →. ℕ) : Prop := dioph {v : option α → ℕ | f.graph (v ∘ some, v none)}

/-- A function is Diophantine if its graph is Diophantine. -/
def dioph_fn (f : (α → ℕ) → ℕ) : Prop := dioph {v : option α → ℕ | f (v ∘ some) = v none}

lemma reindex_dioph_fn {f : (α → ℕ) → ℕ} (g : α → β) (d : dioph_fn f) : dioph_fn (λ v, f (v ∘ g)) :=
by convert reindex_dioph (option β) (option.map g) d

lemma ex_dioph {S : set (α ⊕ β → ℕ)} : dioph S → dioph {v | ∃ x, v ⊗ x ∈ S}
| ⟨γ, p, pe⟩ := ⟨β ⊕ γ, p.map ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr), λ v,
  ⟨λ ⟨x, hx⟩, let ⟨t, ht⟩ := (pe _).1 hx in ⟨x ⊗ t, by simp; rw [
    show (v ⊗ x ⊗ t) ∘ ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr) = (v ⊗ x) ⊗ t,
    from funext $ λ s, by cases s with a b; try {cases a}; refl]; exact ht⟩,
  λ ⟨t, ht⟩, ⟨t ∘ inl, (pe _).2 ⟨t ∘ inr, by simp at ht; rwa [
    show (v ⊗ t) ∘ ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr) = (v ⊗ t ∘ inl) ⊗ t ∘ inr,
    from funext $ λ s, by cases s with a b; try {cases a}; refl] at ht⟩⟩⟩⟩

lemma ex1_dioph {S : set (option α → ℕ)} : dioph S → dioph {v | ∃ x, x ::ₒ v ∈ S}
| ⟨β, p, pe⟩ := ⟨option β, p.map (inr none ::ₒ inl ⊗ inr ∘ some), λ v,
  ⟨λ ⟨x, hx⟩, let ⟨t, ht⟩ := (pe _).1 hx in ⟨x ::ₒ t, by simp; rw [
    show (v ⊗ x ::ₒ t) ∘ (inr none ::ₒ inl ⊗ inr ∘ some) = x ::ₒ v ⊗ t,
    from funext $ λ s, by cases s with a b; try {cases a}; refl]; exact ht⟩,
  λ ⟨t, ht⟩, ⟨t none, (pe _).2 ⟨t ∘ some, by simp at ht; rwa [
    show (v ⊗ t) ∘ (inr none ::ₒ inl ⊗ inr ∘ some) = t none ::ₒ v ⊗ t ∘ some,
    from funext $ λ s, by cases s with a b; try {cases a}; refl] at ht⟩⟩⟩⟩

theorem dom_dioph {f : (α → ℕ) →. ℕ} (d : dioph_pfun f) : dioph f.dom :=
cast (congr_arg dioph $ set.ext $ λ v, (pfun.dom_iff_graph _ _).symm) (ex1_dioph d)

theorem dioph_fn_iff_pfun (f : (α → ℕ) → ℕ) : dioph_fn f = @dioph_pfun α f :=
by refine congr_arg dioph (set.ext $ λ v, _); exact pfun.lift_graph.symm

lemma abs_poly_dioph (p : poly α) : dioph_fn (λ v, (p v).nat_abs) :=
of_no_dummies _ ((p.map some - poly.proj none) * (p.map some + poly.proj none)) $ λ v,
 by { dsimp, exact int.eq_nat_abs_iff_mul_eq_zero }

theorem proj_dioph (i : α) : dioph_fn (λ v, v i) :=
abs_poly_dioph (poly.proj i)

theorem dioph_pfun_comp1 {S : set (option α → ℕ)} (d : dioph S) {f} (df : dioph_pfun f) :
  dioph {v :  α → ℕ | ∃ h : f.dom v, f.fn v h ::ₒ v ∈ S} :=
ext (ex1_dioph (d.inter df)) $ λ v,
⟨λ ⟨x, hS, (h: Exists _)⟩, by
  rw [show (x ::ₒ v) ∘ some = v, from funext $ λ s, rfl] at h;
  cases h with hf h; refine ⟨hf, _⟩; rw [pfun.fn, h]; exact hS,
λ ⟨x, hS⟩, ⟨f.fn v x, hS, show Exists _,
  by rw [show (f.fn v x ::ₒ v) ∘ some = v, from funext $ λ s, rfl]; exact ⟨x, rfl⟩⟩⟩

theorem dioph_fn_comp1 {S : set (option α → ℕ)} (d : dioph S) {f : (α → ℕ) → ℕ} (df : dioph_fn f) :
  dioph {v | f v ::ₒ v ∈ S} :=
ext (dioph_pfun_comp1 d $ cast (dioph_fn_iff_pfun f) df) $ λ v,
⟨λ ⟨_, h⟩, h, λ h, ⟨trivial, h⟩⟩

end

section
variables {α β : Type} {n : ℕ}

open vector3
open_locale vector3

local attribute [reducible] vector3

lemma dioph_fn_vec_comp1 {S : set (vector3 ℕ (succ n))} (d : dioph S) {f : vector3 ℕ n → ℕ}
  (df : dioph_fn f) :
  dioph {v : vector3 ℕ n | f v :: v ∈ S} :=
ext (dioph_fn_comp1 (reindex_dioph _ (none :: some) d) df) $ λ v,
  by { dsimp, congr', ext x, cases x; refl }

theorem vec_ex1_dioph (n) {S : set (vector3 ℕ (succ n))} (d : dioph S) :
  dioph {v : fin2 n → ℕ | ∃ x, x :: v ∈ S} :=
ext (ex1_dioph $ reindex_dioph _ (none :: some) d) $ λ v, exists_congr $ λ x, by { dsimp,
  rw [show option.elim x v ∘ cons none some = x :: v,
  from funext $ λ s, by cases s with a b; refl] }

lemma dioph_fn_vec (f : vector3 ℕ n → ℕ) : dioph_fn f ↔ dioph {v | f (v ∘ fs) = v fz} :=
⟨reindex_dioph _ (fz ::ₒ fs), reindex_dioph _ (none :: some)⟩

lemma dioph_pfun_vec (f : vector3 ℕ n →. ℕ) : dioph_pfun f ↔ dioph {v | f.graph (v ∘ fs, v fz)} :=
⟨reindex_dioph _ (fz ::ₒ fs), reindex_dioph _ (none :: some)⟩

lemma dioph_fn_compn : ∀ {n} {S : set (α ⊕ fin2 n → ℕ)} (d : dioph S)
  {f : vector3 ((α → ℕ) → ℕ) n} (df : vector_allp dioph_fn f),
  dioph {v : α → ℕ | v ⊗ (λ i, f i v) ∈ S}
| 0 S d f := λ df, ext (reindex_dioph _ (id ⊗ fin2.elim0) d) $ λ v,
  by { dsimp, congr', ext x, obtain (_ | _ | _) := x, refl }
| (succ n) S d f := f.cons_elim $ λ f fl, by simp; exact λ df dfl,
  have dioph {v |v ∘ inl ⊗ f (v ∘ inl) :: v ∘ inr ∈ S},
  from ext (dioph_fn_comp1 (reindex_dioph _ (some ∘ inl ⊗ none :: some ∘ inr) d) $
    reindex_dioph_fn inl df) $ λ v,
  by { dsimp, congr', ext x, obtain (_ | _ | _) := x; refl },
  have dioph {v | v ⊗ f v :: (λ (i : fin2 n), fl i v) ∈ S},
  from @dioph_fn_compn n (λ v, S (v ∘ inl ⊗ f (v ∘ inl) :: v ∘ inr)) this _ dfl,
  ext this $ λ v, by { dsimp, congr', ext x, obtain _ | _ | _ := x; refl }

lemma dioph_comp {S : set (vector3 ℕ n)} (d : dioph S) (f : vector3 ((α → ℕ) → ℕ) n)
  (df : vector_allp dioph_fn f) : dioph {v | (λ i, f i v) ∈ S} :=
dioph_fn_compn (reindex_dioph _ inr d) df

lemma dioph_fn_comp {f : vector3 ℕ n → ℕ} (df : dioph_fn f) (g : vector3 ((α → ℕ) → ℕ) n)
  (dg : vector_allp dioph_fn g) : dioph_fn (λ v, f (λ i, g i v)) :=
dioph_comp ((dioph_fn_vec _).1 df) ((λ v, v none) :: λ i v, g i (v ∘ some)) $
by simp; exact ⟨proj_dioph none, (vector_allp_iff_forall _ _).2 $ λ i,
  reindex_dioph_fn _ $ (vector_allp_iff_forall _ _).1 dg _⟩

localized "notation (name := dioph.inter) x ` D∧ `:35 y := dioph.inter x y" in dioph
localized "notation (name := dioph.union) x ` D∨ `:35 y := dioph.union x y" in dioph

localized "notation (name := dioph.vec_ex1_dioph) `D∃`:30 := dioph.vec_ex1_dioph" in dioph

localized "prefix (name := fin2.of_nat') `&`:max := fin2.of_nat'" in dioph
theorem proj_dioph_of_nat {n : ℕ} (m : ℕ) [is_lt m n] : dioph_fn (λ v : vector3 ℕ n, v &m) :=
proj_dioph &m
localized "prefix (name := proj_dioph_of_nat) `D&`:100 := dioph.proj_dioph_of_nat" in dioph

theorem const_dioph (n : ℕ) : dioph_fn (const (α → ℕ) n) :=
abs_poly_dioph (poly.const n)
localized "prefix (name := const_dioph) `D.`:100 := dioph.const_dioph" in dioph

variables {f g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g)
include df dg

lemma dioph_comp2 {S : ℕ → ℕ → Prop} (d : dioph (λ v:vector3 ℕ 2, S (v &0) (v &1))) :
  dioph (λ v, S (f v) (g v)) :=
dioph_comp d [f, g] (by exact ⟨df, dg⟩)

lemma dioph_fn_comp2 {h : ℕ → ℕ → ℕ} (d : dioph_fn (λ v:vector3 ℕ 2, h (v &0) (v &1))) :
  dioph_fn (λ v, h (f v) (g v)) :=
dioph_fn_comp d [f, g] (by exact ⟨df, dg⟩)

lemma eq_dioph : dioph (λ v, f v = g v) :=
dioph_comp2 df dg $ of_no_dummies _ (poly.proj &0 - poly.proj &1)
  (λ v, (int.coe_nat_eq_coe_nat_iff _ _).symm.trans
  ⟨@sub_eq_zero_of_eq ℤ _ (v &0) (v &1), eq_of_sub_eq_zero⟩)
localized "infix (name := eq_dioph) ` D= `:50 := dioph.eq_dioph" in dioph

lemma add_dioph : dioph_fn (λ v, f v + g v) :=
dioph_fn_comp2 df dg $ abs_poly_dioph (poly.proj &0 + poly.proj &1)
localized "infix (name := add_dioph) ` D+ `:80 := dioph.add_dioph" in dioph

lemma mul_dioph : dioph_fn (λ v, f v * g v) :=
dioph_fn_comp2 df dg $ abs_poly_dioph (poly.proj &0 * poly.proj &1)
localized "infix (name := mul_dioph) ` D* `:90 := dioph.mul_dioph" in dioph

lemma le_dioph : dioph {v | f v ≤ g v} :=
dioph_comp2 df dg $ ext (D∃2 $ D&1 D+ D&0 D= D&2) (λ v, ⟨λ ⟨x, hx⟩, le.intro hx, le.dest⟩)
localized "infix (name := le_dioph) ` D≤ `:50 := dioph.le_dioph" in dioph

lemma lt_dioph : dioph {v | f v < g v} := df D+ (D. 1) D≤ dg
localized "infix (name := lt_dioph) ` D< `:50 := dioph.lt_dioph" in dioph

lemma ne_dioph : dioph {v | f v ≠ g v} :=
ext (df D< dg D∨ dg D< df) $ λ v, by { dsimp, exact lt_or_lt_iff_ne }
localized "infix (name := ne_dioph) ` D≠ `:50 := dioph.ne_dioph" in dioph

lemma sub_dioph : dioph_fn (λ v, f v - g v) :=
dioph_fn_comp2 df dg $ (dioph_fn_vec _).2 $
ext (D&1 D= D&0 D+ D&2 D∨ D&1 D≤ D&2 D∧ D&0 D= D.0) $ (vector_all_iff_forall _).1 $ λ x y z,
show (y = x + z ∨ y ≤ z ∧ x = 0) ↔ y - z = x, from
⟨λ o, begin
  rcases o with ae | ⟨yz, x0⟩,
  { rw [ae, add_tsub_cancel_right] },
  { rw [x0, tsub_eq_zero_iff_le.mpr yz] }
end, begin
  rintro rfl,
  cases le_total y z with yz zy,
  { exact or.inr ⟨yz, tsub_eq_zero_iff_le.mpr yz⟩ },
  { exact or.inl (tsub_add_cancel_of_le zy).symm },
end⟩
localized "infix (name := sub_dioph) ` D- `:80 := dioph.sub_dioph" in dioph

lemma dvd_dioph : dioph (λ v, f v ∣ g v) :=
dioph_comp (D∃2 $ D&2 D= D&1 D* D&0) [f, g] (by exact ⟨df, dg⟩)
localized "infix (name := dvd_dioph) ` D∣ `:50 := dioph.dvd_dioph" in dioph

lemma mod_dioph : dioph_fn (λ v, f v % g v) :=
have dioph (λ v : vector3 ℕ 3, (v &2 = 0 ∨ v &0 < v &2) ∧ ∃ (x : ℕ), v &0 + v &2 * x = v &1),
from (D&2 D= D.0 D∨ D&0 D< D&2) D∧ (D∃3 $ D&1 D+ D&3 D* D&0 D= D&2),
dioph_fn_comp2 df dg $ (dioph_fn_vec _).2 $ ext this $ (vector_all_iff_forall _).1 $ λ z x y,
show ((y = 0 ∨ z < y) ∧ ∃ c, z + y * c = x) ↔ x % y = z, from
⟨λ ⟨h, c, hc⟩, begin rw ← hc; simp; cases h with x0 hl, rw [x0, mod_zero],
  exact mod_eq_of_lt hl end,
λ e, by rw ← e; exact ⟨or_iff_not_imp_left.2 $ λ h, mod_lt _ (nat.pos_of_ne_zero h), x / y,
  mod_add_div _ _⟩⟩

localized "infix (name := mod_dioph) ` D% `:80 := dioph.mod_dioph" in dioph

lemma modeq_dioph {h : (α → ℕ) → ℕ} (dh : dioph_fn h) : dioph (λ v, f v ≡ g v [MOD h v]) :=
df D% dh D= dg D% dh
localized "notation (name := modeq_dioph) ` D≡ ` := dioph.modeq_dioph" in dioph

lemma div_dioph : dioph_fn (λ v, f v / g v) :=
have dioph (λ v : vector3 ℕ 3, v &2 = 0 ∧ v &0 = 0 ∨ v &0 * v &2 ≤ v &1 ∧ v &1 < (v &0 + 1) * v &2),
from (D&2 D= D.0 D∧ D&0 D= D.0) D∨ D&0 D* D&2 D≤ D&1 D∧ D&1 D< (D&0 D+ D.1) D* D&2,
dioph_fn_comp2 df dg $ (dioph_fn_vec _).2 $ ext this $ (vector_all_iff_forall _).1 $ λ z x y,
show y = 0 ∧ z = 0 ∨ z * y ≤ x ∧ x < (z + 1) * y ↔ x / y = z,
by refine iff.trans _ eq_comm; exact y.eq_zero_or_pos.elim
  (λ y0, by rw [y0, nat.div_zero]; exact
    ⟨λ o, (o.resolve_right $ λ ⟨_, h2⟩, nat.not_lt_zero _ h2).right, λ z0, or.inl ⟨rfl, z0⟩⟩)
  (λ ypos, iff.trans ⟨λ o, o.resolve_left $ λ ⟨h1, _⟩, ne_of_gt ypos h1, or.inr⟩
    (le_antisymm_iff.trans $ and_congr (nat.le_div_iff_mul_le ypos) $
      iff.trans ⟨lt_succ_of_le, le_of_lt_succ⟩ (div_lt_iff_lt_mul ypos)).symm)
localized "infix (name := div_dioph) ` D/ `:80 := dioph.div_dioph" in dioph

omit df dg
open pell

lemma pell_dioph : dioph (λ v:vector3 ℕ 4, ∃ h : 1 < v &0,
  xn h (v &1) = v &2 ∧ yn h (v &1) = v &3) :=
have dioph {v : vector3 ℕ 4 |
1 < v &0 ∧ v &1 ≤ v &3 ∧
(v &2 = 1 ∧ v &3 = 0 ∨
∃ (u w s t b : ℕ),
  v &2 * v &2 - (v &0 * v &0 - 1) * v &3 * v &3 = 1 ∧
  u * u - (v &0 * v &0 - 1) * w * w = 1 ∧
  s * s - (b * b - 1) * t * t = 1 ∧
  1 < b ∧ (b ≡ 1 [MOD 4 * v &3]) ∧ (b ≡ v &0 [MOD u]) ∧
  0 < w ∧ v &3 * v &3 ∣ w ∧
  (s ≡ v &2 [MOD u]) ∧
  (t ≡ v &1 [MOD 4 * v &3]))}, from
D.1 D< D&0 D∧ D&1 D≤ D&3 D∧
((D&2 D= D.1 D∧ D&3 D= D.0) D∨
 (D∃4 $ D∃5 $ D∃6 $ D∃7 $ D∃8 $
  D&7 D* D&7 D- (D&5 D* D&5 D- D.1) D* D&8 D* D&8 D= D.1 D∧
  D&4 D* D&4 D- (D&5 D* D&5 D- D.1) D* D&3 D* D&3 D= D.1 D∧
  D&2 D* D&2 D- (D&0 D* D&0 D- D.1) D* D&1 D* D&1 D= D.1 D∧
  D.1 D< D&0 D∧ (D≡ (D&0) (D.1) (D.4 D* D&8)) D∧ (D≡ (D&0) (D&5) D&4) D∧
  D.0 D< D&3 D∧ D&8 D* D&8 D∣ D&3 D∧
  (D≡ (D&2) (D&7) D&4) D∧
  (D≡ (D&1) (D&6) (D.4 D* D&8)))),
dioph.ext this $ λ v, matiyasevic.symm

lemma xn_dioph : dioph_pfun (λ v:vector3 ℕ 2, ⟨1 < v &0, λ h, xn h (v &1)⟩) :=
have dioph (λ v:vector3 ℕ 3, ∃ y, ∃ h : 1 < v &1, xn h (v &2) = v &0 ∧ yn h (v &2) = y), from
let D_pell := pell_dioph.reindex_dioph (fin2 4) [&2, &3, &1, &0] in D∃3 D_pell,
(dioph_pfun_vec _).2 $ dioph.ext this $ λ v, ⟨λ ⟨y, h, xe, ye⟩, ⟨h, xe⟩, λ ⟨h, xe⟩, ⟨_, h, xe, rfl⟩⟩

include df dg
/-- A version of **Matiyasevic's theorem** -/
theorem pow_dioph : dioph_fn (λ v, f v ^ g v) :=
have dioph {v : vector3 ℕ 3 |
v &2 = 0 ∧ v &0 = 1 ∨ 0 < v &2 ∧
(v &1 = 0 ∧ v &0 = 0 ∨ 0 < v &1 ∧
∃ (w a t z x y : ℕ),
  (∃ (a1 : 1 < a), xn a1 (v &2) = x ∧ yn a1 (v &2) = y) ∧
  (x ≡ y * (a - v &1) + v &0 [MOD t]) ∧
  2 * a * v &1 = t + (v &1 * v &1 + 1) ∧
  v &0 < t ∧ v &1 ≤ w ∧ v &2 ≤ w ∧
  a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1)}, from
let D_pell := pell_dioph.reindex_dioph (fin2 9) [&4, &8, &1, &0] in
(D&2 D= D.0 D∧ D&0 D= D.1) D∨ (D.0 D< D&2 D∧
((D&1 D= D.0 D∧ D&0 D= D.0) D∨ (D.0 D< D&1 D∧
 (D∃3 $ D∃4 $ D∃5 $ D∃6 $ D∃7 $ D∃8 $ D_pell D∧
  (D≡ (D&1) (D&0 D* (D&4 D- D&7) D+ D&6) (D&3)) D∧
  D.2 D* D&4 D* D&7 D= D&3 D+ (D&7 D* D&7 D+ D.1) D∧
  D&6 D< D&3 D∧ D&7 D≤ D&5 D∧ D&8 D≤ D&5 D∧
  D&4 D* D&4 D- ((D&5 D+ D.1) D* (D&5 D+ D.1) D- D.1) D* (D&5 D* D&2) D* (D&5 D* D&2) D= D.1)))),
dioph_fn_comp2 df dg $ (dioph_fn_vec _).2 $ dioph.ext this $ λ v, iff.symm $
eq_pow_of_pell.trans $ or_congr iff.rfl $ and_congr iff.rfl $ or_congr iff.rfl $ and_congr iff.rfl $
⟨λ ⟨w, a, t, z, a1, h⟩, ⟨w, a, t, z, _, _, ⟨a1, rfl, rfl⟩, h⟩,
 λ ⟨w, a, t, z, ._, ._, ⟨a1, rfl, rfl⟩, h⟩, ⟨w, a, t, z, a1, h⟩⟩

end
end dioph
