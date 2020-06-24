/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/

import tactic
open function

namespace sym2
universe u

inductive sym2_rel (α : Type u) : (α × α) → (α × α) → Prop
| refl (x y : α) : sym2_rel ⟨x,y⟩ ⟨x,y⟩
| swap (x y : α) : sym2_rel ⟨x,y⟩ ⟨y,x⟩

-- The symmetric square is the cartesian product α × α modulo `swap`.
def sym2 (α : Type u) := quot (sym2_rel α)

@[reducible]
def sym2.mk {α : Type u} (x y : α) : sym2 α := quot.mk (sym2_rel α) ⟨x, y⟩

-- def sym2.rec_eq {α : Type u} {β : Sort*} (z : sym2 α) (f : Π (x y : α), z = sym2.mk x y  → β)
-- (h : ∀ (x y x' y' : α), Π (h : z = sym2.mk x y) (h' : z = sym2.mk x' y'), f x y h = f x' y' h') : β :=


-- A type naturally includes in the diagonal of the cartesian square, and this is the quotient of that.
instance sym2.incl_diag (α : Type u) : has_lift α (sym2 α) := ⟨λ x, sym2.mk x x⟩

def sym2.is_diag {α : Type u} (x : sym2 α) : Prop :=
quot.rec_on x (λ y, y.1 = y.2) (begin intros, cases p, simp, simp, tauto, end)

lemma sym2.mk_is_diag {α : Type u} {x y : α} (h : (sym2.mk x y).is_diag) : x = y :=
begin
  exact h,
end

lemma sym2.comm {α : Type u} (x y : α) : sym2.mk x y = sym2.mk y x :=
quot.sound (sym2_rel.swap x y)

def sym2.induce {α β : Type u} (f : α → β) : sym2 α → sym2 β :=
λ z, quot.rec_on z (λ x, sym2.mk (f x.1) (f x.2))
begin
  intros, cases p, simp, simp, apply quot.sound, apply sym2_rel.swap,
end

@[simp]
def sym2.induce.id {α : Type u} : sym2.induce (@id α) = id :=
begin
  ext, induction x, cases x, apply quot.sound, exact sym2_rel.refl x_fst x_snd, refl,
end

def sym2.induce.functorial {α β γ: Type u} {g : β → γ} {f : α → β} : sym2.induce (g ∘ f) = sym2.induce g ∘ sym2.induce f :=
begin
  ext, induction x, cases x, rw comp_app, refl, refl,
end

instance sym2.is_diag.decidable_pred (α : Type u) [decidable_eq α] : decidable_pred (@sym2.is_diag α) :=
begin
  intro x,
  induction x,
  solve_by_elim,
  cases x_p,
  simp only [],
  apply subsingleton.elim,
end

def sym2.mem {α : Type u} (x : α) (z : sym2 α) : Prop :=
begin
  induction z, exact x = z.1 ∨ x = z.2,
  simp only [eq_rec_constant, eq_iff_iff],
  induction z_p, simp,
  simp only [],
  split,
  intro h, cases h, right, exact h, left, exact h,
  intro h, cases h, right, exact h, left, exact h,
end

instance {α : Type u} : has_mem α (sym2 α) := ⟨sym2.mem⟩

lemma sym2.mk_mem {α : Type u} (x y : α) : x ∈ sym2.mk x y :=
begin
  dsimp [has_mem.mem, sym2.mem, sym2.mk, quot.rec],
  left, refl,
end

lemma sym2.eq {α : Type u} {x y z w : α}
: sym2.mk x y = sym2.mk z w → (x = z ∧ y = w) ∨ (x = w ∧ y = z) :=
begin
  intro h,
  
  sorry,
  
end

end sym2
