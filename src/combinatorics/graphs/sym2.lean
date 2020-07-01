/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/

import tactic
open function

namespace sym2
universe u
variables {α : Type u}

inductive rel (α : Type u) : (α × α) → (α × α) → Prop
| refl (x y : α) : rel (x, y) (x, y)
| swap (x y : α) : rel (x, y) (y, x)

attribute [refl] rel.refl

@[symm] lemma rel.symm {x y : α × α} : rel α x y → rel α y x :=
begin
  tidy, cases a, exact a, apply rel.swap,
end

@[trans] lemma rel.trans {x y z : α × α} : rel α x y → rel α y z → rel α x z :=
begin
  tidy, cases_matching* rel _ _ _; apply rel.refl <|> apply rel.swap,
end

instance rel.setoid (α : Type u) : setoid (α × α) :=
begin
  use rel α, tidy, apply rel.trans a a_1,
end

-- The symmetric square is the cartesian product α × α modulo `swap`.
@[reducible]
def sym2 (α : Type u) [h : setoid (α × α)] := quotient h
--def sym2 (α : Type u) := quotient (rel.setoid α)

lemma eq_swap {a b : α} : ⟦(a, b)⟧ = ⟦(b, a)⟧ :=
by { rw quotient.eq, apply rel.swap }

lemma other_unique (a b c : α) : ⟦(a, b)⟧ = ⟦(a, c)⟧ ↔ b = c :=
begin
  split,
  intro h, rw quotient.eq at h, cases h; refl,
  intro h, apply congr_arg _ h,
end

-- A type is naturally included in the diagonal of the cartesian
-- square, and this is the quotient of that.
def incl (x : α) : sym2 α := ⟦(x, x)⟧

def is_diag (x : sym2 α) : Prop :=
quotient.rec_on x (λ y, y.1 = y.2) (begin tidy, cases p; refl, cases p; refl, end)

lemma diag_to_eq (x y : α) (h : is_diag ⟦(x, y)⟧) : x = y :=
by tidy

def induce {α β : Type u} (f : α → β) : sym2 α → sym2 β :=
λ z, quotient.rec_on z (λ x, ⟦(f x.1, f x.2)⟧)
begin
  intros, rw [eq_rec_constant, quotient.eq],
  cases p, refl, apply rel.swap,
end

@[simp]
def induce.id : sym2.induce (@id α) = id :=
by tidy

def induce.functorial {α β γ: Type u} {g : β → γ} {f : α → β} : sym2.induce (g ∘ f) = sym2.induce g ∘ sym2.induce f :=
by tidy

instance is_diag.decidable_pred (α : Type u) [decidable_eq α] : decidable_pred (@is_diag α) :=
begin
  intro x,
  induction x,
  solve_by_elim,
  cases x_p,
  simp only [],
  apply subsingleton.elim,
end

def mem (x : α) (z : sym2 α) : Prop :=
∃ (y : α), z = ⟦(x, y)⟧

def mk_has_mem (x y : α) : mem x ⟦(x, y)⟧ :=
⟨y, rfl⟩

def trunc_mem (x : α) (z : sym2 α) : Type u :=
trunc {y : α // z = ⟦(x, y)⟧}

def mk_has_trunc_mem (x y : α) : trunc_mem x ⟦(x, y)⟧ :=
quot.mk _ ⟨y, rfl⟩

def from_other {a : α} {z : sym2 α} (h : trunc_mem a z) : mem a z :=
trunc.rec_on h (λ x, ⟨x.val, x.property⟩) (λ _ _, rfl)

instance {a : α} {z : sym2 α} : has_lift (trunc_mem a z) (mem a z) := ⟨from_other⟩

lemma eq {x y z w : α} (h : ⟦(x, y)⟧ = ⟦(z, w)⟧):
(x = z ∧ y = w) ∨ (x = w ∧ y = z) :=
begin
  rw quotient.eq at h,
  cases h; tidy,
end

lemma other {a : α} {p : sym2 α} (h : trunc_mem a p) : α :=
trunc.rec_on h subtype.val $ λ ⟨x, _⟩ ⟨y, _⟩,
begin
  convert (other_unique a x y).mp (by cc),
  simp,
end

lemma other_spec (a : α) (z : sym2 α) (h : trunc_mem a z) : ⟦(a, other h)⟧ = z :=
by { induction h, cases h, dunfold other, tidy, }

noncomputable
lemma mem_other {a : α} {z : sym2 α} (h : mem a z) : α :=
classical.some h

lemma mem_other_spec (a : α) (z : sym2 α) (h : mem a z) : ⟦(a, mem_other h)⟧ = z :=
begin
  dunfold mem_other,
  exact (classical.some_spec h).symm,
end

lemma other_is_mem_other {a : α} {z : sym2 α} (h : trunc_mem a z) (h' : mem a z) :
other h = mem_other h' :=
begin
  rw ←other_unique a,
  rw other_spec,
  rw mem_other_spec,
end

lemma is_one_of {a b c : α} (h : mem a ⟦(b, c)⟧) : a = b ∨ a = c :=
begin
  cases h,
  have p := eq h_h,
  tidy,
end


--
-- Relations
--

section relations
variables {r : α → α → Prop}

def in_rel (sym : symmetric r) (z : sym2 α) : Prop :=
quotient.rec_on z (λ z, r z.1 z.2) begin
  intros z w p,
  cases p,
  simp,
  simp,
  split; apply sym,
end

@[simp]
lemma in_rel_prop {sym : symmetric r} {a b : α} : in_rel sym ⟦(a, b)⟧ ↔ r a b :=
by tidy

end relations

end sym2
