/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.equiv_rw

-- Uncomment this line to observe the steps of constructing appropriate equivalences.
-- set_option trace.equiv_rw_type true

-- Rewriting a hypothesis along an equivalence.
example {α β : Type} (e : α ≃ β)
  (f : α → ℕ) (h : ∀ b : β, f (e.symm b) = 0) (i : α) : f i = 0 :=
begin
  equiv_rw e at i,
  apply h,
end

-- Check that dependent hypotheses are reverted and reintroduced.
example {α β : Type} (e : α ≃ β) (Z : α → Type) (f : Π a, Z a → ℕ)
  (h : ∀ (b : β) (x : Z (e.symm b)), f (e.symm b) x = 0)
  (i : α) (x : Z i) : f i x = 0 :=
begin
  equiv_rw e at i,
  guard_hyp i := β,
  guard_target f (e.symm i) x = 0,
  guard_hyp x := Z ((e.symm) i),
  exact h i x,
end

-- Rewriting the goal along an equivalence.
example {α β : Type} (e : α ≃ β) (b : β) : α :=
begin
  equiv_rw e,
  exact b,
end

-- Fail if the equivalence can't be used.
example {α β γ : Type} (e : β ≃ γ) (a : α) : α :=
begin
  success_if_fail { equiv_rw e at a },
  success_if_fail { equiv_rw e },
  exact a,
end

example {α β : Type} (u : unique α) (e : α ≃ β) : β :=
begin
  equiv_rw e at u,
  apply inhabited.default,
end

-- We can rewrite the goal under functors.
example {α β : Type} (e : α ≃ β) (b : β) : option α :=
begin
  equiv_rw e,
  exact some b,
end

-- We can rewrite hypotheses under functors.
example {α β : Type} (e : α ≃ β) (b : option α) : option β :=
begin
  equiv_rw e at b,
  exact b,
end

-- We can rewrite hypotheses under compositions of functors.
example {α β : Type} (e : α ≃ β) (b : list (list α)) : list β :=
begin
  equiv_rw e at b,
  exact b.join,
end


-- Check that we can rewrite in the target position of function types.
example {α β γ : Type} (e : α ≃ β) (f : γ → β) : γ → α :=
begin
  equiv_rw e,
  exact f,
end

-- Check that we can rewrite in the source position of function types.
example {α β γ : Type} (e : α ≃ β) (f : β → γ) : α → γ :=
begin
  equiv_rw e,
  exact f,
end

-- Rewriting under multiple functors.
example {α β : Type} (e : α ≃ β) (b : β) : list (option α) :=
begin
  equiv_rw e,
  exact [none, some b],
end

-- Rewriting under multiple functors, including functions.
example {α β γ : Type} (e : α ≃ β) (b : β) : γ → list (option α) :=
begin
  equiv_rw e,
  exact (λ g, [none, some b]),
end

-- Rewriting in multiple positions.
example {α β : Type*} [has_add β] (e : α ≃ β) : α → α :=
begin
  have : (α → α) ≃ _, {
    apply equiv.arrow_congr,
    apply e,
    apply e,
  },
  equiv_rw e,
  exact (@id β),
end

-- Rewriting in multiple positions.
example {α β : Type} [has_add β] (e : α ≃ β) : β → α → α :=
begin
  equiv_rw e,
  exact (+),
end

-- Rewriting in multiple positions.
example {α β : Type} [has_add β] (e : α ≃ β) : α → α → α :=
begin
  equiv_rw e,
  exact (+),
end

example {α β γ : Type} (e : α ≃ β) (s : β ⊕ γ) : α ⊕ γ :=
begin
  equiv_rw e,
  exact s,
end

example {α β γ : Type} (e : α ≃ β) (s : β ⊕ γ) : (α ⊕ γ) × (γ ⊕ α) :=
begin
  equiv_rw e,
  exact (s, s.swap),
end

example {α β γ : Type} (e : α ≃ β) (s : α ⊕ γ) : (β ⊕ γ) × (γ ⊕ β) :=
begin
  equiv_rw e at s,
  exact (s, s.swap),
end

example {α β γ : Type} (e : α ≃ β) (s : (α ⊕ γ) × β) : (β ⊕ γ) :=
begin
  equiv_rw e at s,
  exact s.1,
end

example {α β : Type} (e : α ≃ β) (b : β) : α × (ℕ ⊕ ℕ) :=
begin
  have e' : α × (ℕ ⊕ ℕ) ≃ _ := by equiv_rw_type e,
  apply e'.inv_fun,
  exact (b, sum.inl 0)
end

example {α β : Type} (e : α ≃ β) (P : α → Prop) (h : { a // P a }) : β :=
begin
  equiv_rw e at h,
  exact h.val,
end

example {α β : Type} (e : α ≃ β) (P : α → Prop) (h : ∀ a, P a) (b : β) : { a // P a } :=
begin
  equiv_rw e,
  use b,
  apply h,
end


example {α β : Type} (e : α ≃ β) (P : α → Prop) (h : ∀ a : α, P a) (b : β) : P (e.symm b) :=
begin
  equiv_rw e.symm at b,
  exact h b,
end

example {α β : Type} (e : α ≃ β) (P : α → Sort*) (h : Π a : α, P a) (b : β) : P (e.symm b) :=
begin
  -- this is a bit perverse, as `equiv_rw e.symm at b` is more natural,
  -- but this tests rewriting in the argument of a dependent function
  equiv_rw e at h,
  exact h _,
end

-- a poor example, rewriting in the base of a dependent pair
example {α β : Type} (P : α → Type) (h : Σ a, P a) (e : α ≃ β) : β :=
begin
  equiv_rw e at h,
  exact h.1
end

-- rewriting in the argument of a dependent function can't be done in one step
example {α β γ : Type} (e : α ≃ β) (P : α → Type*) (h : Π a : α, (P a) × (option α)) (b : β) : option β :=
begin
  equiv_rw e at h,
  have t := h b,
  equiv_rw e at t,
  exact t.2,
end

/-- Transport through trivial families is the identity. -/
-- TODO find a home in mathlib!
@[simp]
lemma eq_rec_constant {α : Sort*} {a a' : α} {β : Sort*}
  (y : β) (h : a = a') :
  (@eq.rec α a (λ a, β) y a' h) = y :=
begin
  cases h,
  refl,
end

-- TODO move to data/equiv/basic
@[simp]
lemma to_fun_as_coe {α β : Sort*} (e : α ≃ β) (a : α) : e.to_fun a = e a := rfl

-- Demonstrate using `equiv_rw` to build new instances of `equiv_functor`
-- (which isn't yet in this PR, so we only define the fields without assembling them)
-- Observe that the next three declarations could easily be implemented by a tactic.

attribute [ext] semigroup

def semigroup.map {α β : Type} (e : α ≃ β) : semigroup α → semigroup β :=
begin
  intro S, fconstructor,
  -- transport data fields using `equiv_rw`
  { have mul := S.mul, equiv_rw e at mul, exact mul, },
  -- transport axioms by simplifying, and applying the original axiom
  { intros, dsimp, simp, apply S.mul_assoc, }
end

-- Note this is purely formal, and will be provided by `equiv_functor` automatically.
@[simps]
def semigroup.map_equiv {α β : Type} (e : α ≃ β) : semigroup α ≃ semigroup β :=
{ to_fun := semigroup.map e,
  inv_fun := semigroup.map e.symm,
  left_inv := by { intro x, funext, ext, dsimp [semigroup.map], simp, },
  right_inv := by { intro x, funext, ext, dsimp [semigroup.map], simp, }, }

lemma semigroup.map_id (α : Type) : semigroup.map_equiv (equiv.refl α) = equiv.refl (semigroup α) :=
by { ext, refl, }

lemma semigroup.map_comp {α β γ : Type} (e : α ≃ β) (f : β ≃ γ) :
  (semigroup.map_equiv e).trans (semigroup.map_equiv f) = semigroup.map_equiv (e.trans f) :=
by { ext, dsimp [semigroup.map, semigroup.map_equiv], simp, }

-- Now we do `monoid`, to try out a structure with constants.
attribute [ext] monoid

def monoid.map {α β : Type} (e : α ≃ β) : monoid α → monoid β :=
begin
  intro S, fconstructor,
  { have mul := S.mul, equiv_rw e at mul, exact mul, },
  { /-
    The next line also works here,
    but this pattern doesn't work for axioms involving constants, e.g. one_mul:
    -/
    -- have mul_assoc := S.mul_assoc, equiv_rw e at mul_assoc, intros, dsimp, simp, apply mul_assoc,
    intros,
    apply e.symm.injective,
    dsimp [(*)], simp,
    have mul_assoc := S.mul_assoc,
    equiv_rw e at mul_assoc,
    apply mul_assoc, },
  { have one := S.one, equiv_rw e at one, exact one, },
  { intros,
    apply e.symm.injective,
    dsimp [(*)], simp,
    have one_mul := S.one_mul,
    equiv_rw e at one_mul,
    apply one_mul, },
  { intros,
    apply e.symm.injective,
    dsimp [(*)], simp,
    have mul_one := S.mul_one,
    equiv_rw e at mul_one,
    apply mul_one, },
end
