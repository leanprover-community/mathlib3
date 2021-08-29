/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.equiv_rw
import control.equiv_functor.instances -- these make equiv_rw more powerful!

-- Uncomment this line to observe the steps of constructing appropriate equivalences.
-- set_option trace.equiv_rw_type true

import tactic.equiv_rw

-- This fails if we use `occurs` rather than `kdepends_on` in `equiv_rw_type`.
instance : equiv_functor set :=
{ map := λ α β e s, by { equiv_rw e.symm, assumption, } }

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
  guard_hyp i : β,
  guard_target f (e.symm i) x = 0,
  guard_hyp x : Z ((e.symm) i),
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

-- Verify that `equiv_rw` will rewrite under `equiv_functor` instances.
example {α β : Type} (u : unique α) (e : α ≃ β) : β :=
begin
  equiv_rw e at u,
  apply inhabited.default,
end

example {α β : Type} (p : equiv.perm α) (e : α ≃ β) : equiv.perm β :=
begin
  equiv_rw e at p,
  exact p,
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
    apply e, },
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
  success_if_fail { equiv_rw e at s {max_depth := 4} },
  equiv_rw e at s,
  exact s.1,
end

-- Test generating the actual equivalence using `equiv_rw_type`.
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
example {α β γ : Type} (e : α ≃ β) (P : α → Type*) (h : Π a : α, (P a) × (option α)) (b : β) :
  option β :=
begin
  equiv_rw e at h,
  have t := h b,
  equiv_rw e at t,
  exact t.2,
end

-- Demonstrate using `equiv_rw` to build new instances of `equiv_functor`
-- Observe that the next three declarations could easily be implemented by a tactic.

-- This has been automated in the `transport` branch,
-- so we won't attempt to write a deriver handler until we join with that.
def semigroup.map {α β : Type} (e : α ≃ β) : semigroup α → semigroup β :=
begin
  intro S,
  refine_struct { .. },
  -- transport data fields using `equiv_rw`
  { have mul := S.mul,
    equiv_rw e at mul,
    -- This `equiv_rw` performs the following steps:
    -- have e' := (equiv.arrow_congr' e (equiv.arrow_congr' e e)),
    -- have h := (e'.symm_apply_apply mul).symm,
    -- revert h,
    -- generalize : (e' mul) = mul',
    -- intro h,
    -- clear_dependent mul,
    -- rename mul' mul,
    exact mul, },
  -- transport axioms by simplifying, and applying the original axiom
  { intros, dsimp, simp, apply S.mul_assoc, }
end

example {α β : Type} (e : α ≃ β) (S : semigroup α) :
  (semigroup.map e S).mul =
    (equiv.arrow_congr' e (equiv.arrow_congr' e e)) has_mul.mul :=
rfl

example {α β : Type} (e : α ≃ β) (S : semigroup α) (x y : β) :
begin
  haveI := semigroup.map e S,
  exact x * y = e (e.symm x * e.symm y)
end :=
rfl

attribute [ext] semigroup

lemma semigroup.id_map (α : Type) : semigroup.map (equiv.refl α) = id :=
by { ext, refl, }

lemma semigroup.map_map {α β γ : Type} (e : α ≃ β) (f : β ≃ γ) :
  semigroup.map (e.trans f) = (semigroup.map f) ∘ (semigroup.map e) :=
by { ext, dsimp [semigroup.map], simp, }

-- TODO (after joining the `transport` branch) create a derive handler for this
instance : equiv_functor semigroup :=
{ map := λ α β e, semigroup.map e,
  map_refl' := semigroup.id_map,
  map_trans' := λ α β γ e f, semigroup.map_map e f, }

-- Verify that we can now use `equiv_rw` under `semigroup`:
example {α : Type} [I : semigroup α] {β : Type} (e : α ≃ β) : semigroup β :=
begin
  equiv_rw e at I,
  exact I,
end

-- Now we do `monoid`, to try out a structure with constants.

-- The constructions and proofs here are written as uniformly as possible.
-- This example is the blueprint for the `transport` tactic.

mk_simp_attribute transport_simps "simps useful inside `transport`"

attribute [transport_simps]
  eq_rec_constant
  cast_eq
  equiv.to_fun_as_coe
  equiv.arrow_congr'_apply
  equiv.symm_apply_apply
  equiv.apply_eq_iff_eq_symm_apply

def monoid.map {α β : Type} (e : α ≃ β) (S : monoid α) : monoid β :=
begin
  refine_struct { .. },
  { have mul := S.mul, equiv_rw e at mul, exact mul, },
  { try { unfold_projs },
    simp only with transport_simps,
    have mul_assoc := S.mul_assoc,
    equiv_rw e at mul_assoc,
    solve_by_elim, },
  { have one := S.one, equiv_rw e at one, exact one, },
  { try { unfold_projs },
    simp only with transport_simps,
    have one_mul := S.one_mul,
    equiv_rw e at one_mul,
    solve_by_elim, },
  { try { unfold_projs },
    simp only with transport_simps,
    have mul_one := S.mul_one,
    equiv_rw e at mul_one,
    solve_by_elim, },
  { have npow := S.npow, equiv_rw e at npow, exact npow, },
  { try { unfold_projs },
    simp only with transport_simps,
    have npow_zero' := S.npow_zero',
    equiv_rw e at npow_zero',
    solve_by_elim, },
  { try { unfold_projs },
    simp only with transport_simps,
    have npow_succ' := S.npow_succ',
    equiv_rw e at npow_succ',
    solve_by_elim, },
end

example {α β : Type} (e : α ≃ β) (S : monoid α) :
  (monoid.map e S).mul =
    (equiv.arrow_congr' e (equiv.arrow_congr' e e)) has_mul.mul :=
rfl

example {α β : Type} (e : α ≃ β) (S : monoid α) (x y : β) :
begin
  haveI := monoid.map e S,
  exact x * y = e (e.symm x * e.symm y)
end :=
rfl

example {α β : Type} (e : α ≃ β) (S : monoid α) :
begin
  haveI := monoid.map e S,
  exact (1 : β) = e (1 : α)
end :=
rfl

example
  {α : Type} {β : Type}
  (m : α → α → α)
  (e : α ≃ β) :
  β → β → β :=
begin
  equiv_rw e at m,
  exact m,
end

-- This used to fail because metavariables were getting stuck!
example
  {α : Type} {β : Type 2}
  (m : α → α → α)
  (e : α ≃ β) :
  β → β → β :=
begin
  equiv_rw e at m,
  exact m,
end
