import tactic.trunc_cases
import tactic.interactive
import tactic.congr
import data.quot

example (t : trunc ℕ) : punit :=
begin
  trunc_cases t,
  exact (),
  -- no more goals, because `trunc_cases` used the correct `trunc.rec_on_subsingleton` recursor
end

example (t : trunc ℕ) : ℕ :=
begin
  trunc_cases t,
  guard_hyp t : ℕ, -- verify that the new hypothesis is still called `t`.
  exact 0,
  -- verify that we don't even need to use `simp`,
  -- because `trunc_cases` has already removed the `eq.rec`.
  refl,
end

example {α : Type} [subsingleton α] (I : trunc (has_zero α)) : α :=
begin
  trunc_cases I,
  exact 0,
end

/-- A mock typeclass, set up so that it's possible to extract data from `trunc (has_unit α)`. -/
class has_unit (α : Type) [has_one α] :=
(unit : α)
(unit_eq_one : unit = 1)

def u {α : Type} [has_one α] [has_unit α] : α := has_unit.unit
attribute [simp] has_unit.unit_eq_one

example {α : Type} [has_one α] (I : trunc (has_unit α)) : α :=
begin
  trunc_cases I,
  exact u, -- Verify that the typeclass is immediately available
  -- Verify that there's no `eq.rec` in the goal.
  (do tgt ← tactic.target, eq_rec ← tactic.mk_const `eq.rec, guard $ ¬ eq_rec.occurs tgt),
  simp [u],
end

universes v w z

/-- Transport through a product is given by individually transporting each component. -/
-- It's a pity that this is no good as a `simp` lemma.
-- (It seems the unification problem with `λ a, W a × Z a` is too hard.)
-- (One could write a tactic to syntactically analyse `eq.rec` expressions
-- and simplify more of them!)
lemma eq_rec_prod {α : Sort v} (W : α → Type w) (Z : α → Type z) {a b : α} (p : W a × Z a) (h : a = b) :
  @eq.rec α a (λ a, W a × Z a) p b h = (@eq.rec α a W p.1 b h, @eq.rec α a Z p.2 b h) :=
begin
  cases h,
  simp only [prod.mk.eta],
end

-- This time, we make a goal that (quite artificially) depends on the `trunc`.
example {α : Type} [has_one α] (I : trunc (has_unit α)) : α × plift (I = I) :=
begin
  -- This time `trunc_cases` has no choice but to use `trunc.rec_on`.
  trunc_cases I,
  { exact ⟨u, plift.up rfl⟩, },
  { -- And so we get an `eq.rec` in the invariance goal.
    -- Since `simp` can't handle it because of the unification problem,
    -- for now we have to handle it by hand.
    convert eq_rec_prod (λ I, α) (λ I, plift (I = I)) _ _,
    { simp [u], },
    { ext, } }
end
