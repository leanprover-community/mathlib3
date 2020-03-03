import tactic.rw_hint
import measure_theory.measurable_space
import measure_theory.integration

/-!
In this file, I've copied and pasted a few lemmas from `measure_theory/`,
and imagined writing the proofs but forgetting the names of the lemmas
that I want to use in rewriting.
We verify that `rw_hint` can identify the lemmas, without *too* many false negatives,
-/

open set lattice encodable measure_theory

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
variables [measurable_space α] [measurable_space β]

-- From measure_theory/measurable_space.lean
lemma test.is_measurable_range_inr : is_measurable (range sum.inr : set (α ⊕ β)) :=
begin
--  rw_hint,
 (do s ← tactic.rw_hint_target,
     guard $ s.length = 4,
     guard $ ("rw ←image_univ", "is_measurable (sum.inr '' univ)") ∈ s),
 rw ←image_univ,
 exact is_measurable_inr_image is_measurable.univ
end.

open measure_theory.simple_func
local infixr ` →ₛ `:25 := simple_func

-- From measure_theory/integration.lean
lemma test.pair_preimage_singleton (f : α →ₛ β) (g : α →ₛ γ) (b : β) (c : γ) :
  (pair f g) ⁻¹' {(b, c)} = (f ⁻¹' {b}) ∩ (g ⁻¹' {c}) :=
begin
  -- Imagine we want to rewrite `{(b, c)}` as `set.prod {b} {c}`,
  -- but can't remember that this lemma is called `prod_singleton_singleton`.
  -- We use `conv { to_lhs, congr, skip, ... }` to focus on the subexpression we plan
  -- to rewrite, then call `rw_hint with set.prod _ _`.
  -- This uniquely identifies the relevant lemma.
  conv {
    to_lhs, congr, skip,
    -- rw_hint with set.prod _ _,
    --  prints:
    -- Try this: rw ←prod_singleton_singleton -- set.prod {b} {c}
    (do s ← conv.lhs >>= (λ e, tactic.rw_hint e tt ```(set.prod _ _)),
      guard $ s = [("rw ←prod_singleton_singleton", "set.prod {b} {c}")]),

    -- If we just call `rw_hint`, it gives some spurious suggestions,
    -- but only 8 suggestions in total, including the one we were looking for.

    -- rw_hint,
    --  prints:
    -- Try this: rw ←image_singleton -- prod.mk b '' {c}
    -- Try this: rw ←prod_singleton_singleton -- set.prod {b} {c}
    -- Try this: rw ←set_compr_eq_eq_singleton -- {b_1 : β × γ | b_1 = (b, c)}
    -- Try this: rw singleton_def -- insert (b, c) ∅
    -- Try this: rw ←finset.coe_singleton -- ↑(finset.singleton (b, c))
    -- Try this: rw ←set_of_eq_eq_singleton -- {n : β × γ | n = (b, c)}
    -- Try this: rw ←pair_eq_singleton -- {(b, c), (b, c)}
    -- Try this: rw ←pure_def -- pure (b, c)
    (do s ← conv.lhs >>= (λ e, tactic.rw_hint e tt),
        guard $ s.length ≤ 10,
        guard $ ("rw ←prod_singleton_singleton", "set.prod {b} {c}") ∈ s),
  },
  rw ←prod_singleton_singleton,
  exact pair_preimage _ _ _ _
end.
