import algebra.big_operators.basic

open tactic

example (α : Type) : finset ℕ → α :=
begin
  (do
    e ← to_expr ``(λ s : finset ℕ, s.sum _), -- works, generating a `add_comm_monoid α` goal
    exact e),
  sorry,
  sorry
end

example (α : Type) : finset ℕ → α :=
begin
  (do
    tgt ← target,
    e ← to_expr ``(λ s : finset ℕ, s.sum _ : %%tgt), -- failed to synthesize type class instance for `add_comm_monoid α`
    exact e),
end

example (α : Type) : finset ℕ → α :=
begin
  (do
    let e : pexpr := ``(λ s : finset ℕ, s.sum _),
    tgt ← target,
    e ← to_expr e,
    infer_type e >>= unify tgt,
    exact e),
  sorry,
  sorry,
end


example : Σ {α : Type}, finset ℕ → α :=
begin
  split,
  -- We decide we want to sum some as-yet-undecided function over our finset:
  refine (λ s, s.sum _),
  -- The creates three new goals
  -- ⊢ Type
  -- s: finset ℕ
  -- ⊢ add_comm_monoid ?m_1
  -- s: finset ℕ
  -- ⊢ ℕ → ?m_1
  show ℕ → _, exact id,
  apply_instance,
end

example : Σ {α : Type}, finset ℕ → α :=
begin
  -- If I try the same thing using the `let α := _` trick to name the type,
  let α := _,
  refine ⟨α, _⟩,
  refine (λ s, s.sum _), -- FAILS
  -- "failed to synthesize type class instance for `add_comm_monoid α`"
  -- The problem here is that `refine` runs
  --- `to_expr ``(%%e : %%tgt) tt >>= exact`,
  -- and it is this `to_expr` that is failing,
  -- even though `to_expr` claims to create new goals for failed typeclass inference
end

example : Σ {α : Type}, finset ℕ → α :=
begin
  let α := _,
  refine ⟨α, _⟩,
  -- Doesn't work with `apply` either:
  apply (λ s, s.sum _), -- FAILS
  -- "invalid field notation, type is not of the form (C ...) where C is a constant
  -- s has type ?m_1"
end

example : Σ {α : Type}, finset ℕ → α :=
begin
  let α := _,
  refine ⟨α, _⟩,
  -- However `apply` with an extra type annotation gets us there:
  apply (λ s : finset ℕ, s.sum _),
  -- Here `apply` is happy to generate new goals for instances,
  -- but because it is doing the unification with the target *later*,
  -- it needs extra hints to work out what the argument `s` means in the binder.
  show ℕ → α, exact id,
  apply_instance,
end



setup_tactic_parser

namespace tactic

meta def equate_with_pattern : expr → expr → expr → tactic unit
| (expr.app f e) (expr.app f0 e0) (expr.app f1 e1) := do
  match e with
  | (expr.mvar _ _ _) := do
    el ← mk_app `eq [e0, e1],
    n ← get_unused_name "h",
    assert n el,
    interactive.rotate,
    get_local n >>= rewrite_target,
    equate_with_pattern f f0 f1
  | _ := do equate_with_pattern e e0 e1 *> equate_with_pattern f f0 f1
  end
| _ _ _ := skip

meta def refine' (e : pexpr) : tactic unit :=
do
  tgt ← target,
  e' ← to_expr e tt ff >>= infer_type,   --    <---  added the ascription `tt ff` to `to_expr`
  equate_with_pattern e' tgt e',
  unify e' tgt,  --  added unification, since I mistakenly removed it from the copied code
  apply e' >> skip --  `apply` not `exact`!

namespace interactive

meta def refine' (q : parse texpr) : tactic unit :=
tactic.refine' q

end interactive

end tactic

example : Σ (α : Type), finset ℕ → α :=
begin
  let α := _,
  refine ⟨α, _⟩,
  refine' λ s : finset ℕ, s.sum _,
  show ℕ → α, exact id,
  apply_instance,
end


example : Σ (α : Type), list ℕ → α :=
begin
  let α := _,
  refine ⟨α, λ L, (L.map _).sum⟩,
  show ℕ → α, exact id,
  apply_instance,
end
