import algebra.big_operators.basic

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
  e' ← to_expr e tt ff >>= infer_type,
  equate_with_pattern e' tgt e',
  unify e' tgt,
  apply e' >> skip

namespace interactive

meta def refine' (q : parse texpr) : tactic unit :=
tactic.refine' q

end interactive

end tactic

example (α : Type*) : finset ℕ → α :=
begin
  refine' (λ s : finset ℕ, s.sum _),  -- don't know how to get rid of the type annotation  `s : finset ℕ`
/-
2 goals
α: Type ?
s: finset ℕ
⊢ add_comm_monoid α

α: Type ?
s: finset ℕ
⊢ ℕ → α
-/
end

example : Σ (α : Type), finset ℕ → α :=
begin
  let α := _,
  refine ⟨α, _⟩,
  refine' λ s : finset ℕ, s.sum _,
  show ℕ → α, exact id,
  apply_instance,
end
