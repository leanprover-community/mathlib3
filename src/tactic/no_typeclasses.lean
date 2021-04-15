/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.binder_matching

open interactive
open lean

namespace expr

meta def modify_binder_info (f : binder_info → binder_info) : expr → expr
| (local_const u p bi type) := local_const u p (f bi) type
| e := e

end expr

namespace tactic

meta def change_binder_info (f : binder_info → binder_info) (e : expr) : tactic expr := do
  t ← infer_type e,
  (binders, _) ← open_pis t,
  let binders := binders.map $ λ b, b.modify_binder_info f,
  pure $ (e.app_of_list binders).lambdas binders

meta def no_typeclasses : expr → tactic expr :=
change_binder_info $ λ bi,
  match bi with
  | binder_info.inst_implicit := binder_info.implicit
  | _ := bi
  end

meta def interactive.no_typeclasses (e : parse parser.pexpr) : tactic unit :=
to_expr e >>= no_typeclasses >>= exact

end tactic

/-
Testcase
-/

class testclass (α : Sort*) :=
(stuff : α → true)

def test {α} [testclass α] (a : α) : true :=
testclass.stuff a

example : true :=
begin
  have := by no_typeclasses @test,
  /-
  this : ∀ {α : Sort ?} {_inst_1 : testclass α}, α → true
  ⊢ true
  -/
  trivial
end
