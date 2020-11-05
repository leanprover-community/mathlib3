import tactic.lint

-- see Note [function coercion]

structure equiv (α β : Sort*) :=
(to_fun : α → β)
(inv_fun : β → α)

instance {α β} : has_coe_to_fun (equiv α β) :=
⟨λ _, α → β, equiv.to_fun⟩

structure sparkling_equiv (α β) extends equiv α β

instance {α β} : has_coe (sparkling_equiv α β) (equiv α β) :=
⟨sparkling_equiv.to_equiv⟩

-- should complain
open tactic
run_cmd do
decl ← get_decl ``sparkling_equiv,
res ← linter.has_coe_to_fun.test decl,
-- linter complains
guard res.is_some

instance {α β} : has_coe_to_fun (sparkling_equiv α β) :=
⟨λ _, α → β, λ f, f.to_equiv.to_fun⟩

-- prima!
run_cmd do
decl ← get_decl ``sparkling_equiv,
res ← linter.has_coe_to_fun.test decl,
-- linter doesn't complain
guard res.is_none




-- Test support for type-class parameters in the `has_coe_to_fun` instance.
namespace with_tc_param

structure equiv (α β : Sort*) :=
(to_fun : α → β)
(inv_fun : β → α)

instance {α β} [nonempty α] : has_coe_to_fun (equiv α β) :=
⟨λ _, α → β, equiv.to_fun⟩

structure sparkling_equiv (α β) [nonempty α] extends equiv α β

instance {α β} [nonempty α] : has_coe (sparkling_equiv α β) (equiv α β) :=
⟨sparkling_equiv.to_equiv⟩

-- should complain
open tactic
run_cmd do
decl ← get_decl ``sparkling_equiv,
res ← linter.has_coe_to_fun.test decl,
-- linter complains
guard res.is_some

end with_tc_param
