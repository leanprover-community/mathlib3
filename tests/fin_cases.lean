import tactic.fin_cases

example (x2 : fin 2) (x3 : fin 3) (n : nat) (y : fin n) : x2.val * x3.val = x3.val * x2.val :=
begin
  fin_cases ; fin_cases,
  success_if_fail { fin_cases },
  all_goals { simp },
end
