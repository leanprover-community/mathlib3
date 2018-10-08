import tactic.fin_cases


example (f : ℕ → Prop) (p : fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val :=
begin
  fin_cases *,
  all_goals { assumption }
end

example (x2 : fin 2) (x3 : fin 3) (n : nat) (y : fin n) : x2.val * x3.val = x3.val * x2.val :=
begin
  fin_cases x2;
  fin_cases x3,
  success_if_fail { fin_cases * },
  success_if_fail { fin_cases y },
  all_goals { simp },
end
