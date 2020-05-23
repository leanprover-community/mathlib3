import complexity_class_defn


open complexity
namespace complexity.class
-- 2.1 P


def P : complexity_class :=
begin 
refine {problems := _},
intro L, cases L,
exact ∃ (d : ℕ) (M : algorithm L_domain bool), M.eval = L_problem ∧ time_bound M (λ n, n^d),
end


-- 2.2 NP and coNP
-- 2.2.1 NP-complete
-- 2.3 PH
-- 2.4 PSPACE
-- 2.5 EXP
-- 2.6 AC0
-- 2.7 NC
-- 2.8 L
-- 2.9 P/poly
-- 2.10 BPP
-- 2.11 MA
-- 2.12 AM
-- 2.13 SZK
-- 2.14 BQP
-- 2.15 #P
-- 2.16 PP