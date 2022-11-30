import tactic.print_sorry

axiom my_sorry : false -- we avoid using noisy code in the test folder, so we use an axiom instead
def foo1 : false := my_sorry
def foo2 : false ∧ false := ⟨my_sorry, foo1⟩
def foo3 : false ∧ false := ⟨foo2.1, my_sorry⟩
def foo4 : true := trivial
def foo5 : true ∧ false := ⟨foo4, foo3.2⟩

meta def metafoo : ℕ → empty := metafoo

open tactic

#eval show tactic unit, from do
  env ← get_env,
  data ← find_all_exprs env (λ e, e.const_name = `my_sorry) (λ _, ff) `foo5,
  guard $ data.map (λ x, x.1) = [`foo5, `foo3, `foo2, `foo1],
  guard $ data.map (λ x, x.2.1) = [ff, tt, tt, tt],
  guard $ data.map (λ x, x.2.2.to_list) = [[`foo3], [`foo2], [`foo1], []],
  -- make sure it doesn't loop on self-referencing meta expressions
  find_all_exprs env (λ e, e.const_name = `my_sorry) (λ _, ff) `metafoo,
  skip
