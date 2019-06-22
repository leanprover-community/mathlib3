import tactic.rewrite_search

open tactic.rewrite_search.discovery




namespace tactic.rewrite_search.testing

local attribute [instance] classical.prop_decidable

example {A B C : Prop} : ((B → C) → (¬(A → C) ∧ ¬(A ∨ B))) = (B ∧ ¬C) :=
  by rewrite_search_using! []

end tactic.rewrite_search.testing




namespace tactic.rewrite_search.testing

axiom foo' : [6] = [7]
axiom bar' : [[5],[5]] = [[6],[6]]

example : [[7],[6]] = [[5],[5]] :=
begin
 rewrite_search_with [←foo', bar'],
end

axiom foo''  : [7] = [8]
axiom foo''' : [8] = [7]

run_cmd (rewrite_list_from_lemma `(foo'')).mmap (λ rw, is_promising_rewrite rw [`([[8],[6]])]) >>= tactic.trace
run_cmd (rewrite_list_from_lemma `(foo''')).mmap (λ rw, is_promising_rewrite rw [`([[8],[6]])]) >>= tactic.trace

def my_test : [[7],[6]] = [[5],[5]] :=
begin
 success_if_fail { rewrite_search_with [ bar'] {help_me := ff} },

 rewrite_search_with! [ bar'] {help_me := tt}
end

end tactic.rewrite_search.testing
