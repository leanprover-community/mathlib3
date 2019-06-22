import tactic.rewrite_search.core
import tactic.rewrite_search.metric.edit_distance.core

open tactic.rewrite_search
open tactic.rewrite_search.edit_distance
open tactic.rewrite_search.metric.edit_distance

namespace tactic.rewrite_search.metric.edit_distance.weight.cm

def cm_of_side (l : list token) (s : side) : list dnum :=
  let (tot, vec) := l.foldl (
    λ n : ℕ × list ℕ, λ t : token, let v := t.freq.get s in (n.1 + v, n.2.concat v)
  ) (0, []) in
  vec.map (λ n : ℕ, dnum.of_nat (n * 1000 / tot))

def compare_component (a b : dnum) : dnum := 1000 + dnum.diff a b

def compare : list dnum → list dnum → list dnum
  | (a :: l1) (b :: l2) := compare_component a b :: compare l1 l2
  | _ _ := []

meta def calculate_weights {α δ : Type} (g : search_state α ed_state ed_partial δ) : tactic (table dnum) :=
  let tl := g.tokens.to_list in
  return $ table.from_list $ compare (cm_of_side tl side.L) (cm_of_side tl side.R)

end tactic.rewrite_search.metric.edit_distance.weight.cm

namespace tactic.rewrite_search.metric
open tactic.rewrite_search.metric.edit_distance.weight.cm

meta def weight.cm : ed_weight_constructor :=
  λ α δ, ⟨init_result.pure (), λ g, calculate_weights g⟩

end tactic.rewrite_search.metric
