import tactic.rewrite_search

axiom foo : [0] = [1]
axiom bar1 : [1] = [2]
axiom bar2 : [2] = [3]
axiom bar3 : [3] = [4]
axiom bar4 : [4] = [5]
axiom bar5 : [5] = [6]
axiom bar6 : [6] = [7]
axiom baz : [4] = [0]

-- Obviously sub-optimal
example : [0] = [7] :=
begin
  -- erw [foo, bar1, bar2, bar3, bar4, bar5, bar6],
  rewrite_search_with [foo, bar1, bar2, bar3, bar4, bar5, bar6, baz]
    { optimal := ff, explain := tt },
end

example : [0] = [7] :=
begin
  /- `rewrite_search` says -/
  erw [foo, bar1, bar2, bar3, bar4, bar5, bar6]
end

-- Obviously optimal
example : [0] = [7] :=
begin
  rewrite_search_with [foo, bar1, bar2, bar3, bar4, bar5, bar6, baz]
    { optimal := tt,  explain := tt },
end

example : [0] = [7] :=
begin
  /- `rewrite_search` says -/
  erw [←baz, bar4, bar5, bar6]
end
