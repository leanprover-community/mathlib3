/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Johan Commelin
-/
import tactic.wlog

section wlog

example {x y : ℕ} : true :=
begin
  suffices : false, trivial,
  wlog h : x ≤ y,
  { guard_hyp h : ¬x ≤ y,
    guard_hyp this : ∀ {x y : ℕ}, x ≤ y → false, -- `wlog` generalizes by default
    guard_target false,
    admit },
  { guard_hyp h : x ≤ y,
    guard_target false,
    admit },
end

example {x y : ℕ} : true :=
begin
  suffices : false, trivial,
  wlog h : x ≤ y generalizing x,
  { guard_hyp h : ¬x ≤ y,
    guard_hyp this : ∀ {x : ℕ}, x ≤ y → false, -- only `x` was generalized
    guard_target false,
    admit },
  { guard_hyp h : x ≤ y,
    guard_target false,
    admit },
end

example {x y z : ℕ} : true :=
begin
  suffices : false, trivial,
  wlog h : x ≤ y + z using H,
  { guard_hyp h : ¬ x ≤ y + z,
    guard_hyp H : ∀ {x y z : ℕ}, x ≤ y + z → false, -- wlog-claim is named `H` instead of `this`
    guard_target false,
    admit },
  { guard_hyp h : x ≤ y + z,
    guard_target false,
    admit },
end

end wlog
