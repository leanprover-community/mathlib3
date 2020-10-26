/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/

import tactic.nth_rewrite

/-!
FIXME

Something incredibly lame is going on here.
We have two different inductive types with two elements floating around,
* `expr_lens.dir`, whose elements correspond to the "function" / "argument" dichotomy
* `side`, whose elements correspond to the LHS / RHS of an equation.
We want to have pairs indexed by these types, with convenient getter/setter methods,
and so have two completely isomorphic but separate structures `dir_pair` and `sided_pair`.

This is LAME!
-/

universe u

namespace tactic.rewrite_search

@[derive decidable_eq, derive inhabited]
inductive side
| L
| R

def side.other : side → side
| side.L := side.R
| side.R := side.L

def side.to_string : side → string
| side.L := "L"
| side.R := "R"

instance : has_to_string side := ⟨side.to_string⟩


@[derive decidable_eq]
structure sided_pair (α : Type u) :=
(l r : α)

namespace sided_pair

variables {α β : Type} (p : sided_pair α)

def get : side → α
| side.L := p.l
| side.R := p.r

def set : side → α → sided_pair α
| side.L v := ⟨v, p.r⟩
| side.R v := ⟨p.l, v⟩

def flip : sided_pair α := ⟨p.r, p.l⟩

def map (f : α → β) : sided_pair β := ⟨f p.l, f p.r⟩

def to_list : list α := [p.l, p.r]

def to_string [has_to_string α] (p : sided_pair α) : string :=
  to_string p.l ++ "-" ++ to_string p.r
instance has_to_string [has_to_string α] : has_to_string (sided_pair α) := ⟨to_string⟩

end sided_pair

structure dir_pair (α : Type u) :=
(l r : α)

namespace dir_pair
open expr_lens

variables {α β : Type} (p : dir_pair α)

def get : dir → α
| dir.F := p.l
| dir.A := p.r

def set : dir → α → dir_pair α
| dir.F v := ⟨v, p.r⟩
| dir.A v := ⟨p.l, v⟩

def flip : dir_pair α := ⟨p.r, p.l⟩

def map (f : α → β) : dir_pair β := ⟨f p.l, f p.r⟩

def to_list : list α := [p.l, p.r]

def to_string [has_to_string α] (p : dir_pair α) : string :=
  to_string p.l ++ "-" ++ to_string p.r
instance has_to_string [has_to_string α] : has_to_string (dir_pair α) := ⟨to_string⟩

end dir_pair

meta inductive how
| rewrite (rule_index : ℕ) (location : ℕ) (addr : option (list expr_lens.dir))
| defeq
| simp  -- TODO handle "explaining" me

meta def how.to_string : how → format
| (how.rewrite idx loc addr) := format!"rewrite {idx} {loc} {addr.iget.to_string}"
| how.defeq := "(defeq)"
| how.simp := "simp"

meta instance how.has_to_format : has_to_format how := ⟨how.to_string⟩

meta structure rewrite :=
(e   : expr)
(prf : tactic expr) -- we defer constructing the proofs until they are needed
(how : how)

meta structure core_cfg :=
(max_iterations     : ℕ := 500)
(optimal            : bool := tt)
(exhaustive         : bool := ff)
(trace              : bool := ff)
(trace_summary      : bool := ff)
(trace_rules        : bool := ff)
(explain            : bool := ff)
(explain_using_conv : bool := tt)

end tactic.rewrite_search

open tactic

namespace rw_equation

/-- Split an expression that is an equation or an iff into its rhs and lhs parts. -/
meta def split : expr → tactic (expr × expr)
| `(%%lhs = %%rhs) := return (lhs, rhs)
| `(%%lhs ↔ %%rhs) := return (lhs, rhs)
| _                := fail "target is not an equation or iff"

/-- The left hand side of an expression (fails if the expression is not an equation or iff). -/
meta def lhs (e : expr) : tactic expr := prod.fst <$> split e

/-- The right hand side of an expression (fails if the expression is not an equation or iff). -/
meta def rhs (e : expr) : tactic expr := prod.snd <$> split e

end rw_equation

/-- Returns true if expression is an equation or iff. -/
meta def is_acceptable_rewrite : expr → bool
| (expr.pi n bi d b) := is_acceptable_rewrite b
| `(%%a = %%b)       := tt
| `(%%a ↔ %%b)       := tt
| _                  := ff

/-- Returns true if the type of expression is an equation or iff. -/
meta def is_acceptable_lemma (r : expr) : tactic bool :=
  is_acceptable_rewrite <$> (infer_type r >>= whnf)

/-- Returns true if the type of expression is an equation or iff
and does not contain metavariables. -/
meta def is_acceptable_hyp (r : expr) : tactic bool :=
  do t ← infer_type r >>= whnf, return $ is_acceptable_rewrite t ∧ ¬t.has_meta_var
