/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/

import tactic.nth_rewrite

/-!
# Types used in rewrite search.
-/

declare_trace rewrite_search

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

def side.to_xhs : side → string
| side.L := "lhs"
| side.R := "rhs"

instance : has_to_string side := ⟨side.to_string⟩

meta inductive how
| rewrite (rule_index : ℕ) (location : ℕ) (addr : option (list expr_lens.dir))

meta def how.to_string : how → format
| (how.rewrite idx loc addr) := format!"rewrite {idx} {loc} {addr.iget.to_string}"

meta instance how.has_to_format : has_to_format how := ⟨how.to_string⟩

meta structure rewrite :=
(e   : expr)
(prf : tactic expr) -- we defer constructing the proofs until they are needed
(how : how)

/-
Configuration options for a rewrite search.
-/
meta structure config extends tactic.nth_rewrite.cfg :=
(max_iterations     : ℕ := 500)
(explain            : bool := ff)
(explain_using_conv : bool := tt)
(suggest            : list name := [])
(inflate_rws        : bool := ff)
(help_me            : bool := ff)

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

namespace tactic.rewrite_search

meta structure edge :=
(f t   : ℕ)
(proof : tactic expr)
(how   : how)

namespace edge
variables (e : edge)

meta def other (r : ℕ) : option ℕ :=
  if e.f = r then e.t else
  if e.t = r then e.f else
  none

meta instance has_to_format : has_to_format edge := ⟨λ e, format!"{e.f}->{e.t}"⟩

end edge

def invalid_index : ℕ := 0xFFFFFFFF

meta structure vertex :=
(id       : ℕ)
(exp      : expr)
(pp       : string)
(root     : bool)
(visited  : bool)
(s        : side)
(parent   : option edge)
(rws      : buffer rewrite)
(rw_front : ℕ)
(adj      : buffer edge)

namespace vertex

meta def same_side (a b : vertex) : bool := a.s = b.s
meta def to_string (v : vertex) : string := v.s.to_string ++ v.pp

meta def create (id : ℕ) (e : expr) (pp : string) (root : bool) (s : side) : vertex :=
⟨ id, e, pp, root, ff, s, none, buffer.nil, 0, buffer.nil ⟩

meta def null : vertex := vertex.create invalid_index (default expr) "__NULLEXPR" ff side.L

meta instance inhabited : inhabited vertex := ⟨null⟩
meta instance has_to_format : has_to_format vertex := ⟨λ v, v.pp⟩

end vertex

-- queue is a list of pending vertex ids to visit
meta structure search_state :=
(conf         : config)
(rs           : list (expr × bool))
(queue        : list ℕ)
(vertices     : buffer vertex)
(solving_edge : option edge)

def LHS_VERTEX_ID : ℕ := 0
def RHS_VERTEX_ID : ℕ := 1

namespace search_state
variables (g : search_state)

meta def set_queue (new_queue : list ℕ) : search_state := { g with queue := new_queue }

meta def set_vertex (v : vertex) : search_state × vertex :=
({ g with vertices := g.vertices.write' v.id v }, v)

end search_state

meta structure proof_unit :=
(proof : expr)
(side : side)
(steps : list how)

meta inductive search_result
| success (proof : expr) (units : list proof_unit) : search_result
| failure (message : string) : search_result

end tactic.rewrite_search
