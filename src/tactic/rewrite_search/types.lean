/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/

import tactic.nth_rewrite

/-!
# Types used in rewrite search.
-/

open tactic tactic.nth_rewrite.congr
universes u

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

/-
Configuration options for a rewrite search.
-/
meta structure config extends tactic.nth_rewrite.cfg :=
(max_iterations     : ℕ := 500)
(optimal            : bool := tt)
(exhaustive         : bool := ff)
(trace              : bool := ff)
(trace_summary      : bool := ff)
(trace_rules        : bool := ff)
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

meta def rewrite_progress := mllist tactic rewrite

meta def progress_init (rs : list (expr × bool)) (exp : expr) (cfg : config) : rewrite_progress :=
(all_rewrites_lazy_of_list rs exp cfg.to_cfg).map $ λ t, ⟨t.1.exp, t.1.proof, how.rewrite t.2.1 t.2.2 t.1.addr⟩

meta def progress_next (prog : rewrite_progress) : tactic (rewrite_progress × option rewrite) :=
do u ← mllist.uncons prog,
   match u with
   | (some (r, p)) := return (p, (some r))
   | none          := return (mllist.nil, none)
   end

meta def simp_rewrite (exp : expr) : tactic rewrite := do
  (simp_exp, simp_prf) ← exp.simp,
  return ⟨simp_exp, pure simp_prf, how.simp⟩

meta def discover_more_rewrites
  (rs : list (expr × bool)) (exp : expr) (cfg : config) (_ : side)
  (prog : option rewrite_progress) :
  tactic (option rewrite_progress × list rewrite) :=
do
  (prog, head) ← match prog with
         | some prog := pure (prog, [])
         | none := do
          let prog := progress_init rs exp cfg,
          sl ← if cfg.try_simp then option.to_list <$> tactic.try_core (simp_rewrite exp)
                               else pure [],
          pure (prog, sl)
         end,
  (prog, rw) ← progress_next prog,
  return (some prog, head.append rw.to_list)

structure bfs_state :=
(curr_depth : ℕ)
(queue      : list (option ℕ))

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

structure rewrite_iter :=
(orig : ℕ)
(front : ℕ)

meta structure vertex :=
(id       : ℕ)
(exp      : expr)
(pp       : string)
(root     : bool)
(visited  : bool)
(s        : side)
(parent   : option edge)
(rw_prog  : option rewrite_progress)
(rws      : buffer rewrite)
(rw_front : ℕ)
(adj      : buffer edge)

namespace vertex

meta def same_side (a b : vertex) : bool := a.s = b.s
meta def to_string (v : vertex) : string := v.s.to_string ++ v.pp

meta def create (id : ℕ) (e : expr) (pp : string) (root : bool) (s : side) : vertex :=
⟨ id, e, pp, root, ff, s, none, none, buffer.nil, 0, buffer.nil ⟩

meta def null : vertex := vertex.create invalid_index (default expr) "__NULLEXPR" ff side.L

meta instance inhabited : inhabited vertex := ⟨null⟩
meta instance has_to_format : has_to_format vertex := ⟨λ v, v.pp⟩

end vertex

meta inductive status
| continue : status
| repeat : status
| done : edge → status
| abort : string → status

meta structure search_state :=
(conf         : config)
(rs           : list (expr × bool))
(strat_state  : bfs_state)
(vertices     : buffer vertex)
(solving_edge : option edge)

def LHS_VERTEX_ID : ℕ := 0
def RHS_VERTEX_ID : ℕ := 1

namespace search_state
variables (g : search_state)

meta def mutate_strat (new_state : bfs_state) : search_state :=
{ g with strat_state := new_state }

meta def set_vertex (v : vertex) : search_state × vertex :=
({ g with vertices := g.vertices.write' v.id v }, v)

meta def get_endpoints (e : edge) : tactic (vertex × vertex) :=
return (g.vertices.read' e.f, g.vertices.read' e.t)

end search_state

meta structure proof_unit :=
(proof : expr)
(side : side)
(steps : list how)

meta inductive search_result
| success (proof : expr) (units : list proof_unit) : search_result
| failure (message : string) : search_result

end tactic.rewrite_search
