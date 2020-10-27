/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/

import data.array.table

import tactic.rewrite_search.core.common
import tactic.rewrite_search.core.hook

/-!
# Types used in rewrite search.
-/

universes u v

open tactic

namespace tactic.rewrite_search

structure bfs_state :=
(curr_depth : ℕ)
(queue      : list (option table_ref))

meta structure edge :=
(f t   : table_ref)
(proof : tactic expr)
(how   : how)

namespace edge
variables (e : edge)

meta def other (r : table_ref) : option table_ref :=
  if e.f = r then e.t else
  if e.t = r then e.f else
  none

meta instance has_to_format : has_to_format edge := ⟨λ e, format!"{e.f}->{e.t}"⟩

end edge

structure rewrite_iter :=
(orig : table_ref)
(front : table_ref)

meta structure vertex :=
(id       : table_ref)
(exp      : expr)
(pp       : string)
(tokens   : list table_ref)
(root     : bool)
(visited  : bool)
(s        : side)
(parent   : option edge)
(rw_prog  : option rewrite_progress)
(rws      : table rewrite)
(rw_front : table_ref)
(adj      : table edge)

namespace vertex

meta def same_side (a b : vertex) : bool := a.s = b.s
meta def to_string (v : vertex) : string := v.s.to_string ++ v.pp
meta def create (id : table_ref) (e : expr) (pp : string) (token_refs : list table_ref)
(root : bool) (s : side) : vertex :=
⟨ id, e, pp, token_refs, root, ff, s, none, none, table.create, table_ref.first, table.create ⟩

meta def null : vertex := vertex.create table_ref.null (default expr) "__NULLEXPR" [] ff side.L

meta instance inhabited : inhabited vertex := ⟨null⟩
meta instance indexed : indexed vertex := ⟨λ v, v.id⟩
meta instance keyed : keyed vertex string := ⟨λ v, v.pp⟩
meta instance has_to_format : has_to_format vertex := ⟨λ v, v.pp⟩

end vertex

def pair := sided_pair table_ref
def pair.null : pair := ⟨table_ref.null, table_ref.null⟩
instance pair.has_to_string : has_to_string pair := ⟨sided_pair.to_string⟩

structure token :=
(id   : table_ref)
(str  : string)
(freq : sided_pair ℕ)

namespace token

def inc (t : token) (s : side) : token := {t with freq := t.freq.set s $ (t.freq.get s) + 1}

def null : token := ⟨ table_ref.null, "__NULLTOKEN", 0, 0 ⟩

instance inhabited : inhabited token := ⟨null⟩
instance indexed : indexed token := ⟨λ t, t.id⟩
instance keyed : keyed token string := ⟨λ v, v.str⟩

end token

meta def find_or_create_token (tokens : table token) (s : side) (tstr : string) :
table token × token :=
match tokens.find_key tstr with
| none := do
  let t : token := ⟨tokens.next_id, tstr, ⟨0, 0⟩⟩,
  let t := t.inc s in (tokens.alloc t, t)
| (some t) := do
  let t := t.inc s in (tokens.update t, t)
end

meta inductive status
| continue : status
| repeat : status
| done : edge → status
| abort : string → status

meta structure search_state :=
(conf         : config)
(rwall_conf   : nth_rewrite.cfg)
(rs           : list (expr × bool))
(strat_state  : bfs_state)
(tokens       : table token)
(vertices     : table vertex)
(solving_edge : option edge)

def LHS_VERTEX_ID : table_ref := table_ref.of_nat 0
def RHS_VERTEX_ID : table_ref := table_ref.of_nat 1

namespace search_state
variables (g : search_state)

meta def mutate_strat (new_state : bfs_state) : search_state :=
{ g with strat_state := new_state }

meta def set_vertex (v : vertex) : search_state × vertex :=
({ g with vertices := g.vertices.set v.id v }, v)

meta def lookup_pair (p : pair) : tactic (vertex × vertex) := do
vf ← g.vertices.get p.l, vt ← g.vertices.get p.r, return (vf, vt)

meta def get_endpoints (e : edge) : tactic (vertex × vertex) := do
vf ← g.vertices.get e.f, vt ← g.vertices.get e.t, return (vf, vt)

end search_state

meta structure proof_unit :=
(proof : expr)
(side : side)
(steps : list how)

meta inductive search_result
| success (proof : expr) (units : list proof_unit) : search_result
| failure (message : string) : search_result

end tactic.rewrite_search
