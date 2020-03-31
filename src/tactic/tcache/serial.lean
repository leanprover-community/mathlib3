import data.option.defs
import .common

universe u

open string

def string.iterator.continue (i : iterator) : char × iterator :=
let c := i.curr in (c, i.next)

namespace name

meta def serialise (n : name) : string := sformat!"{n}`"

meta def deserialise_core_aux : iterator → string → name → name × iterator
| i s p := match i.continue with
  | ('`', i) := (name.mk_string s p, i)
  | ('.', i) := deserialise_core_aux i "" (name.mk_string s p)
  | (c, i) := deserialise_core_aux i (s ++ to_string c) p
end

meta def deserialise_core (l : iterator) : name × iterator :=
deserialise_core_aux l "" name.anonymous

meta def deserialise (l : string) : name :=
prod.fst $ deserialise_core l.mk_iterator

end name

namespace string

meta def serialise (s : string) : string := sformat!"{s}`"

meta def deserialise_core_aux : iterator → string → string × iterator
| i s := match i.continue with
  | ('`', i) := (s, i)
  | (c, i) := deserialise_core_aux i $ s.push c
end

meta def deserialise_core (l : iterator) : string × iterator :=
deserialise_core_aux l ""

meta def deserialise (l : string) : string :=
prod.fst $ deserialise_core l.mk_iterator

end string

namespace nat

meta def serialise (n : nat) : string := sformat!"{n}`"

meta def deserialise_core (l : iterator) : nat × iterator :=
let (s, i) := string.deserialise_core l in (s.to_nat, i)

meta def deserialise (l : string) : nat :=
prod.fst $ deserialise_core l.mk_iterator

end nat

namespace level

meta def serialise : level → string
| level.zero := "0"
| (level.succ l) := "+" ++ l.serialise
| (level.max a b) := "m" ++ a.serialise ++ b.serialise
| (level.imax a b) := "i" ++ a.serialise ++ b.serialise
| (level.param n) := "p" ++ n.serialise
| (level.mvar n) := error "level.mvar not implemented"

meta def deserialise_core : iterator → level × iterator
| i := match i.continue with
  | ('0', i) := (level.zero, i)
  | ('+', i) :=
    let (lvl, i) := deserialise_core i in
    (level.succ lvl, i)
  | ('m', i) :=
    let (a, i) := deserialise_core i in
    let (b, i) := deserialise_core i in
    (level.max a b, i)
  | ('i', i) :=
    let (a, i) := deserialise_core i in
    let (b, i) := deserialise_core i in
    (level.imax a b, i)
  | ('p', i) :=
    let (n, i) := name.deserialise_core i in
    (level.param n, i)
  | (c, i) := error sformat!"bad level {c}"
end

meta def deserialise (l : string) : level :=
prod.fst $ deserialise_core l.mk_iterator

end level

namespace binder_info

meta def serialise : binder_info → string
| binder_info.default := "d"
| binder_info.implicit := "i"
| binder_info.strict_implicit := "s"
| binder_info.inst_implicit := "m"
| binder_info.aux_decl := "a"

meta def deserialise_core : iterator → binder_info × iterator
| i := match i.continue with
  | ('d', i) := (binder_info.default, i)
  | ('i', i) := (binder_info.implicit, i)
  | ('s', i) := (binder_info.strict_implicit, i)
  | ('m', i) := (binder_info.inst_implicit, i)
  | ('a', i) := (binder_info.aux_decl, i)
  | (c, i) := error sformat!"bad binder {c}"
end

meta def deserialise (l : string) : binder_info :=
prod.fst $ deserialise_core l.mk_iterator

end binder_info

namespace list

meta def deserialise_core_aux {α : Type u} (p : iterator → α × iterator) : ℕ → iterator → list α × iterator
| 0 i := ([], i)
| (n + 1) i :=
  let (nm, i) := p i in
  let (others, i) := deserialise_core_aux n i in
  (nm :: others, i)

meta def deserialise_core {α : Type u} (p : iterator → α × iterator) (i : iterator) : list α × iterator :=
let (n, i) := nat.deserialise_core i in
deserialise_core_aux p n i

meta def deserialise {α : Type u} (p : iterator → α × iterator) (l : string) : list α :=
prod.fst $ deserialise_core p l.mk_iterator

end list

namespace expr

meta def serialise_core (lc : list expr) : expr → tactic string
| (expr.const n l) := return sformat!"c{n.serialise}{l.length.serialise}{string.intercalate \"\" (l.map level.serialise)}"
| (expr.sort l) := return sformat!"s{l.serialise}"
| (expr.var n) := return sformat!"v{n}`"
| (expr.app f a) := do
  f ← f.serialise_core,
  a ← a.serialise_core,
  return sformat!"a{f}{a}"
| (expr.pi n bi t v) := do
  t ← t.serialise_core,
  v ← v.serialise_core,
  return sformat!"p{n.serialise}{bi.serialise}{t}{v}"
| (expr.lam n bi t v) := do
  t ← t.serialise_core,
  v ← v.serialise_core,
  return sformat!"l{n.serialise}{bi.serialise}{t}{v}"
| (expr.local_const n₁ n₂ bi v) := do
  let i := lc.index_of (expr.local_const n₁ n₂ bi v),
  return $ if i = lc.length
  then error sformat!"unknown lc! {lc.map expr.to_raw_fmt}"
  else sformat!"o{i.serialise}"
| (expr.macro m l) :=
  match (expr.macro_def_name m, l) with
  | ("annotation", [e]) := e.serialise_core
  | ("sorry", _) := tactic.fail "uses sorry"
  | ("string_macro", _) := tactic.fail "uses string_macro"
  | (n, _) := error sformat!"cannot serialise general macros: {n}"
  end
| e := error sformat!"unknown expr: {e.to_raw_fmt}"

meta def serialise (e : expr) : tactic string := do
  lc ← tactic.local_context,
  serialise_core lc e

meta mutual def deserialise_aux, deserialise_binder_data
with deserialise_aux : list expr → iterator → expr × iterator
  | lc i := match i.continue with
  | ('c', i) :=
    let (n, i) := name.deserialise_core i in
    let (l, i) := list.deserialise_core level.deserialise_core i in do
    (expr.const n l, i)
  | ('s', i) :=
    let (l, i) := level.deserialise_core i in
    (expr.sort l, i)
  | ('v', i) :=
    let (n, i) := nat.deserialise_core i in
    (expr.var n, i)
  | ('a', i) :=
    let (f, i) := deserialise_aux lc i in
    let (a, i) := deserialise_aux lc i in
    (expr.app f a, i)
  | ('p', i) :=
    let (n, bi, t, v, i) := deserialise_binder_data lc i in
    (expr.pi n bi t v, i)
  | ('l', i) :=
    let (n, bi, t, v, i) := deserialise_binder_data lc i in
    (expr.lam n bi t v, i)
  | ('o', i) :=
    let (n, i) := nat.deserialise_core i in
    ((lc.nth n).iget, i)
  | (c, i) := error sformat!"stopped at '{c}'"
end
with [inline] deserialise_binder_data : list expr → iterator → name × binder_info × expr × expr × iterator
| lc i :=
  let (n, i) := name.deserialise_core i in
  let (bi, i) := binder_info.deserialise_core i in
  let (t, i) := deserialise_aux lc i in
  let (v, i) := deserialise_aux lc i in
  (n, bi, t, v, i)

meta def deserialise_core (lc : list expr) (s : string) : expr :=
  prod.fst $ deserialise_aux lc s.mk_iterator

meta def deserialise (s : string) : tactic expr := do
  lc ← tactic.local_context,
  return $ deserialise_core lc s

end expr
