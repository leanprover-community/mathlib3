/-
Copyright (c) 2018 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Tactics based on the strongly connected components (SCC) of a graph where
the vertices are propositions and the edges are implications found
in the context.

They are used for finding the sets of equivalent proposition in a set
of implications.
-/

import tactic.tauto
import category.basic

namespace tactic

meta def closure := ref (expr_map (expr × expr))

namespace closure

meta def mk_closure {α} : (closure → tactic α) → tactic α :=
using_new_ref (expr_map.mk _)

meta def to_tactic_format (cl : closure) : tactic format :=
do m ← read_ref cl,
   let l := m.to_list,
   fmt ← l.mmap $ λ ⟨x,y,p⟩, pformat!"({x}, {y}) : {infer_type p}",
   pure $ to_fmt fmt

meta instance : has_to_tactic_format closure := ⟨ to_tactic_format ⟩

meta def root' (cl : closure) : expr → tactic (expr × expr) | e :=
do m ← read_ref cl,
   match m.find e with
   | none :=
     do p ← mk_app ``iff.refl [e],
        pure (e,p)
   | (some (e₀,p₀)) :=
     do (e₁,p₁) ← root' e₀,
        p ← mk_app ``iff.trans [p₀,p₁],
        modify_ref cl $ λ m, m.insert e (e₁,p),
        pure (e₁,p)
   end

meta def root (cl : closure) (p : expr) : tactic (expr × expr) :=
instantiate_mvars p >>= root' cl

meta def merge (cl : closure) (p : expr) : tactic unit :=
do `(%%e₀ ↔ %%e₁) ← infer_type p >>= instantiate_mvars,
   (e₂,p₀) ← root cl e₀,
   (e₃,p₁) ← root cl e₁,
   if e₂ ≠ e₃ then do
     p₂ ← mk_app ``iff.symm [p₀],
     p ← mk_app ``iff.trans [p₂,p],
     p ← mk_app ``iff.trans [p,p₁],
     modify_ref cl $ λ m, m.insert e₂ (e₃,p)
   else pure ()

meta def prove_eqv (cl : closure) (e₀ e₁ : expr) : tactic expr :=
do (r,p₀) ← root cl e₀,
   (r',p₁) ← root cl e₁,
   is_def_eq r r',
   p₁ ← mk_app ``iff.symm [p₁],
   mk_app ``iff.trans [p₀,p₁]

meta def prove_impl (cl : closure) (e₀ e₁ : expr) : tactic expr :=
cl.prove_eqv e₀ e₁ >>= iff_mp

meta def is_eqv (cl : closure) (e₀ e₁ : expr) : tactic bool :=
do (r,p₀) ← root cl e₀,
   (r',p₁) ← root cl e₁,
   succeeds $ is_def_eq r r'

end closure

@[reducible]
meta def impl_graph := ref (expr_map (list $ expr × expr))

meta def with_impl_graph {α} : (impl_graph → tactic α) → tactic α :=
using_new_ref (expr_map.mk (list $ expr × expr))

namespace impl_graph

meta def add_edge (g : impl_graph) : expr → tactic unit | p :=
do t ← infer_type p,
   match t with
   | `(%%v₀ → %%v₁) :=
     do m ← read_ref g,
        let xs := (m.find v₀).get_or_else [],
        let xs' := (m.find v₁).get_or_else [],
        modify_ref g $ λ m, (m.insert v₀ ((v₁,p) :: xs)).insert v₁ xs'
   | `(%%v₀ ↔ %%v₁) :=
     do p₀ ← mk_mapp ``iff.mp [none,none,p],
        p₁ ← mk_mapp ``iff.mpr [none,none,p],
        add_edge p₀, add_edge p₁
   | _ := failed
   end

section scc
open list
parameter g : expr_map (list $ expr × expr)
parameter visit : ref $ expr_map bool
parameter cl : closure

meta def merge_path (path : list (expr × expr)) (e : expr) : tactic unit :=
do p₀ ← cl.prove_impl e $ path.head.fst,
   (_,ls) ← path.mmap_accuml (λ p p',
     prod.mk <$> mk_mapp ``implies.trans [none,p'.1,none,p,p'.2] <*> pure p) p₀,
   (_,rs) ← path.mmap_accumr (λ p p',
     prod.mk <$> mk_mapp ``implies.trans [none,none,none,p.2,p'] <*> pure p') p₀,
   ps ← mzip_with (λ p₀ p₁, mk_app ``iff.intro [p₀,p₁]) ls.tail rs.init,
   ps.mmap' cl.merge

meta def collapse' : list (expr × expr) → list (expr × expr) → expr → tactic unit
| acc [] v := merge_path acc v
| acc ((x,pr) :: xs) v :=
  do b ← cl.is_eqv x v,
     let acc' := (x,pr)::acc,
     if b
       then merge_path acc' v
       else collapse' acc' xs v

meta def collapse : list (expr × expr) → expr → tactic unit :=
collapse' []

meta def dfs_at :
  list (expr × expr) →
  expr →
  tactic unit
| vs v :=
do m ← read_ref visit,
   match m.find v with
   | (some tt) := pure ()
   | (some ff) := collapse vs v
   | none :=
     do modify_ref visit $ λ m, m.insert v ff,
        ns ← g.find v,
        ns.mmap' $ λ ⟨w,e⟩, dfs_at ((v,e) :: vs) w,
        modify_ref visit $ λ m, m.insert v tt,
        pure ()
   end

end scc

meta def mk_scc (cl : closure) : tactic (expr_map (list (expr × expr))) :=
with_impl_graph $ λ g,
using_new_ref (expr_map.mk bool) $ λ visit,
do ls ← local_context,
   ls.mmap' $ λ l, try (g.add_edge l),
   m ← read_ref g,
   m.to_list.mmap $ λ ⟨v,_⟩, impl_graph.dfs_at m visit cl [] v,
   pure m

end impl_graph

meta def prove_eqv_target (cl : closure) : tactic unit :=
do `(%%p ↔ %%q) ← target >>= whnf,
   cl.prove_eqv p q >>= exact

/-- Use the available equivalences and implications to prove
a goal of the form `p ↔ q`. -/
meta def interactive.scc : tactic unit :=
closure.mk_closure $ λ cl,
do impl_graph.mk_scc cl,
   `(%%p ↔ %%q) ← target,
   cl.prove_eqv p q >>= exact

/-- Collect all the available equivalences and implications and
add assumptions for every equivalence that can be proven using the
strongly connected components technique. Mostly useful for testing. -/
meta def interactive.scc' : tactic unit :=
closure.mk_closure $ λ cl,
do m ← impl_graph.mk_scc cl,
   let ls := m.to_list.map prod.fst,
   let ls' := prod.mk <$> ls <*> ls,
   ls'.mmap' $ λ x,
     do { h ← get_unused_name `h,
          try $ closure.prove_eqv cl x.1 x.2 >>= note h none }

end tactic
