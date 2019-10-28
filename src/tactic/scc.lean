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
import category.basic data.sum

namespace tactic

/--
`closure` implements a disjoint set data structure using path compression
optimization. For the sake of the scc algorithm, it also stores the preorder
numbering of the equivalence graph of the local assumptions.

The `expr_map` encodes a directed forest by storing for every non-root
node, a reference to its parent and a proof of equivalence between
that node's expression and its parent's expression. Given that data
structure, checking that two nodes belong to the same tree is easy and
fast by following the parent reference repeated up to a root. If they
both have the same root, they belong to the same tree, i.e. their
expressions are equivalent. The proof of equivance can be formed by
composing the proofs along the edges of the paths to the root.

More concretely, if we ignore preorder numbering, the set
`{ {e₀,e₁,e₂,e₃}, {e₄,e₅} }` is represented as:

```
e₀ → ⊥      -- no parent, i.e. e₀ is a root
e₁ → e₀, p₁ -- with p₁ : e₁ ↔ e₀
e₂ → e₁, p₂ -- with p₂ : e₂ ↔ e₁
e₃ → e₀, p₃ -- with p₃ : e₃ ↔ e₀
e₄ → ⊥      -- no parent, i.e. e₄ is a root
e₅ → e₄, p₅ -- with p₅ : e₅ ↔ e₄
```

We can check that `e₂` and `e₃` are equivalent by seeking the root of
the tree of each. The parent of `e₂` is `e₁`, the parent of `e₁` is
`e₀` and `e₀` does not have a parent, and thus, this is the root of its root.
The parent of `e₃` is `e₀` and it's also the root, the same as for `e₃` and
they are therefore equivalent. We can build a proof of that equivalence by using
transitivity on `p₂`, `p₁` and `p₃.symm` in that order.

Similarly, we can discover that `e₂` and `e₅` aren't equivalent.

A description of the path compression optimization can be found at:
https://en.wikipedia.org/wiki/Disjoint-set_data_structure#Path_compression

-/
meta def closure := ref (expr_map (ℕ ⊕ (expr × expr)))

namespace closure

meta def mk_closure {α} : (closure → tactic α) → tactic α :=
using_new_ref (expr_map.mk _)

meta def to_tactic_format (cl : closure) : tactic format :=
do m ← read_ref cl,
   let l := m.to_list,
   fmt ← l.mmap $ λ ⟨x,y⟩, match y with
                           | sum.inl y := pp y
                           | sum.inr ⟨y,p⟩ := pformat!"({x}, {y}) : {infer_type p}"
                           end,
   pure $ to_fmt fmt

meta instance : has_to_tactic_format closure := ⟨ to_tactic_format ⟩

meta def root (cl : closure) : expr → tactic (ℕ × expr × expr) | e :=
do m ← read_ref cl,
   match m.find e with
   | none :=
     do p ← mk_app ``iff.refl [e],
        pure (0,e,p)
   | (some (sum.inl n)) :=
     do p ← mk_app ``iff.refl [e],
        pure (n,e,p)
   | (some (sum.inr (e₀,p₀))) :=
     do (n,e₁,p₁) ← root e₀,
        p ← mk_app ``iff.trans [p₀,p₁],
        modify_ref cl $ λ m, m.insert e (sum.inr (e₁,p)),
        pure (n,e₁,p)
   end

meta def merge_intl (cl : closure) (p e₀ p₀ e₁ p₁ : expr) : tactic unit :=
do p₂ ← mk_app ``iff.symm [p₀],
   p ← mk_app ``iff.trans [p₂,p],
   p ← mk_app ``iff.trans [p,p₁],
   modify_ref cl $ λ m, m.insert e₀ $ sum.inr (e₁,p)

meta def merge (cl : closure) (p : expr) : tactic unit :=
do `(%%e₀ ↔ %%e₁) ← infer_type p >>= instantiate_mvars,
   (n₂,e₂,p₂) ← root cl e₀,
   (n₃,e₃,p₃) ← root cl e₁,
   if e₂ ≠ e₃ then do
     if n₂ < n₃ then do p ← mk_app ``iff.symm [p],
                        cl.merge_intl p e₃ p₃ e₂ p₂
                else cl.merge_intl p e₂ p₂ e₃ p₃
   else pure ()

meta def assign_preorder (cl : closure) (e : expr) : tactic unit :=
modify_ref cl $ λ m, m.insert e (sum.inl m.size)

meta def prove_eqv (cl : closure) (e₀ e₁ : expr) : tactic expr :=
do (_,r,p₀) ← root cl e₀,
   (_,r',p₁) ← root cl e₁,
   is_def_eq r r',
   p₁ ← mk_app ``iff.symm [p₁],
   mk_app ``iff.trans [p₀,p₁]

meta def prove_impl (cl : closure) (e₀ e₁ : expr) : tactic expr :=
cl.prove_eqv e₀ e₁ >>= iff_mp

meta def is_eqv (cl : closure) (e₀ e₁ : expr) : tactic bool :=
do (_,r,p₀) ← root cl e₀,
   (_,r',p₁) ← root cl e₁,
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
do p₁ ← cl.prove_impl e path.head.fst,
   p₂ ← mk_mapp ``id [e],
   let path := (e,p₁) :: path,

   (_,ls) ← path.mmap_accuml (λ p p',
     prod.mk <$> mk_mapp ``implies.trans [none,p'.1,none,p,p'.2] <*> pure p) p₂,
   (_,rs) ← path.mmap_accumr (λ p p',
     prod.mk <$> mk_mapp ``implies.trans [none,none,none,p.2,p'] <*> pure p') p₂,
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


/--
Strongly connected component algorithm inspired by Tarjan's and
Dijkstra's scc algorithm.  Whereas they return strongly connected
components by enumerating them, this algorithm returns a disjoint set
data structure using path compression. This is a compact
representation that allows us, after the fact, construct a proof of
equivalence between any two members of an equivalence class.

Tarjan, R. E. (1972), "Depth-first search and linear graph algorithms",
SIAM Journal on Computing, 1 (2): 146–160, doi:10.1137/0201010

Dijkstra, Edsger (1976), A Discipline of Programming, NJ: Prentice Hall, Ch. 25.
-/
meta def dfs_at :
  list (expr × expr) → expr → tactic unit
| vs v :=
do m ← read_ref visit,
   (_,v',_) ← cl.root v,
   match m.find v' with
   | (some tt) :=
        pure ()
   | (some ff) :=
        collapse vs v
   | none :=
     do cl.assign_preorder v,
        modify_ref visit $ λ m, m.insert v ff,
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
