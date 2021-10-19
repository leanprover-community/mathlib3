/-
Copyright (c) 2018 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.tauto
import data.sum

/-!
# Strongly Connected Components

This file defines tactics to construct proofs of equivalences between a set of mutually equivalent
propositions. The tactics use implications transitively to find sets of equivalent propositions.

## Implementation notes

The tactics use a strongly connected components algorithm on a graph where propositions are
vertices and edges are proofs that the source implies the target. The strongly connected components
are therefore sets of propositions that are pairwise equivalent to each other.

The resulting strongly connected components are encoded in a disjoint set data structure to
facilitate the construction of equivalence proofs between two arbitrary members of an equivalence
class.

## Possible generalizations

Instead of reasoning about implications and equivalence, we could generalize the machinery to
reason about arbitrary partial orders.

## References

 * Tarjan, R. E. (1972), "Depth-first search and linear graph algorithms",
   SIAM Journal on Computing, 1 (2): 146–160, doi:10.1137/0201010
 * Dijkstra, Edsger (1976), A Discipline of Programming, NJ: Prentice Hall, Ch. 25.
 * <https://en.wikipedia.org/wiki/Disjoint-set_data_structure>

## Tags

graphs, tactic, strongly connected components, disjoint sets
-/

namespace tactic

/--
`closure` implements a disjoint set data structure using path compression
optimization. For the sake of the scc algorithm, it also stores the preorder
numbering of the equivalence graph of the local assumptions.

The `expr_map` encodes a directed forest by storing for every non-root
node, a reference to its parent and a proof of equivalence between
that node's expression and its parent's expression. Given that data
structure, checking that two nodes belong to the same tree is easy and
fast by repeatedly following the parent references until a root is reached.
If both nodes have the same root, they belong to the same tree, i.e. their
expressions are equivalent. The proof of equivalence can be formed by
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
`e₀` and `e₀` does not have a parent, and thus, this is the root of its tree.
The parent of `e₃` is `e₀` and it's also the root, the same as for `e₂` and
they are therefore equivalent. We can build a proof of that equivalence by using
transitivity on `p₂`, `p₁` and `p₃.symm` in that order.

Similarly, we can discover that `e₂` and `e₅` aren't equivalent.

A description of the path compression optimization can be found at:
<https://en.wikipedia.org/wiki/Disjoint-set_data_structure#Path_compression>

-/
meta def closure := ref (expr_map (ℕ ⊕ (expr × expr)))

namespace closure

/-- `with_new_closure f` creates an empty `closure` `c`, executes `f` on `c`, and then deletes `c`,
returning the output of `f`. -/
meta def with_new_closure {α} : (closure → tactic α) → tactic α :=
using_new_ref (expr_map.mk _)

/-- `to_tactic_format cl` pretty-prints the `closure` `cl` as a list. Assuming `cl` was built by
`dfs_at`, each element corresponds to a node `pᵢ : expr` and is one of the folllowing:
- if `pᵢ` is a root: `"pᵢ ⇐ i"`, where `i` is the preorder number of `pᵢ`,
- otherwise: `"(pᵢ, pⱼ) : P"`, where `P` is `pᵢ ↔ pⱼ`.
Useful for debugging. -/
meta def to_tactic_format (cl : closure) : tactic format :=
do m ← read_ref cl,
   let l := m.to_list,
   fmt ← l.mmap $ λ ⟨x,y⟩, match y with
                           | sum.inl y := pformat!"{x} ⇐ {y}"
                           | sum.inr ⟨y,p⟩ := pformat!"({x}, {y}) : {infer_type p}"
                           end,
   pure $ to_fmt fmt

meta instance : has_to_tactic_format closure := ⟨ to_tactic_format ⟩

/-- `(n,r,p) ← root cl e` returns `r` the root of the tree that `e` is a part of (which might be
itself) along with `p` a proof of `e ↔ r` and `n`, the preorder numbering of the root. -/
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

/-- (Implementation of `merge`.) -/
meta def merge_intl (cl : closure) (p e₀ p₀ e₁ p₁ : expr) : tactic unit :=
do p₂ ← mk_app ``iff.symm [p₀],
   p ← mk_app ``iff.trans [p₂,p],
   p ← mk_app ``iff.trans [p,p₁],
   modify_ref cl $ λ m, m.insert e₀ $ sum.inr (e₁,p)

/-- `merge cl p`, with `p` a proof of `e₀ ↔ e₁` for some `e₀` and `e₁`,
merges the trees of `e₀` and `e₁` and keeps the root with the smallest preorder
number as the root. This ensures that, in the depth-first traversal of the graph,
when encountering an edge going into a vertex whose equivalence class includes
a vertex that originated the current search, that vertex will be the root of
the corresponding tree. -/
meta def merge (cl : closure) (p : expr) : tactic unit :=
do `(%%e₀ ↔ %%e₁) ← infer_type p >>= instantiate_mvars,
   (n₂,e₂,p₂) ← root cl e₀,
   (n₃,e₃,p₃) ← root cl e₁,
   if e₂ ≠ e₃ then do
     if n₂ < n₃ then do p ← mk_app ``iff.symm [p],
                        cl.merge_intl p e₃ p₃ e₂ p₂
                else cl.merge_intl p e₂ p₂ e₃ p₃
   else pure ()

/-- Sequentially assign numbers to the nodes of the graph as they are being visited. -/
meta def assign_preorder (cl : closure) (e : expr) : tactic unit :=
modify_ref cl $ λ m, m.insert e (sum.inl m.size)

/-- `prove_eqv cl e₀ e₁` constructs a proof of equivalence of `e₀` and `e₁` if
they are equivalent. -/
meta def prove_eqv (cl : closure) (e₀ e₁ : expr) : tactic expr :=
do (_,r,p₀) ← root cl e₀,
   (_,r',p₁) ← root cl e₁,
   guard (r = r') <|> fail!"{e₀} and {e₁} are not equivalent",
   p₁ ← mk_app ``iff.symm [p₁],
   mk_app ``iff.trans [p₀,p₁]

/-- `prove_impl cl e₀ e₁` constructs a proof of `e₀ -> e₁` if they are equivalent. -/
meta def prove_impl (cl : closure) (e₀ e₁ : expr) : tactic expr :=
cl.prove_eqv e₀ e₁ >>= iff_mp

/-- `is_eqv cl e₀ e₁` checks whether `e₀` and `e₁` are equivalent without building a proof. -/
meta def is_eqv (cl : closure) (e₀ e₁ : expr) : tactic bool :=
do (_,r,p₀) ← root cl e₀,
   (_,r',p₁) ← root cl e₁,
   return $ r = r'

end closure

/-- mutable graphs between local propositions that imply each other with the proof of implication -/
@[reducible]
meta def impl_graph := ref (expr_map (list $ expr × expr))

/-- `with_impl_graph f` creates an empty `impl_graph` `g`, executes `f` on `g`, and then deletes
`g`, returning the output of `f`. -/
meta def with_impl_graph {α} : (impl_graph → tactic α) → tactic α :=
using_new_ref (expr_map.mk (list $ expr × expr))

namespace impl_graph

/-- `add_edge g p`, with `p` a proof of `v₀ → v₁` or `v₀ ↔ v₁`, adds an edge to the implication
graph `g`. -/
meta def add_edge (g : impl_graph) : expr → tactic unit | p :=
do t ← infer_type p,
   match t with
   | `(%%v₀ → %%v₁) :=
     do is_prop v₀ >>= guardb,
        is_prop v₁ >>= guardb,
        m ← read_ref g,
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

/-- `merge_path path e`, where `path` and `e` forms a cycle with proofs of implication between
consecutive vertices. The proofs are compiled into proofs of equivalences and added to the closure
structure. `e` and the first vertex of `path` do not have to be the same but they have to be
in the same equivalence class. -/
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

/-- (implementation of `collapse`) -/
meta def collapse' : list (expr × expr) → list (expr × expr) → expr → tactic unit
| acc [] v := merge_path acc v
| acc ((x,pr) :: xs) v :=
  do b ← cl.is_eqv x v,
     let acc' := (x,pr)::acc,
     if b
       then merge_path acc' v
       else collapse' acc' xs v

/-- `collapse path v`, where `v` is a vertex that originated the current search
(or a vertex in the same equivalence class as the one that originated the current search).
It or its equivalent should be found in `path`. Since the vertices following `v` in the path
form a cycle with `v`, they can all be added to an equivalence class. -/
meta def collapse : list (expr × expr) → expr → tactic unit :=
collapse' []

/--
Strongly connected component algorithm inspired by Tarjan's and
Dijkstra's scc algorithm. Whereas they return strongly connected
components by enumerating them, this algorithm returns a disjoint set
data structure using path compression. This is a compact
representation that allows us, after the fact, to construct a proof of
equivalence between any two members of an equivalence class.

 * Tarjan, R. E. (1972), "Depth-first search and linear graph algorithms",
   SIAM Journal on Computing, 1 (2): 146–160, doi:10.1137/0201010
 * Dijkstra, Edsger (1976), A Discipline of Programming, NJ: Prentice Hall, Ch. 25.
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

/-- Use the local assumptions to create a set of equivalence classes. -/
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

/--
`scc` uses the available equivalences and implications to prove
a goal of the form `p ↔ q`.

```lean
example (p q r : Prop) (hpq : p → q) (hqr : q ↔ r) (hrp : r → p) : p ↔ r :=
by scc
```
-/
meta def interactive.scc : tactic unit :=
closure.with_new_closure $ λ cl,
do impl_graph.mk_scc cl,
   `(%%p ↔ %%q) ← target,
   cl.prove_eqv p q >>= exact

/-- Collect all the available equivalences and implications and
add assumptions for every equivalence that can be proven using the
strongly connected components technique. Mostly useful for testing. -/
meta def interactive.scc' : tactic unit :=
closure.with_new_closure $ λ cl,
do m ← impl_graph.mk_scc cl,
   let ls := m.to_list.map prod.fst,
   let ls' := prod.mk <$> ls <*> ls,
   ls'.mmap' $ λ x,
     do { h ← get_unused_name `h,
          try $ closure.prove_eqv cl x.1 x.2 >>= note h none }

/--
`scc` uses the available equivalences and implications to prove
a goal of the form `p ↔ q`.

```lean
example (p q r : Prop) (hpq : p → q) (hqr : q ↔ r) (hrp : r → p) : p ↔ r :=
by scc
```

The variant `scc'` populates the local context with all equivalences that `scc` is able to prove.
This is mostly useful for testing purposes.
-/
add_tactic_doc
{ name := "scc",
  category := doc_category.tactic,
  decl_names := [``interactive.scc, ``interactive.scc'],
  tags := ["logic"] }

end tactic
