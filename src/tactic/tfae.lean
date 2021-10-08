/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Simon Hudon
-/
import data.list.tfae
import tactic.scc

/-!
# The Following Are Equivalent (TFAE)

This file provides the tactics `tfae_have` and `tfae_finish` for proving the pairwise equivalence of
propositions in a set using various implications between them.
-/

open expr tactic lean lean.parser

namespace tactic
open interactive interactive.types expr

export list (tfae)

namespace tfae

@[derive has_reflect, derive inhabited]
inductive arrow : Type
| right      : arrow
| left_right : arrow
| left       : arrow

meta def mk_implication : Π (re : arrow) (e₁ e₂ : expr), pexpr
| arrow.right      e₁ e₂ := ``(%%e₁ → %%e₂)
| arrow.left_right e₁ e₂ := ``(%%e₁ ↔ %%e₂)
| arrow.left       e₁ e₂ := ``(%%e₂ → %%e₁)

meta def mk_name : Π (re : arrow) (i₁ i₂ : nat), name
| arrow.right      i₁ i₂ := ("tfae_" ++ to_string i₁ ++ "_to_"  ++ to_string i₂ : string)
| arrow.left_right i₁ i₂ := ("tfae_" ++ to_string i₁ ++ "_iff_" ++ to_string i₂ : string)
| arrow.left       i₁ i₂ := ("tfae_" ++ to_string i₂ ++ "_to_"  ++ to_string i₁ : string)

end tfae

namespace interactive

open tactic.tfae list

meta def parse_list : expr → option (list expr)
| `([]) := pure []
| `(%%e :: %%es) := (::) e <$> parse_list es
| _ := none

/-- In a goal of the form `tfae [a₀, a₁, a₂]`,
`tfae_have : i → j` creates the assertion `aᵢ → aⱼ`. The other possible
notations are `tfae_have : i ← j` and `tfae_have : i ↔ j`. The user can
also provide a label for the assertion, as with `have`: `tfae_have h : i ↔ j`.
-/
meta def tfae_have
  (h : parse $ optional ident <* tk ":")
  (i₁ : parse (with_desc "i" small_nat))
  (re : parse (((tk "→" <|> tk "->")  *> return arrow.right)      <|>
               ((tk "↔" <|> tk "<->") *> return arrow.left_right) <|>
               ((tk "←" <|> tk "<-")  *> return arrow.left)))
  (i₂ : parse (with_desc "j" small_nat)) :
  tactic unit := do
    `(tfae %%l) <- target,
    l ← parse_list l,
    e₁ ← list.nth l (i₁ - 1) <|> fail format!"index {i₁} is not between 1 and {l.length}",
    e₂ ← list.nth l (i₂ - 1) <|> fail format!"index {i₂} is not between 1 and {l.length}",
    type ← to_expr (tfae.mk_implication re e₁ e₂),
    let h := h.get_or_else (mk_name re i₁ i₂),
    tactic.assert h type,
    return ()

/-- Finds all implications and equivalences in the context
to prove a goal of the form `tfae [...]`.
-/
meta def tfae_finish : tactic unit :=
applyc ``tfae_nil <|>
closure.with_new_closure (λ cl,
do impl_graph.mk_scc cl,
   `(tfae %%l) ← target,
   l ← parse_list l,
   (_,r,_) ← cl.root l.head,
   refine ``(tfae_of_forall %%r _ _),
   thm ← mk_const ``forall_mem_cons,
   l.mmap' (λ e,
     do rewrite_target thm, split,
        (_,r',p) ← cl.root e,
        tactic.exact p ),
   applyc ``forall_mem_nil,
   pure ())

end interactive
end tactic

/--
The `tfae` tactic suite is a set of tactics that help with proving that certain
propositions are equivalent.
In `data/list/basic.lean` there is a section devoted to propositions of the
form
```lean
tfae [p1, p2, ..., pn]
```
where `p1`, `p2`, through, `pn` are terms of type `Prop`.
This proposition asserts that all the `pi` are pairwise equivalent.
There are results that allow to extract the equivalence
of two propositions `pi` and `pj`.

To prove a goal of the form `tfae [p1, p2, ..., pn]`, there are two
tactics.  The first tactic is `tfae_have`.  As an argument it takes an
expression of the form `i arrow j`, where `i` and `j` are two positive
natural numbers, and `arrow` is an arrow such as `→`, `->`, `←`, `<-`,
`↔`, or `<->`.  The tactic `tfae_have : i arrow j` sets up a subgoal in
which the user has to prove the equivalence (or implication) of `pi` and `pj`.

The remaining tactic, `tfae_finish`, is a finishing tactic. It
collects all implications and equivalences from the local context and
computes their transitive closure to close the
main goal.

`tfae_have` and `tfae_finish` can be used together in a proof as
follows:

```lean
example (a b c d : Prop) : tfae [a,b,c,d] :=
begin
  tfae_have : 3 → 1,
  { /- prove c → a -/ },
  tfae_have : 2 → 3,
  { /- prove b → c -/ },
  tfae_have : 2 ← 1,
  { /- prove a → b -/ },
  tfae_have : 4 ↔ 2,
  { /- prove d ↔ b -/ },
    -- a b c d : Prop,
    -- tfae_3_to_1 : c → a,
    -- tfae_2_to_3 : b → c,
    -- tfae_1_to_2 : a → b,
    -- tfae_4_iff_2 : d ↔ b
    -- ⊢ tfae [a, b, c, d]
  tfae_finish,
end
```
-/
add_tactic_doc
{ name := "tfae",
  category                 := doc_category.tactic,
  decl_names               := [`tactic.interactive.tfae_have, `tactic.interactive.tfae_finish],
  tags                     := ["logic"],
  inherit_description_from := `tactic.interactive.tfae_finish }
