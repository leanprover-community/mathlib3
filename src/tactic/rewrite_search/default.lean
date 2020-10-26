-- Provide the interactive tactics
import tactic.rewrite_search.interactive

-- FIXME: delete this block
import tactic.rewrite_search.strategy

/-!
# Searching for chains of rewrites

`rewrite_search` is a tactic that attempts to rewrite
the lhs and rhs of an equation or iff so that they become more similar.

In this comment we will provide an overview of the code
and pointers to more specific documentation.

TODO: write this documentation.

-/
