/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import algebra.group.defs

/-!
# Covariants and contravariants
This file contains general lemmas and instances to work with the interactions between a relation and
an action on a Type.
The intended application is the splitting of the ordering from the algebraic assumptions on the
operations in the `ordered_[...]` hierarchy.
The strategy is to introduce two more flexible typeclasses, `covariant_class` and
`contravariant_class`.
* `covariant_class` models the implication `a ≤ b → c * a ≤ c * b` (multiplication is monotone),
* `contravariant_class` models the implication `a * b < a * c → b < c`.
Since `co(ntra)variant_class` takes as input the operation (typically `(+)` or `(*)`) and the order
relation (typically `(≤)` or `(<)`), these are the only two typeclasses that I have used.
The general approach is to formulate the lemma that you are interested and prove it, with the
`ordered_[...]` typeclass of your liking.  After that, you convert the single typeclass,
say `[ordered_cancel_monoid M]`, with three typeclasses, e.g.
`[partial_order M] [left_cancel_semigroup M] [covariant_class M M (function.swap (*)) (≤)]`
and have a go at seeing if the proof still works!
Note that it is possible to combine several co(ntra)variant_class assumptions together.
Indeed, the usual ordered typeclasses arise from assuming the pair
`[covariant_class M M (*) (≤)] [contravariant_class M M (*) (<)]`
on top of order/algebraic assumptions.
A formal remark is that normally covariant_class uses the `(≤)`-relation, while contravariant_class
uses the `(<)`-relation. This need not be the case in general, but seems to be the most common
usage. In the opposite direction, the implication
```lean
[semigroup α] [partial_order α] [contravariant_class α α (*) (≤)] => left_cancel_semigroup α
```
holds (note the `co*ntra*` assumption and the `(≤)`-relation).
# Formalization notes
We stick to the convention of using `function.swap (*)` (or `function.swap (+)`), for the
typeclass assumptions, since `function.swap` is slightly better behaved than `flip`.
However, sometimes as a **non-typeclass** assumption, we prefer `flip (*)` (or `flip (+)`),
as it is easier to use. -/

-- TODO: convert `has_exists_mul_of_le`, `has_exists_add_of_le`?
-- TODO: relationship with `add_con`
-- include equivalence of `left_cancel_semigroup` with
-- `semigroup partial_order contravariant_class α α (*) (≤)`?
-- use ⇒, as per Eric's suggestion?

section variants

variables {M N : Type*} (μ : M → N → N) (r s : N → N → Prop) (m : M) {a b c : N}


variables (M N)
/-- `covariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `covariant_class` doc-string for its meaning. -/
def covariant     : Prop := ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)

/-- `contravariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `contravariant_class` doc-string for its meaning. -/
def contravariant : Prop := ∀ (m) {n₁ n₂}, s (μ m n₁) (μ m n₂) → s n₁ n₂

/--  Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`covariant_class` says that "the action `μ` preserves the relation `r`.

More precisely, the `covariant_class` is a class taking two Types `M N`, together with an "action"
`μ : M → N → N` and a relation `r : N → N`.  Its unique field `covc` is the assertion that
for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
`(n₁, n₂)`, then, the relation `r` also holds for the pair `(μ m n₁, μ m n₂)`,
obtained from `(n₁, n₂)` by "acting upon it by `m`".

If `m : M` and `h : r n₁ n₂`, then `covariant_class.covc m h : r (μ m n₁) (μ m n₂)`.
-/
class covariant_class :=
(covc :  covariant M N μ r)

/--  Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`contravariant_class` says that "if the result of the action `μ` on a pair satisfies the
relation `r`, then the initial pair satisfied the relation `r`.

More precisely, the `contravariant_class` is a class taking two Types `M N`, together with an
"action" `μ : M → N → N` and a relation `r : N → N`.  Its unique field `covtc` is the assertion that
for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
`(μ m n₁, μ m n₂)` obtained from `(n₁, n₂)` by "acting upon it by `m`"", then, the relation `r`
also holds for the pair `(n₁, n₂)`.

If `m : M` and `h : r (μ m n₁) (μ m n₂)`, then `covariant_class.covc m h : r n₁ n₂`.
-/
class contravariant_class :=
(covtc : contravariant M N μ s)

end variants
