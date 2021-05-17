/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Damiano Testa
-/
import algebra.group.defs
import order.basic
/-!
This file begins the splitting of the ordering assumptions from the algebraic assumptions on the
operations in the `ordered_[...]` hierarchy.

The strategy is to introduce two more flexible typeclasses, covariant_class and contravariant_class.

* covariant_class models the implication a ≤ b → c * a ≤ c * b (multiplication is monotone),
* contravariant_class models the implication a * b < a * c → b < c.

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
-- TODO: relationship with add_con
-- include equivalence of `left_cancel_semigroup` with
-- `semigroup partial_order contravariant_class α α (*) (≤)`?
-- use ⇒, as per Eric's suggestion?
section variants

variables {M N : Type*} (μ : M → N → N) (r : N → N → Prop) (m : M) {a b c : N}


variables (M N)
/-- `covariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `covariant_class` doc-string for its meaning. -/
def covariant     : Prop := ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)

/-- `contravariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `contravariant_class` doc-string for its meaning. -/
def contravariant : Prop := ∀ (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) → r n₁ n₂

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

If `m : M` and `h : r (μ m n₁) (μ m n₂)`, then `contravariant_class.covtc m h : r n₁ n₂`.
-/
class contravariant_class :=
(covtc : contravariant M N μ r)

lemma covariant_le_iff_contravariant_lt [linear_order N] :
  covariant M N μ (≤) ↔ contravariant M N μ (<) :=
⟨ λ h a b c bc, not_le.mp (λ k, not_le.mpr bc (h _ k)),
  λ h a b c bc, not_lt.mp (λ k, not_lt.mpr bc (h _ k))⟩

lemma covariant_lt_iff_contravariant_le [linear_order N] :
  covariant M N μ (<) ↔ contravariant M N μ (≤) :=
⟨ λ h a b c bc, not_lt.mp (λ k, not_lt.mpr bc (h _ k)),
  λ h a b c bc, not_le.mp (λ k, not_le.mpr bc (h _ k))⟩

@[to_additive]
lemma covariant_iff_covariant_mul [comm_semigroup N] :
  covariant N N (*) (r) ↔ covariant N N (flip (*)) (r) :=
by rw function.is_symm_op.flip_eq

@[to_additive]
lemma contravariant_mul_iff_flip [comm_semigroup N] :
  contravariant N N (*) (r) ↔ contravariant N N (flip (*)) (r) :=
by rw function.is_symm_op.flip_eq

@[to_additive]
instance covariant_mul_le.to_contravariant_lt_mul [has_mul N] [linear_order N]
  [covariant_class N N (*) (≤)] : contravariant_class N N (*) (<) :=
{ covtc := (covariant_le_iff_contravariant_lt N N (*)).mp covariant_class.covc }

@[to_additive]
instance covariant_mul_le_left.to_covariant_mul_le_right [comm_semigroup N] [has_le N]
  [covariant_class N N (*) (≤)] : covariant_class N N (function.swap (*)) (≤) :=
{ covc := (covariant_iff_covariant_mul N (≤)).mp covariant_class.covc }

@[to_additive]
instance covariant_mul_lt_left.to_covariant_mul_lt_right [comm_semigroup N] [has_lt N]
  [covariant_class N N (*) (<)] : covariant_class N N (function.swap (*)) (<) :=
{ covc := (covariant_iff_covariant_mul N (<)).mp covariant_class.covc }


variables {M N}
section has_mul
variables (a) [has_mul N]

section has_le
variables [has_le N]

@[to_additive]
lemma mul_le_mul_left_n [covariant_class N N (*) (≤)] (bc : b ≤ c) :
  a * b ≤ a * c :=
covariant_class.covc _ bc

@[to_additive]
lemma le_of_mul_le_mul_left_n [contravariant_class N N (*) (≤)]
  (bc : a * b ≤ a * c) :
  b ≤ c :=
contravariant_class.covtc _ bc

@[to_additive]
lemma mul_le_mul_right_n [covariant_class N N (function.swap (*)) (≤)]
  (bc : b ≤ c) :
  b * a ≤ c * a :=
covariant_class.covc a bc

@[to_additive]
lemma le_of_mul_le_mul_right_n [contravariant_class N N (function.swap (*)) (≤)]
  (bc : b * a ≤ c * a) :
  b ≤ c :=
contravariant_class.covtc a bc

end has_le

section has_lt
variables (a) [has_lt N]

@[to_additive]
lemma mul_lt_mul_left_n [covariant_class N N (*) (<)] (bc : b < c) :
  a * b < a * c :=
covariant_class.covc _ bc

@[to_additive]
lemma lt_of_mul_lt_mul_left_n [contravariant_class N N (*) (<)] (bc : a * b < a * c) :
  b < c :=
contravariant_class.covtc _ bc

@[to_additive]
lemma mul_lt_mul_right_n [covariant_class N N (function.swap (*)) (<)]
  (bc : b < c) :
  b * a < c * a :=
covariant_class.covc a bc

@[to_additive]
lemma lt_of_mul_lt_mul_right_n [contravariant_class N N (function.swap (*)) (<)]
  (bc : b * a < c * a) :
  b < c :=
contravariant_class.covtc a bc

end has_lt

end has_mul

@[to_additive]
instance left_cancel_semigroup.to_covariant_mul_le_left [left_cancel_semigroup N]  [partial_order N]
  [covariant_class N N ((*)) (≤)] :
  covariant_class N N ((*)) (<) :=
{ covc := λ a b c bc, by { cases lt_iff_le_and_ne.mp bc with bc cb,
    exact lt_iff_le_and_ne.mpr ⟨mul_le_mul_left_n a bc, (mul_ne_mul_right a).mpr cb⟩ } }
/-
instance left_cancel_semigroup.to_covariant_mul_le_left [left_cancel_semigroup N]  [preorder N]
  [covariant_class N N ((*)) (≤)] :
  covariant_class N N ((*)) (<) :=
{ covc := λ a b c bc, by {
  cases lt_iff_le_not_le.mp bc with bc cb,
  refine lt_iff_le_not_le.mpr _,
  refine ⟨mul_le_mul_left_n a bc, _⟩,

} }
-/

/- This is not instance, since we want to have an instance from `left_cancel_semigroup`s
to the appropriate `covariant_class`. -/
@[to_additive
"An additive semigroup with a partial order and satisfying `left_cancel_add_semigroup`
(i.e. `c + a < c + b → a < b`) is a `left_cancel add_semigroup`."]
def contravariant.to_left_cancel_semigroup [semigroup N] [partial_order N]
  [contravariant_class N N ((*) : N → N → N) (≤)] :
  left_cancel_semigroup N :=
{ mul_left_cancel := λ a b c bc,
    (le_of_mul_le_mul_left_n a bc.le).antisymm (le_of_mul_le_mul_left_n a bc.ge),
  ..(infer_instance : semigroup N) }

/- This is not instance, since we want to have an instance from `right_cancel_semigroup`s
to the appropriate `covariant_class`. -/
/--  A semigroup with a partial order and satisfying `right_cancel_semigroup`
(i.e. `a * c < b * c → a < b`) is a `right_cancel semigroup`. -/
@[to_additive
"An additive semigroup with a partial order and satisfying `right_cancel_add_semigroup`
(`a + c < b + c → a < b`) is a `right_cancel add_semigroup`."]
def contravariant.to_right_cancel_semigroup [semigroup N] [partial_order N]
  [contravariant_class N N (function.swap (*) : N → N → N) (≤)] :
  right_cancel_semigroup N :=
{ mul_right_cancel := λ a b c bc,
    le_antisymm (le_of_mul_le_mul_right_n b bc.le) (le_of_mul_le_mul_right_n b bc.ge)
  ..(infer_instance : semigroup N) }

end variants

variables {α : Type*} {a b c d : α}

section left
variables [preorder α]

section has_mul
variables [has_mul α]

@[to_additive lt_of_add_lt_add_left]
lemma lt_of_mul_lt_mul_left' [contravariant_class α α (*) (<)] :
  a * b < a * c → b < c :=
contravariant_class.covtc a

variable [covariant_class α α (*) (≤)]

@[to_additive]
lemma mul_le_mul_left' (h : a ≤ b) (c) :
  c * a ≤ c * b :=
covariant_class.covc c h

@[to_additive]
lemma mul_lt_of_mul_lt_left (h : a * b < c) (hle : d ≤ b) :
  a * d < c :=
(mul_le_mul_left_n a hle).trans_lt h

@[to_additive]
lemma mul_le_of_mul_le_left (h : a * b ≤ c) (hle : d ≤ b) :
  a * d ≤ c :=
(mul_le_mul_left_n a hle).trans h

@[to_additive]
lemma lt_mul_of_lt_mul_left (h : a < b * c) (hle : c ≤ d) :
  a < b * d :=
h.trans_le (mul_le_mul_left_n b hle)

@[to_additive]
lemma le_mul_of_le_mul_left (h : a ≤ b * c) (hle : c ≤ d) :
  a ≤ b * d :=
h.trans (mul_le_mul_left_n b hle)

end has_mul

-- here we start using properties of one.
section mul_one_class
variables [mul_one_class α] [covariant_class α α (*) (≤)]

@[to_additive le_add_of_nonneg_right]
lemma le_mul_of_one_le_right' (h : 1 ≤ b) : a ≤ a * b :=
by simpa only [mul_one] using mul_le_mul_left_n a h

@[to_additive add_le_of_nonpos_right]
lemma mul_le_of_le_one_right' (h : b ≤ 1) : a * b ≤ a :=
by simpa only [mul_one] using mul_le_mul_left_n a h

@[to_additive]
lemma lt_of_mul_lt_of_one_le_left (h : a * b < c) (hle : 1 ≤ b) : a < c :=
(le_mul_of_one_le_right' hle).trans_lt h

@[to_additive]
lemma le_of_mul_le_of_one_le_left (h : a * b ≤ c) (hle : 1 ≤ b) : a ≤ c :=
(le_mul_of_one_le_right' hle).trans h

@[to_additive]
lemma lt_of_lt_mul_of_le_one_left (h : a < b * c) (hle : c ≤ 1) : a < b :=
h.trans_le (mul_le_of_le_one_right' hle)

@[to_additive]
lemma le_of_le_mul_of_le_one_left (h : a ≤ b * c) (hle : c ≤ 1) : a ≤ b :=
h.trans (mul_le_of_le_one_right' hle)

end mul_one_class

end left

section right

section preorder
variables [preorder α]

section has_mul
variables [has_mul α]

@[to_additive lt_of_add_lt_add_right]
lemma lt_of_mul_lt_mul_right' [contravariant_class α α (function.swap (*)) (<)]
  (h : a * b < c * b) :
  a < c :=
contravariant_class.covtc b h

variable  [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma mul_le_mul_right' (h : a ≤ b) (c) :
  a * c ≤ b * c :=
covariant_class.covc c h

@[to_additive]
lemma mul_lt_of_mul_lt_right (h : a * b < c) (hle : d ≤ a) :
  d * b < c :=
(mul_le_mul_right_n b hle).trans_lt h

@[to_additive]
lemma mul_le_of_mul_le_right (h : a * b ≤ c) (hle : d ≤ a) :
  d * b ≤ c :=
(mul_le_mul_right_n b hle).trans h

@[to_additive]
lemma lt_mul_of_lt_mul_right (h : a < b * c) (hle : b ≤ d) :
  a < d * c :=
h.trans_le (mul_le_mul_right_n c hle)

@[to_additive]
lemma le_mul_of_le_mul_right (h : a ≤ b * c) (hle : b ≤ d) :
  a ≤ d * c :=
h.trans (mul_le_mul_right_n c hle)

end has_mul

-- here we start using properties of one.
section mul_one_class
variables [mul_one_class α] [covariant_class α α (function.swap (*)) (≤)]

@[to_additive le_add_of_nonneg_left]
lemma le_mul_of_one_le_left' (h : 1 ≤ b) : a ≤ b * a :=
by simpa only [one_mul] using mul_le_mul_right_n a h

@[to_additive add_le_of_nonpos_left]
lemma mul_le_of_le_one_left' (h : b ≤ 1) : b * a ≤ a :=
by simpa only [one_mul] using mul_le_mul_right_n a h

@[to_additive]
lemma lt_of_mul_lt_of_one_le_right (h : a * b < c) (hle : 1 ≤ a) : b < c :=
(le_mul_of_one_le_left' hle).trans_lt h

@[to_additive]
lemma le_of_mul_le_of_one_le_right (h : a * b ≤ c) (hle : 1 ≤ a) : b ≤ c :=
(le_mul_of_one_le_left' hle).trans h

@[to_additive]
lemma lt_of_lt_mul_of_le_one_right (h : a < b * c) (hle : b ≤ 1) : a < c :=
h.trans_le (mul_le_of_le_one_left' hle)

@[to_additive]
lemma le_of_le_mul_of_le_one_right (h : a ≤ b * c) (hle : b ≤ 1) : a ≤ c :=
h.trans (mul_le_of_le_one_left' hle)

end mul_one_class

end preorder

end right

section preorder
variables [preorder α]

section has_mul_left_right
variables [has_mul α]
  [covariant_class α α ((*)) (≤)] [covariant_class α α (function.swap (*)) (≤)]

@[to_additive add_le_add]
lemma mul_le_mul' (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
(mul_le_mul_left_n _ h₂).trans (mul_le_mul_right_n d h₁)

@[to_additive]
lemma mul_le_mul_three {e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) : a * b * c ≤ d * e * f :=
mul_le_mul' (mul_le_mul' h₁ h₂) h₃

end has_mul_left_right

-- here we start using properties of one.
section mul_one_class_left_right
variables [mul_one_class α]

section covariant
variable  [covariant_class α α (*) (≤)]

@[to_additive add_pos_of_pos_of_nonneg]
lemma one_lt_mul_of_lt_of_le' (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
lt_of_lt_of_le ha $ le_mul_of_one_le_right' hb

@[to_additive add_pos]
lemma one_lt_mul' (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
one_lt_mul_of_lt_of_le' ha hb.le

@[to_additive]
lemma lt_mul_of_lt_of_one_le' (hbc : b < c) (ha : 1 ≤ a) :
  b < c * a :=
hbc.trans_le $ le_mul_of_one_le_right' ha

@[to_additive]
lemma lt_mul_of_lt_of_one_lt' (hbc : b < c) (ha : 1 < a) :
  b < c * a :=
lt_mul_of_lt_of_one_le' hbc ha.le

end covariant

section contravariant
variable [covariant_class α α (function.swap (*)) (≤)]

@[to_additive add_pos_of_nonneg_of_pos]
lemma one_lt_mul_of_le_of_lt' (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
lt_of_lt_of_le hb $ le_mul_of_one_le_left' ha

@[to_additive]
lemma lt_mul_of_one_le_of_lt' (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
hbc.trans_le $ le_mul_of_one_le_left' ha

@[to_additive]
lemma lt_mul_of_one_lt_of_lt' (ha : 1 < a) (hbc : b < c) : b < a * c :=
lt_mul_of_one_le_of_lt' ha.le hbc

end contravariant

variables [covariant_class α α (*) (≤)]
  [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma le_mul_of_one_le_of_le (ha : 1 ≤ a) (hbc : b ≤ c) : b ≤ a * c :=
one_mul b ▸ mul_le_mul' ha hbc

@[to_additive]
lemma le_mul_of_le_of_one_le (hbc : b ≤ c) (ha : 1 ≤ a) : b ≤ c * a :=
mul_one b ▸ mul_le_mul' hbc ha

@[to_additive add_nonneg]
lemma one_le_mul (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
le_mul_of_one_le_of_le ha hb

@[to_additive add_nonpos]
lemma mul_le_one' (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
one_mul (1:α) ▸ (mul_le_mul' ha hb)

@[to_additive]
lemma mul_le_of_le_one_of_le' (ha : a ≤ 1) (hbc : b ≤ c) : a * b ≤ c :=
one_mul c ▸ mul_le_mul' ha hbc

@[to_additive]
lemma mul_le_of_le_of_le_one' (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
mul_one c ▸ mul_le_mul' hbc ha

@[to_additive]
lemma mul_lt_one_of_lt_one_of_le_one' (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
(mul_le_of_le_of_le_one' le_rfl hb).trans_lt ha

@[to_additive]
lemma mul_lt_one_of_le_one_of_lt_one' (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
(mul_le_of_le_one_of_le' ha le_rfl).trans_lt hb

@[to_additive]
lemma mul_lt_one' (ha : a < 1) (hb : b < 1) : a * b < 1 :=
mul_lt_one_of_le_one_of_lt_one' ha.le hb

@[to_additive]
lemma mul_lt_of_le_one_of_lt' (ha : a ≤ 1) (hbc : b < c) : a * b < c :=
lt_of_le_of_lt (mul_le_of_le_one_of_le' ha le_rfl) hbc

@[to_additive]
lemma mul_lt_of_lt_of_le_one' (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
lt_of_le_of_lt (mul_le_of_le_of_le_one' le_rfl ha) hbc

@[to_additive]
lemma mul_lt_of_lt_one_of_lt' (ha : a < 1) (hbc : b < c) : a * b < c :=
mul_lt_of_le_one_of_lt' ha.le hbc

@[to_additive]
lemma mul_lt_of_lt_of_lt_one' (hbc : b < c) (ha : a < 1) : b * a < c :=
mul_lt_of_lt_of_le_one' hbc ha.le

end mul_one_class_left_right

end preorder

section partial_order
variables [mul_one_class α] [partial_order α]
  [covariant_class α α (*) (≤)] [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma mul_eq_one_iff' (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
iff.intro
  (assume hab : a * b = 1,
   have a ≤ 1, from hab ▸ le_mul_of_le_of_one_le le_rfl hb,
   have a = 1, from le_antisymm this ha,
   have b ≤ 1, from hab ▸ le_mul_of_one_le_of_le ha le_rfl,
   have b = 1, from le_antisymm this hb,
   and.intro ‹a = 1› ‹b = 1›)
  (assume ⟨ha', hb'⟩, by rw [ha', hb', mul_one])

section mono
variables {β : Type*} [preorder β] {f g : β → α}

@[to_additive monotone.add]
lemma monotone.mul' (hf : monotone f) (hg : monotone g) : monotone (λ x, f x * g x) :=
λ x y h, mul_le_mul' (hf h) (hg h)

@[to_additive monotone.add_const]
lemma monotone.mul_const' (hf : monotone f) (a : α) : monotone (λ x, f x * a) :=
hf.mul' monotone_const

@[to_additive monotone.const_add]
lemma monotone.const_mul' (hf : monotone f) (a : α) : monotone (λ x, a * f x) :=
monotone_const.mul' hf

end mono

end partial_order

@[to_additive le_of_add_le_add_left]
lemma le_of_mul_le_mul_left' [left_cancel_semigroup α] [partial_order α]
  [contravariant_class α α (*) (<)]
  {a b c : α} (bc : a * b ≤ a * c) :
  b ≤ c :=
begin
  cases le_iff_eq_or_lt.mp bc,
  { exact le_iff_eq_or_lt.mpr (or.inl ((mul_right_inj a).mp h)) },
  { exact (lt_of_mul_lt_mul_left' h).le }
end

@[to_additive le_of_add_le_add_right]
lemma le_of_mul_le_mul_right' [partial_order α] [right_cancel_semigroup α]
  [contravariant_class α α (function.swap (*)) (<)]
  {a b c : α} (bc : b * a ≤ c * a) :
  b ≤ c :=
begin
  cases le_iff_eq_or_lt.mp bc,
  { exact le_iff_eq_or_lt.mpr (or.inl ((mul_left_inj a).mp h)) },
  { exact (lt_of_mul_lt_mul_right_n _ h).le }
end

variable [partial_order α]

section left_co_co
variables [left_cancel_monoid α]
  [covariant_class α α (*) (≤)]
  [contravariant_class α α (*) (<)]

@[to_additive]
lemma mul_lt_mul_left' (h : a < b) (c : α) : c * a < c * b :=
lt_of_le_not_le (mul_le_mul_left' h.le _)
  (λ j, not_le_of_gt h (le_of_mul_le_mul_left' j))

/-  Why is this instance not available? -/
--/-
@[to_additive]
instance mul_mul_left {α : Type*} [left_cancel_monoid α] [partial_order α]
  [contravariant_class α α (*) (<)] :
  contravariant_class α α (*) (≤) :=
{ covtc :=  by { intros a b c bc,
      cases le_iff_eq_or_lt.mp bc with h h,
      { exact (left_cancel_monoid.mul_left_cancel a b c h).le },
      { exact (lt_of_mul_lt_mul_left_n a h).le } } }

@[to_additive]
instance mul_mul_right {α : Type*} [right_cancel_monoid α] [partial_order α]
  [contravariant_class α α (function.swap (*)) (<)] :
  contravariant_class α α (function.swap (*)) (≤) :=
{ covtc :=  by { intros a b c bc,
      cases le_iff_eq_or_lt.mp bc with h h,
      { exact ((mul_left_inj a).mp h).le },
      { exact (lt_of_mul_lt_mul_right_n a h).le } } }

--/
/-
lemma add_le_add_iff_left {α : Type*} [add_left_cancel_monoid α] [partial_order α]
   [covariant_class α α (+) (≤)] [contravariant_class α α (+) (<)]
 (a : α) {b c : α} : a + b ≤ a + c ↔ b ≤ c :=
⟨λ h, le_of_add_le_add_left a h, λ h, add_le_add_left a h⟩
--/


@[simp, to_additive]
lemma mul_le_mul_iff_left (a : α) {b c : α} : a * b ≤ a * c ↔ b ≤ c :=
⟨λ h, le_of_mul_le_mul_left_n _ h, λ h, mul_le_mul_left_n a h⟩

@[to_additive lt_add_of_pos_right]
lemma lt_mul_of_one_lt_right' (a : α) {b : α} (h : 1 < b) : a < a * b :=
have a * 1 < a * b, from mul_lt_mul_left' h a,
by rwa [mul_one] at this

@[simp, to_additive]
lemma mul_lt_mul_iff_left (a : α) {b c : α} : a * b < a * c ↔ b < c :=
⟨lt_of_mul_lt_mul_left_n a, λ h, mul_lt_mul_left' h a⟩

@[simp, to_additive le_add_iff_nonneg_right]
lemma le_mul_iff_one_le_right' (a : α) {b : α} : a ≤ a * b ↔ 1 ≤ b :=
have a * 1 ≤ a * b ↔ 1 ≤ b, from mul_le_mul_iff_left a,
by rwa mul_one at this

@[simp, to_additive lt_add_iff_pos_right]
lemma lt_mul_iff_one_lt_right' (a : α) {b : α} : a < a * b ↔ 1 < b :=
have a * 1 < a * b ↔ 1 < b, from mul_lt_mul_iff_left a,
by rwa mul_one at this

@[simp, to_additive add_le_iff_nonpos_right]
lemma mul_le_iff_le_one_right' : a * b ≤ a ↔ b ≤ 1 :=
by { convert mul_le_mul_iff_left a, rw [mul_one] }

@[simp, to_additive add_lt_iff_neg_left]
lemma mul_lt_iff_lt_one_left' : a * b < a ↔ b < 1 :=
by { convert mul_lt_mul_iff_left a, rw [mul_one] }

end left_co_co

section right_cos_cos

variables [right_cancel_monoid α]
  [covariant_class α α (function.swap (*)) (≤)]
  [contravariant_class α α (function.swap (*)) (<)]

@[to_additive]
lemma mul_lt_mul_of_right (h : a < b) (c : α) : a * c < b * c :=
(mul_le_mul_right' h.le _).lt_of_not_le
  (λ j, not_le_of_gt h (le_of_mul_le_mul_right' j))

@[to_additive lt_add_of_pos_left]
lemma lt_mul_of_one_lt_left' (a : α) {b : α} (h : 1 < b) : a < b * a :=
have 1 * a < b * a, from mul_lt_mul_of_right h a,
by rwa [one_mul] at this

@[simp, to_additive]
lemma mul_le_mul_iff_right (c : α) : a * c ≤ b * c ↔ a ≤ b :=
⟨le_of_mul_le_mul_right_n _, λ h, mul_le_mul_right_n _ h⟩

@[simp, to_additive]
lemma mul_lt_mul_iff_right (c : α) : a * c < b * c ↔ a < b :=
⟨lt_of_mul_lt_mul_right_n _, λ h, mul_lt_mul_of_right h c⟩

@[simp, to_additive le_add_iff_nonneg_left]
lemma le_mul_iff_one_le_left' (a : α) {b : α} : a ≤ b * a ↔ 1 ≤ b :=
have 1 * a ≤ b * a ↔ 1 ≤ b, from mul_le_mul_iff_right a,
by rwa one_mul at this

@[simp, to_additive lt_add_iff_pos_left]
lemma lt_mul_iff_one_lt_left' (a : α) {b : α} : a < b * a ↔ 1 < b :=
have 1 * a < b * a ↔ 1 < b, from mul_lt_mul_iff_right a,
by rwa one_mul at this

@[simp, to_additive add_le_iff_nonpos_left]
lemma mul_le_iff_le_one_left' : a * b ≤ b ↔ a ≤ 1 :=
by { convert mul_le_mul_iff_right b, rw [one_mul] }

@[simp, to_additive add_lt_iff_neg_right]
lemma mul_lt_iff_lt_one_right' : a * b < b ↔ a < 1 :=
by { convert mul_lt_mul_iff_right b, rw [one_mul] }

end right_cos_cos

section right_co_cos

variables [right_cancel_monoid α]
  [covariant_class α α (*) (≤)]
  [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma mul_lt_mul_of_lt_of_le (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
lt_of_lt_of_le ((mul_le_mul_right_n c h₁.le).lt_of_ne (λ h, h₁.ne ((mul_left_inj c).mp h)))
  (mul_le_mul_left_n b h₂)

@[to_additive]
lemma mul_lt_one_of_lt_one_of_le_one (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul_of_lt_of_le ha hb)

@[to_additive]
lemma lt_mul_of_one_lt_of_le (ha : 1 < a) (hbc : b ≤ c) : b < a * c :=
one_mul b ▸ mul_lt_mul_of_lt_of_le ha hbc

@[to_additive]
lemma mul_le_of_le_one_of_le (ha : a ≤ 1) (hbc : b ≤ c) : a * b ≤ c :=
one_mul c ▸ mul_le_mul' ha hbc

@[to_additive]
lemma mul_le_of_le_of_le_one (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
mul_one c ▸ mul_le_mul' hbc ha

@[to_additive]
lemma mul_lt_of_lt_one_of_le (ha : a < 1) (hbc : b ≤ c) : a * b < c :=
one_mul c ▸ mul_lt_mul_of_lt_of_le ha hbc

@[to_additive]
lemma lt_mul_of_lt_of_one_le (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
mul_one b ▸ mul_lt_mul_of_lt_of_le hbc ha

@[to_additive]
lemma mul_lt_of_lt_of_le_one (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
mul_one c ▸ mul_lt_mul_of_lt_of_le hbc ha

end right_co_cos

variables [cancel_monoid α]
  [covariant_class α α (*) (≤)]
  [contravariant_class α α (*) (<)]
  [covariant_class α α (function.swap (*)) (≤)]

section special

@[to_additive]
lemma mul_lt_mul_of_le_of_lt (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
(mul_le_mul_right_n _ h₁).trans_lt (mul_lt_mul_left' h₂ b)

@[to_additive]
lemma mul_lt_one_of_le_one_of_lt_one (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul_of_le_of_lt ha hb)

@[to_additive]
lemma lt_mul_of_le_of_one_lt (hbc : b ≤ c) (ha : 1 < a) : b < c * a :=
mul_one b ▸ mul_lt_mul_of_le_of_lt hbc ha

@[to_additive]
lemma mul_lt_of_le_of_lt_one (hbc : b ≤ c) (ha : a < 1) : b * a < c :=
mul_one c ▸ mul_lt_mul_of_le_of_lt hbc ha

@[to_additive]
lemma lt_mul_of_one_le_of_lt (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
one_mul b ▸ mul_lt_mul_of_le_of_lt ha hbc

@[to_additive]
lemma mul_lt_of_le_one_of_lt (ha : a ≤ 1) (hbc : b < c) : a * b < c :=
one_mul c ▸ mul_lt_mul_of_le_of_lt ha hbc

end special

variables [contravariant_class α α (function.swap (*)) (<)]

@[to_additive add_lt_add]
lemma mul_lt_mul''' (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
(mul_lt_mul_of_right h₁ c).trans (mul_lt_mul_left' h₂ b)

@[to_additive]
lemma mul_eq_one_iff_eq_one_of_one_le
  (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
⟨λ hab : a * b = 1,
by split; apply le_antisymm; try {assumption};
   rw ← hab; simp [ha, hb],
λ ⟨ha', hb'⟩, by rw [ha', hb', mul_one]⟩

@[to_additive]
lemma mul_lt_one (ha : a < 1) (hb : b < 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul''' ha hb)

@[to_additive]
lemma lt_mul_of_one_lt_of_lt (ha : 1 < a) (hbc : b < c) : b < a * c :=
one_mul b ▸ mul_lt_mul''' ha hbc

@[to_additive]
lemma lt_mul_of_lt_of_one_lt (hbc : b < c) (ha : 1 < a) : b < c * a :=
mul_one b ▸ mul_lt_mul''' hbc ha

@[to_additive]
lemma mul_lt_of_lt_one_of_lt (ha : a < 1) (hbc : b < c) : a * b < c :=
one_mul c ▸ mul_lt_mul''' ha hbc

@[to_additive]
lemma mul_lt_of_lt_of_lt_one (hbc : b < c) (ha : a < 1) : b * a < c :=
mul_one c ▸ mul_lt_mul''' hbc ha
