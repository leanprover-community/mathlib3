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

variables {M N : Type*} (μ : M → N → N) (r : N → N → Prop)


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
class covariant_class : Prop :=
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
class contravariant_class : Prop :=
(covtc : contravariant M N μ r)

lemma rel_iff_cov [covariant_class M N μ r] [contravariant_class M N μ r] (m : M) {a b : N} :
  r (μ m a) (μ m b) ↔ r a b :=
⟨contravariant_class.covtc _,covariant_class.covc _⟩

section covariant
variables {M N μ r} [covariant_class M N μ r]

lemma act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) :
  r (μ m a) (μ m b) :=
covariant_class.covc _ ab

section is_trans
variables [is_trans N r] (m n : M) {a b c d : N}

/-  Lemmas with 3 elements. -/
lemma act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) :
  r (μ m a) c :=
trans (act_rel_act_of_rel m ab) rl

lemma rel_act_of_rel_of_rel_act (ab : r a b) (rr : r c (μ m a)) :
  r c (μ m b) :=
trans rr (act_rel_act_of_rel _ ab)

end is_trans

end covariant

/-  Lemma with 4 elements. -/
section M_eq_N
variables {M N μ r} {mu : N → N → N} [is_trans N r]
  [covariant_class N N mu r] [covariant_class N N (function.swap mu) r] {a b c d : N}

lemma act_rel_act_of_rel_of_rel (ab : r a b) (cd : r c d) :
  r (mu a c) (mu b d) :=
trans (act_rel_act_of_rel c ab : _) (act_rel_act_of_rel b cd)

end M_eq_N

section contravariant
variables {M N μ r} [contravariant_class M N μ r]

lemma rel_of_act_rel_act (m : M) {a b : N} (ab : r (μ m a) (μ m b)) :
  r a b :=
contravariant_class.covtc _ ab

section is_trans
variables [is_trans N r] (m n : M) {a b c d : N}

/-  Lemmas with 3 elements. -/
lemma act_rel_of_act_rel_of_rel_act_rel (ab : r (μ m a) b) (rl : r (μ m b) (μ m c)) :
  r (μ m a) c :=
trans ab (rel_of_act_rel_act m rl)

lemma rel_act_of_act_rel_act_of_rel_act (ab : r (μ m a) (μ m b)) (rr : r b (μ m c)) :
  r a (μ m c) :=
trans (rel_of_act_rel_act m ab) rr

end is_trans

/-  Lemmas with 4 elements.
section M_eq_N
variables {M N μ r} {mu : N → N → N} [is_trans N r]
  [contravariant_class N N mu r] [contravariant_class N N (function.swap mu) r] {a b c d : N}

lemma act_rel_act_of_rel_of_rel (cd : r (mu a c) (mu a d)) (rr : r (mu a c) (mu b d)) :
  r a b :=
begin

end
--trans (act_rel_act_of_rel c ab : _) (act_rel_act_of_rel b cd)

end M_eq_N
 -/

end contravariant

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

@[to_additive]
instance left_cancel_semigroup.to_covariant_mul_le_left [left_cancel_semigroup N] [partial_order N]
  [covariant_class N N (*) (≤)] :
  covariant_class N N (*) (<) :=
{ covc := λ a b c bc, by { cases lt_iff_le_and_ne.mp bc with bc cb,
    exact lt_iff_le_and_ne.mpr ⟨covariant_class.covc a bc, (mul_ne_mul_right a).mpr cb⟩ } }

@[to_additive]
instance right_cancel_semigroup.to_covariant_mul_le_right [right_cancel_semigroup N]
  [partial_order N] [covariant_class N N (function.swap (*)) (≤)] :
  covariant_class N N (function.swap (*)) (<) :=
{ covc := λ a b c bc, by { cases lt_iff_le_and_ne.mp bc with bc cb,
    exact lt_iff_le_and_ne.mpr ⟨covariant_class.covc a bc, (mul_ne_mul_left a).mpr cb⟩ } }

@[to_additive]
instance left_cancel_semigroup.to_contravariant_mul_lt [left_cancel_semigroup N] [partial_order N]
  [contravariant_class N N (*) (<)] :
  contravariant_class N N (*) (≤) :=
{ covtc :=  λ  a b c bc, by { cases le_iff_eq_or_lt.mp bc with h h,
      { exact ((mul_right_inj a).mp h).le },
      { exact (contravariant_class.covtc _ h).le } } }

@[to_additive]
instance right_cancel_semigroup.to_contravariant_mul_lt {α : Type*} [right_cancel_semigroup α]
  [partial_order α] [contravariant_class α α (function.swap (*)) (<)] :
  contravariant_class α α (function.swap (*)) (≤) :=
{ covtc :=  λ a b c bc, by { cases le_iff_eq_or_lt.mp bc with h h,
      { exact ((mul_left_inj a).mp h).le },
      { exact (contravariant_class.covtc _ h).le } } }

variables {M N}
section has_mul
variables [has_mul N]

section has_le
variables [has_le N]

@[simp, to_additive]
lemma mul_le_mul_iff_left [covariant_class N N (*) (≤)] [contravariant_class N N (*) (≤)]
  (a : N) {b c : N} :
  a * b ≤ a * c ↔ b ≤ c :=
rel_iff_cov N N (*) (≤) a

@[simp, to_additive]
lemma mul_le_mul_iff_right
  [covariant_class N N (function.swap (*)) (≤)] [contravariant_class N N (function.swap (*)) (≤)]
  (a : N) {b c : N} :
  b * a ≤ c * a ↔ b ≤ c :=
rel_iff_cov N N (function.swap (*)) (≤) a

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive add_le_add_left]
lemma mul_le_mul_left' [covariant_class N N (*) (≤)] {b c : N} (bc : b ≤ c) (a : N) :
  a * b ≤ a * c :=
covariant_class.covc _ bc

@[to_additive le_of_add_le_add_left]
lemma le_of_mul_le_mul_left' [contravariant_class N N (*) (≤)]
  {a b c : N} (bc : a * b ≤ a * c) :
  b ≤ c :=
contravariant_class.covtc _ bc

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive add_le_add_right]
lemma mul_le_mul_right' [covariant_class N N (function.swap (*)) (≤)]
  {b c : N} (bc : b ≤ c) (a : N) :
  b * a ≤ c * a :=
covariant_class.covc a bc

@[to_additive le_of_add_le_add_right]
lemma le_of_mul_le_mul_right' [contravariant_class N N (function.swap (*)) (≤)]
  {a b c : N} (bc : b * a ≤ c * a) :
  b ≤ c :=
contravariant_class.covtc a bc

end has_le

section has_lt
variables [has_lt N]

@[simp, to_additive]
lemma mul_lt_mul_iff_left [covariant_class N N (*) (<)] [contravariant_class N N (*) (<)]
  (a : N) {b c : N} :
  a * b < a * c ↔ b < c :=
rel_iff_cov N N (*) (<) a

@[simp, to_additive]
lemma mul_lt_mul_iff_right
  [covariant_class N N (function.swap (*)) (<)] [contravariant_class N N (function.swap (*)) (<)]
  (a : N) {b c : N} :
  b * a < c * a ↔ b < c :=
rel_iff_cov N N (function.swap (*)) (<) a

@[to_additive add_lt_add_left]
lemma mul_lt_mul_left' [covariant_class N N (*) (<)] {b c : N} (bc : b < c) (a : N) :
  a * b < a * c :=
covariant_class.covc _ bc

@[to_additive lt_of_add_lt_add_left]
lemma lt_of_mul_lt_mul_left' [contravariant_class N N (*) (<)]
  {a b c : N} (bc : a * b < a * c) :
  b < c :=
contravariant_class.covtc _ bc

@[to_additive add_lt_add_right]
lemma mul_lt_mul_right' [covariant_class N N (function.swap (*)) (<)]
  {b c : N} (bc : b < c) (a : N) :
  b * a < c * a :=
covariant_class.covc a bc

@[to_additive lt_of_add_lt_add_right]
lemma lt_of_mul_lt_mul_right' [contravariant_class N N (function.swap (*)) (<)]
  {a b c : N} (bc : b * a < c * a) :
  b < c :=
contravariant_class.covtc a bc

end has_lt

end has_mul

-- using one
section mul_one_class
variables [mul_one_class N]

section has_le
variables [has_le N]

@[simp, to_additive le_add_iff_nonneg_right]
lemma le_mul_iff_one_le_right'
  [covariant_class N N (*) (≤)] [contravariant_class N N (*) (≤)]
  (a : N) {b : N} : a ≤ a * b ↔ 1 ≤ b :=
iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[simp, to_additive add_le_iff_nonpos_right]
lemma mul_le_iff_le_one_right'
  [covariant_class N N (*) (≤)] [contravariant_class N N (*) (≤)]
  (a : N) {b : N} :
  a * b ≤ a ↔ b ≤ 1 :=
iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[simp, to_additive le_add_iff_nonneg_left]
lemma le_mul_iff_one_le_left'
  [covariant_class N N (function.swap (*)) (≤)] [contravariant_class N N (function.swap (*)) (≤)]
  (a : N) {b : N} :
  a ≤ b * a ↔ 1 ≤ b :=
iff.trans (by rw one_mul) (mul_le_mul_iff_right a)

@[simp, to_additive add_le_iff_nonpos_left]
lemma mul_le_iff_le_one_left'
  [covariant_class N N (function.swap (*)) (≤)] [contravariant_class N N (function.swap (*)) (≤)]
  {a b : N} :
  a * b ≤ b ↔ a ≤ 1 :=
iff.trans (by rw one_mul) (mul_le_mul_iff_right b)

end has_le

section has_lt
variable [has_lt N]

@[to_additive lt_add_of_pos_right]
lemma lt_mul_of_one_lt_right'
  [covariant_class N N (*) (<)]
  (a : N) {b : N} (h : 1 < b) : a < a * b :=
calc a = a * 1 : (mul_one _).symm
   ... < a * b : mul_lt_mul_left' h a

@[simp, to_additive lt_add_iff_pos_right]
lemma lt_mul_iff_one_lt_right'
  [covariant_class N N (*) (<)] [contravariant_class N N (*) (<)]
  (a : N) {b : N} :
  a < a * b ↔ 1 < b :=
iff.trans (by rw mul_one) (mul_lt_mul_iff_left a)

@[simp, to_additive add_lt_iff_neg_left]
lemma mul_lt_iff_lt_one_left'
  [covariant_class N N (*) (<)] [contravariant_class N N (*) (<)] {a b : N} :
  a * b < a ↔ b < 1 :=
iff.trans (by rw mul_one) (mul_lt_mul_iff_left a)

@[simp, to_additive lt_add_iff_pos_left]
lemma lt_mul_iff_one_lt_left'
  [covariant_class N N (function.swap (*)) (<)] [contravariant_class N N (function.swap (*)) (<)]
  (a : N) {b : N} : a < b * a ↔ 1 < b :=
iff.trans (by rw one_mul) (mul_lt_mul_iff_right a)

@[simp, to_additive add_lt_iff_neg_right]
lemma mul_lt_iff_lt_one_right'
  [covariant_class N N (function.swap (*)) (<)] [contravariant_class N N (function.swap (*)) (<)]
  {a : N} (b : N) :
  a * b < b ↔ a < 1 :=
iff.trans (by rw one_mul) (mul_lt_mul_iff_right b)

end has_lt

section preorder
variable [preorder N]

@[to_additive]
lemma mul_le_of_le_of_le_one [covariant_class N N (*) (≤)]
  {a b c : N} (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
calc  b * a ≤ b * 1 : mul_le_mul_left' ha b
        ... = b     : mul_one b
        ... ≤ c     : hbc

/-  Lemma stated for preserving an old name. -/
@[to_additive]
lemma mul_le_one' [covariant_class N N (*) (≤)]
  {a b : N} (hbc : b ≤ 1) (ha : a ≤ 1) : b * a ≤ 1 :=
mul_le_of_le_of_le_one hbc ha

@[to_additive]
lemma lt_mul_of_lt_of_one_le [covariant_class N N (*) (≤)]
  {a b c : N} (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
calc  b < c     : hbc
    ... = c * 1 : (mul_one c).symm
    ... ≤ c * a : mul_le_mul_left' ha c

@[to_additive]
lemma mul_lt_of_lt_of_le_one [covariant_class N N (*) (≤)]
  {a b c : N} (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
calc  b * a ≤ b * 1 : mul_le_mul_left' ha b
        ... = b     : mul_one b
        ... < c     : hbc

@[to_additive]
lemma lt_mul_of_le_of_one_lt [covariant_class N N (*) (<)]
  {a b c : N} (hbc : b ≤ c) (ha : 1 < a) : b < c * a :=
calc  b ≤ c     : hbc
    ... = c * 1 : (mul_one c).symm
    ... < c * a : mul_lt_mul_left' ha c

@[to_additive]
lemma mul_lt_of_le_one_of_lt [covariant_class N N (function.swap (*)) (≤)]
  {a b c : N} (ha : a ≤ 1) (hb : b < c) : a * b < c :=
calc  a * b ≤ 1 * b : mul_le_mul_right' ha b
        ... = b     : one_mul b
        ... < c     : hb

@[to_additive]
lemma mul_le_of_le_one_of_le [covariant_class N N (function.swap (*)) (≤)]
  {a b c : N} (ha : a ≤ 1) (hbc : b ≤ c) :
  a * b ≤ c :=
calc  a * b ≤ 1 * b : mul_le_mul_right' ha b
        ... = b     : one_mul b
        ... ≤ c     : hbc

@[to_additive]
lemma le_mul_of_one_le_of_le [covariant_class N N (function.swap (*)) (≤)]
  {a b c: N} (ha : 1 ≤ a) (hbc : b ≤ c) : b ≤ a * c :=
calc  b ≤ c     : hbc
    ... = 1 * c : (one_mul c).symm
    ... ≤ a * c : mul_le_mul_right' ha c

/--
Assume monotonicity on the `left`. The lemma assuming `right` is `right.mul_lt_one`. -/
@[to_additive]
lemma left.mul_lt_one [covariant_class N N (*) (<)]
  {a b : N} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
calc  a * b < a * 1 : mul_lt_mul_left' hb a
        ... = a     : mul_one a
        ... < 1     : ha

/--
Assume monotonicity on the `right`. The lemma assuming `left` is `left.mul_lt_one`. -/
@[to_additive]
lemma right.mul_lt_one [covariant_class N N (function.swap (*)) (<)]
  {a b : N} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
calc  a * b < 1 * b : mul_lt_mul_right' ha b
        ... = b     : one_mul b
        ... < 1     : hb

@[to_additive]
lemma mul_lt_of_le_of_lt_one
  [covariant_class N N (*) (<)] [covariant_class N N (function.swap (*)) (≤)]
  {a b c: N} (hbc : b ≤ c) (ha : a < 1) : b * a < c :=
calc  b * a ≤ c * a : mul_le_mul_right' hbc a
        ... < c * 1 : mul_lt_mul_left' ha c
        ... = c     : mul_one c

@[to_additive]
lemma mul_lt_of_lt_one_of_le [covariant_class N N (function.swap (*)) (<)]
  {a b c : N} (ha : a < 1) (hbc : b ≤ c) : a * b < c :=
calc  a * b < 1 * b : mul_lt_mul_right' ha b
        ... = b     : one_mul b
        ... ≤ c     : hbc

@[to_additive]
lemma lt_mul_of_one_lt_of_le [covariant_class N N (function.swap (*)) (<)]
  {a b c : N} (ha : 1 < a) (hbc : b ≤ c) : b < a * c :=
calc  b ≤ c     : hbc
    ... = 1 * c : (one_mul c).symm
    ... < a * c : mul_lt_mul_right' ha c

/-- Assumes left covariance. -/
@[to_additive]
lemma le_mul_of_le_of_le_one [covariant_class N N (*) (≤)]
  {a b c : N} (ha : c ≤ a) (hb : 1 ≤ b) : c ≤ a * b :=
calc  c ≤ a     : ha
    ... = a * 1 : (mul_one a).symm
    ... ≤ a * b : mul_le_mul_left' hb a

/-  This lemma is present to mimick the name of an existing one. -/
@[to_additive add_nonneg]
lemma one_le_mul {N : Type*} [comm_monoid N] [preorder N] [covariant_class N N (*) (≤)]
  {a b : N} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
le_mul_of_le_of_le_one ha hb

/-- Assumes left covariance. -/
@[to_additive]
lemma lt_mul_of_lt_of_one_lt [covariant_class N N (*) (<)]
  {a b c : N} (ha : c < a) (hb : 1 < b) : c < a * b :=
calc  c < a     : ha
    ... = a * 1 : (mul_one _).symm
    ... < a * b : mul_lt_mul_left' hb a

/-- Assumes left covariance. -/
@[to_additive]
lemma left.mul_lt_one_of_lt_of_lt_one [covariant_class N N (*) (<)]
  {a b c : N} (ha : a < c) (hb : b < 1) : a * b < c :=
calc  a * b < a * 1 : mul_lt_mul_left' hb a
        ... = a     : mul_one a
        ... < c     : ha

/-- Assumes right covariance. -/
@[to_additive]
lemma right.mul_lt_one_of_lt_of_lt_one [covariant_class N N (function.swap (*)) (<)]
  {a b c : N} (ha : a < 1) (hb : b < c) : a * b < c :=
calc  a * b < 1 * b : mul_lt_mul_right' ha b
        ... = b     : one_mul b
        ... < c     : hb

/-- Assumes right covariance. -/
@[to_additive left.add_nonneg]
lemma right.one_le_mul [covariant_class N N (function.swap (*)) (≤)]
  {a b : N} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
calc  1 ≤ b     : hb
    ... = 1 * b : (one_mul b).symm
    ... ≤ a * b : mul_le_mul_right' ha b

/-- Assumes right covariance. -/
@[to_additive right.pos_add]
lemma right.one_lt_mul [covariant_class N N (function.swap (*)) (<)]
  {b : N} (hb : 1 < b) {a: N} (ha : 1 < a) : 1 < a * b :=
calc  1 < b     : hb
    ... = 1 * b : (one_mul _).symm
    ... < a * b : mul_lt_mul_right' ha b


end preorder

end mul_one_class

/- This is not instance, since we want to have an instance from `left_cancel_semigroup`s
to the appropriate `covariant_class`. -/
/--  A semigroup with a partial order and satisfying `left_cancel_semigroup`
(i.e. `a * c < b * c → a < b`) is a `left_cancel semigroup`. -/
@[to_additive
"An additive semigroup with a partial order and satisfying `left_cancel_add_semigroup`
(i.e. `c + a < c + b → a < b`) is a `left_cancel add_semigroup`."]
def contravariant.to_left_cancel_semigroup [semigroup N] [partial_order N]
  [contravariant_class N N ((*) : N → N → N) (≤)] :
  left_cancel_semigroup N :=
{ mul_left_cancel := λ a b c bc,
    (le_of_mul_le_mul_left' bc.le).antisymm (le_of_mul_le_mul_left' bc.ge),
  ..‹semigroup N› }

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
    le_antisymm (le_of_mul_le_mul_right' bc.le) (le_of_mul_le_mul_right' bc.ge)
  ..‹semigroup N› }

end variants

variables {α : Type*} {a b c d : α}

section left
variables [preorder α]

section has_mul
variables [has_mul α]

section contravariant_mul_lt_left_le_right
variables [covariant_class α α (*) (<)] [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma mul_lt_mul_of_le_of_lt
  (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
(mul_le_mul_right' h₁ _).trans_lt (mul_lt_mul_left' h₂ b)


@[to_additive add_lt_add]
lemma mul_lt_mul''' (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
mul_lt_mul_of_le_of_lt h₁.le h₂

end contravariant_mul_lt_left_le_right

variable [covariant_class α α (*) (≤)]

@[to_additive]
lemma mul_lt_of_mul_lt_left (h : a * b < c) (hle : d ≤ b) :
  a * d < c :=
(mul_le_mul_left' hle a).trans_lt h

@[to_additive]
lemma mul_le_of_mul_le_left (h : a * b ≤ c) (hle : d ≤ b) :
  a * d ≤ c :=
--(mul_le_mul_left' hle a).trans h
@act_rel_of_rel_of_act_rel _ _ _ (≤) _ ⟨λ _ _ _, le_trans⟩ a _ _ _ hle h

@[to_additive]
lemma lt_mul_of_lt_mul_left (h : a < b * c) (hle : c ≤ d) :
  a < b * d :=
h.trans_le (mul_le_mul_left' hle b)

@[to_additive]
lemma le_mul_of_le_mul_left (h : a ≤ b * c) (hle : c ≤ d) :
  a ≤ b * d :=
--h.trans (mul_le_mul_left' hle b)
@rel_act_of_rel_of_rel_act _ _ _ (≤) _ ⟨λ _ _ _, le_trans⟩ b _ _ _ hle h

@[to_additive]
lemma mul_lt_mul_of_lt_of_le [covariant_class α α (function.swap (*)) (<)]
  (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
(mul_le_mul_left' h₂ _).trans_lt (mul_lt_mul_right' h₁ d)

end has_mul

-- here we start using properties of one.
section mul_one_class
variables [mul_one_class α] [covariant_class α α (*) (≤)]

@[to_additive le_add_of_nonneg_right]
lemma le_mul_of_one_le_right' (h : 1 ≤ b) : a ≤ a * b :=
calc  a = a * 1  : (mul_one _).symm
    ... ≤ a * b  : mul_le_mul_left' h a

@[to_additive add_le_of_nonpos_right]
lemma mul_le_of_le_one_right' (h : b ≤ 1) : a * b ≤ a :=
calc  a * b ≤ a * 1 : mul_le_mul_left' h a
        ... = a     : mul_one a

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

variable  [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma mul_lt_of_mul_lt_right (h : a * b < c) (hle : d ≤ a) :
  d * b < c :=
(mul_le_mul_right' hle b).trans_lt h

@[to_additive]
lemma mul_le_of_mul_le_right (h : a * b ≤ c) (hle : d ≤ a) :
  d * b ≤ c :=
(mul_le_mul_right' hle b).trans h

@[to_additive]
lemma lt_mul_of_lt_mul_right (h : a < b * c) (hle : b ≤ d) :
  a < d * c :=
h.trans_le (mul_le_mul_right' hle c)

@[to_additive]
lemma le_mul_of_le_mul_right (h : a ≤ b * c) (hle : b ≤ d) :
  a ≤ d * c :=
h.trans (mul_le_mul_right' hle c)

end has_mul

-- here we start using properties of one.
section mul_one_class
variables [mul_one_class α]

section le_right
variable [covariant_class α α (function.swap (*)) (≤)]

@[to_additive le_add_of_nonneg_left]
lemma le_mul_of_one_le_left' (h : 1 ≤ b) : a ≤ b * a :=
calc  a = 1 * a : (one_mul a).symm
    ... ≤ b * a : mul_le_mul_right' h a

@[to_additive add_le_of_nonpos_left]
lemma mul_le_of_le_one_left' (h : b ≤ 1) : b * a ≤ a :=
calc  b * a ≤ 1 * a : mul_le_mul_right' h a
        ... = a     : one_mul a

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

end le_right

section lt_right

@[to_additive lt_add_of_pos_left]
lemma lt_mul_of_one_lt_left' [covariant_class α α (function.swap (*)) (<)]
  (a : α) {b : α} (h : 1 < b) : a < b * a :=
calc a = 1 * a : (one_mul _).symm
   ... < b * a : mul_lt_mul_right' h a

end lt_right

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
(mul_le_mul_left' h₂ _).trans (mul_le_mul_right' h₁ d)

@[to_additive]
lemma mul_le_mul_three {e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) :
  a * b * c ≤ d * e * f :=
mul_le_mul' (mul_le_mul' h₁ h₂) h₃

end has_mul_left_right

-- here we start using properties of one.
section mul_one_class_left_right
variables [mul_one_class α]

section covariant_left
variable [covariant_class α α (*) (≤)]

@[to_additive add_pos_of_pos_of_nonneg]
lemma one_lt_mul_of_lt_of_le' (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
lt_of_lt_of_le ha $ le_mul_of_one_le_right' hb

@[to_additive add_pos']
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

end covariant_left

section covariant_right
variable [covariant_class α α (function.swap (*)) (≤)]

@[to_additive add_pos_of_nonneg_of_pos]
lemma one_lt_mul_of_le_of_lt' (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
lt_of_lt_of_le hb $ le_mul_of_one_le_left' ha

@[to_additive]
lemma lt_mul_of_one_le_of_lt (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
hbc.trans_le $ le_mul_of_one_le_left' ha

@[to_additive]
lemma lt_mul_of_one_lt_of_lt (ha : 1 < a) (hbc : b < c) : b < a * c :=
lt_mul_of_one_le_of_lt ha.le hbc

end covariant_right

-- up to here
variable [covariant_class α α (*) (≤)]

@[to_additive]
lemma le_mul_of_le_of_one_le (hbc : b ≤ c) (ha : 1 ≤ a) : b ≤ c * a :=
calc  b ≤ c : hbc
    ... = c * 1 : (mul_one c).symm
    ... ≤ c * a : mul_le_mul_left' ha c

@[to_additive add_nonneg]
lemma one_le_mul_right (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
calc  1 ≤ a     : ha
    ... = a * 1 : (mul_one a).symm
    ... ≤ a * b : mul_le_mul_left' hb a

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

end partial_order

section mono
variables [has_mul α] [preorder α]
  {β : Type*} [preorder β] {f g : β → α}

@[to_additive monotone.add_const]
lemma monotone.mul_const' [covariant_class α α (function.swap (*)) (≤)]
  (hf : monotone f) (a : α) : monotone (λ x, f x * a) :=
λ x y h, mul_le_mul_right' (hf h) a
--hf.mul' monotone_const

@[to_additive monotone.const_add]
lemma monotone.const_mul' [covariant_class α α (*) (≤)] (hf : monotone f) (a : α) :
  monotone (λ x, a * f x) :=
λ x y h, mul_le_mul_left' (hf h) a
--monotone_const.mul' hf

@[to_additive monotone.add]
lemma monotone.mul'
  [covariant_class α α (*) (≤)] [covariant_class α α (function.swap (*)) (≤)]
  (hf : monotone f) (hg : monotone g) : monotone (λ x, f x * g x) :=
λ x y h, mul_le_mul' (hf h) (hg h)

end mono
