/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import data.prod
import data.subtype

/-!
# Basic definitions about `≤` and `<`

This file proves basic results about orders, provides extensive dot notation, defines useful order
classes and allows to transfer order instances.

## Type synonyms

* `order_dual α` : A type synonym reversing the meaning of all inequalities.
* `as_linear_order α`: A type synonym to promote `partial_order α` to `linear_order α` using
  `is_total α (≤)`.

### Transfering orders

- `order.preimage`, `preorder.lift`: Transfers a (pre)order on `β` to an order on `α`
  using a function `f : α → β`.
- `partial_order.lift`, `linear_order.lift`: Transfers a partial (resp., linear) order on `β` to a
  partial (resp., linear) order on `α` using an injective function `f`.

### Extra classes

- `no_top_order`, `no_bot_order`: An order without a maximal/minimal element.
- `densely_ordered`: An order with no gap, i.e. for any two elements `a < b` there exists `c` such
  that `a < c < b`.

## Notes

`≤` and `<` are highly favored over `≥` and `>` in mathlib. The reason is that we can formulate all
lemmas using `≤`/`<`, and `rw` has trouble unifying `≤` and `≥`. Hence choosing one direction spares
us useless duplication. This is enforced by a linter. See Note [nolint_ge] for more infos.

Dot notation is particularly useful on `≤` (`has_le.le`) and `<` (`has_lt.lt`). To that end, we
provide many aliases to dot notation-less lemmas. For example, `le_trans` is aliased with
`has_le.le.trans` and can be used to construct `hab.trans hbc : a ≤ c` when `hab : a ≤ b`,
`hbc : b ≤ c`, `lt_of_le_of_lt` is aliased as `has_le.le.trans_lt` and can be used to construct
`hab.trans hbc : a < c` when `hab : a ≤ b`, `hbc : b < c`.

## TODO

- expand module docs
- automatic construction of dual definitions / theorems

## See also

- `algebra.order.basic` for basic lemmas about orders, and projection notation for orders

## Tags

preorder, order, partial order, poset, linear order, chain
-/

open function

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} {r : α → α → Prop}

attribute [simp] le_refl
attribute [ext] has_le

alias le_trans        ← has_le.le.trans
alias lt_of_le_of_lt  ← has_le.le.trans_lt
alias le_antisymm     ← has_le.le.antisymm
alias lt_of_le_of_ne  ← has_le.le.lt_of_ne
alias lt_of_le_not_le ← has_le.le.lt_of_not_le
alias lt_or_eq_of_le  ← has_le.le.lt_or_eq
alias decidable.lt_or_eq_of_le ← has_le.le.lt_or_eq_dec

alias le_of_lt        ← has_lt.lt.le
alias lt_trans        ← has_lt.lt.trans
alias lt_of_lt_of_le  ← has_lt.lt.trans_le
alias ne_of_lt        ← has_lt.lt.ne
alias lt_asymm        ← has_lt.lt.asymm has_lt.lt.not_lt

alias le_of_eq        ← eq.le

attribute [nolint decidable_classical] has_le.le.lt_or_eq_dec

/-- A version of `le_refl` where the argument is implicit -/
lemma le_rfl [preorder α] {x : α} : x ≤ x := le_refl x

@[simp] lemma lt_self_iff_false [preorder α] (x : α) : x < x ↔ false :=
⟨lt_irrefl x, false.elim⟩

namespace eq

/-- If `x = y` then `y ≤ x`. Note: this lemma uses `y ≤ x` instead of `x ≥ y`, because `le` is used
almost exclusively in mathlib. -/
protected lemma ge [preorder α] {x y : α} (h : x = y) : y ≤ x := h.symm.le

lemma trans_le [preorder α] {x y z : α} (h1 : x = y) (h2 : y ≤ z) : x ≤ z := h1.le.trans h2

lemma not_lt [partial_order α] {x y : α} (h : x = y) : ¬(x < y) := λ h', h'.ne h

lemma not_gt [partial_order α] {x y : α} (h : x = y) : ¬(y < x) := h.symm.not_lt

end eq

namespace has_le.le

@[nolint ge_or_gt] -- see Note [nolint_ge]
protected lemma ge [has_le α] {x y : α} (h : x ≤ y) : y ≥ x := h

lemma trans_eq [preorder α] {x y z : α} (h1 : x ≤ y) (h2 : y = z) : x ≤ z := h1.trans h2.le

lemma lt_iff_ne [partial_order α] {x y : α} (h : x ≤ y) : x < y ↔ x ≠ y := ⟨λ h, h.ne, h.lt_of_ne⟩

lemma le_iff_eq [partial_order α] {x y : α} (h : x ≤ y) : y ≤ x ↔ y = x :=
⟨λ h', h'.antisymm h, eq.le⟩

lemma lt_or_le [linear_order α] {a b : α} (h : a ≤ b) (c : α) : a < c ∨ c ≤ b :=
(lt_or_ge a c).imp id $ λ hc, le_trans hc h

lemma le_or_lt [linear_order α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c < b :=
(le_or_gt a c).imp id $ λ hc, lt_of_lt_of_le hc h

lemma le_or_le [linear_order α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c ≤ b :=
(h.le_or_lt c).elim or.inl (λ h, or.inr $ le_of_lt h)

end has_le.le

namespace has_lt.lt

@[nolint ge_or_gt] -- see Note [nolint_ge]
protected lemma gt [has_lt α] {x y : α} (h : x < y) : y > x := h
protected lemma false [preorder α] {x : α} : x < x → false := lt_irrefl x

lemma ne' [preorder α] {x y : α} (h : x < y) : y ≠ x := h.ne.symm

lemma lt_or_lt [linear_order α] {x y : α} (h : x < y) (z : α) : x < z ∨ z < y :=
(lt_or_ge z y).elim or.inr (λ hz, or.inl $ h.trans_le hz)

end has_lt.lt

@[nolint ge_or_gt] -- see Note [nolint_ge]
protected lemma ge.le [has_le α] {x y : α} (h : x ≥ y) : y ≤ x := h

@[nolint ge_or_gt] -- see Note [nolint_ge]
protected lemma gt.lt [has_lt α] {x y : α} (h : x > y) : y < x := h

@[nolint ge_or_gt] -- see Note [nolint_ge]
theorem ge_of_eq [preorder α] {a b : α} (h : a = b) : a ≥ b := h.ge

@[simp, nolint ge_or_gt] -- see Note [nolint_ge]
lemma ge_iff_le [preorder α] {a b : α} : a ≥ b ↔ b ≤ a := iff.rfl
@[simp, nolint ge_or_gt] -- see Note [nolint_ge]
lemma gt_iff_lt [preorder α] {a b : α} : a > b ↔ b < a := iff.rfl

lemma not_le_of_lt [preorder α] {a b : α} (h : a < b) : ¬ b ≤ a := (le_not_le_of_lt h).right

alias not_le_of_lt ← has_lt.lt.not_le

lemma not_lt_of_le [preorder α] {a b : α} (h : a ≤ b) : ¬ b < a := λ hba, hba.not_le h

alias not_lt_of_le ← has_le.le.not_lt

-- See Note [decidable namespace]
protected lemma decidable.le_iff_eq_or_lt [partial_order α] [@decidable_rel α (≤)]
  {a b : α} : a ≤ b ↔ a = b ∨ a < b := decidable.le_iff_lt_or_eq.trans or.comm

lemma le_iff_eq_or_lt [partial_order α] {a b : α} : a ≤ b ↔ a = b ∨ a < b :=
le_iff_lt_or_eq.trans or.comm

lemma lt_iff_le_and_ne [partial_order α] {a b : α} : a < b ↔ a ≤ b ∧ a ≠ b :=
⟨λ h, ⟨le_of_lt h, ne_of_lt h⟩, λ ⟨h1, h2⟩, h1.lt_of_ne h2⟩

-- See Note [decidable namespace]
protected lemma decidable.eq_iff_le_not_lt [partial_order α] [@decidable_rel α (≤)]
  {a b : α} : a = b ↔ a ≤ b ∧ ¬ a < b :=
⟨λ h, ⟨h.le, h ▸ lt_irrefl _⟩, λ ⟨h₁, h₂⟩, h₁.antisymm $
  decidable.by_contradiction $ λ h₃, h₂ (h₁.lt_of_not_le h₃)⟩

lemma eq_iff_le_not_lt [partial_order α] {a b : α} : a = b ↔ a ≤ b ∧ ¬ a < b :=
by haveI := classical.dec; exact decidable.eq_iff_le_not_lt

lemma eq_or_lt_of_le [partial_order α] {a b : α} (h : a ≤ b) : a = b ∨ a < b := h.lt_or_eq.symm

alias decidable.eq_or_lt_of_le ← has_le.le.eq_or_lt_dec
alias eq_or_lt_of_le ← has_le.le.eq_or_lt

attribute [nolint decidable_classical] has_le.le.eq_or_lt_dec

lemma ne.le_iff_lt [partial_order α] {a b : α} (h : a ≠ b) : a ≤ b ↔ a < b :=
⟨λ h', lt_of_le_of_ne h' h, λ h, h.le⟩

-- See Note [decidable namespace]
protected lemma decidable.ne_iff_lt_iff_le [partial_order α] [@decidable_rel α (≤)]
  {a b : α} : (a ≠ b ↔ a < b) ↔ a ≤ b :=
⟨λ h, decidable.by_cases le_of_eq (le_of_lt ∘ h.mp), λ h, ⟨lt_of_le_of_ne h, ne_of_lt⟩⟩

@[simp] lemma ne_iff_lt_iff_le [partial_order α] {a b : α} : (a ≠ b ↔ a < b) ↔ a ≤ b :=
by haveI := classical.dec; exact decidable.ne_iff_lt_iff_le

lemma lt_of_not_ge' [linear_order α] {a b : α} (h : ¬ b ≤ a) : a < b :=
((le_total _ _).resolve_right h).lt_of_not_le h

lemma lt_iff_not_ge' [linear_order α] {x y : α} : x < y ↔ ¬ y ≤ x := ⟨not_le_of_gt, lt_of_not_ge'⟩

lemma ne.lt_or_lt [linear_order α] {x y : α} (h : x ≠ y) : x < y ∨ y < x := lt_or_gt_of_ne h

lemma not_lt_iff_eq_or_lt [linear_order α] {a b : α} : ¬ a < b ↔ a = b ∨ b < a :=
not_lt.trans $ decidable.le_iff_eq_or_lt.trans $ or_congr eq_comm iff.rfl

lemma exists_ge_of_linear [linear_order α] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
match le_total a b with
| or.inl h := ⟨_, h, le_rfl⟩
| or.inr h := ⟨_, le_rfl, h⟩
end

lemma lt_imp_lt_of_le_imp_le {β} [linear_order α] [preorder β] {a b : α} {c d : β}
  (H : a ≤ b → c ≤ d) (h : d < c) : b < a :=
lt_of_not_ge' $ λ h', (H h').not_lt h

lemma le_imp_le_iff_lt_imp_lt {β} [linear_order α] [linear_order β] {a b : α} {c d : β} :
  (a ≤ b → c ≤ d) ↔ (d < c → b < a) :=
⟨lt_imp_lt_of_le_imp_le, le_imp_le_of_lt_imp_lt⟩

lemma lt_iff_lt_of_le_iff_le' {β} [preorder α] [preorder β] {a b : α} {c d : β}
  (H : a ≤ b ↔ c ≤ d) (H' : b ≤ a ↔ d ≤ c) : b < a ↔ d < c :=
lt_iff_le_not_le.trans $ (and_congr H' (not_congr H)).trans lt_iff_le_not_le.symm

lemma lt_iff_lt_of_le_iff_le {β} [linear_order α] [linear_order β] {a b : α} {c d : β}
  (H : a ≤ b ↔ c ≤ d) : b < a ↔ d < c :=
not_le.symm.trans $ (not_congr H).trans $ not_le

lemma le_iff_le_iff_lt_iff_lt {β} [linear_order α] [linear_order β] {a b : α} {c d : β} :
  (a ≤ b ↔ c ≤ d) ↔ (b < a ↔ d < c) :=
⟨lt_iff_lt_of_le_iff_le, λ H, not_lt.symm.trans $ (not_congr H).trans $ not_lt⟩

lemma eq_of_forall_le_iff [partial_order α] {a b : α}
  (H : ∀ c, c ≤ a ↔ c ≤ b) : a = b :=
((H _).1 le_rfl).antisymm ((H _).2 le_rfl)

lemma le_of_forall_le [preorder α] {a b : α}
  (H : ∀ c, c ≤ a → c ≤ b) : a ≤ b :=
H _ le_rfl

lemma le_of_forall_le' [preorder α] {a b : α}
  (H : ∀ c, a ≤ c → b ≤ c) : b ≤ a :=
H _ le_rfl

lemma le_of_forall_lt [linear_order α] {a b : α}
  (H : ∀ c, c < a → c < b) : a ≤ b :=
le_of_not_lt $ λ h, lt_irrefl _ (H _ h)

lemma forall_lt_iff_le [linear_order α] {a b : α} :
  (∀ ⦃c⦄, c < a → c < b) ↔ a ≤ b :=
⟨le_of_forall_lt, λ h c hca, lt_of_lt_of_le hca h⟩

lemma le_of_forall_lt' [linear_order α] {a b : α}
  (H : ∀ c, a < c → b < c) : b ≤ a :=
le_of_not_lt $ λ h, lt_irrefl _ (H _ h)

lemma forall_lt_iff_le' [linear_order α] {a b : α} :
  (∀ ⦃c⦄, a < c → b < c) ↔ b ≤ a :=
⟨le_of_forall_lt', λ h c hac, lt_of_le_of_lt h hac⟩

lemma eq_of_forall_ge_iff [partial_order α] {a b : α}
  (H : ∀ c, a ≤ c ↔ b ≤ c) : a = b :=
((H _).2 le_rfl).antisymm ((H _).1 le_rfl)

/-- monotonicity of `≤` with respect to `→` -/
lemma le_implies_le_of_le_of_le {a b c d : α} [preorder α] (hca : c ≤ a) (hbd : b ≤ d) :
  a ≤ b → c ≤ d :=
λ hab, (hca.trans hab).trans hbd

@[ext]
lemma preorder.to_has_le_injective {α : Type*} :
  function.injective (@preorder.to_has_le α) :=
λ A B h, begin
  cases A, cases B,
  injection h with h_le,
  have : A_lt = B_lt,
  { funext a b,
    dsimp [(≤)] at A_lt_iff_le_not_le B_lt_iff_le_not_le h_le,
    simp [A_lt_iff_le_not_le, B_lt_iff_le_not_le, h_le], },
  congr',
end

@[ext]
lemma partial_order.to_preorder_injective {α : Type*} :
  function.injective (@partial_order.to_preorder α) :=
λ A B h, by { cases A, cases B, injection h, congr' }

@[ext]
lemma linear_order.to_partial_order_injective {α : Type*} :
  function.injective (@linear_order.to_partial_order α) :=
begin
  intros A B h,
  cases A, cases B, injection h,
  obtain rfl : A_le = B_le := ‹_›, obtain rfl : A_lt = B_lt := ‹_›,
  obtain rfl : A_decidable_le = B_decidable_le := subsingleton.elim _ _,
  obtain rfl : A_max = B_max := A_max_def.trans B_max_def.symm,
  obtain rfl : A_min = B_min := A_min_def.trans B_min_def.symm,
  congr
end

theorem preorder.ext {α} {A B : preorder α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
by { ext x y, exact H x y }

theorem partial_order.ext {α} {A B : partial_order α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
by { ext x y, exact H x y }

theorem linear_order.ext {α} {A B : linear_order α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
by { ext x y, exact H x y }

/-- Given a relation `R` on `β` and a function `f : α → β`, the preimage relation on `α` is defined
by `x ≤ y ↔ f x ≤ f y`. It is the unique relation on `α` making `f` a `rel_embedding` (assuming `f`
is injective). -/
@[simp] def order.preimage {α β} (f : α → β) (s : β → β → Prop) (x y : α) : Prop := s (f x) (f y)

infix ` ⁻¹'o `:80 := order.preimage

/-- The preimage of a decidable order is decidable. -/
instance order.preimage.decidable {α β} (f : α → β) (s : β → β → Prop) [H : decidable_rel s] :
  decidable_rel (f ⁻¹'o s) :=
λ x y, H _ _

/-! ### Order dual -/

/-- Type synonym to equip a type with the dual order: `≤` means `≥` and `<` means `>`. -/
def order_dual (α : Type*) : Type* := α

namespace order_dual

instance (α : Type*) [h : nonempty α] : nonempty (order_dual α) := h
instance (α : Type*) [h : subsingleton α] : subsingleton (order_dual α) := h
instance (α : Type*) [has_le α] : has_le (order_dual α) := ⟨λ x y : α, y ≤ x⟩
instance (α : Type*) [has_lt α] : has_lt (order_dual α) := ⟨λ x y : α, y < x⟩
instance (α : Type*) [has_zero α] : has_zero (order_dual α) := ⟨(0 : α)⟩

-- `dual_le` and `dual_lt` should not be simp lemmas:
-- they cause a loop since `α` and `order_dual α` are definitionally equal

lemma dual_le [has_le α] {a b : α} :
  @has_le.le (order_dual α) _ a b ↔ @has_le.le α _ b a := iff.rfl

lemma dual_lt [has_lt α] {a b : α} :
  @has_lt.lt (order_dual α) _ a b ↔ @has_lt.lt α _ b a := iff.rfl

instance (α : Type*) [preorder α] : preorder (order_dual α) :=
{ le_refl          := le_refl,
  le_trans         := λ a b c hab hbc, hbc.trans hab,
  lt_iff_le_not_le := λ _ _, lt_iff_le_not_le,
  .. order_dual.has_le α,
  .. order_dual.has_lt α }

instance (α : Type*) [partial_order α] : partial_order (order_dual α) :=
{ le_antisymm := λ a b hab hba, @le_antisymm α _ a b hba hab, .. order_dual.preorder α }

instance (α : Type*) [linear_order α] : linear_order (order_dual α) :=
{ le_total     := λ a b : α, le_total b a,
  decidable_le := (infer_instance : decidable_rel (λ a b : α, b ≤ a)),
  decidable_lt := (infer_instance : decidable_rel (λ a b : α, b < a)),
  min := @max α _,
  max := @min α _,
  min_def := @linear_order.max_def α _,
  max_def := @linear_order.min_def α _,
  .. order_dual.partial_order α }

instance : Π [inhabited α], inhabited (order_dual α) := id

theorem preorder.dual_dual (α : Type*) [H : preorder α] :
  order_dual.preorder (order_dual α) = H :=
preorder.ext $ λ _ _, iff.rfl

theorem partial_order.dual_dual (α : Type*) [H : partial_order α] :
  order_dual.partial_order (order_dual α) = H :=
partial_order.ext $ λ _ _, iff.rfl

theorem linear_order.dual_dual (α : Type*) [H : linear_order α] :
  order_dual.linear_order (order_dual α) = H :=
linear_order.ext $ λ _ _, iff.rfl

end order_dual

/-! ### Order instances on the function space -/

instance pi.preorder {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] : preorder (Π i, α i) :=
{ le       := λ x y, ∀ i, x i ≤ y i,
  le_refl  := λ a i, le_refl (a i),
  le_trans := λ a b c h₁ h₂ i, le_trans (h₁ i) (h₂ i) }

lemma pi.le_def {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] {x y : Π i, α i} :
  x ≤ y ↔ ∀ i, x i ≤ y i :=
iff.rfl

lemma pi.lt_def {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] {x y : Π i, α i} :
  x < y ↔ x ≤ y ∧ ∃ i, x i < y i :=
by simp [lt_iff_le_not_le, pi.le_def] {contextual := tt}

lemma le_update_iff {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] [decidable_eq ι]
  {x y : Π i, α i} {i : ι} {a : α i} :
  x ≤ function.update y i a ↔ x i ≤ a ∧ ∀ j ≠ i, x j ≤ y j :=
function.forall_update_iff _ (λ j z, x j ≤ z)

lemma update_le_iff {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] [decidable_eq ι]
  {x y : Π i, α i} {i : ι} {a : α i} :
  function.update x i a ≤ y ↔ a ≤ y i ∧ ∀ j ≠ i, x j ≤ y j :=
function.forall_update_iff _ (λ j z, z ≤ y j)

lemma update_le_update_iff {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] [decidable_eq ι]
  {x y : Π i, α i} {i : ι} {a b : α i} :
  function.update x i a ≤ function.update y i b ↔ a ≤ b ∧ ∀ j ≠ i, x j ≤ y j :=
by simp [update_le_iff] {contextual := tt}

instance pi.partial_order {ι : Type u} {α : ι → Type v} [∀ i, partial_order (α i)] :
  partial_order (Π i, α i) :=
{ le_antisymm := λ f g h1 h2, funext (λ b, (h1 b).antisymm (h2 b)),
  ..pi.preorder }

/-! ### Lifts of order instances -/

/-- Transfer a `preorder` on `β` to a `preorder` on `α` using a function `f : α → β`.
See note [reducible non-instances]. -/
@[reducible] def preorder.lift {α β} [preorder β] (f : α → β) : preorder α :=
{ le               := λ x y, f x ≤ f y,
  le_refl          := λ a, le_rfl,
  le_trans         := λ a b c, le_trans,
  lt               := λ x y, f x < f y,
  lt_iff_le_not_le := λ a b, lt_iff_le_not_le }

/-- Transfer a `partial_order` on `β` to a `partial_order` on `α` using an injective
function `f : α → β`. See note [reducible non-instances]. -/
@[reducible] def partial_order.lift {α β} [partial_order β] (f : α → β) (inj : injective f) :
  partial_order α :=
{ le_antisymm := λ a b h₁ h₂, inj (h₁.antisymm h₂), .. preorder.lift f }

/-- Transfer a `linear_order` on `β` to a `linear_order` on `α` using an injective
function `f : α → β`. See note [reducible non-instances]. -/
@[reducible] def linear_order.lift {α β} [linear_order β] (f : α → β) (inj : injective f) :
  linear_order α :=
{ le_total     := λ x y, le_total (f x) (f y),
  decidable_le := λ x y, (infer_instance : decidable (f x ≤ f y)),
  decidable_lt := λ x y, (infer_instance : decidable (f x < f y)),
  decidable_eq := λ x y, decidable_of_iff _ inj.eq_iff,
  .. partial_order.lift f inj }

instance subtype.preorder {α} [preorder α] (p : α → Prop) : preorder (subtype p) :=
preorder.lift (coe : subtype p → α)

@[simp] lemma subtype.mk_le_mk {α} [preorder α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
  (⟨x, hx⟩ : subtype p) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
iff.rfl

@[simp] lemma subtype.mk_lt_mk {α} [preorder α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
  (⟨x, hx⟩ : subtype p) < ⟨y, hy⟩ ↔ x < y :=
iff.rfl

@[simp, norm_cast] lemma subtype.coe_le_coe {α} [preorder α] {p : α → Prop} {x y : subtype p} :
  (x : α) ≤ y ↔ x ≤ y :=
iff.rfl

@[simp, norm_cast] lemma subtype.coe_lt_coe {α} [preorder α] {p : α → Prop} {x y : subtype p} :
  (x : α) < y ↔ x < y :=
iff.rfl

instance subtype.partial_order {α} [partial_order α] (p : α → Prop) :
  partial_order (subtype p) :=
partial_order.lift coe subtype.coe_injective

/-- A subtype of a linear order is a linear order. We explicitly give the proof of decidable
  equality as the existing instance, in order to not have two instances of decidable equality that
  are not definitionally equal. -/
instance subtype.linear_order {α} [linear_order α] (p : α → Prop) : linear_order (subtype p) :=
{ decidable_eq := subtype.decidable_eq,
  .. linear_order.lift coe subtype.coe_injective }

namespace prod

instance (α : Type u) (β : Type v) [has_le α] [has_le β] : has_le (α × β) :=
⟨λ p q, p.1 ≤ q.1 ∧ p.2 ≤ q.2⟩

lemma le_def {α β : Type*} [has_le α] [has_le β] {x y : α × β} :
  x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2 := iff.rfl

@[simp] lemma mk_le_mk {α β : Type*} [has_le α] [has_le β] {x₁ x₂ : α} {y₁ y₂ : β} :
  (x₁, y₁) ≤ (x₂, y₂) ↔ x₁ ≤ x₂ ∧ y₁ ≤ y₂ :=
iff.rfl

instance (α : Type u) (β : Type v) [preorder α] [preorder β] : preorder (α × β) :=
{ le_refl  := λ ⟨a, b⟩, ⟨le_refl a, le_refl b⟩,
  le_trans := λ ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩,
    ⟨le_trans hac hce, le_trans hbd hdf⟩,
  .. prod.has_le α β }

/-- The pointwise partial order on a product.
    (The lexicographic ordering is defined in order/lexicographic.lean, and the instances are
    available via the type synonym `lex α β = α × β`.) -/
instance (α : Type u) (β : Type v) [partial_order α] [partial_order β] :
  partial_order (α × β) :=
{ le_antisymm := λ ⟨a, b⟩ ⟨c, d⟩ ⟨hac, hbd⟩ ⟨hca, hdb⟩,
    prod.ext (hac.antisymm hca) (hbd.antisymm hdb),
  .. prod.preorder α β }

end prod

/-! ### Additional order classes -/

/-- Order without a maximal element. Sometimes called cofinal. -/
class no_top_order (α : Type u) [preorder α] : Prop :=
(no_top : ∀ a : α, ∃ a', a < a')

lemma no_top [preorder α] [no_top_order α] : ∀ a : α, ∃ a', a < a' :=
no_top_order.no_top

instance nonempty_gt {α : Type u} [preorder α] [no_top_order α] (a : α) :
  nonempty {x // a < x} :=
nonempty_subtype.2 (no_top a)

/-- `a : α` is a top element of `α` if it is greater than or equal to any other element of `α`.
This predicate is useful, e.g., to make some statements and proofs work in both cases
`[order_top α]` and `[no_top_order α]`. -/
def is_top {α : Type u} [has_le α] (a : α) : Prop := ∀ b, b ≤ a

@[simp] lemma not_is_top {α : Type u} [preorder α] [no_top_order α] (a : α) : ¬is_top a :=
λ h, let ⟨b, hb⟩ := no_top a in hb.not_le (h b)

lemma is_top.unique {α : Type u} [partial_order α] {a b : α} (ha : is_top a) (hb : a ≤ b) :
  a = b :=
le_antisymm hb (ha b)

/-- Order without a minimal element. Sometimes called coinitial or dense. -/
class no_bot_order (α : Type u) [preorder α] : Prop :=
(no_bot : ∀ a : α, ∃ a', a' < a)

lemma no_bot [preorder α] [no_bot_order α] : ∀ a : α, ∃ a', a' < a :=
no_bot_order.no_bot

/-- `a : α` is a bottom element of `α` if it is less than or equal to any other element of `α`.
This predicate is useful, e.g., to make some statements and proofs work in both cases
`[order_bot α]` and `[no_bot_order α]`. -/
def is_bot {α : Type u} [has_le α] (a : α) : Prop := ∀ b, a ≤ b

@[simp] lemma not_is_bot {α : Type u} [preorder α] [no_bot_order α] (a : α) : ¬is_bot a :=
λ h, let ⟨b, hb⟩ := no_bot a in hb.not_le (h b)

lemma is_bot.unique {α : Type u} [partial_order α] {a b : α} (ha : is_bot a) (hb : b ≤ a) :
  a = b :=
le_antisymm (ha b) hb

instance order_dual.no_top_order (α : Type u) [preorder α] [no_bot_order α] :
  no_top_order (order_dual α) :=
⟨λ a, @no_bot α _ _ a⟩

instance order_dual.no_bot_order (α : Type u) [preorder α] [no_top_order α] :
  no_bot_order (order_dual α) :=
⟨λ a, @no_top α _ _ a⟩

instance nonempty_lt {α : Type u} [preorder α] [no_bot_order α] (a : α) :
  nonempty {x // x < a} :=
nonempty_subtype.2 (no_bot a)

/-- An order is dense if there is an element between any pair of distinct elements. -/
class densely_ordered (α : Type u) [preorder α] : Prop :=
(dense : ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂)

lemma exists_between [preorder α] [densely_ordered α] :
  ∀ {a₁ a₂ : α}, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂ :=
densely_ordered.dense

instance order_dual.densely_ordered (α : Type u) [preorder α] [densely_ordered α] :
  densely_ordered (order_dual α) :=
⟨λ a₁ a₂ ha, (@exists_between α _ _ _ _ ha).imp $ λ a, and.symm⟩

lemma le_of_forall_le_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h : ∀ a, a₂ < a → a₁ ≤ a) :
  a₁ ≤ a₂ :=
le_of_not_gt $ λ ha,
  let ⟨a, ha₁, ha₂⟩ := exists_between ha in
  lt_irrefl a $ lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)

lemma eq_of_le_of_forall_le_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h₁ : a₂ ≤ a₁) (h₂ : ∀ a, a₂ < a → a₁ ≤ a) : a₁ = a₂ :=
le_antisymm (le_of_forall_le_of_dense h₂) h₁

lemma le_of_forall_ge_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h : ∀ a₃ < a₁, a₃ ≤ a₂) :
  a₁ ≤ a₂ :=
le_of_not_gt $ λ ha,
  let ⟨a, ha₁, ha₂⟩ := exists_between ha in
  lt_irrefl a $ lt_of_le_of_lt (h _ ‹a < a₁›) ‹a₂ < a›

lemma eq_of_le_of_forall_ge_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h₁ : a₂ ≤ a₁) (h₂ : ∀ a₃ < a₁, a₃ ≤ a₂) : a₁ = a₂ :=
(le_of_forall_ge_of_dense h₂).antisymm h₁

lemma dense_or_discrete [linear_order α] (a₁ a₂ : α) :
  (∃ a, a₁ < a ∧ a < a₂) ∨ ((∀ a, a₁ < a → a₂ ≤ a) ∧ (∀ a < a₂, a ≤ a₁)) :=
or_iff_not_imp_left.2 $ λ h,
  ⟨λ a ha₁, le_of_not_gt $ λ ha₂, h ⟨a, ha₁, ha₂⟩,
    λ a ha₂, le_of_not_gt $ λ ha₁, h ⟨a, ha₁, ha₂⟩⟩

variables {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Linear order from a total partial order -/

/-- Type synonym to create an instance of `linear_order` from a `partial_order` and
`is_total α (≤)` -/
def as_linear_order (α : Type u) := α

instance {α} [inhabited α] : inhabited (as_linear_order α) :=
⟨ (default α : α) ⟩

noncomputable instance as_linear_order.linear_order {α} [partial_order α] [is_total α (≤)] :
  linear_order (as_linear_order α) :=
{ le_total     := @total_of α (≤) _,
  decidable_le := classical.dec_rel _,
  .. (_ : partial_order α) }
