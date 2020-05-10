/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import data.set.basic
open function

/-!
# Basic definitions about `≤` and `<`

## Definitions

### Predicates on functions

- `monotone f`: a function between two types equipped with `≤` is monotone
  if `a ≤ b` implies `f a ≤ f b`.
- `strict_mono f` : a function between two types equipped with `<` is strictly monotone
  if `a < b` implies `f a < f b`.
- `order_dual α` : a type tag reversing the meaning of all inequalities.

### Transfering orders

- `order.preimage`, `preorder.lift`: transfer a (pre)order on `β` to an order on `α`
  using a function `f : α → β`.
- `partial_order.lift`, `linear_order.lift`, `decidable_linear_order.lift`:
  transfer a partial (resp., linear, decidable linear) order on `β` to a partial
  (resp., linear, decidable linear) order on `α` using an injective function `f`.

### Extra classes

- `no_top_order`, `no_bot_order`: an order without a maximal/minimal element.
- `densely_ordered`: an order with no gaps, i.e. for any two elements `a<b` there exists
  `c`, `a<c<b`.

## Main theorems

- `monotone_of_monotone_nat`: if `f : ℕ → α` and `f n ≤ f (n + 1)` for all `n`, then
  `f` is monotone;
- `strict_mono.nat`: if `f : ℕ → α` and `f n < f (n + 1)` for all `n`, then f is strictly monotone.

## TODO

- expand module docs
- automatic construction of dual definitions / theorems

## Tags

preorder, order, partial order, linear order, monotone, strictly monotone
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} {r : α → α → Prop}

theorem ge_of_eq [preorder α] {a b : α} : a = b → a ≥ b :=
λ h, h ▸ le_refl a

theorem is_refl.swap (r) [is_refl α r] : is_refl α (swap r) := ⟨refl_of r⟩
theorem is_irrefl.swap (r) [is_irrefl α r] : is_irrefl α (swap r) := ⟨irrefl_of r⟩
theorem is_trans.swap (r) [is_trans α r] : is_trans α (swap r) :=
⟨λ a b c h₁ h₂, trans_of r h₂ h₁⟩
theorem is_antisymm.swap (r) [is_antisymm α r] : is_antisymm α (swap r) :=
⟨λ a b h₁ h₂, antisymm h₂ h₁⟩
theorem is_asymm.swap (r) [is_asymm α r] : is_asymm α (swap r) :=
⟨λ a b h₁ h₂, asymm_of r h₂ h₁⟩
theorem is_total.swap (r) [is_total α r] : is_total α (swap r) :=
⟨λ a b, (total_of r a b).swap⟩
theorem is_trichotomous.swap (r) [is_trichotomous α r] : is_trichotomous α (swap r) :=
⟨λ a b, by simpa [swap, or.comm, or.left_comm] using trichotomous_of r a b⟩
theorem is_preorder.swap (r) [is_preorder α r] : is_preorder α (swap r) :=
{..@is_refl.swap α r _, ..@is_trans.swap α r _}
theorem is_strict_order.swap (r) [is_strict_order α r] : is_strict_order α (swap r) :=
{..@is_irrefl.swap α r _, ..@is_trans.swap α r _}
theorem is_partial_order.swap (r) [is_partial_order α r] : is_partial_order α (swap r) :=
{..@is_preorder.swap α r _, ..@is_antisymm.swap α r _}
theorem is_total_preorder.swap (r) [is_total_preorder α r] : is_total_preorder α (swap r) :=
{..@is_preorder.swap α r _, ..@is_total.swap α r _}
theorem is_linear_order.swap (r) [is_linear_order α r] : is_linear_order α (swap r) :=
{..@is_partial_order.swap α r _, ..@is_total.swap α r _}

lemma antisymm_of_asymm (r) [is_asymm α r] : is_antisymm α r :=
⟨λ x y h₁ h₂, (asymm h₁ h₂).elim⟩

/- Convert algebraic structure style to explicit relation style typeclasses -/
instance [preorder α] : is_refl α (≤) := ⟨le_refl⟩
instance [preorder α] : is_refl α (≥) := is_refl.swap _
instance [preorder α] : is_trans α (≤) := ⟨@le_trans _ _⟩
instance [preorder α] : is_trans α (≥) := is_trans.swap _
instance [preorder α] : is_preorder α (≤) := {}
instance [preorder α] : is_preorder α (≥) := {}
instance [preorder α] : is_irrefl α (<) := ⟨lt_irrefl⟩
instance [preorder α] : is_irrefl α (>) := is_irrefl.swap _
instance [preorder α] : is_trans α (<) := ⟨@lt_trans _ _⟩
instance [preorder α] : is_trans α (>) := is_trans.swap _
instance [preorder α] : is_asymm α (<) := ⟨@lt_asymm _ _⟩
instance [preorder α] : is_asymm α (>) := is_asymm.swap _
instance [preorder α] : is_antisymm α (<) := antisymm_of_asymm _
instance [preorder α] : is_antisymm α (>) := antisymm_of_asymm _
instance [preorder α] : is_strict_order α (<) := {}
instance [preorder α] : is_strict_order α (>) := {}
instance preorder.is_total_preorder [preorder α] [is_total α (≤)] : is_total_preorder α (≤) := {}
instance [partial_order α] : is_antisymm α (≤) := ⟨@le_antisymm _ _⟩
instance [partial_order α] : is_antisymm α (≥) := is_antisymm.swap _
instance [partial_order α] : is_partial_order α (≤) := {}
instance [partial_order α] : is_partial_order α (≥) := {}
instance [linear_order α] : is_total α (≤) := ⟨le_total⟩
instance [linear_order α] : is_total α (≥) := is_total.swap _
instance linear_order.is_total_preorder [linear_order α] : is_total_preorder α (≤) := by apply_instance
instance [linear_order α] : is_total_preorder α (≥) := {}
instance [linear_order α] : is_linear_order α (≤) := {}
instance [linear_order α] : is_linear_order α (≥) := {}
instance [linear_order α] : is_trichotomous α (<) := ⟨lt_trichotomy⟩
instance [linear_order α] : is_trichotomous α (>) := is_trichotomous.swap _

theorem preorder.ext {α} {A B : preorder α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
begin
  resetI, cases A, cases B, congr,
  { funext x y, exact propext (H x y) },
  { funext x y,
    dsimp [(≤)] at A_lt_iff_le_not_le B_lt_iff_le_not_le H,
    simp [A_lt_iff_le_not_le, B_lt_iff_le_not_le, H] },
end

theorem partial_order.ext {α} {A B : partial_order α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
by haveI this := preorder.ext H;
   cases A; cases B; injection this; congr'

theorem linear_order.ext {α} {A B : linear_order α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
by haveI this := partial_order.ext H;
   cases A; cases B; injection this; congr'

/-- Given an order `R` on `β` and a function `f : α → β`,
  the preimage order on `α` is defined by `x ≤ y ↔ f x ≤ f y`.
  It is the unique order on `α` making `f` an order embedding
  (assuming `f` is injective). -/
@[simp] def order.preimage {α β} (f : α → β) (s : β → β → Prop) (x y : α) := s (f x) (f y)

infix ` ⁻¹'o `:80 := order.preimage

/-- The preimage of a decidable order is decidable. -/
instance order.preimage.decidable {α β} (f : α → β) (s : β → β → Prop) [H : decidable_rel s] :
  decidable_rel (f ⁻¹'o s) :=
λ x y, H _ _

section monotone
variables [preorder α] [preorder β] [preorder γ]

/-- A function between preorders is monotone if
  `a ≤ b` implies `f a ≤ f b`. -/
def monotone (f : α → β) := ∀⦃a b⦄, a ≤ b → f a ≤ f b

theorem monotone_id : @monotone α α _ _ id := assume x y h, h

theorem monotone_const {b : β} : monotone (λ(a:α), b) := assume x y h, le_refl b

protected theorem monotone.comp {g : β → γ} {f : α → β} (m_g : monotone g) (m_f : monotone f) :
  monotone (g ∘ f) :=
assume a b h, m_g (m_f h)

lemma monotone_of_monotone_nat {f : ℕ → α} (hf : ∀n, f n ≤ f (n + 1)) :
  monotone f | n m h :=
begin
  induction h,
  { refl },
  { transitivity, assumption, exact hf _ }
end

lemma reflect_lt {α β} [linear_order α] [preorder β] {f : α → β} (hf : monotone f)
  {x x' : α} (h : f x < f x') : x < x' :=
by { rw [← not_le], intro h', apply not_le_of_lt h, exact hf h' }

end monotone

/-- A function `f` is strictly monotone if `a < b` implies `f a < f b`. -/
def strict_mono [has_lt α] [has_lt β] (f : α → β) : Prop :=
∀ ⦃a b⦄, a < b → f a < f b

namespace strict_mono
open ordering function

lemma comp [has_lt α] [has_lt β] [has_lt γ] {g : β → γ} {f : α → β}
  (hg : strict_mono g) (hf : strict_mono f) :
  strict_mono (g ∘ f) :=
λ a b h, hg (hf h)

section
variables [linear_order α] [preorder β] {f : α → β}

lemma lt_iff_lt (H : strict_mono f) {a b} :
  f a < f b ↔ a < b :=
⟨λ h, ((lt_trichotomy b a)
  .resolve_left $ λ h', lt_asymm h $ H h')
  .resolve_left $ λ e, ne_of_gt h $ congr_arg _ e, @H _ _⟩

lemma injective (H : strict_mono f) : injective f
| a b e := ((lt_trichotomy a b)
  .resolve_left $ λ h, ne_of_lt (H h) e)
  .resolve_right $ λ h, ne_of_gt (H h) e

theorem compares (H : strict_mono f) {a b} :
  ∀ {o}, compares o (f a) (f b) ↔ compares o a b
| lt := H.lt_iff_lt
| eq := ⟨λ h, H.injective h, congr_arg _⟩
| gt := H.lt_iff_lt

lemma le_iff_le (H : strict_mono f) {a b} :
  f a ≤ f b ↔ a ≤ b :=
⟨λ h, le_of_not_gt $ λ h', not_le_of_lt (H h') h,
 λ h, (lt_or_eq_of_le h).elim (λ h', le_of_lt (H h')) (λ h', h' ▸ le_refl _)⟩
end

protected lemma nat {β} [preorder β] {f : ℕ → β} (h : ∀n, f n < f (n+1)) : strict_mono f :=
by { intros n m hnm, induction hnm with m' hnm' ih, apply h, exact lt.trans ih (h _) }

-- `preorder α` isn't strong enough: if the preorder on α is an equivalence relation,
-- then `strict_mono f` is vacuously true.
lemma monotone [partial_order α] [preorder β] {f : α → β} (H : strict_mono f) : monotone f :=
λ a b h, (lt_or_eq_of_le h).rec (le_of_lt ∘ (@H _ _)) (by rintro rfl; refl)

end strict_mono

section
open function
variables [partial_order α] [partial_order β] {f : α → β}

lemma strict_mono_of_monotone_of_injective (h₁ : monotone f) (h₂ : injective f) :
  strict_mono f :=
λ a b h,
begin
  rw lt_iff_le_and_ne at ⊢ h,
  exact ⟨h₁ h.1, λ e, h.2 (h₂ e)⟩
end

end

/-- Type tag for a set with dual order: `≤` means `≥` and `<` means `>`. -/
def order_dual (α : Type*) := α

namespace order_dual
instance (α : Type*) [h : nonempty α] : nonempty (order_dual α) := h
instance (α : Type*) [has_le α] : has_le (order_dual α) := ⟨λx y:α, y ≤ x⟩
instance (α : Type*) [has_lt α] : has_lt (order_dual α) := ⟨λx y:α, y < x⟩

-- `dual_le` and `dual_lt` should not be simp lemmas:
-- they cause a loop since `α` and `order_dual α` are definitionally equal

lemma dual_le [has_le α] {a b : α} :
  @has_le.le (order_dual α) _ a b ↔ @has_le.le α _ b a := iff.rfl

lemma dual_lt [has_lt α] {a b : α} :
  @has_lt.lt (order_dual α) _ a b ↔ @has_lt.lt α _ b a := iff.rfl

instance (α : Type*) [preorder α] : preorder (order_dual α) :=
{ le_refl  := le_refl,
  le_trans := assume a b c hab hbc, le_trans hbc hab,
  lt_iff_le_not_le := λ _ _, lt_iff_le_not_le,
  .. order_dual.has_le α,
  .. order_dual.has_lt α }

instance (α : Type*) [partial_order α] : partial_order (order_dual α) :=
{ le_antisymm := assume a b hab hba, @le_antisymm α _ a b hba hab, .. order_dual.preorder α }

instance (α : Type*) [linear_order α] : linear_order (order_dual α) :=
{ le_total := assume a b:α, le_total b a, .. order_dual.partial_order α }

instance (α : Type*) [decidable_linear_order α] : decidable_linear_order (order_dual α) :=
{ decidable_le := show decidable_rel (λa b:α, b ≤ a), by apply_instance,
  decidable_lt := show decidable_rel (λa b:α, b < a), by apply_instance,
  .. order_dual.linear_order α }

instance : Π [inhabited α], inhabited (order_dual α) := id

end order_dual

/- order instances on the function space -/

instance pi.preorder {ι : Type u} {α : ι → Type v} [∀i, preorder (α i)] : preorder (Πi, α i) :=
{ le       := λx y, ∀i, x i ≤ y i,
  le_refl  := assume a i, le_refl (a i),
  le_trans := assume a b c h₁ h₂ i, le_trans (h₁ i) (h₂ i) }

instance pi.partial_order {ι : Type u} {α : ι → Type v} [∀i, partial_order (α i)] : partial_order (Πi, α i) :=
{ le_antisymm := λf g h1 h2, funext (λb, le_antisymm (h1 b) (h2 b)),
  ..pi.preorder }

theorem comp_le_comp_left_of_monotone [preorder α] [preorder β]
  {f : β → α} {g h : γ → β} (m_f : monotone f) (le_gh : g ≤ h) : has_le.le.{max w u} (f ∘ g) (f ∘ h) :=
assume x, m_f (le_gh x)

section monotone
variables [preorder α] [preorder γ]

theorem monotone_lam {f : α → β → γ} (m : ∀b, monotone (λa, f a b)) : monotone f :=
assume a a' h b, m b h

theorem monotone_app (f : β → α → γ) (b : β) (m : monotone (λa b, f b a)) : monotone (f b) :=
assume a a' h, m h b

end monotone

/-- Transfer a `preorder` on `β` to a `preorder` on `α` using a function `f : α → β`. -/
def preorder.lift {α β} (f : α → β) (i : preorder β) : preorder α :=
by exactI
{ le := λx y, f x ≤ f y,
  le_refl := λ a, le_refl _,
  le_trans := λ a b c, le_trans,
  lt := λx y, f x < f y,
  lt_iff_le_not_le := λ a b, lt_iff_le_not_le }

/-- Transfer a `partial_order` on `β` to a `partial_order` on `α` using an injective
function `f : α → β`. -/
def partial_order.lift {α β} (f : α → β) (inj : injective f) (i : partial_order β) :
  partial_order α :=
by exactI
{ le_antisymm := λ a b h₁ h₂, inj (le_antisymm h₁ h₂), .. preorder.lift f (by apply_instance) }

/-- Transfer a `linear_order` on `β` to a `linear_order` on `α` using an injective
function `f : α → β`. -/
def linear_order.lift {α β} (f : α → β) (inj : injective f) (i : linear_order β) :
  linear_order α :=
by exactI
{ le_total := λx y, le_total (f x) (f y), .. partial_order.lift f inj (by apply_instance) }

/-- Transfer a `decidable_linear_order` on `β` to a `decidable_linear_order` on `α` using
an injective function `f : α → β`. -/
def decidable_linear_order.lift {α β} (f : α → β) (inj : injective f)
  (i : decidable_linear_order β) : decidable_linear_order α :=
by exactI
{ decidable_le := λ x y, show decidable (f x ≤ f y), by apply_instance,
  decidable_lt := λ x y, show decidable (f x < f y), by apply_instance,
  decidable_eq := λ x y, decidable_of_iff _ ⟨@inj x y, congr_arg f⟩,
  .. linear_order.lift f inj (by apply_instance) }

instance subtype.preorder {α} [i : preorder α] (p : α → Prop) : preorder (subtype p) :=
preorder.lift subtype.val i

instance subtype.partial_order {α} [i : partial_order α] (p : α → Prop) : partial_order (subtype p) :=
partial_order.lift subtype.val subtype.val_injective i

instance subtype.linear_order {α} [i : linear_order α] (p : α → Prop) : linear_order (subtype p) :=
linear_order.lift subtype.val subtype.val_injective i

instance subtype.decidable_linear_order {α} [i : decidable_linear_order α] (p : α → Prop) :
  decidable_linear_order (subtype p) :=
decidable_linear_order.lift subtype.val subtype.val_injective i

instance prod.has_le (α : Type u) (β : Type v) [has_le α] [has_le β] : has_le (α × β) :=
⟨λp q, p.1 ≤ q.1 ∧ p.2 ≤ q.2⟩

instance prod.preorder (α : Type u) (β : Type v) [preorder α] [preorder β] : preorder (α × β) :=
{ le_refl  := assume ⟨a, b⟩, ⟨le_refl a, le_refl b⟩,
  le_trans := assume ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩,
    ⟨le_trans hac hce, le_trans hbd hdf⟩,
  .. prod.has_le α β }

/-- The pointwise partial order on a product.
    (The lexicographic ordering is defined in order/lexicographic.lean, and the instances are
    available via the type synonym `lex α β = α × β`.) -/
instance prod.partial_order (α : Type u) (β : Type v) [partial_order α] [partial_order β] :
  partial_order (α × β) :=
{ le_antisymm := assume ⟨a, b⟩ ⟨c, d⟩ ⟨hac, hbd⟩ ⟨hca, hdb⟩,
    prod.ext (le_antisymm hac hca) (le_antisymm hbd hdb),
  .. prod.preorder α β }

/-!
### Additional order classes
-/

/-- order without a top element; somtimes called cofinal -/
class no_top_order (α : Type u) [preorder α] : Prop :=
(no_top : ∀a:α, ∃a', a < a')

lemma no_top [preorder α] [no_top_order α] : ∀a:α, ∃a', a < a' :=
no_top_order.no_top

/-- order without a bottom element; somtimes called coinitial or dense -/
class no_bot_order (α : Type u) [preorder α] : Prop :=
(no_bot : ∀a:α, ∃a', a' < a)

lemma no_bot [preorder α] [no_bot_order α] : ∀a:α, ∃a', a' < a :=
no_bot_order.no_bot

instance order_dual.no_top_order (α : Type u) [preorder α] [no_bot_order α] :
  no_top_order (order_dual α) :=
⟨λ a, @no_bot α _ _ a⟩

instance order_dual.no_bot_order (α : Type u) [preorder α] [no_top_order α] :
  no_bot_order (order_dual α) :=
⟨λ a, @no_top α _ _ a⟩

/-- An order is dense if there is an element between any pair of distinct elements. -/
class densely_ordered (α : Type u) [preorder α] : Prop :=
(dense : ∀a₁ a₂:α, a₁ < a₂ → ∃a, a₁ < a ∧ a < a₂)

lemma dense [preorder α] [densely_ordered α] : ∀{a₁ a₂:α}, a₁ < a₂ → ∃a, a₁ < a ∧ a < a₂ :=
densely_ordered.dense

instance order_dual.densely_ordered (α : Type u) [preorder α] [densely_ordered α] :
  densely_ordered (order_dual α) :=
⟨λ a₁ a₂ ha, (@dense α _ _ _ _ ha).imp $ λ a, and.symm⟩

lemma le_of_forall_le_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α} (h : ∀a₃>a₂, a₁ ≤ a₃) :
  a₁ ≤ a₂ :=
le_of_not_gt $ assume ha,
  let ⟨a, ha₁, ha₂⟩ := dense ha in
  lt_irrefl a $ lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)

lemma eq_of_le_of_forall_le_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h₁ : a₂ ≤ a₁) (h₂ : ∀a₃>a₂, a₁ ≤ a₃) : a₁ = a₂ :=
le_antisymm (le_of_forall_le_of_dense h₂) h₁

lemma le_of_forall_ge_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}(h : ∀a₃<a₁, a₂ ≥ a₃) :
  a₁ ≤ a₂ :=
le_of_not_gt $ assume ha,
  let ⟨a, ha₁, ha₂⟩ := dense ha in
  lt_irrefl a $ lt_of_le_of_lt (h _ ‹a < a₁›) ‹a₂ < a›

lemma eq_of_le_of_forall_ge_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h₁ : a₂ ≤ a₁) (h₂ : ∀a₃<a₁, a₂ ≥ a₃) : a₁ = a₂ :=
le_antisymm (le_of_forall_ge_of_dense h₂) h₁

lemma dense_or_discrete [linear_order α] (a₁ a₂ : α) :
  (∃a, a₁ < a ∧ a < a₂) ∨ ((∀a>a₁, a ≥ a₂) ∧ (∀a<a₂, a ≤ a₁)) :=
classical.or_iff_not_imp_left.2 $ assume h,
  ⟨assume a ha₁, le_of_not_gt $ assume ha₂, h ⟨a, ha₁, ha₂⟩,
    assume a ha₂, le_of_not_gt $ assume ha₁, h ⟨a, ha₁, ha₂⟩⟩

lemma trans_trichotomous_left [is_trans α r] [is_trichotomous α r] {a b c : α} :
  ¬r b a → r b c → r a c :=
begin
  intros h₁ h₂, rcases trichotomous_of r a b with h₃|h₃|h₃,
  exact trans h₃ h₂, rw h₃, exact h₂, exfalso, exact h₁ h₃
end

lemma trans_trichotomous_right [is_trans α r] [is_trichotomous α r] {a b c : α} :
  r a b → ¬r c b → r a c :=
begin
  intros h₁ h₂, rcases trichotomous_of r b c with h₃|h₃|h₃,
  exact trans h₁ h₃, rw ←h₃, exact h₁, exfalso, exact h₂ h₃
end

variables {s : β → β → Prop} {t : γ → γ → Prop}

theorem is_irrefl_of_is_asymm [is_asymm α r] : is_irrefl α r :=
⟨λ a h, asymm h h⟩

/-- Construct a partial order from a `is_strict_order` relation -/
def partial_order_of_SO (r) [is_strict_order α r] : partial_order α :=
{ le := λ x y, x = y ∨ r x y,
  lt := r,
  le_refl := λ x, or.inl rfl,
  le_trans := λ x y z h₁ h₂,
    match y, z, h₁, h₂ with
    | _, _, or.inl rfl, h₂ := h₂
    | _, _, h₁, or.inl rfl := h₁
    | _, _, or.inr h₁, or.inr h₂ := or.inr (trans h₁ h₂)
    end,
  le_antisymm := λ x y h₁ h₂,
    match y, h₁, h₂ with
    | _, or.inl rfl, h₂ := rfl
    | _, h₁, or.inl rfl := rfl
    | _, or.inr h₁, or.inr h₂ := (asymm h₁ h₂).elim
    end,
  lt_iff_le_not_le := λ x y,
    ⟨λ h, ⟨or.inr h, not_or
      (λ e, by rw e at h; exact irrefl _ h)
      (asymm h)⟩,
    λ ⟨h₁, h₂⟩, h₁.resolve_left (λ e, h₂ $ e ▸ or.inl rfl)⟩ }

section prio
set_option default_priority 100 -- see Note [default priority]
/-- This is basically the same as `is_strict_total_order`, but that definition is
  in Type (probably by mistake) and also has redundant assumptions. -/
@[algebra] class is_strict_total_order' (α : Type u) (lt : α → α → Prop) extends is_trichotomous α lt, is_strict_order α lt : Prop.
end prio

/-- Construct a linear order from a `is_strict_total_order'` relation -/
def linear_order_of_STO' (r) [is_strict_total_order' α r] : linear_order α :=
{ le_total := λ x y,
    match y, trichotomous_of r x y with
    | y, or.inl h := or.inl (or.inr h)
    | _, or.inr (or.inl rfl) := or.inl (or.inl rfl)
    | _, or.inr (or.inr h) := or.inr (or.inr h)
    end,
  ..partial_order_of_SO r }

/-- Construct a decidable linear order from a `is_strict_total_order'` relation -/
def decidable_linear_order_of_STO' (r) [is_strict_total_order' α r] [decidable_rel r] : decidable_linear_order α :=
by letI LO := linear_order_of_STO' r; exact
{ decidable_le := λ x y, decidable_of_iff (¬ r y x) (@not_lt _ _ y x),
  ..LO }

noncomputable def classical.DLO (α) [LO : linear_order α] : decidable_linear_order α :=
{ decidable_le := classical.dec_rel _, ..LO }

theorem is_strict_total_order'.swap (r) [is_strict_total_order' α r] : is_strict_total_order' α (swap r) :=
{..is_trichotomous.swap r, ..is_strict_order.swap r}

instance [linear_order α] : is_strict_total_order' α (<) := {}

/-- A connected order is one satisfying the condition `a < c → a < b ∨ b < c`.
  This is recognizable as an intuitionistic substitute for `a ≤ b ∨ b ≤ a` on
  the constructive reals, and is also known as negative transitivity,
  since the contrapositive asserts transitivity of the relation `¬ a < b`.  -/
@[algebra] class is_order_connected (α : Type u) (lt : α → α → Prop) : Prop :=
(conn : ∀ a b c, lt a c → lt a b ∨ lt b c)

theorem is_order_connected.neg_trans {r : α → α → Prop} [is_order_connected α r]
  {a b c} (h₁ : ¬ r a b) (h₂ : ¬ r b c) : ¬ r a c :=
mt (is_order_connected.conn a b c) $ by simp [h₁, h₂]

theorem is_strict_weak_order_of_is_order_connected [is_asymm α r]
  [is_order_connected α r] : is_strict_weak_order α r :=
{ trans := λ a b c h₁ h₂, (is_order_connected.conn _ c _ h₁).resolve_right (asymm h₂),
  incomp_trans := λ a b c ⟨h₁, h₂⟩ ⟨h₃, h₄⟩,
    ⟨is_order_connected.neg_trans h₁ h₃, is_order_connected.neg_trans h₄ h₂⟩,
  ..@is_irrefl_of_is_asymm α r _ }

@[priority 100] -- see Note [lower instance priority]
instance is_order_connected_of_is_strict_total_order'
  [is_strict_total_order' α r] : is_order_connected α r :=
⟨λ a b c h, (trichotomous _ _).imp_right (λ o,
  o.elim (λ e, e ▸ h) (λ h', trans h' h))⟩

@[priority 100] -- see Note [lower instance priority]
instance is_strict_total_order_of_is_strict_total_order'
  [is_strict_total_order' α r] : is_strict_total_order α r :=
{..is_strict_weak_order_of_is_order_connected}

instance [linear_order α] : is_strict_total_order α (<) := by apply_instance
instance [linear_order α] : is_order_connected α (<) := by apply_instance
instance [linear_order α] : is_incomp_trans α (<) := by apply_instance
instance [linear_order α] : is_strict_weak_order α (<) := by apply_instance

/-- An extensional relation is one in which an element is determined by its set
  of predecessors. It is named for the `x ∈ y` relation in set theory, whose
  extensionality is one of the first axioms of ZFC. -/
@[algebra] class is_extensional (α : Type u) (r : α → α → Prop) : Prop :=
(ext : ∀ a b, (∀ x, r x a ↔ r x b) → a = b)

@[priority 100] -- see Note [lower instance priority]
instance is_extensional_of_is_strict_total_order'
  [is_strict_total_order' α r] : is_extensional α r :=
⟨λ a b H, ((@trichotomous _ r _ a b)
  .resolve_left $ mt (H _).2 (irrefl a))
  .resolve_right $ mt (H _).1 (irrefl b)⟩

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A well order is a well-founded linear order. -/
@[algebra] class is_well_order (α : Type u) (r : α → α → Prop) extends is_strict_total_order' α r : Prop :=
(wf : well_founded r)
end prio

@[priority 100] -- see Note [lower instance priority]
instance is_well_order.is_strict_total_order {α} (r : α → α → Prop) [is_well_order α r] : is_strict_total_order α r := by apply_instance
@[priority 100] -- see Note [lower instance priority]
instance is_well_order.is_extensional {α} (r : α → α → Prop) [is_well_order α r] : is_extensional α r := by apply_instance
@[priority 100] -- see Note [lower instance priority]
instance is_well_order.is_trichotomous {α} (r : α → α → Prop) [is_well_order α r] : is_trichotomous α r := by apply_instance
@[priority 100] -- see Note [lower instance priority]
instance is_well_order.is_trans {α} (r : α → α → Prop) [is_well_order α r] : is_trans α r := by apply_instance
@[priority 100] -- see Note [lower instance priority]
instance is_well_order.is_irrefl {α} (r : α → α → Prop) [is_well_order α r] : is_irrefl α r := by apply_instance
@[priority 100] -- see Note [lower instance priority]
instance is_well_order.is_asymm {α} (r : α → α → Prop) [is_well_order α r] : is_asymm α r := by apply_instance

noncomputable def decidable_linear_order_of_is_well_order (r : α → α → Prop) [is_well_order α r] :
  decidable_linear_order α :=
by { haveI := linear_order_of_STO' r, exact classical.DLO α }

instance empty_relation.is_well_order [subsingleton α] : is_well_order α empty_relation :=
{ trichotomous := λ a b, or.inr $ or.inl $ subsingleton.elim _ _,
  irrefl       := λ a, id,
  trans        := λ a b c, false.elim,
  wf           := ⟨λ a, ⟨_, λ y, false.elim⟩⟩ }

instance nat.lt.is_well_order : is_well_order ℕ (<) := ⟨nat.lt_wf⟩

instance sum.lex.is_well_order [is_well_order α r] [is_well_order β s] : is_well_order (α ⊕ β) (sum.lex r s) :=
{ trichotomous := λ a b, by cases a; cases b; simp; apply trichotomous,
  irrefl       := λ a, by cases a; simp; apply irrefl,
  trans        := λ a b c, by cases a; cases b; simp; cases c; simp; apply trans,
  wf           := sum.lex_wf is_well_order.wf is_well_order.wf }

instance prod.lex.is_well_order [is_well_order α r] [is_well_order β s] : is_well_order (α × β) (prod.lex r s) :=
{ trichotomous := λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩,
    match @trichotomous _ r _ a₁ b₁ with
    | or.inl h₁ := or.inl $ prod.lex.left _ _ h₁
    | or.inr (or.inr h₁) := or.inr $ or.inr $ prod.lex.left _ _ h₁
    | or.inr (or.inl e) := e ▸  match @trichotomous _ s _ a₂ b₂ with
      | or.inl h := or.inl $ prod.lex.right _ h
      | or.inr (or.inr h) := or.inr $ or.inr $ prod.lex.right _ h
      | or.inr (or.inl e) := e ▸ or.inr $ or.inl rfl
      end
    end,
  irrefl := λ ⟨a₁, a₂⟩ h, by cases h with _ _ _ _ h _ _ _ h;
     [exact irrefl _ h, exact irrefl _ h],
  trans := λ a b c h₁ h₂, begin
    cases h₁ with a₁ a₂ b₁ b₂ ab a₁ b₁ b₂ ab;
    cases h₂ with _ _ c₁ c₂ bc _ _ c₂ bc,
    { exact prod.lex.left _ _ (trans ab bc) },
    { exact prod.lex.left _ _ ab },
    { exact prod.lex.left _ _ bc },
    { exact prod.lex.right _ (trans ab bc) }
  end,
  wf := prod.lex_wf is_well_order.wf is_well_order.wf }

/-- An unbounded or cofinal set -/
def unbounded (r : α → α → Prop) (s : set α) : Prop := ∀ a, ∃ b ∈ s, ¬ r b a
/-- A bounded or final set -/
def bounded (r : α → α → Prop) (s : set α) : Prop := ∃a, ∀ b ∈ s, r b a

@[simp] lemma not_bounded_iff {r : α → α → Prop} (s : set α) : ¬bounded r s ↔ unbounded r s :=
begin
  classical,
  simp only [bounded, unbounded, not_forall, not_exists, exists_prop, not_and, not_not]
end

@[simp] lemma not_unbounded_iff {r : α → α → Prop} (s : set α) : ¬unbounded r s ↔ bounded r s :=
by { classical, rw [not_iff_comm, not_bounded_iff] }

namespace well_founded
/-- If `r` is a well founded relation, then any nonempty set has a minimum element
with respect to `r`. -/
theorem has_min {α} {r : α → α → Prop} (H : well_founded r)
  (s : set α) : s.nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬ r x a
| ⟨a, ha⟩ := (acc.rec_on (H.apply a) $ λ x _ IH, classical.not_imp_not.1 $ λ hne hx, hne $
  ⟨x, hx, λ y hy hyx, hne $ IH y hyx hy⟩) ha

/-- The minimum element of a nonempty set in a well-founded order -/
noncomputable def min {α} {r : α → α → Prop} (H : well_founded r)
  (p : set α) (h : p.nonempty) : α :=
classical.some (H.has_min p h)

theorem min_mem {α} {r : α → α → Prop} (H : well_founded r)
  (p : set α) (h : p.nonempty) : H.min p h ∈ p :=
let ⟨h, _⟩ := classical.some_spec (H.has_min p h) in h

theorem not_lt_min {α} {r : α → α → Prop} (H : well_founded r)
  (p : set α) (h : p.nonempty) {x} (xp : x ∈ p) : ¬ r x (H.min p h) :=
let ⟨_, h'⟩ := classical.some_spec (H.has_min p h) in h' _ xp

open set
protected noncomputable def sup {α} {r : α → α → Prop} (wf : well_founded r) (s : set α)
  (h : bounded r s) : α :=
wf.min { x | ∀a ∈ s, r a x } h

protected lemma lt_sup {α} {r : α → α → Prop} (wf : well_founded r) {s : set α} (h : bounded r s)
  {x} (hx : x ∈ s) : r x (wf.sup s h) :=
min_mem wf { x | ∀a ∈ s, r a x } h x hx

section
open_locale classical
protected noncomputable def succ {α} {r : α → α → Prop} (wf : well_founded r) (x : α) : α :=
if h : ∃y, r x y then wf.min { y | r x y } h else x

protected lemma lt_succ {α} {r : α → α → Prop} (wf : well_founded r) {x : α} (h : ∃y, r x y) :
  r x (wf.succ x) :=
by { rw [well_founded.succ, dif_pos h], apply min_mem }
end

protected lemma lt_succ_iff {α} {r : α → α → Prop} [wo : is_well_order α r] {x : α} (h : ∃y, r x y)
  (y : α) : r y (wo.wf.succ x) ↔ r y x ∨ y = x :=
begin
  split,
  { intro h', have : ¬r x y,
    { intro hy, rw [well_founded.succ, dif_pos] at h',
      exact wo.wf.not_lt_min _ h hy h' },
    rcases trichotomous_of r x y with hy | hy | hy,
    exfalso, exact this hy,
    right, exact hy.symm,
    left, exact hy },
  rintro (hy | rfl), exact trans hy (wo.wf.lt_succ h), exact wo.wf.lt_succ h
end

end well_founded

variable (r)
local infix ` ≼ ` : 50 := r

/-- A family of elements of α is directed (with respect to a relation `≼` on α)
  if there is a member of the family `≼`-above any pair in the family.  -/
def directed {ι : Sort v} (f : ι → α) := ∀x y, ∃z, f x ≼ f z ∧ f y ≼ f z

/-- A subset of α is directed if there is an element of the set `≼`-above any
  pair of elements in the set. -/
def directed_on (s : set α) := ∀ (x ∈ s) (y ∈ s), ∃z ∈ s, x ≼ z ∧ y ≼ z

theorem directed_on_iff_directed {s} : @directed_on α r s ↔ directed r (coe : s → α) :=
by simp [directed, directed_on]; refine ball_congr (λ x hx, by simp; refl)

theorem directed_on_image {s} {f : β → α} :
  directed_on r (f '' s) ↔ directed_on (f ⁻¹'o r) s :=
by simp only [directed_on, set.ball_image_iff, set.bex_image_iff, order.preimage]

theorem directed_on.mono {s : set α} (h : directed_on r s)
  {r' : α → α → Prop} (H : ∀ {a b}, r a b → r' a b) :
  directed_on r' s :=
λ x hx y hy, let ⟨z, zs, xz, yz⟩ := h x hx y hy in ⟨z, zs, H xz, H yz⟩

theorem directed_comp {ι} (f : ι → β) (g : β → α) :
  directed r (g ∘ f) ↔ directed (g ⁻¹'o r) f := iff.rfl

variable {r}

theorem directed.mono {s : α → α → Prop} {ι} {f : ι → α}
  (H : ∀ a b, r a b → s a b) (h : directed r f) : directed s f :=
λ a b, let ⟨c, h₁, h₂⟩ := h a b in ⟨c, H _ _ h₁, H _ _ h₂⟩

theorem directed.mono_comp {ι} {rb : β → β → Prop} {g : α → β} {f : ι → α}
  (hg : ∀ ⦃x y⦄, x ≼ y → rb (g x) (g y)) (hf : directed r f) :
  directed rb (g ∘ f) :=
(directed_comp rb f g).2 $ hf.mono hg

section prio
set_option default_priority 100 -- see Note [default priority]
class directed_order (α : Type u) extends preorder α :=
(directed : ∀ i j : α, ∃ k, i ≤ k ∧ j ≤ k)
end prio
