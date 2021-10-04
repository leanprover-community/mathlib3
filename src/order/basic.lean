/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import data.subtype
import data.prod

/-!
# Basic definitions about `≤` and `<`

## Definitions

- `order_dual α` : A type tag reversing the meaning of all inequalities.

### Predicates on functions

* `monotone f`: A function between two types equipped with `≤` is monotone if `a ≤ b` implies
  `f a ≤ f b`.
* `antitone f`: A function between two types equipped with `≤` is antitone if `a ≤ b` implies
  `f b ≤ f a`.
* `monotone_on f s`: Same as `monotone f`, but for all `a, b ∈ s`.
* `antitone_on f s`: Same as `antitone f`, but for all `a, b ∈ s`.
* `strict_mono f` : A function between two types equipped with `<` is strictly monotone if
  `a < b` implies `f a < f b`.
* `strict_anti f` : A function between two types equipped with `<` is strictly antitone if
  `a < b` implies `f b < f a`.
* `strict_mono_on f s`: Same as `strict_mono f`, but for all `a, b ∈ s`.
* `strict_anti_on f s`: Same as `strict_anti f`, but for all `a, b ∈ s`.

### Transfering orders

- `order.preimage`, `preorder.lift`: Transfers a (pre)order on `β` to an order on `α`
  using a function `f : α → β`.
- `partial_order.lift`, `linear_order.lift`: Transfers a partial (resp., linear) order on `β` to a
  partial (resp., linear) order on `α` using an injective function `f`.

### Extra classes

- `no_top_order`, `no_bot_order`: An order without a maximal/minimal element.
- `densely_ordered`: An order with no gap, i.e. for any two elements `a < b` there exists `c` such
  that `a < c < b`.

## Main theorems

- `monotone_nat_of_le_succ`: If `f : ℕ → α` and `f n ≤ f (n + 1)` for all `n`, then `f` is
  monotone.
- `antitone_nat_of_succ_le`: If `f : ℕ → α` and `f (n + 1) ≤ f n` for all `n`, then `f` is
  antitone.
- `strict_mono_nat_of_lt_succ`: If `f : ℕ → α` and `f n < f (n + 1)` for all `n`, then `f` is
  strictly monotone.
- `strict_anti_nat_of_succ_lt`: If `f : ℕ → α` and `f (n + 1) < f n` for all `n`, then `f` is
  strictly antitone.

## TODO

- expand module docs
- automatic construction of dual definitions / theorems

## See also

- `algebra.order.basic` for basic lemmas about orders, and projection notation for orders

## Tags

preorder, order, partial order, linear order, monotone, strictly monotone
-/

open function

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} {r : α → α → Prop}

attribute [simp] le_refl

@[simp] lemma lt_self_iff_false [preorder α] (a : α) : a < a ↔ false :=
⟨lt_irrefl a, false.elim⟩

attribute [ext] has_le

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

lemma dual_compares [has_lt α] {a b : α} {o : ordering} :
  @ordering.compares (order_dual α) _ o a b ↔ @ordering.compares α _ o b a :=
by { cases o, exacts [iff.rfl, eq_comm, iff.rfl] }

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

theorem cmp_le_flip {α} [has_le α] [@decidable_rel α (≤)] (x y : α) :
  @cmp_le (order_dual α) _ _ x y = cmp_le y x := rfl

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

/-! ### Monotonicity -/

section monotone_def
variables [preorder α] [preorder β]

/-- A function `f` is monotone if `a ≤ b` implies `f a ≤ f b`. -/
def monotone (f : α → β) : Prop := ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

/-- A function `f` is antitone if `a ≤ b` implies `f b ≤ f a`. -/
def antitone (f : α → β) : Prop := ∀ ⦃a b⦄, a ≤ b → f b ≤ f a

/-- A function `f` is antitone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f b ≤ f a`. -/
def monotone_on (f : α → β) (s : set α) : Prop :=
∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a ≤ b → f a ≤ f b

/-- A function `f` is monotone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f a ≤ f b`. -/
def antitone_on (f : α → β) (s : set α) : Prop :=
∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a ≤ b → f b ≤ f a

/-- A function `f` is strictly monotone if `a < b` implies `f a < f b`. -/
def strict_mono (f : α → β) : Prop :=
∀ ⦃a b⦄, a < b → f a < f b

/-- A function `f` is strictly antitone if `a < b` implies `f b < f a`. -/
def strict_anti (f : α → β) : Prop :=
∀ ⦃a b⦄, a < b → f b < f a

/-- A function `f` is strictly monotone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f a < f b`. -/
def strict_mono_on (f : α → β) (s : set α) : Prop :=
∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a < b → f a < f b

/-- A function `f` is strictly antitone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f b < f a`. -/
def strict_anti_on (f : α → β) (s : set α) : Prop :=
∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a < b → f b < f a

end monotone_def

/-! #### Monotonicity on the dual order -/

section order_dual
open order_dual
variables [preorder α] [preorder β] {f : α → β} {s : set α}

protected theorem monotone.dual (hf : monotone f) :
  @monotone (order_dual α) (order_dual β) _ _ f :=
λ a b h, hf h

protected lemma monotone.dual_left  (hf : monotone f) :
  @antitone (order_dual α) β _ _ f :=
λ a b h, hf h

protected lemma monotone.dual_right  (hf : monotone f) :
  @antitone α (order_dual β) _ _ f :=
λ a b h, hf h

protected theorem antitone.dual  (hf : antitone f) :
  @antitone (order_dual α) (order_dual β) _ _ f :=
λ a b h, hf h

protected lemma antitone.dual_left  (hf : antitone f) :
  @monotone (order_dual α) β _ _ f :=
λ a b h, hf h

protected lemma antitone.dual_right  (hf : antitone f) :
  @monotone α (order_dual β) _ _ f :=
λ a b h, hf h

protected theorem monotone_on.dual (hf : monotone_on f s) :
  @monotone_on (order_dual α) (order_dual β) _ _ f s :=
λ a ha b hb, hf hb ha

protected lemma monotone_on.dual_left (hf : monotone_on f s) :
  @antitone_on (order_dual α) β _ _ f s :=
λ a ha b hb, hf hb ha

protected lemma monotone_on.dual_right (hf : monotone_on f s) :
  @antitone_on α (order_dual β) _ _ f s :=
λ a ha b hb, hf ha hb

protected theorem antitone_on.dual (hf : antitone_on f s) :
  @antitone_on (order_dual α) (order_dual β) _ _ f s :=
λ a ha b hb, hf hb ha

protected lemma antitone_on.dual_left (hf : antitone_on f s) :
  @monotone_on (order_dual α) β _ _ f s :=
λ a ha b hb, hf hb ha

protected lemma antitone_on.dual_right (hf : antitone_on f s) :
  @monotone_on α (order_dual β) _ _ f s :=
λ a ha b hb, hf ha hb

protected theorem strict_mono.dual (hf : strict_mono f) :
  @strict_mono (order_dual α) (order_dual β) _ _ f :=
λ a b h, hf h

protected lemma strict_mono.dual_left  (hf : strict_mono f) :
  @strict_anti (order_dual α) β _ _ f :=
λ a b h, hf h

protected lemma strict_mono.dual_right  (hf : strict_mono f) :
  @strict_anti α (order_dual β) _ _ f :=
λ a b h, hf h

protected theorem strict_anti.dual  (hf : strict_anti f) :
  @strict_anti (order_dual α) (order_dual β) _ _ f :=
λ a b h, hf h

protected lemma strict_anti.dual_left  (hf : strict_anti f) :
  @strict_mono (order_dual α) β _ _ f :=
λ a b h, hf h

protected lemma strict_anti.dual_right  (hf : strict_anti f) :
  @strict_mono α (order_dual β) _ _ f :=
λ a b h, hf h

protected theorem strict_mono_on.dual (hf : strict_mono_on f s) :
  @strict_mono_on (order_dual α) (order_dual β) _ _ f s :=
λ a ha b hb, hf hb ha

protected lemma strict_mono_on.dual_left (hf : strict_mono_on f s) :
  @strict_anti_on (order_dual α) β _ _ f s :=
λ a ha b hb, hf hb ha

protected lemma strict_mono_on.dual_right (hf : strict_mono_on f s) :
  @strict_anti_on α (order_dual β) _ _ f s :=
λ a ha b hb, hf ha hb

protected theorem strict_anti_on.dual (hf : strict_anti_on f s) :
  @strict_anti_on (order_dual α) (order_dual β) _ _ f s :=
λ a ha b hb, hf hb ha

protected lemma strict_anti_on.dual_left (hf : strict_anti_on f s) :
  @strict_mono_on (order_dual α) β _ _ f s :=
λ a ha b hb, hf hb ha

protected lemma strict_anti_on.dual_right (hf : strict_anti_on f s) :
  @strict_mono_on α (order_dual β) _ _ f s :=
λ a ha b hb, hf ha hb

end order_dual

/-! #### Monotonicity in function spaces -/

section preorder
variables [preorder α]

theorem monotone.comp_le_comp_left [preorder β]
  {f : β → α} {g h : γ → β} (hf : monotone f) (le_gh : g ≤ h) :
  has_le.le.{max w u} (f ∘ g) (f ∘ h) :=
λ x, hf (le_gh x)

variables [preorder γ]

theorem monotone_lam {f : α → β → γ} (hf : ∀ b, monotone (λ a, f a b)) : monotone f :=
λ a a' h b, hf b h

theorem monotone_app (f : β → α → γ) (b : β) (hf : monotone (λ a b, f b a)) : monotone (f b) :=
λ a a' h, hf h b

theorem antitone_lam {f : α → β → γ} (hf : ∀ b, antitone (λ a, f a b)) : antitone f :=
λ a a' h b, hf b h

theorem antitone_app (f : β → α → γ) (b : β) (hf : antitone (λ a b, f b a)) : antitone (f b) :=
λ a a' h, hf h b

end preorder

lemma function.monotone_eval {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] (i : ι) :
  monotone (function.eval i : (Π i, α i) → α i) :=
λ f g H, H i

/-! #### Monotonicity hierarchy -/

section preorder
variables [preorder α]

section preorder
variables [preorder β] {f : α → β}

protected lemma monotone.monotone_on (hf : monotone f) (s : set α) : monotone_on f s :=
λ a _ b _ h, hf h

protected lemma antitone.antitone_on (hf : antitone f) (s : set α) : antitone_on f s :=
λ a _ b _ h, hf h

lemma monotone_on_univ : monotone_on f set.univ ↔ monotone f :=
⟨λ h a b, h trivial trivial, λ h, h.monotone_on _⟩

lemma antitone_on_univ : antitone_on f set.univ ↔ antitone f :=
⟨λ h a b, h trivial trivial, λ h, h.antitone_on _⟩

protected lemma strict_mono.strict_mono_on (hf : strict_mono f) (s : set α) : strict_mono_on f s :=
λ a _ b _ h, hf h

protected lemma strict_anti.strict_anti_on (hf : strict_anti f) (s : set α) : strict_anti_on f s :=
λ a _ b _ h, hf h

lemma strict_mono_on_univ : strict_mono_on f set.univ ↔ strict_mono f :=
⟨λ h a b, h trivial trivial, λ h, h.strict_mono_on _⟩

lemma strict_anti_on_univ : strict_anti_on f set.univ ↔ strict_anti f :=
⟨λ h a b, h trivial trivial, λ h, h.strict_anti_on _⟩

end preorder

section partial_order
variables [partial_order β] {f : α → β}

lemma monotone.strict_mono_of_injective (h₁ : monotone f) (h₂ : injective f) : strict_mono f :=
λ a b h, (h₁ h.le).lt_of_ne (λ H, h.ne $ h₂ H)

lemma antitone.strict_anti_of_injective (h₁ : antitone f) (h₂ : injective f) : strict_anti f :=
λ a b h, (h₁ h.le).lt_of_ne (λ H, h.ne $ h₂ H.symm)

end partial_order
end preorder

section partial_order
variables [partial_order α] [preorder β] {f : α → β}

-- `preorder α` isn't strong enough: if the preorder on `α` is an equivalence relation,
-- then `strict_mono f` is vacuously true.
protected lemma strict_mono.monotone (hf : strict_mono f) : monotone f :=
λ a b h, h.eq_or_lt.rec (by { rintro rfl, refl }) (le_of_lt ∘ (@hf _ _))

protected lemma strict_anti.antitone (hf : strict_anti f) : antitone f :=
λ a b h, h.eq_or_lt.rec (by { rintro rfl, refl }) (le_of_lt ∘ (@hf _ _))

end partial_order

/-! #### Miscellaneous monotonicity results -/

lemma monotone_id [preorder α] : monotone (id : α → α) := λ a b, id

lemma strict_mono_id [preorder α] : strict_mono (id : α → α) := λ a b, id

theorem monotone_const [preorder α] [preorder β] {c : β} : monotone (λ (a : α), c) :=
λ a b _, le_refl c

theorem antitone_const [preorder α] [preorder β] {c : β} : antitone (λ (a : α), c) :=
λ a b _, le_refl c

lemma strict_mono_of_le_iff_le [preorder α] [preorder β] {f : α → β}
  (h : ∀ x y, x ≤ y ↔ f x ≤ f y) : strict_mono f :=
λ a b, by simp [lt_iff_le_not_le, h] {contextual := tt}

lemma injective_of_lt_imp_ne [linear_order α] {f : α → β} (h : ∀ x y, x < y → f x ≠ f y) :
  injective f :=
begin
  intros x y k,
  contrapose k,
  rw [←ne.def, ne_iff_lt_or_gt] at k,
  cases k,
  { exact h _ _ k },
  { exact (h _ _ k).symm }
end

lemma injective_of_le_imp_le [partial_order α] [preorder β] (f : α → β)
  (h : ∀ {x y}, f x ≤ f y → x ≤ y) : injective f :=
λ x y hxy, (h hxy.le).antisymm (h hxy.ge)

section preorder
variables [preorder α] [preorder β] {f g : α → β}

protected lemma strict_mono.ite' (hf : strict_mono f) (hg : strict_mono g) {p : α → Prop}
  [decidable_pred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x)
  (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → f x < g y) :
  strict_mono (λ x, if p x then f x else g x) :=
begin
  intros x y h,
  by_cases hy : p y,
  { have hx : p x := hp h hy,
    simpa [hx, hy] using hf h },
  by_cases hx : p x,
  { simpa [hx, hy] using hfg hx hy h },
  { simpa [hx, hy] using hg h}
end

protected lemma strict_mono.ite (hf : strict_mono f) (hg : strict_mono g) {p : α → Prop}
  [decidable_pred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, f x ≤ g x) :
  strict_mono (λ x, if p x then f x else g x) :=
hf.ite' hg hp $ λ x y hx hy h, (hf h).trans_le (hfg y)

protected lemma strict_anti.ite' (hf : strict_anti f) (hg : strict_anti g) {p : α → Prop}
  [decidable_pred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x)
  (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → g y < f x) :
  strict_anti (λ x, if p x then f x else g x) :=
@strict_mono.ite' α (order_dual β) _ _ f g hf hg p _ hp hfg

protected lemma strict_anti.ite (hf : strict_anti f) (hg : strict_anti g) {p : α → Prop}
  [decidable_pred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, g x ≤ f x) :
  strict_anti (λ x, if p x then f x else g x) :=
hf.ite' hg hp $ λ x y hx hy h, (hfg y).trans_lt (hf h)

end preorder

/-! #### Monotonicity under composition -/

section composition
variables [preorder α] [preorder β] [preorder γ] {g : β → γ} {f : α → β} {s : set α}

protected lemma monotone.comp (hg : monotone g) (hf : monotone f) :
  monotone (g ∘ f) :=
λ a b h, hg (hf h)

lemma monotone.comp_antitone (hg : monotone g) (hf : antitone f) :
  antitone (g ∘ f) :=
λ a b h, hg (hf h)

protected lemma antitone.comp (hg : antitone g) (hf : antitone f) :
  monotone (g ∘ f) :=
λ a b h, hg (hf h)

lemma antitone.comp_monotone (hg : antitone g) (hf : monotone f) :
  antitone (g ∘ f) :=
λ a b h, hg (hf h)

protected lemma monotone.iterate {f : α → α} (hf : monotone f) (n : ℕ) : monotone (f^[n]) :=
nat.rec_on n monotone_id (λ n h, h.comp hf)

protected lemma monotone.comp_monotone_on (hg : monotone g) (hf : monotone_on f s) :
  monotone_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

lemma monotone.comp_antitone_on (hg : monotone g) (hf : antitone_on f s) :
  antitone_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

protected lemma antitone.comp_antitone_on (hg : antitone g) (hf : antitone_on f s) :
  monotone_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

lemma antitone.comp_monotone_on (hg : antitone g) (hf : monotone_on f s) :
  antitone_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

protected lemma strict_mono.comp (hg : strict_mono g) (hf : strict_mono f) :
  strict_mono (g ∘ f) :=
λ a b h, hg (hf h)

lemma strict_mono.comp_strict_anti (hg : strict_mono g) (hf : strict_anti f) :
  strict_anti (g ∘ f) :=
λ a b h, hg (hf h)

protected lemma strict_anti.comp (hg : strict_anti g) (hf : strict_anti f) :
  strict_mono (g ∘ f) :=
λ a b h, hg (hf h)

lemma strict_anti.comp_strict_mono (hg : strict_anti g) (hf : strict_mono f) :
  strict_anti (g ∘ f) :=
λ a b h, hg (hf h)

protected lemma strict_mono.iterate {f : α → α} (hf : strict_mono f) (n : ℕ) :
  strict_mono (f^[n]) :=
nat.rec_on n strict_mono_id (λ n h, h.comp hf)

protected lemma strict_mono.comp_strict_mono_on (hg : strict_mono g) (hf : strict_mono_on f s) :
  strict_mono_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

lemma strict_mono.comp_strict_anti_on (hg : strict_mono g) (hf : strict_anti_on f s) :
  strict_anti_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

protected lemma strict_anti.comp_strict_anti_on (hg : strict_anti g) (hf : strict_anti_on f s) :
  strict_mono_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

lemma strict_anti.comp_strict_mono_on (hg : strict_anti g) (hf : strict_mono_on f s) :
  strict_anti_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

end composition

/-! #### Monotonicity in linear orders  -/

section linear_order
variables [linear_order α]

section preorder
variables [preorder β] {f : α → β} {s : set α}

open ordering

lemma monotone.reflect_lt (hf : monotone f) {a b : α} (h : f a < f b) : a < b :=
lt_of_not_ge (λ h', h.not_le (hf h'))

lemma antitone.reflect_lt (hf : antitone f) {a b : α} (h : f a < f b) : b < a :=
lt_of_not_ge (λ h', h.not_le (hf h'))

lemma strict_mono_on.le_iff_le (hf : strict_mono_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  f a ≤ f b ↔ a ≤ b :=
⟨λ h, le_of_not_gt $ λ h', (hf hb ha h').not_le h,
 λ h, h.lt_or_eq_dec.elim (λ h', (hf ha hb h').le) (λ h', h' ▸ le_refl _)⟩

lemma strict_anti_on.le_iff_le (hf : strict_anti_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  f a ≤ f b ↔ b ≤ a :=
hf.dual_right.le_iff_le hb ha

lemma strict_mono_on.lt_iff_lt (hf : strict_mono_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  f a < f b ↔ a < b :=
by rw [lt_iff_le_not_le, lt_iff_le_not_le, hf.le_iff_le ha hb, hf.le_iff_le hb ha]

lemma strict_anti_on.lt_iff_lt (hf : strict_anti_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  f a < f b ↔ b < a :=
hf.dual_right.lt_iff_lt hb ha

lemma strict_mono.le_iff_le (hf : strict_mono f) {a b : α} :
  f a ≤ f b ↔ a ≤ b :=
(hf.strict_mono_on set.univ).le_iff_le trivial trivial

lemma strict_anti.le_iff_le (hf : strict_anti f) {a b : α} :
  f a ≤ f b ↔ b ≤ a :=
(hf.strict_anti_on set.univ).le_iff_le trivial trivial

lemma strict_mono.lt_iff_lt (hf : strict_mono f) {a b : α} :
  f a < f b ↔ a < b :=
(hf.strict_mono_on set.univ).lt_iff_lt trivial trivial

lemma strict_anti.lt_iff_lt (hf : strict_anti f) {a b : α} :
  f a < f b ↔ b < a :=
(hf.strict_anti_on set.univ).lt_iff_lt trivial trivial

protected theorem strict_mono_on.compares (hf : strict_mono_on f s) {a b : α} (ha : a ∈ s)
  (hb : b ∈ s) :
  ∀ {o : ordering}, o.compares (f a) (f b) ↔ o.compares a b
| ordering.lt := hf.lt_iff_lt ha hb
| ordering.eq := ⟨λ h, ((hf.le_iff_le ha hb).1 h.le).antisymm ((hf.le_iff_le hb ha).1 h.symm.le),
                   congr_arg _⟩
| ordering.gt := hf.lt_iff_lt hb ha

protected theorem strict_anti_on.compares (hf : strict_anti_on f s) {a b : α} (ha : a ∈ s)
  (hb : b ∈ s) {o : ordering} :
  o.compares (f a) (f b) ↔ o.compares b a :=
order_dual.dual_compares.trans $ hf.dual_right.compares hb ha

protected theorem strict_mono.compares (hf : strict_mono f) {a b : α} {o : ordering} :
  o.compares (f a) (f b) ↔ o.compares a b :=
(hf.strict_mono_on set.univ).compares trivial trivial

protected theorem strict_anti.compares (hf : strict_anti f) {a b : α} {o : ordering} :
  o.compares (f a) (f b) ↔ o.compares b a :=
(hf.strict_anti_on set.univ).compares trivial trivial

lemma strict_mono.injective (hf : strict_mono f) : injective f :=
λ x y h, show compares eq x y, from hf.compares.1 h

lemma strict_anti.injective (hf : strict_anti f) : injective f :=
λ x y h, show compares eq x y, from hf.compares.1 h.symm

lemma strict_mono.maximal_of_maximal_image (hf : strict_mono f) {a} (hmax : ∀ p, p ≤ f a) (x : α) :
  x ≤ a :=
hf.le_iff_le.mp (hmax (f x))

lemma strict_mono.minimal_of_minimal_image (hf : strict_mono f) {a} (hmin : ∀ p, f a ≤ p) (x : α) :
  a ≤ x :=
hf.le_iff_le.mp (hmin (f x))

lemma strict_anti.minimal_of_maximal_image (hf : strict_anti f) {a} (hmax : ∀ p, p ≤ f a) (x : α) :
  a ≤ x :=
hf.le_iff_le.mp (hmax (f x))

lemma strict_anti.maximal_of_minimal_image (hf : strict_anti f) {a} (hmin : ∀ p, f a ≤ p) (x : α) :
  x ≤ a :=
hf.le_iff_le.mp (hmin (f x))

end preorder

section partial_order
variables [partial_order β] {f : α → β}

lemma monotone.strict_mono_iff_injective (hf : monotone f) :
  strict_mono f ↔ injective f :=
⟨λ h, h.injective, hf.strict_mono_of_injective⟩

lemma antitone.strict_anti_iff_injective (hf : antitone f) :
  strict_anti f ↔ injective f :=
⟨λ h, h.injective, hf.strict_anti_of_injective⟩

end partial_order
end linear_order

/-! #### Monotonicity in `ℕ` and `ℤ` -/

section preorder
variables [preorder α]

lemma monotone_nat_of_le_succ {f : ℕ → α} (hf : ∀ n, f n ≤ f (n + 1)) :
  monotone f | n m h :=
begin
  induction h,
  { refl },
  { transitivity, assumption, exact hf _ }
end

lemma antitone_nat_of_succ_le {f : ℕ → α} (hf : ∀ n, f (n + 1) ≤ f n) :
  antitone f | n m h :=
begin
  induction h,
  { refl },
  { transitivity, exact hf _, assumption }
end

lemma strict_mono_nat_of_lt_succ [preorder β] {f : ℕ → β} (hf : ∀ n, f n < f (n + 1)) :
  strict_mono f :=
by { intros n m hnm, induction hnm with m' hnm' ih, apply hf, exact ih.trans (hf _) }

lemma strict_anti_nat_of_succ_lt [preorder β] {f : ℕ → β} (hf : ∀ n, f (n + 1) < f n) :
  strict_anti f :=
by { intros n m hnm, induction hnm with m' hnm' ih, apply hf, exact (hf _).trans ih }

lemma forall_ge_le_of_forall_le_succ (f : ℕ → α) {a : ℕ} (h : ∀ n, a ≤ n → f n.succ ≤ f n) {b c : ℕ}
  (hab : a ≤ b) (hbc : b ≤ c) :
  f c ≤ f b :=
begin
  induction hbc with k hbk hkb,
  { exact le_rfl },
  { exact (h _ $ hab.trans hbk).trans hkb }
end

-- TODO@Yael: Generalize the following four to succ orders
/-- If `f` is a monotone function from `ℕ` to a preorder such that `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
lemma monotone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : monotone f) (n : ℕ) {x : α}
  (h1 : f n < x) (h2 : x < f (n + 1)) (a : ℕ) :
  f a ≠ x :=
by { rintro rfl, exact (hf.reflect_lt h1).not_le (nat.le_of_lt_succ $ hf.reflect_lt h2) }

/-- If `f` is an antitone function from `ℕ` to a preorder such that `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
lemma antitone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : antitone f)
  (n : ℕ) {x : α} (h1 : f (n + 1) < x) (h2 : x < f n) (a : ℕ) : f a ≠ x :=
by { rintro rfl, exact (hf.reflect_lt h2).not_le (nat.le_of_lt_succ $ hf.reflect_lt h1) }

/-- If `f` is a monotone function from `ℤ` to a preorder and `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
lemma monotone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : monotone f) (n : ℤ) {x : α}
  (h1 : f n < x) (h2 : x < f (n + 1)) (a : ℤ) :
  f a ≠ x :=
by { rintro rfl, exact (hf.reflect_lt h1).not_le (int.le_of_lt_add_one $ hf.reflect_lt h2) }

/-- If `f` is an antitone function from `ℤ` to a preorder and `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
lemma antitone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : antitone f)
  (n : ℤ) {x : α} (h1 : f (n + 1) < x) (h2 : x < f n) (a : ℤ) : f a ≠ x :=
by { rintro rfl, exact (hf.reflect_lt h2).not_le (int.le_of_lt_add_one $ hf.reflect_lt h1) }

lemma strict_mono.id_le {φ : ℕ → ℕ} (h : strict_mono φ) : ∀ n, n ≤ φ n :=
λ n, nat.rec_on n (nat.zero_le _)
  (λ n hn, nat.succ_le_of_lt (hn.trans_lt $ h $ nat.lt_succ_self n))

end preorder

/-! ### Lifts of order instances -/

/-- Transfer a `preorder` on `β` to a `preorder` on `α` using a function `f : α → β`.
See note [reducible non-instances]. -/
@[reducible] def preorder.lift {α β} [preorder β] (f : α → β) : preorder α :=
{ le               := λ x y, f x ≤ f y,
  le_refl          := λ a, le_refl _,
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
preorder.lift subtype.val

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
partial_order.lift subtype.val subtype.val_injective

instance subtype.linear_order {α} [linear_order α] (p : α → Prop) : linear_order (subtype p) :=
linear_order.lift subtype.val subtype.val_injective

lemma subtype.mono_coe [preorder α] (t : set α) : monotone (coe : (subtype t) → α) :=
λ x y, id

lemma subtype.strict_mono_coe [preorder α] (t : set α) : strict_mono (coe : (subtype t) → α) :=
λ x y, id

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

lemma monotone_fst {α β : Type*} [preorder α] [preorder β] : monotone (@prod.fst α β) :=
λ x y h, h.1

lemma monotone_snd {α β : Type*} [preorder α] [preorder β] : monotone (@prod.snd α β) :=
λ x y h, h.2

/-! ### Additional order classes -/

/-- Order without a maximal element. Sometimes called cofinal. -/
class no_top_order (α : Type u) [preorder α] : Prop :=
(no_top : ∀ a : α, ∃ a', a < a')

lemma no_top [preorder α] [no_top_order α] : ∀ a : α, ∃ a', a < a' :=
no_top_order.no_top

instance nonempty_gt {α : Type u} [preorder α] [no_top_order α] (a : α) :
  nonempty {x // a < x} :=
nonempty_subtype.2 (no_top a)

/-- Order without a minimal element. Sometimes called coinitial or dense. -/
class no_bot_order (α : Type u) [preorder α] : Prop :=
(no_bot : ∀ a : α, ∃ a', a' < a)

lemma no_bot [preorder α] [no_bot_order α] : ∀ a : α, ∃ a', a' < a :=
no_bot_order.no_bot

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
