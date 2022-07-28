/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Violeta Hernández Palacios
-/
import tactic.by_contra
import data.set.basic

/-!
# Well-founded relations

A relation is well-founded if it can be used for induction: for each `x`, `(∀ y, r y x → P y) → P x`
implies `P x`. Well-founded relations can be used for induction and recursion, including
construction of fixed points in the space of dependent functions `Π x : α , β x`.

The predicate `well_founded` is defined in the core library. In this file we prove some extra lemmas
and provide a few new definitions: `is_well_founded.min`, `is_well_founded.sup`, and
`is_well_founded.succ`.

## Todo

The following to-do's apply to `well_founded_gt` as well.

- Define `succ` on `well_founded_lt`, build a `succ_order` instance depending on whether we have a
`no_top_order` or an `order_top`.
- Define `sup` on `well_founded_lt`, prove `is_glb (sup s _)` on linear orders.
- Change `min` to `min_on`, redefine `min` as a global minimum.
-/

/-! ### Generic relation

Note that throughout this section, we give lemmas the names they'd have if the order relation were
`<`. -/

variables {α β : Type*}

/-! We uncouple only the most basic results on well-founded relations from their typeclass. -/

namespace well_founded
variables {r : α → α → Prop} (h : well_founded r)
include h

/-- If `r` is a well-founded relation, then any nonempty set has a minimal element
with respect to `r`. -/
theorem has_min (s : set α) : s.nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬ r x a
| ⟨a, ha⟩ := (acc.rec_on (h.apply a) $ λ x _ IH, not_imp_not.1 $ λ hne hx, hne $
  ⟨x, hx, λ y hy hyx, hne $ IH y hyx hy⟩) ha

/-- A minimal element of a nonempty set with respect to a well-founded relation. -/
noncomputable def min (s : set α) (hs : s.nonempty) : α :=
classical.some (h.has_min s hs)

theorem min_mem (s : set α) (hs : s.nonempty) : h.min s hs ∈ s :=
let ⟨ha, _⟩ := classical.some_spec (h.has_min s hs) in ha

theorem not_lt_min (s : set α) {x} (hx : x ∈ s) : ¬ r x (h.min s ⟨x, hx⟩) :=
let ⟨_, h'⟩ := classical.some_spec (h.has_min s ⟨x, hx⟩) in h' _ hx

omit h
theorem well_founded_iff_has_min {r : α → α → Prop} : well_founded r ↔
  ∀ (s : set α), s.nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬ r x a :=
begin
  refine ⟨λ h, h.has_min, λ h, ⟨λ x, _⟩⟩,
  by_contra hx,
  obtain ⟨m, hm, hm'⟩ := h _ ⟨x, hx⟩,
  refine hm (acc.intro _ (λ y hy, _)),
  by_contra hy',
  exact hm' y hy' hy
end

end well_founded

namespace is_well_founded
variables (r : α → α → Prop) [is_well_founded α r]

/-- If `r` is a well-founded relation, then any nonempty set has a minimal element
with respect to `r`. -/
theorem has_min : ∀ s : set α, s.nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬ r x a := is_well_founded.wf.has_min

/-- A minimal element of a nonempty set with respect to a well-founded relation. See also
`well_founded_lt.min` and `well_founded_gt.max`. -/
@[reducible] noncomputable def min (s : set α) : s.nonempty → α := (@is_well_founded.wf α r _).min s

theorem min_mem : ∀ (s : set α) (hs : s.nonempty), min r s hs ∈ s := is_well_founded.wf.min_mem

theorem not_lt_min : ∀ (s : set α) {x} (hx : x ∈ s), ¬ r x (min r s ⟨x, hx⟩) :=
is_well_founded.wf.not_lt_min

theorem is_well_founded_iff_has_min (r : α → α → Prop) : is_well_founded α r ↔
  ∀ (s : set α), s.nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬ r x a :=
by rw [is_well_founded_iff, well_founded.well_founded_iff_has_min]

@[simp] theorem min_singleton (x : α) : min r _ (set.singleton_nonempty x) = x :=
set.eq_of_mem_singleton $ min_mem _ _ _

open set

/-- A minimal upper bound of a bounded, well-founded order -/
protected noncomputable def sup (s : set α) : bounded r s → α :=
min r {x | ∀ a ∈ s, r a x}

protected lemma lt_sup (s : set α) (h : bounded r s) {x} (hx : x ∈ s) :
  r x (is_well_founded.sup r s h) :=
min_mem r _ h x hx

section classical
open_locale classical

/-- A successor of an element `x` in a well-founded order is a minimal element `y` such that
`x < y` if one exists. Otherwise it is `x` itself. -/
protected noncomputable def succ (x : α) : α :=
if h : ∃ y, r x y then min r {y | r x y} h else x

protected lemma lt_succ {x : α} (h : ∃ y, r x y) :
  r x (is_well_founded.succ r x) :=
by { rw [is_well_founded.succ, dif_pos h], apply min_mem }

end classical

protected lemma lt_succ_iff [is_well_order α r] {x : α} (h : ∃ y, r x y) (y : α) :
  r y (is_well_founded.succ r x) ↔ r y x ∨ y = x :=
begin
  split,
  { intro h', have : ¬r x y,
    { intro hy, rw [is_well_founded.succ, dif_pos] at h',
      exact is_well_founded.not_lt_min _ _ hy h' },
    rcases trichotomous_of r x y with hy | hy | hy,
    { exact (this hy).elim },
    { exact or.inr hy.symm },
    { exact or.inl hy } },
  rintro (hy | rfl),
  { exact trans hy (is_well_founded.lt_succ r h) },
  { exact is_well_founded.lt_succ r h }
end

end is_well_founded

/-! ### Well-founded less than -/

namespace well_founded_lt

/-- If `<` is a well-founded relation, then any nonempty set has a minimal element. -/
theorem has_min [has_lt α] [well_founded_lt α] :
  ∀ s : set α, s.nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬ x < a :=
is_well_founded.has_min (<)

/-- A minimal element of a nonempty set in an order with well-founded `<`.

If you're working with a nonempty linear order, consider defining a
`conditionally_complete_linear_order_bot` instance via
`well_founded.conditionally_complete_linear_order_with_bot` and using `Inf` instead. -/
@[reducible] noncomputable def min [has_lt α] [well_founded_lt α] :
  Π (s : set α) (hs : s.nonempty), α :=
is_well_founded.min (<)

theorem min_mem [has_lt α] [well_founded_lt α] (s : set α) (hs : s.nonempty) : min s hs ∈ s :=
is_well_founded.min_mem _ s hs

theorem not_lt_min [has_lt α] [well_founded_lt α] (s : set α) {x} (hx : x ∈ s) :
  ¬ x < min s ⟨x, hx⟩ :=
is_well_founded.not_lt_min _ s hx

theorem min_le [linear_order α] [well_founded_lt α] (s : set α) {x} (hx : x ∈ s) :
  min s ⟨x, hx⟩ ≤ x :=
le_of_not_lt $ not_lt_min s hx

@[simp] theorem min_singleton [has_lt α] [well_founded_lt α] :
  ∀ x : α, min _ (set.singleton_nonempty x) = x :=
is_well_founded.min_singleton _

theorem is_well_founded_iff_has_min [has_lt α] : well_founded_lt α ↔
  ∀ (s : set α), s.nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬ x < a :=
by rw [well_founded_lt, is_well_founded.is_well_founded_iff_has_min]

/-- A linear order with well-founded `<` has a bottom element given by `min set.univ _`. -/
noncomputable def to_order_bot [linear_order α] [well_founded_lt α] [nonempty α] : order_bot α :=
{ bot := min set.univ set.univ_nonempty,
  bot_le := λ a, min_le _ ⟨⟩ }

theorem self_le_of_strict_mono [linear_order α] [well_founded_lt α] {f : α → α}
  (hf : strict_mono f) : ∀ n, n ≤ f n :=
by { by_contra' h₁, have h₂ := min_mem _ h₁, exact not_lt_min {n : α | f n < n} (hf h₂) h₂ }

private theorem range_eq_iff_eq_of_strict_mono_aux [linear_order α] [partial_order β]
  {f g : α → β} (hf : strict_mono f) (hg : strict_mono g) (hfg : set.range f = set.range g) {a : α}
  (H : ∀ b < a, f b = g b) : f a ≤ g a :=
begin
  obtain ⟨b, hb⟩ : g a ∈ set.range f := by { rw hfg, exact set.mem_range_self a },
  cases lt_or_le b a with hab hab,
  { rw [H b hab] at hb,
    rw hg.injective hb at hab,
    exact hab.false.elim },
  { rw ←hb,
    exact hf.monotone hab }
end

theorem range_eq_iff_eq_of_strict_mono [linear_order α] [partial_order β] [well_founded_lt α]
  {f g : α → β} (hf : strict_mono f) (hg : strict_mono g) : set.range f = set.range g ↔ f = g :=
⟨λ h, begin
  funext a,
  apply induction a,
  exact λ b H, le_antisymm
    (range_eq_iff_eq_of_strict_mono_aux hf hg h H)
    (range_eq_iff_eq_of_strict_mono_aux hg hf h.symm (λ a hab, (H a hab).symm))
end, congr_arg _⟩

end well_founded_lt

namespace function
variable (f : α → β)

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, and a non-empty subset `s`
of `α`, this is an element of `s` whose image under `f` is minimal in the sense of
`function.not_lt_argmin_on`. -/
noncomputable def argmin_on [has_lt β] [well_founded_lt β] (s : set α) (hs : s.nonempty) : α :=
is_well_founded.min (inv_image (<) f) s hs

@[simp] lemma argmin_on_mem [has_lt β] [well_founded_lt β] (s : set α) (hs : s.nonempty) :
  argmin_on f s hs ∈ s :=
is_well_founded.min_mem _ _ _

@[simp] lemma not_lt_argmin_on [has_lt β] [well_founded_lt β] (s : set α) {x : α} (hx : x ∈ s) :
  ¬ f x < f (argmin_on f s ⟨x, hx⟩) :=
is_well_founded.not_lt_min (inv_image (<) f) s hx

@[simp] lemma argmin_on_le [linear_order β] [well_founded_lt β] (s : set α) {x : α} (hx : x ∈ s) :
  f (argmin_on f s ⟨x, hx⟩) ≤ f x :=
le_of_not_lt $ not_lt_argmin_on f s hx

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, this is an element of `α`
whose image under `f` is minimal in the sense of `function.not_lt_argmin`. -/
noncomputable def argmin [has_lt β] [well_founded_lt β] [nonempty α] : α :=
argmin_on f set.univ set.univ_nonempty

@[simp] lemma not_lt_argmin [has_lt β] [well_founded_lt β] [nonempty α] (a : α) :
  ¬ f a < f (argmin f) :=
not_lt_argmin_on _ _ ⟨⟩

@[simp] lemma argmin_le [linear_order β] [well_founded_lt β] [nonempty α] (a : α) :
  f (argmin f) ≤ f a :=
le_of_not_lt $ not_lt_argmin f a

end function

/-! ### Well-founded greater than -/

namespace well_founded_gt

/-- If `<` is a well-founded relation, then any nonempty set has a minimal element. -/
theorem has_max [has_lt α] [well_founded_gt α] :
  ∀ s : set α, s.nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬ a < x :=
is_well_founded.has_min (>)

/-- A maximal element of a nonempty set in an order with well-founded `>`. -/
@[reducible] noncomputable def max [has_lt α] [well_founded_gt α] :
  Π (s : set α) (hs : s.nonempty), α :=
is_well_founded.min (>)

theorem max_mem [has_lt α] [well_founded_gt α] (s : set α) (hs : s.nonempty) : max s hs ∈ s :=
is_well_founded.min_mem _ s hs

theorem not_max_lt [has_lt α] [well_founded_gt α] (s : set α) {x} (hx : x ∈ s)
  (hs : s.nonempty := ⟨x, hx⟩) : ¬ max s hs < x :=
is_well_founded.not_lt_min (>) s hx

theorem le_max [linear_order α] [well_founded_gt α] (s : set α) {x} (hx : x ∈ s)
  (hs : s.nonempty := ⟨x, hx⟩) : x ≤ max s hs :=
le_of_not_lt (not_max_lt s hx hs)

@[simp] theorem max_singleton [has_lt α] [well_founded_gt α] :
  ∀ x : α, max _ (set.singleton_nonempty x) = x :=
is_well_founded.min_singleton _

theorem is_well_founded_iff_has_max [has_lt α] : well_founded_gt α ↔
  ∀ (s : set α), s.nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬ a < x :=
by rw [well_founded_gt, is_well_founded.is_well_founded_iff_has_min]

/-- A linear order with well-founded `>` has a top element given by `max set.univ _`. -/
noncomputable def to_order_top [linear_order α] [well_founded_gt α] [nonempty α] : order_top α :=
{ top := max set.univ set.univ_nonempty,
  le_top := λ a, le_max _ ⟨⟩ }

theorem le_self_of_antitone [linear_order α] [well_founded_gt α] {f : α → α}
  (hf : strict_mono f) : ∀ n, f n ≤ n :=
@well_founded_lt.self_le_of_strict_mono αᵒᵈ _ _ f (λ a b h, hf h)

theorem range_eq_iff_eq_of_strict_anti [linear_order α] [partial_order β] [well_founded_gt α]
  {f g : α → β} (hf : strict_anti f) (hg : strict_anti g) : set.range f = set.range g ↔ f = g :=
@well_founded_lt.range_eq_iff_eq_of_strict_mono αᵒᵈ _ _ _ _ f g (λ a b h, hf h) (λ a b h, hg h)

end well_founded_gt

namespace function
variable (f : α → β)

/-- Given a function `f : α → β` where `β` carries a well-founded `>`, and a non-empty subset `s`
of `α`, this is an element of `s` whose image under `f` is maximal in the sense of
`function.not_argmax_on_lt`. -/
noncomputable def argmax_on [has_lt β] [well_founded_gt β] (s : set α) (hs : s.nonempty) : α :=
is_well_founded.min (inv_image (>) f) s hs

@[simp] lemma argmax_on_mem [has_lt β] [well_founded_gt β] (s : set α) (hs : s.nonempty) :
  argmax_on f s hs ∈ s :=
is_well_founded.min_mem _ _ _

@[simp] lemma not_argmax_on_lt [has_lt β] [well_founded_gt β] (s : set α) {x : α} (hx : x ∈ s) :
  ¬ f (argmax_on f s ⟨x, hx⟩) < f x :=
is_well_founded.not_lt_min (inv_image (>) f) s hx

@[simp] lemma le_argmax_on [linear_order β] [well_founded_gt β] (s : set α) {x : α} (hx : x ∈ s) :
  f x ≤ f (argmax_on f s ⟨x, hx⟩) :=
le_of_not_lt $ not_argmax_on_lt f s hx

/-- Given a function `f : α → β` where `β` carries a well-founded `>`, this is an element of `α`
whose image under `f` is maximal in the sense of `function.not_argmax_lt`. -/
noncomputable def argmax [has_lt β] [well_founded_gt β] [nonempty α] : α :=
argmax_on f set.univ set.univ_nonempty

@[simp] lemma not_argmax_lt [has_lt β] [well_founded_gt β] [nonempty α] (a : α) :
  ¬ f (argmax f) < f a :=
not_argmax_on_lt _ _ ⟨⟩

@[simp] lemma le_argmax [linear_order β] [well_founded_gt β] [nonempty α] (a : α) :
  f a ≤ f (argmax f) :=
le_of_not_lt $ not_argmax_lt f a

end function
