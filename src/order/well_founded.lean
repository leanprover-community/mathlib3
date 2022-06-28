/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import tactic.by_contra
import data.set.basic
import order.bounds

/-!
# Well-founded relations

A relation is well-founded if it can be used for induction: for each `x`, `(∀ y, r y x → P y) → P x`
implies `P x`. Well-founded relations can be used for induction and recursion, including
construction of fixed points in the space of dependent functions `Π x : α , β x`.

The predicate `well_founded` is defined in the core library. In this file we prove some extra lemmas
and provide a few new definitions: `well_founded.min`, `well_founded.sup`, and `well_founded.succ`.
-/

/-! ### Generic relation

Note that throughout this section, we give lemmas the names they'd have if the order relation were
`<`. -/

variables {α β : Type*}

namespace is_well_founded
variables (r : α → α → Prop) [H : is_well_founded α r]

/-- If `r` is a well-founded relation, then any nonempty set has a minimal element
with respect to `r`. -/
theorem has_min {s : set α} : s.nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬ r x a
| ⟨a, ha⟩ := (acc.rec_on (H.wf.apply a) $ λ x _ IH, not_imp_not.1 $ λ hne hx, hne $
  ⟨x, hx, λ y hy hyx, hne $ IH y hyx hy⟩) ha

/-- A minimal element of a nonempty set with respect to a well-founded relation. See also
`well_founded_lt.min` and `well_founded_gt.max`. -/
noncomputable def min [is_well_founded α r] (s : set α) (hs : s.nonempty) : α :=
classical.some (has_min r hs)

theorem min_mem [is_well_founded α r] {s : set α} (hs : s.nonempty) : min r s hs ∈ s :=
let ⟨h, _⟩ := classical.some_spec (has_min r hs) in h

theorem not_lt_min [is_well_founded α r] {s : set α} {x} (hx : x ∈ s) (hs : s.nonempty := ⟨x, hx⟩) :
  ¬ r x (min r s hs) :=
let ⟨_, h'⟩ := classical.some_spec (has_min r hs) in h' _ hx

theorem well_founded_iff_has_min {r : α → α → Prop} : well_founded r ↔
  ∀ {s : set α}, s.nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬ r x a :=
begin
  refine ⟨λ h, @has_min _ r ⟨h⟩, λ h, ⟨λ x, _⟩⟩,
  by_contra hx,
  obtain ⟨m, hm, hm'⟩ := h ⟨x, hx⟩,
  refine hm (acc.intro _ (λ y hy, _)),
  by_contra hy',
  exact hm' y hy' hy
end

-- TODO: remove this, or at least move it elsewhere.
lemma eq_iff_not_lt_of_le {α} [partial_order α] {x y : α} : x ≤ y → y = x ↔ ¬ x < y :=
begin
  split,
  { intros xle nge,
    cases le_not_le_of_lt nge,
    rw xle left at nge,
    exact lt_irrefl x nge },
  { intros ngt xle,
    contrapose! ngt,
    exact lt_of_le_of_ne xle (ne.symm ngt) }
end

-- TODO: rewrite this in terms of `well_founded_gt`.
theorem well_founded_iff_has_max' [partial_order α] : (well_founded ((>) : α → α → Prop) ↔
  ∀ (p : set α), p.nonempty → ∃ m ∈ p, ∀ x ∈ p, m ≤ x → x = m) :=
by simp only [eq_iff_not_lt_of_le, well_founded_iff_has_min]

-- TODO: rewrite this in terms of `well_founded_lt`.
theorem well_founded_iff_has_min' [partial_order α] : (well_founded (has_lt.lt : α → α → Prop)) ↔
  ∀ (p : set α), p.nonempty → ∃ m ∈ p, ∀ x ∈ p, x ≤ m → x = m :=
@well_founded_iff_has_max' αᵒᵈ _

open set

/-- A minimal upper bound of a bounded, well-founded order -/
protected noncomputable def sup [is_well_founded α r] {s : set α} : bounded r s → α :=
min r {x | ∀ a ∈ s, r a x}

protected lemma lt_sup [is_well_founded α r] {s : set α} (h : bounded r s) {x} (hx : x ∈ s) :
  r x (is_well_founded.sup r h) :=
min_mem r h x hx

section classical
open_locale classical

/-- A successor of an element `x` in a well-founded order is a minimal element `y` such that
`x < y` if one exists. Otherwise it is `x` itself. -/
protected noncomputable def succ [is_well_founded α r] (x : α) : α :=
if h : ∃ y, r x y then min r {y | r x y} h else x

protected lemma lt_succ [is_well_founded α r] {x : α} (h : ∃ y, r x y) :
  r x (is_well_founded.succ r x) :=
by { rw [is_well_founded.succ, dif_pos h], apply min_mem }

end classical

protected lemma lt_succ_iff [is_well_order α r] {x : α} (h : ∃ y, r x y) (y : α) :
  r y (is_well_founded.succ r x) ↔ r y x ∨ y = x :=
begin
  split,
  { intro h', have : ¬r x y,
    { intro hy, rw [is_well_founded.succ, dif_pos] at h',
      exact is_well_founded.not_lt_min _ hy h h' },
    rcases trichotomous_of r x y with hy | hy | hy,
    { exact (this hy).elim },
    { exact or.inr hy.symm },
    { exact or.inl hy } },
  rintro (hy | rfl),
  { exact trans hy (is_well_founded.lt_succ r h) },
  { exact is_well_founded.lt_succ r h }
end

end is_well_founded

/-! ### Well-founded order relation -/

/-- A class for a well founded relation `<`. -/
class well_founded_lt (α : Type*) [has_lt α] extends is_well_founded α (<) : Prop

/-- A class for a well founded relation `>`. -/
class well_founded_gt (α : Type*) [has_lt α] extends is_well_founded α (>) : Prop

@[priority 100] -- See note [lower instance priority]
instance (α : Type*) [has_lt α] [h : well_founded_lt α] : well_founded_gt αᵒᵈ := { ..h }
@[priority 100] -- See note [lower instance priority]
instance (α : Type*) [has_lt α] [h : well_founded_gt α] : well_founded_lt αᵒᵈ := { ..h }

namespace well_founded_lt

/-- Inducts on a well-founded `<` relation. -/
theorem induction [has_lt α] [well_founded_lt α] {C : α → Prop} :
  ∀ a, (∀ x, (∀ y, y < x → C y) → C x) → C a :=
is_well_founded.induction (<)

/-- A minimal element of a nonempty set in an order with well-founded `<`.

If you're working with a nonempty linear order, consider defining a
`conditionally_complete_linear_order_bot` instance via
`well_founded.conditionally_complete_linear_order_with_bot` and using `Inf` instead. -/
noncomputable def min [has_lt α] [well_founded_lt α] : Π (s : set α) (hs : s.nonempty), α :=
is_well_founded.min (<)

theorem min_mem [has_lt α] [well_founded_lt α] {s : set α} (hs : s.nonempty) : min s hs ∈ s :=
is_well_founded.min_mem _ hs

theorem not_lt_min [has_lt α] [well_founded_lt α] {s : set α} {x} (hx : x ∈ s)
  (hs : s.nonempty := ⟨x, hx⟩) : ¬ x < min s hs :=
is_well_founded.not_lt_min _ hx

theorem min_le [linear_order α] [well_founded_lt α] {s : set α} {x} (hx : x ∈ s)
  (hs : s.nonempty := ⟨x, hx⟩) : min s hs ≤ x :=
le_of_not_lt (not_lt_min hx hs)

theorem self_le_of_strict_mono [linear_order α] [well_founded_lt α] {f : α → α}
  (hf : strict_mono f) : ∀ n, n ≤ f n :=
by { by_contra' h₁, have h₂ := h.min_mem _ h₁, exact h.not_lt_min _ h₁ (hφ h₂) h₂ }

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
  {f g : β → γ} (hf : strict_mono f) (hg : strict_mono g) : set.range f = set.range g ↔ f = g :=
⟨λ h, begin
  funext a,
  apply induction a,
  exact λ b H, le_antisymm
    (range_eq_iff_eq_of_strict_mono_aux hf hg h H)
    (range_eq_iff_eq_of_strict_mono_aux hg hf h.symm (λ a hab, (H a hab).symm))
end, congr_arg _⟩

end well_founded_lt

namespace well_founded_gt

/-- Inducts on a well-founded `>` relation. -/
theorem induction [has_lt α] [well_founded_lt α] {C : α → Prop} :
  ∀ a, (∀ x, (∀ y, y < x → C y) → C x) → C a :=
is_well_founded.induction (<)

/-- A maximal element of a nonempty set in an order with well-founded `>`. -/
noncomputable def max [has_lt α] [well_founded_gt α] : Π (s : set α) (hs : s.nonempty), α :=
is_well_founded.min (>)

theorem max_mem [has_lt α] [well_founded_gt α] {s : set α} (hs : s.nonempty) : max s hs ∈ s :=
is_well_founded.min_mem _ hs

theorem not_max_lt [has_lt α] [well_founded_gt α] {s : set α} {x} (hx : x ∈ s)
  (hs : s.nonempty := ⟨x, hx⟩) : ¬ max s hs < x :=
is_well_founded.not_lt_min (>) hx

theorem le_max [linear_order α] [well_founded_gt α] {s : set α} {x} (hx : x ∈ s)
  (hs : s.nonempty := ⟨x, hx⟩) : x ≤ max s hs :=
le_of_not_lt (not_max_lt hx hs)

theorem range_eq_iff_eq_of_antitone [linear_order α] [partial_order β] [well_founded_gt α] :
  ∀ {f g : β → γ} (hf : antitone f) (hg : antitone g), set.range f = set.range g ↔ f = g :=
@range_eq_iff_eq_of_strict_mono αᵒᵈ _ _

end well_founded_gt

section linear_order

variables {β : Type*} (h : well_founded ((<) : β → β → Prop))
  {γ : Type*}

theorem self_le_of_strict_mono {φ : β → β} (hφ : strict_mono φ) : ∀ n, n ≤ φ n :=
by { by_contra' h₁, have h₂ := h.min_mem _ h₁, exact h.not_lt_min _ h₁ (hφ h₂) h₂ }

end linear_order

end well_founded

namespace function

variables {β : Type*} (f : α → β)

section has_lt

variables [has_lt β] (h : well_founded ((<) : β → β → Prop))

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, this is an element of `α`
whose image under `f` is minimal in the sense of `function.not_lt_argmin`. -/
noncomputable def argmin [nonempty α] : α :=
well_founded.min (inv_image.wf f h) set.univ set.univ_nonempty

lemma not_lt_argmin [nonempty α] (a : α) : ¬ f a < f (argmin f h) :=
well_founded.not_lt_min (inv_image.wf f h) _ _ (set.mem_univ a)

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, and a non-empty subset `s`
of `α`, this is an element of `s` whose image under `f` is minimal in the sense of
`function.not_lt_argmin_on`. -/
noncomputable def argmin_on (s : set α) (hs : s.nonempty) : α :=
well_founded.min (inv_image.wf f h) s hs

@[simp] lemma argmin_on_mem (s : set α) (hs : s.nonempty) :
  argmin_on f h s hs ∈ s :=
well_founded.min_mem _ _ _

@[simp] lemma not_lt_argmin_on (s : set α) {a : α} (ha : a ∈ s)
  (hs : s.nonempty := set.nonempty_of_mem ha) :
  ¬ f a < f (argmin_on f h s hs) :=
well_founded.not_lt_min (inv_image.wf f h) s hs ha

end has_lt

section linear_order

variables [linear_order β] (h : well_founded ((<) : β → β → Prop))

@[simp] lemma argmin_le (a : α) [nonempty α] : f (argmin f h) ≤ f a :=
not_lt.mp $ not_lt_argmin f h a

@[simp] lemma argmin_on_le (s : set α) {a : α} (ha : a ∈ s)
  (hs : s.nonempty := set.nonempty_of_mem ha) : f (argmin_on f h s hs) ≤ f a :=
not_lt.mp $ not_lt_argmin_on f h s ha hs

end linear_order

end function
