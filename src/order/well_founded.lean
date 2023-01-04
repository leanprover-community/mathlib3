/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import tactic.by_contra
import data.set.image

/-!
# Well-founded relations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A relation is well-founded if it can be used for induction: for each `x`, `(∀ y, r y x → P y) → P x`
implies `P x`. Well-founded relations can be used for induction and recursion, including
construction of fixed points in the space of dependent functions `Π x : α , β x`.

The predicate `well_founded` is defined in the core library. In this file we prove some extra lemmas
and provide a few new definitions: `well_founded.min`, `well_founded.sup`, and `well_founded.succ`,
and an induction principle `well_founded.induction_bot`.
-/

variables {α : Type*}

namespace well_founded

protected theorem is_asymm {α : Sort*} {r : α → α → Prop} (h : well_founded r) : is_asymm α r :=
⟨h.asymmetric⟩

instance {α : Sort*} [has_well_founded α] : is_asymm α has_well_founded.r :=
has_well_founded.wf.is_asymm

protected theorem is_irrefl {α : Sort*} {r : α → α → Prop} (h : well_founded r) : is_irrefl α r :=
(@is_asymm.is_irrefl α r h.is_asymm)

instance {α : Sort*} [has_well_founded α] : is_irrefl α has_well_founded.r :=
is_asymm.is_irrefl

/-- If `r` is a well-founded relation, then any nonempty set has a minimal element
with respect to `r`. -/
theorem has_min {α} {r : α → α → Prop} (H : well_founded r)
  (s : set α) : s.nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬ r x a
| ⟨a, ha⟩ := (acc.rec_on (H.apply a) $ λ x _ IH, not_imp_not.1 $ λ hne hx, hne $
  ⟨x, hx, λ y hy hyx, hne $ IH y hyx hy⟩) ha

/-- A minimal element of a nonempty set in a well-founded order.

If you're working with a nonempty linear order, consider defining a
`conditionally_complete_linear_order_bot` instance via
`well_founded.conditionally_complete_linear_order_with_bot` and using `Inf` instead. -/
noncomputable def min {r : α → α → Prop} (H : well_founded r)
  (s : set α) (h : s.nonempty) : α :=
classical.some (H.has_min s h)

theorem min_mem {r : α → α → Prop} (H : well_founded r)
  (s : set α) (h : s.nonempty) : H.min s h ∈ s :=
let ⟨h, _⟩ := classical.some_spec (H.has_min s h) in h

theorem not_lt_min {r : α → α → Prop} (H : well_founded r)
  (s : set α) (h : s.nonempty) {x} (hx : x ∈ s) : ¬ r x (H.min s h) :=
let ⟨_, h'⟩ := classical.some_spec (H.has_min s h) in h' _ hx

theorem well_founded_iff_has_min {r : α → α → Prop} : (well_founded r) ↔
  ∀ (s : set α), s.nonempty → ∃ m ∈ s, ∀ x ∈ s, ¬ r x m :=
begin
  refine ⟨λ h, h.has_min, λ h, ⟨λ x, _⟩⟩,
  by_contra hx,
  obtain ⟨m, hm, hm'⟩ := h _ ⟨x, hx⟩,
  refine hm ⟨_, λ y hy, _⟩,
  by_contra hy',
  exact hm' y hy' hy
end

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

theorem well_founded_iff_has_max' [partial_order α] : (well_founded ((>) : α → α → Prop) ↔
  ∀ (p : set α), p.nonempty → ∃ m ∈ p, ∀ x ∈ p, m ≤ x → x = m) :=
by simp only [eq_iff_not_lt_of_le, well_founded_iff_has_min]

theorem well_founded_iff_has_min' [partial_order α] : (well_founded (has_lt.lt : α → α → Prop)) ↔
  ∀ (p : set α), p.nonempty → ∃ m ∈ p, ∀ x ∈ p, x ≤ m → x = m :=
@well_founded_iff_has_max' αᵒᵈ _

open set
/-- The supremum of a bounded, well-founded order -/
protected noncomputable def sup {r : α → α → Prop} (wf : well_founded r) (s : set α)
  (h : bounded r s) : α :=
wf.min { x | ∀a ∈ s, r a x } h

protected lemma lt_sup {r : α → α → Prop} (wf : well_founded r) {s : set α} (h : bounded r s)
  {x} (hx : x ∈ s) : r x (wf.sup s h) :=
min_mem wf { x | ∀a ∈ s, r a x } h x hx

section
open_locale classical
/-- A successor of an element `x` in a well-founded order is a minimal element `y` such that
`x < y` if one exists. Otherwise it is `x` itself. -/
protected noncomputable def succ {r : α → α → Prop} (wf : well_founded r) (x : α) : α :=
if h : ∃y, r x y then wf.min { y | r x y } h else x

protected lemma lt_succ {r : α → α → Prop} (wf : well_founded r) {x : α} (h : ∃y, r x y) :
  r x (wf.succ x) :=
by { rw [well_founded.succ, dif_pos h], apply min_mem }
end

protected lemma lt_succ_iff {r : α → α → Prop} [wo : is_well_order α r] {x : α} (h : ∃y, r x y)
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

section linear_order

variables {β : Type*} [linear_order β] (h : well_founded ((<) : β → β → Prop))
  {γ : Type*} [partial_order γ]

theorem min_le {x : β} {s : set β} (hx : x ∈ s) (hne : s.nonempty := ⟨x, hx⟩) :
  h.min s hne ≤ x :=
not_lt.1 $ h.not_lt_min _ _ hx

private theorem eq_strict_mono_iff_eq_range_aux {f g : β → γ} (hf : strict_mono f)
  (hg : strict_mono g) (hfg : set.range f = set.range g) {b : β} (H : ∀ a < b, f a = g a) :
  f b ≤ g b :=
begin
  obtain ⟨c, hc⟩ : g b ∈ set.range f := by { rw hfg, exact set.mem_range_self b },
  cases lt_or_le c b with hcb hbc,
  { rw [H c hcb] at hc,
    rw hg.injective hc at hcb,
    exact hcb.false.elim },
  { rw ←hc,
    exact hf.monotone hbc }
end

include h
theorem eq_strict_mono_iff_eq_range {f g : β → γ} (hf : strict_mono f)
  (hg : strict_mono g) : set.range f = set.range g ↔ f = g :=
⟨λ hfg, begin
  funext a,
  apply h.induction a,
  exact λ b H, le_antisymm
    (eq_strict_mono_iff_eq_range_aux hf hg hfg H)
    (eq_strict_mono_iff_eq_range_aux hg hf hfg.symm (λ a hab, (H a hab).symm))
end, congr_arg _⟩

theorem self_le_of_strict_mono {f : β → β} (hf : strict_mono f) : ∀ n, n ≤ f n :=
by { by_contra' h₁, have h₂ := h.min_mem _ h₁, exact h.not_lt_min _ h₁ (hf h₂) h₂ }

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

section induction

/-- Let `r` be a relation on `α`, let `f : α → β` be a function, let `C : β → Prop`, and
let `bot : α`. This induction principle shows that `C (f bot)` holds, given that
* some `a` that is accessible by `r` satisfies `C (f a)`, and
* for each `b` such that `f b ≠ f bot` and `C (f b)` holds, there is `c`
  satisfying `r c b` and `C (f c)`. -/
lemma acc.induction_bot' {α β} {r : α → α → Prop} {a bot : α} (ha : acc r a) {C : β → Prop}
  {f : α → β} (ih : ∀ b, f b ≠ f bot → C (f b) → ∃ c, r c b ∧ C (f c)) : C (f a) → C (f bot) :=
@acc.rec_on _ _ (λ x, C (f x) → C (f bot)) _ ha $ λ x ac ih' hC,
  (eq_or_ne (f x) (f bot)).elim (λ h, h ▸ hC)
    (λ h, let ⟨y, hy₁, hy₂⟩ := ih x h hC in ih' y hy₁ hy₂)

/-- Let `r` be a relation on `α`, let `C : α → Prop` and let `bot : α`.
This induction principle shows that `C bot` holds, given that
* some `a` that is accessible by `r` satisfies `C a`, and
* for each `b ≠ bot` such that `C b` holds, there is `c` satisfying `r c b` and `C c`. -/
lemma acc.induction_bot {α} {r : α → α → Prop} {a bot : α} (ha : acc r a)
  {C : α → Prop} (ih : ∀ b, b ≠ bot → C b → ∃ c, r c b ∧ C c) : C a → C bot :=
ha.induction_bot' ih

/-- Let `r` be a well-founded relation on `α`, let `f : α → β` be a function,
let `C : β → Prop`, and  let `bot : α`.
This induction principle shows that `C (f bot)` holds, given that
* some `a` satisfies `C (f a)`, and
* for each `b` such that `f b ≠ f bot` and `C (f b)` holds, there is `c`
  satisfying `r c b` and `C (f c)`. -/
lemma well_founded.induction_bot' {α β} {r : α → α → Prop} (hwf : well_founded r) {a bot : α}
  {C : β → Prop} {f : α → β} (ih : ∀ b, f b ≠ f bot → C (f b) → ∃ c, r c b ∧ C (f c)) :
  C (f a) → C (f bot) :=
(hwf.apply a).induction_bot' ih

/-- Let `r` be a well-founded relation on `α`, let `C : α → Prop`, and let `bot : α`.
This induction principle shows that `C bot` holds, given that
* some `a` satisfies `C a`, and
* for each `b` that satisfies `C b`, there is `c` satisfying `r c b` and `C c`.

The naming is inspired by the fact that when `r` is transitive, it follows that `bot` is
the smallest element w.r.t. `r` that satisfies `C`. -/
lemma well_founded.induction_bot {α} {r : α → α → Prop} (hwf : well_founded r) {a bot : α}
  {C : α → Prop} (ih : ∀ b, b ≠ bot → C b → ∃ c, r c b ∧ C c) : C a → C bot :=
hwf.induction_bot' ih

end induction
