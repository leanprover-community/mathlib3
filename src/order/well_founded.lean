/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import data.set.basic

/-!
# Well-founded relations

A relation is well-founded if it can be used for induction: for each `x`, `(∀ y, r y x → P y) → P x`
implies `P x`. Well-founded relations can be used for induction and recursion, including
construction of fixed points in the space of dependent functions `Π x : α , β x`.

The predicate `well_founded` is defined in the core library. In this file we prove some extra lemmas
and provide a few new definitions: `well_founded.min`, `well_founded.sup`, and `well_founded.succ`.
-/

variables {α : Type*}

namespace well_founded
/-- If `r` is a well-founded relation, then any nonempty set has a minimal element
with respect to `r`. -/
theorem has_min {α} {r : α → α → Prop} (H : well_founded r)
  (s : set α) : s.nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬ r x a
| ⟨a, ha⟩ := (acc.rec_on (H.apply a) $ λ x _ IH, not_imp_not.1 $ λ hne hx, hne $
  ⟨x, hx, λ y hy hyx, hne $ IH y hyx hy⟩) ha

/-- A minimal element of a nonempty set in a well-founded order -/
noncomputable def min {α} {r : α → α → Prop} (H : well_founded r)
  (p : set α) (h : p.nonempty) : α :=
classical.some (H.has_min p h)

theorem min_mem {α} {r : α → α → Prop} (H : well_founded r)
  (p : set α) (h : p.nonempty) : H.min p h ∈ p :=
let ⟨h, _⟩ := classical.some_spec (H.has_min p h) in h

theorem not_lt_min {α} {r : α → α → Prop} (H : well_founded r)
  (p : set α) (h : p.nonempty) {x} (xp : x ∈ p) : ¬ r x (H.min p h) :=
let ⟨_, h'⟩ := classical.some_spec (H.has_min p h) in h' _ xp

theorem well_founded_iff_has_min  {α} {r : α → α → Prop} : (well_founded r) ↔
  ∀ (p : set α), p.nonempty → ∃ m ∈ p, ∀ x ∈ p, ¬ r x m :=
begin
  classical,
  split,
  { exact has_min, },
  { set counterexamples := { x : α | ¬ acc r x},
    intro exists_max,
    fconstructor,
    intro x,
    by_contra hx,
    obtain ⟨m, m_mem, hm⟩ := exists_max counterexamples ⟨x, hx⟩,
    refine m_mem (acc.intro _ ( λ y y_gt_m, _)),
    by_contra hy,
    exact hm y hy y_gt_m, },
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
@well_founded_iff_has_max' (order_dual α) _

open set
/-- The supremum of a bounded, well-founded order -/
protected noncomputable def sup {α} {r : α → α → Prop} (wf : well_founded r) (s : set α)
  (h : bounded r s) : α :=
wf.min { x | ∀a ∈ s, r a x } h

protected lemma lt_sup {α} {r : α → α → Prop} (wf : well_founded r) {s : set α} (h : bounded r s)
  {x} (hx : x ∈ s) : r x (wf.sup s h) :=
min_mem wf { x | ∀a ∈ s, r a x } h x hx

section
open_locale classical
/-- A successor of an element `x` in a well-founded order is a minimal element `y` such that
`x < y` if one exists. Otherwise it is `x` itself. -/
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
