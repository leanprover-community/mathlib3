/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/

import tactic.apply
import control.fix
import order.omega_complete_partial_order

/-!
# Lawful fixed point operators

This module defines the laws required of a `has_fix` instance, using the theory of
omega complete partial orders (ωCPO). Proofs of the lawfulness of all `has_fix` instances in
`control.fix` are provided.

## Main definition

 * class `lawful_fix`
-/

universes u v

open_locale classical
variables {α : Type*} {β : α → Type*}

open omega_complete_partial_order

/-- Intuitively, a fixed point operator `fix` is lawful if it satisfies `fix f = f (fix f)` for all
`f`, but this is inconsistent / uninteresting in most cases due to the existence of "exotic"
functions `f`, such as the function that is defined iff its argument is not, familiar from the
halting problem. Instead, this requirement is limited to only functions that are `continuous` in the
sense of `ω`-complete partial orders, which excludes the example because it is not monotone
(making the input argument less defined can make `f` more defined). -/
class lawful_fix (α : Type*) [omega_complete_partial_order α] extends has_fix α :=
(fix_eq : ∀ {f : α →o α}, continuous f → has_fix.fix f = f (has_fix.fix f))

lemma lawful_fix.fix_eq' {α} [omega_complete_partial_order α] [lawful_fix α]
  {f : α → α} (hf : continuous' f) :
  has_fix.fix f = f (has_fix.fix f) :=
lawful_fix.fix_eq (hf.to_bundled _)

namespace part

open part nat nat.upto

namespace fix

variables (f : (Π a, part $ β a) →o (Π a, part $ β a))

lemma approx_mono' {i : ℕ} : fix.approx f i ≤ fix.approx f (succ i) :=
begin
  induction i, dsimp [approx], apply @bot_le _ _ _ (f ⊥),
  intro, apply f.monotone, apply i_ih
end

lemma approx_mono ⦃i j : ℕ⦄ (hij : i ≤ j) : approx f i ≤ approx f j :=
begin
  induction j, cases hij, refine @le_refl _ _ _,
  cases hij, apply @le_refl _ _ _,
  apply @le_trans _ _ _ (approx f j_n) _ (j_ih ‹_›),
  apply approx_mono' f
end

lemma mem_iff (a : α) (b : β a) : b ∈ part.fix f a ↔ ∃ i, b ∈ approx f i a :=
begin
  by_cases h₀ : ∃ (i : ℕ), (approx f i a).dom,
  { simp only [part.fix_def f h₀],
    split; intro hh, exact ⟨_,hh⟩,
    have h₁ := nat.find_spec h₀,
    rw [dom_iff_mem] at h₁,
    cases h₁ with y h₁,
    replace h₁ := approx_mono' f _ _ h₁,
    suffices : y = b, subst this, exact h₁,
    cases hh with i hh,
    revert h₁, generalize : (succ (nat.find h₀)) = j, intro,
    wlog : i ≤ j := le_total i j using [i j b y,j i y b],
    replace hh := approx_mono f case _ _ hh,
    apply part.mem_unique h₁ hh },
  { simp only [fix_def' ⇑f h₀, not_exists, false_iff, not_mem_none],
    simp only [dom_iff_mem, not_exists] at h₀,
    intro, apply h₀ }
end

lemma approx_le_fix (i : ℕ) : approx f i ≤ part.fix f :=
assume a b hh,
by { rw [mem_iff f], exact ⟨_,hh⟩ }

lemma exists_fix_le_approx (x : α) : ∃ i, part.fix f x ≤ approx f i x :=
begin
  by_cases hh : ∃ i b, b ∈ approx f i x,
  { rcases hh with ⟨i,b,hb⟩, existsi i,
    intros b' h',
    have hb' := approx_le_fix f i _ _ hb,
    have hh := part.mem_unique h' hb',
    subst hh, exact hb },
  { simp only [not_exists] at hh, existsi 0,
    intros b' h',
    simp only [mem_iff f] at h',
    cases h' with i h',
    cases hh _ _ h' }
end

include f

/-- The series of approximations of `fix f` (see `approx`) as a `chain` -/
def approx_chain : chain (Π a, part $ β a) := ⟨approx f, approx_mono f⟩

lemma le_f_of_mem_approx {x} (hx : x ∈ approx_chain f) : x ≤ f x :=
begin
  revert hx, simp [(∈)],
  intros i hx, subst x,
  apply approx_mono'
end

lemma approx_mem_approx_chain {i} : approx f i ∈ approx_chain f :=
stream.mem_of_nth_eq rfl

end fix

open fix

variables {α}
variables (f : (Π a, part $ β a) →o (Π a, part $ β a))

open omega_complete_partial_order

open part (hiding ωSup) nat
open nat.upto omega_complete_partial_order

lemma fix_eq_ωSup : part.fix f = ωSup (approx_chain f) :=
begin
  apply le_antisymm,
  { intro x, cases exists_fix_le_approx f x with i hx,
    transitivity' approx f i.succ x,
    { transitivity', apply hx, apply approx_mono' f },
    apply' le_ωSup_of_le i.succ,
    dsimp [approx], refl', },
  { apply ωSup_le _ _ _,
    simp only [fix.approx_chain, order_hom.coe_fun_mk],
    intros y x, apply approx_le_fix f },
end

lemma fix_le {X : Π a, part $ β a} (hX : f X ≤ X) : part.fix f ≤ X :=
begin
  rw fix_eq_ωSup f,
  apply ωSup_le _ _ _,
  simp only [fix.approx_chain, order_hom.coe_fun_mk],
  intros i,
  induction i, dsimp [fix.approx], apply' bot_le,
  transitivity' f X, apply f.monotone i_ih,
  apply hX
end

variables {f} (hc : continuous f)
include hc

lemma fix_eq : part.fix f = f (part.fix f) :=
begin
  rw [fix_eq_ωSup f,hc],
  apply le_antisymm,
  { apply ωSup_le_ωSup_of_le _,
    intros i, existsi [i], intro x, -- intros x y hx,
    apply le_f_of_mem_approx _ ⟨i, rfl⟩, },
  { apply ωSup_le_ωSup_of_le _,
    intros i, existsi i.succ, refl', }
end

end part

namespace part

/-- `to_unit` as a monotone function -/
@[simps]
def to_unit_mono (f : part α →o part α) : (unit → part α) →o (unit → part α) :=
{ to_fun := λ x u, f (x u),
  monotone' := λ x y (h : x ≤ y) u, f.monotone $ h u }

lemma to_unit_cont (f : part α →o part α) (hc : continuous f) : continuous (to_unit_mono f)
| c := begin
  ext ⟨⟩ : 1,
  dsimp [omega_complete_partial_order.ωSup],
  erw [hc, chain.map_comp], refl
end

noncomputable instance : lawful_fix (part α) :=
⟨λ f hc, show part.fix (to_unit_mono f) () = _, by rw part.fix_eq (to_unit_cont f hc); refl⟩

end part

open sigma

namespace pi

noncomputable instance {β} : lawful_fix (α → part β) := ⟨λ f, part.fix_eq⟩

variables {γ : Π a : α, β a → Type*}

section monotone

variables (α β γ)

/-- `sigma.curry` as a monotone function. -/
@[simps]
def monotone_curry [∀ x y, preorder $ γ x y] :
  (Π x : Σ a, β a, γ x.1 x.2) →o (Π a (b : β a), γ a b) :=
{ to_fun := curry,
  monotone' := λ x y h a b, h ⟨a,b⟩ }

/-- `sigma.uncurry` as a monotone function. -/
@[simps]
def monotone_uncurry [∀ x y, preorder $ γ x y] :
  (Π a (b : β a), γ a b) →o (Π x : Σ a, β a, γ x.1 x.2) :=
{ to_fun := uncurry,
  monotone' := λ x y h a, h a.1 a.2 }

variables [∀ x y, omega_complete_partial_order $ γ x y]

open omega_complete_partial_order.chain

lemma continuous_curry : continuous $ monotone_curry α β γ :=
λ c, by { ext x y, dsimp [curry,ωSup], rw [map_comp,map_comp], refl }

lemma continuous_uncurry : continuous $ monotone_uncurry α β γ :=
λ c, by { ext x y, dsimp [uncurry,ωSup], rw [map_comp,map_comp], refl }

end monotone

open has_fix

instance [has_fix $ Π x : sigma β, γ x.1 x.2] : has_fix (Π x (y : β x), γ x y) :=
⟨ λ f, curry (fix $ uncurry ∘ f ∘ curry) ⟩

variables [∀ x y, omega_complete_partial_order $ γ x y]

section curry

variables {f : (Π x (y : β x), γ x y) →o (Π x (y : β x), γ x y)}
variables (hc : continuous f)

lemma uncurry_curry_continuous :
  continuous $ (monotone_uncurry α β γ).comp $ f.comp $ monotone_curry α β γ :=
continuous_comp _ _
  (continuous_comp _ _ (continuous_curry _ _ _) hc)
  (continuous_uncurry _ _ _)

end curry

instance pi.lawful_fix' [lawful_fix $ Π x : sigma β, γ x.1 x.2] : lawful_fix (Π x y, γ x y) :=
{ fix_eq := λ f hc,
    begin
      dsimp [fix],
      conv { to_lhs, erw [lawful_fix.fix_eq (uncurry_curry_continuous hc)] },
      refl,
    end, }

end pi
