/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/

import data.nat.up
import data.stream.basic
import order.omega_complete_partial_order

/-!
# Fixed point

This module defines a generic `fix` operator for defining recursive
computations that are not necessarily well-founded or productive.
An instance is defined for `roption`. The proof of its laws relies
on omega complete partial orders (ωCPO).

## Main definition

 * class `has_fix`
 * class `lawful_fix`
 * `roption.fix`
-/

universes u v

open_locale classical
variables {α : Type*} {β : α → Type*}

/-- `has_fix α` gives us a way to calculate the fixed point
of function of type `α → α`. -/
class has_fix (α : Type*) :=
(fix : (α → α) → α)

open omega_complete_partial_order

section prio

set_option default_priority 100  -- see Note [default priority]

/-- Laws for fixed point operator -/
class lawful_fix (α : Type*) [omega_complete_partial_order α] extends has_fix α :=
(fix_eq : ∀ {f : α →ₘ α}, continuous f → has_fix.fix f = f (has_fix.fix f))

lemma lawful_fix.fix_eq' {α} [omega_complete_partial_order α] [lawful_fix α]
  {f : α → α} (hf : continuous' f) :
  has_fix.fix f = f (has_fix.fix f) :=
lawful_fix.fix_eq (continuous.to_bundled _ hf)

end prio

namespace roption

open roption nat nat.up

section basic

variables (f : (Π a, roption $ β a) → (Π a, roption $ β a))

/-- series of successive, finite approximation of the fixed point of `f` -/
def fix.approx : stream $ Π a, roption $ β a
| 0 := ⊥
| (nat.succ i) := f (fix.approx i)

/-- loop body for finding the fixed point of `f` -/
def fix_aux {p : ℕ → Prop} (i : nat.up p) (g : Π j : nat.up p, i < j → Π a, roption $ β a) : Π a, roption $ β a :=
f $ λ x : α,
assert (¬p (i.val)) $ λ h : ¬ p (i.val),
g (i.succ h) (nat.lt_succ_self _) x

/-- fixed point of `f` -/
protected def fix (x : α) : roption $ β x :=
roption.assert (∃ i, (fix.approx f i x).dom) $ λ h,
well_founded.fix.{1} (nat.up.wf h) (fix_aux f) nat.up.zero x

protected lemma fix_def {x : α} (h' : ∃ i, (fix.approx f i x).dom) :
  roption.fix f x = fix.approx f (nat.succ $ nat.find h') x :=
begin
  let p := λ (i : ℕ), (fix.approx f i x).dom,
  have : p (nat.find h') := nat.find_spec h',
  generalize hk : nat.find h' = k,
  replace hk : nat.find h' = k + (@up.zero p).val := hk,
  rw hk at this,
  revert hk,
  dsimp [roption.fix], rw assert_pos h', revert this,
  generalize : up.zero = z, intros,
  suffices : ∀ x', well_founded.fix (fix._proof_1 f x h') (fix_aux f) z x' = fix.approx f (succ k) x',
    from this _,
  induction k generalizing z; intro,
  { rw [fix.approx,well_founded.fix_eq,fix_aux],
    congr, ext : 1, rw assert_neg, refl,
    rw nat.zero_add at this,
    simpa only [not_not, subtype.val_eq_coe] },
  { rw [fix.approx,well_founded.fix_eq,fix_aux],
    congr, ext : 1,
    have hh : ¬(fix.approx f (z.val) x).dom,
    { apply nat.find_min h',
      rw [hk,nat.succ_add,← nat.add_succ],
      apply nat.lt_of_succ_le,
      apply nat.le_add_left },
    rw succ_add_eq_succ_add at this hk,
    rw [assert_pos hh, k_ih (up.succ z hh) this hk] }
end

lemma fix_def' {x : α} (h' : ¬ ∃ i, (fix.approx f i x).dom) :
  roption.fix f x = none :=
by dsimp [roption.fix]; rw assert_neg h'

end basic

namespace fix

variables (f : (Π a, roption $ β a) →ₘ (Π a, roption $ β a))

lemma approx_mono' {i : ℕ} : fix.approx f i ≤ fix.approx f (succ i) :=
begin
  induction i, dsimp [approx], apply @bot_le _ _ (f ⊥),
  intro, apply f.monotone, apply i_ih
end

lemma approx_mono ⦃i j : ℕ⦄ (hij : i ≤ j) : approx f i ≤ approx f j :=
begin
  induction j, cases hij, refine @le_refl _ _ _,
  cases hij, apply @le_refl _ _ _,
  apply @le_trans _ _ _ (approx f j_n) _ (j_ih hij_a),
  apply approx_mono' f
end

lemma mem_iff (a : α) (b : β a) : b ∈ roption.fix f a ↔ ∃ i, b ∈ approx f i a :=
begin
  by_cases h₀ : ∃ (i : ℕ), (approx f i a).dom,
  { simp only [roption.fix_def f h₀],
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
    apply roption.mem_unique h₁ hh },
  { simp only [fix_def' ⇑f h₀, not_exists, false_iff, not_mem_none],
    simp only [dom_iff_mem, not_exists] at h₀,
    intro, apply h₀ }
end

lemma approx_le_fix (i : ℕ) : approx f i ≤ roption.fix f :=
assume a b hh,
by { rw [mem_iff f], exact ⟨_,hh⟩ }

lemma exists_fix_le_approx (x : α) : ∃ i, roption.fix f x ≤ approx f i x :=
begin
  by_cases hh : ∃ i b, b ∈ approx f i x,
  { rcases hh with ⟨i,b,hb⟩, existsi i,
    intros b' h',
    have hb' := approx_le_fix f i _ _ hb,
    have hh := roption.mem_unique h' hb',
    subst hh, exact hb },
  { simp only [not_exists] at hh, existsi 0,
    intros b' h',
    simp only [mem_iff f] at h',
    cases h' with i h',
    cases hh _ _ h' }
end

include f

/-- series of approximations of `fix f` as a `chain` -/
def approx_chain : chain (Π a, roption $ β a) :=
⟨ approx f, approx_mono f ⟩

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
variables (f : (Π a, roption $ β a) →ₘ (Π a, roption $ β a))

open omega_complete_partial_order

open roption (hiding ωSup) nat
open nat.up omega_complete_partial_order

lemma fix_eq_ωSup : roption.fix f = ωSup (approx_chain f) :=
begin
  apply le_antisymm,
  { intro x, cases exists_fix_le_approx f x with i hx,
    transitivity' approx f i.succ x,
    { transitivity', apply hx, apply approx_mono' f },
    apply' le_ωSup_of_le i.succ,
    dsimp [approx], refl', },
  { apply ωSup_le _ _ _,
    simp only [fix.approx_chain, preorder_hom.coe_fun_mk],
    intros y x, apply approx_le_fix f },
end

lemma fix_le {X : Π a, roption $ β a} (hX : f X ≤ X) : roption.fix f ≤ X :=
begin
  rw fix_eq_ωSup f,
  apply ωSup_le _ _ _,
  simp only [fix.approx_chain, preorder_hom.coe_fun_mk],
  intros i,
  induction i, dsimp [fix.approx], apply' bot_le,
  transitivity' f X, apply f.monotone i_ih,
  apply hX
end

variables {f} (hc : continuous f)
include hc

lemma fix_eq : roption.fix f = f (roption.fix f) :=
begin
  rw [fix_eq_ωSup f,hc],
  apply le_antisymm,
  { apply ωSup_le_ωSup_of_le _,
    intros i, existsi [i], intro x, -- intros x y hx,
    apply le_f_of_mem_approx _ ⟨i, rfl⟩, },
  { apply ωSup_le_ωSup_of_le _,
    intros i, existsi i.succ, refl', }
end

end roption

namespace roption

/-- Convert a function from and to `α` to a function from and to `unit → α`. Useful because
the fixed point machinery for `roption` assumes functions with one argument -/
def to_unit (f : α → α) (x : unit → α) (u : unit) : α := f (x u)

instance : has_fix (roption α) :=
⟨ λ f, roption.fix (to_unit f) () ⟩

/-- `to_unit` as a monotone function -/
@[simps]
def to_unit_mono (f : roption α →ₘ roption α) : (unit → roption α) →ₘ (unit → roption α) :=
{ to_fun := to_unit f,
  monotone := λ x y, assume h : x ≤ y,
    show to_unit f x ≤ to_unit f y,
    from λ u, f.monotone $ h u }

lemma fold_to_unit_mono (f : roption α →ₘ roption α) : to_unit f = to_unit_mono f := rfl

lemma to_unit_cont (f : roption α →ₘ roption α) : Π hc : continuous f, continuous (to_unit_mono f)
| hc := by { intro c, ext ⟨⟩ : 1, dsimp [to_unit,omega_complete_partial_order.ωSup], erw [hc,chain.map_comp], refl }

noncomputable instance : lawful_fix (roption α) :=
⟨ λ f hc, by { dsimp [has_fix.fix],
              conv { to_lhs, rw [fold_to_unit_mono,roption.fix_eq (to_unit_cont f hc)] }, refl } ⟩

end roption

open sigma

namespace pi

instance roption.has_fix {β} : has_fix (α → roption β) :=
⟨ roption.fix ⟩

noncomputable instance {β} : lawful_fix (α → roption β) :=
⟨ λ f hc, by { dsimp [has_fix.fix], conv { to_lhs, rw [roption.fix_eq hc], } } ⟩

variables {γ : Π a : α, β a → Type*}

section monotone

variables (α β γ)

/-- `sigma.curry` as a monotone function -/
@[simps]
def monotone_curry [∀ x y, preorder $ γ x y] : (Π x : Σ a, β a, γ x.1 x.2) →ₘ (Π a (b : β a), γ a b) :=
{ to_fun := curry,
  monotone := λ x y h a b, h ⟨a,b⟩ }

/-- `sigma.uncurry` as a monotone function -/
@[simps]
def monotone_uncurry [∀ x y, preorder $ γ x y] : (Π a (b : β a), γ a b) →ₘ (Π x : Σ a, β a, γ x.1 x.2) :=
{ to_fun := uncurry,
  monotone := λ x y h a, h a.1 a.2 }

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

variables {f : (Π x (y : β x), γ x y) →ₘ (Π x (y : β x), γ x y)}
variables (hc : continuous f)

lemma uncurry_curry_continuous : continuous $ (monotone_uncurry α β γ).comp $ f.comp $ monotone_curry α β γ :=
continuous_comp _ _
  (continuous_comp _ _ (continuous_curry _ _ _) hc)
  (continuous_uncurry _ _ _)

end curry

instance pi.lawful_fix' [lawful_fix $ Π x : sigma β, γ x.1 x.2] : lawful_fix (Π x y, γ x y) :=
{ fix_eq := λ f hc,
  by { dsimp [fix], conv { to_lhs, erw [lawful_fix.fix_eq (uncurry_curry_continuous hc)] }, refl, } }

end pi
