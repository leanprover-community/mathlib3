/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.asymptotics.asymptotics

/-!
# Asymptotic equivalence up to a constant

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `asymptotics.is_Theta l f g` (notation: `f =Θ[l] g`) as
`f =O[l] g ∧ g =O[l] f`, then prove basic properties of this equivalence relation.
-/

open filter
open_locale topology

namespace asymptotics

variables {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*}
  {E' : Type*} {F' : Type*} {G' : Type*}
  {E'' : Type*} {F'' : Type*} {G'' : Type*}
  {R : Type*} {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variables [has_norm E] [has_norm F] [has_norm G]
variables [seminormed_add_comm_group E'] [seminormed_add_comm_group F']
  [seminormed_add_comm_group G'] [normed_add_comm_group E''] [normed_add_comm_group F'']
  [normed_add_comm_group G''] [semi_normed_ring R] [semi_normed_ring R']
variables [normed_field 𝕜] [normed_field 𝕜']
variables {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}
variables {f' : α → E'} {g' : α → F'} {k' : α → G'}
variables {f'' : α → E''} {g'' : α → F''}
variables {l l' : filter α}

/-- We say that `f` is `Θ(g)` along a filter `l` (notation: `f =Θ[l] g`) if `f =O[l] g` and
`g =O[l] f`. -/
def is_Theta (l : filter α) (f : α → E) (g : α → F) : Prop := is_O l f g ∧ is_O l g f

notation f ` =Θ[`:100 l `] ` g:100 := is_Theta l f g

lemma is_O.antisymm (h₁ : f =O[l] g) (h₂ : g =O[l] f) : f =Θ[l] g := ⟨h₁, h₂⟩

@[refl] lemma is_Theta_refl (f : α → E) (l : filter α) : f =Θ[l] f := ⟨is_O_refl _ _, is_O_refl _ _⟩
lemma is_Theta_rfl : f =Θ[l] f := is_Theta_refl _ _
@[symm] lemma is_Theta.symm (h : f =Θ[l] g) : g =Θ[l] f := h.symm

lemma is_Theta_comm : f =Θ[l] g ↔ g =Θ[l] f := ⟨λ h, h.symm, λ h, h.symm⟩

@[trans] lemma is_Theta.trans {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =Θ[l] g)
  (h₂ : g =Θ[l] k) : f =Θ[l] k :=
⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

@[trans] lemma is_O.trans_is_Theta {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =O[l] g)
  (h₂ : g =Θ[l] k) : f =O[l] k :=
h₁.trans h₂.1

@[trans] lemma is_Theta.trans_is_O {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =Θ[l] g)
  (h₂ : g =O[l] k) : f =O[l] k :=
h₁.1.trans h₂

@[trans] lemma is_o.trans_is_Theta {f : α → E} {g : α → F} {k : α → G'} (h₁ : f =o[l] g)
  (h₂ : g =Θ[l] k) : f =o[l] k :=
h₁.trans_is_O h₂.1

@[trans] lemma is_Theta.trans_is_o {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =Θ[l] g)
  (h₂ : g =o[l] k) : f =o[l] k :=
h₁.1.trans_is_o h₂

@[trans] lemma is_Theta.trans_eventually_eq {f : α → E} {g₁ g₂ : α → F} (h : f =Θ[l] g₁)
  (hg : g₁ =ᶠ[l] g₂) : f =Θ[l] g₂ :=
⟨h.1.trans_eventually_eq hg, hg.symm.trans_is_O h.2⟩

@[trans] lemma _root_.filter.eventually_eq.trans_is_Theta {f₁ f₂ : α → E} {g : α → F}
  (hf : f₁ =ᶠ[l] f₂) (h : f₂ =Θ[l] g) : f₁ =Θ[l] g :=
⟨hf.trans_is_O h.1, h.2.trans_eventually_eq hf.symm⟩

@[simp] lemma is_Theta_norm_left : (λ x, ‖f' x‖) =Θ[l] g ↔ f' =Θ[l] g := by simp [is_Theta]
@[simp] lemma is_Theta_norm_right : f =Θ[l] (λ x, ‖g' x‖) ↔ f =Θ[l] g' := by simp [is_Theta]

alias is_Theta_norm_left ↔ is_Theta.of_norm_left is_Theta.norm_left
alias is_Theta_norm_right ↔ is_Theta.of_norm_right is_Theta.norm_right

lemma is_Theta_of_norm_eventually_eq (h : (λ x, ‖f x‖) =ᶠ[l] (λ x, ‖g x‖)) : f =Θ[l] g :=
⟨is_O.of_bound 1 $ by simpa only [one_mul] using h.le,
  is_O.of_bound 1 $ by simpa only [one_mul] using h.symm.le⟩

lemma is_Theta_of_norm_eventually_eq' {g : α → ℝ} (h : (λ x, ‖f' x‖) =ᶠ[l] g) : f' =Θ[l] g :=
is_Theta_of_norm_eventually_eq $ h.mono $ λ x hx, by simp only [← hx, norm_norm]

lemma is_Theta.is_o_congr_left (h : f' =Θ[l] g') : f' =o[l] k ↔ g' =o[l] k :=
⟨h.symm.trans_is_o, h.trans_is_o⟩

lemma is_Theta.is_o_congr_right (h : g' =Θ[l] k') : f =o[l] g' ↔ f =o[l] k' :=
⟨λ H, H.trans_is_Theta h, λ H, H.trans_is_Theta h.symm⟩

lemma is_Theta.is_O_congr_left (h : f' =Θ[l] g') : f' =O[l] k ↔ g' =O[l] k :=
⟨h.symm.trans_is_O, h.trans_is_O⟩

lemma is_Theta.is_O_congr_right (h : g' =Θ[l] k') : f =O[l] g' ↔ f =O[l] k' :=
⟨λ H, H.trans_is_Theta h, λ H, H.trans_is_Theta h.symm⟩

lemma is_Theta.mono (h : f =Θ[l] g) (hl : l' ≤ l) : f =Θ[l'] g := ⟨h.1.mono hl, h.2.mono hl⟩

lemma is_Theta.sup (h : f' =Θ[l] g') (h' : f' =Θ[l'] g') : f' =Θ[l ⊔ l'] g' :=
⟨h.1.sup h'.1, h.2.sup h'.2⟩

@[simp] lemma is_Theta_sup : f' =Θ[l ⊔ l'] g' ↔ f' =Θ[l] g' ∧ f' =Θ[l'] g' :=
⟨λ h, ⟨h.mono le_sup_left, h.mono le_sup_right⟩, λ h, h.1.sup h.2⟩

lemma is_Theta.eq_zero_iff (h : f'' =Θ[l] g'') : ∀ᶠ x in l, f'' x = 0 ↔ g'' x = 0 :=
h.1.eq_zero_imp.mp $ h.2.eq_zero_imp.mono $ λ x, iff.intro

lemma is_Theta.tendsto_zero_iff (h : f'' =Θ[l] g'') : tendsto f'' l (𝓝 0) ↔ tendsto g'' l (𝓝 0) :=
by simp only [← is_o_one_iff ℝ, h.is_o_congr_left]

lemma is_Theta.tendsto_norm_at_top_iff (h : f' =Θ[l] g') :
  tendsto (norm ∘ f') l at_top ↔ tendsto (norm ∘ g') l at_top :=
by simp only [← is_o_const_left_of_ne (one_ne_zero' ℝ), h.is_o_congr_right]

lemma is_Theta.is_bounded_under_le_iff (h : f' =Θ[l] g') :
  is_bounded_under (≤) l (norm ∘ f') ↔ is_bounded_under (≤) l (norm ∘ g') :=
by simp only [← is_O_const_of_ne (one_ne_zero' ℝ), h.is_O_congr_left]

lemma is_Theta.smul [normed_space 𝕜 E'] [normed_space 𝕜' F'] {f₁ : α → 𝕜} {f₂ : α → 𝕜'}
  {g₁ : α → E'} {g₂ : α → F'} (hf : f₁ =Θ[l] f₂) (hg : g₁ =Θ[l] g₂) :
  (λ x, f₁ x • g₁ x) =Θ[l] (λ x, f₂ x • g₂ x) :=
⟨hf.1.smul hg.1, hf.2.smul hg.2⟩

lemma is_Theta.mul {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂) :
  (λ x, f₁ x * f₂ x) =Θ[l] (λ x, g₁ x * g₂ x) :=
h₁.smul h₂

lemma is_Theta.inv {f : α → 𝕜} {g : α → 𝕜'} (h : f =Θ[l] g) : (λ x, (f x)⁻¹) =Θ[l] (λ x, (g x)⁻¹) :=
⟨h.2.inv_rev h.1.eq_zero_imp, h.1.inv_rev h.2.eq_zero_imp⟩

@[simp] lemma is_Theta_inv {f : α → 𝕜} {g : α → 𝕜'} :
  (λ x, (f x)⁻¹) =Θ[l] (λ x, (g x)⁻¹) ↔ f =Θ[l] g :=
⟨λ h, by simpa only [inv_inv] using h.inv, is_Theta.inv⟩

lemma is_Theta.div {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂) :
  (λ x, f₁ x / f₂ x) =Θ[l] (λ x, g₁ x / g₂ x) :=
by simpa only [div_eq_mul_inv] using h₁.mul h₂.inv

lemma is_Theta.pow {f : α → 𝕜} {g : α → 𝕜'} (h : f =Θ[l] g) (n : ℕ) :
  (λ x, (f x) ^ n) =Θ[l] (λ x, (g x) ^ n) :=
⟨h.1.pow n, h.2.pow n⟩

lemma is_Theta.zpow {f : α → 𝕜} {g : α → 𝕜'} (h : f =Θ[l] g) (n : ℤ) :
  (λ x, (f x) ^ n) =Θ[l] (λ x, (g x) ^ n) :=
begin
  cases n,
  { simpa only [zpow_of_nat] using h.pow _ },
  { simpa only [zpow_neg_succ_of_nat] using (h.pow _).inv }
end

lemma is_Theta_const_const {c₁ : E''} {c₂ : F''} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
  (λ x : α, c₁) =Θ[l] (λ x, c₂) :=
⟨is_O_const_const _ h₂ _, is_O_const_const _ h₁ _⟩

@[simp] lemma is_Theta_const_const_iff [ne_bot l] {c₁ : E''} {c₂ : F''} :
  (λ x : α, c₁) =Θ[l] (λ x, c₂) ↔ (c₁ = 0 ↔ c₂ = 0) :=
by simpa only [is_Theta, is_O_const_const_iff, ← iff_def] using iff.comm

@[simp] lemma is_Theta_zero_left : (λ x, (0 : E')) =Θ[l] g'' ↔ g'' =ᶠ[l] 0 :=
by simp only [is_Theta, is_O_zero, is_O_zero_right_iff, true_and]

@[simp] lemma is_Theta_zero_right : f'' =Θ[l] (λ x, (0 : F')) ↔ f'' =ᶠ[l] 0 :=
is_Theta_comm.trans is_Theta_zero_left

lemma is_Theta_const_smul_left [normed_space 𝕜 E'] {c : 𝕜} (hc : c ≠ 0) :
  (λ x, c • f' x) =Θ[l] g ↔ f' =Θ[l] g :=
and_congr (is_O_const_smul_left hc) (is_O_const_smul_right hc)

alias is_Theta_const_smul_left ↔ is_Theta.of_const_smul_left is_Theta.const_smul_left

lemma is_Theta_const_smul_right [normed_space 𝕜 F'] {c : 𝕜} (hc : c ≠ 0) :
  f =Θ[l] (λ x, c • g' x) ↔ f =Θ[l] g' :=
and_congr (is_O_const_smul_right hc) (is_O_const_smul_left hc)

alias is_Theta_const_smul_right ↔ is_Theta.of_const_smul_right is_Theta.const_smul_right

lemma is_Theta_const_mul_left {c : 𝕜} {f : α → 𝕜} (hc : c ≠ 0) :
  (λ x, c * f x) =Θ[l] g ↔ f =Θ[l] g :=
by simpa only [← smul_eq_mul] using is_Theta_const_smul_left hc

alias is_Theta_const_mul_left ↔ is_Theta.of_const_mul_left is_Theta.const_mul_left

lemma is_Theta_const_mul_right {c : 𝕜} {g : α → 𝕜} (hc : c ≠ 0) :
  f =Θ[l] (λ x, c * g x) ↔ f =Θ[l] g :=
by simpa only [← smul_eq_mul] using is_Theta_const_smul_right hc

alias is_Theta_const_mul_right ↔ is_Theta.of_const_mul_right is_Theta.const_mul_right

end asymptotics
