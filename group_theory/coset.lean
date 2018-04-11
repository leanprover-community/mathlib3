/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Scott Morrison
-/

import group_theory.subgroup

open set

variable {γ : Type*}

def left_coset [has_mul γ] (a : γ) (s : set γ) : set γ := (λ x, a * x) '' s
def right_coset [has_mul γ] (s : set γ) (a : γ) : set γ := (λ x, x * a) '' s

local infix ` *l `:70 := left_coset
local infix ` *r `:70 := right_coset

section coset_mul
variable [has_mul γ]

lemma mem_left_coset {s : set γ} {x : γ} (a : γ) (hxS : x ∈ s) : a * x ∈ a *l s :=
mem_image_of_mem (λ b : γ, a * b) hxS

lemma mem_right_coset {s : set γ} {x : γ} (a : γ) (hxS : x ∈ s) : x * a ∈ s *r a :=
mem_image_of_mem (λ b : γ, b * a) hxS

def left_coset_equiv (s : set γ) (a b : γ) := a *l s = b *l s

lemma left_coset_equiv_rel (s : set γ) : equivalence (left_coset_equiv s) :=
mk_equivalence (left_coset_equiv s) (λ a, rfl) (λ a b, eq.symm) (λ a b c, eq.trans)

end coset_mul

section coset_semigroup
variable [semigroup γ]

lemma left_coset_assoc (s : set γ) (a b : γ) : a *l (b *l s) = (a * b) *l s :=
have h : (λ x : γ, a * x) ∘ (λ x : γ, b * x) = (λ x : γ, (a * b) * x), from
  funext (λ c : γ,
    calc ((λ x : γ, a * x) ∘ (λ x : γ, b * x)) c = a * (b * c) : by simp
    ... = (λ x : γ, (a * b) * x) c : by rw ← mul_assoc; simp ),
calc a *l (b *l s) = image ((λ x : γ, a * x) ∘ (λ x : γ, b * x)) s :
    by rw [left_coset, left_coset, ←image_comp]
  ... = (a * b) *l s : by rw [left_coset, h]

lemma right_coset_assoc (s : set γ) (a b : γ) : s *r a *r b = s *r (a * b) :=
have h : (λ x : γ, x * b) ∘ (λ x : γ, x * a) = (λ x : γ, x * (a * b)), from
  funext (λ c : γ,
    calc ((λ x : γ, x * b) ∘ (λ x : γ, x * a)) c = c * a * b :
        by simp
      ... = (λ x : γ, x * (a * b)) c :
        by rw mul_assoc; simp),
calc s *r a *r b  = image ((λ x : γ, x * b) ∘ (λ x : γ, x * a)) s :
    by rw [right_coset, right_coset, ←image_comp]
  ... = s *r (a * b) :
    by rw [right_coset, h]

lemma left_coset_right_coset (s : set γ) (a b : γ) : a *l s *r  b = a *l (s *r b) :=
have h : (λ x : γ, x * b) ∘ (λ x : γ, a * x) = (λ x : γ, a * (x * b)), from
  funext (λ c : γ,
    calc ((λ x : γ, x * b) ∘ (λ x : γ, a * x)) c = a * c * b : by simp
      ... = (λ x : γ, a * (c * b)) c : by rw mul_assoc; simp),
calc a *l s *r b   = image ((λ x : γ, x * b) ∘ (λ x : γ, a * x)) s :
    by rw [right_coset, left_coset, ←image_comp]
  ... = a *l (s *r b) :
    by rw [right_coset, left_coset, ←image_comp, h]

end coset_semigroup

section coset_subgroup
open is_submonoid
open is_subgroup
variables [group γ] (s : set γ) [is_subgroup s]

lemma left_coset_mem_left_coset {a : γ} (ha : a ∈ s) : a *l s = s :=
begin
  simp [left_coset, image, set_eq_def, mem_set_of_eq],
  intro b,
  split,
  { intro h,
    cases h with x hx,
    cases hx with hxl hxr,
    rw [←hxr],
    exact mul_mem ha hxl },
  { intro h,
    existsi a⁻¹ * b,
    split,
    have : a⁻¹ ∈ s, from inv_mem ha,
    exact mul_mem this h,
    simp }
end

lemma right_coset_mem_right_coset {a : γ} (ha : a ∈ s) : s *r a = s :=
begin
  simp [right_coset, image, set_eq_def, mem_set_of_eq],
  intro b,
  split,
  { intro h,
    cases h with x hx,
    cases hx with hxl hxr,
    rw [←hxr],
    exact mul_mem hxl ha },
  { intro h,
    existsi b * a⁻¹,
    split,
    have : a⁻¹ ∈ s, from inv_mem ha,
    exact mul_mem h this,
    simp }
end

lemma one_left_coset : 1 *l s = s := left_coset_mem_left_coset s (one_mem s)

lemma one_right_coset : s *r 1 = s := right_coset_mem_right_coset s (one_mem s)

lemma mem_own_left_coset (a : γ) : a ∈ a *l s :=
by conv in a {rw ←mul_one a}; exact (mem_left_coset a (one_mem s))

lemma mem_own_right_coset (a : γ) : a ∈ s *r a :=
by conv in a {rw ←one_mul a}; exact (mem_right_coset a (one_mem s))

lemma mem_left_coset_left_coset {a : γ} (ha : a *l s = s) : a ∈ s :=
by rw [←ha]; exact mem_own_left_coset s a

lemma mem_right_coset_right_coset {a : γ} (ha : s *r a = s) : a ∈ s :=
by rw [←ha]; exact mem_own_right_coset s a

lemma mem_mem_left_coset {a x : γ} (hx : x ∈ s) (hax : a * x ∈ s) : a ∈ s :=
begin
  apply mem_left_coset_left_coset s,
  conv in s { rw ←left_coset_mem_left_coset s hx },
  rw [left_coset_assoc, left_coset_mem_left_coset s hax]
end

theorem normal_of_eq_cosets [normal_subgroup s] : ∀ g, g *l s = s *r g :=
begin
  intros g,
  apply eq_of_subset_of_subset,
  all_goals { simp [left_coset, right_coset, image], intros a n ha hn },
  existsi g * n * g⁻¹, tactic.swap, existsi g⁻¹ * n * (g⁻¹)⁻¹,
  all_goals {split, apply normal_subgroup.normal, assumption },
  { rw inv_inv g, rw [←mul_assoc, ←mul_assoc], simp, assumption },
  { simp, assumption }
end

theorem eq_cosets_of_normal (h : ∀ g, g *l s = s *r g) : normal_subgroup s:=
begin
  split,
  intros n hn g,
  have hl : g * n ∈ g *l s, from mem_left_coset g hn,
  rw h at hl,
  simp [right_coset] at hl,
  cases hl with x hx,
  cases hx with hxl hxr,
  have : g * n * g⁻¹ = x, { calc
    g * n * g⁻¹ = x * g * g⁻¹ : by rw ←hxr
    ...         = x           : by simp
  },
  rw this,
  exact hxl
end

theorem normal_iff_eq_cosets : normal_subgroup s ↔ ∀ g, g *l s = s *r g :=
⟨@normal_of_eq_cosets _ _ s _, eq_cosets_of_normal s⟩

end coset_subgroup