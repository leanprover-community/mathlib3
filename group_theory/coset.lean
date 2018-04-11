/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Scott Morrison
-/

import group_theory.subgroup

open set

universe u
variable {G : Type u}

def left_coset [has_mul G] (a : G) (S : set G) : set G := image (λ x, a * x) S
def right_coset [has_mul G] (S : set G) (a : G) : set G := image (λ x, x * a) S

infix ` *l `:70 := left_coset
infix ` *r `:70 := right_coset

section coset_mul
variable [has_mul G]

lemma mem_left_coset {S : set G} {x : G} (a : G) (hxS : x ∈ S) : a * x ∈ a *l S :=
mem_image_of_mem (λ b : G, a * b) hxS

lemma mem_right_coset {S : set G} {x : G} (a : G) (hxS : x ∈ S) : x * a ∈ S *r a :=
mem_image_of_mem (λ b : G, b * a) hxS

def left_coset_equiv (S : set G) (a b : G) := a *l S = b *l S

lemma left_coset_equiv_rel (S : set G) : equivalence (left_coset_equiv S) := 
mk_equivalence (left_coset_equiv S) (λ a, rfl) (λ a b, eq.symm) (λ a b c, eq.trans)

end coset_mul

section coset_semigroup
variable [semigroup G]

lemma left_coset_assoc (S : set G) (a b : G) : a *l (b *l S) = (a * b) *l S :=
    have h : (λ x : G, a * x) ∘ (λ x : G, b * x) = (λ x : G, (a * b) * x), from funext (λ c : G, 
    calc
        ((λ x : G, a * x) ∘ (λ x : G, b * x)) c = a * (b * c)               : by simp
        ...                                     = (λ x : G, (a * b) * x) c  : by rw ← mul_assoc; simp ),
    calc
        a *l (b *l S) = image ((λ x : G, a * x) ∘ (λ x : G, b * x)) S         : by rw [left_coset, left_coset, ←image_comp]
        ...          = (a * b) *l S                                           : by rw [left_coset, h]

lemma right_coset_assoc (S : set G) (a b : G) : S *r a *r b = S *r (a * b) :=
    have h : (λ x : G, x * b) ∘ (λ x : G, x * a) = (λ x : G, x * (a * b)), from funext (λ c : G, 
    calc
        ((λ x : G, x * b) ∘ (λ x : G, x * a)) c = c * a * b                 : by simp
        ...                                     = (λ x : G, x * (a * b)) c  : by rw mul_assoc; simp),
    calc
        S *r a *r b  = image ((λ x : G, x * b) ∘ (λ x : G, x * a)) S         : by rw [right_coset, right_coset, ←image_comp]
        ...         = S *r (a * b)                                           : by rw [right_coset, h]

lemma left_coset_right_coset (S : set G) (a b : G) : a *l S *r  b = a *l (S *r b) := 
    have h : (λ x : G, x * b) ∘ (λ x : G, a * x) = (λ x : G, a * (x * b)), from funext (λ c : G, 
    calc
        ((λ x : G, x * b) ∘ (λ x : G, a * x)) c = a * c * b                 : by simp
        ...                                     = (λ x : G, a * (c * b)) c  : by rw mul_assoc; simp),
    calc
        a *l S *r b   = image ((λ x : G, x * b) ∘ (λ x : G, a * x)) S         : by rw [right_coset, left_coset, ←image_comp]
        ...         = a *l (S *r b)                                           : by rw [right_coset, left_coset, ←image_comp, h]

end coset_semigroup

section coset_subgroup
open is_submonoid
open is_subgroup
variables [group G] (S : set G) [is_subgroup S]

lemma left_coset_mem_left_coset {a : G} (ha : a ∈ S) : a *l S = S := 
begin
  simp [left_coset, image],
  simp [set_eq_def, mem_set_of_eq],
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
    have : a⁻¹ ∈ S, from inv_mem ha,
    exact mul_mem this h,
    simp }
end

lemma right_coset_mem_right_coset {a : G} (ha : a ∈ S) : S *r a = S :=
begin
  simp [right_coset, image],
  simp [set_eq_def, mem_set_of_eq],
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
    have : a⁻¹ ∈ S, from inv_mem ha,
    exact mul_mem h this,
    simp }
end

lemma one_left_coset : 1 *l S = S := left_coset_mem_left_coset S (one_mem S)

lemma one_right_coset : S *r 1 = S := right_coset_mem_right_coset S (one_mem S)

lemma mem_own_left_coset (a : G) : a ∈ a *l S := 
by conv in a {rw ←mul_one a}; exact (mem_left_coset a (one_mem S))

lemma mem_own_right_coset (a : G) : a ∈ S *r a :=
by conv in a {rw ←one_mul a}; exact (mem_right_coset a (one_mem S))

lemma mem_left_coset_left_coset {a : G} (ha : a *l S = S) : a ∈ S :=
by rw [←ha]; exact mem_own_left_coset S a 

lemma mem_right_coset_right_coset {a : G} (ha : S *r a = S) : a ∈ S :=
by rw [←ha]; exact mem_own_right_coset S a

lemma mem_mem_left_coset {a x : G} (hx : x ∈ S) (hax : a * x ∈ S) : a ∈ S :=
begin 
  apply mem_left_coset_left_coset S,
  conv in S { rw ←left_coset_mem_left_coset S hx },
  rw [left_coset_assoc, left_coset_mem_left_coset S hax]
end

theorem normal_of_eq_cosets [normal_subgroup S] : ∀ g, g *l S = S *r g :=
begin
  intros g,
  apply eq_of_subset_of_subset,
  all_goals { simp [left_coset, right_coset, image], intros a n ha hn },
  existsi g * n * g⁻¹, tactic.swap, existsi g⁻¹ * n * (g⁻¹)⁻¹,
  all_goals {split, apply normal_subgroup.normal, assumption },
  { rw inv_inv g, rw [←mul_assoc, ←mul_assoc], simp, assumption },
  { simp, assumption }
end

theorem eq_cosets_of_normal (h : ∀ g, g *l S = S *r g) : normal_subgroup S:=
begin
  split,
  intros n hn g,
  have hl : g * n ∈ g *l S, from mem_left_coset g hn,
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

theorem normal_iff_eq_cosets : normal_subgroup S ↔ ∀ g, g *l S = S *r g :=
⟨@normal_of_eq_cosets _ _ S _, eq_cosets_of_normal S⟩

end coset_subgroup