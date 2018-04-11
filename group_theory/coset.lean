/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Scott Morrison
-/

import group_theory.subgroup_

open set

universe u
variable {G : Type u}

def lcoset [has_mul G] (a : G) (S : set G) : set G := image (λ x, a * x) S
def rcoset [has_mul G] (S : set G) (a : G) : set G := image (λ x, x * a) S

infix ` *l `:70 := lcoset
infix ` *r `:70 := rcoset

section coset_mul
variable [has_mul G]

lemma mem_lcoset {S : set G} {x : G} (a : G) (hxS : x ∈ S) : a * x ∈ a *l S :=
mem_image_of_mem (λ b : G, a * b) hxS

lemma mem_rcoset {S : set G} {x : G} (a : G) (hxS : x ∈ S) : x * a ∈ S *r a :=
mem_image_of_mem (λ b : G, b * a) hxS

def lcoset_equiv (S : set G) (a b : G) := a *l S = b *l S

lemma lcoset_equiv_rel (S : set G) : equivalence (lcoset_equiv S) := 
mk_equivalence (lcoset_equiv S) (λ a, rfl) (λ a b, eq.symm) (λ a b c, eq.trans)

end coset_mul

section coset_semigroup
variable [semigroup G]

lemma lcoset_assoc (S : set G) (a b : G) : a *l (b *l S) = (a * b) *l S :=
    have h : (λ x : G, a * x) ∘ (λ x : G, b * x) = (λ x : G, (a * b) * x), from funext (λ c : G, 
    calc
        ((λ x : G, a * x) ∘ (λ x : G, b * x)) c = a * (b * c)               : by simp
        ...                                     = (λ x : G, (a * b) * x) c  : by rw ← mul_assoc; simp ),
    calc
        a *l (b *l S) = image ((λ x : G, a * x) ∘ (λ x : G, b * x)) S         : by rw [lcoset, lcoset, ←image_comp]
        ...          = (a * b) *l S                                           : by rw [lcoset, h]

lemma rcoset_assoc (S : set G) (a b : G) : S *r a *r b = S *r (a * b) :=
    have h : (λ x : G, x * b) ∘ (λ x : G, x * a) = (λ x : G, x * (a * b)), from funext (λ c : G, 
    calc
        ((λ x : G, x * b) ∘ (λ x : G, x * a)) c = c * a * b                 : by simp
        ...                                     = (λ x : G, x * (a * b)) c  : by rw mul_assoc; simp),
    calc
        S *r a *r b  = image ((λ x : G, x * b) ∘ (λ x : G, x * a)) S         : by rw [rcoset, rcoset, ←image_comp]
        ...         = S *r (a * b)                                           : by rw [rcoset, h]

lemma lcoset_rcoset (S : set G) (a b : G) : a *l S *r  b = a *l (S *r b) := 
    have h : (λ x : G, x * b) ∘ (λ x : G, a * x) = (λ x : G, a * (x * b)), from funext (λ c : G, 
    calc
        ((λ x : G, x * b) ∘ (λ x : G, a * x)) c = a * c * b                 : by simp
        ...                                     = (λ x : G, a * (c * b)) c  : by rw mul_assoc; simp),
    calc
        a *l S *r b   = image ((λ x : G, x * b) ∘ (λ x : G, a * x)) S         : by rw [rcoset, lcoset, ←image_comp]
        ...         = a *l (S *r b)                                           : by rw [rcoset, lcoset, ←image_comp, h]

end coset_semigroup

section coset_subgroup
open subgroup
variables [group G] (S : set G) [subgroup S]

lemma lcoset_mem_lcoset {a : G} (ha : a ∈ S) : a *l S = S := 
begin
  simp [lcoset, image],
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

lemma rcoset_mem_rcoset {a : G} (ha : a ∈ S) : S *r a = S :=
begin
  simp [rcoset, image],
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

lemma one_lcoset : 1 *l S = S := lcoset_mem_lcoset S (one_mem S)

lemma one_rcoset : S *r 1 = S := rcoset_mem_rcoset S (one_mem S)

lemma mem_own_lcoset (a : G) : a ∈ a *l S := 
by conv in a {rw ←mul_one a}; exact (mem_lcoset a (one_mem S))

lemma mem_own_rcoset (a : G) : a ∈ S *r a :=
by conv in a {rw ←one_mul a}; exact (mem_rcoset a (one_mem S))

lemma mem_lcoset_lcoset {a : G} (ha : a *l S = S) : a ∈ S :=
by rw [←ha]; exact mem_own_lcoset S a 

lemma mem_rcoset_rcoset {a : G} (ha : S *r a = S) : a ∈ S :=
by rw [←ha]; exact mem_own_rcoset S a

lemma mem_mem_lcoset {a x : G} (hx : x ∈ S) (hax : a * x ∈ S) : a ∈ S :=
begin 
  apply mem_lcoset_lcoset S,
  conv in S { rw ←lcoset_mem_lcoset S hx },
  rw [lcoset_assoc, lcoset_mem_lcoset S hax]
end

theorem normal_of_eq_cosets [normal_subgroup S] : ∀ g, g *l S = S *r g :=
begin
  intros g,
  apply eq_of_subset_of_subset,
  all_goals { simp [lcoset, rcoset, image], intros a n ha hn },
  existsi g * n * g⁻¹, tactic.swap, existsi g⁻¹ * n * (g⁻¹)⁻¹,
  all_goals {split, apply normal_subgroup.normal, assumption },
  { rw inv_inv g, rw [←mul_assoc, ←mul_assoc], simp, assumption },
  { simp, assumption }
end

theorem eq_cosets_of_normal (h : ∀ g, g *l S = S *r g) : normal_subgroup S:=
begin
  split,
  intros n hn g,
  have hl : g * n ∈ g *l S, from mem_lcoset g hn,
  rw h at hl,
  simp [rcoset] at hl,
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