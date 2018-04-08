import algebra.group.subgroup

open set

universe u
variable {G : Type u}

def lcoset [has_mul G] (a : G) (S : set G) : set G := image (λ x, a * x) S
def rcoset [has_mul G] (S : set G) (a : G) : set G := image (λ x, x * a) S

namespace coset_notation

infix ` *ₗ `:70 := lcoset
infix ` *ᵣ `:70 := rcoset

end coset_notation

section coset_mul
open coset_notation
variable [has_mul G]

lemma mem_lcoset {S : set G} {x : G} (a : G) (hxS : x ∈ S) : a * x ∈ a *ₗ S :=
mem_image_of_mem (λ b : G, a * b) hxS

lemma mem_rcoset {S : set G} {x : G} (a : G) (hxS : x ∈ S) : x * a ∈ S *ᵣ a :=
mem_image_of_mem (λ b : G, b * a) hxS

def lcoset_equiv (S : set G) (a b : G) := a *ₗ S = b *ₗ S

lemma lcoset_equiv_rel (S : set G) : equivalence (lcoset_equiv S) := 
mk_equivalence (lcoset_equiv S) (λ a, rfl) (λ a b, eq.symm) (λ a b c, eq.trans)

end coset_mul

section coset_semigroup
open coset_notation
variable [semigroup G]

lemma lcoset_assoc (S : set G) (a b : G) : a *ₗ (b *ₗ S) = (a * b) *ₗ S :=
    have h : (λ x : G, a * x) ∘ (λ x : G, b * x) = (λ x : G, (a * b) * x), from funext (λ c : G, 
    calc
        ((λ x : G, a * x) ∘ (λ x : G, b * x)) c = a * (b * c)               : by simp
        ...                                     = (λ x : G, (a * b) * x) c  : by rw ← mul_assoc; simp ),
    calc
        a *ₗ (b *ₗ S) = image ((λ x : G, a * x) ∘ (λ x : G, b * x)) S         : by rw [lcoset, lcoset, ←image_comp]
        ...          = (a * b) *ₗ S                                           : by rw [lcoset, h]

lemma rcoset_assoc (S : set G) (a b : G) : S *ᵣ a *ᵣ b = S *ᵣ (a * b) :=
    have h : (λ x : G, x * b) ∘ (λ x : G, x * a) = (λ x : G, x * (a * b)), from funext (λ c : G, 
    calc
        ((λ x : G, x * b) ∘ (λ x : G, x * a)) c = c * a * b                 : by simp
        ...                                     = (λ x : G, x * (a * b)) c  : by rw mul_assoc; simp),
    calc
        S *ᵣ a *ᵣ b  = image ((λ x : G, x * b) ∘ (λ x : G, x * a)) S         : by rw [rcoset, rcoset, ←image_comp]
        ...         = S *ᵣ (a * b)                                           : by rw [rcoset, h]

lemma lcoset_rcoset (S : set G) (a b : G) : a *ₗ S *ᵣ  b = a *ₗ (S *ᵣ b) := 
    have h : (λ x : G, x * b) ∘ (λ x : G, a * x) = (λ x : G, a * (x * b)), from funext (λ c : G, 
    calc
        ((λ x : G, x * b) ∘ (λ x : G, a * x)) c = a * c * b                 : by simp
        ...                                     = (λ x : G, a * (c * b)) c  : by rw mul_assoc; simp),
    calc
        a *ₗ S *ᵣ b   = image ((λ x : G, x * b) ∘ (λ x : G, a * x)) S         : by rw [rcoset, lcoset, ←image_comp]
        ...         = a *ₗ (S *ᵣ b)                                           : by rw [rcoset, lcoset, ←image_comp, h]

end coset_semigroup

section coset_subgroup
open subgroup coset_notation
variables [group G] (S : set G) [subgroup S]

lemma lcoset_mem_lcoset {a : G} (ha : a ∈ S) : a *ₗ S = S := 
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

lemma rcoset_mem_rcoset {a : G} (ha : a ∈ S) : S *ᵣ a = S :=
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

lemma one_lcoset : 1 *ₗ S = S := lcoset_mem_lcoset S (one_mem S)

lemma one_rcoset : S *ᵣ 1 = S := rcoset_mem_rcoset S (one_mem S)

lemma mem_own_lcoset (a : G) : a ∈ a *ₗ S := 
by conv in a {rw ←mul_one a}; exact (mem_lcoset a (one_mem S))

lemma mem_own_rcoset (a : G) : a ∈ S *ᵣ a :=
by conv in a {rw ←one_mul a}; exact (mem_rcoset a (one_mem S))

lemma mem_lcoset_lcoset {a : G} (ha : a *ₗ S = S) : a ∈ S :=
by rw [←ha]; exact mem_own_lcoset S a 

lemma mem_rcoset_rcoset {a : G} (ha : S *ᵣ a = S) : a ∈ S :=
by rw [←ha]; exact mem_own_rcoset S a

lemma mem_mem_lcoset {a x : G} (hx : x ∈ S) (hax : a * x ∈ S) : a ∈ S :=
begin 
  apply mem_lcoset_lcoset S,
  conv in S { rw ←lcoset_mem_lcoset S hx },
  rw [lcoset_assoc, lcoset_mem_lcoset S hax]
end

theorem normal_of_eq_cosets [normal_subgroup S] : ∀ g, g *ₗ S = S *ᵣ g :=
begin
  intros g,
  apply eq_of_subset_of_subset,
  all_goals { simp [lcoset, rcoset, image], intros a n ha hn },
  existsi g * n * g⁻¹, tactic.swap, existsi g⁻¹ * n * (g⁻¹)⁻¹,
  all_goals {split, apply normal_subgroup.normal, assumption },
  { rw inv_inv g, rw [←mul_assoc, ←mul_assoc], simp, assumption },
  { simp, assumption }
end

theorem eq_cosets_of_normal (h : ∀ g, g *ₗ S = S *ᵣ g) : normal_subgroup S:=
begin
  split,
  intros n hn g,
  have hl : g * n ∈ g *ₗ S, from mem_lcoset g hn,
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

theorem normal_iff_eq_cosets : normal_subgroup S ↔ ∀ g, g *ₗ S = S *ᵣ g :=
⟨@normal_of_eq_cosets _ _ S _, eq_cosets_of_normal S⟩

end coset_subgroup