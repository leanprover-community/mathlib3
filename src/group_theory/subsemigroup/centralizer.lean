/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Jireh Loreaux
-/
import group_theory.subsemigroup.center

/-!
# Centralizers of magmas and semigroups

## Main definitions

* `set.centralizer`: the centralizer of a subset of a magma
* `subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `set.add_centralizer`: the centralizer of a subset of an additive magma
* `add_subsemigroup.centralizer`: the centralizer of a subset of an additive semigroup

We provide `monoid.centralizer`, `add_monoid.centralizer`, `subgroup.centralizer`, and
`add_subgroup.centralizer` in other files.
-/

variables {M : Type*} {S T : set M}

namespace set

variables (S)

/-- The centralizer of a subset of a magma. -/
@[to_additive add_centralizer /-" The centralizer of a subset of an additive magma. "-/]
def centralizer [has_mul M] : set M := {c | ∀ m ∈ S, m * c = c * m}

variables {S}

@[to_additive mem_add_centralizer]
lemma mem_centralizer_iff [has_mul M] {c : M} : c ∈ centralizer S ↔ ∀ m ∈ S, m * c = c * m :=
iff.rfl

@[to_additive decidable_mem_add_centralizer]
instance decidable_mem_centralizer [has_mul M] [decidable_eq M] [fintype M]
  [decidable_pred (∈ S)] : decidable_pred (∈ centralizer S) :=
λ _, decidable_of_iff' _ (mem_centralizer_iff)

variables (S)

@[simp, to_additive zero_mem_add_centralizer]
lemma one_mem_centralizer [mul_one_class M] : (1 : M) ∈ centralizer S :=
by simp [mem_centralizer_iff]

@[simp]
lemma zero_mem_centralizer [mul_zero_class M] : (0 : M) ∈ centralizer S :=
by simp [mem_centralizer_iff]

variables {S} {a b : M}

@[simp, to_additive add_mem_add_centralizer]
lemma mul_mem_centralizer [semigroup M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
  a * b ∈ centralizer S :=
λ g hg, by rw [mul_assoc, ←hb g hg, ← mul_assoc, ha g hg, mul_assoc]

@[simp, to_additive neg_mem_add_centralizer]
lemma inv_mem_centralizer [group M] (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S :=
λ g hg, by rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]

@[simp]
lemma add_mem_centralizer [distrib M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
  a + b ∈ centralizer S :=
λ c hc, by rw [add_mul, mul_add, ha c hc, hb c hc]

@[simp]
lemma neg_mem_centralizer [has_mul M] [has_distrib_neg M] (ha : a ∈ centralizer S) :
  -a ∈ centralizer S :=
λ c hc, by rw [mul_neg, ha c hc, neg_mul]

@[simp]
lemma inv_mem_centralizer₀ [group_with_zero M] (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S :=
(eq_or_ne a 0).elim (λ h, by { rw [h, inv_zero], exact zero_mem_centralizer S })
  (λ ha0 c hc, by rw [mul_inv_eq_iff_eq_mul₀ ha0, mul_assoc, eq_inv_mul_iff_mul_eq₀ ha0, ha c hc])

@[simp, to_additive sub_mem_add_centralizer]
lemma div_mem_centralizer [group M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
  a / b ∈ centralizer S :=
begin
  rw [div_eq_mul_inv],
  exact mul_mem_centralizer ha (inv_mem_centralizer hb),
end

@[simp]
lemma div_mem_centralizer₀ [group_with_zero M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
  a / b ∈ centralizer S :=
begin
  rw div_eq_mul_inv,
  exact mul_mem_centralizer ha (inv_mem_centralizer₀ hb),
end

@[to_additive add_centralizer_subset]
lemma centralizer_subset [has_mul M] (h : S ⊆ T) : centralizer T ⊆ centralizer S :=
λ t ht s hs, ht s (h hs)

variables (M)

@[simp, to_additive add_centralizer_univ]
lemma centralizer_univ [has_mul M] : centralizer univ = center M :=
subset.antisymm (λ a ha b, ha b (set.mem_univ b)) (λ a ha b hb, ha b)

variables {M} (S)

@[simp, to_additive add_centralizer_eq_univ]
lemma centralizer_eq_univ [comm_semigroup M] : centralizer S = univ :=
subset.antisymm (subset_univ _) $ λ x hx y hy, mul_comm y x

end set

namespace subsemigroup
section
variables {M} [semigroup M] (S)

/-- The centralizer of a subset of a semigroup `M`. -/
@[to_additive "The centralizer of a subset of an additive semigroup."]
def centralizer : subsemigroup M :=
{ carrier := S.centralizer,
  mul_mem' := λ a b, set.mul_mem_centralizer }

@[simp, norm_cast, to_additive] lemma coe_centralizer : ↑(centralizer S) = S.centralizer := rfl

variables {S}

@[to_additive] lemma mem_centralizer_iff {z : M} : z ∈ centralizer S ↔ ∀ g ∈ S, g * z = z * g :=
iff.rfl

@[to_additive] instance decidable_mem_centralizer [decidable_eq M] [fintype M]
  [decidable_pred (∈ S)] : decidable_pred (∈ centralizer S) :=
λ _, decidable_of_iff' _ mem_centralizer_iff

@[to_additive]
lemma centralizer_le (h : S ⊆ T) : centralizer T ≤ centralizer S :=
set.centralizer_subset h

variables (M)

@[simp, to_additive]
lemma centralizer_univ : centralizer set.univ = center M :=
set_like.ext' (set.centralizer_univ M)

end

end subsemigroup
