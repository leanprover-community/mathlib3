/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Some big operators for lists and finite sets.
-/
import algebra.group data.list data.list.comb algebra.group_power data.set.finite data.finset.basic
  data.list.perm
open function list

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section foldl_semigroup
variable [semigroup α]

lemma foldl_mul_assoc : ∀{l : list α} {a₁ a₂}, l.foldl (*) (a₁ * a₂) = a₁ * l.foldl (*) a₂
| [] a₁ a₂ := by simp
| (a :: l) a₁ a₂ :=
  calc (a::l).foldl (*) (a₁ * a₂) = l.foldl (*) (a₁ * (a₂ * a)) : by simp
  ... = a₁ * (a::l).foldl (*) a₂ : by rw [foldl_mul_assoc]; simp

lemma foldl_mul_eq_mul_foldr :
  ∀{l : list α} {a₁ a₂}, l.foldl (*) a₁ * a₂ = a₁ * l.foldr (*) a₂
| [] a₁ a₂ := by simp
| (a :: l) a₁ a₂ := by simp [foldl_mul_assoc]; rw [foldl_mul_eq_mul_foldr]

end foldl_semigroup

section list_prod_monoid
variable [monoid α]

protected definition list.prod (l : list α) : α := l.foldl (*) 1

@[simp] theorem prod_nil : [].prod = 1 := rfl

@[simp] theorem prod_cons {a : α} {l : list α} : (a::l).prod = a * l.prod :=
by simp [list.prod, foldl_mul_assoc.symm]

@[simp] theorem prod_append {l₁ l₂ : list α} : (l₁ ++ l₂).prod = l₁.prod * l₂.prod :=
by simp [list.prod, foldl_mul_assoc.symm]

@[simp] theorem prod_join {l : list (list α)} : l.join.prod = (l.map list.prod).prod :=
by induction l; simp [list.join, *] at *

@[simp] theorem prod_replicate {a : α} {n : ℕ} : (list.replicate n a).prod = a ^ n :=
begin
  induction n with n ih,
  { show [].prod = (1:α), refl },
  { show (a :: list.replicate n a).prod = a ^ (n+1), simp [pow_succ, ih] }
end

end list_prod_monoid

section list_prod_comm_monoid
variable [comm_monoid α]

lemma prod_eq_of_perm {l₁ l₂ : list α} (h : perm l₁ l₂) : l₁.prod = l₂.prod :=
by induction h; repeat { simp [*] }

end list_prod_comm_monoid

namespace finset
section prod_comm_monoid
variables [comm_monoid β] (s : finset α) (f : α → β)

protected definition prod : β :=
quot.lift_on s (λl, (l.val.map f).prod) $
  assume ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ (h : perm l₁ l₂), show (l₁.map f).prod = (l₂.map f).prod,
    from prod_eq_of_perm $ h.perm_map _

variables {s f} {s₁ s₂ : finset α}

@[simp] lemma prod_empty : (∅:finset α).prod f = 1 := rfl

variable [decidable_eq α]

@[simp] lemma prod_to_finset {l : list α} (h : nodup l) : (to_finset l).prod f = (l.map f).prod :=
by rw [←to_finset_eq_of_nodup h]; refl

@[simp] lemma prod_insert {a : α} : a ∉ s → (insert a s).prod f = f a * s.prod f :=
quot.induction_on s $ assume ⟨l, hl⟩ (h : a ∉ l),
  show ((l.insert a).map f).prod = f a * (l.map f).prod, by simp [h, list.insert]

@[simp] lemma prod_singleton {a : α} : ({a}:finset α).prod f = f a :=
by simp [singleton]

lemma prod_union_inter_eq :
  (s₁ ∪ s₂).prod f * (s₁ ∩ s₂).prod f = s₁.prod f * s₂.prod f :=
s₁.induction_on
  (by simp [empty_union, empty_inter])
  begin
    intros a s ha ih,
    by_cases a ∈ s₂ with h₂,
    { have h' : a ∉ s ∩ s₂, from assume ha', ha $ mem_of_mem_inter_left ha',
      have h'' : insert a s ∪ s₂ = s ∪ s₂,
        { rw [←insert_union], exact insert_eq_of_mem (mem_union_right _ h₂) },
      simp [insert_inter_of_mem, h₂, h', h'', ih, ha] },
    { have h' : a ∉ s ∪ s₂, from assume h, (mem_or_mem_of_mem_union h).elim ha h₂,
      rw [insert_inter_of_not_mem h₂, ←insert_union],
      simp [h', ih, -mul_comm, ha] }
  end

lemma prod_union (h : s₁ ∩ s₂ = ∅) : (s₁ ∪ s₂).prod f = s₁.prod f * s₂.prod f :=
by rw [←prod_union_inter_eq, h]; simp

lemma prod_mul_distrib {g : α → β} : s.prod (λx, f x * g x) = s.prod f * s.prod g :=
s.induction_on (by simp) (by simp {contextual:=tt})

lemma prod_image [decidable_eq γ] {s : finset γ} {g : γ → α} :
  (∀x∈s, ∀y∈s, g x = g y → x = y) → (s.image g).prod f = s.prod (λx, f (g x)) :=
quot.induction_on s $ assume ⟨l, hl⟩ h,
  show ((finset.to_finset_of_nodup l hl).image g).prod f = (l.map (f ∘ g)).prod,
    by rw [←map_map, image_to_finset_of_nodup hl h]; refl

end prod_comm_monoid
end finset
