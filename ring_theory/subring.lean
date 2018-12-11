/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import group_theory.subgroup
import data.polynomial
import algebra.ring

universes u v

open group

variables {R : Type u} [ring R]

/-- `S` is a subring: a set containing 1 and closed under multiplication, addition and and additive inverse. -/
class is_subring (S : set R) extends is_add_subgroup S, is_submonoid S : Prop.

instance subset.ring {S : set R} [is_subring S] : ring S :=
by subtype_instance

instance subtype.ring {S : set R} [is_subring S] : ring (subtype S) := subset.ring

namespace is_ring_hom

instance {S : set R} [is_subring S] : is_ring_hom (@subtype.val R S) :=
by refine {..} ; intros ; refl

end is_ring_hom

variables {cR : Type u} [comm_ring cR]

instance subset.comm_ring {S : set cR} [is_subring S] : comm_ring S :=
by subtype_instance

instance subtype.comm_ring {S : set cR} [is_subring S] : comm_ring (subtype S) := subset.comm_ring

instance subring.domain {D : Type*} [integral_domain D] (S : set D) [is_subring S] : integral_domain S :=
by subtype_instance

namespace ring

def closure (s : set R) := add_group.closure (monoid.closure s)

variable {s : set R}

local attribute [reducible] closure

theorem exists_list_of_mem_closure {a : R} (h : a ∈ closure s) :
  (∃ L : list (list R), (∀ l ∈ L, ∀ x ∈ l, x ∈ s ∨ -x ∈ s ∨ x = (-1:R)) ∧ (L.map list.prod).sum = a) :=
add_group.in_closure.rec_on h
  (λ x hx, match x, monoid.exists_list_of_mem_closure hx with
    | _, ⟨L, h1, rfl⟩ := ⟨[L], list.forall_mem_singleton.2 (λ r hr, or.inl (h1 r hr)), zero_add _⟩
    end)
  ⟨[], list.forall_mem_nil _, rfl⟩
  (λ b _ ih, match b, ih with
    | _, ⟨L1, h1, rfl⟩ := ⟨L1.map (list.cons (-1)),
      λ L2 h2, match L2, list.mem_map.1 h2 with
        | _, ⟨L3, h3, rfl⟩ := list.forall_mem_cons.2 ⟨or.inr $ or.inr rfl, h1 L3 h3⟩
        end,
      by simp only [list.map_map, (∘), list.prod_cons, neg_one_mul];
      exact list.rec_on L1 neg_zero.symm (λ hd tl ih,
        by rw [list.map_cons, list.sum_cons, ih, list.map_cons, list.sum_cons, neg_add])⟩
    end)
  (λ r1 r2 hr1 hr2 ih1 ih2, match r1, r2, ih1, ih2 with
    | _, _, ⟨L1, h1, rfl⟩, ⟨L2, h2, rfl⟩ := ⟨L1 ++ L2, list.forall_mem_append.2 ⟨h1, h2⟩,
      by rw [list.map_append, list.sum_append]⟩
    end)

instance : is_subring (closure s) :=
{ one_mem := add_group.mem_closure (is_submonoid.one_mem _),
  mul_mem := λ a b ha hb, add_group.in_closure.rec_on hb
    (λ b hb, add_group.in_closure.rec_on ha
      (λ a ha, add_group.subset_closure (is_submonoid.mul_mem ha hb))
      ((zero_mul b).symm ▸ is_add_submonoid.zero_mem _)
      (λ a ha hab, (neg_mul_eq_neg_mul a b) ▸ is_add_subgroup.neg_mem hab)
      (λ a c ha hc hab hcb, (add_mul a c b).symm ▸ is_add_submonoid.add_mem hab hcb))
    ((mul_zero a).symm ▸ is_add_submonoid.zero_mem _)
    (λ b hb hab, (neg_mul_eq_mul_neg a b) ▸ is_add_subgroup.neg_mem hab)
    (λ b c hb hc hab hac, (mul_add a b c).symm ▸ is_add_submonoid.add_mem hab hac),
  .. add_group.closure.is_add_subgroup _ }

theorem mem_closure {a : R} : a ∈ s → a ∈ closure s :=
add_group.mem_closure ∘ @monoid.subset_closure _ _ _ _

theorem subset_closure : s ⊆ closure s :=
λ _, mem_closure

theorem closure_subset {t : set R} [is_subring t] : s ⊆ t → closure s ⊆ t :=
add_group.closure_subset ∘ monoid.closure_subset

theorem closure_subset_iff (s t : set R) [is_subring t] : closure s ⊆ t ↔ s ⊆ t :=
(add_group.closure_subset_iff _ t).trans
  ⟨set.subset.trans monoid.subset_closure, monoid.closure_subset⟩

end ring
