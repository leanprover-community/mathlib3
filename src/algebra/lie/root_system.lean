/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import linear_algebra.dual

open function (injective)
open equiv (perm)
open linear_map

namespace sum -- move this

variables {α β : Type*} [has_neg α] [has_neg β]

instance : has_neg (α ⊕ β) :=
⟨sum.map has_neg.neg has_neg.neg⟩

@[simp] lemma inl_neg {a : α} : (inl (-a) : α ⊕ β) = -inl a := rfl

@[simp] lemma inr_neg {b : β} : (inr (-b) : α ⊕ β) = -inr b := rfl

end sum

section

class root_system (K V R : Type*)
  [field K] [char_zero K] [add_comm_group V] [vector_space K V] [fintype R] [has_neg R] :=
(root' : R → V)
(coroot' : R → module.dual K V)
(reflexion' : R → V ≃ₗ[K] V)
(root_reflexion' : R → perm R)
(cartan_matrix' : matrix R R ℤ)
(root_injective' : injective root')
(root_ne_zero' : ∀ α, root' α ≠ 0)
(span_range_root' : submodule.span K (set.range root') = ⊤)
(coroot_root_self' : ∀ α, coroot' α (root' α) = 2)
(coroot_root' : ∀ α β, coroot' α (root' β) = cartan_matrix' α β)
(eq_reflexion' : ∀ α,
                 linear_map.id - (to_span_singleton K V (root' α)).comp (coroot' α) = reflexion' α)
(root_root_reflexion' : ∀ α β, root' (root_reflexion' α β) = reflexion' α (root' β))
(root_reflexion_self' : ∀ α, root_reflexion' α α = - α)

variables (K V V₁ V₂ R R₁ R₂ : Type*)
variables [field K] [char_zero K]
variables [add_comm_group V] [add_comm_group V₁] [add_comm_group V₂]
variables [vector_space K V] [vector_space K V₁] [vector_space K V₂]
variables [fintype R] [fintype R₁] [fintype R₂] [has_neg R] [has_neg R₁] [has_neg R₂]
variables [root_system K V R] [root_system K V₁ R₁] [root_system K V₂ R₂]

namespace root_system

variables {R}

def root (α : R) : V := root' K α

variables (R)

lemma root_injective : injective (root K V : R → V) := root_injective'

lemma span_range_root : submodule.span K (set.range $ (root K V : R → V)) = ⊤ := span_range_root'

def cartan_matrix : matrix R R ℤ := cartan_matrix' K V

variables {R}

def coroot (α : R) : module.dual K V := coroot' α

def reflexion (α : R) : V ≃ₗ[K] V := reflexion' α

def root_reflexion (α : R) : perm R := root_reflexion' K V α

lemma root_ne_zero (α : R) : root K V α ≠ 0 := root_ne_zero' α

@[simp]
lemma coroot_root_self (α : R) : coroot K V α (root K V α) = 2 := coroot_root_self' α

lemma coroot_root (α β : R) : coroot K V α (root K V β) = cartan_matrix K V R α β := coroot_root' α β

lemma eq_reflexion (α : R) :
  linear_map.id - (to_span_singleton K V (root K V α)).comp (coroot K V α) = reflexion K V α :=
eq_reflexion' α

lemma root_root_reflexion (α β : R) :
  root K V (root_reflexion K V α β) = reflexion K V α (root K V β) :=
root_root_reflexion' α β

@[simp]
lemma root_reflexion_self (α : R) : root_reflexion K V α α = -α := root_reflexion_self' α

lemma coroot_ne_zero (α : R) : coroot K V α ≠ 0 :=
begin
  intro h,
  apply @two_ne_zero' K,
  rw [← coroot_root_self K V α, h, linear_map.zero_apply]
end

lemma reflexion_apply (α : R) (x : V) :
  reflexion K V α x = x - (coroot K V α x) • root K V α :=
begin
  rw [← linear_equiv.coe_coe, ← eq_reflexion],
  simp only [comp_apply, id_coe, sub_apply, id.def, sub_right_inj,
    to_span_singleton, id_coe, id.def, smul_right_apply],
end

variables {V} (R)

lemma mem_span_range_root (x : V) : x ∈ submodule.span K (set.range (root K V : R → V)) :=
by simp only [span_range_root]

@[simp]
lemma reflexion_root_self (α : R) :
  reflexion K V α (root K V α) = -root K V α :=
by rw [reflexion_apply, coroot_root_self, two_smul, sub_add_eq_sub_sub, sub_self, zero_sub]

@[simp]
lemma root_neg (α : R) : root K V (-α) = -root K V α :=
by rw [← root_reflexion_self K V α, root_root_reflexion, reflexion_root_self]

instance : root_system K (V₁ × V₂) (R₁ ⊕ R₂) :=
{ root' := sum.elim (λ α, (root K V₁ α, 0)) (λ β, (0, root K V₂ β)),
  coroot' := sum.elim (λ α, (coroot K V₁ α).comp (linear_map.fst K V₁ V₂))
                      (λ β, (coroot K V₂ β).comp (linear_map.snd K V₁ V₂)),
  reflexion' := sum.elim (λ α, (reflexion K V₁ α).prod (linear_equiv.refl K V₂))
                         (λ β, (linear_equiv.refl K V₁).prod (reflexion K V₂ β)),
  root_reflexion' := sum.elim (λ α, equiv.sum_congr (root_reflexion K V₁ α) 1)
                              (λ β, equiv.sum_congr 1 (root_reflexion K V₂ β)),
  cartan_matrix' := matrix.from_blocks (cartan_matrix K V₁ R₁) 0 0 (cartan_matrix K V₂ R₂),
  root_injective' :=
  begin
    rintro (α₁ | β₁) (α₂ | β₂);
    simp only [root_injective K V₁ R₁, root_injective K V₂ R₂, root_ne_zero,
      imp_self, function.injective.eq_iff, and_true, true_and, sum.elim_inl, sum.elim_inr,
      prod.mk.inj_iff, eq_self_iff_true, forall_prop_of_false, not_false_iff, false_and, and_false]
  end,
  root_ne_zero' :=
  begin
    rintro (α | β);
    simp only [root_ne_zero, sum.elim_inl, sum.elim_inr, prod.mk_eq_zero, ne.def, not_false_iff,
      false_and, and_false]
  end,
  span_range_root' :=
  begin
    simp only [submodule.eq_top_iff', prod.forall, set.sum.elim_range],
    intros x y,
    have aux : (x, y) = (x, 0) + (0, y),
    { simp only [prod.mk_add_mk, add_zero, zero_add] },
    rw aux,
    apply submodule.add_mem _ _ _,
    { apply submodule.span_mono (set.subset_union_left _ _),
      have hx := mem_span_range_root K R₁ x,
      have := @submodule.mem_map_of_mem K V₁ (V₁ × V₂) _ _ _ _ _ (linear_map.id.prod 0) _ _ hx,
      rw submodule.map_span at this,
      simp only [prod_apply, id_coe, id.def, zero_apply] at this,
      convert this,
      ext v,
      simp only [prod_apply, id_coe, set.mem_range, set.mem_image, id.def,
        exists_exists_eq_and, zero_apply] },
    { apply submodule.span_mono (set.subset_union_right _ _),
      have hy := mem_span_range_root K R₂ y,
      have := @submodule.mem_map_of_mem K V₂ (V₁ × V₂) _ _ _ _ _
        (linear_map.prod 0 linear_map.id) _ _ hy,
      rw submodule.map_span at this,
      simp only [prod_apply, id_coe, id.def, zero_apply] at this,
      convert this,
      ext v,
      simp only [prod_apply, id_coe, set.mem_range, set.mem_image, id.def,
        exists_exists_eq_and, zero_apply] }
  end,
  coroot_root_self' :=
  begin
    rintro (α | β);
    simp only [coroot_root_self, comp_apply, sum.elim_inl, sum.elim_inr, fst_apply, snd_apply]
  end,
  coroot_root' :=
  begin
    rintro (α₁ | β₁) (α₂ | β₂);
    simp only [coroot_root, comp_apply, sum.elim_inl, sum.elim_inr, fst_apply, snd_apply,
      matrix.from_blocks_apply₁₁, matrix.from_blocks_apply₁₂,
      matrix.from_blocks_apply₂₁, matrix.from_blocks_apply₂₂,
      int.cast_zero, matrix.zero_apply, map_zero]
  end,
  eq_reflexion' :=
  begin
    rintro (α | β); ext ⟨x, y⟩;
    simp only [linear_equiv.coe_prod, comp_apply, id.def, id_coe, linear_equiv.coe_coe,
      prod_map_apply, sub_apply, sum.elim_inl, sum.elim_inr, smul_zero, sub_zero,
      fst_apply, snd_apply, prod.fst_sub, prod.snd_sub, linear_equiv.refl_apply,
      to_span_singleton, reflexion_apply, prod.smul_mk, smul_right_apply]
  end,
  root_root_reflexion' :=
  begin
    rintro (α₁ | β₁) (α₂ | β₂);
    simp only [root_root_reflexion, linear_equiv.map_zero, and_true, true_and, equiv.sum_congr_apply,
      sum.map_inl, sum.map_inr, sum.elim_inl, sum.elim_inr, linear_equiv.prod_apply,
      prod.mk.inj_iff, eq_self_iff_true, linear_equiv.refl_apply, equiv.perm.one_apply]
  end,
  root_reflexion_self' :=
  begin
    rintro (α | β);
    simp only [root_reflexion_self, sum.map_inl, sum.map_inr, sum.elim_inl, sum.elim_inr,
      sum.inl_neg, sum.inr_neg, equiv.sum_congr_apply]
  end }

end root_system

end
