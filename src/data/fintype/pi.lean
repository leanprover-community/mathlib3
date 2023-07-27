/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.basic
import data.finset.pi

/-!
# fintype instances for pi types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}

open finset

namespace fintype

variables [decidable_eq α] [fintype α] {δ : α → Type*}

/-- Given for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `fintype.pi_finset t` of all functions taking values in `t a` for all `a`. This is the
analogue of `finset.pi` where the base finset is `univ` (but formally they are not the same, as
there is an additional condition `i ∈ finset.univ` in the `finset.pi` definition). -/
def pi_finset (t : Π a, finset (δ a)) : finset (Π a, δ a) :=
(finset.univ.pi t).map ⟨λ f a, f a (mem_univ a), λ _ _, by simp [function.funext_iff]⟩

@[simp] lemma mem_pi_finset {t : Π a, finset (δ a)} {f : Π a, δ a} :
  f ∈ pi_finset t ↔ ∀ a, f a ∈ t a :=
begin
  split,
  { simp only [pi_finset, mem_map, and_imp, forall_prop_of_true, exists_prop, mem_univ,
               exists_imp_distrib, mem_pi],
    rintro g hg hgf a,
    rw ← hgf,
    exact hg a },
  { simp only [pi_finset, mem_map, forall_prop_of_true, exists_prop, mem_univ, mem_pi],
    exact λ hf, ⟨λ a ha, f a, hf, rfl⟩ }
end

@[simp] lemma coe_pi_finset (t : Π a, finset (δ a)) :
  (pi_finset t : set (Π a, δ a)) = set.pi set.univ (λ a, t a) :=
set.ext $ λ x, by { rw set.mem_univ_pi, exact fintype.mem_pi_finset }

lemma pi_finset_subset (t₁ t₂ : Π a, finset (δ a)) (h : ∀ a, t₁ a ⊆ t₂ a) :
  pi_finset t₁ ⊆ pi_finset t₂ :=
λ g hg, mem_pi_finset.2 $ λ a, h a $ mem_pi_finset.1 hg a

@[simp] lemma pi_finset_empty [nonempty α] : pi_finset (λ _, ∅ : Π i, finset (δ i)) = ∅ :=
eq_empty_of_forall_not_mem $ λ _, by simp

@[simp] lemma pi_finset_singleton (f : Π i, δ i) :
  pi_finset (λ i, {f i} : Π i, finset (δ i)) = {f} :=
ext $ λ _, by simp only [function.funext_iff, fintype.mem_pi_finset, mem_singleton]

lemma pi_finset_subsingleton {f : Π i, finset (δ i)}
  (hf : ∀ i, (f i : set (δ i)).subsingleton) :
  (fintype.pi_finset f : set (Π i, δ i)).subsingleton :=
λ a ha b hb, funext $ λ i, hf _ (mem_pi_finset.1 ha _) (mem_pi_finset.1 hb _)

lemma pi_finset_disjoint_of_disjoint
  (t₁ t₂ : Π a, finset (δ a)) {a : α} (h : disjoint (t₁ a) (t₂ a)) :
  disjoint (pi_finset t₁) (pi_finset t₂) :=
disjoint_iff_ne.2 $ λ f₁ hf₁ f₂ hf₂ eq₁₂,
disjoint_iff_ne.1 h (f₁ a) (mem_pi_finset.1 hf₁ a) (f₂ a) (mem_pi_finset.1 hf₂ a) (congr_fun eq₁₂ a)

end fintype

/-! ### pi -/

/-- A dependent product of fintypes, indexed by a fintype, is a fintype. -/
instance pi.fintype {α : Type*} {β : α → Type*}
  [decidable_eq α] [fintype α] [∀ a, fintype (β a)] : fintype (Π a, β a) :=
⟨fintype.pi_finset (λ _, univ), by simp⟩

@[simp] lemma fintype.pi_finset_univ {α : Type*} {β : α → Type*}
  [decidable_eq α] [fintype α] [∀ a, fintype (β a)] :
  fintype.pi_finset (λ a : α, (finset.univ : finset (β a))) = (finset.univ : finset (Π a, β a)) :=
rfl


instance function.embedding.fintype {α β} [fintype α] [fintype β] [decidable_eq α]
  [decidable_eq β] : fintype (α ↪ β) :=
fintype.of_equiv _ (equiv.subtype_injective_equiv_embedding α β)

@[simp] lemma finset.univ_pi_univ {α : Type*} {β : α → Type*}
  [decidable_eq α] [fintype α] [∀ a, fintype (β a)] :
  finset.univ.pi (λ a : α, (finset.univ : finset (β a))) = finset.univ :=
by { ext, simp }
