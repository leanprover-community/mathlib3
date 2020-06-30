/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import algebra.pi_instances
import data.set.disjointed
import data.support

/-!
# Indicator function

`indicator (s : set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `0` otherwise.

## Implementation note

In mathematics, an indicator function or a characteristic function is a function used to indicate
membership of an element in a set `s`, having the value `1` for all elements of `s` and the value `0`
otherwise. But since it is usually used to restrict a function to a certain set `s`, we let the
indicator function take the value `f x` for some function `f`, instead of `1`. If the usual indicator
function is needed, just set `f` to be the constant function `λx, 1`.

## Tags
indicator, characteristic
-/

noncomputable theory
open_locale classical big_operators

namespace set

universes u v
variables {α : Type u} {β : Type v}

section has_zero
variables [has_zero β] {s t : set α} {f g : α → β} {a : α}

/-- `indicator s f a` is `f a` if `a ∈ s`, `0` otherwise.  -/
@[reducible]
def indicator (s : set α) (f : α → β) : α → β := λ x, if x ∈ s then f x else 0

lemma indicator_apply (s : set α) (f : α → β) (a : α) :
  indicator s f a = if a ∈ s then f a else 0 := rfl

@[simp] lemma indicator_of_mem (h : a ∈ s) (f : α → β) : indicator s f a = f a := if_pos h

@[simp] lemma indicator_of_not_mem (h : a ∉ s) (f : α → β) : indicator s f a = 0 := if_neg h

lemma eq_on_indicator : eq_on (indicator s f) f s := λ x hx, indicator_of_mem hx f

lemma support_indicator : function.support (s.indicator f) ⊆ s :=
λ x hx, hx.imp_symm (λ h, indicator_of_not_mem h f)

lemma indicator_congr (h : ∀ a ∈ s, f a = g a) : indicator s f = indicator s g :=
funext $ λx, by { simp only [indicator], split_ifs, { exact h _ h_1 }, refl }

@[simp] lemma indicator_univ (f : α → β) : indicator (univ : set α) f = f :=
funext $ λx, indicator_of_mem (mem_univ _) f

@[simp] lemma indicator_empty (f : α → β) : indicator (∅ : set α) f = λa, 0 :=
funext $ λx, indicator_of_not_mem (not_mem_empty _) f

variable (β)
@[simp] lemma indicator_zero (s : set α) : indicator s (λx, (0:β)) = λx, (0:β) :=
funext $ λx, by { simp only [indicator], split_ifs, refl, refl }
variable {β}

lemma indicator_indicator (s t : set α) (f : α → β) : indicator s (indicator t f) = indicator (s ∩ t) f :=
funext $ λx, by { simp only [indicator], split_ifs, repeat {simp * at * {contextual := tt}} }

lemma indicator_comp_of_zero {γ} [has_zero γ] {g : β → γ} (hg : g 0 = 0) :
  indicator s (g ∘ f) = λ a, indicator (f '' s) g (indicator s f a) :=
begin
  funext, simp only [indicator],
  split_ifs with h h',
  { refl },
  { have := mem_image_of_mem _ h, contradiction },
  { rwa eq_comm },
  refl
end

lemma indicator_preimage (s : set α) (f : α → β) (B : set β) :
  (indicator s f)⁻¹' B = s ∩ f ⁻¹' B ∪ sᶜ ∩ (λa:α, (0:β)) ⁻¹' B :=
by { rw [indicator, if_preimage] }

lemma indicator_preimage_of_not_mem (s : set α) (f : α → β) {t : set β} (ht : (0:β) ∉ t) :
  (indicator s f)⁻¹' t = s ∩ f ⁻¹' t :=
by simp [indicator_preimage, set.preimage_const_of_not_mem ht]

lemma mem_range_indicator {r : β} {s : set α} {f : α → β} :
  r ∈ range (indicator s f) ↔ (r = 0 ∧ s ≠ univ) ∨ (r ∈ f '' s) :=
by simp [indicator, ite_eq_iff, exists_or_distrib, eq_univ_iff_forall, and_comm, or_comm,
  @eq_comm _ r 0]

end has_zero

section add_monoid
variables [add_monoid β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_union_of_not_mem_inter (h : a ∉ s ∩ t) (f : α → β) :
  indicator (s ∪ t) f a = indicator s f a + indicator t f a :=
by { simp only [indicator], split_ifs, repeat {simp * at * {contextual := tt}} }

lemma indicator_union_of_disjoint (h : disjoint s t) (f : α → β) :
  indicator (s ∪ t) f = λa, indicator s f a + indicator t f a :=
funext $ λa, indicator_union_of_not_mem_inter
  (by { convert not_mem_empty a, have := disjoint.eq_bot h, assumption })
  _

lemma indicator_add (s : set α) (f g : α → β) :
  indicator s (λa, f a + g a) = λa, indicator s f a + indicator s g a :=
by { funext, simp only [indicator], split_ifs, { refl }, rw add_zero }

variables (β)
instance is_add_monoid_hom.indicator (s : set α) : is_add_monoid_hom (λf:α → β, indicator s f) :=
{ map_add := λ _ _, indicator_add _ _ _,
  map_zero := indicator_zero _ _ }

variables {β} {𝕜 : Type*} [monoid 𝕜] [distrib_mul_action 𝕜 β]

lemma indicator_smul (s : set α) (r : 𝕜) (f : α → β) :
  indicator s (λ (x : α), r • f x) = λ (x : α), r • indicator s f x :=
by { simp only [indicator], funext, split_ifs, refl, exact (smul_zero r).symm }

end add_monoid

section add_group
variables [add_group β] {s t : set α} {f g : α → β} {a : α}

variables (β)
instance is_add_group_hom.indicator (s : set α) : is_add_group_hom (λf:α → β, indicator s f) :=
{ .. is_add_monoid_hom.indicator β s }
variables {β}

lemma indicator_neg (s : set α) (f : α → β) : indicator s (λa, - f a) = λa, - indicator s f a :=
show indicator s (- f) = - indicator s f, from is_add_group_hom.map_neg _ _

lemma indicator_sub (s : set α) (f g : α → β) :
  indicator s (λa, f a - g a) = λa, indicator s f a - indicator s g a :=
show indicator s (f - g) = indicator s f - indicator s g, from is_add_group_hom.map_sub _ _ _

lemma indicator_compl (s : set α) (f : α → β) : indicator sᶜ f = λ a, f a - indicator s f a :=
begin
  funext,
  simp only [indicator],
  split_ifs with h₁ h₂,
  { rw sub_zero },
  { rw sub_self },
  { rw ← mem_compl_iff at h₂, contradiction }
end

lemma indicator_finset_sum {β} [add_comm_monoid β] {ι : Type*} (I : finset ι) (s : set α) (f : ι → α → β) :
  indicator s (∑ i in I, f i) = ∑ i in I, indicator s (f i) :=
begin
  convert (finset.sum_hom _ _).symm,
  split,
  exact indicator_zero _ _
end

lemma indicator_finset_bUnion {β} [add_comm_monoid β] {ι} (I : finset ι)
  (s : ι → set α) {f : α → β} : (∀ (i ∈ I) (j ∈ I), i ≠ j → s i ∩ s j = ∅) →
  indicator (⋃ i ∈ I, s i) f = λ a, ∑ i in I, indicator (s i) f a :=
begin
  refine finset.induction_on I _ _,
  assume h,
  { funext, simp },
  assume a I haI ih hI,
  funext,
  simp only [haI, finset.sum_insert, not_false_iff],
  rw [finset.bUnion_insert, indicator_union_of_not_mem_inter, ih _],
  { assume i hi j hj hij,
    exact hI i (finset.mem_insert_of_mem hi) j (finset.mem_insert_of_mem hj) hij },
  simp only [not_exists, exists_prop, mem_Union, mem_inter_eq, not_and],
  assume hx a' ha',
  have := hI a (finset.mem_insert_self _ _) a' (finset.mem_insert_of_mem ha') _,
  { assume h, have h := mem_inter hx h, rw this at h, exact not_mem_empty _ h },
  { assume h, rw h at haI, contradiction }
end

end add_group

section mul_zero_class
variables [mul_zero_class β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_mul (s : set α) (f g : α → β) :
  indicator s (λa, f a * g a) = λa, indicator s f a * indicator s g a :=
by { funext, simp only [indicator], split_ifs, { refl }, rw mul_zero }

end mul_zero_class

section order
variables [has_zero β] [preorder β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_nonneg' (h : a ∈ s → 0 ≤ f a) : 0 ≤ indicator s f a :=
by { rw indicator_apply, split_ifs with as, { exact h as }, refl }

lemma indicator_nonneg (h : ∀ a ∈ s, 0 ≤ f a) : ∀ a, 0 ≤ indicator s f a :=
λ a, indicator_nonneg' (h a)

lemma indicator_nonpos' (h : a ∈ s → f a ≤ 0) : indicator s f a ≤ 0 :=
by { rw indicator_apply, split_ifs with as, { exact h as }, refl }

lemma indicator_nonpos (h : ∀ a ∈ s, f a ≤ 0) : ∀ a, indicator s f a ≤ 0 :=
λ a, indicator_nonpos' (h a)

lemma indicator_le_indicator (h : f a ≤ g a) : indicator s f a ≤ indicator s g a :=
by { simp only [indicator], split_ifs with ha, { exact h }, refl }

lemma indicator_le_indicator_of_subset (h : s ⊆ t) (hf : ∀a, 0 ≤ f a) (a : α) :
  indicator s f a ≤ indicator t f a :=
begin
  simp only [indicator],
  split_ifs with h₁,
  { refl },
  { have := h h₁, contradiction },
  { exact hf a },
  { refl }
end

end order

end set
