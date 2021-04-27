/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import group_theory.perm.support
import group_theory.perm.subgroup
import group_theory.perm.sign
import data.equiv.fintype

/-!

# Subgroup of finite permutations

## Main definitions

* `equiv.perm.finite`: the subgroup of `equiv.perm α` of `p : perm α` with `p.support.finite`.
* `equiv.perm.finite.sign`: the extension of `equiv.perm.sign` to finite permutations over a
not-necessarily finite type.

## Implementation details

To be able to use the existing `equiv.perm.sign` without having `[fintype α]`, we need to juggle
several subtypes of the form `↥↑p.support`. This is because `p : equiv.perm.finite α` is not
actually an `equiv.perm α` until coerced, which is necessary to use `equiv.perm.support`.
Additionally, since the finite-ness proof is via `set.finite`, all the construction of
`[fintype ↥↑p.support]` has to be done manually and noncomputably. To facilitate multiplication
of the permutations specialized to their respective supports, helped embeddings and equivalences
are defined, with helper auxiliary lemmas.

-/

open equiv set

variables {α : Type*}

namespace equiv.perm

protected def finite (α : Type*) : subgroup (perm α) :=
{ carrier := {p : perm α | p.support.finite},
  one_mem' := by simp,
  mul_mem' := λ p q hp hq, (hp.union hq).subset (support_mul_le p q),
  inv_mem' := by simp }

@[simp] lemma finite_support_finite (p : equiv.perm.finite α) : (support (p : perm α)).finite :=
p.prop

@[simp] lemma mem_finite_iff (p : perm α) : p ∈ perm.finite α ↔ p.support.finite := iff.rfl

@[simp] lemma finite_eq_top [fintype α] : perm.finite α = ⊤ :=
begin
  simp_rw [subgroup.eq_top_iff', mem_finite_iff],
  exact λ _, finite.of_fintype (perm.support _)
end

@[simps apply]
protected def restrict (p : perm α) : perm p.support :=
perm.subtype_perm p (by simp)

@[simp] lemma restrict_one : perm.restrict (1 : perm α) = 1 :=
by { ext, simp }

attribute [simps symm_apply] set_congr

@[simp] lemma inv_restrict (p : perm α) : p.restrict⁻¹ =
perm_congr (set_congr (support_inv _)) p⁻¹.restrict :=
begin
  rw inv_eq_iff_mul_eq_one,
  ext,
  simp
end

section embed

variables {s t : set α} (h : s ⊆ t)
include h

def embed_subset : s ↪ t :=
⟨subtype.map id (λ _ hx, h hx), subtype.map_injective _ function.injective_id⟩

@[simp] lemma embed_subset_apply (x : s) : embed_subset h x = ⟨x, h x.prop⟩ := rfl

lemma range_embed_subset : range (embed_subset h) = {x | (x : α) ∈ s} :=
by { ext ⟨⟩, simp }

@[simp] lemma inv_of_mem_range_embed_subset_apply (x) [fintype s] [decidable_eq t] :
  (embed_subset h).inv_of_mem_range x = ⟨x, by simpa [range_embed_subset h] using x.prop⟩ :=
begin
  convert function.embedding.right_inv_of_inv_of_mem_range _ _,
  { simp },
  { apply_instance },
  { apply_instance }
end

end embed

lemma restrict_embed_apply_mem_support (p : perm α) (t : set α)
  [fintype p.support] [decidable_eq t] (h : p.support ⊆ t) (x : t) (hx : (x : α) ∈ p.support) :
  p.restrict.via_embedding (embed_subset h) x = ⟨p x, h (apply_mem_support.mpr hx)⟩ :=
begin
  rw via_embedding_apply_mem_range,
  swap,
  { simpa [range_embed_subset] using hx },
  simp
end

lemma restrict_embed_apply_not_mem_support (p : perm α) (t : set α)
  [fintype p.support] [decidable_eq t] (h : p.support ⊆ t) (x : t) (hx : (x : α) ∉ p.support) :
  p.restrict.via_embedding (embed_subset h) x = ⟨p x, by simp [not_mem_support.mp hx]⟩ :=
begin
  rw via_embedding_apply_not_mem_range,
  swap,
  { simpa [range_embed_subset] using hx },
  simp [not_mem_support.mp hx]
end

@[simp] lemma restrict_embed_apply (p : perm α) (t : set α)
  [fintype p.support] [decidable_eq t] (h : p.support ⊆ t) (x : t) :
  p.restrict.via_embedding (embed_subset h) x = ⟨p x,
   or.cases_on (em ((x : α) ∈ p.support))
   (λ hx, h (apply_mem_support.mpr hx)) (λ hx, by simp [not_mem_support.mp hx])⟩ :=
begin
  by_cases hx : (x : α) ∈ p.support,
  { exact restrict_embed_apply_mem_support _ _ _ _ hx },
  { exact restrict_embed_apply_not_mem_support _ _ _ _ hx }
end

lemma restrict_mul_via_embedding [decidable_eq α]
  (p q : perm α)
  [fintype (p.support)]
  [fintype (q.support)]
  [fintype ((p * q).support)] :
  (p * q).restrict.via_embedding (embed_subset (support_mul_le _ _)) =
  (p.restrict.via_embedding (embed_subset (subset_union_left _ _))) *
      q.restrict.via_embedding (embed_subset (subset_union_right _ _)) :=
by { ext, simp }

noncomputable def finite.sign [decidable_eq α] : perm.finite α →* units ℤ :=
monoid_hom.mk'
  (λ p, by letI : fintype (support (p : perm α)) := finite.fintype p.prop; exact sign (perm.restrict (p : perm α)))
  (λ p q, begin
    dsimp,
    letI : fintype ((p : perm α)).support := finite.fintype p.prop,
    letI : fintype ((q : perm α)).support := finite.fintype q.prop,
    letI : fintype ((p : perm α).support ∪ (q : perm α).support : set α) :=
      finite.fintype (p.prop.union q.prop),
    letI : fintype ((p : perm α) * (q : perm α)).support,
      { refine finite.fintype _,
        exact set.finite.subset (p.prop.union q.prop) (support_mul_le _ _) },
    convert (via_embedding_sign
      ((p : perm α) * (q : perm α)).restrict
      (embed_subset (support_mul_le (p : perm α) (q : perm α)))).symm,
    have hp : sign (p : perm α).restrict = sign (((p : perm α).restrict).via_embedding
      (embed_subset (subset_union_left _ (q : perm α).support))) := by simp,
    have hq : sign (q : perm α).restrict = sign (((q : perm α).restrict).via_embedding
      (embed_subset (subset_union_right (p : perm α).support _))) := by simp,
    rw [hp, hq, ←sign_mul, restrict_mul_via_embedding]
  end)

end equiv.perm
