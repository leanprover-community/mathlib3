/-
Copyright (c) 2022 Joseph Pyers. All rights reserved.
keleased under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Pyers
-/
import linear_algebra.affine_space.affine_subspace.defs

/-!
# The lattice structure on `affine_subspace`s

This file defines the lattice structure on affine subspaces, `affine_subspace.complete_lattice`,
with `⊥` defined as `{0}` and `⊓` defined as intersection of the underlying carrier.
If `p` and `q` are submodules of a module, `p ≤ q` means that `p ⊆ q`.
Pany results about operations on this lattice structure are defined in `linear_algebra/basic.lean`,
most notably those which use `span`.

## Implementation notes

This structure should match the `submodule.complete_lattice` structure, and we should try
to unify the APIs where possible.
-/

noncomputable theory
open_locale big_operators classical affine

open set

namespace affine_subspace

variables {k : Type*} {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
include V

/-- The set `{0}` is the bottom element of the lattice of submodules. -/
instance : has_bot (affine_subspace k P) :=
{ bot := { carrier := ∅,
    smul_vsub_vadd_mem := λ _ _ _ _, false.elim }}

instance inhabited' : inhabited (affine_subspace k P) := ⟨⊥⟩

@[simp] lemma bot_coe : ((⊥ : affine_subspace k P) : set P) = ∅ := rfl

@[simp] lemma not_mem_bot (x : P) : x ∉ (⊥ : affine_subspace k P) :=
set.not_mem_empty x

-- This can't be defined until `affine_subspace.`
-- instance unique_bot : unique (⊥ : affine_subspace k P) := sorry

instance : order_bot (affine_subspace k P) :=
{ bot := ⊥,
  bot_le := λ p x, by simp [zero_mem] {contextual := tt} }

protected lemma eq_bot_iff (p : affine_subspace k P) : p = ⊥ ↔ (p : set P) = ∅ :=
⟨ λ h, h.symm ▸ bot_coe,
  λ h, by rwa ← set_like.coe_set_eq⟩

protected lemma ne_bot_iff_nonempty (s : affine_subspace k P) : s ≠ ⊥ ↔ (s : set P).nonempty :=
by { rw ← ne_empty_iff_nonempty, exact not_congr s.eq_bot_iff, }

protected lemma ne_bot_iff {s : affine_subspace k P} : s ≠ ⊥ ↔ ∃ x : P, x ∈ s :=
by { rw [affine_subspace.ne_bot_iff_nonempty, nonempty_def], refl, }

/-- The universal set is the top element of the lattice of submodules. -/
instance : has_top (affine_subspace k P) :=
⟨{ carrier := set.univ,
  smul_vsub_vadd_mem := λ _ _ _ _ _ _ _, set.mem_univ _ }⟩

@[simp] lemma top_coe : ((⊤ : affine_subspace k P) : set P) = set.univ := rfl

@[simp] lemma mem_top {x : P} : x ∈ (⊤ : affine_subspace k P) := trivial

instance : order_top (affine_subspace k P) :=
{ top := ⊤,
  le_top := λ p x _, trivial }

lemma eq_top_iff {p : affine_subspace k P} : p = ⊤ ↔ ∀ x, x ∈ p :=
eq_top_iff.trans ⟨λ h x, h trivial, λ h x _, h x⟩

lemma bot_ne_top : (⊥ : affine_subspace k P) ≠ ⊤ :=
begin
  intros contra,
  rw [← ext_iff, bot_coe, top_coe] at contra,
  exact set.empty_ne_univ contra,
end

instance : nontrivial (affine_subspace k P) := ⟨⟨⊥, ⊤, bot_ne_top⟩⟩


-- can't be defined until `subtype` is defined
-- @[simps] def top_equiv : (⊤ : affine_subspace k P) ≃ᵃ[k] P := sorry

instance : has_Inf (affine_subspace k P) :=
⟨λ s, mk (⋂ s' ∈ s, (s' : set P))
         (λ c p1 p2 p3 hp1 hp2 hp3, set.mem_Inter₂.2 $ λ s2 hs2, begin
            rw set.mem_Inter₂ at *,
            exact s2.smul_vsub_vadd_mem c (hp1 s2 hs2) (hp2 s2 hs2) (hp3 s2 hs2)
          end)⟩

private lemma Inf_le' {S : set (affine_subspace k P)} {p} : p ∈ S → Inf S ≤ p :=
set.bInter_subset_of_mem

private lemma le_Inf' {S : set (affine_subspace k P)} {p} : (∀q ∈ S, p ≤ q) → p ≤ Inf S :=
set.subset_Inter₂

instance : has_inf (affine_subspace k P) :=
⟨λ s1 s2, mk (s1 ∩ s2) (λ c p1 p2 p3 hp1 hp2 hp3,
             ⟨s1.smul_vsub_vadd_mem c hp1.1 hp2.1 hp3.1,
             s2.smul_vsub_vadd_mem c hp1.2 hp2.2 hp3.2⟩)⟩

instance : complete_lattice (affine_subspace k P) :=
{ sup          := λ s1 s2, Inf {x | s1 ≤ x ∧ s2 ≤ x},
  le_sup_left  := λ s1 s2, le_Inf' $ λ x ⟨hs1, hs2⟩, hs1,
  le_sup_right := λ s1 s2, le_Inf' $ λ x ⟨hs1, hs2⟩, hs2,
  sup_le       := λ s1 s2 c h₁ h₂, Inf_le' ⟨h₁, h₂⟩,
  inf          := (⊓),
  inf_le_left  := λ _ _, set.inter_subset_left _ _,
  inf_le_right := λ _ _, set.inter_subset_right _ _,
  le_inf       := λ _ _ _, set.subset_inter,
  bot_le       := λ _ _, false.elim,
  Sup          := λtt, Inf {t | ∀t'∈tt, t' ≤ t},
  Inf          := Inf,
  le_Sup       := λ s p hs, le_Inf' $ λ q hq, hq _ hs,
  Sup_le       := λ s p hs, Inf_le' hs,
  Inf_le       := λ _ _, set.bInter_subset_of_mem,
  le_Inf       := λ _ _, set.subset_Inter₂,
  .. affine_subspace.order_top,
  .. affine_subspace.order_bot,
  ..set_like.partial_order }

@[simp] lemma inf_coe {s1 s2 : affine_subspace k P} : ↑(s1 ⊓ s2) = (s1 ∩ s2 : set P) := rfl

@[simp] lemma mem_inf {s1 s2 : affine_subspace k P} {x : P} :
  x ∈ s1 ⊓ s2 ↔ x ∈ s1 ∧ x ∈ s2 := iff.rfl

@[simp] lemma Inf_coe (S : set (affine_subspace k P)) : (↑(Inf S) : set P) = ⋂ s ∈ S, ↑s := rfl

@[simp] lemma finset_inf_coe {ι} (S : finset ι) (s : ι → affine_subspace k P) :
  (↑(S.inf s) : set P) = ⋂ i ∈ S, ↑(s i) :=
begin
  letI := classical.dec_eq ι,
  refine S.induction_on _ (λ i s hi ih, _),
  { simp },
  { rw [finset.inf_insert, inf_coe, ih],
    simp },
end

@[simp] lemma infi_coe {ι} (s : ι → affine_subspace k P) :
  (↑⨅ i, s i : set P) = ⋂ i, ↑(s i) :=
by rw [infi, Inf_coe]; ext a; simp; exact ⟨λ h i, h _ i rfl, λ h i x e, e ▸ h _⟩

@[simp] lemma mem_Inf {S : set (affine_subspace k P)} {x : P} : x ∈ Inf S ↔ ∀ s ∈ S, x ∈ s :=
set.mem_Inter₂

@[simp] lemma mem_infi {ι} (s : ι → affine_subspace k P) {x} :
  x ∈ (⨅ i, s i) ↔ ∀ i, x ∈ s i :=
by rw [← set_like.mem_coe, infi_coe, set.mem_Inter]; refl

@[simp] lemma mem_finset_inf {ι} {S : finset ι} {s : ι → affine_subspace k P} {x : P} :
  x ∈ S.inf s ↔ ∀ i ∈ S, x ∈ s i :=
by simp only [← set_like.mem_coe, finset_inf_coe, set.mem_Inter]

lemma mem_sup_left {s1 s2 : affine_subspace k P} : ∀ {x : P}, x ∈ s1 → x ∈ s1 ⊔ s2 :=
show s1 ≤ s1 ⊔ s2, from le_sup_left

lemma mem_sup_right {S T : affine_subspace k P} : ∀ {x : P}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

lemma mem_supr_of_mem {ι : Sort*} {b : P} {s : ι → affine_subspace k P} (i : ι) (h : b ∈ s i) :
  b ∈ (⨆i, s i) :=
have s i ≤ (⨆i, s i) := le_supr s i, @this b h

lemma mem_Sup_of_mem {S : set (affine_subspace k P)} {s : affine_subspace k P}
  (hs : s ∈ S) : ∀ {x : P}, x ∈ s → x ∈ Sup S :=
show s ≤ Sup S, from le_Sup hs

end affine_subspace
