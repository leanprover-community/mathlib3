/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import algebra.module.submodule
import algebra.punit_instances

/-!
# The lattice structure on `submodule`s

This file defines the lattice structure on submodules, `submodule.complete_lattice`, with `⊥`
defined as `{0}` and `⊓` defined as intersection of the underlying carrier.
If `p` and `q` are submodules of a module, `p ≤ q` means that `p ⊆ q`.

Many results about operations on this lattice structure are defined in `linear_algebra/basic.lean`,
most notably those which use `span`.

## Implementation notes

This structure should match the `add_submonoid.complete_lattice` structure, and we should try
to unify the APIs where possible.

-/

variables {R S M : Type*}

section add_comm_monoid
variables [semiring R] [semiring S] [add_comm_monoid M] [module R M] [module S M]
variables [has_scalar S R] [is_scalar_tower S R M]
variables {p q : submodule R M}

namespace submodule

/-- The set `{0}` is the bottom element of the lattice of submodules. -/
instance : has_bot (submodule R M) :=
⟨{ carrier := {0}, smul_mem' := by simp { contextual := tt }, .. (⊥ : add_submonoid M)}⟩

instance inhabited' : inhabited (submodule R M) := ⟨⊥⟩

@[simp] lemma bot_coe : ((⊥ : submodule R M) : set M) = {0} := rfl
@[simp] lemma bot_to_add_submonoid : (⊥ : submodule R M).to_add_submonoid = ⊥ := rfl

section
variables (R)
@[simp] lemma restrict_scalars_bot : restrict_scalars S (⊥ : submodule R M) = ⊥ := rfl

@[simp] lemma mem_bot {x : M} : x ∈ (⊥ : submodule R M) ↔ x = 0 := set.mem_singleton_iff
end

instance unique_bot : unique (⊥ : submodule R M) :=
⟨infer_instance, λ x, subtype.ext $ (mem_bot R).1 x.mem⟩

instance : order_bot (submodule R M) :=
{ bot := ⊥,
  bot_le := λ p x, by simp {contextual := tt},
  ..set_like.partial_order }

protected lemma eq_bot_iff (p : submodule R M) : p = ⊥ ↔ ∀ x ∈ p, x = (0 : M) :=
⟨ λ h, h.symm ▸ λ x hx, (mem_bot R).mp hx,
  λ h, eq_bot_iff.mpr (λ x hx, (mem_bot R).mpr (h x hx)) ⟩

@[ext] protected lemma bot_ext (x y : (⊥ : submodule R M)) : x = y :=
begin
  rcases x with ⟨x, xm⟩, rcases y with ⟨y, ym⟩, congr,
  rw (submodule.eq_bot_iff _).mp rfl x xm,
  rw (submodule.eq_bot_iff _).mp rfl y ym,
end

protected lemma ne_bot_iff (p : submodule R M) : p ≠ ⊥ ↔ ∃ x ∈ p, x ≠ (0 : M) :=
by { haveI := classical.prop_decidable, simp_rw [ne.def, p.eq_bot_iff, not_forall] }

lemma nonzero_mem_of_bot_lt {p : submodule R M} (bot_lt : ⊥ < p) : ∃ a : p, a ≠ 0 :=
let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp bot_lt.ne' in ⟨⟨b, hb₁⟩, hb₂ ∘ (congr_arg coe)⟩

lemma exists_mem_ne_zero_of_ne_bot {p : submodule R M} (h : p ≠ ⊥) : ∃ b : M, b ∈ p ∧ b ≠ 0 :=
let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp h in ⟨b, hb₁, hb₂⟩

/-- The bottom submodule is linearly equivalent to punit as an `R`-module. -/
@[simps] def bot_equiv_punit : (⊥ : submodule R M) ≃ₗ[R] punit :=
{ to_fun := λ x, punit.star,
  inv_fun := λ x, 0,
  map_add' := by { intros, ext, },
  map_smul' := by { intros, ext, },
  left_inv := by { intro x, ext, },
  right_inv := by { intro x, ext, }, }

lemma eq_bot_of_subsingleton (p : submodule R M) [subsingleton p] : p = ⊥ :=
begin
  rw eq_bot_iff,
  intros v hv,
  exact congr_arg coe (subsingleton.elim (⟨v, hv⟩ : p) 0)
end

/-- The universal set is the top element of the lattice of submodules. -/
instance : has_top (submodule R M) :=
⟨{ carrier := set.univ, smul_mem' := λ _ _ _, trivial, .. (⊤ : add_submonoid M)}⟩

@[simp] lemma top_coe : ((⊤ : submodule R M) : set M) = set.univ := rfl

@[simp] lemma top_to_add_submonoid : (⊤ : submodule R M).to_add_submonoid = ⊤ := rfl

@[simp] lemma mem_top {x : M} : x ∈ (⊤ : submodule R M) := trivial

section
variables (R)
@[simp] lemma restrict_scalars_top : restrict_scalars S (⊤ : submodule R M) = ⊤ := rfl
end

instance : order_top (submodule R M) :=
{ top := ⊤,
  le_top := λ p x _, trivial,
  ..set_like.partial_order }

lemma eq_top_iff' {p : submodule R M} : p = ⊤ ↔ ∀ x, x ∈ p :=
eq_top_iff.trans ⟨λ h x, h trivial, λ h x _, h x⟩

/-- The top submodule is linearly equivalent to the module. -/
@[simps] def top_equiv_self : (⊤ : submodule R M) ≃ₗ[R] M :=
{ to_fun := λ x, x,
  inv_fun := λ x, ⟨x, by simp⟩,
  map_add' := by { intros, refl, },
  map_smul' := by { intros, refl, },
  left_inv := by { intro x, ext, refl, },
  right_inv := by { intro x, refl, }, }

instance : has_Inf (submodule R M) :=
⟨λ S, {
  carrier   := ⋂ s ∈ S, (s : set M),
  zero_mem' := by simp,
  add_mem'  := by simp [add_mem] {contextual := tt},
  smul_mem' := by simp [smul_mem] {contextual := tt} }⟩

private lemma Inf_le' {S : set (submodule R M)} {p} : p ∈ S → Inf S ≤ p :=
set.bInter_subset_of_mem

private lemma le_Inf' {S : set (submodule R M)} {p} : (∀q ∈ S, p ≤ q) → p ≤ Inf S :=
set.subset_bInter

instance : has_inf (submodule R M) :=
⟨λ p q, {
  carrier   := p ∩ q,
  zero_mem' := by simp,
  add_mem'  := by simp [add_mem] {contextual := tt},
  smul_mem' := by simp [smul_mem] {contextual := tt} }⟩

instance : complete_lattice (submodule R M) :=
{ sup          := λ a b, Inf {x | a ≤ x ∧ b ≤ x},
  le_sup_left  := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, ha,
  le_sup_right := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, hb,
  sup_le       := λ a b c h₁ h₂, Inf_le' ⟨h₁, h₂⟩,
  inf          := (⊓),
  le_inf       := λ a b c, set.subset_inter,
  inf_le_left  := λ a b, set.inter_subset_left _ _,
  inf_le_right := λ a b, set.inter_subset_right _ _,
  Sup          := λtt, Inf {t | ∀t'∈tt, t' ≤ t},
  le_Sup       := λ s p hs, le_Inf' $ λ q hq, hq _ hs,
  Sup_le       := λ s p hs, Inf_le' hs,
  Inf          := Inf,
  le_Inf       := λ s a, le_Inf',
  Inf_le       := λ s a, Inf_le',
  ..submodule.order_top,
  ..submodule.order_bot }

@[simp] theorem inf_coe : ↑(p ⊓ q) = (p ∩ q : set M) := rfl

@[simp] theorem mem_inf {p q : submodule R M} {x : M} :
  x ∈ p ⊓ q ↔ x ∈ p ∧ x ∈ q := iff.rfl

@[simp] theorem Inf_coe (P : set (submodule R M)) : (↑(Inf P) : set M) = ⋂ p ∈ P, ↑p := rfl

@[simp] theorem infi_coe {ι} (p : ι → submodule R M) :
  (↑⨅ i, p i : set M) = ⋂ i, ↑(p i) :=
by rw [infi, Inf_coe]; ext a; simp; exact
⟨λ h i, h _ i rfl, λ h i x e, e ▸ h _⟩

@[simp] lemma mem_Inf {S : set (submodule R M)} {x : M} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p :=
set.mem_bInter_iff

@[simp] theorem mem_infi {ι} (p : ι → submodule R M) {x} :
  x ∈ (⨅ i, p i) ↔ ∀ i, x ∈ p i :=
by rw [← set_like.mem_coe, infi_coe, set.mem_Inter]; refl

lemma mem_sup_left {S T : submodule R M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

lemma mem_sup_right {S T : submodule R M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

lemma add_mem_sup {S T : submodule R M} {s t : M} (hs : s ∈ S) (ht : t ∈ T) : s + t ∈ S ⊔ T :=
add_mem _ (mem_sup_left hs) (mem_sup_right ht)

lemma mem_supr_of_mem {ι : Sort*} {b : M} {p : ι → submodule R M} (i : ι) (h : b ∈ p i) :
  b ∈ (⨆i, p i) :=
have p i ≤ (⨆i, p i) := le_supr p i,
@this b h

open_locale big_operators

lemma sum_mem_supr {ι : Type*} [fintype ι] {f : ι → M} {p : ι → submodule R M}
  (h : ∀ i, f i ∈ p i) :
  ∑ i, f i ∈ ⨆ i, p i :=
sum_mem _ $ λ i hi, mem_supr_of_mem i (h i)

lemma sum_mem_bsupr {ι : Type*} {s : finset ι} {f : ι → M} {p : ι → submodule R M}
  (h : ∀ i ∈ s, f i ∈ p i) :
  ∑ i in s, f i ∈ ⨆ i ∈ s, p i :=
sum_mem _ $ λ i hi, mem_supr_of_mem i $ mem_supr_of_mem hi (h i hi)

/-! Note that `submodule.mem_supr` is provided in `linear_algebra/basic.lean`. -/

lemma mem_Sup_of_mem {S : set (submodule R M)} {s : submodule R M}
  (hs : s ∈ S) : ∀ {x : M}, x ∈ s → x ∈ Sup S :=
show s ≤ Sup S, from le_Sup hs

end submodule

section nat_submodule

/-- An additive submonoid is equivalent to a ℕ-submodule. -/
def add_submonoid.to_nat_submodule : add_submonoid M ≃o submodule ℕ M :=
{ to_fun := λ S,
  { smul_mem' := λ r s hs, S.nsmul_mem hs _, ..S },
  inv_fun := submodule.to_add_submonoid,
  left_inv := λ ⟨S, _, _⟩, rfl,
  right_inv := λ ⟨S, _, _, _⟩, rfl,
  map_rel_iff' := λ a b, iff.rfl }

@[simp]
lemma add_submonoid.to_nat_submodule_symm :
  ⇑(add_submonoid.to_nat_submodule.symm : _ ≃o add_submonoid M) = submodule.to_add_submonoid := rfl

@[simp]
lemma add_submonoid.coe_to_nat_submodule (S : add_submonoid M) :
  (S.to_nat_submodule : set M) = S := rfl

@[simp]
lemma add_submonoid.to_nat_submodule_to_add_submonoid (S : add_submonoid M) :
  S.to_nat_submodule.to_add_submonoid = S :=
add_submonoid.to_nat_submodule.symm_apply_apply S

@[simp]
lemma submodule.to_add_submonoid_to_nat_submodule (S : submodule ℕ M) :
  S.to_add_submonoid.to_nat_submodule = S :=
add_submonoid.to_nat_submodule.apply_symm_apply S

end nat_submodule

end add_comm_monoid
