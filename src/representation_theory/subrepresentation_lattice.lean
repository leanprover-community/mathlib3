/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import representation_theory.subrepresentation

/-!
# Lattice structure on subrepresentations
TODO
-/

universes u v w
namespace subrepresentation

section lattice
variables {k : Type u} {G : Type v} {M : Type w}
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M] [distrib_mul_action G M]
variables [representation k G M] {φ ψ : subrepresentation k G M}

/-- The set `{0}` is the bottom element of the lattice of submodules. -/
instance : has_bot (subrepresentation k G M) :=
⟨{ carrier := {0}, group_smul_mem' := by simp { contextual := tt }, .. (⊥ : submodule k M) }⟩

instance inhabited' : inhabited (subrepresentation k G M) := ⟨⊥⟩

@[simp] lemma bot_coe : ((⊥ : subrepresentation k G M) : set M) = {0} := rfl

@[simp] lemma bot_to_submodule : (⊥ : subrepresentation k G M).to_submodule= ⊥ := rfl

section
variables (k G)
@[simp] lemma mem_bot {x : M} : x ∈ (⊥ : subrepresentation k G M) ↔ x = 0 := set.mem_singleton_iff
end

instance unique_bot : unique (⊥ : subrepresentation k G M) :=
⟨infer_instance, λ x, subtype.ext $ (mem_bot k G).1 x.mem⟩

lemma nonzero_mem_of_bot_lt {I : subrepresentation k G M} (bot_lt : ⊥ < I) : ∃ a : I, a ≠ 0 :=
begin
  have h := (set_like.lt_iff_le_and_exists.1 bot_lt).2,
  tidy,
end

instance : order_bot (subrepresentation k G M) :=
{ bot := ⊥,
  bot_le := λ p x, by simp {contextual := tt},
  ..set_like.partial_order }

protected lemma eq_bot_iff (p : subrepresentation k G M) : p = ⊥ ↔ ∀ x ∈ p, x = (0 : M) :=
⟨ λ h, h.symm ▸ λ x hx, (mem_bot k G).mp hx,
  λ h, eq_bot_iff.mpr (λ x hx, (mem_bot k G).mpr (h x hx)) ⟩

protected lemma ne_bot_iff (p : subrepresentation k G M) : p ≠ ⊥ ↔ ∃ x ∈ p, x ≠ (0 : M) :=
by { haveI := classical.prop_decidable, simp_rw [ne.def, p.eq_bot_iff, not_forall] }

/-- The universal set is the top element of the lattice of submodules. -/
instance : has_top (subrepresentation k G M) :=
⟨{ carrier := set.univ, group_smul_mem' := λ _ _ _, trivial, .. (⊤ : submodule k M)}⟩

@[simp] lemma top_coe : ((⊤ : subrepresentation k G M) : set M) = set.univ := rfl

@[simp] lemma top_to_submodule : (⊤ : subrepresentation k G M).to_submodule = ⊤ := rfl

@[simp] lemma mem_top {x : M} : x ∈ (⊤ : subrepresentation k G M) := trivial

instance : order_top (subrepresentation k G M) :=
{ top := ⊤,
  le_top := λ p x _, trivial,
  ..set_like.partial_order }

lemma eq_top_iff' {p : subrepresentation k G M} : p = ⊤ ↔ ∀ x, x ∈ p :=
eq_top_iff.trans ⟨λ h x, h trivial, λ h x _, h x⟩

instance : has_Inf (subrepresentation k G M) :=
⟨λ S, {
  carrier   := ⋂ s ∈ S, (s : set M),
  zero_mem' := by simp,
  add_mem'  := by simp [add_mem] {contextual := tt},
  smul_mem' := by simp [smul_mem] {contextual := tt},
  group_smul_mem' := by simp [gsmul_mem] {contextual := tt} }⟩

private lemma Inf_le' {S : set (subrepresentation k G M)} {p} : p ∈ S → Inf S ≤ p :=
set.bInter_subset_of_mem

private lemma le_Inf' {S : set (subrepresentation k G M)} {p} : (∀q ∈ S, p ≤ q) → p ≤ Inf S :=
set.subset_bInter

instance : has_inf (subrepresentation k G M) :=
⟨λ p q, {
  carrier   := p ∩ q,
  zero_mem' := by simp,
  add_mem'  := by simp [add_mem] {contextual := tt},
  smul_mem' := by simp [smul_mem] {contextual := tt},
  group_smul_mem' := by simp [gsmul_mem] {contextual := tt} }⟩

instance : complete_lattice (subrepresentation k G M) :=
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
  ..subrepresentation.order_top,
  ..subrepresentation.order_bot }

end lattice

section
variables {k : Type u} {G : Type v} {M : Type w}
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M] [distrib_mul_action G M]
variables [representation k G M]

/-- Reinterpret a subrepresentation as a `FG`-submodule. -/
noncomputable def to_monoid_algebra_submodule (p : subrepresentation k G M) :
  submodule (monoid_algebra k G) M :=
{ carrier := p.carrier,
  zero_mem' := p.zero_mem',
  add_mem' := p.add_mem',
  smul_mem' := λ x m hm,
  begin
    rw ← finsupp.sum_single x,
    rw representation.sum_smul,
    rw finsupp.sum,
    refine sum_mem _ (λ g hg, _),
    have hmul := @monoid_algebra.single_mul_single k G _ _ g 1 1 (x g),
    rw [one_mul, mul_one] at hmul,
    rw [← hmul, mul_smul, ← monoid_algebra.of_apply, of_smul, ← of'_apply, of'_smul],
    exact gsmul_mem p g (smul_mem p (x g) hm),
  end }
end

end subrepresentation

namespace submodule
variables {k : Type u} {G : Type v} {M : Type w}
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M] [distrib_mul_action G M] [representation k G M]

/-- Reinterpret a `FG`-submodule as a subrepresentation. -/
def of_monoid_algebra_submodule (N : submodule (monoid_algebra k G) M) :
  subrepresentation k G M :=
{ carrier := N.carrier,
  zero_mem' := N.zero_mem,
  add_mem' := N.add_mem',
  smul_mem' := λ r m hm,
  by { have := N.smul_mem' (of' k G r) hm, rwa of'_smul at this, },
  group_smul_mem' := λ g m hm,
  begin
    simp only at *,
    have := N.smul_mem' (monoid_algebra.of k G g) hm,
    rwa of_smul at this,
  end }

end submodule

namespace subrepresentation
variables {k : Type u} {G : Type v} {M : Type w}
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M] [distrib_mul_action G M] [representation k G M]

@[simp] lemma to_of (p : subrepresentation k G M) :
  p.to_monoid_algebra_submodule.of_monoid_algebra_submodule = p :=
by { apply set_like.ext', refl }

@[simp] lemma of_to (p : submodule (monoid_algebra k G) M) :
  p.of_monoid_algebra_submodule.to_monoid_algebra_submodule = p :=
by { apply set_like.ext', refl }

/-- The natural lattice isomorphism between subrepresentations and `FG`-submodules. -/
noncomputable def order_iso_monoid_algebra_submodule :
  order_iso (subrepresentation k G M) (submodule (monoid_algebra k G) M) :=
{ to_fun := to_monoid_algebra_submodule,
  inv_fun := submodule.of_monoid_algebra_submodule,
  left_inv := λ p, by { apply set_like.ext', refl },
  right_inv := λ p, by { apply set_like.ext', refl },
  map_rel_iff' := λ p q, by refl }

@[simp] lemma order_iso_monoid_algebra_submodule_apply (p : subrepresentation k G M) :
  order_iso_monoid_algebra_submodule p = p.to_monoid_algebra_submodule := rfl

end subrepresentation
