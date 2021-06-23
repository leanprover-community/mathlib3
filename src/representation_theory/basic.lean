/-
Copyright (c) 2021 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import algebra.algebra.basic
import algebra.monoid_algebra

open_locale big_operators

/-!
Representations
-/

/--
Representation of monoid G as a k-module M is a k-linear G-action on M.
-/
class repre
  (k : Type*) [semiring k]
  (G : Type*) [monoid G]
  (M : Type*) [add_comm_monoid M] [module k M]
extends distrib_mul_action G M :=
(smul_smul : ∀ (g : G) (r : k) (m : M), g • (r • m) = r • (g • m))

/--
Representation obtained from a monoid_hom from G to endomorphisms on M
-/
def of_monoid_hom
  {k : Type*} [semiring k]
  {G : Type*} [monoid G]
  {M : Type*} [add_comm_monoid M] [module k M]
  (ρ : G →* M →ₗ[k] M) : repre k G M :=
{ to_distrib_mul_action :=
  { to_mul_action :=
    { to_has_scalar := ⟨λ g x, ρ g x⟩,
      one_smul := by simp,
      mul_smul := by simp },
    smul_add := by simp,
    smul_zero := by simp },
  smul_smul := by simp }

section

/--
G-action as an endomorphism.
-/
def linear_map_of_smul
  (k : Type*) [semiring k]
  (G : Type*) [monoid G]
  (M : Type*) [add_comm_monoid M] [module k M]
  [repre k G M] (g : G) : M →ₗ[k] M :=
{ to_fun := λ x : M, g • x,
  map_add' := by {intros x y, apply smul_add},
  map_smul' := by {intros r x, apply repre.smul_smul} }

variables
  {k : Type*} [semiring k]
  {G : Type*} [monoid G]
  {M : Type*} [add_comm_monoid M] [module k M]
  [repre k G M]

@[simp]
lemma linear_map_of_smul_apply (g : G) (x : M) :
(linear_map_of_smul k G M g : M →ₗ[k] M) x = g • x := rfl

/-
Representation of G as a monoid_hom from G to the monoid of endomorphisms of M.
-/
def to_monoid_hom : G →* M →ₗ[k] M :=
{ to_fun := linear_map_of_smul k G M,
  map_one' := by {ext, simp},
  map_mul' := by {intros g h, ext, simp, apply mul_smul} }

end

@[simp]
lemma mul_smul
  {k : Type*} [semiring k]
  {G : Type*} [monoid G]
  {M : Type*} [add_comm_monoid M] [module k M]
  [repre k G M] : ∀ (g h : G) (x : M), (g * h) • x = g • h • x := mul_smul

@[simp]
lemma smul_smul2
  {k : Type*} [semiring k]
  {G : Type*} [monoid G]
  {M : Type*} [add_comm_monoid M] [module k M]
  [s : repre k G M] : ∀ (g : G) (r : k) (m : M), g • (r • m) = r • (g • m) := by {intros, apply s.smul_smul}

section

set_option old_structure_cmd true

structure subrepre
  (k : Type*) [semiring k]
  (G : Type*) [monoid G]
  (M : Type*) [add_comm_monoid M] [module k M]
  [repre k G M] extends submodule k M :=
(smul_mem : ∀ (g : G) {x : M}, x ∈ carrier → g • x ∈ carrier)

end

namespace subrepre

variables
  {k : Type*} [semiring k]
  {G : Type*} [monoid G]
  {M : Type*} [add_comm_monoid M] [module k M]
  [repre k G M]

instance : set_like (subrepre k G M) M :=
⟨λ p : subrepre k G M, p.carrier, by
  { intros p q h,
    cases p,
    cases q,
    congr' }⟩

@[simp] lemma mem_carrier {p : subrepre k G M} (x : M) : x ∈ p.carrier ↔ x ∈ (p : set M) := iff.rfl

@[simp] lemma to_submodule_carrier {p : subrepre k G M} (x : M) : x ∈ p.carrier ↔ x ∈ p.to_submodule.carrier := iff.rfl

@[ext] theorem ext {p q : subrepre k G M} (h : ∀ x : M, x ∈ p ↔ x ∈ q) : p = q := set_like.ext h

/-- Copy of a `subrepr` with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (p : subrepre k G M) (s : set M) (hs : s = ↑p) : subrepre k G M :=
{ carrier := s,
  zero_mem' := hs.symm ▸ p.zero_mem',
  add_mem' := hs.symm ▸ p.add_mem',
  smul_mem' := hs.symm ▸ p.smul_mem',
  smul_mem := hs.symm ▸ p.smul_mem }

@[simp] lemma zero_mem {p : subrepre k G M} : (0 : M) ∈ p := p.zero_mem'

section

variable (p : subrepre k G M)

instance : add_comm_monoid p := p.to_submodule.add_comm_monoid

instance : module k p := p.to_submodule.module

instance : has_scalar G p :=
begin
  split,
  intros g x,
  exact ⟨g • x.val, p.smul_mem g (set_like.coe_mem x)⟩
end

/--
A subrepresentation inherits the representation structure.
-/
instance : repre k G p :=
{ to_distrib_mul_action :=
  { to_mul_action :=
    { to_has_scalar := ⟨(•)⟩,
      one_smul := by {intros, ext, apply one_smul},
      mul_smul := by {intros, ext, apply mul_action.mul_smul} },
    smul_add := by {intros, ext, apply smul_add},
    smul_zero := by {intros,ext, apply smul_zero} },
  smul_smul := by {intros, ext, apply repre.smul_smul} }

@[simp, norm_cast] lemma coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0 :=
(set_like.coe_eq_coe : (x : M) = (0 : p) ↔ x = 0)
@[simp, norm_cast] lemma coe_add (x y : p) : (↑(x + y) : M) = ↑x + ↑y := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : p) : M) = 0 := rfl
@[norm_cast] lemma coe_smul (r : k) (x : p) : ((r • x : p) : M) = r • ↑x := rfl
@[norm_cast] lemma coe_smul2 (g : G) (x : p) : ((g • x : p) : M) = g • ↑x := rfl
@[simp, norm_cast] lemma coe_mk (x : M) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : M) = x := rfl
@[simp] lemma coe_mem (x : p) : (x : M) ∈ p := x.2













end

instance : has_bot (subrepre k G M) :=
⟨{ carrier := {0},
  smul_mem := by {intros g x, simp, intro hx, rw hx, simp},
  ..(⊥ : submodule k M) }⟩

instance : inhabited (subrepre k G M) := ⟨⊥⟩

@[simp] lemma bot_coe : ((⊥ : subrepre k G M) : set M) = {0} := rfl
@[simp] lemma bot_to_submodule : (⊥ : subrepre k G M).to_submodule = ⊥ := rfl
@[simp] lemma mem_bot {x : M} : x ∈ (⊥ : subrepre k G M) ↔ x = 0 := set.mem_singleton_iff
-- @[simp] lemma bot_coe_eq_to_set_coe : ↥(⊥ : subrepre k G M) = ((⊥ : subrepre k G M) : set M) := rfl

instance unique_bot : unique (⊥ : subrepre k G M) :=
⟨⟨0⟩, λ x, subtype.ext $ mem_bot.1 x.mem⟩

instance : order_bot (subrepre k G M) :=
{ bot := ⊥,
  bot_le := by {intros p x, simp, intro h, rw h, simp},
  ..set_like.partial_order }

protected lemma eq_bot_iff (p : subrepre k G M) : p = ⊥ ↔ ∀ x ∈ p, x = (0 : M) :=
⟨ λ h, h.symm ▸ λ x hx, mem_bot.mp hx,
  λ h, eq_bot_iff.mpr (λ x hx, mem_bot.mpr (h x hx)) ⟩

@[ext] protected lemma bot_ext (x y : (⊥ : subrepre k G M)) : x = y :=
begin
  rcases x with ⟨x, xm⟩, rcases y with ⟨y, ym⟩, congr,
  rw (subrepre.eq_bot_iff _).mp rfl x xm,
  rw (subrepre.eq_bot_iff _).mp rfl y ym
end

protected lemma ne_bot_iff (p : subrepre k G M) : p ≠ ⊥ ↔ ∃ x ∈ p, x ≠ (0 : M) :=
by { haveI := classical.prop_decidable, simp_rw [ne.def, p.eq_bot_iff, not_forall] }

/-
https://github.com/leanprover-community/mathlib/blob/6aed9a7720592ca03e36c4a5a9bacec09dfe277b/src/algebra/module/submodule_lattice.lean
Copy lots of simp lemmas from ^
-/

instance : has_top (subrepre k G M) :=
⟨{ carrier := set.univ,
  smul_mem := by {intros g x, simp},
  ..(⊤ : submodule k M) }⟩

@[simp] lemma top_coe : ((⊤ : subrepre k G M) : set M) = set.univ := rfl

@[simp] lemma mem_top {x : M} : x ∈ (⊤ : subrepre k G M) := trivial

instance : order_top (subrepre k G M) :=
{ top := ⊤,
  le_top := λ p x h, trivial,
  ..set_like.partial_order }

lemma eq_top_iff' {p : subrepre k G M} : p = ⊤ ↔ ∀ x, x ∈ p :=
eq_top_iff.trans ⟨λ h x, h trivial, λ h x _, h x⟩

instance : has_Inf (subrepre k G M) :=
⟨λ S, {
  carrier   := ⋂ s ∈ S, (s : set M),
  zero_mem' := by simp,
  add_mem'  := by
    {intros x y,
    simp,
    intros hx hy p hp,
    have hx' := hx p hp,
    have hy' := hy p hp,
    exact p.add_mem' hx' hy'},
  smul_mem' := by
    {intros r x,
    simp,
    intros hx p hp,
    have hx' := hx p hp,
    exact p.smul_mem' r hx'},
  smul_mem := by
    {intros g x,
    simp,
    intros hx p hp,
    have hx' := hx p hp,
    exact p.smul_mem g hx'}
}⟩

instance : has_inf (subrepre k G M) :=
⟨λ p q, {
  carrier   := p ∩ q,
  zero_mem' := by simp,
  add_mem'  := by {simp, intros, split, apply p.add_mem'; assumption, apply q.add_mem'; assumption},
  smul_mem' := by {simp, intros, split, apply p.smul_mem'; assumption, apply q.smul_mem'; assumption},
  smul_mem := by {simp, intros, split, apply p.smul_mem; assumption, apply q.smul_mem; assumption}
}⟩

private lemma Inf_le' {S : set (subrepre k G M)} {p} : p ∈ S → Inf S ≤ p :=
set.bInter_subset_of_mem

private lemma le_Inf' {S : set (subrepre k G M)} {p} : (∀q ∈ S, p ≤ q) → p ≤ Inf S :=
set.subset_bInter

instance : complete_lattice (subrepre k G M) :=
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
  ..subrepre.order_top,
  ..subrepre.order_bot }

end subrepre

/--
A representation of G over k-module M is irreducible if the only subrepresentations are ⊤ and ⊥.
-/
def is_irreducible
  (k : Type*) [semiring k]
  (G : Type*) [monoid G]
  (M : Type*) [add_comm_monoid M] [module k M] [nontrivial M]
  [repre k G M] : Prop :=
∀ (p : subrepre k G M), p = ⊥ ∨ p = ⊤

/-- is_irreducible k G M produces an instance of is_simple lattice (subrepre k G M) -/
instance
  {k : Type*} [semiring k]
  {G : Type*} [monoid G]
  {M : Type*} [add_comm_monoid M] [module k M] [nontrivial M]
  [repre k G M] (h : is_irreducible k G M) : is_simple_lattice (subrepre k G M) :=
{ exists_pair_ne := by
  { existsi (⊤ : subrepre k G M),
    existsi (⊥ : subrepre k G M),
    apply (subrepre.ne_bot_iff (⊤ : subrepre k G M)).mpr,
    cases exists_ne (0 : M) with x hx,
    existsi x,
    have H : x ∈ (⊤ : subrepre k G M), simp,
    exact ⟨H, hx⟩ },
  eq_bot_or_eq_top := h }