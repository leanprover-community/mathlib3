/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import data.finset.pointwise
import group_theory.group_action.sub_mul_action
import group_theory.group_action.fixing_subgroup

import .equivariant_map

import tactic.group

/-!
# Complements on sub_mul_actions
-/

open_locale pointwise


/-!
# Sub_mul_actions on complements of invariant subsets

- We define sub_mul_action of an invariant subset in various contexts,
especially stabilizers and fixing subgroups : `sub_mul_action_of_compl`,
`sub_mul_action_of_stabilizer`, `sub_mul_action_of_fixing_subgroup`.

- We define equivariant maps that relate various of these sub_mul_actions
and permit to manipulate them in a relatively smooth way.
-/

open_locale pointwise

open mul_action

section sub_mul_actions

namespace sub_mul_action

section inclusion

variables {M N α : Type*} [has_smul M α]

/-- The inclusion of a sub_mul_action into the ambient set, as an equivariant map -/
def inclusion (s : sub_mul_action M α) : s →[M] α := {
to_fun := coe,
map_smul' := λ g y, rfl }

lemma inclusion.to_fun_eq_coe (s : sub_mul_action M α) :
  s.inclusion.to_fun  = coe := rfl

end inclusion

section complements

variables (M : Type*) [group M] {α : Type*} [mul_action M α]

/-- Action on the complement of an invariant subset -/
def of_compl (s : sub_mul_action M α) : sub_mul_action M α := {
carrier := sᶜ,
smul_mem' := λ g x,
  by simp only [set_like.mem_coe, set.mem_compl_iff, sub_mul_action.smul_mem_iff', imp_self] }

lemma of_compl_def (s : sub_mul_action M α) :
  (of_compl M s).carrier = sᶜ := rfl

/-- Action of stabilizer of a point on the complement -/
def of_stabilizer (a : α) : sub_mul_action (stabilizer M a) α := {
carrier := { a }ᶜ,
smul_mem' := λ g x,
begin
  simp only [set.mem_compl_iff, set.mem_singleton_iff],
  rw not_imp_not,
  rw smul_eq_iff_eq_inv_smul,
  intro hgx, rw hgx,
  apply symm, rw ← smul_eq_iff_eq_inv_smul,
  conv_rhs { rw ← mem_stabilizer_iff.mp (set_like.coe_mem g) },
  refl,
end }

lemma of_stabilizer.def (a : α) :
  (sub_mul_action.of_stabilizer M a).carrier = { a }ᶜ := rfl

lemma of_stabilizer.mem_iff (a : α) {x : α} :
  x ∈ sub_mul_action.of_stabilizer M a ↔ x ≠ a := iff.rfl

lemma of_stabilizer.neq (a : α) {x : ↥(sub_mul_action.of_stabilizer M a)} :
  ↑x ≠ a := x.prop

instance of_stabilizer_lift (a : α) :
  has_lift_t (sub_mul_action.of_stabilizer M a) α := coe_to_lift

/-- The sub_mul_action of fixing_subgroup M s on the complement -/
def of_fixing_subgroup (s : set α) :
  sub_mul_action (fixing_subgroup M s) α := {
carrier := sᶜ,
smul_mem' :=
begin
  intros c x,
  simp only [set.mem_compl_iff],
  intros hx hcx, apply hx,
  rw [← one_smul M x, ← inv_mul_self ↑c, mul_smul],

  change ↑(c⁻¹) • c • x ∈ s,
  rw (mem_fixing_subgroup_iff M).mp (set_like.coe_mem c⁻¹) (c • x) hcx,
  exact hcx,
end }

lemma of_fixing_subgroup.def {s : set α} :
  (sub_mul_action.of_fixing_subgroup M s).carrier = sᶜ := rfl

lemma of_fixing_subgroup.mem_iff {s : set α} {x : α} :
  x ∈ sub_mul_action.of_fixing_subgroup M s ↔ x ∉ s := iff.rfl

lemma sub_mul_action_of_fixing_subgroup.not_mem {s : set α}
  (x : sub_mul_action.of_fixing_subgroup M s) :
  ↑x ∉ s := x.prop

end complements

end sub_mul_action

section fixing_subgroup

variables (M : Type*) [group M] {α : Type*} [mul_action M α]

lemma fixing_subgroup_of_insert (a : α) (s : set (sub_mul_action.of_stabilizer M a)) :
  fixing_subgroup M (insert a (coe '' s : set α)) =
  (subgroup.map (subgroup.subtype _) (fixing_subgroup ↥(stabilizer M a) s) : subgroup M) :=
begin
  ext m,
  split,
  { intro hm,
    use m,
    { rw mem_stabilizer_iff,
      rw mem_fixing_subgroup_iff at hm,
      apply hm a (set.mem_insert a _) },
    { split,
      simp only [set_like.mem_coe , mem_fixing_subgroup_iff],
      intros y hy,
      rw mem_fixing_subgroup_iff at hm,

      let t : set α := insert a (coe '' s),
      suffices : ↑y ∈ t,
      { rw [← set_like.coe_eq_coe, sub_mul_action.coe_smul],
        apply hm ↑y this, },
      apply set.mem_insert_of_mem,
      use ⟨y, hy, rfl⟩,
      refl } } ,
  { rintro ⟨n, hn, rfl⟩,
    simp only [subgroup.coe_subtype, set_like.mem_coe, mem_fixing_subgroup_iff] at hn ⊢,
    intros y hy,
    cases set.mem_insert_iff.mp hy with hy hy,
      -- y = a
      rw hy, simpa using n.prop,
      -- y ∈ s
      simp only [set.mem_image] at hy,
      obtain ⟨y, hy1, rfl⟩ := hy,
      conv_rhs { rw ← hn y hy1 },
      refl },
end

end fixing_subgroup


section equivariant_map

variables (M : Type*) [group M] {α : Type*} [mul_action M α]

/-- The equivariant map from the sub_mul_action_of stabilizer into the ambient type -/
def sub_mul_action_of_stabilizer_inclusion (a : α):
  (sub_mul_action.of_stabilizer M a) →[stabilizer M a] α := {
to_fun := λ x, ↑x,
map_smul' := λ g x, rfl }
/-
def of_fixing_subgroup.inclusion (s : set α) :
  (sub_mul_action.of_fixing_subgroup M s) →[fixing_subgroup M s] α := {
to_fun := λ x, ↑x,
map_smul' := λ g x, rfl }
 -/


variable (α)

/-- The identity map of the sub_mul_action of the fixing_subgroup
of the empty set into the ambient set, as an equivariant map -/
def sub_mul_action.of_fixing_subgroup_empty_map :
  let φ := (fixing_subgroup M (∅ : set α)).subtype in
  sub_mul_action.of_fixing_subgroup M (∅ : set α) →ₑ[φ] α := {
  to_fun := λ x, x,
  map_smul' := λ g x, rfl }

lemma sub_mul_action.of_fixing_subgroup_empty_map_bijective :
  function.bijective (sub_mul_action.of_fixing_subgroup_empty_map M α) :=
begin
  split,
  { rintros ⟨x,hx⟩ ⟨y, hy⟩ hxy,
    simp only [subtype.mk_eq_mk],
    exact hxy },
  { intro x, use x,
    rw sub_mul_action.of_fixing_subgroup.mem_iff,
    exact set.not_mem_empty x,
    refl }
end

lemma sub_mul_action.of_fixing_subgroup_empty_map_scalars_surjective :
  function.surjective (fixing_subgroup M (∅ : set α)).subtype :=
begin
  intro g,
  use g, rw mem_fixing_subgroup_iff,
  intros x hx, exfalso, simpa using hx,
  refl
end

variable {α}

/-- The identity map of fixing subgroup of stabilizer
into the fixing subgroup of the extended set, as an equivariant map -/
def sub_mul_action.of_fixing_subgroup_of_stabilizer.map
  (a : α) (s : set (sub_mul_action.of_stabilizer M a)) :
  let φ : fixing_subgroup M (insert a (coe '' s : set α)) → fixing_subgroup (stabilizer M a) s :=
  λ m, ⟨⟨(m : M),
    begin
      apply (mem_fixing_subgroup_iff M).mp m.prop,
      apply set.mem_insert
    end ⟩, λ ⟨x, hx⟩,
    begin
      simp only [← set_like.coe_eq_coe],
      refine (mem_fixing_subgroup_iff M).mp m.prop _ _,
      apply set.mem_insert_of_mem,
      exact ⟨x, hx, rfl⟩,
    end ⟩
  in sub_mul_action.of_fixing_subgroup M (insert a (coe '' s : set α)) →ₑ[φ]
    (sub_mul_action.of_fixing_subgroup (stabilizer M a) s) := {
to_fun := λ x, ⟨⟨(x : α), begin
  rintro (h : (x : α) = a),
  apply (sub_mul_action.of_fixing_subgroup.mem_iff M).mp x.prop,
  rw h, apply set.mem_insert,
  end⟩,
  λ h, (sub_mul_action.of_fixing_subgroup.mem_iff M).mp x.prop $
    set.mem_insert_of_mem _ ⟨⟨(x : α), _⟩, ⟨h, rfl⟩⟩⟩,
map_smul' := λ m x, rfl
}

lemma sub_mul_action.of_fixing_subgroup_of_stabilizer.map_bijective
  (a : α) (s : set (sub_mul_action.of_stabilizer M a)) :
  function.bijective (sub_mul_action.of_fixing_subgroup_of_stabilizer.map M a s) :=
begin
  split,
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ h,
  -- PROVE A LEMMA THAT DOES THIS AUTOMATICALLY
    simp only [subtype.mk_eq_mk],
    suffices hx : x = ↑((sub_mul_action.of_fixing_subgroup_of_stabilizer.map M a s) ⟨x, hx⟩),
    suffices hy : y = ↑((sub_mul_action.of_fixing_subgroup_of_stabilizer.map M a s) ⟨y, hy⟩),
    rw hx, rw hy, rw h,
    refl, refl },
  { rintro ⟨⟨x, hx1⟩, hx2⟩,
    refine ⟨⟨x, _⟩, rfl⟩,
    -- ⊢ x ∈ sub_mul_action_of_fixing_subgroup M (insert a (coe '' s))
    rw sub_mul_action.of_fixing_subgroup.mem_iff,
    intro h, cases set.mem_insert_iff.mp h,
    { rw sub_mul_action.of_stabilizer.mem_iff at hx1, exact hx1 h_1 },
    { rw sub_mul_action.of_fixing_subgroup.mem_iff at hx2,
      apply hx2,
      obtain ⟨x1, hx1', rfl⟩ := h_1,
      simp only [set_like.eta],
      exact hx1' } },
end

lemma sub_mul_action.of_fixing_subgroup_of_stabilizer.scalar_map_bijective
  (a : α) (s : set (sub_mul_action.of_stabilizer M a)) :
  function.bijective (sub_mul_action.of_fixing_subgroup_of_stabilizer.map M a s).to_smul_map :=
begin
  split,
  { rintros ⟨m, hm⟩ ⟨n, hn⟩ hmn,
    rw [← set_like.coe_eq_coe, ← set_like.coe_eq_coe, ← coe_coe] at hmn,
    simp only [subtype.mk_eq_mk],
    exact hmn },
  { rintro ⟨⟨m, hm⟩, hm'⟩,
    use m, swap, refl,
    rw mem_fixing_subgroup_iff,
    intros x hx,
    cases set.mem_insert_iff.mp hx with hx hx,
    { -- x = a
      rw hx, exact mem_stabilizer_iff.mp hm },
    { -- x ∈ coe '' s
      obtain ⟨y, hy, rfl⟩ := (set.mem_image _ _ _).mp  hx,
      rw mem_fixing_subgroup_iff at hm',
      let hz := hm' y hy,
      rw [← set_like.coe_eq_coe, sub_mul_action.coe_smul_of_tower] at hz,
      exact hz } }
end



/-- If the fixing_subgroup of `s` is `G`, then the fixing_subgroup of `g • x` is `gGg⁻¹`. -/
lemma fixing_subgroup_smul_eq_fixing_subgroup_map_conj (g : M) (s : set α) :
  (fixing_subgroup M (g • s) = (fixing_subgroup M s).map (mul_aut.conj g).to_monoid_hom) :=
begin
  ext h,
  split,
  { intro hh,
    use (mul_aut.conj g⁻¹) h,
    simp,
    split,
    rintro ⟨x, hx⟩,
    simp only [subtype.coe_mk, ← smul_smul],
    rw inv_smul_eq_iff,
    simpa only [subtype.coe_mk] using hh ⟨_, set.smul_mem_smul_set hx⟩,
    group, },
  { rintro ⟨k, hk, rfl⟩,
    rintro ⟨x, hx⟩,
    simp only [mul_equiv.coe_to_monoid_hom, mul_aut.conj_apply, subtype.coe_mk, ← smul_smul],
    rw smul_eq_iff_eq_inv_smul,
    exact hk ⟨_, set.mem_smul_set_iff_inv_smul_mem.mp hx⟩ }
end

/-- Conjugation induces an equivariant map between the sub_mul_action of
the fixing subgroup of a subset and that of a translate -/
def sub_mul_action.of_fixing_subgroup.conj_map {s t : set α} {g : M} (hst : g • s = t) :
  let φ : fixing_subgroup M s → fixing_subgroup M t :=
λ ⟨m, hm⟩, ⟨(mul_aut.conj g) m,
begin
  rw ← hst,
  rw fixing_subgroup_smul_eq_fixing_subgroup_map_conj ,
  use m, apply and.intro hm, refl,
end⟩ in sub_mul_action.of_fixing_subgroup M s →ₑ[φ] sub_mul_action.of_fixing_subgroup M t := {
to_fun := λ ⟨x, hx⟩, ⟨g • x,
begin
  intro hgxt, apply hx,
  rw ← hst at hgxt,
  exact set.smul_mem_smul_set_iff.mp  hgxt,
end⟩,
map_smul' := λ ⟨m, hm⟩ ⟨x, hx⟩,
begin
  rw ← set_like.coe_eq_coe,
  change g • m • x = (mul_aut.conj g m) • g • x,
  simp only [mul_aut.conj_apply, mul_smul, inv_smul_smul],
end }

lemma sub_mul_action.of_fixing_subgroup.conj_map_bijective {s t : set α} {g : M}
  (hst : g • s = t) :
  function.bijective (sub_mul_action.of_fixing_subgroup.conj_map M hst) :=
begin
  split,
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy,
    simp only [subtype.mk_eq_mk],
    rw ← set_like.coe_eq_coe at hxy,
    change g • x = g • y at hxy,
    apply (mul_action.injective g) hxy },
  { rintro ⟨x, hx⟩,
    have hst' : g⁻¹ • t = s, {
      apply symm, rw ← inv_smul_eq_iff, rw inv_inv,
      exact hst },
    use (sub_mul_action.of_fixing_subgroup.conj_map M hst') ⟨x, hx⟩,
    rw ← set_like.coe_eq_coe,
    change g • g⁻¹ • x = x,
    rw [← mul_smul, mul_inv_self, one_smul] }
end

/-- Conjugation induces an equivariant map between the sub_mul_action of
the stabilizer of a pint and that of its translate -/
def sub_mul_action.of_stabilizer.conj_map {a b : α} {g : M} (hab : g • a = b) :
let φ : stabilizer M a → stabilizer M b := λ ⟨m, hm⟩, ⟨(mul_aut.conj g) m,
begin
  rw ← hab, rw stabilizer_smul_eq_stabilizer_map_conj ,
  use m, apply and.intro hm, refl,
  end⟩ in sub_mul_action.of_stabilizer M a →ₑ[φ] sub_mul_action.of_stabilizer M b := {
to_fun := λ ⟨x, hx⟩, ⟨g • x,
begin
  intro hy,
  simp only [set.mem_singleton_iff] at hy,
  rw ← hab at hy,
  apply hx,
  simp only [set.mem_singleton_iff],
  exact mul_action.injective g hy,
end⟩,
map_smul' := λ ⟨m, hm⟩ ⟨x, hx⟩,
begin
  rw ← set_like.coe_eq_coe,
  simp only [sub_mul_action.coe_smul_of_tower],
  change g • m • x = (mul_aut.conj g m) • g • x,
  simp only [mul_aut.conj_apply, mul_smul, inv_smul_smul],
end }

lemma sub_mul_action.of_stabilizer.conj_map_bijective {a b : α} {g : M} (hab : g • a = b) :
  function.bijective (sub_mul_action.of_stabilizer.conj_map M hab) :=
begin
  split,
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy,
    simp only [subtype.mk_eq_mk],
    rw ← set_like.coe_eq_coe at hxy,
    change g • x = g • y at hxy,
    apply (mul_action.injective g) hxy },
  { rintro ⟨x, hx⟩,
    use (sub_mul_action.of_stabilizer.conj_map M (inv_smul_eq_iff.mpr hab.symm)) ⟨x, hx⟩,
    rw ← set_like.coe_eq_coe,
    change g • g⁻¹ • x = x,
    simp only [smul_inv_smul] }
end

/-- The identity between the iterated sub_mul_action of the fixing_subgroups
and the sub_mul_action of the fixing_subgroup of the union,
as an equivariant map -/
def sub_mul_action.of_fixing_subgroup_union.map (s t : set α) :
let φ : fixing_subgroup M (s ∪ t) →
  fixing_subgroup (fixing_subgroup M s) (coe ⁻¹' t : set (sub_mul_action.of_fixing_subgroup M s)) :=
λ ⟨m, hm⟩, ⟨⟨m,
begin
  rw [fixing_subgroup_union, subgroup.mem_inf] at hm,
  exact hm.left
end⟩,
begin
  rintro ⟨⟨x, hx⟩, hx'⟩,
  simp only [set.mem_preimage] at hx',
  simp only [← set_like.coe_eq_coe, subtype.coe_mk, sub_mul_action.coe_smul_of_tower],
  rw [fixing_subgroup_union, subgroup.mem_inf] at hm,
  exact hm.right ⟨x, hx'⟩
 end⟩ in sub_mul_action.of_fixing_subgroup M (s ∪ t) →ₑ[φ]
    (sub_mul_action.of_fixing_subgroup (fixing_subgroup M s)
      (coe ⁻¹' t : set(sub_mul_action.of_fixing_subgroup M s))) := {
to_fun := λ x, ⟨⟨x, λ hx, x.prop (set.mem_union_left t hx)⟩, λ hx, x.prop
begin
  apply set.mem_union_right s,
  simpa only [set.mem_preimage, subtype.coe_mk] using hx
end⟩,
map_smul' := λ ⟨m, hm⟩ ⟨x, hx⟩,
begin
  rw [← set_like.coe_eq_coe, ← set_like.coe_eq_coe, ← coe_coe],
  refl
end }

lemma sub_mul_action.of_fixing_subgroup_union.map_def (s t : set α)
  (x : sub_mul_action.of_fixing_subgroup M (s ∪ t)) :
  ((sub_mul_action.of_fixing_subgroup_union.map M s t) x : α) = x := rfl

lemma sub_mul_action.of_fixing_subgroup_union.map_bijective (s t : set α) :
  function.bijective (sub_mul_action.of_fixing_subgroup_union.map M s t) :=
begin
  split,
  { intros a b h,
    simp only [coe_coe, ← set_like.coe_eq_coe],
    simp only [← set_like.coe_eq_coe] at h,
    exact h },
  { rintro ⟨⟨a, ha⟩, ha'⟩, use a,
    { intro hy, cases (set.mem_union a s t).mp hy,
      exact ha h,
      apply ha', simp only [set.mem_preimage, sub_mul_action.coe_mk], exact h },
    refl }
end

/-- The equivariant map on sub_mul_action.of_fixing_subgroup given a set inclusion -/
def sub_mul_action.of_fixing_subgroup.map_of_inclusion {s t : set α} (hst : t ⊆ s) :
let φ : fixing_subgroup M s → fixing_subgroup M t := λ ⟨m, hm⟩, ⟨m,
begin
  apply fixing_subgroup_antitone,
  exact hst, exact hm
end⟩
in sub_mul_action.of_fixing_subgroup M s →ₑ[φ] sub_mul_action.of_fixing_subgroup M t := {
to_fun := λ ⟨x, hx⟩, ⟨x, λ h, hx (hst h)⟩,
map_smul' := λ ⟨m, hm⟩ ⟨x, hx⟩, rfl }

/-- The equivariant map between sub_mul_action.of_stabilizer
  and .of_fixing_subgroup of the singleton -/
def sub_mul_action.of_fixing_subgroup_of_singleton.map (a : α)  :
let φ : fixing_subgroup M ({a} : set α) →  stabilizer M a :=
  λ ⟨m, hm⟩, ⟨m, ((mem_fixing_subgroup_iff M).mp hm) a (set.mem_singleton a)⟩
in (sub_mul_action.of_fixing_subgroup M ({a} : set α)) →ₑ[φ]
  (sub_mul_action.of_stabilizer M a) := {
to_fun := λ ⟨x, hx⟩, ⟨x, by simpa using hx⟩,
map_smul' := λ ⟨m, hm⟩ ⟨x, hx⟩, rfl  }

lemma sub_mul_action.of_fixing_subgroup_of_singleton.map_bijective (a : α) :
  function.bijective (sub_mul_action.of_fixing_subgroup_of_singleton.map M a) :=
begin
  split,
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy, exact hxy },
  { rintro ⟨x, hx⟩, use x, refl },
end

/-- The identity between the sub_mul_action of fixing_subgroups
of equal sets, as an equivariant map -/
def sub_mul_action.of_fixing_subgroup_of_eq.map {s t : set α} (hst : s = t) :
let φ: fixing_subgroup M s → fixing_subgroup M t :=  λ ⟨m, hm⟩, ⟨m, begin rw ← hst, exact hm end⟩
in sub_mul_action.of_fixing_subgroup M s →ₑ[φ] sub_mul_action.of_fixing_subgroup M t := {
to_fun := λ ⟨x, hx⟩, ⟨x, begin rw ← hst, exact hx end⟩,
map_smul' := λ ⟨m, hm⟩ ⟨x, hx⟩, rfl }

lemma sub_mul_action.of_fixing_subgroup_of_eq.map_def {s t : set α} (hst : s = t) :
  ∀ (x : α) (hx : x ∈ sub_mul_action.of_fixing_subgroup M s),
  (((sub_mul_action.of_fixing_subgroup_of_eq.map M hst) ⟨x, hx⟩) : α) = x := λ x hx, rfl

lemma sub_mul_action.of_fixing_subgroup_of_eq.to_smul_map_def {s t : set α} (hst : s = t)
  (g : M)  (hg : g ∈ fixing_subgroup M s) :
  g = (sub_mul_action.of_fixing_subgroup_of_eq.map M hst).to_smul_map
    (⟨g, hg⟩ : fixing_subgroup M s) := rfl

lemma sub_mul_action.of_fixing_subgroup_of_eq.map_bijective {s t : set α} (hst : s = t) :
  function.bijective (sub_mul_action.of_fixing_subgroup_of_eq.map M hst) :=
begin
  split,
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy,
    rw ← set_like.coe_eq_coe at hxy ⊢,
    simp only [set_like.coe_mk],
    simp only [sub_mul_action.of_fixing_subgroup_of_eq.map_def M hst] at hxy,
    rw hxy },
  { rintro ⟨x, hxt⟩,
    use x, rw hst, exact hxt,
    refl },
end

lemma sub_mul_action.of_fixing_subgroup_of_eq.to_smul_map_bijective {s t : set α} (hst : s = t) :
  function.bijective (sub_mul_action.of_fixing_subgroup_of_eq.map M hst).to_smul_map :=
begin
  split,
  { rintros ⟨g, hg⟩ ⟨k, hk⟩ hgk,
    rw [← set_like.coe_eq_coe] at hgk ⊢,
    simp only [set_like.coe_mk],
    exact hgk },
  { rintro ⟨k, hk⟩, use k, rw hst, exact hk,
    refl }
end


end equivariant_map

#lint

#exit


variable (α)
def sub_mul_action_of_fixing_subgroup_empty_bihom :
  mul_action_bihom
  (fixing_subgroup M (∅ : set α)) (sub_mul_action_of_fixing_subgroup M (∅ : set α))
  M α := sub_mul_action_of_fixing_subgroup_inclusion' M (∅ : set α)

/-
variable {α}
lemma hj : ∀ (a : α), a ∈ sub_mul_action_of_fixing_subgroup M (∅ : set α) :=
begin
  intro a, change a ∈ (sub_mul_action_of_fixing_subgroup M ∅).carrier,
  rw sub_mul_action_of_fixing_subgroup_def,
  simp only [set.compl_empty]
end

lemma hj' : ∀ (m : M), m ∈ fixing_subgroup M (∅ : set α) :=
begin
  intro m, rw mem_fixing_subgroup_iff, intros y hy,
      exfalso, simpa only using hy,
end
-/

lemma sub_mul_action_of_fixing_subgroup_empty_bihom_bijective :
  function.bijective (sub_mul_action_of_fixing_subgroup_empty_bihom M α).to_fun :=
begin
  split,
    { intros a b h,
      rw ← set_like.coe_eq_coe,
      change (sub_mul_action_of_fixing_subgroup_empty_bihom M α).to_fun a
        = (sub_mul_action_of_fixing_subgroup_empty_bihom M α).to_fun b,
      rw h },
    { intro a, use a,
      change a ∈ (sub_mul_action_of_fixing_subgroup M ∅).carrier,
      rw sub_mul_action_of_fixing_subgroup_def,
      simp only [set.compl_empty], refl }
end

variable (α)
def sub_mul_action_of_fixing_subgroup_empty_bihom' :
  mul_action_bihom M α (fixing_subgroup M (∅ : set α)) (sub_mul_action_of_fixing_subgroup M ∅) := {
to_fun := λ a, ⟨a,
begin
  rw mem_sub_mul_action_of_fixing_subgroup_iff,
  simp only [set.mem_empty_eq, not_false_iff],
end
⟩ ,
to_monoid_hom := {
  to_fun := λ m, ⟨m, λ ⟨y, hy⟩, begin exfalso, simpa only using hy, end ⟩  ,
  map_one' := rfl,
  map_mul' := λ m n, rfl },
map_smul' := λ m a, begin  simp, refl, end }

lemma sub_mul_action_of_fixing_subgroup_empty_bihom'_bijective :
  function.bijective (sub_mul_action_of_fixing_subgroup_empty_bihom' M α).to_fun :=
begin
  split,
    { intros a b, apply set_like.coe_eq_coe.mpr },
    { intro a, use a, rw ← set_like.coe_eq_coe, refl }
end

variable {α}

def sub_mul_action_of_fixing_subgroup_bihom {s : set α} :
  mul_action_bihom (fixing_subgroup M sᶜ) (sub_mul_action_of_fixing_subgroup M sᶜ)
    (equiv.perm s) (s) := {
to_fun := λ ⟨x, hx⟩, ⟨x,
begin
  rw mem_sub_mul_action_of_fixing_subgroup_iff at hx,
  simp only [set.mem_compl_eq, set.not_not_mem] at hx,
  exact hx
end⟩,
to_monoid_hom := {
  to_fun := λ ⟨g, hg⟩,  {
    to_fun := λ ⟨u, hu⟩, ⟨g • u,
    begin
      rw ← set.not_mem_compl_iff at  ⊢ hu,
      intro h,  apply hu,
      let hg' := (mem_fixing_subgroup_iff M).mp (subgroup.inv_mem _ hg) _ h,
      rw inv_smul_smul at hg',
      rw hg', exact h
    end⟩,
    inv_fun := λ ⟨u, hu⟩, ⟨g⁻¹ • u,
    begin
      rw ← set.not_mem_compl_iff at ⊢ hu, intro h,
      apply hu,
      rw mem_fixing_subgroup_iff at hg,
      rw ← smul_inv_smul g u,
      rw hg _ h, exact h,
    end⟩,
    left_inv := λ ⟨u, hu⟩,
    begin
      unfold sub_mul_action_of_fixing_subgroup_bihom._match_2,
      unfold sub_mul_action_of_fixing_subgroup_bihom._match_3,
      simp only [inv_smul_smul]
    end,
    right_inv := λ ⟨u, hu⟩,
    begin
      unfold sub_mul_action_of_fixing_subgroup_bihom._match_3,
      unfold sub_mul_action_of_fixing_subgroup_bihom._match_2,
      simp only [smul_inv_smul]
    end },
  map_one' :=
  begin
    ext ⟨u, hu⟩,
    simp only [equiv.perm.coe_one, id.def],
    have hv : (1 : M) • u ∈ s, rw one_smul, exact hu,
    suffices : (sub_mul_action_of_fixing_subgroup_bihom._match_6 M 1) ⟨u, hu⟩ = ⟨1 • u, hv⟩,
    rw this,
    simp only [one_smul],
    refl
  end,
  map_mul' := λ ⟨x, hx⟩ ⟨y, hy⟩,
  begin
    ext ⟨u, hu⟩,
    simp,
    suffices : sub_mul_action_of_fixing_subgroup_bihom._match_6 M ⟨y, hy⟩ ⟨u, hu⟩
       = ⟨y • u, _⟩,
    rw this,
    suffices : sub_mul_action_of_fixing_subgroup_bihom._match_6 M ⟨x, hx⟩ ⟨y • u, _⟩
      = ⟨x • y • u, _⟩,
    rw this,
    suffices : sub_mul_action_of_fixing_subgroup_bihom._match_6 M ⟨x * y, _⟩ ⟨u, hu⟩
      = ⟨(x * y) • u, _⟩,
    rw this,
    simp only [subtype.coe_mk, mul_smul],
    refl,
    refl,
    refl
  end },
map_smul' := λ ⟨g, hg⟩ ⟨x, hx⟩,
begin
  simp only [monoid_hom.coe_mk, equiv.perm.smul_def],
  unfold sub_mul_action_of_fixing_subgroup_bihom._match_1,
  unfold sub_mul_action_of_fixing_subgroup_bihom._match_6,
  refl
end }

lemma sub_mul_action_of_fixing_subgroup_bihom_def {s : set α}
  (x : α) (hx : x ∈ sub_mul_action_of_fixing_subgroup M sᶜ) :
  x = ((sub_mul_action_of_fixing_subgroup_bihom M).to_fun ⟨x, hx⟩ : α) := rfl

lemma sub_mul_action_of_fixing_subgroup_bihom_bijective {s : set α} :
  function.bijective (@sub_mul_action_of_fixing_subgroup_bihom M α _ _ s).to_fun :=
begin
  unfold sub_mul_action_of_fixing_subgroup_bihom,
  simp,
  split,
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy,
    change (sub_mul_action_of_fixing_subgroup_bihom M).to_fun ⟨x, hx⟩ =
      (sub_mul_action_of_fixing_subgroup_bihom M).to_fun ⟨y, hy⟩ at hxy,
    rw ← set_like.coe_eq_coe, simp only [set_like.coe_mk],
    rw sub_mul_action_of_fixing_subgroup_bihom_def M x hx,
    rw sub_mul_action_of_fixing_subgroup_bihom_def M y hy,
    rw hxy },
  { rintro ⟨x, hx⟩, use x, refl }
end

def sub_mul_action_of_fixing_subgroup_of_inclusion {s t : set α} (hst : s ⊇ t) :
  mul_action_bihom (fixing_subgroup M s) (sub_mul_action_of_fixing_subgroup M s)
   (fixing_subgroup M t) (sub_mul_action_of_fixing_subgroup M t) :=
let h : fixing_subgroup M s ≤ fixing_subgroup M t :=
begin intro m, simp only [mem_fixing_subgroup_iff],
  intros hs y hyt, exact hs y (hst hyt)
end
in let h' : (sub_mul_action_of_fixing_subgroup M s).carrier ≤ (sub_mul_action_of_fixing_subgroup M t).carrier :=
begin intro x, simp only [sub_mul_action_of_fixing_subgroup_def M],
  simp only [set.mem_compl_eq, not_imp_not],
  intro hxt, exact hst hxt,
end
in sub_mul_action_of_leq_bihom M α h h'

lemma sub_mul_action_of_fixing_subgroup_of_fixing_subgroup_def (s t : set α) :
  coe '' (sub_mul_action_of_fixing_subgroup
    (fixing_subgroup M s)
    (coe ⁻¹' t : set (sub_mul_action_of_fixing_subgroup M s))).carrier
    = (sub_mul_action_of_fixing_subgroup M (s ∪ t)).carrier :=
begin
  ext x,
  simp only [sub_mul_action_of_fixing_subgroup_def,
    set.mem_compl_iff, set.mem_union_eq,
    set.mem_image, set.mem_preimage],
  split,
  { rintro ⟨x, hx, rfl⟩,
    exact not_or (sub_mul_action_of_fixing_subgroup_not_mem _ _) hx },
  { intro hx,
    have hx' : x ∈ (sub_mul_action_of_fixing_subgroup M s).carrier,
    { rw sub_mul_action_of_fixing_subgroup_def,
      refine set.mem_compl _,
      exact mt (or.inl) hx },
    use ⟨x, hx'⟩,
    split,
    { simp only [set.mem_preimage, subtype.coe_mk],
      exact mt (or.inr) hx },
    { simp only [subtype.coe_mk] } }
end

lemma sub_mul_action_of_fixing_subgroup_of_stabilizer_def (a : α) (s : set α) :
  coe '' (sub_mul_action_of_fixing_subgroup
    (stabilizer M a)
    (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a))).carrier
    = (sub_mul_action_of_fixing_subgroup M (insert a s)).carrier :=
begin
  ext x,
  simp only [sub_mul_action_of_fixing_subgroup_def,
    set.mem_compl_iff, set.mem_insert_iff,
    set.mem_preimage,
    set.mem_image],
  split,
  { rintro ⟨x, hx, rfl⟩,
    apply not_or _ hx,
    { apply  sub_mul_action_of_stabilizer_neq } },
  { intro hx,
    have hx' : x ∈ (sub_mul_action_of_stabilizer M α a).carrier,
    { rw sub_mul_action_of_stabilizer_def,
      simp only [set.mem_compl_eq, set.mem_singleton_iff],
      exact mt (or.inl) hx },
    use ⟨x, hx'⟩,
    simp only [subtype.coe_mk],
    exact and.intro (mt (or.inr) hx) rfl }
end

def sub_mul_action_of_fixing_subgroup_id (s : set α) :
  mul_action_bihom (fixing_subgroup M s) (sub_mul_action_of_fixing_subgroup M s)
    (fixing_subgroup M s) (sub_mul_action_of_fixing_subgroup M s) := {
to_fun := id,
to_monoid_hom := monoid_hom.id ↥(fixing_subgroup M s),
map_smul' := λ m a, rfl }

def sub_mul_action_of_fixing_subgroup_id_def (s : set α)
  (x : (sub_mul_action_of_fixing_subgroup M s)) :
  (coe ((sub_mul_action_of_fixing_subgroup_id M s).to_fun x) : α) = x := rfl

def sub_mul_action_of_fixing_subgroup_eq_bihom {s t : set α} (hst : s = t) :
  mul_action_bihom (fixing_subgroup M s) (sub_mul_action_of_fixing_subgroup M s)
    (fixing_subgroup M t) (sub_mul_action_of_fixing_subgroup M t) :=
let aux_fun : ∀ x ∈ sub_mul_action_of_fixing_subgroup M s,
  x ∈ sub_mul_action_of_fixing_subgroup M t := λ x hx,
begin rw ← hst, exact hx end
in let aux_hom : ∀ m ∈ fixing_subgroup M s, m ∈ fixing_subgroup M t := λ m hm,
begin rw ← hst, exact hm end
in {
to_fun := λ ⟨x, hx⟩, ⟨x, aux_fun x hx⟩,
to_monoid_hom := {
  to_fun := λ ⟨m, hm⟩, ⟨m, aux_hom m hm⟩,
  map_one' := rfl,
  map_mul' := λ ⟨m, hm⟩ ⟨m', hm'⟩, rfl },
map_smul' := λ ⟨m, hm⟩ ⟨x, hx⟩, rfl }


lemma sub_mul_action_of_fixing_subgroup_eq_bihom_def {s t : set α} (hst : s = t) :
  ∀ (x : α) (hx : x ∈ sub_mul_action_of_fixing_subgroup M s),
  (((sub_mul_action_of_fixing_subgroup_eq_bihom M hst).to_fun ⟨x, hx⟩) : α) = x := λ x hx, rfl

lemma sub_mul_action_of_fixing_subgroup_eq_bihom_monoid_hom_def {s t : set α} (hst : s = t)
  (g : M)  (hg : g ∈ fixing_subgroup M s) :
  g = (sub_mul_action_of_fixing_subgroup_eq_bihom M hst).to_monoid_hom.to_fun
    (⟨g, hg⟩ : fixing_subgroup M s) := rfl

lemma sub_mul_action_of_fixing_subgroup_eq_bihom_bijective {s t : set α} (hst : s = t) :
  function.bijective (sub_mul_action_of_fixing_subgroup_eq_bihom M hst).to_fun :=
begin
  split,
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy,
    rw ← set_like.coe_eq_coe at hxy ⊢,
    simp only [set_like.coe_mk],
    simp only [sub_mul_action_of_fixing_subgroup_eq_bihom_def M hst] at hxy,
    rw hxy },
  { rintro ⟨x, hxt⟩,
    use x, rw hst, exact hxt,
    refl },
end

lemma sub_mul_action_of_fixing_subgroup_eq_bihom_monoid_hom_bijective {s t : set α} (hst : s = t) :
  function.bijective (sub_mul_action_of_fixing_subgroup_eq_bihom M hst).to_monoid_hom.to_fun :=
let aux_hom : ∀ m ∈ fixing_subgroup M s, m ∈ fixing_subgroup M t := λ m hm,
begin rw ← hst, exact hm end
in begin
  split,
  { rintros ⟨g, hg⟩ ⟨k, hk⟩ hgk,
    rw [← set_like.coe_eq_coe] at hgk ⊢,
    simp only [set_like.coe_mk],
    exact hgk },
  { rintro ⟨k, hk⟩, use k, rw hst, exact hk,
    refl }
end

def sub_mul_action_of_fixing_subgroup_union_bihom (s t : set α) : mul_action_bihom
  (fixing_subgroup M (s ∪ t)) (sub_mul_action_of_fixing_subgroup M (s ∪ t))
  (fixing_subgroup (fixing_subgroup M s) (coe ⁻¹' t : set (sub_mul_action_of_fixing_subgroup M s)))
    (sub_mul_action_of_fixing_subgroup (fixing_subgroup M s)
      (coe ⁻¹' t : set(sub_mul_action_of_fixing_subgroup M s))) := {
to_fun := λ x,
let px : ↑x ∉ s ∧ ↑x ∉ t :=
begin
  let px' : ↑x ∈ (sub_mul_action_of_fixing_subgroup M (s ∪ t)).carrier := x.prop,
  rw sub_mul_action_of_fixing_subgroup_def at px',
  simp only [set.compl_union, set.mem_inter_eq, set.mem_compl_eq] at px',
  exact px'
end
in let hx : ↑x ∈ sub_mul_action_of_fixing_subgroup M s :=
begin
  change ↑x ∈ (sub_mul_action_of_fixing_subgroup M s).carrier,
  rw sub_mul_action_of_fixing_subgroup_def,
  simp only [set.mem_compl_eq],
  exact px.left
end
in let hx' : (⟨↑x, hx⟩ : sub_mul_action_of_fixing_subgroup M s) ∈ sub_mul_action_of_fixing_subgroup (fixing_subgroup M s)
  (coe ⁻¹' t : set (sub_mul_action_of_fixing_subgroup M s)) :=
begin
  change (⟨↑x, hx⟩ : sub_mul_action_of_fixing_subgroup M s) ∈
    (sub_mul_action_of_fixing_subgroup (fixing_subgroup M s)
      (coe ⁻¹' t : set (sub_mul_action_of_fixing_subgroup M s))).carrier,
  rw sub_mul_action_of_fixing_subgroup_def ↥(fixing_subgroup M s),
  simp only [set.mem_compl_eq, set.mem_preimage, sub_mul_action.coe_mk],
  exact px.right
end
in ⟨⟨↑x, hx⟩, hx'⟩,
to_monoid_hom := {
  to_fun := λ m,
let pm : ↑m ∈ fixing_subgroup M s ∧ ↑m ∈ fixing_subgroup M t :=
  by simpa only [fixing_subgroup_union M, subgroup.mem_inf] using m.prop
in let hm' : (⟨↑m, pm.left⟩ : fixing_subgroup M s) ∈
  fixing_subgroup (fixing_subgroup M s)
    (coe ⁻¹' t : set ((sub_mul_action_of_fixing_subgroup M s))) :=
begin
  rw mem_fixing_subgroup_iff ↥(fixing_subgroup M s),
  intros x hx,
  simp only [set.mem_preimage] at hx,
  rw ← set_like.coe_eq_coe,
  conv_rhs { rw ← ((mem_fixing_subgroup_iff _).mp pm.right ↑x hx) },
  refl
end
in ⟨⟨↑m, pm.left⟩, hm'⟩,
  map_one' := rfl,
  map_mul' := λ m n, rfl },
map_smul' := λ m x, rfl }

lemma sub_mul_action_of_fixing_subgroup_union_bihom_def (s t : set α) :
  ∀ (x : (sub_mul_action_of_fixing_subgroup M (s ∪ t))),
  (((sub_mul_action_of_fixing_subgroup_union_bihom M s t).to_fun x) : α) = x := λ x, rfl

lemma sub_mul_action_of_fixing_subgroup_union_bihom_surjective (s t : set α) :
  function.bijective (sub_mul_action_of_fixing_subgroup_union_bihom M s t).to_fun :=
begin
  split,
  { intros a b h,
    simp only [coe_coe, ← set_like.coe_eq_coe],
    simp only [← set_like.coe_eq_coe] at h,
    exact h },
  { rintro ⟨⟨a, ha⟩, ha'⟩, use a,
    { intro hy, cases (set.mem_union a s t).mp hy,
      exact ha h,
      apply ha', simp only [set.mem_preimage, sub_mul_action.coe_mk], exact h },
    refl }
end


lemma sub_mul_action_of_fixing_subgroup_union'_mem {s t : set α}
      (x : α)
      (hx : x ∈ sub_mul_action_of_fixing_subgroup M s)
      (hx' : (⟨x, hx⟩ : sub_mul_action_of_fixing_subgroup M s) ∈
        sub_mul_action_of_fixing_subgroup ↥(fixing_subgroup M s)
          (coe ⁻¹' t : set (sub_mul_action_of_fixing_subgroup M s))) :
      x ∈ sub_mul_action_of_fixing_subgroup M (s ∪ t) :=
begin
  intro hxst,
  cases hxst with hxs hxt,
  exact hx hxs,
  apply hx', use hxt
end

def sub_mul_action_of_fixing_subgroup_union'_bihom (s t : set α) : mul_action_bihom
  (fixing_subgroup (fixing_subgroup M s) (coe ⁻¹' t : set (sub_mul_action_of_fixing_subgroup M s)))
    (sub_mul_action_of_fixing_subgroup (fixing_subgroup M s)
      (coe ⁻¹' t : set(sub_mul_action_of_fixing_subgroup M s)))
  (fixing_subgroup M (s ∪ t)) (sub_mul_action_of_fixing_subgroup M (s ∪ t)) := {
to_fun := λ ⟨⟨x, hx⟩, hx'⟩, ⟨x, sub_mul_action_of_fixing_subgroup_union'_mem M x hx hx'⟩,
to_monoid_hom := {
  to_fun := λ ⟨⟨m, hm⟩, hm'⟩, ⟨m,
  begin
    rintro ⟨x,hxst⟩,
    cases em (x ∈ s) with hxs hxs',
    simp only [subtype.coe_mk], exact hm ⟨x, hxs⟩,
    simp only [subtype.coe_mk],
    let z := hm' ⟨⟨x, hxs'⟩, (or.resolve_left hxst hxs')⟩,
    simp only [subtype.coe_mk] at z,
    rw [← subtype.coe_mk x hxs', ← subtype.coe_mk m hm],
    conv_rhs { rw ← z, }, refl,
  end⟩,
  map_one' := rfl,
  map_mul' := λ ⟨⟨m, mn⟩, hm'⟩ ⟨⟨n,hn⟩, hn'⟩, rfl },
map_smul' := λ ⟨⟨m, hm⟩, hm'⟩ ⟨⟨x, hx⟩, hx'⟩, rfl }

lemma sub_mul_action_of_fixing_subgroup_union'_bihom_def {s t : set α}
      (x : α)
      (hx : x ∈ sub_mul_action_of_fixing_subgroup M s)
      (hx' : (⟨x, hx⟩ : sub_mul_action_of_fixing_subgroup M s) ∈
        sub_mul_action_of_fixing_subgroup ↥(fixing_subgroup M s)
          (coe ⁻¹' t : set (sub_mul_action_of_fixing_subgroup M s))) :
      (sub_mul_action_of_fixing_subgroup_union'_bihom M s t).to_fun ⟨⟨x, hx⟩, hx'⟩ =
        ⟨x, sub_mul_action_of_fixing_subgroup_union'_mem M x hx hx'⟩ := rfl

/-
lemma sub_mul_action_of_fixing_subgroup_union'_bihom_def (s t : set α)
  (x : (sub_mul_action_of_fixing_subgroup (fixing_subgroup M s)
      (coe ⁻¹' t : set(sub_mul_action_of_fixing_subgroup M s)))) :
  (x : α) = (sub_mul_action_of_fixing_subgroup_union'_bihom M s t).to_fun x :=
begin
  revert x, rintro ⟨⟨x, hx⟩, hx'⟩,
  refl,
end
 -/

lemma sub_mul_action_of_fixing_subgroup_union_bihom'_surjective (s t : set α) :
  function.bijective (sub_mul_action_of_fixing_subgroup_union'_bihom M s t).to_fun :=
begin
  split,
  { rintros ⟨⟨a, ha⟩, ha'⟩ ⟨⟨b, hb⟩, hb'⟩ h,
    simp only [subtype.mk_eq_mk],
    unfold sub_mul_action_of_fixing_subgroup_union'_bihom at h,
    simp only [subtype.mk_eq_mk] at h,
    change (sub_mul_action_of_fixing_subgroup_union'_bihom M s t).to_fun ⟨⟨a, ha⟩, ha'⟩ =
      (sub_mul_action_of_fixing_subgroup_union'_bihom M s t).to_fun ⟨⟨b, hb⟩, hb'⟩ at h,
    simp only [sub_mul_action_of_fixing_subgroup_union'_bihom_def, subtype.mk_eq_mk] at h,
    exact h },
  { rintro ⟨x, hx⟩,
    rw mem_sub_mul_action_of_fixing_subgroup_iff at hx,
    use x,
    { intro hs, apply hx, exact set.mem_union_left t hs },
    { rw mem_sub_mul_action_of_fixing_subgroup_iff,
      simp only [set.mem_preimage, sub_mul_action.coe_mk],
      intro ht, apply hx, exact set.mem_union_right s ht },
  simp only [sub_mul_action_of_fixing_subgroup_union'_bihom_def] }
end

lemma fixing_subgroup_of_insert (a : α) (s : set (sub_mul_action_of_stabilizer M α a)) :
  fixing_subgroup M (set.insert a (coe '' s)) =
  (subgroup.map (subgroup.subtype _) (fixing_subgroup ↥(stabilizer M a) s) : subgroup M) :=
begin
  ext m,
  split,
  { intro hm,
    use m,
    { rw mem_stabilizer_iff,
      rw mem_fixing_subgroup_iff at hm,
      apply hm a (set.mem_insert a _) },
    { split,
      simp only [set_like.mem_coe , mem_fixing_subgroup_iff],
      intros y hy,
      rw mem_fixing_subgroup_iff at hm,

      let t : set α := set.insert a (coe '' s),
      suffices : ↑y ∈ t,
      { rw ← set_like.coe_eq_coe,
        conv_rhs { rw ← hm ↑y this},
        refl },
      apply set.mem_insert_of_mem,
      use ⟨y, hy, rfl⟩,
      refl } } ,
  { rintro ⟨n, hn, rfl⟩,
    simp only [subgroup.coe_subtype, set_like.mem_coe, mem_fixing_subgroup_iff] at hn ⊢,
    intros y hy,
    cases set.mem_insert_iff.mp hy with hy hy,
      -- y = a
      rw hy, simpa using n.prop,
      -- y ∈ s
      simp only [set.mem_image] at hy,
      obtain ⟨y, hy1, rfl⟩ := hy,
      conv_rhs { rw ← hn y hy1 },
      refl },
end

lemma sub_mul_action_of_fixing_subgroup_of_insert_eq (a : α) (s : set (sub_mul_action_of_stabilizer M α a)) :
  (sub_mul_action_of_fixing_subgroup M (set.insert a (coe '' s))).carrier =
  coe '' (sub_mul_action_of_fixing_subgroup (stabilizer M a) s).carrier :=
begin
  ext,
  simp only [set.mem_image, sub_mul_action.mem_carrier, set_like.mem_coe],
  split,
  { intro hx,
    rw mem_sub_mul_action_of_fixing_subgroup_iff M at hx,
    suffices : x ≠ a,
    { use x,
      split,
      { rw mem_sub_mul_action_of_fixing_subgroup_iff,
        intro h, apply hx, apply set.mem_insert_of_mem,
        use x,
        apply and.intro h, refl },
      refl } ,
    intro h, apply hx, rw h, apply set.mem_insert  },
    { rintro ⟨y, hy, rfl⟩,
    rw mem_sub_mul_action_of_fixing_subgroup_iff,
    intro hy',
    cases set.mem_insert_iff.mp hy' with h h,
    -- ↑y = a
    exact sub_mul_action_of_stabilizer_neq M α a y h,
    -- ↑y ∈ coe '' s
    simp only [set.mem_image, set_like.coe_eq_coe, exists_eq_right] at h,
    exact (mem_sub_mul_action_of_fixing_subgroup_iff (stabilizer M a)).mp hy h },
end

lemma mem_fixing_subgroup_of_mem {K : subgroup M} {m : K} {s t : set α} (hst : s ≤ t):
  m ∈ fixing_subgroup K t → ↑m ∈ fixing_subgroup M s := λ h x,
  begin
    conv_rhs { rw ← (mem_fixing_subgroup_iff M).mp h x (hst x.prop), },
    refl
  end

def sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom
  (a : α) (s : set (sub_mul_action_of_stabilizer M α a)) :
  mul_action_bihom
    (fixing_subgroup M (insert a (coe '' s) : set α))
      (sub_mul_action_of_fixing_subgroup M (insert a (coe '' s : set α)))
    (fixing_subgroup (stabilizer M a) s)
      (sub_mul_action_of_fixing_subgroup (stabilizer M a) s) := {
to_fun := λ x, ⟨⟨(x : α), begin
  rintro (h : (x : α) = a),
  apply (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop,
  rw h, apply set.mem_insert,
  end⟩,
  λ h, (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop $
    set.mem_insert_of_mem _ ⟨⟨(x : α), _⟩, ⟨h, rfl⟩⟩⟩,
-- Second golfing by KB
/- to_fun := λ x, ⟨⟨(x : α), begin
  rw mem_sub_mul_action_of_stabilizer_iff,
  intro h,
  apply (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop,
  rw h, apply set.mem_insert,
  end⟩,
  begin { intro h,
    apply (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop,
    apply set.mem_insert_of_mem,
    refine ⟨⟨(x : α), _⟩, ⟨h, rfl⟩⟩, }
  end⟩, -/
-- First golfing by KB
/- to_fun := λ x, ⟨⟨(x : α), begin
  rw mem_sub_mul_action_of_stabilizer_iff,
  intro h,
  apply (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop,
  rw h, apply set.mem_insert,
  end⟩,
  begin { rw mem_sub_mul_action_of_fixing_subgroup_iff (stabilizer M a),
    intro h,
    apply (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop,
    apply set.mem_insert_of_mem,
    refine ⟨⟨(x : α), _⟩, ⟨h, rfl⟩⟩, }
  end⟩,
-/
-- Initial version
/- to_fun := λ x,
begin
  suffices : ↑x ∈ sub_mul_action_of_stabilizer M α a,
  use x,
  { rw mem_sub_mul_action_of_fixing_subgroup_iff (stabilizer M a),
    intro h,
    apply (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop,
    apply set.mem_insert_of_mem,
    use x, apply and.intro h, simp only [sub_mul_action.coe_mk] },

  rw mem_sub_mul_action_of_stabilizer_iff,
  intro h,
  apply (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop,
  rw h, apply set.mem_insert
end, -/
to_monoid_hom := {
  to_fun := λ m, ⟨⟨(m : M), begin
    -- rw mem_stabilizer_iff,
    apply (mem_fixing_subgroup_iff M).mp m.prop,
    apply set.mem_insert
  end ⟩, λ ⟨x, hx⟩,
    begin
    simp only [← set_like.coe_eq_coe],
    refine (mem_fixing_subgroup_iff M).mp m.prop _ _,
    apply set.mem_insert_of_mem,
    exact ⟨x, hx, rfl⟩, end ⟩,
  -- Initial version
 /-  to_fun := λ m, begin
    suffices hm : ↑m ∈ stabilizer M a,
    { use ⟨m, hm⟩,
      rw mem_fixing_subgroup_iff,
      intros x hx,
      let hm' := (mem_fixing_subgroup_iff M).mp m.prop,
      rw ← set_like.coe_eq_coe,
      suffices : ↑x ∈ set.insert a (coe '' s),
      conv_rhs { rw ← (mem_fixing_subgroup_iff M).mp m.prop ↑x this },
      refl,
      apply set.mem_insert_of_mem,
      use x, exact ⟨hx, rfl⟩ },
    rw mem_stabilizer_iff,
    apply (mem_fixing_subgroup_iff M).mp m.prop,
    apply set.mem_insert,
  end, -/
  map_one' := rfl,
  map_mul' := λ m n, rfl },
map_smul' := λ m x, rfl
}

lemma sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom_bijective
  (a : α) (s : set (sub_mul_action_of_stabilizer M α a)) :
  function.bijective (sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom M a s).to_fun :=
begin
  split,
  { intros x y h,
    rw ← set_like.coe_eq_coe,
    suffices hx : (↑x : α) = ↑((sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom M a s).to_fun x),
    suffices hy : (↑y : α) = ↑((sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom M a s).to_fun y),
    rw hx, rw hy, rw h,
    refl, refl },
  { rintro ⟨⟨x, hx1⟩, hx2⟩,
    refine ⟨⟨x, _⟩, rfl⟩,
    -- ⊢ x ∈ sub_mul_action_of_fixing_subgroup M (insert a (coe '' s))
    rw mem_sub_mul_action_of_fixing_subgroup_iff,
    intro h, cases set.mem_insert_iff.mp h,
    { rw mem_sub_mul_action_of_stabilizer_iff at hx1, exact hx1 h_1 },
    { rw mem_sub_mul_action_of_fixing_subgroup_iff at hx2,
      apply hx2,
      obtain ⟨x1, hx1', rfl⟩ := h_1,
      simp only [set_like.eta],
      exact hx1' } },
end


def sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom'
  (a : α) (s : set (sub_mul_action_of_stabilizer M α a)) :
  mul_action_bihom
    (fixing_subgroup (stabilizer M a) s)
      (sub_mul_action_of_fixing_subgroup (stabilizer M a) s)
    (fixing_subgroup M (set.insert a (coe '' s) : set α))
      (sub_mul_action_of_fixing_subgroup M (insert a (coe '' s : set α))) := {
to_fun := λ x, ⟨(x : α), begin
  intro h,
  cases (set.mem_insert_iff).mp h with h h,
  { apply (mem_sub_mul_action_of_stabilizer_iff _ _ _ _).mp x.val.prop,
    simpa only using h, },
  { apply (mem_sub_mul_action_of_fixing_subgroup_iff _).mp x.prop,
    obtain ⟨y, hy, hy'⟩ := h,
    simp only [coe_coe, set_like.coe_eq_coe] at hy',
    rw ← hy', exact hy },
  end⟩,
to_monoid_hom := {
  to_fun := λ m, ⟨(m : M), λ ⟨y, hy⟩,  begin
    simp only [coe_coe, subtype.coe_mk],
    cases (set.mem_insert_iff).mp hy with hy hy,
    { rw hy,
      conv_rhs { rw ← (mem_stabilizer_iff).mp m.val.prop },
      refl },
    { obtain ⟨z, hz, rfl⟩ := hy,
      conv_rhs { rw ← (mem_fixing_subgroup_iff (stabilizer M a)).mp m.prop z hz },
      refl } end ⟩,
  map_one' := rfl,
  map_mul' := λ m n, rfl },
map_smul' := λ m x, rfl
}

lemma sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom'_bijective
  (a : α) (s : set (sub_mul_action_of_stabilizer M α a)) :
  function.bijective (sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom' M a s).to_fun :=
begin
  split,
  { intros x y h,
    suffices hx : (↑x : α) = ((sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom' M a s).to_fun x),
    suffices hy : (↑y : α) = ↑((sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom' M a s).to_fun y),
    simp only [← set_like.coe_eq_coe, ← coe_coe],
    rw hx, rw hy, rw h,
    refl, refl },
  { rintro ⟨x,hx⟩, -- ⟨x, hx1⟩, hx2⟩,
    suffices : x ∈ sub_mul_action_of_stabilizer M α a,
    use x,
    { intro h, apply hx, apply set.mem_insert_of_mem,
      use x, apply and.intro h, refl },
    refl,
    { intro h, simp only [set.mem_singleton_iff] at h,
      apply hx, rw h, apply set.mem_insert } },
end


def sub_mul_action_of_fixing_subgroup_of_singleton_bihom (a : α)  :
  mul_action_bihom
    (fixing_subgroup M ({a} : set α)) (sub_mul_action_of_fixing_subgroup M ({a} : set α))
    (stabilizer M a) (sub_mul_action_of_stabilizer M α a) := {
to_fun := λ ⟨x, hx⟩, ⟨x, by simpa using hx⟩,
to_monoid_hom := {
  to_fun := λ ⟨m, hm⟩, ⟨m, ((mem_fixing_subgroup_iff M).mp hm) a (set.mem_singleton a)⟩,
  map_one' := rfl,
  map_mul' := λ ⟨m, hm⟩ ⟨n, hn⟩, rfl },
map_smul' := λ ⟨m, hm⟩ ⟨x, hx⟩, rfl  }

lemma sub_mul_action_of_fixing_subgroup_of_singleton_bihom_bijective (a : α) :
  function.bijective (sub_mul_action_of_fixing_subgroup_of_singleton_bihom M a).to_fun :=
begin
  split,
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy, exact hxy },
  { rintro ⟨x, hx⟩, use x, refl },
end

def sub_mul_action_of_fixing_subgroup_of_singleton_bihom' (a : α)  :
  mul_action_bihom
    (stabilizer M a) (sub_mul_action_of_stabilizer M α a)
    (fixing_subgroup M ({a} : set α))
      (sub_mul_action_of_fixing_subgroup M ({a} : set α)) := {
to_fun := λ x, ⟨(x : α), λ h, x.prop h⟩,
to_monoid_hom := {
  to_fun := λ ⟨m, hm⟩, ⟨(m : M), λ ⟨y, hy⟩,
  begin
    simp only [subtype.coe_mk],
    rw (set.mem_singleton_iff.mp hy),
    exact mem_stabilizer_iff.mp hm
  end ⟩,
  map_one' := rfl,
  map_mul' := λ ⟨m, hm⟩ ⟨n, hn⟩, rfl },
map_smul' := λ ⟨m, hm⟩ x, rfl }


lemma sub_mul_action_of_fixing_subgroup_of_singleton_bihom'_bijective (a : α) :
  function.bijective (sub_mul_action_of_fixing_subgroup_of_singleton_bihom' M a).to_fun :=
begin
  split,
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy, exact hxy },
  { rintro ⟨x, hx⟩, use x, refl },
end


/-- If the fixing_subgroup of `s` is `G`, then the fixing_subgroup of `g • x` is `gGg⁻¹`. -/
lemma fixing_subgroup_smul_eq_fixing_subgroup_map_conj (g : M) (s : set α) :
  (fixing_subgroup M (g • s) = (fixing_subgroup M s).map (mul_aut.conj g).to_monoid_hom) :=
begin
  ext h,
  split,
  { intro hh,
    use (mul_aut.conj g⁻¹) h,
    simp,
    split,
    rintro ⟨x, hx⟩,
    simp only [subtype.coe_mk, ← smul_smul],
    rw inv_smul_eq_iff,
    simpa only [subtype.coe_mk] using hh ⟨_, set.smul_mem_smul_set hx⟩,
    group,  },
  { rintro ⟨k, hk, rfl⟩,
    rintro ⟨x, hx⟩,
    simp only [mul_equiv.coe_to_monoid_hom, mul_aut.conj_apply, subtype.coe_mk, ← smul_smul],
    rw smul_eq_iff_eq_inv_smul,
    exact hk ⟨_, mem_smul_set_iff_inv_smul_mem.mp hx⟩ }
end

def sub_mul_action_of_fixing_subgroup_conj_bihom {s t : set α} {g : M} (hst : g • s = t) :
  mul_action_bihom
    (fixing_subgroup M s) (sub_mul_action_of_fixing_subgroup M s)
    (fixing_subgroup M t) (sub_mul_action_of_fixing_subgroup M t) := {
to_fun := λ ⟨x, hx⟩, ⟨g • x,
begin
  intro hgxt, apply hx,
  rw ← hst at hgxt,
  exact smul_mem_smul_set_iff.mp  hgxt,
end⟩,
to_monoid_hom := {
  to_fun := λ ⟨m, hm⟩, ⟨(mul_aut.conj g) m,
  begin
    rw ← hst,
    rw fixing_subgroup_smul_eq_fixing_subgroup_map_conj ,
    use m, apply and.intro hm, refl,
  end⟩,
  map_one' :=
  begin
    rw ← subtype.coe_inj,
    exact (mul_aut.conj g).to_monoid_hom.map_one',
  end,
  map_mul' := λ ⟨m, hm⟩ ⟨n, hn⟩,
  begin
    rw ← subtype.coe_inj,
    apply (mul_aut.conj g).to_monoid_hom.map_mul',
  end },
map_smul' := λ ⟨m, hm⟩ ⟨x, hx⟩,
begin
  simp,
  rw ← set_like.coe_eq_coe,
  change _ • (g • x) = g • (m • x),
  suffices : ((mul_aut.conj g).to_monoid_hom m) • (g • x) = g • (m • x),
  rw ← this, refl,
  simp only [mul_equiv.coe_to_monoid_hom, mul_aut.conj_apply, ← mul_smul],
  refine congr_arg2 _ _ rfl,
  apply inv_mul_cancel_right,
end }

lemma sub_mul_action_of_fixing_subgroup_conj_bihom_bijective {s t : set α} {g : M}
  (hst : g • s = t) :
  function.bijective (sub_mul_action_of_fixing_subgroup_conj_bihom M hst).to_fun :=
begin
  split,
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy,
    simp only [subtype.mk_eq_mk],
    rw ← set_like.coe_eq_coe at hxy,
    change g • x = g • y at hxy,
    apply (mul_action.injective g) hxy },
  { rintro ⟨x, hx⟩,
    have hst' : g⁻¹ • t = s, {
      apply symm, rw ← inv_smul_eq_iff, rw inv_inv,
      exact hst },
    use (sub_mul_action_of_fixing_subgroup_conj_bihom M hst').to_fun ⟨x, hx⟩,

    rw ← set_like.coe_eq_coe,
    change g • g⁻¹ • x = x,
    rw [← mul_smul, mul_inv_self, one_smul] }
end


def sub_mul_action_of_stabilizer_conj_bihom {a b : α} {g : M} (hab : g • a = b) :
  mul_action_bihom
    (stabilizer M a) (sub_mul_action_of_stabilizer M α a)
    (stabilizer M b) (sub_mul_action_of_stabilizer M α b) := {
to_fun := λ ⟨x, hx⟩, ⟨g • x,
begin
  intro hy,
  simp only [set.mem_singleton_iff] at hy,
  rw ← hab at hy,
  apply hx,
  simp only [set.mem_singleton_iff],
  exact mul_action.injective g hy,
end⟩,
to_monoid_hom := {
  to_fun := λ ⟨m, hm⟩, ⟨(mul_aut.conj g) m,
  begin
    rw ← hab, rw stabilizer_smul_eq_stabilizer_map_conj ,
    use m, apply and.intro hm, refl,
  end⟩,
  map_one' :=
  begin
    rw ← subtype.coe_inj,
    exact (mul_aut.conj g).to_monoid_hom.map_one',
  end,
  map_mul' := λ ⟨m, hm⟩ ⟨n, hn⟩,
  begin
    rw ← subtype.coe_inj,
    apply (mul_aut.conj g).to_monoid_hom.map_mul',
  end },
map_smul' := λ ⟨m, hm⟩ ⟨x, hx⟩,
begin
  simp,
  rw ← set_like.coe_eq_coe,
  change _ • (g • x) = g • (m • x),
  suffices : ((mul_aut.conj g).to_monoid_hom m) • (g • x) = g • (m • x),
  rw ← this, refl,
  simp only [mul_equiv.coe_to_monoid_hom, mul_aut.conj_apply, ← mul_smul],
  refine congr_arg2 _ _ rfl,
  apply inv_mul_cancel_right,
end }

def sub_mul_action_of_stabilizer_conj_bihom_bijective {a b : α} {g : M} (hab : g • a = b) :
  function.bijective (sub_mul_action_of_stabilizer_conj_bihom M hab).to_fun :=
begin
  split,
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy,
    simp only [subtype.mk_eq_mk],
    rw ← set_like.coe_eq_coe at hxy,
    change g • x = g • y at hxy,
    apply (mul_action.injective g) hxy },
  { rintro ⟨x, hx⟩,
    have hab' : g⁻¹ • b = a, {
      apply symm, rw ← inv_smul_eq_iff, rw inv_inv,
      exact hab,
      },
    use (sub_mul_action_of_stabilizer_conj_bihom M hab').to_fun ⟨x, hx⟩,

    rw ← set_like.coe_eq_coe,
    change g • g⁻¹ • x = x,
    rw [← mul_smul, mul_inv_self, one_smul] }
end

variables {N β : Type*} [group N] [mul_action N β]

-- version initiale : s = j.to_fun ⁻¹' t
-- il faut : j.to_fun '' sᶜ ⊆ tᶜ
-- t ⊆ j.to_fun '' s
-- ou j.to_fun ⁻¹' t ⊆ s

def mul_action_bihom_of_fixing_subgroup_of_bihom
  (j : mul_action_bihom M α N β)
  {s : set α} {t : set β}
  (hj : t ⊆ set.range j.to_fun) (hst : j.to_fun ⁻¹' t ⊆ s) :
  mul_action_bihom
    (fixing_subgroup M s) (sub_mul_action_of_fixing_subgroup M s)
    (fixing_subgroup N t) (sub_mul_action_of_fixing_subgroup N t) := {
to_fun := λ ⟨x, hx⟩, ⟨j.to_fun x, λ h, hx (hst (set.mem_preimage.mpr h))⟩,
to_monoid_hom := {
  to_fun := λ ⟨m, hm⟩, ⟨j.to_monoid_hom m, λ ⟨y, hy⟩,
  begin
    obtain ⟨x, rfl⟩ := hj hy,
    simp only [subtype.coe_mk],
    rw [j.map_smul'],
    apply congr_arg,
    rw mem_fixing_subgroup_iff at hm,
    apply hm x,
    apply hst,
    rw set.mem_preimage, exact hy
  end⟩,
  map_one' :=
  begin
    rw ← set_like.coe_eq_coe,
    exact j.to_monoid_hom.map_one',
  end,
  map_mul' := λ ⟨m, hm⟩ ⟨n, hn⟩,
  begin
    rw ← set_like.coe_eq_coe,
    exact j.to_monoid_hom.map_mul' m n
  end },
map_smul' := λ ⟨m, hm⟩ ⟨x, hx⟩,
begin
  rw ← set_like.coe_eq_coe,
  exact j.map_smul' m x,
end }

def mul_action_bihom_of_fixing_subgroup_of_bihom_bijective
  (j : mul_action_bihom M α N β) (hj : function.bijective j.to_fun)
  {s : set α} {t : set β} (hst : j.to_fun ⁻¹' t = s) :
let hj' : t ⊆ set.range j.to_fun :=
subset_trans (set.subset_univ t)
  (subset_of_eq (function.surjective.range_eq (function.bijective.surjective hj)).symm)
in
 function.bijective
  (mul_action_bihom_of_fixing_subgroup_of_bihom M j hj' (subset_of_eq hst)).to_fun :=
begin
  split,
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy,
    simp only [subtype.mk_eq_mk],
    apply function.bijective.injective hj,
    rw ← subtype.mk_eq_mk,
    exact hxy },
  { rintro ⟨x, hx⟩,
    obtain ⟨x', hx'⟩ := (function.bijective.surjective hj) x,
    use x',
    { intro h, apply hx, rw ← hx', rw ← set.mem_preimage,
      rw hst, exact h },
    simp_rw ← hx', refl }
end

section stabilizers

-- variables (G : Type*) [group G] (α : Type*) [mul_action G α]

lemma fixing_subgroup_singleton_eq (a : α) :
  fixing_subgroup M ({a} : set α) = stabilizer M a :=
begin
  ext g, rw mem_fixing_subgroup_iff,
  split,
  intro hg, exact hg a (set.mem_singleton a),
  intros hg x hx, rw (set.mem_singleton_iff.mp hx), exact hg,
end

open_locale pointwise

lemma sub_mul_action_of_normal_closure_of_fixing_eq (H : subgroup M) (s : set α)
  (hHs : ∀ h ∈ H, ∀ x ∈ s, h • x ∈ s) :
  ∀ h ∈ subgroup.normal_closure H.carrier, ∀ x ∈  set.image2 (λ (g : M) (x : α), g • x) ⊤ s,
  h • x ∈  set.image2 (λ (g : M) (x : α), g • x) ⊤ s :=
begin
  intros h hh,
  refine subgroup.closure_induction hh _ _ _ _,
  { dsimp,
    -- rintros g ⟨t, ⟨⟨k,rfl⟩, ⟨t',⟨⟨hkH,rfl⟩,⟨u,hgt⟩⟩⟩⟩⟩ ,
    -- rintros g ⟨t, ⟨⟨n, rfl⟩,⟨u,⟨⟨hk, rfl⟩,⟨p,hpn_eq_gp⟩⟩⟩⟩⟩
    rintros g hg x ⟨m, ⟨y, _, hys, rfl⟩⟩,
    rw smul_smul,
    use g * m, use y,
    apply and.intro (set.mem_univ (g * m)),
    apply and.intro hys,
    refl },
  { rintros x ⟨m, ⟨y, _, hys, rfl⟩⟩,
    dsimp,
    rw smul_smul,
    use 1 * m, use y,
    apply and.intro (set.mem_univ (1 * m)),
    apply and.intro hys,
    refl },
  { dsimp,
    rintros m n hm hn,
    rintros x ⟨k, ⟨y, _, hys, rfl⟩⟩,
    rw ← smul_smul,
    apply hm,
    apply hn, use k, use y,
    apply and.intro (set.mem_univ (1 * m)),
    apply and.intro hys,
    refl, },
  { dsimp, intros m hm,
    rintros x ⟨k,y,_,hys,rfl⟩,
    rw smul_smul,
    use (m⁻¹ * k), use y,
    apply and.intro (set.mem_univ _),
    apply and.intro hys,
    refl }
end

example (s : set M) (hs : ∀ m ∈ s, m⁻¹ ∈ s) :
  (subgroup.closure s).carrier = (submonoid.closure s).carrier :=
begin
  change (subgroup.closure s).to_submonoid.carrier = _,
  rw subgroup.closure_to_submonoid s,
  suffices : s ∪ s⁻¹ = s, rw this,
  apply subset_antisymm,
  { intros m hm, cases hm with hm hm,
    exact hm,
    rw ← inv_inv m,
    apply hs, exact set.mem_inv.mpr hm },
  apply set.subset_union_left,
end

def mul_action_of_group_closure_of_invariant (H : set M) (s : set α)
  (hHs : ∀ (m : M) (hm : m ∈ H), m • s ⊆ s) (hH : ∀ (m : M) (hm : m ∈ H), m⁻¹ ∈ H):
  sub_mul_action (subgroup.closure H) α := {
carrier := s,
smul_mem' := begin
  rintro ⟨c,hc⟩,
  suffices : ∀ (x : α) (hx : x ∈ s), c • x ∈ s,
  intros x hx, exact this x hx,

  suffices : (subgroup.closure H).carrier = (submonoid.closure H).carrier,
  rw [← subgroup.mem_carrier, this, submonoid.mem_carrier] at hc,
  refine submonoid.closure_induction hc _ _ _ ,
  { intros g hg x hx,
    apply(hHs g hg), use ⟨x, ⟨hx, rfl⟩⟩ },
  { intros x hx, simp only [one_smul], exact hx },
  { intros m n hm hn x hx, rw ← smul_smul, apply hm, apply hn, exact hx },

  change (subgroup.closure H).to_submonoid.carrier = _,
  rw subgroup.closure_to_submonoid H,
  suffices : H ∪ H⁻¹ = H, rw this,
  apply subset_antisymm,
  { intros m hm, cases hm with hm hm,
    exact hm,
    rw ← inv_inv m,
    apply hH, exact set.mem_inv.mpr hm },
  apply set.subset_union_left,
end }



end stabilizers


#exit

def sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom (a : α) (s : set α) : mul_action_bihom
  (fixing_subgroup M (set.insert a s : set α)) (sub_mul_action_of_fixing_subgroup M (insert a s))
  (fixing_subgroup (stabilizer M a) (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a)))
    (sub_mul_action_of_fixing_subgroup (stabilizer M a) (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a))) := {
to_fun := λ x,
let px : ↑x ≠ a ∧ ↑x ∉ s :=
begin
  let Hx : ↑x ∈ (sub_mul_action_of_fixing_subgroup M (insert a s)).carrier := x.prop,
  rw sub_mul_action_of_fixing_subgroup_def at Hx,
  simp only [set.mem_compl_eq, set.mem_insert_iff] at Hx,
  push_neg at Hx, exact Hx,
end
in let hx : ↑x ∈ sub_mul_action_of_stabilizer M α a :=
begin
  change ↑x ∈ (sub_mul_action_of_stabilizer M α a).carrier,
  rw sub_mul_action_of_stabilizer_def,
  simp only [set.mem_compl_eq, set.mem_singleton_iff],
  exact px.left
end
in let hx' : (⟨↑x, hx⟩ : sub_mul_action_of_stabilizer M α a) ∈
  sub_mul_action_of_fixing_subgroup
    (stabilizer M a)
    (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a)) :=
begin
  change _ ∈ (sub_mul_action_of_fixing_subgroup ↥(stabilizer M a) (coe ⁻¹' s)).carrier,
  rw sub_mul_action_of_fixing_subgroup_def ,
  simp only [set.mem_compl_eq, set.mem_preimage, sub_mul_action.coe_mk],
  exact px.right
end
in ⟨⟨↑x, hx⟩, hx'⟩,
to_monoid_hom := {
  to_fun := λ m,
  let pm : m • a = a ∧ ↑m ∈ fixing_subgroup M s :=
  begin
    let Hm := m.prop,
    rw mem_fixing_subgroup_iff at Hm ⊢,
    split,
    { refine Hm a _, apply set.mem_insert },
    { intros y hy, refine Hm y _,
      change y ∈ insert a s,
      rw set.mem_insert_iff,
      exact or.intro_right _ hy } end
  in let hm : ↑m ∈ stabilizer M a := mem_stabilizer_iff.mp pm.left
  in let hm' : (⟨↑m, hm⟩ : stabilizer M a) ∈ fixing_subgroup (stabilizer M a)
    (coe ⁻¹' s : set ((sub_mul_action_of_stabilizer M α a))) :=
  begin
    rw mem_fixing_subgroup_iff ↥(stabilizer M a),
    intros y hy,
    simp only [set.mem_preimage] at hy,
    rw ← set_like.coe_eq_coe,
    conv_rhs { rw ← ((mem_fixing_subgroup_iff _).mp pm.right ↑y hy) },
    refl
  end
  in ⟨⟨↑m, hm⟩, hm'⟩,
  map_one' := by refl,
  map_mul' := λ m m', by refl },
map_smul' := λ m a, by refl }




#exit


lemma sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom_def (a : α) (s : set α) :
  ∀ (x : (sub_mul_action_of_fixing_subgroup M (insert a s))),
  (((sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom M a s).to_fun x) : α) = x := λ x, rfl


def sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom' (a : α) (s : set α) : mul_action_bihom
  (fixing_subgroup (stabilizer M a) (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a)))
    (sub_mul_action_of_fixing_subgroup (stabilizer M a) (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a)))
    (fixing_subgroup M (set.insert a s : set α)) (sub_mul_action_of_fixing_subgroup M (insert a s))
:= {
to_fun := λ x,
let px : ↑x ≠ a ∧ ↑x ∉ s :=
begin
  split,
  { let Hxx : ↑↑x ∈ (sub_mul_action_of_stabilizer M α a).carrier := (x : sub_mul_action_of_stabilizer M α a).prop,
    rw sub_mul_action_of_stabilizer_def at Hxx,
    simpa using Hxx },
  { let Hx : ↑x ∈ (sub_mul_action_of_fixing_subgroup ↥(stabilizer M a) (coe ⁻¹' s)).carrier := x.prop,
    rw sub_mul_action_of_fixing_subgroup_def at Hx,
    simpa only [set.mem_compl_eq, set.mem_preimage] using Hx }
end
in let hx : ↑x ∈ sub_mul_action_of_stabilizer M α a :=
begin
  change ↑x ∈ (sub_mul_action_of_stabilizer M α a).carrier,
  rw sub_mul_action_of_stabilizer_def,
  simp only [set.mem_compl_eq, set.mem_singleton_iff],
  exact px.left
end
in let hx' : (⟨↑x, hx⟩ : sub_mul_action_of_stabilizer M α a) ∈
  sub_mul_action_of_fixing_subgroup
    (stabilizer M a)
    (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a)) :=
begin
  change _ ∈ (sub_mul_action_of_fixing_subgroup ↥(stabilizer M a) (coe ⁻¹' s)).carrier,
  rw sub_mul_action_of_fixing_subgroup_def ,
  simp only [set.mem_compl_eq, set.mem_preimage, sub_mul_action.coe_mk],
  exact px.right
end
in ⟨⟨↑x, hx⟩, hx'⟩,
to_monoid_hom := {
  to_fun := λ m,
  let pm : m • a = a ∧ ↑m ∈ fixing_subgroup M s :=
  begin
    let Hm := m.prop,
    rw mem_fixing_subgroup_iff at Hm ⊢,
    split,
    { refine Hm a _, apply set.mem_insert },
    { intros y hy, refine Hm y _,
      change y ∈ insert a s,
      rw set.mem_insert_iff,
      exact or.intro_right _ hy } end
  in let hm : ↑m ∈ stabilizer M a := mem_stabilizer_iff.mp pm.left
  in let hm' : (⟨↑m, hm⟩ : stabilizer M a) ∈ fixing_subgroup (stabilizer M a)
    (coe ⁻¹' s : set ((sub_mul_action_of_stabilizer M α a))) :=
  begin
    rw mem_fixing_subgroup_iff ↥(stabilizer M a),
    intros y hy,
    simp only [set.mem_preimage] at hy,
    rw ← set_like.coe_eq_coe,
    conv_rhs { rw ← ((mem_fixing_subgroup_iff _).mp pm.right ↑y hy) },
    refl
  end
  in ⟨⟨↑m, hm⟩, hm'⟩,
  map_one' := by refl,
  map_mul' := λ m m', by refl },
map_smul' := λ m a, by refl }

lemma sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom_def (a : α) (s : set α) :
  ∀ (x : (sub_mul_action_of_fixing_subgroup M (insert a s))),
  (((sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom M a s).to_fun x) : α) = x := λ x, rfl


/-
let hm : ∀ (m : fixing_subgroup M (set.insert a s : set α)), ↑m ∈ stabilizer M a := λ m,
begin
  simp only [mem_stabilizer_iff],
  let Hm := m.prop,
  rw mem_fixing_subgroup_iff at Hm,
  refine Hm a (set.mem_insert a _)
end in
let hm': ∀ (m : fixing_subgroup M (set.insert a s : set α)),
  (⟨↑m, hm m⟩ : stabilizer M a) ∈ fixing_subgroup (stabilizer M a)
    (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a)) := λ m,
begin
  refine (mem_fixing_subgroup_iff ↥(stabilizer M a)).mpr _,
  intros x hx,
  let Hm := m.prop, rw mem_fixing_subgroup_iff at Hm,
  simp at hx,
  let Hmx := Hm x _,
  { rw ← set_like.coe_eq_coe,
    simp only [sub_mul_action.coe_smul_of_tower],
    conv_rhs { rw ← Hmx },
    refl },
  { apply set.mem_insert_of_mem, exact hx },
end in
λ m, ( ⟨⟨↑m, hm m⟩, hm' m⟩ : fixing_subgroup (stabilizer M a) (coe ⁻¹' s)),

to_fun :=
let ha : ∀ (x : sub_mul_action_of_fixing_subgroup M (insert a s : set α)),
  (x : α) ∈ coe '' (sub_mul_action_of_fixing_subgroup
    (stabilizer M a)
    (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a))).carrier := sorry in
let ha' : ∀ (x : sub_mul_action_of_fixing_subgroup M (insert a s : set α)),

  sorry,
map_smul' := sorry,
  }
-/

end group

section stabilizers

variables (G : Type*) [group G] (α : Type*) [mul_action G α]

lemma fixing_subgroup_singleton_eq (a : α) :
  fixing_subgroup G ({a} : set α) = stabilizer G a :=
begin
  ext g,
  split,
  intro hg, rw mem_fixing_subgroup_iff,
    intros x hx, rw (set.mem_singleton_iff.mp hx), exact hg,
  intro hg, exact (mem_fixing_subgroup_iff G).mp hg a (set.mem_singleton a)
end


end stabilizers

end mul_action

end Actions_on_subsets

variables (G : Type*) [group G] (X : Type*) [decidable_eq X] [mul_action G X]

-- lemma test (s : finset X) (g : G) : g • (s : set X) = (g • s : set X) := rfl


-- At least one of the next two lemmas is redundant
/- Unused
lemma action_on_pairs_of.ne (G : Type*) [group G] (X : Type*) [mul_action G X]
  (a b : X) (h_ab : ({a, b} : set X) ∈ action_on_pairs_of G X) : a ≠ b :=
begin
  obtain ⟨a', b', h, hp ⟩ := h_ab,
  cases em (a' = a) with ha ha',
  { rw ha at hp h,
    have hb : b' = b,
    { let w : b' ∈ {a, b'} := is_in_subpair_right,
      rw ← hp at w,
      cases (is_in_subpair_iff.mp w) with hb' hb',
      exfalso, exact h hb'.symm, exact hb' },
    rw hb at h, exact h,  },
  { have ha : a' = b,
    { let w : a' ∈ {a', b'} := is_in_subpair_left,
      rw ← hp at w,
      cases (is_in_subpair_iff.mp w) with ha'' ha'',
      exfalso, exact ha' ha'', exact ha'' },
    rw ha at ha' h,
    intro h, exact ha' h.symm }
end
-/

/- Unused
lemma action_on_pairs_of.mem_of (G : Type*) [group G] (X : Type*) [mul_action G X]
  (a b : X) (hab : a ≠ b) :
  ({a, b} : set X) ∈ action_on_pairs_of G X :=
begin
  split,
  use b, swap, use a,
  split, exact hab,  refl,
end
-/
/- Does not type and Unusable
lemma action_on_pairs_of.mem_of
  (a b : X) (hab : a ≠ b) :
  ({a, b} : set X) ∈ action_on_pairs_of G X :=
begin
  refine pair.is_mem, exact hab,
end
-/


/- Unused, see .pairs

lemma action_on_pairs_of.mk₀ {G X : Type*} [group G] [mul_action G X]
  (a b : X) (hab : a ≠ b) : action_on_pairs_of G X :=
⟨({a,b} : set X), action_on_pairs_of.mem_of G X a b hab⟩

lemma action_on_pairs_of.mk {G X : Type*} [group G] [mul_action G X]
  {a b : X} (hab : a ≠ b) : action_on_pairs_of G X :=
  pair.mk hab

lemma action_on_pairs_of.def {G : Type*} [group G] {X : Type*} [mul_action G X]
  {a b : X} (hab : a ≠ b) :
  ({a, b} : set X) = ↑(pair.mk hab) := pair.is_def hab
-/

/-
lemma action_on_pairs_of.def₀ (G : Type*) [group G] (X : Type*) [mul_action G X]
  (a b : X) (hab : a ≠ b) : ({a, b} : set X) = (action_on_pairs_of.mk₀ a b  hab : set X) :=
begin
  -- have h : action_on_pairs_of.mk G X a b hab = ⟨({a,b} : set X), action_on_pairs_of.mem_of G X a b hab⟩,
  let x : action_on_pairs_of G X := action_on_pairs_of.mk G X a b hab,
  let hx : ({a,b} : set X) ∈ action_on_pairs_of G X := action_on_pairs_of.mem_of G X a b hab,
  let hx' := x.prop,
  type_check sub_mul_action.carrier  ,
  type_check x.val,
  type_check (↑x : set X),

  have h : (x.val : set X) = {a,b},
    {  simp,  },

--   let h := set_like.coe_mk ({a, b} : set X) hx,

  rw ← set_like.coe_mk ({a, b} : set X)  hx,
  apply subtype.mk_eq_mk.mpr ,

  -- rw ← subtype.val_eq_coe,
  apply set_like.coe_eq_coe.mpr,
  refl,

end -/
