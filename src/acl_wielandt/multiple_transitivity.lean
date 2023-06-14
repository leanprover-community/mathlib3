/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import .sub_mul_actions

import .for_mathlib.stabilizer
import .for_mathlib.pretransitive
import .for_mathlib.partitions
import .for_mathlib.set
import .for_mathlib.cardinal

import .primitive
import .for_mathlib.extensions

import set_theory.cardinal.finite
import group_theory.index
import group_theory.group_action.embedding
import group_theory.specific_groups.alternating
import group_theory.perm.list
import group_theory.perm.cycle.concrete
import .index_normal

/-


import order.hom.basic
import order.bounded_order

-- import group_theory.group_action.fixing_subgroup
-- import field_theory.galois

-- import group_theory.specific_groups.alternating

-- import group_theory.subgroup.pointwise
-- import group_theory.coset
-- import group_theory.quotient_group
-- import group_theory.abelianization
-- import group_theory.group_action.defs
-- import group_theory.group_action.basic
-- import group_theory.group_action.group
-- import group_theory.group_action.conj_act
-- import group_theory.group_action.sub_mul_action

-- import order.partition.finpartition
-- import data.finset.lattice

-- import data.setoid.partition
-- import data.set.basic
-- import data.fintype.basic
-- import order.rel_classes
-- import algebra.big_operators.order
-/


open_locale big_operators pointwise cardinal

open_locale classical


namespace mul_action

section transitivity

section monoid
/- It would be better do have it for has_smul
but the instance does not automatically transfer to subtypes -/
variables {M α : Type*} [monoid M] [mul_action M α]

lemma is_pretransitive_of_submonoid {K : submonoid M} (h : is_pretransitive K α) :
  is_pretransitive M α :=
begin
  let h_eq := h.exists_smul_eq,
  apply is_pretransitive.mk,
  intros x y,
  obtain  ⟨⟨k, hk⟩, hk'⟩ := h_eq x y,
  exact ⟨k, hk'⟩
end

lemma is_pretransitive_of_submonoid_le {G K : submonoid M} (hKG : K ≤ G) (h : is_pretransitive K α) :
  is_pretransitive G α :=
begin
  let h_eq := h.exists_smul_eq,
  apply is_pretransitive.mk,
  intros x y,
  obtain  ⟨⟨k, hk⟩, hk'⟩ := h_eq x y,
  use ⟨k, hKG hk⟩,
  exact hk',
end

end monoid

section group

variables (M α : Type*) [group M] [mul_action M α]

/-- Cardinal of an orbit vs index of stabilizers, in nat.card -/
lemma card_orbit_eq_stabilizer_index {a : α} :
  nat.card (orbit M a) = (stabilizer M a).index :=
begin
  change _ = nat.card (M ⧸ (stabilizer M a)),
  unfold nat.card,
  apply cardinal.to_nat_congr ,
  exact (orbit_equiv_quotient_stabilizer M a),
end

/-- Cardinal vs index of stabilizers, for a pretransitive action, in nat.card -/
lemma stabilizer_index_of_pretransitive (h : is_pretransitive M α) {a : α} :
  (stabilizer M a).index = nat.card α :=
begin
  let heq := h.exists_smul_eq,
  rw ← card_orbit_eq_stabilizer_index,
  apply cardinal.to_nat_congr ,
  refine equiv.mk  (λ x, x) (λ y, ⟨y, begin obtain ⟨g, hg⟩ := heq a y,
    use g, rw ← hg, end⟩) _ _,
  { intro y, simp only [subtype.coe_eta]},
  { intro x, refl, },
end

variables {M α}

lemma is_pretransitive_of_subgroup {K : subgroup M} (h : is_pretransitive K α) :
  is_pretransitive M α :=
begin
  apply is_pretransitive_of_submonoid,
  swap, exact K.to_submonoid,
  exact h,
end

lemma is_pretransitive_of_subgroup_le {G K : subgroup M} (hKG : K ≤ G) (h : is_pretransitive K α) :
  is_pretransitive G α :=
begin
  let h_eq := h.exists_smul_eq,
  apply is_pretransitive.mk,
  intros x y,
  obtain  ⟨⟨k, hk⟩, hk'⟩ := h_eq x y,
  use ⟨k, hKG hk⟩,
  exact hk',
end

end group

end transitivity

section multiple_transitivity

open function.embedding nat mul_action

variables (M α : Type*) [group M] [mul_action M α]

/-- An action of a group on a type α is n-pretransitive if the associated
action on (fin n ↪ α) is pretransitive -/
def is_multiply_pretransitive (n : ℕ) :=
  is_pretransitive M (fin n ↪ α)

/-- The equivariant map from (fin 1 ↪ α) to α -/
def fin_one_to_map : (fin 1 ↪ α) →[M] α := {
  to_fun := λ x, x ⟨0, nat.one_pos⟩,
  map_smul' := λ m x, rfl }

lemma fin_one_to_map_bijective : function.bijective (fin_one_to_map M α) :=
begin
  split,
  { intros x y hxy,
    ext i,
    rw (fin.eq_zero i), exact hxy },
  { intro a, use λ _, a,
    { intros i j hij,
      rw [fin.eq_zero i, fin.eq_zero j] },
    refl }
end

variables {M α}

lemma is_multiply_pretransitive_of_subgroup {n : ℕ} {K : subgroup M}
  (h : is_multiply_pretransitive K α n) : is_multiply_pretransitive M α n :=
begin
  unfold is_multiply_pretransitive at *,
  exact is_pretransitive_of_subgroup h,
end

lemma is_multiply_pretransitive_of_le {n : ℕ} {H K : subgroup M}
  (hHK : K ≤ H) (h : is_multiply_pretransitive K α n) : is_multiply_pretransitive H α n :=
begin
  unfold is_multiply_pretransitive at *,
  refine is_pretransitive_of_subgroup_le hHK h,
end

/-- Given an equivariant map α → β, get an equivariant map on function types (ι ↪ α) → (ι ↪ β)-/
def equivariant_map.embedding_of_equivariant_map {N β : Type*} [group N] [mul_action N β]
  {φ : M → N} {f : α →ₑ[φ] β} (hf : function.injective f) (ι : Type*) :
  (ι ↪ α) →ₑ[φ] (ι ↪ β) := {
to_fun := λ x, ⟨f.to_fun ∘ x.to_fun, hf.comp x.inj'⟩,
map_smul' := λ m x,
begin
  ext i,
  simp only [smul_apply, coe_fn_mk, function.comp_app, to_fun_eq_coe, smul_apply],
  rw f.map_smul',
end }

lemma equivariant_map.embedding_of_equivariant_map_apply {N β : Type*} [group N] [mul_action N β]
  {φ : M → N} {f : α →ₑ[φ] β} (hf : function.injective f) {ι : Type*} {x : ι ↪ α} {i : ι} :
  (equivariant_map.embedding_of_equivariant_map hf ι) x i = f (x i) := rfl

lemma equivariant_map.embedding_of_equivariant_map_is_injective {N β : Type*} [group N] [mul_action N β]
  {φ : M → N} {f : α →ₑ[φ] β} (hf : function.injective f) {ι : Type*} :
  function.injective (equivariant_map.embedding_of_equivariant_map hf ι) :=
begin
  intros x y hxy,
  ext i,
  apply hf,
  simp only [← equivariant_map.embedding_of_equivariant_map_apply hf],
  rw hxy
end

lemma equivariant_map.embedding_of_equivariant_map_is_bijective {N β : Type*} [group N] [mul_action N β]
  {φ : M → N} (f : α →ₑ[φ] β) (hf : function.bijective f) {ι : Type*} :
  function.bijective (equivariant_map.embedding_of_equivariant_map hf.injective ι) :=
begin
  split,
  exact equivariant_map.embedding_of_equivariant_map_is_injective hf.injective,
  intro y,
  obtain ⟨g, hgf, hfg⟩ := function.bijective_iff_has_inverse.mp hf,
  let hg := function.right_inverse.injective hfg,
  use ⟨g ∘ y, function.injective.comp hfg.injective (embedding_like.injective y)⟩,
  ext i,
  rw equivariant_map.embedding_of_equivariant_map_apply,
  simp only [coe_fn_mk, function.comp_app],
  rw hfg
end

/-- Multiple transitivity of an image by an equivariant map of a multiply transitive action -/
lemma is_multiply_pretransitive_of_surjective_map {N β : Type*} [group N] [mul_action N β] {n : ℕ}
  {φ : M → N} {f : α →ₑ[φ] β} (hf : function.surjective f)
  (h : is_multiply_pretransitive M α n) : is_multiply_pretransitive N β n :=
begin
  let h_eq := h.exists_smul_eq,
  apply is_pretransitive.mk,
--  intros x y,
  have aux : ∀ (x : fin n ↪ β), ∃ (x' : fin n ↪ α),
    f ∘ x' = x := λ x,
  begin
    let x' : fin n → α := λi, (hf (x i)).some,
    suffices hx' : function.injective x',
    { use ⟨x', hx'⟩,
      ext i,
      simp only [function.comp_app, to_fun_eq_coe],
      rw ← classical.some_spec (hf (x i)),
      simp only [coe_fn_mk] },
    { intros i i' hi,
      let hi' := congr_arg f hi,
      simp only [(classical.some_spec (hf (x _)))] at hi',
      exact x.inj' hi' }
  end,
  intros x y,
  obtain ⟨x', hx'⟩ := aux x,
  obtain ⟨y', hy'⟩ := aux y,
  obtain ⟨g, hg'⟩ := h_eq x' y',
  use φ g,
  ext i,
  change _ • x i = y i,
  rw [← hx', ← hy'], simp only [function.comp_app],
  simp only [← equivariant_map.to_fun_eq_coe],
  simp_rw ← f.map_smul',
  apply congr_arg,
  rw ← hg',
  simp only [to_fun_eq_coe, smul_apply]
end

lemma is_multiply_pretransitive_of_bijective_map_iff {N β : Type*} [group N] [mul_action N β] {n : ℕ}
  {φ : M → N} {f : α →ₑ[φ] β} (hφ : function.surjective φ) (hf : function.bijective f) :
    is_multiply_pretransitive M α n ↔ is_multiply_pretransitive N β n :=
begin
  split,
  apply is_multiply_pretransitive_of_surjective_map hf.surjective,

  intro hN, let hN_heq := hN.exists_smul_eq,
  apply is_pretransitive.mk,
  intros x y,
  let x' : fin n ↪ β := ⟨f ∘ x, hf.injective.comp x.inj'⟩,
  let y' : fin n ↪ β := ⟨f ∘ y, hf.injective.comp y.inj'⟩,
  obtain ⟨g', hg'⟩ := hN_heq x' y',
  obtain ⟨g, hg⟩ := hφ g',
  use g,
  ext i,
  apply hf.injective,
  simp only [smul_apply], simp only [← equivariant_map.to_fun_eq_coe],
  rw f.map_smul',
  rw hg,
  suffices : f.to_fun (x i) = x' i, rw this,
  suffices : f.to_fun (y i) = y' i, rw this,
  rw ← hg', rw ← hg,
  simp only [monoid_hom.to_fun_eq_coe, smul_apply],
  refl, refl,
end

/-
lemma subgroup_is_multiply_pretransitive_via_bijective_bihom_iff {N β : Type*} [group N] [mul_action N β] {n : ℕ}
  {j : mul_action_bihom M α N β} (hj : function.bijective j.to_fun)
  (hj' : function.surjective j.to_monoid_hom.to_fun)
  {M' : subgroup M}:
  is_multiply_pretransitive M' α n ↔ is_multiply_pretransitive (subgroup.map j.to_monoid_hom M') β n :=
begin
  let N' := subgroup.map j.to_monoid_hom M',
  let k : mul_action_bihom M' α (subgroup.map j.to_monoid_hom M') β := {
  to_fun := j.to_fun,
  to_monoid_hom := (j.to_monoid_hom.restrict M').cod_restrict N' (λ ⟨x, hx⟩,
  begin
    rw monoid_hom.restrict_apply,
    exact subgroup.apply_coe_mem_map j.to_monoid_hom M' ⟨x, hx⟩
  end),
  map_smul' := λ ⟨m, hm⟩ x,
  begin
    simp only [monoid_hom.restrict_apply, subgroup.coe_mk, monoid_hom.cod_restrict_apply],
    change (j.to_monoid_hom m) • (j.to_fun x) = _,
    simp only [j.map_smul'],
    refl
  end },
  have hk : function.bijective k.to_fun := hj,
  have hk' : function.surjective k.to_monoid_hom.to_fun,
  { rintro ⟨n, m, hm, hmn⟩,
    use ⟨m, hm⟩,
    -- rw ← set_like.coe_eq_coe,
    simp only [monoid_hom.restrict_apply, subgroup.coe_mk, monoid_hom.to_fun_eq_coe,
      monoid_hom.cod_restrict_apply, subtype.mk_eq_mk],
    exact hmn },
  apply is_multiply_pretransitive_via_bijective_bihom_iff hk hk',
end -/

/-
lemma subgroup'_is_multiply_pretransitive_via_bijective_bihom_iff {N β : Type*} [group N] [mul_action N β] {n : ℕ}
  {j : mul_action_bihom M α N β} (hj : function.bijective j.to_fun)
  (hj' : function.surjective j.to_monoid_hom.to_fun)
  {N' : subgroup N}:
  is_multiply_pretransitive (subgroup.comap j.to_monoid_hom N') α n ↔ is_multiply_pretransitive N' β n :=
begin
  let M' := subgroup.comap j.to_monoid_hom N',
  suffices : N' = subgroup.map j.to_monoid_hom (subgroup.comap j.to_monoid_hom N'),
  conv_rhs { rw this },
  exact subgroup_is_multiply_pretransitive_via_bijective_bihom_iff hj hj',
  rw subgroup.map_comap_eq_self_of_surjective hj'
end

lemma is_pretransitive_iff_image :
  is_pretransitive M α
  ↔ is_pretransitive
    (monoid_hom.range (mul_action.to_perm_hom M α)) α :=
is_pretransitive_via_bijective_bihom
  (canonical_bihom_bijective M α) (canonical_bihom_monoid_hom_surjective M α)


begin
   let j : mul_action_bihom M α (monoid_hom.range (mul_action.to_perm_hom M α)) α := {
  to_fun := λ x, x,
  to_monoid_hom := {
    to_fun := λ m, ⟨mul_action.to_perm m,
    (by simp only [monoid_hom.mem_range, to_perm_hom_apply, exists_apply_eq_apply])⟩,
    map_one' := begin
      ext, simp only [subgroup.coe_mk, to_perm_apply,
        one_smul, subgroup.coe_one, equiv.perm.coe_one, id.def],
    end,
    map_mul' := λ m n, begin
      ext, simp, rw mul_smul, end },
  map_smul' := λ m x,  begin simp, refl end },

  have hj : function.bijective j.to_fun := function.bijective_id,
  suffices hj' : function.surjective (canonical_bihom).to_monoid_hom.to_fun,
  --  rintro ⟨f, m, rfl⟩, use m, refl,
-/
/-
lemma is_multiply_pretransitive_iff_image {n : ℕ} :
  is_multiply_pretransitive M α n
  ↔ is_multiply_pretransitive
    (monoid_hom.range (mul_action.to_perm_hom M α)) α n :=
begin
  unfold is_multiply_pretransitive is_multiply_pretransitive,

  apply is_pretransitive_via_bijective_bihom
  (embedding_bihom_of_bihom_of_bijective_bijective
    (canonical_bihom M α)
    (canonical_bihom_bijective M α)
    (fin n)) ,
  rw embedding_bihom_of_bihom_of_injective.to_monoid_hom.def,
  apply canonical_bihom_monoid_hom_surjective,
end
 -/

variables (M α)

/-- Any action is 0-pretransitive -/
lemma is_zero_pretransitive : is_multiply_pretransitive M α 0 :=
begin
  apply is_pretransitive.mk,
  intros x y, use 1, rw one_smul,
  ext i, exfalso,
  exact is_empty.false i,
end

/-- An action is 1-pretransitive iff it is pretransitive -/
lemma is_pretransitive_iff_is_one_pretransitive :
  is_pretransitive M α ↔ is_multiply_pretransitive M α 1 :=
begin
  unfold is_multiply_pretransitive,
  rw is_pretransitive_of_bijective_map_iff (function.surjective_id) (fin_one_to_map_bijective M α)
end

/-- An action is 2-pretransitive iff it is two_pretransitive… -/
lemma is_two_pretransitive_iff:
  is_multiply_pretransitive M α 2 ↔
  ∀ (a b c d: α) (hab : a ≠ b) (hcd : c ≠ d),
  ∃ (m : M), m • a = c ∧ m • b = d :=
begin
  have : ∀ i : fin(2), i = 0 ∨ i = 1,
  { rintro ⟨i, hi⟩,
    by_cases hi' : i = 0,
    apply or.intro_left,
    apply fin.eq_of_veq ,
    simp only [fin.val_zero', hi'],
    apply or.intro_right,
    apply fin.eq_of_veq,
    simp only [fin.val_one],
    apply nat.eq_of_lt_succ_of_not_lt ,
    exact hi, simp only [lt_one_iff], exact hi', },
  let f : Π (a b : α) (hab : a ≠ b), (fin(2) ↪ α) :=
    λ a b hab, ⟨λ i, ite (i = 0) a b, begin
    intros i j hij,
    by_cases hi : i = 0,
    by_cases hj : j = 0,
    rw [hi, hj],
    simp only [if_pos hi, if_neg hj] at hij, exfalso, exact hab hij,
    by_cases hj : j = 0,
    simp only [if_neg hi, if_pos hj] at hij,exfalso, exact hab hij.symm,
    rw [or.resolve_left (this i) hi, or.resolve_left (this j) hj],
    end⟩,
  have hf0 : ∀ (a b : α) (hab : a ≠ b), (f a b hab) 0 = a,
  { intros a b hab, refl, },
  have hf1 : ∀ (a b : α) (hab : a ≠ b), (f a b hab) 1 = b,
  { intros a b hab, refl, },
  split,
  { intro h,
    let h' := h.exists_smul_eq,
    intros a b c d hab hcd,
    obtain ⟨m, hm⟩ := h' (f a b hab) (f c d hcd),
    rw [← function.embedding.ext_iff] at hm,
    use m,
    split,
    simpa only [smul_apply, coe_fn_mk, eq_self_iff_true, if_true] using hm 0,
    simpa only [smul_apply, coe_fn_mk, eq_self_iff_true, if_true] using hm 1, },
  { intro h,
    apply is_pretransitive.mk,
    intros u v,
    obtain ⟨m, hm⟩ := h (u 0) (u 1) (v 0) (v 1) _ _,
    use m,
    ext,
    cases this x with hx hx,
    simpa only [hx] using hm.left,
    simpa only [hx] using hm.right,
    rw [ne.def, function.embedding.apply_eq_iff_eq], exact zero_ne_one,
    rw [ne.def, function.embedding.apply_eq_iff_eq], exact zero_ne_one, },
end


/-- An n-pretransitive action is m-pretransitive for any m ≤ n -/
lemma is_multiply_pretransitive_of_higher  {n : ℕ}
  (hn : is_multiply_pretransitive M α n) {m : ℕ} (hmn : m ≤ n)
  (hα : ↑n ≤ part_enat.card α) :
  is_multiply_pretransitive M α m :=
begin
  unfold is_multiply_pretransitive,
  let hn_eq := hn.exists_smul_eq,
  apply is_pretransitive.mk,
  intros x y,
  obtain ⟨x', hx'⟩ := may_extend hmn hα x,
  obtain ⟨y', hy'⟩ := may_extend hmn hα y,
  obtain ⟨g, hg⟩ := hn_eq  x' y',
  use g,
  ext, rw [← hy', ← hx', ← hg], refl
end

/-- Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part)-/
theorem stabilizer.is_multiply_pretransitive'
  (hα' : is_pretransitive M α)
  {n : ℕ} :
  is_multiply_pretransitive M α n.succ ↔
  ∀ (a : α), is_multiply_pretransitive (stabilizer M a) (sub_mul_action.of_stabilizer M a) n :=
begin
  let hα'eq := hα'.exists_smul_eq,
  split,
  { -- if the action is n.succ-multiply transitive,
    -- then the action of sub_mul_action_of_stabilizer is n-multiply transitive
     intros hn a, let hn_eq := hn.exists_smul_eq,
    apply is_pretransitive.mk,
    let j : sub_mul_action.of_stabilizer M a ↪ α := {
      to_fun := λ u, id u,
      inj' := λ x y hxy, by simpa using hxy },

    have : ∀ (x : fin n ↪ sub_mul_action.of_stabilizer M a),
      ∃ (x' : fin n.succ ↪ α),
      (fin.cast_le (nat.le_succ n)).to_embedding.trans x' = x.trans j
      ∧ x' ⟨n, nat.lt_succ_self n⟩ = a,
    { intro x,
      refine may_extend_with (x.trans (subtype _)) a _,
      rintro ⟨u, hu⟩,
      simp only [to_fun_eq_coe, trans_apply, function.embedding.coe_subtype] at hu,
      exact (sub_mul_action.of_stabilizer.neq M a) hu },

    intros x y,
    obtain ⟨x', hx', hx'a⟩ := this x,
    obtain ⟨y', hy', hy'a⟩ := this y,
    obtain ⟨g, hg'⟩ := hn_eq x' y',

    have hg : g ∈ stabilizer M a,
    { rw mem_stabilizer_iff,
      conv_lhs { rw ← hx'a },
      rw [← hy'a, ← hg', smul_apply] },

    use ⟨g, hg⟩,
    ext ⟨i, hi⟩,
    simp only [smul_apply, sub_mul_action.coe_smul_of_tower],
    rw ← function.embedding.ext_iff at hx' hy',
    specialize hx' ⟨i, hi⟩, specialize hy' ⟨i, hi⟩,
    simp only [trans_apply, rel_embedding.coe_fn_to_embedding, fin.cast_le_mk,
      id.def, coe_fn_mk] at hx' hy',
    rw [← hx', ← hy', ← hg'], refl },

  { -- if the action of sub_mul_action.of_stabilizer is n-multiply transitive,
    -- then the action is n.succ-multiply transitive.
    intro hn,

    have aux_fun : ∀ (a : α) (x : fin n.succ ↪ α),
      ∃ (g : M) (x1 : fin n ↪ ↥(sub_mul_action.of_stabilizer M a)),
        (fin.cast_le (nat.le_succ n)).to_embedding.trans (g • x)
          = function.embedding.trans x1 (subtype _)
        ∧ g • (x ⟨n, nat.lt_succ_self n⟩) = a,
    { intros a x,
      obtain ⟨g, hgx⟩ := hα'eq (x ⟨n, nat.lt_succ_self n⟩) a,
      use g,
      have zgx : ∀ (i : fin n),
        g • (x i) ∈ sub_mul_action.of_stabilizer M a,
      { rintros ⟨i, hi⟩,
        rw sub_mul_action.of_stabilizer.mem_iff,
        rw ← hgx,
        simp only [fin.coe_eq_cast_succ, fin.cast_succ_mk, ne.def, smul_left_cancel_iff,
          embedding_like.apply_eq_iff_eq],
        exact ne_of_lt hi },
      let x1 : fin n → sub_mul_action.of_stabilizer M a :=
        λ i, ⟨g • (x i), zgx i⟩,
      use x1,
      { intros i j,
        simp only [subtype.mk_eq_mk, fin.coe_eq_cast_succ, smul_left_cancel_iff,
          embedding_like.apply_eq_iff_eq,
          order_embedding.eq_iff_eq, imp_self] },
      refine and.intro _ hgx,
      { ext i, simp, refl, } },

    apply is_pretransitive.mk,
    intro x, -- gx • x = x1 :: a
    let a := x ⟨n, lt_add_one n⟩,
    obtain ⟨gx, x1, hgx, hga⟩ := aux_fun a x,
    intro y, -- gy • y = y1 :: a
    obtain ⟨gy, y1, hgy, hgb⟩ := aux_fun a y,
    -- g • x1 = y1,

    let hna_eq := (hn a).exists_smul_eq,

    obtain ⟨g, hg⟩ := hna_eq x1 y1,

    use gy⁻¹ * g * gx,
    ext ⟨i, hi⟩,
    rw mul_smul, simp only [smul_apply],
    cases lt_or_eq_of_le (le_of_lt_succ hi) with hi' hi',
    { rw ← function.embedding.ext_iff at hgx hgy hg,
      specialize hgx ⟨i, hi'⟩, specialize hgy ⟨i, hi'⟩, specialize hg ⟨i, hi'⟩,
      simp only [trans_apply, rel_embedding.coe_fn_to_embedding, fin.cast_le_mk, smul_apply,
        function.embedding.coe_subtype] at hgx hgy hg,
      rw [hgx, mul_smul, inv_smul_eq_iff, hgy, ← hg], refl },
    { simp only [hi'],
      rw [hga, mul_smul, inv_smul_eq_iff, hgb],
      rw ← mem_stabilizer_iff, exact set_like.coe_mem g } }
end


/-- Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part)-/
theorem stabilizer.is_multiply_pretransitive
  (hα' : is_pretransitive M α)
  {n : ℕ}
  {a : α}:
  -- (hα0 : ↑n ≤ #α) /- (hα : card_ge α n.succ) -/  :
  is_multiply_pretransitive M α n.succ ↔
  is_multiply_pretransitive (stabilizer M a) (sub_mul_action.of_stabilizer M a) n :=
begin
  let hα'eq := hα'.exists_smul_eq,
  split,
  { -- if the action is n.succ-multiply transitive,
    -- then the action of sub_mul_action_of_stabilizer is n-multiply transitive
    intro hn, let hn_eq := hn.exists_smul_eq,
    apply is_pretransitive.mk,
    let j : sub_mul_action.of_stabilizer M a ↪ α := {
      to_fun := λ u, id u,
      inj' := λ x y hxy, by simpa using hxy },

    have : ∀ (x : fin n ↪ sub_mul_action.of_stabilizer M a),
      ∃ (x' : fin n.succ ↪ α),
      (fin.cast_le (nat.le_succ n)).to_embedding.trans x' = x.trans j
      ∧ x' ⟨n, nat.lt_succ_self n⟩ = a,
    { intro x,
      refine may_extend_with (x.trans (subtype _)) a _,
      rintro ⟨u, hu⟩,
      simp only [to_fun_eq_coe, trans_apply, function.embedding.coe_subtype] at hu,
      exact (sub_mul_action.of_stabilizer.neq M a) hu },

    intros x y,
    obtain ⟨x', hx', hx'a⟩ := this x,
    obtain ⟨y', hy', hy'a⟩ := this y,
    obtain ⟨g, hg'⟩ := hn_eq x' y',

    have hg : g ∈ stabilizer M a,
    { rw mem_stabilizer_iff,
      conv_lhs { rw ← hx'a },
      rw [← hy'a, ← hg', smul_apply] },

    use ⟨g, hg⟩,
    ext ⟨i, hi⟩,
    simp only [smul_apply, sub_mul_action.coe_smul_of_tower],
    rw ← function.embedding.ext_iff at hx' hy',
    specialize hx' ⟨i, hi⟩, specialize hy' ⟨i, hi⟩,
    simp only [trans_apply, rel_embedding.coe_fn_to_embedding, fin.cast_le_mk,
      id.def, coe_fn_mk] at hx' hy',
    rw [← hx', ← hy', ← hg'], refl },


  { -- if the action of sub_mul_action.of_stabilizer is n-multiply transitive,
    -- then the action is n.succ-multiply transitive.
    intro hn,

    have aux_fun : ∀ (a : α) (x : fin n.succ ↪ α),
      ∃ (g : M) (x1 : fin n ↪ ↥(sub_mul_action.of_stabilizer M a)),
        (fin.cast_le (nat.le_succ n)).to_embedding.trans (g • x)
          = function.embedding.trans x1 (subtype _)
        ∧ g • (x ⟨n, nat.lt_succ_self n⟩) = a,
    { intros a x,
      obtain ⟨g, hgx⟩ := hα'eq (x ⟨n, nat.lt_succ_self n⟩) a,
      use g,
      have zgx : ∀ (i : fin n),
        g • (x i) ∈ sub_mul_action.of_stabilizer M a,
      { rintros ⟨i, hi⟩,
        rw sub_mul_action.of_stabilizer.mem_iff,
        rw ← hgx,
        simp only [fin.coe_eq_cast_succ, fin.cast_succ_mk, ne.def, smul_left_cancel_iff,
          embedding_like.apply_eq_iff_eq],
        exact ne_of_lt hi },
      let x1 : fin n → sub_mul_action.of_stabilizer M a :=
        λ i, ⟨g • (x i), zgx i⟩,
      use x1,
      { intros i j,
        simp only [subtype.mk_eq_mk, fin.coe_eq_cast_succ, smul_left_cancel_iff,
          embedding_like.apply_eq_iff_eq,
          order_embedding.eq_iff_eq, imp_self] },
      refine and.intro _ hgx,
      { ext i, simp, refl, } },


    apply is_pretransitive.mk,
    intro x, -- obtain gx : gx • x = x1 :: a
    obtain ⟨gx, x1, hgx, hga⟩ := aux_fun a x,
    intro y, -- obtain gy : gy • y = y1 :: a
    obtain ⟨gy, y1, hgy, hgb⟩ := aux_fun a y,
    -- g • x1 = y1,

    let hna_eq := hn.exists_smul_eq,

    obtain ⟨g, hg⟩ := hna_eq x1 y1,

    use gy⁻¹ * g * gx,
    ext ⟨i, hi⟩,
    rw mul_smul, simp only [smul_apply],
    cases lt_or_eq_of_le (le_of_lt_succ hi) with hi' hi',
    { rw ← function.embedding.ext_iff at hgx hgy hg,
      specialize hgx ⟨i, hi'⟩, specialize hgy ⟨i, hi'⟩, specialize hg ⟨i, hi'⟩,
      simp only [trans_apply, rel_embedding.coe_fn_to_embedding, fin.cast_le_mk, smul_apply,
        function.embedding.coe_subtype] at hgx hgy hg,
      rw [hgx, mul_smul, inv_smul_eq_iff, hgy, ← hg], refl },
    { simp only [hi'],
      rw [hga, mul_smul, inv_smul_eq_iff, hgb],
      rw ← mem_stabilizer_iff, exact set_like.coe_mem g } }
end


/-- The fixator of a subset of cardinal d in a k-transitive action
acts (k-d) transitively on the remaining -/
lemma remaining_transitivity (d : ℕ) (s : set α) (hs : part_enat.card s = d)
  (n : ℕ)
  (h : is_multiply_pretransitive M α n) :
  is_multiply_pretransitive
    (fixing_subgroup M s)
    (sub_mul_action.of_fixing_subgroup M s) (n-d) :=
begin
  cases le_total d n with hdn hnd,
  { apply is_pretransitive.mk,
    intros x y,
    let h_eq := h.exists_smul_eq,

    obtain ⟨z'⟩ := (equiv_fin_of_part_enat_card_eq hs),
    let z := z'.symm,
    have hd' : n = (n - d) + d := (nat.sub_add_cancel hdn).symm,

    obtain ⟨x' : fin n ↪ α, hx'1, hx'2⟩ := may_extend_with' z.to_embedding hd' x,
    obtain ⟨y' : fin n ↪ α, hy'1, hy'2⟩ := may_extend_with' z.to_embedding hd' y,
    obtain ⟨g, hg⟩ := h_eq x' y',

    use g,
    { intro a,
      let i := z.symm a,
      have : z.to_embedding.trans (subtype (s : set α)) i = a,
      by simp only [trans_apply, equiv.to_embedding_apply, equiv.apply_symm_apply,
          function.embedding.coe_subtype],

      simp only [← this],
      conv_lhs { rw ← hx'2, }, rw ← hy'2, rw ← hg,
      simp only [trans_apply, smul_apply] },
    { ext i,
      simp only [smul_apply, sub_mul_action.coe_smul_of_tower],
      have : ((y i) : α) = (y.trans (subtype sᶜ) i : α),
      by simp only [trans_apply, function.embedding.coe_subtype],
      rw this,
      have : ((x i) : α) = (x.trans (subtype sᶜ) i : α),
      by simp only [trans_apply, function.embedding.coe_subtype],
      rw this,

      rw ← function.embedding.ext_iff at hx'1 hy'1,
      simp_rw [← hy'1 i, ← hx'1 i, ← hg],
      simp only [trans_apply, smul_apply, rel_embedding.coe_fn_to_embedding],
      refl } },
  { rw nat.sub_eq_zero_of_le hnd,
    apply is_zero_pretransitive }
end

lemma remaining_transitivity' (s : set α) [fintype s]
  (m n : ℕ)
  (hn : (n : part_enat) ≤ part_enat.card α)
  (hmn : m + fintype.card s ≤ n)
  (h : is_multiply_pretransitive M α n) :
  is_multiply_pretransitive
    (fixing_subgroup M s)
    (sub_mul_action.of_fixing_subgroup M s) m :=
begin
  let d := fintype.card s,
  rw ← nat.add_sub_cancel m d,
  apply remaining_transitivity,
  exact part_enat.of_fintype ↥s,
  apply is_multiply_pretransitive_of_higher,
  exact h,
  exact hmn,
  exact hn,
end


private
lemma index_of_fixing_subgroup_of_multiply_pretransitive_aux (k : ℕ) [fintype α]
    (hmk : is_multiply_pretransitive M α k)
    {s : finset α} (hs : s.card = k) :
    (fixing_subgroup M (s : set α)).index * (fintype.card α - s.card).factorial
    = (fintype.card α).factorial :=
begin
  unfreezingI {revert M α},
  induction k with k hrec,

  -- k = 0
  { introsI M α _ _ _ hmk s hs,
    rw finset.card_eq_zero  at hs,
    simp only [hs, finset.coe_empty, finset.card_empty, tsub_zero],
    suffices : fixing_subgroup M ∅ = ⊤,
    by rw [this, subgroup.index_top, one_mul],
    exact galois_connection.l_bot (fixing_subgroup_fixed_points_gc M α) },

  -- induction step
  introsI M α _ _ _ hmk s hs,
  have hGX : is_pretransitive M α,
  { rw is_pretransitive_iff_is_one_pretransitive,
    apply is_multiply_pretransitive_of_higher M α hmk,
    { rw nat.succ_le_succ_iff, apply nat.zero_le },
    { rw ← hs,
      simp only [part_enat.card_eq_coe_fintype_card, fintype.card_coe, part_enat.coe_le_coe],
      exact finset.card_le_univ s } },
  suffices : s.nonempty,
  obtain ⟨a, has⟩ := finset.nonempty.bex this,
  let t' : set (sub_mul_action.of_stabilizer M a) := coe ⁻¹' (↑(s.erase a) : set α),
  have hat' : (coe '' t' : set α) = s.erase a,
  { simp only [subtype.image_preimage_coe, finset.coe_erase, set_like.mem_coe,
    set.inter_eq_left_iff_subset, set.diff_singleton_subset_iff],
    simp_rw sub_mul_action.of_stabilizer.mem_iff,
    intros x _,
    simp only [set.mem_insert_iff],
    cases em (x = a) with hx hx,
    apply or.intro_left, exact hx,
    apply or.intro_right, exact hx },

--   have hat : a ∉ s.erase a := finset.not_mem_erase a s,
  rw ← finset.insert_erase has,
  rw finset.card_insert_of_not_mem (finset.not_mem_erase a s),
  rw finset.coe_insert,

  rw [nat.add_comm, ← nat.sub_sub],
  -- change (fixing_subgroup M ↑(insert a t)).index * _ = _,
  rw ← hat',

  -- have : insert a (coe '' t') = set.insert a (coe '' t'),
  -- refl, rw this,
  rw fixing_subgroup_of_insert,

  --   H.relindex K = (H.subgroup_of K).index = (K : H ⊓ K)
  -- si H ≤ K, H.relindex K * K.index = H.index
  -- (K : H) (G : K) = (G : H)
  -- (G : Gat) = (G : Ga) (Ga : Gat)
  -- prendre K = Ga, H = Gat
  rw subgroup.index_map,
  rw (monoid_hom.ker_eq_bot_iff (stabilizer M a).subtype).mpr
    (by simp only [subgroup.coe_subtype, subtype.coe_injective]),
  simp only [sup_bot_eq, subgroup.subtype_range],

  suffices : (fixing_subgroup (stabilizer M a) t').index *
      (fintype.card α - 1 - fintype.card t').factorial = (fintype.card α - 1).factorial,
  { suffices ht' : fintype.card t' = (s.erase a).card,
    rw mul_comm at this,
    rw [← ht', mul_comm, ← mul_assoc, mul_comm, this],

    suffices hX : 0 < fintype.card α,
    conv_rhs { rw ← nat.mul_factorial_pred hX },
    apply congr_arg2 (*) _ (rfl),

    { -- (stabilizer G a).index = fintype.card α,
      rw ← nat.card_eq_fintype_card,
      apply stabilizer_index_of_pretransitive M α hGX },
    { -- 0 < fintype.card α,
      rw fintype.card_pos_iff, use a },
    { -- fintype.card α = (s.erase a).card
      rw ← set.to_finset_card,
      rw ← finset.card_image_of_injective t'.to_finset (subtype.coe_injective),
      apply congr_arg,
      rw ← finset.coe_inj,
      rw finset.coe_image,
      rw set.coe_to_finset,
      exact hat' } },

  { let hz := hrec (stabilizer M a) (sub_mul_action.of_stabilizer M a)
        ((stabilizer.is_multiply_pretransitive M α hGX).mp hmk) _,
    swap, exact t'.to_finset,
    swap,
    { rw ← finset.card_image_of_injective t'.to_finset (subtype.coe_injective),
      rw [← set.coe_to_finset t', ← finset.coe_image, finset.coe_inj] at hat',
      rw hat',
      rw [finset.card_erase_of_mem has, hs, nat.sub_one k.succ, nat.pred_succ] },

    suffices : fintype.card (sub_mul_action.of_stabilizer M a) = fintype.card α - 1,
    rw [this, set.coe_to_finset t', set.to_finset_card t'] at hz,
    exact hz,

    change fintype.card (sub_mul_action.of_stabilizer M a).carrier = _,
    rw [sub_mul_action.of_stabilizer.def, fintype.card_compl_set, set.card_singleton] },

  { -- s.nonempty
    rw [← finset.card_pos, hs], exact succ_pos k },
end

/-- For a multiply pretransitive action, computes the index of the fixing_subgroup of a subset -/
theorem index_of_fixing_subgroup_of_multiply_pretransitive [fintype α] (s : set α)
  (hMk : is_multiply_pretransitive M α (fintype.card s)) :
  (fixing_subgroup M s).index * (fintype.card α - fintype.card s).factorial
    = (fintype.card α).factorial :=
begin
  rw ← index_of_fixing_subgroup_of_multiply_pretransitive_aux M α _ hMk (set.to_finset_card s),
  rw set.coe_to_finset s,
  rw ← set.to_finset_card,
end


open_locale classical

/-- A 2-transitive action is primitive -/
theorem is_preprimitive_of_two_pretransitive
  (h2 : is_multiply_pretransitive M α 2) : is_preprimitive M α :=
begin
  cases le_or_gt (part_enat.card α) 1 with hα hα,
  -- Trivial case where subsingleton α
  { rw part_enat.card_le_one_iff_subsingleton at hα,
    resetI,
    apply is_preprimitive.on_subsingleton,/-
    haveI : is_pretransitive M α,
    { apply is_pretransitive.mk,
      intros x y, use 1, exact subsingleton_iff.mp hα _ _ },
    apply is_preprimitive.mk,
    { intros B hB,
      apply or.intro_left,
      exact @set.subsingleton_of_subsingleton _ hα B } -/ },
  -- Important case : 2 ≤ #α
  let hα' := id hα, rw gt_iff_lt at hα',
  rw [← cast_one, ← part_enat.succ_le_iff] at hα',
  haveI : is_pretransitive M α,
  { rw is_pretransitive_iff_is_one_pretransitive,
    apply is_multiply_pretransitive_of_higher M α h2 _ hα',
    norm_num },

  apply is_preprimitive.mk,
  intros B hB,
  cases le_or_gt (part_enat.card B) 1 with h h,
  { -- Case : subsingleton
    apply or.intro_left,
    rw [part_enat.card_le_one_iff_subsingleton, set.subsingleton_coe] at h,
    exact h },
  -- Case : top
  apply or.intro_right,
  unfold part_enat.card at h,
  rw [gt_iff_lt, ← cast_one, ← part_enat.succ_le_iff] at h,
  obtain ⟨x : fin 2 ↪ ↥B⟩ := gimme_some h,
  rw set.top_eq_univ,
  apply set.eq_univ_of_forall,
  intro a,

  cases em (a = x 0) with hca hca',
  rw hca, exact subtype.mem (x 0),
  cases em (a = x 1) with hcb hcb',
  rw hcb, exact subtype.mem (x 1),
  unfold is_multiply_pretransitive at h2, let h2_eq := h2.exists_smul_eq,

  let y : fin 2 → α := λ i, if i.val = 0 then x 0 else a,
  have hy0 : y 0 = x 0, by simp,
  have hy1 : y 1 = a, by simp,
  have : ∀ (i : fin 2), i = 0 ∨ i = 1,
  { rintro ⟨i, hi⟩,
    rw nat.lt_succ_iff at hi,
    cases nat.eq_zero_or_pos i with hi_zero hi_pos,
    { apply or.intro_left,
      change _ = (⟨0,_⟩ : fin 2),
      rw fin.mk.inj_iff , exact hi_zero, },
    { apply or.intro_right,
      change _ = (⟨1,_⟩ : fin 2),
      rw fin.mk.inj_iff, exact le_antisymm hi hi_pos } },
  have hy : function.injective y,
  { intros i j hij,
    cases this i with hi hi;
    cases this j with hj hj;
    simp only [hi, hj, hy0, hy1] at hij ⊢;
    exfalso,
    exact hca' hij.symm,
    exact hca' hij },

  obtain ⟨g : M, hg : g • (x.trans (subtype _))  = ⟨y, hy⟩ ⟩ := h2_eq _ _,
  rw ← function.embedding.ext_iff at hg,
  simp at hg,

  rw [← hy1, ← hg 1, ← inv_inv g,  ← set.mem_smul_set_iff_inv_smul_mem],
  rw is_block.def_mem hB (x 0) g⁻¹ (subtype.mem (x 0)) _ ,
  exact (subtype.mem (x 1)),
  { rw [← hy0, ← hg 0, ← mul_smul, inv_mul_self, one_smul],
    exact subtype.mem (x 0) }
end


section finite

variable (α)

/-- The permutation group on α is pretransitive -/
lemma equiv.perm.is_pretransitive :
  mul_action.is_pretransitive (equiv.perm α) α :=
begin
  apply is_pretransitive.mk,
  intros x y,
  use equiv.swap x y,
  simp only [equiv.perm.smul_def],
  rw equiv.swap_apply_left x y
end

variable  [fintype α]

/-- The permutation group on α is fintype.card α-pretransitive -/
theorem equiv_perm_is_fully_pretransitive :
  mul_action.is_multiply_pretransitive (equiv.perm α) α (fintype.card α):=
begin
  apply is_pretransitive.mk,
  intros x y,
  let x' := equiv.of_bijective x.to_fun _,
  let y' := equiv.of_bijective y.to_fun _,
  use x'.symm.trans y',
  ext i,
  simp only [function.embedding.smul_apply, equiv.perm.smul_def, equiv.coe_trans,
    function.comp_app, equiv.of_bijective_apply, function.embedding.to_fun_eq_coe,
    embedding_like.apply_eq_iff_eq],
  exact x'.left_inv i,
  all_goals { rw fintype.bijective_iff_injective_and_card, split },
  any_goals { try {exact fintype.card_fin (fintype.card α) } },
  exact embedding_like.injective y,
  exact embedding_like.injective x,
end

theorem equiv_perm_is_multiply_pretransitive (n : ℕ) :
  mul_action.is_multiply_pretransitive (equiv.perm α) α n :=
begin
  cases le_or_gt n (fintype.card α) with hn hn,
  { apply is_multiply_pretransitive_of_higher (equiv.perm α) α _ hn,
    apply le_of_eq, rw part_enat.card_eq_coe_fintype_card ,
    apply equiv_perm_is_fully_pretransitive, },
  -- hn : n > fintype.card α
  suffices : is_empty (fin n ↪ α),
  { rw is_multiply_pretransitive,
    apply is_pretransitive.mk,
    intro x,
    exfalso, apply this.false, exact x, },
  apply function.embedding.is_empty_of_card_lt,
  simp only [fintype.card_fin],
  exact hn,
end

/-- The action of the permutation group of α on α is preprimitive -/
theorem equiv.perm.is_preprimitive :
  is_preprimitive (equiv.perm α) α :=
begin
  cases subsingleton_or_nontrivial α; resetI,
  exact is_preprimitive.on_subsingleton,
  apply is_preprimitive_of_two_pretransitive,
  apply is_multiply_pretransitive_of_higher,
  apply equiv_perm_is_fully_pretransitive,
  rw ← fintype.one_lt_card_iff_nontrivial at h,
  exact h,
  apply le_of_eq, rw part_enat.of_fintype,
end


variable {α}
lemma aux_lt_iff_lt_or_eq {m n : ℕ} (hmn : m < n) : (m < n - 1) ∨ (m = n - 1) :=
begin
  rw nat.lt_iff_le_not_le,
  cases dec_em (m = n - 1) with h h',
  { exact or.intro_right _ h },
  { apply or.intro_left, apply and.intro,
    { exact nat.le_pred_of_lt hmn},
    { intro h, apply h',
      exact nat.le_antisymm (nat.le_pred_of_lt hmn) h } },
end


/-- A subgroup of equiv.perm α is ⊤ iff it is (fintype.card α - 1)-pretransitive -/
theorem eq_top_of_is_full_minus_one_pretransitive {G : subgroup (equiv.perm α)}
  (hmt : is_multiply_pretransitive ↥G α (fintype.card α - 1)) :
  G = ⊤ :=
begin
  let j : fin (fintype.card α - 1) ↪ fin (fintype.card α) :=
    (fin.cast_le ((fintype.card α).sub_le 1)).to_embedding,
  rw eq_top_iff, intros k _,
  let x : fin(fintype.card α) ↪ α := (fintype.equiv_fin_of_card_eq rfl).symm.to_embedding,
  let hmt_eq := hmt.exists_smul_eq,
  let x' := j.trans x,
  obtain ⟨g, hg'⟩ := hmt_eq x' (k • x'),
  suffices : k = g, { rw this, exact set_like.coe_mem g },

  have hx : ∀ (x : fin(fintype.card α) ↪ α), function.surjective x.to_fun,
  { intro x,
    suffices : function.bijective x.to_fun, exact this.right,
    rw fintype.bijective_iff_injective_and_card,
    exact ⟨embedding_like.injective x, fintype.card_fin (fintype.card α)⟩ },

  have hgk' : ∀ (i : fin (fintype.card α)) (hi : i.val < fintype.card α - 1), (g • x) i = (k • x) i,
  { intros i hi,
    simpa using congr_fun (congr_arg coe_fn hg') ⟨i.val, hi⟩ },
  have hgk : ∀ (i : fin (fintype.card α)), (g • x) i = (k • x) i,
  { intro i,
    cases aux_lt_iff_lt_or_eq i.prop with hi hi,
    { exact hgk' i hi },
    { obtain ⟨j, hxj : (k • x) j = (g • x) i⟩ := hx (k • x) ((g • x) i),
      cases aux_lt_iff_lt_or_eq j.prop with hj hj,
      { exfalso,
        suffices : i = j,
        { rw [← this, ← hi] at hj, refine lt_irrefl _ hj },
        apply embedding_like.injective (g • x),
        rw hgk' j hj, rw hxj },
      { rw ← hxj,
        apply congr_arg,
        rw [fin.eq_iff_veq, hi, hj] } } },

  apply equiv.perm.ext, intro a,
  obtain ⟨i, rfl⟩ := (hx x) a,
  let zi := hgk i,
  simp only [function.embedding.smul_apply, equiv.perm.smul_def] at zi,
  simp only [function.embedding.to_fun_eq_coe],
  rw ← zi,
  refl
end

variable (α)

-- Cette instance n'était pas nécessaire,
-- mais sans elle, Lean utilise des classical dont il ne se dépêtre plus après !
-- (cf alternating_iwasawa)
variable [decidable_eq α]

/-- The alternating group on α is (fintype.card α - 2)-pretransitive -/
theorem alternating_group_is_fully_minus_two_pretransitive :
  mul_action.is_multiply_pretransitive (alternating_group α) α (fintype.card α - 2) :=
begin
  cases lt_or_ge (fintype.card α) 2 with h2 h2,
  { rw nat.sub_eq_zero_of_le (le_of_lt h2),
    apply is_zero_pretransitive },
  -- fintype.card α ≥ 2
  obtain ⟨n,hn⟩ := nat.le.dest h2,
  have hn' : fintype.card α - 2 = n := norm_num.sub_nat_pos (fintype.card α) 2 n hn,
  rw add_comm at hn,
  have hn_le : n ≤ fintype.card α, { rw ← hn, exact le_self_add },

  apply is_pretransitive.mk,
  rw hn',
  intros x y,

  obtain ⟨x', hx'⟩ :=
    may_extend hn_le (le_of_eq (part_enat.of_fintype α).symm) x,
  obtain ⟨y', hy'⟩ :=
    may_extend hn_le (le_of_eq (part_enat.of_fintype α).symm) y,
  let heq := (equiv_perm_is_fully_pretransitive α).exists_smul_eq,
  obtain ⟨g, hg⟩ := heq x' y',
  cases int.units_eq_one_or g.sign with h h,
  { use ⟨g, equiv.perm.mem_alternating_group.mpr h⟩,
    ext i,
    simp only [function.embedding.smul_apply],
    rw [← hx', ← hy', ← hg],
    refl },
  { have hg'1 : n + 1 < fintype.card α,
    { rw ← hn, exact nat.lt.base (n + 1) },
    have hg'2 : n < fintype.card α,
    { apply lt_trans _ hg'1, exact lt_add_one n },

    let g' := equiv.swap (y'.to_fun ⟨n+1, hg'1⟩) (y'.to_fun ⟨n, hg'2⟩),

    have hg' : g'.sign = -1,
    { rw equiv.perm.is_swap.sign_eq,
      use (y'.to_fun ⟨n+1, hg'1⟩), use (y'.to_fun ⟨n, hg'2⟩),
      simp only [to_fun_eq_coe, ne.def, embedding_like.apply_eq_iff_eq, fin.mk_eq_mk,
        nat.succ_ne_self, not_false_iff, true_and],
      refl, },

    use g' * g,
    { rw equiv.perm.mem_alternating_group,
      simp only [equiv.perm.sign_mul, h, hg'],
      norm_num },
    ext i, simp only [function.embedding.smul_apply],
    rw [← hx', ← hy', ← hg],
    simp only [function.embedding.trans_apply, rel_embedding.coe_fn_to_embedding,
      function.embedding.smul_apply, equiv.perm.smul_def],

    change (g' * g) • _ = _,
    rw ← smul_smul,
    simp,
    change (equiv.swap (y'.to_fun ⟨n+1, hg'1⟩) (y'.to_fun ⟨n, hg'2⟩))  _ = _,

    refine equiv.swap_apply_of_ne_of_ne _ _,
    { rw ← hg,
      intro h,
      simp only [function.embedding.to_fun_eq_coe, function.embedding.smul_apply,
        equiv.perm.smul_def, embedding_like.apply_eq_iff_eq] at h,
      apply (lt_iff_not_ge _ _).mp i.prop,
      convert le_succ n,
      simpa using fin.veq_of_eq h, },
    { rw ← hg,
      intro h,
      simp only [function.embedding.to_fun_eq_coe, function.embedding.smul_apply,
        equiv.perm.smul_def, embedding_like.apply_eq_iff_eq] at h,
      apply (lt_iff_not_ge _ _).mp i.prop,
      apply ge_of_eq,
      simpa using fin.veq_of_eq h, }, },
end
/-

variable {α}
lemma aux_lt_iff_lt_or_eq {m n : ℕ} (hmn : m < n) : (m < n - 1) ∨ (m = n - 1) :=
begin
  rw nat.lt_iff_le_not_le,
  cases dec_em (m = n - 1) with h h',
  { exact or.intro_right _ h },
  { apply or.intro_left, apply and.intro,
    { exact nat.le_pred_of_lt hmn},
    { intro h, apply h',
      exact nat.le_antisymm (nat.le_pred_of_lt hmn) h } },
end


/-- A subgroup of equiv.perm α is ⊤ iff it is (fintype.card α - 1)-pretransitive -/
theorem is_fully_minus_one_pretransitive_iff {G : subgroup (equiv.perm α)}
  (hmt : is_multiply_pretransitive ↥G α (fintype.card α - 1)) :
  G = ⊤ :=
begin
  let j : fin (fintype.card α - 1) ↪ fin (fintype.card α) :=
    (fin.cast_le ((fintype.card α).sub_le 1)).to_embedding,
  rw eq_top_iff, intros k _,
  let x : fin(fintype.card α) ↪ α := (fintype.equiv_fin_of_card_eq rfl).symm.to_embedding,
  let hmt_eq := hmt.exists_smul_eq,
  let x' := j.trans x,
  obtain ⟨g, hg'⟩ := hmt_eq x' (k • x'),
  suffices : k = g, { rw this, exact set_like.coe_mem g },

  have hx : ∀ (x : fin(fintype.card α) ↪ α), function.surjective x.to_fun,
  { intro x,
    suffices : function.bijective x.to_fun, exact this.right,
    rw fintype.bijective_iff_injective_and_card,
    exact ⟨embedding_like.injective x, fintype.card_fin (fintype.card α)⟩ },

  have hgk' : ∀ (i : fin (fintype.card α)) (hi : i.val < fintype.card α - 1), (g • x) i = (k • x) i,
  { intros i hi,
    simpa using congr_fun (congr_arg coe_fn hg') ⟨i.val, hi⟩ },
  have hgk : ∀ (i : fin (fintype.card α)), (g • x) i = (k • x) i,
  { intro i,
    cases aux_lt_iff_lt_or_eq i.prop with hi hi,
    { exact hgk' i hi },
    { obtain ⟨j, hxj : (k • x) j = (g • x) i⟩ := hx (k • x) ((g • x) i),
      cases aux_lt_iff_lt_or_eq j.prop with hj hj,
      { exfalso,
        suffices : i = j,
        { rw [← this, ← hi] at hj, refine lt_irrefl _ hj },
        apply embedding_like.injective (g • x),
        rw hgk' j hj, rw hxj },
      { rw ← hxj,
        apply congr_arg,
        apply fin.ext,
        rw [hi, hj] } } },

  apply equiv.perm.ext, intro a,
  obtain ⟨i, rfl⟩ := (hx x) a,
  let zi := hgk i,
  simp only [function.embedding.smul_apply, equiv.perm.smul_def] at zi,
  simp only [function.embedding.to_fun_eq_coe],
  rw ← zi,
  refl
end

variable (α)
/-- The alternating group on α is (fintype.card α - 2)-pretransitive -/
theorem alternating_group_is_fully_minus_two_pretransitive :
  mul_action.is_multiply_pretransitive (alternating_group α) α (fintype.card α - 2) :=
begin
  cases lt_or_ge (fintype.card α) 2 with h2 h2,
  { rw nat.sub_eq_zero_of_le (le_of_lt h2),
    apply is_zero_pretransitive },
  -- fintype.card α ≥ 2
  obtain ⟨n,hn⟩ := nat.le.dest h2,
  have hn' : fintype.card α - 2 = n := norm_num.sub_nat_pos (fintype.card α) 2 n hn,
  rw add_comm at hn,
  have hn_le : n ≤ fintype.card α, { rw ← hn, exact le_self_add },

  apply is_pretransitive.mk,
  rw hn',
  intros x y,

  obtain ⟨x', hx'⟩ :=
    may_extend hn_le (le_of_eq (part_enat.of_fintype α).symm) x,
  obtain ⟨y', hy'⟩ :=
    may_extend hn_le (le_of_eq (part_enat.of_fintype α).symm) y,
  let heq := (equiv_perm_is_fully_pretransitive α).exists_smul_eq,
  obtain ⟨g, hg⟩ := heq x' y',
  cases int.units_eq_one_or g.sign with h h,
  { use ⟨g, equiv.perm.mem_alternating_group.mpr h⟩,
    ext i,
    simp only [function.embedding.smul_apply],
    rw [← hx', ← hy', ← hg],
    refl },
  { have hg'1 : n + 1 < fintype.card α,
    { rw ← hn, exact nat.lt.base (n + 1) },
    have hg'2 : n < fintype.card α,
    { apply lt_trans _ hg'1, exact lt_add_one n },

    let g' := equiv.swap (y'.to_fun ⟨n+1, hg'1⟩) (y'.to_fun ⟨n, hg'2⟩),

    have hg' : g'.sign = -1,
    { rw equiv.perm.is_swap.sign_eq,
      unfold equiv.perm.is_swap,
      use (y'.to_fun ⟨n+1, hg'1⟩), use (y'.to_fun ⟨n, hg'2⟩),
      split,
      { intro h,
        let h' := function.embedding.injective y' h,
        simp only [subtype.mk_eq_mk] at h',
        exact nat.succ_ne_self _ h' },
      refl },

    use g' * g,
    { rw equiv.perm.mem_alternating_group,
      simp only [equiv.perm.sign_mul, h, hg'],
      norm_num },
    ext i, simp only [function.embedding.smul_apply],
    rw [← hx', ← hy', ← hg],

      simp only [function.embedding.trans_apply, rel_embedding.coe_fn_to_embedding,
        function.embedding.smul_apply, equiv.perm.smul_def],

    change (g' * g) • _ = _,
    rw ← smul_smul,
    simp,
    change (equiv.swap (y'.to_fun ⟨n+1, hg'1⟩) (y'.to_fun ⟨n, hg'2⟩))  _ = _,

    refine equiv.swap_apply_of_ne_of_ne _ _,
    { rw ← hg,
      intro h,
      simp only [function.embedding.to_fun_eq_coe, function.embedding.smul_apply,
        equiv.perm.smul_def, embedding_like.apply_eq_iff_eq] at h,
      let h' := fin.veq_of_eq h,
      simp only [fin.val_eq_coe, fin.coe_cast_le] at h',
      let hi := i.prop,
      rw h' at hi,
      simpa only [add_lt_iff_neg_left, not_lt_zero'] using hi } ,
    { rw ← hg,
      intro h,
      simp only [function.embedding.to_fun_eq_coe, function.embedding.smul_apply,
        equiv.perm.smul_def, embedding_like.apply_eq_iff_eq] at h,
      let h' := fin.veq_of_eq h,
      simp only [fin.val_eq_coe, fin.coe_cast_le] at h',
      let hi := i.prop,
      rw h' at hi,
      simpa only [lt_self_iff_false] using hi} },
end

 -/
variable {α}
/-- A subgroup of equiv.perm α which is (fintype.card α - 2)-pretransitive
  contains the alternating group  -/
theorem alternating_group_le_of_full_minus_two_pretransitive
  {G : subgroup (equiv.perm α)}
  (hmt : is_multiply_pretransitive ↥G α (fintype.card α - 2)) :
  alternating_group α ≤ G :=
begin
  cases nat.lt_or_ge (fintype.card α) 2 with hα1 hα,
  { -- fintype.card α  < 2
    rw nat.lt_succ_iff at hα1,
    suffices : alternating_group α = ⊥, rw this, exact bot_le,
    rw ← subgroup.card_le_one_iff_eq_bot,
    suffices : fintype.card ↥(alternating_group α) ≤ fintype.card (equiv.perm α),
    { apply le_trans this,
      rw fintype.card_perm,
      exact nat.factorial_le hα1 },
    apply fintype.card_subtype_le },

  suffices : ∃ (s : set α), fintype.card s = fintype.card α - 2,
  obtain ⟨s, hs⟩ := this,
  rw ← hs at hmt,
  let hyp := index_of_fixing_subgroup_of_multiply_pretransitive G α s hmt,
  rw [hs, (nat.sub_sub_self hα), nat.factorial_two] at hyp,

  let hyp' := nat.mul_le_mul_right 2
    (nat.le_of_dvd (begin rw fintype.card_pos_iff, use 1, end)
      (subgroup.index_dvd_card  (fixing_subgroup G s))),
  rw [hyp, mul_comm] at hyp',

  apply large_subgroup_of_perm_contains_alternating,
  rw fintype.card_equiv (equiv.refl _) , exact hyp',

  obtain ⟨s, hs⟩ := finset.exists_smaller_set (⊤: finset α)
    (fintype.card α - 2) (nat.sub_le _ _),
  use s,
  simp only [finset.coe_sort_coe, fintype.card_coe],
  exact hs.right,
end

/-- The alternating group on 3 letters or more acts primitively -/
lemma alternating_group.is_pretransitive (h : 3 ≤ fintype.card α) :
  is_pretransitive (alternating_group α) α :=
begin
  rw is_pretransitive_iff_is_one_pretransitive,
  apply is_multiply_pretransitive_of_higher,
  exact alternating_group_is_fully_minus_two_pretransitive α,
  apply le_trans _ (nat.sub_le_sub_right h 2), norm_num,
  simp only [part_enat.of_fintype, part_enat.coe_le_coe, nat.sub_le]
end

/- This lemma proves the trivial blocks property even if the action is not preprimitive
because it is not pretransitive (for fintype.card α ≤ 2)-/
lemma alternating_group.has_trivial_blocks (B : set α) (hB : is_block (alternating_group α) B):
  is_trivial_block B :=
begin
  cases le_or_lt (fintype.card α) 2 with h2 h2,
  { exact is_trivial_block.of_card_le_2 h2 B },
  cases le_or_lt (fintype.card α) 3 with h3 h4,
  { have h3' : fintype.card α = 3 := le_antisymm h3 h2,
    cases le_or_lt (fintype.card B) 1 with h1 h2,
    { apply or.intro_left,
      rw [← set.subsingleton_coe,  ← fintype.card_le_one_iff_subsingleton],
      exact h1 },
    { apply or.intro_right,
      rw [fintype.one_lt_card_iff] at h2,
      -- using h2, get a ≠ b in B
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := h2,
      simp only [ne.def, subtype.mk_eq_mk] at hab,
      -- using h3', get c ≠ a, b
      have : ∃ (c : α), c ∉ {a, b},
      { by_contradiction,
        push_neg at h,
        have : ({a, b} : finset α) = finset.univ,
        { ext c, split,
          intro hc, exact finset.mem_univ c,
          intro _, exact h c, },
        rw lt_iff_not_ge at h2, apply h2, rw ge_iff_le,
        rw ← finset.card_eq_iff_eq_univ at this,
        rw ← this,
        rw finset.card_doubleton hab, },
      obtain ⟨c, hc⟩ := this,
      simp only [finset.mem_insert, finset.mem_singleton, not_or_distrib] at hc,
      suffices : ({a, b, c} : finset α) = finset.univ,
      rw eq_top_iff,
      rw [set.top_eq_univ, ← finset.coe_univ, ← this],
      intros x hx,
      simp only [finset.coe_insert, finset.coe_singleton, set.mem_insert_iff, set.mem_singleton_iff] at hx,
      cases hx with hxa hx,
      rw hxa, exact ha,
      cases hx with hxb hxc,
      rw hxb, exact hb,
      rw hxc,

      -- get a three_cycle g = c[a,b,c]
      let g : alternating_group α := ⟨(equiv.swap a b) * (equiv.swap c b), -- cycle [a,b,c]
      begin
        rw equiv.perm.mem_alternating_group,
        rw equiv.perm.sign_mul,
        rw equiv.perm.sign_swap  hab,
        rw equiv.perm.sign_swap hc.right,
        simp only [int.units_mul_self],
      end ⟩ ,
      suffices : g • B = B,
      rw ← this,
      use b,
      apply and.intro hb,
      change ((equiv.swap a b) * (equiv.swap c b)) • b = c,
      simp only [equiv.perm.smul_def, equiv.perm.coe_mul, function.comp_app],
      rw equiv.swap_apply_right,
      rw equiv.swap_apply_of_ne_of_ne hc.left hc.right,

      -- g • B = B
      rw is_block.mk_mem at hB,
      apply hB g a ha,
      change ((equiv.swap a b) * (equiv.swap c b)) • a ∈ B,
      simp only [equiv.perm.smul_def, equiv.perm.coe_mul, function.comp_app],
      rw equiv.swap_apply_of_ne_of_ne (ne_comm.mp hc.left) hab,
      rw equiv.swap_apply_left,
      exact hb,

      -- {a, b, c} = finset.univ
      rw [← finset.card_eq_iff_eq_univ, h3'],
      rw finset.card_insert_of_not_mem,
      rw finset.card_doubleton (ne_comm.mp hc.right),
      simp only [finset.mem_insert, finset.mem_singleton, not_or_distrib],
      apply and.intro hab,
      exact ne_comm.mp hc.left, } },

  -- 4 ≤ fintype.card α
  change 4 ≤ fintype.card α at h4,
  suffices : is_preprimitive (alternating_group α) α,
  exact this.has_trivial_blocks hB,
  apply is_preprimitive_of_two_pretransitive,
  apply is_multiply_pretransitive_of_higher,
  apply alternating_group_is_fully_minus_two_pretransitive,
  apply le_trans _ (nat.sub_le_sub_right h4 2), norm_num,
  simp only [part_enat.of_fintype, part_enat.coe_le_coe, nat.sub_le],
end

/-- The alternating group on 3 letters or more acts primitively -/
theorem alternating_group.is_preprimitive (h : 3 ≤ fintype.card α):
  is_preprimitive (alternating_group α) α :=
begin
  haveI := alternating_group.is_pretransitive h,
  apply is_preprimitive.mk,
  exact alternating_group.has_trivial_blocks
end

/- lemma alternating_group.is_pretransitive' (h : 3 ≤ fintype.card α) :
  is_pretransitive (alternating_group α) α :=
begin
  classical,
  apply is_pretransitive.mk,
  intros x y,
  cases em (y = x) with hxy hxy,
  use 1, rw [hxy, one_smul],
  suffices : nonempty(finset.erase (finset.erase finset.univ x) y),
  obtain ⟨z, hz⟩ := this,
  simp only [finset.mem_erase, ne.def, finset.mem_univ, and_true] at hz,
  let g := [x,y,z].form_perm,
  suffices : [x,y,z].nodup,
  use g,
  rw equiv.perm.mem_alternating_group,
  apply equiv.perm.is_three_cycle.sign,
  rw ← card_support_eq_three_iff ,
  rw list.support_form_perm_of_nodup _ this _,
  rw list.to_finset_card_of_nodup this,
  simp only [list.length],
  intros t ht, simpa only [and_false] using ht,
  change g • x = y,
  simp only [equiv.perm.smul_def],
  rw list.form_perm_apply_head x y _ this,
  -- nodup
  simp only [list.nodup_cons, list.mem_cons_iff, list.mem_singleton, list.not_mem_nil,
    not_false_iff, list.nodup_nil, and_true, not_or_distrib],
  split, split,
  exact ne_comm.mp hxy, exact ne_comm.mp hz.right, exact ne_comm.mp hz.left,
  { rw ← fintype.card_pos_iff ,
    simp only [fintype.card_coe],
    rw finset.card_erase_of_mem, rw finset.card_erase_of_mem,
    rw nat.sub_sub,
    refine lt_of_lt_of_le _ (nat.sub_le_sub_right h _),
    norm_num,
    exact finset.mem_univ x,
    simp only [finset.mem_erase, ne.def, finset.mem_univ, and_true],
    exact hxy },
end
 -/

end finite

end multiple_transitivity

end mul_action


#lint
