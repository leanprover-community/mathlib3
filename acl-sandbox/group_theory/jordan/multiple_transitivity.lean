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

-- import .equivariant_map
-- import .maximal_subgroups
import .primitive
import .for_mathlib.extensions

import set_theory.cardinal.finite
import group_theory.index
import group_theory.group_action.embedding

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
/- It would be better do have it for has_scalar
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
  let j : (fin 1 ↪ α) →[M] α := {
  to_fun := λ x, x ⟨0, nat.one_pos⟩,
  map_smul' := λ m x, rfl },
  have : function.bijective j,
  { split,
    { intros x y hxy,
      ext i,
      rw (fin.eq_zero i), exact hxy },
    { intro a, use λ _, a,
      { intros i j hij,
        rw [fin.eq_zero i, fin.eq_zero j] },
      refl } },
  unfold is_multiply_pretransitive,
  rw is_pretransitive_of_bijective_map_iff (function.surjective_id) this,
end

/-- An n-pretransitive action is m-pretransitive for any m ≤ n -/
lemma is_multiply_pretransitive_of_higher  {n : ℕ}
  (hn : is_multiply_pretransitive M α n) {m : ℕ} (hmn : m ≤ n)
  (hα : ↑n ≤ enat.card α) :
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
      exact (sub_mul_action.of_stabilizer_neq M a) hu },

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
        change _ ∈  (sub_mul_action.of_stabilizer M a).carrier ,
        rw sub_mul_action.of_stabilizer_def,
        simp only [set.mem_compl_eq, set.mem_singleton_iff],
        rw ← hgx,
        simp only [← smul_apply],
        intro h, apply ne_of_lt hi,
        let h' := function.embedding.injective (g • x) h,
        simpa using h' },
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
      exact (sub_mul_action.of_stabilizer_neq M a) hu },

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
        change _ ∈  (sub_mul_action.of_stabilizer M a).carrier ,
        rw sub_mul_action.of_stabilizer_def,
        simp only [set.mem_compl_eq, set.mem_singleton_iff],
        rw ← hgx,
        simp only [← smul_apply],
        intro h, apply ne_of_lt hi,
        let h' := function.embedding.injective (g • x) h,
        simpa using h' },
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
lemma remaining_transitivity (d : ℕ) (s : set α) [fintype s] (hs : fintype.card s = d)
  (n : ℕ)
  (h : is_multiply_pretransitive M α n) :
  is_multiply_pretransitive
    (fixing_subgroup M (s : set α))
    (sub_mul_action.of_fixing_subgroup M (s : set α)) (n-d) :=
begin
  cases le_total d n with hdn hnd,
  { apply is_pretransitive.mk,
    intros x y,
    let h_eq := h.exists_smul_eq,

    obtain ⟨z⟩ := gimme_some_equiv hs.symm,

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
      simp only [enat.card_eq_coe_fintype_card, fintype.card_coe, enat.coe_le_coe],
      exact finset.card_le_univ s } },
  suffices : s.nonempty,
  obtain ⟨a, has⟩ := finset.nonempty.bex this,
  let t' : set (sub_mul_action.of_stabilizer M a) := coe ⁻¹' (↑(s.erase a) : set α),
  have hat' : (coe '' t' : set α) = s.erase a,
  { simp only [subtype.image_preimage_coe, finset.coe_erase, set_like.mem_coe,
    set.inter_eq_left_iff_subset, set.diff_singleton_subset_iff],
    simp_rw sub_mul_action.of_stabilizer_mem_iff,
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

  have : insert a (coe '' t') = set.insert a (coe '' t'),
  refl, rw this,
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
    rw [sub_mul_action.of_stabilizer_def, fintype.card_compl_set, set.card_singleton] },

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
  cases le_or_gt (enat.card α) 1 with hα hα,
  -- Trivial case where subsingleton α
  { rw enat.card_le_one_iff_subsingleton at hα,
    apply is_preprimitive.mk,
    { apply is_pretransitive.mk,
      intros x y, use 1, exact subsingleton_iff.mp hα _ _ },
    { intros B hB,
      apply or.intro_left,
      exact @set.subsingleton_of_subsingleton _ hα B } },
  -- Important case : 2 ≤ #α
  let hα' := id hα, rw gt_iff_lt at hα',
  rw [← cast_one, ← enat.succ_le_iff] at hα',
  apply is_preprimitive.mk,
  rw is_pretransitive_iff_is_one_pretransitive,
  apply is_multiply_pretransitive_of_higher M α h2 _ hα',

  norm_num,
  intros B hB,
  cases le_or_gt (enat.card B) 1 with h h,
  { -- Case : subsingleton
    apply or.intro_left,
    rw [enat.card_le_one_iff_subsingleton, set.subsingleton_coe] at h,
    exact h },
  -- Case : top
  apply or.intro_right,
  unfold enat.card at h,
  rw [gt_iff_lt, ← cast_one, ← enat.succ_le_iff] at h,
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


end multiple_transitivity
end mul_action

#lint
