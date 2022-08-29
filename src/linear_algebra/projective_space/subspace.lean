/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth
-/

import linear_algebra.projective_space.independence

/-!
# Subspaces of Projective Space

In this file we define subspaces of a projective space, and show that the subspaces of a projective
space form a complete lattice under inclusion.

## Implementation Details

A subspace of a projective space ℙ K V is defined to be a structure consisting of a subset of
ℙ K V such that if two nonzero vectors in V determine points in ℙ K V which are in the subset, and
the sum of the two vectors is nonzero, then the point determined by the sum of the two vectors is
also in the subset.

## Results

- There is a Galois insertion between the subsets of points of a projective space
  and the subspaces of the projective space, which is given by taking the span of the set of points.
- The subspaces of a projective space form a complete lattice under inclusion.

# Future Work
- Show that there is a one-to-one order-preserving correspondence between subspaces of a
  projective space and the submodules of the underlying vector space.
-/

variables (K V : Type*) [field K] [add_comm_group V] [module K V]

namespace projectivization

/-- A subspace of a projective space is a structure consisting of a set of points such that:
If two nonzero vectors determine points which are in the set, and the sum of the two vectors is
nonzero, then the point determined by the sum is also in the set. -/
@[ext] structure subspace :=
(carrier : set (ℙ K V))
(mem_add' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
  mk K v hv ∈ carrier → mk K w hw ∈ carrier → mk K (v + w) (hvw) ∈ carrier)

namespace subspace

variables {K V}

instance : set_like (subspace K V) (ℙ K V) :=
{ coe := carrier,
  coe_injective' := λ A B, by { cases A, cases B, simp } }

@[simp]
lemma mem_carrier_iff (A : subspace K V) (x : ℙ K V) : x ∈ A.carrier ↔ x ∈ A := iff.refl _

lemma mem_add (T : subspace K V) (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
  projectivization.mk K v hv ∈ T → projectivization.mk K w hw ∈ T →
  projectivization.mk K (v + w) (hvw) ∈ T :=
  T.mem_add' v w hv hw hvw

/-- The span of a set of points in a projective space is defined inductively to be the set of points
which contains the original set, and contains all points determined by the (nonzero) sum of two
nonzero vectors, each of which determine points in the span. -/
inductive span_carrier (S : set (ℙ K V)) : set (ℙ K V)
| of (x : ℙ K V) (hx : x ∈ S) : span_carrier x
| mem_add (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    span_carrier (projectivization.mk K v hv) → span_carrier (projectivization.mk K w hw) →
    span_carrier (projectivization.mk K (v + w) (hvw))

/-- The span of a set of points in projective space is a subspace. -/
def span (S : set (ℙ K V)) : subspace K V :=
{ carrier := span_carrier S,
  mem_add' := λ v w hv hw hvw,
    span_carrier.mem_add v w hv hw hvw }

/-- The span of a set of points contains the set of points. -/
lemma subset_span (S : set (ℙ K V)) : S ⊆ span S := λ x hx, span_carrier.of _ hx

/-- The span of a set of points is a Galois insertion between sets of points of a projective space
and subspaces of the projective space. -/
def gi : galois_insertion (span : set (ℙ K V) → subspace K V) coe :=
{ choice := λ S hS, span S,
  gc := λ A B, ⟨λ h, le_trans (subset_span _) h, begin
    intros h x hx,
    induction hx,
    { apply h, assumption },
    { apply B.mem_add, assumption' }
  end⟩,
  le_l_u := λ S, subset_span _,
  choice_eq := λ _ _, rfl }

/-- The span of a subspace is the subspace. -/
@[simp] lemma span_coe (W : subspace K V) : span ↑W = W := galois_insertion.l_u_eq gi W

/-- The infimum of two subspaces exists. -/
instance has_inf : has_inf (subspace K V) :=
⟨λ A B, ⟨A ⊓ B, λ v w hv hw hvw h1 h2,
  ⟨A.mem_add _ _ hv hw _ h1.1 h2.1, B.mem_add _ _ hv hw _ h1.2 h2.2⟩⟩⟩

/-- Infimums of arbitrary collections of subspaces exist. -/
instance has_Inf : has_Inf (subspace K V) :=
⟨λ A, ⟨Inf (coe '' A), λ v w hv hw hvw h1 h2 t, begin
  rintro ⟨s, hs, rfl⟩,
  exact s.mem_add v w hv hw _ (h1 s ⟨s, hs, rfl⟩) (h2 s ⟨s, hs, rfl⟩),
end⟩⟩

/-- The subspaces of a projective space form a complete lattice. -/
instance : complete_lattice (subspace K V) :=
{ inf_le_left := λ A B x hx, by exact hx.1,
  inf_le_right := λ A B x hx, by exact hx.2,
  le_inf := λ A B C h1 h2 x hx, ⟨h1 hx, h2 hx⟩,
  ..(infer_instance : has_inf _),
  ..complete_lattice_of_Inf (subspace K V)
  begin
    refine λ s, ⟨λ a ha x hx, (hx _ ⟨a, ha, rfl⟩), λ a ha x hx E, _⟩,
    rintros ⟨E, hE, rfl⟩,
    exact (ha hE hx)
  end }

instance subspace_inhabited : inhabited (subspace K V) :=
{ default := ⊤ }

instance : has_emptyc (subspace K V) :=
{ emptyc := ⊥}

/-- The span of the empty set is the bottom of the lattice of subspaces. -/
@[simp] lemma span_empty : span (∅ : set (ℙ K V)) = ⊥ := gi.gc.l_bot

/-- The span of the entire projective space is the top of the lattice of subspaces. -/
@[simp] lemma span_univ : span (set.univ : set (ℙ K V)) = ⊤ :=
by { rw [eq_top_iff, set_like.le_def], intros x hx, exact subset_span _ (set.mem_univ x) }

/-- The span of a set of points is contained in a subspace if and only if the set of points is
contained in the subspace. -/
lemma span_le_subspace_iff {S : set (ℙ K V)} {W : subspace K V} : span S ≤ W ↔ S ⊆ W :=
gi.gc S W

/-- If a set of points is a subset of another set of points, then its span will be contained in the
span of that set. -/
@[mono] lemma monotone_span : monotone (span : set (ℙ K V) → subspace K V) := gi.gc.monotone_l

lemma subset_span_trans {S T U : set (ℙ K V)} (hST : S ⊆ span T) (hTU : T ⊆ span U) :
  S ⊆ span U :=
gi.gc.le_u_l_trans hST hTU

/-- The supremum of two subspaces is equal to the span of their union. -/
lemma span_union (S T : set (ℙ K V)) : span (S ∪ T) = span S ⊔ span T := (@gi K V _ _ _).gc.l_sup

/-- The supremum of a collection of subspaces is equal to the span of the union of the
collection. -/
lemma span_Union {ι} (s : ι → set (ℙ K V)) : span (⋃ i, s i) = ⨆ i, span (s i) :=
(@gi K V _ _ _).gc.l_supr

/-- The supremum of a subspace and the span of a set of points is equal to the span of the union of
the subspace and the set of points. -/
lemma sup_span {S : set (ℙ K V)} {W : subspace K V} : W ⊔ span S = span (W ∪ S) :=
by rw [span_union, span_coe]

lemma span_sup {S : set (ℙ K V)} {W : subspace K V}: span S ⊔ W = span (S ∪ W) :=
by rw [span_union, span_coe]

/-- A point in a projective space is contained in the span of a set of points if and only if the
point is contained in all subspaces of the projective space which contain the set of points. -/
lemma mem_span {S : set (ℙ K V)} (u : ℙ K V) : u ∈ span S ↔ ∀ (W : subspace K V), S ⊆ W → u ∈ W :=
by { simp_rw ← span_le_subspace_iff, exact ⟨λ hu W hW, hW hu, λ W, W (span S) (le_refl _)⟩ }

/-- The span of a set of points in a projective space is equal to the infimum of the collection of
subspaces which contain the set. -/
lemma span_eq_Inf {S : set (ℙ K V)} : span S = Inf {W | S ⊆ W} :=
begin
  ext,
  simp_rw [mem_carrier_iff, mem_span x],
  refine ⟨λ hx, _, λ hx W hW, _⟩,
  { rintros W ⟨T, ⟨hT, rfl⟩⟩, exact (hx T hT) },
  { exact (@Inf_le _ _ {W : subspace K V | S ⊆ ↑W} W hW) x hx },
end

/-- If a set of points in projective space is contained in a subspace, and that subspace is
contained in the span of the set of points, then the span of the set of points is equal to
the subspace. -/
lemma span_eq_of_le {S : set (ℙ K V)} {W : subspace K V} (hS : S ⊆ W) (hW : W ≤ span S) :
  span S = W :=
le_antisymm (span_le_subspace_iff.mpr hS) hW

/-- The spans of two sets of points in a projective space are equal if and only if each set of
points is contained in the span of the other set. -/
lemma span_eq_span_iff {S T : set (ℙ K V)} : span S = span T ↔ S ⊆ span T ∧ T ⊆ span S :=
⟨λ h, ⟨h ▸ subset_span S, h.symm ▸ subset_span T⟩,
  λ h, le_antisymm (span_le_subspace_iff.2 h.1) (span_le_subspace_iff.2 h.2)⟩

open_locale big_operators

/-- If a family of vectors is such that every nonzero vector in the family determines a point in the
corresponding projective space which is contained in a subspace, then every nonzero finite sum of
vectors from the family also determines a point contained in that subspace. -/
lemma mk_sum_mem {ι : Type*} (s : finset ι) (W : subspace K V) (f : ι → V)
  (hf : ∀ i, i ∈ s →  f i = 0 ∨ ∃ (hi : f i ≠ 0), projectivization.mk K (f i) (hi) ∈ W)
  (hs : ∑ i in s, f i ≠ 0) : projectivization.mk K (∑ i in s, f i) hs ∈ W :=
begin
  suffices : (∑ (i : ι) in s, f i = 0) ∨
    (∃ (h : (∑ (i : ι) in s, f i ≠ 0)), (projectivization.mk K (∑ (i : ι) in s, f i) h ∈ W)), by
    { rcases this, contradiction, cases this, assumption },
  apply finset.sum_induction f (λ x, x = 0 ∨ (∃ hx : x ≠ 0, projectivization.mk K x hx ∈ W)),
  { intros a b ha hb, by_cases hab : a + b = 0,
    { left, exact hab },
    { cases ha; cases hb,
      { rw [ha, hb, zero_add], simp },
      { simp_rw [ha, zero_add], right, exact hb },
      { simp_rw [hb, add_zero], right, exact ha },
      { right, cases ha, cases hb, exact ⟨hab, mem_add W a b ha_w hb_w hab ha_h hb_h⟩ } } },
  { simp },
  { intros i hi, exact hf i hi }
end

/-- If a family of vectors is such that every nonzero vector in the family determines a point in the
corresponding projective space which is contained in a subspace, then every nonzero linear
combination of vectors from the family also determines a point contained in that subspace. -/
lemma mk_sum_smul_mem {ι : Type*} (s : finset ι) (W : subspace K V) (f : ι → V) (g : ι → K)
  (hf : ∀ i, i ∈ s →  f i = 0 ∨ ∃ (hi : f i ≠ 0), projectivization.mk K (f i) (hi) ∈ W)
  (hs : ∑ i in s, (g i) • f i ≠ 0) : projectivization.mk K (∑ i in s, (g i) • f i) hs ∈ W :=
begin
  refine mk_sum_mem s W (g • f) _ hs,
  intro i,
  by_cases hgz : g i = 0,
  { rw [hgz, zero_smul], simp },
  { by_cases hfz : f i = 0,
    { rw [hfz, smul_zero], simp },
    { intro hi, right,
      refine ⟨by { rw [ne.def, smul_eq_zero, not_or_distrib], exact ⟨hgz, hfz⟩ }, _⟩,
      cases (or.resolve_left (hf i hi) hfz), convert h using 1, rw mk_eq_mk_iff', use g i } }
end

/-- If a set of points in a projective space has the property that for any two unique points
contained in the set, these points being dependent with a third point in the projective space
implies that this third point is contained in the set, then the set is a subspace. -/
def mk_of_dependent (S : set (ℙ K V))
  (h : ∀ u v w, u ≠ v → u ∈ S → v ∈ S → dependent ![u, v, w] → w ∈ S) : subspace K V :=
{ carrier := S,
  mem_add' := λ u v hu hv huv huS hvS,
  begin
    by_cases heq : projectivization.mk K u hu = projectivization.mk K v hv,
    { convert hvS using 1,
      rw mk_eq_mk_iff' at heq ⊢,
      cases heq with a ha,
      exact ⟨a + 1, by { rw [add_smul, ha, one_smul] }⟩ },
    { refine h _ _ (projectivization.mk K (u + v) huv) heq huS hvS _,
      convert dependent.mk ![u, v, u + v] _ _,
      { ext i, fin_cases i; simp },
      { intro i, fin_cases i; assumption },
      { rw fintype.not_linear_independent_iff,
        refine ⟨![-1, -1, 1], _, ⟨2, by { simp }⟩⟩,
        simp only [fin.sum_univ_three, matrix.cons_val_zero, neg_smul, one_smul,
          matrix.cons_val_one, matrix.head_cons, matrix.cons_vec_bit0_eq_alt0, matrix.cons_append,
          matrix.empty_append, matrix.cons_vec_alt0],
        abel } },
  end }

/-- If a set of points in a projective space has the property that for any independent family of
points contained in the set, this family being dependent with another point in the projective space
implies that this point is contained in the set, then the set is a subspace. -/
def mk_of_dependent' (S : set (ℙ K V)) (h : ∀ (ι : Type*) (f : ι → ℙ K V) (hf: independent f)
  (u : ℙ K V) (hf' : dependent (λ t, sum.rec_on t f (λ _, u) : ι ⊕ punit → ℙ K V))
  (h : ∀ i, f i ∈ S), u ∈ S) : subspace K V :=
mk_of_dependent S
begin
  intros u v w huv huS hvS hdep,
  refine h (ulift $ fin 2) (![u, v] ∘ ulift.down) _ _ _ _,
  { rw [independent_iff],
    rw [← independent_pair_iff_neq, independent_iff] at huv,
    apply linear_independent.comp huv ulift.down (ulift.down_injective) },
  { rw [dependent_iff] at hdep ⊢, by_contra, apply hdep,
    convert linear_independent.comp h (![sum.inl 0, sum.inl 1, sum.inr punit.star]) _,
    { ext i, fin_cases i; refl },
    { intros m n _, fin_cases m; fin_cases n; tidy } },
  { simp_rw [ulift.forall, function.comp_app], intro x, fin_cases x; assumption },
end

/-- If a family of points in a projective space is independent, and adding a point to the family
results in it becoming dependent, then the added point's representative is in the span
of the representatives of the original family. -/
lemma independent_sum_punit_dependent {ι : Type*} (f : ι → ℙ K V) (hf: independent f) (u : ℙ K V)
  (hf' : dependent (λ t, sum.rec_on t f (λ _, u) : ι ⊕ punit → ℙ K V)) :
  u.rep ∈ submodule.span K (set.range (projectivization.rep ∘ f)) :=
begin
  simp_rw [dependent_iff, independent_iff] at hf' hf,
  have : ¬ linear_independent K (sum.elim (projectivization.rep ∘ f)
    (projectivization.rep ∘ (λ t, u) : punit → V)), by { convert hf', ext, cases x; simp },
  have hu : linear_independent K (λ (x : punit), u.rep) :=
    linear_independent_unique (λ (x : punit), u.rep) (rep_nonzero u),
  have hd : ¬ disjoint (submodule.span K (set.range (projectivization.rep ∘ f)))
    (submodule.span K (set.range (projectivization.rep ∘ (λ t, u) : punit → V))), by
    { by_contra, exact this (linear_independent.sum_type hf hu h) },
  rw [disjoint_iff, ← ne.def, submodule.ne_bot_iff] at hd,
  rcases hd with ⟨v, hv1, hv3⟩,
  cases submodule.mem_inf.1 hv1 with hv1 hv2,
  have hv : v ∈ submodule.span K {u.rep}, by { convert hv2, simp },
  cases submodule.mem_span_singleton.1 hv with a ha,
  rw [← ha] at hv1,
  convert submodule.smul_mem _ a⁻¹ hv1,
  have haz : a ≠ 0, by { by_contra haz, rw [haz, zero_smul] at ha, exact hv3 ha.symm },
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel haz, one_smul],
end

/-- If a subspace of a projective space contains a family of independent points, and this family is
dependent with another point in the projective space, then the point is contained in the
subspace. -/
lemma mem_of_dependent' {ι : Type*} (W : subspace K V) (f : ι → ℙ K V) (hf: independent f)
  (u : ℙ K V) (hf' : dependent (λ t, sum.rec_on t f (λ _, u) : ι ⊕ punit → ℙ K V))
  (h : ∀ i, f i ∈ W) : u ∈ W :=
begin
  let hu := independent_sum_punit_dependent f hf u hf',
  rcases (submodule.mem_span_finite_of_mem_span hu) with ⟨s, ⟨h2, h3⟩⟩,
  rcases mem_span_finset.1 h3 with ⟨g, hg⟩,
  convert mk_sum_smul_mem s W (λ x, x : V → V) (g) _ _,
  { rw [← mk_rep u, mk_eq_mk_iff'], use 1, rw one_smul, exact hg },
  { intros i his, by_cases hi : i = 0,
    { left, exact hi },
    { right,
      refine ⟨hi, _⟩,
      cases h2 his with y hy,
      rw function.comp_app at hy,
      convert h y,
      rw [← mk_rep (f y), mk_eq_mk_iff'],
      exact ⟨1, by { rwa one_smul }⟩ } },
  { rw hg, exact rep_nonzero u },
end

/-- If a subspace of a projective space contains two unique points, and a third point from the
projective space is dependent with the two unique points, then the third point is contained in the
subspace. -/
lemma mem_of_dependent (W : subspace K V) (u v w : ℙ K V) (h: u ≠ v) (hu : u ∈ W) (hv : v ∈ W)
  (hdep: dependent ![u, v, w]) : w ∈ W :=
begin
  refine mem_of_dependent' W ![u, v] _ w _ _,
  { rwa independent_pair_iff_neq },
  { rw [dependent_iff] at hdep ⊢,
    by_contra,
    apply hdep,
    convert linear_independent.comp h (![sum.inl 0, sum.inl 1, sum.inr punit.star]) _,
    { ext, fin_cases x; refl },
    { intros m n; fin_cases m; fin_cases n; tidy } },
  { intro i, fin_cases i; assumption },
end

/-- A nonzero vector v in V belongs to a submodule M of V if and only the representative of the
point associated to v in ℙ K V belongs to M. -/
lemma mem_submodule_iff_rep_mem (v : V) (hv : v ≠ 0) (M : submodule K V) :
  v ∈ M ↔ (projectivization.mk K v hv).rep ∈ M :=
by { obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K v hv, rw ← ha, simp }

/-- This function associates to a submodule M of V a set of points from ℙ K V, which consists
of points associated to nonzero vectors contained in M. This set of points is infact a subspace of
ℙ K V. -/
inductive projective_linear_subspace_set (M : submodule K V) : set (ℙ K V)
| mk (v : V) (hv : v ≠ 0) (h : v ∈ M) : projective_linear_subspace_set (projectivization.mk K v hv)

/-- This function associates to a submodule M of the vector space V the subspace of ℙ K V which
consists of the points whose associated submodule is contained in M -/
def projective_linear_subspace (M : submodule K V) : subspace K V :=
{ carrier := {v | v.submodule ≤ M},
  mem_add' :=
  begin
    intros v w hv hw hvw hvM hwM,
    rw [set.mem_set_of_eq, submodule_mk, submodule.span_singleton_le_iff_mem] at hvM hwM ⊢,
    exact M.add_mem hvM hwM
  end }

/-- This function associates to a submodule M of the vector space V the subspace of ℙ K V consisting
of the points whose representative's are contained in M. -/
def projective_linear_subspace₂ (M : submodule K V) : subspace K V :=
{ carrier := {v | v.rep ∈ M},
  mem_add' :=
  begin
    intros v w hv hw hvw hvM hwM,
    simp_rw [set.mem_set_of_eq, ← mem_submodule_iff_rep_mem] at hvM hwM M ⊢,
    exact M.add_mem hvM hwM
  end }

/-- The subspaces of ℙ K V associated to a submodule of V by the above two functions are equal. -/
lemma projective_linear_subspace_eq_projective_linear_subspace₂ (M : submodule K V) :
  projective_linear_subspace M = projective_linear_subspace₂ M :=
begin
  ext,
  unfold projective_linear_subspace,
  unfold projective_linear_subspace₂,
  simp_rw [set.mem_set_of_eq, projectivization.submodule_eq, submodule.span_singleton_le_iff_mem]
end

/-- The subspace of ℙ K V associated to a submodule M of V by the function
projective_linear_subspace is equal to the subset of ℙ K V associated to M by the function
projective_linear_subspace_set. -/
lemma projective_linear_subspace_eq_projective_linear_subspace_set (M : submodule K V) :
  projective_linear_subspace_set M = projective_linear_subspace M :=
begin
  ext, refine ⟨λ hx, _, λ hx, _⟩,
  { induction hx with v hv hvM, rwa ← submodule.span_singleton_le_iff_mem at hvM },
  { have : submodule.span K {x.rep} ≤ M, by
      { convert hx, nth_rewrite 1 ← mk_rep x,
        exact (projectivization.submodule_mk (x.rep) (rep_nonzero x)).symm },
    rw submodule.span_singleton_le_iff_mem at this,
    convert (projective_linear_subspace_set.mk x.rep (rep_nonzero x) (this)),
    exact (mk_rep x).symm },
end

/-- This function associated to a subspace W of ℙ K V a submodule of the vector space V, which is
equal to the supremum of the collection of submodules associated to the points of W. -/
def to_submodule (W : subspace K V) : submodule K V :=
  ⨆ (v : ℙ K V) (hv : v ∈ W), projectivization.submodule v

/-- This function associated to a subspace W of ℙ K V a submodule of the vector space V, which is
equal to the collection of nonzero vectors associated to a point of W, and the zero vector. -/
def to_submodule₂ (W : subspace K V) : submodule K V :=
{ carrier := {v | v = 0 ∨ ∃ (hv : v ≠ 0), projectivization.mk K v hv ∈ W},
  add_mem' := begin
    intros a b ha hb,
    simp only [ne.def, set.mem_set_of_eq] at ha hb ⊢,
    by_cases h : a + b = 0,
    { exact or.inl h },
    { refine or.inr ⟨h, _⟩,
      cases ha; cases hb,
      { rw [ha, hb, zero_add] at h, contradiction },
      { cases hb with _ hb, convert hb, rw [ha, zero_add] },
      { cases ha with _ ha, convert ha, rw [hb, add_zero] },
      { cases ha, cases hb, exact mem_add W a b _ _ h ha_h hb_h } },
  end,
  zero_mem' := by { simp },
  smul_mem' := begin
    intros c x hx,
    simp only [ne.def, smul_eq_zero, set.mem_set_of_eq] at hx ⊢,
    rcases hx with ⟨_, ⟨_, _⟩⟩; by_cases hcz : c = 0,
    { exact or.inl (or.inl hcz) },
    { exact or.inl (or.inr hx) },
    { exact or.inl (or.inl hcz) },
    { right,
      cases hx with h hx,
      refine ⟨by { rw not_or_distrib, exact ⟨hcz, h⟩ }, _⟩,
      convert hx using 1,
      rw mk_eq_mk_iff',
      exact ⟨c, refl _⟩ },
  end }

/-- The submodules of V associated to a subspace of ℙ K V by the functions to_submodule and
to_submodule₂ are equal. -/
lemma to_submodule_eq_to_submodule₂ (W : subspace K V) : to_submodule W = to_submodule₂ W :=
begin
  ext, refine ⟨λ hx, _, λ hx, _⟩,
  { apply submodule.supr_induction _ hx,
    { intros v u hu,
      apply submodule.supr_induction _ hu,
      { intros hv w hw,
        suffices : v.submodule ≤ W.to_submodule₂, by { exact this hw },
        rw [submodule_eq, submodule.span_singleton_le_iff_mem],
        rw ← mk_rep v at hv,
        exact or.inr ⟨rep_nonzero v, hv⟩ },
      { simp },
      { intros y z, exact submodule.add_mem _ } },
    { simp },
    { intros y z, exact submodule.add_mem _ } },
  { cases hx,
    { rw hx, simp },
    { cases hx with hx hxW,
      rw [← submodule.span_singleton_le_iff_mem, ← submodule_mk x hx],
      convert @le_supr₂ _ _ (λ v, v ∈ W) _ _ (projectivization.mk K x hx) hxW,
      refl } }
end

/-- The to_submodule function is an order-preserving bijection between the subspaces of the
projective space ℙ K V and the submodules of the underlying vector space V, and its inverse is the
projective_linear_subspace function. -/
def equiv : subspace K V ≃o submodule K V :=
{ to_fun := to_submodule,
  inv_fun := projective_linear_subspace,
  left_inv := begin
    intros x,
    rw [to_submodule_eq_to_submodule₂, projective_linear_subspace_eq_projective_linear_subspace_2],
    ext,
    simp only [mk_rep, exists_prop, set.mem_set_of_eq, mem_carrier_iff],
    refine ⟨λ hx, _, λ hx, _⟩,
    { cases hx, exfalso, exact rep_nonzero x_1 hx, cases hx with _ hx, rwa mk_rep x_1 at hx },
    { exact or.inr ⟨rep_nonzero x_1, by { rwa mk_rep x_1 }⟩ },
  end,
  right_inv := begin
    intros x,
    rw [to_submodule_eq_to_submodule₂, projective_linear_subspace_eq_projective_linear_subspace_2],
    ext v,
    refine ⟨λ hv, _, λ hv, _⟩,
    { cases hv, rw hv, exact submodule.zero_mem _, cases hv, rwa mem_submodule_iff_rep_mem },
    { by_cases hvz : v = 0, left, exact hvz, right, use hvz, rwa mem_submodule_iff_rep_mem at hv },
  end,
  map_rel_iff' := begin
    intros W S,
    dsimp,
    simp_rw to_submodule_eq_to_submodule₂,
    unfold to_submodule₂,
    simp only [ne.def, submodule.mk_le_mk, set.set_of_subset_set_of, forall_eq_or_imp,
      eq_self_iff_true, not_true, is_empty.exists_iff, or_false, forall_exists_index, true_and],
    split,
    { intros h v hvW,
      cases (or.resolve_left (h v.rep (rep_nonzero v) (by { rwa mk_rep v})) (rep_nonzero v)),
      rwa mk_rep v at * },
    { intros h v hv hvW, exact or.inr ⟨hv, h hvW⟩ },
  end }

/-- A point in a projective space is a subspace. -/
instance : has_singleton (ℙ K V) (subspace K V) :=
{ singleton := λ x,
  { carrier := {x},
    mem_add' :=
    begin
      rintros v w hv hw hvw (rfl : _ = x) (h : _ = _),
      rw mk_eq_mk_iff' at h,
      cases h with a ha,
      rw [set.mem_singleton_iff, mk_eq_mk_iff'],
      refine ⟨1+ a, _⟩,
      rw [add_smul, ha, one_smul],
    end }}

/-- The submodule of V corresponding to the span of a set of points in a projective space ℙ K V is
equal to the span of the points' representatives in V. -/
lemma subspace_equivalence_of_span_eq_span_image_reps (S : set (ℙ K V)) :
  equiv (span S) = submodule.span K (projectivization.rep '' S) :=
begin
  ext,
  refine ⟨λ hx, _, λ hx, _⟩,
  { apply submodule.supr_induction _ hx,
    { intros v y hy,
      apply ((submodule.mem_supr _).1) hy (submodule.span K (projectivization.rep '' S)),
      clear hy,
      intro hv,
      induction hv with s hs _ _ _ _ _ _ _ hus hws,
      { rw [← mk_rep s, submodule_mk, submodule.span_singleton_le_iff_mem],
        exact submodule.subset_span ⟨s, ⟨hs, rfl⟩⟩ },
      { rw [submodule_mk, submodule.span_singleton_le_iff_mem] at *,
        exact submodule.add_mem _ hus hws } },
    { exact submodule.zero_mem _ },
    { intros y z hy hz, exact submodule.add_mem _ hy hz } },
  { refine (submodule.span_le.2) _ hx,
    rintros y ⟨v, ⟨hs, hv⟩⟩,
    refine submodule.mem_supr_of_mem v (submodule.mem_supr_of_mem (subspace.subset_span S hs) _),
    rw [← hv, ← mk_rep v, submodule_mk, mk_rep],
    exact submodule.mem_span_singleton_self (v.rep) },
end

/-- The span of a single point in a projective space is equal to the singleton subspace consisting
of the point. -/
@[simp]
lemma span_singleton (v : ℙ K V) : span ({v} : set (ℙ K V)) = {v} := span_coe {v}

/-- A singleton subspace is less than or equal to another subspace if and only if the point
determining the singleton subspace is contained in the other subspace. -/
lemma singleton_le_iff (a : ℙ K V) (W : subspace K V) : {a} ≤ W ↔ a ∈ W :=
  by { change ({a} : set (ℙ K V)) ⊆ W ↔ a ∈ W, rw [set.singleton_subset_iff, set_like.mem_coe] }

@[simp]
lemma subspace_equivalence_empty : equiv (∅ : subspace K V) = ⊥ := order_iso.map_bot equiv

@[simp]
lemma subspace_equivalence_top : equiv (⊤ : subspace K V) = ⊤ := order_iso.map_top equiv

/-- The submodule of V associated to the singleton subspace {v} of ℙ K V is equal to the span of
the representative of v in V. -/
@[simp]
lemma subspace_equivalence_singleton (v : ℙ K V) :
  equiv ({v} : subspace K V) = submodule.span K {v.rep} :=
  by { rw [← span_singleton v, subspace_equivalence_of_span_eq_span_image_reps], simp }

/-- The submodule of V associated to the singleton subspace {v} of ℙ K V is equal to the submodule
of V associated to the point v. -/
lemma submodule_eq_to_submodule (v : ℙ K V) : v.submodule = to_submodule {v} :=
by {rw submodule_eq v, convert (subspace_equivalence_singleton v).symm }

/--The submodule of V associated to the span of {v, w} in ℙ K V
is equal to the span of the set of representatives of v and w in V. -/
@[simp]
lemma subspace_equivalence_span_pair (u v : ℙ K V) :
  equiv (span {u, v} : subspace K V) = (submodule.span K {u.rep, v.rep}) :=
  by { rw [subspace_equivalence_of_span_eq_span_image_reps, set.image_pair] }

@[simp]
lemma subspace_equivalence_span_triple (u v w : ℙ K V) :
  equiv (span {u, v, w} : subspace K V) = (submodule.span K {u.rep, v.rep, w.rep}) :=
  by { rw [subspace_equivalence_of_span_eq_span_image_reps, set.image_insert_eq, set.image_pair] }

/-- A point in ℙ K V belongs to a subspace S of ℙ K V if and only if the point's representative
belongs to the submodule of V associated to S. -/
lemma rep_mem_equiv_submodule_iff (v : ℙ K V) (S : subspace K V) : v.rep ∈ equiv S ↔ v ∈ S :=
begin
  rw [← singleton_le_iff, ← submodule.span_singleton_le_iff_mem, ← subspace_equivalence_singleton],
  exact rel_iso.map_rel_iff equiv
end

/-- If three points u, v, w of the projective space ℙ K V are such that u is contiained in the span
of v and w, and u is not equal to v, then w is contained in the span of v and u. -/
lemma mem_span_exchange (u v w : ℙ K V) (hu : u ∈ span ({v, w} : set (ℙ K V))) (huv : u ≠ v) :
  w ∈ span ({v, u} : set (ℙ K V)) :=
begin
  have h : u ∉ ({v} : subspace K V), by
    { rw [← mem_carrier_iff], unfold carrier, rwa set.mem_singleton_iff },
  simp_rw [← rep_mem_equiv_submodule_iff, subspace_equivalence_span_pair,
    subspace_equivalence_singleton, set.pair_comm v.rep _] at *,
  exact mem_span_insert_exchange hu h
end

/-- A family of points in a projective space ℙ K V is independent if and only if the family of
singleton subspaces determined by the points is independent in the lattice of subspaces of ℙ K V. -/
lemma independent_iff_lattice_independent_singleton {ι : Type*} (f : ι → ℙ K V) :
  independent f ↔ complete_lattice.independent (λ i, ({f i} : subspace K V)) :=
begin
  rw [independent_iff_complete_lattice_independent,
    ← complete_lattice.independent_map_order_iso_iff (@equiv K V _ _ _)],
  suffices : (λ (i : ι), (f i).submodule) = (equiv ∘ λ (i : ι), {f i}), by { rw this },
  ext,
  rw [function.comp_app],
  suffices : equiv {f x} = (f x).submodule, by { rw this },
  unfold equiv,
  rw [rel_iso.coe_fn_mk, equiv.coe_fn_mk], exact supr_singleton,
end

end subspace

end projectivization
