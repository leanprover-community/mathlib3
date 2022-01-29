/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.padics.padic_integers
import topology.continuous_function.compact
import topology.continuous_function.locally_constant

/-!
# p-adic measure theory

This file defines p-adic distributions and measures on the space of locally constant functions
from a profinite space to a normed ring. We then use the measure to construct the p-adic integral.
In fact, we prove that this integral is linearly and continuously extended on `C(X, A`.

## Main definitions and theorems
 * `exists_finset_clopen`
 * `measures`
 * `integral`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12)

## Tags
p-adic L-function, p-adic integral, measure, totally disconnected, locally constant, compact,
Hausdorff
-/

variables (X : Type*) [topological_space X] [compact_space X] [t2_space X]
  [totally_disconnected_space X]
variables {R : Type*} [normed_group R]
variables (A : Type*) [normed_comm_ring A]

abbreviation inclusion : locally_constant X A →ₗ[A] C(X, A) :=
locally_constant.to_continuous_map_linear_map A

variable {X}

namespace set

lemma diff_inter_mem_sUnion {α : Type*} {s : set (set α)} (a y : set α) (h : y ∈ s) :
  (a \ ⋃₀ s) ∩ y = ∅ :=
begin
  rw [set.inter_comm, ← set.inter_diff_assoc, set.diff_eq_empty],
  exact (set.inter_subset_left y a).trans (set.subset_sUnion_of_mem h),
end

end set

namespace is_clopen

/-- The finite union of clopen sets is clopen. -/
lemma clopen_finite_Union {H : Type*} [topological_space H]
  (s : finset(set H)) (hs : ∀ x ∈ s, is_clopen x) :
  is_clopen ⋃₀ (s : set(set H)) :=
begin
  classical,
  apply finset.induction_on' s,
  { simp, },
  { rintros a S h's hS aS US,
    simp, apply is_clopen.union (hs a h's) US, },
end

/-- Given a finite set of clopens, one can find a finite disjoint set of clopens contained in
  it. -/
lemma clopen_Union_disjoint {H : Type*} [topological_space H]
  (s : finset(set H)) (hs : ∀ x ∈ s, is_clopen x) :
  ∃ (t : finset (set H)),
  (∀ (x ∈ (t : set (set H))), is_clopen x) ∧
  ⋃₀ (s : set(set H)) = ⋃₀ (t : set(set H)) ∧
  (∀ (x : set H) (hx : x ∈ t), ∃ z ∈ s, x ⊆ z) ∧
  ∀ (x y : set H) (hx : x ∈ t) (hy : y ∈ t) (h : x ≠ y), x ∩ y = ∅ :=
begin
  classical,
  apply finset.induction_on' s,
  { use ∅, simp, },
  { rintros a S h's hS aS ⟨t, clo, union, sub, disj⟩,
    set b := a \ ⋃₀ S with hb,
    use insert b t, split,
    { rintros x hx, simp at hx, cases hx,
      { rw hx, rw hb, apply is_clopen.diff (hs a h's) _,
        apply clopen_finite_Union, rintros y hy, apply hs y (hS hy), },
      { apply clo x hx,  }, },
    split,
    { simp only [finset.coe_insert, set.sUnion_insert], rw hb, rw ←union, rw set.diff_union_self, },
    { split,
      { rintros x hx, simp only [finset.mem_insert] at hx, cases hx,
        { use a, rw hx, rw hb, simp, apply set.diff_subset, },
        { specialize sub x hx, rcases sub with ⟨z, hz, xz⟩,
          refine ⟨z, _, xz⟩, rw finset.mem_insert, right, assumption, }, },
      { rintros x y hx hy ne, rw finset.mem_insert at hx, rw finset.mem_insert at hy,
        have : ∀ y ∈ t, b ∩ y = ∅,
        { rintros y hy, rw hb, rw union,
          apply set.diff_inter_mem_sUnion, assumption, },
        cases hx,
        { cases hy,
          { rw [hx, hy] at ne, exfalso, simp at ne, assumption, },
          { rw hx, apply this y hy, }, },
        { cases hy,
          { rw set.inter_comm, rw hy, apply this x hx, },
          { apply disj x y hx hy ne, }, }, }, }, },
end

end is_clopen

namespace locally_constant.density

variables (ε : ℝ) [hε : fact (0 < ε)]
abbreviation h {A : Type*} [normed_ring A] : A → set A :=
  λ (x : A), metric.ball x (ε / 4)

/-- The set of (ε/4)-balls. -/
abbreviation S {A : Type*} [normed_ring A] : set (set A) :=
  set.range (h ε)

variables {A} (f : C(X, A))

/-- Preimage of (ε/4)-balls. -/
abbreviation B : set(set X) :=
  { j : set X | ∃ (U ∈ ((S ε) : set(set A))), j = f ⁻¹' U }

lemma opens {j : set X} (hj : j ∈ (B ε f)) : is_open j :=
begin
  rw set.mem_set_of_eq at hj,
  rcases hj with ⟨U, hU, jU⟩, rw jU, apply continuous.is_open_preimage,
  { continuity, },
  { rw set.mem_range at hU, cases hU with y hy, rw ←hy,
    apply metric.is_open_ball, },
end

variables {t : finset (set A)}

/-- If there is a finite set of sets from `S` whose preimage forms a cover for `X`,
  then the union of the preimages of all the sets from `S` also forms a cover. -/
lemma sUnion_sub_of_finset_sub (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) : set.univ ⊆ set.sUnion (B ε f) :=
begin
  rintros x hx, simp only [exists_prop, set.mem_range, exists_exists_eq_and, set.mem_set_of_eq],
  have xt := ht hx,
  simp only [exists_prop, set.mem_preimage, set.mem_Union, set.mem_range, exists_and_distrib_right,
    set.supr_eq_Union, set.Union_exists] at xt,
  rcases xt with ⟨j, ⟨hj, jS⟩, fj⟩, refine ⟨f⁻¹' j, _, _⟩,
  { cases jS with a jS,
    refine ⟨a, by rw jS⟩, },
  simp [fj],
end

/-- If there is a finite set of sets from `S` whose preimage forms a cover for `X`,
  then there is a cover of `X` by clopen sets, with the image of each set being
  contained in an element of `S`. -/
def set_clopen (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) : set (set X) :=
  {j : set X | ∃ (U : set X) (hU : U ∈ (B ε f)),
    j ∈ classical.some (topological_space.is_topological_basis.open_eq_sUnion
    (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) (opens ε f hU))}

lemma mem_set_clopen (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) {x : set X} : x ∈ (set_clopen ε f ht) ↔
  ∃ (U : set X) (hU : U ∈ (B ε f)),
    x ∈ classical.some (topological_space.is_topological_basis.open_eq_sUnion
    (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) (opens ε f hU)) :=
begin
  rw set_clopen,
  simp only [exists_prop, set.mem_range, exists_exists_eq_and, set.mem_set_of_eq],
end

/-- Elements of `set_clopen` are clopen. -/
lemma set_clopen_sub_clopen_set (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) : (set_clopen ε f ht) ⊆ {s : set X | is_clopen s} :=
begin
  intros j hj,
  obtain ⟨W, hW, hj⟩ := (mem_set_clopen ε f ht).1 hj,
  obtain ⟨H, H1⟩ := classical.some_spec (topological_space.is_topological_basis.open_eq_sUnion
    (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) (opens ε f hW)),
  apply H, apply hj,
end

/-- `set_clopen` covers X. -/
lemma univ_sub_sUnion_set_clopen (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) : set.univ ⊆ ⋃₀ (set_clopen ε f ht) :=
begin
  intros x hx, rw set.mem_sUnion,
  have f' := @loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _,
  have sUnion_sub_of_finset_sub := sUnion_sub_of_finset_sub ε f ht,
-- writing `f⁻¹' U` as a union of basis elements (clopen sets)
  conv at sUnion_sub_of_finset_sub { congr, skip, rw set.sUnion_eq_Union, congr, funext,
    apply_congr classical.some_spec (classical.some_spec
    (topological_space.is_topological_basis.open_eq_sUnion f' (opens ε f i.prop))), },
  rw set.Union at sUnion_sub_of_finset_sub,
  have g3 := sUnion_sub_of_finset_sub hx,
  simp only [exists_prop, set.mem_Union, set.mem_range, set_coe.exists, exists_exists_eq_and,
    set.supr_eq_Union, set.mem_set_of_eq, subtype.coe_mk] at g3,
  rcases g3 with ⟨U, hU, a, ha, xa⟩,
  refine ⟨a, _, xa⟩,
  rw mem_set_clopen,
  simp only [exists_prop, set.mem_range, exists_exists_eq_and, set.mem_set_of_eq],
  refine ⟨U, hU, ha⟩,
end

/-- The image of each element of `set_clopen` is contained in an element of `S`. -/
lemma exists_B_of_mem_clopen (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) {x : set X} (hx : x ∈ set_clopen ε f ht) :
  ∃ (U : set X) (H : U ∈ B ε f), x ⊆ U :=
begin
  rw mem_set_clopen at hx,
  rcases hx with ⟨U, hU, xU⟩, refine ⟨U, hU, _⟩,
  obtain ⟨H, H1⟩ := classical.some_spec
    (topological_space.is_topological_basis.open_eq_sUnion
    (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) (@opens _ _ _ _ _ _ _ ε f U hU)),
  rw H1, intros u hu, simp only [exists_prop, set.mem_set_of_eq],
  refine ⟨x, _, hu⟩,
  convert xU,
  ext, simp only [exists_prop, iff_self],
end

/-- Every element of `set_clopen` is open. -/
lemma mem_set_clopen_is_open (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) (i : (set_clopen ε f ht)) : is_open (i : set X) :=
begin
  apply topological_space.is_topological_basis.is_open
    (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) ((set_clopen_sub_clopen_set ε f ht) i.2),
end

abbreviation f' := @loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _

/-- A restatement of `univ_sub_sUnion_set_clopen`. -/
lemma cover (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) :
  (set.univ : set X) ⊆ ⋃ (i : (set_clopen ε f ht)), ↑i :=
begin
  convert univ_sub_sUnion_set_clopen ε f ht,
  rw set.sUnion_eq_Union,
end

/-- Obtain a finite subcover of `set_clopen` using the compactness of `X`. -/
noncomputable abbreviation s' (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) := classical.some (is_compact.elim_finite_subcover
  (@compact_univ X _ _) _ (mem_set_clopen_is_open ε f ht) (cover ε f ht))
/-- `s'` covers `X`. -/
abbreviation h's (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) := classical.some_spec (is_compact.elim_finite_subcover
  (@compact_univ X _ _) _ (mem_set_clopen_is_open ε f ht) (cover ε f ht))
/-- Coercing a subset of `set_clopen` in `s'` to `set X`. -/
abbreviation s1 (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) := λ (x : s' ε f ht), (x.1 : set X)

/-- The range of `s1` is finite. -/
lemma fin (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) : (set.range (s1 ε f ht)).finite :=
by { apply set.finite_range _, exact plift.fintype (s' ε f ht), }

/-- Any element in the range of `s1` is clopen. -/
lemma is_clopen_x (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) {x : set X} (hx : x ∈ (fin ε f ht).to_finset) :
  is_clopen x :=
begin
  simp only [set.mem_range, set_coe.exists, set.finite.mem_to_finset, finset.mem_coe] at hx,
  rcases hx with ⟨⟨⟨v, hv⟩, hw⟩, hU⟩,
  convert (set_clopen_sub_clopen_set ε f ht) hv,
  rw ←hU,
  delta s1,
  simp,
end

/-- If there is a finite set of sets from `S` whose preimage forms a cover for `X`,
  then there is a finset of `sets X` containing clopen sets, with the image of each set being
  contained in an element of `S`. We use `s'` to get a finite disjoint clopen cover of `X`;
  note : it is not a partition -/
noncomputable def finset_clopen (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) : finset (set X) :=
  classical.some (is_clopen.clopen_Union_disjoint
    (set.finite.to_finset (fin ε f ht)) (λ x hx, (is_clopen_x ε f ht hx)))

-- The various parts of `is_clopen.clopen_Union_disjoint`, to be used for properties of `s`.
abbreviation clo (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) := (classical.some_spec (is_clopen.clopen_Union_disjoint
    (set.finite.to_finset (fin ε f ht)) (λ x hx, (is_clopen_x ε f ht hx)))).1
abbreviation hs (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) := (classical.some_spec (is_clopen.clopen_Union_disjoint
    (set.finite.to_finset (fin ε f ht)) (λ x hx, (is_clopen_x ε f ht hx)))).2.1
abbreviation sub (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) := (classical.some_spec (is_clopen.clopen_Union_disjoint
    (set.finite.to_finset (fin ε f ht)) (λ x hx, (is_clopen_x ε f ht hx)))).2.2.1
abbreviation disj (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) := (classical.some_spec (is_clopen.clopen_Union_disjoint
    (set.finite.to_finset (fin ε f ht)) (λ x hx, (is_clopen_x ε f ht hx)))).2.2.2

/-- Elements of `finset_clopen` are clopen. -/
lemma finset_clopen_is_clopen (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) {x : set X} (hx : x ∈ finset_clopen ε f ht) :
  is_clopen x := clo ε f ht x hx

/-- The image of every element of `finset_clopen` is contained in some element of `S`. -/
lemma exists_sub_S (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) {x : set X} (hx : x ∈ finset_clopen ε f ht) :
  ∃ U ∈ ((S ε) : set(set A)), (set.image f x : set A) ⊆ U :=
begin
  rcases sub ε f ht x hx with ⟨z, hz, wz⟩,
  simp only [set.mem_range, set_coe.exists, set.finite.mem_to_finset, finset.mem_coe] at hz,
  -- `z'` is a lift of `x` in `V`
  rcases hz with ⟨⟨⟨z', h1⟩, h2⟩, h3⟩,
  rcases exists_B_of_mem_clopen ε f ht h1 with ⟨U, BU, xU⟩,
  simp only [exists_prop, exists_exists_eq_and, set.mem_set_of_eq] at BU,
  cases BU with U' h4,
  refine ⟨U', h4.1, _⟩, transitivity (set.image f z),
  { apply set.image_subset _ wz, },
  { simp only [set.image_subset_iff], rw [←h4.2, ←h3],
    delta s1,
    simp only [xU, subtype.coe_mk], },
end

variables (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t) (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i)

/-- Showing that `finset_clopen` is a disjoint cover of `X`. -/
lemma finset_clopen_prop (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) (a : X) :
  ∃! (b : set X) (H : b ∈ finset_clopen ε f ht), a ∈ b :=
begin
-- proving that every element `a : X` is contained in a unique element `j` of `s`
  obtain ⟨j, hj, aj⟩ : ∃ j ∈ finset_clopen ε f ht, a ∈ j,
  { have ha := h's ε f ht (set.mem_univ a),
    have hs := hs ε f ht,
    delta s1 at hs,
    suffices : a ∈ ⋃₀ (finset_clopen ε f ht : set(set X)),
    { simp only [exists_prop, set.mem_set_of_eq, finset.mem_coe] at this,
      cases this with j hj, refine ⟨j, hj.1, hj.2⟩, },
    { rw finset_clopen,
      rw ←hs,
      simp only [set.mem_Union, set.finite.coe_to_finset, subtype.val_eq_coe, set.sUnion_range],
      simp only [exists_prop, set.mem_Union, set_coe.exists, exists_and_distrib_right,
        subtype.coe_mk] at ha,
      -- have the element `U` of `V`, now translate it to `s`
      rcases ha with ⟨U, ⟨hU, s'U⟩, aU⟩,
      delta s',
      refine ⟨⟨⟨U, hU⟩, s'U⟩, aU⟩, }, },
  refine ⟨j, _, λ y hy, _⟩,
  { -- existence
    simp only [exists_prop, set.image_subset_iff, set.mem_range, exists_exists_eq_and,
      exists_unique_iff_exists],
    refine ⟨hj, aj⟩, },
  { -- uniqueness, coming from the disjointness of the clopen cover, `disj`
    simp only [exists_prop, exists_unique_iff_exists] at hy,
    cases hy with h1 h2,
    have disj := disj ε f ht,
    specialize disj j y hj h1,
    by_cases h : j = y, { rw h.symm, },
    { exfalso, specialize disj h, rw ←set.mem_empty_eq, rw ←disj,
      apply set.mem_inter aj _,
      simp only [and_true, implies_true_iff, eq_iff_true_of_subsingleton] at h2,
      exact h2.1, }, },
end

noncomputable abbreviation c' := λ (s : set X) (H : s ∈ (finset_clopen ε f ht) ∧ nonempty s),
  classical.choice (H.2)

noncomputable abbreviation c2 (f : C(X, A)) (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) : X → A :=
λ x, f (c' ε f ht (classical.some (exists_of_exists_unique (finset_clopen_prop ε f ht x)) )
begin
  have := (exists_prop.1 (exists_of_exists_unique (classical.some_spec
    (exists_of_exists_unique (finset_clopen_prop ε f ht x))))),
  split,
  refine finset.mem_coe.1 (this).1,
  apply set.nonempty.to_subtype, rw set.nonempty, use x,
  apply this.2,
end).

/-- Any element of `finset_clopen` is open. -/
lemma mem_finset_clopen_is_open {U : set X} (hU : U ∈ finset_clopen ε f ht) : is_open U :=
begin
  rw finset_clopen at hU,
  apply (clo ε f ht U hU).1,
end

lemma loc_const : is_locally_constant (c2 ε f ht) :=
begin
  have c2 := c2 ε f ht, -- this line must be useless because c2 is data and have forgets defns
  --have ht1 := ht1 ε f ht,
  have finset_clopen_prop := finset_clopen_prop ε f ht,
  have ht4 : ∀ (a : X), ∃ (b : set X) (H : b ∈ (finset_clopen ε f ht)), a ∈ b,
   { rintros a, apply exists_of_exists_unique, simpa using finset_clopen_prop a },
--  show is_locally_constant c2,
  rw is_locally_constant.iff_exists_open, rintros x, specialize ht4 x,
      rcases ht4 with ⟨U, hU, xU⟩, use U, split, { apply mem_finset_clopen_is_open ε f ht hU, },
      use xU, rintros x' x'U, --rw _root_.c2,
      --simp,
      delta c2,
      apply congr_arg,
      have : classical.some (exists_of_exists_unique (finset_clopen_prop x)) = classical.some
        (exists_of_exists_unique (finset_clopen_prop x')),
      { congr, ext y, simp, rintros hy, split,
        { rintros xy, specialize finset_clopen_prop x, simp at finset_clopen_prop,
          cases finset_clopen_prop with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU xU,
          have hby := hby y hy xy, rw hby, rw ←hbU, apply x'U, },
          { rintros xy, specialize finset_clopen_prop x', simp at finset_clopen_prop,
            cases finset_clopen_prop with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU x'U,
            have hby := hby y hy xy, rw hby, rw ←hbU, apply xU, }, },
      congr',
      repeat { ext y, simp, rintros hy, split,
      { rintros xy, specialize finset_clopen_prop x', simp at finset_clopen_prop,
        cases finset_clopen_prop with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU x'U,
        have hby := hby y hy xy, rw hby, rw ←hbU, apply xU, },
        { rintros xy, specialize finset_clopen_prop x, simp at finset_clopen_prop,
          cases finset_clopen_prop with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU xU,
          have hby := hby y hy xy, rw hby, rw ←hbU, apply x'U, }, },
      simp, ext y, revert y,
      rw ← set.ext_iff, symmetry,
      { congr, ext y, simp, rintros hy, split,
        { rintros xy, specialize finset_clopen_prop x, simp at finset_clopen_prop,
          cases finset_clopen_prop with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU xU,
          have hby := hby y hy xy, rw hby, rw ←hbU, apply x'U, },
        { rintros xy, specialize finset_clopen_prop x', simp at finset_clopen_prop,
          cases finset_clopen_prop with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU x'U,
          have hby := hby y hy xy, rw hby, rw ←hbU, apply xU, }, },
end

theorem tp_dense [nonempty X] (hε : 0 < ε) (f : C(X, A)) (t : finset(set A))
 (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t) (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) :
  ∃ (b : C(X, A)) (H_1 : b ∈ set.range (inclusion X A)), dist f b < ε :=
begin
  --have ht1 := ht1 ε f ht, --have ht5 := ht1.2,
  have finset_clopen_prop := finset_clopen_prop ε f ht,
  have ht4 : ∀ (a : X), ∃ (b : set X) (H : b ∈ (finset_clopen ε f ht)), a ∈ b,
   { rintros a, apply exists_of_exists_unique, specialize finset_clopen_prop a, convert finset_clopen_prop, simp, },
   have loc_const := loc_const ε f ht,
   refine ⟨inclusion X A ⟨(c2 ε f ht), loc_const⟩, _, _⟩, { simp, },
/-     set b : locally_constant X A :=
      (∑ s in T', if H : s ∈ T' then ((f (c' s H)) • (char_fn X (c s H))) else 0) with hb, -/
    { have : dist f (inclusion X A ⟨(c2 ε f ht), loc_const⟩) ≤ (ε/2),
      { rw [dist_eq_norm, continuous_map.norm_eq_supr_norm],
        refine cSup_le _ _,
        { rw set.range_nonempty_iff_nonempty, assumption, },
        { rintros m hm, rw set.mem_range at hm, cases hm with y hy, rw ←hy, have finset_clopen_prop := finset_clopen_prop y,
          rcases finset_clopen_prop with ⟨w, wT, hw⟩,
          obtain ⟨w1, w2⟩ := exists_prop.1 (exists_of_exists_unique wT),
          have : (inclusion X A ⟨(c2 ε f ht), loc_const⟩) y =
                 f (c' ε f ht w ⟨w1, ⟨⟨y, w2⟩⟩⟩),
          { change c2 ε f ht y = _, --rw c2,
            --simp,
            delta c2,
            apply congr_arg,
            congr' 2, swap, congr, swap 3, congr,
            repeat { apply hw, refine classical.some_spec (exists_of_exists_unique (finset_clopen_prop y)), }, },
          convert_to ∥(f y) - ((inclusion X A ⟨(c2 ε f ht), loc_const⟩) y)∥ ≤ ε/2,
          { simp only [continuous_map.coe_sub, pi.sub_apply], },
          rw this, --obtain ⟨U, hU, wU⟩ := (ht1 w w1).2, --have yU := wU w2, simp at yU,
          --rw S at ht5, rw set.mem_range at ht5, cases ht5 with z hz,
          have ht5 := (exists_sub_S ε f ht w1), rcases ht5 with ⟨U, hU, wU⟩,
          --rw h at hz, simp only [continuous_map.to_fun_eq_coe] at hz,
          --rw S at hU,
          rw set.mem_range at hU, cases hU with z hz,
          have tired' : f (c' ε f ht w ⟨w1, ⟨⟨y, w2⟩⟩⟩) ∈ set.image f w,
          { simp,
            refine ⟨(c' ε f ht w ⟨w1, ⟨⟨y, w2⟩⟩⟩), _, _⟩, { simp, }, refl, },
          have tired := wU tired',
          have tS' : f y ∈ set.image f w, { simp, refine ⟨y, w2, _⟩, refl, },
          have tS := wU tS',
          --rw h at hz,
          rw hz.symm at tired, rw mem_ball_iff_norm at tired, rw hz.symm at tS,
          --have sub : f y - f ↑(c' w w1) = (f y - z) - (f ↑(c' w w1) - z),
          rw mem_ball_iff_norm at tS,
          conv_lhs { rw sub_eq_sub_add_sub _ _ z, },
          have : ε/2 = ε/4 + ε/4, { rw div_add_div_same, linarith, }, rw this,
          apply norm_add_le_of_le _ (le_of_lt tS),
          apply le_of_lt, rw ←norm_neg _, simp [tired], }, },
    rw le_iff_lt_or_eq at this, cases this, transitivity (ε/2), assumption, exact half_lt_self hε,
    { rw this, exact half_lt_self hε, }, },
end

variable (X)
theorem dense_C [nonempty X] : @dense (C(X, A)) _ (set.range (inclusion X A)) :=
begin
  rintros f,
  rw metric.mem_closure_iff,
  rintros ε hε,
  set h := λ (x : A), (metric.ball x (ε/4)) with h',
  set S := set.range h with hS,
  have g : (⋃₀ S) = set.univ,
  { rw set.sUnion_eq_univ_iff, rintros, refine ⟨metric.ball a (ε/4), _, _⟩, rw hS, rw set.mem_range,
    use a, simp, apply div_pos hε zero_lt_four, },
  set preh := set.preimage f (⋃₀ S) with preh',
  have g' : preh = set.univ,
  { rw preh', rw g, exact set.preimage_univ, },
  rw preh' at g',
  rw set.preimage_sUnion at g',
  rw set.subset.antisymm_iff at g',
  obtain ⟨t, ht⟩ := is_compact.elim_finite_subcover _ _ _ g'.2,
  { exact tp_dense ε hε f t ht, },
  { exact compact_univ, },
  { rintros i, apply is_open_Union, rintros hi, apply continuous.is_open_preimage _,
    { rw [hS, h'] at hi, simp at hi, cases hi with y hy,
      suffices : is_open (metric.ball y (ε/4)),
      { rw hy at this, assumption, },
      refine @metric.is_open_ball A _ y (ε/4), },
    exact continuous_map.continuous f, },
-- working with clopen sets makes life easy
end

end locally_constant.density

variables (X) (A)
def measures :=
  {φ : linear_map A (locally_constant X A) A //
    ∃ K : ℝ, 0 < K ∧ ∀ f : (locally_constant X A), ∥φ f∥ ≤ K * ∥inclusion X A f∥ }

noncomputable instance : normed_group (locally_constant X A) :=
normed_group.induced
  locally_constant.to_continuous_map_add_monoid_hom
  locally_constant.to_continuous_map_injective

variables {X} {A}
lemma integral_cont (φ : measures X A) : continuous (φ.1) :=
begin
  /-suffices : ∀ (b : locally_constant X A) (ε : ℝ), ε > 0 → (∃ (δ : ℝ) (H : δ > 0),
      ∀ (a : locally_constant X A), dist a b < δ → dist ((φ.val) a) ((φ.val) b) < ε),-/
  rw metric.continuous_iff, rintros b ε hε,
  obtain ⟨K, hKpos, hK⟩ := φ.prop,
  refine ⟨ε/K, div_pos hε hKpos, _⟩,
  rintros a dab, rw dist_eq_norm,
  rw ←linear_map.map_sub,
  specialize hK (a - b), apply lt_of_le_of_lt hK _, rw mul_comm, rw ←lt_div_iff hKpos,
  convert dab,
  change ∥inclusion X A (a - b)∥ = dist (inclusion X A a) (inclusion X A b),
  rw [dist_eq_norm, ← linear_map.map_sub],
  --refl,
end

variables (X) (A)
lemma di [nonempty X] : dense_inducing (inclusion X A) := ⟨⟨rfl⟩, locally_constant.density.dense_C X⟩

lemma uni_ind [nonempty X] : uniform_inducing (inclusion X A) := ⟨rfl⟩

variables {X} {A}
lemma uni_cont (φ : measures X A) : uniform_continuous ⇑(φ.val) :=
begin
  refine metric.uniform_continuous_iff.mpr _,
  rintros ε hε,
  obtain ⟨K, hKpos, hK⟩ := φ.prop,
  refine ⟨ε/K, div_pos hε hKpos, _⟩,
  rintros a b dab, rw dist_eq_norm,
  rw ←linear_map.map_sub,
  specialize hK (a - b), apply lt_of_le_of_lt hK _, rw mul_comm, rw ←lt_div_iff hKpos,
  convert dab,
  change ∥inclusion X A (a - b)∥ = dist (inclusion X A a) (inclusion X A b),
  rw [dist_eq_norm, ← linear_map.map_sub],
  --refl,
end

variables {X} {A}
lemma cont [complete_space A] [nonempty X] (φ : measures X A) :
  continuous ((di X A).extend (φ.val)) :=
begin
  refine uniform_continuous.continuous _,
  refine uniform_continuous_uniformly_extend _ (dense_inducing.dense (di X A)) _,
  { apply uni_ind, },
  { apply uni_cont, },
end

noncomputable def integral [nonempty X] (φ : measures X A) [complete_space A] :
  continuous_linear_map A C(X, A) A :=
begin
  have cont := cont φ,
  have di := di X A,
  split,
  swap,
  { split, swap 3,
    { --X nonempty needed here, for the topo space on loc const to exist
      apply dense_inducing.extend di (φ.1), },
    { refine dense_range.induction_on₂ (dense_inducing.dense di) _ _,
      { exact is_closed_eq (cont.comp continuous_add)
        ((cont.comp continuous_fst).add (cont.comp continuous_snd)) },
      { rintros a b,
        change di.extend (φ.val) (inclusion X A a + inclusion X A b) =
  di.extend (φ.val) (inclusion X A a) + di.extend (φ.val) (inclusion X A b),
        rw ← linear_map.map_add,
        change di.extend (φ.val) ((inclusion X A) (a + b)) =
  di.extend (φ.val) (inclusion X A a) + di.extend (φ.val) (inclusion X A b),
        repeat { rw dense_inducing.extend_eq di (integral_cont φ), },
        { simp only [linear_map.map_add], }, }, },
    { rintros m, refine (λ b, dense_range.induction_on (dense_inducing.dense di) b _ _),
      { exact is_closed_eq (cont.comp (continuous_const.smul continuous_id))
        ((continuous_const.smul continuous_id).comp cont) },
      { rintros a,
        change di.extend (φ.val) (m • inclusion X A a) =
        m • di.extend (φ.val) (inclusion X A a),
        rw ← linear_map.map_smul,
        change di.extend (φ.val) ((inclusion X A) (m • a)) =
        m • di.extend (φ.val) (inclusion X A a),
        repeat { rw dense_inducing.extend_eq di (integral_cont φ), },
        simp only [linear_map.map_smul], }, }, },
  simp only [auto_param_eq], assumption,
end
