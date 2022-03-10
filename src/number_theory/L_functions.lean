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

This file defines p-adic distributions and measure on the space of locally constant functions
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

variables (X : Type*) [topological_space X]
variables (A : Type*) [normed_comm_ring A]

/-- The A-linear injective map from `locally_constant X A` to `C(X, A)` -/
abbreviation inclusion : locally_constant X A →ₗ[A] C(X, A) :=
locally_constant.to_continuous_map_linear_map A

variable {X}
variables [compact_space X]

namespace set
lemma diff_inter_eq_empty {α : Type*} (a : set α) {b c : set α} (h : c ⊆ b) :
  a \ b ∩ c = ∅ :=
begin
  ext x,
  simp only [and_imp, mem_empty_eq, mem_inter_eq, not_and, mem_diff, iff_false],
  intro _,
  exact mt (@h x),
end


lemma diff_inter_mem_sUnion {α : Type*} {s : set (set α)} (a y : set α) (h : y ∈ s) :
  (a \ ⋃₀ s) ∩ y = ∅ :=
diff_inter_eq_empty a $ subset_sUnion_of_mem h

end set

namespace is_clopen

lemma is_closed_sUnion {H : Type*} [topological_space H]
  {s : finset(set H)} (hs : ∀ x ∈ s, is_closed x) :
  is_closed ⋃₀ (s : set(set H)) :=
by { simpa only [← is_open_compl_iff, set.compl_sUnion, set.sInter_image] using is_open_bInter
    (finset.finite_to_set s) (λ i hi, _), apply is_open_compl_iff.2 (hs i hi), }

lemma is_clopen_sUnion {H : Type*} [topological_space H]
  (s : finset(set H)) (hs : ∀ x ∈ s, is_clopen x) :
  is_clopen ⋃₀ (s : set(set H)) :=
⟨is_open_sUnion (λ t ht, (hs t ht).1), is_closed_sUnion (λ t ht, (hs t ht).2) ⟩

/-- The finite union of clopen sets is clopen. -/
lemma clopen_finite_Union {H : Type*} [topological_space H]
  (s : finset(set H)) (hs : ∀ x ∈ s, is_clopen x) :
  is_clopen ⋃₀ (s : set(set H)) :=
  by { rw set.sUnion_eq_bUnion, apply is_clopen_bUnion hs, }

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
  { use ∅, simp only [finset.not_mem_empty, forall_false_left, set.mem_empty_eq, forall_const,
      finset.coe_empty, eq_self_iff_true, and_self], },
  { rintros a S h's hS aS ⟨t, clo, union, sub, disj⟩,
    set b := a \ ⋃₀ S with hb,
    refine ⟨insert b t, _, _, ⟨λ x hx, _, λ x y hx hy ne, _⟩⟩,
    { rintros x hx,
      simp only [finset.coe_insert, set.mem_insert_iff, finset.mem_coe] at hx,
      cases hx,
      { rw hx, apply is_clopen.diff (hs a h's) (clopen_finite_Union _ (λ y hy, (hs y (hS hy)))), },
      { apply clo x hx, }, },
    { simp only [finset.coe_insert, set.sUnion_insert], rw [←union, set.diff_union_self], },
    { simp only [finset.mem_insert] at hx, cases hx,
      { use a, rw hx, simp only [true_and, true_or, eq_self_iff_true, finset.mem_insert],
        apply set.diff_subset, },
      { rcases sub x hx with ⟨z, hz, xz⟩, refine ⟨z, _, xz⟩,
        rw finset.mem_insert, right, assumption, }, },
    { rw finset.mem_insert at hx, rw finset.mem_insert at hy,
      have : ∀ y ∈ t, b ∩ y = ∅,
      { rintros y hy, rw [hb, union], apply set.diff_inter_mem_sUnion, assumption, },
      cases hx,
      { cases hy,
        { exfalso, apply ne, rw [hx, hy], },
        { rw hx, apply this y hy, }, },
      { cases hy,
        { rw set.inter_comm, rw hy, apply this x hx, },
        { apply disj x y hx hy ne, }, }, }, },
end

end is_clopen

namespace locally_constant.density

variables (ε : ℝ)

/-- Takes an element of `A` to an `ε/4`-ball centered around it. -/
abbreviation h {A : Type*} [normed_ring A] : A → set A :=
  λ (x : A), metric.ball x (ε / 4)

/-- The set of (ε/4)-balls. -/
abbreviation S {A : Type*} [normed_ring A] : set (set A) := set.range (h ε)

variables {A} (f : C(X, A))

/-- Preimage of (ε/4)-balls. -/
abbreviation B : set(set X) := { j : set X | ∃ (U ∈ ((S ε) : set(set A))), j = f ⁻¹' U }

lemma opens {j : set X} (hj : j ∈ (B ε f)) : is_open j :=
begin
  rcases hj with ⟨hj_w, ⟨hj_h_w_w, rfl⟩, rfl⟩,
  exact continuous.is_open_preimage f.2 _ (metric.is_open_ball),
end

variable [fact (0 < ε)]
/-- `X` is covered by a union of preimage of finitely many elements of `S` under `f` -/
lemma exists_finset_univ_sub : ∃ (t : finset (set A)), set.univ ⊆ ⨆ (i : set A) (H : i ∈ t)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i :=
begin
  have g : (⋃₀ S ε) = (set.univ : set A),
  { rw set.sUnion_eq_univ_iff, rintros, refine ⟨metric.ball a (ε/4), _, _⟩,
    { simp only [set.mem_range, exists_apply_eq_apply], },
    { simp only [metric.mem_ball, dist_self],
      refine div_pos (fact.out _) zero_lt_four, }, },
  have g' : set.preimage f (⋃₀ S ε) = set.univ,
  { rw g, exact set.preimage_univ, },
  rw [set.preimage_sUnion, set.subset.antisymm_iff] at g',
  refine is_compact.elim_finite_subcover compact_univ _ (λ i, is_open_Union
    (λ hi, continuous.is_open_preimage (continuous_map.continuous f) i _)) g'.2,
  cases hi with y hy, rw [←hy], refine @metric.is_open_ball A _ y (ε/4),
end

/-- Choosing a finset as given in `exists_finset_univ_sub` -/
noncomputable abbreviation t : finset (set A) := classical.some (exists_finset_univ_sub ε f)

lemma exists_finset_univ_sub_prop : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t ε f)
  (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i := classical.some_spec (exists_finset_univ_sub ε f)

/-- If there is a finite set of sets from `S` whose preimage forms a cover for `X`,
  then the union of the preimages of all the sets from `S` also forms a cover. -/
lemma sUnion_sub_of_finset_sub : set.univ ⊆ set.sUnion (B ε f) :=
begin
  rintros x hx,
  obtain ⟨-, ⟨j, rfl⟩, -, ⟨hj, rfl⟩, -, ⟨⟨a, jS⟩, rfl⟩, fj⟩ := (exists_finset_univ_sub_prop ε f) hx,
  exact ⟨f⁻¹' j, ⟨j, ⟨_, jS⟩, rfl⟩, fj⟩,
end

variables [t2_space X] [totally_disconnected_space X]

/-- If there is a finite set of sets from `S` whose preimage forms a cover for `X`,
  then there is a cover of `X` by clopen sets, with the image of each set being
  contained in an element of `S`. -/
def set_clopen : set (set X) := {j : set X | ∃ (U : set X) (hU : U ∈ (B ε f)),
    j ∈ classical.some (topological_space.is_topological_basis.open_eq_sUnion
    (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) (opens ε f hU))}

lemma mem_set_clopen {x : set X} : x ∈ (set_clopen ε f) ↔ ∃ (U : set X) (hU : U ∈ (B ε f)),
    x ∈ classical.some (topological_space.is_topological_basis.open_eq_sUnion
    (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) (opens ε f hU)) := iff.rfl

/-- Elements of `set_clopen` are clopen. -/
lemma set_clopen_sub_clopen_set : (set_clopen ε f) ⊆ {s : set X | is_clopen s} :=
begin
  intros j hj,
  obtain ⟨W, hW, hj⟩ := (mem_set_clopen ε f).1 hj,
  obtain ⟨H, -⟩ := classical.some_spec (topological_space.is_topological_basis.open_eq_sUnion
    (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) (opens ε f hW)),
  exact H hj,
end

/-- `set_clopen` covers X. -/
lemma univ_sub_sUnion_set_clopen : set.univ ⊆ ⋃₀ (set_clopen ε f) :=
begin
  rintros x hx, rw set.mem_sUnion,
  have f' := @loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _,
  have sUnion_sub_of_finset_sub := sUnion_sub_of_finset_sub ε f,
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
lemma exists_B_of_mem_clopen {x : set X} (hx : x ∈ set_clopen ε f) :
  ∃ (U : set X) (H : U ∈ B ε f), x ⊆ U :=
begin
  rcases hx with ⟨U, hU, xU⟩, refine ⟨U, hU, _⟩,
  obtain ⟨H, H1⟩ := classical.some_spec
    (topological_space.is_topological_basis.open_eq_sUnion
    (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) (opens ε f hU)),
  rw H1, intros u hu, simp only [exists_prop, set.mem_set_of_eq],
  refine ⟨x, _, hu⟩,
  convert xU,
  ext, simp only [exists_prop, iff_self],
end

/-- Every element of `set_clopen` is open. -/
lemma mem_set_clopen_is_open (i : (set_clopen ε f)) : is_open (i : set X) :=
 topological_space.is_topological_basis.is_open (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _)
  ((set_clopen_sub_clopen_set ε f) i.2)

/-- A restatement of `univ_sub_sUnion_set_clopen`. -/
lemma cover : (set.univ : set X) ⊆ ⋃ (i : (set_clopen ε f)), ↑i :=
by { convert univ_sub_sUnion_set_clopen ε f, rw set.sUnion_eq_Union, }

/-- Obtain a finite subcover of `set_clopen` using the compactness of `X`. -/
noncomputable abbreviation s' := classical.some (is_compact.elim_finite_subcover
  (@compact_univ X _ _) _ (mem_set_clopen_is_open ε f) (cover ε f))

/-- Coercing a subset of `set_clopen` in `s'` to `set X`. -/
abbreviation s1 := λ (x : s' ε f), (x.1 : set X)

/-- The range of `s1` is finite. -/
lemma fin : (set.range (s1 ε f)).finite :=
by { apply set.finite_range _, exact plift.fintype (s' ε f), }

/-- Any element in the range of `s1` is clopen. -/
lemma is_clopen_x {x : set X} (hx : x ∈ (fin ε f).to_finset) : is_clopen x :=
begin
  simp only [set.mem_range, set_coe.exists, set.finite.mem_to_finset, finset.mem_coe] at hx,
  rcases hx with ⟨⟨⟨v, hv⟩, hw⟩, hU⟩,
  convert (set_clopen_sub_clopen_set ε f) hv,
  rw ←hU,
  delta s1,
  simp,
end

/-- If there is a finite set of sets from `S` whose preimage forms a cover for `X`,
  then there is a finset of `sets X` containing clopen sets, with the image of each set being
  contained in an element of `S`. We use `s'` to get a finite disjoint clopen cover of `X`;
  note : it is not a partition -/
noncomputable def finset_clopen : finset (set X) :=
  classical.some (is_clopen.clopen_Union_disjoint
    (set.finite.to_finset (fin ε f)) (λ x hx, (is_clopen_x ε f hx)))

/-- Elements of `finset_clopen` are clopen. -/
lemma finset_clopen_is_clopen {x : set X} (hx : x ∈ finset_clopen ε f) : is_clopen x :=
  (classical.some_spec (is_clopen.clopen_Union_disjoint (set.finite.to_finset (fin ε f))
    (λ x hx, (is_clopen_x ε f hx)))).1 x hx

/-- The image of every element of `finset_clopen` is contained in some element of `S`. -/
lemma exists_sub_S {x : set X} (hx : x ∈ finset_clopen ε f) :
  ∃ U ∈ ((S ε) : set(set A)), (set.image f x : set A) ⊆ U :=
begin
  rcases (classical.some_spec (is_clopen.clopen_Union_disjoint
    (set.finite.to_finset (fin ε f)) (λ x hx, (is_clopen_x ε f hx)))).2.2.1 x hx with ⟨z, hz, wz⟩,
  simp only [set.mem_range, set_coe.exists, set.finite.mem_to_finset, finset.mem_coe] at hz,
  -- `z'` is a lift of `x` in `V`
  rcases hz with ⟨⟨⟨z', h1⟩, h2⟩, h3⟩,
  rcases exists_B_of_mem_clopen ε f h1 with ⟨U, BU, xU⟩,
  simp only [exists_prop, exists_exists_eq_and, set.mem_set_of_eq] at BU,
  cases BU with U' h4,
  refine ⟨U', h4.1, _⟩, transitivity (set.image f z),
  { apply set.image_subset _ wz, },
  { simp only [set.image_subset_iff], rw [←h4.2, ←h3],
    delta s1,
    simp only [xU, subtype.coe_mk], },
end

/-- Showing that `finset_clopen` is a disjoint cover of `X`. -/
lemma finset_clopen_prop (a : X) : ∃! (b ∈ finset_clopen ε f), a ∈ b :=
begin
-- proving that every element `a : X` is contained in a unique element `j` of `s`
  obtain ⟨j, hj, aj⟩ : ∃ j ∈ finset_clopen ε f, a ∈ j,
  { -- `s'` covers `X`
    have ha := classical.some_spec (is_compact.elim_finite_subcover
      (@compact_univ X _ _) _ (mem_set_clopen_is_open ε f) (cover ε f)) (set.mem_univ a),
    have hs := (classical.some_spec (is_clopen.clopen_Union_disjoint
      (set.finite.to_finset (fin ε f)) (λ x hx, (is_clopen_x ε f hx)))).2.1,
    delta s1 at hs,
    suffices : a ∈ ⋃₀ (finset_clopen ε f : set(set X)),
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
    have disj := (classical.some_spec (is_clopen.clopen_Union_disjoint
      (set.finite.to_finset (fin ε f)) (λ x hx, (is_clopen_x ε f hx)))).2.2.2 j y hj h1,
    by_cases h : j = y,
    { rw h.symm, },
    { exfalso, specialize disj h, rw ←set.mem_empty_eq, rw ←disj,
      apply set.mem_inter aj _,
      simp only [and_true, implies_true_iff, eq_iff_true_of_subsingleton] at h2,
      exact h2.1, }, },
end

/-- Takes a nonempty `s` in `finset_clopen` and returns an element of it. -/
noncomputable abbreviation c' := λ (s : set X) (H : s ∈ (finset_clopen ε f) ∧ nonempty s),
  classical.choice (H.2)

/-- Any `x` in `X` must belong to a unique `s` in `finset_clopen`. `c2` takes `x` to the image of
  any element of `s` under `f`, which is the same `f x`. -/
noncomputable abbreviation c2 (f : C(X, A)) : X → A :=
λ x, f (c' ε f (classical.some (exists_of_exists_unique (finset_clopen_prop ε f x)) )
begin
  have := (exists_prop.1 (exists_of_exists_unique (classical.some_spec
    (exists_of_exists_unique (finset_clopen_prop ε f x))))),
  split,
  refine finset.mem_coe.1 (this).1,
  apply set.nonempty.to_subtype,
  refine ⟨x, this.2⟩,
end).

/-- Any element of `finset_clopen` is open. -/
lemma mem_finset_clopen_is_open {U : set X} (hU : U ∈ finset_clopen ε f) : is_open U :=
by { rw finset_clopen at hU, apply (finset_clopen_is_clopen ε f hU).1, }

/-- An equivalent version of `disj`. -/
lemma mem_finset_clopen_unique' {U V : set X} {y : X}
  (hU : U ∈ finset_clopen ε f) (hUy : y ∈ U) (hVy : y ∈ V) (hV : V ∈ finset_clopen ε f) : V = U :=
begin
  by_contra,
  have := (classical.some_spec (is_clopen.clopen_Union_disjoint
    (set.finite.to_finset (fin ε f)) (λ x hx, (is_clopen_x ε f hx)))).2.2.2 _ _ hV hU h,
  revert this,
  --change (V ∩ U) ≠ ∅,
  refine set.nonempty.ne_empty ⟨y, set.mem_inter hVy hUy⟩,
end

/-- Given `x` in `X`, there is a unique element `U` of `finset_clopen` such that `x ∈ U`. For any
  `y ∈ U`, `y` is contained in any other element `V` of `finset_clopen` containing `x`. -/
lemma mem_finset_clopen_unique {U V : set X} {x y : X}
  (U_prop : (U ∈ finset_clopen ε f ∧ x ∈ U) ∧ ∀ (y : set X), y ∈ finset_clopen ε f →
    x ∈ y → y = U) (hy : y ∈ U) (hV : V ∈ finset_clopen ε f) : x ∈ V ↔ y ∈ V :=
begin
  obtain ⟨W, hW⟩ := finset_clopen_prop ε f y,
  simp only [and_imp, exists_prop, exists_unique_iff_exists] at hW,
  split; intro h,
  { rw U_prop.2 V hV h, assumption, },
  { rw hW.2 V hV h, rw ←(hW.2 U U_prop.1.1 hy), apply U_prop.1.2, },
end

/-- `c2` is locally constant -/
lemma loc_const : is_locally_constant (c2 ε f) :=
begin
  rw is_locally_constant.iff_exists_open, rintros x,
  obtain ⟨U, hU⟩ := finset_clopen_prop ε f x,
  simp only [and_imp, exists_prop, exists_unique_iff_exists] at hU,
  refine ⟨U, mem_finset_clopen_is_open ε f hU.1.1, hU.1.2, λ x' hx', _⟩,
  delta c2,
  congr',
  swap 4, ext y, revert y, rw ←set.ext_iff, congr, -- is there a better way to do this?
  any_goals
  { ext y, simp only [exists_prop, and.congr_right_iff, exists_unique_iff_exists],
    intro hy, symmetry, apply mem_finset_clopen_unique ε f hU hx' hy, },
end

/-- Given an `f ∈ C(X, A)` and an `ε > 0`, one can find a locally constant function `b` which is in
  an ε-ball with center `f`, `b` is precisely `c2`. -/
theorem loc_const_dense' : ∃ (b : C(X, A)) (H_1 : b ∈ set.range (inclusion X A)),
  dist f b < ε := ⟨inclusion X A ⟨c2 ε f, loc_const ε f⟩, ⟨⟨c2 ε f, loc_const ε f⟩, rfl⟩,
  gt_of_gt_of_ge (half_lt_self (fact.out _))
begin
-- showing that the distance between `f` and `c2` is less than or equal to `ε/2`
  rw [dist_eq_norm, continuous_map.norm_eq_supr_norm],
  -- empty type is special case
  cases is_empty_or_nonempty X with hempty hnonempty,
  { change _ ≥ dite _ _ _,
    split_ifs with h,
    { rcases h with ⟨⟨_, x, _⟩, _⟩,
      exact (@is_empty.false _ hempty x).elim },
    exact le_of_lt (half_pos (fact.out _)) },
-- writing the distance in terms of the sup norm
  refine cSup_le _ (λ m hm, _),
  { rw set.range_nonempty_iff_nonempty, assumption, }, -- this is where `nonempty X` is needed
  { cases hm with y hy,
    simp only [continuous_map.coe_sub, locally_constant.coe_mk,
      locally_constant.to_continuous_map_linear_map_apply, pi.sub_apply,
      locally_constant.coe_continuous_map] at hy,
    rw ←hy,
    -- reduced to proving ∥f(y) - c2(y)∥ ≤ ε/2
    obtain ⟨w, wT, hw⟩ := finset_clopen_prop ε f y,
    -- `w` is the unique element of `finset_clopen` to which `y` belongs
    simp only [exists_prop, exists_unique_iff_exists] at wT,
    simp only [and_imp, exists_prop, exists_unique_iff_exists] at hw,
    have : c2 ε f y = f (c' ε f w ⟨wT.1, ⟨⟨y, wT.2⟩⟩⟩),
    -- showing that `w` is the same as the `classical.some _` used in `c2`
    { delta c2, congr',
      any_goals
      { have := classical.some_spec (exists_of_exists_unique (finset_clopen_prop ε f y)),
        simp only [exists_prop, exists_unique_iff_exists] at *,
        apply hw _ (this.1) (this.2), }, },
    rw this,
    obtain ⟨U, hU, wU⟩ := exists_sub_S ε f wT.1,
    -- `U` is a set of `A` which is an element of `S` and contains `f(w)`
    cases hU with z hz,
    -- `U` is the `ε/4`-ball centered at `z`
    have mem_U : f (c' ε f w ⟨wT.1, ⟨⟨y, wT.2⟩⟩⟩) ∈ U :=
      wU ⟨(c' ε f w ⟨wT.1, ⟨⟨y, wT.2⟩⟩⟩), subtype.coe_prop _, rfl⟩,
    have tS : f y ∈ U := wU ⟨y, wT.2, rfl⟩,
    rw [hz.symm, mem_ball_iff_norm] at *,
    conv_lhs { rw sub_eq_sub_add_sub _ _ z, },
    -- unfolding everything in terms of `z`, and then using `mem_U` and `tS`
    have : ε/2 = ε/4 + ε/4, { rw div_add_div_same, linarith, },
    rw this, apply norm_add_le_of_le (le_of_lt _) (le_of_lt tS),
    rw ←norm_neg _, simp only [mem_U, neg_sub], },
end ⟩

variable (X)
/-- The locally constant functions from `X` to `A` (viewed as a subset of C(X, A)) are dense
  in C(X, A). -/
theorem loc_const_dense : dense (set.range (inclusion X A)) :=
  λ f, begin
  rw metric.mem_closure_iff,
  rintros ε hε,
  haveI : fact (0 < ε) := fact.mk hε,
-- we have all the ingredients from `loc_const_dense'`, only need `exists_finset_univ_sub_prop`
  apply loc_const_dense' ε f,
end

end locally_constant.density

variables (X) (A)

/-- Given a profinite space `X` and a normed commutative ring `A`, a `p-adic measure` is a
  "bounded" linear map from the locally constant functions from `X` to `A` to `A` -/
def measures :=
  {φ : (locally_constant X A) →ₗ[A] A //
    ∃ K : ℝ, 0 < K ∧ ∀ f : (locally_constant X A), ∥φ f∥ ≤ K * ∥inclusion X A f∥ }

instance : has_zero (measures X A) :=
{ zero := ⟨0, ⟨1, ⟨zero_lt_one,
  λ f, by { simp only [norm_zero, one_mul, norm_nonneg, linear_map.zero_apply], } ⟩ ⟩ ⟩, }

noncomputable instance : inhabited (measures X A) := classical.inhabited_of_nonempty'

/-- Giving `locally_constant` the normed group structure induced from `C(X, A)` -/
noncomputable instance : normed_group (locally_constant X A) :=
  normed_group.induced locally_constant.to_continuous_map_add_monoid_hom
  locally_constant.to_continuous_map_injective

-- probably should be "measure"
namespace measure
open locally_constant.density

variables {X} {A}

instance : has_coe_to_fun (measures X A) :=
{ F := _,
  coe := λ φ, φ.1, }

/-- Any measure is uniformly continuous -/
lemma uniform_continuous (φ : measures X A) : uniform_continuous ⇑φ :=
begin
  refine metric.uniform_continuous_iff.mpr (λ ε hε, _),
  obtain ⟨K, hKpos, hK⟩ := φ.prop,
  refine ⟨ε/K, div_pos hε hKpos, λ a b dab, _⟩, -- 0 < K needed here
  rw [dist_eq_norm, ←linear_map.map_sub],
  specialize hK (a - b), apply lt_of_le_of_lt hK _, rw [mul_comm, ←lt_div_iff hKpos],
  convert dab,
  change ∥inclusion X A (a - b)∥ = dist (inclusion X A a) (inclusion X A b),
  rw [dist_eq_norm, ← linear_map.map_sub],
end

lemma integral_cont (φ : measures X A) : continuous ⇑φ :=
  uniform_continuous.continuous (uniform_continuous _)

variables (X) (A)

/-- The inclusion map from `locally_constant X A` to `C(X, A)` is uniform inducing -/
lemma uni_ind : uniform_inducing (inclusion X A) := ⟨rfl⟩

variables [t2_space X] [totally_disconnected_space X]

/-- The inclusion map from `locally_constant X A` to `C(X, A)` is dense inducing -/
lemma dense_ind_inclusion : dense_inducing (inclusion X A) :=
  ⟨⟨rfl⟩, loc_const_dense X⟩

variables {X} {A}

/-- If `A` is a complete space, the extension of `measure X A` to C(X, A) → A is
  uniformly continuous -/
lemma uniform_continuous_extend [complete_space A] (φ : measures X A) :
  _root_.uniform_continuous ((dense_ind_inclusion X A).extend ⇑φ) :=
  uniform_continuous_uniformly_extend (uni_ind X A)
    (dense_inducing.dense (dense_ind_inclusion X A)) (uniform_continuous φ)

/-- The extension of `measures X A` to C(X, A) → A is continuous when `A` is a complete space -/
lemma cont [complete_space A] (φ : measures X A) :
  continuous ((dense_ind_inclusion X A).extend ⇑φ) :=
  uniform_continuous.continuous (uniform_continuous_extend φ)

/-- The extended map is additive -/
lemma map_add_extend [complete_space A] (φ : measures X A) (x y : C(X, A)) :
  (dense_ind_inclusion X A).extend ⇑φ (x + y) =
  (dense_ind_inclusion X A).extend ⇑φ x + (dense_ind_inclusion X A).extend ⇑φ y :=
begin
  have cont := cont φ,
  have di := dense_ind_inclusion X A,
--   it is sufficient to restrict to `inclusion`, since it has dense range
  refine dense_range.induction_on₂ di.dense
    (is_closed_eq (cont.comp continuous_add)
      ((cont.comp continuous_fst).add (cont.comp continuous_snd))) (λ a b, _) x y,
--   restricting to `inclusion`
    rw ← linear_map.map_add,
    simp only [dense_inducing.extend_eq di (integral_cont φ), linear_map.map_add ⇑φ a b],
end

/-- The extended map preserves smul -/
lemma map_smul_extend [complete_space A] (φ : measures X A) (m : A) (x : C(X, A)) :
  (dense_ind_inclusion X A).extend ⇑φ (m • x) =
  m • (dense_ind_inclusion X A).extend ⇑φ x :=
begin
  let : has_continuous_smul A C(X, A) := continuous_map.has_continuous_smul X,
  have cont := cont φ,
  have di := dense_ind_inclusion X A,
--   it is sufficient to restrict to `inclusion`, since it has dense range
  refine dense_range.induction_on di.dense x
    (is_closed_eq (cont.comp (continuous_const.smul continuous_id))
      ((continuous_const.smul continuous_id).comp cont)) (λ a, _),
--   restricting to `inclusion`
    rw ← linear_map.map_smul,
    simp only [dense_inducing.extend_eq di (integral_cont φ), linear_map.map_smul ⇑φ m a],
end

/-- Given a profinite space `X` and a normed commutative ring `A`, and a `p-adic measure` φ, the
  `p-adic integral` on a locally constant function `f` from `X` to `A` is φ(f). This map can then
  be extended continuously and linearly to C(X, A), due to `loc_const_dense`. We use the dense
  inducing and uniform continuity properties of the map `inclusion X A`. -/
noncomputable def integral [complete_space A] (φ : measures X A) :
  continuous_linear_map A C(X, A) A :=
  ⟨{ to_fun := dense_inducing.extend (dense_ind_inclusion X A) (φ.1),
     map_add' := λ x y, map_add_extend φ x y,
     map_smul' := λ m x, map_smul_extend φ m x, },
     cont φ⟩

end measure
