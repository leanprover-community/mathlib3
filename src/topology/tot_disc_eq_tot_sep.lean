/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Kevin Buzzard
-/
import topology.continuous_function.bounded

/-!
# File contents
We prove that a locally compact Hausdorff space is totally disconnected
if and only if it is totally separated, `loc_compact_t2_tot_disc_iff_tot_sep`.
This is an important property used to define a generalized integral on profinite spaces.

The proof relies on first proving the same for compact spaces. One implication is obvious.
For the other side, we prove an equivalent statement : the space has a basis of clopens.
-/

open classical

namespace compact_space

/-- A compact Hausdorff space is totally disconnected if and only if it is totally separated, this
  is also true for locally compact spaces. -/
theorem compact_t2_tot_disc_iff_tot_sep (H : Type*) [topological_space H] [compact_space H]
  [t2_space H] : totally_disconnected_space H ↔ totally_separated_space H :=
begin
  split,
  { intro h, constructor,
    rintros x - y - hxy,
    by_contradiction g,
    simp only [not_exists, not_and, exists_and_distrib_left] at g,
    suffices g' : y ∈ connected_component x,
    { rw [totally_disconnected_space_iff_connected_component_singleton.1 h x,
      set.mem_singleton_iff] at g',
      apply hxy g'.symm, },
    rw [connected_component_eq_Inter_clopen, set.mem_Inter],
    classical, by_contradiction,
    simp only [and_imp, exists_prop, subtype.forall, subtype.coe_mk, not_forall] at h,
    rcases h with ⟨Z, hZ, hZy⟩, cases hZ with hZ hZx,
    have g' := g Z hZ.1 Zᶜ (is_clopen_compl hZ).1 hZx hZy,
    simpa using g' },
  apply totally_separated_space.totally_disconnected_space,
end

end compact_space

variables {H : Type*} [topological_space H]

namespace totally_separated_space

lemma exists_clopen_of_tot_sep [totally_separated_space H]
  (x y : H) (hxy : x ≠ y) : ∃ (U : set H) (hU : is_clopen U), x ∈ U ∧ y ∈ Uᶜ :=
begin
  obtain ⟨U, V, hU, hV, Ux, Vy, f, disj⟩ :=
    totally_separated_space.is_totally_separated_univ H x (set.mem_univ x) y (set.mem_univ y) hxy,
  have clopen_U := is_clopen_inter_of_disjoint_cover_clopen (is_clopen_univ) f hU hV disj,
  rw set.univ_inter _ at clopen_U,
  have g : V = Uᶜ,
  { rw set.univ_subset_iff at f,
    rw [set.compl_eq_univ_diff _, <-f, set.union_diff_left], symmetry',
    rw set.diff_eq_self, simp_rw disj,},
  rw g at Vy, refine ⟨U, clopen_U, Ux, Vy⟩,
end

end totally_separated_space

lemma ne_mem_of_mem_compl {α : Type*} {x : α} {U : set α} (H : x ∈ U) :
  ∀ (y : α) (Uy : y ∈ Uᶜ), x ≠ y :=
begin
  rintros y Uy,
  classical,
  by_contradiction,
  push_neg at h, rw h at H,
  have f := set.mem_inter H Uy,
  rw [set.inter_compl_self _, set.mem_empty_eq] at f, assumption,
end

namespace compact_space

/-- Every member of an open set in a compact Hausdorff totally disconnected space
  is contained in a clopen set contained in the open set.  -/
lemma compact_exists_clopen_in_open [compact_space H] [t2_space H]
  [totally_disconnected_space H] {x : H} {U : set H} (is_open : is_open U) (memU : x ∈ U) :
    ∃ (V : set H) (hV : is_clopen V), x ∈ V ∧ V ⊆ U :=
begin
  by_cases Uᶜ = ∅,
  { rw set.compl_empty_iff at h, rw h,
    refine ⟨set.univ, is_clopen_univ, set.mem_univ x, set.subset_univ _⟩, },
  { have f : totally_separated_space H,
    { refine (compact_space.compact_t2_tot_disc_iff_tot_sep H).1 _, apply_instance, },
    have ex : ∀ (y : H) (hy : y ∈ Uᶜ), ∃ (V : set H), is_clopen V ∧ (y ∈ V ∧ x ∈ Vᶜ),
    { rintros y hy,
      rw ←compl_compl U at memU,
      obtain ⟨U, hU, Uy, Ux⟩ :=
        @totally_separated_space.exists_clopen_of_tot_sep _ _ f y x
          (ne_mem_of_mem_compl hy x memU),
      refine ⟨U, hU, Uy, Ux⟩, },
    set h := λ (y : H) (hy : y ∈ Uᶜ), some (ex y hy) with fh,
    set V := (⨆ (y : H) (hy : y ∈ Uᶜ), h y hy) with hV,
    have sub : Uᶜ ⊆ V,
    { intros y hy,
      rw [hV, set.mem_Union],
      use y, rw set.mem_Union, use hy,
      obtain ⟨g1, g2, g3⟩ := some_spec (ex y hy),
      refine g2, },
    rw hV at sub,
    rw ←is_closed_compl_iff at is_open,
    have comp : is_compact Uᶜ := by { exact is_closed.compact is_open},
    obtain ⟨t, fin⟩ := is_compact.elim_finite_subcover comp _ _ sub,
    { rw set.compl_subset_comm at fin,
      set W := (⨆ (i : H) (H_1 : i ∈ t), (λ (y : H), ⨆ (hy : y ∈ Uᶜ), h y hy) i)ᶜ with hW,
      rw [set.compl_Union] at hW,
      refine ⟨W, _, _, fin⟩,
      { have g : fintype (t : set H), { exact finset_coe.fintype t, },
        rw hW,
        suffices f : ∀ y : ((t : set H) ∩ Uᶜ),
          is_clopen (h y.val ((set.mem_inter_iff y.val _ _).1 y.property).2)ᶜ,
        { classical,
          have g := is_clopen_Inter f,
          simp only [subtype.val_eq_coe] at g,
          have h' : (⋂ (i : H) (i_1 : i ∈ t) (i_1 : i ∈ Uᶜ), (h i i_1)ᶜ) = ⋂ (i : (↑t ∩ Uᶜ)),
            (h ↑i ((set.mem_inter_iff i.val _ _).1 i.property).2)ᶜ,
          { ext, split,
            { rintros a,
              rw set.mem_Inter at *,
              rintros j, specialize a j,
              rw set.mem_Inter at *,
              have b := a ((set.mem_inter_iff j.val _ _).1 j.property).1,
              rw set.mem_Inter at *,
              specialize b ((set.mem_inter_iff j.val _ _).1 j.property).2,
              exact b, },
            { rintros a,
              rw set.mem_Inter at *,
              rintros j, rw set.mem_Inter,
              rintros b,
              rw set.mem_Inter,
              rintros c, specialize a ⟨j, set.mem_inter b c⟩,
              exact a, }, },
          conv { congr, congr, funext, rw [set.compl_Union],
                 conv { congr, funext, rw [set.compl_Union], }, },
          rw [h'], apply g, },
        { rintros y,
          obtain ⟨g1, g2, g3⟩ :=
            some_spec (ex y.val ((set.mem_inter_iff y.val _ _).1 y.property).2),
          apply is_clopen_compl, refine g1, }, },
      { rw [hW, set.mem_Inter],
        rintros i,
        conv { congr, congr, funext, rw [set.compl_Union],
               conv { congr, funext, rw [set.compl_Union], }, },
        rw set.mem_Inter,
        rintros hi,
        rw set.mem_Inter,
        rintros Ui,
        obtain ⟨g1, g2, g3⟩ := some_spec (ex i Ui),
        refine g3, }, },
    {  rintros i,
       apply is_open_Union,
       rintros hi,
       obtain ⟨g1, g2, g3⟩ := some_spec (ex i hi),
      refine g1.1, }, },
end

end compact_space

open_locale topological_space filter

namespace t2_space

/-- A Hausdorff space with a clopen basis is totally separated. -/
lemma tot_sep_of_zero_dim [t2_space H]
  (h : ∃ (B : set (set H)) (hB : topological_space.is_topological_basis B), ∀ x ∈ B, is_clopen x)
    : totally_separated_space H :=
begin
  constructor,
  rw is_totally_separated,
  apply @t2_space.cases_on H _ _ _ _, { assumption, },
  rintros a x hx y hy ne,
  obtain ⟨U, V, hU, hV, xU, yV, disj⟩ := a x y ne,
  rcases h with ⟨B, hB, h⟩,
  obtain ⟨W, hW, xW, Wsub⟩ := topological_space.is_topological_basis.exists_subset_of_mem_open
    hB xU hU,
  specialize h W hW,
  have yW : y ∈ Wᶜ,
  { rw set.mem_compl_iff W y,
    contrapose disj, rw [set.not_not_mem] at disj,
    have g := set.mem_inter (Wsub disj) yV,
    apply set.nonempty.ne_empty,
    change' set.nonempty (U ∩ V), apply set.nonempty_of_mem g, },
  refine ⟨W, Wᶜ, h.1, (is_clopen_compl h).1, xW, yW, _, set.inter_compl_self W⟩,
  rw set.union_compl_self,
end

end t2_space

namespace locally_compact_space

/-- A locally compact Hausdorff totally disconnected space has a basis with clopen elements. -/
lemma loc_compact_Haus_tot_disc_of_zero_dim (α : Type*) [topological_space α]
  [locally_compact_space α] [t2_space α] [totally_disconnected_space α] :
  ∃ (B : set (set α)) (hB : topological_space.is_topological_basis B), ∀ x ∈ B, is_clopen x :=
begin
  set C := {Z : set α | is_clopen Z} with hC,
  have h_open : ∀ Z ∈ C, is_open Z,
  { rintros Z h, change (is_clopen Z) at h, apply h.1, },
  have h_nhds : ∀(a:α) (U : set α), a ∈ U → is_open U → ∃Z ∈ C, a ∈ Z ∧ Z ⊆ U,
  { rintros a U memU h_open,
    obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset h_open memU,
    obtain ⟨t, h, ht, xt⟩ := mem_interior.1 xs,
    set u : set s := (coe : s → α)⁻¹' (interior s) with hu,
    have u_open_in_s : is_open u,
    { apply is_open.preimage (continuous_subtype_coe) is_open_interior, },
    obtain ⟨V, clopen_in_s, Vx, V_sub⟩ := @compact_space.compact_exists_clopen_in_open s _
      (compact_iff_compact_space.1 comp) (subtype.t2_space) (subtype.totally_disconnected_space)
        ⟨a, h xt⟩ u u_open_in_s xs,
    have V_clopen : (set.image (coe : s → α) V) ∈ C,
    { show is_clopen (set.image (coe : s → α) V), split,
      { set v : set u := (coe : u → s)⁻¹' V with hv,
        have : (coe : u → α) = (coe : s → α) ∘ (coe : u → s), { exact rfl, },
        have pre_f : embedding (coe : u → α),
        { rw this, refine embedding.comp embedding_subtype_coe embedding_subtype_coe, },
        have f' : open_embedding (coe : u → α),
        { constructor, apply pre_f,
          { have : set.range (coe : u → α) = interior s,
            { rw [this, set.range_comp],
              have g : set.range (coe : u → s) = u,
              { ext, split,
                { rw set.mem_range, rintros ⟨y, hy⟩, rw ←hy, apply y.property, },
                rintros hx, rw set.mem_range, use ⟨x, hx⟩, simp, },
              rw [g, subtype.image_preimage_coe],
              apply set.inter_eq_self_of_subset_left interior_subset, },
            rw this, apply is_open_interior, }, },
        have f2 : is_open v,
        { rw hv, apply is_open.preimage (continuous_subtype_coe) clopen_in_s.1, },
        have f3 : (set.image (coe : s → α) V) = (set.image (coe : u → α) v),
        { rw [this, hv], symmetry',
          rw set.image_comp, congr, rw [subtype.image_preimage_coe],
          apply set.inter_eq_self_of_subset_left V_sub, },
        rw f3, apply (open_embedding.is_open_map f') v f2, },
      { apply (closed_embedding.closed_iff_image_closed
          (is_closed.closed_embedding_subtype_coe (is_compact.is_closed comp))).1
            (clopen_in_s).2, }, },
    refine ⟨_, V_clopen, _, _⟩,
    { simp [Vx, h xt], },
    { transitivity s,
      { simp, },
      assumption, }, },
  have f := topological_space.is_topological_basis_of_open_of_nhds h_open h_nhds,
  use C, simp [f],
end

/-- A locally compact Hausdorff space is totally disconnected
  if and only if it is totally separated. -/
theorem loc_compact_t2_tot_disc_iff_tot_sep [locally_compact_space H] [t2_space H] :
  totally_disconnected_space H ↔ totally_separated_space H :=
begin
  split,
  { rintros h,
    apply t2_space.tot_sep_of_zero_dim (@loc_compact_Haus_tot_disc_of_zero_dim _ _ _ _ h), },
  apply totally_separated_space.totally_disconnected_space,
end

end locally_compact_space
