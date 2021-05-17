import measure_theory.integration
import algebra.group.hom
import ring_theory.int.basic
import data.padics.padic_integers
import set_theory.zfc
import topology.category.Profinite
import topology.locally_constant.algebra
import topology.metric_space.basic
import topology.continuous_on
import topology.opens
import data.setoid.partition
import topology.continuous_function.bounded

def clopen_sets (H : Type*) [topological_space H] := {s : set H // is_clopen s}

open_locale big_operators

/-variables (X : Profinite)

/-instance semi {R : Type*} [semiring R] : semimodule R (locally_constant X R) :=
begin
  refine ring_hom.to_semimodule _,
  constructor,
  swap 5, intros r, constructor, swap 2, rintros x,
  sorry
end -/

--variables {R : Type*} [ring R] {Γ₀   : Type*}  [linear_ordered_comm_group_with_zero Γ₀] (v : valuation R Γ₀)

/-
/-- Very interesting, equating 2 zeros of C(X,R) coming from different sources. -/
lemma zero' {R : Type*} [normed_group R] : (0 : C(X,R)) = (add_monoid.to_has_zero C(X,R)).zero :=
begin
  exact rfl,
end -/

example (S : Type*) : set.nonempty (set.univ : set S) → nonempty S := begin refine set.nonempty_iff_univ_nonempty.mpr, end

lemma bdd_above_compact_range_norm {R : Type*} [normed_group R] (f : C(X, R)) : bdd_above (set.range (λ (x : X), ∥f x∥)) :=
begin
{  set g := λ (x : X), ∥(f x)∥ with hg,
  have cont : continuous g, { rw hg, refine continuous.norm _, show continuous f, apply f.2, },
  set bdd_cont := bounded_continuous_function.mk_of_compact ⟨g,cont⟩ with hb,
  have bdd := @bounded_continuous_function.bounded_range _ _ _ _ bdd_cont,
  rw real.bounded_iff_bdd_below_bdd_above at bdd,
  suffices : bdd_above (set.range bdd_cont), convert this, exact bdd.2, },
end

noncomputable instance dis' {R : Type*} [normed_group R] : has_norm C(X,R) :=
{ norm := λ f, (⨆ x : X, ∥f x∥) }

lemma met {R : Type*} [normed_group R] [nonempty X] : normed_group.core C(X,R) :=
{
  norm_eq_zero_iff := begin
    rintros f, split,
    { rintros h, rw le_antisymm_iff at h, cases h with h1 h2,
      suffices : ∀ x : X, ∥f x∥ ≤ 0,
      {  ext, specialize this x, rw [norm_le_zero_iff] at this, simp [this], },
      rintros x, refine (cSup_le_iff  _ _).1 _ (∥f x∥) _,
      exact set.range (λ x, ∥f x∥), apply bdd_above_compact_range_norm,
      { rw set.range_nonempty_iff_nonempty, assumption, },
      { change Sup (set.range (λ x, ∥f x∥)) ≤ 0 at h1, assumption,}, exact ⟨x, rfl⟩, },
    { rintros h, rw h,-- conv_lhs { congr, funext, rw zero',},
      have : ∀ x : X, ∥(0 : C(X, R)) x∥ = 0, { rintros x, rw norm_eq_zero, refl, },
      unfold has_norm.norm, conv_lhs { congr, funext, rw this x, },
      { refine csupr_const, }, },
  end,
  triangle := begin
              rintros x y, refine csupr_le (λ z, _),
              transitivity (∥x z∥ + ∥y z∥), {  exact norm_add_le (x z) (y z), },
              { apply add_le_add,
                { apply le_cSup, { apply bdd_above_compact_range_norm, },
                  exact ⟨z, rfl⟩ },
                { apply le_cSup, { apply bdd_above_compact_range_norm, }, exact ⟨z, rfl⟩ },
              },
              end,
  norm_neg := begin
                rintros f, unfold has_norm.norm, congr, ext, refine norm_neg (f x),
              end,
}

noncomputable instance {R : Type*} [normed_group R] [h : nonempty X] : normed_group C(X,R) :=
  normed_group.of_core _ (met X)

--example {R : Type*} [normed_group R] : metric_space R := begin  library_search, end

noncomputable instance uniform {R : Type*} [normed_group R] [h : nonempty X] : uniform_space C(X, R) :=
begin
  have : metric_space C(X,R), { refine normed_group.to_metric_space, },
  apply metric_space.to_uniform_space',
end
--  @metric_space.to_uniform_space' _ (normed_group.to_metric_space)

--todo
--instance completeness {R : Type*} [normed_group R] : complete_space C(X, R) := sorry

--topo ring assumption not really needed
def inclusion (R : Type*) [topological_space R] : locally_constant X R → C(X,R) :=
  λ x, ⟨x, locally_constant.continuous x⟩

noncomputable instance {R : Type*} [normed_group R] [h : nonempty X] : topological_space (locally_constant X R) :=
topological_space.induced (inclusion X R) uniform_space.to_topological_space


--instance lin'' {R : Type*} [topological_space R] [add_monoid R] : add_monoid_hom (locally_constant X R) C(X,R) :=

/-instance lin' {R : Type*} [topological_space R] : has_scalar R (locally_constant X R) :=
begin
  constructor, intros r f, constructor, swap,
  sorry
end

instance linear' {R : Type*} [topological_space R] : mul_action_hom R (locally_constant X R) -/

lemma sub {R : Type*} [topological_space R] : function.injective (inclusion X R) :=
begin
  intros f g h, rw inclusion at h, simp at h, rw h,
end

--instance topo_space {R : Type*} [topological_space R] :  topological_space (locally_constant ↥X R) := sorry

/-lemma totally_disconnected_space.is_disconnected {A : Type*} [topological_space A]
  [totally_disconnected_space A] : ∃ (U V : set A) (hU : is_open U) (hV : is_open V)
    (hnU : U.nonempty) (hnV : V.nonempty) (hdis : disjoint U V), U ∪ V = ⊤:= sorry -/

open classical

--local attribute [instance] classical.prop_decidable

--open_locale classical

noncomputable def char_fn {R : Type*} [topological_space R] [ring R] [topological_ring R] (U : clopen_sets X) : locally_constant X R :=
{
  to_fun := λ x, by classical; exact if (x ∈ U.val) then 1 else 0,
  is_locally_constant :=
    begin
      rw is_locally_constant.iff_exists_open, rintros x,
      by_cases x ∈ U.val,
      { refine ⟨U.val, ((U.prop).1), h, _⟩, rintros y hy, simp [h, hy], },
      { rw ←set.mem_compl_iff at h, refine ⟨(U.val)ᶜ, (is_clopen_compl U.prop).1, h, _⟩,
        rintros y hy, rw set.mem_compl_iff at h, rw set.mem_compl_iff at hy, simp [h, hy], },
    end,
}

--lemma exists_local {R : Type*} [topological_space R] [ring R] [topological_ring R] (a b : X) (h : a ≠ b) : ∃ (f : locally_constant X R), f a = 1 ∧ f b = 0 := sorry

/-lemma exists_local' {R : Type*} [has_norm R] [topological_space R] [ring R] [topological_ring R] (g : C(X,R)) (U : set X) [is_open U] :
   ∀ (x : X) (h : x ∈ U) (ε : ℝ) [hε : ε > 0], ∃ (f : locally_constant X R) (V : set X)
    (hV : is_open V) (hVx : x ∈ V), ∀ (y : X) (hy : y ∈ V), ∥(g - (inclusion X f)) y∥ < ε := sorry -/

--variable [topological_space R]

/- lemma Inter_nonempty_of {α : Type*} {ι : Type*} {s : ι → set α} :
  (⋂ j, s j).nonempty → ∀ (i : ι), (s i).nonempty :=
begin
  rintros h i,
  refine set.nonempty.mono _ h,
  exact set.Inter_subset (λ (i : ι), s i) i,
end -/

example (P : Prop) : ¬ ¬ P → P := not_not.mp -/

open classical

/-- A compact Hausdorff space is totally disconnected if and only if it is totally separated, this
  is also true for locally compact spaces. -/
lemma compact_t2_tot_disc_iff_tot_sep (H : Type*) [topological_space H] [compact_space H] [t2_space H] :
  totally_disconnected_space H ↔ totally_separated_space H :=
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

variables {H : Type*} [topological_space H]

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

lemma ne_mem_of_mem_compl {α : Type*} {x : α} {U : set α} (H : x ∈ U) : ∀ (y : α) (Uy : y ∈ Uᶜ), x ≠ y :=
begin
  rintros y Uy,
  classical,
  by_contradiction,
  push_neg at h, rw h at H,
  have f := set.mem_inter H Uy,
  rw [set.inter_compl_self _, set.mem_empty_eq] at f, assumption,
end

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
    { refine (compact_t2_tot_disc_iff_tot_sep H).1 _, apply_instance, },
    have ex : ∀ (y : H) (hy : y ∈ Uᶜ), ∃ (V : set H), is_clopen V ∧ (y ∈ V ∧ x ∈ Vᶜ),
    { rintros y hy,
      rw ←compl_compl U at memU,
      obtain ⟨U, hU, Uy, Ux⟩ := @exists_clopen_of_tot_sep _ _ f y x (ne_mem_of_mem_compl hy x memU),
      refine ⟨U, hU, Uy, Ux⟩, },
    set h := λ (y : H) (hy : y ∈ Uᶜ), classical.some (ex y hy) with fh,
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
          obtain ⟨g1, g2, g3⟩ := some_spec (ex y.val ((set.mem_inter_iff y.val _ _).1 y.property).2),
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

open_locale topological_space filter

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
    obtain ⟨V, clopen_in_s, Vx, V_sub⟩ := @compact_exists_clopen_in_open s _
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

/--  -/
lemma zero_dim_of_tot_sep {H : Type*} [topological_space H] [t2_space H]
  (h : ∃ (B : set (set H)) (hB : topological_space.is_topological_basis B), ∀ x ∈ B, is_clopen x) :
    totally_separated_space H :=
begin
  constructor,
  rw is_totally_separated,
  apply @t2_space.cases_on H _ _ _ _, { assumption, },
  rintros a x hx y hy ne,
  obtain ⟨U, V, hU, hV, xU, yV, disj⟩ := a x y ne,
  rcases h with ⟨B, hB, h⟩,
  obtain ⟨W, hW, xW, Wsub⟩ := topological_space.is_topological_basis.exists_subset_of_mem_open hB xU hU,
  specialize h W hW,
  have yW : y ∈ Wᶜ,
  { rw set.mem_compl_iff W y, contrapose disj, simp at disj,
    have g := set.mem_inter (Wsub disj) yV,
    apply set.nonempty.ne_empty,
    change' set.nonempty (U ∩ V), apply set.nonempty_of_mem g, },
  refine ⟨W, Wᶜ, h.1, (is_clopen_compl h).1, xW, yW, _, set.inter_compl_self W⟩,
  rw set.union_compl_self,
end

lemma loc_compact_t2_tot_disc_iff_tot_sep {H : Type*} [topological_space H]
  [locally_compact_space H] [t2_space H] :
  totally_disconnected_space H ↔ totally_separated_space H :=
begin
  split,
  { rintros h, apply zero_dim_of_tot_sep (@loc_compact_Haus_tot_disc_of_zero_dim _ _ _ _ h), },
  apply totally_separated_space.totally_disconnected_space,
end

open topological_space.is_topological_basis

lemma is_basis_iff_cover' {H : Type*} [topological_space H] {B : set (set H)}
  (h : topological_space.is_topological_basis B) : ∀ (U : set H) (hU : is_open U),
    ∃ Us ⊆ B, U = ⋃₀ Us :=
begin
  rintros U,
  exact topological_space.is_topological_basis.open_eq_sUnion h,
end

lemma diff_inter_mem_sUnion {α : Type*} (s : set (set α)) (a y : set α) (h : y ∈ s) : (a \ ⋃₀ s) ∩ y = ∅ :=
begin
  rw set.diff_eq, suffices : (⋃₀ s)ᶜ ∩ y = ∅,
  { rw set.inter_assoc, rw this, rw set.inter_empty, },
  apply set.inter_empty_of_inter_sUnion_empty h _, rw set.compl_inter_self,
end
--instance : measurable_set (clopen_sets X) :=

lemma clopen_finite_Union {H : Type*} [topological_space H]
  [locally_compact_space H] [t2_space H] [totally_disconnected_space H] (s : finset(set H)) (hs : ∀ x ∈ s, is_clopen x) :
  is_clopen ⋃₀ (s : set(set H)) :=
begin
  classical,
  apply finset.induction_on' s,
  { simp, },
  { rintros a S h's hS aS US,
    simp, apply is_clopen_union (hs a h's) US, },
end

lemma clopen_Union_disjoint {H : Type*} [topological_space H]
  [locally_compact_space H] [t2_space H] [totally_disconnected_space H] (s : finset(set H)) (hs : ∀ x ∈ s, is_clopen x) :
  ∃ (t : finset (set H)), (∀ (x ∈ (t : set (set H))), is_clopen x) ∧ ⋃₀ (s : set(set H)) = ⋃₀ (t : set(set H)) ∧ (∀ (x : set H) (hx : x ∈ t), ∃ z ∈ s, x ⊆ z) ∧ ∀ (x y : set H) (hx : x ∈ t) (hy : y ∈ t) (h : x ≠ y), x ∩ y = ∅ :=
begin
  classical,
  apply finset.induction_on' s,
  { use ∅, simp, },
  { rintros a S h's hS aS ⟨t, clo, union, sub, disj⟩,
    set b := a \ ⋃₀ S with hb,
    use insert b t, split,
    { rintros x hx, simp at hx, cases hx,
      { rw hx, rw hb, apply is_clopen_diff (hs a h's) _,
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
          apply diff_inter_mem_sUnion, assumption, },
        cases hx,
        { cases hy,
          { rw [hx, hy] at ne, exfalso, simp at ne, assumption, },
          { rw hx, apply this y hy, }, },
        { cases hy,
          { rw set.inter_comm, rw hy, apply this x hx, },
          { apply disj x y hx hy ne, }, }, }, }, },
end
