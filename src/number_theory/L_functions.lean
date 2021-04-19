import measure_theory.integration
import algebra.group.hom
import ring_theory.int.basic
import data.padics.padic_integers
import set_theory.zfc
import topology.category.Profinite
import topology.locally_constant.algebra
import topology.algebra.continuous_functions
import topology.metric_space.basic
import topology.continuous_on
import topology.opens
import data.setoid.partition

variables {A : Type*} [integral_domain A] [algebra ℚ A]

def dirichlet_char_space (f : ℤ) : monoid { χ : mul_hom ℤ ℂ // ∀ a : ℤ, gcd a f ≠ 1 ↔ χ a = 0 } :=
{
  mul := begin
        rintros a b, sorry,
        end,
  one := begin sorry end,
  one_mul := begin sorry end,
  mul_one := begin sorry end,
  mul_assoc := begin sorry end,
}

instance dir_char (f : ℤ) : group { χ : mul_hom ℤ ℂ // ∀ a : ℤ, gcd a f ≠ 1 ↔ χ a = 0 } := sorry

variables (p : ℕ) [fact p.prime]

instance topo : topological_space (units ℤ_[p]) := sorry

instance compact : compact_space (units ℤ_[p]) := sorry

instance t2 : t2_space (units ℤ_[p]) := sorry

instance td : totally_disconnected_space (units ℤ_[p]) := sorry

--instance cat : (units ℤ_[p]) ∈ category_theory.Cat.objects Profinite :=

instance topo' : topological_space (units A) := sorry

/-- A-valued points of weight space -/ --shouldn't this be a category theory statement?
def weight_space : group ({ χ : mul_hom (units ℤ_[p]) (units A) // continuous χ }) := sorry

def clopen_sets (H : Type*) [topological_space H] := {s : set H // is_clopen s}

instance bool' {H : Type*} [topological_space H] : boolean_algebra (clopen_sets H) := sorry

--instance union : semilattice_inf_bot (clopen_sets X) := sorry

/-instance has_union' : has_union (clopen_sets X) :=
begin
constructor,
sorry
end-/

open_locale big_operators

--variables {R : Type*} [ring R] [topological_space R]
--variables {R : Type*} [ring R] [topological_space R] [topological_ring R]
variables (X : Profinite)

structure  distribution {R : Type*} [add_monoid R] :=
(phi : clopen_sets X → R)
(count_add ⦃f : ℕ → clopen_sets X⦄ :
  (∀ i j, pairwise (disjoint on f) →
  phi((f i) ∪ (f j)) = phi (f i) + phi (f j)))

instance semi {R : Type*} [semiring R] : semimodule R (locally_constant X R) := sorry

--variables {R : Type*} [ring R] {Γ₀   : Type*}  [linear_ordered_comm_group_with_zero Γ₀] (v : valuation R Γ₀)

noncomputable instance dis' {R : Type*} [normed_group R] : has_norm C(X,R) :=
begin
  constructor, exact λ f, (⨆ x : X, ∥f x∥),
end

/-- Very interesting, equating 2 zeros of C(X,R) coming from different sources. -/
lemma zero' {R : Type*} [normed_group R] : (0 : C(X,R)) = (add_monoid.to_has_zero C(X,R)).zero :=
begin
  exact rfl,
end

example (S : Type*) : set.nonempty (set.univ : set S) → nonempty S := begin refine set.nonempty_iff_univ_nonempty.mpr, end

lemma bdd_above_compact_range_norm {R : Type*} [normed_group R] (f : C(X, R)) : bdd_above (set.range (λ (x : X), ∥f x∥)) :=
begin
{  set g := λ (x : X), ∥(f x)∥ with hg,
  have cont : continuous g, { rw hg, refine continuous.norm _, show continuous f, apply f.2, },
  set bdd_cont := bounded_continuous_function.mk_of_compact g cont with hb,
  have bdd := @bounded_continuous_function.bounded_range _ _ _ _ bdd_cont,
  rw real.bounded_iff_bdd_below_bdd_above at bdd,
  suffices : bdd_above (set.range bdd_cont), convert this, exact bdd.2, },
end

lemma met {R : Type*} [normed_group R] : normed_group.core C(X,R) :=
{
  norm_eq_zero_iff := begin
    rintros f, split,
    { rintros h, rw le_antisymm_iff at h, cases h with h1 h2,
      suffices : ∀ x : X, ∥f x∥ ≤ 0,
      {  ext, specialize this x, rw [norm_le_zero_iff] at this, simp [this], refl, },
      rintros x, refine (cSup_le_iff  _ _).1 _ (∥f x∥) _,
      exact set.range (λ x, ∥f x∥), apply bdd_above_compact_range_norm,
      { by_cases h' : nonempty X, { rw set.range_nonempty_iff_nonempty, assumption, }, { exfalso, apply h', apply nonempty.intro, exact x, }, },
      { change Sup (set.range (λ x, ∥f x∥)) ≤ 0 at h1, assumption,}, simp, },
    { rintros h, rw h, conv_lhs { congr, funext, rw zero',},
      have : ∀ x : X, ∥(0 : C(X, R)) x∥ = 0, { rintros x, rw norm_eq_zero, refl, },
      unfold has_norm.norm, conv_lhs { congr, funext, rw this x, },
      refine @csupr_const ℝ X _ h' _, },
  end,
  triangle := begin
              rintros x y, refine csupr_le _, rintros z,
              transitivity (∥x z∥ + ∥y z∥), {  refine norm_add_le (x z) (y z), },
              { apply add_le_add, { apply le_cSup, { apply bdd_above_compact_range_norm, }, simp, },
                { apply le_cSup, { apply bdd_above_compact_range_norm, }, simp, }, },
              end,
  norm_neg := begin
                rintros f, unfold has_norm.norm, congr, ext, refine norm_neg (f x),
              end,
}

noncomputable instance blah {R : Type*} [normed_group R] : normed_group C(X,R) :=
  normed_group.of_core _ (met X)

--example {A : Type*} [normed_group A] : topological_space A := begin refine uniform_space.to_topological_space, end

noncomputable instance uniform {R : Type*} [normed_group R] : uniform_space C(X, R) :=
  metric_space.to_uniform_space'

--todo
instance completeness {R : Type*} [normed_group R] : complete_space C(X, R) := sorry

--topo ring assumption not really needed
def inclusion {R : Type*} [topological_space R] : locally_constant X R → C(X,R) :=
  λ x, ⟨x, locally_constant.continuous x⟩

lemma sub [topological_space R] [topological_ring R] : function.injective (@inclusion X R _ _ _) := sorry

instance topo_space {R : Type*} [topological_space R] :  topological_space (locally_constant ↥X R) := sorry

lemma totally_disconnected_space.is_disconnected {A : Type*} [topological_space A]
  [totally_disconnected_space A] : ∃ (U V : set A) (hU : is_open U) (hV : is_open V)
    (hnU : U.nonempty) (hnV : V.nonempty) (hdis : disjoint U V), U ∪ V = ⊤:= sorry

open classical
local attribute [instance] prop_decidable

noncomputable def char_fn {R : Type*} [topological_space R] (U : clopen_sets X) : locally_constant X R :=
{
  to_fun := λ x, if (x ∈ U.val) then 1 else 0,
  is_locally_constant := sorry
}

lemma exists_local {R : Type*} [topological_space R] [ring R] [topological_ring R] (a b : X) (h : a ≠ b) : ∃ (f : locally_constant X R), f a = 1 ∧ f b = 0 := sorry

lemma exists_local' {R : Type*} [has_norm R] [topological_space R] [ring R] [topological_ring R] (g : C(X,R)) (U : set X) [is_open U] :
   ∀ (x : X) (h : x ∈ U) (ε : ℝ) [hε : ε > 0], ∃ (f : locally_constant X R) (V : set X)
    (hV : is_open V) (hVx : x ∈ V), ∀ (y : X) (hy : y ∈ V), ∥(g - (inclusion X f)) y∥ < ε := sorry

--variable [topological_space R]

lemma Inter_nonempty_of {α : Type*} {ι : Type*} {s : ι → set α} :
  (⋂ j, s j).nonempty → ∀ (i : ι), (s i).nonempty :=
begin
  rintros h i,
  refine set.nonempty.mono _ h,
  exact set.Inter_subset (λ (i : ι), s i) i,
end

/-- A compact Hausdorff space is totally disconnected if and only if it is totally separated, this
  is also true for locally compact spaces. -/
lemma compact_t2_tot_disc_iff_tot_sep {H : Type*} [topological_space H]
  [compact_space H] [t2_space H] :
  totally_disconnected_space H ↔ totally_separated_space H :=
begin
  split,
  { intro h, constructor, rw is_totally_separated,
    rintros x hx y hy hxy,
    have f := @connected_component_eq_Inter_clopen H _ _ _ x,
    by_contradiction g, simp at g,
    suffices g' : y ∈ connected_component x,
    { rw totally_disconnected_space_iff_connected_component_singleton.1 h x at g',
      rw set.mem_singleton_iff at g', apply hxy g'.symm, },
    rw f, rw set.mem_Inter, by_contradiction, simp at h,
    rcases h with ⟨Z, hZ, hZx, hZy⟩,
    have g' := g Z hZ.1 Zᶜ (is_clopen_compl hZ).1 hZx hZy, simp at g', assumption, },
  apply totally_separated_space.totally_disconnected_space,
end

lemma tot_sep_exists_clopen {H : Type*} [topological_space H] [totally_separated_space H]
  (x y : H) (hxy : x ≠ y) : ∃ (U : set H) (hU : is_clopen U), x ∈ U ∧ y ∈ Uᶜ :=
begin
  obtain ⟨U, V, hU, hV, Ux, Vy, f, disj⟩ :=
    totally_separated_space.is_totally_separated_univ H x (set.mem_univ x) y (set.mem_univ y) hxy,
  have clopen_U := is_clopen_inter_of_disjoint_cover_clopen (is_clopen_univ) f hU hV disj,
  rw set.univ_inter _ at clopen_U,
  have g : V = Uᶜ,
  { rw set.univ_subset_iff at f, rw [set.compl_eq_univ_diff _, <-f, set.union_diff_left], symmetry',
     rw set.diff_eq_self, simp_rw disj,},
  rw g at Vy, refine ⟨U, clopen_U, Ux, Vy⟩,
end

lemma stuff {α : Type*} {x : α} [U : set α] (H : x ∈ U) : ∀ y ∈ Uᶜ, x ≠ y :=
begin
  rintros y Uy,
  by_contradiction,
  simp at h, rw h at H,
  have f := set.mem_inter H Uy, rw set.inter_compl_self _ at f, simp at f, assumption,
end

lemma compact_exists_clopen_in_open {H : Type*} [topological_space H] [compact_space H] [t2_space H]
  [totally_disconnected_space H] {x : H} {U : set H} [is_open U] (memU : x ∈ U) : ∃ (V : set H)
  (hV : is_clopen V), x ∈ V ∧ V ⊆ U :=
begin
  by_cases Uᶜ = ∅,
  { rw set.compl_empty_iff at h, rw h,
    refine ⟨set.univ, is_clopen_univ, set.mem_univ x, set.subset_univ _⟩, },
  { rw compact_t2_tot_disc_iff_tot_sep at *,
    have ex : ∀ (y : H) (hy : y ∈ Uᶜ), ∃ (V : set H), is_clopen V ∧ (y ∈ V ∧ x ∈ Vᶜ),
    { rintros y hy, rw ←compl_compl U at memU,
      obtain ⟨U, hU, Uy, Ux⟩ := @tot_sep_exists_clopen H _ _inst_10 y x (@stuff H y Uᶜ hy x memU),
      refine ⟨U, hU, Uy, Ux⟩, },
      set h := λ (y : H) (hy : y ∈ Uᶜ), classical.some (ex y hy) with fh,
    set V := (⨆ (y : H) (hy : y ∈ Uᶜ), h y hy) with hV,
    have sub : Uᶜ ⊆ V,
    { intros y hy, rw hV, rw set.mem_Union, use y, rw set.mem_Union, use hy,
      obtain ⟨g1, g2, g3⟩ := some_spec (ex y hy),
      refine g2, },
    rw hV at sub,
    rw ←is_closed_compl_iff at _inst_11,
    have comp : is_compact Uᶜ := by { exact is_closed.compact _inst_11 },
    obtain ⟨t, fin⟩ := is_compact.elim_finite_subcover comp _ _ sub,
    { rw set.compl_subset_comm at fin,
      set W := (⨆ (i : H) (H_1 : i ∈ t), (λ (y : H), ⨆ (hy : y ∈ Uᶜ), h y hy) i)ᶜ with hW,
      rw [set.compl_Union] at hW,
      refine ⟨W, _, _, fin⟩,
      have g : fintype (t : set H), exact finset_coe.fintype t,
      rw hW,
      suffices f : ∀ y : ((t : set H) ∩ Uᶜ), is_clopen (h y.val ((set.mem_inter_iff y.val _ _).1 y.property).2)ᶜ,
      { have g := is_clopen_Inter f,
        simp only [subtype.val_eq_coe] at g,
        have h' : (⋂ (i : H) (i_1 : i ∈ t) (i_1 : i ∈ Uᶜ), (h i i_1)ᶜ) = ⋂ (i : (↑t ∩ Uᶜ)), (h ↑i ((set.mem_inter_iff i.val _ _).1 i.property).2)ᶜ,
        { ext, split,
          { rintros a, rw set.mem_Inter at *, rintros j, specialize a j, rw set.mem_Inter at *,
            have b := a ((set.mem_inter_iff j.val _ _).1 j.property).1, rw set.mem_Inter at *,
            specialize b ((set.mem_inter_iff j.val _ _).1 j.property).2, exact b, },
            { rintros a, rw set.mem_Inter at *, rintros j, rw set.mem_Inter, rintros b,
              rw set.mem_Inter, rintros c, specialize a ⟨j, set.mem_inter b c⟩, exact a, }, },
        conv { congr, congr, funext, rw [set.compl_Union],
               conv { congr, funext, rw [set.compl_Union], }, },
        rw [h'], apply g, },
      { rintros y, obtain ⟨g1, g2, g3⟩ := some_spec (ex y.val ((set.mem_inter_iff y.val _ _).1 y.property).2),
        apply is_clopen_compl, refine g1, },
      { rw hW, rw set.mem_Inter, rintros i, conv { congr, congr, funext, rw [set.compl_Union],
               conv { congr, funext, rw [set.compl_Union], }, }, rw set.mem_Inter, rintros hi, rw set.mem_Inter,
        rintros Ui, obtain ⟨g1, g2, g3⟩ := some_spec (ex i Ui),
        refine g3, }, },
    {  rintros i, apply is_open_Union, rintros hi, obtain ⟨g1, g2, g3⟩ := some_spec (ex i hi),
      refine g1.1, }, },
end

open_locale topological_space filter

lemma loc_compact_Haus_tot_disc_of_zero_dim (H : Type*) [topological_space H]
  [locally_compact_space H] [t2_space H] [totally_disconnected_space H] :
  ∃ (B : set (set H)) (hB : topological_space.is_topological_basis B), ∀ x ∈ B, is_clopen x :=
begin
  set C := {Z : set H | is_clopen Z} with hC,
  have h_open : ∀ Z ∈ C, is_open Z,
  { rintros Z h, change (is_clopen Z) at h, apply h.1, },
  have h_nhds : ∀(a:H) (U : set H), a ∈ U → is_open U → ∃Z ∈ C, a ∈ Z ∧ Z ⊆ U,
  { rintros a U memU h_open,
    obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset h_open memU,
    obtain ⟨t, h, ht, xt⟩ := mem_interior.1 xs,
    set u : set s := (coe : s → H)⁻¹' (interior s) with hu,
    have u_open_in_s : is_open u, { apply is_open.preimage (continuous_subtype_coe) is_open_interior, },
    obtain ⟨V, clopen_in_s, Vx, V_sub⟩ := @compact_exists_clopen_in_open s _
      (compact_iff_compact_space.1 comp) (subtype.t2_space) (subtype.totally_disconnected_space) ⟨a, h xt⟩
        u u_open_in_s xs,
    have V_clopen : (set.image (coe : s → H) V) ∈ C,
    { show is_clopen (set.image (coe : s → H) V), split,
      { set v : set u := (coe : u → s)⁻¹' V with hv,
        have : (coe : u → H) = (coe : s → H) ∘ (coe : u → s), exact rfl,
        have pre_f : embedding (coe : u → H),
        { rw this, refine embedding.comp _ _, exact embedding_subtype_coe, exact embedding_subtype_coe, },
        have f' : open_embedding (coe : u → H),
        { constructor, apply pre_f,
          { have : set.range (coe : u → H) = interior s,
            { rw this, rw set.range_comp,
              have g : set.range (coe : u → s) = u,
              { ext, split,
                { rw set.mem_range, rintros ⟨y, hy⟩, rw ←hy, apply y.property, },
                rintros hx, rw set.mem_range, use ⟨x, hx⟩, simp, },
              simp [g], apply set.inter_eq_self_of_subset_left interior_subset, },
            rw this, apply is_open_interior, }, },
        have f2 : is_open v,
        { rw hv, apply is_open.preimage, exact continuous_subtype_coe, apply clopen_in_s.1, },
        have f3 : (set.image (coe : s → H) V) = (set.image (coe : u → H) v),
        { rw this, rw hv, symmetry', rw set.image_comp, congr, simp, apply set.inter_eq_self_of_subset_left V_sub, },
        rw f3, apply (open_embedding.is_open_map f') v f2, },
      { apply (closed_embedding.closed_iff_image_closed (is_closed.closed_embedding_subtype_coe (is_compact.is_closed comp))).1 (clopen_in_s).2, }, },
    refine ⟨_, V_clopen, _, _⟩,
    { simp [Vx, h xt], },
    { transitivity s,
      { simp, },
      assumption, }, },
  have f := topological_space.is_topological_basis_of_open_of_nhds h_open h_nhds,
  use C, simp [f],
end

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
  obtain ⟨W, hW, xW, Wsub⟩ := topological_space.mem_basis_subset_of_mem_open hB xU hU,
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
  exact topological_space.sUnion_basis_of_is_open h,
/-  convert topological_space.opens.is_basis_iff_cover,
  split,
  { intros hB U hU,
    rcases topological_space.sUnion_basis_of_is_open hB hU with ⟨sUs, F, hU⟩,
    existsi {U : set (set H) | U ∈ B ∧ ↑U ∈ sUs},
    split,
    { intros U hU, exact hU.left },
    { apply ext,
      rw [Sup_s, hU],
      congr' with s; split; intro hs,
      { rcases H hs with ⟨V, hV⟩,
        rw ← hV.right at hs,
        refine ⟨V, ⟨⟨hV.left, hs⟩, hV.right⟩⟩ },
      { rcases hs with ⟨V, ⟨⟨H₁, H₂⟩, H₃⟩⟩,
        subst H₃, exact H₂ } } },
  { intro h,
    rw is_basis_iff_nbhd,
    intros U x hx,
    rcases h U with ⟨Us, hUs, H⟩,
    replace H := congr_arg (coe : _ → set α) H,
    rw Sup_s at H,
    change x ∈ ↑U at hx,
    rw H at hx,
    rcases set.mem_sUnion.mp hx with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩,
    refine ⟨V,hUs H₁,_⟩,
    cases V with V hV,
    dsimp at H₂, subst H₂,
    refine ⟨hsV,_⟩,
    change V ⊆ U, rw H,
    exact set.subset_sUnion_of_mem ⟨⟨V, _⟩, ⟨H₁, rfl⟩⟩ } -/
end

lemma clopen_Union_disjoint {H : Type*} [topological_space H]
  [locally_compact_space H] [t2_space H] [totally_disconnected_space H] (s : finset(set H)) (hs : ∀ x ∈ s, is_clopen x) :
  ∃ (t : finset (set H)), ⋃₀ (s : set(set H)) = ⋃₀ (t : set(set H)) ∧ ∀ (x y : set H) (hx : x ∈ t) (hy : y ∈ t), ∃ z ∈ s, x ⊆ z ∧ x ∩ y = ∅ :=
begin
  sorry
end

lemma clopen_union_disjoint {H : Type*} [topological_space H]
  [locally_compact_space H] [t2_space H] [totally_disconnected_space H] {C : set H} (hC : is_clopen C) :
  ∃ (s : set (set H)), C = Sup s ∧ ∀ (x y : set H) (hx : x ∈ s) (hy : y ∈ s), is_clopen x ∧ is_clopen y ∧ x ∩ y = ∅ :=
begin

  sorry,
end

lemma clopen_union_disjoint' {H : Type*} [topological_space H]
  [locally_compact_space H] [t2_space H] [totally_disconnected_space H] {C : set H} (hC : is_open C) :
  ∃ (s : set (set H)), C = Sup s ∧ ∀ (x y : set H) (hx : x ∈ s) (hy : y ∈ s), is_clopen x ∧ is_clopen y ∧ x ∩ y = ∅ :=
begin
  obtain ⟨B, hB, h⟩ := @loc_compact_Haus_tot_disc_of_zero_dim H _ _ _ _,
--  have D : set (topological_space.opens H) := {Z // is_clopen (Z : set H)},
--  have f : topological_space.opens.is_basis _ hB,
  obtain ⟨V, hV, f⟩ := is_basis_iff_cover'.1 hB C hC,
  set g : V × V → set H := λ ⟨x, y⟩, x.1 \ y.1 with hg,
  use (set.range g),
  split,
  {sorry},
  {sorry},
  --rw topological_space.opens.is_basis_iff_cover.1
end

/- lemma clopen_union_disjoint {H : Type*} [topological_space H] [boolean_algebra A] [t : finset {Z : set H | is_clopen Z}] :
  ∃ (s : finset {Z : set H | is_clopen Z}), (∀ (x y :set  H) (hx : x ∈ s) (hy : y ∈ s), (x : set H) ∩ y = ∅) ∧ ⨆ (Z : A) (Ht : Z ∈ t), Z = ⨆ (Z : A) (Hs : Z ∈ s), Z := -/

--show that locally compact Hausdorff is tot disc iff zero dim
open_locale big_operators

example (a b c : ℤ) : a ≤ b → b < c → a < c :=
begin
  exact lt_of_le_of_lt,
end

instance scalar {A : Type*} [group A] : has_scalar A (locally_constant X A) := sorry

instance scalar' {A : Type*} [normed_group A] : has_scalar A (locally_constant X A) := sorry

theorem dense_C {A : Type*} [normed_group A] (H : nonempty X) : -- [topological_space R] [topological_ring R] [has_norm R] :
  @dense (C(X, A)) _ (set.range (inclusion X)) :=
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
--  set T := set.range preh with hT,
  have g' : preh = set.univ,
  { rw preh', rw g, exact set.preimage_univ, },
  rw preh' at g',
  rw set.preimage_sUnion at g',
  rw set.subset.antisymm_iff at g',
  obtain ⟨t, ht⟩ := is_compact.elim_finite_subcover _ _ _ g'.2,
  { simp at ht,
    suffices ht' : ∃ (T' : finset (set X)), (∀ s ∈ T', is_clopen s ∧ (∃ U ∈ t, s ⊆ f ⁻¹' U)) ∧
      setoid.is_partition (T' : set(set X)),
    { rcases ht' with ⟨T', ht1, ht2, ht3⟩,
      set c := λ (s : set X) (H : s ∈ T'), (⟨s, (ht1 s H).1⟩ : clopen_sets X) with hc,
      have ne : ∀ (s : set X) (H : s ∈ T'), nonempty s,
      { sorry, },
      set c' := λ (s : set X) (H : s ∈ T'), classical.choice (ne s H) with h'c,
      have ht4 : ∀ (a : X), ∃ (b : set X) (H : b ∈ T'), a ∈ b,
      { rintros a, apply exists_of_exists_unique, simp only [exists_prop], sorry, },
        --set c2 : X → A := λ (x : X), f (c' (classical.some (exists_of_exists_unique (ht3 x)) )
          --(finset.mem_coe.1 (exists_prop.1 (exists_of_exists_unique (classical.some_spec
            --(exists_of_exists_unique (ht3 x))))).1) ) with hc2,
        set b : locally_constant X A :=
        (∑ s in T', if H : s ∈ T' then ((f (c' s H)) • (char_fn X (c s H))) else 0) with hb,
        refine ⟨(inclusion X b), _, _⟩, { simp, },
        { have : dist f (inclusion X b) ≤ (ε/2),
          { --unfold has_dist.dist, simp,
            refine cSup_le _ _,
            { rw set.range_nonempty_iff_nonempty, assumption, },
            { rintros m hm, rw set.mem_range at hm, cases hm with y hy, rw ←hy, specialize ht3 y, rcases ht3 with ⟨w, wT, hw⟩,
              obtain ⟨w1, w2⟩ := exists_prop.1 (exists_of_exists_unique wT),
              have : (inclusion X b) y = f (c' w w1), sorry,
              convert_to ∥(f y) - ((inclusion X b) y)∥ ≤ ε/2, congr, sorry,
              rw this, obtain ⟨U, hU, wU⟩ := (ht1 w w1).2, have yU := wU w2, simp at yU, have tS : (t : set(set A)) ⊆ S, sorry, have SU := tS hU, rw hS at SU, rw set.mem_range at SU, cases SU with z hz, rw h' at hz, simp at hz, rw hz.symm at yU,
              have tired : f (c' w w1) ∈ U, sorry,
              rw hz.symm at tired, rw mem_ball_iff_norm at tired, rw mem_ball_iff_norm at yU, --have sub : f y - f ↑(c' w w1) = (f y - z) - (f ↑(c' w w1) - z),
              conv_lhs { rw sub_eq_sub_add_sub _ _ z, }, have : ε/2 = ε/4 + ε/4, sorry, rw this, apply norm_add_le_of_le _ (le_of_lt yU), apply le_of_lt, rw ←norm_neg _, simp [tired], }, },
           rw le_iff_lt_or_eq at this, cases this, transitivity (ε/2), assumption, exact half_lt_self hε, { rw this, exact half_lt_self hε, }, }, },
    { set B : set(set X) := { j : set X | (set.image f j) ∈ t ∧ (set.image f j) ∈ S } with hB,
      have opens : ∀ j ∈ B, is_open j, sorry,
      obtain ⟨C, hC, h⟩ := loc_compact_Haus_tot_disc_of_zero_dim X, simp at g',
      have g'' : (set.univ ⊆ set.sUnion B), sorry,
      conv at g'' { congr, skip, rw set.sUnion_eq_Union, congr, funext, apply_congr classical.some_spec (classical.some_spec (topological_space.sUnion_basis_of_is_open hC (opens i.val i.prop))), },
      simp at g'', rw set.Union at g'',
      have try : ∃ (V ⊆ C), ((set.univ : set X) ⊆ set.sUnion V) ∧ ∀ x ∈ V, ∃ U ∈ B, x ⊆ U,
      { refine ⟨ {j : set X | ∃ (U : set X) (hU : U ∈ B), j ∈ classical.some (topological_space.sUnion_basis_of_is_open hC (opens U hU))}, _, _ ⟩, intros j hj, simp at hj, rcases hj with ⟨W, hW, hj⟩,
        obtain ⟨H, H1⟩ := classical.some_spec (topological_space.sUnion_basis_of_is_open hC (opens W hW)), apply H, simp [hj], split,
        { intros x hx, rw set.mem_sUnion, have g3 := g'' hx, simp at g3, rcases g3 with ⟨U, hU, a, ha, xa⟩, refine ⟨a, _, xa⟩, simp, refine ⟨U, hU, ha⟩, },
        { rintros x hx, simp at hx, rcases hx with ⟨U, hU⟩, use U, cases hU with hU xU, simp [hU],
          obtain ⟨H, H1⟩ := classical.some_spec (topological_space.sUnion_basis_of_is_open hC (opens U _)), rw H1, sorry, sorry, }, },
      rcases try with ⟨V, hV, cover, clopen⟩,
      rw set.sUnion_eq_Union at cover,
      obtain ⟨s', h's⟩ := is_compact.elim_finite_subcover (@compact_univ X _ _) _ _ cover,
      set s1 := {i : set X | ∃ (j : V) (H : j ∈ s'), (j : set X) = i } with hs1,
      have fin : set.finite s1, sorry,
      obtain ⟨s, hs, sub⟩ := clopen_Union_disjoint (set.finite.to_finset fin) _,
      use s,
      { split,
        { rintros w hw, split, sorry,
          { use set.image f w, split, sorry, sorry, }, },
          constructor, sorry, sorry, },
      {sorry,}, sorry, }, },
  { exact compact_univ, },
  { rintros i, apply is_open_Union, rintros hi, apply continuous.is_open_preimage _,
    { rw [hS, h'] at hi, simp at hi, cases hi with y hy,
      suffices : is_open (metric.ball y (ε/4)),
      { rw hy at this, assumption, },
      refine @metric.is_open_ball A _ y (ε/4), },
    exact continuous_map.continuous f, },
-- working with clopen sets makes life easy
end

structure distribution' {R : Type*} [semiring R] [topological_space R] :=
(phi : (locally_constant X R) →ₗ[R] R)

def measures := {φ : distribution X // ∀ S : clopen_sets X, ∃ K : Γ₀, v (φ.phi S) ≤ K }

def measures' [topological_space R] := {φ : @distribution' X R _ _ // ∀ f : (locally_constant X R), ∃ K : Γ₀, v (φ.phi f) ≤ K }

noncomputable def integral [topological_space R] [topological_ring R] (φ : measures' X v) : C(X, R) →ₗ[R] R :=
begin
  split,
  swap 3,
  {  apply dense_inducing.extend _ (φ.1).phi,
    sorry,
    sorry,
    sorry, },
  sorry, sorry,
end

lemma cont [topological_space R] [topological_ring R] (φ : measures' X v) : continuous (integral X v φ) := sorry

/-structure dir_sys ( α : Type* ) :=
(h : ℕ → finset α )
(sys : ∀ (i j : ℕ) (hji : j ≤ i), (h i : set α) → (h j : set α))
(hsys : ∀ (i j : ℕ) (hji : j ≤ i), function.surjective (sys i j hji) )
(maps : ∀ i j k (h1 : k ≤ j) (h2 : j ≤ i), sys j k h1 ∘ sys i j h2  = sys i k (trans h1 h2) )

variables {G : Type*} [comm_group G] {α : Type*} [ϕ : dir_sys α]

open_locale big_operators
--set_option trace.class_instances
structure distribution :=
( φ : ↑(ϕ.h) → G )
(sum : ∀ (i j : ℕ) (hi : j ≤ i) (x : ϕ.h j), φ j x = tsum (λ (y : (ϕ.lam i j hi)⁻¹ x), φ i y) ) -/

structure system {X : Type*} [set X] :=
( h : ℕ → finset X )
( projlim : X = Prop ) --inverse limit
