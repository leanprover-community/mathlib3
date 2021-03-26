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

variables {R : Type*} [ring R] {Γ₀   : Type*}  [linear_ordered_comm_group_with_zero Γ₀] (v : valuation R Γ₀)

instance dis [topological_space R] : has_dist C(X,R) := sorry

noncomputable instance met [topological_space R] : metric_space C(X,R) := sorry
/-{
  dist_self := sorry
  eq_of_dist_eq_zero := sorry
  dist_comm := sorry
  dist_triangle := sorry
  edist := sorry
  edist_dist := sorry
  to_uniform_space := sorry
  uniformity_dist := sorry
}-/

noncomputable instance uniform [topological_space R] : uniform_space C(X, R) := metric_space.to_uniform_space'

instance completeness [topological_space R] : complete_space C(X, R) := sorry

--topo ring assumption not really needed
def inclusion [topological_space R] [topological_ring R] : locally_constant X R → C(X,R) := sorry

lemma sub [topological_space R] [topological_ring R] : function.injective (@inclusion X R _ _ _) := sorry

instance topo_space :  topological_space (locally_constant ↥X R) := sorry

lemma totally_disconnected_space.is_disconnected {A : Type*} [topological_space A]
  [totally_disconnected_space A] : ∃ (U V : set A) (hU : is_open U) (hV : is_open V)
    (hnU : U.nonempty) (hnV : V.nonempty) (hdis : disjoint U V), U ∪ V = ⊤:= sorry

open classical
local attribute [instance] prop_decidable

noncomputable def char_fn (U : clopen_sets X) : locally_constant X R :=
{
  to_fun := λ x, if (x ∈ U.val) then 1 else 0,
  is_locally_constant := sorry
}

lemma exists_local (a b : X) (h : a ≠ b) : ∃ (f : locally_constant X R), f a = 1 ∧ f b = 0 := sorry

lemma exists_local' [has_norm R] [topological_space R] [topological_ring R] (g : C(X,R)) (U : set X) [is_open U] :
   ∀ (x : X) (h : x ∈ U) (ε : ℝ) [hε : ε > 0], ∃ (f : locally_constant X R) (V : set X)
    (hV : is_open V) (hVx : x ∈ V), ∀ (y : X) (hy : y ∈ V), ∥(g - (inclusion X f)) y∥ < ε := sorry

variable [topological_space R]

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

lemma loc_compact_Haus_tot_disc_of_zero_dim {H : Type*} [topological_space H]
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

lemma loc_compact_t2_tot_disc_iff_tot_sep {H : Type*} [topological_space H]
  [locally_compact_space H] [t2_space H] :
  totally_disconnected_space H ↔ totally_separated_space H :=
begin
  split,
  { rintros h, constructor, rw is_totally_separated,
    rintros x hx y hy hxy,
    apply locally_compact_space.rec_on _inst_8,
    rintros f,
    have g := t2_separation hxy,
    rcases g with ⟨Ux, Uy, hUx, hUy, memUx, memUy, disj⟩,
    have f' := f x Ux (mem_nhds_sets hUx memUx),
    rcases f' with ⟨C, hC, hCsub, compC⟩,
    sorry},
  apply totally_separated_space.totally_disconnected_space,
end

open topological_space.is_topological_basis

lemma is_basis_iff_cover' {H : Type*} [topological_space H] {B : set (set H)} :
  topological_space.is_topological_basis B ↔ ∀ (U : set H) (hU : is_open U), ∃ Us ⊆ B, U = Sup Us :=
begin
  sorry,
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

lemma clopen_union_disjoint {H : Type*} [topological_space H]
  [locally_compact_space H] [t2_space H] [totally_disconnected_space H] {C : set H} (hC : is_clopen C) :
  ∃ (s : set (set H)), C = Sup s ∧ ∀ (x y : set H) (hx : x ∈ s) (hy : y ∈ s), is_clopen x ∧ is_clopen y ∧ x ∩ y = ∅ :=
begin
  sorry,
end

lemma clopen_union_disjoint {H : Type*} [topological_space H]
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
lemma dense_C [topological_space R] [topological_ring R] [has_norm R] :
  @dense (C(X,R)) _ (set.range (inclusion X)) :=
begin
  rintros f,
  rw metric.mem_closure_iff,
  rintros ε hε,
--  have g : (⋃x:R, metric.ball x ε) = univ,
  have h := @totally_disconnected_space.is_disconnected X _ _,
  rcases h with ⟨U, V, hU, hV, hnU, hnV, hdis, h⟩,
  set x := classical.some hnU with hx,
  set y := classical.some hnV with hy,
  rcases @exists_local' X R _ _ _ _ f U hU x _ ε hε with ⟨kx, Vx, hVx, mem_hVx, hkx⟩,
-- working with clopen sets makes life easy
--  rcases exists_local X x y _ with ⟨f, hf1, hf2⟩,
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
