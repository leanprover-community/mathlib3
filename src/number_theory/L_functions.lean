import measure_theory.integration
import algebra.group.hom
import ring_theory.int.basic
import data.padics.padic_integers
import set_theory.zfc
import topology.category.Profinite
import topology.locally_constant.algebra
import topology.algebra.continuous_functions
import topology.metric_space.basic

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

variables (X : Profinite)

def clopen_sets := {s : set X // is_clopen s}

instance bool' : boolean_algebra (clopen_sets X) := sorry

instance union : semilattice_inf_bot (clopen_sets X) := sorry

instance has_union' : has_union (clopen_sets X) :=
begin
constructor,
sorry
end

open_locale big_operators

--variables {R : Type*} [ring R] [topological_space R]
--variables {R : Type*} [ring R] [topological_space R] [topological_ring R]
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

/-- This is false because empty intersection of a set gives itself -/
lemma Inter_nonempty_of' {α  β : Type*} {ι : set β} {s : ι → set α} :
  (⋂ j, s j).nonempty → nonempty ι :=
begin
  sorry
end

/-- A compact Hausdorff space is totally disconnected if and only if it is totally separated, this
  is also true for locally compact spaces. -/
-- TODO : Prove for locally compact spaces
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

lemma closed_of_compact_space {H : Type*} [topological_space H] [compact_space H] {U : set H}
  [h : is_closed U] : is_compact U :=
begin
  exact is_closed.compact h,
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
      set V := (⨆ (i : H) (H_1 : i ∈ t), (λ (y : H), ⨆ (hy : y ∈ Uᶜ), h y hy) i)ᶜ with hV,
      simp only [set.compl_Union] at hV,
      refine ⟨V, _, _, fin⟩,
      have g : fintype (t : set H), exact finset_coe.fintype t,
      { rw hV,
        suffices f : ∀ y : ((t : set H) ∩ Uᶜ), is_clopen (h y.val ((set.mem_inter_iff y.val _ _).1 y.property).2),
        { have g := is_clopen_Inter f,
--          convert_to (is_clopen (⋂ (i : H) (i_1 : i ∈ ((t : set H) ∩ Uᶜ), (some _)ᶜ)) using set.mem_inter_iff,
          conv at g { congr, congr, funext, norm_num, rw [set.set_coe_eq_subtype ((t : set H) ∩ Uᶜ)], },
         --rw [set.set_coe_eq_subtype (↑t ∩ Uᶜ)] at g,
--          change (is_clopen (⋂ (i : H) (i_1 : i ∈ ((t : set H) ∩ Uᶜ)), (λ (y ∈ (↑t ∩ Uᶜ)), h y _) i i_1)) at g,
--          suffices h : ⋂ (i : (t : set H) ∩ Uᶜ), (h i.val ((set.mem_inter_iff i.val _ _).1 i.property).2) = ⋂ (i : H) (i_1 : i ∈ t) (i_1 : i ∈ Uᶜ), h i i_1,
          simp only [subtype.val_eq_coe] at g, },
        { rintros y, obtain ⟨g1, g2, g3⟩ := some_spec (ex y.val ((set.mem_inter_iff y.val _ _).1 y.property).2),
          refine g1, }, },
      { rw hV, rw set.mem_Inter, rintros i, rw set.mem_Inter, rintros hi, rw set.mem_Inter,
        rintros Ui, obtain ⟨g1, g2, g3⟩ := some_spec (ex i Ui),
      refine g3, },
    },
    { rintros i, apply is_open_Union, rintros hi, obtain ⟨g1, g2, g3⟩ := some_spec (ex i hi),
      refine g1.1, },

    have ne : set.nonempty Uᶜ,
    {contrapose h, rw not_not, rw <-set.not_nonempty_iff_eq_empty, assumption, },
    set y := set.nonempty.to_subtype ne with hy, },
end

lemma compact_Haus_tot_disc_iff_zero_dim {H : Type*} [topological_space H]
  [compact_space H] [t2_space H] [totally_disconnected_space H] :
  ∃ (B : set (set H)) (hB : topological_space.is_topological_basis B), ∀ x ∈ B, is_clopen x :=
begin
  rw set.subset_bUnion_of_mem
  sorry
end

lemma loc_compact_Haus_tot_disc_iff_zero_dim {H : Type*} [topological_space H]
  [locally_compact_space H] [t2_space H] [totally_disconnected_space H] :
  ∃ (B : set (set H)), topological_space.is_topological_basis B ∧ ∀ x ∈ B, is_clopen x :=
begin
  sorry
end

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
