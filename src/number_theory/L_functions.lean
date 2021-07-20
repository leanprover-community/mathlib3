import measure_theory.integration
import algebra.group.hom
import ring_theory.int.basic
import number_theory.padics.padic_integers
import set_theory.zfc
import topology.category.Profinite
import topology.locally_constant.algebra
--import topology.algebra.continuous_functions
import topology.metric_space.basic
import topology.continuous_on
import topology.opens
import data.setoid.partition
import topology.continuous_function.bounded
import number_theory.padics.ring_homs
import number_theory.bernoulli_polynomials
import ring_theory.roots_of_unity
import topology.continuous_function.compact

def clopen_sets (H : Type*) [topological_space H] := {s : set H // is_clopen s}

open_locale big_operators

--variables {R : Type*} [ring R] [topological_space R]
--variables {R : Type*} [ring R] [topological_space R] [topological_ring R]
variables (X : Type*) [topological_space X] [compact_space X] [t2_space X] [totally_disconnected_space X]

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

/-noncomputable instance {R : Type*} [normed_group R] : has_norm C(X,R) :=
{ norm := λ f, (⨆ x : X, ∥f x∥) }

lemma norm_def {R : Type*} [normed_group R] (f : C(X,R)) : ∥f∥ = ⨆ x : X, ∥f x∥ := rfl

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
--  @metric_space.to_uniform_space' _ (normed_group.to_metric_space)-/

variables {R : Type*} [normed_group R]

--instance : normed_group C(X, R) := continuous_map.normed_group X R
noncomputable instance : uniform_space C(X, R) := metric_space.to_uniform_space'

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

noncomputable def char_fn {R : Type*} [topological_space R] [ring R] [topological_ring R]
  (U : clopen_sets X) : locally_constant X R :=
{
  to_fun := λ x, by classical; exact if (x ∈ U.val) then 1 else 0,
  is_locally_constant :=
    begin
      rw is_locally_constant.iff_exists_open, rintros x,
      by_cases x ∈ U.val,
      { refine ⟨U.val, ((U.prop).1), h, _⟩, rintros y hy, simp [h, hy], },
      { rw ←set.mem_compl_iff at h, refine ⟨(U.val)ᶜ, (is_clopen.compl U.prop).1, h, _⟩,
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

example (P : Prop) : ¬ ¬ P → P := not_not.mp

/-lemma tot_sep_exists_clopen {H : Type*} [topological_space H] [totally_separated_space H]
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
end-/

open_locale topological_space filter

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
    simp, apply is_clopen.union (hs a h's) US, },
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
          apply diff_inter_mem_sUnion, assumption, },
        cases hx,
        { cases hy,
          { rw [hx, hy] at ne, exfalso, simp at ne, assumption, },
          { rw hx, apply this y hy, }, },
        { cases hy,
          { rw set.inter_comm, rw hy, apply this x hx, },
          { apply disj x y hx hy ne, }, }, }, }, },
end

--show that locally compact Hausdorff is tot disc iff zero dim
open_locale big_operators

example (a b c : ℤ) : a ≤ b → b < c → a < c :=
begin
  exact lt_of_le_of_lt,
end

--instance scalar {A : Type*} [group A] : has_scalar A (locally_constant X A) := sorry

--instance scalar' {A : Type*} [normed_group A] : has_scalar A (locally_constant X A) := sorry

--lemma inc_sum : inclusion X ∑ (x in s), f x = ∑ (x in s), inclusion X f x :=

def h {A : Type*} [normed_ring A] (ε : ℝ) : A → set A := λ (x : A), metric.ball x (ε / 4)

def S {A : Type*} [normed_ring A] (ε : ℝ) : set (set A) := set.range (h ε)

variables {A : Type*} [normed_comm_ring A] (f : C(X, A)) (ε : ℝ) [hε : 0 < ε]

def B : set(set X) := { j : set X | ∃ (U ∈ ((S ε) : set(set A))), j = f ⁻¹' U }

lemma opens : ∀ j ∈ (B X f ε), is_open j :=
begin
  rintros j hj, rw B at hj, rw set.mem_set_of_eq at hj,
  rcases hj with ⟨U, hU, jU⟩, rw jU, apply continuous.is_open_preimage, continuity,
  rw S at hU, rw set.mem_range at hU, cases hU with y hy, rw ←hy, rw h,
  simp, apply metric.is_open_ball,
end

lemma g'' (t : finset(set A))
  (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t) (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) : (set.univ ⊆ set.sUnion (B X f ε)) :=
begin
  rintros x hx, simp, have xt := ht hx, simp at xt,
  rcases xt with ⟨j, hj, jS, fj⟩, use f⁻¹' j, split,
  { use j, split, assumption, refl, }, simp [fj],
end

lemma dense_C_suff (f : C(X, A)) (t : finset(set A))
  (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t) (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) :
  ∃ (T' : finset (set X)), (∀ s ∈ T', is_clopen s ∧ ∃ U ∈ ((S ε) : set(set A)), (set.image f s : set A) ⊆ U) ∧
      ∀ (a : X), ∃! (b : set X) (H : b ∈ T'), a ∈ b :=
begin
  set B : set(set X) := (B X f ε) with hB,
  have f' := @loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _,
  obtain ⟨C, hC, h⟩ := @loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _,
  have g'' := g'' X f ε t ht,
  conv at g'' { congr, skip, rw set.sUnion_eq_Union, congr, funext, apply_congr classical.some_spec (classical.some_spec (topological_space.is_topological_basis.open_eq_sUnion f' (opens X f ε i.val i.prop))), },
  simp at g'', rw set.Union at g'',
  have try : ∃ (V ⊆ {s : set X | is_clopen s}), ((set.univ : set X) ⊆ set.sUnion V) ∧ ∀ x ∈ V, ∃ U ∈ B, x ⊆ U,
  { refine ⟨ {j : set X | ∃ (U : set X) (hU : U ∈ B), j ∈ classical.some (topological_space.is_topological_basis.open_eq_sUnion f' (opens X f ε U hU))}, _, _ ⟩, intros j hj, simp only [set.mem_set_of_eq, exists_const] at hj, rcases hj with ⟨W, hW, hj⟩,
    obtain ⟨H, H1⟩ := classical.some_spec (topological_space.is_topological_basis.open_eq_sUnion f' (opens X f ε W hW)), apply H, apply hj, split,
    { intros x hx, rw set.mem_sUnion, have g3 := g'' hx, simp at g3, rcases g3 with ⟨U, hU, a, ha, xa⟩, refine ⟨a, _, xa⟩, simp, refine ⟨U, hU, ha⟩, },
      { rintros x hx, simp at hx, rcases hx with ⟨U, hU⟩, use U, cases hU with hU xU, simp [hU],
        obtain ⟨H, H1⟩ := classical.some_spec (topological_space.is_topological_basis.open_eq_sUnion f' (opens X f ε U _)), rw H1, intros u hu, simp, refine ⟨x, xU, hu⟩, }, },
  rcases try with ⟨V, hV, cover, clopen⟩,
  rw set.sUnion_eq_Union at cover,
  obtain ⟨s', h's⟩ := is_compact.elim_finite_subcover (@compact_univ X _ _) _ _ cover,
  --set s1 := (λ (i : V) (H : i ∈ s'), (i : set X)) with hs1,
  --have fin : set.finite (set.range s1),
  set s1 : (s' : set V) → set X := λ x, (x.1 : set X) with hs1,
  --set s1 := {i : set X | ∃ (j : V) (H : j ∈ s'), (j : set X) = i } with hs1,
  have fin : (set.range s1).finite,
  { apply set.finite_range _, apply finset.subtype.fintype, },
  obtain ⟨s, clo, hs, sub, disj⟩ := clopen_Union_disjoint (set.finite.to_finset fin) _,
  use s,
  { split,
    { rintros w hw, split, {apply clo w hw, },
      { specialize sub w hw, rcases sub with ⟨z, hz, wz⟩, simp at hz, rcases hz with ⟨z', h1, h2, h3⟩,
        specialize clopen z' h1, rcases clopen with ⟨U, BU, xU⟩, rw hB at BU, rw _root_.B at BU, simp at BU,
        rcases BU with ⟨U', h4, h5⟩, refine ⟨U', h4, _⟩, transitivity (set.image f z),
        { apply set.image_subset _ wz, }, { simp, rw ←h5, rw ←h3, rw hs1, simp [xU], }, }, },
    --constructor,
    { rintros a, have ha := h's (set.mem_univ a), simp at ha, rcases ha with ⟨U, hU, aU⟩,
      have : ∃ j ∈ s, a ∈ j,
      { have ha := h's (set.mem_univ a), simp at hs,
        suffices : a ∈ ⋃₀ (s : set (set X)), simp at this, cases this with j hj, use j, assumption,
        rw ←hs, simp, cases hU with hU s'U, refine ⟨U, hU, s'U, _⟩, rw hs1, simp [aU], },
      rcases this with ⟨j, hj, aj⟩, use j,
      split,
      { simp, refine ⟨hj, aj⟩, },
      { rintros y hy, simp at hy, cases hy with h1 h2, specialize disj j y hj h1,
        by_cases h : j = y, rw h.symm,
        exfalso, specialize disj h, have k := set.mem_inter aj h2, rw disj at k, simp at k, assumption, }, }, },
  { rintros x hx, simp at hx, rcases hx with ⟨U, hU, h1, h2⟩,
    suffices : is_clopen U, rw hs1 at h2, simp at h2, rw ←h2, apply this,
    have UC := hV hU, apply set.mem_def.1 UC, },
  { rintros i, have iC := hV i.2, apply topological_space.is_topological_basis.is_open f' iC, },
end

lemma inc_eval (f : locally_constant X A) (y : X) : inclusion X A f y = f y :=
begin
  rw inclusion, simp,
end

example {α : Type*} (s t : set α) (h : s = t) : s ⊆ t ∧ t ⊆ s := begin refine set.subset.antisymm_iff.mp h, end

lemma sub_iff {α : Type*} (s t : set α) (h : s = t) : ∀ (x : α), x ∈ s ↔ x ∈ t :=
begin
  rw set.subset.antisymm_iff at h, rintros x, split,
  {revert x, show s ⊆ t, apply h.1,},
  {revert x, show t ⊆ s, apply h.2,},
end

example {α β γ : Type*} [add_comm_monoid γ] (s : finset α) (y : β) (f : α → (β → γ)) :
  (∑ x in s, f x) y = ∑ x in s, f x y :=
begin refine finset.sum_apply y s (λ (c : α), f c), end

example : ring C(X, A) :=
begin
  apply_instance,
end

lemma coe_sub (g : C(X, A)) : ((f - g) : X → A) = (f : X → A) - g :=
begin exact rfl, end

--Thank you to the collaborative spirit of Lean
example {J : Type*} [normed_ring J] (f g : C(X, J)) (y : X) : (f - g) y = f y - g y :=
begin
  simp only [continuous_map.coe_sub, pi.sub_apply],
end

lemma sub_apply (f : C(X, A)) (g : locally_constant X A) (y : X) :
  ∥(f - inclusion X A g) y ∥ = ∥f y - (inclusion X A g) y∥ :=
begin
  simp only [continuous_map.coe_sub, pi.sub_apply],
end

example {α : Type*} [topological_space α] (s : set α) (hs : is_clopen s) : is_open s := begin apply hs.1, end

noncomputable def T' (ε : ℝ) (f : C(X, A)) (t : finset(set A))
 (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t) (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) : finset (set X) :=
classical.some (dense_C_suff X ε f t ht)

variables (t : finset(set A)) (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t) (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i)

lemma ht1 : ∀ s ∈ T' X ε f t ht, is_clopen s ∧ ∃ U ∈ ((S ε) : set(set A)), (set.image f s : set A) ⊆ U :=
begin
  rintros s hs,
  apply (classical.some_spec (dense_C_suff X ε f t ht)).1, apply hs,
end

lemma ht3 : ∀ (a : X), ∃! (b : set X) (H : b ∈ T' X ε f t ht), a ∈ b :=
begin
  apply (classical.some_spec (dense_C_suff X ε f t ht)).2,
end

lemma ht5 : ∀ s ∈ (T' X ε f t ht), ∃ U ∈ ((S ε) : set(set A)),  (set.image f s : set A) ⊆ U :=
begin
  rintros s hs,
  suffices : is_clopen s ∧ ∃ U ∈ ((S ε) : set(set A)), (set.image f s : set A) ⊆ U, apply this.2,
  apply (classical.some_spec (dense_C_suff X ε f t ht)).1, apply hs,
end

def c := λ (s : set X) (H : s ∈ (T' X ε f t ht)), (⟨s, (ht1 X f ε t ht s H).1⟩ : clopen_sets X)

noncomputable def c' := λ (s : set X) (H : s ∈ (T' X ε f t ht) ∧ nonempty s), classical.choice (H.2)

lemma mem_nonempty {α : Type*} {s : set α} {x : α} (h : x ∈ s) : nonempty s :=
begin
  refine set.nonempty.to_subtype _, rw set.nonempty, refine ⟨x, h⟩,
end

noncomputable def c2 (f : C(X, A)) (ε : ℝ) (t : finset(set A))
  (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t) (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) : X → A :=
λ x, f (c' X f ε t ht (classical.some (exists_of_exists_unique (ht3 X f ε t ht x)) )
begin
  have := (exists_prop.1 (exists_of_exists_unique (classical.some_spec (exists_of_exists_unique (ht3 X f ε t ht x))))),
  split,
  refine finset.mem_coe.1 (this).1,
  apply set.nonempty.to_subtype, rw set.nonempty, use x,
  apply this.2,
end).

/-λ (x : X), f (c' X f ε t ht (classical.some (exists_of_exists_unique (ht3 X f ε t ht x)) )
  (finset.mem_coe.1 (exists_prop.1 (exists_of_exists_unique (classical.some_spec (exists_of_exists_unique (ht3 X f ε t ht x))))).1) ) -/

lemma loc_const : is_locally_constant (c2 X f ε t ht) :=
begin
  have c2 := c2 X f ε t ht, -- this line must be useless because c2 is data and have forgets defns
  have ht1 := ht1 X f ε t ht,
  have ht3 := ht3 X f ε t ht,
  have ht4 : ∀ (a : X), ∃ (b : set X) (H : b ∈ (T' X ε f t ht)), a ∈ b,
   { rintros a, apply exists_of_exists_unique, simpa using ht3 a },
--  show is_locally_constant c2,
  rw is_locally_constant.iff_exists_open, rintros x, specialize ht4 x,
      rcases ht4 with ⟨U, hU, xU⟩, use U, split, {specialize ht1 U hU, apply (ht1.1).1, },
      use xU, rintros x' x'U, rw _root_.c2, simp, apply congr_arg,
      have : classical.some (exists_of_exists_unique (ht3 x)) = classical.some (exists_of_exists_unique (ht3 x')),
      { congr, ext y, simp, rintros hy, split,
        { rintros xy, specialize ht3 x, simp at ht3,
          cases ht3 with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU xU,
          have hby := hby y hy xy, rw hby, rw ←hbU, apply x'U, },
          { rintros xy, specialize ht3 x', simp at ht3,
            cases ht3 with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU x'U,
            have hby := hby y hy xy, rw hby, rw ←hbU, apply xU, }, },
      congr',
      repeat { ext y, simp, rintros hy, split,
      { rintros xy, specialize ht3 x', simp at ht3,
        cases ht3 with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU x'U,
        have hby := hby y hy xy, rw hby, rw ←hbU, apply xU, },
        { rintros xy, specialize ht3 x, simp at ht3,
          cases ht3 with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU xU,
          have hby := hby y hy xy, rw hby, rw ←hbU, apply x'U, }, },
      simp, ext y, revert y,
      apply sub_iff, symmetry,
      { congr, ext y, simp, rintros hy, split,
        { rintros xy, specialize ht3 x, simp at ht3,
          cases ht3 with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU xU,
          have hby := hby y hy xy, rw hby, rw ←hbU, apply x'U, },
        { rintros xy, specialize ht3 x', simp at ht3,
          cases ht3 with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU x'U,
          have hby := hby y hy xy, rw hby, rw ←hbU, apply xU, }, },
end

theorem tp_dense (H : nonempty X) (hε : 0 < ε) (f : C(X, A)) (t : finset(set A))
 (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t) (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) :
  ∃ (b : C(X, A)) (H_1 : b ∈ set.range (inclusion X A)), dist f b < ε :=
begin
  have ht1 := ht1 X f ε t ht, --have ht5 := ht1.2,
  have ht3 := ht3 X f ε t ht,
  have ht4 : ∀ (a : X), ∃ (b : set X) (H : b ∈ (T' X ε f t ht)), a ∈ b,
   { rintros a, apply exists_of_exists_unique, specialize ht3 a, convert ht3, simp, },
   have loc_const := loc_const X f ε t ht,
   refine ⟨inclusion X A ⟨(c2 X f ε t ht), loc_const⟩, _, _⟩, { simp, },
/-     set b : locally_constant X A :=
      (∑ s in T', if H : s ∈ T' then ((f (c' s H)) • (char_fn X (c s H))) else 0) with hb, -/
    { have : dist f (inclusion X A ⟨(c2 X f ε t ht), loc_const⟩) ≤ (ε/2),
      { rw [dist_eq_norm, continuous_map.norm_eq_supr_norm],
        refine cSup_le _ _,
        { rw set.range_nonempty_iff_nonempty, assumption, },
        { rintros m hm, rw set.mem_range at hm, cases hm with y hy, rw ←hy, have ht3 := ht3 y, rcases ht3 with ⟨w, wT, hw⟩,
          obtain ⟨w1, w2⟩ := exists_prop.1 (exists_of_exists_unique wT),
          have : (inclusion X A ⟨(c2 X f ε t ht), loc_const⟩) y = f (c' X f ε t ht w ⟨w1, mem_nonempty w2⟩),
          { rw inc_eval, simp, rw c2, simp, apply congr_arg,
            congr' 2, swap, congr, swap 3, congr,
            repeat { apply hw, refine classical.some_spec (exists_of_exists_unique (ht3 y)), }, },
          convert_to ∥(f y) - ((inclusion X A ⟨(c2 X f ε t ht), loc_const⟩) y)∥ ≤ ε/2, apply sub_apply,
          rw this, --obtain ⟨U, hU, wU⟩ := (ht1 w w1).2, --have yU := wU w2, simp at yU,
          have ht5 := (ht1 w w1).2, rcases ht5 with ⟨U, hU, wU⟩, --rw S at ht5, rw set.mem_range at ht5, cases ht5 with z hz,
          rw S at hU, rw set.mem_range at hU, cases hU with z hz, --rw h at hz, simp only [continuous_map.to_fun_eq_coe] at hz,
          have tired' : f (c' X f ε t ht w ⟨w1, mem_nonempty w2⟩) ∈ set.image f w, { simp, refine ⟨(c' X f ε t ht w ⟨w1, mem_nonempty w2⟩), _, _⟩, { simp, }, refl, },
          have tired := wU tired',
          have tS' : f y ∈ set.image f w, { simp, refine ⟨y, w2, _⟩, refl, },
          have tS := wU tS',
          rw h at hz, rw hz.symm at tired, rw mem_ball_iff_norm at tired, rw hz.symm at tS, rw mem_ball_iff_norm at tS, --have sub : f y - f ↑(c' w w1) = (f y - z) - (f ↑(c' w w1) - z),
          conv_lhs { rw sub_eq_sub_add_sub _ _ z, },
          have : ε/2 = ε/4 + ε/4, { rw div_add_div_same, linarith, }, rw this, apply norm_add_le_of_le _ (le_of_lt tS),
          apply le_of_lt, rw ←norm_neg _, simp [tired], }, },
    rw le_iff_lt_or_eq at this, cases this, transitivity (ε/2), assumption, exact half_lt_self hε,
    { rw this, exact half_lt_self hε, }, },
end

theorem dense_C (H : nonempty X) : @dense (C(X, A)) _ (set.range (inclusion X A)) :=
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
  { simp at ht, apply tp_dense X ε H hε f t ht, },
  { exact compact_univ, },
  { rintros i, apply is_open_Union, rintros hi, apply continuous.is_open_preimage _,
    { rw [hS, h'] at hi, simp at hi, cases hi with y hy,
      suffices : is_open (metric.ball y (ε/4)),
      { rw hy at this, assumption, },
      refine @metric.is_open_ball A _ y (ε/4), },
    exact continuous_map.continuous f, },
-- working with clopen sets makes life easy
end
--end of density section

--instance bool' {H : Type*} [topological_space H] : boolean_algebra (clopen_sets H) :=
/-begin
  rw boolean_algebra,
  constructor,
end-/

lemma clopen_coe (a b : clopen_sets X) : a.val = b.val → a = b :=
begin
  rintros h,
  have : ∀ (a : clopen_sets X), a = ⟨a.val, a.prop⟩,
    { simp only [implies_true_iff, eq_self_iff_true, subtype.coe_eta, subtype.val_eq_coe], },
  rw this a, rw this b, simp [h],
end

instance union : semilattice_inf_bot (clopen_sets X) :=
begin
  constructor,
  swap 5, use ⟨∅, is_clopen_empty⟩,
  swap 5, rintros a b, refine (a.val ⊆ b.val),
  swap 8, rintros a b, refine ⟨a.val ∩ b.val, is_clopen.inter a.prop b.prop⟩,
  { rintros a, apply set.empty_subset, },
  { rintros a b, apply set.inter_subset_left, },
  { rintros a b, apply set.inter_subset_right, },
  { rintros a b c ab ac, apply set.subset_inter_iff.2 ⟨ab, ac⟩, },
  { rintros a, apply set.subset.refl, },
  { rintros a b c ab ac, apply set.subset.trans ab ac, },
  { rintros a b ab ba, apply clopen_coe, apply set.subset.antisymm ab ba, },
end

instance : lattice (clopen_sets X) :=
begin
  refine subtype.lattice _ _,
  { rintros x y, apply is_clopen.union, },
  { rintros x y, apply is_clopen.inter, },
end

--instance : boolean_algebra (clopen_sets X) := sorry

instance has_union' : has_union (clopen_sets X) :=
begin
constructor,
rintros U V, refine ⟨U.val ∪ V.val, _⟩, apply is_clopen.union U.prop V.prop,
end

variables {Γ₀   : Type*}  [linear_ordered_comm_group_with_zero Γ₀] (v : valuation A nnreal) --what to do?

structure  distribution {R : Type*} [add_monoid R] :=
(phi : clopen_sets X → R)
(count_add ⦃f : ℕ → clopen_sets X⦄ :
  (∀ (S T : clopen_sets X), S ⊓ T = ⊥ →
  phi(S ∪ T) = phi S + phi T)) --define has_sup lattice structure via gi

/-structure  distribution {R : Type*} [add_monoid R] :=
(phi : clopen_sets X → R)
(count_add ⦃f : ℕ → clopen_sets X⦄ :
  (∀ i j, pairwise (disjoint on f) →
  phi((f i) ∪ (f j)) = phi (f i) + phi (f j))) -/

instance : has_scalar A (locally_constant X A) :=
{ smul := λ a f,
  { to_fun := λ x, a*f(x),
    is_locally_constant := begin
      refine is_locally_constant.comp _ (has_mul.mul a),
      apply locally_constant.is_locally_constant f,
    end } }

instance : mul_action A (locally_constant X A) :=
{ smul := (•),
  one_smul := one_mul,
  mul_smul := λ a b f, begin
    repeat {rw locally_constant.has_scalar,},
    refine congr_fun _ f, simp, ext, simp, rw mul_assoc,
  end }

instance : distrib_mul_action A (locally_constant X A) :=
{
  smul_add := λ r f g, begin
    repeat { rw locally_constant.has_scalar, }, ext, exact mul_add r (f x) (g x),
  end,
  smul_zero := λ r, begin ext, exact mul_zero r, end,
  ..locally_constant.mul_action X
   }

instance semi : module A (locally_constant X A) :=
{
  add_smul := λ r s f, by {ext, exact add_mul r s (f x)},
  zero_smul := zero_mul,
  ..locally_constant.distrib_mul_action X }

variable (A)

noncomputable def inclusion' [h : nonempty X] : continuous_linear_map A (locally_constant X A) C(X, A) :=
{ to_fun := inclusion X A,
  map_add' := λ x y, begin ext, refl end,
  map_smul' := λ m x, begin ext y, rw inclusion, simp,
--    simp only [continuous_map.coe_mk, continuous_map.smul_coe, smul_eq_mul, pi.smul_apply],
      refl, end }

  --map_zero' := begin ext, refl, end,
  --map_one' := begin ext, refl, end,
  --map_mul' := λ x y, begin ext, refl, end,

variable {A}

structure distribution' [nonempty X] :=
(phi : linear_map A (locally_constant X A) A)

def measures := {φ : distribution X // ∀ S : clopen_sets X, ∃ K : ℝ, (v (φ.phi S) : ℝ) ≤ K }

/-def measures' (h : nonempty X) :=
  {φ : distribution' X h //
    ∀ f : (locally_constant X A), ∃ K : ℝ, (v (φ.phi f) : ℝ) ≤ K * ∥inclusion X A f∥ } -/

variable (A)

def measures' [nonempty X] :=
  {φ : distribution' X //
    ∃ K : ℝ, ∀ f : (locally_constant X A), ∥φ.phi f∥ ≤ K * ∥inclusion X A f∥ }

def measures'' [nonempty X] :=
  {φ : distribution' X //
    ∃ K : ℝ, 0 < K ∧ ∀ f : (locally_constant X A), ∥φ.phi f∥ ≤ K * ∥inclusion X A f∥ }

noncomputable theory
instance : metric_space (locally_constant X A) :=
begin
  refine metric_space.induced (inclusion X A) (sub X) _, apply_instance,
end

/-instance pms [nonempty X] : pseudo_metric_space (locally_constant X A) := --because nonempty is a class, hence put it in []
begin
  refine pseudo_metric_space.induced (inclusion X A) _, apply_instance,
end-/

/-instance [nonempty X] : pseudo_metric_space (locally_constant X A) :=
begin
  refine pseudo_metric_space.induced (inclusion X A) _, apply_instance,
end-/

instance : has_norm (locally_constant X A) :=
begin
  refine {norm := _},
  rintros f, exact ∥inclusion X A f∥,
end

/-instance (h : nonempty X) [decidable (@locally_constant.pseudo_metric_space X A _ h)] : ∀ (x y : locally_constant X A),
  (@locally_constant.pseudo_metric_space X A _ h).dist x y =
    (@locally_constant.has_norm X A _ h).norm (x - y) :=-/

instance [nonempty X] : normed_group (locally_constant X A) :=
{
  dist_eq := begin
    intros x y,
    change dist (inclusion' X A x) (inclusion' X A y) = ∥inclusion' X A (x - y)∥,
    rw dist_eq_norm,
    rw (inclusion' X A).map_sub,
  end,
  ..locally_constant.metric_space X A, ..locally_constant.has_norm X A,
}
/-begin
  refine ⟨_, locally_constant.has_norm X h, _, locally_constant.pseudo_metric_space X h⟩,
sorry
end-/
--{ ..locally_constant.pseudo_metric_space X h, ..locally_constant.has_norm X h,   },

example {α : Type*} [has_lt α] [has_le α] (a b c : ℤ) (h1 : a ≤ b) (h2 : b < c) : a < c :=
begin
  exact lt_of_le_of_lt h1 h2,
end

lemma integral_cont [nonempty X] (φ : measures'' X A) : continuous (φ.1).phi :=
begin
  /-suffices : ∀ (b : locally_constant X A) (ε : ℝ), ε > 0 → (∃ (δ : ℝ) (H : δ > 0),
      ∀ (a : locally_constant X A), dist a b < δ → dist ((φ.val.phi) a) ((φ.val.phi) b) < ε),-/
  rw metric.continuous_iff, rintros b ε hε,
  obtain ⟨K, hKpos, hK⟩ := φ.prop,
  refine ⟨ε/K, div_pos hε hKpos, _⟩,
  rintros a dab, rw dist_eq_norm,
  rw ←linear_map.map_sub,
  specialize hK (a - b), apply lt_of_le_of_lt hK _, rw mul_comm, rw ←lt_div_iff hKpos,
  convert dab,
  change ∥inclusion X A (a - b)∥ = dist (inclusion' X A a) (inclusion' X A b),
  rw dist_eq_norm,
--  change inclusion' X A _ = inclusion' X A _ - inclusion' X A _,
  rw ←continuous_linear_map.map_sub, refl,
end

lemma di (h : nonempty X) : dense_inducing (inclusion X A) :=
begin
  constructor,
  { constructor, refl, },
  { apply dense_C, assumption, },
end

lemma uni_ind [h : nonempty X] : uniform_inducing (inclusion X A) :=
begin
  exact {comap_uniformity := refl
                       (filter.comap
                          (λ (x : locally_constant X A × locally_constant X A),
                             (inclusion X A x.fst, inclusion X A x.snd))
                          (uniformity C(X, A)))},
end

lemma uni_cont [h : nonempty X] (φ : measures'' X A) : uniform_continuous ⇑(φ.val.phi) :=
begin
  refine metric.uniform_continuous_iff.mpr _,
  rintros ε hε,
  obtain ⟨K, hKpos, hK⟩ := φ.prop,
  refine ⟨ε/K, div_pos hε hKpos, _⟩,
  rintros a b dab, rw dist_eq_norm,
  rw ←linear_map.map_sub,
  specialize hK (a - b), apply lt_of_le_of_lt hK _, rw mul_comm, rw ←lt_div_iff hKpos,
  convert dab,
  change ∥inclusion X A (a - b)∥ = dist (inclusion' X A a) (inclusion' X A b),
  rw dist_eq_norm,
  rw ←continuous_linear_map.map_sub, refl,
end

/-noncomputable instance [h : nonempty X] : normed_ring C(X,A) :=
{ norm_mul := λ f g, csupr_le $ λ x, le_trans (norm_mul_le _ _) (mul_le_mul
    (le_csupr (bdd_above_compact_range_norm X f) x)
    (le_csupr (bdd_above_compact_range_norm X g) x)
    (norm_nonneg (g x))
    (norm_nonneg f)),
--  ..continuous_map_ring,
  ..(infer_instance : normed_group C(X,A))
}-/

instance [h : nonempty X] : has_continuous_smul A C(X, A) :=
{ continuous_smul := begin
  change continuous ((λ p, p.1 * p.2 : C(X,A) × C(X,A) → C(X,A)) ∘
    (λ p, ((continuous_map.const p.fst), p.2) : A × C(X,A) → C(X,A) × C(X,A))),
  -- should be factored out
  have h : continuous (continuous_map.const : A → C(X,A)),
  { rw metric.continuous_iff,
    intros a ε hε,
    refine ⟨ε/2, (show 0<ε/2, by linarith), λ b hb, _⟩,
    rw dist_eq_norm at hb ⊢,
    refine lt_of_le_of_lt _ (show ε/2 < ε, by linarith),
    rw continuous_map.norm_eq_supr_norm,
    apply csupr_le,
    intro x,
    apply le_of_lt,
    simp [hb] },
  continuity,
end }

lemma cont [complete_space A] (h : nonempty X) (φ : measures'' X A) : continuous ((di  X A h).extend (φ.val.phi)) :=
begin
  refine uniform_continuous.continuous _,
  refine uniform_continuous_uniformly_extend _ (dense_inducing.dense (di X A h)) _,
  { apply uni_ind, },
  { apply uni_cont, },
end

noncomputable def integral (h : nonempty X) (φ : measures'' X A) [complete_space A] :
  continuous_linear_map A C(X, A) A :=
begin
  have cont := cont X A h φ,
  have di := di X A h,
  split,
  swap,
  { split, swap 3,
    { apply dense_inducing.extend di (φ.1).phi, }, --X nonempty needed here, for the topo space on loc const to exist
    { refine dense_range.induction_on₂ (dense_inducing.dense di) _ _,
      { exact is_closed_eq (cont.comp continuous_add)
        ((cont.comp continuous_fst).add (cont.comp continuous_snd)) },
      { rintros a b,
        change di.extend (φ.val.phi) (inclusion' X A a + inclusion' X A b) =
  di.extend (φ.val.phi) (inclusion X A a) + di.extend (φ.val.phi) (inclusion X A b),
        rw ←continuous_linear_map.map_add,
        change di.extend (φ.val.phi) ((inclusion X A) (a + b)) =
  di.extend (φ.val.phi) (inclusion X A a) + di.extend (φ.val.phi) (inclusion X A b),
        repeat { rw dense_inducing.extend_eq di (integral_cont X A φ), },
        { simp only [linear_map.map_add], }, }, },
    { rintros m, refine (λ b, dense_range.induction_on (dense_inducing.dense di) b _ _),
      { exact is_closed_eq (cont.comp (continuous_const.smul continuous_id))
        ((continuous_const.smul continuous_id).comp cont) },
      { rintros a,
        change di.extend (φ.val.phi) (m • inclusion' X A a) =
        m • di.extend (φ.val.phi) (inclusion X A a),
        rw ←continuous_linear_map.map_smul,
        change di.extend (φ.val.phi) ((inclusion X A) (m • a)) =
        m • di.extend (φ.val.phi) (inclusion X A a),
        repeat { rw dense_inducing.extend_eq di (integral_cont X A φ), },
        simp only [linear_map.map_smul], }, }, },
  simp only [auto_param_eq], assumption,
end

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

--variables {A : Type*} [integral_domain A] [algebra ℚ A]

variables (p : ℕ) [fact p.prime]

/-def dirichlet_char_space (f : ℕ) := { χ : mul_hom ℤ_[p] A // ∀ a : ℤ, gcd a f ≠ 1 → χ a = 0 }
--iff requires A to be an int dom

lemma dir_char_zero_iff (f : ℕ) (χ : dirichlet_char_space A p f) (a : ℤ) :
  gcd a f ≠ 1 → χ.val a = 0 := χ.prop a

example {a b c : Prop} (f1 : a ↔ c) (f2 : b ↔ c) : a ∧ b ↔ c :=
begin
  split,
  repeat { simp [f1, f2], },
end

example {α β : Type*} [has_mul β] (x y : α) (f g : α → β) : (f * g) x = f x * g x :=
begin
  refine pi.mul_apply f g x,
end

/-lemma int_cast_inducing : inducing (@int.cast A _ _ _ _) :=
begin
  suggest,
end-/

instance (f : ℕ) : monoid (dirichlet_char_space A p f) :=
{
  mul := begin
        rintros a b, constructor, swap, constructor, swap, exact a.val * b.val,
        { rintros x y, rw pi.mul_apply (a.val) (b.val), rw pi.mul_apply (a.val) (b.val),
          rw pi.mul_apply (a.val) (b.val), --how to do it once
          rw mul_hom.map_mul (a.val) x y, rw mul_hom.map_mul (b.val) x y, ring, },
        rintros n, simp only [mul_hom.coe_mk, pi.mul_apply, subtype.val_eq_coe],
        intro h,
        have f1 := a.prop n h, rw f1, rw zero_mul,
        end,
  one := begin constructor, swap, constructor, swap,
  set one : ℤ → A := λ n, if gcd n f = 1 then 1 else 0 with h,
  rw padic_int.
  apply dense_inducing.extend _ one,
  apply_instance,
  exact int.cast,
  split,
  swap, apply padic_int.dense_range_int_cast,


  swap,
  end,
  one_mul := begin sorry end,
  mul_one := begin sorry end,
  mul_assoc := begin sorry end,
} -/

--instance (f : ℤ) : group { χ : mul_hom ℤ A // ∀ a : ℤ, gcd a f ≠ 1 ↔ χ a = 0 } := sorry

--instance : compact_space ℤ_[p] := sorry
--instance : locally_compact_space ℤ_[p] := infer_instance
--instance : totally_disconnected_space ℤ_[p] := sorry

instance topo : topological_space (units ℤ_[p]) := infer_instance
--units Z_p → Z_p is a closed immersion (inj and image is closed) and has subspace topo
--instance : compact_space (units ℤ_[p]) := sorry

--instance : t2_space (units ℤ_[p]) := sorry

--instance : totally_disconnected_space (units ℤ_[p]) := sorry

--instance cat : (units ℤ_[p]) ∈ category_theory.Cat.objects Profinite :=

instance topo' : topological_space (units A) := infer_instance
