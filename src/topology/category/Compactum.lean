/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import category_theory.monad.types
import category_theory.monad.limits
import category_theory.equivalence
import topology.category.Top
import data.set.constructions

/-!

# Compact Hausdorff Spaces

This file proves the equivalence between the category of compact Hausdorff topological spaces
and the category of algebras for the ultrafilter monad.

TODO: Add more details.

-/

open category_theory filter topological_space category_theory.limits has_finite_inter
open_locale classical

/-- The type `Compactum` of Compacta, defined as algebras for the ultrafilter monad. -/
@[derive category]
def Compactum := monad.algebra (of_type_functor $ ultrafilter)

namespace Compactum

/-- The forgetful functor to Type* -/
@[derive [creates_limits,faithful]]
def forget : Compactum ⥤ Type* := monad.forget _
/-- The "free" Compactum functor. -/
def free : Type* ⥤ Compactum := monad.free _
/-- The adjunction between `free` and `forget`. -/
def adj : free ⊣ forget := monad.adj _

instance : concrete_category Compactum := { forget := forget }
instance : has_coe_to_sort Compactum := ⟨Type*,forget.obj⟩
instance {X Y : Compactum} : has_coe_to_fun (X ⟶ Y) := ⟨λ f, X → Y, λ f, f.f⟩
instance : has_limits Compactum := has_limits_of_has_limits_creates_limits forget

/-- The structure map for a compactum, essentially sending an ultrafilter to its limit. -/
def str (X : Compactum) : ultrafilter X → X := X.a
/-- The monadic join. -/
def join (X : Compactum) : ultrafilter (ultrafilter X) → ultrafilter X :=
  (μ_ $ of_type_functor ultrafilter).app _
/-- The inclusion of `X` into `ultrafilter X`. -/
def incl (X : Compactum) : X → ultrafilter X :=
  (η_ $ of_type_functor ultrafilter).app _

@[simp] lemma str_incl (X : Compactum) (x : X) : X.str (X.incl x) = x :=
begin
  change ((η_ (of_type_functor ultrafilter)).app _ ≫ X.a) _ = _,
  rw monad.algebra.unit,
  refl,
end

@[simp] lemma str_hom_commute (X Y : Compactum) (f : X ⟶ Y) (xs : ultrafilter X) :
  f (X.str xs) = Y.str (ultrafilter.map f xs) :=
begin
  change (X.a ≫ f.f) _ = _,
  rw ←f.h,
  refl,
end

@[simp] lemma join_distrib (X : Compactum) (uux : ultrafilter (ultrafilter X)) :
  X.str (X.join uux) = X.str (ultrafilter.map X.str uux) :=
begin
  change ((μ_ (of_type_functor ultrafilter)).app _ ≫ X.a) _ = _,
  rw monad.algebra.assoc,
  refl,
end

instance {X : Compactum} : topological_space X :=
{ is_open := { U | ∀ (F : ultrafilter X), X.str F ∈ U → U ∈ F.1 },
  is_open_univ := λ _ _, filter.univ_sets _,
  is_open_inter := λ S T h3 h4 h5 h6,
    filter.inter_sets _ (h3 _ h6.1) (h4 _ h6.2),
  is_open_sUnion := λ S h1 F ⟨T,hT,h2⟩,
    filter.sets_of_superset _ (h1 T hT _ h2) (set.subset_sUnion_of_mem hT) }

theorem is_closed_iff {X : Compactum} (S : set X) : is_closed S ↔
  (∀ F : ultrafilter X, S ∈ F.1 → X.str F ∈ S) :=
begin
  split,
  { intros cond F h,
    specialize cond F,
    by_contradiction c,
    specialize cond c,
    cases F with F hF,
    rw ultrafilter_iff_compl_mem_iff_not_mem at hF,
    rw hF at cond,
    contradiction },
  { intros h1 F h2,
    specialize h1 F,
    cases mem_or_compl_mem_of_ultrafilter F.2 S,
    { specialize h1 h, contradiction },
    assumption }
end

instance {X : Compactum} : compact_space X :=
begin
  constructor,
  rw compact_iff_ultrafilter_le_nhds,
  intros F hF h,
  refine ⟨X.str ⟨F,hF⟩,by tauto,_⟩,
  rw le_nhds_iff,
  intros S h1 h2,
  exact h2 ⟨F,hF⟩ h1,
end

/-- A local definition used only in the proofs. -/
private def basic {X : Compactum} (A : set X) : set (ultrafilter X) := {F | A ∈ F.1}
/-- A local definition used only in the proofs. -/
private def cl {X : Compactum} (A : set X) : set X := X.str '' (basic A)

private lemma basic_inter {X : Compactum} (A B : set X) : basic (A ∩ B) = basic A ∩ basic B :=
begin
  ext G,
  split,
  { intro hG, refine ⟨_,_⟩;
    apply filter.sets_of_superset _ hG;
    intros x hx;
    finish },
  { rintros ⟨h1,h2⟩,
    apply filter.inter_sets,
    assumption' }
end

private lemma subset_cl {X : Compactum} (A : set X) : A ⊆ cl A :=
begin
  intros a ha,
  use X.incl a,
  refine ⟨_,by simp⟩,
  assumption,
end

private theorem cl_cl {X : Compactum} (A : set X) : cl (cl A) ⊆ cl A :=
begin
  let fsu := finset (set (ultrafilter X)),
  let ssu := set (set (ultrafilter X)),
  let ι : fsu → ssu := coe,
  rintros _ ⟨F,hF,rfl⟩,
  let C0 : ssu := {Z | ∃ B ∈ F.1, X.str ⁻¹' B = Z},
  let AA := {G : ultrafilter X | A ∈ G.1},
  let C1 := insert AA C0,
  let C2 := finite_inter_closure C1,
  have claim1 : ∀ B C ∈ C0, B ∩ C ∈ C0,
  { rintros B C ⟨Q,hQ,rfl⟩ ⟨R,hR,rfl⟩,
    use Q ∩ R,
    simp,
    apply inter_sets,
    assumption' },
  have claim2 : ∀ B ∈ C0, set.nonempty B,
  { rintros B ⟨Q,hQ,rfl⟩,
    suffices : Q.nonempty,
    { rcases this with ⟨q,hq⟩,
      use X.incl q,
      simpa },
    apply nonempty_of_mem_ultrafilter _ F.2,
    assumption },
  have claim3 : ∀ B ∈ C0, (AA ∩ B).nonempty,
  { rintros B ⟨Q,hQ,rfl⟩,
    have : (Q ∩ cl A) ∈ F.1,
    { apply filter.inter_sets,
      assumption' },
    have : (Q ∩ cl A).nonempty,
    { apply nonempty_of_mem_ultrafilter _ F.2,
      assumption },
    rcases this with ⟨q,hq1,P,hq2,hq3⟩,
    refine ⟨P,hq2,_⟩,
    rw ←hq3 at hq1,
    simpa },
  suffices : ∀ (T : fsu), ι T ⊆ C1 → (⋂₀ ι T).nonempty,
  { obtain ⟨G,h1,hG⟩ := exists_ultrafilter_of_finite_inter_nonempty _ this,
    let GG : ultrafilter (ultrafilter X) := ⟨G,hG⟩,
    use X.join GG,
    have : ultrafilter.map X.str GG = F,
    { suffices : (ultrafilter.map X.str GG).1 ≤ F.1,
      { ext1,
        exact is_ultrafilter.unique F.2 (ultrafilter.map X.str GG).2.1 this },
      intros S hS,
      apply h1,
      right,
      use S,
      simpa },
    rw [join_distrib, this],
    refine ⟨_,rfl⟩,
    apply h1,
    left,
    refl },
  have claim4 := finite_inter_closure_has_finite_inter C1,
  have claim5 : has_finite_inter C0,
  { split,
    { use set.univ,
      refine ⟨filter.univ_sets _,_⟩,
      simp },
    { assumption } },
  have claim6 : ∀ P ∈ C2, (P : set (ultrafilter X)).nonempty,
  { suffices : ∀ P ∈ C2, P ∈ C0 ∨ ∃ Q ∈ C0, P = AA ∩ Q,
    { intros P hP,
      cases this P hP,
      apply claim2, assumption,
      rcases h with ⟨Q,hQ,rfl⟩,
      apply claim3, assumption },
    intros P hP,
    apply claim5.finite_inter_closure_insert,
    assumption },
  intros T hT,
  suffices : ⋂₀ ι T ∈ C2,
  { apply claim6,
    assumption },
  apply claim4.finite_inter_mem,
  intros t ht,
  apply finite_inter_closure.basic,
  apply hT,
  assumption,
end

lemma is_closed_cl {X : Compactum} (A : set X) : is_closed (cl A) :=
begin
  rw is_closed_iff,
  intros F hF,
  exact cl_cl _ ⟨F,hF,rfl⟩,
end

lemma str_eq_of_le_nhds {X : Compactum} (F : ultrafilter X) (x : X) :
  F.1 ≤ nhds x → X.str F = x :=
begin
  --sorry,
  intro cond,
  have claim1 : ∀ (A : set X), is_closed A → A ∈ F.1 → x ∈ A,
  { intros A hA h,
    rw le_nhds_iff at cond,
    by_contradiction,
    have : x ∈ Aᶜ, by assumption,
    specialize cond Aᶜ this hA,
    have := ultrafilter_iff_compl_mem_iff_not_mem.mp F.2,
    rw this at cond,
    contradiction },
  have claim2 : ∀ (A : set X), A ∈ F.1 → x ∈ cl A,
  { intros A hA,
    apply claim1 _ (is_closed_cl _),
    exact filter.sets_of_superset _ hA (subset_cl _) },
  let T0 : set (set (ultrafilter X)) := { S | ∃ A ∈ F.1, S = basic A },
  let AA := (X.str ⁻¹' {x}),
  let T1 := insert AA T0,
  let T2 := finite_inter_closure T1,
  have claim3 : ∀ (S1 S2 ∈ T0), S1 ∩ S2 ∈ T0,
  { rintros S1 S2 ⟨S1,hS1,rfl⟩ ⟨S2,hS2,rfl⟩,
    exact ⟨S1 ∩ S2, F.1.inter_sets hS1 hS2, by simp [basic_inter]⟩ },
  have claim4 : ∀ (S ∈ T0), (AA ∩ S).nonempty,
  { rintros S ⟨S,hS,rfl⟩,
    rcases claim2 _ hS with ⟨G,hG,hG2⟩, -- claim2 used!
    exact ⟨G,hG2,hG⟩ },
  have claim5 : ∀ (S ∈ T0), set.nonempty S,
  { rintros S ⟨S,hS,rfl⟩,
    exact ⟨F,hS⟩ },
  have claim6 : ∀ (S ∈ T2), set.nonempty S, -- clean up needed starting here.
  { suffices : ∀ S ∈ T2, S ∈ T0 ∨ ∃ Q ∈ T0, S = AA ∩ Q,
    { intros S hS,
      specialize this _ hS,
      cases this,
      apply claim5,
      assumption,
      rcases this with ⟨Q,hQ,rfl⟩,
      apply claim4,
      assumption },
    intros S hS,
    apply finite_inter_closure_insert,
    { split,
      { use set.univ,
        refine ⟨filter.univ_sets _,_⟩,
        unfold basic,
        ext,
        split,
        { intro, apply filter.univ_sets, },
        { tauto } },
      { assumption } },
    { assumption } },
  suffices : ∀ (F : finset (set (ultrafilter X))), ↑F ⊆ T1 →
    (⋂₀ (↑F : set (set (ultrafilter X)))).nonempty,
  { obtain ⟨G,h1,hG⟩ := exists_ultrafilter_of_finite_inter_nonempty _ this,
    let GG : ultrafilter (ultrafilter X) := ⟨G,hG⟩,
    have c1 : X.join GG = F,
    { suffices : (X.join GG).1 ≤ F.1,
      { ext1,
        apply is_ultrafilter.unique,
        exact F.2,
        exact (X.join GG).2.1,
        assumption },
      intros P hP,
      apply h1,
      right,
      use P,
      refine ⟨hP,_⟩,
      refl },
    have c2 : ({x} : set X) ∈ (ultrafilter.map X.str GG).1,
    { apply h1,
      left,
      refl },
    have c3 : ultrafilter.map X.str GG = X.incl x,
    { suffices : (ultrafilter.map X.str GG).1 ≤ (X.incl x).1,
      { ext1,
        apply is_ultrafilter.unique,
        exact (X.incl x).2,
        exact (ultrafilter.map X.str GG).2.1,
        assumption },
      intros P hP,
      apply filter.sets_of_superset _ c2,
      rintros x ⟨rfl⟩,
      exact hP },
    rw [←c1,join_distrib,c3],
    simp },
  intros T hT,
  apply claim6,
  apply finite_inter_mem,
  exact finite_inter_closure_has_finite_inter _,
  intros t ht,
  apply finite_inter_closure.basic,
  apply hT,
  exact ht,
end

lemma le_nhds_of_str_eq {X : Compactum} (F : ultrafilter X) (x : X) :
  X.str F = x → F.1 ≤ nhds x := λ h, le_nhds_iff.mpr (λ s hx hs, hs _ $ by rwa h)

instance {X : Compactum} : t2_space X :=
begin
  rw t2_iff_ultrafilter,
  intros _ _ _ hF hx hy,
  replace hx := str_eq_of_le_nhds ⟨_,hF⟩ _ hx,
  replace hy := str_eq_of_le_nhds ⟨_,hF⟩ _ hy,
  cc,
end

lemma continuous_of_hom {X Y : Compactum} (f : X ⟶ Y) : continuous f :=
begin
  rw continuous_iff_ultrafilter,
  intros x _ h1 h2,
  change (ultrafilter.map f ⟨_,h1⟩).1 ≤ _,
  apply le_nhds_of_str_eq,
  rw [←str_hom_commute, str_eq_of_le_nhds ⟨_,h1⟩ x h2],
end

/-
def to_Top : Compactum ⥤ Top :=
{ obj := λ X, Top.of X,
  map := λ X Y f,
  { to_fun := f,
    continuous_to_fun := continuous_of_hom _ } }
-/

noncomputable def of_Top (X : Type*) [topological_space X]
  [compact_space X] [t2_space X] : Compactum :=
{ A := X,
  a := ultrafilter.Lim,
  unit' := begin
    ext x,
    letI : nonempty X := ⟨x⟩,
    change Lim (pure x : ultrafilter X).1 = x,
    letI := (pure x : ultrafilter X).2.1,
    apply Lim_eq,
    finish [le_nhds_iff],
  end,
  assoc' := begin
    ext FF,
    change ultrafilter (ultrafilter X) at FF,
    simp at *,
    change (mjoin FF).Lim = (ultrafilter.map ultrafilter.Lim FF).Lim,
    set x := (ultrafilter.map ultrafilter.Lim FF).Lim,
    have claim : ∀ (U : set X) (F : ultrafilter X), F.Lim ∈ U → is_open U → U ∈ F.1,
    { intros U F h1 hU,
      suffices : F.1 ≤ nhds (F.Lim),
      { rw le_nhds_iff at this,
        apply this,
        assumption' },
      have : is_compact (set.univ : set X),
      { suffices : compact_space X,
        { cases this,
          assumption },
        apply_instance },
      have := compact_iff_ultrafilter_le_nhds.mp this,
      specialize this F.1 F.2 _,
      rcases this with ⟨a,ha,cond⟩,
      apply le_nhds_Lim,
      use a,
      assumption,
      intros U hU,
      simp at hU,
      rw hU,
      apply filter.univ_sets },
    have c1 : (ultrafilter.map ultrafilter.Lim FF).Lim = x, by refl,
    have c2 : (ultrafilter.map ultrafilter.Lim FF).1 ≤ nhds x,
    { rw le_nhds_iff,
      intros U hx hU,
      apply claim,
      rwa c1,
      assumption },
    have c3 : ∀ (U : set X), x ∈ U → is_open U → { G : ultrafilter X | U ∈ G.1 } ∈ FF.1,
    { intros U hx hU,
      suffices : ultrafilter.Lim ⁻¹' U ∈ FF.1,
      { apply filter.sets_of_superset _ this,
        intros P hP,
        simp at hP,
        simp,
        apply claim,
        assumption' },
      apply c2,
      apply mem_nhds_sets,
      assumption' },
    have : ∀ (U : set X), x ∈ U → is_open U → U ∈ (mjoin FF).1,
    { apply c3 },
    have : (mjoin FF).1 ≤ nhds x,
    { rw le_nhds_iff,
      apply this },
    letI := (mjoin FF).2.1,
    apply Lim_eq,
    assumption,
  end }

instance {X : Type*} [topological_space X] [compact_space X] [t2_space X] [nonempty X] :
  nonempty (of_Top X) := by {obtain ⟨x⟩ := (show nonempty X, by apply_instance), use x}

def hom_of_continuous {X Y : Compactum} (f : X → Y) (cont : continuous f) : X ⟶ Y :=
{ f := f,
  h' := begin
    rw continuous_iff_ultrafilter at cont,
    ext (F : ultrafilter X),
    specialize cont (X.str F) F.1 F.2,
    have := le_nhds_of_str_eq F (X.str F) rfl,
    specialize cont this,
    have cont' := str_eq_of_le_nhds (ultrafilter.map f F) _ cont,
    simp only [types_comp_apply, of_type_functor_map],
    erw ←cont',
    refl,
  end }

end Compactum

/-- The type of Compact Hausdorff topological spaces. -/
structure CompHaus :=
(to_Top : Top)
[is_compact : compact_space to_Top . tactic.apply_instance]
[is_hausdorff : t2_space to_Top . tactic.apply_instance]

namespace CompHaus

instance : has_coe_to_sort CompHaus := ⟨Type*,λ X, X.to_Top⟩
instance {X : CompHaus} : compact_space X := X.is_compact
instance {X : CompHaus} : t2_space X := X.is_hausdorff

instance category : category CompHaus := induced_category.category to_Top

end CompHaus

def Compactum_to_CompHaus : Compactum ⥤ CompHaus :=
{ obj := λ X, { to_Top := { α := X } },
  map := λ X Y f,
  { to_fun := f,
    continuous_to_fun := Compactum.continuous_of_hom _ }}

namespace Compactum_to_CompHaus

def full : full Compactum_to_CompHaus :=
{ preimage := λ X Y f, Compactum.hom_of_continuous f.1 f.2 }

def faithful : faithful Compactum_to_CompHaus := {}

private theorem helper {X : Type*} [topological_space X] [compact_space X] [t2_space X]
  (U : set X) : is_open U ↔ (∀ F : ultrafilter X, F.Lim ∈ U → U ∈ F.1) :=
begin
  rw is_open_iff_ultrafilter,
  refine ⟨λ h F hF, h _ hF _ F.2 (is_ultrafilter.le_nhds_Lim _),_⟩,
  intros cond x hx f hf h,
  let F : ultrafilter X := ⟨f,hf⟩,
  change F.1 ≤ _ at h,
  rw ←is_ultrafilter.Lim_eq_iff_le_nhds at h,
  rw ←h at *,
  exact cond _ hx
end

noncomputable def iso_of_Top {D : CompHaus} :
  Compactum_to_CompHaus.obj (Compactum.of_Top D) ≅ D :=
{ hom :=
  { to_fun := id,
    continuous_to_fun := λ _ h, by {rw helper at h, exact h} },
  inv :=
  { to_fun := id,
    continuous_to_fun := λ _ h1, by {rw helper, intros _ h2, exact h1 _ h2} } }

noncomputable def ess_surj : ess_surj Compactum_to_CompHaus :=
{ obj_preimage := λ X, Compactum.of_Top X,
  iso' := λ _, iso_of_Top }

noncomputable def is_equivalence : is_equivalence Compactum_to_CompHaus :=
begin
  apply equivalence.equivalence_of_fully_faithfully_ess_surj _,
  exact Compactum_to_CompHaus.full,
  exact Compactum_to_CompHaus.faithful,
  exact Compactum_to_CompHaus.ess_surj,
end

end Compactum_to_CompHaus
