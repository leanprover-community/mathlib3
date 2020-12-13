/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import category_theory.monad.types
import category_theory.monad.limits
import category_theory.equivalence
import topology.category.CompHaus
import data.set.constructions

/-!

# Compacta and Compact Hausdorff Spaces

Recall that, given a monad `M` on `Type*`, an *algebra* for `M` consists of the following data:
- A type `X : Type*`
- A "structure" map `M X → X`.
This data must also satisfy a distributivity and unit axiom, and algebras for `M` form a category
in an evident way.

See the file `category_theory.monad.algebra` for a general version, as well as the following link.
https://ncatlab.org/nlab/show/monad

This file proves the equivalence between the category of *compact Hausdorff topological spaces*
and the category of algebras for the *ultrafilter monad*.

## Notation:

Here are the main objects introduced in this file.
- `Compactum` is the type of compacta, which we define as algebras for the ultrafilter monad.
- `Compactum_to_CompHaus` is the functor `Compactum ⥤ CompHaus`. Here `CompHaus` is the usual
  category of compact Hausdorff spaces.
- `Compactum_to_CompHaus.is_equivalence` is a term of type `is_equivalence Compactum_to_CompHaus`.

The proof of this equivalence is a bit technical. But the idea is quite simply that the structure
map `ultrafilter X → X` for an algebra `X` of the ultrafilter monad should be considered as the map
sending an ultrafilter to its limit in `X`. The topology on `X` is then defined by mimicking the
characterization of open sets in terms of ultrafilters.

Any `X : Compactum` is endowed with a coercion to `Type*`, as well as the following instances:
- `topological_space X`.
- `compact_space X`.
- `t2_space X`.

Any morphism `f : X ⟶ Y` of is endowed with a coercion to a function `X → Y`, which is shown to
be continuous in `continuous_of_hom`.

The function `Compactum.of_topological_space` can be used to construct a `Compactum` from a
topological space which satisfies `compact_space` and `t2_space`.

We also add wrappers around structures which already exist. Here are the main ones, all in the
`Compactum` namespace:

- `forget : Compactum ⥤ Type*` is the forgetful functor, which induces a `concrete_category`
  instance for `Compactum`.
- `free : Type* ⥤ Compactum` is the left adjoint to `forget`, and the adjunction is in `adj`.
- `str : ultrafilter X → X` is the structure map for `X : Compactum`.
  The notation `X.str` is preferred.
- `join : ultrafilter (ultrafilter X) → ultrafilter X` is the monadic join for `X : Compactum`.
  Again, the notation `X.join` is preferred.
- `incl : X → ultrafilter X` is the unit for `X : Compactum`. The notation `X.incl` is preferred.

## References

- E. Manes, Algebraic Theories, Graduate Texts in Mathematics 26, Springer-Verlag, 1976.
- https://ncatlab.org/nlab/show/ultrafilter

-/

open category_theory filter topological_space category_theory.limits has_finite_inter
open_locale classical

local notation `β` := of_type_functor ultrafilter

/-- The type `Compactum` of Compacta, defined as algebras for the ultrafilter monad. -/
@[derive [category, inhabited]]
def Compactum := monad.algebra β

namespace Compactum

/-- The forgetful functor to Type* -/
@[derive [creates_limits,faithful]]
def forget : Compactum ⥤ Type* := monad.forget _

/-- The "free" Compactum functor. -/
def free : Type* ⥤ Compactum := monad.free _

/-- The adjunction between `free` and `forget`. -/
def adj : free ⊣ forget := monad.adj _

-- Basic instances
instance : concrete_category Compactum := { forget := forget }
instance : has_coe_to_sort Compactum := ⟨Type*,forget.obj⟩
instance {X Y : Compactum} : has_coe_to_fun (X ⟶ Y) := ⟨λ f, X → Y, λ f, f.f⟩
instance : has_limits Compactum := has_limits_of_has_limits_creates_limits forget

/-- The structure map for a compactum, essentially sending an ultrafilter to its limit. -/
def str (X : Compactum) : ultrafilter X → X := X.a

/-- The monadic join. -/
def join (X : Compactum) : ultrafilter (ultrafilter X) → ultrafilter X := (μ_ β).app _

/-- The inclusion of `X` into `ultrafilter X`. -/
def incl (X : Compactum) : X → ultrafilter X := (η_ β).app _

@[simp] lemma str_incl (X : Compactum) (x : X) : X.str (X.incl x) = x :=
begin
  change ((η_ β).app _ ≫ X.a) _ = _,
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
  change ((μ_ β).app _ ≫ X.a) _ = _,
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
    by_contradiction c,
    specialize cond F c,
    cases F with F hF,
    rw ultrafilter_iff_compl_mem_iff_not_mem at hF,
    rw hF at cond,
    contradiction },
  { intros h1 F h2,
    specialize h1 F,
    cases mem_or_compl_mem_of_ultrafilter F.2 S;
    finish }
end

instance {X : Compactum} : compact_space X :=
begin
  constructor,
  rw compact_iff_ultrafilter_le_nhds,
  intros F hF h,
  refine ⟨X.str ⟨F,hF⟩, by tauto, _⟩,
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
  { intro hG,
    refine ⟨_, _⟩;
    apply filter.sets_of_superset _ hG;
    intros x hx;
    finish },
  { rintros ⟨h1,h2⟩,
    exact G.val.inter_sets h1 h2 }
end

private lemma subset_cl {X : Compactum} (A : set X) : A ⊆ cl A := λ a ha, ⟨X.incl a, ha,by simp⟩

private theorem cl_cl {X : Compactum} (A : set X) : cl (cl A) ⊆ cl A :=
begin
  rintros _ ⟨F,hF,rfl⟩,
  -- Notation to be used in this proof.
  let fsu := finset (set (ultrafilter X)),
  let ssu := set (set (ultrafilter X)),
  let ι : fsu → ssu := coe,
  let C0 : ssu := {Z | ∃ B ∈ F.1, X.str ⁻¹' B = Z},
  let AA := {G : ultrafilter X | A ∈ G.1},
  let C1 := insert AA C0,
  let C2 := finite_inter_closure C1,
  -- C0 is closed under intersections.
  have claim1 : ∀ B C ∈ C0, B ∩ C ∈ C0,
  { rintros B C ⟨Q,hQ,rfl⟩ ⟨R,hR,rfl⟩,
    use Q ∩ R,
    simp only [and_true, eq_self_iff_true, set.preimage_inter, subtype.val_eq_coe],
    exact inter_sets _ hQ hR },
  -- All sets in C0 are nonempty.
  have claim2 : ∀ B ∈ C0, set.nonempty B,
  { rintros B ⟨Q,hQ,rfl⟩,
    obtain ⟨q⟩ := nonempty_of_mem_ultrafilter F.2 hQ,
    use X.incl q,
    simpa, },
  -- The intersection of AA with every set in C0 is nonempty.
  have claim3 : ∀ B ∈ C0, (AA ∩ B).nonempty,
  { rintros B ⟨Q,hQ,rfl⟩,
    have : (Q ∩ cl A).nonempty,
    { apply nonempty_of_mem_ultrafilter F.2,
      exact F.1.inter_sets hQ hF },
    rcases this with ⟨q,hq1,P,hq2,hq3⟩,
    refine ⟨P,hq2,_⟩,
    rw ←hq3 at hq1,
    simpa },
  -- Suffices to show that the intersection of any finite subcollection of C1 is nonempty.
  suffices : ∀ (T : fsu), ι T ⊆ C1 → (⋂₀ ι T).nonempty,
  { obtain ⟨G,h1,hG⟩ := exists_ultrafilter_of_finite_inter_nonempty _ this,
    let GG : ultrafilter (ultrafilter X) := ⟨G, hG⟩,
    use X.join GG,
    have : ultrafilter.map X.str GG = F,
    { suffices : (ultrafilter.map X.str GG).1 ≤ F.1,
      { ext1,
        exact is_ultrafilter.unique F.2 (ultrafilter.map X.str GG).2.1 this },
      intros S hS,
      refine h1 (or.inr ⟨S, by simpa⟩) },
    rw [join_distrib, this],
    exact ⟨h1 (or.inl rfl), rfl⟩ },
  -- C2 is closed under finite intersections (by construction!).
  have claim4 := finite_inter_closure_has_finite_inter C1,
  -- C0 is closed under finite intersections by claim1.
  have claim5 : has_finite_inter C0 := ⟨⟨set.univ, filter.univ_sets _, by simp⟩, claim1⟩,
  -- Every element of C2 is nonempty.
  have claim6 : ∀ P ∈ C2, (P : set (ultrafilter X)).nonempty,
  { suffices : ∀ P ∈ C2, P ∈ C0 ∨ ∃ Q ∈ C0, P = AA ∩ Q,
    { intros P hP,
      cases this P hP,
      { exact claim2 _ h },
      { rcases h with ⟨Q, hQ, rfl⟩,
        exact claim3 _ hQ } },
    intros P hP,
    exact claim5.finite_inter_closure_insert _ hP },
  intros T hT,
  -- Suffices to show that the intersection of the T's is contained in C2.
  suffices : ⋂₀ ι T ∈ C2, by exact claim6 _ this,
  -- Finish
  apply claim4.finite_inter_mem,
  intros t ht,
  exact finite_inter_closure.basic (@hT t ht),
end

lemma is_closed_cl {X : Compactum} (A : set X) : is_closed (cl A) :=
begin
  rw is_closed_iff,
  intros F hF,
  exact cl_cl _ ⟨F, hF, rfl⟩,
end

lemma str_eq_of_le_nhds {X : Compactum} (F : ultrafilter X) (x : X) :
  F.1 ≤ nhds x → X.str F = x :=
begin
  -- Notation to be used in this proof.
  let fsu := finset (set (ultrafilter X)),
  let ssu := set (set (ultrafilter X)),
  let ι : fsu → ssu := coe,
  let T0 : ssu := { S | ∃ A ∈ F.1, S = basic A },
  let AA := (X.str ⁻¹' {x}),
  let T1 := insert AA T0,
  let T2 := finite_inter_closure T1,
  intro cond,
  -- If F contains a closed set A, then x is contained in A.
  have claim1 : ∀ (A : set X), is_closed A → A ∈ F.1 → x ∈ A,
  { intros A hA h,
    by_contradiction H,
    rw le_nhds_iff at cond,
    specialize cond Aᶜ H hA,
    rw ultrafilter_iff_compl_mem_iff_not_mem.mp F.2 at cond,
    contradiction },
  -- If A ∈ F, then x ∈ cl A.
  have claim2 : ∀ (A : set X), A ∈ F.1 → x ∈ cl A,
  { intros A hA,
    exact claim1 (cl A) (is_closed_cl A) (F.val.sets_of_superset hA (subset_cl A)) },
  -- T0 is closed under intersections.
  have claim3 : ∀ (S1 S2 ∈ T0), S1 ∩ S2 ∈ T0,
  { rintros S1 S2 ⟨S1, hS1, rfl⟩ ⟨S2, hS2, rfl⟩,
    exact ⟨S1 ∩ S2, F.1.inter_sets hS1 hS2, by simp [basic_inter]⟩ },
  -- For every S ∈ T0, the intersection AA ∩ S is nonempty.
  have claim4 : ∀ (S ∈ T0), (AA ∩ S).nonempty,
  { rintros S ⟨S, hS, rfl⟩,
    rcases claim2 _ hS with ⟨G, hG, hG2⟩,
    exact ⟨G, hG2, hG⟩ },
  -- Every element of T0 is nonempty.
  have claim5 : ∀ (S ∈ T0), set.nonempty S,
  { rintros S ⟨S, hS, rfl⟩,
    exact ⟨F, hS⟩ },
  -- Every element of T2 is nonempty.
  have claim6 : ∀ (S ∈ T2), set.nonempty S,
  { suffices : ∀ S ∈ T2, S ∈ T0 ∨ ∃ Q ∈ T0, S = AA ∩ Q,
    { intros S hS,
      cases this _ hS with h h,
      { exact claim5 S h },
      { rcases h with ⟨Q, hQ, rfl⟩,
        exact claim4 Q hQ } },
    intros S hS,
    apply finite_inter_closure_insert,
    { split,
      { use set.univ,
        refine ⟨filter.univ_sets _, _⟩,
        ext,
        refine ⟨_, by tauto⟩,
        { intro,
          apply filter.univ_sets, } },
      { exact claim3} },
    { exact hS} },
  -- It suffices to show that the intersection of any finite subset of T1 is nonempty.
  suffices : ∀ (F : fsu), ↑F ⊆ T1 → (⋂₀ ι F).nonempty,
  { obtain ⟨G,h1,hG⟩ := exists_ultrafilter_of_finite_inter_nonempty _ this,
    let GG : ultrafilter (ultrafilter X) := ⟨G, hG⟩,
    have c1 : X.join GG = F,
    { suffices : (X.join GG).1 ≤ F.1,
      { ext1,
        exact is_ultrafilter.unique F.2 (join X GG).2.1 this},
      intros P hP,
      exact h1 (or.inr ⟨P, hP, rfl⟩) },
    have c2 : ultrafilter.map X.str GG = X.incl x,
    { suffices : (ultrafilter.map X.str GG).1 ≤ (X.incl x).1,
      { ext1,
        exact is_ultrafilter.unique (incl X x).2 (ultrafilter.map (str X) GG).2.1 this },
      intros P hP,
      apply filter.sets_of_superset _ (h1 (or.inl rfl)),
      rintros x ⟨rfl⟩,
      exact hP },
    simp [←c1, c2] },
  -- Finish...
  intros T hT,
  refine claim6 _ (finite_inter_mem (finite_inter_closure_has_finite_inter _) _ _),
  intros t ht,
  exact finite_inter_closure.basic (@hT t ht)
end

lemma le_nhds_of_str_eq {X : Compactum} (F : ultrafilter X) (x : X) :
  X.str F = x → F.1 ≤ nhds x := λ h, le_nhds_iff.mpr (λ s hx hs, hs _ $ by rwa h)

-- All the hard work above boils down to this t2_space instance.
instance {X : Compactum} : t2_space X :=
begin
  rw t2_iff_ultrafilter,
  intros _ _ _ hF hx hy,
  replace hx := str_eq_of_le_nhds ⟨_, hF⟩ _ hx,
  replace hy := str_eq_of_le_nhds ⟨_, hF⟩ _ hy,
  cc,
end

/-- The structure map of a compactum actually computes limits. -/
lemma Lim_eq_str {X : Compactum} (F : ultrafilter X) : F.Lim = X.str F :=
begin
  erw [is_ultrafilter.Lim_eq_iff_le_nhds, le_nhds_iff],
  tauto,
end

lemma cl_eq_closure {X : Compactum} (A : set X) : cl A = closure A :=
begin
  ext,
  rw mem_closure_iff_ultrafilter,
  split,
  { rintro ⟨F, h1, h2⟩,
    exact ⟨F, h1, le_nhds_of_str_eq _ _ h2⟩ },
  { rintro ⟨F, h1, h2⟩,
    exact ⟨F, h1, str_eq_of_le_nhds _ _ h2⟩ }
end

/-- Any morphism of compacta is continuous. -/
lemma continuous_of_hom {X Y : Compactum} (f : X ⟶ Y) : continuous f :=
begin
  rw continuous_iff_ultrafilter,
  intros x _ h1 h2,
  change (ultrafilter.map f ⟨_, h1⟩).1 ≤ _,
  apply le_nhds_of_str_eq,
  rw [← str_hom_commute, str_eq_of_le_nhds ⟨_, h1⟩ x h2],
end

/-- Given any compact Hausdorff space, we construct a Compactum. -/
noncomputable def of_topological_space (X : Type*) [topological_space X]
  [compact_space X] [t2_space X] : Compactum :=
{ A := X,
  a := ultrafilter.Lim,
  unit' := by {ext x, exact Lim_eq (by finish [le_nhds_iff]) },
  assoc' := begin
    ext FF,
    change ultrafilter (ultrafilter X) at FF,
    set x := (ultrafilter.map ultrafilter.Lim FF).Lim with c1,
    have c2 : ∀ (U : set X) (F : ultrafilter X), F.Lim ∈ U → is_open U → U ∈ F.1,
    { intros U F h1 hU,
      exact c1 ▸ is_open_iff_ultrafilter.mp hU _ h1 _ F.2 (is_ultrafilter.le_nhds_Lim _) },
    have c3 : (ultrafilter.map ultrafilter.Lim FF).1 ≤ nhds x,
    { rw le_nhds_iff,
      intros U hx hU,
      refine c2 _ _ (by rwa ← c1) hU },
    have c4 : ∀ (U : set X), x ∈ U → is_open U → { G : ultrafilter X | U ∈ G.1 } ∈ FF.1,
    { intros U hx hU,
      suffices : ultrafilter.Lim ⁻¹' U ∈ FF.1,
      { apply filter.sets_of_superset _ this,
        intros P hP,
        exact c2 U P hP hU},
      exact @c3 U (mem_nhds_sets hU hx) },
    apply Lim_eq,
    rw le_nhds_iff,
    exact c4,
  end }

/-- Any continuous map between Compacta is a morphism of compacta. -/
def hom_of_continuous {X Y : Compactum} (f : X → Y) (cont : continuous f) : X ⟶ Y :=
{ f := f,
  h' := begin
    rw continuous_iff_ultrafilter at cont,
    ext (F : ultrafilter X),
    specialize cont (X.str F) F.1 F.2 (le_nhds_of_str_eq F (X.str F) rfl),
    have := str_eq_of_le_nhds (ultrafilter.map f F) _ cont,
    simpa only [←this, types_comp_apply, of_type_functor_map],
  end }

end Compactum

/-- The functor functor from Compactum to CompHaus. -/
def Compactum_to_CompHaus : Compactum ⥤ CompHaus :=
{ obj := λ X, { to_Top := { α := X } },
  map := λ X Y f,
  { to_fun := f,
    continuous_to_fun := Compactum.continuous_of_hom _ }}

namespace Compactum_to_CompHaus

/-- The functor Compactum_to_CompHaus is full. -/
def full : full Compactum_to_CompHaus :=
{ preimage := λ X Y f, Compactum.hom_of_continuous f.1 f.2 }

/-- The functor Compactum_to_CompHaus is faithful. -/
lemma faithful : faithful Compactum_to_CompHaus := {}

/-- This definition is used to prove essential surjectivity of Compactum_to_CompHaus. -/
noncomputable def iso_of_topological_space {D : CompHaus} :
  Compactum_to_CompHaus.obj (Compactum.of_topological_space D) ≅ D :=
{ hom :=
  { to_fun := id,
    continuous_to_fun := λ _ h, by {rw is_open_iff_ultrafilter' at h, exact h} },
  inv :=
  { to_fun := id,
    continuous_to_fun := λ _ h1, by {rw is_open_iff_ultrafilter', intros _ h2, exact h1 _ h2} } }

/-- The functor Compactum_to_CompHaus is essentially surjective. -/
noncomputable def ess_surj : ess_surj Compactum_to_CompHaus :=
{ obj_preimage := λ X, Compactum.of_topological_space X,
  iso' := λ _, iso_of_topological_space }

/-- The functor Compactum_to_CompHaus is an equivalence of categories. -/
noncomputable def is_equivalence : is_equivalence Compactum_to_CompHaus :=
begin
  apply equivalence.equivalence_of_fully_faithfully_ess_surj _,
  exact Compactum_to_CompHaus.full,
  exact Compactum_to_CompHaus.faithful,
  exact Compactum_to_CompHaus.ess_surj,
end

end Compactum_to_CompHaus
