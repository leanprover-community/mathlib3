import category_theory.monad.algebra
import category_theory.monad.types
import category_theory.limits.creates
import category_theory.monad.limits
import category_theory.limits.types
import category_theory.limits.preserves.basic
import category_theory.equivalence
import topology.category.Top
import topology.stone_cech
import topology.order
import topology.separation
import data.set.constructions
import data.set.basic
import data.finset

open category_theory filter topological_space category_theory.limits
open_locale classical

@[derive category]
def Compactum := monad.algebra (of_type_functor $ ultrafilter)

namespace Compactum

@[derive [creates_limits,faithful]]
def forget : Compactum ⥤ Type* := monad.forget _
def free : Type* ⥤ Compactum := monad.free _
def adj : free ⊣ forget := monad.adj _

instance : concrete_category Compactum := { forget := forget }
instance : has_coe_to_sort Compactum := ⟨Type*,forget.obj⟩
instance {X Y : Compactum} : has_coe_to_fun (X ⟶ Y) := ⟨λ f, X → Y, λ f, f.f⟩
instance : has_limits Compactum := has_limits_of_has_limits_creates_limits forget

def str (X : Compactum) : ultrafilter X → X := X.a
def join (X : Compactum) : ultrafilter (ultrafilter X) → ultrafilter X :=
  (μ_ $ of_type_functor ultrafilter).app _
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
    change ∀ _, _ at cond,
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
  use X.str ⟨F,hF⟩,
  refine ⟨by tauto,_⟩,
  rw le_nhds_iff,
  intros S h1 h2,
  exact h2 ⟨F,hF⟩ h1,
end

def basic {X : Compactum} (A : set X) : set (ultrafilter X) := {F | A ∈ F.1}
def closure {X : Compactum} (A : set X) : set X := X.str '' (basic A)

@[simp] lemma closure_empty {X : Compactum} : closure (∅ : set X) = ∅ :=
begin
  suffices : basic (∅ : set X) = ∅,
  { unfold closure, rw this, simp },
  ext F,
  split,
  { intro h,
    unfold basic at h,
    dsimp at h,
    rw ←set.compl_univ at h,
    change _ ∈ F.val at h,
    rw ultrafilter_iff_compl_mem_iff_not_mem.mp F.2 set.univ at h,
    apply h,
    exact filter.univ_sets _ },
  { intro h,
    exact false.elim h }
end

lemma subset_closure {X : Compactum} (A : set X) : A ⊆ closure A :=
begin
  intros a ha,
  use X.incl a,
  refine ⟨_,by simp⟩,
  assumption,
end

open has_finite_inter

theorem closure_closure {X : Compactum} (A : set X) : closure (closure A) ⊆ closure A :=
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
    have : (Q ∩ closure A) ∈ F.1,
    { apply filter.inter_sets,
      assumption' },
    have : (Q ∩ closure A).nonempty,
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

lemma is_closed_closure {X : Compactum} (A : set X) : is_closed (closure A) :=
begin
  rw is_closed_iff,
  intros F hF,
  apply closure_closure,
  refine ⟨F,_,rfl⟩,
  assumption,
end

lemma str_eq_of_tendsto {X : Compactum} (F : ultrafilter X) (x : X) : F.1 ≤ nhds x → X.str F = x :=
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
  have claim2 : ∀ (A : set X), A ∈ F.1 → x ∈ closure A,
  { intros A hA,
    apply claim1,
    exact is_closed_closure _,
    apply filter.sets_of_superset _ hA,
    exact subset_closure _ },
  let T0 : set (set (ultrafilter X)) := { S | ∃ A ∈ F.1, S = basic A },
  let AA := (X.str ⁻¹' {x}),
  let T1 := insert AA T0,
  let T2 := finite_inter_closure T1,
  have claim3 : ∀ (S1 S2 ∈ T0), S1 ∩ S2 ∈ T0,
  { rintros S1 S2 ⟨S1,hS1,rfl⟩ ⟨S2,hS2,rfl⟩,
    use S1 ∩ S2,
    split,
    apply filter.inter_sets, assumption',
    unfold basic,
    ext G,
    split,
    intro hG,
    apply filter.inter_sets,
    exact hG.1, exact hG.2,
    intro hG,
    split;
    apply filter.sets_of_superset _ hG;
    simp },
  have claim4 : ∀ (S ∈ T0), (AA ∩ S).nonempty,
  { rintros S ⟨S,hS,rfl⟩,
    specialize claim2 _ hS,
    rcases claim2 with ⟨G,hG,hG2⟩, -- claim2 used!
    use G,
    split,
    assumption' },
  have claim5 : ∀ (S ∈ T0), set.nonempty S,
  { rintros S ⟨S,hS,rfl⟩,
    use F,
    assumption },
  have claim6 : ∀ (S ∈ T2), set.nonempty S,
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

lemma tendsto_of_str_eq {X : Compactum} (F : ultrafilter X) (x : X) :
  X.str F = x → F.1 ≤ nhds x :=
begin
  rintro ⟨rfl⟩,
  rw le_nhds_iff,
  intros S hx hS,
  exact hS F hx,
end

instance {X : Compactum} : t2_space X :=
begin
  rw t2_iff_ultrafilter,
  intros F x y hF hx hy,
  let G : ultrafilter X := ⟨F,hF⟩,
  replace hx := str_eq_of_tendsto G x hx,
  replace hy := str_eq_of_tendsto G y hy,
  cc,
end

lemma continuous_of_morphism {X Y : Compactum} (f : X ⟶ Y) : continuous f :=
begin
  rw continuous_iff_ultrafilter,
  intros x F hF hx,
  let G : ultrafilter X := ⟨F,hF⟩,
  change (ultrafilter.map f G).1 ≤ _,
  apply tendsto_of_str_eq,
  replace hx := str_eq_of_tendsto G x hx,
  rw ←str_hom_commute,
  congr,
  assumption,
end

def to_Top : Compactum ⥤ Top :=
{ obj := λ X, Top.of X,
  map := λ X Y f,
  { to_fun := f,
    continuous_to_fun := continuous_of_morphism _ } }

noncomputable def of_nonempty_Top (X : Type*) [nonempty X] [topological_space X]
  [compact_space X] [t2_space X] : Compactum :=
{ A := X,
  a := λ (F : ultrafilter X), Lim F.1,
  unit' := begin
    ext x,
    simp,
    change Lim (pure x : ultrafilter X).1 = x,
    letI := (pure x : ultrafilter X).2.1,
    apply Lim_eq,
    rw le_nhds_iff,
    intros U hx hU,
    assumption,
  end,
  assoc' := begin
    let Lim' : ultrafilter X → X := λ F, Lim F.1,
    ext FF,
    change ultrafilter (ultrafilter X) at FF,
    simp at *,
    change Lim' (mjoin FF) = Lim' (ultrafilter.map Lim' FF),
    set x := Lim' (ultrafilter.map Lim' FF),
    have claim : ∀ (U : set X) (F : ultrafilter X), Lim' F ∈ U → is_open U → U ∈ F.1,
    { intros U F h1 hU,
      suffices : F.1 ≤ nhds (Lim' F),
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
      apply Lim_spec,
      use a,
      assumption,
      intros U hU,
      simp at hU,
      rw hU,
      apply filter.univ_sets },
    have c1 : Lim' (ultrafilter.map Lim' FF) = x, by refl,
    have c2 : (ultrafilter.map Lim' FF).1 ≤ nhds x,
    { rw le_nhds_iff,
      intros U hx hU,
      apply claim,
      rwa c1,
      assumption },
    have c3 : ∀ (U : set X), x ∈ U → is_open U → { G : ultrafilter X | U ∈ G.1 } ∈ FF.1,
    { intros U hx hU,
      suffices : Lim' ⁻¹' U ∈ FF.1,
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
  nonempty (of_nonempty_Top X) :=
begin
  have c : nonempty X := by apply_instance,
  rcases c,
  use c,
end

noncomputable def morphism_of_continuous {X Y : Type*} [topological_space X] [topological_space Y]
  [compact_space X] [compact_space Y] [t2_space X] [t2_space Y] [nonempty X] [nonempty Y]
  (f : X → Y) (cont : continuous f) : (of_nonempty_Top X) ⟶ (of_nonempty_Top Y) :=
{ f := f,
  h' := begin
    rw continuous_iff_ultrafilter at cont,
    ext (F : ultrafilter X),
    simp,
    change Lim _ = f (Lim _),
    have : F.1 ≤ nhds (Lim F.1),
    { have : is_compact (set.univ : set X),
      { suffices : compact_space X,
        { cases this,
          assumption },
        apply_instance },
      have := compact_iff_ultrafilter_le_nhds.mp this,
      specialize this F.1 F.2 _,
      rcases this with ⟨a,ha,cond⟩,
      apply Lim_spec,
      use a,
      assumption,
      intros U hU,
      simp at hU,
      rw hU,
      apply filter.univ_sets },
    specialize cont _ F.1 F.2 this,
    letI := (ultrafilter.map f F).2.1,
    apply Lim_eq,
    assumption,
  end }

def morphism_of_continuous' {X Y : Compactum} (f : X → Y) (cont : continuous f) : X ⟶ Y :=
{ f := f,
  h' := begin
    by_cases nonempty X,
    have : nonempty Y,
    { rcases h,
      use f h },
    letI := this,
    letI := h,
    rw continuous_iff_ultrafilter at cont,
    ext (F : ultrafilter X),
    specialize cont (X.str F) F.1 F.2,
    have := tendsto_of_str_eq F (X.str F) rfl,
    specialize cont this,
    have cont' := str_eq_of_tendsto (ultrafilter.map f F) _ cont,
    simp,
    erw ←cont',
    refl,
    ext (F : ultrafilter X),
    rcases nonempty_of_mem_ultrafilter set.univ F.2 (filter.univ_sets _),
    exact false.elim (h ⟨w⟩),
  end }

end Compactum

structure CompHaus :=
(to_Top : Top)
[is_compact : compact_space to_Top . tactic.apply_instance]
[is_hausdorff : t2_space to_Top . tactic.apply_instance]

namespace CompHaus

instance : has_coe_to_sort CompHaus := ⟨Type*,λ X, X.to_Top⟩
instance {X : CompHaus} : compact_space X := X.is_compact
instance {X : CompHaus} : t2_space X := X.is_hausdorff

instance category : large_category CompHaus :=
induced_category.category to_Top

end CompHaus

def Compactum_to_CompHaus : Compactum ⥤ CompHaus :=
{ obj := λ X,
    { to_Top :=
      { α := X } },
    map := λ X Y f,
    { to_fun := f,
      continuous_to_fun := Compactum.continuous_of_morphism _ }}

namespace Compactum_to_CompHaus

def full : full Compactum_to_CompHaus :=
{ preimage := λ X Y f, Compactum.morphism_of_continuous' f.1 f.2 }

def faithful : faithful Compactum_to_CompHaus := {}

def empty_Compactum : Compactum :=
{ A := pempty,
  a := λ F, begin
     exfalso,
     rcases nonempty_of_mem_ultrafilter set.univ F.2 (filter.univ_sets _),
     apply pempty.elim,
     exact w,
  end }

theorem is_open_iff_ultrafilter {X : Type*} [topological_space X] (U : set X) : is_open U ↔
  (∀ (F : ultrafilter X) (x : X), F.1 ≤ nhds x → x ∈ U → U ∈ F.1) :=
begin
  split,
  { intros hU F x h hx,
    rw le_nhds_iff at h,
    specialize h U hx hU,
    assumption },
  { intro h,
    rw ←is_closed_compl_iff,
    suffices : closure Uᶜ ⊆ Uᶜ,
    { have : closure Uᶜ = Uᶜ,
      { ext,
        split,
        apply this,
        intro hx,
        apply subset_closure,
        assumption },
      rw ←this,
      exact is_closed_closure },
    intros x hx,
    rw mem_closure_iff_ultrafilter at hx,
    rcases hx with ⟨F,h1,h2⟩,
    specialize h F x h2,
    by_contradiction,
    have : x ∈ U, rwa ←set.not_not_mem,
    specialize h this,
    rw ultrafilter_iff_compl_mem_iff_not_mem.mp F.2 at h1,
    contradiction },
end

lemma eq_lim_iff {X : Type*} [topological_space X] [compact_space X] [t2_space X] [nonempty X]
  (x : X) (F : ultrafilter X) : Lim F.1 = x ↔ F.1 ≤ nhds x :=
begin
  have claim : F.1 ≤ nhds (Lim F.1),
  { have cpt : compact_space X := by apply_instance,
    cases cpt,
    rw compact_iff_ultrafilter_le_nhds at cpt,
    specialize cpt F.1 F.2,
    apply Lim_spec,
    have : F.1 ≤ principal set.univ,
    { intros S hS,
      simp at hS,
      rw hS,
      apply filter.univ_sets },
    specialize cpt this,
    rcases cpt with ⟨a,ha,h1⟩,
    use a,
    assumption },
  split,
  { intro h,
    rw ←h,
    exact claim },
  { intro h,
    have t2 : t2_space X := by apply_instance,
    rw t2_iff_ultrafilter at t2,
    specialize t2 F.1 F.2 claim h,
    assumption }
end

theorem helper {X : Type*} [topological_space X] [compact_space X] [t2_space X] [nonempty X]
  (U : set X) : is_open U ↔ (∀ F : ultrafilter X, Lim F.1 ∈ U → U ∈ F.1) :=
begin
  split,
  { intros hU F hF,
    have : F.1 ≤ nhds (Lim F.1),
    { rw ←eq_lim_iff },
    rw le_nhds_iff at this,
    apply this,
    assumption' },
  { intros cond,
    rw is_open_iff_ultrafilter,
    intros F x h hx,
    specialize cond F,
    rw ←eq_lim_iff at h,
    rw ←h at hx,
    specialize cond hx,
    assumption },
end

noncomputable def iso_nonempty {D : CompHaus} [nonempty D] :
  Compactum_to_CompHaus.obj (Compactum.of_nonempty_Top D) ≅ D :=
{ hom :=
  { to_fun := id,
    continuous_to_fun := begin
      intros U hU,
      simp,
      rw helper at hU,
      assumption,
    end},
  inv :=
  { to_fun := id,
    continuous_to_fun := begin
      intros U hU,
      change set D at U,
      simp,
      rw helper,
      intros F hF,
      specialize hU F hF,
      assumption,
    end} }

def iso_empty {D : CompHaus} (cond : ¬ nonempty D) :
  Compactum_to_CompHaus.obj empty_Compactum ≅ D :=
{ hom :=
  { to_fun := λ (x : pempty), pempty.elim x,
    continuous_to_fun := begin
      intros U hU,
      have : U = ∅, { apply set.eq_empty_of_not_nonempty, assumption },
      rw this,
      simp,
    end},
  inv :=
  { to_fun := λ x, false.elim $ cond ⟨x⟩,
    continuous_to_fun := begin
      intros U hU,
      have : U = ∅,
      { apply set.eq_empty_of_not_nonempty,
        change ¬nonempty pempty,
        intro c,
        cases c,
        apply pempty.elim,
        exact c },
      rw this,
      simp,
    end},
  inv_hom_id' := begin
    ext,
    exfalso,
    apply cond,
    use x,
  end}

noncomputable def ess_surj : ess_surj Compactum_to_CompHaus :=
{ obj_preimage := λ X, if h : nonempty X then
    by letI := h; exact Compactum.of_nonempty_Top X else
    empty_Compactum,
  iso' := begin
    intros D,
    simp,
    split_ifs,
    letI := h,
    exact iso_nonempty,
    apply iso_empty,
    assumption,
  end}

end Compactum_to_CompHaus

noncomputable def Compactum_CompHaus_equiv : is_equivalence Compactum_to_CompHaus :=
begin
  have I1 : full Compactum_to_CompHaus := Compactum_to_CompHaus.full,
  have I2 : faithful Compactum_to_CompHaus := Compactum_to_CompHaus.faithful,
  have I3 : ess_surj Compactum_to_CompHaus := Compactum_to_CompHaus.ess_surj,
  apply equivalence.equivalence_of_fully_faithfully_ess_surj _,
  assumption',
end
