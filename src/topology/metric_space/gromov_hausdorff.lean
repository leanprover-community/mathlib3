/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.closeds
import set_theory.cardinal
import topology.metric_space.gromov_hausdorff_realized
import topology.metric_space.completion
import topology.metric_space.kuratowski

/-!
# Gromov-Hausdorff distance

This file defines the Gromov-Hausdorff distance on the space of nonempty compact metric spaces
up to isometry.

We introduce the space of all nonempty compact metric spaces, up to isometry,
called `GH_space`, and endow it with a metric space structure. The distance,
known as the Gromov-Hausdorff distance, is defined as follows: given two
nonempty compact spaces `X` and `Y`, their distance is the minimum Hausdorff distance
between all possible isometric embeddings of `X` and `Y` in all metric spaces.
To define properly the Gromov-Hausdorff space, we consider the non-empty
compact subsets of `ℓ^∞(ℝ)` up to isometry, which is a well-defined type,
and define the distance as the infimum of the Hausdorff distance over all
embeddings in `ℓ^∞(ℝ)`. We prove that this coincides with the previous description,
as all separable metric spaces embed isometrically into `ℓ^∞(ℝ)`, through an
embedding called the Kuratowski embedding.
To prove that we have a distance, we should show that if spaces can be coupled
to be arbitrarily close, then they are isometric. More generally, the Gromov-Hausdorff
distance is realized, i.e., there is a coupling for which the Hausdorff distance
is exactly the Gromov-Hausdorff distance. This follows from a compactness
argument, essentially following from Arzela-Ascoli.

## Main results

We prove the most important properties of the Gromov-Hausdorff space: it is a polish space,
i.e., it is complete and second countable. We also prove the Gromov compactness criterion.

-/

noncomputable theory
open_locale classical topological_space
universes u v w

open classical set function topological_space filter metric quotient
open bounded_continuous_function nat Kuratowski_embedding
open sum (inl inr)

local attribute [instance] metric_space_sum


namespace Gromov_Hausdorff

section GH_space
/- In this section, we define the Gromov-Hausdorff space, denoted `GH_space` as the quotient
of nonempty compact subsets of `ℓ^∞(ℝ)` by identifying isometric sets.
Using the Kuratwoski embedding, we get a canonical map `to_GH_space` mapping any nonempty
compact type to `GH_space`. -/

/-- Equivalence relation identifying two nonempty compact sets which are isometric -/
private definition isometry_rel :
  nonempty_compacts ℓ_infty_ℝ → nonempty_compacts ℓ_infty_ℝ → Prop :=
  λ x y, nonempty (x.val ≃ᵢ y.val)

/-- This is indeed an equivalence relation -/
private lemma is_equivalence_isometry_rel : equivalence isometry_rel :=
⟨λ x, ⟨isometric.refl _⟩, λ x y ⟨e⟩, ⟨e.symm⟩, λ x y z ⟨e⟩ ⟨f⟩, ⟨e.trans f⟩⟩

/-- setoid instance identifying two isometric nonempty compact subspaces of ℓ^∞(ℝ) -/
instance isometry_rel.setoid : setoid (nonempty_compacts ℓ_infty_ℝ) :=
setoid.mk isometry_rel is_equivalence_isometry_rel

/-- The Gromov-Hausdorff space -/
definition GH_space : Type := quotient (isometry_rel.setoid)

/-- Map any nonempty compact type to `GH_space` -/
definition to_GH_space (X : Type u) [metric_space X] [compact_space X] [nonempty X] : GH_space :=
  ⟦nonempty_compacts.Kuratowski_embedding X⟧

instance : inhabited GH_space := ⟨quot.mk _ ⟨{0}, by simp⟩⟩

/-- A metric space representative of any abstract point in `GH_space` -/
@[nolint has_inhabited_instance]
definition GH_space.rep (p : GH_space) : Type := (quot.out p).val

lemma eq_to_GH_space_iff {X : Type u} [metric_space X] [compact_space X] [nonempty X]
  {p : nonempty_compacts ℓ_infty_ℝ} :
  ⟦p⟧ = to_GH_space X ↔ ∃ Ψ : X → ℓ_infty_ℝ, isometry Ψ ∧ range Ψ = p.val :=
begin
  simp only [to_GH_space, quotient.eq],
  split,
  { assume h,
    rcases setoid.symm h with ⟨e⟩,
    have f := (Kuratowski_embedding.isometry X).isometric_on_range.trans e,
    use λ x, f x,
    split,
    { apply isometry_subtype_coe.comp f.isometry },
    { rw [range_comp, f.range_eq_univ, set.image_univ, subtype.range_coe] } },
  { rintros ⟨Ψ, ⟨isomΨ, rangeΨ⟩⟩,
    have f := ((Kuratowski_embedding.isometry X).isometric_on_range.symm.trans
               isomΨ.isometric_on_range).symm,
    have E : (range Ψ ≃ᵢ (nonempty_compacts.Kuratowski_embedding X).val) =
        (p.val ≃ᵢ range (Kuratowski_embedding X)),
      by { dunfold nonempty_compacts.Kuratowski_embedding, rw [rangeΨ]; refl },
    have g := cast E f,
    exact ⟨g⟩ }
end

lemma eq_to_GH_space {p : nonempty_compacts ℓ_infty_ℝ} : ⟦p⟧ = to_GH_space p.val :=
begin
 refine eq_to_GH_space_iff.2 ⟨((λ x, x) : p.val → ℓ_infty_ℝ), _, subtype.range_coe⟩,
 apply isometry_subtype_coe
end

section
local attribute [reducible] GH_space.rep

instance rep_GH_space_metric_space {p : GH_space} : metric_space (p.rep) :=
by apply_instance

instance rep_GH_space_compact_space {p : GH_space} : compact_space (p.rep) :=
by apply_instance

instance rep_GH_space_nonempty {p : GH_space} : nonempty (p.rep) :=
by apply_instance
end

lemma GH_space.to_GH_space_rep (p : GH_space) : to_GH_space (p.rep) = p :=
begin
  change to_GH_space (quot.out p).val = p,
  rw ← eq_to_GH_space,
  exact quot.out_eq p
end

/-- Two nonempty compact spaces have the same image in `GH_space` if and only if they are
isometric. -/
lemma to_GH_space_eq_to_GH_space_iff_isometric {X : Type u} [metric_space X] [compact_space X]
  [nonempty X] {Y : Type v} [metric_space Y] [compact_space Y] [nonempty Y] :
  to_GH_space X = to_GH_space Y ↔ nonempty (X ≃ᵢ Y) :=
⟨begin
  simp only [to_GH_space, quotient.eq],
  assume h,
  rcases h with ⟨e⟩,
  have I : ((nonempty_compacts.Kuratowski_embedding X).val ≃ᵢ
             (nonempty_compacts.Kuratowski_embedding Y).val)
          = ((range (Kuratowski_embedding X)) ≃ᵢ (range (Kuratowski_embedding Y))),
    by { dunfold nonempty_compacts.Kuratowski_embedding, refl },
  have e' := cast I e,
  have f := (Kuratowski_embedding.isometry X).isometric_on_range,
  have g := (Kuratowski_embedding.isometry Y).isometric_on_range.symm,
  have h := (f.trans e').trans g,
  exact ⟨h⟩
end,
begin
  rintros ⟨e⟩,
  simp only [to_GH_space, quotient.eq],
  have f := (Kuratowski_embedding.isometry X).isometric_on_range.symm,
  have g := (Kuratowski_embedding.isometry Y).isometric_on_range,
  have h := (f.trans e).trans g,
  have I : ((range (Kuratowski_embedding X)) ≃ᵢ (range (Kuratowski_embedding Y))) =
    ((nonempty_compacts.Kuratowski_embedding X).val ≃ᵢ
      (nonempty_compacts.Kuratowski_embedding Y).val),
    by { dunfold nonempty_compacts.Kuratowski_embedding, refl },
  have h' := cast I h,
  exact ⟨h'⟩
end⟩

/-- Distance on `GH_space`: the distance between two nonempty compact spaces is the infimum
Hausdorff distance between isometric copies of the two spaces in a metric space. For the definition,
we only consider embeddings in `ℓ^∞(ℝ)`, but we will prove below that it works for all spaces. -/
instance : has_dist (GH_space) :=
{ dist := λ x y, Inf $
    (λ p : nonempty_compacts ℓ_infty_ℝ × nonempty_compacts ℓ_infty_ℝ,
      Hausdorff_dist p.1.val p.2.val) '' (set.prod {a | ⟦a⟧ = x} {b | ⟦b⟧ = y}) }

/-- The Gromov-Hausdorff distance between two nonempty compact metric spaces, equal by definition to
the distance of the equivalence classes of these spaces in the Gromov-Hausdorff space. -/
def GH_dist (X : Type u) (Y : Type v) [metric_space X] [nonempty X] [compact_space X]
  [metric_space Y] [nonempty Y] [compact_space Y] : ℝ := dist (to_GH_space X) (to_GH_space Y)

lemma dist_GH_dist (p q : GH_space) : dist p q = GH_dist (p.rep) (q.rep) :=
by rw [GH_dist, p.to_GH_space_rep, q.to_GH_space_rep]

/-- The Gromov-Hausdorff distance between two spaces is bounded by the Hausdorff distance
of isometric copies of the spaces, in any metric space. -/
theorem GH_dist_le_Hausdorff_dist {X : Type u} [metric_space X] [compact_space X] [nonempty X]
  {Y : Type v} [metric_space Y] [compact_space Y] [nonempty Y]
  {γ : Type w} [metric_space γ] {Φ : X → γ} {Ψ : Y → γ} (ha : isometry Φ) (hb : isometry Ψ) :
  GH_dist X Y ≤ Hausdorff_dist (range Φ) (range Ψ) :=
begin
  /- For the proof, we want to embed `γ` in `ℓ^∞(ℝ)`, to say that the Hausdorff distance is realized
  in `ℓ^∞(ℝ)` and therefore bounded below by the Gromov-Hausdorff-distance. However, `γ` is not
  separable in general. We restrict to the union of the images of `X` and `Y` in `γ`, which is
  separable and therefore embeddable in `ℓ^∞(ℝ)`. -/
  rcases exists_mem_of_nonempty X with ⟨xX, _⟩,
  let s : set γ := (range Φ) ∪ (range Ψ),
  let Φ' : X → subtype s := λ y, ⟨Φ y, mem_union_left _ (mem_range_self _)⟩,
  let Ψ' : Y → subtype s := λ y, ⟨Ψ y, mem_union_right _ (mem_range_self _)⟩,
  have IΦ' : isometry Φ' := λ x y, ha x y,
  have IΨ' : isometry Ψ' := λ x y, hb x y,
  have : is_compact s, from (is_compact_range ha.continuous).union (is_compact_range hb.continuous),
  letI : metric_space (subtype s) := by apply_instance,
  haveI : compact_space (subtype s) := ⟨is_compact_iff_is_compact_univ.1 ‹is_compact s›⟩,
  haveI : nonempty (subtype s) := ⟨Φ' xX⟩,
  have ΦΦ' : Φ = subtype.val ∘ Φ', by { funext, refl },
  have ΨΨ' : Ψ = subtype.val ∘ Ψ', by { funext, refl },
  have : Hausdorff_dist (range Φ) (range Ψ) = Hausdorff_dist (range Φ') (range Ψ'),
  { rw [ΦΦ', ΨΨ', range_comp, range_comp],
    exact Hausdorff_dist_image (isometry_subtype_coe) },
  rw this,
  -- Embed `s` in `ℓ^∞(ℝ)` through its Kuratowski embedding
  let F := Kuratowski_embedding (subtype s),
  have : Hausdorff_dist (F '' (range Φ')) (F '' (range Ψ')) =
    Hausdorff_dist (range Φ') (range Ψ') := Hausdorff_dist_image (Kuratowski_embedding.isometry _),
  rw ← this,
  -- Let `A` and `B` be the images of `X` and `Y` under this embedding. They are in `ℓ^∞(ℝ)`, and
  -- their Hausdorff distance is the same as in the original space.
  let A : nonempty_compacts ℓ_infty_ℝ := ⟨F '' (range Φ'), ⟨(range_nonempty _).image _,
      (is_compact_range IΦ'.continuous).image (Kuratowski_embedding.isometry _).continuous⟩⟩,
  let B : nonempty_compacts ℓ_infty_ℝ := ⟨F '' (range Ψ'), ⟨(range_nonempty _).image _,
      (is_compact_range IΨ'.continuous).image (Kuratowski_embedding.isometry _).continuous⟩⟩,
  have AX : ⟦A⟧ = to_GH_space X,
  { rw eq_to_GH_space_iff,
    exact ⟨λ x, F (Φ' x), ⟨(Kuratowski_embedding.isometry _).comp IΦ', by rw range_comp⟩⟩ },
  have BY : ⟦B⟧ = to_GH_space Y,
  { rw eq_to_GH_space_iff,
    exact ⟨λ x, F (Ψ' x), ⟨(Kuratowski_embedding.isometry _).comp IΨ', by rw range_comp⟩⟩ },
  refine cInf_le ⟨0,
    begin simp [lower_bounds], assume t _ _ _ _ ht, rw ← ht, exact Hausdorff_dist_nonneg end⟩ _,
  apply (mem_image _ _ _).2,
  existsi (⟨A, B⟩ : nonempty_compacts ℓ_infty_ℝ × nonempty_compacts ℓ_infty_ℝ),
  simp [AX, BY]
end

/-- The optimal coupling constructed above realizes exactly the Gromov-Hausdorff distance,
essentially by design. -/
lemma Hausdorff_dist_optimal {X : Type u} [metric_space X] [compact_space X] [nonempty X]
  {Y : Type v} [metric_space Y] [compact_space Y] [nonempty Y] :
  Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)) = GH_dist X Y :=
begin
  inhabit X, inhabit Y,
  /- we only need to check the inequality `≤`, as the other one follows from the previous lemma.
     As the Gromov-Hausdorff distance is an infimum, we need to check that the Hausdorff distance
     in the optimal coupling is smaller than the Hausdorff distance of any coupling.
     First, we check this for couplings which already have small Hausdorff distance: in this
     case, the induced "distance" on `X ⊕ Y` belongs to the candidates family introduced in the
     definition of the optimal coupling, and the conclusion follows from the optimality
     of the optimal coupling within this family.
  -/
  have A : ∀ p q : nonempty_compacts (ℓ_infty_ℝ), ⟦p⟧ = to_GH_space X → ⟦q⟧ = to_GH_space Y →
        Hausdorff_dist (p.val) (q.val) < diam (univ : set X) + 1 + diam (univ : set Y) →
        Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)) ≤
        Hausdorff_dist (p.val) (q.val),
  { assume p q hp hq bound,
    rcases eq_to_GH_space_iff.1 hp with ⟨Φ, ⟨Φisom, Φrange⟩⟩,
    rcases eq_to_GH_space_iff.1 hq with ⟨Ψ, ⟨Ψisom, Ψrange⟩⟩,
    have I : diam (range Φ ∪ range Ψ) ≤ 2 * diam (univ : set X) + 1 + 2 * diam (univ : set Y),
    { rcases exists_mem_of_nonempty X with ⟨xX, _⟩,
      have : ∃ y ∈ range Ψ, dist (Φ xX) y < diam (univ : set X) + 1 + diam (univ : set Y),
      { rw Ψrange,
        have : Φ xX ∈ p.val := Φrange ▸ mem_range_self _,
        exact exists_dist_lt_of_Hausdorff_dist_lt this bound
          (Hausdorff_edist_ne_top_of_nonempty_of_bounded p.2.1 q.2.1 p.2.2.bounded q.2.2.bounded) },
      rcases this with ⟨y, hy, dy⟩,
      rcases mem_range.1 hy with ⟨z, hzy⟩,
      rw ← hzy at dy,
      have DΦ : diam (range Φ) = diam (univ : set X) := Φisom.diam_range,
      have DΨ : diam (range Ψ) = diam (univ : set Y) := Ψisom.diam_range,
      calc
        diam (range Φ ∪ range Ψ) ≤ diam (range Φ) + dist (Φ xX) (Ψ z) + diam (range Ψ) :
          diam_union (mem_range_self _) (mem_range_self _)
        ... ≤ diam (univ : set X) + (diam (univ : set X) + 1 + diam (univ : set Y)) +
              diam (univ : set Y) :
          by { rw [DΦ, DΨ], apply add_le_add (add_le_add (le_refl _) (le_of_lt dy)) (le_refl _) }
        ... = 2 * diam (univ : set X) + 1 + 2 * diam (univ : set Y) : by ring },

    let f : X ⊕ Y → ℓ_infty_ℝ := λ x, match x with | inl y := Φ y | inr z := Ψ z end,
    let F : (X ⊕ Y) × (X ⊕ Y) → ℝ := λ p, dist (f p.1) (f p.2),
    -- check that the induced "distance" is a candidate
    have Fgood : F ∈ candidates X Y,
    { simp only [candidates, forall_const, and_true, add_comm, eq_self_iff_true, dist_eq_zero,
                 and_self, set.mem_set_of_eq],
      repeat {split},
      { exact λ x y, calc
        F (inl x, inl y) = dist (Φ x) (Φ y) : rfl
        ... = dist x y : Φisom.dist_eq x y },
      { exact λ x y, calc
        F (inr x, inr y) = dist (Ψ x) (Ψ y) : rfl
        ... = dist x y : Ψisom.dist_eq x y },
      { exact λ x y, dist_comm _ _ },
      { exact λ x y z, dist_triangle _ _ _ },
      { exact λ x y, calc
        F (x, y) ≤ diam (range Φ ∪ range Ψ) :
        begin
          have A : ∀ z : X ⊕ Y, f z ∈ range Φ ∪ range Ψ,
          { assume z,
            cases z,
            { apply mem_union_left, apply mem_range_self },
            { apply mem_union_right, apply mem_range_self } },
          refine dist_le_diam_of_mem _ (A _) (A _),
          rw [Φrange, Ψrange],
          exact (p.2.2.union q.2.2).bounded,
        end
        ... ≤ 2 * diam (univ : set X) + 1 + 2 * diam (univ : set Y) : I } },
    let Fb := candidates_b_of_candidates F Fgood,
    have : Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)) ≤ HD Fb :=
      Hausdorff_dist_optimal_le_HD _ _ (candidates_b_of_candidates_mem F Fgood),
    refine le_trans this (le_of_forall_le_of_dense (λ r hr, _)),
    have I1 : ∀ x : X, (⨅ y, Fb (inl x, inr y)) ≤ r,
    { assume x,
      have : f (inl x) ∈ p.val, by { rw [← Φrange], apply mem_range_self },
      rcases exists_dist_lt_of_Hausdorff_dist_lt this hr
        (Hausdorff_edist_ne_top_of_nonempty_of_bounded p.2.1 q.2.1 p.2.2.bounded q.2.2.bounded)
        with ⟨z, zq, hz⟩,
      have : z ∈ range Ψ, by rwa [← Ψrange] at zq,
      rcases mem_range.1 this with ⟨y, hy⟩,
      calc (⨅ y, Fb (inl x, inr y)) ≤ Fb (inl x, inr y) :
          cinfi_le (by simpa using HD_below_aux1 0) y
        ... = dist (Φ x) (Ψ y) : rfl
        ... = dist (f (inl x)) z : by rw hy
        ... ≤ r : le_of_lt hz },
    have I2 : ∀ y : Y, (⨅ x, Fb (inl x, inr y)) ≤ r,
    { assume y,
      have : f (inr y) ∈ q.val, by { rw [← Ψrange], apply mem_range_self },
      rcases exists_dist_lt_of_Hausdorff_dist_lt' this hr
        (Hausdorff_edist_ne_top_of_nonempty_of_bounded p.2.1 q.2.1 p.2.2.bounded q.2.2.bounded)
        with ⟨z, zq, hz⟩,
      have : z ∈ range Φ, by rwa [← Φrange] at zq,
      rcases mem_range.1 this with ⟨x, hx⟩,
      calc (⨅ x, Fb (inl x, inr y)) ≤ Fb (inl x, inr y) :
          cinfi_le (by simpa using HD_below_aux2 0) x
        ... = dist (Φ x) (Ψ y) : rfl
        ... = dist z (f (inr y)) : by rw hx
        ... ≤ r : le_of_lt hz },
    simp [HD, csupr_le I1, csupr_le I2] },
  /- Get the same inequality for any coupling. If the coupling is quite good, the desired
  inequality has been proved above. If it is bad, then the inequality is obvious. -/
  have B : ∀ p q : nonempty_compacts (ℓ_infty_ℝ), ⟦p⟧ = to_GH_space X → ⟦q⟧ = to_GH_space Y →
        Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)) ≤
        Hausdorff_dist (p.val) (q.val),
  { assume p q hp hq,
    by_cases h : Hausdorff_dist (p.val) (q.val) < diam (univ : set X) + 1 + diam (univ : set Y),
    { exact A p q hp hq h },
    { calc Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y))
               ≤ HD (candidates_b_dist X Y) :
             Hausdorff_dist_optimal_le_HD _ _ (candidates_b_dist_mem_candidates_b)
           ... ≤ diam (univ : set X) + 1 + diam (univ : set Y) : HD_candidates_b_dist_le
           ... ≤ Hausdorff_dist (p.val) (q.val) : not_lt.1 h } },
  refine le_antisymm _ _,
  { apply le_cInf,
    { refine (set.nonempty.prod _ _).image _; exact ⟨_, rfl⟩ },
    { rintro b ⟨⟨p, q⟩, ⟨hp, hq⟩, rfl⟩,
      exact B p q hp hq } },
  { exact GH_dist_le_Hausdorff_dist (isometry_optimal_GH_injl X Y) (isometry_optimal_GH_injr X Y) }
end

/-- The Gromov-Hausdorff distance can also be realized by a coupling in `ℓ^∞(ℝ)`, by embedding
the optimal coupling through its Kuratowski embedding. -/
theorem GH_dist_eq_Hausdorff_dist (X : Type u) [metric_space X] [compact_space X] [nonempty X]
  (Y : Type v) [metric_space Y] [compact_space Y] [nonempty Y] :
  ∃ Φ : X → ℓ_infty_ℝ, ∃ Ψ : Y → ℓ_infty_ℝ, isometry Φ ∧ isometry Ψ ∧
  GH_dist X Y = Hausdorff_dist (range Φ) (range Ψ) :=
begin
  let F := Kuratowski_embedding (optimal_GH_coupling X Y),
  let Φ := F ∘ optimal_GH_injl X Y,
  let Ψ := F ∘ optimal_GH_injr X Y,
  refine ⟨Φ, Ψ, _, _, _⟩,
  { exact (Kuratowski_embedding.isometry _).comp (isometry_optimal_GH_injl X Y) },
  { exact (Kuratowski_embedding.isometry _).comp (isometry_optimal_GH_injr X Y) },
  { rw [← image_univ, ← image_univ, image_comp F, image_univ, image_comp F (optimal_GH_injr X Y),
      image_univ, ← Hausdorff_dist_optimal],
    exact (Hausdorff_dist_image (Kuratowski_embedding.isometry _)).symm },
end

/-- The Gromov-Hausdorff distance defines a genuine distance on the Gromov-Hausdorff space. -/
instance : metric_space GH_space :=
{ dist_self := λ x, begin
    rcases exists_rep x with ⟨y, hy⟩,
    refine le_antisymm _ _,
    { apply cInf_le,
      { exact ⟨0, by { rintro b ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩, exact Hausdorff_dist_nonneg } ⟩},
      { simp, existsi [y, y], simpa } },
    { apply le_cInf,
      { exact (nonempty.prod ⟨y, hy⟩ ⟨y, hy⟩).image _ },
      { rintro b ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩, exact Hausdorff_dist_nonneg } },
  end,
  dist_comm := λ x y, begin
    have A : (λ (p : nonempty_compacts ℓ_infty_ℝ × nonempty_compacts ℓ_infty_ℝ),
                 Hausdorff_dist ((p.fst).val) ((p.snd).val)) ''
             (set.prod {a | ⟦a⟧ = x} {b | ⟦b⟧ = y})
           = ((λ (p : nonempty_compacts ℓ_infty_ℝ × nonempty_compacts ℓ_infty_ℝ),
                 Hausdorff_dist ((p.fst).val) ((p.snd).val)) ∘ prod.swap) ''
                 (set.prod {a | ⟦a⟧ = x} {b | ⟦b⟧ = y}) :=
      by { congr, funext, simp, rw Hausdorff_dist_comm },
    simp only [dist, A, image_comp, image_swap_prod],
  end,
  eq_of_dist_eq_zero := λ x y hxy, begin
    /- To show that two spaces at zero distance are isometric, we argue that the distance
    is realized by some coupling. In this coupling, the two spaces are at zero Hausdorff distance,
    i.e., they coincide. Therefore, the original spaces are isometric. -/
    rcases GH_dist_eq_Hausdorff_dist x.rep y.rep with ⟨Φ, Ψ, Φisom, Ψisom, DΦΨ⟩,
    rw [← dist_GH_dist, hxy] at DΦΨ,
    have : range Φ = range Ψ,
    { have hΦ : is_compact (range Φ) := is_compact_range Φisom.continuous,
      have hΨ : is_compact (range Ψ) := is_compact_range Ψisom.continuous,
      apply (Hausdorff_dist_zero_iff_eq_of_closed _ _ _).1 (DΦΨ.symm),
      { exact hΦ.is_closed },
      { exact hΨ.is_closed },
      { exact Hausdorff_edist_ne_top_of_nonempty_of_bounded (range_nonempty _)
          (range_nonempty _) hΦ.bounded hΨ.bounded } },
    have T : ((range Ψ) ≃ᵢ y.rep) = ((range Φ) ≃ᵢ y.rep), by rw this,
    have eΨ := cast T Ψisom.isometric_on_range.symm,
    have e := Φisom.isometric_on_range.trans eΨ,
    rw [← x.to_GH_space_rep, ← y.to_GH_space_rep, to_GH_space_eq_to_GH_space_iff_isometric],
    exact ⟨e⟩
  end,
  dist_triangle := λ x y z, begin
    /- To show the triangular inequality between `X`, `Y` and `Z`, realize an optimal coupling
    between `X` and `Y` in a space `γ1`, and an optimal coupling between `Y` and `Z` in a space
    `γ2`. Then, glue these metric spaces along `Y`. We get a new space `γ` in which `X` and `Y` are
    optimally coupled, as well as `Y` and `Z`. Apply the triangle inequality for the Hausdorff
    distance in `γ` to conclude. -/
    let X := x.rep,
    let Y := y.rep,
    let Z := z.rep,
    let γ1 := optimal_GH_coupling X Y,
    let γ2 := optimal_GH_coupling Y Z,
    let Φ : Y → γ1 := optimal_GH_injr X Y,
    have hΦ : isometry Φ := isometry_optimal_GH_injr X Y,
    let Ψ : Y → γ2 := optimal_GH_injl Y Z,
    have hΨ : isometry Ψ := isometry_optimal_GH_injl Y Z,
    let γ := glue_space hΦ hΨ,
    letI : metric_space γ := metric.metric_space_glue_space hΦ hΨ,
    have Comm : (to_glue_l hΦ hΨ) ∘ (optimal_GH_injr X Y) =
      (to_glue_r hΦ hΨ) ∘ (optimal_GH_injl Y Z) := to_glue_commute hΦ hΨ,
    calc dist x z = dist (to_GH_space X) (to_GH_space Z) :
        by rw [x.to_GH_space_rep, z.to_GH_space_rep]
      ... ≤ Hausdorff_dist (range ((to_glue_l hΦ hΨ) ∘ (optimal_GH_injl X Y)))
                       (range ((to_glue_r hΦ hΨ) ∘ (optimal_GH_injr Y Z))) :
        GH_dist_le_Hausdorff_dist
          ((to_glue_l_isometry hΦ hΨ).comp (isometry_optimal_GH_injl X Y))
          ((to_glue_r_isometry hΦ hΨ).comp (isometry_optimal_GH_injr Y Z))
      ... ≤ Hausdorff_dist (range ((to_glue_l hΦ hΨ) ∘ (optimal_GH_injl X Y)))
                           (range ((to_glue_l hΦ hΨ) ∘ (optimal_GH_injr X Y)))
          + Hausdorff_dist (range ((to_glue_l hΦ hΨ) ∘ (optimal_GH_injr X Y)))
                           (range ((to_glue_r hΦ hΨ) ∘ (optimal_GH_injr Y Z))) :
        begin
          refine Hausdorff_dist_triangle (Hausdorff_edist_ne_top_of_nonempty_of_bounded
            (range_nonempty _) (range_nonempty _) _ _),
          { exact (is_compact_range (isometry.continuous ((to_glue_l_isometry hΦ hΨ).comp
              (isometry_optimal_GH_injl X Y)))).bounded },
          { exact (is_compact_range (isometry.continuous ((to_glue_l_isometry hΦ hΨ).comp
              (isometry_optimal_GH_injr X Y)))).bounded }
        end
      ... = Hausdorff_dist ((to_glue_l hΦ hΨ) '' (range (optimal_GH_injl X Y)))
                           ((to_glue_l hΦ hΨ) '' (range (optimal_GH_injr X Y)))
          + Hausdorff_dist ((to_glue_r hΦ hΨ) '' (range (optimal_GH_injl Y Z)))
                           ((to_glue_r hΦ hΨ) '' (range (optimal_GH_injr Y Z))) :
        by simp only [← range_comp, Comm, eq_self_iff_true, add_right_inj]
      ... = Hausdorff_dist (range (optimal_GH_injl X Y))
                           (range (optimal_GH_injr X Y))
          + Hausdorff_dist (range (optimal_GH_injl Y Z))
                           (range (optimal_GH_injr Y Z)) :
        by rw [Hausdorff_dist_image (to_glue_l_isometry hΦ hΨ),
               Hausdorff_dist_image (to_glue_r_isometry hΦ hΨ)]
      ... = dist (to_GH_space X) (to_GH_space Y) + dist (to_GH_space Y) (to_GH_space Z) :
        by rw [Hausdorff_dist_optimal, Hausdorff_dist_optimal, GH_dist, GH_dist]
      ... = dist x y + dist y z:
        by rw [x.to_GH_space_rep, y.to_GH_space_rep, z.to_GH_space_rep]
  end }

end GH_space --section
end Gromov_Hausdorff

/-- In particular, nonempty compacts of a metric space map to `GH_space`. We register this
in the topological_space namespace to take advantage of the notation `p.to_GH_space`. -/
definition topological_space.nonempty_compacts.to_GH_space {X : Type u} [metric_space X]
  (p : nonempty_compacts X) : Gromov_Hausdorff.GH_space := Gromov_Hausdorff.to_GH_space p.val

open topological_space

namespace Gromov_Hausdorff

section nonempty_compacts
variables {X : Type u} [metric_space X]

theorem GH_dist_le_nonempty_compacts_dist (p q : nonempty_compacts X) :
  dist p.to_GH_space q.to_GH_space ≤ dist p q :=
begin
  have ha : isometry (coe : p.val → X) := isometry_subtype_coe,
  have hb : isometry (coe : q.val → X) := isometry_subtype_coe,
  have A : dist p q = Hausdorff_dist p.val q.val := rfl,
  have I : p.val = range (coe : p.val → X), by simp,
  have J : q.val = range (coe : q.val → X), by simp,
  rw [I, J] at A,
  rw A,
  exact GH_dist_le_Hausdorff_dist ha hb
end

lemma to_GH_space_lipschitz :
  lipschitz_with 1 (nonempty_compacts.to_GH_space : nonempty_compacts X → GH_space) :=
lipschitz_with.mk_one GH_dist_le_nonempty_compacts_dist

lemma to_GH_space_continuous :
  continuous (nonempty_compacts.to_GH_space : nonempty_compacts X → GH_space) :=
to_GH_space_lipschitz.continuous

end nonempty_compacts

section
/- In this section, we show that if two metric spaces are isometric up to `ε₂`, then their
Gromov-Hausdorff distance is bounded by `ε₂ / 2`. More generally, if there are subsets which are
`ε₁`-dense and `ε₃`-dense in two spaces, and isometric up to `ε₂`, then the Gromov-Hausdorff
distance between the spaces is bounded by `ε₁ + ε₂/2 + ε₃`. For this, we construct a suitable
coupling between the two spaces, by gluing them (approximately) along the two matching subsets. -/


variables {X : Type u} [metric_space X] [compact_space X] [nonempty X]
          {Y : Type v} [metric_space Y] [compact_space Y] [nonempty Y]

-- we want to ignore these instances in the following theorem
local attribute [instance, priority 10] sum.topological_space sum.uniform_space
/-- If there are subsets which are `ε₁`-dense and `ε₃`-dense in two spaces, and
isometric up to `ε₂`, then the Gromov-Hausdorff distance between the spaces is bounded by
`ε₁ + ε₂/2 + ε₃`. -/
theorem GH_dist_le_of_approx_subsets {s : set X} (Φ : s → Y) {ε₁ ε₂ ε₃ : ℝ}
  (hs : ∀ x : X, ∃ y ∈ s, dist x y ≤ ε₁) (hs' : ∀ x : Y, ∃ y : s, dist x (Φ y) ≤ ε₃)
  (H : ∀ x y : s, abs (dist x y - dist (Φ x) (Φ y)) ≤ ε₂) :
  GH_dist X Y ≤ ε₁ + ε₂ / 2 + ε₃ :=
begin
  refine le_of_forall_pos_le_add (λ δ δ0, _),
  rcases exists_mem_of_nonempty X with ⟨xX, _⟩,
  rcases hs xX with ⟨xs, hxs, Dxs⟩,
  have sne : s.nonempty := ⟨xs, hxs⟩,
  letI : nonempty s := sne.to_subtype,
  have : 0 ≤ ε₂ := le_trans (abs_nonneg _) (H ⟨xs, hxs⟩ ⟨xs, hxs⟩),
  have : ∀ p q : s, abs (dist p q - dist (Φ p) (Φ q)) ≤ 2 * (ε₂/2 + δ) := λ p q, calc
    abs (dist p q - dist (Φ p) (Φ q)) ≤ ε₂ : H p q
    ... ≤ 2 * (ε₂/2 + δ) : by linarith,
  -- glue `X` and `Y` along the almost matching subsets
  letI : metric_space (X ⊕ Y) :=
    glue_metric_approx (λ x:s, (x:X)) (λ x, Φ x) (ε₂/2 + δ) (by linarith) this,
  let Fl := @sum.inl X Y,
  let Fr := @sum.inr X Y,
  have Il : isometry Fl := isometry_emetric_iff_metric.2 (λ x y, rfl),
  have Ir : isometry Fr := isometry_emetric_iff_metric.2 (λ x y, rfl),
  /- The proof goes as follows : the `GH_dist` is bounded by the Hausdorff distance of the images
  in the coupling, which is bounded (using the triangular inequality) by the sum of the Hausdorff
  distances of `X` and `s` (in the coupling or, equivalently in the original space), of `s` and
  `Φ s`, and of `Φ s` and `Y` (in the coupling or, equivalently, in the original space). The first
  term is bounded by `ε₁`, by `ε₁`-density. The third one is bounded by `ε₃`. And the middle one is
  bounded by `ε₂/2` as in the coupling the points `x` and `Φ x` are at distance `ε₂/2` by
  construction of the coupling (in fact `ε₂/2 + δ` where `δ` is an arbitrarily small positive
  constant where positivity is used to ensure that the coupling is really a metric space and not a
  premetric space on `X ⊕ Y`). -/
  have : GH_dist X Y ≤ Hausdorff_dist (range Fl) (range Fr) :=
    GH_dist_le_Hausdorff_dist Il Ir,
  have : Hausdorff_dist (range Fl) (range Fr) ≤ Hausdorff_dist (range Fl) (Fl '' s)
                                              + Hausdorff_dist (Fl '' s) (range Fr),
  { have B : bounded (range Fl) := (is_compact_range Il.continuous).bounded,
    exact Hausdorff_dist_triangle (Hausdorff_edist_ne_top_of_nonempty_of_bounded
      (range_nonempty _) (sne.image _) B (B.subset (image_subset_range _ _))) },
  have : Hausdorff_dist (Fl '' s) (range Fr) ≤ Hausdorff_dist (Fl '' s) (Fr '' (range Φ))
                                             + Hausdorff_dist (Fr '' (range Φ)) (range Fr),
  { have B : bounded (range Fr) := (is_compact_range Ir.continuous).bounded,
    exact Hausdorff_dist_triangle' (Hausdorff_edist_ne_top_of_nonempty_of_bounded
      ((range_nonempty _).image _) (range_nonempty _)
      (bounded.subset (image_subset_range _ _) B) B) },
  have : Hausdorff_dist (range Fl) (Fl '' s) ≤ ε₁,
  { rw [← image_univ, Hausdorff_dist_image Il],
    have : 0 ≤ ε₁ := le_trans dist_nonneg Dxs,
    refine Hausdorff_dist_le_of_mem_dist this (λ x hx, hs x)
      (λ x hx, ⟨x, mem_univ _, by simpa⟩) },
  have : Hausdorff_dist (Fl '' s) (Fr '' (range Φ)) ≤ ε₂/2 + δ,
  { refine Hausdorff_dist_le_of_mem_dist (by linarith) _ _,
    { assume x' hx',
      rcases (set.mem_image _ _ _).1 hx' with ⟨x, ⟨x_in_s, xx'⟩⟩,
      rw ← xx',
      use [Fr (Φ ⟨x, x_in_s⟩), mem_image_of_mem Fr (mem_range_self _)],
      exact le_of_eq (glue_dist_glued_points (λ x:s, (x:X)) Φ (ε₂/2 + δ) ⟨x, x_in_s⟩) },
    { assume x' hx',
      rcases (set.mem_image _ _ _).1 hx' with ⟨y, ⟨y_in_s', yx'⟩⟩,
      rcases mem_range.1 y_in_s' with ⟨x, xy⟩,
      use [Fl x, mem_image_of_mem _ x.2],
      rw [← yx', ← xy, dist_comm],
      exact le_of_eq (glue_dist_glued_points (@subtype.val X s) Φ (ε₂/2 + δ) x) } },
  have : Hausdorff_dist (Fr '' (range Φ)) (range Fr) ≤ ε₃,
  { rw [← @image_univ _ _ Fr, Hausdorff_dist_image Ir],
    rcases exists_mem_of_nonempty Y with ⟨xY, _⟩,
    rcases hs' xY with ⟨xs', Dxs'⟩,
    have : 0 ≤ ε₃ := le_trans dist_nonneg Dxs',
    refine Hausdorff_dist_le_of_mem_dist this (λ x hx, ⟨x, mem_univ _, by simpa⟩) (λ x _, _),
    rcases hs' x with ⟨y, Dy⟩,
    exact ⟨Φ y, mem_range_self _, Dy⟩ },
  linarith
end
end --section

/-- The Gromov-Hausdorff space is second countable. -/
instance : second_countable_topology GH_space :=
begin
  refine second_countable_of_countable_discretization (λ δ δpos, _),
  let ε := (2/5) * δ,
  have εpos : 0 < ε := mul_pos (by norm_num) δpos,
  have : ∀ p:GH_space, ∃ s : set (p.rep), finite s ∧ (univ ⊆ (⋃x∈s, ball x ε)) :=
    λ p, by simpa using finite_cover_balls_of_compact (@compact_univ p.rep _ _) εpos,
  -- for each `p`, `s p` is a finite `ε`-dense subset of `p` (or rather the metric space
  -- `p.rep` representing `p`)
  choose s hs using this,
  have : ∀ p:GH_space, ∀ t:set (p.rep), finite t → ∃ n:ℕ, ∃ e:equiv t (fin n), true,
  { assume p t ht,
    letI : fintype t := finite.fintype ht,
    exact ⟨fintype.card t, fintype.equiv_fin t, trivial⟩ },
  choose N e hne using this,
  -- cardinality of the nice finite subset `s p` of `p.rep`, called `N p`
  let N := λ p:GH_space, N p (s p) (hs p).1,
  -- equiv from `s p`, a nice finite subset of `p.rep`, to `fin (N p)`, called `E p`
  let E := λ p:GH_space, e p (s p) (hs p).1,
  -- A function `F` associating to `p : GH_space` the data of all distances between points
  -- in the `ε`-dense set `s p`.
  let F : GH_space → Σn:ℕ, (fin n → fin n → ℤ) :=
    λ p, ⟨N p, λ a b, floor (ε⁻¹ * dist ((E p).symm a) ((E p).symm b))⟩,
  refine ⟨_, by apply_instance, F, λ p q hpq, _⟩,
  /- As the target space of F is countable, it suffices to show that two points
  `p` and `q` with `F p = F q` are at distance `≤ δ`.
  For this, we construct a map `Φ` from `s p ⊆ p.rep` (representing `p`)
  to `q.rep` (representing `q`) which is almost an isometry on `s p`, and
  with image `s q`. For this, we compose the identification of `s p` with `fin (N p)`
  and the inverse of the identification of `s q` with `fin (N q)`. Together with
  the fact that `N p = N q`, this constructs `Ψ` between `s p` and `s q`, and then
  composing with the canonical inclusion we get `Φ`. -/
  have Npq : N p = N q := (sigma.mk.inj_iff.1 hpq).1,
  let Ψ : s p → s q := λ x, (E q).symm (fin.cast Npq ((E p) x)),
  let Φ : s p → q.rep := λ x, Ψ x,
  -- Use the almost isometry `Φ` to show that `p.rep` and `q.rep`
  -- are within controlled Gromov-Hausdorff distance.
  have main : GH_dist p.rep q.rep ≤ ε + ε/2 + ε,
  { refine GH_dist_le_of_approx_subsets Φ  _ _ _,
    show ∀ x : p.rep, ∃ (y : p.rep) (H : y ∈ s p), dist x y ≤ ε,
    { -- by construction, `s p` is `ε`-dense
      assume x,
      have : x ∈ ⋃y∈(s p), ball y ε := (hs p).2 (mem_univ _),
      rcases mem_bUnion_iff.1 this with ⟨y, ys, hy⟩,
      exact ⟨y, ys, le_of_lt hy⟩ },
    show ∀ x : q.rep, ∃ (z : s p), dist x (Φ z) ≤ ε,
    { -- by construction, `s q` is `ε`-dense, and it is the range of `Φ`
      assume x,
      have : x ∈ ⋃y∈(s q), ball y ε := (hs q).2 (mem_univ _),
      rcases mem_bUnion_iff.1 this with ⟨y, ys, hy⟩,
      let i : ℕ := E q ⟨y, ys⟩,
      let hi := ((E q) ⟨y, ys⟩).is_lt,
      have ihi_eq : (⟨i, hi⟩ : fin (N q)) = (E q) ⟨y, ys⟩, by rw [fin.ext_iff, fin.coe_mk],
      have hiq : i < N q := hi,
      have hip : i < N p, { rwa Npq.symm at hiq },
      let z := (E p).symm ⟨i, hip⟩,
      use z,
      have C1 : (E p) z = ⟨i, hip⟩ := (E p).apply_symm_apply ⟨i, hip⟩,
      have C2 : fin.cast Npq ⟨i, hip⟩ = ⟨i, hi⟩ := rfl,
      have C3 : (E q).symm ⟨i, hi⟩ = ⟨y, ys⟩,
        by { rw ihi_eq, exact (E q).symm_apply_apply ⟨y, ys⟩ },
      have : Φ z = y :=
        by { simp only [Φ, Ψ], rw [C1, C2, C3], refl },
      rw this,
      exact le_of_lt hy },
    show ∀ x y : s p, abs (dist x y - dist (Φ x) (Φ y)) ≤ ε,
    { /- the distance between `x` and `y` is encoded in `F p`, and the distance between
      `Φ x` and `Φ y` (two points of `s q`) is encoded in `F q`, all this up to `ε`.
      As `F p = F q`, the distances are almost equal. -/
      assume x y,
      have : dist (Φ x) (Φ y) = dist (Ψ x) (Ψ y) := rfl,
      rw this,
      -- introduce `i`, that codes both `x` and `Φ x` in `fin (N p) = fin (N q)`
      let i : ℕ := E p x,
      have hip : i < N p := ((E p) x).2,
      have hiq : i < N q, by rwa Npq at hip,
      have i' : i = ((E q) (Ψ x)), by { simp [Ψ] },
      -- introduce `j`, that codes both `y` and `Φ y` in `fin (N p) = fin (N q)`
      let j : ℕ := E p y,
      have hjp : j < N p := ((E p) y).2,
      have hjq : j < N q, by rwa Npq at hjp,
      have j' : j = ((E q) (Ψ y)).1, by { simp [Ψ] },
      -- Express `dist x y` in terms of `F p`
      have : (F p).2 ((E p) x) ((E p) y) = floor (ε⁻¹ * dist x y),
        by simp only [F, (E p).symm_apply_apply],
      have Ap : (F p).2 ⟨i, hip⟩ ⟨j, hjp⟩ = floor (ε⁻¹ * dist x y),
        by { rw ← this, congr; apply (fin.ext_iff _ _).2; refl },
      -- Express `dist (Φ x) (Φ y)` in terms of `F q`
      have : (F q).2 ((E q) (Ψ x)) ((E q) (Ψ y)) = floor (ε⁻¹ * dist (Ψ x) (Ψ y)),
        by simp only [F, (E q).symm_apply_apply],
      have Aq : (F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩ = floor (ε⁻¹ * dist (Ψ x) (Ψ y)),
        by { rw ← this, congr; apply (fin.ext_iff _ _).2; [exact i', exact j'] },
      -- use the equality between `F p` and `F q` to deduce that the distances have equal
      -- integer parts
      have : (F p).2 ⟨i, hip⟩ ⟨j, hjp⟩ = (F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩,
      { -- we want to `subst hpq` where `hpq : F p = F q`, except that `subst` only works
        -- with a constant, so replace `F q` (and everything that depends on it) by a constant `f`
        -- then `subst`
        revert hiq hjq,
        change N q with (F q).1,
        generalize_hyp : F q = f at hpq ⊢,
        subst hpq,
        intros,
        refl },
      rw [Ap, Aq] at this,
      -- deduce that the distances coincide up to `ε`, by a straightforward computation
      -- that should be automated
      have I := calc
        abs (ε⁻¹) * abs (dist x y - dist (Ψ x) (Ψ y)) =
          abs (ε⁻¹ * (dist x y - dist (Ψ x) (Ψ y))) : (abs_mul _ _).symm
        ... = abs ((ε⁻¹ * dist x y) - (ε⁻¹ * dist (Ψ x) (Ψ y))) : by { congr, ring }
        ... ≤ 1 : le_of_lt (abs_sub_lt_one_of_floor_eq_floor this),
      calc
        abs (dist x y - dist (Ψ x) (Ψ y)) = (ε * ε⁻¹) * abs (dist x y - dist (Ψ x) (Ψ y)) :
          by rw [mul_inv_cancel (ne_of_gt εpos), one_mul]
        ... = ε * (abs (ε⁻¹) * abs (dist x y - dist (Ψ x) (Ψ y))) :
          by rw [abs_of_nonneg (le_of_lt (inv_pos.2 εpos)), mul_assoc]
        ... ≤ ε * 1 : mul_le_mul_of_nonneg_left I (le_of_lt εpos)
        ... = ε : mul_one _ } },
  calc dist p q = GH_dist (p.rep) (q.rep) : dist_GH_dist p q
    ... ≤ ε + ε/2 + ε : main
    ... = δ : by { simp [ε], ring }
end

/-- Compactness criterion: a closed set of compact metric spaces is compact if the spaces have
a uniformly bounded diameter, and for all `ε` the number of balls of radius `ε` required
to cover the spaces is uniformly bounded. This is an equivalence, but we only prove the
interesting direction that these conditions imply compactness. -/
lemma totally_bounded {t : set GH_space} {C : ℝ} {u : ℕ → ℝ} {K : ℕ → ℕ}
  (ulim : tendsto u at_top (𝓝 0))
  (hdiam : ∀ p ∈ t, diam (univ : set (GH_space.rep p)) ≤ C)
  (hcov : ∀ p ∈ t, ∀ n:ℕ, ∃ s : set (GH_space.rep p),
    cardinal.mk s ≤ K n ∧ univ ⊆ ⋃x∈s, ball x (u n)) :
  totally_bounded t :=
begin
  /- Let `δ>0`, and `ε = δ/5`. For each `p`, we construct a finite subset `s p` of `p`, which
  is `ε`-dense and has cardinality at most `K n`. Encoding the mutual distances of points in `s p`,
  up to `ε`, we will get a map `F` associating to `p` finitely many data, and making it possible to
  reconstruct `p` up to `ε`. This is enough to prove total boundedness. -/
  refine metric.totally_bounded_of_finite_discretization (λ δ δpos, _),
  let ε := (1/5) * δ,
  have εpos : 0 < ε := mul_pos (by norm_num) δpos,
  -- choose `n` for which `u n < ε`
  rcases metric.tendsto_at_top.1 ulim ε εpos with ⟨n, hn⟩,
  have u_le_ε : u n ≤ ε,
  { have := hn n (le_refl _),
    simp only [real.dist_eq, add_zero, sub_eq_add_neg, neg_zero] at this,
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) this) },
  -- construct a finite subset `s p` of `p` which is `ε`-dense and has cardinal `≤ K n`
  have : ∀ p:GH_space, ∃ s : set (p.rep), ∃ N ≤ K n, ∃ E : equiv s (fin N),
    p ∈ t → univ ⊆ ⋃x∈s, ball x (u n),
  { assume p,
    by_cases hp : p ∉ t,
    { have : nonempty (equiv (∅ : set (p.rep)) (fin 0)),
      { rw ← fintype.card_eq, simp },
      use [∅, 0, bot_le, choice (this)] },
    { rcases hcov _ (set.not_not_mem.1 hp) n with ⟨s, ⟨scard, scover⟩⟩,
      rcases cardinal.lt_omega.1 (lt_of_le_of_lt scard (cardinal.nat_lt_omega _)) with ⟨N, hN⟩,
      rw [hN, cardinal.nat_cast_le] at scard,
      have : cardinal.mk s = cardinal.mk (fin N), by rw [hN, cardinal.mk_fin],
      cases quotient.exact this with E,
      use [s, N, scard, E],
      simp [hp, scover] } },
  choose s N hN E hs using this,
  -- Define a function `F` taking values in a finite type and associating to `p` enough data
  -- to reconstruct it up to `ε`, namely the (discretized) distances between elements of `s p`.
  let M := (floor (ε⁻¹ * max C 0)).to_nat,
  let F : GH_space → (Σk:fin ((K n).succ), (fin k → fin k → fin (M.succ))) :=
    λ p, ⟨⟨N p, lt_of_le_of_lt (hN p) (nat.lt_succ_self _)⟩,
         λ a b, ⟨min M (floor (ε⁻¹ * dist ((E p).symm a) ((E p).symm b))).to_nat,
                lt_of_le_of_lt ( min_le_left _ _) (nat.lt_succ_self _) ⟩ ⟩,
  refine ⟨_, by apply_instance, (λ p, F p), _⟩,
  -- It remains to show that if `F p = F q`, then `p` and `q` are `ε`-close
  rintros ⟨p, pt⟩ ⟨q, qt⟩ hpq,
  have Npq : N p = N q := (fin.ext_iff _ _).1 (sigma.mk.inj_iff.1 hpq).1,
  let Ψ : s p → s q := λ x, (E q).symm (fin.cast Npq ((E p) x)),
  let Φ : s p → q.rep := λ x, Ψ x,
  have main : GH_dist (p.rep) (q.rep) ≤ ε + ε/2 + ε,
  { -- to prove the main inequality, argue that `s p` is `ε`-dense in `p`, and `s q` is `ε`-dense
    -- in `q`, and `s p` and `s q` are almost isometric. Then closeness follows
    -- from `GH_dist_le_of_approx_subsets`
    refine GH_dist_le_of_approx_subsets Φ  _ _ _,
    show ∀ x : p.rep, ∃ (y : p.rep) (H : y ∈ s p), dist x y ≤ ε,
    { -- by construction, `s p` is `ε`-dense
      assume x,
      have : x ∈ ⋃y∈(s p), ball y (u n) := (hs p pt) (mem_univ _),
      rcases mem_bUnion_iff.1 this with ⟨y, ys, hy⟩,
      exact ⟨y, ys, le_trans (le_of_lt hy) u_le_ε⟩ },
    show ∀ x : q.rep, ∃ (z : s p), dist x (Φ z) ≤ ε,
    { -- by construction, `s q` is `ε`-dense, and it is the range of `Φ`
      assume x,
      have : x ∈ ⋃y∈(s q), ball y (u n) := (hs q qt) (mem_univ _),
      rcases mem_bUnion_iff.1 this with ⟨y, ys, hy⟩,
      let i : ℕ := E q ⟨y, ys⟩,
      let hi := ((E q) ⟨y, ys⟩).2,
      have ihi_eq : (⟨i, hi⟩ : fin (N q)) = (E q) ⟨y, ys⟩, by rw [fin.ext_iff, fin.coe_mk],
      have hiq : i < N q := hi,
      have hip : i < N p, { rwa Npq.symm at hiq },
      let z := (E p).symm ⟨i, hip⟩,
      use z,
      have C1 : (E p) z = ⟨i, hip⟩ := (E p).apply_symm_apply ⟨i, hip⟩,
      have C2 : fin.cast Npq ⟨i, hip⟩ = ⟨i, hi⟩ := rfl,
      have C3 : (E q).symm ⟨i, hi⟩ = ⟨y, ys⟩,
        by { rw ihi_eq, exact (E q).symm_apply_apply ⟨y, ys⟩ },
      have : Φ z = y :=
        by { simp only [Φ, Ψ], rw [C1, C2, C3], refl },
      rw this,
      exact le_trans (le_of_lt hy) u_le_ε },
    show ∀ x y : s p, abs (dist x y - dist (Φ x) (Φ y)) ≤ ε,
    { /- the distance between `x` and `y` is encoded in `F p`, and the distance between
      `Φ x` and `Φ y` (two points of `s q`) is encoded in `F q`, all this up to `ε`.
      As `F p = F q`, the distances are almost equal. -/
      assume x y,
      have : dist (Φ x) (Φ y) = dist (Ψ x) (Ψ y) := rfl,
      rw this,
      -- introduce `i`, that codes both `x` and `Φ x` in `fin (N p) = fin (N q)`
      let i : ℕ := E p x,
      have hip : i < N p := ((E p) x).2,
      have hiq : i < N q, by rwa Npq at hip,
      have i' : i = ((E q) (Ψ x)), by { simp [Ψ] },
      -- introduce `j`, that codes both `y` and `Φ y` in `fin (N p) = fin (N q)`
      let j : ℕ := E p y,
      have hjp : j < N p := ((E p) y).2,
      have hjq : j < N q, by rwa Npq at hjp,
      have j' : j = ((E q) (Ψ y)), by { simp [Ψ] },
      -- Express `dist x y` in terms of `F p`
      have Ap : ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = (floor (ε⁻¹ * dist x y)).to_nat := calc
        ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = ((F p).2 ((E p) x) ((E p) y)).1 :
          by { congr; apply (fin.ext_iff _ _).2; refl }
        ... = min M (floor (ε⁻¹ * dist x y)).to_nat :
          by simp only [F, (E p).symm_apply_apply]
        ... = (floor (ε⁻¹ * dist x y)).to_nat :
        begin
          refine min_eq_right (int.to_nat_le_to_nat (floor_mono _)),
          refine mul_le_mul_of_nonneg_left (le_trans _ (le_max_left _ _)) ((inv_pos.2 εpos).le),
          change dist (x : p.rep) y ≤ C,
          refine le_trans (dist_le_diam_of_mem compact_univ.bounded (mem_univ _) (mem_univ _)) _,
          exact hdiam p pt
        end,
      -- Express `dist (Φ x) (Φ y)` in terms of `F q`
      have Aq : ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1 = (floor (ε⁻¹ * dist (Ψ x) (Ψ y))).to_nat := calc
        ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1 = ((F q).2 ((E q) (Ψ x)) ((E q) (Ψ y))).1 :
          by { congr; apply (fin.ext_iff _ _).2; [exact i', exact j'] }
        ... = min M (floor (ε⁻¹ * dist (Ψ x) (Ψ y))).to_nat :
          by simp only [F, (E q).symm_apply_apply]
        ... = (floor (ε⁻¹ * dist (Ψ x) (Ψ y))).to_nat :
        begin
          refine min_eq_right (int.to_nat_le_to_nat (floor_mono _)),
          refine mul_le_mul_of_nonneg_left (le_trans _ (le_max_left _ _)) ((inv_pos.2 εpos).le),
          change dist (Ψ x : q.rep) (Ψ y) ≤ C,
          refine le_trans (dist_le_diam_of_mem compact_univ.bounded (mem_univ _) (mem_univ _)) _,
          exact hdiam q qt
        end,
      -- use the equality between `F p` and `F q` to deduce that the distances have equal
      -- integer parts
      have : ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1,
      { -- we want to `subst hpq` where `hpq : F p = F q`, except that `subst` only works
        -- with a constant, so replace `F q` (and everything that depends on it) by a constant `f`
        -- then `subst`
        revert hiq hjq,
        change N q with (F q).1,
        generalize_hyp : F q = f at hpq ⊢,
        subst hpq,
        intros,
        refl },
      have : floor (ε⁻¹ * dist x y) = floor (ε⁻¹ * dist (Ψ x) (Ψ y)),
      { rw [Ap, Aq] at this,
        have D : 0 ≤ floor (ε⁻¹ * dist x y) :=
          floor_nonneg.2 (mul_nonneg (le_of_lt (inv_pos.2 εpos)) dist_nonneg),
        have D' : floor (ε⁻¹ * dist (Ψ x) (Ψ y)) ≥ 0 :=
          floor_nonneg.2 (mul_nonneg (le_of_lt (inv_pos.2 εpos)) dist_nonneg),
        rw [← int.to_nat_of_nonneg D, ← int.to_nat_of_nonneg D', this] },
      -- deduce that the distances coincide up to `ε`, by a straightforward computation
      -- that should be automated
      have I := calc
        abs (ε⁻¹) * abs (dist x y - dist (Ψ x) (Ψ y)) =
          abs (ε⁻¹ * (dist x y - dist (Ψ x) (Ψ y))) : (abs_mul _ _).symm
        ... = abs ((ε⁻¹ * dist x y) - (ε⁻¹ * dist (Ψ x) (Ψ y))) : by { congr, ring }
        ... ≤ 1 : le_of_lt (abs_sub_lt_one_of_floor_eq_floor this),
      calc
        abs (dist x y - dist (Ψ x) (Ψ y)) = (ε * ε⁻¹) * abs (dist x y - dist (Ψ x) (Ψ y)) :
          by rw [mul_inv_cancel (ne_of_gt εpos), one_mul]
        ... = ε * (abs (ε⁻¹) * abs (dist x y - dist (Ψ x) (Ψ y))) :
          by rw [abs_of_nonneg (le_of_lt (inv_pos.2 εpos)), mul_assoc]
        ... ≤ ε * 1 : mul_le_mul_of_nonneg_left I (le_of_lt εpos)
        ... = ε : mul_one _ } },
  calc dist p q = GH_dist (p.rep) (q.rep) : dist_GH_dist p q
    ... ≤ ε + ε/2 + ε : main
    ... = δ/2 : by { simp [ε], ring }
    ... < δ : half_lt_self δpos
end

section complete

/- We will show that a sequence `u n` of compact metric spaces satisfying
`dist (u n) (u (n+1)) < 1/2^n` converges, which implies completeness of the Gromov-Hausdorff space.
We need to exhibit the limiting compact metric space. For this, start from
a sequence `X n` of representatives of `u n`, and glue in an optimal way `X n` to `X (n+1)`
for all `n`, in a common metric space. Formally, this is done as follows.
Start from `Y 0 = X 0`. Then, glue `X 0` to `X 1` in an optimal way, yielding a space
`Y 1` (with an embedding of `X 1`). Then, consider an optimal gluing of `X 1` and `X 2`, and
glue it to `Y 1` along their common subspace `X 1`. This gives a new space `Y 2`, with an
embedding of `X 2`. Go on, to obtain a sequence of spaces `Y n`. Let `Z0` be the inductive
limit of the `Y n`, and finally let `Z` be the completion of `Z0`.
The images `X2 n` of `X n` in `Z` are at Hausdorff distance `< 1/2^n` by construction, hence they
form a Cauchy sequence for the Hausdorff distance. By completeness (of `Z`, and therefore of its
set of nonempty compact subsets), they converge to a limit `L`. This is the nonempty
compact metric space we are looking for.  -/

variables (X : ℕ → Type) [∀ n, metric_space (X n)] [∀ n, compact_space (X n)] [∀ n, nonempty (X n)]

/-- Auxiliary structure used to glue metric spaces below, recording an isometric embedding
of a type `A` in another metric space. -/
structure aux_gluing_struct (A : Type) [metric_space A] : Type 1 :=
(space  : Type)
(metric : metric_space space)
(embed  : A → space)
(isom   : isometry embed)

instance (A : Type) [metric_space A] : inhabited (aux_gluing_struct A) :=
⟨{ space := A,
  metric := by apply_instance,
  embed := id,
  isom := λ x y, rfl }⟩

/-- Auxiliary sequence of metric spaces, containing copies of `X 0`, ..., `X n`, where each
`X i` is glued to `X (i+1)` in an optimal way. The space at step `n+1` is obtained from the space
at step `n` by adding `X (n+1)`, glued in an optimal way to the `X n` already sitting there. -/
def aux_gluing (n : ℕ) : aux_gluing_struct (X n) := nat.rec_on n
  { space  := X 0,
    metric := by apply_instance,
    embed  := id,
    isom   := λ x y, rfl }
(λ n Y, by letI : metric_space Y.space := Y.metric; exact
  { space  := glue_space Y.isom (isometry_optimal_GH_injl (X n) (X (n+1))),
    metric := by apply_instance,
    embed  := (to_glue_r Y.isom (isometry_optimal_GH_injl (X n) (X (n+1))))
              ∘ (optimal_GH_injr (X n) (X (n+1))),
    isom   := (to_glue_r_isometry _ _).comp (isometry_optimal_GH_injr (X n) (X (n+1))) })

/-- The Gromov-Hausdorff space is complete. -/
instance : complete_space GH_space :=
begin
  have : ∀ (n : ℕ), 0 < ((1:ℝ) / 2) ^ n, by { apply pow_pos, norm_num },
  -- start from a sequence of nonempty compact metric spaces within distance `1/2^n` of each other
  refine metric.complete_of_convergent_controlled_sequences (λ n, (1/2)^n) this (λ u hu, _),
  -- `X n` is a representative of `u n`
  let X := λ n, (u n).rep,
  -- glue them together successively in an optimal way, getting a sequence of metric spaces `Y n`
  let Y := aux_gluing X,
  letI : ∀ n, metric_space (Y n).space := λ n, (Y n).metric,
  have E : ∀ n : ℕ,
    glue_space (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ)) = (Y n.succ).space :=
    λ n, by { simp [Y, aux_gluing], refl },
  let c := λ n, cast (E n),
  have ic : ∀ n, isometry (c n) := λ n x y, rfl,
  -- there is a canonical embedding of `Y n` in `Y (n+1)`, by construction
  let f : Πn, (Y n).space → (Y n.succ).space :=
    λ n, (c n) ∘ (to_glue_l (aux_gluing X n).isom (isometry_optimal_GH_injl (X n) (X n.succ))),
  have I : ∀ n, isometry (f n),
  { assume n,
    apply isometry.comp,
    { assume x y, refl },
    { apply to_glue_l_isometry } },
  -- consider the inductive limit `Z0` of the `Y n`, and then its completion `Z`
  let Z0 := metric.inductive_limit I,
  let Z := uniform_space.completion Z0,
  let Φ := to_inductive_limit I,
  let coeZ := (coe : Z0 → Z),
  -- let `X2 n` be the image of `X n` in the space `Z`
  let X2 := λ n, range (coeZ ∘ (Φ n) ∘ (Y n).embed),
  have isom : ∀ n, isometry (coeZ ∘ (Φ n) ∘ (Y n).embed),
  { assume n,
    apply isometry.comp completion.coe_isometry _,
    apply isometry.comp _ (Y n).isom,
    apply to_inductive_limit_isometry },
  -- The Hausdorff distance of `X2 n` and `X2 (n+1)` is by construction the distance between
  -- `u n` and `u (n+1)`, therefore bounded by `1/2^n`
  have D2 : ∀ n, Hausdorff_dist (X2 n) (X2 n.succ) < (1/2)^n,
  { assume n,
    have X2n : X2 n = range ((coeZ ∘ (Φ n.succ) ∘ (c n)
      ∘ (to_glue_r (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ))))
      ∘ (optimal_GH_injl (X n) (X n.succ))),
    { change X2 n = range (coeZ ∘ (Φ n.succ) ∘ (c n)
        ∘ (to_glue_r (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ)))
        ∘ (optimal_GH_injl (X n) (X n.succ))),
      simp only [X2, Φ],
      rw [← to_inductive_limit_commute I],
      simp only [f],
      rw ← to_glue_commute },
    rw range_comp at X2n,
    have X2nsucc : X2 n.succ = range ((coeZ ∘ (Φ n.succ) ∘ (c n)
      ∘ (to_glue_r (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ))))
      ∘ (optimal_GH_injr (X n) (X n.succ))), by refl,
    rw range_comp at X2nsucc,
    rw [X2n, X2nsucc, Hausdorff_dist_image, Hausdorff_dist_optimal, ← dist_GH_dist],
    { exact hu n n n.succ (le_refl n) (le_succ n) },
    { apply isometry.comp completion.coe_isometry _,
      apply isometry.comp _ ((ic n).comp (to_glue_r_isometry _ _)),
      apply to_inductive_limit_isometry } },
  -- consider `X2 n` as a member `X3 n` of the type of nonempty compact subsets of `Z`, which
  -- is a metric space
  let X3 : ℕ → nonempty_compacts Z := λ n, ⟨X2 n,
    ⟨range_nonempty _, is_compact_range (isom n).continuous ⟩⟩,
  -- `X3 n` is a Cauchy sequence by construction, as the successive distances are
  -- bounded by `(1/2)^n`
  have : cauchy_seq X3,
  { refine cauchy_seq_of_le_geometric (1/2) 1 (by norm_num) (λ n, _),
    rw one_mul,
    exact le_of_lt (D2 n) },
  -- therefore, it converges to a limit `L`
  rcases cauchy_seq_tendsto_of_complete this with ⟨L, hL⟩,
  -- the images of `X3 n` in the Gromov-Hausdorff space converge to the image of `L`
  have M : tendsto (λ n, (X3 n).to_GH_space) at_top (𝓝 L.to_GH_space) :=
    tendsto.comp (to_GH_space_continuous.tendsto _) hL,
  -- By construction, the image of `X3 n` in the Gromov-Hausdorff space is `u n`.
  have : ∀ n, (X3 n).to_GH_space = u n,
  { assume n,
    rw [nonempty_compacts.to_GH_space, ← (u n).to_GH_space_rep,
        to_GH_space_eq_to_GH_space_iff_isometric],
    constructor,
    convert (isom n).isometric_on_range.symm, },
  -- Finally, we have proved the convergence of `u n`
  exact ⟨L.to_GH_space, by simpa [this] using M⟩
end

end complete--section

end Gromov_Hausdorff --namespace
