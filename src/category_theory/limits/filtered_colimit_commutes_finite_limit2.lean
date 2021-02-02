/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.colimit_limit2
import category_theory.limits.shapes.finite_limits

/-!
# Filtered colimits commute with finite limits.

We show that for a functor `F : J × K ⥤ Type v`, when `J` is finite and `K` is filtered,
the universal morphism `colimit_limit_to_limit_colimit F` comparing the
colimit (over `K`) of the limits (over `J`) with the limit of the colimits is an isomorphism.

(In fact, to prove that it is injective only requires that `J` has finitely many objects.)

## References
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
* [Stacks: Filtered colimits](https://stacks.math.columbia.edu/tag/002W)
-/

universes v₁ v₂ u₁ u₂ u₃

open category_theory
open category_theory.category
open category_theory.limits.types
open category_theory.limits.types.filtered_colimit

namespace category_theory.limits

variables {J : Type u₁} {K : Type u₂} [category.{v₁} J] [category.{v₂} K]

variables (F : J ⥤ K ⥤ Type u₃)

variables {cj : Π (j : J), cone (F.obj j)}
variables {ck : Π (k : K), cocone (F.flip.obj k)}
variables (tj : Π (j : J), is_limit (cj j))
variables (tk : Π (k : K), is_colimit (ck k))
variables {c₁ : cocone (cones_to_functor tj)} (t₁ : is_colimit c₁)
variables {c₂ : cone (cocones_to_functor tk)} (t₂ : is_limit c₂)

variables [is_filtered J]
section
variables [fintype K]

lemma colimit_to_limit_injective :
  function.injective (colimit_to_limit tj tk t₁ t₂) :=
begin
  classical,
  -- Suppose we have two terms `x y` in the colimit (over `K`) of the limits (over `J`),
  -- and that these have the same image under `colimit_limit_to_limit_colimit F`.
  intros x y h,
  -- These elements of the colimit have representatives somehwere:
  obtain ⟨kx, x, rfl⟩ := jointly_surjective (cones_to_functor tj) t₁ x,
  obtain ⟨ky, y, rfl⟩ := jointly_surjective (cones_to_functor tj) t₁ y,
  dsimp at x y,
  -- Since the images of `x` and `y` are equal in a limit, they are equal componentwise
  -- (indexed by `j : J`),
  replace h := λ (j : K), congr_arg (c₂.π.app j) h,
  change ∀ j, (c₁.ι.app kx ≫ limits.colimit_to_limit tj tk t₁ t₂ ≫ c₂.π.app j) x =
              (c₁.ι.app ky ≫ limits.colimit_to_limit tj tk t₁ t₂ ≫ c₂.π.app j) y at h,
  simp_rw ι_colimit_to_limit_π at h,
  dsimp at h,
  have : ∀ (k : K), ∃ (j : J) (f : kx ⟶ j) (g : ky ⟶ j),
              (F.flip.obj k).map f ((cj kx).π.app k x) = (F.flip.obj k).map g ((cj ky).π.app k y),
  { intro k,
    rw ←is_colimit_eq_iff _ (tk k),
    rw h },
  choose j f g w using this,

  -- We now use that `J` is filtered, picking some point to the right of all these
  -- morphisms `f k` and `g k`.
  let O : finset J := finset.univ.image j ∪ {kx, ky},
  have kxO : kx ∈ O := finset.mem_union.mpr (or.inr (by simp)),
  have kyO : ky ∈ O := finset.mem_union.mpr (or.inr (by simp)),
  have kjO : ∀ k, j k ∈ O := λ j, finset.mem_union.mpr (or.inl (by simp)),

  let H : finset (Σ' (X Y : J) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) :=
    (finset.univ).image (λ k : K, ⟨kx, j k, kxO,
      finset.mem_union.mpr (or.inl (by simp)),
      f k⟩) ∪
    (finset.univ).image (λ k : K, ⟨ky, j k, kyO,
      finset.mem_union.mpr (or.inl (by simp)),
      g k⟩),
  obtain ⟨S, T, W⟩ := is_filtered.sup_exists O H,

  have fH : ∀ k, (⟨kx, j k, kxO, kjO k, f k⟩ : (Σ' (X Y : J) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y)) ∈ H :=
    λ j, (finset.mem_union.mpr (or.inl
    begin
      simp only [true_and, finset.mem_univ, eq_self_iff_true, exists_prop_of_true,
        finset.mem_image, heq_iff_eq],
      refine ⟨j, rfl, _⟩,
      simp only [heq_iff_eq],
      exact ⟨rfl, rfl, rfl⟩,
    end)),
  have gH : ∀ k, (⟨ky, j k, kyO, kjO k, g k⟩ : (Σ' (X Y : J) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y)) ∈ H :=
    λ j, (finset.mem_union.mpr (or.inr
    begin
      simp only [true_and, finset.mem_univ, eq_self_iff_true, exists_prop_of_true,
        finset.mem_image, heq_iff_eq],
      refine ⟨j, rfl, _⟩,
      simp only [heq_iff_eq],
      exact ⟨rfl, rfl, rfl⟩,
    end)),
  rw is_colimit_eq_iff _ t₁,
  refine ⟨_, T kxO, T kyO, _⟩,
  apply is_limit_ext (tj _),
  intro k,
  change (limits.is_limit.map (cj kx) (tj S) (F.map (T kxO)) ≫ (cj S).π.app k) x = (limits.is_limit.map (cj ky) (tj S) (F.map (T kyO)) ≫ (cj S).π.app k) y,
  rw is_limit.map_π,
  rw is_limit.map_π,
  rw ← W _ _ (fH k),
  rw ← W _ _ (gH k),
  rw functor.map_comp,
  rw nat_trans.comp_app,
  rw functor.map_comp,
  rw nat_trans.comp_app,
  dsimp,
  have := w k,
  dsimp at this,
  rw this,
end

end

section

variables [fin_category K]

/--
This follows this proof from
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
although with different names.
-/
lemma colimit_limit_to_limit_colimit_surjective :
  function.surjective (colimit_to_limit tj tk t₁ t₂) :=
begin
  classical,
  -- We begin with some element `x` in the limit (over K) over the colimits (over J),
  intro x,

  -- This consists of some coherent family of elements in the various colimits,
  -- and so our first task is to pick representatives of these elements.
  have z := λ k, jointly_surjective _ (tk k) (c₂.π.app _ x),

  -- `j : K ⟶ J` records where the representative of the element in the `k`-th element of `x` lives
  -- `y j : F.obj (j, k j)` is the representative
  -- and we record that these representatives, when mapped back into the relevant colimits,
  -- are actually the components of `x`.
  choose j y e using z,

  -- As a first step, we use that `J` is filtered to pick some point `j' : J` above all the `j k`
  let j' : J := is_filtered.sup (finset.univ.image j) ∅,
  -- and name the morphisms as `g k : j k ⟶ j'`.
  have g : Π k, j k ⟶ j' := λ k, is_filtered.to_sup (finset.univ.image j) ∅ (by simp),
  clear_value j',

  -- Recalling that the components of `x`, which are indexed by `k : K`, are "coherent",
  -- in other words preserved by morphisms in the `K` direction,
  -- we see that for any morphism `f : k ⟶ k'` in `K`,
  -- the images of `y k` and `y k'`, when mapped to `F.obj (k', j')` respectively by
  -- `(f, g k)` and `(𝟙 k', g k')`, both represent the same element in the colimit.
  have w : ∀ {k k' : K} (f : k ⟶ k'),
              (ck k').ι.app j' ((F.map (g k')).app k' (y k')) =
              (ck k').ι.app j' ((F.obj j').map f ((F.map (g _)).app k (y k))),
  { intros k k' f,
    change ((F.flip.obj k').map (g k') ≫ (ck k').ι.app j') (y k') =
      ((F.flip.obj k).map (g k) ≫ (F.obj j').map f ≫ (ck k').ι.app j') (y k),
    rw (ck k').w,
    have : (F.flip.obj k).map (g k) ≫ (F.obj j').map f = (F.obj _).map f ≫ (F.flip.obj _).map (g _),
    { simp only [functor.flip_obj_map, nat_trans.naturality] },
    rw [reassoc_of this, (ck _).w, e, ← c₂.w f],
    change (tk k).map (ck k') (F.flip.map f) (c₂.π.app k x) =
      (ck k').ι.app (j k) ((F.obj (j k)).map f (y k)),
    rw [← e, ← types_comp_apply ((ck k).ι.app (j k)) ((tk k).map (ck k') (F.flip.map f)) (y k),
      is_colimit.ι_map],
    refl },

  -- Because `J` is filtered, we can restate this as saying that
  -- for each such `f`, there is some place to the right of `j'`
  -- where these images of `y k` and `y k'` become equal.
  have w' : ∀ (k k' : K) (f : k ⟶ k'),
        ∃ (j : J) (g' h' : j' ⟶ j),
          (F.map g').app k' ((F.map (g k')).app k' (y k')) =
            (F.map h').app k' ((F.obj j').map f ((F.map (g k)).app k (y k))),
  { intros k k' f,
    specialize w f,
    rw is_colimit_eq_iff _ (tk k') at w,
    apply w },

  -- We take a moment to restate `w` more conveniently.
  choose jf gf hf wf using w',
  clear w,

  -- We're now ready to use the fact that `J` is filtered a second time,
  -- picking some place to the right of all of
  -- the morphisms `gf f : j' ⟶ kh f` and `hf f : j' ⟶ jf f`.
  -- At this point we're relying on there being only finitely morphisms in `K`.
  let O := finset.univ.bUnion (λ k, finset.univ.bUnion (λ k', finset.univ.image (jf k k'))) ∪ {j'},
  have jfO : ∀ {j j'} (f : j ⟶ j'), jf _ _ f ∈ O := λ j j' f, finset.mem_union.mpr (or.inl (
  begin
    rw [finset.mem_bUnion],
    refine ⟨j, finset.mem_univ j, _⟩,
    rw [finset.mem_bUnion],
    refine ⟨j', finset.mem_univ j', _⟩,
    rw [finset.mem_image],
    refine ⟨f, finset.mem_univ _, _⟩,
    refl,
  end)),
  have j'O : j' ∈ O := finset.mem_union.mpr (or.inr (finset.mem_singleton.mpr rfl)),
  let H : finset (Σ' (X Y : J) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) :=
    finset.univ.bUnion (λ k : K, finset.univ.bUnion (λ k' : K, finset.univ.bUnion (λ f : k ⟶ k',
      {⟨j', jf _ _ f, j'O, jfO f, gf _ _ f⟩, ⟨j', jf _ _ f, j'O, jfO f, hf _ _ f⟩}))),

  obtain ⟨j'', i', s'⟩ := is_filtered.sup_exists O H,
  -- We then restate this slightly more conveniently, as a family of morphism `i f : jf _ _ f ⟶ j''`,
  -- satisfying `gf f ≫ i f = hf f' ≫ i f'`.
  let i : Π {k k'} (f : k ⟶ k'), jf _ _ f ⟶ j'' := λ k k' f, i' (jfO f),
  have s : ∀ {k₁ k₂ k₃ k₄} (f : k₁ ⟶ k₂) (f' : k₃ ⟶ k₄), gf _ _ f ≫ i f = hf _ _ f' ≫ i f',
  { intros,
    rw [s', s'],
    swap 2,
    exact j'O,
    swap 2,
    { rw [finset.mem_bUnion],
      refine ⟨k₁, finset.mem_univ _, _⟩,
      rw [finset.mem_bUnion],
      refine ⟨k₂, finset.mem_univ _, _⟩,
      rw [finset.mem_bUnion],
      refine ⟨f, finset.mem_univ _, _⟩,
      simp only [true_or, eq_self_iff_true, and_self, finset.mem_insert, heq_iff_eq], },
    { rw [finset.mem_bUnion],
      refine ⟨k₃, finset.mem_univ _, _⟩,
      rw [finset.mem_bUnion],
      refine ⟨k₄, finset.mem_univ _, _⟩,
      rw [finset.mem_bUnion],
      refine ⟨f', finset.mem_univ _, _⟩,
      simp only [eq_self_iff_true, or_true, and_self, finset.mem_insert, finset.mem_singleton,
        heq_iff_eq], } },
  clear_value i,
  clear s' i' H jfO j'O O,

  -- We're finally ready to construct the pre-image, and verify it really maps to `x`.
  fsplit,

  { -- We construct the pre-image (which, recall is meant to be a point
    -- in the colimit (over `J`) of the limits (over `K`)) via a representative at `j''`.
    apply c₁.ι.app j'' _,
    -- This representative is meant to be an element of a limit,
    -- so we need to construct a family of elements in `F.obj (j, k'')` for varying `j`,
    -- then show that are coherent with respect to morphisms in the `j` direction.
    apply types.is_limit.mk (tj j'') (λ k, _) _,
    { -- We construct the elements as the images of the `y k`.
      apply (F.map _).app k (y k),
      apply g _ ≫ gf _ _ (𝟙 _) ≫ i (𝟙 k) },
    { -- After which it's just a calculation, using `s` and `wf`, to see they are coherent.
      intros k k' f,
      change (F.obj j'').map f ((F.map (g k ≫ gf k k (𝟙 k) ≫ i (𝟙 k))).app k (y k)) = (F.map (g k' ≫ gf k' k' (𝟙 k') ≫ i (𝟙 k'))).app k' (y k'),
      rw s (𝟙 _) f,
      simp only [F.map_comp, nat_trans.comp_app],
      change ((F.map (g k)).app k ≫ (F.map (hf k k' f)).app k ≫ (F.map (i f)).app k ≫ (F.obj j'').map f) (y k) = _,
      have : (F.map (hf k k' f)).app k ≫ (F.map (i f)).app k ≫ (F.obj j'').map f
           = (F.obj _).map f ≫ (F.map (hf k k' f)).app _ ≫ (F.map (i f)).app _,
      { simp only [nat_trans.naturality, nat_trans.naturality_assoc] },
      rw this,
      change (F.map (i f)).app k' ((F.map (hf k k' f)).app k' ((F.obj j').map f ((F.map (g k)).app k (y k)))) =
        (F.map (i (𝟙 k'))).app k' ((F.map (gf k' k' (𝟙 k'))).app k' ((F.map (g k')).app k' (y k'))),
      rw ← wf _ _ f,
      change
        ((F.map (g k') ≫ F.map (gf k k' f) ≫ F.map (i f)).app k') (y k') =
          (F.map (g k') ≫ F.map (gf k' k' (𝟙 k')) ≫ F.map (i (𝟙 k'))).app k' (y k'),
      rw [← F.map_comp, ← F.map_comp, ← F.map_comp, ← F.map_comp, s (𝟙 k') f, ← s f f] } },
  -- Finally we check that this maps to `x`.
  { -- We can do this componentwise:
    apply is_limit_ext t₂,
    intro k,
    rw ← e,
    change (c₁.ι.app j'' ≫ limits.colimit_to_limit tj tk t₁ t₂ ≫ c₂.π.app k) _ = _,
    rw ι_colimit_to_limit_π,
    dsimp only [types_comp_apply],

    -- and as each component is an equation in a colimit, we can verify it by
    -- pointing out the morphism which carries one representative to the other:
    rw [types.is_limit.π_mk, is_colimit_eq_iff _ (tk k)],
    refine ⟨j'', 𝟙 _, g k ≫ gf _ _ (𝟙 k) ≫ i (𝟙 k), _⟩,
    simp only [functor.flip_obj_map, F.map_id, F.map_comp, nat_trans.comp_app, nat_trans.id_app,
      types_comp_apply, types_id_apply] },
end

noncomputable def filtered_colimit_finite_limit_iso : c₁.X ≅ c₂.X :=
equiv.to_iso
  (equiv.of_bijective
    (colimit_to_limit tj tk t₁ t₂)
    ⟨colimit_to_limit_injective _ _ _ _ _, colimit_limit_to_limit_colimit_surjective _ _ _ _ _⟩)

@[simp]
lemma filtered_colimit_finite_limit_iso_hom :
  (filtered_colimit_finite_limit_iso F tj tk t₁ t₂).hom = colimit_to_limit tj tk t₁ t₂ :=
rfl

end

end category_theory.limits
