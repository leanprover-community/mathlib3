/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.quasi_compact
import topology.quasi_separated

/-!
# Quasi-separated morphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A morphism of schemes `f : X ⟶ Y` is quasi-separated if the diagonal morphism `X ⟶ X ×[Y] X` is
quasi-compact.

A scheme is quasi-separated if the intersections of any two affine open sets is quasi-compact.
(`algebraic_geometry.quasi_separated_space_iff_affine`)

We show that a morphism is quasi-separated if the preimage of every affine open is quasi-separated.

We also show that this property is local at the target,
and is stable under compositions and base-changes.

## Main result
- `is_localization_basic_open_of_qcqs` (**Qcqs lemma**):
  If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

open_locale algebraic_geometry

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism is `quasi_separated` if diagonal map is quasi-compact. -/
@[mk_iff]
class quasi_separated (f : X ⟶ Y) : Prop :=
(diagonal_quasi_compact : quasi_compact (pullback.diagonal f))

/-- The `affine_target_morphism_property` corresponding to `quasi_separated`, asserting that the
domain is a quasi-separated scheme. -/
def quasi_separated.affine_property : affine_target_morphism_property :=
(λ X Y f _, quasi_separated_space X.carrier)

lemma quasi_separated_space_iff_affine (X : Scheme) :
  quasi_separated_space X.carrier ↔ ∀ (U V : X.affine_opens), is_compact (U ∩ V : set X.carrier) :=
begin
  rw quasi_separated_space_iff,
  split,
  { intros H U V, exact H U V U.1.2 U.2.is_compact V.1.2 V.2.is_compact },
  { intros H,
    suffices : ∀ (U : opens X.carrier) (hU : is_compact U.1) (V : opens X.carrier)
      (hV : is_compact V.1), is_compact (U ⊓ V).1,
    { intros U V hU hU' hV hV', exact this ⟨U, hU⟩ hU' ⟨V, hV⟩ hV' },
    intros U hU V hV,
    apply compact_open_induction_on V hV,
    { simp },
    { intros S hS V hV,
      change is_compact (U.1 ∩ (S.1 ∪ V.1)),
      rw set.inter_union_distrib_left,
      apply hV.union,
      clear hV,
      apply compact_open_induction_on U hU,
      { simp },
      { intros S hS W hW,
      change is_compact ((S.1 ∪ W.1) ∩ V.1),
        rw set.union_inter_distrib_right,
        apply hW.union,
        apply H } } }
end

lemma quasi_compact_affine_property_iff_quasi_separated_space {X Y : Scheme} [is_affine Y]
  (f : X ⟶ Y) :
  quasi_compact.affine_property.diagonal f ↔ quasi_separated_space X.carrier :=
begin
  delta affine_target_morphism_property.diagonal,
  rw quasi_separated_space_iff_affine,
  split,
  { intros H U V,
    haveI : is_affine _ := U.2,
    haveI : is_affine _ := V.2,
    let g : pullback (X.of_restrict U.1.open_embedding) (X.of_restrict V.1.open_embedding) ⟶ X :=
      pullback.fst ≫ X.of_restrict _,
    have : is_open_immersion g := infer_instance,
    have e := homeomorph.of_embedding _ this.base_open.to_embedding,
    rw is_open_immersion.range_pullback_to_base_of_left at e,
    erw [subtype.range_coe, subtype.range_coe] at e,
    rw is_compact_iff_compact_space,
    exact @@homeomorph.compact_space _ _ (H _ _) e },
  { introv H h₁ h₂,
    resetI,
    let g : pullback f₁ f₂ ⟶ X := pullback.fst ≫ f₁,
    have : is_open_immersion g := infer_instance,
    have e := homeomorph.of_embedding _ this.base_open.to_embedding,
    rw is_open_immersion.range_pullback_to_base_of_left at e,
    simp_rw is_compact_iff_compact_space at H,
    exact @@homeomorph.compact_space _ _
      (H ⟨⟨_, h₁.base_open.open_range⟩, range_is_affine_open_of_open_immersion _⟩
        ⟨⟨_, h₂.base_open.open_range⟩, range_is_affine_open_of_open_immersion _⟩) e.symm },
end

lemma quasi_separated_eq_diagonal_is_quasi_compact :
  @quasi_separated = morphism_property.diagonal @quasi_compact :=
by { ext, exact quasi_separated_iff _ }

lemma quasi_compact_affine_property_diagonal_eq :
  quasi_compact.affine_property.diagonal = quasi_separated.affine_property :=
by { ext, rw quasi_compact_affine_property_iff_quasi_separated_space, refl }

lemma quasi_separated_eq_affine_property_diagonal :
  @quasi_separated =
    target_affine_locally quasi_compact.affine_property.diagonal :=
begin
  rw [quasi_separated_eq_diagonal_is_quasi_compact, quasi_compact_eq_affine_property],
  exact diagonal_target_affine_locally_eq_target_affine_locally
    _ quasi_compact.affine_property_is_local
end

lemma quasi_separated_eq_affine_property :
  @quasi_separated =
    target_affine_locally quasi_separated.affine_property :=
by rw [quasi_separated_eq_affine_property_diagonal, quasi_compact_affine_property_diagonal_eq]

lemma quasi_separated.affine_property_is_local :
  quasi_separated.affine_property.is_local :=
quasi_compact_affine_property_diagonal_eq ▸
quasi_compact.affine_property_is_local.diagonal

@[priority 900]
instance quasi_separated_of_mono {X Y : Scheme} (f : X ⟶ Y) [mono f] : quasi_separated f :=
⟨infer_instance⟩

lemma quasi_separated_stable_under_composition :
  morphism_property.stable_under_composition @quasi_separated :=
quasi_separated_eq_diagonal_is_quasi_compact.symm ▸
  quasi_compact_stable_under_composition.diagonal
    quasi_compact_respects_iso
    quasi_compact_stable_under_base_change

lemma quasi_separated_stable_under_base_change :
  morphism_property.stable_under_base_change @quasi_separated :=
quasi_separated_eq_diagonal_is_quasi_compact.symm ▸
  quasi_compact_stable_under_base_change.diagonal
    quasi_compact_respects_iso

instance quasi_separated_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [quasi_separated f] [quasi_separated g] : quasi_separated (f ≫ g) :=
quasi_separated_stable_under_composition f g infer_instance infer_instance

lemma quasi_separated_respects_iso : morphism_property.respects_iso @quasi_separated :=
quasi_separated_eq_diagonal_is_quasi_compact.symm ▸
  quasi_compact_respects_iso.diagonal

lemma quasi_separated.affine_open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [quasi_separated f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)],
      ∀ (i : 𝒰.J), quasi_separated_space (pullback f (𝒰.map i)).carrier,
    ∀ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J),
      quasi_separated_space (pullback f (𝒰.map i)).carrier,
    ∀ {U : Scheme} (g : U ⟶ Y) [is_affine U] [is_open_immersion g],
      quasi_separated_space (pullback f g).carrier,
    ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)]
      (𝒰' : Π (i : 𝒰.J), Scheme.open_cover.{u} (pullback f (𝒰.map i)))
      [∀ i j, is_affine ((𝒰' i).obj j)], by exactI ∀ (i : 𝒰.J) (j k : (𝒰' i).J),
        compact_space (pullback ((𝒰' i).map j) ((𝒰' i).map k)).carrier] :=
begin
  have := quasi_compact.affine_property_is_local.diagonal_affine_open_cover_tfae f,
  simp_rw [← quasi_compact_eq_affine_property,
    ← quasi_separated_eq_diagonal_is_quasi_compact,
    quasi_compact_affine_property_diagonal_eq] at this,
  exact this
end

lemma quasi_separated.is_local_at_target :
  property_is_local_at_target @quasi_separated :=
quasi_separated_eq_affine_property_diagonal.symm ▸
  quasi_compact.affine_property_is_local.diagonal.target_affine_locally_is_local

lemma quasi_separated.open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [quasi_separated f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      quasi_separated (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      quasi_separated (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), quasi_separated (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      quasi_separated (pullback.snd : pullback f g ⟶ _),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤),
      ∀ i, quasi_separated (f ∣_ (U i))] :=
quasi_separated.is_local_at_target.open_cover_tfae f

lemma quasi_separated_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [is_affine Y] :
  quasi_separated f ↔ quasi_separated_space X.carrier :=
by rw [quasi_separated_eq_affine_property,
  quasi_separated.affine_property_is_local.affine_target_iff f,
  quasi_separated.affine_property]

lemma quasi_separated_space_iff_quasi_separated (X : Scheme) :
  quasi_separated_space X.carrier ↔ quasi_separated (terminal.from X) :=
(quasi_separated_over_affine_iff _).symm

lemma quasi_separated.affine_open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  quasi_separated f ↔ ∀ i, quasi_separated_space (pullback f (𝒰.map i)).carrier :=
begin
  rw [quasi_separated_eq_affine_property,
    quasi_separated.affine_property_is_local.affine_open_cover_iff f 𝒰],
  refl,
end

lemma quasi_separated.open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  (f : X ⟶ Y) :
  quasi_separated f ↔ ∀ i, quasi_separated (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
quasi_separated.is_local_at_target.open_cover_iff f 𝒰

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [quasi_separated g] :
  quasi_separated (pullback.fst : pullback f g ⟶ X) :=
quasi_separated_stable_under_base_change.fst f g infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [quasi_separated f] :
  quasi_separated (pullback.snd : pullback f g ⟶ Y) :=
quasi_separated_stable_under_base_change.snd f g infer_instance

instance {X Y Z: Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [quasi_separated f] [quasi_separated g] :
  quasi_separated (f ≫ g) :=
quasi_separated_stable_under_composition f g infer_instance infer_instance

lemma quasi_separated_space_of_quasi_separated {X Y : Scheme} (f : X ⟶ Y)
  [hY : quasi_separated_space Y.carrier] [quasi_separated f] : quasi_separated_space X.carrier :=
begin
  rw quasi_separated_space_iff_quasi_separated at hY ⊢,
  have : f ≫ terminal.from Y = terminal.from X := terminal_is_terminal.hom_ext _ _,
  rw ← this,
  resetI, apply_instance
end

instance quasi_separated_space_of_is_affine (X : Scheme) [is_affine X] :
  quasi_separated_space X.carrier :=
begin
  constructor,
  intros U V hU hU' hV hV',
  obtain ⟨s, hs, e⟩ := (is_compact_open_iff_eq_basic_open_union _).mp ⟨hU', hU⟩,
  obtain ⟨s', hs', e'⟩ := (is_compact_open_iff_eq_basic_open_union _).mp ⟨hV', hV⟩,
  rw [e, e', set.Union₂_inter],
  simp_rw [set.inter_Union₂],
  apply hs.is_compact_bUnion,
  { intros i hi,
    apply hs'.is_compact_bUnion,
    intros i' hi',
    change is_compact (X.basic_open i ⊓ X.basic_open i').1,
    rw ← Scheme.basic_open_mul,
    exact ((top_is_affine_open _).basic_open_is_affine _).is_compact }
end

lemma is_affine_open.is_quasi_separated {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
  is_quasi_separated (U : set X.carrier)  :=
begin
  rw is_quasi_separated_iff_quasi_separated_space,
  exacts [@@algebraic_geometry.quasi_separated_space_of_is_affine _ hU, U.is_open],
end

lemma quasi_separated_of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [H : quasi_separated (f ≫ g)] : quasi_separated f :=
begin
  rw (quasi_separated.affine_open_cover_tfae f).out 0 1,
  rw (quasi_separated.affine_open_cover_tfae (f ≫ g)).out 0 2 at H,
  use (Z.affine_cover.pullback_cover g).bind (λ x, Scheme.affine_cover _),
  split, { intro i, dsimp, apply_instance },
  rintro ⟨i, j⟩, dsimp at *,
  specialize H _ i,
  refine @@quasi_separated_space_of_quasi_separated _ H _,
  { exact pullback.map _ _ _ _ (𝟙 _) _ _ (by simp) (category.comp_id _) ≫
      (pullback_right_pullback_fst_iso g (Z.affine_cover.map i) f).hom },
  { apply algebraic_geometry.quasi_separated_of_mono }
end

lemma exists_eq_pow_mul_of_is_affine_open (X : Scheme) (U : opens X.carrier) (hU : is_affine_open U)
  (f : X.presheaf.obj (op U)) (x : X.presheaf.obj (op $ X.basic_open f)) :
  ∃ (n : ℕ) (y : X.presheaf.obj (op U)),
    y |_ X.basic_open f = (f |_ X.basic_open f) ^ n * x :=
begin
  have := (is_localization_basic_open hU f).2,
  obtain ⟨⟨y, _, n, rfl⟩, d⟩ := this x,
  use [n, y],
  delta Top.presheaf.restrict_open Top.presheaf.restrict,
  simpa [mul_comm x] using d.symm,
end

lemma exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux (X : Scheme)
  (S : X.affine_opens) (U₁ U₂ : opens X.carrier)
  {n₁ n₂ : ℕ} {y₁ : X.presheaf.obj (op U₁)}
  {y₂ : X.presheaf.obj (op U₂)} {f : X.presheaf.obj (op $ U₁ ⊔ U₂)}
  {x : X.presheaf.obj (op $ X.basic_open f)}
  (h₁ : S.1 ≤ U₁) (h₂ : S.1 ≤ U₂)
  (e₁ : X.presheaf.map (hom_of_le $ X.basic_open_le
    (X.presheaf.map (hom_of_le le_sup_left).op f) : _ ⟶ U₁).op y₁ =
      X.presheaf.map (hom_of_le (by { erw X.basic_open_res, exact inf_le_left })).op
        (X.presheaf.map (hom_of_le le_sup_left).op f) ^ n₁ *
      (X.presheaf.map (hom_of_le (by { erw X.basic_open_res, exact inf_le_right })).op) x)
  (e₂ : X.presheaf.map (hom_of_le $ X.basic_open_le
    (X.presheaf.map (hom_of_le le_sup_right).op f) : _ ⟶ U₂).op y₂ =
      X.presheaf.map (hom_of_le (by { rw X.basic_open_res, exact inf_le_left })).op
        (X.presheaf.map (hom_of_le le_sup_right).op f) ^ n₂ *
      (X.presheaf.map (hom_of_le (by { rw X.basic_open_res, exact inf_le_right })).op) x) :
  ∃ n : ℕ, X.presheaf.map (hom_of_le $ h₁).op
    ((X.presheaf.map (hom_of_le le_sup_left).op f) ^ (n + n₂) * y₁) =
    X.presheaf.map (hom_of_le $ h₂).op
      ((X.presheaf.map (hom_of_le le_sup_right).op f) ^ (n + n₁) * y₂) :=
begin
  have := (is_localization_basic_open S.2
    (X.presheaf.map (hom_of_le $ le_trans h₁ le_sup_left).op f)),
  obtain ⟨⟨_, n, rfl⟩, e⟩ :=
    (@is_localization.eq_iff_exists _ _ _ _ _ _ this (X.presheaf.map (hom_of_le $ h₁).op
      ((X.presheaf.map (hom_of_le le_sup_left).op f) ^ n₂ * y₁))
    (X.presheaf.map (hom_of_le $ h₂).op
      ((X.presheaf.map (hom_of_le le_sup_right).op f) ^ n₁ * y₂))).mp _,
  swap,
  { simp only [map_pow, ring_hom.algebra_map_to_algebra, map_mul, ← comp_apply,
      ← functor.map_comp, ← op_comp, hom_of_le_comp],
    have h₃ : X.basic_open ((X.presheaf.map (hom_of_le (h₁.trans le_sup_left)).op) f) ≤ S.val,
    { simpa only [X.basic_open_res] using inf_le_left, },
    transitivity
      X.presheaf.map (hom_of_le $ h₃.trans $ h₁.trans le_sup_left).op f ^ (n₂ + n₁) *
      X.presheaf.map (hom_of_le $ (X.basic_open_res f _).trans_le inf_le_right).op x,
    { rw [pow_add, mul_assoc], congr' 1,
      convert congr_arg (X.presheaf.map (hom_of_le _).op) e₁,
      { simp only [map_pow, map_mul, ← comp_apply, ← functor.map_comp, ← op_comp], congr },
      { simp only [map_pow, map_mul, ← comp_apply, ← functor.map_comp, ← op_comp], congr },
      { rw [X.basic_open_res, X.basic_open_res], rintros x ⟨H₁, H₂⟩, exact ⟨h₁ H₁, H₂⟩ } },
    { rw [add_comm, pow_add, mul_assoc], congr' 1,
      convert congr_arg (X.presheaf.map (hom_of_le _).op) e₂.symm,
      { simp only [map_pow, map_mul, ← comp_apply, ← functor.map_comp, ← op_comp], congr },
      { simp only [map_pow, map_mul, ← comp_apply, ← functor.map_comp, ← op_comp], congr },
      { simp only [X.basic_open_res],
        rintros x ⟨H₁, H₂⟩, exact ⟨h₂ H₁, H₂⟩ } } },
  use n,
  simp only [pow_add, map_pow, map_mul, ← comp_apply, ← mul_assoc,
    ← functor.map_comp, subtype.coe_mk] at e ⊢,
  exact e
end

lemma exists_eq_pow_mul_of_is_compact_of_is_quasi_separated (X : Scheme)
  (U : opens X.carrier) (hU : is_compact U.1) (hU' : is_quasi_separated U.1)
  (f : X.presheaf.obj (op U)) (x : X.presheaf.obj (op $ X.basic_open f)) :
  ∃ (n : ℕ) (y : X.presheaf.obj (op U)), y |_ X.basic_open f = (f |_ X.basic_open f) ^ n * x :=
begin
  delta Top.presheaf.restrict_open Top.presheaf.restrict,
  revert hU' f x,
  apply compact_open_induction_on U hU,
  { intros hU' f x,
    use [0, f],
    refine @@subsingleton.elim (CommRing.subsingleton_of_is_terminal
      (X.sheaf.is_terminal_of_eq_empty _)) _ _,
    erw eq_bot_iff,
    exact X.basic_open_le f },
  { -- Given `f : 𝒪(S ∪ U), x : 𝒪(X_f)`, we need to show that `f ^ n * x` is the restriction of
    -- some `y : 𝒪(S ∪ U)` for some `n : ℕ`.
    intros S hS U hU hSU f x,
    -- We know that such `y₁, n₁` exists on `S` by the induction hypothesis.
    obtain ⟨n₁, y₁, hy₁⟩ := hU (hSU.of_subset $ set.subset_union_left _ _)
      (X.presheaf.map (hom_of_le le_sup_left).op f) (X.presheaf.map (hom_of_le _).op x),
    swap, { rw X.basic_open_res, exact inf_le_right },
    -- We know that such `y₂, n₂` exists on `U` since `U` is affine.
    obtain ⟨n₂, y₂, hy₂⟩ := exists_eq_pow_mul_of_is_affine_open X _ U.2
      (X.presheaf.map (hom_of_le le_sup_right).op f) (X.presheaf.map (hom_of_le _).op x),
    delta Top.presheaf.restrict_open Top.presheaf.restrict at hy₂,
    swap, { rw X.basic_open_res, exact inf_le_right },
    -- Since `S ∪ U` is quasi-separated, `S ∩ U` can be covered by finite affine opens.
    obtain ⟨s, hs', hs⟩ := (is_compact_open_iff_eq_finset_affine_union _).mp
      ⟨hSU _ _ (set.subset_union_left _ _) S.2 hS
        (set.subset_union_right _ _) U.1.2 U.2.is_compact, (S ⊓ U.1).2⟩,
    haveI := hs'.to_subtype,
    casesI nonempty_fintype s,
    replace hs : S ⊓ U.1 = supr (λ i : s, (i : opens X.carrier)) := by { ext1, simpa using hs },
    have hs₁ : ∀ i : s, i.1.1 ≤ S,
    { intro i, change (i : opens X.carrier) ≤ S,
      refine le_trans _ inf_le_left, use U.1, erw hs, exact le_supr _ _ },
    have hs₂ : ∀ i : s, i.1.1 ≤ U.1,
    { intro i, change (i : opens X.carrier) ≤ U,
      refine le_trans _ inf_le_right, use S, erw hs, exact le_supr _ _ },
    -- On each affine open in the intersection, we have `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`
    -- for some `n` since `f ^ n₂ * y₁ = f ^ (n₁ + n₂) * x = f ^ n₁ * y₂` on `X_f`.
    have : ∀ i : s, ∃ n : ℕ,
      X.presheaf.map (hom_of_le $ hs₁ i).op
        ((X.presheaf.map (hom_of_le le_sup_left).op f) ^ (n + n₂) * y₁) =
      X.presheaf.map (hom_of_le $ hs₂ i).op
        ((X.presheaf.map (hom_of_le le_sup_right).op f) ^ (n + n₁) * y₂),
    { intro i,
      exact exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux X i.1 S U (hs₁ i) (hs₂ i)
        hy₁ hy₂ },
    choose n hn using this,
    -- We can thus choose a big enough `n` such that `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`
    -- on `S ∩ U`.
    have : X.presheaf.map (hom_of_le $ inf_le_left).op
      ((X.presheaf.map (hom_of_le le_sup_left).op f) ^ (finset.univ.sup n + n₂) * y₁) =
        X.presheaf.map (hom_of_le $ inf_le_right).op
          ((X.presheaf.map (hom_of_le le_sup_right).op f) ^ (finset.univ.sup n + n₁) * y₂),
    { fapply X.sheaf.eq_of_locally_eq' (λ i : s, i.1.1),
      { refine λ i, hom_of_le _, erw hs, exact le_supr _ _ },
      { exact le_of_eq hs },
      { intro i,
        replace hn := congr_arg (λ x, X.presheaf.map (hom_of_le
          (le_trans (hs₁ i) le_sup_left)).op f ^ (finset.univ.sup n - n i) * x) (hn i),
        dsimp only at hn,
        delta Scheme.sheaf SheafedSpace.sheaf,
        simp only [← map_pow, map_mul, ← comp_apply, ← functor.map_comp, ← op_comp, ← mul_assoc]
          at hn ⊢,
        erw [← map_mul, ← map_mul] at hn,
        rw [← pow_add, ← pow_add, ← add_assoc, ← add_assoc, tsub_add_cancel_of_le] at hn,
        convert hn,
        exact finset.le_sup (finset.mem_univ _) } },
    use finset.univ.sup n + n₁ + n₂,
    -- By the sheaf condition, since `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`, it can be glued into
    -- the desired section on `S ∪ U`.
    use (X.sheaf.obj_sup_iso_prod_eq_locus S U.1).inv ⟨⟨_ * _, _ * _⟩, this⟩,
    refine X.sheaf.eq_of_locally_eq₂
      (hom_of_le (_ : X.basic_open (X.presheaf.map (hom_of_le le_sup_left).op f) ≤ _))
      (hom_of_le (_ : X.basic_open (X.presheaf.map (hom_of_le le_sup_right).op f) ≤ _)) _ _ _ _ _,
    { rw X.basic_open_res, exact inf_le_right },
    { rw X.basic_open_res, exact inf_le_right },
    { rw [X.basic_open_res, X.basic_open_res],
      erw ← inf_sup_right,
      refine le_inf_iff.mpr ⟨X.basic_open_le f, le_of_eq rfl⟩ },
    { convert congr_arg (X.presheaf.map (hom_of_le _).op)
        (X.sheaf.obj_sup_iso_prod_eq_locus_inv_fst S U.1 ⟨⟨_ * _, _ * _⟩, this⟩) using 1,
      { delta Scheme.sheaf SheafedSpace.sheaf,
        simp only [← comp_apply (X.presheaf.map _) (X.presheaf.map _),
          ← functor.map_comp, ← op_comp],
        congr },
      { delta Scheme.sheaf SheafedSpace.sheaf,
        simp only [map_pow, map_mul, ← comp_apply, ← functor.map_comp, ← op_comp, mul_assoc,
          pow_add], erw hy₁, congr' 1, rw [← mul_assoc, ← mul_assoc], congr' 1,
        rw [mul_comm, ← comp_apply, ← functor.map_comp], congr } },
    { convert congr_arg (X.presheaf.map (hom_of_le _).op)
        (X.sheaf.obj_sup_iso_prod_eq_locus_inv_snd S U.1 ⟨⟨_ * _, _ * _⟩, this⟩) using 1,
      { delta Scheme.sheaf SheafedSpace.sheaf,
        simp only [← comp_apply (X.presheaf.map _) (X.presheaf.map _),
          ← functor.map_comp, ← op_comp],
        congr },
      { delta Scheme.sheaf SheafedSpace.sheaf,
        simp only [map_pow, map_mul, ← comp_apply, ← functor.map_comp, ← op_comp, mul_assoc,
          pow_add], erw hy₂, rw [← comp_apply, ← functor.map_comp], congr } } }
end

/-- If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.
This is known as the **Qcqs lemma** in [R. Vakil, *The rising sea*][RisingSea]. -/
lemma is_localization_basic_open_of_qcqs {X : Scheme} {U : opens X.carrier}
  (hU : is_compact U.1) (hU' : is_quasi_separated U.1)
  (f : X.presheaf.obj (op U)) :
  is_localization.away f (X.presheaf.obj (op $ X.basic_open f)) :=
begin
  constructor,
  { rintro ⟨_, n, rfl⟩,
    simp only [map_pow, subtype.coe_mk, ring_hom.algebra_map_to_algebra],
    exact is_unit.pow _ (RingedSpace.is_unit_res_basic_open _ f), },
  { intro z,
    obtain ⟨n, y, e⟩ := exists_eq_pow_mul_of_is_compact_of_is_quasi_separated X U hU hU' f z,
    refine ⟨⟨y, _, n, rfl⟩, _⟩,
    simpa only [map_pow, subtype.coe_mk, ring_hom.algebra_map_to_algebra, mul_comm z]
      using e.symm },
  { intros x y,
    rw [← sub_eq_zero, ← map_sub, ring_hom.algebra_map_to_algebra],
    simp_rw [← @sub_eq_zero _ _ (_ * x) (_ * y), ← mul_sub],
    generalize : x - y = z,
    split,
    { intro H,
      obtain ⟨n, e⟩ := exists_pow_mul_eq_zero_of_res_basic_open_eq_zero_of_is_compact X hU _ _ H,
      refine ⟨⟨_, n, rfl⟩, _⟩,
      simpa [mul_comm z] using e },
    { rintro ⟨⟨_, n, rfl⟩, e : f ^ n * z = 0⟩,
      rw [← ((RingedSpace.is_unit_res_basic_open _ f).pow n).mul_right_inj, mul_zero, ← map_pow,
        ← map_mul, e, map_zero] } }
end

end algebraic_geometry
