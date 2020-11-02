/-
Copyright (c) 2020 Bhavik Mehta, E. W. Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/

import category_theory.sites.grothendieck
import category_theory.sites.pretopology
import category_theory.sites.sheaf
import category_theory.full_subcategory
import category_theory.types

universes v u
namespace category_theory

open category_theory category limits sieve classical

variables {C : Type u} [category.{v} C]

namespace sheaf
namespace grothendieck_topology

variables {P : Cᵒᵖ ⥤ Type v}
variables {X Y : C} {S : sieve X} {R : presieve X}
variables (J J₂ : grothendieck_topology C)

lemma is_sheaf_for_bind (P : Cᵒᵖ ⥤ Type v) (U : sieve X)
  (B : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄, U f → sieve Y)
  (hU : is_sheaf_for P U)
  (hB : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), is_sheaf_for P (B hf))
  (hB' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f) ⦃Z⦄ (g : Z ⟶ Y), is_separated_for P ((B hf).pullback g)) :
  is_sheaf_for P (sieve.bind U B) :=
begin
  intros s hs,
  let y : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), family_of_elements P (B hf) :=
    λ Y f hf Z g hg, s _ (presieve.bind_comp _ _ hg),
  have hy : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).consistent,
  { intros Y f H Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm,
    apply hs,
    apply reassoc_of comm },
  let t : family_of_elements P U,
  { intros Y f hf,
    apply (hB hf).amalgamate (y hf) (hy hf) },
  have ht : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), is_amalgamation_for (y hf) (t f hf),
  { intros Y f hf,
    apply (hB hf).is_amalgamation_for _ },
  have hT : t.consistent,
  { rw is_sieve_consistent_iff,
    intros Z W f h hf,
    apply (hB (U.downward_closed hf h)).is_separated_for.ext,
    intros Y l hl,
    apply (hB' hf (l ≫ h)).ext,
    intros M m hm,
    have : (bind ⇑U B) (m ≫ l ≫ h ≫ f),
    { have : bind U B _ := presieve.bind_comp f hf hm,
      simpa using this },
    transitivity s (m ≫ l ≫ h ≫ f) this,
    { have := ht (U.downward_closed hf h) _ ((B _).downward_closed hl m),
      rw [op_comp, functor_to_types.map_comp_apply] at this,
      rw this,
      change s _ _ = s _ _,
      simp },
    { have : s _ _ = _ := (ht hf _ hm).symm,
      simp only [assoc] at this,
      rw this,
      simp } },
  refine ⟨hU.amalgamate t hT, _, _⟩,
  { rintro Z _ ⟨Y, f, g, hg, hf, rfl⟩,
    rw [op_comp, functor_to_types.map_comp_apply, is_sheaf_for.valid_glue _ _ _ hg],
    apply ht hg _ hf },
  { intros y hy,
    apply hU.is_separated_for.ext,
    intros Y f hf,
    apply (hB hf).is_separated_for.ext,
    intros Z g hg,
    rw [←functor_to_types.map_comp_apply, ←op_comp, hy _ (presieve.bind_comp _ _ hg),
        hU.valid_glue _ _ hf, ht hf _ hg] }
end

lemma is_sheaf_for_trans (P : Cᵒᵖ ⥤ Type v) (R S : sieve X)
  (hR : is_sheaf_for P R)
  (hR' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : S f), is_separated_for P (R.pullback f))
  (hS : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : R f), is_sheaf_for P (S.pullback f)) :
  is_sheaf_for P S :=
begin
  have : (bind ⇑R (λ (Y : C) (f : Y ⟶ X) (hf : R f), pullback f S) : presieve X) ≤ S,
  { rintros Z f ⟨W, f, g, hg, (hf : S _), rfl⟩,
    apply hf },
  apply is_sheaf_for_subsieve_aux P this,
  apply is_sheaf_for_bind _ _ _ hR hS,
  { intros Y f hf Z g,
    dsimp,
    rw ← pullback_comp,
    apply (hS (R.downward_closed hf _)).is_separated_for },
  { intros Y f hf,
    have : (sieve.pullback f (bind R (λ T (k : T ⟶ X) (hf : R k), pullback k S))) = R.pullback f,
    { ext Z g,
      split,
      { rintro ⟨W, k, l, hl, _, comm⟩,
        rw [mem_pullback, ← comm],
        simp [hl] },
      { intro a,
        refine ⟨Z, 𝟙 Z, _, a, _⟩,
        simp [hf] } },
    rw this,
    apply hR' hf },
end

/-- Construct the finest Grothendieck topology for which the given presheaf is a sheaf. -/
def finest_topology_single (P : Cᵒᵖ ⥤ Type v) : grothendieck_topology C :=
{ sieves := λ X S, ∀ Y (f : Y ⟶ X), is_sheaf_for P (S.pullback f),
  top_mem' := λ X Y f,
  begin
    rw sieve.pullback_top,
    exact is_sheaf_for_top_sieve P,
  end,
  pullback_stable' := λ X Y S f hS Z g,
  begin
    rw ← pullback_comp,
    apply hS,
  end,
  transitive' := λ X S hS R hR Z g,
  begin
    refine is_sheaf_for_trans P (pullback g S) _ (hS Z g) _ _,
    { intros Y f hf,
      rw ← pullback_comp,
      apply (hS _ _).is_separated_for },
    { intros Y f hf,
      have := hR hf _ (𝟙 _),
      rw [pullback_id, pullback_comp] at this,
      apply this },
  end }

/-- Construct the finest Grothendieck topology for which the given presheaves are sheaves. -/
def finest_topology (Ps : set (Cᵒᵖ ⥤ Type v)) : grothendieck_topology C :=
Inf (finest_topology_single '' Ps)

lemma sheaf_for_finest_topology (Ps : set (Cᵒᵖ ⥤ Type v)) :
  P ∈ Ps → is_sheaf (finest_topology Ps) P :=
begin
  intros h X S hS,
  simpa using hS _ ⟨⟨_, _, ⟨_, h, rfl⟩, rfl⟩, rfl⟩ _ (𝟙 _),
end

lemma is_finest_topology (Ps : set (Cᵒᵖ ⥤ Type v)) (J : grothendieck_topology C)
  (hJ : ∀ P ∈ Ps, is_sheaf J P) : J ≤ finest_topology Ps :=
begin
  intros X S hS,
  rintro _ ⟨⟨_, _, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩,
  intros Y f,
  exact hJ P hP (S.pullback f) (J.pullback_stable f hS),
end

def canonical_topology : grothendieck_topology C :=
finest_topology (set.range yoneda.obj)

-- def matching_family (P : Cᵒᵖ ⥤ Type v) (S : sieve X) : Type (max u v) :=
-- S.functor ⟶ P

-- def amalgamation {P : Cᵒᵖ ⥤ Type v} {S : sieve X} (γ : matching_family P S) :=
-- {α : yoneda.obj X ⟶ P // S.functor_inclusion ≫ α = γ}

-- @[derive subsingleton]
-- def sheaf_condition_at (S : sieve X) (P : Cᵒᵖ ⥤ Type v) : Type (max u v) :=
-- Π (γ : matching_family P S), unique (amalgamation γ)

-- def sheaf_condition_at_top (P : Cᵒᵖ ⥤ Type v) : sheaf_condition_at (⊤ : sieve X) P :=
-- λ γ,
-- begin
--   refine ⟨⟨⟨inv (⊤:sieve X).functor_inclusion ≫ γ, _⟩⟩, _⟩,
--   { simp },
--   { rintro ⟨a, ha⟩,
--     apply subtype.ext,
--     simp [ha] }
-- end

-- @[derive subsingleton]
-- def sheaf_condition (P : Cᵒᵖ ⥤ Type v) : Type (max u v) :=
-- Π (X : C) (S ∈ J X), sheaf_condition_at S P

-- def canonical_map (P : Cᵒᵖ ⥤ Type v) (S : sieve X) : (yoneda.obj X ⟶ P) → (S.functor ⟶ P) :=
-- λ f, S.functor_inclusion ≫ f

-- def sheaf_condition2 (P : Cᵒᵖ ⥤ Type v) : Prop :=
-- ∀ X (S : sieve X), S ∈ J X → function.bijective (canonical_map P S)

-- -- noncomputable def sheaf_condition2_equiv (P : Cᵒᵖ ⥤ Type v) : sheaf_condition J P ≃ sheaf_condition2 J P :=
-- -- { to_fun := λ t X S hS,
-- --   begin
-- --     split,
-- --     { intros α₁ α₂ hα,
-- --       exact subtype.ext_iff.1 (((t X S _ hS).2 ⟨α₁, hα⟩).trans ((t X S _ hS).2 ⟨α₂, rfl⟩).symm) },
-- --     { intros γ,
-- --       exact ⟨_, (t X S γ hS).1.1.2⟩ }
-- --   end,
-- --   inv_fun := λ t X S γ hS,
-- --   begin
-- --     specialize t X S hS,
-- --     rw function.bijective_iff_has_inverse at t,
-- --     choose t ht₁ ht₂ using t,
-- --     refine ⟨⟨⟨t γ, ht₂ γ⟩⟩, λ a, _⟩,
-- --     cases a with a ha,
-- --     apply subtype.ext,
-- --     dsimp,
-- --     rw [← ht₁ a, ← ha],
-- --     refl,
-- --   end

-- -- }

-- def matching_family' (P : Cᵒᵖ ⥤ Type v) {c : C} (S : sieve c) :=
-- {x : Π {d : C} {f : d ⟶ c}, S.arrows f → P.obj (opposite.op d) //
--  ∀ {d e : C} (f : d ⟶ c) (g : e ⟶ d) (h : S.arrows f), x (S.downward_closed h g) = P.map g.op (x h)}

-- def amalgamation' {P : Cᵒᵖ ⥤ Type v} {c : C} {S : sieve c} (γ : matching_family' P S) :=
-- {y : P.obj (opposite.op c) // ∀ {d : C} (f : d ⟶ c) (hf : S.arrows f), P.map f.op y = γ.1 hf}

-- @[derive subsingleton]
-- def sheaf_condition' (P : Cᵒᵖ ⥤ Type v) : Type (max u v) :=
-- Π (c : C) (S : sieve c) (γ : matching_family' P S), S ∈ J c → unique (amalgamation' γ)

-- def matching_family'_equiv_matching_family (P : Cᵒᵖ ⥤ Type v) :
--   matching_family' P S ≃ matching_family P S :=
-- { to_fun := λ x, ⟨λ _ t, x.1 t.2, λ c c' f, funext $ λ t, x.2 _ _ t.2⟩,
--   inv_fun := λ x, ⟨λ d f hf, x.app _ ⟨f, hf⟩, λ d d' f g h, congr_fun (x.2 g.op) ⟨f, h⟩⟩,
--   left_inv := λ _, subtype.ext $ funext $ λ _, funext $ λ _, funext $ λ _, rfl,
--   right_inv := λ _, by { ext _ ⟨_, _⟩, refl } }

-- def amalgamation'_equiv_amalgamation (P : Cᵒᵖ ⥤ Type v) (x : matching_family' P S) :
--   amalgamation (matching_family'_equiv_matching_family P x) ≃ (amalgamation' x) :=
-- { to_fun := λ γ,
--   { val := γ.1.app _ (𝟙 X),
--     property := λ d f hf,
--     begin
--       have := congr_fun (γ.1.naturality f.op) (𝟙 _),
--       dsimp at this,
--       erw ← this,
--       rw comp_id,
--       have q := congr_arg (λ t, nat_trans.app t (opposite.op d)) γ.2,
--       dsimp at q,
--       have := congr_fun q ⟨f, hf⟩,
--       exact this,
--     end },
--   inv_fun := λ γ,
--   { val :=
--     { app := λ c f, P.map f.op γ.1,
--       naturality' := λ c c' f, funext $ λ g, functor_to_types.map_comp_apply P g.op f γ.1 },
--     property :=
--     begin
--       ext c ⟨f, hf⟩,
--       apply γ.2,
--     end },
--   left_inv :=
--   begin
--     rintro ⟨γ₁, γ₂⟩,
--     ext d f,
--     dsimp,
--     rw ← functor_to_types.naturality _ _ γ₁ f.op (𝟙 X),
--     dsimp,
--     simp,
--   end,
--   right_inv :=
--   begin
--     intro γ,
--     ext1,
--     apply functor_to_types.map_id_apply,
--   end }

-- def sheaf'_equiv_sheaf (P : Cᵒᵖ ⥤ Type v) :
--   sheaf_condition J P ≅ sheaf_condition' J P :=
-- { hom :=
--   begin
--     intros h c S γ hS,
--     apply equiv.unique (amalgamation'_equiv_amalgamation _ _).symm,
--     apply h _ _ hS,
--   end,
--   inv :=
--   begin
--     intros h c S hS γ,
--     haveI := h _ _ ((matching_family'_equiv_matching_family P).symm γ) hS,
--     have := equiv.unique (amalgamation'_equiv_amalgamation P ((matching_family'_equiv_matching_family P).symm γ)),
--     simpa using this,
--   end }

-- def finest_topology_sieves (P : Cᵒᵖ ⥤ Type v) : Π (X : C), set (sieve X) :=
-- λ X S, ∀ Y (f : Y ⟶ X), nonempty (sheaf_condition_at (S.pullback f) P)

-- def aux_map {Z : C} (S : sieve X) (α : Z ⟶ Y) (f : Y ⟶ X) :
--   (S.pullback (α ≫ f)).functor ⟶ (S.pullback f).functor :=
-- { app := λ T z, ⟨z.1 ≫ α, by simpa using z.2⟩ }.

-- def finest_topology (F : Cᵒᵖ ⥤ Type v) : grothendieck_topology C :=
-- { sieves := finest_topology_sieves F,
--   top_mem' := λ X Y f,
--   begin
--     rw pullback_top,
--     refine ⟨sheaf_condition_at_top _⟩,
--   end,
--   pullback_stable' := λ X Y S f hS Z g,
--   begin
--     rw ← pullback_comp,
--     apply hS _,
--   end,
--   transitive' := λ U S hS S' t,
--   begin
--     intros W f,
--     cases hS _ f with hfS,
--     refine ⟨λ φ, _⟩,
--     let ψ : (S.pullback f).functor ⟶ F,
--     { refine ⟨_, _⟩,
--       { intros V α,
--         have q := t α.2 _ (𝟙 _),
--         rw pullback_id at q,
--         apply (classical.choice q (aux_map S' α.1 f ≫ φ)).1.1.1.app _ (𝟙 _) },
--       { intros V₁ V₂ k,
--         sorry,
--         -- ext1 α,
--         -- dsimp,
--         -- have q₁ := t α.2 _ (𝟙 _),
--         -- rw pullback_id at q₁,
--         -- let z₁ := (classical.choice q₁ (aux_map S' α.1 f ≫ φ)).1.1.1,
--         -- have := k.unop ≫ α.1,
--         -- -- have q₂ := t (S.downward_closed α.2 k.unop) _ (𝟙 _),
--         -- -- rw pullback_id at q₂,
--         -- have q₂ : nonempty (sheaf_condition_at (pullback (((pullback f S).functor.map k α).1 ≫ f) S') F),
--         --   dsimp [sieve.functor],
--         --   rw assoc,
--         --   have q₂ := t (S.downward_closed α.2 k.unop) _ (𝟙 _),
--         --   rw pullback_id at q₂,
--         --   apply q₂,
--         -- let z₂ := (classical.choice q₂ (aux_map S' ((S.pullback f).functor.map k α).1 f ≫ φ)).1.1.1,
--         -- change z₂.app V₂ (𝟙 _) = F.map k (z₁.app V₁ (𝟙 _)),
--         -- have := (classical.choice q₂ (aux_map S' ((S.pullback f).functor.map k α).1 f ≫ φ)).1.1.2,
--       }
--     },
--     refine ⟨⟨⟨(classical.choice (hS _ f) ψ).1.1.1, _⟩⟩, _⟩,
--     have := (classical.choice (hS _ f) ψ).1.1.2,
--   end
-- }

-- variables (C J)

-- structure Sheaf :=
-- (P : Cᵒᵖ ⥤ Type v)
-- (sheaf_cond : sheaf_condition J P)

-- instance : category (Sheaf C J) := induced_category.category Sheaf.P

end grothendieck_topology
end sheaf

end category_theory
