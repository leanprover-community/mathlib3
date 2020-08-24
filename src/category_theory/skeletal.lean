-- /-
-- Copyright (c) 2020 Bhavik Mehta. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Bhavik Mehta
-- -/
-- import category_theory.isomorphism_classes

-- /-!
-- # Skeleton of a category

-- Defines skeletal categories as categories in which any two isomorphic objects are equal.
-- -/

-- universes v₁ v₂ v₃ u₁ u₂ u₃

-- namespace category_theory

-- open category

-- variables (C : Type u₁) [category.{v₁} C]
-- variables (D : Type u₂) [category.{v₂} D]
-- variables (E : Type u₃) [category.{v₃} E]

-- /-- A category is skeletal if isomorphic objects are equal. -/
-- def skeletal : Prop := ∀ (X Y : C), is_isomorphic X Y → X = Y

-- variable (C)

-- /--
-- `is_skeleton_of C D F` says that `F : D ⥤ C` exhibits `D` as a skeletal full subcategory of `C`,
-- in particular `F` is a (strong) equivalence and `D` is skeletal.
-- -/
-- structure is_skeleton_of (F : D ⥤ C) :=
-- (skel : skeletal D)
-- (eqv : is_equivalence F)

-- local attribute [instance] is_isomorphic_setoid

-- def sparse_skeleton := quotient (is_isomorphic_setoid C)


-- namespace sparse_skeleton

-- instance preorder : preorder (sparse_skeleton C) :=
-- { le :=
--   begin
--     refine quotient.lift₂ (λ X Y, nonempty (X ⟶ Y)) _,
--     rintros _ _ _ _ ⟨i₁⟩ ⟨i₂⟩,
--     apply propext ⟨_, _⟩,
--     { rintro ⟨f⟩,
--       refine ⟨i₁.inv ≫ f ≫ i₂.hom⟩ },
--     { rintro ⟨g⟩,
--       refine ⟨i₁.hom ≫ g ≫ i₂.inv⟩ },
--   end,
--   le_refl :=
--   begin
--     refine quotient.ind (λ a, _),
--     exact ⟨𝟙 _⟩,
--   end,
--   le_trans :=
--   begin
--     intros _ _ _,
--     apply quotient.induction_on₃ a b c,
--     rintros _ _ _ ⟨f⟩ ⟨g⟩,
--     refine ⟨f ≫ g⟩,
--   end }

-- instance sparse {X Y : sparse_skeleton C} : subsingleton (X ⟶ Y) :=
-- ⟨by { rintros ⟨⟨f₁⟩⟩ ⟨⟨f₂⟩⟩, refl }⟩

-- instance subsingleton_iso {X Y : sparse_skeleton C} : subsingleton (X ≅ Y) :=
-- ⟨by { intros i₁ i₂, ext1, apply subsingleton.elim }⟩

-- variables {C} {D}

-- @[simps]
-- def map (F : C ⥤ D) : sparse_skeleton C ⥤ sparse_skeleton D :=
-- { obj := quotient.lift (quotient.mk ∘ F.obj) $
--     λ _ _ k, nonempty.elim k (quotient.sound ∘ nonempty.intro ∘ F.map_iso),
--   map := λ X Y, quotient.rec_on_subsingleton₂ X Y $
--            λ x y k, hom_of_le (nonempty.elim (le_of_hom k) (λ t, nonempty.intro (F.map t))) }

-- def map_comp (F : C ⥤ D) (G : D ⥤ E) : map (F ⋙ G) ≅ map F ⋙ map G :=
-- nat_iso.of_components (λ X, quotient.rec_on_subsingleton X (λ x, iso.refl _)) (by tidy)

-- def map_id : map (𝟭 C) ≅ 𝟭 _ :=
-- nat_iso.of_components (λ X, quotient.rec_on_subsingleton X (λ x, iso.refl _)) (by tidy)

-- def map_func {F₁ F₂ : C ⥤ D} (k : F₁ ⟶ F₂) : map F₁ ⟶ map F₂ :=
-- { app := λ X, quotient.rec_on_subsingleton X (λ x, ⟨⟨⟨k.app x⟩⟩⟩) }

-- def map_iso {F₁ F₂ : C ⥤ D} (h : F₁ ≅ F₂) : map F₁ ≅ map F₂ :=
-- { hom := map_func h.hom, inv := map_func h.inv }

-- variables [∀ X Y : C, subsingleton (X ⟶ Y)]

-- def functor.eq_of_iso {F₁ F₂ : D ⥤ C} (hC : skeletal C) (hF : F₁ ≅ F₂) : F₁ = F₂ :=
-- functor.ext (λ X, hC _ _ ⟨hF.app X⟩) (λ _ _ _, subsingleton.elim _ _)

-- lemma functor_skeletal (hC : skeletal C) : skeletal (D ⥤ C) :=
-- λ F₁ F₂ h, h.elim (functor.eq_of_iso hC)

-- lemma functor_sparse (F₁ F₂ : D ⥤ C) : subsingleton (F₁ ⟶ F₂) :=
-- ⟨λ α β, nat_trans.ext α β (funext (λ _, subsingleton.elim _ _))⟩

-- def iso_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≅ Y :=
-- { hom := f, inv := g }

-- lemma equiv_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≈ Y :=
-- ⟨iso_of_both_ways f g⟩

-- instance : partial_order (sparse_skeleton C) :=
-- { le_antisymm :=
--   begin
--     refine quotient.ind₂ _,
--     rintros _ _ ⟨f⟩ ⟨g⟩,
--     apply quotient.sound,
--     apply equiv_of_both_ways f g,
--   end,
--   ..category_theory.sparse_skeleton.preorder C }

-- lemma skeletal : skeletal (sparse_skeleton C) :=
-- begin
--   intros X Y,
--   apply quotient.induction_on₂ X Y,
--   rintros _ _ ⟨⟨⟨⟨f⟩⟩⟩, ⟨⟨⟨g⟩⟩⟩, _, _⟩,
--   apply quotient.sound,
--   apply equiv_of_both_ways f g,
-- end


-- end sparse_skeleton

-- def to_sparse_skeleton : C ⥤ sparse_skeleton C :=
-- { obj := quotient.mk,
--   map := λ X Y f, ⟨⟨⟨f⟩⟩⟩ }

-- end category_theory
