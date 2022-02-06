-- import algebra.homology.exact
-- import category_theory.abelian.pseudoelements

-- open category_theory
-- open category_theory.limits


-- noncomputable theory

-- universes v u

-- variables {C : Type u} [category.{v} C]
-- variables [has_zero_morphisms C] [has_images C] [has_kernels C] [has_cokernels C]

-- def coker_to_im {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [exact f g] :
--   cokernel f ⟶ image_subobject g :=
-- cokernel.desc _ (factor_thru_image_subobject g) begin
--   have eq1 : f ≫ g = 0 := exact.w,
--   rw ←image_subobject_arrow_comp g at eq1,
--   rw [←category.assoc] at eq1,
--   have eq2 : (0 : X ⟶ Z) = 0 ≫ (image_subobject g).arrow,
--   { simp only [zero_comp], },
--   rw eq2 at eq1,
--   rwa cancel_mono (image_subobject g).arrow at eq1,
-- end

-- lemma coker_to_im.aux2 {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [exact f g] :
--   cokernel.π _ ≫ (coker_to_im f g) = factor_thru_image_subobject g :=
-- begin
--   simp only [coker_to_im, cokernel.π_desc],
-- end

-- lemma coker_to_im.mono [abelian C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [exact f g] :
--   mono (coker_to_im f g) :=
-- begin
--   sorry
-- end
