-- /-
-- Copyright (c) 2021 Jujian Zhang. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jujian Zhang
-- -/
-- import linear_algebra.tensor_product
-- import algebra.category.CommRing.basic
-- import algebra.category.Module.basic

-- /-!
-- # Extension of scalars
-- Given `R S : CommRing` and `f : R ⟶ S`, we can construct a functor `Module R ⥤ Module S` by
-- sending `M : Module R` to `M ⊗[R] S` and `l : M1 ⟶ M2` to `m ⊗ s ↦ l m ⊗ s`

-- -/

-- open_locale tensor_product

-- namespace extension_of_scalars

-- universe u

-- variables {R S : CommRing.{u}} (f : R ⟶ S) (M : Module R)
-- include f

-- /--
-- `R` can act on `S` via `f : R ⟶ S` by `r • s := f r * s`
-- -/
-- @[reducible] def has_scalar_R_S : has_scalar R S :=
-- ⟨λ r s, f r * s⟩

-- local attribute [instance] has_scalar_R_S

-- lemma  has_scalar_R_S.smul_def (r : R) (s : S) :
--   @has_scalar.smul _ _ (has_scalar_R_S f) r s = f r * s := rfl

-- /--
-- See above
-- -/
-- def mul_action_R_S : mul_action R S :=
-- { one_smul := λ s, by { unfold has_scalar.smul, rw [ring_hom.map_one, one_mul] },
--   mul_smul := λ r r' s, by { unfold has_scalar.smul, rw [ring_hom.map_mul, mul_assoc] },
--   ..(has_scalar_R_S f)}

-- local attribute [instance] mul_action_R_S

-- /--
-- This action is distributive
-- -/
-- def distrib_mul_action_R_S : distrib_mul_action R S :=
-- { smul_add := λ r s s', by { unfold has_scalar.smul, rw mul_add },
--   smul_zero := λ r, by { unfold has_scalar.smul, rw mul_zero },
--   ..(mul_action_R_S f)}

-- local attribute [instance] distrib_mul_action_R_S

-- /--
-- This action gives `S` an `R`-module strucutre
-- -/
-- def is_R_mod_S : module R S :=
-- { add_smul := λ r r' s, by { unfold has_scalar.smul, rw [ring_hom.map_add, add_mul] },
--   zero_smul := λ s, by { unfold has_scalar.smul, rw [ring_hom.map_zero, zero_mul] },
--   ..(distrib_mul_action_R_S f) }

-- local attribute [instance] is_R_mod_S

-- include M
-- local notation M `⊗` S := @tensor_product R _ M S _ _ _ (is_R_mod_S f)

-- /--
-- Since `S` has an `R`-module structure, `M ⊗[R] S` can be given an `S`-module structure.
-- The scalar multiplication is defined by `s • (m ⊗ s') := m ⊗ (s * s')`
-- -/
-- @[reducible] def has_scalar_S_M_tensor_S : has_scalar S (M ⊗ S) :=
-- { smul := λ s', @tensor_product.lift R _ M S (M ⊗ S) _ _ _ _ (is_R_mod_S f) _
--   { to_fun := λ m,
--     { to_fun := λ s, @tensor_product.tmul R _ M S _ _ _ (is_R_mod_S f) m (s * s'),
--       map_add' := λ x y, by rw [add_mul, tensor_product.tmul_add],
--       map_smul' := λ x y, begin
--         rw [ring_hom.id_apply],
--         rw [has_scalar_R_S.smul_def f x, mul_assoc, ←has_scalar_R_S.smul_def],
--         erw @tensor_product.tmul_smul R _ R _ M S _ _ _ (is_R_mod_S f) _ _
--           (distrib_mul_action_R_S f) _ x m (y * s'),

--       end },
--     map_add' := λ _ _, begin
--       ext s, simp only [linear_map.coe_mk, linear_map.add_apply],
--       rw tensor_product.add_tmul
--     end,
--     map_smul' := λ _ _, begin
--       ext s, simp only [linear_map.smul_apply, ring_hom.id_apply, linear_map.coe_mk],
--       rw @tensor_product.smul_tmul R _ R _ M S _ _ _ (is_R_mod_S f) _ (distrib_mul_action_R_S f) _,
--       rw tensor_product.tmul_smul
--     end } }

-- local attribute [instance] has_scalar_S_M_tensor_S

-- lemma has_scalar_S_M_tensor_S.smul_pure_tensor (s s' : S) (m : M) :
--   s • (@tensor_product.tmul R _ M S _ _ _ (is_R_mod_S f) m s') =
--   @tensor_product.tmul R _ M S _ _ _ (is_R_mod_S f) m (s * s') :=
-- begin
--   unfold has_scalar.smul, simp only [tensor_product.lift.tmul, linear_map.coe_mk],
--   rw mul_comm,
-- end

-- /--
-- See above
-- -/
-- def mul_action_S_M_tensor_S : mul_action S (M ⊗ S) :=
-- { one_smul := λ x, begin
--     apply @tensor_product.induction_on R _ M S _ _ _ (is_R_mod_S f) _ x;
--     unfold has_scalar.smul,
--     { simp only [map_zero] },
--     { intros m s, simp only [tensor_product.lift.tmul, linear_map.coe_mk, mul_one], },
--     { intros x y ihx ihy, simp only [map_add, ihx, ihy] },
--   end,
--   mul_smul := λ s s' x, begin
--     apply @tensor_product.induction_on R _ M S _ _ _ (is_R_mod_S f) _ x;
--     unfold has_scalar.smul,
--     { simp only [map_zero] },
--     { intros m s'', simp only [tensor_product.lift.tmul, linear_map.coe_mk],
--       rw [mul_comm s s', mul_assoc], },
--     { intros x y ihx ihy,
--       conv_lhs { rw [map_add] },
--       conv_rhs { rw [map_add, map_add, ←ihx, ←ihy], } }
--   end,
--   ..(has_scalar_S_M_tensor_S f M) }

-- local attribute [instance] mul_action_S_M_tensor_S

-- private lemma distrib_mul_action_S_M_tensor_S.smul_zero (s : S) : s • (0 : M ⊗ S) = 0 :=
-- begin
--   unfold has_scalar.smul,
--   simp only [map_zero],
-- end

-- /--
-- See above
-- -/
-- def distrib_mul_action_S_M_tensor_S : distrib_mul_action S (M ⊗ S) :=
-- { smul_zero := distrib_mul_action_S_M_tensor_S.smul_zero f M,
--   smul_add := λ r x y, begin
--     apply @tensor_product.induction_on R _ M S _ _ _ (is_R_mod_S f) _ x,
--     { rw [zero_add, distrib_mul_action_S_M_tensor_S.smul_zero, zero_add] },
--     { intros m s, unfold has_scalar.smul, simp only [map_add] },
--     { intros z z' ihz ihz',
--       unfold has_scalar.smul, simp only [map_add] }
--   end }

-- /--
-- See above
-- -/
-- @[reducible] def module : Module S :=
-- { carrier := M ⊗ S,
--   is_module :=
--     { add_smul := λ s s' x, begin
--         apply @tensor_product.induction_on R _ M S _ _ _ (is_R_mod_S f) _ x,
--         { rw [distrib_mul_action_S_M_tensor_S.smul_zero,
--               distrib_mul_action_S_M_tensor_S.smul_zero,
--               distrib_mul_action_S_M_tensor_S.smul_zero, zero_add] },
--         { rintros m s'',
--           rw [has_scalar_S_M_tensor_S.smul_pure_tensor,
--               has_scalar_S_M_tensor_S.smul_pure_tensor,
--               has_scalar_S_M_tensor_S.smul_pure_tensor, add_mul,
--               tensor_product.tmul_add] },
--         { rintros x y ihx ihy,
--           conv_lhs { rw [smul_add, ihx, ihy] },
--           have : s • x + s' • x + (s • y + s' • y) = s • x + s • y + (s' • x + s' • y),
--           { rw [add_assoc, add_assoc],
--             apply congr_arg2 (+), refl,
--             rw [←add_assoc, ←add_assoc],
--             apply congr_arg2 (+), rw add_comm, refl, },
--           erw this,
--           conv_rhs { rw [smul_add, smul_add] },
--           refl }
--       end,
--       zero_smul := λ x, begin
--         apply @tensor_product.induction_on R _ M S _ _ _ (is_R_mod_S f) _ x,
--         { rw smul_zero },
--         { rintros m s,
--           rw [has_scalar_S_M_tensor_S.smul_pure_tensor, zero_mul, tensor_product.tmul_zero], },
--         { rintros x y ihx ihy, rw [smul_add, ihx, ihy, zero_add] }
--       end,
--       ..(distrib_mul_action_S_M_tensor_S f M) } }

-- omit M
-- /--
-- Extension of scalars is a functor where an `R`-module `M` is sent to `M ⊗ S` and
-- `l : M1 ⟶ M2` is sent to `m ⊗ s ↦ l m ⊗ s`
-- -/
-- @[reducible] def map {M1 M2 : Module R} (l : M1 ⟶ M2) : (module f M1) ⟶ (module f M2) :=
-- { to_fun := @tensor_product.lift R _ M1 S (M2 ⊗ S) _ _ _ _ (is_R_mod_S f) _
--        {to_fun := λ m : M1,
--         { to_fun := λ (s : ↥S), @tensor_product.tmul R _ M2 S _ _ _ (is_R_mod_S f) (l m) s,
--           map_add' := λ s s', by rw tensor_product.tmul_add,
--           map_smul' := λ r s, by rw [ring_hom.id_apply, tensor_product.tmul_smul] },
--         map_add' := λ m m', begin
--           ext s, simp only [map_add, linear_map.coe_mk, linear_map.add_apply],
--           rw tensor_product.add_tmul
--         end,
--         map_smul' := λ s m, begin
--           ext s,
--           simp only [linear_map.smul_apply, ring_hom.id_apply,
--             linear_map.coe_mk, linear_map.map_smulₛₗ],
--           rw @tensor_product.smul_tmul R _ R _ M2 S _ _ _ (is_R_mod_S f) _
--             (distrib_mul_action_R_S f),
--           rw tensor_product.tmul_smul
--         end},
--   map_add' := λ x y, by rw map_add,
--   map_smul' := λ s x, begin
--     apply @tensor_product.induction_on R _ M1 S _ _ _ (is_R_mod_S f) _ x,
--     { rw [smul_zero, map_zero, smul_zero], },
--     { rintros m s',
--       rw [has_scalar_S_M_tensor_S.smul_pure_tensor, ring_hom.id_apply,
--         tensor_product.lift.tmul, tensor_product.lift.tmul, linear_map.coe_mk, linear_map.coe_mk,
--         has_scalar_S_M_tensor_S.smul_pure_tensor], },
--     { rintros x y ihx ihy,
--       rw [ring_hom.id_apply] at ihx ihy ⊢,
--       rw [smul_add, linear_map.map_add, ihx, ihy, linear_map.map_add, smul_add], }
--   end }

-- /--
-- The functor extension of scalars
-- -/
-- def _root_.extension_of_scalars : Module.{u} R ⥤ Module.{u} S :=
-- { obj := module f,
--   map := λ M1 M2 l, map f l,
--   map_id' := λ M, begin
--     ext x, rw [map, Module.id_apply],
--     apply @tensor_product.induction_on R _ M S _ _ _ (is_R_mod_S f) _ x,
--     { rw map_zero },
--     { intros m s, rw [linear_map.coe_mk, tensor_product.lift.tmul], refl, },
--     { intros x y ihx ihy, rw [linear_map.coe_mk] at ihx ihy ⊢,
--       rw [map_add, ihx, ihy], }
--   end,
--   map_comp' := λ M1 M2 M3 g h, begin
--     ext x,
--     rw [map, map, map, linear_map.coe_mk, category_theory.comp_apply,
--       linear_map.coe_mk, linear_map.coe_mk],
--     apply @tensor_product.induction_on R _ _ S _ _ _ (is_R_mod_S f) _ x,
--     { rw [map_zero, map_zero, map_zero], },
--     { rintros m s, rw [tensor_product.lift.tmul, tensor_product.lift.tmul], refl, },
--     { rintros x y ihx ihy,
--       rw [map_add, ihx, ihy, map_add, map_add], }
--   end }

-- end extension_of_scalars
