import topology.sheaves.presheaf
import topology.sheaves.stalks
import algebra.category.BundledModule.basic
import algebra.category.Group.limits

open Top topological_space opposite category_theory
-- open_locale tensor_product

namespace presheaf_of_module

section defs

variables {X : Top} (𝓞 : presheaf CommRing X)

structure presheaf_of_module :=
(self : presheaf BundledModule X)
(agree : self ⋙ BundledModule.forget_to_Ring ⋙ forget Ring = 𝓞 ⋙ forget CommRing)

structure sheaf_of_module extends presheaf_of_module 𝓞 :=
(is_sheaf : presheaf.is_sheaf (self ⋙ BundledModule.forget_to_Ab))

end defs

section restriction_by

variables {X : Top} {𝓞1 𝓞2 : presheaf CommRing X} (f : 𝓞1 ⟶ 𝓞2)
include f

def restriction_by.obj (𝓕 : presheaf_of_module 𝓞2) : presheaf_of_module 𝓞1 :=
{ self := { obj := λ U, ⟨⟨(𝓞1.obj U)⟩, begin
  refine (@restriction_of_scalar.functor ⟨(𝓞1.obj U)⟩ ⟨𝓞2.obj U⟩ (f.app U)).obj
    { carrier := (𝓕.self.obj U).M, is_module := begin
      convert (𝓕.self.obj U).M.is_module,

    end },
end⟩,
    map := _,
    map_id' := _,
    map_comp' := _ },
  agree := begin
    have eq1 := 𝓕.agree,
  end }

end restriction_by

end presheaf_of_module


-- namespace presheaf_of_module

-- section defs
-- variables {X : Top} (𝓞 : presheaf CommRing X)

-- structure core :=
-- (self : presheaf Ab X)
-- [is_module : ∀ (U : opens X), module (𝓞.obj (op U)) (self.obj (op U))]

-- attribute [instance] core.is_module

-- def is_module_UV (𝓜 : presheaf_of_module.core 𝓞) {U V : opens X} (inc : op U ⟶ op V) :
--   module (𝓞.obj (op U)) (𝓜.self.obj (op V)) :=
-- @restriction_of_scalars.is_module (𝓞.obj (op U)) (𝓞.obj (op V)) ⟨𝓜.self.obj (op V)⟩ (𝓞.map inc)

-- local attribute [instance] is_module_UV

-- def has_scalar_UV (𝓜 : presheaf_of_module.core 𝓞) {U V : opens X} (inc : op U ⟶ op V) :
--   has_scalar (𝓞.obj (op U)) (𝓜.self.obj (op V)) :=
-- @restriction_of_scalars.has_scalar (𝓞.obj (op U)) (𝓞.obj (op V)) ⟨𝓜.self.obj (op V)⟩ (𝓞.map inc)

-- local attribute [instance] has_scalar_UV

-- structure _root_.presheaf_of_module extends presheaf_of_module.core 𝓞 :=
-- (compatible : ∀ {U V : opens X} (inc : op U ⟶ op V) (r : 𝓞.obj (op U)) (m : self.obj (op U)),
--   self.map inc (r • m) = 𝓞.map inc r • self.map inc m)

-- variable {𝓞}
-- lemma is_linear_map (𝓕 : presheaf_of_module 𝓞) {U V : opens X} (inc : op U ⟶ op V) :
--   @@is_linear_map (𝓞.obj (op U)) _ _ _ _ (is_module_UV 𝓞 _ inc) (𝓕.self.map inc) :=
-- { map_add := map_add _,
--   map_smul := 𝓕.compatible inc }

-- def to_linear_map (𝓕 : presheaf_of_module 𝓞) {U V : opens X} (inc : op U ⟶ op V) :
--   (⟨𝓕.self.obj (op U)⟩ : Module (𝓞.obj (op U))) ⟶
--   ({ carrier := 𝓕.self.obj (op V), is_module := is_module_UV 𝓞 _ inc } : Module (𝓞.obj (op U))) :=
-- { to_fun := 𝓕.self.map inc,
--   map_add' := by simp,
--   map_smul' := 𝓕.compatible inc }

-- @[ext] structure morphism (𝓕1 𝓕2 : presheaf_of_module 𝓞) :=
-- (to_fun : 𝓕1.self ⟶ 𝓕2.self)
-- (compatible : ∀ {U V : opens X} (inc : op U ⟶ op V) (r : 𝓞.obj (op U)) (m : 𝓕1.self.obj (op U)),
--   to_fun.app _ (r • m) = r • to_fun.app _ m )

-- lemma morphism.is_linear {𝓕1 𝓕2 : presheaf_of_module 𝓞} (φ : morphism 𝓕1 𝓕2)
--   {U V : opens X} (inc : op U ⟶ op V) :
--   _root_.is_linear_map (𝓞.obj (op U)) (φ.to_fun.app (op U)) :=
-- { map_add := map_add _,
--   map_smul := morphism.compatible _ inc }

-- def morphism.comp {𝓕1 𝓕2 𝓕3 : presheaf_of_module 𝓞}
--   (f12 : morphism 𝓕1 𝓕2) (f23 : morphism 𝓕2 𝓕3) : morphism 𝓕1 𝓕3 :=
-- { to_fun := f12.to_fun ≫ f23.to_fun,
--   compatible := λ U V inc r m, begin
--     simp only [nat_trans.comp_app, comp_apply, f12.compatible inc, f23.compatible inc],
--   end }

-- lemma morphism.comp_to_fun {𝓕1 𝓕2 𝓕3 : presheaf_of_module 𝓞}
--   (f12 : morphism 𝓕1 𝓕2) (f23 : morphism 𝓕2 𝓕3) :
--   (morphism.comp f12 f23).to_fun = f12.to_fun ≫ f23.to_fun := rfl

-- def morphism.id (𝓕 : presheaf_of_module 𝓞) : morphism 𝓕 𝓕 :=
-- { to_fun := 𝟙 _,
--   compatible := λ U V inc r m, begin
--     simp only [nat_trans.id_app, id_apply],
--   end }

-- instance : category (presheaf_of_module 𝓞) :=
-- { hom := morphism,
--   id := morphism.id,
--   comp := λ _ _ _ f12 f23, morphism.comp f12 f23,
--   id_comp' := λ _ _ _, begin
--     ext U_op x,
--     simpa [morphism.comp_to_fun, comp_app],
--   end,
--   comp_id' := λ _ _ _, begin
--     ext U_op x,
--     simpa [morphism.comp_to_fun, comp_app],
--   end,
--   assoc' := λ _ _ _ _ _ _ _, begin
--     ext U_op x,
--     simp [morphism.comp_to_fun, comp_app],
--   end }

-- variable (𝓞)
-- structure _root_.sheaf_of_module extends _root_.presheaf_of_module 𝓞 :=
-- (is_sheaf : presheaf.is_sheaf self)

-- instance : category (sheaf_of_module 𝓞) :=
-- { hom := λ 𝓕1 𝓕2, morphism 𝓕1.1 𝓕2.1,
--   id := λ _, morphism.id _,
--   comp := λ _ _ _ f12 f23, morphism.comp f12 f23,
--   id_comp' := λ _ _ _, begin
--     ext U_op x,
--     simpa [morphism.comp_to_fun, comp_app],
--   end,
--   comp_id' := λ _ _ _, begin
--     ext U_op x,
--     simpa [morphism.comp_to_fun, comp_app],
--   end,
--   assoc' := λ _ _ _ _ _ _ _, begin
--     ext U_op x,
--     simp [morphism.comp_to_fun, comp_app],
--   end }

-- end defs

-- section restriction

-- variables {X : Top} {𝓞1 𝓞2 : presheaf CommRing X} (f : 𝓞1 ⟶ 𝓞2)
-- include f

-- def restriction_by.obj (𝓕 : presheaf_of_module 𝓞2) : presheaf_of_module 𝓞1 :=
-- { self := 𝓕.self,
--   is_module := λ U, @restriction_of_scalars.is_module (𝓞1.obj (op U)) (𝓞2.obj (op U))
--       ⟨𝓕.self.obj (op U)⟩ (f.app (op U)),
--   compatible := λ U V inc r m, begin
--     erw [𝓕.compatible inc, (ring_hom.congr_fun (f.naturality inc) r).symm],
--     refl,
--   end }

-- local notation f `^*` 𝓕 := restriction_by.obj f 𝓕

-- def restriction_by.map {𝓕1 𝓕2 : presheaf_of_module 𝓞2} (φ : 𝓕1 ⟶ 𝓕2) :
--   (f^*𝓕1) ⟶ (f^*𝓕2) :=
-- { to_fun := φ.to_fun,
--   compatible := λ U V inc r m, begin
--     erw [φ.compatible inc],
--     refl,
--   end }
-- local notation f `^*→` φ := restriction_by.map f φ

-- def restriction_by.functor : presheaf_of_module 𝓞2 ⥤ presheaf_of_module 𝓞1 :=
-- { obj := λ 𝓕, f ^* 𝓕,
--   map := λ _ _ φ, f ^*→ φ,
--   map_id' := λ _, rfl,
--   map_comp' := λ _ _ _ _ _, rfl }

-- end restriction

-- section extension

-- variables {X : Top} {𝓞1 𝓞2 : presheaf CommRing X} (f : 𝓞1 ⟶ 𝓞2)
-- include f

-- variable (𝓕 : presheaf_of_module 𝓞1)
-- include 𝓕

-- def test (U V : opens X) (inc : op U ⟶ op V) :
--   linear_map (𝓞2.map inc) ((extension_of_scalars (f.app (op U))).obj ⟨𝓕.self.obj (op U)⟩)
--     ((extension_of_scalars (f.app (op V))).obj ⟨𝓕.self.obj (op V)⟩) :=
-- { to_fun := λ x, begin
--     induction x using tensor_product.induction_on,
--   end,
--   map_add' := _,
--   map_smul' := _ }

-- def extension_by.obj_presheaf_Ab (𝓕 : presheaf_of_module 𝓞1) : presheaf Ab X :=
-- { obj := λ U,
--     ⟨(extension_of_scalars (f.app U)).obj
--       { carrier := (𝓕.self.obj U), is_module := 𝓕.is_module (unop U) }⟩,
--   map := λ U V inc,
--     { to_fun := test _ _ (unop U) (unop V) inc,
--       map_zero' := by simp,
--       map_add' := by simp },
--   map_id' := _,
--   map_comp' := _ }

-- end extension

-- end presheaf_of_module
