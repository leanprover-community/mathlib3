import algebra.category.BundledModule.basic
import topology.sheaves.presheaf
import algebra.category.Module.change_of_rings

open category_theory Top topological_space change_of_rings Module'

section

universe u

variables {T : Top.{u}}

structure presheaf_of_module (𝓞 : presheaf CommRing T) :=
(self : presheaf RingModulePair T)
(e : self ⋙ RingModulePair.forget_to_Ring ≅ 𝓞)

instance {𝓞 : presheaf CommRing T} (𝓕 : presheaf_of_module 𝓞) :
  ∀ (U : (opens T)ᵒᵖ), module (𝓞.obj U) (𝓕.self.obj U).M :=
λ U, begin
  haveI : algebra (𝓞.obj U) (𝓕.self.obj U).R := (𝓕.e.app U).inv.to_algebra,
  change module (𝓞.obj U) (restrict_scalars (𝓞.obj U) (𝓕.self.obj U).R _),
  apply_instance,
end

lemma presheaf_of_module.compatible_smul {𝓞 : presheaf CommRing T} (𝓕 : presheaf_of_module 𝓞)
  {U V :(opens T)ᵒᵖ} (inc : U ⟶ V) (r : 𝓞.obj U) (m : (𝓕.self.obj U).M) :
  (𝓕.self.map inc).2 (r • m) = (𝓞.map inc) r • (𝓕.self.map inc).2 m :=
begin
  haveI : algebra (𝓞.obj U) ((𝓕.self ⋙ RingModulePair.forget_to_Ring).obj U) :=
    (𝓕.e.app U).inv.to_algebra,
  rw restriction_of_scalars.smul_def,
  unfold algebra_map,
  rw linear_map.map_smul,
  change (𝓕.e.inv.app U) r • _ = (𝓕.e.inv.app V) _ • _,
  simp only [restriction_of_scalars.smul_def'],

  congr' 1,
  erw ring_hom.congr_fun (𝓕.e.inv.naturality inc) r,
  refl,
end

-- def presheaf_of_module.restrict_module {𝓞 : presheaf CommRing T} (𝓕 : presheaf_of_module 𝓞)
--   {U V :(opens T)ᵒᵖ} (inc : U ⟶ V) :
--   (_ : Module (𝓞.obj U)) ⟶ (_ : Module (𝓞.obj V))

namespace presheaf_of_module

section defs

variables {𝓞 : presheaf CommRing T}

def morphism (𝓕1 𝓕2 : presheaf_of_module 𝓞) := 𝓕1.self ⟶ 𝓕2.self

instance : category (presheaf_of_module 𝓞) :=
{ hom := morphism,
  id := λ 𝓕, 𝟙 (𝓕.self),
  comp := λ 𝓕1 𝓕2 𝓕3 f g, f ≫ g }.

end defs

namespace restriction

variables {𝓞1 𝓞2 : presheaf CommRing T} (f : 𝓞1 ⟶ 𝓞2)
include f

def obj (𝓕 : presheaf_of_module 𝓞2) : presheaf_of_module 𝓞1 :=
{ self :=
    { obj := λ U, { R := 𝓞1.obj U, M := restriction_of_scalars.module (f.app U) ⟨(𝓕.self.obj U).M⟩ },
      map := λ U V inc, ⟨𝓞1.map inc,
        { to_fun := (𝓕.self.map inc).2,
          map_add' := λ _ _, by rw map_add,
          map_smul' := λ r x, begin
            simp only [ring_hom.id_apply],
            erw presheaf_of_module.compatible_smul,
            erw [restriction_of_scalars.smul_def'],
            conv_rhs { erw [restriction_of_scalars.smul_def], },
            congr',
            erw ring_hom.congr_fun (f.naturality inc),
            refl,
          end }⟩,
      map_id' := λ U, begin
        rw bundledMap.ext,
        split,
        { ext r,
          change _ = r,
          simp only [id_apply, category_theory.functor.map_id], },
        { intros m,
          change (𝓕.self.map _).2 m = m,
          rw calc ((𝓕.self.map (𝟙 U)).snd) m
              = (bundledMap.id (𝓕.self.obj U)).2 m : _
          ... = m : rfl,
          have : 𝓕.self.map (𝟙 U) = 𝟙 (𝓕.self.obj U) := category_theory.functor.map_id _ _,
          erw this,
          congr', },
      end,
      map_comp' := λ U V W incUV incVW, begin
        rw bundledMap.ext,
        split,
        { rw bundledMap.comp_fst,
          simp only [category_theory.functor.map_comp], },
        { intros m,
          change (𝓕.self.map (incUV ≫ incVW)).2 m = (𝓕.self.map incVW).2 ((𝓕.self.map incUV).2 m),
          erw category_theory.functor.map_comp 𝓕.self incUV incVW,
          refl, }
      end },
  e :=
    { hom :=
        { app := λ U, 𝟙 _,
          naturality' := λ U V inc, sorry },
      inv :=
        { app := λ U, 𝟙 _,
          naturality' := λ U V inc, sorry },
      hom_inv_id' := sorry,
      inv_hom_id' := sorry } }.

end restriction

end presheaf_of_module

end
