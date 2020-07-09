
import data.qpf.indexed.mvpfunctor.basic
import data.qpf.indexed.constructions.basic

import category_theory.products

universes u

namespace mvqpf
variables {I J K : Type u}
  (F : fam I ⥤ fam J) [q  : mvqpf F]
  (G : fam J ⥤ fam K) [q' : mvqpf G]

open category_theory

-- def comp (v : fam J) : fam K :=
-- -- F $ λ i : fin' n, G i v
-- λ k : K, F.obj (λ i : I, (G i).obj v k) _

namespace comp
open mvfunctor mvpfunctor
variables {F G} {α β : fam J} (f : α ⟶ β)

-- protected def mk (x : F $ λ i, G i α) : (comp F G) α := x

-- protected def get (x : (comp F G) α) : F $ λ i, G i α := x

-- @[simp] protected lemma mk_get (x : (comp F G) α) : comp.mk (comp.get x) = x := rfl

-- @[simp] protected lemma get_mk (x : F $ λ i, G i α) : comp.get (comp.mk x) = x := rfl

-- protected def map' : (λ (i : fin' n), G i α) ⟹ λ (i : fin' n), G i β :=
-- λ i, map f

-- protected def map : (comp F G) α → (comp F G) β :=
-- (map (λ i, map f) : F (λ i, G i α) → F (λ i, G i β))

-- instance : mvfunctor (comp F G) :=
-- { map := λ α β, comp.map }

-- lemma map_mk (x : F $ λ i, G i α) :
--   f <$$> comp.mk x = comp.mk ((λ i (x : G i α), f <$$> x) <$$> x) := rfl

-- lemma get_map (x : comp F G α) :
--   comp.get (f <$$> x) = (λ i (x : G i α), f <$$> x) <$$> comp.get x := rfl

include q q'

local attribute [simp] category_theory.functor.map_comp_map category_theory.functor.map_comp_map_assoc
local attribute [-simp] functor.map_comp -- functor.map_comp_assoc
-- #check box F _ _

-- lemma box_comp' {α : fam I} (A : Π i, set (fam.unit i ⟶ α)) :
--   box G (box F A) ≤ (box (F ⋙ G) A : Π i, set (fam.unit i ⟶ (F ⋙ G).obj α)) :=
-- begin
--   introv i a,
--   simp only [set.mem_sep_iff,set.mem_set_of_eq,box], erw set.mem_set_of_eq,
--   { introv h₀ h₁,
--     refine h₀ _ (F.map f) (F.map g) _,
--     clear h₀, introv h₂, apply h₂, apply h₁ },
-- end

-- lemma box_comp {α : fam I} (A : Π i, set (fam.unit i ⟶ α)) :
--   box (F ⋙ G) A = (box G (box F A) : Π i, set (fam.unit i ⟶ G.obj (F.obj α))) :=
-- begin
--   ext j y, simp only [set.mem_sep_iff,set.mem_set_of_eq,box], erw set.mem_set_of_eq,
--   split,
--   { introv h₀ h₁,
--     specialize h₀,
--     -- apply repr_mono,
--     -- simp [← abs_map'], rw ← abs_map,
--     },
--   { introv h₀ h₁,
--     refine h₀ _ (F.map f) (F.map g) _,
--     clear h₀, introv h₂, apply h₂, apply h₁ },
-- end

section defs

variables F G

@[simp]
def abs (α) : (pfunctor.comp (P G) (P F)).obj α ⟶ (F ⋙ G).obj α :=
pfunctor.comp.get _ _ α ≫ (P G).map (abs F _) ≫ abs G _ ≫ 𝟙 (G.obj (F.obj α))

@[simp]
def repr (α) : (F ⋙ G).obj α ⟶ (pfunctor.comp (P G) (P F)).obj α :=
𝟙 (G.obj (F.obj α)) ≫ @repr _ _ G q' _ ≫ (P G).map (repr F α) ≫ pfunctor.comp.mk _ _ _

end defs

lemma abs_repr ⦃α⦄ : comp.repr F G α ≫ comp.abs F G _ = 𝟙 ((F ⋙ G).obj α) :=
by { intros,
  simp only [repr, abs, category.id_comp, category.comp_id, category.assoc, pfunctor.comp.mk_get_assoc, functor.map_comp_map_assoc],
  erw [functor.map_comp_map_assoc, abs_repr, category_theory.functor.map_id, category.id_comp, category.id_comp, abs_repr], refl }

lemma abs_map ⦃α β⦄ (f : α ⟶ β) : (pfunctor.comp (P G) (P F)).map f ≫ comp.abs F G _ = comp.abs F G _ ≫ (F ⋙ G).map f :=
by { intros, simp only [comp.abs, abs_map, functor.comp_map, pfunctor.comp.map_get_assoc, functor.map_comp_map,
     abs_map_assoc, category.comp_id, category.assoc, category_theory.functor.map_comp_map] }

instance : mvqpf (F ⋙ G) :=
{ P         := pfunctor.comp (P G) (P F),
  abs := abs F G,
  repr := repr F G,
  abs_repr := abs_repr,
  abs_map := abs_map,
  -- box_inter := λ α A B i, by {
  --   apply congr_fun _ i, dsimp,
  --   simp [box_inter',box_comp], }
 }

end comp

end mvqpf
