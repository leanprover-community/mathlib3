import category_theory.stalks

universes v u

open category_theory.limits

namespace category_theory

structure PreorderPresheaf extends PresheafedSpace.{v} (Type v) :=
(preorder : Π x : X, preorder (to_PresheafedSpace.stalk x))

instance (F : PreorderPresheaf.{v}) (x : F.X) : preorder (F.to_PresheafedSpace.stalk x) :=
F.preorder x

namespace PreorderPresheaf

-- what's going on with the @s !?
structure hom (F G : PreorderPresheaf.{v}) :=
(hom : F.to_PresheafedSpace ⟶ G.to_PresheafedSpace)
(monotone : Π (x : F.X) (a b : @PresheafedSpace.stalk (Type v) _ _ G.to_PresheafedSpace (PresheafedSpace.hom.f hom x)),
   (a ≤ b) → ((@PresheafedSpace.stalk_map (Type v) _ _ _ _ hom x) a ≤ (@PresheafedSpace.stalk_map (Type v) _ _ _ _ hom x) b))

@[extensionality] lemma hom.ext
  (F G : PreorderPresheaf.{v}) {f g : hom F G}
  (w : f.hom = g.hom) : f = g :=
begin
  cases f, cases g,
  congr; assumption
end

def id (F : PreorderPresheaf.{v}) : hom F F :=
{ hom := 𝟙 F.to_PresheafedSpace,
  monotone := λ x a b h, begin simp, exact h, end  }

def comp (F G H : PreorderPresheaf.{v}) (α : hom F G) (β : hom G H) : hom F H :=
{ hom := α.hom ≫ β.hom,
  monotone := λ x a b h,
  begin
    simp,
    apply α.monotone,
    apply β.monotone,
    exact h,
  end  }

section
local attribute [simp] id comp
instance : category PreorderPresheaf.{v} :=
{ hom := hom,
  id := id,
  comp := comp,
  comp_id' := λ X Y f, begin ext1, dsimp, simp, end,
  id_comp' := λ X Y f, begin ext1, dsimp, simp, end,
  assoc' := λ W X Y Z f g h, begin ext1, dsimp, simp, end }
end
-- TODO should `dsimp` and `simp` come before `ext` in `tidy`?

end PreorderPresheaf

end category_theory
