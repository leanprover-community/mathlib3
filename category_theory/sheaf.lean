@[reducible]
def covering_family (U : X) : Type u := set (over.{u u} U)

namespace covering_family

variables {U : X} (c : covering_family U)

def sieve : presheaf X :=
let
  y (Ui : c) := yoneda.map Ui.val.hom,
  pb (Ujk : c × c) : presheaf X := limits.pullback (y Ujk.1) (y Ujk.2),
  re (Ui : c) : presheaf X := yoneda.obj Ui.val.left,
  left  : limits.sigma pb ⟶ limits.sigma re :=
    sigma.desc $ λ Ujk : c × c, pullback.π₁ (y Ujk.1) (y Ujk.2) ≫ sigma.ι re Ujk.1,
  right : limits.sigma pb ⟶ limits.sigma re :=
    sigma.desc $ λ Ujk : c × c, pullback.π₂ (y Ujk.1) (y Ujk.2) ≫ sigma.ι re Ujk.2
in coequalizer left right

def π : c.sieve ⟶ yoneda.obj U :=
coequalizer.desc _ _ (sigma.desc $ λ Ui, yoneda.map Ui.val.hom)
begin
  ext1, dsimp at *,
  rw ←category.assoc,
  rw ←category.assoc,
  simp,
end

def sheaf_condition (F : presheaf X) := is_iso $ (yoneda.obj F).map c.π
