import tactic.coherence

open category_theory

namespace tactic

namespace bicategory
open_locale bicategory
open category_theory.bicategory

/-- normalize 1-morphisms -/
meta def normalize : expr → expr → tactic expr
| p `(%%f ≫ %%g) := do pf ← normalize p f, normalize pf g
| p `(𝟙 %%a)      := return p
| p f              := to_expr ``(%%p ≫ %%f)

meta def to_normalize_aux : expr → expr → tactic expr
| p `(%%f ≫ %%g) := do
    pf₂  ← to_normalize_aux p f,
    pf   ← normalize p f,
    pfg₂ ← to_normalize_aux pf g,
    to_expr ``((α_ %%p %%f %%g).symm ≪≫ whisker_right_iso %%pf₂ %%g ≪≫ %%pfg₂)
| p `(𝟙 %%a)     := to_expr ``(ρ_ %%p)
| p f             := to_expr ``(iso.refl (%%p ≫ %%f))

/-- 2-isomorphism between the original 1-morphism and the normalized 1-morphism -/
meta def to_normalize (f : expr) : tactic expr :=
do
  `(%%a ⟶ %%b) ← infer_type f,
  p  ← to_expr ``(𝟙 %%a),
  f' ← to_normalize_aux p f,
  to_expr ``((λ_ _).symm ≪≫ %%f')

/-- 2-isomorphism between `f` and `g` that are related by `id_comp`, `comp_id`, and `assoc`. -/
meta def can (f : expr) (g : expr) : tactic expr :=
do
  `(%%a ⟶ %%b) ← infer_type f,
  f' ← to_normalize f,
  g' ← to_normalize g,
  to_expr ``(%%f' ≪≫ iso.symm %%g')

end bicategory

namespace interactive
setup_tactic_parser

/--
The tactic `can` yields an isomorphism `f ≅ g` for 1-morphisms `f` and `g` that are
related by `id_comp`, `comp_id`, and `assoc`.
-/
meta def can : tactic unit :=
do
  `(%%f ≅ %%g) ← get_goal >>= infer_type,
  f_to_g ← tactic.bicategory.can f g,
  tactic.exact f_to_g

open_locale bicategory
universes w v u
variables {B : Type u} [bicategory.{w v} B]
variables {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)

example : f ≫ g ≫ h ≅ f ≫ (g ≫ h) := by can
example : ((f ≫ g) ≫ 𝟙 c ≫ h) ≫ i ≅ f ≫ (g ≫ h) ≫ i := by can
example : f ≫ g ≫ 𝟙 c ≫ h ≫ i ≫ 𝟙 e ≅ 𝟙 a ≫ (f ≫ g ≫ h) ≫ 𝟙 d ≫ i := by can
example : f ≅ f := by can

def assoc₄ : ((f ≫ g) ≫ h) ≫ i ≅ f ≫ g ≫ h ≫ i := by can

example  : (assoc₄ f g h i).hom = (α_ _ _ _).hom ≫ (α_ _ _ _).hom :=
begin
  dsimp [assoc₄],
  coherence
  -- `can` yields a rather complicated expression, but by the coherence theorem this is
  -- equal to the simpler expression containing only two associators.
  -- TODO: Write more efficient version of `can`.
  /-
  ⊢ ((λ_ (((f ≫ g) ≫ h) ≫ i)).inv ≫
          (α_ (𝟙 a) ((f ≫ g) ≫ h) i).inv ≫
            ((α_ (𝟙 a) (f ≫ g) h).inv ≫
                    ((α_ (𝟙 a) f g).inv ≫ 𝟙 (𝟙 a ≫ f) ▷ g ≫ 𝟙 ((𝟙 a ≫ f) ≫ g)) ▷ h ≫
                      𝟙 (((𝟙 a ≫ f) ≫ g) ≫ h)) ▷
                i ≫
              𝟙 ((((𝟙 a ≫ f) ≫ g) ≫ h) ≫ i)) ≫
        ((((((𝟙 ((((𝟙 a ≫ f) ≫ g) ≫ h) ≫ i) ≫ 𝟙 (((𝟙 a ≫ f) ≫ g) ≫ h) ▷ i) ≫
                        (α_ ((𝟙 a ≫ f) ≫ g) h i).hom) ≫
                      𝟙 ((𝟙 a ≫ f) ≫ g) ▷ (h ≫ i)) ≫
                  (α_ (𝟙 a ≫ f) g (h ≫ i)).hom) ≫
                𝟙 (𝟙 a ≫ f) ▷ (g ≫ h ≫ i)) ≫
            (α_ (𝟙 a) f (g ≫ h ≫ i)).hom) ≫
          (λ_ (f ≫ g ≫ h ≫ i)).hom =
      (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom
  -/
end

end interactive

end tactic
