import category_theory.abelian.basic

.

open category_theory

namespace category_theory

variables {C : Type*} [category C]

namespace arrow

inductive composable : arrow C → arrow C → Prop
| intro {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : composable f g

inductive composable_path : C → C → list (arrow C) → Prop
| nil (X : C) : composable_path X X []
| cons {X Y Z : C} (f : X ⟶ Y) (L : list (arrow C)) (hL : composable_path Y Z L) :
    composable_path X Z (f :: L)

lemma composable.tgt_eq_src : Π {f g : arrow C}, composable f g → f.right = g.left
| _ _ (composable.intro f g) := rfl

def composable.comp : Π {f g : arrow C}, composable f g → arrow C
| f g hfg := f.hom ≫ eq_to_hom hfg.tgt_eq_src ≫ g.hom

-- lemma composable_path.composable :
--   Π {f g : arrow C} {L : list (arrow C)} (h : composable_path (f :: g :: L)),
--     composable f g
-- | _ _ _ (composable_path.cons f g L hfg hgL) := hfg

lemma composable_path.tail :
  Π  {X Y Z : C} (f : X ⟶ Y) (L : list (arrow C)) (hL : composable_path X Z (f :: L)),
    composable_path Y Z L
| _ _ _ _ _ (composable_path.cons f L hL) := hL

-- def composable_path.comp : Π {X Y : C} {L : list (arrow C)} (h : composable_path X Y L), arrow C
-- | X _ [] h := 𝟙 X
-- | X Y (f::L) h := f.hom ≫ eq_to_hom sorry ≫
--     (composable_path.comp (h.tail f.hom L)).hom

end arrow

structure diagram (C : Type*) [category C] :=
(index : Type*)
(map : index → arrow C)

namespace diagram

variables (D : diagram C)

def contains_list (I : set D.index) (L : list (arrow C)) : Prop :=
∀ f : arrow C, f ∈ L → ∃ i ∈ I, f = D.map i

def commutative (I : set D.index) : Prop :=
∀ (L₁ L₂ : list (arrow C)) (h₁ : D.contains_list I L₁) (h₂ : D.contains_list I L₂)
  (hL₁ : arrow.composable_path L₁) (hL₂ : arrow.composable_path L₂),
  hL₁.comp = hL₂.comp


/-
a --- i₁ --> b
|            |
i₂           j₁
|            |
v            v
c --- j₂ --> d

-/
def is_pullback (I : finset D.index) [decidable_eq D.index] : Prop :=
I.card = 4 ∧ ∃ (i₁ i₂ j₁ j₂ : D.index), I = {i₁, i₂, j₁, j₂} ∧
  ∃ (ha : (D.map i₁).left = (D.map i₂).left) (hb : (D.map i₁).right = (D.map j₁).left)
    (hc : (D.map i₂).right = (D.map j₂).left) (hd : (D.map j₁).right = (D.map j₂).right),
  -- commutative
  (D.map i₁).hom ≫ eq_to_hom hb ≫ (D.map j₁).hom ≫ eq_to_hom hd =
  eq_to_hom ha ≫ (D.map i₂).hom ≫ eq_to_hom hc ≫ (D.map j₂).hom ∧
  -- universal property
  ∀ (T : C) (f₁ : T ⟶ (D.map j₁).left) (f₂ : T ⟶ (D.map j₂).left),
    f₁ ≫ (D.map j₁).hom ≫ eq_to_hom hd = f₂ ≫ (D.map j₂).hom →
    ∃! (φ : T ⟶ (D.map i₁).left),
      φ ≫ (D.map i₁).hom ≫ eq_to_hom hb = f₁ ∧
      φ ≫ eq_to_hom ha ≫ (D.map i₂).hom ≫ eq_to_hom hc = f₂

lemma is_pullback.commutative (I : finset D.index) [decidable_eq D.index]
  (H : D.is_pullback I) : D.commutative I :=
begin
  rcases H with ⟨h4, H⟩,
  rcases H with ⟨i₁, i₂, j₁, j₂, rfl, ha, hb, hc, hd, hcomm, -⟩,
  intros L₁ L₂ h₁ h₂ hL₁ hL₂,
  cases hL₁,
  -- ⟨i₁, i₂, j₁, j₂⟩⟩,
end

end diagram

end category_theory
