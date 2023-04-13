import category_theory.abelian.basic
import tactic

noncomputable theory

open category_theory

constant ComplexAnalyticSpace : Type 1

@[instance]
constant ComplexAnalyticSpace.category : large_category ComplexAnalyticSpace

constant dim (X : ComplexAnalyticSpace) : ℤ

-- TODO: should we split this into two steps? The abelian category, and then the derived one?
/-- The derived(!) category of D-modules on a complex analytic space `X`. -/
constant Dmodule (X : ComplexAnalyticSpace) : Type 1

namespace Dmodule
variable {X : ComplexAnalyticSpace}

@[instance]
constant category : large_category (Dmodule X)
@[instance]
constant preadditive : preadditive (Dmodule X)

constant tensor (V₁ V₂ : Dmodule X) : Dmodule X
infix ` ⊗ `:10 := Dmodule.tensor

constant tensor_hom {V₁ V₂ W₁ W₂ : Dmodule X} (f : V₁ ⟶ V₂) (g : W₁ ⟶ W₂) :
  V₁ ⊗ W₁ ⟶ V₂ ⊗ W₂
infix ` ⊗' `:10 := Dmodule.tensor_hom

constant shift (V : Dmodule X) (i : ℤ) : Dmodule X
notation V`⟦`i`⟧` := shift V i

variables (V : Dmodule X) (i j : ℤ)

axiom shift_zero : V⟦0⟧ = V
axiom shift_add : V⟦i+j⟧ = V⟦i⟧⟦j⟧

constant shift_hom {V W : Dmodule X} (f : V ⟶ W) (i : ℤ) : V⟦i⟧ ⟶ W⟦i⟧
notation f`⟦`i`⟧'` := shift_hom f i

end Dmodule

/-- Unit D-module -/
constant ℚ' {X : ComplexAnalyticSpace} : Dmodule X

/-- Perverse pushforward -/
constant pR {X Y : ComplexAnalyticSpace}
  (i : ℤ) (f : X ⟶ Y) (V : Dmodule X) : Dmodule Y

/-- Pushforward -/
constant R {X Y : ComplexAnalyticSpace}
  (i : ℤ) (f : X ⟶ Y) (V : Dmodule X) : Dmodule Y

-- ** -- ** -- ** -- ** -- ** -- ** -- ** -- ** -- ** -- ** -- ** -- ** --

variables {X Y Z : ComplexAnalyticSpace}
variables (f : X ⟶ Y) (g : Y ⟶ Z)
variables (M N P : Dmodule X)
variables (a a' b b' c c' d i j k : ℤ)

/-- The map from a component in the Leray spectral sequence. -/
constant R_comp : R i g (R j f M) ⟶ R (i+j) (f ≫ g) M

instance R_comp' : inhabited (R i g (R j f M) ⟶ R (i+j) (f ≫ g) M) :=
{ default := R_comp f g M i j }

meta def ring_tac : tactic unit := `[ring]
meta def linarith_tac : tactic unit := `[dsimp at *; linarith]

constant tensor_shift (hab : a + a' = 0 . linarith_tac) (hcd : b + b' = 0 . linarith_tac) :
  M⟦a⟧ ⊗ N⟦a'⟧ ⟶ M⟦b⟧ ⊗ N⟦b'⟧

instance tensor_shift_default [fact (a + a' = 0)] [fact (b + b' = 0)] :
  inhabited (M⟦a⟧ ⊗ N⟦a'⟧ ⟶ M⟦b⟧ ⊗ N⟦b'⟧) :=
{ default := tensor_shift M N a a' b b' (fact.out _) (fact.out _) }

instance tensor_hom_default (M N P Q : Dmodule X)
  [inhabited (M ⟶ P)] [inhabited (N ⟶ Q)] : inhabited (M ⊗ N ⟶ P ⊗ Q) :=
{ default := (default : M ⟶ P) ⊗' (default : N ⟶ Q) }

instance shift_hom_default (M N : Dmodule X) (i : ℤ) [inhabited (M ⟶ N)] :
  inhabited (M⟦i⟧ ⟶ N⟦i⟧) :=
{ default := (default : M ⟶ N)⟦i⟧' }

def upper_triangle_commutes_up_to_sign (n : ℤˣ) (M N P : Dmodule X)
  [inhabited (M ⟶ N)] [inhabited (N ⟶ P)] [inhabited (M ⟶ P)] : Prop :=
(default : M ⟶ N) ≫ (default : N ⟶ P) = n • (default : M ⟶ P)

def square_commutes_up_to_sign (n : ℤˣ) (A B C D : Dmodule X)
  [inhabited (A ⟶ B)] [inhabited (B ⟶ D)] [inhabited (A ⟶ C)] [inhabited (C ⟶ D)] : Prop :=
(default : A ⟶ B) ≫ (default : B ⟶ D) = n • ((default : A ⟶ C) ≫ (default : C ⟶ D))

variables [fact (a + a' = 0)] [fact (b + b' = 0)] [fact (c + c' = 0)]

axiom tensor_shift_triangle :
  upper_triangle_commutes_up_to_sign ((-1:ℤˣ) ^ ((a+b) * (b+c)))
  (M⟦a⟧ ⊗ N⟦a'⟧)  /- ⟶ -/  (M⟦b⟧ ⊗ N⟦b'⟧)
--                 \             |
--                  ↘            v
                           (M⟦c⟧ ⊗ N⟦c'⟧)

axiom Rcomp_shift_square :
  square_commutes_up_to_sign 1
    ((R j g (R i f M))⟦a⟧ ⊗ (R j g (R i f M))⟦a'⟧)    /- ⟶ -/    ((R j g (R i f M))⟦b⟧ ⊗ (R j g (R i f M))⟦b'⟧)
--                        |                                                            |
--                        |                                                            |
--                        v                                                            v
  ((R (j+i) (f ≫ g) M)⟦a⟧ ⊗ (R (j+i) (f ≫ g) M)⟦a'⟧) /- ⟶ -/ ((R (j+i) (f ≫ g) M)⟦b⟧ ⊗ (R (j+i) (f ≫ g) M)⟦b'⟧)

-- axiom tensor_shift_comp'
--   (ha : a + a' = 0 . linarith_tac) (hb : b + b' = 0 . linarith_tac) (hc : c + c' = 0 . linarith_tac) :
--   tensor_shift M N a a' b b' ≫ tensor_shift M N b b' c c' =
--     (-1:ℤˣ) ^ ((a + b) * (b + c) : ℤ) • tensor_shift M N a a' c c'

-- ** -- ** -- ** -- ** -- ** -- ** -- ** -- ** -- ** -- ** -- ** -- ** --
