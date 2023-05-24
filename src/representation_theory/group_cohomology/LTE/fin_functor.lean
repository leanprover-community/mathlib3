import category_theory.preadditive.basic
import category_theory.abelian.projective
import tactic.interval_cases


noncomputable theory

open category_theory
open category_theory.limits

universe variables v u

namespace category_theory

variables {C : Type u} [category.{v} C]

namespace fin3_functor_mk

variables (F : fin 3 → C) (a : F 0 ⟶ F 1) (b : F 1 ⟶ F 2)

def map' : Π (i j : fin 3) (hij : i ≤ j), F i ⟶ F j
| ⟨0,hi⟩ ⟨0,hj⟩ _ := 𝟙 _
| ⟨1,hi⟩ ⟨1,hj⟩ _ := 𝟙 _
| ⟨2,hi⟩ ⟨2,hj⟩ _ := 𝟙 _
| ⟨0,hi⟩ ⟨1,hj⟩ _ := a
| ⟨1,hi⟩ ⟨2,hj⟩ _ := b
| ⟨0,hi⟩ ⟨2,hj⟩ _ := a ≫ b
| ⟨i+3,hi⟩ _ _ := by { exfalso, revert hi, dec_trivial }
| _ ⟨j+3,hj⟩ _ := by { exfalso, revert hj, dec_trivial }
| ⟨i+1,hi⟩ ⟨0,hj⟩ H := by { exfalso, revert H, dec_trivial }
| ⟨i+2,hi⟩ ⟨1,hj⟩ H := by { exfalso, revert H, dec_trivial }
.

lemma map'_id : ∀ (i : fin 3), map' F a b i i le_rfl = 𝟙 _
| ⟨0,hi⟩ := rfl
| ⟨1,hi⟩ := rfl
| ⟨2,hi⟩ := rfl
| ⟨i+3,hi⟩ := by { exfalso, revert hi, dec_trivial }

lemma map'_comp : Π (i j k : fin 3) (hij : i ≤ j) (hjk : j ≤ k),
  map' F a b i j hij ≫ map' F a b j k hjk = map' F a b i k (hij.trans hjk)
| ⟨0, _⟩ ⟨0, _⟩ k _ _ := category.id_comp _
| ⟨1, _⟩ ⟨1, _⟩ k _ _ := category.id_comp _
| i ⟨1, _⟩ ⟨1, _⟩ _ _ := category.comp_id _
| i ⟨2, _⟩ ⟨2, _⟩ _ _ := category.comp_id _
| ⟨0, _⟩ ⟨1, _⟩ ⟨2, _⟩ _ _ := rfl
| ⟨i+3,hi⟩ _ _ _ _ := by { exfalso, revert hi, dec_trivial }
| _ ⟨j+3,hj⟩ _ _ _ := by { exfalso, revert hj, dec_trivial }
| _ _ ⟨k+3,hk⟩ _ _ := by { exfalso, revert hk, dec_trivial }
| ⟨i+1,hi⟩ ⟨0,hj⟩ _ H _ := by { exfalso, revert H, dec_trivial }
| ⟨i+2,hi⟩ ⟨1,hj⟩ _ H _ := by { exfalso, revert H, dec_trivial }
| _ ⟨i+1,hi⟩ ⟨0,hj⟩ _ H := by { exfalso, revert H, dec_trivial }
| _ ⟨i+2,hi⟩ ⟨1,hj⟩ _ H := by { exfalso, revert H, dec_trivial }


end fin3_functor_mk

def fin3_functor_mk (F : fin 3 → C) (a : F 0 ⟶ F 1) (b : F 1 ⟶ F 2) : fin 3 ⥤ C :=
{ obj := F,
  map := λ i j hij, fin3_functor_mk.map' F a b i j hij.le,
  map_id' := λ i, fin3_functor_mk.map'_id F a b i,
  map_comp' := λ i j k hij hjk, by rw fin3_functor_mk.map'_comp F a b i j k hij.le hjk.le }

namespace fin4_functor_mk

variables (F : fin 4 → C) (a : F 0 ⟶ F 1) (b : F 1 ⟶ F 2) (c : F 2 ⟶ F 3)

def map' : Π (i j : fin 4) (hij : i ≤ j), F i ⟶ F j
| ⟨0,hi⟩ ⟨0,hj⟩ _ := 𝟙 _
| ⟨1,hi⟩ ⟨1,hj⟩ _ := 𝟙 _
| ⟨2,hi⟩ ⟨2,hj⟩ _ := 𝟙 _
| ⟨3,hi⟩ ⟨3,hj⟩ _ := 𝟙 _
| ⟨0,hi⟩ ⟨1,hj⟩ _ := a
| ⟨1,hi⟩ ⟨2,hj⟩ _ := b
| ⟨2,hi⟩ ⟨3,hj⟩ _ := c
| ⟨0,hi⟩ ⟨2,hj⟩ _ := a ≫ b
| ⟨1,hi⟩ ⟨3,hj⟩ _ := b ≫ c
| ⟨0,hi⟩ ⟨3,hj⟩ _ := a ≫ b ≫ c
| ⟨i+4,hi⟩ _ _ := by { exfalso, revert hi, dec_trivial }
| _ ⟨j+4,hj⟩ _ := by { exfalso, revert hj, dec_trivial }
| ⟨i+1,hi⟩ ⟨0,hj⟩ H := by { exfalso, revert H, dec_trivial }
| ⟨i+2,hi⟩ ⟨1,hj⟩ H := by { exfalso, revert H, dec_trivial }
| ⟨3,hi⟩ ⟨2,hj⟩ H := by { exfalso, revert H, dec_trivial }
.

lemma map'_id : ∀ (i : fin 4), map' F a b c i i le_rfl = 𝟙 _
| ⟨0,hi⟩ := rfl
| ⟨1,hi⟩ := rfl
| ⟨2,hi⟩ := rfl
| ⟨3,hi⟩ := rfl
| ⟨i+4,hi⟩ := by { exfalso, revert hi, dec_trivial }

lemma map'_comp : Π (i j k : fin 4) (hij : i ≤ j) (hjk : j ≤ k),
  map' F a b c i j hij ≫ map' F a b c j k hjk = map' F a b c i k (hij.trans hjk)
| ⟨0, _⟩ ⟨0, _⟩ k _ _ := category.id_comp _
| ⟨1, _⟩ ⟨1, _⟩ k _ _ := category.id_comp _
| ⟨2, _⟩ ⟨2, _⟩ k _ _ := category.id_comp _
| i ⟨1, _⟩ ⟨1, _⟩ _ _ := category.comp_id _
| i ⟨2, _⟩ ⟨2, _⟩ _ _ := category.comp_id _
| i ⟨3, _⟩ ⟨3, _⟩ _ _ := category.comp_id _
| ⟨0, _⟩ ⟨1, _⟩ ⟨2, _⟩ _ _ := rfl
| ⟨0, _⟩ ⟨1, _⟩ ⟨3, _⟩ _ _ := rfl
| ⟨0, _⟩ ⟨2, _⟩ ⟨3, _⟩ _ _ := category.assoc a b c
| ⟨1, _⟩ ⟨2, _⟩ ⟨3, _⟩ _ _ := rfl
| ⟨i+4,hi⟩ _ _ _ _ := by { exfalso, revert hi, dec_trivial }
| _ ⟨j+4,hj⟩ _ _ _ := by { exfalso, revert hj, dec_trivial }
| _ _ ⟨k+4,hk⟩ _ _ := by { exfalso, revert hk, dec_trivial }
| ⟨i+1,hi⟩ ⟨0,hj⟩ _ H _ := by { exfalso, revert H, dec_trivial }
| ⟨i+2,hi⟩ ⟨1,hj⟩ _ H _ := by { exfalso, revert H, dec_trivial }
| ⟨3,hi⟩ ⟨2,hj⟩ _ H _ := by { exfalso, revert H, dec_trivial }
| _ ⟨i+1,hi⟩ ⟨0,hj⟩ _ H := by { exfalso, revert H, dec_trivial }
| _ ⟨i+2,hi⟩ ⟨1,hj⟩ _ H := by { exfalso, revert H, dec_trivial }
| _ ⟨3,hi⟩ ⟨2,hj⟩ _ H := by { exfalso, revert H, dec_trivial }


end fin4_functor_mk

def fin4_functor_mk (F : fin 4 → C) (a : F 0 ⟶ F 1) (b : F 1 ⟶ F 2) (c : F 2 ⟶ F 3) : fin 4 ⥤ C :=
{ obj := F,
  map := λ i j hij, fin4_functor_mk.map' F a b c i j hij.le,
  map_id' := λ i, fin4_functor_mk.map'_id F a b c i,
  map_comp' := λ i j k hij hjk, by rw fin4_functor_mk.map'_comp F a b c i j k hij.le hjk.le }

end category_theory
