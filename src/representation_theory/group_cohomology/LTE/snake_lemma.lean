import category_theory.preadditive.basic
import category_theory.abelian.projective
import data.matrix.notation
import tactic.interval_cases
import category_theory.abelian.pseudoelements

import .short_exact_sequence
import .abelian_category
import .fin_functor
import .exact_seq

noncomputable theory

open category_theory
open category_theory.limits
open_locale pseudoelement

universe variables v u

namespace eq

variables {X : Type*} {x y : X} (h : x = y)

@[nolint unused_arguments]
abbreviation lhs (h : x = y) := x

@[nolint unused_arguments]
abbreviation rhs (h : x = y) := y

@[simp] lemma lhs_def : h.lhs = x := rfl
@[simp] lemma rhs_def : h.rhs = y := rfl

end eq

namespace category_theory

/-- The base diagram for the snake lemma. The object are indexed by `fin 4 × fin 3`:

(0,0) --> (0,1) --> (0,2)              | the kernels
  |         |         |
  v         v         v
(1,0) --> (1,1) --> (1,2)              | the first exact row
  |         |         |
  v         v         v
(2,0) --> (2,1) --> (2,2)              | the second exact row
  |         |         |
  v         v         v
(3,0) --> (3,1) --> (3,2)              | the cokernels

-/
@[derive [preorder, decidable_eq]]
def snake_diagram := fin 4 × fin 3

namespace snake_diagram

@[simps]
def o (i : fin 4) (j : fin 3) : snake_diagram := (i,j)

@[simp] lemma o_le_o (i j : fin 4) (k l : fin 3) :
  o i k ≤ o j l ↔ i ≤ j ∧ k ≤ l := iff.rfl

meta def hom_tac : tactic unit :=
`[simp only [category_theory.snake_diagram.o_le_o,
      category_theory.snake_diagram.o_fst, category_theory.snake_diagram.o_snd,
      prod.le_def, and_true, true_and, le_refl],
  dec_trivial! ]

def hom (i j : snake_diagram) (hij : i ≤ j . hom_tac) : i ⟶ j := hom_of_le hij

lemma hom_ext {i j : snake_diagram} (f g : i ⟶ j) : f = g := by ext

section

meta def map_tac : tactic unit :=
`[dsimp only [mk_functor, mk_functor.map', eq_to_hom_refl, hom_of_le_refl, true_and, le_refl],
  simp only [category.id_comp, category.comp_id, functor.map_id],
  refl]

parameters {C : Type u} [category.{v} C]

parameters (F : fin 4 → fin 3 → C)
parameters (f0 : F 0 0 ⟶ F 0 1) (g0 : F 0 1 ⟶ F 0 2)
parameters (a0 : F 0 0 ⟶ F 1 0) (b0 : F 0 1 ⟶ F 1 1) (c0 : F 0 2 ⟶ F 1 2)
parameters (f1 : F 1 0 ⟶ F 1 1) (g1 : F 1 1 ⟶ F 1 2)
parameters (a1 : F 1 0 ⟶ F 2 0) (b1 : F 1 1 ⟶ F 2 1) (c1 : F 1 2 ⟶ F 2 2)
parameters (f2 : F 2 0 ⟶ F 2 1) (g2 : F 2 1 ⟶ F 2 2)
parameters (a2 : F 2 0 ⟶ F 3 0) (b2 : F 2 1 ⟶ F 3 1) (c2 : F 2 2 ⟶ F 3 2)
parameters (f3 : F 3 0 ⟶ F 3 1) (g3 : F 3 1 ⟶ F 3 2)
parameters (sq00 : a0 ≫ f1 = f0 ≫ b0) (sq01 : b0 ≫ g1 = g0 ≫ c0)
parameters (sq10 : a1 ≫ f2 = f1 ≫ b1) (sq11 : b1 ≫ g2 = g1 ≫ c1)
parameters (sq20 : a2 ≫ f3 = f2 ≫ b2) (sq21 : b2 ≫ g3 = g2 ≫ c2)

namespace mk_functor

def col : Π (j : fin 3), fin 4 ⥤ C
| ⟨0,h⟩ := fin4_functor_mk (flip F 0) a0 a1 a2
| ⟨1,h⟩ := fin4_functor_mk (flip F 1) b0 b1 b2
| ⟨2,h⟩ := fin4_functor_mk (flip F 2) c0 c1 c2
| ⟨j+3,h⟩ := by { exfalso, revert h, dec_trivial }

def row : Π (i : fin 4), fin 3 ⥤ C
| ⟨0,h⟩ := fin3_functor_mk (F 0) f0 g0
| ⟨1,h⟩ := fin3_functor_mk (F 1) f1 g1
| ⟨2,h⟩ := fin3_functor_mk (F 2) f2 g2
| ⟨3,h⟩ := fin3_functor_mk (F 3) f3 g3
| ⟨j+4,h⟩ := by { exfalso, revert h, dec_trivial }

lemma col_obj (i : fin 4) (j : fin 3) : (col j).obj i = F i j :=
by fin_cases i; fin_cases j; refl.

lemma row_obj (i : fin 4) (j : fin 3) : (row i).obj j = F i j :=
by fin_cases i; fin_cases j; refl.

lemma row_eq_col_obj (i : fin 4) (j : fin 3) : (row i).obj j = (col j).obj i :=
(row_obj i j).trans (col_obj i j).symm

def map'  (x y : snake_diagram) (h : x ≤ y) : F x.1 x.2 ⟶ F y.1 y.2 :=
eq_to_hom (by rw [row_obj]) ≫
(row x.1).map h.2.hom ≫ eq_to_hom (by rw [row_obj, col_obj]) ≫
(col y.2).map h.1.hom ≫ eq_to_hom (by rw [col_obj])

lemma map'_id (x : snake_diagram) : map' x x le_rfl = 𝟙 _ :=
by simp only [map', hom_of_le_refl, functor.map_id,
  eq_to_hom_trans, category.id_comp, eq_to_hom_refl]

def square_commutes (i j : fin 4) (k l : fin 3) (hij : i ≤ j) (hkl : k ≤ l) : Prop :=
(col k).map hij.hom ≫ eq_to_hom (by rw [row_obj, col_obj]) ≫
(row j).map hkl.hom =
eq_to_hom (by rw [col_obj]; refl) ≫
map' (o i k) (o j l) ⟨hij, hkl⟩ ≫ eq_to_hom (by rw [row_obj]; refl)

include sq00 sq01 sq10 sq11 sq20 sq21

lemma square_commutes_row (i : fin 4) (k l : fin 3) (hkl : k ≤ l) :
  square_commutes i i k l le_rfl hkl :=
begin
  dsimp [square_commutes, map'],
  simp only [map', hom_of_le_refl, functor.map_id, eq_to_hom_trans, eq_to_hom_trans_assoc,
    category.id_comp, category.comp_id, category.assoc],
  erw [hom_of_le_refl],
  simp only [map', hom_of_le_refl, functor.map_id, eq_to_hom_trans, eq_to_hom_trans_assoc,
    category.id_comp, category.comp_id, category.assoc],
  rw [← category.assoc, eq_comm],
  convert category.comp_id _,
end

lemma square_commutes_col (i j : fin 4) (k : fin 3) (hij : i ≤ j) :
  square_commutes i j k k hij le_rfl :=
begin
  dsimp [square_commutes, map'],
  simp only [map', hom_of_le_refl, functor.map_id, eq_to_hom_trans, eq_to_hom_trans_assoc,
    category.id_comp, category.comp_id, category.assoc],
  erw [hom_of_le_refl],
  simp only [map', hom_of_le_refl, functor.map_id, eq_to_hom_trans, eq_to_hom_trans_assoc,
    category.id_comp, category.comp_id, category.assoc],
  rw [eq_comm],
  convert category.id_comp _,
end

lemma square_commutes_one (i : fin 4) (j : fin 3) (hi : i < 3) (hj : j < 2) :
  square_commutes i (i+1) j (j+1) (by dec_trivial!) (by dec_trivial!) :=
begin
  fin_cases i, swap 4, { exfalso, revert hi, dec_trivial },
  all_goals { fin_cases j, swap 3, { exfalso, revert hj, dec_trivial },
    all_goals {
      simp only [square_commutes, map', eq_to_hom_refl, category.comp_id, category.id_comp],
      assumption }, },
end
.

lemma square_commutes_comp_row (i j k : fin 4) (l m : fin 3)
  (hij : i ≤ j) (hjk : j ≤ k) (hlm : l ≤ m)
  (h1 : square_commutes i j l m hij hlm) (h2 : square_commutes j k l m hjk hlm) :
  square_commutes i k l m (hij.trans hjk) hlm :=
begin
  dsimp [square_commutes, map'] at h1 h2 ⊢,
  simp only [map', hom_of_le_refl, functor.map_id, eq_to_hom_trans, eq_to_hom_trans_assoc,
    category.id_comp, category.comp_id, category.assoc] at h1 h2 ⊢,
  let φ : _ := _, let ψ : _ := _,
  calc _ = φ ≫ h2.lhs : _
     ... = φ ≫ h2.rhs : by { congr' 1, }
     ... = h1.lhs ≫ ψ : _
     ... = h1.rhs ≫ ψ : by { congr' 1, }
     ... = _ : _,
  swap 5, { exact functor.map _ hij.hom },
  swap 4, { refine (eq_to_hom _ ≫ _ ≫ eq_to_hom _),
    swap 2, { apply row_eq_col_obj; assumption },
    swap 3, { symmetry, apply row_eq_col_obj; assumption },
    exact functor.map _ hjk.hom },
  all_goals { dsimp [φ, ψ, eq.lhs_def, eq.rhs_def] },
  { simp only [← functor.map_comp_assoc], refl },
  { simp only [category.assoc], refl },
  { simp only [eq_to_hom_trans, eq_to_hom_trans_assoc, category.assoc],
    dsimp,
    simp only [hom_of_le_refl, eq_to_hom_trans, eq_to_hom_trans_assoc,
      category.id_comp, category.comp_id, category.assoc, ← functor.map_comp_assoc],
    refl, },
end

lemma square_commutes_comp_col (i j : fin 4) (l m n : fin 3)
  (hij : i ≤ j) (hlm : l ≤ m) (hmn : m ≤ n)
  (h1 : square_commutes i j l m hij hlm) (h2 : square_commutes i j m n hij hmn) :
  square_commutes i j l n hij (hlm.trans hmn) :=
begin
  dsimp [square_commutes, map'] at h1 h2 ⊢,
  simp only [map', hom_of_le_refl, functor.map_id, eq_to_hom_trans, eq_to_hom_trans_assoc,
    category.id_comp, category.comp_id, category.assoc] at h1 h2 ⊢,
  let φ : _ := _, let ψ : _ := _,
  calc _ = h1.lhs ≫ φ : _
     ... = h1.rhs ≫ φ : by { congr' 1, }
     ... = ψ ≫ h2.lhs : _
     ... = ψ ≫ h2.rhs : by { congr' 1, }
     ... = _ : _,
  swap 5, { exact functor.map _ hmn.hom },
  swap 4, { refine (eq_to_hom _ ≫ _ ≫ eq_to_hom _),
    swap 2, { symmetry, apply row_eq_col_obj; assumption },
    swap 3, { apply row_eq_col_obj; assumption },
    exact functor.map _ hlm.hom },
  all_goals { dsimp [φ, ψ, eq.lhs_def, eq.rhs_def] },
  { simp only [category.assoc, ← functor.map_comp], refl },
  { simp only [category.assoc], refl },
  { simp only [eq_to_hom_trans, eq_to_hom_trans_assoc, category.assoc],
    dsimp,
    simp only [hom_of_le_refl, eq_to_hom_trans, eq_to_hom_trans_assoc,
      category.id_comp, category.comp_id, category.assoc, ← functor.map_comp_assoc],
    refl, },
end

lemma col_comp_row (i j : fin 4) (k l : fin 3) (hij : i ≤ j) (hkl : k ≤ l) :
  (col k).map hij.hom ≫ eq_to_hom (by rw [row_obj, col_obj]) ≫
  (row j).map hkl.hom =
  eq_to_hom (by rw [col_obj]; refl) ≫
  map' (o i k) (o j l) ⟨hij, hkl⟩ ≫ eq_to_hom (by rw [row_obj]; refl) :=
begin
  cases i with i hi, cases j with j hj, cases k with k hk, cases l with l hl,
  have hkl' := hkl,
  rw [← fin.coe_fin_le, fin.coe_mk, fin.coe_mk] at hij hkl,
  obtain ⟨j, rfl⟩ := nat.exists_eq_add_of_le hij,
  obtain ⟨l, rfl⟩ := nat.exists_eq_add_of_le hkl,
  clear hij,
  induction j with j IHj,
  { apply square_commutes_row; assumption },
  refine square_commutes_comp_row F f0 g0 a0 b0 c0 f1 g1 a1 b1 c1 f2 g2 a2 b2 c2 f3 g3
    sq00 sq01 sq10 sq11 sq20 sq21 ⟨i, hi⟩ ⟨i+j, _⟩ _ _ _ _ _ hkl' _ _,
  { refine lt_trans _ hj, exact lt_add_one (i+j) },
  { simp only [← fin.coe_fin_le, fin.coe_mk], exact le_self_add },
  { simp only [← fin.coe_fin_le, fin.coe_mk], exact (lt_add_one (i+j)).le },
  { refine IHj _ _, },
  clear IHj hkl,
  induction l with l IHl,
  { apply square_commutes_col; assumption },
  refine square_commutes_comp_col F f0 g0 a0 b0 c0 f1 g1 a1 b1 c1 f2 g2 a2 b2 c2 f3 g3
    sq00 sq01 sq10 sq11 sq20 sq21 _ _ ⟨k, hk⟩ ⟨k+l, _⟩ _ _ _ _ _ _,
  { refine lt_trans _ hl, exact lt_add_one (k+l) },
  { simp only [← fin.coe_fin_le, fin.coe_mk], exact le_self_add },
  { simp only [← fin.coe_fin_le, fin.coe_mk], exact (lt_add_one (k+l)).le },
  { refine IHl _ _ _, simp only [← fin.coe_fin_le, fin.coe_mk], exact le_self_add },
  clear IHl,
  convert square_commutes_one F f0 g0 a0 b0 c0 f1 g1 a1 b1 c1 f2 g2 a2 b2 c2 f3 g3
    sq00 sq01 sq10 sq11 sq20 sq21 _ _ _ _ using 2,
  { rw [nat.one_mod, add_assoc, nat.mod_eq_of_lt hj] },
  { rw [nat.one_mod, add_assoc, nat.mod_eq_of_lt hl] },
  { rw [← fin.coe_fin_lt, fin.coe_mk], refine nat.lt_of_succ_lt_succ hj, },
  { rw [← fin.coe_fin_lt, fin.coe_mk], refine nat.lt_of_succ_lt_succ hl, },
end

lemma map'_comp (x y z : snake_diagram) (hxy : x ≤ y) (hyz : y ≤ z) :
  map' x y hxy ≫ map' y z hyz = map' x z (hxy.trans hyz) :=
begin
  delta map',
  slice_lhs 4 7 { rw [eq_to_hom_trans_assoc] },
  rw [col_comp_row],
  { dsimp [map'],
    simp only [map', eq_to_hom_trans_assoc, category.assoc, eq_to_hom_refl,
      category.comp_id, category.id_comp, ← functor.map_comp_assoc],
    refl },
  all_goals { assumption },
end

end mk_functor

include sq00 sq01 sq10 sq11 sq20 sq21

def mk_functor : snake_diagram ⥤ C :=
{ obj := function.uncurry F,
  map := λ x y h, mk_functor.map' F f0 g0 a0 b0 c0 f1 g1 a1 b1 c1 f2 g2 a2 b2 c2 f3 g3 x y h.le,
  map_id' := λ x, mk_functor.map'_id F f0 g0 a0 b0 c0 f1 g1 a1 b1 c1 f2 g2 a2 b2 c2 f3 g3 x,
  map_comp' := λ x y z hxy hyz, by { rw mk_functor.map'_comp; assumption } }

@[simp] lemma mk_functor_map_f0 : mk_functor.map (hom (0,0) (0,1)) = f0 := by map_tac
@[simp] lemma mk_functor_map_g0 : mk_functor.map (hom (0,1) (0,2)) = g0 := by map_tac
@[simp] lemma mk_functor_map_a0 : mk_functor.map (hom (0,0) (1,0)) = a0 := by map_tac
@[simp] lemma mk_functor_map_b0 : mk_functor.map (hom (0,1) (1,1)) = b0 := by map_tac
@[simp] lemma mk_functor_map_c0 : mk_functor.map (hom (0,2) (1,2)) = c0 := by map_tac
@[simp] lemma mk_functor_map_f1 : mk_functor.map (hom (1,0) (1,1)) = f1 := by map_tac
@[simp] lemma mk_functor_map_g1 : mk_functor.map (hom (1,1) (1,2)) = g1 := by map_tac
@[simp] lemma mk_functor_map_a1 : mk_functor.map (hom (1,0) (2,0)) = a1 := by map_tac
@[simp] lemma mk_functor_map_b1 : mk_functor.map (hom (1,1) (2,1)) = b1 := by map_tac
@[simp] lemma mk_functor_map_c1 : mk_functor.map (hom (1,2) (2,2)) = c1 := by map_tac
@[simp] lemma mk_functor_map_f2 : mk_functor.map (hom (2,0) (2,1)) = f2 := by map_tac
@[simp] lemma mk_functor_map_g2 : mk_functor.map (hom (2,1) (2,2)) = g2 := by map_tac
@[simp] lemma mk_functor_map_a2 : mk_functor.map (hom (2,0) (3,0)) = a2 := by map_tac
@[simp] lemma mk_functor_map_b2 : mk_functor.map (hom (2,1) (3,1)) = b2 := by map_tac
@[simp] lemma mk_functor_map_c2 : mk_functor.map (hom (2,2) (3,2)) = c2 := by map_tac
@[simp] lemma mk_functor_map_f3 : mk_functor.map (hom (3,0) (3,1)) = f3 := by map_tac
@[simp] lemma mk_functor_map_g3 : mk_functor.map (hom (3,1) (3,2)) = g3 := by map_tac

end

section

variables {𝒜 ℬ : Type*} [category 𝒜] [category ℬ]
variables (A : fin 3 → 𝒜) (F : fin 4 → 𝒜 ⥤ ℬ)
variables (f : A 0 ⟶ A 1) (g : A 1 ⟶ A 2) (α : F 0 ⟶ F 1) (β : F 1 ⟶ F 2) (γ : F 2 ⟶ F 3)

def mk_functor' : snake_diagram ⥤ ℬ :=
mk_functor (λ i, (F i).obj ∘ A)
  /- FA₀₀ -/  ((F 0).map f)  /- FA₀₁ -/  ((F 0).map g)  /- FA₀₂ -/
  (α.app _)                  (α.app _)                  (α.app _)
  /- FA₁₀ -/  ((F 1).map f)  /- FA₁₁ -/  ((F 1).map g)  /- FA₁₂ -/
  (β.app _)                  (β.app _)                  (β.app _)
  /- FA₂₀ -/  ((F 2).map f)  /- FA₂₁ -/  ((F 2).map g)  /- FA₂₂ -/
  (γ.app _)                  (γ.app _)                  (γ.app _)
  /- FA₃₀ -/  ((F 3).map f)  /- FA₃₁ -/  ((F 3).map g)  /- FA₃₂ -/
(α.naturality _).symm (α.naturality _).symm
(β.naturality _).symm (β.naturality _).symm
(γ.naturality _).symm (γ.naturality _).symm

end

section

variables {𝒜 ℬ 𝒞 : Type*} [category 𝒜] [category ℬ] [category 𝒞]
variables (A : fin 3 → 𝒜 ⥤ ℬ) (F : fin 4 → ℬ ⥤ 𝒞)
variables (f : A 0 ⟶ A 1) (g : A 1 ⟶ A 2) (α : F 0 ⟶ F 1) (β : F 1 ⟶ F 2) (γ : F 2 ⟶ F 3)

def mk_functor'' : 𝒜 → snake_diagram ⥤ 𝒞 :=
λ x, mk_functor' ![(A 0).obj x, (A 1).obj x, (A 2).obj x] F (f.app x) (g.app x) α β γ

end

section

variables {𝒜 : Type*} [category 𝒜] [abelian 𝒜]

-- move (ang generalize) this
lemma exact_kernel_ι_self {A B : 𝒜} (f : A ⟶ B) : exact (kernel.ι f) f :=
by { rw abelian.exact_iff, tidy } -- why do we not have abelian.exact_kernel?

-- move this
lemma exact_self_cokernel_π {A B : 𝒜} (f : A ⟶ B) : exact f (cokernel.π f) :=
abelian.exact_cokernel _

local notation `kernel_map`   := kernel.map _ _ _ _
local notation `cokernel_map` := cokernel.map _ _ _ _

def mk_of_short_exact_sequence_hom (A B : short_exact_sequence 𝒜) (f : A ⟶ B) :
  snake_diagram ⥤ 𝒜 :=
mk_functor
/- == Passing in the matrix of objects first, to make Lean happy == -/
![![kernel f.1, kernel f.2, kernel f.3],
  ![A.1, A.2, A.3],
  ![B.1, B.2, B.3],
  ![cokernel f.1, cokernel f.2, cokernel f.3]]
/- == All the morphisms in the diagram == -/
  /- ker f.1 -/   (kernel_map f.sq1)   /- ker f.2 -/   (kernel_map f.sq2)   /- ker f.3 -/
  (kernel.ι _)                         (kernel.ι _)                         (kernel.ι _)
  /-   A.1   -/          A.f           /-   A.2   -/          A.g           /-   A.3   -/
       f.1                                  f.2                                  f.3
  /-   B.1   -/          B.f           /-   B.2   -/          B.g           /-   B.3   -/
  (cokernel.π _)                       (cokernel.π _)                       (cokernel.π _)
  /- coker f.1 -/ (cokernel_map f.sq1) /- coker f.2 -/ (cokernel_map f.sq2) /- coker f.3 -/
/- == Prove that the squares commute == -/
(by { delta kernel.map, rw [kernel.lift_ι] }) (by { delta kernel.map, rw [kernel.lift_ι] })
f.sq1 f.sq2
(by { delta cokernel.map, rw [cokernel.π_desc] }) (by { delta cokernel.map, rw [cokernel.π_desc] })
.

end

end snake_diagram

open snake_diagram (o hom)

example (i : fin 4) : o i 0 ⟶ o i 1 := hom (i,0) (i,1)

local notation x `⟶[`D`]` y := D.map (hom x y)

section definitions

variables (𝒜 : Type u) [category.{v} 𝒜] [has_images 𝒜] [has_zero_morphisms 𝒜] [has_kernels 𝒜]

variables {𝒜}

structure is_snake_input (D : snake_diagram ⥤ 𝒜) : Prop :=
(row_exact₁ : exact ((1,0) ⟶[D] (1,1)) ((1,1) ⟶[D] (1,2)))
(row_exact₂ : exact ((2,0) ⟶[D] (2,1)) ((2,1) ⟶[D] (2,2)))
(col_exact₁ : ∀ j, exact ((0,j) ⟶[D] (1,j)) ((1,j) ⟶[D] (2,j)))
(col_exact₂ : ∀ j, exact ((1,j) ⟶[D] (2,j)) ((2,j) ⟶[D] (3,j)))
(col_mono : ∀ j, mono ((0,j) ⟶[D] (1,j)))
(col_epi  : ∀ j, epi ((2,j) ⟶[D] (3,j)))
(row_mono : mono ((2,0) ⟶[D] (2,1)))
(row_epi  : epi ((1,1) ⟶[D] (1,2)))

namespace is_snake_input

variables {D : snake_diagram ⥤ 𝒜}

@[nolint unused_arguments]
lemma map_eq (hD : is_snake_input D) {x y : snake_diagram} (f g : x ⟶ y) : D.map f = D.map g :=
congr_arg _ (snake_diagram.hom_ext _ _)

@[nolint unused_arguments]
lemma map_eq_id (hD : is_snake_input D) {x : snake_diagram} (f : x ⟶ x) : D.map f = 𝟙 _ :=
by rw [snake_diagram.hom_ext f (𝟙 x), D.map_id]

lemma hom_eq_zero₁ (hD : is_snake_input D) {x y : snake_diagram} (f : x ⟶ y)
  (h : x.1 < 2 ∧ x.1 + 1 < y.1 . snake_diagram.hom_tac) : D.map f = 0 :=
begin
  cases x with i j, cases y with k l, cases h with h₀ h₁, rcases f with ⟨⟨⟨hik, hjl⟩⟩⟩,
  dsimp at h₀ h₁ hik hjl,
  let f₁ := hom (i,j) (i+1,j),
  let f₂ := hom (i+1,j) (i+2,j),
  let f₃ := hom (i+2,j) (k,l),
  calc D.map _
      = D.map ((f₁ ≫ f₂) ≫ f₃)             : hD.map_eq _ _
  ... = ((D.map f₁) ≫ D.map f₂) ≫ D.map f₃ : by simp only [D.map_comp]
  ... = 0 ≫ D.map f₃                        : _
  ... = 0                                   : zero_comp,
  congr' 1,
  obtain (rfl|rfl) : i = 0 ∨ i = 1, { dec_trivial! },
  { exact (hD.col_exact₁ j).w },
  { exact (hD.col_exact₂ j).w },
end
.

open snake_diagram

meta def aux_simp : tactic unit :=
`[dsimp only [snake_diagram.mk_of_short_exact_sequence_hom],
  simp only [mk_functor_map_f0, mk_functor_map_g0, mk_functor_map_a0, mk_functor_map_b0,
    mk_functor_map_c0, mk_functor_map_f1, mk_functor_map_g1, mk_functor_map_a1,
    mk_functor_map_b1, mk_functor_map_c1, mk_functor_map_f2, mk_functor_map_g2,
    mk_functor_map_a2, mk_functor_map_b2, mk_functor_map_c2, mk_functor_map_f3, mk_functor_map_g3]]

lemma mk_of_short_exact_sequence_hom {𝒜 : Type*} [category 𝒜] [abelian 𝒜]
  (A B : short_exact_sequence 𝒜) (f : A ⟶ B) :
  is_snake_input (snake_diagram.mk_of_short_exact_sequence_hom A B f) :=
{ row_exact₁ := by { aux_simp, exact A.exact' },
  row_exact₂ := by { aux_simp, exact B.exact' },
  col_exact₁ := λ j, by { fin_cases j; aux_simp, all_goals { apply exact_kernel_ι_self, } },
  col_exact₂ := λ j, by { fin_cases j; aux_simp, all_goals { apply exact_self_cokernel_π } },
  col_mono := λ j, by { fin_cases j; aux_simp, all_goals { apply_instance } },
  col_epi := λ j, by { fin_cases j; aux_simp, all_goals { apply_instance } },
  row_mono := by { aux_simp, exact B.mono' },
  row_epi := by { aux_simp, exact A.epi' }, }

end is_snake_input

end definitions

section

open abelian.pseudoelement

variables {𝒜 : Type u} [category.{v} 𝒜] [abelian 𝒜]
variables {D : snake_diagram ⥤ 𝒜}

namespace is_snake_input

local attribute [instance] abelian.pseudoelement.over_to_sort
  abelian.pseudoelement.hom_to_fun
  abelian.pseudoelement.has_zero

section move_me

local attribute [instance] abelian.pseudoelement.over_to_sort
  abelian.pseudoelement.hom_to_fun

lemma injective_iff_mono {P Q : 𝒜} (f : P ⟶ Q) : function.injective f ↔ mono f :=
⟨λ h, mono_of_zero_of_map_zero _ (zero_of_map_zero _ h),
  by introsI h; apply pseudo_injective_of_mono⟩

lemma surjective_iff_epi {P Q : 𝒜} (f : P ⟶ Q) : function.surjective f ↔ epi f :=
⟨epi_of_pseudo_surjective _, by introI h; apply pseudo_surjective_of_epi⟩

lemma exists_of_exact {P Q R : 𝒜} {f : P ⟶ Q} {g : Q ⟶ R} (e : exact f g) (q) (hq : g q = 0) :
  ∃ p, f p = q :=
(pseudo_exact_of_exact e).2 _ hq

lemma eq_zero_of_exact {P Q R : 𝒜} {f : P ⟶ Q} {g : Q ⟶ R} (e : exact f g) (p) : g (f p) = 0 :=
(pseudo_exact_of_exact e).1 _

@[simp]
lemma kernel_ι_apply {P Q : 𝒜} (f : P ⟶ Q) (a) : f (kernel.ι f a) = 0 :=
begin
  rw ← abelian.pseudoelement.comp_apply,
  simp,
end

-- (AT) I don't know if we actually want this lemma, but it came in handy below.
lemma eq_zero_iff_kernel_ι_eq_zero {P Q : 𝒜} (f : P ⟶ Q) (q) : kernel.ι f q = 0 ↔ q = 0 :=
begin
  split,
  { intro h,
    apply_fun kernel.ι f,
    simp [h],
    rw injective_iff_mono,
    apply_instance },
  { intro h,
    simp [h] },
end

@[simp]
lemma cokernel_π_apply {P Q : 𝒜} (f : P ⟶ Q) (a) : cokernel.π f (f a) = 0 :=
begin
  rw ← abelian.pseudoelement.comp_apply,
  simp,
end

lemma exists_of_cokernel_π_eq_zero {P Q : 𝒜} (f : P ⟶ Q) (a) :
  cokernel.π f a = 0 → ∃ b, f b = a :=
begin
  intro h,
  apply exists_of_exact _ _ h,
  apply snake_diagram.exact_self_cokernel_π,
end

lemma cokernel_π_surjective {P Q : 𝒜} (f : P ⟶ Q) : function.surjective (cokernel.π f) :=
begin
  rw surjective_iff_epi,
  apply_instance,
end

--move
lemma exact_is_iso_iff {P Q Q' R : 𝒜} (f : P ⟶ Q) (g : Q' ⟶ R) (e : Q ⟶ Q') [is_iso e] :
  exact f (e ≫ g) ↔ exact (f ≫ e) g :=
begin
  let E := as_iso e,
  change exact f (E.hom ≫ g) ↔ exact (f ≫ E.hom) g,
  conv_rhs { rw (show g = E.inv ≫ E.hom ≫ g, by simp) },
  rw exact_comp_hom_inv_comp_iff
end

--lemma exact_comp_is_iso {P Q R R' : 𝒜} (f : P ⟶ Q) (g : Q ⟶ R) (e : R ⟶ R') [is_iso e] :
--  exact f (g ≫ e) ↔ exact f g := exact_comp_iso

end move_me

lemma row_exact₀ (hD : is_snake_input D) : exact ((0,0) ⟶[D] (0,1)) ((0,1) ⟶[D] (0,2)) :=
begin
  refine exact_of_pseudo_exact _ _ ⟨λ a, _, _⟩,
  { apply_fun ((0,2) ⟶[D] (1,2)),
    swap, { rw injective_iff_mono, exact hD.col_mono _ },
    simp_rw [← abelian.pseudoelement.comp_apply, ← D.map_comp, abelian.pseudoelement.apply_zero],
    change D.map (hom (0,0) (1,0) ≫ hom (1,0) (1,1) ≫ hom (1,1) (1,2)) a = 0,
    simp [abelian.pseudoelement.comp_apply, eq_zero_of_exact hD.row_exact₁] },
  { intros b hb,
    apply_fun ((0,2) ⟶[D] (1,2)) at hb,
    simp_rw [← abelian.pseudoelement.comp_apply,
      ← D.map_comp, abelian.pseudoelement.apply_zero] at hb,
    change D.map (hom (0,1) (1,1) ≫ hom (1,1) (1,2)) b = 0 at hb,
    simp_rw [D.map_comp, abelian.pseudoelement.comp_apply] at hb,
    let b' := ((0,1) ⟶[D] (1,1)) b,
    change ((1,1) ⟶[D] (1,2)) b' = 0 at hb,
    obtain ⟨c,hc⟩ := exists_of_exact hD.row_exact₁ b' hb,
    have hcz : ((1,0) ⟶[D] (2,0)) c = 0,
    { apply_fun ((2,0) ⟶[D] (2,1)),
      swap, { rw injective_iff_mono, apply hD.row_mono },
      simp_rw [← abelian.pseudoelement.comp_apply, ← D.map_comp, abelian.pseudoelement.apply_zero],
      change D.map (hom (1,0) (1,1) ≫ hom (1,1) (2,1)) c = 0,
      simp_rw [D.map_comp, abelian.pseudoelement.comp_apply, hc],
      dsimp [b'],
      apply eq_zero_of_exact,
      apply hD.col_exact₁ },
    obtain ⟨d,hd⟩ := exists_of_exact (hD.col_exact₁ _) c hcz,
    use d,
    apply_fun ((0,1) ⟶[D] (1,1)),
    swap, { rw injective_iff_mono, exact hD.col_mono _ },
    dsimp only [b'] at hc,
    rw [← hc, ← hd],
    simp_rw [← abelian.pseudoelement.comp_apply, ← D.map_comp],
    refl }
end

lemma row_exact₃ (hD : is_snake_input D) : exact ((3,0) ⟶[D] (3,1)) ((3,1) ⟶[D] (3,2)) :=
begin
  refine exact_of_pseudo_exact _ _ ⟨λ a, _,λ b hb, _⟩,
  { obtain ⟨b, hb⟩ := (surjective_iff_epi ((2,0) ⟶[D] (3,0))).2 (hD.col_epi 0) a,
    rw [← hb, ← abelian.pseudoelement.comp_apply, ← abelian.pseudoelement.comp_apply,
      ← D.map_comp, ← D.map_comp, map_eq hD ((hom (2, 0) (3, 0)) ≫ (hom _ (3, 1)) ≫
      (hom _ (3, 2))) ((hom (2, 0) (2, 1)) ≫ (hom _ (2, 2)) ≫ (hom _ _)), ← category.assoc,
      D.map_comp _ (hom (2, 2) (3, 2)), D.map_comp, hD.row_exact₂.w, zero_comp, zero_apply] },
  { set f₁ := hom (2, 1) (2, 2),
    set f₂ := hom (2, 2) (3, 2),
    set f₃ := hom (1, 1) (2, 1),
    set f₄ := hom (2, 0) (3, 0),
    set f₅ := hom (3, 0) (3, 1),
    obtain ⟨c, hc⟩ := (surjective_iff_epi ((2,1) ⟶[D] (3,1))).2 (hD.col_epi 1) b,
    let d := D.map f₁ c,
    have hd : D.map f₂ d = 0,
    { rw [← abelian.pseudoelement.comp_apply, ← D.map_comp, map_eq hD ((hom (2, 1) (2, 2)) ≫
      (hom _ (3, 2))) ((hom (2, 1) (3, 1)) ≫ (hom _ (3, 2))), D.map_comp,
      abelian.pseudoelement.comp_apply, hc, hb] },
    obtain ⟨e, he⟩ := exists_of_exact (hD.col_exact₂ 2) d hd,
    obtain ⟨f, hf⟩ := (surjective_iff_epi ((1,1) ⟶[D] (1,2))).2 hD.row_epi e,
    have hfzero : ((2,1) ⟶[D] (3,1)) ((D.map f₃) f) = 0,
    { rw [← abelian.pseudoelement.comp_apply, (hD.col_exact₂ 1).w, zero_apply] },
    have hdiff : D.map f₁ c = D.map f₁ (D.map f₃ f),
    { rw [← abelian.pseudoelement.comp_apply, ← D.map_comp, map_eq hD ((hom (1, 1) (2, 1)) ≫
      (hom _ (2, 2))) ((hom (1, 1) (1, 2)) ≫ (hom _ (2, 2))), D.map_comp,
      abelian.pseudoelement.comp_apply, hf, he] },
    obtain ⟨g, ⟨hg₁, hg₂⟩⟩ := sub_of_eq_image _ _ _ hdiff,
    obtain ⟨h, hh⟩ := exists_of_exact hD.row_exact₂ g hg₁,
    use D.map f₄ h,
    rw [← abelian.pseudoelement.comp_apply, ← D.map_comp, map_eq hD
      ((hom (2, 0) (3, 0)) ≫ (hom _ (3, 1))) ((hom _ (2, 1)) ≫ (hom _ _)), D.map_comp,
      abelian.pseudoelement.comp_apply, hh, hg₂ _ ((2,1) ⟶[D] (3,1)) hfzero, hc] }
end

lemma row_exact (hD : is_snake_input D) (i : fin 4) :
  exact ((i,0) ⟶[D] (i,1)) ((i,1) ⟶[D] (i,2)) :=
by { fin_cases i, exacts [hD.row_exact₀, hD.row_exact₁, hD.row_exact₂, hD.row_exact₃] }

lemma hom_eq_zero₂ (hD : is_snake_input D) {x y : snake_diagram} (f : x ⟶ y)
  (h : x.2 = 0 ∧ y.2 = 2 . snake_diagram.hom_tac) : D.map f = 0 :=
begin
  cases x with i j, cases y with k l, rcases f with ⟨⟨⟨hik, hjl⟩⟩⟩,
  dsimp at h hik hjl, rcases h with ⟨rfl, rfl⟩,
  let f₁ := hom (i,0) (i,1),
  let f₂ := hom (i,1) (i,2),
  let f₃ := hom (i,2) (k,2),
  calc D.map _
      = D.map ((f₁ ≫ f₂) ≫ f₃)             : hD.map_eq _ _
  ... = ((D.map f₁) ≫ D.map f₂) ≫ D.map f₃ : by simp only [D.map_comp]
  ... = 0                                    : by rw [(hD.row_exact i).w, zero_comp]
end

section long_snake

lemma ker_row₁_to_row₂ (hD : is_snake_input D) :
  (kernel.ι ((1,0) ⟶[D] (1,1))) ≫ ((1,0) ⟶[D] (2,0)) = 0 :=
begin
  refine zero_morphism_ext _ (λ a, (injective_iff_mono ((2,0) ⟶[D] (2,1))).2 hD.row_mono _),
  rw [apply_zero, ← abelian.pseudoelement.comp_apply, category.assoc,
    abelian.pseudoelement.comp_apply, ← D.map_comp, map_eq hD
    ((hom (1, 0) (2, 0)) ≫ (hom _ (2, 1))) ((hom _ (1, 1)) ≫ (hom _ _)), D.map_comp,
    abelian.pseudoelement.comp_apply, kernel_ι_apply, apply_zero]
end

def ker_row₁_to_top_left (hD : is_snake_input D) : kernel ((1,0) ⟶[D] (1,1)) ⟶ D.obj (0, 0) :=
by { letI := hD.col_mono 0, exact (limits.kernel.lift _ _ (ker_row₁_to_row₂ hD)) ≫
    (limits.kernel.lift _ _ (((abelian.exact_iff _ _).1 (hD.col_exact₁ 0)).2)) ≫
    inv (abelian.factor_thru_image ((0,0) ⟶[D] (1,0))) }

lemma ker_row₁_to_top_left_mono (hD : is_snake_input D) : mono (ker_row₁_to_top_left hD) :=
begin
  suffices : mono ((limits.kernel.lift _ _ (ker_row₁_to_row₂ hD)) ≫
    (limits.kernel.lift _ _ (((abelian.exact_iff _ _).1 (hD.col_exact₁ 0)).2))),
  { letI := this, exact mono_comp _ _, },
  exact mono_comp _ _
end

lemma ker_row₁_to_top_left_comp_eq_ι (hD : is_snake_input D) : ker_row₁_to_top_left hD ≫
  ((0,0) ⟶[D] (1,0)) = kernel.ι ((1,0) ⟶[D] (1,1)) :=
begin
  letI := hD.col_mono 0,
  have : inv (abelian.factor_thru_image ((0,0) ⟶[D] (1,0))) ≫ ((0,0) ⟶[D] (1,0)) =
    category_theory.abelian.image.ι _ := by simp,
  rw [ker_row₁_to_top_left, category.assoc, category.assoc, this],
  simp
end

lemma long_row₀_exact (hD : is_snake_input D) :
  exact (ker_row₁_to_top_left hD) ((0,0) ⟶[D] (0,1)) :=
begin
  refine abelian.pseudoelement.exact_of_pseudo_exact _ _ ⟨λ a, _, λ a ha, _⟩,
  { refine (injective_iff_mono _).2 (hD.col_mono _) _,
    rw [apply_zero, ← abelian.pseudoelement.comp_apply, ← D.map_comp, map_eq hD
      ((hom (0, 0) (0, 1)) ≫ (hom _ (1, 1))) ((hom _ (1, 0)) ≫ (hom _ _)), D.map_comp,
      ← abelian.pseudoelement.comp_apply, ← category.assoc, ker_row₁_to_top_left_comp_eq_ι hD,
      abelian.pseudoelement.comp_apply, kernel_ι_apply] },
  { let b := ((0,0) ⟶[D] (1,0)) a,
    have hb : ((1,0) ⟶[D] (1,1)) b = 0,
    { rw [← abelian.pseudoelement.comp_apply, ← D.map_comp, map_eq hD
        ((hom (0, 0) (1, 0)) ≫ (hom _ (1, 1))) ((hom _ (0, 1)) ≫ (hom _ _)), D.map_comp,
        abelian.pseudoelement.comp_apply, ha, apply_zero] },
    obtain ⟨c, hc⟩ := exists_of_exact category_theory.exact_kernel_ι _ hb,
    refine ⟨c, (injective_iff_mono _).2 (hD.col_mono _) _⟩,
    rw [← abelian.pseudoelement.comp_apply, ker_row₁_to_top_left_comp_eq_ι hD, hc] }
end

lemma row₁_middle_to_coker_row₂_eq_zero (hD : is_snake_input D) :
   ((1,1) ⟶[D] (1,2)) ≫ ((1,2) ⟶[D] (2,2)) ≫ (limits.cokernel.π ((2,1) ⟶[D] (2,2))) = 0 :=
begin
  refine zero_morphism_ext _ (λ a, _),
  rw [← category.assoc, abelian.pseudoelement.comp_apply, ← D.map_comp, map_eq hD
    ((hom (1, 1) (1, 2)) ≫ (hom _ (2, 2))) ((hom _ (2, 1)) ≫ (hom _ _)), D.map_comp,
    ← abelian.pseudoelement.comp_apply],
  simp,
end

lemma row₁_to_coker_row₂_eq_zero (hD : is_snake_input D) :
  ((1,2) ⟶[D] (2,2)) ≫ (limits.cokernel.π ((2,1) ⟶[D] (2,2))) = 0 :=
begin
  letI := hD.row_epi,
  have := row₁_middle_to_coker_row₂_eq_zero hD,
  rw [← limits.comp_zero] at this,
  exact (cancel_epi _).1 this
end

lemma ker_col₂_to_coker_row₂_eq_zero (hD : is_snake_input D) :
  kernel.ι ((2,2) ⟶[D] (3,2)) ≫ (limits.cokernel.π ((1,2) ⟶[D] (2,2))) = 0 :=
begin
  refine zero_morphism_ext _ (λ a, _),
  obtain ⟨c, hc⟩ := exists_of_exact (hD.col_exact₂ 2) (kernel.ι (_ ⟶[D] _) a) (kernel_ι_apply _ _),
  rw [abelian.pseudoelement.comp_apply, ← hc, cokernel_π_apply]
end

def bottom_right_to_coker_row₂ (hD : is_snake_input D) :
  D.obj (3, 2) ⟶ cokernel ((2,1) ⟶[D] (2,2)) :=
by { letI := hD.col_epi 2, exact
  (inv (abelian.factor_thru_coimage ((2,2) ⟶[D] (3,2)))) ≫
  (limits.cokernel.desc _ _ (ker_col₂_to_coker_row₂_eq_zero hD)) ≫
  (limits.cokernel.desc _ _ (row₁_to_coker_row₂_eq_zero hD)) }

lemma bottom_right_to_coker_row₂_epi (hD : is_snake_input D) : epi (bottom_right_to_coker_row₂ hD) :=
begin
  suffices : epi ((limits.cokernel.desc _ _ (ker_col₂_to_coker_row₂_eq_zero hD)) ≫
    (limits.cokernel.desc _ _ (row₁_to_coker_row₂_eq_zero hD))),
  { letI := this, exact epi_comp _ _ },
  exact epi_comp _ _,
end

lemma bottom_right_to_coker_row₂_comp_eq_π (hD : is_snake_input D) : ((2,2) ⟶[D] (3,2))  ≫
  bottom_right_to_coker_row₂ hD = cokernel.π ((2,1) ⟶[D] (2,2)) :=
begin
  letI := hD.col_epi 2,
  have : ((2,2) ⟶[D] (3,2)) ≫ inv (abelian.factor_thru_coimage ((2,2) ⟶[D] (3,2))) =
    category_theory.abelian.coimage.π _ := by simp,
  rw [bottom_right_to_coker_row₂, ← category.assoc, ← category.assoc, this],
  simp
end

lemma long_row₃_exact (hD : is_snake_input D) :
  exact ((3,1) ⟶[D] (3,2)) (bottom_right_to_coker_row₂ hD) :=
begin
  refine abelian.pseudoelement.exact_of_pseudo_exact _ _ ⟨λ a, _, λ a ha, _⟩,
  { letI := hD.col_epi 1,
    obtain ⟨b, hb⟩ := abelian.pseudoelement.pseudo_surjective_of_epi ((2,1) ⟶[D] (3,1)) a,
    rw [← hb, ← abelian.pseudoelement.comp_apply, ← abelian.pseudoelement.comp_apply,
      ← category.assoc, ← D.map_comp, map_eq hD ((hom (2, 1) (3, 1)) ≫ (hom _ (3, 2)))
      ((hom _ (2, 2)) ≫ (hom _ _)), D.map_comp, category.assoc,
      bottom_right_to_coker_row₂_comp_eq_π hD, (snake_diagram.exact_self_cokernel_π _).w,
      zero_apply], },
  { letI := hD.col_epi 2,
    obtain ⟨b, hb⟩ := abelian.pseudoelement.pseudo_surjective_of_epi ((2,2) ⟶[D] (3,2)) a,
    rw [← hb, ← abelian.pseudoelement.comp_apply, bottom_right_to_coker_row₂_comp_eq_π hD] at ha,
    obtain ⟨c, hc⟩ := exists_of_exact (abelian.exact_cokernel _) _ ha,
    refine ⟨((2,1) ⟶[D] (3,1)) c, _⟩,
    rw [← hb, ← hc, ← abelian.pseudoelement.comp_apply, ← abelian.pseudoelement.comp_apply,
      ← D.map_comp, map_eq hD ((hom (2, 1) (3, 1)) ≫ (hom _ (3, 2))) ((hom _ (2, 2)) ≫ (hom _ _)),
      D.map_comp] }
end

end long_snake

example (hD : is_snake_input D) (f : (o 1 0) ⟶ (o 2 2)) : D.map f = 0 := hD.hom_eq_zero₂ f

section delta

variable (hD : is_snake_input D)
include hD

def to_top_right_kernel : D.obj (1,0) ⟶ kernel ((1,1) ⟶[D] (2,2)) :=
kernel.lift _ (_ ⟶[D] _)
begin
  rw ← D.map_comp,
  change D.map (hom (1,0) (2,0) ≫ hom (2,0) (2,1) ≫ hom (2,1) (2,2)) = 0,
  simp [hD.row_exact₂.1],
end

def cokernel_to_top_right_kernel_to_right_kernel :
  cokernel hD.to_top_right_kernel ⟶ kernel ((1,2) ⟶[D] (2,2)) :=
cokernel.desc _ (kernel.lift _ (kernel.ι _ ≫ (_ ⟶[D] _)) begin
  rw [category.assoc, ← D.map_comp],
  have : hom (1,1) (1,2) ≫ hom (1,2) (2,2) = hom (1,1) (2,2) := rfl,
  rw this, clear this,
  simp [abelian.pseudoelement.comp_apply],
end) begin
  dsimp only [to_top_right_kernel],
  ext a,
  apply_fun kernel.ι (D.map (hom (1, 2) (2, 2))),
  swap, { rw injective_iff_mono, apply_instance },
  simp [← abelian.pseudoelement.comp_apply, hD.row_exact₁.1],
end

instance : mono hD.cokernel_to_top_right_kernel_to_right_kernel :=
begin
  sorry,
  /-apply mono_of_zero_of_map_zero,
  intros a h,
  obtain ⟨b,rfl⟩ := cokernel_π_surjective _ a,
  rw ← eq_zero_iff_kernel_ι_eq_zero at h,
  simp [← abelian.pseudoelement.comp_apply, cokernel_to_top_right_kernel_to_right_kernel] at h,
  simp [ abelian.pseudoelement.comp_apply] at h,
  have : ∃ c, ((1,0) ⟶[D] (1,1)) c = kernel.ι ((1,1) ⟶[D] (2,2)) b,
  { apply exists_of_exact _ _ h,
    exact hD.row_exact₁ },
  obtain ⟨c,hc⟩ := this,
  let f : cokernel hD.to_top_right_kernel ⟶ cokernel ((1,0) ⟶[D] (1,1)) :=
    cokernel.desc _ _ _,
  swap, { refine kernel.ι _ ≫ cokernel.π _ },
  swap, { simp [to_top_right_kernel] },
  apply_fun f,
  swap, {
    rw injective_iff_mono,
    apply mono_of_zero_of_map_zero,
    intros a ha,
    dsimp [f] at ha,
    obtain ⟨a,rfl⟩ := cokernel_π_surjective _ a,
    simp [← abelian.pseudoelement.comp_apply] at ha,
    simp [abelian.pseudoelement.comp_apply] at ha,
    have : ∃ c, ((1,0) ⟶[D] (1,1)) c = kernel.ι ((1,1) ⟶[D] (2,2)) a,
    { apply exists_of_exact _ _ ha,
      apply snake_diagram.exact_self_cokernel_π, },
    obtain ⟨c,hc⟩ := this,
    have : hD.to_top_right_kernel c = a,
    { apply_fun kernel.ι ((1,1) ⟶[D] (2,2)),
      swap, { rw injective_iff_mono, apply_instance },
      dsimp [to_top_right_kernel],
      simp [← abelian.pseudoelement.comp_apply],
      erw kernel.lift_ι,
      exact hc },
    simp [← this] },
  dsimp only [f],
  simp [← abelian.pseudoelement.comp_apply, to_top_right_kernel],
  simp [abelian.pseudoelement.comp_apply, ← hc],-/
end .

instance : epi hD.cokernel_to_top_right_kernel_to_right_kernel :=
begin
  apply epi_of_pseudo_surjective,
  intros a,
  let a' := kernel.ι ((1,2) ⟶[D] (2,2)) a,
  obtain ⟨b,hb⟩ : ∃ b, ((1,1) ⟶[D] (1,2)) b = a',
  { suffices : function.surjective ((1,1) ⟶[D] (1,2)), by apply this,
    rw surjective_iff_epi,
    apply hD.row_epi },
  obtain ⟨c,hc⟩ : ∃ c, kernel.ι ((1,1) ⟶[D] (2,2)) c = b,
  { have : exact (kernel.ι ((1,1) ⟶[D] (2,2))) ((1,1) ⟶[D] (2,2)) := exact_kernel_ι,
    apply exists_of_exact this,
    rw [(show hom (1,1) (2,2) = hom (1,1) (1,2) ≫ hom (1,2) (2,2), by refl),
      D.map_comp, abelian.pseudoelement.comp_apply, hb],
    dsimp only [a'],
    simp },
  use cokernel.π hD.to_top_right_kernel c,
  apply_fun kernel.ι ((1,2) ⟶[D] (2,2)),
  swap, { rw injective_iff_mono, apply_instance },
  dsimp only [to_top_right_kernel, cokernel_to_top_right_kernel_to_right_kernel],
  simp [← abelian.pseudoelement.comp_apply],
  change _ = a',
  rw ← hb,
  simp [← hb, abelian.pseudoelement.comp_apply, ← hc],
end .

instance : is_iso hD.cokernel_to_top_right_kernel_to_right_kernel :=
is_iso_of_mono_of_epi _

def bottom_left_cokernel_to : cokernel ((1,0) ⟶[D] (2,1)) ⟶ D.obj (2,2) :=
cokernel.desc _ (_ ⟶[D] _)
begin
  rw ← D.map_comp,
  change D.map (hom (1,0) (2,0) ≫ hom (2,0) (2,1) ≫ hom (2,1) (2,2)) = 0,
  simp_rw D.map_comp,
  simp [hD.row_exact₂.1],
end

def left_cokernel_to_kernel_bottom_left_cokernel_to :
  cokernel ((1,0) ⟶[D] (2,0)) ⟶ kernel hD.bottom_left_cokernel_to :=
kernel.lift _ (cokernel.desc _ ((_ ⟶[D] _) ≫ cokernel.π _) begin
  rw [← category.assoc, ← D.map_comp],
  have : hom (1,0) (2,0) ≫ hom (2,0) (2,1) = hom _ _ := rfl,
  rw this, clear this,
  simp [abelian.pseudoelement.comp_apply],
end) begin
  dsimp only [bottom_left_cokernel_to],
  ext a,
  obtain ⟨b,rfl⟩ : ∃ b, cokernel.π ((1,0) ⟶[D] (2,0)) b = a,
  { have : function.surjective (cokernel.π ((1,0) ⟶[D] (2,0))),
    by { rw surjective_iff_epi, apply_instance },
    apply this },
  simp [← abelian.pseudoelement.comp_apply, hD.row_exact₂.1],
end

instance : mono hD.left_cokernel_to_kernel_bottom_left_cokernel_to :=
begin
  apply mono_of_zero_of_map_zero,
  intros a ha,
  obtain ⟨a,rfl⟩ := cokernel_π_surjective _ a,
  dsimp [left_cokernel_to_kernel_bottom_left_cokernel_to] at ha,
  rw ← eq_zero_iff_kernel_ι_eq_zero at ha,
  simp [← abelian.pseudoelement.comp_apply] at ha,
  simp [abelian.pseudoelement.comp_apply] at ha,
  obtain ⟨c,hc⟩ : ∃ c, ((1,0) ⟶[D] (2,1)) c = ((2,0) ⟶[D] (2,1)) a,
  { apply exists_of_exact _ _ ha,
    apply abelian.exact_cokernel, },
  have : ((1,0) ⟶[D] (2,0)) c = a,
  { apply_fun ((2,0) ⟶[D] (2,1)),
    swap, { rw injective_iff_mono, apply hD.row_mono },
    simpa only [← hc, ← abelian.pseudoelement.comp_apply, ← D.map_comp] },
  simp [← this],
end .

instance : epi hD.left_cokernel_to_kernel_bottom_left_cokernel_to :=
begin
  apply epi_of_pseudo_surjective,
  intros a,
  let a' := kernel.ι hD.bottom_left_cokernel_to a,
  obtain ⟨b,hb⟩ := cokernel_π_surjective _ a',
  have : ((2,1) ⟶[D] (2,2)) b = 0,
  { apply_fun hD.bottom_left_cokernel_to at hb,
    dsimp [a', bottom_left_cokernel_to] at hb,
    simpa [← abelian.pseudoelement.comp_apply] using hb },
  obtain ⟨c,hc⟩ : ∃ c, ((2,0) ⟶[D] (2,1)) c = b,
  { apply exists_of_exact _ _ this,
    exact hD.row_exact₂ },
  use cokernel.π ((1,0) ⟶[D] (2,0)) c,
  apply_fun kernel.ι hD.bottom_left_cokernel_to,
  swap, { rw injective_iff_mono, apply_instance },
  change _ = a',
  simp [← abelian.pseudoelement.comp_apply, ← hb,
    left_cokernel_to_kernel_bottom_left_cokernel_to],
  simp [abelian.pseudoelement.comp_apply, hc],
end

instance : is_iso hD.left_cokernel_to_kernel_bottom_left_cokernel_to :=
is_iso_of_mono_of_epi _

def δ_aux : cokernel hD.to_top_right_kernel ⟶ kernel hD.bottom_left_cokernel_to :=
cokernel.desc _ (kernel.lift _ (kernel.ι _ ≫ (_ ⟶[D] _) ≫ cokernel.π _) begin
  dsimp only [bottom_left_cokernel_to],
  simp,
  rw ← D.map_comp,
  have : hom (1,1) (2,1) ≫ hom (2,1) (2,2) = hom _ _ := rfl,
  rw this,
  simp [abelian.pseudoelement.comp_apply],
end)
begin
  dsimp only [to_top_right_kernel],
  simp,
  ext,
  apply_fun kernel.ι hD.bottom_left_cokernel_to,
  swap, { rw injective_iff_mono, apply_instance },
  simp [← abelian.pseudoelement.comp_apply],
  rw [← category.assoc, ← D.map_comp],
  have : hom (1,0) (1,1) ≫ hom (1,1) (2,1) = hom _ _, refl, rw this, clear this,
  simp [abelian.pseudoelement.comp_apply],
end

def to_kernel : D.obj (0,2) ⟶ kernel ((1,2) ⟶[D] (2,2)) :=
kernel.lift _ (_ ⟶[D] _) (hD.col_exact₁ _).1

instance : mono hD.to_kernel :=
begin
  dsimp [to_kernel],
  haveI : mono ((0,2) ⟶[D] (1,2)) := hD.col_mono _,
  apply_instance,
end

instance : epi hD.to_kernel :=
kernel.lift.epi (hD.col_exact₁ _)

instance : is_iso hD.to_kernel :=
is_iso_of_mono_of_epi _

def cokernel_to : cokernel ((1,0) ⟶[D] (2,0)) ⟶ D.obj (3,0) :=
cokernel.desc _ (_ ⟶[D] _) (hD.col_exact₂ _).1

instance : mono hD.cokernel_to :=
abelian.category_theory.limits.cokernel.desc.category_theory.mono _ _ (hD.col_exact₂ _)

instance : epi hD.cokernel_to :=
begin
  dsimp [cokernel_to],
  haveI : epi ((2,0) ⟶[D] (3,0)) := hD.col_epi _,
  apply_instance,
end

instance : is_iso hD.cokernel_to :=
is_iso_of_mono_of_epi _

def δ : D.obj (0,2) ⟶ D.obj (3,0) :=
  hD.to_kernel ≫ inv hD.cokernel_to_top_right_kernel_to_right_kernel ≫  -- <-- this is an iso
  hD.δ_aux ≫ -- <- this is the key
  inv hD.left_cokernel_to_kernel_bottom_left_cokernel_to ≫ hD.cokernel_to -- <-- this is an iso

def to_δ_aux : D.obj (0,1) ⟶ cokernel hD.to_top_right_kernel :=
kernel.lift _ ((0,1) ⟶[D] (1,1)) begin
  rw [(show (hom (1,1) (2,2) = hom (1,1) (2,1) ≫ hom _ _), by refl), D.map_comp,
    ← category.assoc, (hD.col_exact₁ _).1],
  simp,
end ≫ cokernel.π _

def from_δ_aux : kernel hD.bottom_left_cokernel_to ⟶ D.obj (3,1) :=
kernel.ι _ ≫ cokernel.desc _ ((2,1) ⟶[D] (3,1)) begin
  rw [(show hom (1,0) (2,1) = hom (1,0) (1,1) ≫ hom (1,1) (2,1), by refl),
    D.map_comp, category.assoc, (hD.col_exact₂ _).w],
  simp,
end

theorem exact_to_δ_aux : exact hD.to_δ_aux hD.δ_aux :=
begin
  apply exact_of_pseudo_exact,
  split,
  { intros a,
    dsimp [δ_aux, to_δ_aux],
    rw ← eq_zero_iff_kernel_ι_eq_zero,
    simp only [←abelian.pseudoelement.comp_apply, cokernel.π_desc,
      kernel.lift_ι_assoc, category.assoc, kernel.lift_ι],
    simp [abelian.pseudoelement.comp_apply, eq_zero_of_exact (hD.col_exact₁ _)] },
  { intros b hb,
    obtain ⟨b,rfl⟩ := cokernel_π_surjective _ b,
    dsimp [δ_aux] at hb,
    rw ← eq_zero_iff_kernel_ι_eq_zero at hb,
    simp only [←abelian.pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι] at hb,
    simp only [abelian.pseudoelement.comp_apply] at hb,
    let b' := kernel.ι ((1,1) ⟶[D] (2,2)) b,
    obtain ⟨c,hc⟩ := exists_of_cokernel_π_eq_zero _ _ hb, clear hb,
    change _ = ((1,1) ⟶[D] (2,1)) b' at hc,
    rw [(show hom (1,0) (2,1) = hom (1,0) (1,1) ≫ hom _ _, by refl), D.map_comp,
      abelian.pseudoelement.comp_apply] at hc,
    obtain ⟨z,h1,h2⟩ := sub_of_eq_image _ _ _ hc.symm, clear hc,
    specialize h2 _ ((1,1) ⟶[D] (1,2)) (eq_zero_of_exact hD.row_exact₁ _),
    obtain ⟨w,hw⟩ : ∃ w, ((0,1) ⟶[D] (1,1)) w = z := exists_of_exact (hD.col_exact₁ _) _ h1,
    clear h1,
    use w,
    dsimp only [b'] at h2,
    dsimp only [to_δ_aux],
    simp only [abelian.pseudoelement.comp_apply],
    apply_fun hD.cokernel_to_top_right_kernel_to_right_kernel,
    swap, { rw injective_iff_mono, apply_instance },
    dsimp only [cokernel_to_top_right_kernel_to_right_kernel],
    simp only [←abelian.pseudoelement.comp_apply, cokernel.π_desc, category.assoc],
    simp only [abelian.pseudoelement.comp_apply],
    apply_fun kernel.ι ((1,2) ⟶[D] (2,2)),
    swap, { rw injective_iff_mono, apply_instance },
    simp only [←abelian.pseudoelement.comp_apply, kernel.lift_ι_assoc,
      category.assoc, kernel.lift_ι],
    simp only [abelian.pseudoelement.comp_apply],
    rw [hw, h2] }
end

theorem exact_from_δ_aux : exact hD.δ_aux hD.from_δ_aux :=
begin
  apply exact_of_pseudo_exact,
  split,
  { intros a,
    dsimp [δ_aux, from_δ_aux],
    obtain ⟨a,rfl⟩ := cokernel_π_surjective _ a,
    simp only [←abelian.pseudoelement.comp_apply,
      cokernel.π_desc, kernel.lift_ι_assoc, category.assoc],
    simp [abelian.pseudoelement.comp_apply, eq_zero_of_exact (hD.col_exact₂ _)] },
  { intros b hb,
    let b' := kernel.ι hD.bottom_left_cokernel_to b,
    obtain ⟨c,hc⟩ := cokernel_π_surjective _ b',
    simp only [from_δ_aux, abelian.pseudoelement.comp_apply] at hb,
    change cokernel.desc ((1,0) ⟶[D] (2,1)) _ _ b' = 0 at hb,
    rw ← hc at hb,
    simp only [←abelian.pseudoelement.comp_apply, cokernel.π_desc] at hb,
    obtain ⟨d,hd⟩ : ∃ d, ((1,1) ⟶[D] (2,1)) d = c := exists_of_exact (hD.col_exact₂ _) _ hb,
    obtain ⟨e,he⟩ : ∃ e, kernel.ι ((1,1) ⟶[D] (2,2)) e = d,
    { apply exists_of_exact _ _ (_ : ((1,1) ⟶[D] (2,2)) d = 0),
      { apply exact_kernel_ι },
      dsimp [b'] at hc,
      apply_fun hD.bottom_left_cokernel_to at hc,
      simp only [bottom_left_cokernel_to, ←abelian.pseudoelement.comp_apply, cokernel.π_desc] at hc,
      rw [(show hom (1,1) (2,2) = hom (1,1) (2,1) ≫ hom (2,1) (2,2), by refl), D.map_comp,
        abelian.pseudoelement.comp_apply, hd, hc],
      simp only [abelian.pseudoelement.comp_apply],
      change hD.bottom_left_cokernel_to (kernel.ι hD.bottom_left_cokernel_to b) = 0,
      apply kernel_ι_apply },
    use cokernel.π hD.to_top_right_kernel e,
    apply_fun kernel.ι hD.bottom_left_cokernel_to,
    swap, { rw injective_iff_mono, apply_instance },
    change _ = b',
    dsimp [δ_aux],
    simp only [←abelian.pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι],
    simp only [abelian.pseudoelement.comp_apply],
    rw [he, hd, hc] }
end

theorem exact_to_δ : exact ((0,1) ⟶[D] (0,2)) hD.δ :=
begin
  dsimp [δ],
  rw [exact_is_iso_iff, exact_is_iso_iff, exact_comp_iso],
  convert hD.exact_to_δ_aux using 1,
  rw is_iso.comp_inv_eq,
  dsimp [to_kernel, to_δ_aux, cokernel_to_top_right_kernel_to_right_kernel],
  ext,
  simp only [cokernel.π_desc, kernel.lift_ι_assoc, category.assoc, kernel.lift_ι],
  simpa only [← D.map_comp],
end

theorem exact_from_δ : exact hD.δ ((3,0) ⟶[D] (3,1)) :=
begin
  dsimp [δ],
  rw [← category.assoc, ← category.assoc, ← exact_is_iso_iff, exact_iso_comp],
  convert hD.exact_from_δ_aux using 1,
  rw [category.assoc, is_iso.inv_comp_eq],
  dsimp [cokernel_to, left_cokernel_to_kernel_bottom_left_cokernel_to, from_δ_aux],
  ext,
  simp only [cokernel.π_desc, kernel.lift_ι_assoc, cokernel.π_desc_assoc, category.assoc],
  simpa only [← D.map_comp],
end

end delta

section delta_spec

variables (hD : is_snake_input D)

def to_kernel' : kernel ((1,1) ⟶[D] (2,2)) ⟶ D.obj (0,2) :=
kernel.lift _ (kernel.ι _ ≫ D.map (hom (1,1) (1,2))) begin
  erw [category.assoc, ← D.map_comp, kernel.condition],
end ≫ inv hD.to_kernel

instance to_kernel_epi : epi hD.to_kernel' :=
begin
  dsimp [to_kernel'],
  apply_with epi_comp { instances := ff }, swap, apply_instance,
  haveI : epi ((1,1) ⟶[D] (1,2)) := hD.row_epi,
  replace hh := pseudo_surjective_of_epi ((1,1) ⟶[D] (1,2)),
  apply epi_of_pseudo_surjective,
  intros t,
  obtain ⟨s,hs⟩ := hh (kernel.ι ((1,2) ⟶[D] (2,2)) t),
  obtain ⟨w,hw⟩ : ∃ w, kernel.ι ((1,1) ⟶[D] (2,2)) w = s,
  { have : exact (kernel.ι ((1,1) ⟶[D] (2,2))) ((1,1) ⟶[D] (2,2)) :=
      exact_kernel_ι,
    replace this := pseudo_exact_of_exact this,
    apply this.2,
    rw [(show (hom (1,1) (2,2)) = hom (1,1) (1,2) ≫ hom (1,2) (2,2), by refl),
      functor.map_comp, abelian.pseudoelement.comp_apply, hs,
      ← abelian.pseudoelement.comp_apply, kernel.condition,
      abelian.pseudoelement.zero_apply] },
  use w,
  apply abelian.pseudoelement.pseudo_injective_of_mono
    (kernel.ι ((1,2) ⟶[D] (2,2))),
  rw [← hs, ← abelian.pseudoelement.comp_apply, kernel.lift_ι,
    abelian.pseudoelement.comp_apply, hw],
end

def cokernel_to' : D.obj (3,0) ⟶ cokernel ((1,0) ⟶[D] (2,1)) :=
inv hD.cokernel_to ≫ cokernel.desc _ (D.map (hom (2,0) (2,1)) ≫ cokernel.π _) begin
  erw [← category.assoc, ← D.map_comp, cokernel.condition],
end

instance cokernel_to'_mono : mono hD.cokernel_to' := begin
  dsimp [cokernel_to'],
  apply_with mono_comp { instances := ff }, apply_instance,
  apply abelian.pseudoelement.mono_of_zero_of_map_zero,
  intros a ha,
  obtain ⟨b,rfl⟩ : ∃ b, cokernel.π ((1,0) ⟶[D] (2,0)) b = a,
  { apply abelian.pseudoelement.pseudo_surjective_of_epi },
  rw [← abelian.pseudoelement.comp_apply, cokernel.π_desc,
    abelian.pseudoelement.comp_apply] at ha,
  obtain ⟨c,hc⟩ : ∃ c, ((1,0) ⟶[D] (2,1)) c = ((2,0) ⟶[D] (2,1)) b,
  { have : exact ((1,0) ⟶[D] (2,1)) (cokernel.π _) := abelian.exact_cokernel _,
    replace this := pseudo_exact_of_exact this,
    apply this.2,
    exact ha },
  have hc' : ((1,0) ⟶[D] (2,0)) c = b,
  { haveI : mono ((2,0) ⟶[D] (2,1)) := hD.row_mono,
    apply abelian.pseudoelement.pseudo_injective_of_mono ((2,0) ⟶[D] (2,1)),
    rw [← abelian.pseudoelement.comp_apply, ← D.map_comp],
    exact hc },
  rw [← hc', ← abelian.pseudoelement.comp_apply, cokernel.condition,
    abelian.pseudoelement.zero_apply],
end

lemma δ_spec : hD.to_kernel' ≫ hD.δ ≫ hD.cokernel_to' =
  kernel.ι _ ≫ D.map (hom (1,1) (2,1)) ≫ cokernel.π _ :=
begin
  dsimp only [is_snake_input.δ ,is_snake_input.to_kernel', is_snake_input.cokernel_to'],
  simp only [category.assoc, is_iso.hom_inv_id_assoc, is_iso.inv_hom_id_assoc],
  dsimp only [is_snake_input.cokernel_to_top_right_kernel_to_right_kernel],
  dsimp only [is_snake_input.left_cokernel_to_kernel_bottom_left_cokernel_to],
  dsimp only [is_snake_input.δ_aux],
  let t := _, change _ ≫ _ ≫ _ ≫ t = _,
  have ht : t = kernel.ι _,
  { dsimp [t],
    rw is_iso.inv_comp_eq,
    apply coequalizer.hom_ext,
    simp only [cokernel.π_desc, category.assoc, kernel.lift_ι, cokernel.π_desc_assoc] },
  rw ht, clear ht, clear t,
  let t := _, change t ≫ _ = _,
  let s := _, change t ≫ s ≫ _ = _,
  have hst : t ≫ s = cokernel.π _,
  { dsimp [s,t],
    rw is_iso.comp_inv_eq,
    apply equalizer.hom_ext,
    simp only [cokernel.π_desc] },
  rw reassoc_of hst, clear hst, clear s, clear t,
  simp only [cokernel.π_desc_assoc, kernel.lift_ι],
end

lemma eq_δ_of_spec (e : D.obj (0,2) ⟶ D.obj (3,0))
  (he : hD.to_kernel' ≫ e ≫ hD.cokernel_to' = kernel.ι _ ≫
    D.map (hom (1,1) (2,1)) ≫ cokernel.π _) :
  e = hD.δ :=
begin
  rw ← cancel_mono hD.cokernel_to',
  rw ← cancel_epi hD.to_kernel',
  rw [he, δ_spec],
end

end delta_spec

local attribute [instance] limits.has_zero_object.has_zero

lemma exact_zero_to_ker_row₁_to_top_left (hD : is_snake_input D) :
  exact (0 : 0 ⟶ kernel ((1,0) ⟶[D] (1,1))) hD.ker_row₁_to_top_left :=
begin
  haveI : mono hD.ker_row₁_to_top_left := ker_row₁_to_top_left_mono hD,
  apply exact_zero_left_of_mono,
end

lemma exact_bottom_right_to_coker_row₂_to_zero (hD : is_snake_input D) :
  exact hD.bottom_right_to_coker_row₂ (0 : cokernel ((2,1) ⟶[D] (2,2)) ⟶ 0) :=
begin
  rw ← epi_iff_exact_zero_right,
  apply bottom_right_to_coker_row₂_epi hD,
end

lemma ten_term_exact_seq (hD : is_snake_input D) :
  exact_seq 𝒜 [
    (0 : 0 ⟶ kernel ((1,0) ⟶[D] (1,1))),
    hD.ker_row₁_to_top_left, (0,0) ⟶[D] (0,1), (0,1) ⟶[D] (0,2),
    hD.δ,
    (3,0) ⟶[D] (3,1), (3,1) ⟶[D] (3,2), hD.bottom_right_to_coker_row₂,
    (0 : cokernel ((2,1) ⟶[D] (2,2)) ⟶ 0)] :=
begin
  refine exact_seq.cons _ _ hD.exact_zero_to_ker_row₁_to_top_left _ _,
  refine exact_seq.cons _ _ hD.long_row₀_exact _ _,
  refine exact_seq.cons _ _ hD.row_exact₀ _ _,
  refine exact_seq.cons _ _ hD.exact_to_δ _ _,
  refine exact_seq.cons _ _ hD.exact_from_δ _ _,
  refine exact_seq.cons _ _ hD.row_exact₃ _ _,
  refine exact_seq.cons _ _ hD.long_row₃_exact _ _,
  refine exact_seq.cons _ _ hD.exact_bottom_right_to_coker_row₂_to_zero _ _,
  refine exact_seq.single _,
end

lemma eight_term_exact_seq (hD : is_snake_input D) :
  exact_seq 𝒜 [hD.ker_row₁_to_top_left, (0,0) ⟶[D] (0,1), (0,1) ⟶[D] (0,2),
    hD.δ,
    (3,0) ⟶[D] (3,1), (3,1) ⟶[D] (3,2), hD.bottom_right_to_coker_row₂] :=
exact_seq.extract hD.ten_term_exact_seq 1 7

lemma six_term_exact_seq (hD : is_snake_input D) :
  exact_seq 𝒜 [(0,0) ⟶[D] (0,1), (0,1) ⟶[D] (0,2), hD.δ, (3,0) ⟶[D] (3,1), (3,1) ⟶[D] (3,2)] :=
exact_seq.extract hD.eight_term_exact_seq 1 5

end is_snake_input

variables (𝒜)

structure snake_input extends snake_diagram ⥤ 𝒜 :=
(is_snake_input : is_snake_input to_functor)

namespace snake_input

instance : category (snake_input 𝒜) := induced_category.category to_functor

@[simps] def proj (x : snake_diagram) : snake_input 𝒜 ⥤ 𝒜 :=
induced_functor _ ⋙ (evaluation _ _).obj x

def mk_of_short_exact_sequence_hom (A B : short_exact_sequence 𝒜) (f : A ⟶ B) :
  snake_input 𝒜 :=
⟨snake_diagram.mk_of_short_exact_sequence_hom A B f,
is_snake_input.mk_of_short_exact_sequence_hom A B f⟩

def kernel_sequence (D : snake_input 𝒜)
  (h1 : mono ((1,0) ⟶[D] (1,1))) (h2 : is_zero (D.obj (3,0))) :
  short_exact_sequence 𝒜 :=
{ fst := D.obj (0,0),
  snd := D.obj (0,1),
  trd := D.obj (0,2),
  f := (0,0) ⟶[D] (0,1),
  g := (0,1) ⟶[D] (0,2),
  mono' :=
  begin
    letI := h1,
    refine abelian.pseudoelement.mono_of_zero_of_map_zero _ (λ a ha, _),
    obtain ⟨b, hb⟩ := is_snake_input.exists_of_exact
      (is_snake_input.long_row₀_exact D.is_snake_input) a ha,
    rw [← hb],
    simp [is_snake_input.ker_row₁_to_top_left, limits.kernel.ι_of_mono ((1,0) ⟶[D] (1,1))]
  end,
  epi' :=
  begin
    rw (abelian.tfae_epi (D.obj (3,0)) ((0,1) ⟶[D] (0,2))).out 0 2,
    convert D.2.exact_to_δ,
    apply h2.eq_of_tgt,
  end,
  exact' := D.2.row_exact _ }

end snake_input

class has_snake_lemma :=
(δ : snake_input.proj 𝒜 (0,2) ⟶ snake_input.proj 𝒜 (3,0))
(exact_δ : ∀ (D : snake_input 𝒜), exact ((0,1) ⟶[D] (0,2)) (δ.app D))
(δ_exact : ∀ (D : snake_input 𝒜), exact (δ.app D) ((3,0) ⟶[D.1] (3,1))) -- why can't I write `⟶[D]`

namespace snake_lemma

variables [has_snake_lemma 𝒜]

variables {𝒜}

def δ (D : snake_input 𝒜) : D.obj (0,2) ⟶ D.obj (3,0) := has_snake_lemma.δ.app D

lemma exact_δ (D : snake_input 𝒜) : exact ((0,1) ⟶[D] (0,2)) (δ D) :=
has_snake_lemma.exact_δ D

lemma δ_exact (D : snake_input 𝒜) : exact (δ D) ((3,0) ⟶[D] (3,1)) :=
has_snake_lemma.δ_exact D

end snake_lemma

end

end category_theory
