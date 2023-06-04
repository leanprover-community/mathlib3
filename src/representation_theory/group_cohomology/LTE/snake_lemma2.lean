import .snake_lemma
import .exact_seq2

noncomputable theory

open category_theory category_theory.limits

variables {𝒜 : Type*} [category 𝒜] [abelian 𝒜]
variables (A₀ B₀ C₀ : 𝒜)
variables (A₁ B₁ C₁ : 𝒜)
variables (A₂ B₂ C₂ : 𝒜)
variables (A₃ B₃ C₃ : 𝒜)
variables (f₀ : A₀ ⟶ B₀) (g₀ : B₀ ⟶ C₀)
variables (a₀ : A₀ ⟶ A₁) (b₀ : B₀ ⟶ B₁) (c₀ : C₀ ⟶ C₁)
variables (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁)
variables (a₁ : A₁ ⟶ A₂) (b₁ : B₁ ⟶ B₂) (c₁ : C₁ ⟶ C₂)
variables (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂)
variables (a₂ : A₂ ⟶ A₃) (b₂ : B₂ ⟶ B₃) (c₂ : C₂ ⟶ C₃)
variables (f₃ : A₃ ⟶ B₃) (g₃ : B₃ ⟶ C₃)

namespace category_theory

local notation `kernel_map`   := kernel.map _ _ _ _
local notation `cokernel_map` := cokernel.map _ _ _ _

structure snake : Prop :=
(row_exact₁ : exact f₁ g₁)
(row_exact₂ : exact f₂ g₂)
[row_epi : epi g₁]
[row_mono : mono f₂]
(col_exact_a : exact_seq 𝒜 [a₀, a₁, a₂])
(col_exact_b : exact_seq 𝒜 [b₀, b₁, b₂])
(col_exact_c : exact_seq 𝒜 [c₀, c₁, c₂])
[col_mono_a : mono a₀]
[col_mono_b : mono b₀]
[col_mono_c : mono c₀]
[col_epi_a : epi a₂]
[col_epi_b : epi b₂]
[col_epi_c : epi c₂]
(sq_a₀ : a₀ ≫ f₁ = f₀ ≫ b₀)
(sq_b₀ : b₀ ≫ g₁ = g₀ ≫ c₀)
(sq_a₁ : a₁ ≫ f₂ = f₁ ≫ b₁)
(sq_b₁ : b₁ ≫ g₂ = g₁ ≫ c₁)
(sq_a₂ : a₂ ≫ f₃ = f₂ ≫ b₂)
(sq_b₂ : b₂ ≫ g₃ = g₂ ≫ c₂)

namespace snake

lemma mk_of_sequence_hom (sq₁ : a₁ ≫ f₂ = f₁ ≫ b₁) (sq₂ : b₁ ≫ g₂ = g₁ ≫ c₁)
  (h₁ : exact f₁ g₁) (h₂ : exact f₂ g₂) [epi g₁] [mono f₂] : snake
  (kernel a₁) (kernel b₁) (kernel c₁)
  A₁ B₁ C₁
  A₂ B₂ C₂
  (cokernel a₁) (cokernel b₁) (cokernel c₁)
  (kernel_map sq₁) (kernel_map sq₂)
  (kernel.ι _) (kernel.ι _) (kernel.ι _)
  f₁ g₁
  a₁ b₁ c₁
  f₂ g₂
  (cokernel.π _) (cokernel.π _) (cokernel.π _)
  (cokernel_map sq₁) (cokernel_map sq₂) :=
{ row_exact₁ := h₁,
  row_exact₂ := h₂,
  col_exact_a := exact_seq.cons _ _ exact_kernel_ι _ $ (exact_iff_exact_seq _ _).mp (abelian.exact_cokernel _),
  col_exact_b := exact_seq.cons _ _ exact_kernel_ι _ $ (exact_iff_exact_seq _ _).mp (abelian.exact_cokernel _),
  col_exact_c := exact_seq.cons _ _ exact_kernel_ι _ $ (exact_iff_exact_seq _ _).mp (abelian.exact_cokernel _),
  sq_a₀ := (limits.kernel.lift_ι _ _ _).symm,
  sq_b₀ := (limits.kernel.lift_ι _ _ _).symm,
  sq_a₁ := sq₁,
  sq_b₁ := sq₂,
  sq_a₂ := cokernel.π_desc _ _ _,
  sq_b₂ := cokernel.π_desc _ _ _ }

variables
 {A₀ B₀ C₀
  A₁ B₁ C₁
  A₂ B₂ C₂
  A₃ B₃ C₃
  f₀ g₀ a₀ b₀ c₀ f₁ g₁ a₁ b₁ c₁ f₂ g₂ a₂ b₂ c₂ f₃ g₃}

variables (S : snake
  A₀ B₀ C₀
  A₁ B₁ C₁
  A₂ B₂ C₂
  A₃ B₃ C₃
  f₀ g₀ a₀ b₀ c₀ f₁ g₁ a₁ b₁ c₁ f₂ g₂ a₂ b₂ c₂ f₃ g₃)

variables

def snake_diagram : snake_diagram ⥤ 𝒜 :=
snake_diagram.mk_functor
![![A₀, B₀, C₀],
  ![A₁, B₁, C₁],
  ![A₂, B₂, C₂],
  ![A₃, B₃, C₃]]
f₀ g₀ a₀ b₀ c₀ f₁ g₁ a₁ b₁ c₁ f₂ g₂ a₂ b₂ c₂ f₃ g₃
S.sq_a₀ S.sq_b₀ S.sq_a₁ S.sq_b₁ S.sq_a₂ S.sq_b₂

lemma is_snake_input : is_snake_input S.snake_diagram :=
{ row_exact₁ := by { dsimp only [snake_diagram], simpa using S.row_exact₁, },
  row_exact₂ := by { dsimp only [snake_diagram], simpa using S.row_exact₂ },
  col_exact₁ := begin
    intros j,
    dsimp only [snake_diagram],
    fin_cases j with [0, 1, 2]; simp; rw exact_iff_exact_seq,
    exacts [S.col_exact_a.extract 0 2, S.col_exact_b.extract 0 2, S.col_exact_c.extract 0 2],
  end,
  col_exact₂ := begin
    intros j,
    dsimp only [snake_diagram],
    fin_cases j with [0, 1, 2]; simp; rw exact_iff_exact_seq,
    exacts [S.col_exact_a.extract 1 2, S.col_exact_b.extract 1 2, S.col_exact_c.extract 1 2],
  end,
  col_mono := begin
    intros j,
    dsimp only [snake_diagram],
    fin_cases j with [0, 1, 2]; simp,
    exacts [S.col_mono_a, S.col_mono_b, S.col_mono_c],
  end,
  col_epi := begin
    intros j,
    dsimp only [snake_diagram],
    fin_cases j with [0, 1, 2]; simp,
    exacts [S.col_epi_a, S.col_epi_b, S.col_epi_c],
  end,
  row_mono := by { dsimp only [snake_diagram], simp, exact S.row_mono },
  row_epi := by { dsimp only [snake_diagram], simpa using S.row_epi } }

def snake_input : snake_input 𝒜 := ⟨S.snake_diagram, S.is_snake_input⟩

def δ : C₀ ⟶ A₃ := S.is_snake_input.δ

lemma six_term_exact_seq : exact_seq 𝒜 [f₀, g₀, S.δ, f₃, g₃] :=
begin
  have := S.is_snake_input.six_term_exact_seq,
  dsimp only [snake_diagram] at this,
  simpa only [snake_diagram.mk_functor_map_f0, snake_diagram.mk_functor_map_g0,
    snake_diagram.mk_functor_map_f3, snake_diagram.mk_functor_map_g3],
end

end snake

lemma mono_of_exact_of_eq_zero (hfg : exact f₁ g₁) (h : f₁ = 0) : mono g₁ :=
by rwa [(abelian.tfae_mono A₁ g₁).out 0 2, ← h]

lemma cokernel.map_mono_of_epi_of_mono (sq : f₁ ≫ b₁ = a₁ ≫ f₂)
  [epi a₁] [mono b₁] [mono f₂] :
  mono (cokernel.map f₁ f₂ a₁ b₁ sq) :=
begin
  have S := snake.mk_of_sequence_hom A₁ B₁ (cokernel f₁) A₂ B₂ (cokernel f₂)
    f₁ (cokernel.π _) a₁ b₁ (cokernel.map f₁ f₂ a₁ b₁ sq) f₂ (cokernel.π _) sq.symm (by simp)
    (abelian.exact_cokernel _) (abelian.exact_cokernel _),
  apply (S.col_exact_c).pair.mono_of_is_zero,
  exact (S.six_term_exact_seq.drop 1).pair.is_zero_of_is_zero_is_zero
    (is_zero_kernel_of_mono _) (is_zero_cokernel_of_epi _),
end

end category_theory
