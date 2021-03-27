import algebra.category.Module.abelian
import algebra.homology2.homological_complex
/-

Experiments with R-modules, to test new ideas for complexes

-/

section subquotients

universes u v

variables {R : Type u} [ring R] {M : Type v} [add_comm_group M] [module R M] {Z B : submodule R M}

namespace submodule

def subsubmodule_as_submodule (hBZ : B ≤ Z) : submodule R Z :=
{ carrier := {z | z.1 ∈ B},
  zero_mem' := B.zero_mem,
  add_mem' := λ _ _, B.add_mem,
  smul_mem' := λ _ _, B.smul_mem _ }

variable (hBZ : B ≤ Z)

@[derive add_comm_group] def subquotient : Type v :=
submodule.quotient (submodule.subsubmodule_as_submodule hBZ : submodule R Z)

instance : module R (subquotient hBZ) := by { dunfold subquotient, apply_instance }

variables {N : Type v} [add_comm_group N] [module R N] {Y A : submodule R N} {f : M →ₗ[R] N}
  (hAY : A ≤ Y)

-- is this already in mathlib?
def induced_map (f : M →ₗ[R] N) (hfZ : Z.map f ≤ Y) : Z →ₗ[R] Y :=
{ to_fun := λ z, ⟨f z.1, hfZ ⟨z.1, z.2, rfl⟩⟩,
  map_add' := λ _ _, subtype.ext $ f.map_add _ _,
  map_smul' := λ _ _, subtype.ext $ f.map_smul _ _ }

namespace subquotient

def map (hfZ : Z.map f ≤ Y) (hfB : B.map f ≤ A) : subquotient hBZ →ₗ[R] subquotient hAY :=
mapq (subsubmodule_as_submodule hBZ) (subsubmodule_as_submodule hAY) (induced_map _ hfZ)
  (λ m hmb, hfB ⟨m, hmb, rfl⟩)

end subquotient -- namespace

end submodule -- namespace

end subquotients -- section

-- needs a proper name
def s : complex_shape ℤ :=
{ r := λ i j, j = i + 1,
  succ_eq := by intros; linarith,
  pred_eq := by intros; linarith }

universe u

variables (R : Type) [ring R]

variables (A B C : homological_complex.{0 1} (Module R) s)

variables {i j k : ℤ}

def cycle (hjk : s.r j k) : submodule R (C.X j) := ((C.d j k) : C.X j →ₗ[R] C.X k).ker

namespace cycle

variables {A B}

def map (φ : A ⟶ B) (hjk : s.r j k) : cycle R A hjk →ₗ[R] cycle R B hjk :=
submodule.induced_map (φ.f j) begin
  rintros - ⟨m, hm, rfl⟩,
  change (φ.f j ≫ B.d j k) m = 0,
  rw φ.commutes,
  change φ.f k (_) = 0,
  convert (φ.f k).map_zero,
end

end cycle

def boundary (hij : s.r i j) : submodule R (C.X j) := ((C.d i j) : C.X i →ₗ[R] C.X j).range

variables (hij : s.r i j) (hjk : s.r j k)

namespace boundary

variables {A B}

def map (φ : A ⟶ B) : boundary R A hij →ₗ[R] boundary R B hij :=
submodule.induced_map (φ.f j) begin
  rintros - ⟨-, ⟨a, -, rfl⟩, rfl⟩,
  use [φ.f i a, trivial],
  change (φ.f i ≫ _) a = _,
  rw φ.commutes,
  refl,
end

end boundary

namespace submodule

lemma boundary_le_cycle : boundary R C hij ≤ cycle R C hjk :=
begin
  rintro - ⟨m, -, rfl⟩,
  change (C.d i j ≫ C.d j k) m = 0,
  rw C.d_comp_d i j k,
  refl,
end

end submodule

open submodule

-- roll-your-own exactness

variables {R A B C}

def homological_complex.exact (φ : A ⟶ B) (ψ : B ⟶ C) : Prop :=
∀ i, (φ.f i).range = (ψ.f i).ker

variables (R C)

-- this probably shouldn't be in the root namespace
@[derive add_comm_group] def homology : Type :=
submodule.subquotient (boundary_le_cycle R C hij hjk)

namespace homology

open submodule

instance : module R (homology R C hij hjk) := by {dunfold homology, apply_instance }

def map (φ : A ⟶ B) : homology R A hij hjk →ₗ[R] homology R B hij hjk :=
submodule.mapq _ _ (cycle.map R φ hjk) begin
  rintro aj ⟨ai, -, ha⟩,
  use [φ.f i ai, trivial],
  change (φ.f i ≫ _) _ = _,
  rw φ.commutes,
  change φ.f j _ = _,
  rw ha,
  refl,
end

theorem map_exact (φ : A ⟶ B) (ψ : B ⟶ C) (hφψ : homological_complex.exact φ ψ) :
  (map R hij hjk φ).range = (map R hij hjk ψ).ker :=
begin
  sorry
end

-- TODO : boundary map from homology to homology with i,j,k,l and two more
-- exactness theorems

end homology
