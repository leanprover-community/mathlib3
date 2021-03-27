import algebra.category.Module.abelian
import algebra.homology2.homological_complex
/-

Experiments with R-modules, to test new ideas for complexes

-/

section subquotients

universes u v

variables {R : Type u} [ring R] {M : Type v} [add_comm_group M] [module R M] (Z B : submodule R M)

namespace submodule

/-- `subquotient Z B` is `Z/(Z ∩ B)` as an `R`-module -/
@[derive add_comm_group] def subquotient : Type v :=
submodule.quotient (submodule.comap (Z.subtype : Z →ₗ[R] M) B : submodule R Z)

instance : module R (subquotient Z B) := by { dunfold subquotient, apply_instance }

variables {N : Type v} [add_comm_group N] [module R N] {Y A : submodule R N} {f : M →ₗ[R] N}
  (hAY : A ≤ Y)

variables {Z B}

-- is this already in mathlib?
def induced_map (f : M →ₗ[R] N) (hfZ : Z.map f ≤ Y) : Z →ₗ[R] Y :=
{ to_fun := λ z, ⟨f z.1, hfZ ⟨z.1, z.2, rfl⟩⟩,
  map_add' := λ _ _, subtype.ext $ f.map_add _ _,
  map_smul' := λ _ _, subtype.ext $ f.map_smul _ _ }

namespace subquotient

def map (hfZ : Z.map f ≤ Y) (hfB : B.map f ≤ A) : subquotient Z B →ₗ[R] subquotient Y A :=
mapq (_) (_) (induced_map _ hfZ)
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

@[simp] lemma map_apply (φ : A ⟶ B) (hjk : s.r j k) (m : cycle R A hjk) :
  (map R φ hjk m : B.X j)= φ.f j m := rfl

lemma map_zero {φ : A ⟶ B} (hjk : s.r j k) (hφ : φ.f j = 0) : map R φ hjk = 0 :=
begin
  ext a,
  change φ.f j a = 0,
  rw hφ,
  refl,
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
submodule.subquotient (cycle R C hjk) (boundary R C hij)

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

lemma map_zero (φ : A ⟶ B) (hφ : φ.f j = 0) : map R hij hjk φ = 0 :=
begin
  apply quot_hom_ext,
  simp [map, cycle.map_zero _ _ hφ],
end

variable {C}

theorem map_comp (φ : A ⟶ B) (ψ : B ⟶ C) :
  map R hij hjk (φ ≫ ψ) = (map R hij hjk ψ).comp (map R hij hjk φ) :=
begin
  ext a,
  apply quotient.induction_on' a, clear a,
  intro a,
  rw quotient.mk'_eq_mk,
  simp [map],
  refl,
end
.

theorem map_exact (φ : A ⟶ B) (ψ : B ⟶ C)
  --(hφψ : homological_complex.exact φ ψ)  -- let's see how much we need.
  (h1 : (φ ≫ ψ).f j = 0) -- need this for the easy way
  -- will need more: 0 -> A -> B -> C -> 0 short exact is enough of course
  :
  (map R hij hjk φ).range = (map R hij hjk ψ).ker :=
begin
  ext x,
  split,
  { rintro ⟨a, -, rfl⟩,
    change (map R hij hjk ψ).comp (map R hij hjk φ) a = 0,
    rw ← map_comp,
    rw map_zero R hij hjk (φ ≫ ψ) h1,
    refl },
  { rintro (h : map R hij hjk ψ x = 0),
    sorry
  }
end

-- TODO : boundary map from homology to homology with i,j,k,l and two more
-- exactness theorems

end homology
