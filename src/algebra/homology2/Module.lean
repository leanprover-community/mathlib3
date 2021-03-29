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

/-- The `R`-module structure on the subquotient. -/
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

/-- The map Z/B → Y/A induced by a map from M to N sending Z to Y and B to A. -/
def map (hfZ : Z.map f ≤ Y) (hfB : B.map f ≤ A) : subquotient Z B →ₗ[R] subquotient Y A :=
mapq _ _ (induced_map _ hfZ) (λ m hmb, hfB ⟨m, hmb, rfl⟩)

end subquotient -- namespace

end submodule -- namespace

end subquotients -- section

-- needs a proper name
def s : complex_shape ℤ :=
{ r := λ i j, j = i + 1,
  succ_eq := by intros; linarith,
  pred_eq := by intros; linarith }

variables (R : Type) [ring R]

variables (A B C : homological_complex.{0 1} (Module R) s)
variables {A B}

variables {i j k : ℤ}

lemma commutes_apply (φ : A ⟶ B) (a : A.X i) :
   B.d i j (φ.f i a) = φ.f j (A.d i j a) :=
begin
  change (φ.f i ≫ B.d i j) a = (A.d i j ≫ φ.f j) a,
  rw φ.comm,
end

def cycle (hjk : s.r j k) : submodule R (C.X j) := ((C.d j k) : C.X j →ₗ[R] C.X k).ker

namespace cycle

variables {A B}

def map (φ : A ⟶ B) (hjk : s.r j k) : cycle R A hjk →ₗ[R] cycle R B hjk :=
submodule.induced_map (φ.f j) begin
  rintros - ⟨m, hm, rfl⟩,
  change (φ.f j ≫ B.d j k) m = 0,
  rw φ.comm,
  change φ.f k (_) = 0,
  convert (φ.f k).map_zero,
end

@[simp] lemma map_apply (φ : A ⟶ B) (hjk : s.r j k) (m : cycle R A hjk) :
  (map R φ hjk m : B.X j)= φ.f j m := rfl

@[simp] lemma map_zero {φ : A ⟶ B} (hjk : s.r j k) (hφ : φ.f j = 0) : map R φ hjk = 0 :=
begin
  ext a,
  change φ.f j a = 0,
  rw hφ,
  refl,
end

@[simp] lemma map_comp {φ : A ⟶ B} {ψ : B ⟶ C} (hjk : s.r j k) :
  map R (φ ≫ ψ) hjk = (map R ψ hjk).comp (map R φ hjk) := rfl

end cycle

def boundary (hij : s.r i j) : submodule R (C.X j) := ((C.d i j) : C.X i →ₗ[R] C.X j).range

variables (hij : s.r i j) (hjk : s.r j k)

namespace boundary

def map (φ : A ⟶ B) : boundary R A hij →ₗ[R] boundary R B hij :=
submodule.induced_map (φ.f j) begin
  rintros - ⟨-, ⟨a, -, rfl⟩, rfl⟩,
  use [φ.f i a, trivial],
  change (φ.f i ≫ _) a = _,
  rw φ.comm,
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

/- I can't find the linear maps projecting from a product -/
def prod.lfst (R M N : Type*) [ring R] [add_comm_group M] [add_comm_group N]
  [module R M] [module R N] : M × N →ₗ[R] M :=
{ to_fun := prod.fst,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl }

def prod.lsnd (R M N : Type*) [ring R] [add_comm_group M] [add_comm_group N]
  [module R M] [module R N] : M × N →ₗ[R] N :=
{ to_fun := prod.snd,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl }

open submodule

-- roll-your-own exactness

variables {R C}

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
  rw φ.comm,
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
  apply quot_hom_ext,
  intro a,
  simp [map],
end
.

theorem map_exact (φ : A ⟶ B) (ψ : B ⟶ C)
  --(hφψ : homological_complex.exact φ ψ)  -- let's see how much we need.
  (hi : function.surjective (ψ.f i))
  (hj : (φ.f j).range = (ψ.f j).ker)
  (hk : function.injective (φ.f k))
  -- will need more: 0 -> A -> B -> C -> 0 short exact is enough of course
  :
  (map R hij hjk φ).range = (map R hij hjk ψ).ker :=
begin
  ext x,
  split,
  { rintro ⟨a, -, rfl⟩,
    change (map R hij hjk ψ).comp (map R hij hjk φ) a = 0,
    rw ← map_comp,
    rw map_zero R hij hjk (φ ≫ ψ) _, refl,
    ext x,
    show φ.f j x ∈ (ψ.f j).ker,
    rw ← hj,
    exact ⟨x, trivial, rfl⟩ },
  { -- should there be a submodule.quotient.induction_on?
    apply quotient.induction_on' x, clear x,
    intro b,
    rw quotient.mk'_eq_mk,
    rintro (hb : map R hij hjk ψ (submodule.quotient.mk b) = 0),
    /-
       φ     ψ
    Ai -> Bi -> Ci
    \/    \/    \/ d
    Aj -> Bj -> Cj
    \/    \/    \/ d
    Ak -> Bk -> Ck


    -/
    --
    simp only [map, mapq_apply, cycle.map_apply, subtype_apply, quotient.mk_eq_zero, mem_comap] at hb,
    rcases hb with ⟨c, -, hc⟩,
    rcases hi c with ⟨bi, rfl⟩,
    have hb2 : (b : B.X j) - B.d i j bi ∈ (φ.f j).range,
      simp [hj, linear_map.mem_ker, (ψ.f j).map_sub, ← hc, commutes_apply],
    rcases hb2 with ⟨a, -, ha⟩,
    have ha' : A.d j k a = 0,
      apply hk,
      rw [← commutes_apply, linear_map.map_zero, ha, linear_map.map_sub],
      convert sub_zero _,
        rw ← linear_map.comp_apply,
        change (B.d i j ≫ B.d j k) _ = _,
        rw B.d_comp_d,
        refl,
      exact b.2.symm,
    -- does submodule.range not use the "remove x ∈ ⊤" trick?
    use [submodule.quotient.mk ⟨a, ha'⟩, trivial],
    simp only [map, mapq_apply],
    change mkq _ _ = mkq _ b,
    symmetry,
    rw ← linear_map.sub_mem_ker_iff,
    rw ker_mkq,
    simp only [cycle.map_apply, coe_sub, subtype_apply, mem_comap, subtype.coe_mk],
    use [bi, trivial],
    rw ha,
    abel }
end
.

section boundary_map

variables {l : ℤ} (hkl : s.r k l)

    /-
       φ     ψ
    Ai -> Bi -> Ci
    \/    \/    \/ d
    Aj -> Bj -> Cj
    \/    \/    \/ d
    Ak -> Bk -> Ck
    \/    \/    \/ d
    Al -> Bl -> Cl

    Want a map from H(Cj) to H(Ak)
    Need: Bj -> Cj surjective
    Need φ.k.im = ψ.k.ker
    Need Al → Bl injective
    Then we can define the map from cycles in Cj to cycles in Ak
    using a choice. The resulting map to H(Ak) is choice-free
    if φ.j im = ψ.j.ker and is zero on coboundaries.
    To prove it's R-linear will need some more.

    -/

example : module R (B.X j × A.X k) := prod.semimodule

def aux_prod (φ : A ⟶ B) (hjk : s.r j k) : submodule R (A.X k × B.X j) :=
linear_map.ker ((B.d j k).comp (prod.lsnd R _ _) - (φ.f k).comp (prod.lfst R _ _))

@[simp] lemma mem_aux_prod (φ : A ⟶ B) (b : B.X j) (a : A.X k) :
  (a,b) ∈ aux_prod R φ hjk ↔ B.d j k b = φ.f k a :=
begin
  simp [aux_prod, prod.lsnd, prod.lfst, sub_eq_zero],
end


-- TODO : boundary map from homology to homology with i,j,k,l and two more
-- exactness theorems


end boundary_map


end homology
