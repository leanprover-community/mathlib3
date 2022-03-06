import algebra.algebra.basic
import algebra.homology.homology
import algebra.category.Group.limits
import algebra.category.Group.colimits
import algebra.category.Group.zero
import algebra.category.Group.images
import category_theory.closed.monoidal
import category_theory.limits.preserves.shapes.kernels
import category_theory.monoidal.preadditive
import algebra.category.Module.monoidal

universes u v

def cast_hom (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] {i j : ℕ} (h : i = j) : A i →+ A j :=
{ to_fun := cast (congr_arg A h),
  map_zero' := by { cases h, refl, },
  map_add' := λ x y, by { cases h, refl, }}

@[simp]
lemma cast_hom_cast_hom (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] {i j k : ℕ} (h₁ : i = j) (h₂ : j = k) (x):
  cast_hom A h₂ (cast_hom A h₁ x) = cast_hom A (h₁.trans h₂) x :=
by { cases h₁, cases h₂, refl, }

@[simp]
lemma cast_hom_refl (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] {i} (x : A i):
  cast_hom A (eq.refl _) x = x :=
rfl

class graded_monoid (A : ℕ → Type*) :=
(one : A 0)
(mul : Π {i j}, A i → A j → A (i+j))
(mul_one : ∀ {i} {x : A i}, mul x one = x)
(one_mul : ∀ {i} {x : A i}, mul one x = cast (congr_arg A (zero_add _).symm) x)
(mul_assoc : ∀ {i j k} {x : A i} {y : A j} {z : A k},
  mul (mul x y) z = cast (congr_arg A (add_assoc _ _ _).symm) (mul x (mul y z)))

def gmul {A : ℕ → Type*} [graded_monoid A] {i j} (x : A i) (y : A j) : A (i + j) :=
  graded_monoid.mul x y

class graded_semiring (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] extends graded_monoid A :=
(mul_zero : ∀ {i j} (x : A i), gmul x (0 : A j) = 0)
(zero_mul : ∀ {i j} (x : A j), gmul (0 : A i) x = 0)
(left_distrib : ∀ {i j} {x : A i} {y z : A j}, gmul x (y + z) = gmul x y + gmul x z)
(right_distrib : ∀ {i j} {x y : A i} {z : A j}, gmul (x + y) z = gmul x z + gmul y z)

class graded_comm_ring (A : ℕ → Type*) [Π n, add_comm_group (A n)] extends graded_semiring A :=
(mul_comm : ∀ {i j} {x : A i} {y : A j},
  gmul x y = cast_hom A (add_comm _ _) ((-1 : ℤ)^(i * j) • gmul y x))

class differential_graded (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] :=
(d : Π {i}, A i →+ A (i+1))
(d_squared : ∀ {i} {x : A i}, d (d x) = 0)

def d {A : ℕ → Type*} [Π n, add_comm_group (A n)] [differential_graded A]
  {i} : A i →+ A (i + 1) :=
@differential_graded.d A _ _ i

@[simp]
lemma d_squared {A : ℕ → Type*} [Π n, add_comm_group (A n)] [differential_graded A] {i} {x : A i} :
  d (d x) = 0 :=
differential_graded.d_squared

@[simp]
lemma cast_hom_d {A : ℕ → Type*} [Π n, add_comm_group (A n)] [differential_graded A] {i j : ℕ} {x : A i}
  (h : i + 1 = j + 1):
  cast_hom A h (d x) = d (cast_hom A (nat.succ.inj h) x) :=
by { cases h, refl, }

class differential_graded_ring (A : ℕ → Type*) [Π n, add_comm_group (A n)]
  extends differential_graded A, graded_semiring A :=
(d_mul : ∀ {i j} {x : A i} {y : A j},
  d (gmul x y) = cast_hom A (by abel) (gmul (d x) y) + (-1 : ℤ)^i • (gmul x (d y) : A (i + (j+1))))

set_option old_structure_cmd true

class differential_graded_comm_ring (A : ℕ → Type*) [Π n, add_comm_group (A n)]
  extends graded_comm_ring A, differential_graded_ring A

variables {A : ℕ → Type*} [Π n, add_comm_group (A n)] [differential_graded_ring A]

lemma d_mul {i j} {x : A i} {y : A j} :
  d (gmul x y) = cast_hom A (by abel) (gmul (d x) y) + (-1 : ℤ)^i • (gmul x (d y) : A (i + (j+1))) :=
differential_graded_ring.d_mul

lemma mul_cycle_of_cycle_cycle {i j} (x : A i) (y : A j) (dx : d x = 0) (dy : d y = 0) :
  d (gmul x y) = 0 :=
begin
  rw [d_mul, dx, dy, graded_semiring.mul_zero x, graded_semiring.zero_mul y],
  rw [smul_zero, add_zero, add_monoid_hom.map_zero],
end

lemma mul_boundary_of_cycle_boundary {i j} (x : A i) (y : A j) (dx : d x = 0) :
  gmul x (d y) = d ((-1 : ℤ)^i • gmul x y) :=
begin
  rw [(@d A _ _ (i+j)).map_zsmul, d_mul, dx],
  rw [graded_semiring.zero_mul y, add_monoid_hom.map_zero, zero_add],
  rw [smul_smul, ←pow_add, ←two_mul, pow_mul],
  rw [show (-1 : ℤ)^2 = 1, by norm_num, one_pow, one_smul],
end

lemma mul_boundary_of_boundary_cycle {i j} (x : A i) (y : A j) (dy : d y = 0) :
  gmul (d x) y = cast_hom A (by abel) (d (gmul x y)) :=
begin
  rw [d_mul, dy, graded_semiring.mul_zero x, smul_zero, add_zero],
  rw [cast_hom_cast_hom, cast_hom_refl],
end

variables (R : Type*) [comm_ring R]

class differential_graded_module (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] [Π n, module R (A n)]
  extends differential_graded A :=
(d_smul : ∀ {i} (c : R) (x : A i), d (c • x) = c • d x)

def d_linear_map {A : ℕ → Type*} [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_module R A]
  {i} : A i →ₗ[R] A (i + 1) :=
{ map_smul' := differential_graded_module.d_smul,
  ..d }

class differential_graded_algebra (A : ℕ → Type*) [Π n, add_comm_group (A n)] [Π n, module R (A n)]
  extends differential_graded_module R A, differential_graded_ring A.

def mul_bilinear (A : ℕ → Type u) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A] (i j : ℕ) :
  tensor_product R (A i) (A j) →ₗ[R] A (i + j) :=
tensor_product.lift
{ to_fun := λ x,
  { to_fun := λ y, gmul x y,
    map_add' := sorry,
    map_smul' := sorry, },
  map_add' := sorry,
  map_smul' := sorry,  }

@[simp, to_additive] lemma CommGroup.of_hom_apply {X Y : Type*} [comm_group X] [comm_group Y] (f : X →* Y) (x : X) :
  CommGroup.of_hom f x = f x :=
rfl

@[simp] lemma Module.of_hom_apply {X Y : Type*} [add_comm_group X] [add_comm_group Y] [module R X] [module R Y] (f : X →ₗ[R] Y) (x : X) :
  Module.of_hom f x = f x :=
rfl

def cast_linear_map (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] [Π n, module R (A n)] {i j : ℕ} (h : i = j) : A i →ₗ[R] A j :=
{ map_smul' := λ r x, by { cases h, refl, },
  ..cast_hom A h }

@[simp]
lemma cast_linear_map_cast_linear_map (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] [Π n, module R (A n)] {i j k : ℕ} (h₁ : i = j) (h₂ : j = k) (x):
  cast_linear_map R A h₂ (cast_linear_map R A h₁ x) = cast_linear_map R A (h₁.trans h₂) x :=
by { cases h₁, cases h₂, refl, }

@[simp]
lemma cast_linear_map_refl (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] [Π n, module R (A n)] {i} (x : A i):
  cast_linear_map R A (eq.refl _) x = x :=
rfl

@[simp]
lemma d_linear_map_squared {A : ℕ → Type*} [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_module R A] {i} {x : A i} :
  d_linear_map R (d_linear_map R x) = 0 :=
differential_graded.d_squared

@[simp]
lemma cast_linear_map_d {A : ℕ → Type*} [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_module R A] {i j : ℕ} {x : A i}
  (h : i + 1 = j + 1):
  cast_linear_map R A h (d_linear_map R x) = d_linear_map R (cast_linear_map R A (nat.succ.inj h) x) :=
by { cases h, refl, }

def to_homological_complex (A : ℕ → Type*) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_module R A] :
  cochain_complex (Module R) ℕ :=
{ X := λ i, Module.of R (A i),
  d := λ i j, if h : i + 1 = j then Module.of_hom (d_linear_map R) ≫ Module.of_hom (cast_linear_map R A h) else 0,
  shape' := λ i j w, by rwa dif_neg,
  d_comp_d' := λ i j k w₁ w₂, begin
    ext x,
    split_ifs,
    { cases w₁, cases w₂, simp, },
    { exfalso, exact h w₁, }
  end, }

def graded.homology (A : ℕ → Type*) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_module R A] : ℕ → Type* :=
λ i, (to_homological_complex R A).homology i

noncomputable theory

instance (A : ℕ → Type*) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_module R A] (i : ℕ) :
  add_comm_group (graded.homology R A i) :=
by { dsimp [graded.homology], apply_instance, }

instance (A : ℕ → Type*) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_module R A] (i : ℕ) :
  module R (graded.homology R A i) :=
by { dsimp [graded.homology], apply_instance, }

open category_theory
open category_theory.limits
open category_theory.monoidal_category

attribute [instance, priority 100] closed.is_adj

def foo {C : Type*} [category C] [preadditive C] [has_cokernels C]
  [monoidal_category C] [monoidal_preadditive C] [monoidal_closed C]
  {X Y Z : C} (f : Y ⟶ Z) :
  X ⊗ cokernel f ≅ cokernel (𝟙 X ⊗ f) :=
(as_iso (cokernel_comparison f (tensor_left X))).symm

def foo' {C : Type*} [category C] [preadditive C] [has_cokernels C]
  [monoidal_category C] [monoidal_preadditive C] [monoidal_closed C]
  {X Y Z : C} (f : X ⟶ Y) :
  cokernel f ⊗ Z ≅ cokernel (f ⊗ 𝟙 Z) :=
sorry

def nn (A : ℕ → Type*) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A] (i j : ℕ) :
  (to_homological_complex R A).homology i ⊗ (to_homological_complex R A).homology j ⟶ (to_homological_complex R A).homology (i + j) :=
begin
  refine (foo _).hom ≫ _,
  refine cokernel.desc _ _ _,
  refine (foo' _).hom ≫ _,
  refine cokernel.desc _ _ _,
  refine _ ≫ cokernel.π _,
  refine factor_thru_kernel_subobject _ _ _,
  refine ((kernel_subobject _).arrow ⊗ (kernel_subobject _).arrow) ≫ _,
  exact Module.of_hom (mul_bilinear R A i j),
  -- Now we have three proofs obligations. Discharging these nicely will require some custom extensionality lemmas.
  { apply tensor_product.ext', intros, sorry, },
  { sorry, },
  { sorry, }
end

def mm (A : ℕ → Type*) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A] (i j : ℕ) :
  graded.homology R A j →+ (graded.homology R A i →+ graded.homology R A (i + j)) :=
 (adjunction.of_left_adjoint (tensor_left (Module.of R (graded.homology R A i)))).hom_equiv _ _ (nn R A i j)

instance (A : ℕ → Type*) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A] :
  graded_monoid (graded.homology R A) :=
{ one := sorry,
  mul := λ i j x y, begin end,
  one_mul := sorry,
  mul_one := sorry,
  mul_assoc := sorry, }


instance (A : ℕ → Type*) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A] :
  graded_semiring (graded.homology R A) :=
sorry

-- total

-- @[derive add_comm_monoid]
-- def graded.total (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] := dfinsupp A

-- instance (A : ℕ → Type*) [Π n, add_comm_group (A n)] : add_comm_group (graded.total A) :=
-- by { dsimp [graded.total], apply_instance, }

-- instance (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] [graded_semiring A] : semiring (graded.total A) :=
-- { mul := λ f g, begin end,
--   ..(by apply_instance : add_comm_monoid (graded.total A)) }
