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
import category_theory.abelian.homology
import algebra.category.Module.abelian

universes u v

section
variables {ι : Type*} (A : ι → Type*) [Π n, comm_monoid (A n)] {i j k : ι}

@[to_additive]
def cast_monoid_hom (h : i = j) : A i →* A j :=
{ to_fun := cast (congr_arg A h),
  map_one' := by { cases h, refl, },
  map_mul' := λ x y, by { cases h, refl, }}

@[simp, to_additive]
lemma cast_monoid_hom_cast_monoid_hom (h₁ : i = j) (h₂ : j = k) (x):
  cast_monoid_hom A h₂ (cast_monoid_hom A h₁ x) = cast_monoid_hom A (h₁.trans h₂) x :=
by { cases h₁, cases h₂, refl, }

@[simp, to_additive]
lemma cast_monoid_hom_refl {i} (x : A i) : cast_monoid_hom A (eq.refl _) x = x :=
rfl

end

section
variables (R : Type*) [semiring R]
variables {ι : Type*} (A : ι → Type*) [Π n, add_comm_monoid (A n)] [Π n, module R (A n)] {i j k : ι}

def cast_linear_map (h : i = j) : A i →ₗ[R] A j :=
{ map_smul' := λ r x, by { cases h, refl, },
  ..cast_add_monoid_hom A h }

@[simp]
lemma cast_linear_map_cast_linear_map (h₁ : i = j) (h₂ : j = k) (x):
  cast_linear_map R A h₂ (cast_linear_map R A h₁ x) = cast_linear_map R A (h₁.trans h₂) x :=
by { cases h₁, cases h₂, refl, }

@[simp]
lemma cast_linear_map_refl (x : A i) : cast_linear_map R A (eq.refl _) x = x :=
rfl

end

class graded_monoid (A : ℕ → Type*) :=
(one : A 0)
(mul : Π {i j}, A i → A j → A (i+j))
(mul_one : ∀ {i} {x : A i}, mul x one = x)
(one_mul : ∀ {i} {x : A i}, mul one x = cast (congr_arg A (zero_add _).symm) x)
(mul_assoc : ∀ {i j k} {x : A i} {y : A j} {z : A k},
  mul (mul x y) z = cast (congr_arg A (add_assoc _ _ _).symm) (mul x (mul y z)))

instance monoid_zero {A : ℕ → Type*} [graded_monoid A] : monoid (A 0) :=
{ one := graded_monoid.one,
  mul := graded_monoid.mul,
  one_mul := λ a, @graded_monoid.one_mul _ _ 0 a,
  mul_one := λ a, @graded_monoid.mul_one _ _ 0 a,
  mul_assoc := λ a b c, @graded_monoid.mul_assoc _ _ 0 0 0 a b c, }

def gmul {A : ℕ → Type*} [graded_monoid A] {i j} (x : A i) (y : A j) : A (i + j) :=
  graded_monoid.mul x y

@[simp] lemma gmul_one {A : ℕ → Type*} [graded_monoid A] {i} (x : A i) : gmul x (1 : A 0) = x :=
graded_monoid.mul_one

@[simp] lemma one_gmul {A : ℕ → Type*} [graded_monoid A] {i} (x : A i) :
  gmul (1 : A 0) x = cast (congr_arg A (zero_add _).symm) x :=
graded_monoid.one_mul

class graded_semiring (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] extends graded_monoid A :=
(mul_zero : ∀ {i j} (x : A i), gmul x (0 : A j) = 0)
(zero_mul : ∀ {i j} (x : A j), gmul (0 : A i) x = 0)
(left_distrib : ∀ {i j} {x : A i} {y z : A j}, gmul x (y + z) = gmul x y + gmul x z)
(right_distrib : ∀ {i j} {x y : A i} {z : A j}, gmul (x + y) z = gmul x z + gmul y z)

class graded_comm_ring (A : ℕ → Type*) [Π n, add_comm_group (A n)] extends graded_semiring A :=
(mul_comm : ∀ {i j} {x : A i} {y : A j},
  gmul x y = cast_add_monoid_hom A (add_comm _ _) ((-1 : ℤ)^(i * j) • gmul y x))

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
lemma cast_add_monoid_hom_d {A : ℕ → Type*} [Π n, add_comm_group (A n)] [differential_graded A] {i j : ℕ} {x : A i}
  (h : i + 1 = j + 1):
  cast_add_monoid_hom A h (d x) = d (cast_add_monoid_hom A (nat.succ.inj h) x) :=
by { cases h, refl, }

class differential_graded_ring (A : ℕ → Type*) [Π n, add_comm_group (A n)]
  extends differential_graded A, graded_semiring A :=
(d_mul : ∀ {i j} {x : A i} {y : A j},
  d (gmul x y) = cast_add_monoid_hom A (by abel) (gmul (d x) y) + (-1 : ℤ)^i • (gmul x (d y) : A (i + (j+1))))

set_option old_structure_cmd true

class differential_graded_comm_ring (A : ℕ → Type*) [Π n, add_comm_group (A n)]
  extends graded_comm_ring A, differential_graded_ring A

section

variables {A : ℕ → Type*} [Π n, add_comm_group (A n)] [differential_graded_ring A]

lemma d_mul {i j} (x : A i) (y : A j) :
  d (gmul x y) = cast_add_monoid_hom A (by abel) (gmul (d x) y) + (-1 : ℤ)^i • (gmul x (d y) : A (i + (j+1))) :=
differential_graded_ring.d_mul

@[simp]
lemma d_one (A : ℕ → Type*) [Π n, add_comm_group (A n)] [differential_graded_ring A] :
  d (1 : A 0) = 0 :=
by simpa using d_mul (1 : A 0) (1 : A 0)


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
  gmul (d x) y = cast_add_monoid_hom A (by abel) (d (gmul x y)) :=
begin
  rw [d_mul, dy, graded_semiring.mul_zero x, smul_zero, add_zero],
  rw [cast_add_monoid_hom_cast_add_monoid_hom, cast_add_monoid_hom_refl],
end

end

variables (R : Type u) [comm_ring R]

class differential_graded_module (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] [Π n, module R (A n)]
  extends differential_graded A :=
(d_smul : ∀ {i} (c : R) (x : A i), d (c • x) = c • d x)

def d_linear_map {A : ℕ → Type*} [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_module R A]
  {i} : A i →ₗ[R] A (i + 1) :=
{ map_smul' := differential_graded_module.d_smul,
  ..d }

class differential_graded_algebra (A : ℕ → Type*) [Π n, add_comm_group (A n)] [Π n, module R (A n)]
  extends differential_graded_ring A :=
(d_smul : ∀ {i} (c : R) (x : A i), d (c • x) = c • d x)

/-
Unfortunately we can't just use
`differential_graded_algebra extends differential_graded_module`,
as this creates two non-defeq paths to `differential_graded`.
-/
instance differential_graded_algebra.to_differential_graded_module (A : ℕ → Type*)
  [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A] :
  differential_graded_module R A :=
{ d := λ i, d,
  d_squared := λ i x, d_squared,
  d_smul := λ i, differential_graded_algebra.d_smul, }

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


section
variables {R}

@[simp]
lemma d_linear_map_squared {A : ℕ → Type*} [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_module R A] {i} {x : A i} :
  d_linear_map R (d_linear_map R x) = 0 :=
differential_graded.d_squared

@[simp]
lemma d_linear_map_one {A : ℕ → Type*} [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A] :
  d_linear_map R (1 : A 0) = 0 :=
d_one A

-- lemma d_linear_map_gmul {A : ℕ → Type*} [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A] {i j : ℕ} (x : A i) (y : A j) :
--   d_linear_map R (gmul x y) = gmul (d_linear_map R x) y + gmul x (d_linear_map R y) :=
-- d_one A


lemma mul_cycle_of_cycle_cycle' {A : ℕ → Type*} [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A]
  {i j} (x : A i) (y : A j) (dx : d x = 0) (dy : d y = 0) :
  d_linear_map R (gmul x y) = 0 :=
mul_cycle_of_cycle_cycle x y dx dy

@[simp]
lemma cast_linear_map_d {A : ℕ → Type*} [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_module R A] {i j : ℕ} {x : A i}
  (h : i + 1 = j + 1):
  cast_linear_map R A h (d_linear_map R x) = d_linear_map R (cast_linear_map R A (nat.succ.inj h) x) :=
by { cases h, refl, }

end

@[simps]
def to_cochain_complex (A : ℕ → Type v) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_module R A] :
  cochain_complex (Module.{v} R) ℕ :=
{ X := λ i, Module.of R (A i),
  d := λ i j, if h : i + 1 = j then Module.of_hom (d_linear_map R) ≫ Module.of_hom (cast_linear_map R A h) else 0,
  shape' := λ i j w, by rwa dif_neg,
  d_comp_d' := λ i j k w₁ w₂, begin
    ext x,
    split_ifs,
    { cases w₁, cases w₂, simp, },
    { exfalso, exact h w₁, }
  end, }

def graded.homology (A : ℕ → Type v) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_module R A] : ℕ → Type* :=
λ i, (to_cochain_complex R A).homology i

noncomputable theory

instance (A : ℕ → Type v) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_module R A] (i : ℕ) :
  add_comm_group (graded.homology R A i) :=
by { dsimp [graded.homology], apply_instance, }

instance (A : ℕ → Type v) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_module R A] (i : ℕ) :
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

-- At this point we specialise the universe levels, because we only have the monoidal structure on `Module R` in that case.

def nn (A : ℕ → Type u) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A] (i j : ℕ) :
  (to_cochain_complex R A).homology i ⊗ (to_cochain_complex R A).homology j ⟶ (to_cochain_complex R A).homology (i + j) :=
begin
  refine (foo _).hom ≫ _,
  refine cokernel.desc _ _ _,
  refine (foo' _).hom ≫ _,
  refine cokernel.desc _ _ _,
  refine _ ≫ cokernel.π _,
  refine factor_thru_kernel_subobject _ _ _,
  refine ((kernel_subobject _).arrow ⊗ (kernel_subobject _).arrow) ≫ _,
  exact Module.of_hom (mul_bilinear R A i j),
  -- Now we have three proof obligations. Discharging these nicely will require some custom extensionality lemmas.
  { apply tensor_product.ext', intros, sorry, },
  { sorry, },
  { sorry, }
end

def mm (A : ℕ → Type u) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A] (i j : ℕ) :
  graded.homology R A j →ₗ[R] (graded.homology R A i →ₗ[R] graded.homology R A (i + j)) :=
monoidal_closed.curry (nn R A i j).




namespace Module

namespace homology

variables {R}
variables {M N P : Module.{u} R} (f : M ⟶ N) (g : N ⟶ P) (w : f ≫ g = 0)

/--
Construct elements of the homology of `f g` from elements of the kernel of `g`.
-/
def mk : linear_map.ker g →ₗ[R] (homology f g w : Module R) :=
(Module.kernel_iso_ker g).inv ≫ (kernel_subobject_iso g).inv ≫ homology.π f g w

variables {f g w}

/--
Pick an arbitrary representative of the homology of a pair of morphisms `f g`.
-/
def out (x : homology f g w) : linear_map.ker g :=
(Module.kernel_iso_ker g).hom ((kernel_subobject_iso g).hom
  (quot.out ((Module.cokernel_iso_range_quotient _).hom x)))

@[simp]
lemma mk_out (x : homology f g w) :
  mk f g w (out x) = x :=
begin
  dsimp [mk, out],
  apply (show function.injective (cokernel_iso_range_quotient (image_to_kernel f g w)).hom,
    { rw ←mono_iff_injective, apply_instance, }),
  simp only [set_like.eta, category_theory.coe_hom_inv_id, homology.π,
    cokernel_π_cokernel_iso_range_quotient_hom_apply, submodule.mkq_apply],
  apply quotient.out_eq',
end

-- We supply an arbitrary proof that `g (f z) = 0`, so this can be used to rewrite.
@[simp]
lemma mk_boundary (z : M) (h : g (f z) = 0) : mk f g w ⟨f z, h⟩ = 0 :=
begin
  dsimp [mk],
  convert linear_map.congr_fun (homology.condition f g w) (factor_thru_image_subobject f z) using 2,
  apply (show function.injective (kernel_subobject g).arrow,
    { rw ←mono_iff_injective, apply_instance, }),
  simp,
end

/--
To show that two elements in homology constructed from representatives are the same,
it suffices to show those representatives differ by a boundary.
-/
lemma mk_ext {x y : linear_map.ker g} (z : M) (h : x.1 = y.1 + f z) :
  mk f g w x = mk f g w y :=
begin
  have h' : x = y + ⟨f z, linear_map.congr_fun w z⟩, { ext, exact h, },
  subst h',
  rw [linear_map.map_add, mk_boundary, add_zero],
end

/--
To show two elements in homology are the same,
it suffices to show their representatives differ by a boundary.
-/
lemma ext {x y : homology f g w}
  (z : M) (h : homology.out x = homology.out y + ⟨f z, linear_map.congr_fun w z⟩) :
  x = y :=
begin
  rw [←mk_out x, ←mk_out y],
  exact mk_ext _ (congr_arg subtype.val h),
end

end homology

end Module



variables (A : ℕ → Type u) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A]

lemma d_from_nat {V : Type*} [category V] [has_zero_morphisms V] [has_zero_object V] (C : cochain_complex V ℕ) (i : ℕ) :
  homological_complex.d_from C i = C.d i (i+1) ≫ (C.X_next_iso rfl).inv :=
by rw homological_complex.d_from_eq

lemma d_to_nat {V : Type*} [category V] [has_zero_morphisms V] [has_zero_object V] (C : chain_complex V ℕ) (i : ℕ) :
  homological_complex.d_to C i = (C.X_prev_iso rfl).hom ≫ C.d (i+1) i :=
by rw homological_complex.d_to_eq

lemma d_from_eq_zero {i : ℕ} {x : A i} (dx : d x = 0) :
  (homological_complex.d_from (to_cochain_complex R A) i) x = 0 :=
begin
  rw d_from_nat,
  simp [to_cochain_complex],
  erw [dx, linear_map.map_zero],
end

@[simp]
lemma iso_hom_apply_eq_zero {X Y : Module R} (f : X ≅ Y) (x : X) : f.hom x = 0 ↔ x = 0 := sorry
@[simp]
lemma iso_inv_apply_eq_zero {X Y : Module R} (f : X ≅ Y) (y : Y) : f.inv y = 0 ↔ y = 0 := sorry

@[simp]
lemma ker_d_from_nat (C : cochain_complex (Module R) ℕ) (i : ℕ) :
  linear_map.ker (homological_complex.d_from C i) = linear_map.ker (C.d i (i+1)) :=
begin
  rw d_from_nat,
  ext, split,
  { intro h, simpa using h, },
  { intro h, simpa using h, },
end

section
open Module.homology

@[simp] lemma d_out (A : ℕ → Type u) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A] (i : ℕ)
  (x : graded.homology R A i) : (d : A i →+ A (i+1)) (@coe _ ((to_cochain_complex R A).X i) (@coe_to_lift _ _ (@coe_base _ _ coe_subtype)) (out x)) = 0 :=
by simpa using (out x).2

def mm' (A : ℕ → Type u) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A] (i j : ℕ) :
  graded.homology R A j →ₗ[R] (graded.homology R A i →ₗ[R] graded.homology R A (i + j)) :=
{ to_fun := λ x,
  { to_fun := λ y, mk _ _ _ begin fsplit, exact (gmul (out y).1 (out x).1 : A (i + j)), simp, rw mul_cycle_of_cycle_cycle', simp, simp, end,
    map_add' := sorry,
    map_smul' := sorry, },
  map_add' := sorry,
  map_smul' := sorry, }

end

def mk {i : ℕ} (x : A i) (dx : d x = 0) : (to_cochain_complex R A).homology i :=
Module.homology.mk _ _ _ begin fsplit, exact x, exact d_from_eq_zero R A dx, end

-- def mk' {i : ℕ} (x : add_monoid_hom.ker (d : A i →+ A (i+1))) : (to_cochain_complex R A).homology i :=
-- Module.homology.mk _ _ _ begin fsplit, exact x.1, exact d_from_eq_zero R A x.2, end

lemma mk_out {i : ℕ} (x : (to_cochain_complex R A).homology i) :
  mk R A (Module.homology.out x).1 sorry = x :=
sorry

lemma mk_cast (A : ℕ → Type u) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A]
  {i j : ℕ} (h : i = j) (x : A i) (dx : d (cast (congr_arg A h) x) = 0) :
  mk R A (cast (congr_arg A h) x) dx =
    cast (congr_arg (graded.homology R A) h : graded.homology R A i = graded.homology R A j)
    (mk R A x (by { cases h, simpa using dx })) :=
begin
  cases h,
  refl,
end

lemma nn_mk_mk (A : ℕ → Type*) [Π n, add_comm_group (A n)] [Π n, module R (A n)] [differential_graded_algebra R A]
  {i j} (x : A i) (dx : d x = 0) (y : A j) (dy : d y = 0) :
  nn R A i j (mk R A x dx ⊗ₜ[R] mk R A y dy) =
  mk R A (gmul x y) (mul_cycle_of_cycle_cycle x y dx dy) :=
begin
  dsimp [nn, foo],
  erw inv_cokernel_comparison_desc_apply,
end

def one : graded.homology R A 0 :=
mk R A (1 : A 0) (d_one A)

lemma one_mul'
  {i : ℕ} (x : graded.homology R A i) :
  (nn R A 0 i) (one R A ⊗ₜ[R] x) = cast sorry x :=
begin
  rw ←mk_out R A x,
  rw one,
  rw nn_mk_mk,
  simp only [one_gmul],
  rw mk_cast,
  refl,
end

instance :
  graded_monoid (graded.homology R A) :=
{ one := one R A,
  mul := λ i j x y, mm R A i j y x,
  one_mul := λ i x, one_mul' R A x,
  mul_one := sorry,
  mul_assoc := sorry, }

lemma graded.homology.gmul_def
  {i j} (x : graded.homology R A i) (y : graded.homology R A j) : gmul x y = mm R A i j y x :=
rfl

instance :
  graded_semiring (graded.homology R A) :=
{ mul_zero := begin intros, simp only [graded.homology.gmul_def, mm], simp only [linear_map.zero_apply, map_zero], end,
  zero_mul := begin intros, simp only [graded.homology.gmul_def, mm], simp only [map_zero], end,
  left_distrib := begin intros, simp only [graded.homology.gmul_def, mm], simp only [map_add, add_left_inj, linear_map.add_apply], end,
  right_distrib := begin intros, simp only [graded.homology.gmul_def, mm, linear_map.map_add], end, }

-- total

-- @[derive add_comm_monoid]
-- def graded.total (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] := dfinsupp A

-- instance (A : ℕ → Type*) [Π n, add_comm_group (A n)] : add_comm_group (graded.total A) :=
-- by { dsimp [graded.total], apply_instance, }

-- instance (A : ℕ → Type*) [Π n, add_comm_monoid (A n)] [graded_semiring A] : semiring (graded.total A) :=
-- { mul := λ f g, begin end,
--   ..(by apply_instance : add_comm_monoid (graded.total A)) }
