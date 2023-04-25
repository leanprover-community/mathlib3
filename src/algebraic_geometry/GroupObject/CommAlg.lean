import algebra.category.Algebra.basic
import category_theory.monoidal.CommMon_
universes u v

open category_theory
#check Algebra
/-- The category of commutative `R`-algebras. -/
structure CommAlg (R : Type u) [comm_ring R] :=
(carrier : Type v)
[is_comm_ring : comm_ring carrier]
[is_algebra : algebra R carrier]

attribute [instance] CommAlg.is_comm_ring CommAlg.is_algebra

namespace CommAlg
variables (R : Type u) [comm_ring R]

instance : has_coe_to_sort (CommAlg R) (Type v) := ⟨CommAlg.carrier⟩

instance : category (CommAlg.{u v} R) :=
{ hom   := λ A B, A →ₐ[R] B,
  id    := λ A, alg_hom.id R A,
  comp  := λ A B C f g, g.comp f }

instance : concrete_category.{v} (CommAlg.{u v} R) :=
{ forget := { obj := λ R, R, map := λ R S f, (f : R → S) },
  forget_faithful := { } }

instance has_forget_to_Ring : has_forget₂ (CommAlg.{u v} R) Ring.{v} :=
{ forget₂ :=
  { obj := λ A, Ring.of A,
    map := λ A₁ A₂ f, alg_hom.to_ring_hom f, } }

instance has_forget_to_Module : has_forget₂ (CommAlg.{u v} R) (Module.{v} R) :=
{ forget₂ :=
  { obj := λ M, Module.of R M,
    map := λ M₁ M₂ f, alg_hom.to_linear_map f, } }

instance has_forget_to_Algebra : has_forget₂ (CommAlg.{u v} R) (Algebra.{v} R) :=
{ forget₂ :=
  { obj := λ A, Algebra.of R A.carrier,
    map := λ A B f, f }}

instance : monoidal_category (Algebra.{v} R) := by apply_instance

/-- The object in the category of commutative R-algebras associated to a type equipped with the
appropriate typeclasses. -/
def of (X : Type v) [comm_ring X] [algebra R X] : CommAlg.{u v} R := ⟨X⟩

/-- Typecheck a `alg_hom` as a morphism in `CommAlg R`. -/
def of_hom {R : Type u} [comm_ring R] {X Y : Type v} [comm_ring X] [algebra R X]
  [comm_ring Y] [algebra R Y] (f : X →ₐ[R] Y) : of R X ⟶ of R Y := f

@[simp] lemma of_hom_apply {R : Type u} [comm_ring R]
  {X Y : Type v} [comm_ring X] [algebra R X] [comm_ring Y] [algebra R Y] (f : X →ₐ[R] Y) (x : X) :
  of_hom f x = f x := rfl

instance : inhabited (CommAlg R) := ⟨of R R⟩

@[simp]
lemma coe_of (X : Type u) [comm_ring X] [algebra R X] : (of R X : Type u) = X := rfl

variables (R)

/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simps]
def of_self_iso (M : CommAlg.{u v} R) : CommAlg.of R M ≅ M :=
{ hom := 𝟙 M, inv := 𝟙 M }

variables {R} {M N U : CommAlg.{u v} R}

@[simp] lemma id_apply (m : M) : (𝟙 M : M → M) m = m := rfl

@[simp] lemma coe_comp (f : M ⟶ N) (g : N ⟶ U) :
  ((f ≫ g) : M → U) = g ∘ f := rfl


end CommAlg

variables {R : Type u} [comm_ring R]
variables {X₁ X₂ : Type u}

/-- Build an isomorphism in the category `CommAlg R` from a `alg_equiv` between commutative `algebra`s. -/
@[simps]
def alg_equiv.to_CommAlg_iso
  {g₁ : comm_ring X₁} {g₂ : comm_ring X₂} {m₁ : algebra R X₁} {m₂ : algebra R X₂} (e : X₁ ≃ₐ[R] X₂) :
  CommAlg.of R X₁ ≅ CommAlg.of R X₂ :=
{ hom := (e : X₁ →ₐ[R] X₂),
  inv := (e.symm : X₂ →ₐ[R] X₁),
  hom_inv_id' := begin ext, exact e.left_inv x, end,
  inv_hom_id' := begin ext, exact e.right_inv x, end, }

namespace category_theory.iso

/-- Build a `alg_equiv` from an isomorphism in the category `CommAlg R`. -/
@[simps]
def to_comm_alg_equiv {X Y : CommAlg R} (i : X ≅ Y) : X ≃ₐ[R] Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_add'  := by tidy,
  map_mul'  := by tidy,
  commutes' := by tidy, }.

end category_theory.iso

/-- Algebra equivalences between `algebras`s are the same as (isomorphic to) isomorphisms in
`Algebra`. -/
@[simps]
def alg_equiv_iso_CommAlg_iso {X Y : Type u}
  [comm_ring X] [comm_ring Y] [algebra R X] [algebra R Y] :
  (X ≃ₐ[R] Y) ≅ (CommAlg.of R X ≅ CommAlg.of R Y) :=
{ hom := λ e, e.to_CommAlg_iso,
  inv := λ i, i.to_comm_alg_equiv, }

instance (X : Type u) [comm_ring X] [algebra R X] : has_coe (subalgebra R X) (CommAlg R) :=
⟨ λ N, CommAlg.of R N ⟩

instance CommAlg.forget_reflects_isos : reflects_isomorphisms (forget (CommAlg.{u} R)) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    let i := as_iso ((forget (CommAlg.{u} R)).map f),
    let e : X ≃ₐ[R] Y := { ..f, ..i.to_equiv },
    exact ⟨(is_iso.of_iso e.to_CommAlg_iso).1⟩,
  end }
