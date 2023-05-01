import algebra.category.Algebra.basic
import algebra.module.opposites
import ring_theory.tensor_product
import algebra.category.Module.basic
import category_theory.closed.monoidal
import algebraic_geometry.GroupObject.CommAlg
noncomputable theory
universes v u w
open category_theory
open_locale tensor_product

lemma algebra.tensor_product.map_id {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] :
  algebra.tensor_product.map (alg_hom.id R A) (alg_hom.id R A) = alg_hom.id R (A ⊗[R] A) :=
alg_hom.ext $ λ x, linear_map.ext_iff.1 tensor_product.map_id x

lemma algebra.tensor_product.map_comp {R A B C A' B' C' : Type*} [comm_semiring R] [semiring A]
  [semiring B] [semiring C] [semiring A'] [semiring B'] [semiring C'] [algebra R A] [algebra R B]
  [algebra R C] [algebra R A'] [algebra R B'] [algebra R C']
  (f' : B →ₐ[R] C) (f : A →ₐ[R] B) (g' : B' →ₐ[R] C') (g : A' →ₐ[R] B') :
  algebra.tensor_product.map (f'.comp f) (g'.comp g) = (algebra.tensor_product.map f' g').comp
    (algebra.tensor_product.map f g) :=
alg_hom.ext $ λ x, linear_map.ext_iff.1 (tensor_product.map_comp f'.to_linear_map
  f.to_linear_map g'.to_linear_map g.to_linear_map) x

--bundled or not?
class coalgebra (R : Type u) [comm_semiring R] (A : Type v)
  [add_comm_monoid A] [module R A] :=
(comul' : A →ₗ[R] A ⊗[R] A)
(counit' : A →ₗ[R] R)
(comul_coassoc' : (tensor_product.assoc R A A A).to_linear_map.comp
  ((tensor_product.map comul' linear_map.id).comp comul')
  = (tensor_product.map linear_map.id comul').comp comul')
(counit_right' : (tensor_product.rid R A).to_linear_map.comp
  ((tensor_product.map linear_map.id counit').comp comul') = linear_map.id)
(counit_left' : (tensor_product.lid R A).to_linear_map.comp
  ((tensor_product.map counit' linear_map.id).comp comul') = linear_map.id)

structure Coalgebra (R : Type u) [comm_ring R] :=
(carrier : Type v)
[is_add_comm_group : add_comm_group carrier]
[is_module : module R carrier]
[is_coalgebra : coalgebra R carrier]

instance {R : Type u} [comm_ring R] : has_coe_to_sort (Coalgebra R) (Type v) := ⟨Coalgebra.carrier⟩

def Coalgebra.of (R : Type u) [comm_ring R] (A : Type v) [add_comm_group A]
  [module R A] [coalgebra R A] : Coalgebra R := ⟨A⟩

attribute [instance] Coalgebra.is_add_comm_group Coalgebra.is_module Coalgebra.is_coalgebra
namespace coalgebra
variables (R : Type*) [comm_semiring R] (A : Type*) [add_comm_monoid A] [module R A]
  [coalgebra R A] {B : Type*} [add_comm_monoid B] [module R B] [coalgebra R B]

def comul := @comul' R _ A _ _
def counit := @counit' R _ A _ _

variables {R A}

lemma comul_coassoc : (tensor_product.assoc R A A A).to_linear_map.comp
  ((tensor_product.map (comul R A) linear_map.id).comp (comul R A))
  = (tensor_product.map linear_map.id (comul R A)).comp (comul R A) :=
comul_coassoc'

lemma counit_right : (tensor_product.rid R A).to_linear_map.comp
  ((tensor_product.map linear_map.id (counit R A)).comp (comul R A)) = linear_map.id :=
counit_right'

lemma counit_left : (tensor_product.lid R A).to_linear_map.comp
  ((tensor_product.map (counit R A) linear_map.id).comp (comul R A)) = linear_map.id :=
counit_left'

end coalgebra
open coalgebra
-- with asterisk or not?
@[ext] structure coalg_hom (R : Type*) [comm_semiring R] (A : Type*) [add_comm_monoid A]
  [module R A] [coalgebra R A] (B : Type*) [add_comm_monoid B] [module R B] [coalgebra R B]
  extends A →ₗ[R] B :=
(map_comul : (tensor_product.map to_linear_map to_linear_map).comp (comul R A)
  = (comul R B).comp to_linear_map)
(map_counit : (counit R B).comp to_linear_map = counit R A)

namespace coalg_hom
open coalgebra
variables {R : Type*} [comm_semiring R] {A : Type*} [add_comm_monoid A] [module R A]
  [coalgebra R A] {B : Type*} [add_comm_monoid B] [module R B] [coalgebra R B]
  {C : Type*} [add_comm_monoid C] [module R C] [coalgebra R C]

@[simp] lemma map_comul_apply (f : coalg_hom R A B) (x : A) :
  (tensor_product.map f.1 f.1) (comul R A x) = comul R B (f.1 x) :=
linear_map.ext_iff.1 f.map_comul x

@[simp] lemma map_counit_apply (f : coalg_hom R A B) (x : A) :
  counit R B (f.1 x) = counit R A x := linear_map.ext_iff.1 f.map_counit x

variables (R A)

@[simps] def id : coalg_hom R A A :=
{ to_linear_map := linear_map.id,
  map_comul :=
  begin
    ext,
    simp only [tensor_product.map_id, linear_map.id_comp, linear_map.comp_id],
  end,
  map_counit := by ext; refl }

variables {R A}

@[simps] def comp (g : coalg_hom R B C) (f : coalg_hom R A B) : coalg_hom R A C :=
{ to_linear_map := g.1.comp f.1,
  map_comul :=
  begin
    ext,
    simp only [tensor_product.map_comp, linear_map.coe_comp, function.comp_app, map_comul_apply],
  end,
  map_counit :=
  begin
    ext,
    dsimp,
    rw [map_counit_apply, map_counit_apply],
  end }

end coalg_hom

section
variables {R : Type u} [comm_ring R]

instance Coalgebra.category : category (Coalgebra.{v} R) :=
{ hom   := λ A B, coalg_hom R A B,
  id    := λ A, coalg_hom.id R A,
  comp  := λ A B C f g, g.comp f }.

instance : concrete_category.{v} (Coalgebra.{v} R) :=
{ forget := { obj := λ A, A, map := λ A B f, (f.to_linear_map : A → B) },
  forget_faithful := { } }

instance : has_forget₂ (Coalgebra.{v} R) (Module.{v} R) :=
{ forget₂ :=
  { obj := λ A, Module.of R A,
    map := λ A B f, f.to_linear_map }}

end
section
set_option old_structure_cmd true

class bialgebra (R : Type*) [comm_semiring R] (A : Type*) [semiring A] [algebra R A]
  extends coalgebra R A :=
(comul_map_one' : comul' 1 = 1)
(comul_map_mul' : ∀ x y, comul' (x * y) = comul' x * comul' y)
(counit_map_one' : counit' 1 = 1)
(counit_map_mul' : ∀ x y, counit' (x * y) = counit' x * counit' y)
end

section
variables (R : Type u) [comm_ring R] (A : Type v)

structure Bialgebra :=
(carrier : Type v)
[is_ring : ring carrier]
[is_algebra : algebra R carrier]
[is_bialgebra : bialgebra R carrier]

structure CommBialgebra :=
(carrier : Type v)
[is_comm_ring : comm_ring carrier]
[is_algebra : algebra R carrier]
[is_bialgebra : bialgebra R carrier]

instance : has_coe_to_sort (Bialgebra R) (Type v) := ⟨Bialgebra.carrier⟩
instance : has_coe_to_sort (CommBialgebra R) (Type v) :=
⟨CommBialgebra.carrier⟩

attribute [instance] Bialgebra.is_ring Bialgebra.is_algebra Bialgebra.is_bialgebra
  CommBialgebra.is_comm_ring CommBialgebra.is_algebra CommBialgebra.is_bialgebra

def Bialgebra.of [ring A] [algebra R A] [bialgebra R A] : Bialgebra R := ⟨A⟩

def CommBialgebra.of [comm_ring A] [algebra R A] [bialgebra R A] : CommBialgebra R := ⟨A⟩

variables {R}

def Bialgebra.to_Coalgebra (A : Bialgebra R) : Coalgebra R := ⟨A⟩
def CommBialgebra.to_Bialgebra (A : CommBialgebra R) : Bialgebra R := ⟨A⟩
def CommBialgebra.to_CommAlg (A : CommBialgebra R) : CommAlg R := ⟨A⟩

end
namespace bialgebra

variables (R : Type*) [comm_semiring R] (A : Type*) [semiring A] [algebra R A] [bialgebra R A]

def comul : A →ₐ[R] A ⊗[R] A :=
alg_hom.of_linear_map comul' comul_map_one' comul_map_mul'

def counit : A →ₐ[R] R :=
alg_hom.of_linear_map counit' counit_map_one' counit_map_mul'

lemma comul_coassoc : (algebra.tensor_product.assoc R A A A).to_alg_hom.comp
  ((algebra.tensor_product.map (comul R A) (alg_hom.id R A)).comp (comul R A))
  = (algebra.tensor_product.map (alg_hom.id R A) (comul R A)).comp (comul R A) :=
by ext; exact linear_map.ext_iff.1 (@comul_coassoc' R _ A _ _ _) x

lemma counit_right : (algebra.tensor_product.rid R A).to_alg_hom.comp
  ((algebra.tensor_product.map (alg_hom.id R A) (counit R A)).comp (comul R A)) = alg_hom.id R A :=
by ext; exact linear_map.ext_iff.1 (@counit_right' R _ A _ _ _) x

lemma counit_left : (algebra.tensor_product.lid R A).to_alg_hom.comp
  ((algebra.tensor_product.map (counit R A) (alg_hom.id R A)).comp (comul R A)) = alg_hom.id R A :=
by ext; exact linear_map.ext_iff.1 (@counit_left' R _ A _ _ _) x

def mk' {A : Type*} [semiring A] [algebra R A]
  (comul : A →ₐ[R] A ⊗[R] A) (counit : A →ₐ[R] R)
  (comul_coassoc : (tensor_product.assoc R A A A).to_linear_map.comp
  ((tensor_product.map comul.to_linear_map linear_map.id).comp comul.to_linear_map)
  = (tensor_product.map linear_map.id comul.to_linear_map).comp comul.to_linear_map)
  (counit_right : (tensor_product.rid R A).to_linear_map.comp
  ((tensor_product.map linear_map.id counit.to_linear_map).comp comul.to_linear_map)
  = linear_map.id)
  (counit_left : (tensor_product.lid R A).to_linear_map.comp
  ((tensor_product.map counit.to_linear_map linear_map.id).comp comul.to_linear_map)
  = linear_map.id) :
  bialgebra R A :=
{ comul' := comul.to_linear_map,
  counit' := counit.to_linear_map,
  comul_coassoc' := comul_coassoc,
  counit_right' := counit_right,
  counit_left' := counit_left,
  comul_map_one' := map_one comul,
  comul_map_mul' := map_mul comul,
  counit_map_one' := map_one counit,
  counit_map_mul' := map_mul counit }

end bialgebra
section
variables (R : Type*) [comm_semiring R] (A : Type*) [semiring A] [algebra R A]
  [bialgebra R A] (B : Type*) [semiring B] [algebra R B] [bialgebra R B]

open bialgebra
-- with asterisk or not?
@[ext] structure bialg_hom extends A →ₐ[R] B :=
(map_comul : (algebra.tensor_product.map to_alg_hom to_alg_hom).comp (comul R A)
  = (bialgebra.comul R B).comp to_alg_hom)
(map_counit : (bialgebra.counit R B).comp to_alg_hom = counit R A)

variables {R A B}

def bialg_hom.to_coalg_hom (f : bialg_hom R A B) : coalg_hom R A B :=
{ to_linear_map := f.to_alg_hom.to_linear_map,
  map_comul := by ext x; exact alg_hom.ext_iff.1 f.map_comul x,
  map_counit := by ext x; exact alg_hom.ext_iff.1 f.map_counit x }
end

namespace bialg_hom
open bialgebra
variables {R : Type*} [comm_semiring R] {A : Type*} [semiring A] [algebra R A]
  [bialgebra R A] {B : Type*} [semiring B] [algebra R B] [bialgebra R B]
  {C : Type*} [semiring C] [algebra R C] [bialgebra R C]

@[simp] lemma map_comul_apply (f : bialg_hom R A B) (x : A) :
  (algebra.tensor_product.map f.1 f.1) (bialgebra.comul R A x) = bialgebra.comul R B (f.1 x) :=
alg_hom.ext_iff.1 f.map_comul x

@[simp] lemma map_counit_apply (f : bialg_hom R A B) (x : A) :
  bialgebra.counit R B (f.1 x) = bialgebra.counit R A x := alg_hom.ext_iff.1 f.map_counit x

variables (R A)

@[simps] def id : bialg_hom R A A :=
{ to_alg_hom := alg_hom.id _ _,
  map_comul :=
  begin
    ext,
    simp only [algebra.tensor_product.map_id, alg_hom.id_comp, alg_hom.comp_id],
  end,
  map_counit := by ext; refl }

variables {R A}

@[simps] def comp (g : bialg_hom R B C) (f : bialg_hom R A B) : bialg_hom R A C :=
{ to_alg_hom := g.1.comp f.1,
  map_comul :=
  begin
    ext,
    simp only [algebra.tensor_product.map_comp, alg_hom.coe_comp,
      function.comp_app, map_comul_apply],
 end,
  map_counit :=
  begin
    ext,
    dsimp,
    rw [map_counit_apply, map_counit_apply],
  end }

end bialg_hom
section
variables {R : Type u} [comm_ring R]

instance : category (Bialgebra.{v} R) :=
{ hom   := λ A B, bialg_hom R A B,
  id    := λ A, bialg_hom.id R A,
  comp  := λ A B C f g, g.comp f }

instance : concrete_category.{v} (Bialgebra.{v} R) :=
{ forget := { obj := λ A, A, map := λ A B f, (f.to_alg_hom : A → B) },
  forget_faithful := { } }

instance : has_forget₂ (Bialgebra.{v} R) (Algebra.{v} R) :=
{ forget₂ :=
  { obj := λ A, Algebra.of R A,
    map := λ A₁ A₂ f, f.to_alg_hom } }

instance : has_forget₂ (Bialgebra.{v} R) (Coalgebra.{v} R) :=
{ forget₂ :=
  { obj := Bialgebra.to_Coalgebra,
    map := λ A₁ A₂ f, f.to_coalg_hom } }

instance :
  category (CommBialgebra.{v} R) :=
show category (induced_category (Bialgebra.{v} R) CommBialgebra.to_Bialgebra),
by apply_instance

instance : concrete_category.{v} (CommBialgebra.{v} R) :=
induced_category.concrete_category _

instance : has_forget₂ (CommBialgebra.{v} R) (Bialgebra.{v} R) :=
{ forget₂ :=
  { obj := CommBialgebra.to_Bialgebra,
    map := λ A₁ A₂ f, f } }

instance : has_forget₂ (CommBialgebra.{v} R) (CommAlg.{u v} R) :=
{ forget₂ :=
  { obj := CommBialgebra.to_CommAlg,
     map := λ A B f, f.to_alg_hom }}

end
section
set_option old_structure_cmd true

class hopf_algebra (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A]
  extends bialgebra R A :=
(i [] : A →ₗ[R] A)
(i_left [] : (linear_map.mul' R A).comp ((tensor_product.map i linear_map.id).comp
  (comul R A)) = (algebra.linear_map R A).comp (counit R A))
(i_right [] : (linear_map.mul' R A).comp ((tensor_product.map linear_map.id i).comp
  (comul R A)) = (algebra.linear_map R A).comp (counit R A))

end

section
variables (R : Type u) [comm_ring R]

structure HopfAlgebra :=
(carrier : Type v)
[is_ring : ring carrier]
[is_algebra : algebra R carrier]
[is_hopf_algebra : hopf_algebra R carrier]

structure CommHopfAlgebra :=
(carrier : Type v)
[is_comm_ring : comm_ring carrier]
[is_algebra : algebra R carrier]
[is_hopf_algebra : hopf_algebra R carrier]

attribute [instance] HopfAlgebra.is_ring HopfAlgebra.is_algebra HopfAlgebra.is_hopf_algebra
  CommHopfAlgebra.is_comm_ring CommHopfAlgebra.is_algebra CommHopfAlgebra.is_hopf_algebra

instance : has_coe_to_sort (HopfAlgebra R) (Type v) := ⟨HopfAlgebra.carrier⟩
instance : has_coe_to_sort (CommHopfAlgebra R) (Type v) :=
⟨CommHopfAlgebra.carrier⟩

def HopfAlgebra.of (A : Type v) [ring A] [algebra R A] [hopf_algebra R A] : HopfAlgebra R := ⟨A⟩
def CommHopfAlgebra.of (A : Type v) [comm_ring A] [algebra R A] [hopf_algebra R A] :
  CommHopfAlgebra R := ⟨A⟩

variables {R}

def HopfAlgebra.to_Bialgebra (A : HopfAlgebra R) :
  Bialgebra R :=
{ carrier := A.carrier,
  is_ring := by apply_instance,
  is_algebra := by apply_instance,
  is_bialgebra := by apply_instance }

def CommHopfAlgebra.to_HopfAlgebra (A : CommHopfAlgebra.{v} R) : HopfAlgebra.{v} R := ⟨A⟩
def CommHopfAlgebra.to_CommBialgebra (A : CommHopfAlgebra R) : CommBialgebra R := ⟨A⟩
def CommHopfAlgebra.to_CommAlg (A : CommHopfAlgebra R) : CommAlg R := ⟨A⟩

end
namespace hopf_algebra
section
variables (R : Type*) [comm_semiring R] (A : Type*) [semiring A] [algebra R A] [hopf_algebra R A]

def comul := bialgebra.comul R A
def counit := bialgebra.counit R A

lemma comul_coassoc : (algebra.tensor_product.assoc R A A A).to_alg_hom.comp
  ((algebra.tensor_product.map (comul R A) (alg_hom.id R A)).comp (comul R A))
  = (algebra.tensor_product.map (alg_hom.id R A) (comul R A)).comp (comul R A) :=
bialgebra.comul_coassoc R A

lemma counit_right : (algebra.tensor_product.rid R A).to_alg_hom.comp
  ((algebra.tensor_product.map (alg_hom.id R A) (counit R A)).comp (comul R A)) = alg_hom.id R A :=
bialgebra.counit_right R A

lemma counit_left : (algebra.tensor_product.lid R A).to_alg_hom.comp
  ((algebra.tensor_product.map (counit R A) (alg_hom.id R A)).comp (comul R A)) = alg_hom.id R A :=
bialgebra.counit_left R A

lemma i_map_one : i R A 1 = 1 := sorry
lemma i_map_mul {x y : A} : i R A (x * y) = i R A y * i R A x := sorry

def of_op_alg_hom {R : Type u} [comm_ring R] {A : Type v} [semiring A] [algebra R A] [bialgebra R A]
  (i : A →ₐ[R] Aᵐᵒᵖ) :
  hopf_algebra R A :=
{ i := (mul_opposite.op_linear_equiv R).symm.to_linear_map.comp i.to_linear_map,
  i_left := sorry,
  i_right := sorry, .. show bialgebra R A, by assumption }

def of_alg_hom {R : Type u} [comm_ring R] {A : Type v} [comm_semiring A] [algebra R A]
  [bialgebra R A] (i : A →ₐ[R] A) :
  hopf_algebra R A :=
{ i := i.to_linear_map,
  i_left := sorry,
  i_right := sorry, .. show bialgebra R A, by assumption }

end
end hopf_algebra
section
variables {R : Type u} [comm_ring R]

instance :
  category (HopfAlgebra.{v} R) :=
show category (induced_category (Bialgebra.{v} R) HopfAlgebra.to_Bialgebra),
by apply_instance

instance : concrete_category.{v} (HopfAlgebra.{v} R) :=
induced_category.concrete_category _

instance HopfAlgebra.has_forget₂_to_Bialgebra :
  has_forget₂ (HopfAlgebra.{v} R) (Bialgebra.{v} R) :=
{ forget₂ :=
  { obj := HopfAlgebra.to_Bialgebra,
    map := λ A₁ A₂ f, f } }

instance :
  category (CommHopfAlgebra.{v} R) :=
show category (induced_category (HopfAlgebra.{v} R) CommHopfAlgebra.to_HopfAlgebra),
by apply_instance

instance : concrete_category.{v} (CommHopfAlgebra.{v} R) :=
induced_category.concrete_category _

instance : has_forget₂ (CommHopfAlgebra.{v} R) (HopfAlgebra.{v} R) :=
{ forget₂ :=
  { obj := CommHopfAlgebra.to_HopfAlgebra,
    map := λ A₁ A₂ f, f } }

instance CommHopfAlgebra.has_forget₂_to_CommAlg :
  has_forget₂ (CommHopfAlgebra.{v} R) (CommAlg.{u v} R) :=
{ forget₂ :=
  { obj := CommHopfAlgebra.to_CommAlg,
     map := λ A B f, f.to_alg_hom }}

end

-- this'll need refactoring... but i don't care
