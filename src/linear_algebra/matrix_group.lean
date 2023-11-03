/-
Copyright (c) 2022 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/

import algebra.group.defs
import group_theory.subgroup.basic
import data.matrix.basic
import linear_algebra.general_linear_group
import linear_algebra.unitary_group

/-!
# Matrix groups

In this file we define a typeclass `matrix_group` for groups, which elements are matrices and
the operation is matrix multiplication.

We provide $GL$, $U$, $O$, $SL$, $SU$, $SO$ as instances of matrix groups.

## Main definitions

* `matrix_group n R G` is a typeclass stating that `G` is a some group of `n` by `n` matrices
over `R`
* `matrix_group.special` is a function which takes a group `G` and produces a corresponding special
group (e.g. $U → SU$)

-/

-----------------------------------------------
/-
Maybe it should be added to algebra.hom.group? I'm a newbie and don't want to change
so fundamental file. This is only used in `special_to_matrix_group` below (implicitly).
-/

namespace hidden

variables (L M N : Type*) [mul_one_class L] [mul_one_class M] [mul_one_class N]

/--
  transitivity of `coe_is_monoid_hom`
-/
attribute [priority 100]
instance coe_is_monoid_hom_trans [LM_lift : has_lift_t L M] [MN_lift : has_lift_t M N]
  [LM_hom : coe_is_monoid_hom L M] [MN_hom : coe_is_monoid_hom M N] :
  @coe_is_monoid_hom L N ⟨MN_lift.lift ∘ LM_lift.lift⟩ _ _ :=
{ coe_one :=
  begin
    simp [coe, lift_t],
    have h : has_lift_t.lift (1 : L) = (1 : M), from LM_hom.coe_one,
    rw h, exact MN_hom.coe_one
  end,

  coe_mul :=
  begin
    intros x y,
    simp [coe, lift_t],
    have h : (has_lift_t.lift : L → M) (x * y) = has_lift_t.lift x * has_lift_t.lift y,
      from LM_hom.coe_mul _ _,
    rw h, exact MN_hom.coe_mul _ _
  end }

end hidden
open hidden
-------------------------------------------------


universes u u' v w w'

variables (n : out_param (Type u)) [decidable_eq n] [fintype n]
variables (R : out_param (Type v)) [comm_ring R]

/--
`matrix_group n R G` states that `G` is a group which elements are actually are `matrix n n R`.
-/
class matrix_group (G : Type w) extends group G, has_coe_t G (matrix n n R),
  coe_is_monoid_hom G (matrix n n R) :=
(coe_injective : function.injective coe)

variables {n R}

namespace matrix_group

section coe_to_GL
/--
`hom_to_GL` is a natural embedding of a matrix group into `GL`
-/
def hom_to_GL {G : Type w} [matrix_group n R G] : G →* (GL n R) :=
{ to_fun := λ x,
  { val := (x : matrix n n R),
    inv := ↑(x⁻¹),
    val_inv :=
    begin
      rw [←coe_is_monoid_hom.coe_mul x x⁻¹, mul_right_inv, coe_is_monoid_hom.coe_one],
      apply_instance
    end,
    inv_val :=
    begin
      rw [←coe_is_monoid_hom.coe_mul x⁻¹ x, inv_mul_self, coe_is_monoid_hom.coe_one],
      apply_instance
    end },

  map_one' :=
  begin
    apply units.ext,
    simp [units.val],
  end,

  map_mul' :=
  begin
    intros x y,
    apply units.ext,
    simp [units.val],
  end }

lemma hom_to_GL_injective {G : Type w} [h : matrix_group n R G] :
  function.injective (@hom_to_GL n _ _ R _ G _).to_fun :=
begin
  simp [function.injective], intros x y,
  simp [hom_to_GL],
  intro heq, intro _,
  exact h.coe_injective heq
end

instance has_coe_to_GL (G : Type w) [matrix_group n R G] : has_coe_t G (GL n R) :=
⟨hom_to_GL.to_fun⟩

instance coe_to_GL_is_hom (G : Type w) [matrix_group n R G] : coe_is_monoid_hom G (GL n R) :=
⟨hom_to_GL.map_one', hom_to_GL.map_mul'⟩

end coe_to_GL

section special

/--
`special G` is a subgroup of matrix group `G` of matrices with determinant $1$.
-/
def special (G : Type w) [matrix_group n R G] : subgroup G :=
@monoid_hom.ker G _ Rˣ _ (monoid_hom.comp (@matrix.general_linear_group.det n _ _ R _) hom_to_GL)

instance special_to_matrix_group {G : Type w} [h : matrix_group n R G] :
matrix_group n R ↥(special G) := @matrix_group.mk n _ _ R _ (special G) _ _
  (hidden.coe_is_monoid_hom_trans _ G _) -- TODO: make it implicit
  begin
    apply function.injective.comp,
    exacts [h.coe_injective, subtype.val_injective]
  end

end special

section examples
variables (n R)

instance GL_is_matrix_group : matrix_group n R (GL n R) := @matrix_group.mk n _ _ R _ (GL n R) _ _
  { coe_mul := by {intros x y, refl},
    coe_one := by refl }
  units.ext

instance U_is_matrix_group [star_ring R] : matrix_group n R (matrix.unitary_group n R) :=
@matrix_group.mk n _ _ R _ (matrix.unitary_group n R) _ _ _
  begin
    simp [function.injective],
    intros x y,
    simp [has_coe_t.coe, coe_b, has_coe.coe]
  end

/--
Special linear group
-/
def SL : subgroup (GL n R) := special (GL n R)
/--
Special unitary group
-/
def SU [star_ring R] : subgroup (matrix.unitary_group n R) := special (matrix.unitary_group n R)
/--
Special orthogonal group
-/
def SO : subgroup (matrix.orthogonal_group n R) := special (matrix.orthogonal_group n R)

end examples

end matrix_group
