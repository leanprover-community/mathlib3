/-

The Genera Linear group $GL(n, R)$
-/
import linear_algebra.matrix
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.special_linear_group
import linear_algebra.determinant


/-!
# The General Linear group $GL(n, R)$

This file defines the elements of the General Linear group `general_linear_group n R`,
consisting of all invertible `n` by `n` `R`-matrices.


## Main definitions

 * `matrix.GL` is the type of matrices over R with unit determinant
 * `matrix.GL.group` gives the group structure (under multiplication)
 * `matrix.GL_plus.GL_pos` gives the subgroup of matrices with positive determinant (over a linear ordered ring)

## Implementation notes


## References


## Tags

matrix group, group, matrix inverse
-/

namespace matrix
universes u v
open_locale matrix
open linear_map


section

variables (n : Type u) [decidable_eq n] [fintype n] (R : Type v) [comm_ring R]

/-- `GL n R` is the group of `n` by `n` `R`-matrices with unit determinant. 
Defined as a subtype of matrices
-/
abbreviation GL (R : Type*) [comm_ring R] :  Type* := units (matrix n n R )





lemma GL.is_unit_det  (A : GL n R) : is_unit ( (A : matrix n n R).det) :=
begin
  rw ←matrix.is_unit_iff_is_unit_det,
  exact units.is_unit _
end


/--The `GL n R` and `general_linear_group R n` are multiplicatively equivalent-/
def GL_mul_equiv_general_linear_group : (GL n R) ≃* (linear_map.general_linear_group R ( n → R)) :=
units.map_equiv to_lin_alg_equiv'.to_mul_equiv

/--Given a matrix with unit determinant we get an element of `GL n R`-/
noncomputable def GL.mk' (A: matrix n n R) (h: is_unit (det A)): GL n R:=
⟨A, nonsing_inv A, by {apply mul_nonsing_inv, apply h,}, by  {apply nonsing_inv_mul, apply h, }⟩ 

end
namespace GL



variables {n : Type u} [decidable_eq n] [fintype n] {R : Type v} [comm_ring R]

instance coe_matrix : has_coe (GL n R) (matrix n n R) :=
⟨λ A, A.val⟩


instance coe_fun : has_coe_to_fun (GL n R) :=
{ F   := λ _, n → n → R,
  coe := λ A, A.val }

/--Given a element of `GL n R` it gives the associated linear map-/

def to_lin' (A : GL n R) := matrix.to_lin' A

lemma ext_iff (A B : GL n R) : A = B ↔ (∀ i j, A i j = B i j) :=
begin
dsimp at *, fsplit, work_on_goal 0 { intros ᾰ i j, induction ᾰ, refl }, intros ᾰ,
 ext1, dsimp at *, ext1, solve_by_elim,
end

@[ext] lemma ext (A B : GL n R) : (∀ i j, A i j = B i j) → A = B :=
(GL.ext_iff A B).mpr



section coe_lemmas

variables (A B : GL n R)





@[simp] lemma mul_val : ↑(A * B) = A ⬝ B := rfl

@[simp] lemma mul_apply : ⇑(A * B) = (A ⬝ B) := rfl




@[simp] lemma one_val : ↑(1 : GL n R) = (1 : matrix n n R) := rfl

@[simp] lemma one_apply : ⇑(1 : GL n R) = (1 : matrix n n R) := rfl


@[simp] lemma to_lin'_mul :
  to_lin' (A * B) = (to_lin' A).comp (to_lin' B) :=
matrix.to_lin'_mul A B

@[simp] lemma to_lin'_one :
  to_lin' (1 : GL n R) = linear_map.id :=
matrix.to_lin'_one




noncomputable instance:  has_inv (GL n R):=
⟨λ A, ⟨nonsing_inv A, A, by {simp, apply nonsing_inv_mul, apply GL.is_unit_det _ _ A,},
by { simp, apply mul_nonsing_inv, apply GL.is_unit_det _ _ A, }, ⟩⟩

@[simp] lemma inv_val : ↑(A⁻¹) = nonsing_inv A := rfl

@[simp] lemma inv_apply : ⇑(A⁻¹) = nonsing_inv A := rfl

end coe_lemmas

lemma is_left_inv (A : GL n R): A⁻¹ *  A = 1:=

begin
 have h0:= GL.is_unit_det _ _ A,
have:=nonsing_inv_mul A h0, rw ← mul_eq_mul at this, ext, dsimp,rw nonsing_inv,
cases h0, dsimp at *, solve_by_elim,
end


noncomputable instance : group (GL n R) :=
{ mul := λ u₁ u₂, ⟨u₁.val * u₂.val, u₂.inv * u₁.inv,
    by rw [mul_assoc, ← mul_assoc u₂.val, units.val_inv, one_mul, units.val_inv],
    by rw [mul_assoc, ← mul_assoc u₁.inv, units.inv_val, one_mul, units.inv_val]⟩,
  one := ⟨1, 1, one_mul 1, one_mul 1⟩,
  mul_one := λ u,  mul_one u,
  one_mul := λ u,  one_mul u,
  mul_assoc := λ u₁ u₂ u₃,  mul_assoc u₁ u₂ u₃,
  inv := GL.has_inv.inv,
  mul_left_inv := λ u,  by {apply is_left_inv,} }


lemma sl_det_is_unit (A: special_linear_group n R ): is_unit (det A):=
begin
have:=A.2, simp at *,
end




noncomputable instance SL_to_GL: has_coe (special_linear_group n R) (GL n R):=
 ⟨λ A,  ⟨A.1, nonsing_inv A.1, by {apply mul_nonsing_inv, apply sl_det_is_unit A,}, by  {apply nonsing_inv_mul, apply sl_det_is_unit A, } ⟩ ⟩




@[simp] lemma GL_vals (A : GL n R): ∀ i j, A i j = A.1 i j:=
begin
unfold_coes, intros i j, 
refl,
end  



lemma det_not_zero [nontrivial R] (A: GL n R): det A ≠ 0:=
begin
have:=GL.is_unit_det _ _ A, simp, by_contradiction, unfold_coes at *, rw h at this, simp at *, exact this,
 end  



end GL

namespace GL_plus

variables  (n : Type u) [decidable_eq n] [fintype n] (R : Type v)
 [linear_ordered_comm_ring R ]


lemma one_in_GL_pos : 0 < det (1:GL n R ) :=
begin
simp only [det_one, gt_iff_lt, GL.one_apply,zero_lt_one],
end


lemma mul_in_GL_pos (A B :GL n R ) (h1: 0<  det A  ) (h2: 0<  det B ): 0 <det (A*B):=

begin
simp only [gt_iff_lt, det_mul, mul_eq_mul], apply mul_pos h1 h2,
end


lemma inv_det_pos  (A:GL n R ) (h: 0 < det A ):  0 < det (A⁻¹).1 :=

begin
have h0:=(GL.is_unit_det _ _ A),
have h1:=is_unit_nonsing_inv_det A h0,
have h2:= nonsing_inv_det A h0,
have h3: 0 < det ⇑A*  det (⇑A)⁻¹ , by {rw mul_comm, rw h2, linarith}, unfold_coes at *,
convert (zero_lt_mul_left h).mp h3,
end



/-- This is the subgroup of `nxn` matrices with  entries over a
linear ordered ring and positive determinant-/


noncomputable def GL_pos : subgroup (GL n R) :=
{carrier:={M  | 0 < det M},
 one_mem':=one_in_GL_pos _ _ ,
 mul_mem':=λ A B h1 h2, mul_in_GL_pos _ _ A B h1 h2,
 inv_mem':=λ A h1, by {have:= inv_det_pos _ _ A h1, simp only [set.mem_set_of_eq] at *,
 unfold_coes at *, convert this, }
}




@[simp] lemma mem_GL_pos (A: GL n R ) :
  A  ∈ (GL_pos n R)  ↔ 0 < A.1.det := iff.rfl


instance GL_pos_to_GL : has_coe (GL_pos n R)  (GL n R) := ⟨λ A, A.val⟩



lemma SL_det_pos' (A : special_linear_group n R): 0< (A).1.det:=

begin
have:=A.2, simp only [gt_iff_lt, subtype.val_eq_coe],
 simp only [subtype.val_eq_coe] at this,  rw this,linarith,
end

noncomputable instance SL_to_GL_pos: has_coe (special_linear_group n R) (GL_pos n R):=
⟨λ A, ⟨(A : GL n R), by {simp, apply SL_det_pos' _ _ A}, ⟩⟩

end GL_plus



end matrix
