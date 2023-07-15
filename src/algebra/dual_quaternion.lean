/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.dual_number
import algebra.quaternion

/-!
# Dual quaternions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Similar to the way that rotations in 3D space can be represented by quaternions of unit length,
rigid motions in 3D space can be represented by dual quaternions of unit length.

## Main results

* `quaternion.dual_number_equiv`: quaternions over dual numbers or dual
  numbers over quaternions are equivalent constructions.

## References

* <https://en.wikipedia.org/wiki/Dual_quaternion>
-/

variables {R : Type*} [comm_ring R]

namespace quaternion

/-- The dual quaternions can be equivalently represented as a quaternion with dual coefficients,
or as a dual number with quaternion coefficients.

See also `matrix.dual_number_equiv` for a similar result. -/
def dual_number_equiv :
  quaternion (dual_number R) ≃ₐ[R] dual_number (quaternion R) :=
{ to_fun := λ q,
    (⟨q.re.fst, q.im_i.fst, q.im_j.fst, q.im_k.fst⟩,
     ⟨q.re.snd, q.im_i.snd, q.im_j.snd, q.im_k.snd⟩),
  inv_fun := λ d,
    ⟨(d.fst.re, d.snd.re), (d.fst.im_i, d.snd.im_i),
     (d.fst.im_j, d.snd.im_j), (d.fst.im_k, d.snd.im_k)⟩,
  left_inv := λ ⟨⟨r, rε⟩, ⟨i, iε⟩, ⟨j, jε⟩, ⟨k, kε⟩⟩, rfl,
  right_inv := λ ⟨⟨r, i, j, k⟩, ⟨rε, iε, jε, kε⟩⟩, rfl,
  map_mul' := begin
    rintros ⟨⟨xr, xrε⟩, ⟨xi, xiε⟩, ⟨xj, xjε⟩, ⟨xk, xkε⟩⟩,
    rintros ⟨⟨yr, yrε⟩, ⟨yi, yiε⟩, ⟨yj, yjε⟩, ⟨yk, ykε⟩⟩,
    ext : 1,
    { refl },
    { dsimp,
      congr' 1; ring },
  end,
  map_add' := begin
    rintros ⟨⟨xr, xrε⟩, ⟨xi, xiε⟩, ⟨xj, xjε⟩, ⟨xk, xkε⟩⟩,
    rintros ⟨⟨yr, yrε⟩, ⟨yi, yiε⟩, ⟨yj, yjε⟩, ⟨yk, ykε⟩⟩,
    refl
  end,
  commutes' := λ r, rfl }

/-! Lemmas characterizing `quaternion.dual_number_equiv`. -/

-- `simps` can't work on `dual_number` because it's not a structure
@[simp] lemma re_fst_dual_number_equiv (q : quaternion (dual_number R)) :
  (dual_number_equiv q).fst.re = q.re.fst := rfl
@[simp] lemma im_i_fst_dual_number_equiv (q : quaternion (dual_number R)) :
  (dual_number_equiv q).fst.im_i = q.im_i.fst := rfl
@[simp] lemma im_j_fst_dual_number_equiv (q : quaternion (dual_number R)) :
  (dual_number_equiv q).fst.im_j = q.im_j.fst := rfl
@[simp] lemma im_k_fst_dual_number_equiv (q : quaternion (dual_number R)) :
  (dual_number_equiv q).fst.im_k = q.im_k.fst := rfl
@[simp] lemma re_snd_dual_number_equiv (q : quaternion (dual_number R)) :
  (dual_number_equiv q).snd.re = q.re.snd := rfl
@[simp] lemma im_i_snd_dual_number_equiv (q : quaternion (dual_number R)) :
  (dual_number_equiv q).snd.im_i = q.im_i.snd := rfl
@[simp] lemma im_j_snd_dual_number_equiv (q : quaternion (dual_number R)) :
  (dual_number_equiv q).snd.im_j = q.im_j.snd := rfl
@[simp] lemma im_k_snd_dual_number_equiv (q : quaternion (dual_number R)) :
  (dual_number_equiv q).snd.im_k = q.im_k.snd := rfl
@[simp] lemma fst_re_dual_number_equiv_symm (d : dual_number (quaternion R)) :
  (dual_number_equiv.symm d).re.fst = d.fst.re := rfl
@[simp] lemma fst_im_i_dual_number_equiv_symm (d : dual_number (quaternion R)) :
  (dual_number_equiv.symm d).im_i.fst = d.fst.im_i := rfl
@[simp] lemma fst_im_j_dual_number_equiv_symm (d : dual_number (quaternion R)) :
  (dual_number_equiv.symm d).im_j.fst = d.fst.im_j := rfl
@[simp] lemma fst_im_k_dual_number_equiv_symm (d : dual_number (quaternion R)) :
  (dual_number_equiv.symm d).im_k.fst = d.fst.im_k := rfl
@[simp] lemma snd_re_dual_number_equiv_symm (d : dual_number (quaternion R)) :
  (dual_number_equiv.symm d).re.snd = d.snd.re := rfl
@[simp] lemma snd_im_i_dual_number_equiv_symm (d : dual_number (quaternion R)) :
  (dual_number_equiv.symm d).im_i.snd = d.snd.im_i := rfl
@[simp] lemma snd_im_j_dual_number_equiv_symm (d : dual_number (quaternion R)) :
  (dual_number_equiv.symm d).im_j.snd = d.snd.im_j := rfl
@[simp] lemma snd_im_k_dual_number_equiv_symm (d : dual_number (quaternion R)) :
  (dual_number_equiv.symm d).im_k.snd = d.snd.im_k := rfl

end quaternion
