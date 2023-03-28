/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.char_p.invertible
import linear_algebra.affine_space.midpoint

/-!
# Midpoint of a segment for characteristic zero

We collect lemmas that require that the underlying ring has characteristic zero.

## Tags

midpoint
-/

open affine_map affine_equiv

lemma line_map_inv_two {R : Type*} {V P : Type*} [division_ring R] [char_zero R]
  [add_comm_group V] [module R V] [add_torsor V P] (a b : P) :
  line_map a b (2⁻¹:R) = midpoint R a b :=
rfl

lemma line_map_one_half {R : Type*} {V P : Type*} [division_ring R] [char_zero R]
  [add_comm_group V] [module R V] [add_torsor V P] (a b : P) :
  line_map a b (1/2:R) = midpoint R a b :=
by rw [one_div, line_map_inv_two]

lemma homothety_inv_of_two {R : Type*} {V P : Type*} [comm_ring R] [invertible (2:R)]
  [add_comm_group V] [module R V] [add_torsor V P] (a b : P) :
  homothety a (⅟2:R) b = midpoint R a b :=
rfl

lemma homothety_inv_two {k : Type*} {V P : Type*} [field k] [char_zero k]
  [add_comm_group V] [module k V] [add_torsor V P] (a b : P) :
  homothety a (2⁻¹:k) b = midpoint k a b :=
rfl

lemma homothety_one_half {k : Type*} {V P : Type*} [field k] [char_zero k]
  [add_comm_group V] [module k V] [add_torsor V P] (a b : P) :
  homothety a (1/2:k) b = midpoint k a b :=
by rw [one_div, homothety_inv_two]

@[simp] lemma pi_midpoint_apply {k ι : Type*} {V : Π i : ι, Type*} {P : Π i : ι, Type*} [field k]
  [invertible (2:k)] [Π i, add_comm_group (V i)] [Π i, module k (V i)]
  [Π i, add_torsor (V i) (P i)] (f g : Π i, P i) (i : ι) :
  midpoint k f g i = midpoint k (f i) (g i) := rfl
