/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek
-/

/-!
# Copy functions for arrays

This file provides functions to copy (part) of an array to another array.
We include monadic variants.
-/

universe variables u v z

namespace array

variables {k : Type v → Type z} [monad k] {α : Type u} {β : Type v} {n m : ℕ}

/-- Auxiliary function for copying part of an array to another array while applying a function.
If `x` is an array of length `n`, and `y` is an array of length `m`, and `r` is an index,
then `map_copy_aux f r x y` will take the slice `x[r .. (min n m)]`, apply `f` to it,
and write it to the corresponding slice of `y`. -/
def map_copy_aux (f : α → β) : ℕ → array n α → array m β → array m β
| r x y := if h : r < n ∧ r < m then
             let fn : fin n := ⟨r, and.elim_left h⟩ in
             let fm : fin m := ⟨r, and.elim_right h⟩ in
             have wf : m - (r + 1) < m - r,
               from nat.lt_of_succ_le $ by rw [← nat.succ_sub h.2, nat.succ_sub_succ],
             map_copy_aux (r + 1) x $ y.write fm (f $ x.read fn)
           else y
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ a, m - a.1)⟩]}

/-- Function for copying part of an array to another array while applying a function.
If `x` is an array of length `n`, and `y` is an array of length `m`,
then `array.map_copy f x y` will take the first `(min n m)` coefficients of `x`, apply `f` to them,
and write them to the corresponding of `y`.

See `array.copy` for the version with `f = id`. -/
def map_copy (x : array n α) (y : array m β) (f : α → β) : array m β :=
map_copy_aux f 0 x y

/-- Function for copying part of an array to another array.
If `x` is an array of length `n`, and `y` is an array of length `m`,
then `array.copy f x y` will take the first `(min n m)` coefficients of `x`,
and write them to the corresponding of `y`.

See `array.map_copy` for a version that allows one to apply a function `f : α → β`
to the coefficients of `x` before writing to `y`. -/
def copy (x : array n α) (y : array m α) : array m α :=
map_copy x y id

/-- Auxiliary function for copying part of a list to an array while applying a function.
If `x` is an array of length `n`, and `l` is a list of length `k`, and `m` is an index,
then `map_copy_from_list_aux x f l m` will take the slice `l[m .. (min n k)]`, apply `f` to it,
and write it to the corresponding slice of `y`. -/
def map_copy_from_list_aux (x : array n β) (f : α → β) :
  list α → ℕ → array n β
| [] m          := x
| (a :: rest) m := if h : m < n then
                     (map_copy_from_list_aux rest (m + 1)).write ⟨m, h⟩ (f a)
                   else x

/-- Function for copying part of a list to an array while applying a function.
If `x` is an array of length `n`, and `l` is a list of length `k`, and `m` is an index,
then `array.map_copy_from_list x f l` will take the the first `(min n k)` coefficients of `l`,
apply `f` to them, and write them to the corresponding coefficients of `x`. -/
def map_copy_from_list (x : array n β) (f : α → β) (l : list α) : array n β :=
map_copy_from_list_aux x f l 0

/-- Auxiliary function for monadic copying
part of an array to another array while applying a function.
If `x` is an array of length `n`, and `y` is an array of length `m`, and `r` is an index,
then `mmap_copy_aux f r x y` will take the slice `x[r .. (min n m)]`,
apply the monadic function `f` to it, and write it to the corresponding slice of `y`. -/
def mmap_copy_aux (f : α → k β) : ℕ → array n α → array m β → k (array m β)
| r x y := do if h : r < n ∧ r < m then do
                let fn : fin n := ⟨r, and.elim_left h⟩,
                let fm : fin m := ⟨r, and.elim_right h⟩,
                y ← y.write fm <$> f (x.read fn),
                have wf : m - (r + 1) < m - r,
                  from nat.lt_of_succ_le $ by rw [← nat.succ_sub h.2, nat.succ_sub_succ],
                mmap_copy_aux (r + 1) x y
              else return y
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ a, m - a.1)⟩]}

/-- Function for monadic copying part of an array to another array while applying a function.
If `x` is an array of length `n`, and `y` is an array of length `m`,
then `array.mmap_copy f x y` will take the first `(min n m)` coefficients of `x`,
apply the monadic function `f` to them, and write them to the corresponding of `y`. -/
def mmap_copy (x : array n α) (y : array m β) (f : α → k β) : k (array m β) :=
mmap_copy_aux f 0 x y

end array
