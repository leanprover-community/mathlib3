/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.fin.vec_notation

/-!
# Stuff for data.fin.vec_notation
-/

namespace function
open matrix (vec_cons)
open fin

lemma update_head {α : Type*} {i : ℕ} {x y : α} {t : fin i → α} :
  update (vec_cons x t) 0 y = vec_cons y t :=
begin
  rw [funext_iff, fin.forall_fin_succ],
  refine ⟨rfl, λ j, _⟩,
  rw update_noteq,
  { simp only [vec_cons, fin.cons_succ] },
  exact succ_ne_zero j
end

lemma update_cons_one {α : Type*} {i : ℕ} {x y z : α} {t : fin i → α} :
  update (vec_cons x (vec_cons y t)) 1 z = vec_cons x (vec_cons z t) :=
begin
  simp only [funext_iff, forall_fin_succ],
  refine ⟨rfl, rfl, λ j, _⟩,
  rw update_noteq,
  { simp only [vec_cons, cons_succ] },
  exact (succ_injective _).ne (fin.succ_ne_zero _),
end

lemma update_cons_two {α : Type*} {i : ℕ} {w x y z : α} {t : fin i → α} :
  update (vec_cons w (vec_cons x (vec_cons y t))) 2 z =
    vec_cons w (vec_cons x (vec_cons z t)) :=
begin
  simp only [funext_iff, forall_fin_succ],
  refine ⟨rfl, rfl, rfl, λ j, _⟩,
  rw update_noteq,
  { simp only [vec_cons, cons_succ] },
  exact (succ_injective _).ne ((succ_injective _).ne (succ_ne_zero _))
end

lemma swap_cons {α : Type*} {i : ℕ} {x y : α} {t : fin i → α} :
  vec_cons x (vec_cons y t) ∘ equiv.swap 0 1 = vec_cons y (vec_cons x t) :=
begin
  rw [funext_iff],
  simp only [forall_fin_succ],
  refine ⟨rfl, rfl, λ j, _⟩,
  simp only [vec_cons, cons_succ, comp_apply],
  rw [equiv.swap_apply_of_ne_of_ne, cons_succ, cons_succ],
  { exact succ_ne_zero _ },
  exact (succ_injective _).ne (succ_ne_zero _)
end

end function
