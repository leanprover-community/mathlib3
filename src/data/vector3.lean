/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fin.fin2
import tactic.localized

/-!
# Alternate definition of `vector` in terms of `fin2`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides a locale `vector3` which overrides the `[a, b, c]` notation to create a `vector3`
instead of a `list`.

The `::` notation is also overloaded by this file to mean `vector3.cons`.
-/

open fin2 nat

universes u
variables {α : Type*} {m n : ℕ}

/-- Alternate definition of `vector` based on `fin2`. -/
def vector3 (α : Type u) (n : ℕ) : Type u := fin2 n → α

instance [inhabited α] : inhabited (vector3 α n) := pi.inhabited _

namespace vector3

/-- The empty vector -/
@[pattern] def nil : vector3 α 0.

/-- The vector cons operation -/
@[pattern] def cons (a : α) (v : vector3 α n) : vector3 α (succ n) :=
λ i, by { refine i.cases' _ _, exact a, exact v }

/- We do not want to make the following notation global, because then these expressions will be
overloaded, and only the expected type will be able to disambiguate the meaning. Worse: Lean will
try to insert a coercion from `vector3 α _` to `list α`, if a list is expected. -/
localized "notation (name := vector.list)
  `[` l:(foldr `, ` (h t, vector3.cons h t) vector3.nil `]`) := l" in vector3
notation (name := vector.cons) a :: b := cons a b

@[simp] lemma cons_fz (a : α) (v : vector3 α n) : (a :: v) fz = a := rfl
@[simp] lemma cons_fs (a : α) (v : vector3 α n) (i) : (a :: v) (fs i) = v i := rfl

/-- Get the `i`th element of a vector -/
@[reducible] def nth (i : fin2 n) (v : vector3 α n) : α := v i

/-- Construct a vector from a function on `fin2`. -/
@[reducible] def of_fn (f : fin2 n → α) : vector3 α n := f

/-- Get the head of a nonempty vector. -/
def head (v : vector3 α (succ n)) : α := v fz

/-- Get the tail of a nonempty vector. -/
def tail (v : vector3 α (succ n)) : vector3 α n := λ i, v (fs i)

lemma eq_nil (v : vector3 α 0) : v = [] := funext $ λ i, match i with end

lemma cons_head_tail (v : vector3 α (succ n)) : head v :: tail v = v :=
funext $ λ i, fin2.cases' rfl (λ _, rfl) i

/-- Eliminator for an empty vector. -/
def nil_elim {C : vector3 α 0 → Sort u} (H : C []) (v : vector3 α 0) : C v :=
by rw eq_nil v; apply H

/-- Recursion principle for a nonempty vector. -/
def cons_elim {C : vector3 α (succ n) → Sort u} (H : Π (a : α) (t : vector3 α n), C (a :: t))
  (v : vector3 α (succ n)) : C v :=
by rw ← (cons_head_tail v); apply H

@[simp] lemma cons_elim_cons {C H a t} : @cons_elim α n C H (a :: t) = H a t := rfl

/-- Recursion principle with the vector as first argument. -/
@[elab_as_eliminator]
protected def rec_on {C : Π {n}, vector3 α n → Sort u} {n} (v : vector3 α n)
  (H0 : C [])
  (Hs : Π {n} (a) (w : vector3 α n), C w → C (a :: w)) : C v :=
nat.rec_on n
  (λ v, v.nil_elim H0)
  (λ n IH v, v.cons_elim (λ a t, Hs _ _ (IH _))) v

@[simp] lemma rec_on_nil {C H0 Hs} : @vector3.rec_on α @C 0 [] H0 @Hs = H0 := rfl

@[simp] lemma rec_on_cons {C H0 Hs n a v} :
  @vector3.rec_on α @C (succ n) (a :: v) H0 @Hs = Hs a v (@vector3.rec_on α @C n v H0 @Hs) :=
rfl

/-- Append two vectors -/
def append (v : vector3 α m) (w : vector3 α n) : vector3 α (n+m) :=
nat.rec_on m (λ _, w) (λ m IH v, v.cons_elim $ λ a t, @fin2.cases' (n+m) (λ _, α) a (IH t)) v

local infix ` +-+ `:65 := vector3.append

@[simp] lemma append_nil (w : vector3 α n) : [] +-+ w = w := rfl

@[simp] lemma append_cons (a : α) (v : vector3 α m) (w : vector3 α n) :
  (a :: v) +-+ w = a :: (v +-+ w) := rfl

@[simp] lemma append_left : ∀ {m} (i : fin2 m) (v : vector3 α m) {n} (w : vector3 α n),
  (v +-+ w) (left n i) = v i
| ._ (@fz m)   v n w := v.cons_elim (λ a t, by simp [*, left])
| ._ (@fs m i) v n w := v.cons_elim (λ a t, by simp [*, left])

@[simp] lemma append_add : ∀ {m} (v : vector3 α m) {n} (w : vector3 α n) (i : fin2 n),
  (v +-+ w) (add i m) = w i
| 0        v n w i := rfl
| (succ m) v n w i := v.cons_elim (λ a t, by simp [*, add])

/-- Insert `a` into `v` at index `i`. -/
def insert (a : α) (v : vector3 α n) (i : fin2 (succ n)) : vector3 α (succ n) :=
λ j, (a :: v) (insert_perm i j)

@[simp] lemma insert_fz (a : α) (v : vector3 α n) : insert a v fz = a :: v :=
by refine funext (λ j, j.cases' _ _); intros; refl

@[simp] lemma insert_fs (a : α) (b : α) (v : vector3 α n) (i : fin2 (succ n)) :
  insert a (b :: v) (fs i) = b :: insert a v i :=
funext $ λ j, by
{ refine j.cases' _ (λ j, _); simp [insert, insert_perm],
  refine fin2.cases' _ _ (insert_perm i j); simp [insert_perm] }

lemma append_insert (a : α) (t : vector3 α m) (v : vector3 α n) (i : fin2 (succ n))
  (e : succ n + m = succ (n + m)) :
  insert a (t +-+ v) (eq.rec_on e (i.add m)) = eq.rec_on e (t +-+ insert a v i) :=
begin
  refine vector3.rec_on t (λ e, _) (λ k b t IH e, _) e, refl,
  have e' := succ_add n k,
  change insert a (b :: (t +-+ v)) (eq.rec_on (congr_arg succ e') (fs (add i k)))
    = eq.rec_on (congr_arg succ e') (b :: (t +-+ insert a v i)),
  rw ← (eq.drec_on e' rfl : fs (eq.rec_on e' (i.add k) : fin2 (succ (n + k))) = eq.rec_on
    (congr_arg succ e') (fs (i.add k))),
  simp, rw IH, exact eq.drec_on e' rfl
end

end vector3

section vector3
open vector3
open_locale vector3

/-- "Curried" exists, i.e. `∃ x₁ ... xₙ, f [x₁, ..., xₙ]`. -/
def vector_ex : Π k, (vector3 α k → Prop) → Prop
| 0        f := f []
| (succ k) f := ∃x : α, vector_ex k (λ v, f (x :: v))

/-- "Curried" forall, i.e. `∀ x₁ ... xₙ, f [x₁, ..., xₙ]`. -/
def vector_all : Π k, (vector3 α k → Prop) → Prop
| 0        f := f []
| (succ k) f := ∀ x : α, vector_all k (λ v, f (x :: v))

lemma exists_vector_zero (f : vector3 α 0 → Prop) : Exists f ↔ f [] :=
⟨λ ⟨v, fv⟩, by rw ← (eq_nil v); exact fv, λ f0, ⟨[], f0⟩⟩

lemma exists_vector_succ (f : vector3 α (succ n) → Prop) : Exists f ↔ ∃x v, f (x :: v) :=
⟨λ ⟨v, fv⟩, ⟨_, _, by rw cons_head_tail v; exact fv⟩, λ ⟨x, v, fxv⟩, ⟨_, fxv⟩⟩

lemma vector_ex_iff_exists : ∀ {n} (f : vector3 α n → Prop), vector_ex n f ↔ Exists f
| 0        f := (exists_vector_zero f).symm
| (succ n) f := iff.trans (exists_congr (λ x, vector_ex_iff_exists _)) (exists_vector_succ f).symm

lemma vector_all_iff_forall : ∀ {n} (f : vector3 α n → Prop), vector_all n f ↔ ∀ v, f v
| 0        f := ⟨λ f0 v, v.nil_elim f0, λ al, al []⟩
| (succ n) f := (forall_congr (λ x, vector_all_iff_forall (λ v, f (x :: v)))).trans
  ⟨λ al v, v.cons_elim al, λ al x v, al (x :: v)⟩

/-- `vector_allp p v` is equivalent to `∀ i, p (v i)`, but unfolds directly to a conjunction,
  i.e. `vector_allp p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
def vector_allp (p : α → Prop) (v : vector3 α n) : Prop :=
vector3.rec_on v true (λ n a v IH, @vector3.rec_on _ (λ n v, Prop) _ v (p a) (λ n b v' _, p a ∧ IH))

@[simp] lemma vector_allp_nil (p : α → Prop) : vector_allp p [] = true := rfl
@[simp] lemma vector_allp_singleton (p : α → Prop) (x : α) : vector_allp p [x] = p x := rfl
@[simp] lemma vector_allp_cons (p : α → Prop) (x : α) (v : vector3 α n) :
  vector_allp p (x :: v) ↔ p x ∧ vector_allp p v :=
vector3.rec_on v (and_true _).symm (λ n a v IH, iff.rfl)

lemma vector_allp_iff_forall (p : α → Prop) (v : vector3 α n) : vector_allp p v ↔ ∀ i, p (v i) :=
begin
  refine v.rec_on _ _,
  { exact ⟨λ _, fin2.elim0, λ _, trivial⟩ },
  { simp, refine λ n a v IH, (and_congr_right (λ _, IH)).trans
      ⟨λ ⟨pa, h⟩ i, by {refine i.cases' _ _, exacts [pa, h]}, λ h, ⟨_, λ i, _⟩⟩,
    { have h0 := h fz, simp at h0, exact h0 },
    { have hs := h (fs i), simp at hs, exact hs } }
end

lemma vector_allp.imp {p q : α → Prop} (h : ∀ x, p x → q x) {v : vector3 α n}
  (al : vector_allp p v) : vector_allp q v :=
(vector_allp_iff_forall _ _).2 (λ i, h _ $ (vector_allp_iff_forall _ _).1 al _)

end vector3
