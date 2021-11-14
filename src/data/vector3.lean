/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fin.fin2
import tactic.localized

/-!
# Alternate definition of `vector` in terms of `fin2`

This file provides a locale `vector3` which overrides `[a, b, c]` notation to create `vector3` not
`list`.

The `::` notation is overloaded by this file to mean `vector3.cons`.
-/

universes u

open fin2 nat

/-- Alternate definition of `vector` based on `fin2`. -/
def vector3 (α : Type u) (n : ℕ) : Type u := fin2 n → α

namespace vector3

/-- The empty vector -/
@[pattern] def nil {α} : vector3 α 0.

/-- The vector cons operation -/
@[pattern] def cons {α} {n} (a : α) (v : vector3 α n) : vector3 α (succ n) :=
λi, by {refine i.cases' _ _, exact a, exact v}

/- We do not want to make the following notation global, because then these expressions will be
overloaded, and only the expected type will be able to disambiguate the meaning. Worse: Lean will
try to insert a coercion from `vector3 α _` to `list α`, if a list is expected. -/
localized "notation `[` l:(foldr `, ` (h t, vector3.cons h t) nil `]`) := l" in vector3
notation a :: b := cons a b

@[simp] theorem cons_fz {α} {n} (a : α) (v : vector3 α n) : (a :: v) fz = a := rfl
@[simp] theorem cons_fs {α} {n} (a : α) (v : vector3 α n) (i) : (a :: v) (fs i) = v i := rfl

/-- Get the `i`th element of a vector -/
@[reducible] def nth {α} {n} (i : fin2 n) (v : vector3 α n) : α := v i

/-- Construct a vector from a function on `fin2`. -/
@[reducible] def of_fn {α} {n} (f : fin2 n → α) : vector3 α n := f

/-- Get the head of a nonempty vector. -/
def head {α} {n} (v : vector3 α (succ n)) : α := v fz

/-- Get the tail of a nonempty vector. -/
def tail {α} {n} (v : vector3 α (succ n)) : vector3 α n := λi, v (fs i)

theorem eq_nil {α} (v : vector3 α 0) : v = [] :=
funext $ λi, match i with end

theorem cons_head_tail {α} {n} (v : vector3 α (succ n)) : head v :: tail v = v :=
funext $ λi, fin2.cases' rfl (λ_, rfl) i

def nil_elim {α} {C : vector3 α 0 → Sort u} (H : C []) (v : vector3 α 0) : C v :=
by rw eq_nil v; apply H

def cons_elim {α n} {C : vector3 α (succ n) → Sort u} (H : Π (a : α) (t : vector3 α n), C (a :: t))
  (v : vector3 α (succ n)) : C v :=
by rw ← (cons_head_tail v); apply H

@[simp] theorem cons_elim_cons {α n C H a t} : @cons_elim α n C H (a :: t) = H a t := rfl

@[elab_as_eliminator]
protected def rec_on {α} {C : Π {n}, vector3 α n → Sort u} {n} (v : vector3 α n)
  (H0 : C [])
  (Hs : Π {n} (a) (w : vector3 α n), C w → C (a :: w)) : C v :=
nat.rec_on n
  (λv, v.nil_elim H0)
  (λn IH v, v.cons_elim (λa t, Hs _ _ (IH _))) v

@[simp] theorem rec_on_nil {α C H0 Hs} : @vector3.rec_on α @C 0 [] H0 @Hs = H0 :=
rfl

@[simp] theorem rec_on_cons {α C H0 Hs n a v} :
  @vector3.rec_on α @C (succ n) (a :: v) H0 @Hs = Hs a v (@vector3.rec_on α @C n v H0 @Hs) :=
rfl

/-- Append two vectors -/
def append {α} {m} (v : vector3 α m) {n} (w : vector3 α n) : vector3 α (n+m) :=
nat.rec_on m (λ_, w) (λm IH v, v.cons_elim $ λa t, @fin2.cases' (n+m) (λ_, α) a (IH t)) v

local infix ` +-+ `:65 := vector3.append

@[simp] theorem append_nil {α} {n} (w : vector3 α n) : [] +-+ w = w := rfl

@[simp] theorem append_cons {α} (a : α) {m} (v : vector3 α m) {n} (w : vector3 α n) :
  (a::v) +-+ w = a :: (v +-+ w) := rfl

@[simp] theorem append_left {α} : ∀ {m} (i : fin2 m) (v : vector3 α m) {n} (w : vector3 α n),
  (v +-+ w) (left n i) = v i
| ._ (@fz m)   v n w := v.cons_elim (λa t, by simp [*, left])
| ._ (@fs m i) v n w := v.cons_elim (λa t, by simp [*, left])

@[simp] theorem append_add {α} : ∀ {m} (v : vector3 α m) {n} (w : vector3 α n) (i : fin2 n),
  (v +-+ w) (add i m) = w i
| 0        v n w i := rfl
| (succ m) v n w i := v.cons_elim (λa t, by simp [*, add])

/-- Insert `a` into `v` at index `i`. -/
def insert {α} (a : α) {n} (v : vector3 α n) (i : fin2 (succ n)) : vector3 α (succ n) :=
λj, (a :: v) (insert_perm i j)

@[simp] theorem insert_fz {α} (a : α) {n} (v : vector3 α n) : insert a v fz = a :: v :=
by refine funext (λj, j.cases' _ _); intros; refl

@[simp] theorem insert_fs {α} (a : α) {n} (b : α) (v : vector3 α n) (i : fin2 (succ n)) :
  insert a (b :: v) (fs i) = b :: insert a v i :=
funext $ λj, by {
  refine j.cases' _ (λj, _); simp [insert, insert_perm],
  refine fin2.cases' _ _ (insert_perm i j); simp [insert_perm] }

theorem append_insert {α} (a : α) {k} (t : vector3 α k) {n} (v : vector3 α n) (i : fin2 (succ n))
  (e : succ n + k = succ (n + k)) :
  insert a (t +-+ v) (eq.rec_on e (i.add k)) = eq.rec_on e (t +-+ insert a v i) :=
begin
  refine vector3.rec_on t (λe, _) (λk b t IH e, _) e, refl,
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

/-- "Curried" exists, i.e. ∃ x1 ... xn, f [x1, ..., xn] -/
def vector_ex {α} : Π k, (vector3 α k → Prop) → Prop
| 0        f := f []
| (succ k) f := ∃x : α, vector_ex k (λv, f (x :: v))

/-- "Curried" forall, i.e. ∀ x1 ... xn, f [x1, ..., xn] -/
def vector_all {α} : Π k, (vector3 α k → Prop) → Prop
| 0        f := f []
| (succ k) f := ∀x : α, vector_all k (λv, f (x :: v))

theorem exists_vector_zero {α} (f : vector3 α 0 → Prop) : Exists f ↔ f [] :=
⟨λ⟨v, fv⟩, by rw ← (eq_nil v); exact fv, λf0, ⟨[], f0⟩⟩

theorem exists_vector_succ {α n} (f : vector3 α (succ n) → Prop) : Exists f ↔ ∃x v, f (x :: v) :=
⟨λ⟨v, fv⟩, ⟨_, _, by rw cons_head_tail v; exact fv⟩, λ⟨x, v, fxv⟩, ⟨_, fxv⟩⟩

theorem vector_ex_iff_exists {α} : ∀ {n} (f : vector3 α n → Prop), vector_ex n f ↔ Exists f
| 0        f := (exists_vector_zero f).symm
| (succ n) f := iff.trans (exists_congr (λx, vector_ex_iff_exists _)) (exists_vector_succ f).symm

theorem vector_all_iff_forall {α} : ∀ {n} (f : vector3 α n → Prop), vector_all n f ↔ ∀ v, f v
| 0        f := ⟨λf0 v, v.nil_elim f0, λal, al []⟩
| (succ n) f := (forall_congr (λx, vector_all_iff_forall (λv, f (x :: v)))).trans
  ⟨λal v, v.cons_elim al, λal x v, al (x::v)⟩

/-- `vector_allp p v` is equivalent to `∀ i, p (v i)`, but unfolds directly to a conjunction,
  i.e. `vector_allp p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
def vector_allp {α} (p : α → Prop) {n} (v : vector3 α n) : Prop :=
vector3.rec_on v true (λn a v IH, @vector3.rec_on _ (λn v, Prop) _ v (p a) (λn b v' _, p a ∧ IH))

@[simp] theorem vector_allp_nil {α} (p : α → Prop) : vector_allp p [] = true := rfl
@[simp] theorem vector_allp_singleton {α} (p : α → Prop) (x : α) : vector_allp p [x] = p x := rfl
@[simp] theorem vector_allp_cons {α} (p : α → Prop) {n} (x : α) (v : vector3 α n) :
  vector_allp p (x :: v) ↔ p x ∧ vector_allp p v :=
vector3.rec_on v (and_true _).symm (λn a v IH, iff.rfl)

theorem vector_allp_iff_forall {α} (p : α → Prop) {n} (v : vector3 α n) :
  vector_allp p v ↔ ∀ i, p (v i) :=
begin refine v.rec_on _ _,
  { exact ⟨λ_, fin2.elim0, λ_, trivial⟩ },
  { simp, refine λn a v IH, (and_congr_right (λ_, IH)).trans
      ⟨λ⟨pa, h⟩ i, by {refine i.cases' _ _, exacts [pa, h]}, λh, ⟨_, λi, _⟩⟩,
    { have h0 := h fz, simp at h0, exact h0 },
    { have hs := h (fs i), simp at hs, exact hs } }
end

theorem vector_allp.imp {α} {p q : α → Prop} (h : ∀ x, p x → q x)
  {n} {v : vector3 α n} (al : vector_allp p v) : vector_allp q v :=
(vector_allp_iff_forall _ _).2 (λi, h _ $ (vector_allp_iff_forall _ _).1 al _)

end vector3
