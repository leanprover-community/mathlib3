/-
Copyright (c) 2021 David Wärn,. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Scott Morrison
-/
import combinatorics.quiver.basic

/-!
# Paths in quivers

Given a quiver `V`, we define the type of paths from `a : V` to `b : V` as an inductive
family. We define composition of paths and the action of prefunctors on paths.
-/

universes v v₁ v₂ u u₁ u₂

namespace quiver

/-- `G.path a b` is the type of paths from `a` to `b` through the arrows of `G`. -/
inductive path {V : Type u} [quiver.{v} V] (a : V) : V → Sort (max (u+1) v)
| nil  : path a
| cons : Π {b c : V}, path b → (b ⟶ c) → path c

/-- An arrow viewed as a path of length one. -/
def hom.to_path {V} [quiver V] {a b : V} (e : a ⟶ b) : path a b :=
path.nil.cons e

namespace path

variables {V : Type u} [quiver V]

/-- The length of a path is the number of arrows it uses. -/
def length {a : V} : Π {b : V}, path a b → ℕ
| _ path.nil        := 0
| _ (path.cons p _) := p.length + 1

instance {a : V} : inhabited (path a a) := ⟨path.nil⟩

@[simp] lemma length_nil {a : V} :
  (path.nil : path a a).length = 0 := rfl

@[simp] lemma length_cons (a b c : V) (p : path a b)
  (e : b ⟶ c) : (p.cons e).length = p.length + 1 := rfl

/-- Composition of paths. -/
def comp {a b : V} : Π {c}, path a b → path b c → path a c
| _ p (path.nil) := p
| _ p (path.cons q e) := (p.comp q).cons e

@[simp] lemma comp_cons {a b c d : V} (p : path a b) (q : path b c) (e : c ⟶ d) :
  p.comp (q.cons e) = (p.comp q).cons e := rfl
@[simp] lemma comp_nil {a b : V} (p : path a b) : p.comp path.nil = p := rfl
@[simp] lemma nil_comp {a : V} : ∀ {b} (p : path a b), path.nil.comp p = p
| a path.nil := rfl
| b (path.cons p e) := by rw [comp_cons, nil_comp]
@[simp] lemma comp_assoc {a b c : V} : ∀ {d}
  (p : path a b) (q : path b c) (r : path c d),
    (p.comp q).comp r = p.comp (q.comp r)
| c p q path.nil := rfl
| d p q (path.cons r e) := by rw [comp_cons, comp_cons, comp_cons, comp_assoc]

end path

end quiver

namespace prefunctor

open quiver

variables {V : Type u₁} [quiver.{v₁} V] {W : Type u₂} [quiver.{v₂} W] (F : prefunctor V W)

/-- The image of a path under a prefunctor. -/
def map_path {a : V} :
  Π {b : V}, path a b → path (F.obj a) (F.obj b)
| _ path.nil := path.nil
| _ (path.cons p e) := path.cons (map_path p) (F.map e)

@[simp] lemma map_path_nil (a : V) : F.map_path (path.nil : path a a) = path.nil := rfl
@[simp] lemma map_path_cons {a b c : V} (p : path a b) (e : b ⟶ c) :
  F.map_path (path.cons p e) = path.cons (F.map_path p) (F.map e) := rfl

@[simp] lemma map_path_comp {a b : V} (p : path a b) :
  ∀ {c : V} (q : path b c), F.map_path (p.comp q) = (F.map_path p).comp (F.map_path q)
| _ path.nil := rfl
| _ (path.cons p e) := begin dsimp, rw [map_path_comp], end

@[simp]
lemma map_path_to_path {a b : V} (f : a ⟶ b) : F.map_path f.to_path = (F.map f).to_path := rfl

end prefunctor
