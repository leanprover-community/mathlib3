/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/
import tactic.nth_rewrite
import data.nat.basic
import data.vector

structure F :=
(a : ℕ)
(v : vector ℕ a)
(p : v.val = [])

example (f : F) : f.v.val = [] :=
begin
  nth_rewrite 0 [f.p],
end

structure cat :=
  (O : Type)
  (H : O → O → Type)
  (i : Π o : O, H o o)
  (c : Π {X Y Z : O} (f : H X Y) (g : H Y Z), H X Z)
  (li : Π {X Y : O} (f : H X Y), c (i X) f = f)
  (ri : Π {X Y : O} (f : H X Y), c f (i Y) = f)
  (a : Π {W X Y Z : O} (f : H W X) (g : H X Y) (h : H Y Z), c (c f g) h = c f (c g h))

open tactic

example (C : cat) (W X Y Z : C.O) (f : C.H X Y) (g : C.H W X) (h k : C.H Y Z) :
  C.c (C.c g f) h = C.c g (C.c f h) :=
begin
  nth_rewrite 0 [C.a],
end

example (C : cat) (X Y : C.O) (f : C.H X Y) : C.c f (C.i Y) = f :=
begin
  nth_rewrite 0 [C.ri],
end

-- The next two examples fail when using the kabstract backend.

axiom foo : [1] = [2]

example : [[1], [1], [1]] = [[1], [2], [1]] :=
begin
  nth_rewrite_lhs 1 [foo],
end

axiom foo' : [6] = [7]
axiom bar' : [[5],[5]] = [[6],[6]]

example : [[7],[6]] = [[5],[5]] :=
begin
  nth_rewrite_lhs 0 foo',
  nth_rewrite_rhs 0 bar',
  nth_rewrite_lhs 0 ←foo',
  nth_rewrite_lhs 0 ←foo',
end

axiom wowzer : (3, 3) = (5, 2)
axiom kachow (n : ℕ) : (4, n) = (5, n)
axiom pchew (n : ℕ) : (n, 5) = (5, n)
axiom smash (n m : ℕ) : (n, m) = (1, 1)

example : [(3, 3), (5, 9), (5, 9)] = [(4, 5), (3, 6), (1, 1)] :=
begin
  nth_rewrite_lhs 0 wowzer,
  nth_rewrite_lhs 2 ←pchew,
  nth_rewrite_rhs 0 pchew,

  nth_rewrite_rhs 0 smash,
  nth_rewrite_rhs 1 smash,
  nth_rewrite_rhs 2 smash,
  nth_rewrite_lhs 0 smash,
  nth_rewrite_lhs 1 smash,
  nth_rewrite_lhs 2 smash,
end

example (a b c : ℕ) : c + a + b = a + c + b :=
begin
  nth_rewrite_rhs 1 add_comm,
end
-- With the `kabstract` backend, we only find one rewrite, even though there are obviously two.
-- The problem is that `(a + b) + c` matches directly, so the WHOLE THING gets replaced with a
-- metavariable, per the `kabstract` strategy. This is devastating to the search, since we cannot
-- see inside this metavariable.

-- I still think it's fixable. Because all applications have an order, I'm pretty sure we can't
-- miss any rewrites if we also look inside every thing we chunk-up into a metavariable as well.
-- In almost every case this will bring up no results (with the exception of situations like this
-- one), so there should be essentially no change in complexity.

example (x y : Prop) (h₁ : x ↔ y) (h₂ : x ↔ x ∧ x) : x ∧ x ↔ x :=
begin
  nth_rewrite_rhs 1 [h₁] at h₂,
  nth_rewrite_rhs 0 [← h₁] at h₂,
  nth_rewrite_rhs 0 h₂,
end

example (x y : ℕ) (h₁ : x = y) (h₂ : x = x + x) : x + x = x :=
begin
  nth_rewrite_rhs 1 [h₁] at h₂,
  nth_rewrite_rhs 0 [← h₁] at h₂,
  nth_rewrite_rhs 0 h₂,
end

example (x y z : ℕ) (h1 : x = y) (h2 : y = z) :
  x + x + x + y = y + y + x + x :=
begin
  nth_rewrite 2 [h1, h2], -- h2 is not used
  nth_rewrite 2 [h2],
  repeat { rw h1 },
  repeat { rw h2 },
end
