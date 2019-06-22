-- Copyright (c) 2018 Keeley Hoek. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Keeley Hoek, Scott Morrison
import tactic.rewrite_search

open tactic.rewrite_search.strategy
open tactic.rewrite_search.metric
open tactic.rewrite_search.tracer

namespace tactic.rewrite_search.testing

axiom foo' : [6] = [7]
axiom bar' : [[5],[5]] = [[6],[6]]

example : [[7],[6]] = [[5],[5]] :=
begin
 success_if_fail { rewrite_search_with [] },
-- rw [←foo', bar']
 rewrite_search_with [←foo', bar'] {explain := tt},
end

@[search] private axiom foo : [0] = [1]
@[search] private axiom bar1 : [1] = [2]
@[search] private axiom bar2 : [3] = [2]
@[search] private axiom bar3 : [3] = [4]

private example (a : unit) : [[0],[0]] = [[4],[4]] :=
begin
/- `rewrite_search` says -/
-- nth_rewrite_lhs 0 foo,
-- nth_rewrite_lhs 0 bar1,
-- nth_rewrite_lhs 0 foo,
-- nth_rewrite_lhs 0 bar1,
-- nth_rewrite_rhs 0 ←bar3,
-- nth_rewrite_rhs 0 ←bar3,
-- nth_rewrite_rhs 1 bar2,
-- nth_rewrite_rhs 0 bar2,

/- `rewrite_search` says -/
conv { to_lhs, congr, skip, rw foo, },
conv { to_lhs, congr, skip, rw bar1, },
conv { to_lhs, congr, },
-- conv { to_lhs, (*→func→arg→func) congr, congr, skip, congr, rw bar1, },
-- conv { to_rhs, (*→arg→func) congr, skip, congr, rw ←bar3, },
-- conv { to_rhs, (*→func→arg→func) congr, congr, skip, congr, rw ←bar3, },
-- conv { to_rhs, (*→func→arg→func) congr, congr, skip, congr, rw bar2, },
-- conv { to_rhs, (*→arg→func) congr, skip, congr, rw bar2, }

  rewrite_search_with [foo, bar1, ← bar2, bar2, ← bar3] {explain := tt},
end

private example (a : unit) : [[0],[0]] = [[4],[4]] :=
begin
  rewrite_search_with [foo, bar1, ← bar2, bar2, ← bar3]
    { strategy := pexplore {}, metric := edit_distance },
end

private example : [[0],[0]] = [[4],[4]] :=
begin
/- `rewrite_search` says -/
-- nth_rewrite_lhs 0 foo,
-- nth_rewrite_lhs 0 bar1,
-- nth_rewrite_lhs 0 ←bar2,
-- nth_rewrite_lhs 0 foo,
-- nth_rewrite_rhs 0 ←bar3,
-- nth_rewrite_rhs 0 ←bar3,
-- nth_rewrite_rhs 1 bar2,
-- nth_rewrite_rhs 0 ←bar1

/- `rewrite_search` says -/
-- conv { to_lhs, congr, rw [foo, bar1], skip, rw [foo, bar1] },
-- conv { to_rhs, congr, rw [←bar3, bar2], skip, rw [←bar3, bar2] },

  rewrite_search { metric := edit_distance, strategy := pexplore, }
end

@[search] private axiom qux' : [[1], [2]] = [[6], [7]]
@[search] private axiom qux'' : [6] = [7]
private example : [[1], [1]] = [[7], [7]] :=
begin
-- nth_rewrite_lhs 0 bar1,
-- nth_rewrite_lhs 0 qux',
-- nth_rewrite_rhs 1 ←qux'',
  rewrite_search { view := unit_tracer },
end

private example : [[0],[0]] = [[4],[4]] :=
begin
-- nth_rewrite_lhs 0 foo,
-- nth_rewrite_lhs 0 bar1,
-- nth_rewrite_lhs 0 ←bar2,
-- nth_rewrite_lhs 0 bar3,
-- nth_rewrite_lhs 0 foo,
-- nth_rewrite_lhs 0 bar1,
-- nth_rewrite_rhs 1 ←bar3,
-- nth_rewrite_rhs 0 bar2,
  rewrite_search { explain := ff },
end

private structure cat :=
  (O : Type)
  (H : O → O → Type)
  (i : Π o : O, H o o)
  (c : Π {X Y Z : O} (f : H X Y) (g : H Y Z), H X Z)
  (li : Π {X Y : O} (f : H X Y), c (i X) f = f)
  (ri : Π {X Y : O} (f : H X Y), c f (i Y) = f)
  (a : Π {W X Y Z : O} (f : H W X) (g : H X Y) (h : H Y Z), c (c f g) h = c f (c g h))

attribute [search] cat.li cat.a

private example (C : cat) (X Y Z : C.O) (f : C.H X Y) (g : C.H Y X) (w : C.c g f = C.i Y) (h k : C.H Y Z) (p : C.c f h = C.c f k) : h = k :=
begin
-- rewrite_search_using `search {trace := tt, trace_rules:=tt}, -- not quite there, we haven't activated intense search
perform_nth_rewrite 0 [← @cat.li C Y Z h],
perform_nth_rewrite 0 [← w],
perform_nth_rewrite 0 [C.a],
perform_nth_rewrite 0 [p],
perform_nth_rewrite 0 [← C.a],
perform_nth_rewrite 0 [w],
perform_nth_rewrite 0 [@cat.li C Y Z k],
-- PROJECT automate this!
-- rw [← C.li Y Z h],
-- rw [← C.li Y Z k],
-- rw [← w],
-- rw [C.a],
-- rw [C.a],
-- rw [p],
end

end tactic.rewrite_search.testing

namespace tactic.rewrite_search.examples

constants f g : ℕ → ℕ → ℕ → ℕ
@[search] axiom f_0_0 : ∀ a b c : ℕ, f a b c = f 0 b c
@[search] axiom f_0_1 : ∀ a b c : ℕ, f a b c = f 1 b c
@[search] axiom f_0_2 : ∀ a b c : ℕ, f a b c = f 2 b c
@[search] axiom f_1_0 : ∀ a b c : ℕ, f a b c = f a 0 c
@[search] axiom f_1_1 : ∀ a b c : ℕ, f a b c = f a 1 c
@[search] axiom f_1_2 : ∀ a b c : ℕ, f a b c = f a 2 c
@[search] axiom f_2_0 : ∀ a b c : ℕ, f a b c = f a b 0
@[search] axiom f_2_1 : ∀ a b c : ℕ, f a b c = f a b 1
@[search] axiom f_2_2 : ∀ a b c : ℕ, f a b c = f a b 2
@[search] axiom g_0_0 : ∀ a b c : ℕ, g a b c = g 0 b c
@[search] axiom g_0_1 : ∀ a b c : ℕ, g a b c = g 1 b c
@[search] axiom g_0_2 : ∀ a b c : ℕ, g a b c = g 2 b c
@[search] axiom g_1_0 : ∀ a b c : ℕ, g a b c = g a 0 c
@[search] axiom g_1_1 : ∀ a b c : ℕ, g a b c = g a 1 c
@[search] axiom g_1_2 : ∀ a b c : ℕ, g a b c = g a 2 c
@[search] axiom g_2_0 : ∀ a b c : ℕ, g a b c = g a b 0
@[search] axiom g_2_1 : ∀ a b c : ℕ, g a b c = g a b 1
@[search] axiom g_2_2 : ∀ a b c : ℕ, g a b c = g a b 2
@[search] axiom f_g : f 0 1 2 = g 2 0 1

set_option trace.app_builder true

lemma test : f 0 0 0 = g 0 0 0 :=
-- by erw [f_2_2, f_1_1, g_0_2, g_2_1, ←f_g]
by rewrite_search {trace := ff, explain := tt, trace_summary := tt, exhaustive := tt, view := unit_tracer, strategy := pexplore {pop_size := 1}, metric := edit_distance {refresh_freq := 5} weight.cm}
-- begin
-- perform_nth_rewrite [f_2_2] 0,
-- perform_nth_rewrite [f_1_1] 0,
-- perform_nth_rewrite [g_0_2] 0,
-- perform_nth_rewrite [g_2_1] 0,
-- perform_nth_rewrite [← f_g] 0,
-- end


lemma test_bfs : f 0 0 0 = g 0 0 0 :=
-- by erw [f_2_2, f_1_1, g_0_2, g_2_1, ←f_g]
by rewrite_search {trace := ff, explain := tt, trace_summary := tt, exhaustive := tt, strategy := pexplore {pop_size:=5}, metric := edit_distance {} weight.cm }

-- Compare: in these next two we just change pop_size 1 -> 5, and we find a much much
-- better proof, but we see a little more stuff.

-- lemma test_svm : f 0 0 0 = g 0 0 0 :=
-- -- by erw [f_2_2, f_1_1, g_0_2, g_2_1, ←f_g]
-- by rewrite_search {trace := ff, explain := tt, trace_summary := tt, exhaustive := tt, strategy := pexplore {pop_size := 1}, metric := edit_distance {refresh_freq := 1} weight.svm}

-- lemma test_svm2 : f 0 0 0 = g 0 0 0 :=
-- -- by erw [f_2_2, f_1_1, g_0_2, g_2_1, ←f_g]
-- by rewrite_search {trace := ff, explain := tt, trace_summary := tt, exhaustive := tt, strategy := pexplore {pop_size := 5}, metric := edit_distance {refresh_freq := 1} weight.svm}

lemma test_cm2 : f 0 0 0 = g 0 0 0 :=
-- by erw [f_2_2, f_1_1, g_0_2, g_2_1, ←f_g]
by rewrite_search {trace := ff, explain := tt, trace_summary := tt, exhaustive := tt, strategy := pexplore {pop_size := 5}, metric := edit_distance {refresh_freq := 1} weight.cm}

constant h : ℕ → ℕ
@[search,simp] axiom a1 : h 0 = h 1
@[search,simp] axiom a2 : h 1 = h 2
@[search,simp] axiom a3 : h 2 = h 3
@[search,simp] axiom a4 : h 3 = h 4

lemma test2 : h 0 = h 4 :=
-- by erw [a1, a2, ←a4, ←a3]
by rewrite_search

constants a b c d e : ℚ

lemma test3 : (a * (b + c)) * d = a * (b * d) + a * (c * d) :=
by rewrite_search_with [add_comm, add_assoc, mul_assoc, mul_comm, left_distrib, right_distrib] {explain := tt, trace_summary := tt, metric := edit_distance {}}

-- lemma test4 : (a * (b + c + 1)) * d = a * (b * d) + a * (1 * d) + a * (c * d) :=
-- by rewrite_search_with [add_comm, add_assoc, mul_one, mul_assoc, mul_comm, left_distrib, right_distrib] {explain := tt, trace_summary := tt, view := visualiser, metric := edit_distance {refresh_freq := 10} cm, strategy := pexplore {pop_size := 3}, max_iterations := 1000}

namespace tactic.rewrite_search.tesseract

constants f_1 f_2 f_3 f_4 f_5 : ℕ -> ℕ -> ℕ ->  ℕ
@[search] axiom f_1_1_1: forall n1 n2 n3  : ℕ, f_1 n1 n2 n3  = f_1 1 n2 n3
@[search] axiom f_2_1_1: forall n1 n2 n3  : ℕ, f_2 n1 n2 n3  = f_2 1 n2 n3
@[search] axiom f_3_1_1: forall n1 n2 n3  : ℕ, f_3 n1 n2 n3  = f_3 1 n2 n3
@[search] axiom f_4_1_1: forall n1 n2 n3  : ℕ, f_4 n1 n2 n3  = f_4 1 n2 n3
@[search] axiom f_5_1_1: forall n1 n2 n3  : ℕ, f_5 n1 n2 n3  = f_5 1 n2 n3
@[search] axiom f_1_1_2: forall n1 n2 n3  : ℕ, f_1 n1 n2 n3  = f_1 2 n2 n3
@[search] axiom f_2_1_2: forall n1 n2 n3  : ℕ, f_2 n1 n2 n3  = f_2 2 n2 n3
@[search] axiom f_3_1_2: forall n1 n2 n3  : ℕ, f_3 n1 n2 n3  = f_3 2 n2 n3
@[search] axiom f_4_1_2: forall n1 n2 n3  : ℕ, f_4 n1 n2 n3  = f_4 2 n2 n3
@[search] axiom f_5_1_2: forall n1 n2 n3  : ℕ, f_5 n1 n2 n3  = f_5 2 n2 n3
@[search] axiom f_1_1_3: forall n1 n2 n3  : ℕ, f_1 n1 n2 n3  = f_1 3 n2 n3
@[search] axiom f_2_1_3: forall n1 n2 n3  : ℕ, f_2 n1 n2 n3  = f_2 3 n2 n3
@[search] axiom f_3_1_3: forall n1 n2 n3  : ℕ, f_3 n1 n2 n3  = f_3 3 n2 n3
@[search] axiom f_4_1_3: forall n1 n2 n3  : ℕ, f_4 n1 n2 n3  = f_4 3 n2 n3
@[search] axiom f_5_1_3: forall n1 n2 n3  : ℕ, f_5 n1 n2 n3  = f_5 3 n2 n3
@[search] axiom f_1_2_1: forall n1 n2 n3  : ℕ, f_1 n1 n2 n3  = f_1 n1 1 n3
@[search] axiom f_2_2_1: forall n1 n2 n3  : ℕ, f_2 n1 n2 n3  = f_2 n1 1 n3
@[search] axiom f_3_2_1: forall n1 n2 n3  : ℕ, f_3 n1 n2 n3  = f_3 n1 1 n3
@[search] axiom f_4_2_1: forall n1 n2 n3  : ℕ, f_4 n1 n2 n3  = f_4 n1 1 n3
@[search] axiom f_5_2_1: forall n1 n2 n3  : ℕ, f_5 n1 n2 n3  = f_5 n1 1 n3
@[search] axiom f_1_2_2: forall n1 n2 n3  : ℕ, f_1 n1 n2 n3  = f_1 n1 2 n3
@[search] axiom f_2_2_2: forall n1 n2 n3  : ℕ, f_2 n1 n2 n3  = f_2 n1 2 n3
@[search] axiom f_3_2_2: forall n1 n2 n3  : ℕ, f_3 n1 n2 n3  = f_3 n1 2 n3
@[search] axiom f_4_2_2: forall n1 n2 n3  : ℕ, f_4 n1 n2 n3  = f_4 n1 2 n3
@[search] axiom f_5_2_2: forall n1 n2 n3  : ℕ, f_5 n1 n2 n3  = f_5 n1 2 n3
@[search] axiom f_1_2_3: forall n1 n2 n3  : ℕ, f_1 n1 n2 n3  = f_1 n1 3 n3
@[search] axiom f_2_2_3: forall n1 n2 n3  : ℕ, f_2 n1 n2 n3  = f_2 n1 3 n3
@[search] axiom f_3_2_3: forall n1 n2 n3  : ℕ, f_3 n1 n2 n3  = f_3 n1 3 n3
@[search] axiom f_4_2_3: forall n1 n2 n3  : ℕ, f_4 n1 n2 n3  = f_4 n1 3 n3
@[search] axiom f_5_2_3: forall n1 n2 n3  : ℕ, f_5 n1 n2 n3  = f_5 n1 3 n3
@[search] axiom f_1_3_1: forall n1 n2 n3  : ℕ, f_1 n1 n2 n3  = f_1 n1 n2 1
@[search] axiom f_2_3_1: forall n1 n2 n3  : ℕ, f_2 n1 n2 n3  = f_2 n1 n2 1
@[search] axiom f_3_3_1: forall n1 n2 n3  : ℕ, f_3 n1 n2 n3  = f_3 n1 n2 1
@[search] axiom f_4_3_1: forall n1 n2 n3  : ℕ, f_4 n1 n2 n3  = f_4 n1 n2 1
@[search] axiom f_5_3_1: forall n1 n2 n3  : ℕ, f_5 n1 n2 n3  = f_5 n1 n2 1
@[search] axiom f_1_3_2: forall n1 n2 n3  : ℕ, f_1 n1 n2 n3  = f_1 n1 n2 2
@[search] axiom f_2_3_2: forall n1 n2 n3  : ℕ, f_2 n1 n2 n3  = f_2 n1 n2 2
@[search] axiom f_3_3_2: forall n1 n2 n3  : ℕ, f_3 n1 n2 n3  = f_3 n1 n2 2
@[search] axiom f_4_3_2: forall n1 n2 n3  : ℕ, f_4 n1 n2 n3  = f_4 n1 n2 2
@[search] axiom f_5_3_2: forall n1 n2 n3  : ℕ, f_5 n1 n2 n3  = f_5 n1 n2 2
@[search] axiom f_1_3_3: forall n1 n2 n3  : ℕ, f_1 n1 n2 n3  = f_1 n1 n2 3
@[search] axiom f_2_3_3: forall n1 n2 n3  : ℕ, f_2 n1 n2 n3  = f_2 n1 n2 3
@[search] axiom f_3_3_3: forall n1 n2 n3  : ℕ, f_3 n1 n2 n3  = f_3 n1 n2 3
@[search] axiom f_4_3_3: forall n1 n2 n3  : ℕ, f_4 n1 n2 n3  = f_4 n1 n2 3
@[search] axiom f_5_3_3: forall n1 n2 n3  : ℕ, f_5 n1 n2 n3  = f_5 n1 n2 3

namespace v1
@[search] axiom f_1_f_2 : f_1 1 1 1 = f_2 1 1 1
@[search] axiom f_2_f_3 : f_2 1 1 1 = f_3 1 1 1
@[search] axiom f_3_f_5 : f_3 1 1 1 = f_5 1 1 1
@[search] axiom f_1_f_4 : f_1 0 1 2 = f_4 2 0 1
@[search] axiom f_4_f_5 : f_4 0 1 2 = f_5 2 0 1

-- rewrite_search_with (saw/visited/used) 114/112/13 expressions during proof of tactic.rewrite_search.examples.tactic.rewrite_search.tesseract.v1.test
lemma test : f_1 0 0 0 = f_5 0 0 0 :=
-- by erw [f_2_2, f_1_1, g_0_2, g_2_1, ←f_g]
by rewrite_search {trace := ff, explain := tt, trace_summary := tt, exhaustive := ff, strategy := pexplore {pop_size := 1, pop_alternate := ff}, metric := edit_distance {}, max_iterations := 1000}
end v1

namespace v2
@[search] axiom f_1_f_2' : f_1 0 1 2 = f_2 2 0 1
@[search] axiom f_2_f_3' : f_2 0 1 2 = f_3 2 0 1
@[search] axiom f_3_f_5' : f_3 0 1 2 = f_5 2 0 1
@[search] axiom f_1_f_4' : f_1 0 1 2 = f_4 2 0 1
-- @[search] axiom f_4_f_5' : f_4 0 1 2 = f_5 2 0 1

-- lemma test : f_1 0 0 0 = f_5 0 0 0 :=
-- -- by erw [f_2_2, f_1_1, g_0_2, g_2_1, ←f_g]
-- by rewrite_search {trace := ff, explain := tt, trace_summary := tt, exhaustive := ff, strategy := pexplore { pop_size := 100 }, metric := edit_distance {refresh_freq := 5} cm}
end v2

end tactic.rewrite_search.tesseract

end tactic.rewrite_search.examples

-- Maybe Scott wants this
--
-- structure cat :=
--   (O : Type)
--   (H : O → O → Type)
--   (i : Π o : O, H o o)
--   (c : Π {X Y Z : O} (f : H X Y) (g : H Y Z), H X Z)
--   (li : Π {X Y : O} (f : H X Y), c (i X) f = f)
--   (ri : Π {X Y : O} (f : H X Y), c f (i Y) = f)
--   (a : Π {W X Y Z : O} (f : H W X) (g : H X Y) (h : H Y Z), c (c f g) h = c f (c g h))

-- attribute [search] cat.li cat.a

-- private example (C : cat) (X Y Z : C.O) (f : C.H X Y) (g : C.H Y X) (w : C.c g f = C.i Y) (h k : C.H Y Z) (p : C.c f h = C.c f k) : h = k :=
-- begin
-- rewrite_search {},
-- end
