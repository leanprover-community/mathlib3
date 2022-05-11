import algebra.big_operators.basic

inductive domino_coverable : finset (ℕ × ℕ) → Prop
| empty : domino_coverable ∅
| horizontal (x) (s : finset (ℕ × ℕ)) (w₁ : x ∉ s) (w₂ : (x + (1,0) ∉ s)) (c : domino_coverable s) :
    domino_coverable (s ∪ {x, x + (1,0)})
| vertical   (x) (s : finset (ℕ × ℕ)) (w₁ : x ∉ s) (w₂ : (x + (0,1) ∉ s)) (c : domino_coverable s) :
    domino_coverable (s ∪ {x, x + (0,1)})

def square (n : ℕ) := (finset.range n).product (finset.range n)
def corners_removed (n : ℕ) := ((square n).erase (0,0)).erase (n-1, n-1)

lemma not_of_invariant_ne {α : Type*} (P : α → Prop) (a : α)
  (h : ∃ {β : Type*} (f : α → β) (b : β) (w : ∀ a, P a → f a = b), f a ≠ b) : ¬ P a :=
by tidy

def iterate₂ {α : Type*} (z : α) (f g : α → α) (w : ∀ a, f (g a) = g (f a)) : ℕ × ℕ → α :=
λ p, f^[p.1] (g^[p.2] z)

@[simp] lemma cf₁ {α : Type*} (z : α) (f g : α → α) (w : ∀ a, f (g a) = g (f a)) (x y : ℕ) :
  iterate₂ z f g w (x + 1, y) = f (iterate₂ z f g w (x, y)) :=
function.iterate_succ_apply' _ _ _

@[simp] lemma cf₂ {α : Type*} (z : α) (f g : α → α) (w : ∀ a, f (g a) = g (f a)) (x y : ℕ) :
  iterate₂ z f g w (x, y + 1) = g (iterate₂ z f g w (x, y)) :=
begin
  have w : function.commute f g := w,
  dsimp [iterate₂],
  rw [←function.iterate_succ_apply, w.iterate_iterate, w.iterate_iterate,
    ←function.iterate_succ_apply' g],
end

theorem corners_removed_not_domino_coverable (n : ℕ) (p : 0 < n) :
  ¬ domino_coverable (corners_removed n) :=
begin
  -- We are trying to show some property does not hold.
  -- Let's guess that we should construct an invariant of terms satisfying this property,
  -- and calculate it.
  apply not_of_invariant_ne,
  -- Let's break apart that goal.
  refine ⟨_, _, _, _, _⟩,
  -- There's nothing to say about the first three goals,
  -- so let's work on the 4th one.
  work_on_goal 4 {
    -- Introduce variables for the universal quantifiers.
    intros a h,
    -- Since `h` is an inductive predicate, it may be helpful to look at cases:
    induction h,
    -- The first goal must just specifiy the value of our invariant on the empty set;
    -- it's not useful by itself.
    rotate,
    -- The BIG IDEA:
    -- Our condition says something about the value of our invariant on a union of sets,
    -- so let's try something *additive*.
    -- (Note this idea would be slightly smaller if we could easily see this condition
    -- was about a disjoint union of sets.)
    -- We're going to have to jump back out to a different goal to say that.
    },
  work_on_goal 2 {
    refine (λ s, s.sum _),
    -- Note that the new function goal includes `s` as a potential dependency.
    -- (Lean knows that it is open to us to use a different value function for each set!)
    -- Let's rule that out.
    any_goals { clear s, },
  },
  -- Our condition about the empty set is now profitable:
  work_on_goal 8 { exact finset.sum_empty, },
  -- Let's return to looking at the horizontal condition.
  work_on_goal 4 {
    -- Split the sum over the union, and use the inductive hypothesis.
    rw [finset.sum_union, h_ih, zero_add],
    rw [finset.sum_insert, finset.sum_singleton],
    -- We've now reached a fun fact (althought with unreadable names):
    -- `g x + g (x + (1,0)) = 0`.

    -- There are some minor goals to discharge:
    work_on_goal 2 { simp, },
    work_on_goal 2 { simp [h_w₁, h_w₂], }, },
  -- Now the same for the vertical condition:
  work_on_goal 5 {
    -- Split the sum over the union, and use the inductive hypothesis.
    rw [finset.sum_union, h_ih, zero_add],
    rw [finset.sum_insert, finset.sum_singleton],
    -- `g x + g (x + (0,1)) = 0`.

    -- Again, there are some minor goals to discharge:
    work_on_goal 2 { simp, },
    work_on_goal 2 { simp [h_w₁, h_w₂], }, },
  -- Since we have "interesting" conditions of the form x + y = 0,
  -- it might be best if we work in an `add_comm_group` rather than just an `add_comm_monoid`.
  work_on_goal 3 { refine add_comm_group.to_add_comm_monoid _, },
  -- Actually, let's cheat horribly and set the target type to `ℤ`.
  -- There are some hopefully uninteresting technically difficulties arising from
  -- postponing this goal any further. :-(
  work_on_goal 1 { exact ℤ },
  work_on_goal 1 { apply_instance, },
  -- Now let's return to the horizontal condition.
  work_on_goal 1 {
    -- Discard irrelevancies:
    clear_dependent a h_s,
    rcases h_x with ⟨x, y⟩,
    simp only [prod.mk_add_mk, add_zero],
    rw add_eq_zero_iff_neg_eq,
    symmetry,
    -- This looks really good! If we were defining our function on `ℕ × ℕ` by induction,
    -- we'd see this was determining values!
    -- Let's do the same work on the vertical condition, first.
  },
  work_on_goal 2 {
    -- Discard irrelevancies:
    clear_dependent a h_s,
    rcases h_x with ⟨x, y⟩,
    simp only [prod.mk_add_mk, add_zero],
    rw add_eq_zero_iff_neg_eq,
    symmetry,
  },
  -- Now specify that our valuation function has the desired form.
  work_on_goal 3 {
    apply iterate₂,
  },
  work_on_goal 1 {
    simp, -- Discharged! Notice this is automatically solving for metavariables.
  },
  work_on_goal 1 {
    simp?,
  },
  -- Discharge the proof obligation --a = --a:
  work_on_goal 2 { intros, refl, },
  -- Cheating for now, and guess we should use 1 at the base square:
  work_on_goal 1 { exact 1, },
  { dsimp [corners_removed, square],
    -- after that, it's "just" a calculation,
    -- but I'm not going to do it now.
    sorry
  }
end
