import tactic.simp_result
import data.equiv.basic

open tactic

-- Check that we can walk.
example : true :=
by { simp_result { trivial } }

-- Comparison without `dsimp_result`:
example : true :=
begin
  exact (id trivial),
  (do `(id trivial) ← result, skip),
  success_if_fail { (do `(trivial) ← result, skip) },
end

-- Check that `dsimp_result` removes unnecessary `id`s.
example : true :=
begin
  dsimp_result { exact (id trivial) },
  success_if_fail { (do `(id trivial) ← result, skip) },
  (do `(trivial) ← result, skip),
end

-- Comparison without `dsimp_result`:
example (a : ℕ) (b : list ℕ) (h : b.length < a) : ℕ :=
begin
  revert a,
  intros a h,
  exact 0,
  (do `((λ (h : list.length _ < _), 0) _) ← result, skip),
  success_if_fail { (do `(0) ← result, skip) },
end

-- Check that `dsimp_result` does beta-reductions after `revert`.
example (a : ℕ) (b : list ℕ) (h : b.length < a) : ℕ :=
begin
  dsimp_result
  { revert a,
    intros a h,
    exact 0, },
  success_if_fail { (do `((λ (h : list.length _ < _), 0) _) ← result, skip), },
  (do `(0) ← result, skip),
end

meta def guard_result_pp (s : string) : tactic unit :=
do
  r ← (to_string <$> (result >>= pp)),
  guard (r = s) <|> fail format!"result was {r} but expected {s}"

-- Comparison without `simp_result`:
example {α β : Type} (e : α ≃ β) (a : α) : β :=
begin
  exact e (e.symm (e a)),
  guard_result_pp "⇑e (⇑(equiv.symm e) (⇑e a))",
end

-- Check that `simp_result` applies non-definitional simplifications to the result.
example {α β : Type} (e : α ≃ β) (a : α) : β :=
begin
  simp_result { exact e (e.symm (e a)) },
  guard_result_pp "⇑e a",
end

-- Check that `simp_result only [...]` behaves as expected.
example {α β : Type} (e : α ≃ β) (a : α) : β :=
begin
  simp_result only [equiv.apply_symm_apply] { exact e (e.symm (e a)) },
  guard_result_pp "⇑e a",
end

-- Check that `simp_result only []` does not simplify.
-- (Note the `simp_result` succeeds even if no simplification occurs.)
example {α β : Type} (e : α ≃ β) (a : α) : β :=
begin
  simp_result only [] { exact e (e.symm (e a)) },
  guard_result_pp "⇑e (⇑(equiv.symm e) (⇑e a))",
end

-- Comparison without `simp_result`
example {α : Type} (a b : α) (h : a = b) : ℕ :=
begin
  subst h,
  exact 0,
  guard_result_pp "eq.rec 0 h",
end

-- Check that we can remove `eq.rec` transports through constant families
-- introduced by irrelevant use of `subst`.
example {α : Type} (a b : α) (h : a = b) : ℕ :=
begin
  simp_result only [eq_rec_constant]
  { subst h,
    exact 0, },
  guard_result_pp "0",
end

-- Check that `simp_result` performs simplifications on all results.
example : ℕ × ℕ :=
begin
  split,
  simp_result
  { exact id 0,
    exact id 1, },
  guard_result_pp "(0, 1)",
end
