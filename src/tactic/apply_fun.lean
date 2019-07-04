import tactic.monotonicity
import order.basic

open tactic interactive (parse) interactive (loc.ns)
     interactive.types (texpr location) lean.parser (tk)

local postfix `?`:9001 := optional

meta def apply_fun_name (e : expr) (h : name) (M : option pexpr) : tactic unit :=
do {
  H ← get_local h,
  t ← infer_type H,
  match t with
  | `(%%l = %%r) := do
      tactic.interactive.«have» h none ``(congr_arg %%e %%H),
      tactic.clear H
  | `(%%l ≤ %%r) := do
       if M.is_some then do
         Hmono ← M >>= tactic.i_to_expr,
         tactic.interactive.«have» h none ``(%%Hmono %%H)
       else do {
         n ← get_unused_name `mono,
         tactic.interactive.«have» n ``(monotone %%e) none,
         do { intro_lst [`x, `y, `h], `[dsimp, mono], skip } <|> swap,
         Hmono ← get_local n,
         tactic.interactive.«have» h none ``(%%Hmono %%H) },
       tactic.clear H
  | _ := skip
  end,
  -- let's try to force β-reduction at `h`
  try (tactic.interactive.dsimp tt [] [] (loc.ns [h])
         {eta := false, beta := true})
  } <|> fail ("failed to apply " ++ to_string e ++ " at " ++ to_string h)

namespace tactic.interactive
/-- Apply a function to some local assumptions which are either equalities or
    inequalities. For instance, if the context contains `h : a = b` and
    some function `f` then `apply_fun f at h` turns `h` into `h : f a = f b`.
    When the assumption is an inequality `h : a ≤ b`, a side goal `monotone f`
    is created, unless this condition is provided using
    `apply_fun f at h using P` where `P : monotone f`, or the `mono` tactic can
    prove it. -/
meta def apply_fun (q : parse texpr) (locs : parse location)
  (lem : parse (tk "using" *> texpr)?) : tactic unit :=
do e ← tactic.i_to_expr q,
   match locs with
   | (loc.ns l) := do
      l.mmap' (λ l, match l with
      | some h :=  apply_fun_name e h lem
      | none := skip
      end)
   | wildcard := do ctx ← local_context,
                    ctx.mmap' (λ h, apply_fun_name e h.local_pp_name lem)
   end
end tactic.interactive

open function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : injective $ g ∘ f) :
  injective f :=
begin
  intros x x' h,
  apply_fun g at h,
  exact H h
end

example (f : ℕ → ℕ) (a b : ℕ) (monof : monotone f)  (h : a ≤ b) : f a ≤ f b :=
begin
  apply_fun f at h,
  assumption,
  assumption
end

example (a b : ℕ) (h : a = b) : a + 1 = b + 1 :=
begin
  apply_fun (λ n, n+1) at h,
  -- check that `h` was β-reduced
  guard_hyp' h := a + 1 = b + 1,
  exact h
end

example (f : ℕ → ℕ) (a b : ℕ) (monof : monotone f)  (h : a ≤ b) : f a ≤ f b :=
begin
  apply_fun f at h using monof,
  assumption
end

-- monotonicity will be proved by `mono` in the next example
example (a b : ℕ) (h : a ≤ b) : a + 1 ≤ b + 1 :=
begin
  apply_fun (λ n, n+1) at h,
  exact h
end
