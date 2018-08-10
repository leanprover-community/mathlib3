
import tactic.monotonicity.interactive

import algebra.ordered_ring

import data.list.basic

open list tactic tactic.interactive

meta class elaborable (α : Type) (β : out_param Type) :=
  (elaborate : α → tactic β)

export elaborable (elaborate)

meta instance : elaborable pexpr expr :=
⟨ to_expr ⟩

meta instance elaborable_list {α α'} [elaborable α α'] : elaborable (list α) (list α') :=
⟨ mmap elaborate ⟩

meta def mono_function.elaborate : mono_function ff → tactic mono_function
| (mono_function.non_assoc x y z) :=
mono_function.non_assoc <$> elaborate x
                        <*> elaborate y
                        <*> elaborate z
| (mono_function.assoc x y z) :=
mono_function.assoc <$> elaborate x
                    <*> traverse elaborate y
                    <*> traverse elaborate z
| (mono_function.assoc_comm x y) :=
mono_function.assoc_comm <$> elaborate x
                         <*> elaborate y

meta instance elaborable_mono_function : elaborable (mono_function ff) mono_function :=
⟨ mono_function.elaborate ⟩

meta instance prod_elaborable {α α' β β' : Type} [elaborable α α']  [elaborable β β']
: elaborable (α × β) (α' × β') :=
⟨ λ i, prod.rec_on i (λ x y, prod.mk <$> elaborate x <*> elaborate y) ⟩

meta def parse_mono_function' (l r : pexpr) :=
do l' ← to_expr l,
   r' ← to_expr r,
   parse_ac_mono_function { mono_cfg . } l' r'

run_cmd
do xs ← mmap to_expr [``(1),``(2),``(3)],
   ys ← mmap to_expr [``(1),``(2),``(4)],
   x ← match_prefix { unify := ff } xs ys,
   p ← elaborate ([``(1),``(2)] , [``(3)], [``(4)]),
   guard $ x = p

run_cmd
do xs ← mmap to_expr [``(1),``(2),``(3),``(6),``(7)],
   ys ← mmap to_expr [``(1),``(2),``(4),``(5),``(6),``(7)],
   x ← match_assoc { unify := ff } xs ys,
   p ← elaborate ([``(1), ``(2)], [``(3)], ([``(4), ``(5)], [``(6), ``(7)])),
   guard (x = p)

run_cmd
do x ← to_expr ``(7 + 3 : ℕ) >>= check_ac,
   x ← pp x.2.2.1,
   let y := "(some (is_left_id.left_id has_add.add, (is_right_id.right_id has_add.add, 0)))",
   guard (x.to_string = y) <|> fail ("guard: " ++ x.to_string)

meta def test_pp {α} [has_to_tactic_format α] (tag : format) (expected : string) (prog : tactic α) : tactic unit :=
do r ← prog,
   pp_r ← pp r,
   guard (pp_r.to_string = expected) <|> fail format!"test_pp: {tag}"

run_cmd
do test_pp "test1"
           "(3 + 6, (4 + 5, ([], has_add.add _ 2 + 1)))"
           (parse_mono_function' ``(1 + 3 + 2 + 6) ``(4 + 2 + 1 + 5)),
   test_pp "test2"
           "([1] ++ [3] ++ [2] ++ [6], ([4] ++ [2] ++ [1] ++ [5], ([], append none _ none)))"
           (parse_mono_function' ``([1] ++ [3] ++ [2] ++ [6]) ``([4] ++ [2] ++ ([1] ++ [5]))),
   test_pp "test3"
           "([3] ++ [2], ([5] ++ [4], ([], append (some [1]) _ (some [2]))))"
           (parse_mono_function' ``([1] ++ [3] ++ [2] ++ [2]) ``([1] ++ [5] ++ ([4] ++ [2])))

lemma bar
  (h : 3 + 6 ≤ 4 + 5)
: 1 + 3 + 2 + 6 ≤ 4 + 2 + 1 + 5 :=
begin
  ac_mono,
end

lemma bar'
  (h : 3 ≤ (4 : ℤ))
  (h' : 5 ≤ (6 : ℤ))
: (1 + 3 + 2) - 6 ≤ (4 + 2 + 1 : ℤ) - 5 :=
begin
  transitivity (1 + 3 + 2 - 5 : ℤ),
  ac_mono,
  ac_mono,
end

example (x y z : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ (y : ℤ))
: (1 + 3 + x) - y ≤ (1 + 4 + x : ℤ) - z :=
begin
  transitivity (1 + 3 + x - z : ℤ),
  mono, mono,
  mono, mono,
end

example (x y z : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ (y : ℤ))
: (1 + 3 + x) - y ≤ (1 + 4 + x : ℤ) - z :=
begin
  ac_mono, mono*
end

@[simp]
def list.le' {α : Type*} [has_le α] : list α → list α → Prop
 | (x::xs) (y::ys) := x ≤ y ∧ list.le' xs ys
 | [] [] := true
 | _ _ := false

@[simp]
instance list_has_le {α : Type*} [has_le α] : has_le (list α) :=
⟨ list.le' ⟩

lemma list.le_refl {α : Type*} [preorder α] {xs : list α}
: xs ≤ xs :=
begin
  induction xs with x xs,
  { trivial },
  { simp [has_le.le,list.le],
    split, apply le_refl, apply xs_ih }
end

-- @[trans]
lemma list.le_trans {α : Type*} [preorder α]
  {xs zs : list α} (ys : list α)
  (h  : xs ≤ ys)
  (h' : ys ≤ zs)
: xs ≤ zs :=
begin
  revert ys zs,
  induction xs with x xs
  ; intros ys zs h h'
  ; cases ys with y ys
  ; cases zs with z zs
  ; try { cases h ; cases h' ; done },
  { apply list.le_refl },
  { simp [has_le.le,list.le],
    split,
    apply le_trans h.left h'.left,
    apply xs_ih _ h.right h'.right, }
end

@[monotonic]
lemma list_le_mono_left {α : Type*} [preorder α] {xs ys zs : list α}
  (h : xs ≤ ys)
: xs ++ zs ≤ ys ++ zs :=
begin
  revert ys,
  induction xs with x xs ; intros ys h,
  { cases ys, apply list.le_refl, cases h },
  { cases ys with y ys, cases h, simp [has_le.le,list.le] at *,
    revert h, apply and.imp_right,
    apply xs_ih }
end

@[monotonic]
lemma list_le_mono_right {α : Type*} [preorder α] {xs ys zs : list α}
  (h : xs ≤ ys)
: zs ++ xs ≤ zs ++ ys :=
begin
  revert ys zs,
  induction xs with x xs ; intros ys zs h,
  { cases ys, { simp, apply list.le_refl }, cases h  },
  { cases ys with y ys, cases h, simp [has_le.le,list.le] at *,
    suffices : list.le' ((zs ++ [x]) ++ xs) ((zs ++ [y]) ++ ys),
    { refine cast _ this, simp, },
    apply list.le_trans (zs ++ [y] ++ xs),
    { apply list_le_mono_left,
      induction zs with z zs,
      { simp [has_le.le,list.le], apply h.left },
      { simp [has_le.le,list.le], split, apply le_refl,
        apply zs_ih, } },
    { apply xs_ih h.right, } }
end

lemma bar_bar'
  (h : [] ++ [3] ++ [2] ≤ [1] ++ [5] ++ [4])
: [] ++ [3] ++ [2] ++ [2] ≤ [1] ++ [5] ++ ([4] ++ [2]) :=
begin
  ac_mono,
end

lemma bar_bar''
  (h : [3] ++ [2] ++ [2] ≤ [5] ++ [4] ++ [])
: [1] ++ ([3] ++ [2]) ++ [2] ≤ [1] ++ [5] ++ ([4] ++ []) :=
begin
  ac_mono,
end

lemma bar_bar
  (h : [3] ++ [2] ≤ [5] ++ [4])
: [1] ++ [3] ++ [2] ++ [2] ≤ [1] ++ [5] ++ ([4] ++ [2]) :=
begin
  ac_mono,
end

def P (x : ℕ) := 7 ≤ x
def Q (x : ℕ) := x ≤ 7

@[monotonic]
lemma P_mono {x y : ℕ}
  (h : x ≤ y)
: P x → P y :=
by { intro h', apply le_trans h' h }

@[monotonic]
lemma Q_mono {x y : ℕ}
  (h : y ≤ x)
: Q x → Q y :=
by apply le_trans h

example (x y z : ℕ)
  (h : x ≤ y)
: P (x + z) → P (z + y) :=
begin
  ac_mono,
  ac_mono,
end

example (x y z : ℕ)
  (h : y ≤ x)
: Q (x + z) → Q (z + y) :=
begin
  ac_mono,
  ac_mono,
end

example (x y z k m n : ℤ)
  (h₀ : z ≤ 0)
  (h₁ : y ≤ x)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  ac_mono,
  ac_mono,
  ac_mono,
end

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  ac_mono,
  ac_mono,
  ac_mono,
  solve_by_elim
end

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
by {  ac_mono* h₁ }

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : m + x + n ≤ y + n + m)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
by { ac_mono* h₁ }

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : n + x + m ≤ y + n + m)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  ac_mono* : m + x + n ≤ y + n + m,
  transitivity ; [ skip , apply h₁ ],
  apply le_of_eq,
  ac_refl,
end

example (x y z k m n : ℤ)
  (h₁ : x ≤ y)
: true :=
begin
  have : (m + x + n) * z + k ≤ z * (y + n + m) + k,
  { ac_mono,
    success_if_fail { ac_mono },
    admit },
  trivial
end

example (x y z k m n : ℕ)
  (h₁ : x ≤ y)
: true :=
begin
  have : (m + x + n) * z + k ≤ z * (y + n + m) + k,
  { ac_mono*,
    change 0 ≤ z, apply nat.zero_le, },
  trivial
end

example (x y z k m n : ℕ)
  (h₁ : x ≤ y)
: true :=
begin
  have : (m + x + n) * z + k ≤ z * (y + n + m) + k,
  { ac_mono,
    change (m + x + n) * z ≤ z * (y + n + m),
    admit },
  trivial,
end

example (x y z k m n i j : ℕ)
  (h₁ : x + i = y + j)
: (m + x + n + i) * z + k = z * (j + n + m + y) + k :=
begin
  ac_mono^3,
  simp [h₁],
end

example (x y z k m n i j : ℕ)
  (h₁ : x + i = y + j)
: (m + x + n + i) * z + k = z * (j + n + m + y) + k :=
begin
  ac_mono*,
  simp [h₁],
end

example (x y : ℕ)
  (h : x ≤ y)
: true :=
begin
  (do v ← mk_mvar,
      p ← to_expr ```(%%v + x ≤ y + %%v),
      assert `h' p),
  ac_mono h,
  trivial,
  exact 1,
end

namespace tactic.interactive
open interactive interactive.types lean.parser

meta def guard_expr_eq' (t : expr) (p : parse $ tk ":=" *> texpr) : tactic unit :=
do e ← to_expr p, is_def_eq t e

/--
`guard_target t` fails if the target of the main goal is not `t`.
We use this tactic for writing tests.
-/
meta def guard_target' (p : parse texpr) : tactic unit :=
do t ← target, guard_expr_eq' t p

end tactic.interactive

example {x y z : ℕ} : true :=
begin
  have : y + x ≤ y + z,
  { mono,
    guard_target' x ≤ z,
    admit },
  trivial
end

example {x y z : ℕ} : true :=
begin
  suffices : x + y ≤ z + y, trivial,
  mono,
  guard_target' x ≤ z,
  admit,
end

example {x y z w : ℕ} : true :=
begin
  have : x + y ≤ z + w,
  { mono,
    guard_target' x ≤ z, admit,
    guard_target' y ≤ w, admit },
  trivial
end

example {x y z w : ℕ} : true :=
begin
  have : x * y ≤ z * w,
  { mono using [0 ≤ z,0 ≤ y],
    { guard_target 0 ≤ z, admit },
    { guard_target 0 ≤ y, admit },
    guard_target' x ≤ z, admit,
    guard_target' y ≤ w, admit },
  trivial
end

example {x y z w : Prop} : true :=
begin
  have : x ∧ y → z ∧ w,
  { mono,
    guard_target' x → z, admit,
    guard_target' y → w, admit },
  trivial
end

example {x y z w : Prop} : true :=
begin
  have : x ∨ y → z ∨ w,
  { mono,
    guard_target' x → z, admit,
    guard_target' y → w, admit },
  trivial
end

example {x y z w : ℤ} : true :=
begin
  suffices : x + y < w + z, trivial,
  have : x < w, admit,
  have : y ≤ z, admit,
  mono right,
end

example {x y z w : ℤ} : true :=
begin
  suffices : x * y < w * z, trivial,
  have : x < w, admit,
  have : y ≤ z, admit,
  mono right,
  { guard_target' 0 < y, admit },
  { guard_target' 0 ≤ w, admit },
end

open tactic

example (x y : ℕ)
  (h : x ≤ y)
: true :=
begin
  (do v ← mk_mvar,
      p ← to_expr ```(%%v + x ≤ y + %%v),
      assert `h' p),
  ac_mono h,
  trivial,
  exact 3
end
