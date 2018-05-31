/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Define a sequence of simple machine languages, starting with Turing
machines and working up to more complex lanaguages based on
Wang B-machines.
-/
import data.finset data.sum data.finsupp data.array.lemmas

namespace turing

@[derive decidable_eq]
inductive dir | left | right

namespace dir
def rev : dir → dir
| left := right
| right := left
end dir

def move_tape {Γ} [inhabited Γ] :
  dir → Γ × list Γ × list Γ → Γ × list Γ × list Γ
| dir.left (a, L, R) := (L.head, L.tail, a :: R)
| dir.right (a, L, R) := (R.head, a :: L, R.tail)

namespace TM0

section
parameters (Γ : Type*) [inhabited Γ]
parameters (Λ : Type*)

inductive stmt
| move {} : dir → stmt
| write {} : Γ → stmt

structure machine :=
(start : Λ)
(trans : Λ → Γ → option (Λ × stmt))

structure state :=
(q : Λ)
(tape : Γ × list Γ × list Γ)

def step (M : machine) : state → option state
| ⟨q, T⟩ := (M.trans q T.1).map (λ ⟨q', a⟩, ⟨q',
  match a with
  | stmt.move d := move_tape d T
  | stmt.write a := (a, T.2)
  end⟩)

def supports [fintype Γ] (M : machine) (S : finset Λ) :=
M.start ∈ S ∧ ∀ {q a q' s}, (q', s) ∈ M.trans q a → q ∈ S → q' ∈ S

theorem step_supports [fintype Γ] (M : machine) {S}
  (ss : supports M S) : ∀ {s s' : state},
  s' ∈ step M s → s.q ∈ S → s'.q ∈ S
| ⟨q, T⟩ s' h₁ h₂ := begin
  rcases option.map_eq_some'.1 h₁ with ⟨⟨q', a⟩, h, rfl⟩,
  exact ss.2 h h₂,
end

end

end TM0

namespace TM1

section
parameters (Γ : Type*) [inhabited Γ]
parameters (Λ : Type*)

inductive stmt
| move : dir → stmt → stmt
| write : Γ → stmt → stmt
| branch : (Γ → stmt) → stmt
| goto {} : Λ → stmt
| halt {} : stmt
open stmt

structure state :=
(q : stmt)
(tape : Γ × list Γ × list Γ)

parameters {Γ Λ}
def step (funcs : Λ → stmt) : state → option state
| ⟨q, T⟩ := begin
  induction q generalizing T,
  case TM1.stmt.move   : d q IH { exact IH (move_tape d T) },
  case TM1.stmt.write  : a q IH { exact IH (a, T.2) },
  case TM1.stmt.branch : p IH   { exact IH T.1 T },
  case TM1.stmt.goto   : l      { exact some ⟨funcs l, T⟩ },
  case TM1.stmt.halt            { exact none }
end

def supports_stmt [fintype Γ] (S : finset Λ) : stmt → Prop
| (move d q) := supports_stmt q
| (write a q) := supports_stmt q
| (branch f) := ∀ a, supports_stmt (f a)
| (goto l) := l ∈ S
| halt := true

def supports [fintype Γ] (M : Λ → stmt) (S : finset Λ) :=
∀ q ∈ S, supports_stmt S (M q)

local attribute [instance] classical.dec
noncomputable def stmts₁ [fintype Γ] : stmt → finset stmt
| Q@(move d q) := insert Q (stmts₁ q)
| Q@(write a q) := insert Q (stmts₁ q)
| Q@(branch f) := insert Q (finset.univ.bind (λ a, stmts₁ (f a)))
| Q@(goto l) := {Q}
| Q@halt := {Q}

theorem stmts₁_self [fintype Γ] {q} : q ∈ stmts₁ q :=
by cases q; simp [stmts₁]

noncomputable def stmts [fintype Γ]
  (M : Λ → stmt) (S : finset Λ) : finset stmt :=
S.bind (λ q, stmts₁ (M q))

theorem step_supports [fintype Γ] (M : Λ → stmt) {S}
  (ss : supports M S) : ∀ {s s' : state},
  s' ∈ step M s → s.q ∈ stmts M S → s'.q ∈ stmts M S
| ⟨q₁, T⟩ s' h₁ h₂ := begin
  rcases finset.mem_bind.1 h₂ with ⟨l, hl, h⟩,
  change q₁ ∈ stmts₁ (M l) at h,
  suffices : q₁ ∈ stmts₁ (M l) → supports_stmt S (M l) →
    s'.q ∈ stmts₁ (M l) ∨ s'.q ∈ stmts M S,
  from (or_iff_right_of_imp
    (λ h, finset.mem_bind.2 ⟨_, hl, h⟩)).1 (this h (ss _ hl)),
  clear h h₂, induction M l generalizing q₁ T;
    intros h hs; simp [stmts₁] at h ⊢,
  case TM1.stmt.move : d q IH {
    rcases h with rfl | h,
    { exact (IH q _ h₁ stmts₁_self hs).imp_left or.inr },
    { exact (IH q₁ _ h₁ h hs).imp_left or.inr } },
  case TM1.stmt.write : a q IH {
    rcases h with rfl | h,
    { exact (IH q _ h₁ stmts₁_self hs).imp_left or.inr },
    { exact (IH q₁ _ h₁ h hs).imp_left or.inr } },
  case TM1.stmt.branch : f IH {
    rcases h with rfl | ⟨a, h⟩,
    { exact (IH _ (f T.1) _ h₁ stmts₁_self (hs _))
        .imp_left (λ h, or.inr ⟨_, h⟩) },
    { exact (IH _ q₁ _ h₁ h (hs _))
        .imp_left (λ h, or.inr ⟨_, h⟩) } },
  case TM1.stmt.goto : l {
    subst h, cases h₁,
    simp [stmts],
    exact or.inr ⟨_, hs, stmts₁_self⟩ },
  case TM1.stmt.halt { subst h, cases h₁ }
end

end

end TM1

namespace TM1to0

section
parameters (Γ : Type*) [inhabited Γ]
parameters (Λ : Type*)

local notation `stmt₁` := TM1.stmt Γ Λ

local notation `stmt₀` := TM0.stmt Γ

open TM0.stmt

def trans (funcs : Λ → stmt₁) : stmt₁ → Γ → option (stmt₁ × stmt₀)
| (TM1.stmt.move d q) a := some (q, move d)
| (TM1.stmt.write a q) s := some (q, write a)
| (TM1.stmt.branch f) s := trans (f s) s
| (TM1.stmt.goto l) s := some (funcs l, write s)
| TM1.stmt.halt s := none

def translate (funcs : Λ → stmt₁) (main : stmt₁) : TM0.machine Γ stmt₁ :=
⟨main, trans funcs⟩

end

end TM1to0

namespace TM2

section
parameters (Γ : Type*) [inhabited Γ]
parameters (Λ : Type*)
parameters (σ : Type*)

inductive stmt
| move : dir → stmt → stmt
| move_until : dir → (Γ → σ → bool) → stmt → stmt
| write : (Γ → σ → Γ) → stmt → stmt
| load : (Γ → σ → σ) → stmt → stmt
| branch : (Γ → σ → bool) → stmt → stmt → stmt
| goto {} : (Γ → σ → Λ) → stmt
| halt {} : stmt
open stmt

structure state :=
(q : stmt)
(var : σ)
(tape : Γ × list Γ × list Γ)

def step_aux (funcs : Λ → stmt) :
  stmt → σ → Γ × list Γ × list Γ → option state
| (move d q) v T := step_aux q v (move_tape d T)
| (move_until d f q) v T :=
  if f T.1 v then step_aux q v T else some ⟨q, v, move_tape d T⟩
| (write f q) v (a, LR) := step_aux q v (f a v, LR)
| (load f q) v T := step_aux q (f T.1 v) T
| (branch f q₁ q₂) v T :=
  if f T.1 v then step_aux q₁ v T else step_aux q₂ v T
| (goto f) v T := some ⟨funcs (f T.1 v), v, T⟩
| halt v T := none

def step (funcs : Λ → stmt) : state → option state
| ⟨q, v, T⟩ := step_aux funcs q v T

end

end TM2

namespace TM2to1

section
parameters (Γ : Type*) [inhabited Γ]
parameters (Λ : Type*)
parameters (σ : Type*)

local notation `stmt₂` := TM2.stmt Γ Λ σ

local notation `stmt₁` := TM1.stmt Γ (stmt₂ × σ)

open TM1.stmt

def translate' (funcs : Λ → stmt₂) : stmt₂ → σ → stmt₁
| (TM2.stmt.move d q) s := move d (translate' q s)
| (TM2.stmt.move_until d p q) s :=
  branch $ λ a,
  if p a s then translate' q s else
  goto (TM2.stmt.move_until d p q, s)
| (TM2.stmt.write f q) s :=
  branch $ λ a, write (f a s) $ translate' q s
| (TM2.stmt.load f q) s :=
  branch $ λ a, translate' q (f a s)
| (TM2.stmt.branch f q₁ q₂) s :=
  branch $ λ a, if f a s then translate' q₁ s else translate' q₂ s
| (TM2.stmt.goto l) s :=
  branch $ λ a, goto (funcs (l a s), s)
| TM2.stmt.halt s := halt

def translate (funcs : Λ → stmt₂) (f : σ → stmt₂) : stmt₂ × σ → stmt₁
| (q, s) := translate' funcs q s

end

end TM2to1

namespace TM3

section
parameters (Γ : Type*) [inhabited Γ]
parameters (Λ : Type*)
parameters (σ : Type*)
parameters (K : ℕ)

inductive stmt
| move : dir → stmt → stmt
| move_until : dir → (Γ → σ → bool) → stmt → stmt
| write : (Γ → σ → Γ) → stmt → stmt
| load : (Γ → σ → σ) → stmt → stmt
| branch : (Γ → σ → bool) → stmt → stmt → stmt
| goto {} : (Γ → σ → Λ) → stmt
| push {} : fin K → (σ → Γ) → stmt → stmt
| pop {} : fin K → (σ → option Γ → σ) → stmt → stmt
| halt {} : stmt
open stmt

structure machine :=
(main : stmt) (funcs : Λ → stmt)

structure state :=
(q : stmt)
(var : σ)
(stk : array K (list Γ))
(tape : Γ × list Γ × list Γ)

def step_aux (funcs : Λ → stmt) :
  stmt → σ → array K (list Γ) → Γ × list Γ × list Γ → option state
| (move d q) v S T := step_aux q v S (move_tape d T)
| (move_until d f q) v S T :=
  if f T.1 v then step_aux q v S T else some ⟨q, v, S, move_tape d T⟩
| (write f q) v S (a, LR) := step_aux q v S (f a v, LR)
| (load f q) v S T := step_aux q (f T.1 v) S T
| (branch f q₁ q₂) v S T :=
  if f T.1 v then step_aux q₁ v S T else step_aux q₂ v S T
| (goto f) v S T := some ⟨funcs (f T.1 v), v, S, T⟩
| (push k f q) v S T :=
  step_aux q v (S.write k (f v :: S.read k)) T
| (pop k f q) v S T :=
  step_aux q (f v (S.read k).head') (S.write k (S.read k).tail) T
| halt v S T := none

def step (funcs : Λ → stmt) : state → option state
| ⟨q, v, S, T⟩ := step_aux funcs q v S T

end

end TM3

namespace TM3to2

section
parameters (Γ : Type*) [inhabited Γ]
parameters (Λ : Type*)
parameters (σ : Type*)
parameters (K : ℕ)

local notation `stmt₃` := TM3.stmt Γ Λ σ K

@[derive decidable_eq]
inductive stackel
| val : Γ → stackel
| bottom {}
| top {}

instance stackel.inhabited : inhabited stackel :=
⟨stackel.val (default _)⟩

parameters {Γ}
def stackel.is_bottom : stackel → bool
| stackel.bottom := tt
| _ := ff 

def stackel.is_top : stackel → bool
| stackel.top := tt
| _ := ff 

def stackel.get : stackel → option Γ
| (stackel.val a) := some a
| _ := none
parameters (Γ)

section
open stackel

def stackel_equiv : stackel ≃ option (option Γ) :=
begin
  refine ⟨λ s, _, λ s, _, _, _⟩,
  { cases s, exacts [some (some s), none, some none] },
  { rcases s with _|_|s, exacts [bottom, top, val s] },
  { intro s, cases s; refl },
  { intro s, rcases s with _|_|s; refl },
end

end

@[derive decidable_eq]
structure alph :=
(base : Γ)
(stack : array K stackel)
(dir : dir)
(last_pos : bool)

instance alph.inhabited : inhabited alph :=
⟨⟨default _, default _, dir.right, ff⟩⟩

local notation `stmt₂` := TM2.stmt alph stmt₃ σ

open TM2.stmt

def at_stack (k : fin K) (q : stmt₂) (f : stmt₂ → stmt₂) : stmt₂ :=
let go (d : dir) : stmt₂ :=
  move_until d (λ a s, (a.stack.read k).is_bottom) $
  move_until dir.right (λ a s, (a.stack.read k).is_top) $
  f $
  move_until dir.left (λ a s, (a.stack.read k).is_bottom) $
  move_until d.rev (λ a s, a.last_pos) $
  write (λ a s, {last_pos := ff, ..a}) $
  q in
write (λ a s, {last_pos := tt, ..a}) $
branch (λ a s, a.dir = dir.left)
  (go dir.left) (go dir.right)

def push (k : fin K) (f : σ → Γ) (q : stmt₂) : stmt₂ :=
at_stack k q $ λ done,
write (λ a s, {stack := a.stack.write k (stackel.val (f s)), ..a}) $
move dir.right $
write (λ a s, {stack := a.stack.write k stackel.top, ..a}) $
done

def pop (k : fin K) (f : σ → option Γ → σ) (q : stmt₂) : stmt₂ :=
at_stack k q $ λ done,
move dir.right $
load (λ a s, f s $
  match a.stack.read k with
  | (stackel.val a) := some a
  | _ := none
  end) $
branch (λ a s, (a.stack.read k).is_bottom)
( done )
( move dir.right $
  write (λ a s, {stack := a.stack.write k (default _), ..a}) $
  done )

def translate (funcs : Λ → stmt₃) : stmt₃ → stmt₂
| (TM3.stmt.move dir.left q) :=
  let q' := move dir.left (translate q) in
  branch (λ a s, a.dir = dir.left)
  ( move dir.left $
    write (λ a s, {dir := dir.left, ..a}) $
    translate q )
  ( move dir.left $
    translate q )
| (TM3.stmt.move dir.right q) :=
  move dir.right (translate q)
| (TM3.stmt.move_until d p q) :=
  branch (λ a s, p a.base s)
  ( translate q )
  ( goto (λ a s, TM3.stmt.move_until d p q) )
| (TM3.stmt.write f q) :=
  write (λ a s, {base := f a.base s, ..a}) $
  translate q
| (TM3.stmt.load f q) :=
  load (λ a, f a.base) $
  translate q
| (TM3.stmt.branch f q₁ q₂) :=
  branch (λ a, f a.base) (translate q₁) (translate q₂)
| (TM3.stmt.goto l) :=
  goto (λ a s, funcs (l a.base s))
| (TM3.stmt.push k f q) := push k f (translate q)
| (TM3.stmt.pop k f q) := pop k f (translate q)
| TM3.stmt.halt := halt

end

end TM3to2

end turing