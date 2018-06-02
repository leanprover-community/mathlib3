/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Define a sequence of simple machine languages, starting with Turing
machines and working up to more complex lanaguages based on
Wang B-machines.
-/
import data.finset data.sum data.finsupp data.array.lemmas
import data.pfun logic.relation

open relation

namespace turing

/-- A direction for the turing machine `move` command, either
  left or right. -/
@[derive decidable_eq]
inductive dir | left | right

namespace dir
def rev : dir → dir
| left := right
| right := left
end dir

def tape (Γ) := Γ × list Γ × list Γ

def tape.mk {Γ} [inhabited Γ] (l : list Γ) : tape Γ :=
(l.head, [], l.tail)

def tape.move {Γ} [inhabited Γ] : dir → tape Γ → tape Γ
| dir.left (a, L, R) := (L.head, L.tail, a :: R)
| dir.right (a, L, R) := (R.head, a :: L, R.tail)

def tape.write {Γ} (b : Γ) : tape Γ → tape Γ
| (a, LR) := (b, LR)

def tape.nth {Γ} [inhabited Γ] : tape Γ → ℤ → Γ
| (a, L, R) 0 := a
| (a, L, R) (n+1:ℕ) := R.inth n
| (a, L, R) -[1+ n] := L.inth n

theorem tape.move_left_nth {Γ} [inhabited Γ] :
  ∀ (T : tape Γ) (i : ℤ), (T.move dir.left).nth i = T.nth (i-1)
| (a, L, R) -[1+ n]      := by cases L; refl
| (a, L, R) 0           := by cases L; refl
| (a, L, R) 1           := rfl
| (a, L, R) ((n+1:ℕ)+1) := by rw add_sub_cancel; refl

theorem tape.move_right_nth {Γ} [inhabited Γ] :
  ∀ (T : tape Γ) (i : ℤ), (T.move dir.right).nth i = T.nth (i+1)
| (a, L, R) (n+1:ℕ)    := by cases R; refl
| (a, L, R) 0         := by cases R; refl
| (a, L, R) -1        := rfl
| (a, L, R) -[1+ n+1] := show _ = tape.nth _ (-[1+ n] - 1 + 1),
  by rw sub_add_cancel; refl

@[simp] theorem tape.write_self {Γ} : ∀ (T : tape Γ), T.write T.1 = T
| (a, LR) := rfl

theorem tape.write_nth {Γ} [inhabited Γ] (b : Γ) :
  ∀ (T : tape Γ) {i : ℤ}, (T.write b).nth i = if i = 0 then b else T.nth i
| (a, L, R) 0       := rfl
| (a, L, R) (n+1:ℕ) := rfl
| (a, L, R) -[1+ n] := rfl

def eval {σ} (f : σ → option σ) : σ → roption σ :=
pfun.fix (λ s, roption.some $
  match f s with none := sum.inl s | some s' := sum.inr s' end)

namespace TM0

section
parameters (Γ : Type*) [inhabited Γ] -- type of tape symbols
parameters (Λ : Type*) [inhabited Λ] -- type of "labels" or TM states

/-- A Turing machine "statement" is just a command to either move
  left or right, or write a symbol on the tape. -/
inductive stmt
| move {} : dir → stmt
| write {} : Γ → stmt

/-- A Post-Turing machine with symbol type `Γ` and label type `Λ`
  is a function which, given the current state `q : Λ` and
  the tape head `a : Γ`, either halts (returns `none`) or returns
  a new state `q' : Λ` and a `stmt` describing what to do,
  either a move left or right, or a write command.
  
  Both `Λ` and `Γ` are required to be inhabited; the default value
  for `Γ` is the "blank" tape value, and the default value of `Λ` is
  the initial state. -/
def machine := Λ → Γ → option (Λ × stmt)

/-- The configuration state of a Turing machine during operation
  consists of a label (machine state), and a tape, represented in
  the form `(a, L, R)` meaning the tape looks like `L.rev ++ [a] ++ R`
  with the machine currently reading the `a`. The lists are
  automatically extended with blanks as the machine moves around. -/
structure cfg :=
(q : Λ)
(tape : tape Γ)

/-- Execution semantics of the Turing machine. -/
def step (M : machine) : cfg → option cfg
| ⟨q, T⟩ := (M q T.1).map (λ ⟨q', a⟩, ⟨q',
  match a with
  | stmt.move d := T.move d
  | stmt.write a := T.write a
  end⟩)

parameters {Γ Λ}
/-- The statement `reaches M s₁ s₂` means that `s₂` is obtained
  starting from `s₁` after a finite number of steps from `s₂`. -/
def reaches (M : machine) : cfg → cfg → Prop :=
refl_trans_gen (λ a b, b ∈ step M a)

/-- Evaluate a Turing machine on initial input to a final state,
  if it terminates. -/
def eval (M : machine) (l : list Γ) : roption cfg :=
eval (step M) ⟨default Λ, tape.mk l⟩

/-- The raw definition of a Turing machine does not require that
  `Γ` and `Λ` are finite, and in practice we will be interested
  in the infinite `Λ` case. We recover instead a notion of
  "effectively finite" Turing machines, which only make use of a
  finite subset of their states. We say that a finset `S ⊆ Λ`
  supports a Turing machine `M` if `S` is closed under the
  transition function and contains the initial state. -/
def supports [fintype Γ] (M : machine) (S : finset Λ) :=
default Λ ∈ S ∧ ∀ {q a q' s}, (q', s) ∈ M q a → q ∈ S → q' ∈ S

theorem step_supports [fintype Γ] (M : machine) {S}
  (ss : supports M S) : ∀ {c c' : cfg},
  c' ∈ step M c → c.q ∈ S → c'.q ∈ S
| ⟨q, T⟩ c' h₁ h₂ := begin
  rcases option.map_eq_some'.1 h₁ with ⟨⟨q', a⟩, h, rfl⟩,
  exact ss.2 h h₂,
end

end

end TM0

namespace TM1

section
parameters (Γ : Type*) [inhabited Γ] -- Type of tape symbols
parameters (Λ : Type*) -- Type of function labels

/-- The TM1 model is a simplification of TM0 (Post-Turing model)
  in the direction of Wang B-machines. A machine is given by
  a `Λ` indexed set of procedures or functions. Each function
  has a body which is a `stmt`, which can either be a `move` or
  `write` command, a `branch` (switch based on the current tape value),
  a `goto` (call another function), or `halt`. Note that here
  most statements do not have labels; `goto` commands can only
  go to a new function. -/
inductive stmt
| move : dir → stmt → stmt
| write : Γ → stmt → stmt
| branch : (Γ → stmt) → stmt
| goto {} : Λ → stmt
| halt {} : stmt
open stmt

/-- The configuration of a TM1 machine is given by the currently
  evaluating statement, and the tape. -/
structure cfg :=
(q : stmt)
(tape : tape Γ)

parameters {Γ Λ}
/-- The semantics of TM1 evaluation. -/
def step (M : Λ → stmt) : cfg → option cfg
| ⟨q, T⟩ := begin
  induction q generalizing T,
  case TM1.stmt.move   : d q IH { exact IH (T.move d) },
  case TM1.stmt.write  : a q IH { exact IH (T.write a) },
  case TM1.stmt.branch : p IH   { exact IH T.1 T },
  case TM1.stmt.goto   : l      { exact some ⟨M l, T⟩ },
  case TM1.stmt.halt            { exact none }
end

def reaches (M : Λ → stmt) : cfg → cfg → Prop :=
refl_trans_gen (λ a b, b ∈ step M a)

variables [inhabited Λ]
def eval (M : Λ → stmt) (l : list Γ) : roption cfg :=
eval (step M) ⟨M (default _), tape.mk l⟩

variables [fintype Γ]
def supports_stmt (S : finset Λ) : stmt → Prop
| (move d q) := supports_stmt q
| (write a q) := supports_stmt q
| (branch f) := ∀ a, supports_stmt (f a)
| (goto l) := l ∈ S
| halt := true

/-- A set `S` of labels supports machine `M` if all the `goto`
  statements in the functions in `S` refer only to other functions
  in `S`. -/
def supports (M : Λ → stmt) (S : finset Λ) :=
default Λ ∈ S ∧ ∀ q ∈ S, supports_stmt S (M q)

local attribute [instance] classical.dec
noncomputable def stmts₁ : stmt → finset stmt
| Q@(move d q) := insert Q (stmts₁ q)
| Q@(write a q) := insert Q (stmts₁ q)
| Q@(branch f) := insert Q (finset.univ.bind (λ a, stmts₁ (f a)))
| Q@(goto l) := {Q}
| Q@halt := {Q}

theorem stmts₁_self {q} : q ∈ stmts₁ q :=
by cases q; simp [stmts₁]

theorem stmts₁_trans {q₁ q₂} :
  q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ :=
begin
  intros h₁₂ q₀ h₀₁,
  induction q₂; simp [stmts₁, finset.subset_iff] at h₁₂ ⊢,
  case TM1.stmt.move : d q IH {
    rcases h₁₂ with rfl | h₁₂,
    { simp [stmts₁] at h₀₁, rcases h₀₁ with rfl | h; simp * },
    { exact or.inr (IH h₁₂) } },
  case TM1.stmt.write : a q IH {
    rcases h₁₂ with rfl | h₁₂,
    { simp [stmts₁] at h₀₁, rcases h₀₁ with rfl | h; simp * },
    { exact or.inr (IH h₁₂) } },
  case TM1.stmt.branch : f IH {
    rcases h₁₂ with rfl | ⟨a, h₁₂⟩,
    { simp [stmts₁] at h₀₁,
      rcases h₀₁ with rfl | ⟨a, h⟩, {simp},
      exact or.inr ⟨_, h⟩ },
    { exact or.inr ⟨_, IH _ h₁₂⟩ } },
  case TM1.stmt.goto : l {
    subst h₁₂, simpa [stmts₁] using h₀₁ },
  case TM1.stmt.halt {
    subst h₁₂, simpa [stmts₁] using h₀₁ }
end

theorem stmts₁_supports_stmt_mono {S q₁ q₂}
  (h : q₁ ∈ stmts₁ q₂) (hs : supports_stmt S q₂) : supports_stmt S q₁ :=
begin
  induction q₂; simp [stmts₁, supports_stmt] at h hs,
  case TM1.stmt.move : d q IH {
    rcases h with rfl | h, exacts [hs, IH h hs] },
  case TM1.stmt.write : a q IH {
    rcases h with rfl | h, exacts [hs, IH h hs] },
  case TM1.stmt.branch : f IH {
    rcases h with rfl | ⟨a, h⟩, exacts [hs, IH a h (hs a)] },
  case TM1.stmt.goto : l { subst h, exact hs },
  case TM1.stmt.halt { subst h, trivial }
end

noncomputable def stmts
  (M : Λ → stmt) (S : finset Λ) : finset stmt :=
S.bind (λ q, stmts₁ (M q))

theorem stmts_trans {M : Λ → stmt} {S q₁ q₂}
  (h₁ : q₁ ∈ stmts₁ q₂) : q₂ ∈ stmts M S → q₁ ∈ stmts M S :=
by simp [stmts]; exact λ l ls h₂, ⟨_, ls, stmts₁_trans h₂ h₁⟩

theorem stmts_supports_stmt {M : Λ → stmt} {S q}
  (ss : supports M S) : q ∈ stmts M S → supports_stmt S q :=
by simp [stmts]; exact
λ l ls h, stmts₁_supports_stmt_mono h (ss.2 _ ls)

theorem step_supports (M : Λ → stmt) {S}
  (ss : supports M S) : ∀ {c c' : cfg},
  c' ∈ step M c → c.q ∈ stmts M S → c'.q ∈ stmts M S
| ⟨q₁, T⟩ c' h₁ h₂ := begin
  rcases finset.mem_bind.1 h₂ with ⟨l, hl, h⟩,
  change q₁ ∈ stmts₁ (M l) at h,
  suffices : q₁ ∈ stmts₁ (M l) → supports_stmt S (M l) →
    c'.q ∈ stmts₁ (M l) ∨ c'.q ∈ stmts M S,
  from (or_iff_right_of_imp
    (λ h, finset.mem_bind.2 ⟨_, hl, h⟩)).1 (this h (ss.2 _ hl)),
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
parameters {Γ : Type*} [inhabited Γ]
parameters {Λ : Type*} [inhabited Λ]

local notation `stmt₁` := TM1.stmt Γ Λ
local notation `cfg₁` := TM1.cfg Γ Λ
local notation `stmt₀` := TM0.stmt Γ

parameters (M : Λ → stmt₁)
include M

def Λ' := stmt₁
instance : inhabited Λ' := ⟨M (default _)⟩

open TM0.stmt

def tr' : Λ' → Γ → option (Λ' × stmt₀)
| (TM1.stmt.move d q) s := some (q, move d)
| (TM1.stmt.write a q) s := some (q, write a)
| (TM1.stmt.branch f) s := tr' (f s) s
| (TM1.stmt.goto l) s := some (M l, write s)
| TM1.stmt.halt s := none

local notation `cfg₀` := TM0.cfg Γ Λ'

def tr : TM0.machine Γ Λ' := tr'

def tr_cfg : cfg₁ → cfg₀ | ⟨q, T⟩ := ⟨q, T⟩

theorem tr_reaches {c₁ c₂} : TM1.reaches M c₁ c₂ →
  TM0.reaches tr (tr_cfg c₁) (tr_cfg c₂) :=
refl_trans_gen_lift' tr_cfg $ λ ⟨q₁, T⟩ c₂ h, begin
  simp [tr_cfg],
  refine refl_trans_gen.cases_head_iff.2 (or.inr _),
  revert h, induction q₁ generalizing T; intro h,
  case TM1.stmt.move : d q IH {
    exact ⟨_, rfl, refl_trans_gen.cases_head_iff.2 (or.inr (IH _ h))⟩ },
  case TM1.stmt.write : a q IH {
    exact ⟨_, rfl, refl_trans_gen.cases_head_iff.2 (or.inr (IH _ h))⟩ },
  case TM1.stmt.branch : f IH { exact IH _ _ h },
  case TM1.stmt.goto : l {
    cases h, refine ⟨_, rfl, _⟩,
    simp [TM0.step], refl },
  case TM1.stmt.halt { cases h }
end

variables [fintype Γ]
local attribute [instance] classical.dec
local attribute [simp] TM1.stmts₁_self
theorem tr_supports {S} (ss : TM1.supports M S) :
  TM0.supports tr (TM1.stmts M S) :=
⟨finset.mem_bind.2 ⟨_, ss.1, TM1.stmts₁_self⟩, λ q a q' s h₁ h₂, begin
  have := TM1.stmts_supports_stmt ss h₂,
  revert this, induction q; intro hs,
  case TM1.stmt.move : d q {
    cases h₁, refine TM1.stmts_trans _ h₂, simp [TM1.stmts₁] },
  case TM1.stmt.write : b q {
    cases h₁, refine TM1.stmts_trans _ h₂, simp [TM1.stmts₁] },
  case TM1.stmt.branch : f IH {
    refine IH _ h₁ (TM1.stmts_trans _ h₂) (hs a),
    simp [TM1.stmts₁], exact or.inr ⟨_, TM1.stmts₁_self⟩ },
  case TM1.stmt.goto : l {
    cases h₁, exact finset.mem_bind.2 ⟨_, hs, TM1.stmts₁_self⟩ },
  case TM1.stmt.halt { cases h₁ }
end⟩

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

structure cfg :=
(q : stmt)
(var : σ)
(tape : tape Γ)

parameters {Γ Λ σ}
def step_aux (M : Λ → stmt) :
  stmt → σ → tape Γ → option cfg
| (move d q) v T := step_aux q v (T.move d)
| (move_until d f q) v T :=
  if f T.1 v then some ⟨q, v, T⟩ else some ⟨move_until d f q, v, T.move d⟩
| (write f q) v T := step_aux q v (T.write (f T.1 v))
| (load f q) v T := step_aux q (f T.1 v) T
| (branch f q₁ q₂) v T :=
  if f T.1 v then step_aux q₁ v T else step_aux q₂ v T
| (goto f) v T := some ⟨M (f T.1 v), v, T⟩
| halt v T := none

def step (M : Λ → stmt) : cfg → option cfg
| ⟨q, v, T⟩ := step_aux M q v T

def reaches (M : Λ → stmt) : cfg → cfg → Prop :=
refl_trans_gen (λ a b, b ∈ step M a)

theorem move_until_left_reaches
  (M : Λ → stmt) (f : Γ → σ → bool) (q v) (L₁ R₁ L₂ : list Γ)
  {a₁ a₂} {A : list Γ}
  (H₁ : L₁ ++ [a₁] = L₂ ++ a₂ :: A)
  (H₂ : ∀ a ∈ A, ¬ f a v) (H₃ : f a₂ v) :
  reaches M
    ⟨move_until dir.left f q, v, (a₁, L₁.reverse, R₁)⟩
    ⟨q, v, (a₂, L₂.reverse, A ++ R₁)⟩ :=
begin
  suffices : ∀ L₂ {a₂ R₁} (H₁ : L₁ ++ [a₁] = L₂ ++ a₂ :: A), reaches M
    ⟨move_until dir.left f q, v, (a₁, L₁.reverse, R₁)⟩
    ⟨move_until dir.left f q, v, (a₂, L₂.reverse, A ++ R₁)⟩,
  { refine refl_trans_gen.tail _ (this _ H₁) _,
    simp [step, step_aux, H₃] },
  clear H₁ H₃, simp at H₂,
  induction A with a A IH; intros L₂ a₂ R₁ H₁,
  { cases list.append_inj_left' H₁ rfl,
    cases (list.append_right_inj _).1 H₁,
    exact refl_trans_gen.refl },
  { simp at H₂,
    refine refl_trans_gen.tail _
      (IH H₂.2 (L₂ ++ [a₂]) (by simp [H₁])) _,
    simp [step, step_aux, H₂.1], refl }
end

theorem move_until_right_reaches
  (M : Λ → stmt) (f : Γ → σ → bool) (q v) (L₁ R₁ R₂ : list Γ)
  {a₁ a₂} {A : list Γ}
  (H₁ : a₁ :: R₁ = A ++ a₂ :: R₂)
  (H₂ : ∀ a ∈ A, ¬ f a v) (H₃ : f a₂ v) :
  reaches M
    ⟨move_until dir.right f q, v, (a₁, L₁.reverse, R₁)⟩
    ⟨q, v, (a₂, (L₁ ++ A).reverse, R₂)⟩ :=
begin
  suffices : ∀ (A R₂ : list Γ) {a₂} {L₁ : list Γ}
    (H₁ : (a₁ :: R₁ : list Γ) = A.reverse ++ a₂ :: R₂)
    (H₂ : ∀ (a : Γ), a ∈ A → f a v = ff), reaches M
    ⟨move_until dir.right f q, v, (a₁, L₁.reverse, R₁)⟩
    ⟨move_until dir.right f q, v, (a₂, A ++ L₁.reverse, R₂)⟩,
  { simp,
    refine refl_trans_gen.tail _
      (this A.reverse _ (by simpa using H₁) (by simpa using H₂)) _,
    simp [step, step_aux, H₃] },
  clear H₁ H₂ H₃ A, intro A,
  induction A with a A IH; intros R₂ a₂ L₁ H₁ H₂,
  { cases H₁, exact refl_trans_gen.refl },
  { simp at H₁ H₂,
    refine refl_trans_gen.tail _ (IH _ H₁ H₂.2) _,
    simp [step, step_aux, H₂.1], refl }
end

variables [inhabited Λ] [inhabited σ]
def eval (M : Λ → stmt) (l : list Γ) : roption cfg :=
eval (step M) ⟨M (default _), default _, tape.mk l⟩

variables [fintype Γ] [fintype σ]
def supports_stmt (S : finset Λ) : stmt → Prop
| (move d q) := supports_stmt q
| (move_until d f q) := supports_stmt q
| (write f q) := supports_stmt q
| (load f q) := supports_stmt q
| (branch f q₁ q₂) := supports_stmt q₁ ∧ supports_stmt q₂
| (goto l) := ∀ a v, l a v ∈ S
| halt := true

def supports (M : Λ → stmt) (S : finset Λ) :=
default Λ ∈ S ∧ ∀ q ∈ S, supports_stmt S (M q)

local attribute [instance] classical.dec
noncomputable def stmts₁ : stmt → finset stmt
| Q@(move d q) := insert Q (stmts₁ q)
| Q@(move_until d f q) := insert Q (stmts₁ q)
| Q@(write f q) := insert Q (stmts₁ q)
| Q@(load f q) := insert Q (stmts₁ q)
| Q@(branch f q₁ q₂) := insert Q (stmts₁ q₁ ∪ stmts₁ q₂)
| Q@(goto l) := {Q}
| Q@halt := {Q}

theorem stmts₁_self {q} : q ∈ stmts₁ q :=
by cases q; simp [stmts₁]

theorem stmts₁_trans {q₁ q₂} :
  q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ :=
begin
  intros h₁₂ q₀ h₀₁,
  induction q₂ with _ q IH _ _ q IH _ q IH _ q IH;
    simp [stmts₁, finset.subset_iff] at h₁₂ ⊢,
  iterate 4 {
    rcases h₁₂ with rfl | h₁₂,
    { simp [stmts₁] at h₀₁, rcases h₀₁ with rfl | h; simp * },
    { exact or.inr (IH h₁₂) } },
  case TM2.stmt.branch : f q₁ q₂ IH₁ IH₂ {
    rcases h₁₂ with rfl | h₁₂ | h₁₂,
    { simp [stmts₁] at h₀₁, rcases h₀₁ with rfl | h; simp * },
    { simp [IH₁ h₁₂] }, { simp [IH₂ h₁₂] } },
  case TM2.stmt.goto : l {
    subst h₁₂, simpa [stmts₁] using h₀₁ },
  case TM2.stmt.halt {
    subst h₁₂, simpa [stmts₁] using h₀₁ }
end

theorem stmts₁_supports_stmt_mono {S q₁ q₂}
  (h : q₁ ∈ stmts₁ q₂) (hs : supports_stmt S q₂) : supports_stmt S q₁ :=
begin
  induction q₂ with _ q IH _ _ q IH _ q IH _ q IH;
    simp [stmts₁, supports_stmt] at h hs,
  iterate 4 { rcases h with rfl | h; [exact hs, exact IH h hs] },
  case TM2.stmt.branch : f q₁ q₂ IH₁ IH₂ {
    rcases h with rfl | h | h, exacts [hs, IH₁ h hs.1, IH₂ h hs.2] },
  case TM2.stmt.goto : l { subst h, exact hs },
  case TM2.stmt.halt { subst h, trivial }
end

noncomputable def stmts
  (M : Λ → stmt) (S : finset Λ) : finset stmt :=
S.bind (λ q, stmts₁ (M q))

theorem stmts_trans {M : Λ → stmt} {S q₁ q₂}
  (h₁ : q₁ ∈ stmts₁ q₂) : q₂ ∈ stmts M S → q₁ ∈ stmts M S :=
by simp [stmts]; exact λ l ls h₂, ⟨_, ls, stmts₁_trans h₂ h₁⟩

theorem stmts_supports_stmt {M : Λ → stmt} {S q}
  (ss : supports M S) : q ∈ stmts M S → supports_stmt S q :=
by simp [stmts]; exact
λ l ls h, stmts₁_supports_stmt_mono h (ss.2 _ ls)

theorem step_supports (M : Λ → stmt) {S}
  (ss : supports M S) : ∀ {c c' : cfg},
  c' ∈ step M c → c.q ∈ stmts M S → c'.q ∈ stmts M S
| ⟨q₁, v, T⟩ c' h₁ h₂ := begin
  simp [step] at h₁,
  rcases finset.mem_bind.1 h₂ with ⟨l, hl, h⟩,
  change q₁ ∈ stmts₁ (M l) at h,
  suffices : q₁ ∈ stmts₁ (M l) → supports_stmt S (M l) →
    c'.q ∈ stmts₁ (M l) ∨ c'.q ∈ stmts M S,
  from (or_iff_right_of_imp
    (λ h, finset.mem_bind.2 ⟨_, hl, h⟩)).1 (this h (ss.2 _ hl)),
  clear h h₂,
  induction M l with _ q IH _ _ q IH _ q IH _ q IH generalizing q₁ v T;
    intros h hs; simp [stmts₁] at h ⊢,
  case TM2.stmt.move_until : d f q IH {
    rcases h with rfl | h,
    { revert h₁, simp [step_aux], split_ifs; intro,
      { cases h₁, exact or.inl (or.inr stmts₁_self) },
      { cases h₁, exact or.inl (or.inl rfl) } },
    { exact (IH q₁ _ _ h₁ h hs).imp_left or.inr } },
  iterate 3 {
    rcases h with rfl | h,
    { exact (IH q _ _ h₁ stmts₁_self hs).imp_left or.inr },
    { exact (IH q₁ _ _ h₁ h hs).imp_left or.inr } },
  case TM2.stmt.branch : f q₁' q₂' IH₁ IH₂ {
    rcases h with rfl | h | h,
    { revert h₁, simp [step_aux], split_ifs; intro,
      { exact (IH₁ _ _ _ h₁ stmts₁_self hs.1).imp_left (λ h, or.inr (or.inl h)) },
      { exact (IH₂ _ _ _ h₁ stmts₁_self hs.2).imp_left (λ h, or.inr (or.inr h)) } },
    { exact (IH₁ _ _ _ h₁ h hs.1).imp_left (λ h, or.inr (or.inl h)) },
    { exact (IH₂ _ _ _ h₁ h hs.2).imp_left (λ h, or.inr (or.inr h)) } },
  case TM2.stmt.goto : l {
    subst h, cases h₁,
    simp [stmts],
    exact or.inr ⟨_, hs _ _, stmts₁_self⟩ },
  case TM2.stmt.halt { subst h, cases h₁ }
end

end

end TM2

namespace TM2to1

section
parameters {Γ : Type*} [inhabited Γ]
parameters {Λ : Type*} [inhabited Λ]
parameters {σ : Type*} [inhabited σ]

local notation `stmt₂` := TM2.stmt Γ Λ σ
local notation `cfg₂` := TM2.cfg Γ Λ σ

parameters (M : Λ → stmt₂)
include M

def Λ' := stmt₂ × σ
instance : inhabited Λ' := ⟨(M (default _), default _)⟩

local notation `stmt₁` := TM1.stmt Γ Λ'
local notation `cfg₁` := TM1.cfg Γ Λ'

open TM1.stmt

def tr' : stmt₂ → σ → stmt₁
| (TM2.stmt.move d q) s := move d (tr' q s)
| (TM2.stmt.move_until d p q) s :=
  branch $ λ a,
  if p a s then goto (q, s) else
  move d $ goto (TM2.stmt.move_until d p q, s)
| (TM2.stmt.write f q) s :=
  branch $ λ a, write (f a s) $ tr' q s
| (TM2.stmt.load f q) s :=
  branch $ λ a, tr' q (f a s)
| (TM2.stmt.branch f q₁ q₂) s :=
  branch $ λ a, if f a s then tr' q₁ s else tr' q₂ s
| (TM2.stmt.goto l) s :=
  branch $ λ a, goto (M (l a s), s)
| TM2.stmt.halt s := halt

def tr : Λ' → stmt₁
| (q, s) := tr' q s

def tr_cfg : cfg₂ → cfg₁
| ⟨q, v, T⟩ := ⟨tr (q, v), T⟩

theorem tr_reaches {c₁ c₂} : TM2.reaches M c₁ c₂ →
  TM1.reaches tr (tr_cfg c₁) (tr_cfg c₂) :=
refl_trans_gen_lift' tr_cfg $ λ ⟨q₁, v, T⟩ c₂ h, begin
  simp [tr_cfg, TM2.step] at h ⊢,
  refine refl_trans_gen.cases_head_iff.2 (or.inr _),
  revert h, induction q₁ generalizing v T; intro h,
  case TM2.stmt.move : d q IH { exact IH _ _ h },
  case TM2.stmt.move_until : d f q IH {
    rw (_ : TM1.step _ _ = TM1.step _ ⟨ite _ _ _, _⟩); [skip, refl],
    revert h, simp [TM2.step_aux]; split_ifs;
    { intro h', subst h', exact ⟨_, rfl, by refl⟩ } },
  case TM2.stmt.write : a q IH { exact IH _ _ h },
  case TM2.stmt.load : f q IH { exact IH _ _ h },
  case TM2.stmt.branch : f q₁ q₂ IH₁ IH₂ {
    rw (_ : TM1.step _ _ = TM1.step _ ⟨ite _ _ _, _⟩); [skip, refl],
    revert h, simp [TM2.step_aux]; split_ifs; intro h',
    { exact IH₁ _ _ h' }, { exact IH₂ _ _ h' } },
  case TM2.stmt.goto : l { cases h, exact ⟨_, rfl, by refl⟩ },
  case TM2.stmt.halt { cases h }
end

variables [fintype Γ] [fintype σ]
noncomputable def tr_supp (S : finset Λ) : finset Λ' :=
(TM2.stmts M S).product finset.univ

local attribute [instance] classical.dec
local attribute [simp] TM2.stmts₁_self
theorem tr_supports {S} (ss : TM2.supports M S) :
  TM1.supports tr (tr_supp S) :=
⟨by simp [tr_supp, TM2.stmts]; exact ⟨_, ss.1, TM2.stmts₁_self⟩,
λ ⟨q, v⟩ h, begin
  simp [tr_supp] at h,
  have := TM2.stmts_supports_stmt ss h, revert this,
  induction q generalizing v; intro hs,
  case TM2.stmt.move : d q IH {
    exact IH (TM2.stmts_trans (by simp [TM2.stmts₁]) h) _ hs },
  case TM2.stmt.move_until : d f q IH {
    intro a, simp [tr, tr'],
    split_ifs; simpa [TM1.supports_stmt, tr_supp],
    exact TM2.stmts_trans (by simp [TM2.stmts₁]) h },
  case TM2.stmt.write : b q IH {
    exact λ _, IH (TM2.stmts_trans (by simp [TM2.stmts₁]) h) _ hs },
  case TM2.stmt.load : f q IH {
    exact λ _, IH (TM2.stmts_trans (by simp [TM2.stmts₁]) h) _ hs },
  case TM2.stmt.branch : f q₁ q₂ IH₁ IH₂ {
    intro a, simp [tr, tr'], split_ifs,
    { exact IH₁ (TM2.stmts_trans (by simp [TM2.stmts₁]) h) _ hs.1 },
    { exact IH₂ (TM2.stmts_trans (by simp [TM2.stmts₁]) h) _ hs.2 } },
  case TM2.stmt.goto : l {
    intro a, simp [tr, tr', TM1.supports_stmt, tr_supp, TM2.stmts],
    exact ⟨_, hs a v, TM2.stmts₁_self⟩ },
  case TM2.stmt.halt { trivial }
end⟩

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
| push {} : fin K → (σ → Γ) → stmt → stmt
| pop {} : fin K → (σ → option Γ → σ) → stmt → stmt
| branch : (Γ → σ → bool) → stmt → stmt → stmt
| goto {} : (Γ → σ → Λ) → stmt
| halt {} : stmt
open stmt

structure cfg :=
(q : stmt)
(var : σ)
(stk : array K (list Γ))
(tape : tape Γ)

parameters {Γ Λ σ K}
def step_aux (M : Λ → stmt) :
  stmt → σ → array K (list Γ) → tape Γ → option cfg
| (move d q)         v S T := step_aux q v S (T.move d)
| (move_until d f q) v S T :=
  if f T.1 v then some ⟨q, v, S, T⟩ else
    some ⟨move_until d f q, v, S, T.move d⟩
| (write f q)        v S T := step_aux q v S (T.write (f T.1 v))
| (load f q)         v S T := step_aux q (f T.1 v) S T
| (push k f q)       v S T :=
  step_aux q v (S.write k (f v :: S.read k)) T
| (pop k f q)        v S T :=
  step_aux q (f v (S.read k).head') (S.write k (S.read k).tail) T
| (branch f q₁ q₂)   v S T :=
  if f T.1 v then step_aux q₁ v S T else step_aux q₂ v S T
| (goto f)           v S T := some ⟨M (f T.1 v), v, S, T⟩
| halt               v S T := none

def step (M : Λ → stmt) : cfg → option cfg
| ⟨q, v, S, T⟩ := step_aux M q v S T

def reaches (M : Λ → stmt) : cfg → cfg → Prop :=
refl_trans_gen (λ a b, b ∈ step M a)

variables [inhabited Λ] [inhabited σ]
def eval (M : Λ → stmt) (l : list Γ) : roption cfg :=
eval (step M) ⟨M (default _), default _, default _, tape.mk l⟩

variables [fintype Γ] [fintype σ]
def supports_stmt (S : finset Λ) : stmt → Prop
| (move d q)         := supports_stmt q
| (move_until d f q) := supports_stmt q
| (write f q)        := supports_stmt q
| (load f q)         := supports_stmt q
| (push k f q)       := supports_stmt q
| (pop k f q)        := supports_stmt q
| (branch f q₁ q₂)   := supports_stmt q₁ ∧ supports_stmt q₂
| (goto l)           := ∀ a v, l a v ∈ S
| halt               := true

def supports (M : Λ → stmt) (S : finset Λ) :=
default Λ ∈ S ∧ ∀ q ∈ S, supports_stmt S (M q)

local attribute [instance] classical.dec
noncomputable def stmts₁ : stmt → finset stmt
| Q@(move d q)         := insert Q (stmts₁ q)
| Q@(move_until d f q) := insert Q (stmts₁ q)
| Q@(write f q)        := insert Q (stmts₁ q)
| Q@(load f q)         := insert Q (stmts₁ q)
| Q@(push k f q)       := insert Q (stmts₁ q)
| Q@(pop k f q)        := insert Q (stmts₁ q)
| Q@(branch f q₁ q₂)   := insert Q (stmts₁ q₁ ∪ stmts₁ q₂)
| Q@(goto l)           := {Q}
| Q@halt               := {Q}

theorem stmts₁_self {q} : q ∈ stmts₁ q :=
by cases q; simp [stmts₁]

theorem stmts₁_trans {q₁ q₂} :
  q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ :=
begin
  intros h₁₂ q₀ h₀₁,
  induction q₂ with _ q IH _ _ q IH _ q IH _ q IH _ _ q IH _ _ q IH;
    simp [stmts₁, finset.subset_iff] at h₁₂ ⊢,
  iterate 6 {
    rcases h₁₂ with rfl | h₁₂,
    { simp [stmts₁] at h₀₁, rcases h₀₁ with rfl | h; simp * },
    { exact or.inr (IH h₁₂) } },
  case TM3.stmt.branch : f q₁ q₂ IH₁ IH₂ {
    rcases h₁₂ with rfl | h₁₂ | h₁₂,
    { simp [stmts₁] at h₀₁, rcases h₀₁ with rfl | h; simp * },
    { simp [IH₁ h₁₂] }, { simp [IH₂ h₁₂] } },
  case TM3.stmt.goto : l {
    subst h₁₂, simpa [stmts₁] using h₀₁ },
  case TM3.stmt.halt {
    subst h₁₂, simpa [stmts₁] using h₀₁ }
end

theorem stmts₁_supports_stmt_mono {S q₁ q₂}
  (h : q₁ ∈ stmts₁ q₂) (hs : supports_stmt S q₂) : supports_stmt S q₁ :=
begin
  induction q₂ with _ q IH _ _ q IH _ q IH _ q IH _ _ q IH _ _ q IH;
    simp [stmts₁, supports_stmt] at h hs,
  iterate 6 { rcases h with rfl | h; [exact hs, exact IH h hs] },
  case TM3.stmt.branch : f q₁ q₂ IH₁ IH₂ {
    rcases h with rfl | h | h, exacts [hs, IH₁ h hs.1, IH₂ h hs.2] },
  case TM3.stmt.goto : l { subst h, exact hs },
  case TM3.stmt.halt { subst h, trivial }
end

noncomputable def stmts
  (M : Λ → stmt) (S : finset Λ) : finset stmt :=
S.bind (λ q, stmts₁ (M q))

theorem stmts_trans {M : Λ → stmt} {S q₁ q₂}
  (h₁ : q₁ ∈ stmts₁ q₂) : q₂ ∈ stmts M S → q₁ ∈ stmts M S :=
by simp [stmts]; exact λ l ls h₂, ⟨_, ls, stmts₁_trans h₂ h₁⟩

theorem stmts_supports_stmt {M : Λ → stmt} {S q}
  (ss : supports M S) : q ∈ stmts M S → supports_stmt S q :=
by simp [stmts]; exact
λ l ls h, stmts₁_supports_stmt_mono h (ss.2 _ ls)

theorem step_supports (M : Λ → stmt) {S}
  (ss : supports M S) : ∀ {c c' : cfg},
  c' ∈ step M c → c.q ∈ stmts M S → c'.q ∈ stmts M S
| ⟨q₁, v, ST, T⟩ c' h₁ h₂ := begin
  simp [step] at h₁,
  rcases finset.mem_bind.1 h₂ with ⟨l, hl, h⟩,
  change q₁ ∈ stmts₁ (M l) at h,
  suffices : q₁ ∈ stmts₁ (M l) → supports_stmt S (M l) →
    c'.q ∈ stmts₁ (M l) ∨ c'.q ∈ stmts M S,
  from (or_iff_right_of_imp
    (λ h, finset.mem_bind.2 ⟨_, hl, h⟩)).1 (this h (ss.2 _ hl)),
  clear h h₂,
  induction M l with _ q IH _ _ q IH _ q IH _ q IH _ _ q IH _ _ q IH
    generalizing q₁ v ST T;
    intros h hs; simp [stmts₁] at h ⊢,
  case TM3.stmt.move_until : d f q IH {
    rcases h with rfl | h,
    { revert h₁, simp [step_aux], split_ifs; intro,
      { cases h₁, exact or.inl (or.inr stmts₁_self) },
      { cases h₁, exact or.inl (or.inl rfl) } },
    { exact (IH q₁ _ _ _ h₁ h hs).imp_left or.inr } },
  iterate 5 {
    rcases h with rfl | h,
    { exact (IH q _ _ _ h₁ stmts₁_self hs).imp_left or.inr },
    { exact (IH q₁ _ _ _ h₁ h hs).imp_left or.inr } },
  case TM3.stmt.branch : f q₁' q₂' IH₁ IH₂ {
    rcases h with rfl | h | h,
    { revert h₁, simp [step_aux], split_ifs; intro,
      { exact (IH₁ _ _ _ _ h₁ stmts₁_self hs.1).imp_left (λ h, or.inr (or.inl h)) },
      { exact (IH₂ _ _ _ _ h₁ stmts₁_self hs.2).imp_left (λ h, or.inr (or.inr h)) } },
    { exact (IH₁ _ _ _ _ h₁ h hs.1).imp_left (λ h, or.inr (or.inl h)) },
    { exact (IH₂ _ _ _ _ h₁ h hs.2).imp_left (λ h, or.inr (or.inr h)) } },
  case TM3.stmt.goto : l {
    subst h, cases h₁,
    simp [stmts],
    exact or.inr ⟨_, hs _ _, stmts₁_self⟩ },
  case TM3.stmt.halt { subst h, cases h₁ }
end

end

end TM3

namespace TM3to2

section
parameters {Γ : Type*} [inhabited Γ]
parameters {Λ : Type*} [inhabited Λ]
parameters {σ : Type*} [inhabited σ]
parameters {K : ℕ}

local notation `stmt₃` := TM3.stmt Γ Λ σ K
local notation `cfg₃` := TM3.cfg Γ Λ σ K

@[derive decidable_eq]
inductive stackel
| val : Γ → stackel
| bottom {}
| top {}

instance stackel.inhabited : inhabited stackel :=
⟨stackel.val (default _)⟩

def stackel.is_bottom : stackel → bool
| stackel.bottom := tt
| _ := ff 

def stackel.is_top : stackel → bool
| stackel.top := tt
| _ := ff 

def stackel.get : stackel → option Γ
| (stackel.val a) := some a
| _ := none

def stack_val (l : list Γ) : ℤ → stackel :=
tape.nth (stackel.bottom, [], l.map stackel.val ++ [stackel.top])

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
structure Γ' :=
(base : Γ)
(stack : array K stackel)
(left : bool)
(last_pos : bool)

instance Γ'.inhabited : inhabited Γ' :=
⟨⟨default _, default _, ff, ff⟩⟩

def Γ'.write_stack (a : Γ') (k : fin K) (v : stackel) : Γ' :=
{stack := a.stack.write k v, ..a}

def Γ'_equiv : Γ' ≃ (Γ × array K stackel × bool × bool) :=
⟨λ ⟨a, b, c, d⟩, ⟨a, b, c, d⟩, λ ⟨a, b, c, d⟩, ⟨a, b, c, d⟩,
 λ ⟨a, b, c, d⟩, rfl, λ ⟨a, b, c, d⟩, rfl⟩

section
variable [fintype Γ]

instance stackel.fintype : fintype stackel :=
fintype.of_equiv _ stackel_equiv.symm

instance Γ'.fintype : fintype Γ' :=
fintype.of_equiv _ Γ'_equiv.symm

end

parameters (M : Λ → stmt₃)
include M

def Λ' := stmt₃
instance : inhabited Λ' := ⟨M (default _)⟩

local notation `stmt₂` := TM2.stmt Γ' Λ' σ
local notation `cfg₂` := TM2.cfg Γ' Λ' σ

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
branch (λ a s, a.left) (go dir.left) (go dir.right)

def push (k : fin K) (f : σ → Γ) (q : stmt₂) : stmt₂ :=
at_stack k q $ λ done,
write (λ a s, a.write_stack k (stackel.val (f s))) $
move dir.right $
write (λ a s, a.write_stack k stackel.top) $
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
( write (λ a s, a.write_stack k stackel.top) $
  move dir.right $
  write (λ a s, a.write_stack k (default _)) $
  done )

def tr : Λ' → stmt₂
| (TM3.stmt.move dir.left q) :=
  let q' := move dir.left (tr q) in
  branch (λ a s, a.left)
  ( move dir.left $
    write (λ a s, {left := tt, ..a}) $
    tr q )
  ( move dir.left $
    tr q )
| (TM3.stmt.move dir.right q) :=
  move dir.right (tr q)
| (TM3.stmt.move_until d p q) :=
  branch (λ a s, p a.base s)
  ( tr q )
  ( goto (λ a s, TM3.stmt.move_until d p q) )
| (TM3.stmt.write f q) :=
  write (λ a s, {base := f a.base s, ..a}) $
  tr q
| (TM3.stmt.load f q) :=
  load (λ a, f a.base) $
  tr q
| (TM3.stmt.branch f q₁ q₂) :=
  branch (λ a, f a.base) (tr q₁) (tr q₂)
| (TM3.stmt.goto l) :=
  goto (λ a s, M (l a.base s))
| (TM3.stmt.push k f q) := push k f (tr q)
| (TM3.stmt.pop k f q) := pop k f (tr q)
| TM3.stmt.halt := halt

def tr_tape (S : array K (list Γ))
  (T : tape Γ) (T' : tape Γ') (k : ℤ) : Prop :=
∀ i : ℤ, T'.nth (i+k) = {
  base := T.nth (i+k),
  left := -(T'.2.1.length : ℤ) ≤ i ∧ i ≤ 0,
  last_pos := ff,
  stack := ⟨λ k, stack_val (S.read k) i⟩}

inductive tr_cfg : cfg₃ → cfg₂ → Prop
| mk {q v S T T' k} : tr_tape S T T' k →
  tr_cfg ⟨q, v, S, T⟩ ⟨tr q, v, T'⟩

/-
theorem tr_reaches {c₁ c₂} (h : TM3.reaches M c₁ c₂) :
  ∀ {t₁}, tr_cfg c₁ t₁ → ∃ t₂, tr_cfg c₂ t₂ ∧ TM2.reaches tr t₁ t₂ :=
begin
  apply refl_trans_gen.head_induction_on h,
  { exact λ t₁ h₂, ⟨t₁, h₂, refl_trans_gen.refl⟩ },
  intros c₁' c₂' h' H IH t₁' h₂,
  suffices : ∃ t₂ t₃, t₂ ∈ TM2.step (tr M) t₁' ∧
    tr_cfg c₂' t₃ ∧ TM2.reaches (tr M) t₂ t₃,
  { rcases this with ⟨t₃, t₄, h₁₃, ct, r₃₄⟩,
    rcases IH ct with ⟨t₂, ct₂, r₄₂⟩,
    exact ⟨t₂, ct₂, refl_trans_gen.head h₁₃ $ refl_trans_gen.trans r₃₄ r₄₂⟩ },
  cases h₂ with q v S T T' k hT,
  clear H IH h c₁ c₂ h₂, simp [TM2.step, TM3.step] at h' ⊢,
  induction q generalizing v S T T' k hT,
  case TM3.stmt.move : d q IH {
    cases d,
    { simp [TM3.step, TM3.step_aux, tr, TM2.step, TM2.step_aux] at h' ⊢,
      let TL := T'.move dir.left,
      let T₂ := TL.write {left := if T'.1.left then tt else TL.1.left, .. TL.1},
      suffices : tr_tape M S (T.move dir.left) T₂ k,
      { convert IH this h', funext, congr,
        cases e : T'.1.left; simp [T₂, TL, e],
        rcases T'.move dir.left with ⟨⟨⟩⟩, refl },
      intro i,
      by_cases i0 : i + k = 0,
      { simp [i0, T₂] }
       }
  }
end
-/

variables [fintype Γ] [fintype σ]
@[simp] noncomputable def tr_supp (S : finset Λ) : finset Λ' := TM3.stmts M S

local attribute [instance] classical.dec
local attribute [simp] TM3.stmts₁_self
theorem at_stack_supports {S k q} {f : stmt₂ → stmt₂}
  (hf : ∀ q, TM2.supports_stmt S q → TM2.supports_stmt S (f q))
  (hq : TM2.supports_stmt S (tr q)) : TM2.supports_stmt S (at_stack k (tr q) f) :=
by split; exact hf _ (by exact hq)

theorem tr_supports {S} (ss : TM3.supports M S) :
  TM2.supports tr (tr_supp S) :=
⟨finset.mem_bind.2 ⟨_, ss.1, TM3.stmts₁_self⟩,
λ q h, begin
  have := TM3.stmts_supports_stmt ss h, revert this,
  induction q; intro hs,
  case TM3.stmt.move : d q IH {
    have IH := IH (TM3.stmts_trans (by simp [TM3.stmts₁]) h) hs,
    cases d, exacts [⟨IH, IH⟩, IH] },
  case TM3.stmt.move_until : d f q IH {
    have IH := IH (TM3.stmts_trans (by simp [TM3.stmts₁]) h) hs,
    exact ⟨IH, λ a v, h⟩ },
  iterate 2 { exact q_ih (TM3.stmts_trans (by simp [TM3.stmts₁]) h) hs },
  case TM3.stmt.push : k f q IH {
    have IH := IH (TM3.stmts_trans (by simp [TM3.stmts₁]) h) hs,
    exact at_stack_supports M (λ q h, h) IH },
  case TM3.stmt.pop : k f q IH {
    have IH := IH (TM3.stmts_trans (by simp [TM3.stmts₁]) h) hs,
    exact at_stack_supports M (λ q h, ⟨h, h⟩) IH },
  case TM3.stmt.branch : f q₁ q₂ IH₁ IH₂ {
    exact ⟨
      IH₁ (TM3.stmts_trans (by simp [TM3.stmts₁]) h) hs.1,
      IH₂ (TM3.stmts_trans (by simp [TM3.stmts₁]) h) hs.2⟩ },
  case TM3.stmt.goto : l {
    exact λ a v, finset.mem_bind.2 ⟨_, hs a.base v, TM3.stmts₁_self⟩ },
  case TM3.stmt.halt { trivial }
end⟩

end

end TM3to2

end turing