/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Define a sequence of simple machine languages, starting with Turing
machines and working up to more complex lanaguages based on
Wang B-machines.
-/
import data.finset data.pfun logic.relation

open relation

namespace turing

/-- A direction for the turing machine `move` command, either
  left or right. -/
@[derive decidable_eq]
inductive dir | left | right

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

@[simp] theorem tape.nth_zero {Γ} [inhabited Γ] :
  ∀ (T : tape Γ), T.nth 0 = T.1
| (a, L, R) := rfl

@[simp] theorem tape.move_left_nth {Γ} [inhabited Γ] :
  ∀ (T : tape Γ) (i : ℤ), (T.move dir.left).nth i = T.nth (i-1)
| (a, L, R) -[1+ n]      := by cases L; refl
| (a, L, R) 0           := by cases L; refl
| (a, L, R) 1           := rfl
| (a, L, R) ((n+1:ℕ)+1) := by rw add_sub_cancel; refl

@[simp] theorem tape.move_right_nth {Γ} [inhabited Γ] :
  ∀ (T : tape Γ) (i : ℤ), (T.move dir.right).nth i = T.nth (i+1)
| (a, L, R) (n+1:ℕ)    := by cases R; refl
| (a, L, R) 0         := by cases R; refl
| (a, L, R) -1        := rfl
| (a, L, R) -[1+ n+1] := show _ = tape.nth _ (-[1+ n] - 1 + 1),
  by rw sub_add_cancel; refl

@[simp] theorem tape.write_self {Γ} : ∀ (T : tape Γ), T.write T.1 = T
| (a, LR) := rfl

@[simp] theorem tape.write_nth {Γ} [inhabited Γ] (b : Γ) :
  ∀ (T : tape Γ) {i : ℤ}, (T.write b).nth i = if i = 0 then b else T.nth i
| (a, L, R) 0       := rfl
| (a, L, R) (n+1:ℕ) := rfl
| (a, L, R) -[1+ n] := rfl

def eval {σ} (f : σ → option σ) : σ → roption σ :=
pfun.fix (λ s, roption.some $
  match f s with none := sum.inl s | some s' := sum.inr s' end)

def reaches {σ} (f : σ → option σ) : σ → σ → Prop :=
refl_trans_gen (λ a b, b ∈ f a)

def reaches₁ {σ} (f : σ → option σ) : σ → σ → Prop :=
trans_gen (λ a b, b ∈ f a)

theorem reaches₁_eq {σ} {f : σ → option σ} {a b c}
  (h : f a = f b) : reaches₁ f a c ↔ reaches₁ f b c :=
trans_gen.head'_iff.trans (trans_gen.head'_iff.trans $ by rw h).symm

theorem reaches_total {σ} {f : σ → option σ}
  {a b c} : reaches f a b → reaches f a c →
  reaches f b c ∨ reaches f c b :=
refl_trans_gen.total_of_right_unique $ λ _ _ _, option.mem_unique

theorem mem_eval {σ} {f : σ → option σ} {a b} :
  b ∈ eval f a ↔ reaches f a b ∧ f b = none :=
⟨λ h, begin
  refine pfun.fix_induction h (λ a h IH, _),
  cases e : f a with a',
  { rw roption.mem_unique h (pfun.mem_fix_iff.2 $ or.inl $
      roption.mem_some_iff.2 $ by rw e; refl),
    exact ⟨refl_trans_gen.refl, e⟩ },
  { rcases pfun.mem_fix_iff.1 h with h | ⟨_, h, h'⟩;
      rw e at h; cases roption.mem_some_iff.1 h,
    cases IH a' h' (by rwa e) with h₁ h₂,
    exact ⟨refl_trans_gen.head e h₁, h₂⟩ }
end, λ ⟨h₁, h₂⟩, begin
  refine refl_trans_gen.head_induction_on h₁ _ (λ a a' h _ IH, _),
  { refine pfun.mem_fix_iff.2 (or.inl _),
    rw h₂, apply roption.mem_some },
  { refine pfun.mem_fix_iff.2 (or.inr ⟨_, _, IH⟩),
    rw show f a = _, from h,
    apply roption.mem_some }
end⟩

theorem eval_maximal₁ {σ} {f : σ → option σ} {a b}
  (h : b ∈ eval f a) (c) : ¬ reaches₁ f b c | bc :=
let ⟨ab, b0⟩ := mem_eval.1 h, ⟨b', h', _⟩ := trans_gen.head'_iff.1 bc in
by cases b0.symm.trans h'

theorem eval_maximal {σ} {f : σ → option σ} {a b}
  (h : b ∈ eval f a) {c} : reaches f b c ↔ c = b :=
let ⟨ab, b0⟩ := mem_eval.1 h in
refl_trans_gen_iff_eq $ λ b' h', by cases b0.symm.trans h'

theorem reaches_eval {σ} {f : σ → option σ} {a b}
  (ab : reaches f a b) : eval f a = eval f b :=
roption.ext $ λ c,
 ⟨λ h, let ⟨ac, c0⟩ := mem_eval.1 h in
    mem_eval.2 ⟨(or_iff_left_of_imp $ by exact
      λ cb, (eval_maximal h).1 cb ▸ refl_trans_gen.refl).1
      (reaches_total ab ac), c0⟩,
  λ h, let ⟨bc, c0⟩ := mem_eval.1 h in mem_eval.2 ⟨ab.trans bc, c0⟩,⟩

def respects {σ₁ σ₂}
  (f₁ : σ₁ → option σ₁) (f₂ : σ₂ → option σ₂) (tr : σ₁ → σ₂ → Prop) :=
∀ ⦃a₁ a₂⦄, tr a₁ a₂ → (match f₁ a₁ with
  | some b₁ := ∃ b₂, tr b₁ b₂ ∧ reaches₁ f₂ a₂ b₂
  | none := f₂ a₂ = none
  end : Prop)

theorem tr_reaches₁ {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) {b₁} (ab : reaches₁ f₁ a₁ b₁) :
  ∃ b₂, tr b₁ b₂ ∧ reaches₁ f₂ a₂ b₂ :=
begin
  induction ab with c₁ ac c₁ d₁ ac cd IH,
  { have := H aa,
    rwa (show f₁ a₁ = _, from ac) at this },
  { rcases IH with ⟨c₂, cc, ac₂⟩,
    have := H cc,
    rw (show f₁ c₁ = _, from cd) at this,
    rcases this with ⟨d₂, dd, cd₂⟩,
    exact ⟨_, dd, ac₂.trans cd₂⟩ }
end

theorem tr_reaches {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) {b₁} (ab : reaches f₁ a₁ b₁) :
  ∃ b₂, tr b₁ b₂ ∧ reaches f₂ a₂ b₂ :=
begin
  rcases refl_trans_gen_iff_eq_or_trans_gen.1 ab with rfl | ab,
  { exact ⟨_, aa, refl_trans_gen.refl⟩ },
  { exact let ⟨b₂, bb, h⟩ := tr_reaches₁ H aa ab in
    ⟨b₂, bb, h.to_refl⟩ }
end

theorem tr_reaches_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) {b₂} (ab : reaches f₂ a₂ b₂) :
  ∃ c₁ c₂, reaches f₂ b₂ c₂ ∧ tr c₁ c₂ ∧ reaches f₁ a₁ c₁ :=
begin
  induction ab with c₂ d₂ ac cd IH,
  { exact ⟨_, _, refl_trans_gen.refl, aa, refl_trans_gen.refl⟩ },
  { rcases IH with ⟨e₁, e₂, ce, ee, ae⟩,
    rcases refl_trans_gen.cases_head ce with rfl | ⟨d', cd', de⟩,
    { have := H ee, revert this,
      cases eg : f₁ e₁ with g₁; simp [respects],
      { intro c0, cases cd.symm.trans c0 },
      { intros g₂ gg cg,
        rcases trans_gen.head'_iff.1 cg with ⟨d', cd', dg⟩,
        cases option.mem_unique cd cd',
        exact ⟨_, _, dg, gg, ae.tail eg⟩ } },
    { cases option.mem_unique cd cd',
      exact ⟨_, _, de, ee, ae⟩ } }
end

theorem tr_eval {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ b₁ a₂} (aa : tr a₁ a₂)
  (ab : b₁ ∈ eval f₁ a₁) : ∃ b₂, tr b₁ b₂ ∧ b₂ ∈ eval f₂ a₂ :=
begin
  cases mem_eval.1 ab with ab b0,
  rcases tr_reaches H aa ab with ⟨b₂, bb, ab⟩,
  refine ⟨_, bb, mem_eval.2 ⟨ab, _⟩⟩,
  have := H bb, rwa b0 at this
end

theorem tr_eval_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ b₂ a₂} (aa : tr a₁ a₂)
  (ab : b₂ ∈ eval f₂ a₂) : ∃ b₁, tr b₁ b₂ ∧ b₁ ∈ eval f₁ a₁ :=
begin
  cases mem_eval.1 ab with ab b0,
  rcases tr_reaches_rev H aa ab with ⟨c₁, c₂, bc, cc, ac⟩,
  cases (refl_trans_gen_iff_eq
    (by exact option.eq_none_iff_forall_not_mem.1 b0)).1 bc,
  refine ⟨_, cc, mem_eval.2 ⟨ac, _⟩⟩,
  have := H cc, cases f₁ c₁ with d₁, {refl},
  rcases this with ⟨d₂, dd, bd⟩,
  rcases trans_gen.head'_iff.1 bd with ⟨e, h, _⟩,
  cases b0.symm.trans h
end

theorem tr_eval_dom {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) :
  (eval f₂ a₂).dom ↔ (eval f₁ a₁).dom :=
⟨λ h, let ⟨b₂, tr, h, _⟩ := tr_eval_rev H aa ⟨h, rfl⟩ in h,
 λ h, let ⟨b₂, tr, h, _⟩ := tr_eval H aa ⟨h, rfl⟩ in h⟩

def frespects {σ₁ σ₂} (f₂ : σ₂ → option σ₂) (tr : σ₁ → σ₂) (a₂ : σ₂) : option σ₁ → Prop
| (some b₁) := reaches₁ f₂ a₂ (tr b₁)
| none := f₂ a₂ = none

theorem frespects_eq {σ₁ σ₂} {f₂ : σ₂ → option σ₂} {tr : σ₁ → σ₂} {a₂ b₂}
  (h : f₂ a₂ = f₂ b₂) : ∀ {b₁}, frespects f₂ tr a₂ b₁ ↔ frespects f₂ tr b₂ b₁
| (some b₁) := reaches₁_eq h
| none := by simp [frespects, h]

theorem fun_respects {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂} :
  respects f₁ f₂ (λ a b, tr a = b) ↔ ∀ ⦃a₁⦄, frespects f₂ tr (tr a₁) (f₁ a₁) :=
forall_congr $ λ a₁, by cases f₁ a₁; simp [frespects, respects]

theorem tr_eval' {σ₁ σ₂}
  (f₁ : σ₁ → option σ₁) (f₂ : σ₂ → option σ₂) (tr : σ₁ → σ₂)
  (H : respects f₁ f₂ (λ a b, tr a = b))
  (a₁) : eval f₂ (tr a₁) = tr <$> eval f₁ a₁ :=
roption.ext $ λ b₂, by simp; exact
 ⟨λ h, let ⟨b₁, bb, hb⟩ :=
    tr_eval_rev H rfl h in ⟨b₁, hb, bb⟩,
  λ ⟨b₁, ab, bb⟩, begin
    rcases tr_eval H rfl ab with ⟨_, rfl, h⟩,
    rwa bb at h
  end⟩

def dwrite {K} [decidable_eq K] {C : K → Type*}
  (S : ∀ k, C k) (k') (l : C k') (k) : C k :=
if h : k = k' then eq.rec_on h.symm l else S k

@[simp] theorem dwrite_eq {K} [decidable_eq K] {C : K → Type*}
  (S : ∀ k, C k) (k) (l : C k) : dwrite S k l k = l :=
by simp [dwrite]

@[simp] theorem dwrite_ne {K} [decidable_eq K] {C : K → Type*}
  (S : ∀ k, C k) (k') (l : C k') (k) (h : ¬ k = k') : dwrite S k' l k = S k :=
by simp [dwrite, h]

@[simp] theorem dwrite_self
  {K} [decidable_eq K] {C : K → Type*}
  (S : ∀ k, C k) (k) : dwrite S k (S k) = S :=
funext $ λ k', by unfold dwrite; split_ifs; [subst h, refl]

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

parameters {Γ Λ}
/-- Execution semantics of the Turing machine. -/
def step (M : machine) : cfg → option cfg
| ⟨q, T⟩ := (M q T.1).map (λ ⟨q', a⟩, ⟨q',
  match a with
  | stmt.move d := T.move d
  | stmt.write a := T.write a
  end⟩)

/-- The statement `reaches M s₁ s₂` means that `s₂` is obtained
  starting from `s₁` after a finite number of steps from `s₂`. -/
def reaches (M : machine) : cfg → cfg → Prop :=
refl_trans_gen (λ a b, b ∈ step M a)

/-- The initial configuration. -/
def init (M : machine) (l : list Γ) : cfg :=
⟨default Λ, tape.mk l⟩

/-- Evaluate a Turing machine on initial input to a final state,
  if it terminates. -/
def eval (M : machine) (l : list Γ) : roption (list Γ) :=
(eval (step M) ⟨default Λ, tape.mk l⟩).map (λ c, c.tape.2.2)

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
parameters (σ : Type*) -- Type of variable settings

/-- The TM1 model is a simplification and extension of TM0
  (Post-Turing model) in the direction of Wang B-machines. The machine's
  internal state is extended with a (finite) store `σ` of variables
  that may be accessed and updated at any time.
  A machine is given by a `Λ` indexed set of procedures or functions.
  Each function has a body which is a `stmt`, which can either be a
  `move` or `write` command, a `branch` (if statement based on the
  current tape value), a `load` (set the variable value),
  a `goto` (call another function), or `halt`. Note that here
  most statements do not have labels; `goto` commands can only
  go to a new function. All commands have access to the variable value
  and current tape value. -/
inductive stmt
| move : dir → stmt → stmt
| write : (Γ → σ → Γ) → stmt → stmt
| load : (Γ → σ → σ) → stmt → stmt
| branch : (Γ → σ → bool) → stmt → stmt → stmt
| goto {} : (Γ → σ → Λ) → stmt
| halt {} : stmt
open stmt

/-- The configuration of a TM1 machine is given by the currently
  evaluating statement, the variable store value, and the tape. -/
structure cfg :=
(q : option stmt)
(var : σ)
(tape : tape Γ)

parameters {Γ Λ σ}
/-- The semantics of TM1 evaluation. -/
def step_aux (M : Λ → stmt) : stmt → σ → tape Γ → cfg
| (move d q)       v T := step_aux q v (T.move d)
| (write a q)      v T := step_aux q v (T.write (a T.1 v))
| (load s q)       v T := step_aux q (s T.1 v) T
| (branch p q₁ q₂) v T :=
  cond (p T.1 v) (step_aux q₁ v T) (step_aux q₂ v T)
| (goto l)         v T := ⟨some (M (l T.1 v)), v, T⟩
| halt             v T := ⟨none, v, T⟩

def step (M : Λ → stmt) : cfg → option cfg
| ⟨none,   v, T⟩ := none
| ⟨some q, v, T⟩ := some (step_aux M q v T)

variables [inhabited Λ] [inhabited σ]
def init (M : Λ → stmt) (l : list Γ) : cfg :=
⟨some (M (default _)), default _, tape.mk l⟩

def eval (M : Λ → stmt) (l : list Γ) : roption (list Γ) :=
(eval (step M) (init M l)).map (λ c, c.tape.2.2)

variables [fintype Γ]
def supports_stmt (S : finset Λ) : stmt → Prop
| (move d q)       := supports_stmt q
| (write a q)      := supports_stmt q
| (load s q)       := supports_stmt q
| (branch p q₁ q₂) := supports_stmt q₁ ∧ supports_stmt q₂
| (goto l)         := ∀ a v, l a v ∈ S
| halt             := true

/-- A set `S` of labels supports machine `M` if all the `goto`
  statements in the functions in `S` refer only to other functions
  in `S`. -/
def supports (M : Λ → stmt) (S : finset Λ) :=
default Λ ∈ S ∧ ∀ q ∈ S, supports_stmt S (M q)

local attribute [instance] classical.dec
noncomputable def stmts₁ : stmt → finset stmt
| Q@(move d q)       := insert Q (stmts₁ q)
| Q@(write a q)      := insert Q (stmts₁ q)
| Q@(load s q)       := insert Q (stmts₁ q)
| Q@(branch p q₁ q₂) := insert Q (stmts₁ q₁ ∪ stmts₁ q₂)
| Q                  := {Q}

theorem stmts₁_self {q} : q ∈ stmts₁ q :=
by cases q; simp [stmts₁]

theorem stmts₁_trans {q₁ q₂} :
  q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ :=
begin
  intros h₁₂ q₀ h₀₁,
  induction q₂ with _ q IH _ q IH _ q IH;
    simp [stmts₁, finset.subset_iff] at h₁₂ ⊢,
  iterate 3 {
    rcases h₁₂ with rfl | h₁₂,
    { simp [stmts₁] at h₀₁, rcases h₀₁ with rfl | h; simp * },
    { exact or.inr (IH h₁₂) } },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    rcases h₁₂ with rfl | h₁₂ | h₁₂,
    { simp [stmts₁] at h₀₁, rcases h₀₁ with rfl | h; simp * },
    { simp [IH₁ h₁₂] }, { simp [IH₂ h₁₂] } },
  case TM1.stmt.goto : l {
    subst h₁₂, simpa [stmts₁] using h₀₁ },
  case TM1.stmt.halt {
    subst h₁₂, simpa [stmts₁] using h₀₁ }
end

theorem stmts₁_supports_stmt_mono {S q₁ q₂}
  (h : q₁ ∈ stmts₁ q₂) (hs : supports_stmt S q₂) : supports_stmt S q₁ :=
begin
  induction q₂ with _ q IH _ q IH _ q IH;
    simp [stmts₁, supports_stmt] at h hs,
  iterate 3 { rcases h with rfl | h; [exact hs, exact IH h hs] },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    rcases h with rfl | h | h, exacts [hs, IH₁ h hs.1, IH₂ h hs.2] },
  case TM1.stmt.goto : l { subst h, exact hs },
  case TM1.stmt.halt { subst h, trivial }
end

noncomputable def stmts
  (M : Λ → stmt) (S : finset Λ) : finset (option stmt) :=
(S.bind (λ q, stmts₁ (M q))).insert_none

theorem stmts_trans {M : Λ → stmt} {S q₁ q₂}
  (h₁ : q₁ ∈ stmts₁ q₂) : some q₂ ∈ stmts M S → some q₁ ∈ stmts M S :=
by simp [stmts]; exact λ l ls h₂, ⟨_, ls, stmts₁_trans h₂ h₁⟩

theorem stmts_supports_stmt {M : Λ → stmt} {S q}
  (ss : supports M S) : some q ∈ stmts M S → supports_stmt S q :=
by simp [stmts]; exact
λ l ls h, stmts₁_supports_stmt_mono h (ss.2 _ ls)

theorem step_supports (M : Λ → stmt) {S}
  (ss : supports M S) : ∀ {c c' : cfg},
  c' ∈ step M c → c.q ∈ stmts M S → c'.q ∈ stmts M S
| ⟨some q₁, v, T⟩ c' h₁ h₂ := begin
  rcases finset.mem_bind.1 (finset.some_mem_insert_none.1 h₂) with ⟨l, hl, h⟩,
  simp [step] at h₁ h₂, subst c',
  suffices : q₁ ∈ stmts₁ (M l) → supports_stmt S (M l) →
    (∃ q, (step_aux M q₁ v T).q = some q ∧ q ∈ stmts₁ (M l)) ∨
    (step_aux M q₁ v T).q ∈ stmts M S,
  from (or_iff_right_of_imp (by exact λ ⟨q, h₁, h₂⟩,
    h₁.symm ▸ finset.some_mem_insert_none.2
      (finset.mem_bind.2 ⟨_, hl, h₂⟩))).1 (this h (ss.2 _ hl)),
  clear h h₂, induction M l with _ q IH _ q IH _ q IH generalizing q₁ v T;
    intros h hs; simp [stmts₁] at h ⊢,
  iterate 3 {
    rcases h with rfl | h,
    { exact (IH q _ _ stmts₁_self hs).imp_left
      (λ ⟨q', h₁, h₂⟩, ⟨q', h₁, or.inr h₂⟩) },
    { exact (IH q₁ _ _ h hs).imp_left
      (λ ⟨q', h₁, h₂⟩, ⟨q', h₁, or.inr h₂⟩) } },
  case TM1.stmt.branch : p q₁' q₂' IH₁ IH₂ {
    rcases h with rfl | h | h,
    { simp [step_aux], cases p T.1 v,
      { exact (IH₂ _ _ _ stmts₁_self hs.2).imp_left
        (λ ⟨q', h₁, h₂⟩, ⟨q', h₁, or.inr (or.inr h₂)⟩) },
      { exact (IH₁ _ _ _ stmts₁_self hs.1).imp_left
        (λ ⟨q', h₁, h₂⟩, ⟨q', h₁, or.inr (or.inl h₂)⟩) } },
    { exact (IH₁ _ _ _ h hs.1).imp_left
      (λ ⟨q', h₁, h₂⟩, ⟨q', h₁, or.inr (or.inl h₂)⟩) },
    { exact (IH₂ _ _ _ h hs.2).imp_left
      (λ ⟨q', h₁, h₂⟩, ⟨q', h₁, or.inr (or.inr h₂)⟩) } },
  case TM1.stmt.goto : l { subst h,
    exact or.inr (finset.some_mem_insert_none.2 $
      finset.mem_bind.2 ⟨_, hs _ _, stmts₁_self⟩) },
  case TM1.stmt.halt { subst h,
    exact or.inr (multiset.mem_cons_self _ _) }
end

end

end TM1

namespace TM1to0

section
parameters {Γ : Type*} [inhabited Γ]
parameters {Λ : Type*} [inhabited Λ]
parameters {σ : Type*} [inhabited σ]

local notation `stmt₁` := TM1.stmt Γ Λ σ
local notation `cfg₁` := TM1.cfg Γ Λ σ
local notation `stmt₀` := TM0.stmt Γ

parameters (M : Λ → stmt₁)
include M

def Λ' := option stmt₁ × σ
instance : inhabited Λ' := ⟨(some (M (default _)), default _)⟩

open TM0.stmt

def tr_aux (s : Γ) : stmt₁ → σ → Λ' × stmt₀
| (TM1.stmt.move d q)       v := ((some q, v), move d)
| (TM1.stmt.write a q)      v := ((some q, v), write (a s v))
| (TM1.stmt.load a q)       v := tr_aux q (a s v)
| (TM1.stmt.branch p q₁ q₂) v := cond (p s v) (tr_aux q₁ v) (tr_aux q₂ v)
| (TM1.stmt.goto l)         v := ((some (M (l s v)), v), write s)
| TM1.stmt.halt             v := ((none, v), write s)

local notation `cfg₀` := TM0.cfg Γ Λ'

def tr : TM0.machine Γ Λ'
| (none,   v) s := none
| (some q, v) s := some (tr_aux s q v)

def tr_cfg : cfg₁ → cfg₀ | ⟨q, v, T⟩ := ⟨(q, v), T⟩

theorem tr_respects : respects (TM1.step M) (TM0.step tr)
  (λ c₁ c₂, tr_cfg c₁ = c₂) :=
fun_respects.2 $ λ ⟨q₁, v, T⟩, begin
  cases q₁ with q₁, {exact rfl},
  simp [tr_cfg, TM1.step, frespects],
  induction q₁ with _ q IH _ q IH _ q IH generalizing v T,
  case TM1.stmt.move  : d q IH { exact trans_gen.head rfl (IH _ _) },
  case TM1.stmt.write : a q IH { exact trans_gen.head rfl (IH _ _) },
  case TM1.stmt.load : a q IH { exact (reaches₁_eq (by refl)).2 (IH _ _) },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    simp [TM1.step_aux], cases e : p T.1 v,
    { exact (reaches₁_eq (by simp! [e])).2 (IH₂ _ _) },
    { exact (reaches₁_eq (by simp! [e])).2 (IH₁ _ _) } },
  case TM1.stmt.goto : l { apply trans_gen.single, simp! },
  case TM1.stmt.halt     { apply trans_gen.single, simp! }
end

variables [fintype Γ] [fintype σ]
noncomputable def tr_stmts (S : finset Λ) : finset Λ' :=
(TM1.stmts M S).product finset.univ

local attribute [instance] classical.dec
local attribute [simp] TM1.stmts₁_self
theorem tr_supports {S} (ss : TM1.supports M S) : TM0.supports tr (tr_stmts S) :=
⟨by simp [tr_stmts]; exact finset.some_mem_insert_none.2
  (finset.mem_bind.2 ⟨_, ss.1, TM1.stmts₁_self⟩),
 λ q a q' s h₁ h₂, begin
  rcases q with ⟨_|q, v⟩, {cases h₁},
  cases q' with q' v', simp [tr_stmts] at h₂ ⊢,
  cases q', {simp [TM1.stmts]},
  simp [tr] at h₁,
  have := TM1.stmts_supports_stmt ss h₂,
  revert this, induction q generalizing v; intro hs,
  case TM1.stmt.move : d q {
    cases h₁, refine TM1.stmts_trans _ h₂, simp [TM1.stmts₁] },
  case TM1.stmt.write : b q {
    cases h₁, refine TM1.stmts_trans _ h₂, simp [TM1.stmts₁] },
  case TM1.stmt.load : b q IH {
    refine IH (TM1.stmts_trans _ h₂) _ h₁ hs, simp [TM1.stmts₁] },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    simp! at h₁, cases p a v,
    { refine IH₂ (TM1.stmts_trans _ h₂) _ h₁ hs.2, simp [TM1.stmts₁] },
    { refine IH₁ (TM1.stmts_trans _ h₂) _ h₁ hs.1, simp [TM1.stmts₁] } },
  case TM1.stmt.goto : l {
    cases h₁, exact finset.some_mem_insert_none.2
      (finset.mem_bind.2 ⟨_, hs _ _, TM1.stmts₁_self⟩) },
  case TM1.stmt.halt { cases h₁ }
end⟩

theorem tr_eval (l : list Γ) : TM0.eval tr l = TM1.eval M l :=
(congr_arg _ (tr_eval' _ _ _ tr_respects ⟨_, _, _⟩)).trans begin
  simp [tr_cfg],
  rw [roption.map_map, TM1.eval],
  congr', exact funext (λ ⟨_, _, _⟩, rfl)
end

end
end TM1to0

namespace TM2

section
parameters {K : Type*} [decidable_eq K] -- Index type of stacks
parameters (Γ : K → Type*) [∀ k, inhabited (Γ k)] -- Type of stack elements
parameters (Λ : Type*) -- Type of function labels
parameters (σ : Type*) -- Type of variable settings

/-- The TM2 model removes the tape entirely from the TM1 model,
  replacing it with an arbitrary (finite) collection of stacks.
  The operation `push` puts an element on one of the stacks,
  and `pop` removes an element from a stack (and modifying the
  internal state based on the result). `peek` modifies the
  internal state but does not remove an element. -/
inductive stmt
| push {} : ∀ k, (σ → Γ k) → stmt → stmt
| peek {} : ∀ k, (σ → option (Γ k) → σ) → stmt → stmt
| pop {} : ∀ k, (σ → option (Γ k) → σ) → stmt → stmt
| load : (σ → σ) → stmt → stmt
| branch : (σ → bool) → stmt → stmt → stmt
| goto {} : (σ → Λ) → stmt
| halt {} : stmt
open stmt

structure cfg :=
(q : option stmt)
(var : σ)
(stk : ∀ k, list (Γ k))

parameters {Γ Λ σ K}
def step_aux (M : Λ → stmt) :
  stmt → σ → (∀ k, list (Γ k)) → cfg
| (push k f q)     v S := step_aux q v (dwrite S k (f v :: S k))
| (peek k f q)     v S := step_aux q (f v (S k).head') S
| (pop k f q)      v S := step_aux q (f v (S k).head') (dwrite S k (S k).tail)
| (load a q)       v S := step_aux q (a v) S
| (branch f q₁ q₂) v S :=
  cond (f v) (step_aux q₁ v S) (step_aux q₂ v S)
| (goto f)         v S := ⟨some (M (f v)), v, S⟩
| halt             v S := ⟨none, v, S⟩

def step (M : Λ → stmt) : cfg → option cfg
| ⟨none,   v, S⟩ := none
| ⟨some q, v, S⟩ := some (step_aux M q v S)

def reaches (M : Λ → stmt) : cfg → cfg → Prop :=
refl_trans_gen (λ a b, b ∈ step M a)

variables [inhabited Λ] [inhabited σ]
def init (M : Λ → stmt) (k) (L : list (Γ k)) : cfg :=
⟨some (M (default _)), default _, dwrite (λ _, []) k L⟩

def eval (M : Λ → stmt) (k) (L : list (Γ k)) : roption (list (Γ k)) :=
(eval (step M) (init M k L)).map $ λ c, c.stk k

variables [fintype K] [∀ k, fintype (Γ k)] [fintype σ]
def supports_stmt (S : finset Λ) : stmt → Prop
| (push k f q)     := supports_stmt q
| (peek k f q)     := supports_stmt q
| (pop k f q)      := supports_stmt q
| (load a q)       := supports_stmt q
| (branch f q₁ q₂) := supports_stmt q₁ ∧ supports_stmt q₂
| (goto l)         := ∀ v, l v ∈ S
| halt             := true

def supports (M : Λ → stmt) (S : finset Λ) :=
default Λ ∈ S ∧ ∀ q ∈ S, supports_stmt S (M q)

local attribute [instance] classical.dec
noncomputable def stmts₁ : stmt → finset stmt
| Q@(push k f q)     := insert Q (stmts₁ q)
| Q@(peek k f q)     := insert Q (stmts₁ q)
| Q@(pop k f q)      := insert Q (stmts₁ q)
| Q@(load a q)       := insert Q (stmts₁ q)
| Q@(branch f q₁ q₂) := insert Q (stmts₁ q₁ ∪ stmts₁ q₂)
| Q@(goto l)         := {Q}
| Q@halt             := {Q}

theorem stmts₁_self {q} : q ∈ stmts₁ q :=
by cases q; simp [stmts₁]

theorem stmts₁_trans {q₁ q₂} :
  q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ :=
begin
  intros h₁₂ q₀ h₀₁,
  induction q₂ with _ _ q IH _ _ q IH _ _ q IH _ q IH;
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
  induction q₂ with _ _ q IH _ _ q IH _ _ q IH _ q IH;
    simp [stmts₁, supports_stmt] at h hs,
  iterate 4 { rcases h with rfl | h; [exact hs, exact IH h hs] },
  case TM2.stmt.branch : f q₁ q₂ IH₁ IH₂ {
    rcases h with rfl | h | h, exacts [hs, IH₁ h hs.1, IH₂ h hs.2] },
  case TM2.stmt.goto : l { subst h, exact hs },
  case TM2.stmt.halt { subst h, trivial }
end

noncomputable def stmts
  (M : Λ → stmt) (S : finset Λ) : finset (option stmt) :=
(S.bind (λ q, stmts₁ (M q))).insert_none

theorem stmts_trans {M : Λ → stmt} {S q₁ q₂}
  (h₁ : q₁ ∈ stmts₁ q₂) : some q₂ ∈ stmts M S → some q₁ ∈ stmts M S :=
by simp [stmts]; exact λ l ls h₂, ⟨_, ls, stmts₁_trans h₂ h₁⟩

theorem stmts_supports_stmt {M : Λ → stmt} {S q}
  (ss : supports M S) : some q ∈ stmts M S → supports_stmt S q :=
by simp [stmts]; exact
λ l ls h, stmts₁_supports_stmt_mono h (ss.2 _ ls)

theorem step_supports (M : Λ → stmt) {S}
  (ss : supports M S) : ∀ {c c' : cfg},
  c' ∈ step M c → c.q ∈ stmts M S → c'.q ∈ stmts M S
| ⟨some q₁, v, T⟩ c' h₁ h₂ := begin
  rcases finset.mem_bind.1 (finset.some_mem_insert_none.1 h₂) with ⟨l, hl, h⟩,
  simp [step] at h₁, subst c',
  suffices : q₁ ∈ stmts₁ (M l) → supports_stmt S (M l) →
    (∃ q, (step_aux M q₁ v T).q = some q ∧ q ∈ stmts₁ (M l)) ∨
    (step_aux M q₁ v T).q ∈ stmts M S,
  from (or_iff_right_of_imp (by exact λ ⟨q, h₁, h₂⟩,
    h₁.symm ▸ finset.some_mem_insert_none.2
      (finset.mem_bind.2 ⟨_, hl, h₂⟩))).1 (this h (ss.2 _ hl)),
  clear h h₂, induction M l with _ _ q IH _ _ q IH _ _ q IH _ q IH generalizing q₁ v T;
    intros h hs; simp [stmts₁] at h ⊢,
  iterate 4 {
    rcases h with rfl | h,
    { exact (IH q _ _ stmts₁_self hs).imp_left
      (λ ⟨q', h₁, h₂⟩, ⟨q', h₁, or.inr h₂⟩) },
    { exact (IH q₁ _ _ h hs).imp_left
      (λ ⟨q', h₁, h₂⟩, ⟨q', h₁, or.inr h₂⟩) } },
  case TM2.stmt.branch : p q₁' q₂' IH₁ IH₂ {
    rcases h with rfl | h | h,
    { simp [step_aux], cases p v,
      { exact (IH₂ _ _ _ stmts₁_self hs.2).imp_left
        (λ ⟨q', h₁, h₂⟩, ⟨q', h₁, or.inr (or.inr h₂)⟩) },
      { exact (IH₁ _ _ _ stmts₁_self hs.1).imp_left
        (λ ⟨q', h₁, h₂⟩, ⟨q', h₁, or.inr (or.inl h₂)⟩) } },
    { exact (IH₁ _ _ _ h hs.1).imp_left
      (λ ⟨q', h₁, h₂⟩, ⟨q', h₁, or.inr (or.inl h₂)⟩) },
    { exact (IH₂ _ _ _ h hs.2).imp_left
      (λ ⟨q', h₁, h₂⟩, ⟨q', h₁, or.inr (or.inr h₂)⟩) } },
  case TM2.stmt.goto : l { subst h,
    exact or.inr (finset.some_mem_insert_none.2 $
      finset.mem_bind.2 ⟨_, hs _, stmts₁_self⟩) },
  case TM2.stmt.halt { subst h,
    exact or.inr (multiset.mem_cons_self _ _) }
end

end

end TM2

namespace TM2to1

section
parameters {K : Type*} [decidable_eq K]
parameters {Γ : K → Type*} [∀ k, inhabited (Γ k)]
parameters {Λ : Type*} [inhabited Λ]
parameters {σ : Type*} [inhabited σ]

local notation `stmt₂` := TM2.stmt Γ Λ σ
local notation `cfg₂` := TM2.cfg Γ Λ σ

inductive stackel (k : K)
| val : Γ k → stackel
| bottom : stackel
| top : stackel

instance stackel.inhabited (k) : inhabited (stackel k) :=
⟨stackel.val (default _)⟩

def stackel.is_bottom {k} : stackel k → bool
| (stackel.bottom _) := tt
| _ := ff 

def stackel.is_top {k} : stackel k → bool
| (stackel.top _) := tt
| _ := ff 

def stackel.get {k} : stackel k → option (Γ k)
| (stackel.val a) := some a
| _ := none

section
open stackel

def stackel_equiv {k} : stackel k ≃ option (option (Γ k)) :=
begin
  refine ⟨λ s, _, λ s, _, _, _⟩,
  { cases s, exacts [some (some s), none, some none] },
  { rcases s with _|_|s, exacts [bottom _, top _, val s] },
  { intro s, cases s; refl },
  { intro s, rcases s with _|_|s; refl },
end

end

def Γ' := ∀ k, stackel k

instance Γ'.inhabited : inhabited Γ' := ⟨λ _, default _⟩

instance stackel.fintype {k} [fintype (Γ k)] : fintype (stackel k) :=
fintype.of_equiv _ stackel_equiv.symm

instance Γ'.fintype [fintype K] [∀ k, fintype (Γ k)] : fintype Γ' :=
pi.fintype

inductive st_act (k : K)
| push {} : (σ → Γ k) → st_act
| pop {} : bool → (σ → option (Γ k) → σ) → st_act

section
open st_act

def st_run {k : K} : st_act k → stmt₂ → stmt₂
| (push f)   := TM2.stmt.push k f
| (pop ff f) := TM2.stmt.peek k f
| (pop tt f) := TM2.stmt.pop k f

def st_var {k : K} (v : σ) (l : list (Γ k)) : st_act k → σ
| (push f)  := v
| (pop b f) := f v l.head'

def st_write {k : K} (v : σ) (l : list (Γ k)) : st_act k → list (Γ k)
| (push f) := f v :: l
| (pop ff f) := l
| (pop tt f) := l.tail

@[elab_as_eliminator] theorem {l} stmt_st_rec
  {C : stmt₂ → Sort l}
  (H₁ : Π k (s : st_act k) q (IH : C q), C (st_run s q))
  (H₂ : Π a q (IH : C q), C (TM2.stmt.load a q))
  (H₃ : Π p q₁ q₂ (IH₁ : C q₁) (IH₂ : C q₂), C (TM2.stmt.branch p q₁ q₂))
  (H₄ : Π l, C (TM2.stmt.goto l))
  (H₅ : C TM2.stmt.halt) : ∀ n, C n
| (TM2.stmt.push k f q)     := H₁ _ (push f) _ (stmt_st_rec q)
| (TM2.stmt.peek k f q)     := H₁ _ (pop ff f) _ (stmt_st_rec q)
| (TM2.stmt.pop k f q)      := H₁ _ (pop tt f) _ (stmt_st_rec q)
| (TM2.stmt.load a q)       := H₂ _ _ (stmt_st_rec q)
| (TM2.stmt.branch a q₁ q₂) := H₃ _ _ _ (stmt_st_rec q₁) (stmt_st_rec q₂)
| (TM2.stmt.goto l)         := H₄ _
| TM2.stmt.halt             := H₅

theorem supports_run [fintype K] [∀ k, fintype (Γ k)] [fintype σ]
  (S : finset Λ) {k} (s : st_act k) (q) :
  TM2.supports_stmt S (st_run s q) ↔ TM2.supports_stmt S q :=
by rcases s with _|_|_; refl

end

inductive Λ' : Type (max u_1 u_2 u_3 u_4)
| normal {} : stmt₂ → Λ'
| go (k) : st_act k → stmt₂ → Λ'
| ret {} : K → stmt₂ → Λ'
open Λ'

local notation `stmt₁` := TM1.stmt Γ' Λ' σ
local notation `cfg₁` := TM1.cfg Γ' Λ' σ

open TM1.stmt

def tr_st_act {k} (q : stmt₁) : st_act k → stmt₁
| (st_act.push f) :=
  write (λ a s, dwrite a k $ stackel.val $ f s) $
  move dir.right $
  write (λ a s, dwrite a k $ stackel.top k) q
| (st_act.pop b f) :=
  move dir.left $
  load (λ a s, f s (a k).get) $
  cond b
  ( branch (λ a s, (a k).is_bottom)
    ( move dir.right q )
    ( move dir.right $
      write (λ a s, dwrite a k $ default _) $
      move dir.left $
      write (λ a s, dwrite a k $ stackel.top k) q ) )
  ( move dir.right q )

def tr_init (k) (L : list (Γ k)) : list Γ' :=
stackel.bottom :: match L.reverse with
| [] := [stackel.top]
| (a::L') := dwrite stackel.top k (stackel.val a) ::
  (L'.map stackel.val ++ [stackel.top k]).map (dwrite (default _) k)
end

parameters (M : Λ → stmt₂)
include M

theorem step_run {k : K} (q v S) : ∀ s : st_act k,
  TM2.step_aux M (st_run s q) v S =
  TM2.step_aux M q (st_var v (S k) s) (dwrite S k (st_write v (S k) s))
| (st_act.push f) := rfl
| (st_act.pop ff f) := by simp!
| (st_act.pop tt f) := rfl

def Λ'_inh : inhabited Λ' := ⟨normal (M (default _))⟩

def tr_normal : stmt₂ → stmt₁
| (TM2.stmt.push k f q)     := goto (λ _ _, go k (st_act.push f) q)
| (TM2.stmt.peek k f q)     := goto (λ _ _, go k (st_act.pop ff f) q)
| (TM2.stmt.pop k f q)      := goto (λ _ _, go k (st_act.pop tt f) q)
| (TM2.stmt.load a q)       := load (λ _, a) (tr_normal q)
| (TM2.stmt.branch f q₁ q₂) := branch (λ a, f) (tr_normal q₁) (tr_normal q₂)
| (TM2.stmt.goto l)         := goto (λ a s, normal (M (l s)))
| TM2.stmt.halt             := halt

theorem tr_normal_run {k} (s q) :
  tr_normal (st_run s q) = goto (λ _ _, go k s q) :=
by rcases s with _|_|_; refl

def tr : Λ' → stmt₁
| (normal q) := tr_normal q
| (go k s q) :=
  branch (λ a s, (a k).is_top) (tr_st_act (goto (λ _ _, ret k q)) s)
    (move dir.right $ goto (λ _ _, go k s q))
| (ret k q) :=
  branch (λ a s, (a k).is_bottom) (tr_normal q)
    (move dir.left $ goto (λ _ _, ret k q))

def tr_stk {k} (S : list (Γ k)) (L : list (stackel k)) : Prop :=
∃ n, L = (S.map stackel.val).reverse_core (stackel.top k :: list.repeat (default _) n)

local attribute [pp_using_anonymous_constructor] turing.TM1.cfg
inductive tr_cfg : cfg₂ → cfg₁ → Prop
| mk {q v} {S : ∀ k, list (Γ k)} {L : list Γ'} :
  (∀ k, tr_stk (S k) (L.map (λ a, a k))) →
  tr_cfg ⟨q, v, S⟩ ⟨tr_normal <$> q, v, (stackel.bottom, [], L)⟩

theorem tr_respects_aux₁ {k} (o q v) : ∀ S₁ {s S₂} {T : list Γ'},
  T.map (λ (a : Γ'), a k) = (list.map stackel.val S₁).reverse_core (s :: S₂) →
  ∃ a T₁ T₂,
    T = list.reverse_core T₁ (a :: T₂) ∧
    a k = s ∧
    T₁.map (λ (a : Γ'), a k) = S₁.map stackel.val ∧
    T₂.map (λ (a : Γ'), a k) = S₂ ∧
    ∀ {b},
      reaches₁ (TM1.step tr) ⟨some (goto (λ _ _, go k o q)), v,
        (a, T₁ ++ [stackel.bottom], T₂)⟩ b →
      reaches₁ (TM1.step tr) ⟨some (goto (λ _ _, go k o q)), v,
        (stackel.bottom, [], T)⟩ b
| [] s S₂ (a :: T) hT := by injection hT with es e₂; exact
  ⟨a, [], _, rfl, es, rfl, e₂, λ b rb, trans_gen.head rfl ((reaches₁_eq (by refl)).1 rb)⟩
| (s' :: S₁) s S₂ T hT :=
  let ⟨a, T₁, b'::T₂, e, es', e₁, e₂, H⟩ := tr_respects_aux₁ S₁ hT in
  by injection e₂ with es e₂; exact
  ⟨b', a::T₁, T₂, e, es, by simpa [es'], e₂,
      λ b rb, H (trans_gen.head rfl ((reaches₁_eq (by simp! [es'])).1 rb))⟩

local attribute [simp] TM1.step TM1.step_aux tr tr_st_act st_var st_write
  tape.move tape.write list.reverse_core stackel.get stackel.is_bottom

theorem tr_respects_aux₂
  {k q v} {S : Π k, list (Γ k)} {T₁ T₂ : list Γ'} {a : Γ'}
  (hT : ∀ k, tr_stk (S k) ((T₁.reverse_core (a :: T₂)).map (λ (a : Γ'), a k)))
  (e₁ : T₁.map (λ (a : Γ'), a k) = list.map stackel.val (S k))
  (ea : a k = stackel.top k) (o) :
  let v' := st_var v (S k) o,
      Sk' := st_write v (S k) o,
      S' : ∀ k, list (Γ k) := dwrite S k Sk' in
  ∃ b (T₁' T₂' : list Γ'),
    (∀ (k' : K), tr_stk (S' k') ((T₁'.reverse_core (b :: T₂')).map (λ (a : Γ'), a k'))) ∧
    T₁'.map (λ a, a k) = Sk'.map stackel.val ∧
    b k = stackel.top k ∧
    TM1.step tr ⟨some (tr_st_act q o), v, (a, T₁ ++ [stackel.bottom], T₂)⟩ =
    TM1.step tr ⟨some q, v', (b, T₁' ++ [stackel.bottom], T₂')⟩ :=
begin
  dsimp, cases o with f b f,
  { -- push
    refine ⟨_, dwrite a k (stackel.val (f v)) :: T₁,
      _, _, by simp [e₁]; refl, by simp, rfl⟩,
    intro k', cases hT k' with n e,
    by_cases h : k' = k,
    { subst k', existsi n.pred,
      simp [list.reverse_core_eq, e₁, list.append_left_inj] at e ⊢,
      simp [e] },
    { cases T₂ with t T₂,
      { existsi n+1,
        simpa [h, list.reverse_core_eq, e₁, list.repeat_add] using
          congr_arg (++ [default Γ' k']) e },
      { existsi n,
        simpa [h, list.reverse_core_eq] using e } } },
  have dw := dwrite_self S k,
  cases T₁ with t T₁; cases eS : S k with s Sk;
    rw eS at e₁ dw; injection e₁ with tk e₁'; cases b,
  { -- peek nil
    simp [eS, dw],
    exact ⟨_, [], _, hT, rfl, ea, rfl⟩ },
  { -- pop nil
    simp [eS, dw],
    exact ⟨_, [], _, hT, rfl, ea, rfl⟩ },
  { -- peek cons
    dsimp at tk,
    simp [eS, tk, dw],
    exact ⟨_, t::T₁, _, hT, e₁, ea, rfl⟩ },
  { -- pop cons
    dsimp at tk,
    simp [eS, tk],
    refine ⟨_, _, _, _, e₁', by simp, rfl⟩,
    intro k', cases hT k' with n e,
    by_cases h : k' = k,
    { subst k', existsi n+1,
      simp [list.reverse_core_eq, eS, e₁', list.append_left_inj] at e ⊢,
      simp [e] },
    { existsi n, simpa [h, list.map_reverse_core] using e } },
end

theorem tr_respects_aux₃ {k b q v}
  {S : Π k, list (Γ k)} {T : list Γ'}
  (hT : ∀ k, tr_stk (S k) (T.map (λ (a : Γ'), a k)))
  (rb : reaches₁ (TM1.step tr)
    ⟨some (goto (λ _ _, ret k q)), v, (stackel.bottom, [], T)⟩ b) :
  ∀ (T₁ : list Γ') {T₂ : list Γ'} {a : Γ'} {S₁}
    (e : T = T₁.reverse_core (a :: T₂))
    (ha : (a k).is_bottom = ff)
    (e₁ : T₁.map (λ (a : Γ'), a k) = list.map stackel.val S₁),
    reaches₁ (TM1.step tr) ⟨some (goto (λ _ _, ret k q)), v,
      (a, T₁ ++ [stackel.bottom], T₂)⟩ b
| [] T₂ a S₁ e ha e₁ :=
  trans_gen.head rfl ((reaches₁_eq (by simp [ha, e])).1 rb)
| (b :: T₁) T₂ a (s :: S₁) e ha e₁ := begin
    injection e₁ with es e₁, dsimp at es,
    refine trans_gen.head rfl ((reaches₁_eq _).1
      (tr_respects_aux₃ T₁ e (by simp [es]) e₁)),
    simp [ha]
  end

theorem tr_respects_aux {q v T k} {S : Π k, list (Γ k)}
  (hT : ∀ (k : K), tr_stk (S k) (list.map (λ (a : Γ'), a k) T))
  (o : st_act k)
  (IH : ∀ {v : σ} {S : Π (k : K), list (Γ k)} {T : list Γ'},
    (∀ (k : K), tr_stk (S k) (list.map (λ (a : Γ'), a k) T)) →
    (∃ b, tr_cfg (TM2.step_aux M q v S) b ∧
         reaches₁ (TM1.step tr) ⟨some (tr_normal q), v, (stackel.bottom, [], T)⟩ b)) :
  ∃ b, tr_cfg (TM2.step_aux M (st_run o q) v S) b ∧
    reaches₁ (TM1.step tr) ⟨some (tr_normal (st_run o q)),
      v, (stackel.bottom, [], T)⟩ b :=
begin
  rcases hT k with ⟨n, hTk⟩,
  simp [tr_normal_run],
  rcases tr_respects_aux₁ M o q v _ hTk with ⟨a, T₁, T₂, rfl, ea, e₁, e₂, hgo⟩,
  rcases tr_respects_aux₂ M hT e₁ ea _ with ⟨b, T₁', T₂', hT', e₁', eb, hrun⟩,
  rcases IH hT' with ⟨c, gc, rc⟩,
  simp [step_run],
  refine ⟨c, gc, hgo (trans_gen.head rfl ((reaches₁_eq (by simp [ea]; exact hrun)).2 _))⟩,
  exact tr_respects_aux₃ M hT'
    (trans_gen.head rfl ((reaches₁_eq (by refl)).2 rc)) _ rfl (by simp [eb]) e₁'
end

local attribute [simp] respects TM2.step TM2.step_aux tr_normal

theorem tr_respects : respects (TM2.step M) (TM1.step tr) tr_cfg :=
λ c₁ c₂ h, begin
  cases h with q v S L hT, clear h,
  cases q; simp,
  revert v S L hT, refine stmt_st_rec _ _ _ _ _ q; clear q; intros,
  { exact tr_respects_aux M hT s @IH },
  { exact let ⟨b, c, r⟩ := IH hT in
      ⟨b, c, (reaches₁_eq (by simp)).1 r⟩ },
  { simp, cases e : p v,
    { rcases IH₂ hT with ⟨b, c, r⟩,
      refine ⟨b, c, (reaches₁_eq _).1 r⟩, simp [e] },
    { rcases IH₁ hT with ⟨b, c, r⟩,
      refine ⟨b, c, (reaches₁_eq _).1 r⟩, simp [e] } },
  { exact ⟨_, ⟨hT⟩, trans_gen.single rfl⟩ },
  { exact ⟨_, ⟨hT⟩, trans_gen.single rfl⟩ }
end

theorem tr_cfg_init (k) (L : list (Γ k)) :
  by haveI := Λ'_inh M; exact
  tr_cfg (TM2.init M k L) (TM1.init (tr M) (tr_init k L)) :=
⟨λ k', begin
  simp [tr_init, (∘)],
  cases e : L.reverse with a L'; simp [tr_init],
  { cases list.reverse_eq_nil.1 e, simp, exact ⟨0, rfl⟩ },
  by_cases k' = k,
  { subst k', existsi 0,
    simp [list.reverse_core_eq, (∘)],
    rw [← list.map_reverse, e], refl },
  { simp [h, (∘)],
    existsi L'.length + 1,
    rw list.repeat_add, refl }
end⟩

theorem tr_eval_dom (k) (L : list (Γ k)) :
  by haveI := Λ'_inh M; exact
  (TM1.eval (tr M) (tr_init k L)).dom ↔ (TM2.eval M k L).dom :=
tr_eval_dom tr_respects (tr_cfg_init _ _)

theorem tr_eval (k) (L : list (Γ k)) {L₁ L₂}
  (H₁ : by haveI := Λ'_inh M; exact
        L₁ ∈ TM1.eval (tr M) (tr_init k L))
  (H₂ : L₂ ∈ TM2.eval M k L) :
  ∃ S : ∀ k, list (Γ k),
    (∀ k', tr_stk (S k') (L₁.map (λ a, a k'))) ∧ S k = L₂ :=
begin
  rcases (roption.mem_map_iff _).1 H₁ with ⟨c₁, h₁, rfl⟩,
  rcases (roption.mem_map_iff _).1 H₂ with ⟨c₂, h₂, rfl⟩,
  rcases tr_eval (tr_respects M) (tr_cfg_init M k L) h₂
    with ⟨_, ⟨q, v, S, L₁', hT⟩, h₃⟩,
  cases roption.mem_unique h₁ h₃,
  exact ⟨S, hT, rfl⟩
end

variables [fintype K] [∀ k, fintype (Γ k)] [fintype σ]
local attribute [instance] classical.dec
local attribute [simp] TM2.stmts₁_self

noncomputable def tr_stmts₁ : stmt₂ → finset Λ'
| Q@(TM2.stmt.push k f q)     := {go k (st_act.push f) q, ret k q} ∪ tr_stmts₁ q
| Q@(TM2.stmt.peek k f q)     := {go k (st_act.pop ff f) q, ret k q} ∪ tr_stmts₁ q
| Q@(TM2.stmt.pop k f q)      := {go k (st_act.pop tt f) q, ret k q} ∪ tr_stmts₁ q
| Q@(TM2.stmt.load a q)       := tr_stmts₁ q
| Q@(TM2.stmt.branch f q₁ q₂) := tr_stmts₁ q₁ ∪ tr_stmts₁ q₂
| _                           := ∅

theorem tr_stmts₁_run {k s q} : tr_stmts₁ (st_run s q) = {go k s q, ret k q} ∪ tr_stmts₁ q :=
by rcases s with _|_|_; dsimp [tr_stmts₁, st_run]; congr

noncomputable def tr_supp (S : finset Λ) : finset Λ' :=
S.bind (λ l, insert (normal (M l)) (tr_stmts₁ (M l)))

local attribute [simp] tr_stmts₁ tr_stmts₁_run supports_run
  tr_normal_run TM1.supports_stmt TM2.supports_stmt

theorem tr_supports {S} (ss : TM2.supports M S) :
  by haveI := Λ'_inh M; exact
  TM1.supports (tr M) (tr_supp M S) :=
⟨finset.mem_bind.2 ⟨_, ss.1, finset.mem_insert.2 $ or.inl rfl⟩,
λ l' h, begin
  letI := Λ'_inh M,
  suffices : ∀ q l' (ss' : TM2.supports_stmt S q)
    (h : l' = turing.TM2to1.Λ'.normal q ∨ l' ∈ tr_stmts₁ M q)
    (sub : ∀ x ∈ tr_stmts₁ M q, x ∈ tr_supp M S),
    TM1.supports_stmt (tr_supp M S) (tr M l'),
  { simp [tr_supp] at h,
    rcases h with ⟨l, lS, h⟩,
    exact this _ _ (ss.2 l lS) h (λ x hx,
      finset.mem_bind.2 ⟨_, lS, finset.mem_insert_of_mem hx⟩) },
  refine stmt_st_rec _ _ _ _ _; clear h l'; intros,
  { -- stack op
    simp at h sub ss',
    have hgo := sub _ (or.inr $ or.inr rfl),
    have hret := sub _ (or.inl rfl),
    rcases h with rfl | rfl | h | rfl,
    { simp [hgo] },
    { simp [hret],
      exact IH (normal q) ss' (or.inl rfl)
        (λ x hx, sub x $ or.inr $ or.inl hx) },
    { exact IH _ ss' (or.inr h)
        (λ x hx, sub x $ or.inr $ or.inl hx) },
    { simp [hgo],
      rcases s with _|_|_; simp! [hret] } },
  { -- load
    dsimp at h sub, rcases h with rfl | h,
    { exact IH _ ss' (or.inl rfl) sub },
    { exact IH _ ss' (or.inr h) sub } },
  { -- branch
    simp at h sub, rcases h with rfl | h | h,
    { exact ⟨
        IH₁ _ ss'.1 (or.inl rfl) (λ x hx, sub x $ or.inl hx),
        IH₂ _ ss'.2 (or.inl rfl) (λ x hx, sub x $ or.inr hx)⟩ },
    { exact IH₁ _ ss'.1 (or.inr h) (λ x hx, sub x $ or.inl hx) },
    { exact IH₂ _ ss'.2 (or.inr h) (λ x hx, sub x $ or.inr hx) } },
  { -- goto
    simp at h, subst h,
    exact λ a s, finset.mem_bind.2 ⟨_, ss' s, by simp⟩ },
  { -- halt
    simp at h, subst h, trivial }
end⟩

end

end TM2to1

end turing
