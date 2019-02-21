/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Define a sequence of simple machine languages, starting with Turing
machines and working up to more complex lanaguages based on
Wang B-machines.
-/
import data.fintype data.pfun logic.relation

open relation

namespace turing

/-- A direction for the turing machine `move` command, either
  left or right. -/
@[derive decidable_eq]
inductive dir | left | right

def tape (Γ) := Γ × list Γ × list Γ

def tape.mk {Γ} [inhabited Γ] (l : list Γ) : tape Γ :=
(l.head, [], l.tail)

def tape.mk' {Γ} [inhabited Γ] (L R : list Γ) : tape Γ :=
(R.head, L, R.tail)

def tape.move {Γ} [inhabited Γ] : dir → tape Γ → tape Γ
| dir.left (a, L, R) := (L.head, L.tail, a :: R)
| dir.right (a, L, R) := (R.head, a :: L, R.tail)

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

def tape.write {Γ} (b : Γ) : tape Γ → tape Γ
| (a, LR) := (b, LR)

@[simp] theorem tape.write_self {Γ} : ∀ (T : tape Γ), T.write T.1 = T
| (a, LR) := rfl

@[simp] theorem tape.write_nth {Γ} [inhabited Γ] (b : Γ) :
  ∀ (T : tape Γ) {i : ℤ}, (T.write b).nth i = if i = 0 then b else T.nth i
| (a, L, R) 0       := rfl
| (a, L, R) (n+1:ℕ) := rfl
| (a, L, R) -[1+ n] := rfl

def tape.map {Γ Γ'} (f : Γ → Γ') : tape Γ → tape Γ'
| (a, L, R) := (f a, L.map f, R.map f)

@[simp] theorem tape.map_fst {Γ Γ'} (f : Γ → Γ') : ∀ (T : tape Γ), (T.map f).1 = f T.1
| (a, L, R) := rfl

@[simp] theorem tape.map_write {Γ Γ'} (f : Γ → Γ') (b : Γ) :
  ∀ (T : tape Γ), (T.write b).map f = (T.map f).write (f b)
| (a, L, R) := rfl

@[class] def pointed_map {Γ Γ'} [inhabited Γ] [inhabited Γ'] (f : Γ → Γ') :=
f (default _) = default _

theorem tape.map_move {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : Γ → Γ') [pointed_map f] :
  ∀ (T : tape Γ) d, (T.move d).map f = (T.map f).move d
| (a, [],   R) dir.left  := prod.ext ‹pointed_map f› rfl
| (a, b::L, R) dir.left  := rfl
| (a, L, [])   dir.right := prod.ext ‹pointed_map f› rfl
| (a, L, b::R) dir.right := rfl

theorem tape.map_mk {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : Γ → Γ') [f0 : pointed_map f] :
  ∀ (l : list Γ), (tape.mk l).map f = tape.mk (l.map f)
| []     := prod.ext ‹pointed_map f› rfl
| (a::l) := rfl

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

theorem reaches₁_fwd {σ} {f : σ → option σ}
  {a b c} (h₁ : reaches₁ f a c) (h₂ : b ∈ f a) : reaches f b c :=
begin
  rcases trans_gen.head'_iff.1 h₁ with ⟨b', hab, hbc⟩,
  cases option.mem_unique hab h₂, exact hbc
end

def reaches₀ {σ} (f : σ → option σ) (a b : σ) : Prop :=
∀ c, reaches₁ f b c → reaches₁ f a c

theorem reaches₀.trans {σ} {f : σ → option σ} {a b c : σ}
  (h₁ : reaches₀ f a b) (h₂ : reaches₀ f b c) : reaches₀ f a c
| d h₃ := h₁ _ (h₂ _ h₃)

@[refl] theorem reaches₀.refl {σ} {f : σ → option σ} (a : σ) : reaches₀ f a a
| b h := h

theorem reaches₀.single {σ} {f : σ → option σ} {a b : σ}
  (h : b ∈ f a) : reaches₀ f a b
| c h₂ := h₂.head h

theorem reaches₀.head {σ} {f : σ → option σ} {a b c : σ}
  (h : b ∈ f a) (h₂ : reaches₀ f b c) : reaches₀ f a c :=
(reaches₀.single h).trans h₂

theorem reaches₀.tail {σ} {f : σ → option σ} {a b c : σ}
  (h₁ : reaches₀ f a b) (h : c ∈ f b) : reaches₀ f a c :=
h₁.trans (reaches₀.single h)

theorem reaches₀_eq {σ} {f : σ → option σ} {a b}
  (e : f a = f b) : reaches₀ f a b
| d h := (reaches₁_eq e).2 h

theorem reaches₁.to₀ {σ} {f : σ → option σ} {a b : σ}
  (h : reaches₁ f a b) : reaches₀ f a b
| c h₂ := h.trans h₂

theorem reaches.to₀ {σ} {f : σ → option σ} {a b : σ}
  (h : reaches f a b) : reaches₀ f a b
| c h₂ := h₂.trans_right h

theorem reaches₀.tail' {σ} {f : σ → option σ} {a b c : σ}
  (h : reaches₀ f a b) (h₂ : c ∈ f b) : reaches₁ f a c :=
h _ (trans_gen.single h₂)

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
| none := by unfold frespects; rw h

theorem fun_respects {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂} :
  respects f₁ f₂ (λ a b, tr a = b) ↔ ∀ ⦃a₁⦄, frespects f₂ tr (tr a₁) (f₁ a₁) :=
forall_congr $ λ a₁, by cases f₁ a₁; simp only [frespects, respects, exists_eq_left', forall_eq']

theorem tr_eval' {σ₁ σ₂}
  (f₁ : σ₁ → option σ₁) (f₂ : σ₂ → option σ₂) (tr : σ₁ → σ₂)
  (H : respects f₁ f₂ (λ a b, tr a = b))
  (a₁) : eval f₂ (tr a₁) = tr <$> eval f₁ a₁ :=
roption.ext $ λ b₂,
 ⟨λ h, let ⟨b₁, bb, hb⟩ := tr_eval_rev H rfl h in
    (roption.mem_map_iff _).2 ⟨b₁, hb, bb⟩,
  λ h, begin
    rcases (roption.mem_map_iff _).1 h with ⟨b₁, ab, bb⟩,
    rcases tr_eval H rfl ab with ⟨_, rfl, h⟩,
    rwa bb at h
  end⟩

def dwrite {K} [decidable_eq K] {C : K → Type*}
  (S : ∀ k, C k) (k') (l : C k') (k) : C k :=
if h : k = k' then eq.rec_on h.symm l else S k

@[simp] theorem dwrite_eq {K} [decidable_eq K] {C : K → Type*}
  (S : ∀ k, C k) (k) (l : C k) : dwrite S k l k = l :=
dif_pos rfl

@[simp] theorem dwrite_ne {K} [decidable_eq K] {C : K → Type*}
  (S : ∀ k, C k) (k') (l : C k') (k) (h : ¬ k = k') : dwrite S k' l k = S k :=
dif_neg h

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
def init (l : list Γ) : cfg :=
⟨default Λ, tape.mk l⟩

/-- Evaluate a Turing machine on initial input to a final state,
  if it terminates. -/
def eval (M : machine) (l : list Γ) : roption (list Γ) :=
(eval (step M) (init l)).map (λ c, c.tape.2.2)

/-- The raw definition of a Turing machine does not require that
  `Γ` and `Λ` are finite, and in practice we will be interested
  in the infinite `Λ` case. We recover instead a notion of
  "effectively finite" Turing machines, which only make use of a
  finite subset of their states. We say that a set `S ⊆ Λ`
  supports a Turing machine `M` if `S` is closed under the
  transition function and contains the initial state. -/
def supports (M : machine) (S : set Λ) :=
default Λ ∈ S ∧ ∀ {q a q' s}, (q', s) ∈ M q a → q ∈ S → q' ∈ S

theorem step_supports (M : machine) {S}
  (ss : supports M S) : ∀ {c c' : cfg},
  c' ∈ step M c → c.q ∈ S → c'.q ∈ S
| ⟨q, T⟩ c' h₁ h₂ := begin
  rcases option.map_eq_some'.1 h₁ with ⟨⟨q', a⟩, h, rfl⟩,
  exact ss.2 h h₂,
end

theorem univ_supports (M : machine) : supports M set.univ :=
⟨trivial, λ q a q' s h₁ h₂, trivial⟩

end

section
variables {Γ : Type*} [inhabited Γ]
variables {Γ' : Type*} [inhabited Γ']
variables {Λ : Type*} [inhabited Λ]
variables {Λ' : Type*} [inhabited Λ']

def stmt.map (f : Γ → Γ') : stmt Γ → stmt Γ'
| (stmt.move d)  := stmt.move d
| (stmt.write a) := stmt.write (f a)

def cfg.map (f : Γ → Γ') (g : Λ → Λ') : cfg Γ Λ → cfg Γ' Λ'
| ⟨q, T⟩ := ⟨g q, T.map f⟩

variables (M : machine Γ Λ)
  (f₁ : Γ → Γ') (f₂ : Γ' → Γ) (g₁ : Λ → Λ') (g₂ : Λ' → Λ)

def machine.map : machine Γ' Λ'
| q l := (M (g₂ q) (f₂ l)).map (prod.map g₁ (stmt.map f₁))

theorem machine.map_step {S} (ss : supports M S)
  [pointed_map f₁] (f₂₁ : function.right_inverse f₁ f₂)
  (g₂₁ : ∀ q ∈ S, g₂ (g₁ q) = q) :
  ∀ c : cfg Γ Λ, c.q ∈ S → 
    (step M c).map (cfg.map f₁ g₁) =
    step (M.map f₁ f₂ g₁ g₂) (cfg.map f₁ g₁ c)
| ⟨q, T⟩ h := begin
  unfold step machine.map cfg.map,
  simp only [turing.tape.map_fst, g₂₁ q h, f₂₁ _],
  rcases M q T.1 with _|⟨q', d|a⟩, {refl},
  { simp only [step, cfg.map, option.map_some', tape.map_move f₁], refl },
  { simp only [step, cfg.map, option.map_some', tape.map_write], refl }
end

theorem map_init [pointed_map f₁] [g0 : pointed_map g₁] (l : list Γ) :
  (init l).map f₁ g₁ = init (l.map f₁) :=
congr (congr_arg cfg.mk g0) (tape.map_mk _ _)

theorem machine.map_respects {S} (ss : supports M S)
  [pointed_map f₁] [pointed_map g₁]
  (f₂₁ : function.right_inverse f₁ f₂)
  (g₂₁ : ∀ q ∈ S, g₂ (g₁ q) = q) :
  respects (step M) (step (M.map f₁ f₂ g₁ g₂))
    (λ a b, a.q ∈ S ∧ cfg.map f₁ g₁ a = b)
| c _ ⟨cs, rfl⟩ := begin
  cases e : step M c with c'; unfold respects,
  { rw [← M.map_step f₁ f₂ g₁ g₂ ss f₂₁ g₂₁ _ cs, e], refl },
  { refine ⟨_, ⟨step_supports M ss e cs, rfl⟩, trans_gen.single _⟩,
    rw [← M.map_step f₁ f₂ g₁ g₂ ss f₂₁ g₂₁ _ cs, e], exact rfl }
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
(l : option Λ)
(var : σ)
(tape : tape Γ)

parameters {Γ Λ σ}
/-- The semantics of TM1 evaluation. -/
def step_aux : stmt → σ → tape Γ → cfg
| (move d q)       v T := step_aux q v (T.move d)
| (write a q)      v T := step_aux q v (T.write (a T.1 v))
| (load s q)       v T := step_aux q (s T.1 v) T
| (branch p q₁ q₂) v T :=
  cond (p T.1 v) (step_aux q₁ v T) (step_aux q₂ v T)
| (goto l)         v T := ⟨some (l T.1 v), v, T⟩
| halt             v T := ⟨none, v, T⟩

def step (M : Λ → stmt) : cfg → option cfg
| ⟨none,   v, T⟩ := none
| ⟨some l, v, T⟩ := some (step_aux (M l) v T)

variables [inhabited Λ] [inhabited σ]
def init (l : list Γ) : cfg :=
⟨some (default _), default _, tape.mk l⟩

def eval (M : Λ → stmt) (l : list Γ) : roption (list Γ) :=
(eval (step M) (init l)).map (λ c, c.tape.2.2)

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
by cases q; apply finset.mem_insert_self

theorem stmts₁_trans {q₁ q₂} :
  q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ :=
begin
  intros h₁₂ q₀ h₀₁,
  induction q₂ with _ q IH _ q IH _ q IH;
    simp only [stmts₁] at h₁₂ ⊢;
    simp only [finset.mem_insert, finset.mem_union,
      finset.insert_empty_eq_singleton, finset.mem_singleton] at h₁₂,
  iterate 3 {
    rcases h₁₂ with rfl | h₁₂,
    { unfold stmts₁ at h₀₁, exact h₀₁ },
    { exact finset.mem_insert_of_mem (IH h₁₂) } },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    rcases h₁₂ with rfl | h₁₂ | h₁₂,
    { unfold stmts₁ at h₀₁, exact h₀₁ },
    { exact finset.mem_insert_of_mem (finset.mem_union_left _ $ IH₁ h₁₂) },
    { exact finset.mem_insert_of_mem (finset.mem_union_right _ $ IH₂ h₁₂) } },
  case TM1.stmt.goto : l {
    subst h₁₂, exact h₀₁ },
  case TM1.stmt.halt {
    subst h₁₂, exact h₀₁ }
end

theorem stmts₁_supports_stmt_mono {S q₁ q₂}
  (h : q₁ ∈ stmts₁ q₂) (hs : supports_stmt S q₂) : supports_stmt S q₁ :=
begin
  induction q₂ with _ q IH _ q IH _ q IH;
    simp only [stmts₁, supports_stmt, finset.mem_insert, finset.mem_union,
      finset.insert_empty_eq_singleton, finset.mem_singleton] at h hs,
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
by simp only [stmts, finset.mem_insert_none, finset.mem_bind,
  option.mem_def, forall_eq', exists_imp_distrib];
exact λ l ls h₂, ⟨_, ls, stmts₁_trans h₂ h₁⟩

theorem stmts_supports_stmt {M : Λ → stmt} {S q}
  (ss : supports M S) : some q ∈ stmts M S → supports_stmt S q :=
by simp only [stmts, finset.mem_insert_none, finset.mem_bind,
  option.mem_def, forall_eq', exists_imp_distrib];
exact λ l ls h, stmts₁_supports_stmt_mono h (ss.2 _ ls)

theorem step_supports (M : Λ → stmt) {S}
  (ss : supports M S) : ∀ {c c' : cfg},
  c' ∈ step M c → c.l ∈ S.insert_none → c'.l ∈ S.insert_none
| ⟨some l₁, v, T⟩ c' h₁ h₂ := begin
  replace h₂ := ss.2 _ (finset.some_mem_insert_none.1 h₂),
  simp only [step, option.mem_def] at h₁, subst c',
  revert h₂, induction M l₁ with _ q IH _ q IH _ q IH generalizing v T;
    intro hs,
  iterate 3 { exact IH _ _ hs },
  case TM1.stmt.branch : p q₁' q₂' IH₁ IH₂ {
    unfold step_aux, cases p T.1 v,
    { exact IH₂ _ _ hs.2 },
    { exact IH₁ _ _ hs.1 } },
  case TM1.stmt.goto { exact finset.some_mem_insert_none.2 (hs _ _) },
  case TM1.stmt.halt { apply multiset.mem_cons_self }
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

def tr_cfg : cfg₁ → cfg₀
| ⟨l, v, T⟩ := ⟨(l.map M, v), T⟩

theorem tr_respects : respects (TM1.step M) (TM0.step tr)
  (λ c₁ c₂, tr_cfg c₁ = c₂) :=
fun_respects.2 $ λ ⟨l₁, v, T⟩, begin
  cases l₁ with l₁, {exact rfl},
  unfold tr_cfg TM1.step frespects option.map function.comp option.bind,
  induction M l₁ with _ q IH _ q IH _ q IH generalizing v T,
  case TM1.stmt.move  : d q IH { exact trans_gen.head rfl (IH _ _) },
  case TM1.stmt.write : a q IH { exact trans_gen.head rfl (IH _ _) },
  case TM1.stmt.load : a q IH { exact (reaches₁_eq (by refl)).2 (IH _ _) },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    unfold TM1.step_aux, cases e : p T.1 v,
    { exact (reaches₁_eq (by simp only [TM0.step, tr, tr_aux, e]; refl)).2 (IH₂ _ _) },
    { exact (reaches₁_eq (by simp only [TM0.step, tr, tr_aux, e]; refl)).2 (IH₁ _ _) } },
  iterate 2 {
    exact trans_gen.single (congr_arg some
      (congr (congr_arg TM0.cfg.mk rfl) (tape.write_self T))) }
end

variables [fintype Γ] [fintype σ]
noncomputable def tr_stmts (S : finset Λ) : finset Λ' :=
(TM1.stmts M S).product finset.univ

local attribute [instance] classical.dec
local attribute [simp] TM1.stmts₁_self
theorem tr_supports {S : finset Λ} (ss : TM1.supports M S) :
  TM0.supports tr (↑(tr_stmts S)) :=
⟨finset.mem_product.2 ⟨finset.some_mem_insert_none.2
  (finset.mem_bind.2 ⟨_, ss.1, TM1.stmts₁_self⟩),
  finset.mem_univ _⟩,
 λ q a q' s h₁ h₂, begin
  rcases q with ⟨_|q, v⟩, {cases h₁},
  cases q' with q' v', simp only [tr_stmts, finset.mem_coe,
    finset.mem_product, finset.mem_univ, and_true] at h₂ ⊢,
  cases q', {exact multiset.mem_cons_self _ _},
  simp only [tr, option.mem_def] at h₁,
  have := TM1.stmts_supports_stmt ss h₂,
  revert this, induction q generalizing v; intro hs,
  case TM1.stmt.move : d q {
    cases h₁, refine TM1.stmts_trans _ h₂,
    unfold TM1.stmts₁,
    exact finset.mem_insert_of_mem TM1.stmts₁_self },
  case TM1.stmt.write : b q {
    cases h₁, refine TM1.stmts_trans _ h₂,
    unfold TM1.stmts₁,
    exact finset.mem_insert_of_mem TM1.stmts₁_self },
  case TM1.stmt.load : b q IH {
    refine IH (TM1.stmts_trans _ h₂) _ h₁ hs,
    unfold TM1.stmts₁,
    exact finset.mem_insert_of_mem TM1.stmts₁_self },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    change cond (p a v) _ _ = ((some q', v'), s) at h₁,
    cases p a v,
    { refine IH₂ (TM1.stmts_trans _ h₂) _ h₁ hs.2,
      unfold TM1.stmts₁,
      exact finset.mem_insert_of_mem (finset.mem_union_right _ TM1.stmts₁_self) },
    { refine IH₁ (TM1.stmts_trans _ h₂) _ h₁ hs.1,
      unfold TM1.stmts₁,
      exact finset.mem_insert_of_mem (finset.mem_union_left _ TM1.stmts₁_self) } },
  case TM1.stmt.goto : l {
    cases h₁, exact finset.some_mem_insert_none.2
      (finset.mem_bind.2 ⟨_, hs _ _, TM1.stmts₁_self⟩) },
  case TM1.stmt.halt { cases h₁ }
end⟩

theorem tr_eval (l : list Γ) : TM0.eval tr l = TM1.eval M l :=
(congr_arg _ (tr_eval' _ _ _ tr_respects ⟨some _, _, _⟩)).trans begin
  rw [roption.map_eq_map, roption.map_map, TM1.eval],
  congr', exact funext (λ ⟨_, _, _⟩, rfl)
end

end
end TM1to0

/- Reduce an n-symbol Turing machine to a 2-symbol Turing machine -/
namespace TM1to1
open TM1

section
parameters {Γ : Type*} [inhabited Γ]

theorem exists_enc_dec [fintype Γ] :
  ∃ n (enc : Γ → vector bool n) (dec : vector bool n → Γ),
    enc (default _) = vector.repeat ff n ∧ ∀ a, dec (enc a) = a :=
begin
  rcases fintype.exists_equiv_fin Γ with ⟨n, ⟨F⟩⟩,
  let G : fin n ↪ fin n → bool := ⟨λ a b, a = b,
    λ a b h, of_to_bool_true $ (congr_fun h b).trans $ to_bool_tt rfl⟩,
  let H := (F.to_embedding.trans G).trans
    (equiv.vector_equiv_fin _ _).symm.to_embedding,
  let enc := H.set_value (default _) (vector.repeat ff n),
  exact ⟨_, enc, function.inv_fun enc,
    H.set_value_eq _ _, function.left_inverse_inv_fun enc.2⟩
end

parameters {Λ : Type*} [inhabited Λ]
parameters {σ : Type*} [inhabited σ]

local notation `stmt₁` := stmt Γ Λ σ
local notation `cfg₁` := cfg Γ Λ σ

inductive Λ' : Type (max u_1 u_2 u_3)
| normal : Λ → Λ'
| write : Γ → stmt₁ → Λ'
instance : inhabited Λ' := ⟨Λ'.normal (default _)⟩

local notation `stmt'` := stmt bool Λ' σ
local notation `cfg'` := cfg bool Λ' σ

def read_aux : ∀ n, (vector bool n → stmt') → stmt'
| 0     f := f vector.nil
| (i+1) f := stmt.branch (λ a s, a)
    (stmt.move dir.right $ read_aux i (λ v, f (tt :: v)))
    (stmt.move dir.right $ read_aux i (λ v, f (ff :: v)))

parameters {n : ℕ} (enc : Γ → vector bool n) (dec : vector bool n → Γ)

def move (d : dir) (q : stmt') : stmt' := (stmt.move d)^[n] q

def read (f : Γ → stmt') : stmt' :=
read_aux n (λ v, move dir.left $ f (dec v))

def write : list bool → stmt' → stmt'
| []       q := q
| (a :: l) q := stmt.write (λ _ _, a) $ stmt.move dir.right $ write l q

def tr_normal : stmt₁ → stmt'
| (stmt.move dir.left q)  := move dir.right $ (move dir.left)^[2] $ tr_normal q
| (stmt.move dir.right q) := move dir.right $ tr_normal q
| (stmt.write f q)        := read $ λ a, stmt.goto $ λ _ s, Λ'.write (f a s) q
| (stmt.load f q)         := read $ λ a, stmt.load (λ _ s, f a s) $ tr_normal q
| (stmt.branch p q₁ q₂)   := read $ λ a,
  stmt.branch (λ _ s, p a s) (tr_normal q₁) (tr_normal q₂)
| (stmt.goto l)           := read $ λ a,
  stmt.goto (λ _ s, Λ'.normal (l a s))
| stmt.halt               := move dir.right $ move dir.left $ stmt.halt

def tr_tape' (L R : list Γ) : tape bool :=
tape.mk'
  (L.bind (λ x, (enc x).to_list.reverse))
  (R.bind (λ x, (enc x).to_list) ++ [default _])

def tr_tape : tape Γ → tape bool
| (a, L, R) := tr_tape' L (a :: R)

theorem tr_tape_drop_right : ∀ R : list Γ,
  list.drop n (R.bind (λ x, (enc x).to_list)) =
  R.tail.bind (λ x, (enc x).to_list)
| []     := list.drop_nil _
| (a::R) := list.drop_left' (enc a).2

parameters (enc0 : enc (default _) = vector.repeat ff n)

section
include enc0
theorem tr_tape_take_right : ∀ R : list Γ,
  list.take' n (R.bind (λ x, (enc x).to_list)) =
  (enc R.head).to_list
| []     := show list.take' n list.nil = _,
    by rw [list.take'_nil]; exact (congr_arg vector.to_list enc0).symm
| (a::R) := list.take'_left' (enc a).2
end

parameters (M : Λ → stmt₁)

def tr : Λ' → stmt'
| (Λ'.normal l)  := tr_normal (M l)
| (Λ'.write a q) := write (enc a).to_list $ move dir.left $ tr_normal q

def tr_cfg : cfg₁ → cfg'
| ⟨l, v, T⟩ := ⟨l.map Λ'.normal, v, tr_tape T⟩

include enc0

theorem tr_tape'_move_left (L R) :
  (tape.move dir.left)^[n] (tr_tape' L R) =
  (tr_tape' L.tail (L.head :: R)) :=
begin
  cases L with a L,
  { simp only [enc0, vector.repeat, tr_tape',
      list.cons_bind, list.head, list.append_assoc],
    suffices : ∀ i R', default _ ∈ R' →
      (tape.move dir.left^[i]) (tape.mk' [] R') =
      tape.mk' [] (list.repeat ff i ++ R'),
    from this n _ (list.mem_append_right _
      (list.mem_singleton_self _)),
    intros i R' hR, induction i with i IH, {refl},
    rw [nat.iterate_succ', IH],
    refine prod.ext rfl (prod.ext rfl (list.cons_head_tail
      (list.ne_nil_of_mem $ list.mem_append_right _ hR))) },
  { simp only [tr_tape', list.cons_bind, list.append_assoc],
    suffices : ∀ L' R' l₁ l₂
      (hR : default _ ∈ R')
      (e : vector.to_list (enc a) = list.reverse_core l₁ l₂),
      (tape.move dir.left^[l₁.length]) (tape.mk' (l₁ ++ L') (l₂ ++ R')) =
      tape.mk' L' (vector.to_list (enc a) ++ R'),
    { simpa only [list.length_reverse, vector.to_list_length]
        using this _ _ _ _ _ (list.reverse_reverse _).symm,
      exact list.mem_append_right _ (list.mem_singleton_self _) },
    intros, induction l₁ with b l₁ IH generalizing l₂,
    { cases e, refl },
    simp only [list.length, list.cons_append, nat.iterate_succ],
    convert IH _ e,
    exact prod.ext rfl (prod.ext rfl (list.cons_head_tail
      (list.ne_nil_of_mem $ list.mem_append_right _ hR))) }
end

theorem tr_tape'_move_right (L R) :
  (tape.move dir.right)^[n] (tr_tape' L R) =
  (tr_tape' (R.head :: L) R.tail) :=
begin
  cases R with a R,
  { simp only [enc0, vector.repeat, tr_tape', list.head,
      list.cons_bind, vector.to_list_mk, list.reverse_repeat],
    suffices : ∀ i L',
      (tape.move dir.right^[i]) (ff, L', []) =
      (ff, list.repeat ff i ++ L', []),
    from this n _,
    intros, induction i with i IH, {refl},
    rw [nat.iterate_succ', IH],
    refine prod.ext rfl (prod.ext rfl rfl) },
  { simp only [tr_tape', list.cons_bind, list.append_assoc],
    suffices : ∀ L' R' l₁ l₂ : list bool,
      (tape.move dir.right^[l₂.length]) (tape.mk' (l₁ ++ L') (l₂ ++ R')) =
      tape.mk' (list.reverse_core l₂ l₁ ++ L') R',
    { simpa only [vector.to_list_length] using this _ _ [] (enc a).to_list },
    intros, induction l₂ with b l₂ IH generalizing l₁, {refl},
    exact IH (b::l₁) }
end

theorem step_aux_move (d q v T) :
  step_aux (move d q) v T =
  step_aux q v ((tape.move d)^[n] T) :=
begin
  suffices : ∀ i,
    step_aux (stmt.move d^[i] q) v T =
    step_aux q v (tape.move d^[i] T), from this n,
  intro, induction i with i IH generalizing T, {refl},
  rw [nat.iterate_succ', step_aux, IH, ← nat.iterate_succ]
end

parameters (encdec : ∀ a, dec (enc a) = a)
include encdec

theorem step_aux_read (f v L R) :
  step_aux (read f) v (tr_tape' L R) =
  step_aux (f R.head) v (tr_tape' L (R.head :: R.tail)) :=
begin
  suffices : ∀ f,
    step_aux (read_aux n f) v (tr_tape' enc L R) =
    step_aux (f (enc R.head)) v
      (tr_tape' enc (R.head :: L) R.tail),
  { rw [read, this, step_aux_move enc enc0, encdec,
      tr_tape'_move_left enc enc0], refl },
  cases R with a R,
  { suffices : ∀ i f L',
      step_aux (read_aux i f) v (ff, L', []) =
      step_aux (f (vector.repeat ff i)) v
        (ff, list.repeat ff i ++ L', []),
    { intro f, convert this n f _,
      refine prod.ext rfl (prod.ext ((list.cons_bind _ _ _).trans _) rfl),
      simp only [list.head, enc0, vector.repeat, vector.to_list, list.reverse_repeat] },
    clear f L, intros, induction i with i IH generalizing L', {refl},
    change step_aux (read_aux i (λ v, f (ff :: v))) v (ff, ff :: L', [])
      = step_aux (f (vector.repeat ff (nat.succ i))) v (ff, ff :: (list.repeat ff i ++ L'), []),
    rw [IH], congr',
    simpa only [list.append_assoc] using congr_arg (++ L') (list.repeat_add ff i 1).symm },
  { simp only [tr_tape', list.cons_bind, list.append_assoc],
    suffices : ∀ i f L' R' l₁ l₂ h,
      step_aux (read_aux i f) v
        (tape.mk' (l₁ ++ L') (l₂ ++ R')) =
      step_aux (f ⟨l₂, h⟩) v
        (tape.mk' (l₂.reverse_core l₁ ++ L') R'),
    { intro f, convert this n f _ _ _ _ (enc a).2;
        simp only [subtype.eta]; refl },
    clear f L a R, intros, subst i,
    induction l₂ with a l₂ IH generalizing l₁, {refl},
    change (tape.mk' (l₁ ++ L') (a :: (l₂ ++ R'))).1 with a,
    transitivity step_aux
      (read_aux l₂.length (λ v, f (a :: v))) v
      (tape.mk' (a :: l₁ ++ L') (l₂ ++ R')),
    { cases a; refl },
    rw IH, refl }
end

theorem step_aux_write (q v a b L R) :
  step_aux (write (enc a).to_list q) v (tr_tape' L (b :: R)) =
  step_aux q v (tr_tape' (a :: L) R) :=
begin
  simp only [tr_tape', list.cons_bind, list.append_assoc],
  suffices : ∀ {L' R'} (l₁ l₂ l₂' : list bool)
    (e : l₂'.length = l₂.length),
    step_aux (write l₂ q) v (tape.mk' (l₁ ++ L') (l₂' ++ R')) =
    step_aux q v (tape.mk' (list.reverse_core l₂ l₁ ++ L') R'),
  from this [] _ _ ((enc b).2.trans (enc a).2.symm),
  clear a b L R, intros,
  induction l₂ with a l₂ IH generalizing l₁ l₂',
  { cases list.length_eq_zero.1 e, refl },
  cases l₂' with b l₂'; injection e with e,
  unfold write step_aux,
  convert IH _ _ e, refl
end

theorem tr_respects : respects (step M) (step tr)
  (λ c₁ c₂, tr_cfg c₁ = c₂) :=
fun_respects.2 $ λ ⟨l₁, v, (a, L, R)⟩, begin
  cases l₁ with l₁, {exact rfl},
  suffices : ∀ q R, reaches (step (tr enc dec M))
    (step_aux (tr_normal dec q) v (tr_tape' enc L R))
    (tr_cfg enc (step_aux q v (tape.mk' L R))),
  { refine trans_gen.head' rfl (this _ (a::R)) },
  clear R l₁, intros,
  induction q with _ q IH _ q IH _ q IH generalizing v L R,
  case TM1.stmt.move : d q IH {
    cases d; simp only [tr_normal, nat.iterate, step_aux_move enc enc0, step_aux,
      tr_tape'_move_left enc enc0, tr_tape'_move_right enc enc0];
      apply IH },
  case TM1.stmt.write : a q IH {
    simp only [tr_normal, step_aux_read enc dec enc0 encdec, step_aux],
    refine refl_trans_gen.head rfl _,
    simp only [tr, tr_normal, step_aux,
      step_aux_write enc dec enc0 encdec,
      step_aux_move enc enc0, tr_tape'_move_left enc enc0],
    apply IH },
  case TM1.stmt.load : a q IH {
    simp only [tr_normal, step_aux_read enc dec enc0 encdec],
    apply IH },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    simp only [tr_normal, step_aux_read enc dec enc0 encdec, step_aux],
    change (tape.mk' L R).1 with R.head,
    cases p R.head v; [apply IH₂, apply IH₁] },
  case TM1.stmt.goto : l {
    simp only [tr_normal, step_aux_read enc dec enc0 encdec, step_aux], 
    apply refl_trans_gen.refl },
  case TM1.stmt.halt {
    simp only [tr_normal, step_aux, tr_cfg, step_aux_move enc enc0,
      tr_tape'_move_left enc enc0, tr_tape'_move_right enc enc0],
    apply refl_trans_gen.refl }
end

omit enc0 encdec
local attribute [instance] classical.dec
parameters [fintype Γ]
noncomputable def writes : stmt₁ → finset Λ'
| (stmt.move d q)       := writes q
| (stmt.write f q)      := finset.univ.image (λ a, Λ'.write a q) ∪ writes q
| (stmt.load f q)       := writes q
| (stmt.branch p q₁ q₂) := writes q₁ ∪ writes q₂
| (stmt.goto l)         := ∅
| stmt.halt             := ∅

noncomputable def tr_supp (S : finset Λ) : finset Λ' :=
S.bind (λ l, insert (Λ'.normal l) (writes (M l)))

theorem supports_stmt_move {S d q} :
  supports_stmt S (move d q) = supports_stmt S q :=
suffices ∀ {i}, supports_stmt S (stmt.move d^[i] q) = _, from this,
by intro; induction i generalizing q; simp only [*, nat.iterate]; refl

theorem supports_stmt_write {S l q} :
  supports_stmt S (write l q) = supports_stmt S q :=
by induction l with a l IH; simp only [write, supports_stmt, *]

local attribute [simp] supports_stmt_move supports_stmt_write

theorem supports_stmt_read {S} : ∀ {f : Γ → stmt'},
  (∀ a, supports_stmt S (f a)) → supports_stmt S (read f) :=
suffices ∀ i (f : vector bool i → stmt'),
  (∀ v, supports_stmt S (f v)) → supports_stmt S (read_aux i f),
from λ f hf, this n _ (by intro; simp only [supports_stmt_move, hf]),
λ i f hf, begin
  induction i with i IH, {exact hf _},
  split; apply IH; intro; apply hf,
end

theorem tr_supports {S} (ss : supports M S) :
  supports tr (tr_supp S) :=
⟨finset.mem_bind.2 ⟨_, ss.1, finset.mem_insert_self _ _⟩,
λ q h, begin
  suffices : ∀ q, supports_stmt S q →
    (∀ q' ∈ writes q, q' ∈ tr_supp M S) →
    supports_stmt (tr_supp M S) (tr_normal dec q) ∧
    ∀ q' ∈ writes q, supports_stmt (tr_supp M S) (tr enc dec M q'),
  { rcases finset.mem_bind.1 h with ⟨l, hl, h⟩,
    have := this _ (ss.2 _ hl) (λ q' hq,
      finset.mem_bind.2 ⟨_, hl, finset.mem_insert_of_mem hq⟩),
    rcases finset.mem_insert.1 h with rfl | h,
    exacts [this.1, this.2 _ h] },
  intros q hs hw, induction q,
  case TM1.stmt.move : d q IH {
    unfold writes at hw ⊢,
    replace IH := IH hs hw, refine ⟨_, IH.2⟩,
    cases d; simp only [tr_normal, nat.iterate, supports_stmt_move, IH] },
  case TM1.stmt.write : f q IH {
    unfold writes at hw ⊢,
    simp only [finset.mem_image, finset.mem_union, finset.mem_univ,
      exists_prop, true_and] at hw ⊢,
    replace IH := IH hs (λ q hq, hw q (or.inr hq)),
    refine ⟨supports_stmt_read _ $ λ a _ s,
      hw _ (or.inl ⟨_, rfl⟩), λ q' hq, _⟩,
    rcases hq with ⟨a, q₂, rfl⟩ | hq,
    { simp only [tr, supports_stmt_write, supports_stmt_move, IH.1] },
    { exact IH.2 _ hq } },
  case TM1.stmt.load : a q IH {
    unfold writes at hw ⊢,
    replace IH := IH hs hw,
    refine ⟨supports_stmt_read _ (λ a, IH.1), IH.2⟩ },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    unfold writes at hw ⊢,
    simp only [finset.mem_union] at hw ⊢,
    replace IH₁ := IH₁ hs.1 (λ q hq, hw q (or.inl hq)),
    replace IH₂ := IH₂ hs.2 (λ q hq, hw q (or.inr hq)),
    exact ⟨supports_stmt_read _ (λ a, ⟨IH₁.1, IH₂.1⟩),
      λ q, or.rec (IH₁.2 _) (IH₂.2 _)⟩ },
  case TM1.stmt.goto : l {
    refine ⟨_, λ _, false.elim⟩,
    refine supports_stmt_read _ (λ a _ s, _),
    exact finset.mem_bind.2 ⟨_, hs _ _, finset.mem_insert_self _ _⟩ },
  case TM1.stmt.halt {
    refine ⟨_, λ _, false.elim⟩,
    simp only [supports_stmt, supports_stmt_move, tr_normal] }
end⟩

end

end TM1to1

namespace TM0to1

section
parameters {Γ : Type*} [inhabited Γ]
parameters {Λ : Type*} [inhabited Λ]

inductive Λ'
| normal : Λ → Λ'
| act : TM0.stmt Γ → Λ → Λ'
instance : inhabited Λ' := ⟨Λ'.normal (default _)⟩

local notation `cfg₀` := TM0.cfg Γ Λ
local notation `stmt₁` := TM1.stmt Γ Λ' unit
local notation `cfg₁` := TM1.cfg Γ Λ' unit

parameters (M : TM0.machine Γ Λ)

open TM1.stmt

def tr : Λ' → stmt₁
| (Λ'.normal q) :=
  branch (λ a _, (M q a).is_none) halt $
  goto (λ a _, match M q a with
  | none := default _
  | some (q', s) := Λ'.act s q'
  end)
| (Λ'.act (TM0.stmt.move d) q) :=
  move d $ goto (λ _ _, Λ'.normal q)
| (Λ'.act (TM0.stmt.write a) q) :=
  write (λ _ _, a) $ goto (λ _ _, Λ'.normal q)

def tr_cfg : cfg₀ → cfg₁
| ⟨q, T⟩ := ⟨cond (M q T.1).is_some
  (some (Λ'.normal q)) none, (), T⟩

theorem tr_respects : respects (TM0.step M) (TM1.step tr)
  (λ a b, tr_cfg a = b) :=
fun_respects.2 $ λ ⟨q, T⟩, begin
  cases e : M q T.1,
  { simp only [TM0.step, tr_cfg, e]; exact eq.refl none },
  cases val with q' s,
  simp only [frespects, TM0.step, tr_cfg, e, option.is_some, cond, option.map_some'],
  have : TM1.step (tr M) ⟨some (Λ'.act s q'), (), T⟩ =
    some ⟨some (Λ'.normal q'), (), TM0.step._match_1 T s⟩,
  { cases s with d a; refl },
  refine trans_gen.head _ (trans_gen.head' this _),
  { unfold TM1.step TM1.step_aux tr has_mem.mem,
    rw e, refl },
  cases e' : M q' _,
  { apply refl_trans_gen.single,
    unfold TM1.step TM1.step_aux tr has_mem.mem,
    rw e', refl },
  { refl }
end

end

end TM0to1

namespace TM2

section
parameters {K : Type*} [decidable_eq K] -- Index type of stacks
parameters (Γ : K → Type*) -- Type of stack elements
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
(l : option Λ)
(var : σ)
(stk : ∀ k, list (Γ k))

parameters {Γ Λ σ K}
def step_aux : stmt → σ → (∀ k, list (Γ k)) → cfg
| (push k f q)     v S := step_aux q v (dwrite S k (f v :: S k))
| (peek k f q)     v S := step_aux q (f v (S k).head') S
| (pop k f q)      v S := step_aux q (f v (S k).head') (dwrite S k (S k).tail)
| (load a q)       v S := step_aux q (a v) S
| (branch f q₁ q₂) v S :=
  cond (f v) (step_aux q₁ v S) (step_aux q₂ v S)
| (goto f)         v S := ⟨some (f v), v, S⟩
| halt             v S := ⟨none, v, S⟩

def step (M : Λ → stmt) : cfg → option cfg
| ⟨none,   v, S⟩ := none
| ⟨some l, v, S⟩ := some (step_aux (M l) v S)

def reaches (M : Λ → stmt) : cfg → cfg → Prop :=
refl_trans_gen (λ a b, b ∈ step M a)

variables [inhabited Λ] [inhabited σ]
def init (k) (L : list (Γ k)) : cfg :=
⟨some (default _), default _, dwrite (λ _, []) k L⟩

def eval (M : Λ → stmt) (k) (L : list (Γ k)) : roption (list (Γ k)) :=
(eval (step M) (init k L)).map $ λ c, c.stk k

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
by cases q; apply finset.mem_insert_self

theorem stmts₁_trans {q₁ q₂} :
  q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ :=
begin
  intros h₁₂ q₀ h₀₁,
  induction q₂ with _ _ q IH _ _ q IH _ _ q IH _ q IH;
    simp only [stmts₁] at h₁₂ ⊢;
    simp only [finset.mem_insert, finset.insert_empty_eq_singleton,
      finset.mem_singleton, finset.mem_union] at h₁₂,
  iterate 4 {
    rcases h₁₂ with rfl | h₁₂,
    { unfold stmts₁ at h₀₁, exact h₀₁ },
    { exact finset.mem_insert_of_mem (IH h₁₂) } },
  case TM2.stmt.branch : f q₁ q₂ IH₁ IH₂ {
    rcases h₁₂ with rfl | h₁₂ | h₁₂,
    { unfold stmts₁ at h₀₁, exact h₀₁ },
    { exact finset.mem_insert_of_mem (finset.mem_union_left _ (IH₁ h₁₂)) },
    { exact finset.mem_insert_of_mem (finset.mem_union_right _ (IH₂ h₁₂)) } },
  case TM2.stmt.goto : l {
    subst h₁₂, exact h₀₁ },
  case TM2.stmt.halt {
    subst h₁₂, exact h₀₁ }
end

theorem stmts₁_supports_stmt_mono {S q₁ q₂}
  (h : q₁ ∈ stmts₁ q₂) (hs : supports_stmt S q₂) : supports_stmt S q₁ :=
begin
  induction q₂ with _ _ q IH _ _ q IH _ _ q IH _ q IH;
    simp only [stmts₁, supports_stmt, finset.mem_insert, finset.mem_union,
      finset.insert_empty_eq_singleton, finset.mem_singleton] at h hs,
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
by simp only [stmts, finset.mem_insert_none, finset.mem_bind,
  option.mem_def, forall_eq', exists_imp_distrib];
exact λ l ls h₂, ⟨_, ls, stmts₁_trans h₂ h₁⟩

theorem stmts_supports_stmt {M : Λ → stmt} {S q}
  (ss : supports M S) : some q ∈ stmts M S → supports_stmt S q :=
by simp only [stmts, finset.mem_insert_none, finset.mem_bind,
  option.mem_def, forall_eq', exists_imp_distrib];
exact λ l ls h, stmts₁_supports_stmt_mono h (ss.2 _ ls)

theorem step_supports (M : Λ → stmt) {S}
  (ss : supports M S) : ∀ {c c' : cfg},
  c' ∈ step M c → c.l ∈ S.insert_none → c'.l ∈ S.insert_none
| ⟨some l₁, v, T⟩ c' h₁ h₂ := begin
  replace h₂ := ss.2 _ (finset.some_mem_insert_none.1 h₂),
  simp only [step, option.mem_def] at h₁, subst c',
  revert h₂, induction M l₁ with _ _ q IH _ _ q IH _ _ q IH _ q IH generalizing v T;
    intro hs,
  iterate 4 { exact IH _ _ hs },
  case TM2.stmt.branch : p q₁' q₂' IH₁ IH₂ {
    unfold step_aux, cases p v,
    { exact IH₂ _ _ hs.2 },
    { exact IH₁ _ _ hs.1 } },
  case TM2.stmt.goto { exact finset.some_mem_insert_none.2 (hs _) },
  case TM2.stmt.halt { apply multiset.mem_cons_self }
end

end

end TM2

namespace TM2to1

section
parameters {K : Type*} [decidable_eq K]
parameters {Γ : K → Type*}
parameters {Λ : Type*} [inhabited Λ]
parameters {σ : Type*} [inhabited σ]

local notation `stmt₂` := TM2.stmt Γ Λ σ
local notation `cfg₂` := TM2.cfg Γ Λ σ

inductive stackel (k : K)
| val : Γ k → stackel
| bottom : stackel
| top : stackel

instance stackel.inhabited (k) : inhabited (stackel k) :=
⟨stackel.top _⟩

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
| normal {} : Λ → Λ'
| go (k) : st_act k → stmt₂ → Λ'
| ret {} : K → stmt₂ → Λ'
open Λ'
instance : inhabited Λ' := ⟨normal (default _)⟩

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

theorem step_run {k : K} (q v S) : ∀ s : st_act k,
  TM2.step_aux (st_run s q) v S =
  TM2.step_aux q (st_var v (S k) s) (dwrite S k (st_write v (S k) s))
| (st_act.push f) := rfl
| (st_act.pop ff f) := by unfold st_write; rw dwrite_self; refl
| (st_act.pop tt f) := rfl

def tr_normal : stmt₂ → stmt₁
| (TM2.stmt.push k f q)     := goto (λ _ _, go k (st_act.push f) q)
| (TM2.stmt.peek k f q)     := goto (λ _ _, go k (st_act.pop ff f) q)
| (TM2.stmt.pop k f q)      := goto (λ _ _, go k (st_act.pop tt f) q)
| (TM2.stmt.load a q)       := load (λ _, a) (tr_normal q)
| (TM2.stmt.branch f q₁ q₂) := branch (λ a, f) (tr_normal q₁) (tr_normal q₂)
| (TM2.stmt.goto l)         := goto (λ a s, normal (l s))
| TM2.stmt.halt             := halt

theorem tr_normal_run {k} (s q) :
  tr_normal (st_run s q) = goto (λ _ _, go k s q) :=
by rcases s with _|_|_; refl

parameters (M : Λ → stmt₂)
include M

def tr : Λ' → stmt₁
| (normal q) := tr_normal (M q)
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
  tr_cfg ⟨q, v, S⟩ ⟨q.map normal, v, (stackel.bottom, [], L)⟩

theorem tr_respects_aux₁ {k} (o q v) : ∀ S₁ {s S₂} {T : list Γ'},
  T.map (λ (a : Γ'), a k) = (list.map stackel.val S₁).reverse_core (s :: S₂) →
  ∃ a T₁ T₂,
    T = list.reverse_core T₁ (a :: T₂) ∧
    a k = s ∧
    T₁.map (λ (a : Γ'), a k) = S₁.map stackel.val ∧
    T₂.map (λ (a : Γ'), a k) = S₂ ∧
    reaches₀ (TM1.step tr)
      ⟨some (go k o q), v, (stackel.bottom, [], T)⟩
      ⟨some (go k o q), v, (a, T₁ ++ [stackel.bottom], T₂)⟩
| [] s S₂ (a :: T) hT := by injection hT with es e₂; exact
  ⟨a, [], _, rfl, es, rfl, e₂, reaches₀.single rfl⟩
| (s' :: S₁) s S₂ T hT :=
  let ⟨a, T₁, b'::T₂, e, es', e₁, e₂, H⟩ := tr_respects_aux₁ S₁ hT in
  by injection e₂ with es e₂; exact
  ⟨b', a::T₁, T₂, e, es, congr (congr_arg list.cons es') e₁,
    e₂, H.tail (by unfold TM1.step;
      change some (cond (TM2to1.stackel.is_top (a k)) _ _) = _;
      rw es'; refl)⟩

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
    TM1.step_aux (tr_st_act q o) v (a, T₁ ++ [stackel.bottom], T₂) =
    TM1.step_aux q v' (b, T₁' ++ [stackel.bottom], T₂') :=
begin
  dsimp only,
  cases o with f b f,
  case TM2to1.st_act.push : {
    refine ⟨_, dwrite a k (stackel.val (f v)) :: T₁,
      _, _, by simp only [list.map, dwrite_eq, e₁]; refl,
      by simp only [tape.write, tape.move, dwrite_eq], rfl⟩,
    intro k', cases hT k' with n e,
    by_cases h : k' = k,
    { subst k', existsi n.pred,
      simp only [list.reverse_core_eq, list.map_append, list.map_reverse, e₁,
        list.map_cons, list.append_left_inj] at e,
      simp only [list.reverse_core_eq, e.1, e.2, list.map_append, prod.fst,
        list.map_reverse, list.reverse_cons, list.map, dwrite_eq, e₁, list.map_tail,
        list.tail_repeat, TM2to1.st_write] },
    { cases T₂ with t T₂,
      { existsi n+1,
        simpa only [dwrite_ne _ _ _ _ h, list.reverse_core_eq, e₁, list.repeat_add,
          tape.write, tape.move, list.reverse_cons, list.map_reverse, list.map_append,
          list.map, list.head, list.tail, list.append_assoc] using
          congr_arg (++ [default Γ' k']) e },
      { existsi n,
        simpa only [dwrite_ne _ _ _ _ h, list.reverse_core_eq, e₁, list.repeat_add,
          tape.write, tape.move, list.reverse_cons, list.map_reverse, list.map_append,
          list.map, list.head, list.tail, list.append_assoc] using e } } },
  have dw := dwrite_self S k,
  cases T₁ with t T₁; cases eS : S k with s Sk;
    rw eS at e₁ dw; injection e₁ with tk e₁'; cases b,
  { -- peek nil
    simp only [dw, st_write],
    exact ⟨_, [], _, hT, rfl, ea, rfl⟩ },
  { -- pop nil
    simp only [dw, st_write, list.tail],
    exact ⟨_, [], _, hT, rfl, ea, rfl⟩ },
  { -- peek cons
    change t k = stackel.val s at tk,
    simp only [eS, tk, dw, st_write, TM1.step_aux, tr_st_act, cond, tape.move,
      list.head, list.tail, list.cons_append],
    exact ⟨_, t::T₁, _, hT, e₁, ea, rfl⟩ },
  { -- pop cons
    change t k = stackel.val s at tk,
    simp only [tk, st_write, list.tail, TM1.step_aux, tr_st_act, cond,
      tape.move, list.cons_append, list.head],
    refine ⟨_, _, _, _, e₁', dwrite_eq _ _ _, rfl⟩,
    intro k', cases hT k' with n e,
    by_cases h : k' = k,
    { subst k', existsi n+1,
      simp only [list.reverse_core_eq, eS, e₁', list.append_left_inj,
        list.map_append, list.map_reverse, list.map, list.reverse_cons,
        list.append_assoc, list.cons_append] at e ⊢,
      simp only [tape.move, tape.write, list.head, list.tail, dwrite_eq],
      rw [e.2.2]; refl },
    { existsi n, simpa only [dwrite_ne _ _ _ _ h, list.map, list.head, list.tail,
        list.reverse_core, list.map_reverse_core, tape.move, tape.write] using e } },
end

theorem tr_respects_aux₃ {k q v}
  {S : Π k, list (Γ k)} {T : list Γ'}
  (hT : ∀ k, tr_stk (S k) (T.map (λ (a : Γ'), a k))) :
  ∀ (T₁ : list Γ') {T₂ : list Γ'} {a : Γ'} {S₁}
    (e : T = T₁.reverse_core (a :: T₂))
    (ha : (a k).is_bottom = ff)
    (e₁ : T₁.map (λ (a : Γ'), a k) = list.map stackel.val S₁),
    reaches₀ (TM1.step tr)
      ⟨some (ret k q), v, (a, T₁ ++ [stackel.bottom], T₂)⟩
      ⟨some (ret k q), v, (stackel.bottom, [], T)⟩
| [] T₂ a S₁ e ha e₁ := reaches₀.single (by simp only [ha, e, TM1.step,
    option.mem_def, tr, TM1.step_aux] {constructor_eq:=ff}; refl)
| (b :: T₁) T₂ a (s :: S₁) e ha e₁ := begin
    unfold list.map at e₁, injection e₁ with es e₁,
    refine reaches₀.head _ (tr_respects_aux₃ T₁ e (by rw es; refl) e₁),
    simp only [ha, option.mem_def, TM1.step, tr, TM1.step_aux], refl
  end

theorem tr_respects_aux {q v T k} {S : Π k, list (Γ k)}
  (hT : ∀ (k : K), tr_stk (S k) (list.map (λ (a : Γ'), a k) T))
  (o : st_act k)
  (IH : ∀ {v : σ} {S : Π (k : K), list (Γ k)} {T : list Γ'},
    (∀ (k : K), tr_stk (S k) (list.map (λ (a : Γ'), a k) T)) →
    (∃ b, tr_cfg (TM2.step_aux q v S) b ∧
      reaches (TM1.step tr) (TM1.step_aux (tr_normal q) v (stackel.bottom, [], T)) b)) :
  ∃ b, tr_cfg (TM2.step_aux (st_run o q) v S) b ∧
    reaches (TM1.step tr) (TM1.step_aux (tr_normal (st_run o q))
      v (stackel.bottom, [], T)) b :=
begin
  rcases hT k with ⟨n, hTk⟩,
  simp only [tr_normal_run],
  rcases tr_respects_aux₁ M o q v _ hTk with ⟨a, T₁, T₂, rfl, ea, e₁, e₂, hgo⟩,
  rcases tr_respects_aux₂ M hT e₁ ea _ with ⟨b, T₁', T₂', hT', e₁', eb, hrun⟩,
  have hret := tr_respects_aux₃ M hT' _ rfl (by rw eb; refl) e₁',
  have := hgo.tail' rfl,
  simp only [ea, tr, TM1.step_aux] at this,
  rw [hrun, TM1.step_aux] at this,
  rcases IH hT' with ⟨c, gc, rc⟩,
  simp only [step_run],
  refine ⟨c, gc, (this.to₀.trans hret _ (trans_gen.head' rfl rc)).to_refl⟩
end

local attribute [simp] respects TM2.step TM2.step_aux tr_normal

theorem tr_respects : respects (TM2.step M) (TM1.step tr) tr_cfg :=
λ c₁ c₂ h, begin
  cases h with l v S L hT, clear h,
  cases l, {constructor},
  simp only [TM2.step, respects, option.map_some'],
  suffices : ∃ b, _ ∧ reaches (TM1.step (tr M)) _ _,
  from let ⟨b, c, r⟩ := this in ⟨b, c, trans_gen.head' rfl r⟩,
  rw [tr],
  revert v S L hT, refine stmt_st_rec _ _ _ _ _ (M l); intros,
  { exact tr_respects_aux M hT s @IH },
  { exact IH hT },
  { unfold TM2.step_aux tr_normal TM1.step_aux,
    cases p v; [exact IH₂ hT, exact IH₁ hT] },
  { exact ⟨_, ⟨hT⟩, refl_trans_gen.refl⟩ },
  { exact ⟨_, ⟨hT⟩, refl_trans_gen.refl⟩ }
end

theorem tr_cfg_init (k) (L : list (Γ k)) :
  tr_cfg (TM2.init k L) (TM1.init (tr_init k L)) :=
⟨λ k', begin
  unfold tr_init,
  cases e : L.reverse with a L',
  { cases list.reverse_eq_nil.1 e, rw dwrite_self, exact ⟨0, rfl⟩ },
  by_cases k' = k,
  { subst k', existsi 0,
    simp only [list.tail, dwrite_eq, list.reverse_core_eq,
      list.repeat, tr_init, list.map, list.map_map, (∘), list.map_id' (λ _, rfl)],
    rw [← list.map_reverse, e], refl },
  { existsi L'.length + 1,
    simp only [dwrite_ne _ _ _ _ h, list.tail, tr_init, list.map_map,
      list.map, list.map_append, list.repeat_add, (∘),
      list.map_const] {constructor_eq:=ff},
    refl }
end⟩

theorem tr_eval_dom (k) (L : list (Γ k)) :
  (TM1.eval tr (tr_init k L)).dom ↔ (TM2.eval M k L).dom :=
tr_eval_dom tr_respects (tr_cfg_init _ _)

theorem tr_eval (k) (L : list (Γ k)) {L₁ L₂}
  (H₁ : L₁ ∈ TM1.eval tr (tr_init k L))
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
by rcases s with _|_|_; unfold tr_stmts₁ st_run

noncomputable def tr_supp (S : finset Λ) : finset Λ' :=
S.bind (λ l, insert (normal l) (tr_stmts₁ (M l)))

local attribute [simp] tr_stmts₁ tr_stmts₁_run supports_run
  tr_normal_run TM1.supports_stmt TM2.supports_stmt

theorem tr_supports {S} (ss : TM2.supports M S) :
  TM1.supports tr (tr_supp S) :=
⟨finset.mem_bind.2 ⟨_, ss.1, finset.mem_insert.2 $ or.inl rfl⟩,
λ l' h, begin
  suffices : ∀ q (ss' : TM2.supports_stmt S q)
    (sub : ∀ x ∈ tr_stmts₁ M q, x ∈ tr_supp M S),
    TM1.supports_stmt (tr_supp M S) (tr_normal q) ∧
    (∀ l' ∈ tr_stmts₁ M q, TM1.supports_stmt (tr_supp M S) (tr M l')),
  { rcases finset.mem_bind.1 h with ⟨l, lS, h⟩,
    have := this _ (ss.2 l lS) (λ x hx,
      finset.mem_bind.2 ⟨_, lS, finset.mem_insert_of_mem hx⟩),
    rcases finset.mem_insert.1 h with rfl | h;
    [exact this.1, exact this.2 _ h] },
  clear h l', refine stmt_st_rec _ _ _ _ _; intros,
  { -- stack op
    rw TM2to1.supports_run at ss',
    simp only [TM2to1.tr_stmts₁_run, finset.mem_union,
      finset.has_insert_eq_insert, finset.insert_empty_eq_singleton,
      finset.mem_insert, finset.mem_singleton] at sub,
    have hgo := sub _ (or.inl $ or.inr rfl),
    have hret := sub _ (or.inl $ or.inl rfl),
    cases IH ss' (λ x hx, sub x $ or.inr hx) with IH₁ IH₂,
    refine ⟨by simp only [tr_normal_run, TM1.supports_stmt]; intros; exact hgo, λ l h, _⟩,
    rw [tr_stmts₁_run] at h,
    simp only [TM2to1.tr_stmts₁_run, finset.mem_union,
      finset.has_insert_eq_insert, finset.insert_empty_eq_singleton,
      finset.mem_insert, finset.mem_singleton] at h,
    rcases h with ⟨rfl | rfl⟩ | h,
    { unfold TM1.supports_stmt TM2to1.tr,
      exact ⟨IH₁, λ _ _, hret⟩ },
    { unfold TM1.supports_stmt TM2to1.tr,
      rcases s with _|_|_,
      { exact ⟨λ _ _, hret, λ _ _, hgo⟩ },
      { exact ⟨λ _ _, hret, λ _ _, hgo⟩ },
      { exact ⟨⟨λ _ _, hret, λ _ _, hret⟩, λ _ _, hgo⟩ } },
    { exact IH₂ _ h } },
  { -- load
    unfold TM2to1.tr_stmts₁ at ss' sub ⊢,
    exact IH ss' sub },
  { -- branch
    unfold TM2to1.tr_stmts₁ at sub,
    cases IH₁ ss'.1 (λ x hx, sub x $ finset.mem_union_left _ hx) with IH₁₁ IH₁₂,
    cases IH₂ ss'.2 (λ x hx, sub x $ finset.mem_union_right _ hx) with IH₂₁ IH₂₂,
    refine ⟨⟨IH₁₁, IH₂₁⟩, λ l h, _⟩,
    rw [tr_stmts₁] at h,
    rcases finset.mem_union.1 h with h | h;
    [exact IH₁₂ _ h, exact IH₂₂ _ h] },
  { -- goto
    rw tr_stmts₁, unfold TM2to1.tr_normal TM1.supports_stmt,
    unfold TM2.supports_stmt at ss',
    exact ⟨λ _ v, finset.mem_bind.2 ⟨_, ss' v, finset.mem_insert_self _ _⟩, λ _, false.elim⟩ },
  { exact ⟨trivial, λ _, false.elim⟩ } -- halt
end⟩

end

end TM2to1

end turing
