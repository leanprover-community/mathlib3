/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Basic machinery for defining general coinductive types

Work in progress
-/
import data.pfun
import logic.basic

universes u₀ u₁ u₂ v w

open nat function roption list

variables {ι : Type u₁}
variables {α : ι → Type u₀}
variables {β : Π i, α i → Type u₂}
variables (γ : Π i (a : α i), β i a → ι)
-- variables (η : α → ι)

local prefix `♯`:0 := cast (by casesm* _ ∧ _ ; simp [*] <|> cc <|> solve_by_elim)

local attribute [instance, priority 0] classical.prop_decidable

section
open interactive interactive.types lean tactic
meta def h_subst (h : parse texpr) : tactic unit :=
do (ta,a,tb,b) ← to_expr h >>= infer_type >>= match_heq,
   trace ta,
   trace a,
   trace tb,
   trace b
run_cmd add_interactive [`h_subst]
end

namespace coinduction.approx

/-
coinductive ind {α : Type u} (β : α → Type v) : Type (max u v)
| intro : ∀ a, (β a → ind) → ind
-/

inductive cofix_a : ι → ℕ → Type (max u₀ u₁ u₂)
| continue {} (i : ι) : cofix_a i 0
| intro {n} : ∀ {i} (a : α i), (Π b : β i a, cofix_a (γ _ _ b) n) → cofix_a i (succ n)

variables {β γ}

def head' : Π {i n}, cofix_a γ i (succ n) → α i
 | i n (cofix_a.intro a _) := a

def children' : Π {i n} (x : cofix_a γ i (succ n)), (Π b : β i (head' x), cofix_a γ (γ _ _ b) n)
 | i n (cofix_a.intro _ f) := f

inductive agree
: ∀ {i j : ι} {n : ℕ}, cofix_a γ i n → cofix_a γ j (n+1) → Prop
 | trivial (i : ι) (x₀ : cofix_a γ i 0)  (x₁ : cofix_a γ i 1) : agree x₀ x₁
 | step {i n} (x : α i)
   (ch₀ : Π b : β i x, cofix_a γ (γ _ x b) n)
   (ch₁ : Π b : β i x, cofix_a γ (γ _ x b) (succ n)) :
   (∀ j, agree (ch₀ j) (ch₁ j)) →
   agree (cofix_a.intro _ ch₀) (cofix_a.intro _ ch₁)

def all_agree {i} (x : Π n, cofix_a γ i n) :=
∀ n, agree (x n) (x (succ n))

@[simp]
lemma agree_trivoal {i} {x : cofix_a γ i 0} {y : cofix_a γ i 1}
: agree x y :=
by { cases x, constructor }

lemma agree_def {a b : ι} {n : ℕ} (x : cofix_a γ a (succ n)) (y : cofix_a γ b (succ n+1))
  (h₀ : a = b)
  (h₁ : head' x == head' y)
  (h₂ : ∀ (i : β _ _) (j : β _ _), i == j →
        agree (children' x i) (children' y j))
: agree x y :=
begin
  cases x, cases y, subst b,
  dsimp [head',children'] at h₁ h₂, subst h₁,
  constructor,
  intros, apply h₂, refl,
end

section
open tactic
meta def subst_all : tactic unit :=
repeat $
do gs ← get_goals,
   ls ← local_context,
   ls.mmap' (try ∘ subst),
   gs' ← get_goals,
   guard (gs ≠ gs')

run_cmd add_interactive [`subst_all]

end

lemma agree_children {a a' b b' : ι} {n : ℕ}
  (x : cofix_a γ a (succ n))
  (y : cofix_a γ b (succ n+1))
  -- (ch_x : )
  {i : β a (head' x)}
  {j : β b (head' y)}
  -- (ch_x : cofix_a γ (γ a (head' x) i) n)
  -- (ch_y : cofix_a γ (γ b (head' y) j) (succ n))
  (ch_x : cofix_a γ a' n)
  (ch_y : cofix_a γ b' (succ n))
  (h₀ : i == j)
  (h₁ : agree x y)
  (h₂ : children' x i == ch_x)
  (h₃ : children' y j == ch_y)
  (h₄ : γ a (head' x) i = a')
  (h₅ : γ b (head' y) j = b')
: agree ch_x ch_y :=
begin
  cases h₁,
  dunfold children' head' at *,
  subst_all, apply h₁_a,
end

def truncate
: ∀ {i : ι} {n : ℕ}, cofix_a γ i (n+1) → cofix_a γ i n
 | _ 0 (cofix_a.intro _ _) := cofix_a.continue _
 | _ (succ n) (cofix_a.intro i f) := cofix_a.intro i $ λ j, truncate $ f _

lemma truncate_eq_of_agree {i j : ι} {n : ℕ}
  {x : cofix_a γ i n}
  {y : cofix_a γ j (succ n)}
  (h : agree x y)
: truncate y == x :=
begin
  induction h,
  case agree.trivial : i x
  { cases x, cases truncate h_x₁, refl },
  case agree.step : j n a
  { simp [truncate], ext,
    apply eq_of_heq, apply h_ih }
end

lemma truncate_eq_of_agree' {i : ι} {n : ℕ}
  (x : cofix_a γ i n)
  (y : cofix_a γ i (succ n))
  (h : agree x y)
: truncate y = x :=
eq_of_heq $ truncate_eq_of_agree h

variables {X : ι → Type w}
variables (f : Π i, X i → Σ (y : α i), Π b : β i y, X (γ _ _ b))

def s_corec : Π {i : ι} (x₀ : X i) n, cofix_a γ i n
 | _ _ 0 := cofix_a.continue _
 | i j (succ n) :=
   let ⟨y,g⟩ := f i j in
   cofix_a.intro y (λ b, s_corec (g _) _)
   -- cofix_a.intro y (λ i, s_corec _ _)
   -- cofix_a.intro y (λ i, s_corec (g i) _)

lemma P_corec {i : ι} (s : X i) (n : ℕ) : agree (s_corec f s n) (s_corec f s (succ n)) :=
begin
  revert i,
  induction n with n ; introv,
  constructor,
  cases h : f i s with y g,
  simp [s_corec,h] at ⊢ n_ih,
  constructor,
  introv, apply n_ih,
end

def path (β : Π i, α i → Type v) := list (Σ i (a : α i), β i a)

@[reducible]
def link {β : Π i, α i → Type v} {i : ι} {y : α i} (j : β i y) : (Σ i (a : α i), β i a) :=
⟨i,_,j⟩

def select' : ∀ {i : ι} {n : ℕ}, cofix_a γ i n → path @β → roption (Σ i, α i)
 | _ ._ (cofix_a.continue _) _ := roption.none
 | _ (succ _) (cofix_a.intro y' ch) [] := return ⟨ _, y' ⟩
 | i (succ _) (cofix_a.intro y ch) (⟨i', y', j⟩ :: ys) :=
assert (i = i' ∧ y == y') $ λ h,
select' (ch $ ♯ j) ys

def subtree' : ∀ {i : ι} {n : ℕ} (ps : path @β) (x : cofix_a γ i (n + ps.length)), roption (Σ i, cofix_a γ i n)
 | i n [] t := return ⟨_,t⟩
 | i' n (⟨i, y, j⟩ :: ys) (cofix_a.intro y' ch) :=
assert (i' = i ∧ y == y') $ λ h,
subtree' ys (ch $ ♯ j)

#check γ

open list

lemma select_of_lt_length' {i : ι} {n : ℕ}
  {ps : path @β}
  {x : cofix_a γ i n}
  (Hg : n < ps.length)
: @select' _ α @β _ _ _ x ps = roption.none :=
begin
  revert i x n,
  induction ps ; introv Hg,
  { cases not_lt_zero _ Hg },
  { rcases ps_hd with ⟨ i', y', j ⟩,
    cases x with _ n _ y ch,
    { dsimp [select'], refl },
    by_cases h : i = i' ∧ y == y',
    { simp [select',assert_if_pos,*],
      apply ps_ih, apply lt_of_succ_lt_succ Hg, },
    { simp [select',assert_if_neg,*], } },
end

@[simp]
lemma select_cons' {i : ι} {n : ℕ}
  {ps : path β}
  {y : α i} {j : β i y} {ch : β i y → cofix_a γ _ (n + length ps)}
: select' (cofix_a.intro y ch) (⟨i,y,j⟩ :: ps) = select' (ch j) ps :=
by { simp [select',assert_if_pos,cast_eq], refl, }

@[simp, priority 0]
lemma subtree_cons {i : ι} {n : ℕ}
  {ps : path β}
  {y : α i} {j : β i y} {ch : β i y → cofix_a γ _ (n + length ps)}
: subtree' (⟨i,y,j⟩ :: ps) (cofix_a.intro y ch) = subtree' ps (ch j) :=
by simp [subtree',assert_if_pos,cast_eq] ; refl

lemma subtree_cons_of_ne {i i' : ι} {n : ℕ}
  {ps : path β}
  {y : α i} {y' : α i'} {j : β i y} {ch : β i' y' → cofix_a γ _ (n + length ps)}
  (Hne :  ¬(i = i' ∧ y == y'))
: subtree' (⟨i,y,j⟩ :: ps) (cofix_a.intro y' ch) = none :=
by simp [subtree',assert_if_neg,*]

@[simp]
lemma mem_subtree_cons_iff {i i' : ι} {n : ℕ}
  {x : cofix_a γ i' n}
  {ps : path β}
  {y : α i} {y' : α i'} {j : β i y} {ch : β i' y' → cofix_a γ _ (n + length ps)}
: sigma.mk i' x ∈ subtree' (link j :: ps : path β) (cofix_a.intro _ ch) ↔
  ∃ h : i = i' ∧ y' == y, sigma.mk i' x ∈ subtree' ps (ch $ ♯ j) :=
begin
  split ; intro H,
  { have : i = i' ∧ y == y',
    { by_contradiction,
      simp [subtree_cons_of_ne a,has_mem.mem,roption.mem] at H,
      rcases H with ⟨ H₀, H₁ ⟩, cases H₀, },
    cases this, subst i, cases this_right,
    existsi (and.intro rfl heq.rfl), simp at H,
    exact H, },
  { rcases H with ⟨⟨_,Hy⟩,H⟩, subst H_w_left, subst Hy,
    simp, exact H, },
end

instance {i} : subsingleton (cofix_a γ i 0) :=
⟨ by { intros, casesm* cofix_a γ i 0, refl } ⟩

def all_or_nothing {i} (f : Π x : α i, roption (β i x))
: roption { g : Π x, β i x // ∀ x, g x ∈ f x } :=
⟨ ∀ x, (f x).dom, assume h, ⟨ λ x, (f _).get (h _), assume x, ⟨ h x, rfl ⟩ ⟩ ⟩

open list nat
lemma head_succ' {i : ι} (n m : ℕ) (x : Π n, cofix_a γ i n)
  (Hconsistent : all_agree x)
: head' (x (succ n)) = head' (x (succ m)) :=
begin
  suffices : ∀ n, head' (x (succ n)) = head' (x 1),
  { simp [this] },
  clear m n, intro,
  cases h₀ : x (succ n) with _ _ _ i₀ f₀,
  cases h₁ : x 1 with _ _ _ i₁ f₁,
  simp [head'],
  induction n with n,
  { rw h₁ at h₀, cases h₀, trivial },
  { have H := Hconsistent (succ n),
    cases h₂ : x (succ n) with _ i₂ f₂,
    rw [h₀,h₂] at H,
    apply n_ih (λ k, truncate $ f₀ k),
    rw h₂,
    cases H with h H,
    congr, funext j,
    rw truncate_eq_of_agree',
    apply H_a, }
end

lemma subtree'_congr {ι : Type*} {α : ι → Type*} {β : Π (i : ι), α i → Type*}
  {γ : Π (i : ι) (a : α i), β i a → ι}
  {i j : ι} {n : ℕ} (ps : path β)
  (x : cofix_a γ i (n + length ps))
  (y : cofix_a γ j (n + length ps))
  (h  : i = j)
  (h' : x == y) :
subtree' ps x = subtree' ps y :=
begin
  have := type_eq_of_heq h',
end

-- set_option pp.implicit true
#check @subtree'


lemma agree_of_mem_subtree' {i i' : ι} (ps : path β)
  {f : Π n : ℕ, cofix_a γ i n}
  {g : Π n : ℕ, cofix_a γ i' n}
  (Hi : i = i')
  (Hg : all_agree g)
  (Hsub : ∀ (x : ℕ), (sigma.mk i $ f x) ∈ subtree' ps (g (x + list.length ps)))
: all_agree f :=
begin
  subst i',
  induction ps generalizing i g; intro,
  { simp! at Hsub,
    have := (Hsub n),
    replace Hsub := (Hsub $ succ n),
    dsimp [length] at *,
    -- simp at *,
    rw [this,Hsub], apply Hg, },
  { dsimp at Hsub,
    apply ps_ih Hg, intro,
    specialize Hsub x,
    cases h : (g (x + (length ps_tl + 1))),
    rw h at Hsub, rcases ps_hd with ⟨ j, y, k ⟩,
    simp [subtree'] at Hsub,
    rcases Hsub with ⟨ ⟨h₀,h₁⟩, Hsub ⟩,
    subst_all,
    revert Hsub, apply eq.mp,
    h_generalize _ : _ == k',
    have Heq : (a_1 k') == (g (x + length ps_tl)), admit,
    -- have := heq.subst this,
    let := (a_1 k'),
    let := (g (x + length ps_tl)),
    apply congr_arg,
    apply subtree'_congr _ _ _ _ Heq,
    apply congr_arg,
    subst_all,
    congr' ,
    h_subst this,
     },

  -- revert f g,
  -- induction ps generalizing i i' g,
  -- -- admit,
  -- -- done,
  -- -- ; introv Hg Hsub,
  -- { simp [subtree'] at *, simp [*,all_agree],
  --   intro, refine cast _ (Hg n),
  --   have Hsub' := Hsub n,
  --   specialize Hsub (succ n),
  --   casesm* _ ∧ _, subst i',
  --   simp at *,
  --   simp *, refl },
  -- { intro n,
  --   rcases ps_hd with ⟨ ii, y, j ⟩,
  --   induction n with n generalizing f g i' j, simp,
  --   have Hg_succ_n := Hg (succ n),
  --   have : i' = ii, admit,
  --   subst ii,
  --   -- have f_head : ∀ n, y = (head' (f (succ n))),
  --   -- { admit },
  --   have g_head : ∀ n, y = (head' (g (succ n))),
  --   { -- intro n, specialize Hsub 0,
  --     -- cases Hk : g (0 + length (link j :: ps_tl)) with _ y₂ ch₂,
  --     -- have Hsub' := Hsub,
  --     -- simp! at Hk, rw Hk,
  --     -- done,
  --     -- rw Hk at Hsub,
  --     -- simp at Hsub, rcases Hsub with ⟨ ⟨ _, _⟩ , _⟩, cases Hsub_w_right,
  --     -- change head' (cofix_a.intro y₂ ch₂) = _,
  --     -- rw ← Hk,
  --     -- apply head_succ' _ _ g Hg,
  --     admit
  --     },
  --   -- revert f g,
  --   -- have stuff : ∀ n, cofix_a γ (γ i (head' (g (succ n))) (cast (by rw g_head) j)) n = cofix_a γ (γ i y j) n,
  --   -- { intro n, specialize g_head n, subst y, refl },
  --   revert n_ih,
  --   cases h_succ_n : f (succ n),
  --   cases h_succ_succ_n : f (succ $ succ n),
  --   cases h_n : f n,
  --   have : a = a_2, admit, subst a_2,
  --   intro, constructor,
  --   intro, cases (a_1 j_1), constructor,
  --   have : a = a_2, admit, subst a_2,
  --   intro,
  --   constructor, intro,
  --   -- have : a = y, admit, subst a,
  --   let g' : Π (n : ℕ), cofix_a γ (γ i' y j) n,
  --   { intro n, refine cast _ (children' (g $ succ n) (cast (by rw g_head) j)),
  --     specialize g_head n, subst y, refl },
  --   let f' : Π (n : ℕ), cofix_a γ (γ i a j_1) n,
  --   { intro n, refine cast _ (children' (f $ succ n) (cast _ j_1)),
  --     specialize g_head n, subst y, refl },
  --   specialize @ps_ih _ _ g' _ _ ,
  --   { -- cases h_n : f (succ n_1),
  --     -- cases h_succ_n : f (succ $ succ n),
  --     -- have : a = a_2, admit, subst a_2,
  --     -- apply agree.step,
  --     -- intros j',
  --     -- refine cast _ ps_ih,
  --     simp [h_succ_n,h_n] at ps_ih,
  --     -- specialize ps_ih_a j_1,
  --     cases ps_ih,
  --     -- congr,
  --     -- simp [f',h_succ_n,children'],
  --     { apply cast_eq_of_heq, clear_except h_succ_n,
  --       h_generalize _ : j_1 == j', revert j', rw [h_succ_n,children'],
  --       intros, cc, },
  --     { apply cast_eq_of_heq, clear_except h_succ_succ_n,
  --       h_generalize _ : j_1 == j', revert j', rw [h_succ_succ_n,children'],
  --       intros, cc, }, },
  --   { simp [g',all_agree], clear_except Hg,
  --     intro,
  --     h_generalize _ : _ == a₀,
  --     h_generalize _ : _ == a₁,
  --     specialize Hg (succ n), revert Hg Ha₀ Ha₁,
  --     h_generalize! _ : _ == ii,
  --     h_generalize! _ : _ == jj,
  --     cases h_succ : (g (succ n)), cases h_succ_succ : (g (succ (succ n))),
  --     dsimp [head',children'],
  --     intros, cases Hg,
  --     have : a = y, admit, subst a,
  --     refine cast _ (Hg_a jj), cc, },
  --   intro k,
  --   have Hsub_k := Hsub (k),
  --   cases Hk_succ : g (k + length (link j :: ps_tl)) with _ y₂ ch₂,
  --   simp [Hk_succ] at Hsub_k,
  --   rcases Hsub_k with ⟨ ⟨ Hsub_i, Hsub_y ⟩, Hsub_k ⟩,
  --   rcases Hsub_k_w_right,
  --   simp [g',f'],
  --   clear_except Hk_succ Hsub_k,
  --   h_generalize! _ : _ == ch_f,
  --   h_generalize! _ : _ == i₃,
  --   h_generalize! _ : _ == ch_g,
  --   h_generalize! _ : _ == j₃,
  --   { dsimp [add_one,add_succ,nat.add_zero] at Hk_succ,
  --     rw [Hk_succ,children'],
  --     intros,
  --     -- have : a = y, admit, subst a,
  --     refine cast _ Hsub_k,
  --     apply congr, apply congr_arg,
  --     { admit },
  --     { congr, dsimp [head'] at j₃, cases Hj₃, } },
  --   congr,
  --   change g (succ $ k + length ps_tl) = _ at Hk_succ,
  --   generalize Hj : cast _ i = j,
  --   generalize Hk : cast _ i = k,
  --   have Hjk : j == k, cc, clear Hj Hk,
  --   revert k Hk_succ,
  --   clear_except , generalize : (g (succ (k + length ps_tl))) = z,
  --   intros, subst z, simp [children'], cases Hjk, refl }
end

lemma ext_aux {i : ι} {n : ℕ} (x y : cofix_a γ i (succ n)) (z : cofix_a γ i n)
  (hx : agree z x)
  (hy : agree z y)
  (hrec : ∀ (ps : path β),
             (select' x ps).dom →
             (select' y ps).dom →
             n = ps.length →
            (select' x ps) = (select' y ps))
: x = y :=
begin
  induction n with n generalizing i,
  { cases x, cases y, cases z,
    suffices : x_a = y_a,
    { congr, assumption, subst y_a, simp,
      funext i, cases x_a_1 i, cases y_a_1 i, refl },
    clear hx hy,
    specialize hrec [] trivial trivial rfl,
    simp [select'] at hrec, injection hrec,
    replace h_2 := congr_fun (eq_of_heq h_2) trivial,
    injection h_2,
    apply eq_of_heq h_4,  },
  { cases x, cases y, cases z,
    have : y_a = z_a,
    { casesm* agree _ _, cc, },
    have : x_a = y_a,
    { casesm* agree _ _, cc, },
    subst x_a, subst z_a, congr,
    funext j, casesm* agree _ _,
    apply n_ih _ _ (z_a_1 j),
    { apply_assumption },
    { apply_assumption },
    { intros,
      have : succ n = 1 + length ps,
      { simp [*,one_add], },
      have Hselect : ∀ (x_a_1 : β i y_a → cofix_a γ _ (succ n)),
        (select' (cofix_a.intro y_a x_a_1) (⟨i, y_a, j⟩ :: ps)) = (select' (x_a_1 j) ps),
      { rw this, simp [select_cons'], },
      specialize hrec (⟨ i, y_a, j⟩ :: ps) _ _ (♯ this)
      ; try { simp [Hselect,*], },
      { simp [select',assert_if_pos] at hrec, exact hrec }, }, }
end

end coinduction.approx
open coinduction.approx

structure cofix_intl {α : ι → Type u₀} {β : Π i, α i → Type u₂}
  (γ : Π i a, β i a → ι) (i : ι) :=
  (approx : ∀ n, cofix_a γ i n)
  (consistent : all_agree approx)

def cofix {β : Π i, α i → Type u₂}
          (γ : Π i a, β i a → ι)
          (i : ι) := cofix_intl γ i

namespace cofix

variables {X : ι → Type*}
variables (f : Π i, X i → Σ y, Π a: β i y, X (γ i y a))
variables {β}

protected def corec {i : ι} (a : X i) : cofix γ i :=
{ approx := s_corec f a
, consistent := P_corec _ _ }
-- s : stream (set α)
-- h₀ : ∀ i, s i ≠ ∅
-- h₁ : ∀ i, s (i+1) ⊆ s i
-- example : (⋂ i, s i) ≠ ∅
variables {β γ}
variable {i : ι}
def head : cofix γ i → α i
 | ⟨ x, _ ⟩ := head' (x 1)

-- #check @head_succ' ι α β γ i
-- #check children'
-- #check cofix_a γ

-- #check eq.mp
-- #check @subtype.mk
def children : Π (x : cofix γ i) (y : β _ (head x)), cofix γ (γ _ _ y)
 | z@⟨ x, P ⟩ j :=
let H := λ n : ℕ, @head_succ' ι α β γ i n 0 x P in
have H' : Π n, β i (head z) = β i (head' (x (succ n))),
  by { simp [H], refl },
have H'' : Π n, γ i (head' (x (succ n))) (cast (by rw H') j) = γ i (head z) j,
  by { intro, h_generalize! h : j == k, rw [H], simp, refl },
{ approx := λ n,
    cast (by rw H'') (children' (x (succ n)) (cast _ j))
, consistent :=
  begin
    intro,
    have P' := P (succ n),
    apply agree_children (x $ succ n) (x $ succ $ succ n) ;
      try { refl <|> assumption <|> rw ← H'' <|> simp },
    simp,
  end }
-- #check β
-- #print agree
-- #print cofix_intl
-- #check @cofix
protected def s_mk {i} (x : α i) (ch : Π b : β i x, cofix γ (γ i x b)) : Π n, cofix_a γ i n
 | 0 :=  cofix_a.continue _
 | (succ n) := cofix_a.intro x (λ j, (ch j).approx _)

protected def P_mk {i} (x : α i) (ch : Π b : β i x, cofix γ (γ i x b))
: all_agree (cofix.s_mk x ch) :=
begin
  intro i, induction i,
  { constructor },
  { constructor,
    intros j,
    have := (ch j).consistent,
    apply_assumption, }
end

protected def mk {i} (x : α i) (ch : Π b : β i x, cofix γ (γ i x b)) : cofix γ i :=
{ approx := cofix.s_mk x ch
, consistent := cofix.P_mk x ch }

@[simp]
lemma children_mk {i} (x : α i) (ch : Π b : β i x, cofix γ (γ i x b))
: children (cofix.mk x ch) = ch :=
begin
  funext i,
  dsimp [cofix.mk,children],
  cases h : ch i,
  simp, congr,
  funext n,
  dsimp [cofix.s_mk,children',cast_eq],
  rw h,
end

lemma mk_head_children (x : cofix γ i)
: x = cofix.mk (head x) (children x) :=
begin
  cases x,
  unfold cofix.mk,
  congr,
  funext n,
  induction n with n,
  { dsimp [head], cases x_approx 0, refl },
  dunfold cofix.s_mk,
  cases h : x_approx (succ n) with _ _ _ hd ch,
  { simp [children],
    split,
    { unfold head,
      change x_approx with ({ cofix_intl . approx := x_approx, consistent := x_consistent}).approx,
      rw ← head_succ' n 0 _ x_consistent,
      change _ = (head' $ x_approx (succ n)),
      rw h, refl },
    { apply hfunext,
      dsimp, congr' 1,
      { dsimp [head],
        rw [← head_succ' n,h], refl,
        assumption },
      { intros, simp,
        h_generalize! _ : _ == k,
        rw h, intros, congr, cc, } } },
end

protected def cases {r : Π {i}, cofix γ i → Sort w}
  (f : ∀ {i : ι} (x : α i) (c : Π b : β i x, cofix γ (γ i x b)), r (cofix.mk x c)) (x : cofix γ i) : r x :=
suffices r (cofix.mk (head x) (children x)),
  by { rw [mk_head_children x], exact this },
f (head x) (children x)

protected def cases_on {r : Π {i}, cofix γ i → Sort w}
  (x : cofix γ i)
  (f : ∀ {i} (x : α i) (c : Π b : β i x, cofix γ (γ i x b)), r (cofix.mk x c)) :
  r x :=
cofix.cases @f x

@[simp]
lemma head_mk {i} (x : α i) (ch : Π b : β i x, cofix γ (γ i x b))
: head (cofix.mk x ch) = x :=
rfl

@[simp]
lemma cases_mk {r : Π {i}, cofix γ i → Sort*} {i}
  (x : α i) (ch : Π b : β i x, cofix γ (γ i x b))
  (f : ∀ {i} (x : α i) (c : Π b : β i x, cofix γ (γ i x b)), r (cofix.mk x c)) :
  cofix.cases @f (cofix.mk x ch) = f x ch :=
begin
  simp [cofix.cases],
  h_generalize h : _ == k,
  rw [children_mk] at h, subst h, refl,
end

@[simp]
lemma head_corec  (x : X i)
: head (cofix.corec _ f x) = (f _ x).fst :=
begin
  dsimp [cofix.corec,head,s_corec],
  cases f i x, refl
end

@[simp]
lemma children_corec  (x : X i) (y : β _ (head (cofix.corec _ f x)))
: children (cofix.corec _ f x) y = cofix.corec γ f (cast _ $ (f i x).2 $ cast (by { simp }) y) :=
sorry

lemma children_cast_eq_of_eq {x} (y : cofix γ i) {i : β _ (head y)}
  (H : x = y)
: children x (♯ i) = ♯ children y i :=
by { subst y, refl }

def select : ∀ (x : cofix γ i) (ps : path β), roption (Σ i, α i)
 | ⟨approx,H⟩ ps := select' (approx $ succ ps.length) ps

@[simp]
lemma select_nil (x : cofix γ i)
: select x [] = return ⟨i,head x⟩ :=
begin
  cases x, dsimp [select,head,select',head',length],
  cases x_approx 1, simp [select',head'],
end

-- @[simp]
lemma select_cons (x : cofix γ i) (y i p)
  (H : y = head x)
: select x (⟨_,y,i⟩ :: p) = select (children x $ ♯ i) p :=
begin
  cases H,
  cases x, simp [select,head,select',head',children],
  dsimp [length,select,select',children'],
  generalize Hj : (cast _ i) = j,
  replace Hj : i == j, cc,
  revert i j,
  cases H : x_approx (succ (length p + 1)),
  simp [children',select'], intros,
  h_generalize! h : _ == k,
  h_generalize! h' : _ == k',
  -- simp,
  dsimp [select',head],
  rw [H,select',children'],
  intros,
  rw assert_if_pos,
  { subst_all,  h_generalize h'' : j == k₁,
    { have : a_1 k₁ == k, cc,
      clear h h' h'' k',
      dsimp at a_1,
      revert k,
      rw [← head_succ' (length p + 1)], },
    h_subst this,
    congr, },
  { dsimp [head], rw [head_succ' _ (length p + 1) x_approx x_consistent],
    change head' (x_approx _) = _,
    rw H, refl },
end

lemma dom_select_cons (x : cofix γ i) (y i p)
: (select x (⟨_,y,i⟩ :: p)).dom → y = head x :=
sorry
#check all_or_nothing
#check subtree' _
def subtree : Π (x : cofix γ i) (ps : path β), roption (Σ i, cofix γ i)
 | ⟨approx, consistent⟩ ps :=
do ⟨ f, Hf ⟩ ← all_or_nothing (λ y, subtree' ps (approx (_ + ps.length))),
   return (⟨ f
   , assume _, agree_of_mem_subtree' _ consistent Hf _ ⟩ )

def child (x : cofix γ i) (ps : path β)
          (H : (subtree x ps).dom) (b : β _ (head ((subtree x ps).get H).2))
: cofix _ _ :=
children ((subtree x ps).get H).2 b

#check child

@[simp]
lemma subtree_nil (x : cofix γ i)
: subtree x [] = return ⟨_,x⟩ :=
sorry

@[simp]
lemma subtree_nil_dom (x : cofix γ i)
: (subtree x []).dom ↔ true :=
sorry

@[simp]
lemma subtree_nil_get (x : cofix γ i)
: (subtree x []).get (by simp) = x :=
by simp; refl

@[simp]
lemma subtree_cons' (x : cofix γ i) {y i p}
  (H : y = head x)
: subtree x (⟨_,y,i⟩ :: p) = subtree (children x (♯ i)) p :=
sorry

@[simp]
lemma subtree_cons_dom' (x : cofix γ i) {y i p}
  (H : y = head x)
: (subtree x (⟨_,y,i⟩ :: p)).dom :=
begin
  cases x,
  simp [subtree],
end


@[simp]
lemma child_nil (x : cofix γ i)
          (H : (subtree x []).dom) (i : β _ (head ((subtree x []).get H).2))
: child x [] H i == (children x (cast (by { simp, }) i))  :=
sorry

@[simp]
lemma child_cons (x : cofix γ i) {y i p}
  (H' : y = head x)
  (H₀ : (subtree x (⟨_,y,i⟩ :: p)).dom)
  (j : β _ (head ((subtree x (⟨_,y,i⟩ :: p)).get H₀).2))
: child x (⟨_,y,i⟩ :: p) _ j == child (children x (♯ i)) p (♯ H₀) (♯ j) :=
sorry

end cofix
