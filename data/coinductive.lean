/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Basic machinery for defining general coinductive types

Work in progress
-/
import data.pfun

import data.stream

universes u v w

open nat function roption list

variables {α : Type u}
variables (β : α → Type v)

local prefix `♯`:0 := cast (by simp [*] <|> cc <|> solve_by_elim)

local attribute [instance, priority 0] classical.prop_decidable

namespace coinduction.approx

/-
coinductive ind {α : Type u} (β : α → Type v) : Type (max u v)
| intro : ∀ a, (β a → ind) → ind
-/

inductive cofix_a : ℕ → Type (max u v)
| continue : cofix_a 0
| intro {n} : ∀ a, (β a → cofix_a n) → cofix_a (succ n)

variables {β}

def head' : Π {n}, cofix_a β (succ n) → α
 | n (cofix_a.intro i _) := i

def children' : Π {n} (x : cofix_a β (succ n)), (β (head' x) → cofix_a β n)
 | n (cofix_a.intro _ f) := f

def agree
: ∀ {n : ℕ}, cofix_a β n → cofix_a β (n+1) → Prop
 | 0 continue _ := true
 | n (cofix_a.intro x y) (cofix_a.intro x' y') :=
   x = x' ∧ ∀ i j : β _, i == j → agree (y i) (y' j)

def all_agree (x : Π n, cofix_a β n) :=
∀ n, agree (x n) (x (succ n))

@[simp]
lemma agree_trival {x : cofix_a β 0} {y : cofix_a β 1}
: agree x y :=
by { cases x, trivial }

lemma agree_def {n : ℕ} (x : cofix_a β (succ n)) (y : cofix_a β (succ n+1))
  (h₀ : head' x = head' y)
  (h₁ : ∀ (i : β _) (j : β _), i == j → agree (children' x i) (children' y j))
: agree x y :=
begin
  cases x, cases y,
  unfold agree,
  cases h₀,
  existsi rfl,
  unfold children' at h₁,
  intro, apply h₁,
end

lemma agree_children {n : ℕ} (x : cofix_a β (succ n)) (y : cofix_a β (succ n+1))
  {i j}
  (h₀ : i == j)
  (h₁ : agree x y)
: agree (children' x i) (children' y j) :=
begin
  cases x, cases y,
  unfold agree at h₁,
  cases h₁ with h h₁, subst x_a,
  unfold children',
  cases h₀, apply h₁,
  assumption,
end

def truncate {α : Type u} {β : α → Type v}
: ∀ {n : ℕ}, cofix_a β (n+1) → cofix_a β n
 | 0 (cofix_a.intro _ _) := cofix_a.continue _
 | (succ n) (cofix_a.intro i f) := cofix_a.intro i $ truncate ∘ f

lemma truncate_eq_of_agree {α : Type u} {β : α → Type v} {n : ℕ}
  (x : cofix_a β n)
  (y : cofix_a β (succ n))
  (h : agree x y)
: truncate y = x :=
begin
  revert x y,
  induction n
  ; intros x y
  ; cases x ; cases y,
  { intro h', refl },
  { simp [agree,truncate,exists_imp_distrib],
    introv h₀ h₁,
    subst x_a, split, refl,
    apply heq_of_eq, funext y, unfold comp,
    apply n_ih,
    apply h₁, refl }
end

variables {X : Type w}
variables (f : X → Σ y, β y → X)

def s_corec : Π (i : X) n, cofix_a β n
 | _ 0 := cofix_a.continue _
 | j (succ n) :=
   let ⟨y,g⟩ := f j in
   cofix_a.intro y (λ i, s_corec (g i) _)

lemma P_corec (i : X) (n : ℕ) : agree (s_corec f i n) (s_corec f i (succ n)) :=
begin
  revert i,
  induction n with n ; intro i,
  trivial,
  cases h : f i with y g,
  simp [s_corec,h,s_corec._match_1,agree] at ⊢ n_ih,
  introv h',
  cases h',
  apply n_ih,
end

abbreviation path' (β : α → Type v) := list (Σ i, β i)

def select' : ∀ {n : ℕ}, cofix_a β n → path' β → roption α
 | ._ (cofix_a.continue _) _ := roption.none
 | (succ _) (cofix_a.intro y' ch) [] := return y'
 | (succ _) (cofix_a.intro y' ch) (⟨y, i⟩ :: ys) :=
assert (y = y') $ λ h,
select' (ch $ ♯ i) ys

def subtree' : ∀ {n : ℕ} (ps : path' β) (x : cofix_a β (n + ps.length)), roption (cofix_a β n)
 | n [] t := return t
 | n (⟨y, i⟩ :: ys) (cofix_a.intro y' ch) :=
assert (y = y') $ λ h,
subtree' ys (ch $ ♯i)

open list

lemma select_of_lt_length' {n : ℕ}
  {ps : path' β}
  {x : cofix_a β n}
  (Hg : n < ps.length)
: @select' α β _ x ps = roption.none :=
begin
  revert x n,
  induction ps ; introv Hg,
  { cases not_lt_zero _ Hg },
  { cases ps_hd with y' i,
    cases x with n y ch,
    { dsimp [select'], refl },
    by_cases (β y' = β y),
    { simp [select',assert_if_pos,*],
      apply ps_ih, apply lt_of_succ_lt_succ Hg, },
    { simp [select',assert_if_neg,*], } },
end

@[simp]
lemma select_cons' {n : ℕ}
  {ps : path' β}
  {y : α} {i : β y} {ch : β y → cofix_a β (n + length ps)}
: select' (cofix_a.intro y ch) (⟨y,i⟩ :: ps) = select' (ch i) ps :=
by simp [select',assert_if_pos,cast_eq]

@[simp, priority 0]
lemma subtree_cons {n : ℕ}
  {ps : path' β}
  {y : α} {i : β y} {ch : β y → cofix_a β (n + length ps)}
: subtree' (⟨y,i⟩ :: ps) (cofix_a.intro y ch) = subtree' ps (ch i) :=
by simp [subtree',assert_if_pos,cast_eq]

lemma subtree_cons_of_ne {n : ℕ}
  {ps : path' β}
  {y y' : α} {i : β y} {ch : β y' → cofix_a β (n + length ps)}
  (Hne : y ≠ y')
: subtree' (⟨y,i⟩ :: ps) (cofix_a.intro y' ch) = none :=
by { simp [*,subtree',assert_if_neg], refl }

@[simp]
lemma mem_subtree_cons_iff {n : ℕ}
  {x : cofix_a β n}
  {ps : path' β}
  {y y' : α} {i : β y} {ch : β y' → cofix_a β (n + length ps)}
: x ∈ subtree' (⟨y,i⟩ :: ps) (cofix_a.intro y' ch) ↔ ∃ h : y' = y, x ∈ subtree' ps (ch $ ♯i) :=
begin
  split ; intro H,
  { have : y = y',
    { by_contradiction,
      simp [subtree_cons_of_ne a,has_mem.mem,roption.mem] at H,
      cases H with H, cases H, },
    subst y',
    existsi rfl, simp at H,
    simp [cast_eq,H], },
  { cases H, subst y,
    simp, exact H_h, },
end

instance : subsingleton (cofix_a β 0) :=
⟨ by { intros, casesm* cofix_a β 0, refl } ⟩

def all_or_nothing (f : Π x : α, roption (β x))
: roption { g : Π x, β x // ∀ x, g x ∈ f x } :=
⟨ ∀ x, (f x).dom, assume h, ⟨ λ x, (f _).get (h _), assume x, ⟨ h x, rfl ⟩ ⟩ ⟩

open list nat
lemma head_succ' (n m : ℕ) (x : Π n, cofix_a β n)
  (Hconsistent : all_agree x)
: head' (x (succ n)) = head' (x (succ m)) :=
begin
  suffices : ∀ n, head' (x (succ n)) = head' (x 1),
  { simp [this] },
  clear m n, intro,
  cases h₀ : x (succ n) with _ i₀ f₀,
  cases h₁ : x 1 with _ i₁ f₁,
  simp [head'],
  induction n with n,
  { rw h₁ at h₀, cases h₀, trivial },
  { have H := Hconsistent (succ n),
    cases h₂ : x (succ n) with _ i₂ f₂,
    rw [h₀,h₂] at H,
    apply n_ih (truncate ∘ f₀),
    rw h₂,
    unfold agree at H,
    cases H with h H, cases h,
    congr, funext j, unfold comp,
    rw truncate_eq_of_agree,
    apply H, refl }
end

lemma agree_of_mem_subtree' (ps : path' β) {f g : Π n : ℕ, cofix_a β n}
 (Hg : all_agree g)
 (Hsub : ∀ (x : ℕ), f x ∈ subtree' ps (g (x + list.length ps)))
: all_agree f :=
begin
  revert f g,
  induction ps
  ; introv Hg Hsub,
  { simp [subtree'] at *, simp [*,all_agree], apply_assumption, },
  { intro n,
    induction n with n, simp,
    have Hg_succ_n := Hg (succ n),
    cases ps_hd with y i,
    have : ∀ n, y = (head' (g (succ n))),
    { intro j, specialize Hsub 0,
      cases Hk : g (0 + length (sigma.mk y i :: ps_tl)) with _ y₂ ch₂,
      have Hsub' := Hsub,
      rw Hk at Hsub,
      simp at Hsub, cases Hsub, subst y,
      change head' (cofix_a.intro y₂ ch₂) = _,
      rw ← Hk,
      apply head_succ' _ _ g Hg, },
    let g' := λ n, children' (g $ succ n) (cast (by rw this) i),
    apply @ps_ih _ g',
    { simp [g',all_agree], clear_except Hg,
      intro,
      generalize Hj : cast _ i = j,
      generalize Hk : cast _ i = k,
      have Hjk : j == k, cc, clear Hj Hk,
      specialize Hg (succ n),
      cases (g (succ n)), cases (g (succ (succ n))),
      simp [children'], simp [agree] at Hg,
      apply Hg.2 _ _ Hjk, },
    intro k,
    have Hsub_k := Hsub (k),
    cases Hk_succ : g (k + length (sigma.mk y i :: ps_tl)) with _ y₂ ch₂,
    simp [Hk_succ] at Hsub_k,
    cases Hsub_k with _ Hsub_k, subst y,
    simp [g'],
    refine cast _ Hsub_k,
    congr,
    change g (succ $ k + length ps_tl) = _ at Hk_succ,
    generalize Hj : cast _ i = j,
    generalize Hk : cast _ i = k,
    have Hjk : j == k, cc, clear Hj Hk,
    revert k Hk_succ,
    clear_except , generalize : (g (succ (k + length ps_tl))) = z,
    intros, subst z, simp [children'], cases Hjk, refl }
end

@[simp]
lemma roption.get_return {α} (x : α) (H)
: roption.get (return x) H = x :=
rfl

lemma ext_aux {n : ℕ} (x y : cofix_a β (succ n)) (z : cofix_a β n)
  (hx : agree z x)
  (hy : agree z y)
  (hrec : ∀ (ps : path' β),
             (select' x ps).dom →
             (select' y ps).dom →
             n = ps.length →
            (select' x ps) = (select' y ps))
: x = y :=
begin
  induction n with n,
  { cases x, cases y, cases z,
    suffices : x_a = y_a,
    { congr, assumption, subst y_a, simp,
      funext i, cases x_a_1 i, cases y_a_1 i, refl },
    clear hx hy,
    specialize hrec [] trivial trivial rfl,
    simp [select'] at hrec, injection hrec,
    replace h_2 := congr_fun (eq_of_heq h_2) trivial,
    exact h_2,  },
  { cases x, cases y, cases z,
    have : y_a = z_a,
    { simp [agree] at hx hy, cc, },
    have : x_a = y_a,
    { simp [agree] at hx hy, cc, },
    subst x_a, subst z_a, congr,
    funext i, simp [agree] at hx hy,
    apply n_ih _ _ (z_a_1 i),
    { apply hx _ _ rfl },
    { apply hy _ _ rfl },
    { intros,
      have : succ n = 1 + length ps,
      { simp [*,one_add], },
      have Hselect : ∀ (x_a_1 : β y_a → cofix_a β (succ n)),
        (select' (cofix_a.intro y_a x_a_1) (⟨y_a, i⟩ :: ps)) = (select' (x_a_1 i) ps),
      { rw this, simp [select_cons'], },
      specialize hrec (⟨ y_a, i⟩ :: ps) _ _ (♯ this)
      ; try { simp [Hselect,*], },
      { simp [select',assert_if_pos] at hrec, exact hrec }, }, }
end

end coinduction.approx
open coinduction.approx

structure cofix_intl  {α : Type u} (β : α → Type v) : Type (max u v) :=
  (approx : ∀ n, cofix_a β n)
  (consistent : all_agree approx)

def cofix (β : α → Type*) := cofix_intl β

namespace cofix

variables {X : Type*}
variables (f : X → Σ y, β y → X)
variables {β}
protected def corec (i : X) : cofix β :=
{ approx := s_corec f i
, consistent := P_corec _ _ }
variables {β}
def head : cofix β → α
 | ⟨ x, _ ⟩ := head' (x 1)

def children : Π (x : cofix β), (β (head x) → cofix β)
 | ⟨ x, P ⟩ i :=
let H := λ n : ℕ, @head_succ' _ _ n 0 x P in
{ approx := λ n, children' (x _) (cast (congr_arg _ $ by simp [head,H]) i)
, consistent :=
  begin
    intro,
    have P' := P (succ n),
    apply agree_children _ _ _ P',
    transitivity i,
    apply cast_heq,
    symmetry,
    apply cast_heq,
  end }

protected def s_mk (x : α) (ch : β x → cofix β) : Π n, cofix_a β n
 | 0 :=  cofix_a.continue _
 | (succ n) := cofix_a.intro x (λ i, (ch i).approx n)

protected def P_mk  (x : α) (ch : β x → cofix β)
: all_agree (cofix.s_mk x ch)
 | 0 := by unfold cofix.s_mk
 | (succ n) := by { unfold cofix.s_mk agree,
                    existsi rfl,
                    introv h, cases h,
                    apply (ch i).consistent }

protected def mk (x : α) (ch : β x → cofix β) : cofix β :=
{ approx := cofix.s_mk x ch
, consistent := cofix.P_mk x ch }

@[simp]
lemma children_mk (x : α) (ch : β x → cofix β)
: children (cofix.mk x ch) = ch :=
begin
  funext i,
  dsimp [cofix.mk,children],
  cases h : ch i,
  congr,
  funext n,
  dsimp [cofix.s_mk,children',cast_eq],
  rw h,
end

lemma mk_head_children (x : cofix β)
: x = cofix.mk (head x) (children x) :=
begin
  cases x,
  unfold cofix.mk,
  congr,
  funext n,
  induction n with n,
  { dsimp [head], cases x_approx 0, refl },
  unfold cofix.s_mk,
  cases h : x_approx (succ n) with _ hd ch,
  simp [children],
  split,
  { unfold head,
    change x_approx with ({ cofix_intl . approx := x_approx, consistent := x_consistent}).approx,
    rw ← head_succ' n 0 _ x_consistent,
    change _ = (head' $ x_approx (succ n)),
    rw h, refl },
  { change ch with children' (cofix_a.intro hd ch),
    clear n_ih,
    apply hfunext,
    { unfold head, rw [← h,head_succ' n _ x_approx x_consistent] },
    introv h',
    congr, rw h,
    transitivity y, apply h',
    symmetry, apply cast_heq, },
end

protected def cases {r : cofix β → Sort w}
  (f : ∀ (i : α) (c : β i → cofix β), r (cofix.mk i c)) (x : cofix β) : r x :=
suffices r (cofix.mk (head x) (children x)),
  by { rw [mk_head_children x], exact this },
f (head x) (children x)

protected def cases_on {r : cofix β → Sort w}
    (x : cofix β) (f : ∀ (i : α) (c : β i → cofix β), r (cofix.mk i c)) : r x :=
cofix.cases f x

@[simp]
lemma head_mk (x : α) (ch : β x → cofix β)
: head (cofix.mk x ch) = x :=
rfl

@[simp]
lemma cases_mk {r : cofix β → Sort*} (x : α) (ch : β x → cofix β) (f : Π x (ch : β x → cofix β), r (cofix.mk x ch))
: cofix.cases f (cofix.mk x ch) = f x ch :=
sorry

@[simp]
lemma head_corec  (i : X)
: head (cofix.corec f i) = (f i).fst :=
sorry

@[simp]
lemma children_corec  (i : X) (y : β (head (cofix.corec f i)))
: children (cofix.corec f i) y = cofix.corec f ((f i).2 $ ♯ y) :=
sorry

lemma children_cast_eq_of_eq {x} (y : cofix β) {i : β (head y)}
  (H : x = y)
: children x (♯ i) = children y i :=
by { subst y, refl, }

def select : ∀ (x : cofix β) (ps : path' β), roption α
 | ⟨approx,H⟩ ps := select' (approx $ succ ps.length) ps

@[simp]
lemma select_nil (x : cofix β)
: select x [] = return (head x) :=
begin
  cases x, dsimp [select,head,select',head',length],
  cases x_approx 1, simp [select',head'],
end

@[simp]
lemma select_cons (x : cofix β) (y i p)
  (H : y = head x)
: select x (⟨y,i⟩ :: p) = select (children x $ ♯ i) p :=
begin
  cases H,
  cases x, simp [select,head,select',head',children],
  dsimp [length,select,select',children'],
  generalize Hj : (cast _ i) = j,
  replace Hj : i == j, cc,
  revert i j,
  cases H : (x_approx (succ (length p + 1))),
  simp [children',select'], intros,
  rw assert_if_pos,
  { congr, apply eq_of_heq, transitivity i, apply cast_heq, assumption, },
  { congr, simp [head], rw [head_succ' _ (length p + 1) x_approx x_consistent],
    change head' (x_approx _) = _,
    rw H, refl },
end

lemma dom_select_cons (x : cofix β) (y i p)
: (select x (⟨y,i⟩ :: p)).dom → y = head x :=
sorry

def subtree : Π (x : cofix β) (ps : path' β), roption (cofix β)
 | ⟨approx, consistent⟩ ps :=
do ⟨f,Hf⟩ ← all_or_nothing (λ n, @subtree' α β _ ps (approx (n + ps.length))),
   return (⟨ f
   , assume _, agree_of_mem_subtree' _ consistent Hf _ ⟩ )

def child (x : cofix β) (ps : path' β)
          (H : (subtree x ps).dom) (i : β (head ((subtree x ps).get H)))
: cofix β :=
children ((subtree x ps).get H) i

@[simp]
lemma subtree_nil (x : cofix β)
: subtree x [] = return x :=
sorry

@[simp]
lemma subtree_nil_dom (x : cofix β)
: (subtree x []).dom ↔ true :=
sorry

@[simp]
lemma subtree_nil_get (x : cofix β)
: (subtree x []).get (by simp) = x :=
by simp

@[simp]
lemma subtree_cons' (x : cofix β) {y i p}
  (H : y = head x)
: subtree x (⟨y,i⟩ :: p) = subtree (children x (♯ i)) p :=
sorry

@[simp]
lemma subtree_cons_dom' (x : cofix β) {y i p}
  (H : y = head x)
: (subtree x (⟨y,i⟩ :: p)).dom :=
sorry



@[simp]
lemma child_nil (x : cofix β)
          (H : (subtree x []).dom) (i : β (head ((subtree x []).get H)))
: child x [] H i = children x (cast (by simp) i) :=
sorry

@[simp]
lemma child_cons (x : cofix β) {y i p}
  (H' : y = head x)
  (H₀ : (subtree x (⟨y,i⟩ :: p)).dom)
  (j : β (head ((subtree x (⟨y,i⟩ :: p)).get H₀)))
: child x (⟨y,i⟩ :: p) _ j = child (children x (♯ i)) p (♯ H₀) (♯ j) :=
sorry

lemma ext (x y : cofix β)
  (H : ∀ (ps : path' β), (select x ps).dom →
                         (select y ps).dom →
                         select x ps = select y ps)
: x = y :=
begin
  cases x, cases y,
  congr, funext i,
  induction i with i,
  { cases x_approx 0, cases y_approx 0, refl },
  { apply ext_aux, apply_assumption,
    rw i_ih, apply_assumption,
    introv h₀ h₁ H',
    simp [select] at H,
    cases H',
    apply H ps ; assumption, }
end

section bisim
  variable (R : cofix β → cofix β → Prop)
  local infix ~ := R

  def is_bisimulation :=
      ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ →
        head s₁ = head s₂ ∧
        (∀ i j : β (head _), i == j → children s₁ i ~ children s₂ j)

  theorem nth_of_bisim (bisim : is_bisimulation R) :
     ∀ (s₁ s₂) (ps : path' β)
       (H₁ : (select s₁ ps).dom)
       (H₂ : (select s₂ ps).dom),
       s₁ ~ s₂ →
         (select s₁ ps) = (select s₂ ps) ∧
         ∀ Hi Hj i j, i == j →
                child s₁ ps Hi i ~ child s₂ ps Hj j :=
  begin
    intros _ _ _,
    revert s₁ s₂,
    induction ps,
    { introv _ _ h₀,
      have h₁ := bisim h₀,
      simp, split, cc,
      intros,
      apply h₁.2, cc, },
    { introv _ _ h₀,
      cases ps_hd with y i,
      have hd₁ : y = head s₁, { apply dom_select_cons, assumption },
      have hd₂ : y = head s₂, { apply dom_select_cons, assumption },
      split, rw [select_cons,select_cons] ; try { assumption },
      { apply (ps_ih _ _ _ _ _).1 ; clear ps_ih,
        simp [hd₁] at H₁, assumption,
        simp [hd₂] at H₂, assumption,
        simp [is_bisimulation] at bisim,
        apply (bisim h₀).2, cc, },
      intros,
      { simp [hd₁] at ⊢ H₁, simp [hd₂] at ⊢ H₂,
        apply (ps_ih _ _ _ _ _).2 ; clear ps_ih
        ; try { cc <|> assumption },
        apply (bisim h₀).2, cc, } },
  end

  theorem eq_of_bisim (bisim : is_bisimulation R) : ∀ {s₁ s₂}, s₁ ~ s₂ → s₁ = s₂ :=
  begin
    introv Hr, apply ext,
    introv Hs₁ Hs₂,
    have H := nth_of_bisim R bisim _ _ ps ,
    apply (H _ _ _).left ; assumption,
  end
end bisim

section coinduction

variables β
def R (s₁ s₂ : cofix β) :=
   head s₁ = head s₂ ∧
            ∀ (FR : Π x y : cofix β, Prop),
              reflexive FR →
              FR s₁ s₂ →
            ∀ i j, i == j →
                FR (children s₁ i) (children s₂ j)

open ulift
lemma R_is_bisimulation : is_bisimulation (R β) :=
begin
  simp [is_bisimulation,R],
  introv H_head H_coind,
  split, assumption,
  introv Hij,
  split,
  { apply H_coind (λ x y, head x = head y)
    ; simp [reflexive] <|> assumption },
  { intros,
    let FR' : cofix β → cofix β → Prop := λ x y,
        FR x y →
        ∀ i j, i == j → FR (children x i) (children y j),
    apply H_coind FR' ; try { assumption },
    { simp [FR',reflexive], intros, subst i_2, solve_by_elim, },
    { simp [FR'], intros, apply H_coind ; assumption, }, },
end

variables {β}

-- lemma coinduction {s₁ s₂ : cofix β}
--   (hh : head s₁ = head s₂)
--   (ht : ∀ {γ : Sort u} (fr : cofix β → γ),
--           fr s₁ = fr s₂ →
--           ∀ i j, i == j →
--                  fr (children s₁ i) = fr (children s₂ j))
-- : s₁ = s₂ :=

lemma coinduction {s₁ s₂ : cofix β}
  (hh : head s₁ = head s₂)
  (ht : ∀ (FR : cofix β → cofix β → Prop),
          reflexive FR →
          FR s₁ s₂ →
          ∀ i j, i == j →
                 FR (children s₁ i) (children s₂ j))
: s₁ = s₂ :=
eq_of_bisim
  (R β) (R_is_bisimulation β)
  (and.intro hh $
   begin
     intros, specialize ht FR,
     apply ht ; assumption,
   end)

end coinduction

def iterate (x : α) (f : Π x, β x → α) : cofix β :=
cofix.corec (λ x, ⟨ x, f x⟩) x

universes u' v'

def map {α' : Type u'} {β' : α' → Type v'}
  (f : α → α') (g : Π x, β' (f x) → β x)
  (x : cofix  β) : cofix β' :=
cofix.corec (λ t, ⟨ f (head t), λ k, children t (g _ k) ⟩) x

def corec_on {X : Type*} (x₀ : X) (f : X → (Σ (y : α), β y → X)) : cofix β :=
cofix.corec f x₀

theorem corec_eq {X : Type*} (f : X → (Σ (y : α), β y → X)) (x₀ : X)
: cofix.corec f x₀ = sigma.rec_on (f x₀) (λ y ch, cofix.mk y (λ i, cofix.corec f (ch i))) :=
begin
  cases Hf : f x₀, simp,
  apply coinduction,
  { simp [*], },
  { intros, rw [children_mk,children_corec],
    generalize Hi : cast _ i = k,
    have : k == j, cc, clear Hi a_2 i,
    cases (f x₀), injection Hf, subst fst_1, cases h_2,
    suffices : (cofix.corec f ((sigma.mk fst snd).snd k)) = (cofix.corec f (snd j)),
    { rw this, apply a },
    congr, cc, }
end

theorem corec_eq' {X : Type*} (f : X → α) (g : Π x : X, β (f x) → X) (x₀ : X)
: cofix.corec (λ x, ⟨f x,g x⟩) x₀ = cofix.mk (f x₀) (λ i, cofix.corec (λ x, ⟨f x,g x⟩) (g x₀ i)) :=
corec_eq _ x₀

end cofix

attribute [irreducible] cofix
