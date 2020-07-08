/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Basic machinery for defining general coinductive types

Work in progress
-/
import data.pfun tactic.interactive
       data.qpf.univariate.basic
       meta.coinductive_predicates
universes u v w

open nat function list (hiding head')

variables (F : pfunctor.{u})

local prefix `♯`:0 := cast (by simp [*] <|> cc <|> solve_by_elim)

namespace pfunctor
namespace approx

inductive cofix_a : ℕ → Type u
| continue : cofix_a 0
| intro {n} : ∀ a, (F.B a → cofix_a n) → cofix_a (succ n)

@[ext]
lemma cofix_a_eq_zero : ∀ x y : cofix_a F 0, x = y
| cofix_a.continue cofix_a.continue := rfl

variables {F}

def head' : Π {n}, cofix_a F (succ n) → F.A
 | n (cofix_a.intro i _) := i

def children' : Π {n} (x : cofix_a F (succ n)), F.B (head' x) → cofix_a F n
 | n (cofix_a.intro a f) := f

lemma approx_eta  {n : ℕ} (x : cofix_a F (n+1)) :
  x = cofix_a.intro (head' x) (children' x) :=
by cases x; refl


inductive agree
: ∀ {n : ℕ}, cofix_a F n → cofix_a F (n+1) → Prop
 | continue (x : cofix_a F 0) (y : cofix_a F 1) : agree x y
 | intro {n} {a} (x : F.B a → cofix_a F n) (x' : F.B a → cofix_a F (n+1)) :
   (∀ i : F.B a, agree (x i) (x' i)) →
   agree (cofix_a.intro a x) (cofix_a.intro a x')

def all_agree (x : Π n, cofix_a F n) :=
∀ n, agree (x n) (x (succ n))

@[simp]
lemma agree_trival {x : cofix_a F 0} {y : cofix_a F 1}
: agree x y :=
by { constructor }

lemma agree_children {n : ℕ} (x : cofix_a F (succ n)) (y : cofix_a F (succ n+1))
  {i j}
  (h₀ : i == j)
  (h₁ : agree x y)
: agree (children' x i) (children' y j) :=
begin
  cases h₁, cases h₀,
  apply h₁_a_1,
end

def truncate
: ∀ {n : ℕ}, cofix_a F (n+1) → cofix_a F n
 | 0 (cofix_a.intro _ _) := cofix_a.continue
 | (succ n) (cofix_a.intro i f) := cofix_a.intro i $ truncate ∘ f

lemma truncate_eq_of_agree {n : ℕ}
  (x : cofix_a F n)
  (y : cofix_a F (succ n))
  (h : agree x y)
: truncate y = x :=
begin
  induction n generalizing x y
  ; cases x ; cases y,
  { refl },
  { cases h with _ _ _ _ _ h₀ h₁,
    cases h,
    simp [truncate,exists_imp_distrib,(∘)],
    ext y, apply n_ih,
    apply h₁ }
end

variables {X : Type w}
variables (f : X → F.apply X)

def s_corec : Π (i : X) n, cofix_a F n
 | _ 0 := cofix_a.continue
 | j (succ n) :=
   let ⟨y,g⟩ := f j in
   cofix_a.intro y (λ i, s_corec (g i) _)

lemma P_corec (i : X) (n : ℕ) : agree (s_corec f i n) (s_corec f i (succ n)) :=
begin
  induction n with n generalizing i,
  constructor,
  cases h : f i with y g,
  simp [s_corec,h,s_corec._match_1] at ⊢ n_ih,
  constructor,
  introv,
  apply n_ih,
end

def path (F : pfunctor.{u}) := list F.Idx

open list

instance : subsingleton (cofix_a F 0) :=
⟨ by { intros, casesm* cofix_a F 0, refl } ⟩

open list nat
lemma head_succ' (n m : ℕ) (x : Π n, cofix_a F n)
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
    cases H,
    congr, funext j, dsimp [comp],
    rw truncate_eq_of_agree,
    apply H_a_1 }
end

end approx
open approx

structure M_intl :=
  (approx : ∀ n, cofix_a F n)
  (consistent : all_agree approx)

def M := M_intl

namespace M

lemma ext' (x y : M F)
  (H : ∀ i : ℕ, x.approx i = y.approx i)
: x = y :=
begin
  cases x, cases y,
  congr, ext, apply H,
end

variables {X : Type*}
variables (f : X → F.apply X)
variables {F}

protected def corec (i : X) : M F :=
{ approx := s_corec f i
, consistent := P_corec _ _ }

variables {F}

def head : M F → F.A
 | x := head' (x.1 1)

def children : Π (x : M F), F.B (head x) → M F
| x i :=
   let H := λ n : ℕ, @head_succ' _ n 0 x.1 x.2 in
   { approx := λ n, children' (x.1 _) (cast (congr_arg _ $ by simp [head,H]; refl) i)
   , consistent :=
     begin
       intro,
       have P' := x.2 (succ n),
       apply agree_children _ _ _ P',
       transitivity i,
       apply cast_heq,
       symmetry,
       apply cast_heq,
     end }

def ichildren [inhabited (M F)] [decidable_eq F.A] : F.Idx → M F → M F
 | i x :=
if H' : i.1 = head x
  then children x (cast (congr_arg _ $ by simp [head,H']; refl) i.2)
  else default _

lemma head_succ (n m : ℕ) (x : M F)
: head' (x.approx (succ n)) = head' (x.approx (succ m)) :=
head_succ' n m _ x.consistent

lemma head_eq_head' : Π (x : M F) (n : ℕ),
  head x = head' (x.approx $ n+1)
| ⟨x,h⟩ n := head_succ' _ _ _ h

lemma head'_eq_head : Π (x : M F) (n : ℕ),
  head' (x.approx $ n+1) = head x
| ⟨x,h⟩ n := head_succ' _ _ _ h

lemma truncate_approx (x : M F) (n : ℕ) :
  truncate (x.approx $ n+1) = x.approx n :=
truncate_eq_of_agree _ _ (x.consistent _)

def from_cofix : M F → F.apply (M F)
 | x := ⟨head x,λ i, children x i ⟩

namespace approx

protected def s_mk (x : F.apply $ M F) : Π n, cofix_a F n
 | 0 :=  cofix_a.continue
 | (succ n) := cofix_a.intro x.1 (λ i, (x.2 i).approx n)

protected def P_mk  (x : F.apply $ M F)
: all_agree (approx.s_mk x)
 | 0 := by { constructor }
 | (succ n) := by { constructor, introv,
                    apply (x.2 i).consistent }

end approx

protected def mk (x : F.apply $ M F) : M F :=
{ approx := approx.s_mk x
, consistent := approx.P_mk x }

inductive agree' : ℕ → M F → M F → Prop
| trivial (x y : M F) : agree' 0 x y
| step {n : ℕ} {a} (x y : F.B a → M F) {x' y'} :
  x' = M.mk ⟨a,x⟩ →
  y' = M.mk ⟨a,y⟩ →
  (∀ i, agree' n (x i) (y i)) →
  agree' (succ n) x' y'

@[simp]
lemma from_cofix_mk (x : F.apply $ M F)
: from_cofix (M.mk x) = x :=
begin
  funext i,
  dsimp [M.mk,from_cofix],
  cases x with x ch, congr, ext i,
  cases h : ch i,
  simp [children,M.approx.s_mk,children',cast_eq],
  dsimp [M.approx.s_mk,children'],
  congr, rw h,
end

lemma mk_from_cofix (x : M F)
: M.mk (from_cofix x) = x :=
begin
  apply ext', intro n,
  dsimp [M.mk],
  induction n with n,
  { dsimp [head], ext },
  dsimp [approx.s_mk,from_cofix,head],
  cases h : x.approx (succ n) with _ hd ch,
  have h' : hd = head' (x.approx 1),
  { rw [← head_succ' n,h,head'], apply x.consistent },
  revert ch, rw h', intros, congr,
  { ext a, dsimp [children],
    h_generalize! hh : a == a'',
    rw h, intros, cases hh, refl },
end

lemma mk_inj {x y : F.apply $ M F}
  (h : M.mk x = M.mk y) : x = y :=
by rw [← from_cofix_mk x,h,from_cofix_mk]

protected def cases {r : M F → Sort w}
  (f : ∀ (x : F.apply $ M F), r (M.mk x)) (x : M F) : r x :=
suffices r (M.mk (from_cofix x)),
  by { haveI := classical.prop_decidable,
       haveI := inhabited.mk x,
       rw [← mk_from_cofix x], exact this },
f _

protected def cases_on {r : M F → Sort w}
  (x : M F) (f : ∀ (x : F.apply $ M F), r (M.mk x)) : r x :=
M.cases f x

protected def cases_on' {r : M F → Sort w}
  (x : M F) (f : ∀ a f, r (M.mk ⟨a,f⟩)) : r x :=
M.cases_on x (λ ⟨a,g⟩, f a _)

lemma approx_mk (a : F.A) (f : F.B a → M F) (i : ℕ) :
  (M.mk ⟨a, f⟩).approx (succ i) = cofix_a.intro a (λ j, (f j).approx i) :=
by refl

lemma agree'_refl [inhabited (M F)] [decidable_eq F.A] {n : ℕ} (x : M F) :
  agree' n x x :=
by { induction n generalizing x; induction x using pfunctor.M.cases_on'; constructor; try { refl }, intros, apply n_ih }

lemma agree_iff_agree' [inhabited (M F)] [decidable_eq F.A] {n : ℕ} (x y : M F) :
  agree (x.approx n) (y.approx $ n+1) ↔ agree' n x y :=
begin
  split; intros h,
  { induction n generalizing x y, constructor,
    { induction x using pfunctor.M.cases_on',
      induction y using pfunctor.M.cases_on',
      simp only [approx_mk] at h, cases h,
      constructor; try { refl },
      intro i, apply n_ih, apply h_a_1 } },
  { induction n generalizing x y, constructor,
    { cases h,
      induction x using pfunctor.M.cases_on',
      induction y using pfunctor.M.cases_on',
      simp only [approx_mk],
      replace h_a_1 := mk_inj h_a_1, cases h_a_1,
      replace h_a_2 := mk_inj h_a_2, cases h_a_2,
      constructor, intro i, apply n_ih, apply h_a_3 } },
end

@[simp]
lemma cases_mk {r : M F → Sort*} (x : F.apply $ M F) (f : Π (x : F.apply $ M F), r (M.mk x))
: pfunctor.M.cases f (M.mk x) = f x :=
begin
  dsimp [M.mk,pfunctor.M.cases,from_cofix,head,approx.s_mk,head'],
  cases x, dsimp [approx.s_mk],
  apply eq_of_heq,
  apply rec_heq_of_heq, congr,
  ext, dsimp [children,approx.s_mk,children'],
  cases h : x_snd x, dsimp [head],
  congr, ext,
  change (x_snd (x)).approx x_1 = _,
  rw h
end

@[simp]
lemma cases_on_mk {r : M F → Sort*} (x : F.apply $ M F) (f : Π x : F.apply $ M F, r (M.mk x))
: pfunctor.M.cases_on (M.mk x) f = f x :=
cases_mk x f

@[simp]
lemma cases_on_mk' {r : M F → Sort*} {a} (x : F.B a → M F) (f : Π a (f : F.B a → M F), r (M.mk ⟨a,f⟩))
: pfunctor.M.cases_on' (M.mk ⟨a,x⟩) f = f a x :=
cases_mk ⟨_,x⟩ _

inductive is_path  : path F → M F → Prop
| nil (x : M F) : is_path [] x
| cons (xs : path F) {a} (x : M F) (f : F.B a → M F) (i : F.B a) :
  x = M.mk ⟨a,f⟩ →
  is_path xs (f i) →
  is_path (⟨a,i⟩ :: xs) x

lemma is_path_cons {xs : path F} {a a'} {f : F.B a → M F} {i : F.B a'}
  (h : is_path (⟨a',i⟩ :: xs) (M.mk ⟨a,f⟩)) :
  a = a' :=
begin
  revert h, generalize h : (M.mk ⟨a,f⟩) = x,
  intros h', cases h', subst x,
  cases mk_inj h'_a_1, refl,
end

lemma is_path_cons' {xs : path F} {a} {f : F.B a → M F} {i : F.B a}
  (h : is_path (⟨a,i⟩ :: xs) (M.mk ⟨a,f⟩)) :
  is_path xs (f i) :=
begin
  revert h, generalize h : (M.mk ⟨a,f⟩) = x,
  intros h', cases h', subst x,
  cases mk_inj h'_a_1, exact h'_a_2,
end

def isubtree [decidable_eq F.A] [inhabited (M F)] : path F → M F → M F
 | [] x := x
 | (⟨a, i⟩ :: ps) x :=
pfunctor.M.cases_on' x (λ a' f,
(if h : a = a' then isubtree ps (f $ cast (by rw h) i)
 else default (M F) : (λ x, M F) (M.mk ⟨a',f⟩)))

def iselect [decidable_eq F.A] [inhabited (M F)] (ps : path F) : M F → F.A :=
λ (x : M F), head $ isubtree ps x

lemma iselect_eq_default [decidable_eq F.A] [inhabited (M F)] (ps : path F) (x : M F)
  (h : ¬ is_path ps x) :
  iselect ps x = head (default $ M F) :=
begin
  induction ps generalizing x,
  { exfalso, apply h, constructor },
  { cases ps_hd with a i,
    induction x using pfunctor.M.cases_on',
    simp [iselect,isubtree] at ps_ih ⊢,
    by_cases h'' : a = x_a, subst x_a,
    { simp *, rw ps_ih, intro h', apply h,
      constructor; try { refl }, apply h' },
    { simp * } }
end

lemma head_mk (x : F.apply (M F)) :
  head (M.mk x) = x.1 :=
eq.symm $
calc  x.1
    = (from_cofix (M.mk x)).1 : by rw from_cofix_mk
... = head (M.mk x)           : by refl

lemma children_mk {a} (x : F.B a → (M F)) (i : F.B (head (M.mk ⟨a,x⟩)))
: children (M.mk ⟨a,x⟩) i = x (cast (by rw head_mk) i) :=
by apply ext'; intro n; refl

lemma ichildren_mk [decidable_eq F.A] [inhabited (M F)] (x : F.apply (M F)) (i : F.Idx)
: ichildren i (M.mk x) = x.iget i :=
by { dsimp [ichildren,pfunctor.apply.iget],
     congr, ext, apply ext',
     dsimp [children',M.mk,approx.s_mk],
     intros, refl }

lemma isubtree_cons [decidable_eq F.A] [inhabited (M F)] (ps : path F) {a} (f : F.B a → M F) {i : F.B a} :
  isubtree (⟨_,i⟩ :: ps) (M.mk ⟨a,f⟩) = isubtree ps (f i) :=
by simp only [isubtree,ichildren_mk,pfunctor.apply.iget,dif_pos,isubtree,M.cases_on_mk']; refl

lemma iselect_nil [decidable_eq F.A] [inhabited (M F)] {a} (f : F.B a → M F) :
  iselect nil (M.mk ⟨a,f⟩) = a :=
by refl

lemma iselect_cons [decidable_eq F.A] [inhabited (M F)] (ps : path F) {a} (f : F.B a → M F) {i} :
  iselect (⟨a,i⟩ :: ps) (M.mk ⟨a,f⟩) = iselect ps (f i) :=
by simp only [iselect,isubtree_cons]

lemma corec_def {X} (f : X → F.apply X) (x₀ : X) :
  M.corec f x₀ = M.mk (M.corec f <$> f x₀)  :=
begin
  dsimp [M.corec,M.mk],
  congr, ext n,
  cases n with n,
  { dsimp [s_corec,approx.s_mk], refl, },
  { dsimp [s_corec,approx.s_mk], cases h : (f x₀),
    dsimp [s_corec._match_1,(<$>),pfunctor.map],
    congr, }
end

lemma ext_aux [inhabited (M F)] [decidable_eq F.A] {n : ℕ} (x y z : M F)
  (hx : agree' n z x)
  (hy : agree' n z y)
  (hrec : ∀ (ps : path F),
             n = ps.length →
            iselect ps x = iselect ps y)
: x.approx (n+1) = y.approx (n+1) :=
begin
  induction n with n generalizing x y z,
  { specialize hrec [] rfl,
    induction x using pfunctor.M.cases_on', induction y using pfunctor.M.cases_on',
    simp only [iselect_nil] at hrec, subst hrec,
    simp only [approx_mk, true_and, eq_self_iff_true, heq_iff_eq],
    ext, },
  { cases hx, cases hy,
    induction x using pfunctor.M.cases_on', induction y using pfunctor.M.cases_on',
    subst z,
    replace hx_a_2 := mk_inj hx_a_2, cases hx_a_2,
    replace hy_a_1 := mk_inj hy_a_1, cases hy_a_1,
    replace hy_a_2 := mk_inj hy_a_2, cases hy_a_2,
    simp [approx_mk], ext i, apply n_ih,
    { apply hx_a_3 }, { apply hy_a_3 },
    introv h, specialize hrec (⟨_,i⟩ :: ps) (congr_arg _ h),
    simp [iselect_cons] at hrec, exact hrec }
end

open pfunctor.approx

-- variables (F : pfunctor.{v})
variables {F}

local prefix `♯`:0 := cast (by simp [*] <|> cc <|> solve_by_elim)

local attribute [instance, priority 0] classical.prop_decidable

lemma ext [inhabited (M F)] [decidable_eq F.A]
  (x y : M F)
  (H : ∀ (ps : path F), iselect ps x = iselect ps y)
: x = y :=
begin
  apply ext', intro i,
  induction i with i,
  { cases x.approx 0, cases y.approx 0, constructor },
  { apply ext_aux x y x,
    { rw ← agree_iff_agree', apply x.consistent },
    { rw [← agree_iff_agree',i_ih], apply y.consistent },
    introv H',
    simp [iselect] at H,
    cases H',
    apply H ps }
end

section bisim
  variable (R : M F → M F → Prop)
  local infix ~ := R

  structure is_bisimulation :=
  (head : ∀ {a a'} {f f'}, M.mk ⟨a,f⟩ ~ M.mk ⟨a',f'⟩ → a = a')
  (tail : ∀ {a} {f f' : F.B a → M F},
    M.mk ⟨a,f⟩ ~ M.mk ⟨a,f'⟩ →
    (∀ (i : F.B a), f i ~ f' i) )

  variables [inhabited (M F)] [decidable_eq F.A]
  theorem nth_of_bisim (bisim : is_bisimulation R) (s₁ s₂) (ps : path F) :
       s₁ ~ s₂ →
         is_path ps s₁ ∨ is_path ps s₂ →
         iselect ps s₁ = iselect ps s₂ ∧
         ∃ a (f f' : F.B a → M F),
           isubtree ps s₁ = M.mk ⟨a,f⟩ ∧
           isubtree ps s₂ = M.mk ⟨a,f'⟩ ∧
         ∀ (i : F.B a), f i ~ f' i :=
  begin
    intros h₀ hh,
    induction s₁ using pfunctor.M.cases_on' with a f,
      induction s₂ using pfunctor.M.cases_on' with a' f',
      have : a = a' := bisim.head h₀, subst a',
      induction ps with i ps generalizing a f f',
      { existsi [rfl,a,f,f',rfl,rfl],
        apply bisim.tail h₀ },
      cases i with a' i,
      have : a = a',
      { cases hh; cases is_path_cons hh; refl },
      subst a', dsimp [iselect] at ps_ih ⊢,
      have h₁ := bisim.tail h₀ i,
      induction h : (f i) using pfunctor.M.cases_on' with a₀ f₀,
      induction h' : (f' i) using pfunctor.M.cases_on' with a₁ f₁,
      simp only [h,h',isubtree_cons] at ps_ih ⊢,
      rw [h,h'] at h₁,
      have : a₀ = a₁ := bisim.head h₁, subst a₁,
      apply (ps_ih _ _ _ h₁),
      rw [← h,← h'], apply or_of_or_of_imp_of_imp hh is_path_cons' is_path_cons'
  end

  theorem eq_of_bisim (bisim : is_bisimulation R) : ∀ s₁ s₂, s₁ ~ s₂ → s₁ = s₂ :=
  begin
    introv Hr, apply ext,
    introv,
    by_cases h : is_path ps s₁ ∨ is_path ps s₂,
    { have H := nth_of_bisim R bisim _ _ ps Hr h,
      exact H.left },
    { rw not_or_distrib at h, cases h with h₀ h₁,
      simp only [iselect_eq_default,*,not_false_iff] }
  end
end bisim

section coinduction

variables F

coinductive R : Π (s₁ s₂ : M F), Prop
| intro {a} (s₁ s₂ : F.B a → M F) :
   (∀ i, R (s₁ i) (s₂ i)) →
   R (M.mk ⟨_,s₁⟩) (M.mk ⟨_,s₂⟩)

section
variables [decidable_eq F.A] [inhabited $ M F]

open ulift
lemma R_is_bisimulation : is_bisimulation (R F) :=
begin
  constructor; introv hr,
  { suffices : (λ a b, head a = head b) (M.mk ⟨a, f⟩) (M.mk ⟨a', f'⟩),
    { simp only [head_mk] at this, exact this },
    refine R.cases_on _ hr _,
    intros, simp only [head_mk] },
  { suffices : (λ a b, ∀ i j, i == j → R F (children a i) (children b j)) (M.mk ⟨a, f⟩) (M.mk ⟨a, f'⟩),
    { specialize this (cast (by rw head_mk) i) (cast (by rw head_mk) i) heq.rfl,
      simp only [children_mk] at this, exact this, },
    refine R.cases_on _ hr _,
    introv h₂ h₃,
    let k := cast (by rw head_mk) i_1,
    have h₀ : (children (M.mk ⟨a_1, s₁⟩) i_1) = s₁ k := children_mk _ _,
    have h₁ : (children (M.mk ⟨a_1, s₂⟩) j) = s₂ k,
    { rw children_mk, congr, symmetry, apply eq_of_heq h₃ },
    rw [h₀,h₁], apply h₂ },
end

end
variables {F}

lemma coinduction {s₁ s₂ : M F}
  (hh : R _ s₁ s₂)
: s₁ = s₂ :=
begin
  haveI := inhabited.mk s₁,
  exact eq_of_bisim
    (R F) (R_is_bisimulation F) _ _
    hh
end

lemma coinduction' {s₁ s₂ : M F}
  (hh : R _ s₁ s₂)
: s₁ = s₂ :=
begin
  have hh' := hh, revert hh',
  apply R.cases_on F hh, clear hh s₁ s₂,
  introv h₀ h₁,
  rw coinduction h₁
end

end coinduction

universes u' v'

def corec_on {X : Type*} (x₀ : X) (f : X → F.apply X) : M F :=
M.corec f x₀

end M

end pfunctor

namespace tactic.interactive
open tactic (hiding coinduction) lean.parser interactive interactive.types

meta def bisim (ids : parse $ types.with_ident_list) (g : parse $ optional (tk "generalizing" *> many ident)) : tactic unit :=
do applyc ``pfunctor.M.coinduction,
   coinduction ``pfunctor.M.R.corec_on ids g

end tactic.interactive

namespace pfunctor

open M

variables {P : pfunctor.{u}} {α : Type u}

def M_dest : M P → P.apply (M P) := from_cofix

def M_corec : (α → P.apply α) → (α → M P) := M.corec

lemma M_dest_corec (g : α → P.apply α) (x : α) :
  M_dest (M_corec g x) = M_corec g <$> g x :=
by rw [M_corec,M_dest,corec_def,from_cofix_mk]

lemma M_bisim (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f',
      M_dest x = ⟨a, f⟩ ∧
      M_dest y = ⟨a, f'⟩ ∧
      ∀ i, R (f i) (f' i)) :
  ∀ x y, R x y → x = y :=
begin
  intros,
  bisim with x y ih generalizing x y,
  rcases h _ _ ih with ⟨ a', f, f', h₀, h₁, h₂ ⟩, clear h, dsimp [M_dest] at h₀ h₁,
  existsi [a',f,f'], split,
  { intro, existsi [f i,f' i,h₂ _,rfl], refl },
  split,
  { rw [← h₀,mk_from_cofix] },
  { rw [← h₁,mk_from_cofix] },
end

theorem M_bisim' {α : Type*} (Q : α → Prop) (u v : α → M P)
    (h : ∀ x, Q x → ∃ a f f',
      M_dest (u x) = ⟨a, f⟩ ∧
      M_dest (v x) = ⟨a, f'⟩ ∧
      ∀ i, ∃ x', Q x' ∧ f i = u x' ∧ f' i = v x') :
  ∀ x, Q x → u x = v x :=
λ x Qx,
let R := λ w z : M P, ∃ x', Q x' ∧ w = u x' ∧ z = v x' in
@M_bisim P R
  (λ x y ⟨x', Qx', xeq, yeq⟩,
    let ⟨a, f, f', ux'eq, vx'eq, h'⟩ := h x' Qx' in
      ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
  _ _ ⟨x, Qx, rfl, rfl⟩

-- for the record, show M_bisim follows from M_bisim'
theorem M_bisim_equiv (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f',
      M_dest x = ⟨a, f⟩ ∧
      M_dest y = ⟨a, f'⟩ ∧
      ∀ i, R (f i) (f' i)) :
  ∀ x y, R x y → x = y :=
λ x y Rxy,
let Q : M P × M P → Prop := λ p, R p.fst p.snd in
M_bisim' Q prod.fst prod.snd
  (λ p Qp,
    let ⟨a, f, f', hx, hy, h'⟩ := h p.fst p.snd Qp in
    ⟨a, f, f', hx, hy, λ i, ⟨⟨f i, f' i⟩, h' i, rfl, rfl⟩⟩)
  ⟨x, y⟩ Rxy

theorem M_corec_unique (g : α → P.apply α) (f : α → M P)
    (hyp : ∀ x, M_dest (f x) = f <$> (g x)) :
  f = M_corec g :=
begin
  ext x,
  apply M_bisim' (λ x, true) _ _ _ _ trivial,
  clear x,
  intros x _,
  cases gxeq : g x with a f',
  have h₀ : M_dest (f x) = ⟨a, f ∘ f'⟩,
  { rw [hyp, gxeq, pfunctor.map_eq] },
  have h₁ : M_dest (M_corec g x) = ⟨a, M_corec g ∘ f'⟩,
  { rw [M_dest_corec, gxeq, pfunctor.map_eq], },
  refine ⟨_, _, _, h₀, h₁, _⟩,
  intro i,
  exact ⟨f' i, trivial, rfl, rfl⟩
end

def M_mk : P.apply (M P) → M P := M_corec (λ x, M_dest <$> x)

theorem M_mk_M_dest (x : M P) : M_mk (M_dest x) = x :=
begin
  apply M_bisim' (λ x, true) (M_mk ∘ M_dest) _ _ _ trivial,
  clear x,
  intros x _,
  cases Mxeq : M_dest x with a f',
  have : M_dest (M_mk (M_dest x)) = ⟨a, _⟩,
  { rw [M_mk, M_dest_corec, Mxeq, pfunctor.map_eq, pfunctor.map_eq] },
  refine ⟨_, _, _, this, rfl, _⟩,
  intro i,
  exact ⟨f' i, trivial, rfl, rfl⟩
end

theorem M_dest_M_mk (x : P.apply (M P)) : M_dest (M_mk x) = x :=
begin
  have : M_mk ∘ M_dest = id := funext M_mk_M_dest,
  rw [M_mk, M_dest_corec, ←comp_map, ←M_mk, this, id_map, id]
end

def corec₁ {α : Type u} (F : Π X, (α → X) → α → P.apply X) : α → M P :=
M_corec (F _ id)

def M_corec' {α : Type u} (F : Π {X : Type u}, (α → X) → α → M P ⊕ P.apply X) (x : α) : M P :=
corec₁
(λ X rec (a : M P ⊕ α),
     let y := a >>= F (rec ∘ sum.inr) in
     match y with
     | sum.inr y := y
     | sum.inl y := (rec ∘ sum.inl) <$> M_dest y
     end )
(@sum.inr (M P) _ x)

end pfunctor
