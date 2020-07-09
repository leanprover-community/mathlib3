/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Basic machinery for defining general coinductive types

Work in progress
-/
import data.pfun
import data.qpf.indexed.pfunctor.basic
import tactic.wlog meta.coinductive_predicates
import tactic.interactive

universes u v w

open nat function list (hiding head')

variables {I J : Type u} (F : pfunctor.{u} I I)

local prefix `♯`:0 := cast (by simp [*] <|> cc <|> solve_by_elim)

namespace pfunctor
namespace approx

inductive cofix_a : ℕ → I → Type u
| continue {i} : cofix_a 0 i
| intro {n} {i} : ∀ a, (F.B i a ⟶ cofix_a n) → cofix_a (succ n) i

-- #exit
@[ext]
lemma cofix_a_eq_zero : ∀ {i} (x y : cofix_a F 0 i), x = y
| i cofix_a.continue cofix_a.continue := rfl

variables {F}

def head' : Π {i n}, cofix_a F (succ n) i → F.A i
 | _ n (cofix_a.intro i _) := i

def children' : Π {i n} (x : cofix_a F (succ n) i), F.B i (head' x) ⟶ cofix_a F n
 | i n (cofix_a.intro a f) := f

lemma approx_eta {i} {n : ℕ} (x : cofix_a F (n+1) i) :
  x = cofix_a.intro (head' x) (children' x) :=
by cases x; refl

inductive agree
: ∀ {i} {n : ℕ}, cofix_a F n i → cofix_a F (n+1) i → Prop
 | continue {i} (x : cofix_a F 0 i) (y : cofix_a F 1 i) : agree x y
 | intro {i n} {a} (x : F.B i a ⟶ cofix_a F n) (x' : F.B i a ⟶ cofix_a F (n+1)) :
   (∀ j (b : F.B i a j), agree ((x : Π j, F.B i a j → cofix_a F n j) b) (x' b)) →
   agree (cofix_a.intro a x) (cofix_a.intro a x')

def all_agree {i} (x : Π n, cofix_a F n i) :=
∀ n, agree (x n) (x (succ n))

@[simp]
lemma agree_trival {i} {x : cofix_a F 0 i} {y : cofix_a F 1 i} : agree x y :=
by { constructor }

lemma agree_children {i} {n : ℕ} (x : cofix_a F (succ n) i) (y : cofix_a F (succ n+1) i)
  {j a b}
  (h₀ : a == b)
  (h₁ : agree x y)
: agree (@children' I _ _ _ x j a) (children' y b) :=
begin
  cases h₁, cases h₀,
  apply h₁_a_1,
end

def truncate
: ∀ {n : ℕ}, cofix_a F (n+1) ⟶ cofix_a F n
 | 0 _ (cofix_a.intro _ _) := cofix_a.continue
 | (succ n) _ (cofix_a.intro i f) := cofix_a.intro i $ f ≫ truncate

lemma truncate_eq_of_agree {i} {n : ℕ}
  (x : cofix_a F n i)
  (y : cofix_a F (succ n) i)
  (h : agree x y)
: truncate y = x :=
begin
  induction n generalizing i x y
  ; cases x ; cases y,
  { refl },
  { cases h with _ h₀ h₁,
    simp [truncate,exists_imp_distrib,(∘)],
    ext y, apply n_ih _ (h_x' _),
    apply_assumption }
end

variables {X : fam I}
variables (f : X ⟶ F.obj X)

def s_corec : Π n, X ⟶ cofix_a F n
 | 0 _ _ := cofix_a.continue
 | (succ n) _ j :=
   let ⟨y,g⟩ := f j in
   cofix_a.intro y $ g ≫ s_corec _

lemma P_corec {i} (x : X i) (n : ℕ) : agree (s_corec f n x) (s_corec f (succ n) x) :=
begin
  induction n with n generalizing i x,
  constructor,
  cases h : f x with y g,
  simp [s_corec,h,s_corec._match_1] at ⊢ n_ih,
  constructor,
  introv,
  apply n_ih,
end

def path (F : pfunctor.{u} I I) := list $ sigma F.Idx

open list

instance {i} : subsingleton (cofix_a F 0 i) :=
⟨ by { intros, casesm* cofix_a F 0 i, refl } ⟩

open list nat
lemma head_succ' {i} (n m : ℕ) (x : Π n, cofix_a F n i)
  (Hconsistent : all_agree x)
: head' (x (succ n)) = head' (x (succ m)) :=
begin
  suffices : ∀ n, head' (x (succ n)) = head' (x 1),
  { simp [this] },
  clear m n, intro,
  cases h₀ : x (succ n) with _ _ _ i₀ f₀,
  cases h₁ : x 1 with _ i₁ f₁,
  simp [head'],
  induction n with n,
  { rw h₁ at h₀, cases h₀, trivial },
  { have H := Hconsistent (succ n),
    cases h₂ : x (succ n) with _ i₂ f₂,
    rw [h₀,h₂] at H,
    apply n_ih (f₀ ≫ truncate),
    rw h₂,
    cases H,
    congr, funext j k, dsimp [comp],
    rw truncate_eq_of_agree,
    apply H_a_1 }
end

end approx
open approx

structure M_intl (i : I) :=
(approx : ∀ n, cofix_a F n i)
(consistent : all_agree approx)

def M := @M_intl

namespace M

lemma ext' {i} (x y : M F i)
  (H : ∀ i : ℕ, x.approx i = y.approx i)
: x = y :=
begin
  cases x, cases y,
  congr, ext, apply H,
end

variables {X : fam I}
variables (f : X ⟶ F.obj X)
variables {F}

protected def corec : X ⟶ M F :=
λ i x,
{ M_intl . approx := λ n, s_corec f n x
, consistent := λ n, P_corec f x n }

variables {F}

def head : M F ⟶ F.A :=
λ i (x : M F i), head' (x.1 1)

def children : Π {i} (x : M F i), F.B i (head x) ⟶ M F
| j x i y :=
   let H := λ n : ℕ, @head_succ' _ F j n 0 x.1 x.2 in
   { M_intl . approx := λ n, children' (x.1 _) (cast (by simp [head,H]; refl) y)
   , consistent :=
     begin
       intro,
       have P' := x.2 (succ n),
       apply agree_children _ _ _ P',
       transitivity y,
       apply cast_heq,
       symmetry,
       apply cast_heq,
     end }

def ichildren {i} (x : F.Idx i) [inhabited (M F x.idx)] [decidable_eq $ F.A i] : M F i → M F x.idx
 | y :=
if H' : x.1 = head y
  then children y (cast (by simp [head,H']; refl) x.2.2)
  else default _

lemma head_succ {i} (n m : ℕ) (x : M F i)
: head' (x.approx (succ n)) = head' (x.approx (succ m)) :=
head_succ' n m _ x.consistent

lemma head_eq_head' {i} : Π (x : M F i) (n : ℕ),
  head x = head' (x.approx $ n+1)
| ⟨x,h⟩ n := head_succ' _ _ _ h

lemma head'_eq_head {i} : Π (x : M F i) (n : ℕ),
  head' (x.approx $ n+1) = head x
| ⟨x,h⟩ n := head_succ' _ _ _ h

lemma truncate_approx {i} (x : M F i) (n : ℕ) :
  truncate (x.approx $ n+1) = x.approx n :=
truncate_eq_of_agree _ _ (x.consistent _)

def from_cofix : M F ⟶ F.obj (M F) :=
λ i x, (⟨head x,λ i a, children x a ⟩ : F.obj (M F) i)

namespace approx

protected def s_mk {i} (x : F.obj (M F) i) : Π n, cofix_a F n i
 | 0 :=  cofix_a.continue
 | (succ n) := cofix_a.intro x.1 (λ i j, (x.2 j).approx n)

protected def P_mk {i} (x : F.obj (M F) i)
: all_agree (approx.s_mk x)
 | 0 := by { constructor }
 | (succ n) := by { constructor, introv,
                    apply (x.2 _).consistent }

end approx

protected def mk : F.obj (M F) ⟶ M F :=
λ i x,
{ M_intl . approx := approx.s_mk x
, consistent := approx.P_mk x }

inductive agree' : Π {i}, ℕ → M F i → M F i → Prop
| trivial {i} (x y : M F i) : agree' 0 x y
| step {i} {n : ℕ} {a} (x y : F.B i a ⟶ M F) {x' y'} :
  x' = M.mk ⟨a,x⟩ →
  y' = M.mk ⟨a,y⟩ →
  (∀ j (a : F.B i a j), agree' n (x a) (y a)) →
  agree' (succ n) x' y'

@[simp]
lemma from_cofix_mk {i} (x : F.obj (M F) i)
: from_cofix (M.mk x) = x :=
begin
  dsimp [M.mk,from_cofix],
  cases x with x ch, congr, ext i,
  cases h : ch x_1,
  simp [children,M.approx.s_mk,children',cast_eq],
  dsimp [M.approx.s_mk,children'],
  congr, rw h,
end

lemma mk_from_cofix {i} (x : M F i)
: M.mk (from_cofix x) = x :=
begin
  apply ext', intro n,
  dsimp [M.mk],
  induction n with n,
  { dsimp [head], ext },
  dsimp [approx.s_mk,from_cofix,head],
  cases h : x.approx (succ n) with _ _ _ hd ch,
  have h' : hd = head' (x.approx 1),
  { rw [← head_succ' n,h,head'], apply x.consistent },
  revert ch, rw h', intros, congr,
  { ext _ a, dsimp [children],
    h_generalize! hh : a == a'',
    rw h, intros, cases hh, refl },
end

lemma mk_inj {i} {x y : F.obj (M F) i}
  (h : M.mk x = M.mk y) : x = y :=
by rw [← from_cofix_mk x,h,from_cofix_mk]

@[simp]
lemma mk_inj_iff {i} {x y : F.obj (M F) i} :
  M.mk x = M.mk y ↔ x = y :=
⟨mk_inj,congr_arg _⟩

protected def cases {r : Π {i}, M F i → Sort w}
  (f : ∀ {i} (x : F.obj (M F) i), r (M.mk x)) {i} (x : M F i) : r x :=
suffices r (M.mk (from_cofix x)),
  by { haveI := classical.prop_decidable,
       haveI := inhabited.mk x,
       rw [← mk_from_cofix x], exact this },
f _

protected def cases_on {r : Π {i}, M F i → Sort w}
  {i} (x : M F i) (f : ∀ {i} (x : F.obj (M F) i), r (M.mk x)) : r x :=
M.cases @f x

protected def cases_on' {r : Π {i}, M F i → Sort w}
  {i} (x : M F i) (f : ∀ {i} (a : F.A i) f, r (M.mk ⟨a,f⟩)) : r x :=
M.cases_on x (λ i ⟨a,g⟩, f a _)

lemma approx_mk {i} (a : F.A i) (f : F.B i a ⟶ M F) (i : ℕ) :
  (M.mk ⟨a, f⟩).approx (succ i) = cofix_a.intro a (λ j x, (f x).approx i) :=
by refl

lemma agree'_refl {i} {n : ℕ} (x : M F i) :
  agree' n x x :=
by { resetI, induction n generalizing i x; induction x using pfunctor.M.cases_on'; constructor; try { refl }, intros, apply n_ih }

lemma agree_iff_agree' {i} {n : ℕ} (x y : M F i) :
  agree (x.approx n) (y.approx $ n+1) ↔ agree' n x y :=
begin
  split; intros h,
  { induction n generalizing i x y, constructor,
    { induction x using pfunctor.M.cases_on',
      induction y using pfunctor.M.cases_on',
      simp only [approx_mk] at h, cases h,
      constructor; try { refl },
      intros j a, apply n_ih, apply h_a_1 } },
  { induction n generalizing x y i, constructor,
    { cases h,
      induction x using pfunctor.M.cases_on',
      induction y using pfunctor.M.cases_on',
      simp only [approx_mk],
      replace h_a_1 := mk_inj h_a_1, cases h_a_1, clear h_a_1,
      replace h_a_2 := mk_inj h_a_2, cases h_a_2, clear h_a_2 i,
      constructor, intros j a,
      apply n_ih, apply h_a_3 } },
end

@[simp]
lemma cases_mk {r : Π {i}, M F i → Sort*} {i} (x : F.obj (M F) i) (f : Π i (x : F.obj (M F) i), r (M.mk x))
: pfunctor.M.cases f (M.mk x) = f _ x :=
begin
  dsimp [M.mk,pfunctor.M.cases,from_cofix,head,approx.s_mk,head'],
  cases x, dsimp [approx.s_mk],
  apply eq_of_heq,
  apply rec_heq_of_heq, congr,
  ext, dsimp [children,approx.s_mk,children'],
  cases h : x_snd x_1, dsimp [head],
  congr, ext,
  change (x_snd x_1).approx x_2 = _,
  rw h
end

@[simp]
lemma cases_on_mk {r : Π {i}, M F i → Sort*} {i} (x : F.obj (M F) i) (f : Π i (x : F.obj (M F) i), r (M.mk x))
: pfunctor.M.cases_on (M.mk x) f = f _ x :=
cases_mk x f

@[simp]
lemma cases_on_mk' {r : Π {i}, M F i → Sort*} {i a} (x : F.B i a ⟶ M F) (f : Π {i} a (f : F.B i a ⟶ M F), r (M.mk ⟨a,f⟩))
: pfunctor.M.cases_on' (M.mk ⟨a,x⟩) @f = f a x :=
cases_mk ⟨_,x⟩ _

inductive is_path : Π {i}, path F → M F i → Prop
| nil {i} (x : M F i) : is_path [] x
| cons {i} (xs : path F) {a} (x : M F i) (f : F.B i a ⟶ M F) {j} (b : F.B _ a j) :
  x = M.mk ⟨_,f⟩ →
  is_path xs (f b) →
  is_path (⟨_,a,j,b⟩ :: xs) x

lemma is_path_cons {i k} {xs : path F} {a a'} {f : F.B i a ⟶ M F} {j} {x : F.B k a' j}
  (h : is_path (⟨k,a',j,x⟩ :: xs) (M.mk ⟨a,f⟩)) :
  sigma.mk i a = ⟨k,a'⟩ :=
begin
  revert h, generalize h : (M.mk ⟨a,f⟩) = y,
  intros h', cases h', subst y,
  cases mk_inj h'_a_1, refl,
end

lemma is_path_cons' {i} {xs : path F} {a} {f : F.B i a ⟶ M F} {j} {x : F.B i a j}
  (h : is_path (⟨_,a,j,x⟩ :: xs) (M.mk ⟨a,f⟩)) :
  is_path xs (f x) :=
begin
  revert h, generalize h : (M.mk ⟨a,f⟩) = x,
  intros h', cases h', subst x,
  cases mk_inj h'_a_1, exact h'_a_2,
end

-- #print instances inhabited
-- #check @pfunctor.M.cases_on'

-- instance [inhabited I] : inhabited (Idx F (default I)) :=
-- ⟨ ⟨ _, _ ⟩ ⟩

-- def last_idx [inhabited I] (p : path F) : I :=
-- p.ilast

-- def isubtree [decidable_eq I] [∀ i, decidable_eq $ F.A i] [Π i, inhabited (M F i)] : Π {i}, path F → M F i → M F i
--  | i [] x := x
--  | i (⟨j, a, i', y⟩ :: ps) x :=
-- @pfunctor.M.cases_on' _ _ (λ _ _, M F i) _ x (λ k a' f,
-- (if h : sigma.mk j a = sigma.mk k a' then isubtree ps (f i' $ _)
--  else default (M F i)  -- : (λ x, M F) (M.mk ⟨a',f⟩)))

inductive isubtree {j} : Π {i}, path F → M F i → M F j → Prop
| nil (t : M F j) : isubtree [] t t
| cons {i k} (a : F.A i) (t : F.B i a ⟶ M F) (x : F.B i a k) (xs : path F) (t' : M F j) :
  isubtree xs ((t : Π j, F.B i a j → M F j) x) t' →
  isubtree (⟨i,a,_,x⟩ :: xs) (M.mk ⟨a,t⟩) t'

-- #exit
-- def iselect [decidable_eq F.A] [inhabited (M F)] (ps : path F) : M F → F.A :=
-- λ (x : M F), head $ isubtree ps x

def iselect (ps : path F) {i j} (t : M F i) (a : F.A j) : Prop :=
∃ t' : F.B j a ⟶ M F, isubtree ps t (M.mk ⟨a,t'⟩)

-- #exit
lemma head_mk {i} (x : F.obj (M F) i) :
  head (M.mk x) = x.1 :=
eq.symm $
calc  x.1
    = (from_cofix (M.mk x)).1 : by rw from_cofix_mk
... = head (M.mk x)           : by refl

-- #exit
lemma children_mk {i j a} (f : F.B i a ⟶ M F) (x : F.B _ (head (M.mk ⟨a,f⟩)) j)
: children (M.mk ⟨a,f⟩) x = f (cast (by rw head_mk) x) :=
by apply ext'; intro n; refl

-- #exit
-- lemma ichildren_mk [decidable_eq F.A] [inhabited (M F)] (x : F.apply (M F)) (i : F.Idx)
-- : ichildren i (M.mk x) = x.iget i :=
-- by { dsimp [ichildren,pfunctor.apply.iget],
--      congr, ext, apply ext',
--      dsimp [children',M.mk,approx.s_mk],
--      intros, refl }

-- #exit
-- lemma isubtree_cons [decidable_eq F.A] [inhabited (M F)] (ps : path F) {a} (f : F.B a → M F) {i : F.B a} :
--   isubtree (⟨_,i⟩ :: ps) (M.mk ⟨a,f⟩) = isubtree ps (f i) :=
-- by simp only [isubtree,ichildren_mk,pfunctor.apply.iget,dif_pos,isubtree,M.cases_on_mk']; refl

-- #exit
lemma isubtree_nil {i j} (t : M F i) (t' : M F j) :
  isubtree [] t t' ↔ sigma.mk i t = ⟨j,t'⟩ :=
by split; intros h; cases h; constructor

lemma isubtree_cons (ps : path F) {i j k a b} (f : F.B i a ⟶ M F) (t : M F k) :
  isubtree (⟨i,a,j,b⟩ :: ps) (M.mk ⟨a,f⟩) t ↔ isubtree ps (f b) t :=
begin
  split; intro h,
  { generalize_hyp hh : (M.mk ⟨a, f⟩) = t' at h,
    generalize_hyp hh' : (⟨i, ⟨a, ⟨j, b⟩⟩⟩ :: ps : path F) = t'' at h,
    induction h; cases hh',
    cases M.mk_inj hh, assumption },
  { constructor, assumption }
end

lemma eq_of_isubtree_cons {ps : path F} {i i' j k a a' b} {f : F.B i a ⟶ M F} {t : M F k} :
  isubtree (⟨i',a',j,b⟩ :: ps) (M.mk ⟨a,f⟩) t → sigma.mk i' a' = ⟨i,a⟩ :=
begin
  generalize h : (M.mk ⟨a,f⟩) = z,
  intro h', cases h', cases M.mk_inj h, refl
end

lemma iselect_nil' {i a} (f : F.B i a ⟶ M F) :
  iselect nil (M.mk ⟨a,f⟩) a :=
⟨f,isubtree.nil _⟩

lemma iselect_nil {i a j a'} (f : F.B i a ⟶ M F) :
  iselect nil (M.mk ⟨a,f⟩) a' ↔ sigma.mk i a = ⟨j,a'⟩ :=
begin
  simp only [iselect,isubtree_nil] { constructor_eq := ff },
  split; intros h,
  { cases h with t' h, cases congr_arg sigma.fst h, simp only [true_and, heq_iff_eq, mk_inj_iff] at h,
    cases h.2, refl },
  { cases h, refine ⟨_,rfl⟩ }
end

lemma eq_of_iselect_cons {ps : path F} {i i' j k a a' b} {f : F.B i a ⟶ M F} {t : F.A k} :
  iselect (⟨i',a',j,b⟩ :: ps) (M.mk ⟨a,f⟩) t → sigma.mk i' a' = ⟨i,a⟩ :=
λ ⟨f,h⟩, eq_of_isubtree_cons h


-- #exit
lemma iselect_cons (ps : path F) {i j k a b} (f : F.B i a ⟶ M F) (t : F.A k) :
  iselect (⟨i,a,j,b⟩ :: ps) (M.mk ⟨a,f⟩) t ↔ iselect ps (f b) t :=
by simp only [iselect,isubtree_cons]

lemma isubtree_eq_default (ps : path F) {i} (x : M F i) {j} (t : M F j)
  (h : ¬ is_path ps x) :
  ¬ isubtree ps x t :=
begin
  intro h', apply h _, clear h,
  induction ps generalizing i j x t,
  { constructor },
  { rcases ps_hd with ⟨i',a,j,b⟩,
    induction x using pfunctor.M.cases_on',
    classical,
    by_cases h'' : @sigma.mk _ F.A i' a = ⟨x_i,x_a⟩, cases h'',
    { rw [isubtree_cons] at h', -- rw ps_ih, intro h', apply h,
      constructor; try { refl },
      apply ps_ih (x_f b) _ h' },
    { cases eq_of_isubtree_cons h',
      rw [isubtree_cons] at h',
      constructor, refl,
      apply ps_ih _ _ h', } }
end

lemma iselect_eq_default (ps : path F) {i} (x : M F i) {j} (y : F.A j)
  (h : ¬ is_path ps x) :
  ¬ iselect ps x y :=
λ ⟨f,h'⟩, isubtree_eq_default ps _ _ h h'

lemma corec_def {i X} (f : X ⟶ F.obj X) (x₀ : X i) :
  M.corec f x₀ = M.mk (F.map (M.corec f) (f x₀))  :=
begin
  dsimp [M.corec,M.mk],
  congr, ext n,
  cases n with n,
  { dsimp [s_corec,approx.s_mk], refl, },
  { dsimp [s_corec,approx.s_mk], cases h : (f x₀),
    dsimp [s_corec._match_1,(<$>),pfunctor.map],
    congr, }
end

-- #exit
lemma ext_aux {n : ℕ} {i} (x y z : M F i)
  (hx : agree' n z x)
  (hy : agree' n z y)
  (hrec : ∀ (ps : path F) {j} (a : F.A j),
             n = ps.length →
            (iselect ps x a ↔ iselect ps y a))
: x.approx (n+1) = y.approx (n+1) :=
begin
  induction n with n generalizing i x y z,
  { specialize hrec [] (head x) rfl,
    induction x using pfunctor.M.cases_on', induction y using pfunctor.M.cases_on',
    simp only [iselect_nil,head_mk] at hrec { constructor_eq := ff },
    cases hrec.1 rfl,
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
    introv h, specialize hrec (⟨_,y_a,_,x⟩ :: ps) a (congr_arg _ h),
    simp [iselect_cons] at hrec, exact hrec }
end

open pfunctor.approx

-- variables (F : pfunctor.{v})
variables {F}

local prefix `♯`:0 := cast (by simp [*] <|> cc <|> solve_by_elim)

local attribute [instance, priority 0] classical.prop_decidable

-- #exit
lemma ext -- [inhabited (M F)] [decidable_eq F.A]
  {i} (x y : M F i)
  (H : ∀ (ps : path F) {j} (a : F.A j), iselect ps x a ↔ iselect ps y a)
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
  variable (R : Π {i}, M F i → M F i → Prop)
  local infix ~ := R

  structure is_bisimulation :=
  (head : ∀ {i} {a a' : F.A i} {f f'}, M.mk ⟨a,f⟩ ~ M.mk ⟨a',f'⟩ → a = a')
  (tail : ∀ {j a} {f f' : F.B j a ⟶ M F},
    M.mk ⟨a,f⟩ ~ M.mk ⟨a,f'⟩ →
    (∀ {i} (x : F.B j a i), f x ~ f' x) )

  theorem nth_of_bisim (bisim : is_bisimulation @R) {i} (s₁ s₂ : M F i) (ps : path F) :
       s₁ ~ s₂ →
         is_path ps s₁ ∨ is_path ps s₂ →
         -- (∃ a : F.A j, iselect ps s₁ a ∧ iselect ps s₂ a) ∧
         ∃ j a (f f' : F.B j a ⟶ M F),
           isubtree ps s₁ (M.mk ⟨a,f⟩) ∧
           isubtree ps s₂ (M.mk ⟨a,f'⟩) ∧
         ∀ {k} (x : F.B j a k), f x ~ f' x :=
  begin
    intros hh,
    induction s₁ using pfunctor.M.cases_on' with i a f,
    induction s₂ using pfunctor.M.cases_on' with i' a' f',
    have : a = a' := bisim.head hh, subst a',
    induction ps with p ps generalizing i' a f f',
    { intro, existsi [_,a,f,f'], simp [isubtree_nil],
      intros, apply bisim.tail hh, },
    rintro hh',
    rcases p with ⟨aa,b,c,d⟩,
    have : sigma.mk _ a = ⟨aa,b⟩,
    { cases hh'; cases is_path_cons hh'; refl },
    cases this, simp only [isubtree_cons] at ⊢,
    have h₁ := bisim.tail hh d,
    induction h : (f d) using pfunctor.M.cases_on' with i₀ a₀ f₀,
    induction h' : (f' d) using pfunctor.M.cases_on' with i₁ a₁ f₁,
    rw [h,h'] at h₁,
    have : a₀ = a₁ := bisim.head h₁, subst a₁,
    apply (ps_ih _ _ _ h₁),
    rw [← h,← h'], apply or_of_or_of_imp_of_imp hh' is_path_cons' is_path_cons'
  end

  lemma det {i j k} {x : M F i} {s₁ : M F j} {s₂ : M F k} (ps : path F)
    (h : isubtree ps x s₁)
    (h' : isubtree ps x s₂) : sigma.mk j s₁ = ⟨k,s₂⟩ :=
  begin
    induction ps generalizing i x; cases h, cases h', refl,
    erw isubtree_cons at h h', apply @ps_ih _ (h_t h_x) h h',
  end

  lemma det' {i j k} {x : M F i} {s₁ : F.A j} {s₂ : F.A k} (ps : path F)
    (h : iselect ps x s₁)
    (h' : iselect ps x s₂) : sigma.mk j s₁ = ⟨k,s₂⟩ :=
  begin
    cases h with f h,
    cases h' with f' h',
    have := det _ h h', cases congr_arg sigma.fst this,
    simp [-sigma.mk.inj_iff] at this, cases this, refl,
  end

  lemma d {i j} {s₁ s₂ : M F i} (ps : path F)
    (h : ∃ {j} (a : F.A j), iselect ps s₁ a ∧ iselect ps s₂ a) :
    (∀ (a : F.A j), iselect ps s₁ a ↔ iselect ps s₂ a) :=
  begin
    introv, rcases h with ⟨k,b,h,h'⟩,
    by_cases h₁ : sigma.mk j a = ⟨k,b⟩,
    { cases h₁, apply iff_of_true h h' },
    { apply iff_of_false,
      { intro h₂, cases det' ps h h₂,
        apply h₁ rfl },
      { intro h₂, cases det' ps h' h₂,
        apply h₁ rfl }  }
  end

  theorem eq_of_bisim (bisim : is_bisimulation @R) : ∀ {i} {s₁ s₂ : M F i}, s₁ ~ s₂ → s₁ = s₂ :=
  begin
    introv Hr, apply ext,
    intros ps j,
    by_cases h : is_path ps s₁ ∨ is_path ps s₂,
    { have H := nth_of_bisim @R bisim _ _ ps Hr h,
      apply d, rcases H with ⟨k,a,f,f',h₀,h₁,h₂⟩,
      refine ⟨k,a,⟨f,h₀⟩,⟨f',h₁⟩⟩ },
    { rw not_or_distrib at h, cases h with h₀ h₁,
      simp only [iselect_eq_default,*,not_false_iff,false_iff,forall_true_iff], }
  end
end bisim
-- #print eq_of_bisim
section coinduction

variables F

coinductive R : Π i (s₁ s₂ : M F i), Prop
| intro {i a} (s₁ s₂ : F.B i a ⟶ M F) :
   (∀ j (x : F.B i a j), R j ((s₁ : Π {j}, F.B i a j → M F j) x) (s₂ x)) →
   R i (M.mk ⟨_,s₁⟩) (M.mk ⟨_,s₂⟩)

section

open ulift

lemma R_is_bisimulation : is_bisimulation (R F) :=
begin
  constructor; introv hr,
  { suffices : (λ a b, head a = head b) (M.mk ⟨a, f⟩) (M.mk ⟨a', f'⟩),
    { simp only [head_mk] at this, exact this },
    refine R.cases_on _ hr _,
    intros, simp only [head_mk] },
  { revert hr,
    suffices : ∀ k (y z : M F k)
      (hy : sigma.mk k y = ⟨j,M.mk ⟨a, f⟩⟩)
      (hz : sigma.mk k z = ⟨j,M.mk ⟨a, f'⟩⟩)
      (hr : R F k y z), R F i (f x) (f' x),
    { apply this _ _ _ rfl rfl },
    intros, revert hy hz,
    refine R.cases_on _ hr _,
    introv h₂ hy hz,
    cases congr_arg sigma.fst hy, simp only [true_and, heq_iff_eq, mk_inj_iff] at hy,
    cases congr_arg sigma.fst hz, simp only [true_and, heq_iff_eq, mk_inj_iff] at hz,
    cases hy.2, cases hz.2,
    apply h₂ },
end

end
variables {F}

lemma coinduction {i} {s₁ s₂ : M F i}
  (hh : R F i s₁ s₂)
: s₁ = s₂ :=
begin
  exact eq_of_bisim
    (R F) (R_is_bisimulation F)
    hh
end

lemma coinduction' {i} {s₁ s₂ : M F i}
  (hh : R F _ s₁ s₂)
: s₁ = s₂ :=
begin
  have hh' := hh, revert hh',
  apply R.cases_on F hh, clear hh s₁ s₂,
  introv h₀ h₁,
  rw coinduction h₁
end

end coinduction

universes u' v'

def corec_on {X : fam I} {i} (x₀ : X i) (f : X ⟶ F.obj X) : M F i :=
M.corec f x₀

end M

end pfunctor

namespace tactic.interactive
open tactic (hiding coinduction) lean.parser interactive interactive.types

meta def bisim (ns : parse with_ident_list) (g : parse $ optional (tk "generalizing" *> many ident)) : tactic unit :=
do applyc ``pfunctor.M.coinduction,
   coinduction ``pfunctor.M.R.corec_on ns g

end tactic.interactive

namespace pfunctor

open M

variables {P : pfunctor.{u} I I} {α : fam I}

def M_dest : M P ⟶ P.obj (M P) := from_cofix

def M_corec : (α ⟶ P.obj α) → (α ⟶ M P) := M.corec

lemma M_dest_corec (g : α ⟶ P.obj α) {i} (x : α i) :
  M_dest (M_corec g x) = P.map (M_corec g) (g x) :=
by rw [M_corec,M_dest,corec_def,from_cofix_mk]

lemma M_dest_corec' (g : α ⟶ P.obj α) :
  M_corec g ≫ M_dest = g ≫ P.map (M_corec g) :=
funext $ λ i, funext $ λ x, M_dest_corec _ _
section tactic
-- #check @environment.decl_filter_map
open tactic expr
-- run_cmd do
--   d ← get_decl ``tactic.coinduction,
--   env ← get_env,
--   some fn ← pure (env.decl_olean d.to_name),
--   let xs := env.decl_filter_map (λ d,
--     do n ← env.decl_olean d.to_name,
--        guard (n = fn ∧ d.to_name.update_prefix name.anonymous = `compact_relation),
--        pure d.to_name),
--   trace $ xs.take 10,
--   skip

meta def find_private_decl (n : name) (fr : option name) : tactic name :=
do env ← get_env,
   fn ← option_t.run (do
         fr ← option_t.mk (return fr),
         d ← monad_lift $ get_decl fr,
         option_t.mk (return $ env.decl_olean d.to_name) ),
   let p : string → bool :=
     match fn with
     | (some fn) := λ x, fn = x
     | none := λ _, tt
     end,
   let xs := env.decl_filter_map (λ d,
     do fn ← env.decl_olean d.to_name,
        guard ((`_private).is_prefix_of d.to_name ∧ p fn ∧ d.to_name.update_prefix name.anonymous = n),
        pure d.to_name),
   match xs with
   | [n] := pure n
   | [] := fail "no such private found"
   | _ := fail "many matches found"
   end


open lean.parser interactive

@[user_command]
meta def import_private_cmd (_ : parse $ tk "import_private") : lean.parser unit :=
do n  ← ident,
   fr ← optional (tk "from" *> ident),
   n ← find_private_decl n fr,
   c ← resolve_constant n,
   d ← get_decl n,
   let c := @expr.const tt c d.univ_levels,
   new_n ← new_aux_decl_name,
   add_decl $ declaration.defn new_n d.univ_params d.type c reducibility_hints.abbrev d.is_trusted,
   let new_not := sformat!"local notation `{n.update_prefix name.anonymous}` := {new_n}",
   emit_command_here $ new_not,
   skip .

import_private compact_relation from tactic.coinduction


-- meta def mk_sigma : list expr → tactic expr
-- | [] := mk_const ``punit
-- | [x] := pure x
-- | (x :: xs) :=
--   do y ← mk_sigma xs,
--      α ← infer_type x,
--      β ← infer_type y,
--      t ← lambdas [x] β >>= instantiate_mvars,
--      -- trace α, trace β, trace t,
--      trace_expr x, trace_expr y, trace_expr t,
--      r ← mk_mapp ``psigma.mk [α,t] >>= trace_expr,
--      -- r ← mk_mapp ``psigma.mk [α,t,x,y] >>= trace_expr >>= instantiate_mvars,
--      -- r ← mk_const ``psigma.mk,
--      pure $ r x y
--      -- pure r

-- @[tactic.elim_gen_prod]
-- meta def elim_gen_prod' : nat → expr → list expr → list name → tactic (list expr × expr × list name)
-- | 0       e hs ns := return (hs.reverse, e, ns)
-- | (n + 1) e hs ns := do
--   t ← infer_type e,
--   if t.is_app_of `eq then return (hs.reverse, e, ns)
--   else do
--     [(_, [h, h'], _)] ← cases_core e (ns.take 1),
--     trace h,
--     elim_gen_prod' n h' (h :: hs) (ns.drop 1)

meta def rename_using (h : expr) : list name → tactic (expr × list name)
| [] := pure (h,[])
| (new :: ns) :=
  do n ← revert h,
     h' ← intro new,
     intron (n - 1),
     pure (h',ns)

-- @[tactic.coinduction]
-- meta def coinduction'' (rule : expr) (ns : list name) : tactic unit := focus1 $
-- do
--   ctxts' ← intros,
--   ctxts ← ctxts'.mmap (λv,
--     local_const v.local_uniq_name v.local_pp_name v.local_binder_info <$> infer_type v),
--   mvars ← apply_core rule {approx := ff, new_goals := new_goals.all},
--   -- analyse relation
--   g ← list.head <$> get_goals,
--   (list.cons _ m_is) ← return $ mvars.drop_while (λv, v.2 ≠ g),
--   tgt ← target,
--   (is, ty) ← mk_local_pis tgt,
--   -- construct coinduction predicate
--   (bs, eqs) ← compact_relation ctxts <$>
--     ((is.zip m_is).mmap (λ⟨i, m⟩, prod.mk i <$> instantiate_mvars m.2)),
--   solve1 (do
--     eqs ← mk_and_lst <$> eqs.mmap (λ⟨i, m⟩,
--       mk_app `eq [m, i] >>= instantiate_mvars)
--     <|> do { x ← mk_sigma (eqs.map prod.fst),
--              y ← mk_sigma (eqs.map prod.snd),
--              t ← infer_type x,
--              mk_mapp `eq [t,x,y] },
--     rel ← mk_exists_lst bs eqs,
--     exact (rel.lambdas is)),
--   -- prove predicate
--   solve1 (do
--     target >>= instantiate_mvars >>= change, -- TODO: bug in existsi & constructor when mvars in hyptohesis
--     bs.mmap existsi,
--     iterate (econstructor >> skip)),

--   -- clean up remaining coinduction steps
--   all_goals (do
--     ctxts'.reverse.mmap clear,
--     target >>= instantiate_mvars >>= change, -- TODO: bug in subst when mvars in hyptohesis
--     is ← intro_lst $ is.map expr.local_pp_name,
--     h ← intro1,
--     (_, h, ns) ← elim_gen_prod (bs.length - (if eqs.length = 0 then 1 else 0)) h [] ns,
--     (match eqs with
--     | [] := clear h
--     | (e::eqs) := do
--       (hs, h, ns) ← elim_gen_prod eqs.length h [] ns,
--       (h::(hs.reverse) : list _).mfoldl (λ (hs : list name) (h : expr),
--         do [(_,hs',σ)] ← cases_core h hs,
--            clear (h.instantiate_locals σ),
--            pure $ hs.drop hs'.length) ns,
--       skip
--     end))

end tactic

lemma M_bisim (R : Π i, M P i → M P i → Prop)
    (h : ∀ i x y, R i x y → ∃ a f f',
      M_dest x = ⟨a, f⟩ ∧
      M_dest y = ⟨a, f'⟩ ∧
      ∀ j x', R j (f x') (f' x')) :
  ∀ i x y, R i x y → x = y :=
begin
  intros,
  bisim with j _ _ ih generalizing i x y,
  rcases h _ _ _ ih with ⟨ a', f, f', h₀, h₁, h₂ ⟩, clear h,
  existsi [a',f,f'], split,
  { intros, existsi [_,_,_,h₂ _ x], refl },
  split,
  { rw [← h₀,M_dest,mk_from_cofix] },
  { rw [← h₁,M_dest,mk_from_cofix] },
end

theorem M_bisim' {α : fam I} (Q : Π j, α j → Prop) (u v : α ⟶ M P)
    (h : ∀ i x, Q i x → ∃ a f f',
      M_dest (u x) = ⟨a, f⟩ ∧
      M_dest (v x) = ⟨a, f'⟩ ∧
      ∀ j (y : P.B i a j), ∃ (x' : α j), Q j x' ∧ f y = u x' ∧ f' y = v x') :
  ∀ i x, Q i x → u x = v x :=
λ i x Qx,
let R := λ j (w z : M P j), ∃ x', Q j x' ∧ w = u x' ∧ z = v x' in
@M_bisim I P R
  (λ i x y ⟨x', Qx', xeq, yeq⟩,
    let ⟨a, f, f', ux'eq, vx'eq, h'⟩ := h i x' Qx' in
      ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
  _ _ _ ⟨x, Qx, rfl, rfl⟩

-- for the record, show M_bisim follows from M_bisim'
theorem M_bisim_equiv (R : Π i, M P i → M P i → Prop)
    (h : ∀ i x y, R i x y → ∃ a f f',
      M_dest x = ⟨a, f⟩ ∧
      M_dest y = ⟨a, f'⟩ ∧
      ∀ j x', R j (f x') (f' x')) :
  ∀ i x y, R i x y → x = y :=
λ i x y Rxy,
let Q : Π i, M P i × M P i → Prop := λ i p, R i p.fst p.snd in
M_bisim' Q (λ _, prod.fst) (λ _, prod.snd)
  (λ i p Qp,
    let ⟨a, f, f', hx, hy, h'⟩ := h _ p.fst p.snd Qp in
    ⟨a, f, f', hx, hy, λ j y, ⟨⟨f y, f' y⟩, h' _ _, rfl, rfl⟩⟩)
  _ ⟨x, y⟩ Rxy

theorem M_corec_unique (g : α ⟶ P.obj α) (f : α ⟶ M P)
    (hyp : ∀ i x, M_dest (@f i x) = P.map f (g x)) :
  f = M_corec g :=
begin
  ext i x,
  apply M_bisim' (λ i x, true) _ _ _ _ _ trivial,
  clear x,
  intros i x _,
  cases gxeq : g x with a f',
  have h₀ : M_dest (f x) = ⟨a, f' ≫ f⟩,
  { rw [hyp, gxeq, pfunctor.map_eq'] },
  have h₁ : M_dest (M_corec g x) = ⟨a, f' ≫ M_corec g⟩,
  { rw [M_dest_corec, gxeq, pfunctor.map_eq'], },
  refine ⟨_, _, _, h₀, h₁, _⟩,
  intros i y,
  exact ⟨f' y, trivial, rfl, rfl⟩
end

def M_mk : P.obj (M P) ⟶ M P := M_corec (P.map M_dest)

theorem M_mk_M_dest {i} (x : M P i) : M_mk (M_dest x) = x :=
begin
  apply M_bisim' (λ i x, true) (M_dest ≫ M_mk) _ _ _ _ trivial,
  clear x,
  intros j x _,
  cases Mxeq : M_dest x with a f',
  have : M_dest (M_mk (M_dest x)) = ⟨a, _⟩,
  { rw [M_mk, M_dest_corec, Mxeq, pfunctor.map_eq', pfunctor.map_eq'] },
  refine ⟨_, _, _, this, rfl, _⟩,
  intros i y,
  exact ⟨f' y, trivial, rfl, rfl⟩
end

theorem M_mk_M_dest' : M_dest ≫ M_mk = 𝟙 (M P) :=
funext (λ i, funext $ λ i, M_mk_M_dest _)

theorem M_dest_M_mk : M_mk ≫ M_dest = 𝟙 (P.obj (M P)) :=
by rw [M_mk,M_dest_corec',←map_comp, ←M_mk, M_mk_M_dest', map_id]

theorem M_dest_M_mk' {i} (x : P.obj (M P) i) : M_dest (M_mk x) = x :=
show (M_mk ≫ M_dest) x = x,
by rw M_dest_M_mk; refl

-- def corec₁ {α : Type u} (F : Π X, (α → X) → α → P.apply X) : α → M P :=
-- M_corec (F _ id)

-- def M_corec' {α : Type u} (F : Π {X : Type u}, (α → X) → α → M P ⊕ P.apply X) (x : α) : M P :=
-- corec₁
-- (λ X rec (a : M P ⊕ α),
--      let y := a >>= F (rec ∘ sum.inr) in
--      match y with
--      | sum.inr y := y
--      | sum.inl y := (rec ∘ sum.inl) <$> M_dest y
--      end )
-- (@sum.inr (M P) _ x)

end pfunctor
