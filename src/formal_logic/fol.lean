/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- A development of first-order logic in Lean.

* The object theory uses classical logic
* We use de Bruijn variables.
* We use a deep embedding of the logic, i.e. the type of terms and formulas is inductively defined.
* There is no well-formedness predicate; all elements of type "term" are well-formed.
-/

import data.fin formal_logic.to_mathlib

open nat set
universe variables u v

localized "notation h :: t  := dvector.cons h t" in fol
localized "notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`:0) := l" in fol

namespace fol

/- realizers of variables are just maps ℕ → S. We need some operations on them -/

/-- Given a valuation v, a nat n, and an x : S, return v truncated to its first n values, with the rest of the values replaced by x. --/
def subst_realize {S : Type u} (v : ℕ → S) (x : S) (n k : ℕ) : S :=
if k < n then v k else if n < k then v (k - 1) else x

localized "notation v `[`:95 x ` //' `:95 n `]`:0 := fol.subst_realize v x n" in fol

/-- --/
@[simp] lemma subst_realize_lt {S : Type u} (v : ℕ → S) (x : S) {n k : ℕ} (H : k < n) :
  v[x //' n] k = v k :=
by simp only [H, subst_realize, if_true, eq_self_iff_true]

@[simp] lemma subst_realize_gt {S : Type u} (v : ℕ → S) (x : S) {n k : ℕ} (H : n < k) :
  v[x //' n] k = v (k-1) :=
have h : ¬(k < n), from lt_asymm H,
by simp only [*, subst_realize, if_true, eq_self_iff_true, if_false]

@[simp] lemma subst_realize_var_eq {S : Type u} (v : ℕ → S) (x : S) (n : ℕ) : v[x //' n] n = x :=
by simp only [subst_realize, lt_irrefl, eq_self_iff_true, if_false]

lemma subst_realize_congr {S : Type u} {v v' : ℕ → S} (hv : ∀k, v k = v' k) (x : S) (n k : ℕ) :
 v [x //' n] k = v' [x //' n] k :=
by apply decidable.lt_by_cases k n; intro h;
   simp only [*, subst_realize_lt, subst_realize_gt, subst_realize_var_eq, eq_self_iff_true]

lemma subst_realize2 {S : Type u} (v : ℕ → S) (x x' : S) (n₁ n₂ k : ℕ) :
  v [x' //' n₁ + n₂] [x //' n₁] k = v [x //' n₁] [x' //' n₁ + n₂ + 1] k :=
begin
    apply decidable.lt_by_cases k n₁; intro h,
    { have : k < n₁ + n₂, from lt_of_le_of_lt (k.le_add_right n₂) (add_lt_add_right h n₂),
      have : k < n₁ + n₂ + 1, from lt.step this,
      simp only [*, fol.subst_realize_lt, eq_self_iff_true] },
    { have : k < n₂ + (k + 1), from nat.lt_add_left _ _ n₂ (lt.base k),
      subst h, simp [*, add_assoc] },
    apply decidable.lt_by_cases k (n₁ + n₂ + 1); intro h',
    { have : k - 1 < n₁ + n₂, from (nat.sub_lt_right_iff_lt_add (one_le_of_lt h)).2 h',
      simp * },
    { subst h', simp [h] },
    { have : n₁ + n₂ < k - 1, from nat.lt_sub_right_of_add_lt h',
      have : n₁ < k - 1, from lt_of_le_of_lt (n₁.le_add_right n₂) this,
      simp only [*, fol.subst_realize_gt, eq_self_iff_true] }
end

lemma subst_realize2_0 {S : Type u} (v : ℕ → S) (x x' : S) (n k : ℕ) :
  v [x' //' n] [x //' 0] k = v [x //' 0] [x' //' n + 1] k :=
let h := subst_realize2 v x x' 0 n k in by simp only [zero_add] at h; exact h

lemma subst_realize_irrel {S : Type u} {v₁ v₂ : ℕ → S} {n : ℕ} (hv : ∀k < n, v₁ k = v₂ k) (x : S)
  {k : ℕ} (hk : k < n + 1) : v₁[x //' 0] k = v₂[x //' 0] k :=
begin
  cases k, refl, have h : 0 < succ k, from zero_lt_succ k, simp [h, hv k (lt_of_succ_lt_succ hk)]
end

lemma lift_subst_realize_cancel {S : Type u} (v : ℕ → S) (k : ℕ) :
  (λn, v (n + 1))[v 0 //' 0] k = v k :=
begin
  cases k, refl, have h : 0 < succ k, from zero_lt_succ k, simp [h],
end

lemma subst_fin_realize_eq {S : Type u} {n} {v₁ : dvector S n} {v₂ : ℕ → S}
  (hv : ∀k (hk : k < n), v₁.nth k hk = v₂ k) (x : S) (k : ℕ) (hk : k < n+1) :
    (x::v₁).nth k hk = v₂[x //' 0] k :=
begin
  cases k, refl,
  have h : 0 < succ k, from zero_lt_succ k,
  have h' : (0 : fin (n+1)).val < (fin.mk (succ k) hk).val, from h,
  rw [subst_realize_gt v₂ x h, dvector.nth], apply hv
end

structure Language : Type (u+1) :=
(functions : ℕ → Type u) (relations : ℕ → Type u)

def Language.constants (L : Language) := L.functions 0

variable (L : Language.{u})

/- preterm L l is a partially applied term. if applied to n terms, it becomes a term.
* Every element of preterm L 0 is a well-formed term.
* We use this encoding to avoid mutual or nested inductive types, since those are not too convenient to work with in Lean. -/
inductive preterm : ℕ → Type u
| var {} : ∀ (k : ℕ), preterm 0
| func : ∀ {l : ℕ} (f : L.functions l), preterm l
| app : ∀ {l : ℕ} (t : preterm (l + 1)) (s : preterm 0), preterm l
export preterm

@[reducible] def term := preterm L 0

variable {L}
prefix `&`:max := fol.preterm.var

@[simp] def apps : ∀{l}, preterm L l → dvector (term L) l → term L
| _ t []       := t
| _ t (t'::ts) := apps (app t t') ts

-- @[simp] def apps' : ∀{l l'}, preterm L (l'+l) → dvector (term L) l → preterm L l'
-- | _ _ t []       := t
-- | _ _ t (t'::ts) := apps' (app t t') ts

-- @[simp] def rev_apps : ∀{l l'}, preterm L (l+l) → dvector (term L) l' → preterm L l
-- | _ _ t []       := sorry
-- | l _ t (@dvector.cons _ l' t' ts) := app (@rev_apps (l+1) l' t ts) t'

@[simp] lemma apps_zero (t : term L) (ts : dvector (term L) 0) : apps t ts = t :=
by cases ts; refl

lemma apps_eq_app {l} (t : preterm L (l+1)) (s : term L) (ts : dvector (term L) l) :
  ∃t' s', apps t (s::ts) = app t' s' :=
begin
  induction ts generalizing s, exact ⟨t, s, rfl⟩, exact ts_ih (app t s) ts_x
end

namespace preterm
@[simp] def change_arity' : ∀{l l'} (h : l = l') (t : preterm L l), preterm L l'
| _ _ h &k          := by induction h; exact &k
| _ _ h (func f)    := func (by induction h; exact f)
| _ _ h (app t₁ t₂) := app (change_arity' (congr_arg succ h) t₁) t₂

@[simp] lemma change_arity'_rfl : ∀{l} (t : preterm L l), change_arity' rfl t = t
| _ &k          := by refl
| _ (func f)    := by refl
| _ (app t₁ t₂) := by dsimp; simp*

end preterm

-- lemma apps'_concat {l l'} (t : preterm L (l'+(l+1))) (s : term L) (ts : dvector (term L) l) :
--   apps' t (ts.concat s) = app (apps' (t.change_arity' (by simp)) ts) s :=
-- begin
--   induction ts generalizing s,
--   { simp },
--   { apply ts_ih (app t ts_x) s }
-- end

lemma apps_ne_var {l} {f : L.functions l} {ts : dvector (term L) l} {k : ℕ} :
  apps (func f) ts ≠ &k :=
begin
  intro h, cases ts, injection h,
  rcases apps_eq_app (func f) ts_x ts_xs with ⟨t, s, h'⟩, cases h.symm.trans h'
end

lemma apps_inj' {l} {t t' : preterm L l} {ts ts' : dvector (term L) l}
  (h : apps t ts = apps t' ts') : t = t' ∧ ts = ts' :=
begin
  induction ts; cases ts',
  { exact ⟨h, rfl⟩ },
  { rcases ts_ih h with ⟨⟨rfl, rfl⟩, rfl⟩, exact ⟨rfl, rfl⟩ }
end

-- lemma apps_inj_length {l l'} {f : L.functions l} {f' : L.functions l'}
--   {ts : dvector (term L) l} {ts' : dvector (term L) l'}
--   (h : apps (func f) ts = apps (func f') ts') : l = l' :=
-- begin
--   sorry
-- end

-- lemma apps'_inj_length {l₁ l₂ l'} {f : L.functions (l' + l₁)} {f' : L.functions (l' + l₂)}
--   {ts : dvector (term L) l₁} {ts' : dvector (term L) l₂}
--   (h : apps' (func f) ts = apps' (func f') ts') : l₁ = l₂ :=
-- begin
--   sorry
--   -- induction ts generalizing l'; cases ts',
--   -- { refl },
--   -- { rcases apps'_eq_app (func f') ts'_x ts'_xs with ⟨t, s, h'⟩, cases h.trans h' },
--   -- { rcases apps'_eq_app (func f) ts_x ts_xs with ⟨t, s, h'⟩, cases h.symm.trans h' },
--   -- { rcases apps'_eq_app (func f) ts_x ts_xs with ⟨t₁, s₁, h₁⟩,
--   --   rcases apps'_eq_app (func f') ts'_x ts'_xs with ⟨t₂, s₂, h₂⟩,
--   --    }
-- end

lemma apps_inj {l} {f f' : L.functions l} {ts ts' : dvector (term L) l}
  (h : apps (func f) ts = apps (func f') ts') : f = f' ∧ ts = ts' :=
by rcases apps_inj' h with ⟨h', rfl⟩; cases h'; exact ⟨rfl, rfl⟩

def term_of_function {l} (f : L.functions l) : arity' (term L) (term L) l :=
arity'.of_dvector_map $ apps (func f)

@[elab_as_eliminator] def term.rec {C : term L → Sort v}
  (hvar : ∀(k : ℕ), C &k)
  (hfunc : Π {l} (f : L.functions l) (ts : dvector (term L) l) (ih_ts : ∀t, ts.pmem t → C t),
    C (apps (func f) ts)) : ∀(t : term L), C t :=
have h : ∀{l} (t : preterm L l) (ts : dvector (term L) l) (ih_ts : ∀s, ts.pmem s → C s),
  C (apps t ts),
begin
  intros, induction t; try {rw ts.zero_eq},
  { apply hvar },
  { apply hfunc t_f ts ih_ts },
  { apply t_ih_t (t_s::ts), intros t ht,
    cases ht,
    { induction ht, apply t_ih_s ([]), intros s hs, cases hs },
    { exact ih_ts t ht }},
end,
λt, h t ([]) (by intros s hs; cases hs)

@[elab_as_eliminator] def term.elim' {C : Type v}
  (hvar : ∀(k : ℕ), C)
  (hfunc : Π {{l}} (f : L.functions l) (ts : dvector (term L) l) (ih_ts : dvector C l), C) :
  ∀{l} (t : preterm L l) (ts : dvector (term L) l) (ih_ts : dvector C l), C
| _ &k ts ih_ts        := hvar k
| _ (func f) ts ih_ts  := hfunc f ts ih_ts
| _ (app t s) ts ih_ts := term.elim' t (s::ts) (term.elim' s ([]) ([])::ih_ts)

@[elab_as_eliminator] def term.elim {C : Type v}
  (hvar : ∀(k : ℕ), C)
  (hfunc : Π {{l}} (f : L.functions l) (ts : dvector (term L) l) (ih_ts : dvector C l), C) :
  ∀(t : term L), C :=
λt, term.elim' hvar hfunc t ([]) ([])

lemma term.elim'_apps {C : Type v}
  (hvar : ∀(k : ℕ), C)
  (hfunc : Π {{l}} (f : L.functions l) (ts : dvector (term L) l) (ih_ts : dvector C l), C)
  {l} (t : preterm L l) (ts : dvector (term L) l) :
  @term.elim' L C hvar hfunc 0 (apps t ts) ([]) ([]) = @term.elim' L C hvar hfunc l t ts
  (ts.map $ term.elim hvar hfunc) :=
begin
  induction ts,
  { refl },
  { dsimp only [dvector.map, apps], rw [ts_ih], refl }
end

lemma term.elim_apps {C : Type v}
  (hvar : ∀(k : ℕ), C)
  (hfunc : Π {{l}} (f : L.functions l) (ts : dvector (term L) l) (ih_ts : dvector C l), C)
  {l} (f : L.functions l) (ts : dvector (term L) l) :
  @term.elim L C hvar hfunc (apps (func f) ts) = hfunc f ts (ts.map $ @term.elim L C hvar hfunc) :=
by dsimp only [term.elim]; rw term.elim'_apps; refl

/- lift_term_at _ t n m raises variables in t which are at least m by n -/
@[simp] def lift_term_at : ∀ {l}, preterm L l → ℕ → ℕ → preterm L l
| _ &k          n m := &(if m ≤ k then k+n else k)
| _ (func f)    n m := func f
| _ (app t₁ t₂) n m := app (lift_term_at t₁ n m) (lift_term_at t₂ n m)

localized "notation t ` ↑' `:90 n ` # `:90 m:90 := fol.lift_term_at t n m" in fol -- input ↑ with \u or \upa

-- @[simp] lemma lift_term_var_le {k n m} (h : m ≤ k) : &k ↑' n # m = (&(k+n) : term L) := dif_pos h
-- @[simp] lemma lift_term_var_gt {k n m} (h : ¬(m ≤ k)) : &k ↑' n # m = (&k : term L) := dif_neg h
-- @[simp] lemma lift_term_at_func {l} (f : L.functions l) (n m) : func f ↑' n # m = func f := by refl
-- @[simp] lemma lift_term_at_app {l} (t : preterm L (l+1)) (s : preterm L 0) (n m) :
--   app t s ↑' n # m = app (t ↑' n # m) (s ↑' n # m) := by refl

@[reducible] def lift_term {l} (t : preterm L l) (n : ℕ) : preterm L l := t ↑' n # 0
localized "infix ` ↑ `:100 := fol.lift_term" in fol -- input ↑' with \u or \upa
@[reducible, simp] def lift_term1 {l} (t : preterm L l) : preterm L l := t ↑ 1

@[simp] lemma lift_term_def {l} (t : preterm L l) (n : ℕ) : t ↑' n # 0 = t ↑ n := by refl

lemma injective_lift_term_at : ∀ {l} {n m : ℕ},
  function.injective (λ(t : preterm L l), lift_term_at t n m)
| _ n m &k &k' h := by simp at h; split_ifs at h; simp; linarith
| _ n m &k (func f')            h := by cases h
| _ n m &k (app t₁' t₂')        h := by cases h
| _ n m (func f) &k'            h := by cases h
| _ n m (func f) (func f')      h := h
| _ n m (func f) (app t₁' t₂')  h := by cases h
| _ n m (app t₁ t₂) &k'         h := by cases h
| _ n m (app t₁ t₂) (func f')   h := by cases h
| _ n m (app t₁ t₂) (app t₁' t₂') h :=
  begin injection h, congr; apply injective_lift_term_at; assumption end

@[simp] lemma lift_term_at_zero : ∀ {l} (t : preterm L l) (m : ℕ), t ↑' 0 # m = t
| _ &k          m := by simp [lift_term_at]
| _ (func f)    m := by refl
| _ (app t₁ t₂) m := by dsimp; congr; apply lift_term_at_zero

@[simp] lemma lift_term_zero {l} (t : preterm L l) : t ↑ 0 = t := lift_term_at_zero t 0

/- the following lemmas simplify iterated lifts, depending on the size of m' -/
lemma lift_term_at2_small : ∀ {l} (t : preterm L l) (n n') {m m'}, m' ≤ m →
  (t ↑' n # m) ↑' n' # m' = (t ↑' n' # m') ↑' n # (m + n')
| _ &k          n n' m m' H :=
  begin
    by_cases h : m ≤ k,
    { have h₁ : m' ≤ k := le_trans H h,
      have h₂ : m' ≤ k + n, from le_trans h₁ (k.le_add_right n),
      simp [*, add_right_comm] },
    { have h₁ : ¬m + n' ≤ k + n', from λ h', h (le_of_add_le_add_right h'),
      have h₂ : ¬m + n' ≤ k, from λ h', h₁ (le_trans h' (k.le_add_right n')),
      by_cases h' : m' ≤ k; simp * }
  end
| _ (func f)    n n' m m' H := by refl
| _ (app t₁ t₂) n n' m m' H :=
  begin dsimp; congr1; apply lift_term_at2_small; assumption end

lemma lift_term_at2_medium : ∀ {l} (t : preterm L l) {n} (n') {m m'}, m ≤ m' → m' ≤ m+n →
  (t ↑' n # m) ↑' n' # m' = t ↑' (n+n') # m
| _ &k          n n' m m' H₁ H₂ :=
  begin
    by_cases h : m ≤ k,
    { have h₁ : m' ≤ k + n, from le_trans H₂ (add_le_add_right h n), simp [*, add_assoc], },
    { have h₁ : ¬m' ≤ k, from λ h', h (le_trans H₁ h'), simp * }
  end
| _ (func f)    n n' m m' H₁ H₂ := by refl
| _ (app t₁ t₂) n n' m m' H₁ H₂ :=
  begin dsimp; congr1; apply lift_term_at2_medium; assumption end

lemma lift_term2_medium {l} (t : preterm L l) {n} (n') {m'} (h : m' ≤ n) :
  (t ↑ n) ↑' n' # m' = t ↑ (n+n') :=
lift_term_at2_medium t n' m'.zero_le (by simp*)

lemma lift_term2 {l} (t : preterm L l) (n n') : (t ↑ n) ↑ n' = t ↑ (n+n') :=
lift_term2_medium t n' n.zero_le

lemma lift_term_at2_eq {l} (t : preterm L l) (n n' m : ℕ) :
  (t ↑' n # m) ↑' n' # (m+n) = t ↑' (n+n') # m :=
lift_term_at2_medium t n' (m.le_add_right n) (le_refl _)

lemma lift_term_at2_large {l} (t : preterm L l) {n} (n') {m m'} (H : m + n ≤ m') :
  (t ↑' n # m) ↑' n' # m' = (t ↑' n' # (m'-n)) ↑' n # m :=
have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
have H₂ : m ≤ m' - n, from nat.le_sub_right_of_add_le H,
begin rw fol.lift_term_at2_small t n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

@[simp] lemma lift_term_var0 (n : ℕ) : &0 ↑ n = (&n : term L) :=
by have h : 0 ≤ 0 := le_refl 0; rw [←lift_term_def]; simp [h, -lift_term_def]

@[simp] lemma lift_term_at_apps {l} (t : preterm L l) (ts : dvector (term L) l) (n m : ℕ) :
  (apps t ts) ↑' n # m = apps (t ↑' n # m) (ts.map $ λx, x ↑' n # m) :=
by induction ts generalizing t;[refl, apply ts_ih (app t ts_x)]

@[simp] lemma lift_term_apps {l} (t : preterm L l) (ts : dvector (term L) l) (n : ℕ) :
  (apps t ts) ↑ n = apps (t ↑ n) (ts.map $ λx, x ↑ n) :=
lift_term_at_apps t ts n 0

/- subst_term t s n substitutes s for (&n) and reduces the level of all variables above n by 1 -/
def subst_term : ∀ {l}, preterm L l → term L → ℕ → preterm L l
| _ &k          s n := subst_realize var (s ↑ n) n k
| _ (func f)    s n := func f
| _ (app t₁ t₂) s n := app (subst_term t₁ s n) (subst_term t₂ s n)

localized "notation t `[`:max s ` // `:95 n `]`:0 := fol.subst_term t s n" in fol

@[simp] lemma subst_term_var_lt (s : term L) {k n : ℕ} (H : k < n) : &k[s // n] = &k :=
by simp only [H, fol.subst_term, fol.subst_realize_lt, eq_self_iff_true]

@[simp] lemma subst_term_var_gt (s : term L) {k n : ℕ} (H : n < k) : &k[s // n] = &(k-1) :=
by simp only [H, fol.subst_term, fol.subst_realize_gt, eq_self_iff_true]

@[simp] lemma subst_term_var_eq (s : term L) (n : ℕ) : &n[s // n] = s ↑' n # 0 :=
by simp [subst_term]

lemma subst_term_var0 (s : term L) : &0[s // 0] = s := by simp

@[simp] lemma subst_term_func {l} (f : L.functions l) (s : term L) (n : ℕ) :
  (func f)[s // n] = func f :=
by refl

@[simp] lemma subst_term_app {l} (t₁ : preterm L (l+1)) (t₂ s : term L) (n : ℕ) :
  (app t₁ t₂)[s // n] = app (t₁[s // n]) (t₂[s // n]) :=
by refl

@[simp] lemma subst_term_apps {l} (t : preterm L l) (ts : dvector (term L) l) (s : term L)
  (n : ℕ) : (apps t ts)[s // n] = apps (t[s // n]) (ts.map $ λx, x[s // n]) :=
by induction ts generalizing t;[refl, apply ts_ih (app t ts_x)]

/- the following lemmas simplify first lifting and then substituting, depending on the size
  of the substituted variable -/
lemma lift_at_subst_term_large : ∀{l} (t : preterm L l) (s : term L) {n₁} (n₂) {m}, m ≤ n₁ →
 (t ↑' n₂ # m)[s // n₁+n₂] = (t [s // n₁]) ↑' n₂ # m
| _ &k          s n₁ n₂ m h :=
  begin
    apply decidable.lt_by_cases k n₁; intro h₂,
    { have : k < n₁ + n₂, from lt_of_le_of_lt (k.le_add_right n₂) (by simp*),
      by_cases m ≤ k; simp* },
    { subst h₂, simp [*, lift_term2_medium] },
    { have h₂ : m < k, by apply lt_of_le_of_lt; assumption,
      have : m ≤ k - 1, from nat.le_sub_right_of_add_le (succ_le_of_lt h₂),
      have : m ≤ k, from le_of_lt h₂,
      have : 1 ≤ k, from one_le_of_lt h₂,
      simp [*, nat.add_sub_swap this n₂, -add_assoc] }
  end
| _ (func f)    s n₁ n₂ m h := rfl
| _ (app t₁ t₂) s n₁ n₂ m h := by simp*

lemma lift_subst_term_large {l} (t : preterm L l) (s : term L) (n₁ n₂) :
  (t ↑ n₂)[s // n₁+n₂] = (t [s // n₁]) ↑ n₂ :=
lift_at_subst_term_large t s n₂ n₁.zero_le

lemma lift_subst_term_large' {l} (t : preterm L l) (s : term L) (n₁ n₂) :
  (t ↑ n₂)[s // n₂+n₁] = (t [s // n₁]) ↑ n₂ :=
by rw [add_comm]; apply lift_subst_term_large

lemma lift_at_subst_term_medium : ∀{l} (t : preterm L l) (s : term L) {n₁ n₂ m}, m ≤ n₂ →
  n₂ ≤ m + n₁ → (t ↑' n₁+1 # m)[s // n₂] = t ↑' n₁ # m
| _ &k          s n₁ n₂ m h₁ h₂ :=
  begin
    by_cases h : m ≤ k,
    { have h₃ : n₂ < k + (n₁ + 1), from lt_succ_of_le (le_trans h₂ (add_le_add_right h _)),
      simp [*, add_sub_cancel_right] },
    { have h₃ : k < n₂, from lt_of_lt_of_le (lt_of_not_ge h) h₁, simp* }
  end
| _ (func f)    s n₁ n₂ m h₁ h₂ := rfl
| _ (app t₁ t₂) s n₁ n₂ m h₁ h₂ := by simp*

lemma lift_subst_term_medium {l} (t : preterm L l) (s : term L) (n₁ n₂) :
  (t ↑ ((n₁ + n₂) + 1))[s // n₁] = t ↑ (n₁ + n₂) :=
lift_at_subst_term_medium t s n₁.zero_le (by rw [zero_add]; exact n₁.le_add_right n₂)

lemma lift_at_subst_term_eq {l} (t : preterm L l) (s : term L) (n : ℕ) : (t ↑' 1 # n)[s // n] = t :=
begin rw [lift_at_subst_term_medium t s, lift_term_at_zero]; refl end

@[simp] lemma lift_term1_subst_term {l} (t : preterm L l) (s : term L) : (t ↑ 1)[s // 0] = t :=
lift_at_subst_term_eq t s 0

lemma lift_at_subst_term_small : ∀{l} (t : preterm L l) (s : term L) (n₁ n₂ m),
 (t ↑' n₁ # (m + n₂ + 1))[s ↑' n₁ # m // n₂] = (t [s // n₂]) ↑' n₁ # (m + n₂)
| _ &k          s n₁ n₂ m :=
  begin
    by_cases h : m + n₂ + 1 ≤ k,
    { change m + n₂ + 1 ≤ k at h,
      have h₂ : n₂ < k := lt_of_le_of_lt (le_add_left n₂ m) (lt_of_succ_le h),
      have h₃ : n₂ < k + n₁ := by apply nat.lt_add_right; exact h₂,
      have h₄ : m + n₂ ≤ k - 1 := nat.le_sub_right_of_add_le h,
      simp [*, nat.add_sub_swap (one_le_of_lt h₂)] },
    { change ¬(m + n₂ + 1 ≤ k) at h,
      apply decidable.lt_by_cases k n₂; intro h₂,
      { have h₃ : ¬(m + n₂ ≤ k) := λh', not_le_of_gt h₂ (le_trans (le_add_left n₂ m) h'),
        simp [h, h₂, h₃] },
      { subst h₂,
        have h₃ : ¬(k + m + 1 ≤ k) := by rw [add_comm k m]; exact h,
        simp [h, h₃],
        exact lift_term_at2_small _ _ _ m.zero_le },
      { have h₃ : ¬(m + n₂ ≤ k - 1) :=
          λh', h $ (nat.le_sub_right_iff_add_le $ one_le_of_lt h₂).mp h',
        simp [h, h₂, h₃] }}
  end
| _ (func f)    s n₁ n₂ m := rfl
| _ (app t₁ t₂) s n₁ n₂ m := by simp [*, -add_assoc]

lemma subst_term2 : ∀{l} (t : preterm L l) (s₁ s₂ : term L) (n₁ n₂),
  t [s₁ // n₁] [s₂ // n₁ + n₂] = t [s₂ // n₁ + n₂ + 1] [s₁[s₂ // n₂] // n₁]
| _ &k          s₁ s₂ n₁ n₂ :=
  begin -- can we use subst_realize2 here?
    apply decidable.lt_by_cases k n₁; intro h,
    { have : k < n₁ + n₂, from lt_of_le_of_lt (k.le_add_right n₂) (by simp*),
      have : k < n₁ + n₂ + 1, from lt.step this,
      simp only [*, eq_self_iff_true, fol.subst_term_var_lt] },
    { have : k < k + (n₂ + 1), from lt_succ_of_le (le_add_right _ n₂),
      subst h, simp [*, add_assoc, lift_subst_term_large'] },
    apply decidable.lt_by_cases k (n₁ + n₂ + 1); intro h',
    { have : k - 1 < n₁ + n₂, from (nat.sub_lt_right_iff_lt_add (one_le_of_lt h)).2 h',
      simp * },
    { subst h', simp [h, lift_subst_term_medium] },
    { have : n₁ + n₂ < k - 1, from nat.lt_sub_right_of_add_lt h',
      have : n₁ < k - 1, from lt_of_le_of_lt (n₁.le_add_right n₂) this,
      simp only [*, eq_self_iff_true, fol.subst_term_var_gt] }
  end
| _ (func f)    s₁ s₂ n₁ n₂ := rfl
| _ (app t₁ t₂) s₁ s₂ n₁ n₂ := by simp*

lemma subst_term2_0 {l} (t : preterm L l) (s₁ s₂ : term L) (n) :
  t [s₁ // 0] [s₂ // n] = t [s₂ // n + 1] [s₁[s₂ // n] // 0] :=
let h := subst_term2 t s₁ s₂ 0 n in by simp only [zero_add] at h; exact h

lemma lift_subst_term_cancel : ∀{l} (t : preterm L l) (n : ℕ), (t ↑' 1 # (n+1))[&0 // n] = t
| _ &k          n :=
  begin
    apply decidable.lt_by_cases n k; intro h,
    { change n+1 ≤ k at h, have h' : n < k+1, from lt.step (lt_of_succ_le h), simp [h, h'] },
    { have h' : ¬(k+1 ≤ k), from not_succ_le_self k, simp [h, h'] },
    { have h' : ¬(n+1 ≤ k) := not_le_of_lt (lt.step h), simp [h, h'] }
  end
| _ (func f)    n := rfl
| _ (app t₁ t₂) n := by dsimp; simp *


/- Probably useful facts about substitution which we should add when needed:
(forall M N i j k, ( M [ j ← N] ) ↑' k # (j+i) = (M ↑' k # (S (j+i))) [ j ← (N ↑' k # i ) ])
subst_travers : (forall M N P n, (M [← N]) [n ← P] = (M [n+1 ← P])[← N[n← P]])
erasure_lem3 : (forall n m t, m>n->#m = (#m ↑' 1 # (S n)) [n ← t]).
lift_is_lift_sublemma : forall j v, j<v->exists w,#v=w↑1#j.
lift_is_lift : (forall N A n i j,N ↑' i # n=A ↑' 1 # j -> j<n -> exists M,N=M ↑' 1 # j)
subst_is_lift : (forall N T A n j, N [n ← T]=A↑' 1#j->j<n->exists M,N=M↑' 1#j)
-/

/- preformula l is a partially applied formula. if applied to n terms, it becomes a formula.
  * We only have implication as binary connective. Since we use classical logic, we can define
    the other connectives from implication and falsum.
  * Similarly, universal quantification is our only quantifier.
  * We could make `falsum` and `equal` into elements of rel. However, if we do that, then we cannot make the interpretation of them in a model definitionally what we want.
-/
variable (L)
inductive preformula : ℕ → Type u
| falsum {} : preformula 0
| equal (t₁ t₂ : term L) : preformula 0
| rel {l : ℕ} (R : L.relations l) : preformula l
| apprel {l : ℕ} (f : preformula (l + 1)) (t : term L) : preformula l
| imp (f₁ f₂ : preformula 0) : preformula 0
| all (f : preformula 0) : preformula 0
export preformula
@[reducible] def formula := preformula L 0
variable {L}

localized "notation `⊥` := fol.preformula.falsum" in fol -- input: \bot
localized "infix ` ≃ `:88 := fol.preformula.equal" in fol -- input \~- or \simeq
localized "infixr ` ⟹ `:62 := fol.preformula.imp" in fol -- input \==>
prefix `∀'`:110 := fol.preformula.all
def not   (f : formula L)     : formula L := f ⟹ ⊥
prefix `∼`:max := fol.not -- input \~, the ASCII character ~ has too low precedence
localized "notation `⊤` := ∼⊥" in fol -- input: \top
def and   (f₁ f₂ : formula L) : formula L := ∼(f₁ ⟹ ∼f₂)
localized "infixr ` ⊓ ` := fol.and" in fol -- input: \sqcap
def or    (f₁ f₂ : formula L) : formula L := ∼f₁ ⟹ f₂
localized "infixr ` ⊔ ` := fol.or" in fol -- input: \sqcup
def biimp (f₁ f₂ : formula L) : formula L := (f₁ ⟹ f₂) ⊓ (f₂ ⟹ f₁)
localized "infix ` ⇔ `:61 := fol.biimp" in fol -- input \<=>
def ex    (f : formula L)     : formula L := ∼ ∀' ∼f
prefix `∃'`:110 := fol.ex -- input \ex

@[simp] def apps_rel : ∀{l} (f : preformula L l) (ts : dvector (term L) l), formula L
| 0     f []      := f
| (n+1) f (t::ts) := apps_rel (apprel f t) ts

@[simp] lemma apps_rel_zero (f : formula L) (ts : dvector (term L) 0) : apps_rel f ts = f :=
by cases ts; refl

-- lemma apps_rel_ne_falsum {l} {R : L.relations l} {ts : dvector (term L) l} :
--   apps_rel (rel R) ts ≠ ⊥ :=
-- by induction l; cases ts; [{cases ts_xs, intro h, injection h}, apply l_ih]

-- lemma apps_rel_ne_falsum {l} {f : preformula L (l+1)} {ts : dvector (term L) (l+1)} :
--   apps_rel f ts ≠ ⊥ :=
-- by induction l; cases ts; [{cases ts_xs, intro h, injection h}, apply l_ih]
-- lemma apps_rel_ne_equal {l} {f : preformula L (l+1)} {ts : dvector (term L) (l+1)}
--   {t₁ t₂ : term L} : apps_rel f ts ≠ t₁ ≃ t₂ :=
-- by induction l; cases ts; [{cases ts_xs, intro h, injection h}, apply l_ih]
-- lemma apps_rel_ne_imp {l} {f : preformula L (l+1)} {ts : dvector (term L) (l+1)}
--   {f₁ f₂ : formula L} : apps_rel f ts ≠ f₁ ⟹ f₂ :=
-- by induction l; cases ts; [{cases ts_xs, intro h, injection h}, apply l_ih]
-- lemma apps_rel_ne_all {l} {f : preformula L (l+1)} {ts : dvector (term L) (l+1)}
--   {f' : formula L} : apps_rel f ts ≠ ∀' f' :=
-- by induction l; cases ts; [{cases ts_xs, intro h, injection h}, apply l_ih]

def formula_of_relation {l} (R : L.relations l) : arity' (term L) (formula L) l :=
arity'.of_dvector_map $ apps_rel (rel R)

@[elab_as_eliminator] def formula.rec' {C : formula L → Sort v}
  (hfalsum : C ⊥)
  (hequal : Π (t₁ t₂ : term L), C (t₁ ≃ t₂))
  (hrel : Π {{l}} (R : L.relations l) (ts : dvector (term L) l), C (apps_rel (rel R) ts))
  (himp : Π {{f₁ f₂ : formula L}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
  (hall : Π {{f : formula L}} (ih : C f), C (∀' f)) :
  ∀{l} (f : preformula L l) (ts : dvector (term L) l), C (apps_rel f ts)
| _ falsum       ts := by cases ts; exact hfalsum
| _ (t₁ ≃ t₂)    ts := by cases ts; apply hequal
| _ (rel R)      ts := by apply hrel
| _ (apprel f t) ts := by apply formula.rec' f (t::ts)
| _ (f₁ ⟹ f₂)   ts := by cases ts; exact himp (formula.rec' f₁ ([])) (formula.rec' f₂ ([]))
| _ (∀' f)       ts := by cases ts; exact hall (formula.rec' f ([]))

@[elab_as_eliminator] def formula.rec {C : formula L → Sort v}
  (hfalsum : C ⊥)
  (hequal : Π (t₁ t₂ : term L), C (t₁ ≃ t₂))
  (hrel : Π {{l}} (R : L.relations l) (ts : dvector (term L) l), C (apps_rel (rel R) ts))
  (himp : Π {{f₁ f₂ : formula L}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
  (hall : Π {{f : formula L}} (ih : C f), C (∀' f)) : ∀f, C f :=
λf, formula.rec' hfalsum hequal hrel himp hall f ([])

@[simp] def formula.rec'_apps_rel {C : formula L → Sort v}
  (hfalsum : C ⊥)
  (hequal : Π (t₁ t₂ : term L), C (t₁ ≃ t₂))
  (hrel : Π {{l}} (R : L.relations l) (ts : dvector (term L) l), C (apps_rel (rel R) ts))
  (himp : Π {{f₁ f₂ : formula L}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
  (hall : Π {{f : formula L}} (ih : C f), C (∀' f))
  {l} (f : preformula L l) (ts : dvector (term L) l) :
  @formula.rec' L C hfalsum hequal hrel himp hall 0 (apps_rel f ts) ([]) =
  @formula.rec' L C hfalsum hequal hrel himp hall l f ts :=
begin
  induction ts,
  { refl },
  { dsimp only [dvector.map, apps_rel], rw [ts_ih], refl }
end

@[simp] def formula.rec_apps_rel {C : formula L → Sort v}
  (hfalsum : C ⊥)
  (hequal : Π (t₁ t₂ : term L), C (t₁ ≃ t₂))
  (hrel : Π {{l}} (R : L.relations l) (ts : dvector (term L) l), C (apps_rel (rel R) ts))
  (himp : Π {{f₁ f₂ : formula L}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
  (hall : Π {{f : formula L}} (ih : C f), C (∀' f))
  {l} (R : L.relations l) (ts : dvector (term L) l) :
  @formula.rec L C hfalsum hequal hrel himp hall (apps_rel (rel R) ts) = hrel R ts :=
by dsimp only [formula.rec]; rw formula.rec'_apps_rel; refl

@[simp] def lift_formula_at : ∀ {l}, preformula L l → ℕ → ℕ → preformula L l
| _ falsum       n m := falsum
| _ (t₁ ≃ t₂)    n m := lift_term_at t₁ n m ≃ lift_term_at t₂ n m
| _ (rel R)      n m := rel R
| _ (apprel f t) n m := apprel (lift_formula_at f n m) (lift_term_at t n m)
| _ (f₁ ⟹ f₂)   n m := lift_formula_at f₁ n m ⟹ lift_formula_at f₂ n m
| _ (∀' f)       n m := ∀' lift_formula_at f n (m+1)

localized "notation f ` ↑↑' `:90 n ` # `:90 m:90 := fol.lift_formula_at f n m" in fol -- input ↑' with \upa

@[reducible] def lift_formula {l} (f : preformula L l) (n : ℕ) : preformula L l := f ↑↑' n # 0
localized "infix ` ↑↑ `:100 := fol.lift_formula" in fol -- input ↑↑' with \upa
@[reducible, simp] def lift_formula1 {l} (f : preformula L l) : preformula L l := f ↑↑ 1

@[simp] lemma lift_formula_def {l} (f : preformula L l) (n : ℕ) : f ↑↑' n # 0 = f ↑↑ n := by refl
@[simp] lemma lift_formula1_not (n : ℕ) (f : formula L) : ∼f ↑↑ n  = ∼(f ↑↑ n) := by refl

lemma injective_lift_formula_at {l} {n m : ℕ} :
  function.injective (λ (f : preformula L l), lift_formula_at f n m) :=
begin
  intros f f' H, induction f generalizing m; cases f'; injection H,
  { simp only [injective_lift_term_at h_1, injective_lift_term_at h_2, eq_self_iff_true, and_self] },
  { simp only [f_ih h_1, injective_lift_term_at h_2, eq_self_iff_true, and_self] },
  { simp only [f_ih_f₁ h_1, f_ih_f₂ h_2, eq_self_iff_true, and_self] },
  { simp only [f_ih h_1, eq_self_iff_true] }
end

@[simp] lemma lift_formula_at_zero : ∀ {l} (f : preformula L l) (m : ℕ), f ↑↑' 0 # m = f
| _ falsum       m := by refl
| _ (t₁ ≃ t₂)    m := by simp
| _ (rel R)      m := by refl
| _ (apprel f t) m := by simp; apply lift_formula_at_zero
| _ (f₁ ⟹ f₂)   m := by dsimp; congr1; apply lift_formula_at_zero
| _ (∀' f)       m := by simp; apply lift_formula_at_zero

/- the following lemmas simplify iterated lifts, depending on the size of m' -/
lemma lift_formula_at2_small : ∀ {l} (f : preformula L l) (n n') {m m'}, m' ≤ m →
  (f ↑↑' n # m) ↑↑' n' # m' = (f ↑↑' n' # m') ↑↑' n # (m + n')
| _ falsum       n n' m m' H := by refl
| _ (t₁ ≃ t₂)    n n' m m' H := by simp [lift_term_at2_small, H]
| _ (rel R)      n n' m m' H := by refl
| _ (apprel f t) n n' m m' H :=
  by simp [lift_term_at2_small, H]; apply lift_formula_at2_small; assumption
| _ (f₁ ⟹ f₂)   n n' m m' H := by dsimp; congr1; apply lift_formula_at2_small; assumption
| _ (∀' f)       n n' m m' H := by simp [lift_term_at2_small, H, add_right_comm,
    lift_formula_at2_small f n n' (add_le_add_right H 1)]

lemma lift_formula_at2_medium : ∀ {l} (f : preformula L l) (n n') {m m'}, m ≤ m' → m' ≤ m+n →
  (f ↑↑' n # m) ↑↑' n' # m' = f ↑↑' (n+n') # m
| _ falsum       n n' m m' H₁ H₂ := by refl
| _ (t₁ ≃ t₂)    n n' m m' H₁ H₂ := by simp [*, lift_term_at2_medium]
| _ (rel R)      n n' m m' H₁ H₂ := by refl
| _ (apprel f t) n n' m m' H₁ H₂ := by simp [*, lift_term_at2_medium]
| _ (f₁ ⟹ f₂)   n n' m m' H₁ H₂ := by simp*
| _ (∀' f)       n n' m m' H₁ H₂ :=
  have m' + 1 ≤ (m + 1) + n, from
    le_trans (add_le_add_right H₂ 1) (by simp [add_right_comm]),
  by simp *

lemma lift_formula_at2_eq {l} (f : preformula L l) (n n' m : ℕ) :
  (f ↑↑' n # m) ↑↑' n' # (m+n) = f ↑↑' (n+n') # m :=
lift_formula_at2_medium f n n' (m.le_add_right n) (le_refl _)

lemma lift_formula_at2_large {l} (f : preformula L l) (n n') {m m'} (H : m + n ≤ m') :
  (f ↑↑' n # m) ↑↑' n' # m' = (f ↑↑' n' # (m'-n)) ↑↑' n # m :=
have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
have H₂ : m ≤ m' - n, from nat.le_sub_right_of_add_le H,
begin rw lift_formula_at2_small f n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

@[simp] lemma lift_formula_at_apps_rel {l} (f : preformula L l) (ts : dvector (term L) l)
  (n m : ℕ) : (apps_rel f ts) ↑↑' n # m = apps_rel (f ↑↑' n # m) (ts.map $ λx, x ↑' n # m) :=
by induction ts generalizing f;[refl, apply ts_ih (apprel f ts_x)]

@[simp] lemma lift_formula_apps_rel {l} (f : preformula L l) (ts : dvector (term L) l)
  (n : ℕ) : (apps_rel f ts) ↑↑ n = apps_rel (f ↑↑ n) (ts.map $ λx, x ↑ n) :=
lift_formula_at_apps_rel f ts n 0

@[simp] def subst_formula : ∀ {l}, preformula L l → term L → ℕ → preformula L l
| _ falsum       s n := falsum
| _ (t₁ ≃ t₂)    s n := subst_term t₁ s n ≃ subst_term t₂ s n
| _ (rel R)      s n := rel R
| _ (apprel f t) s n := apprel (subst_formula f s n) (subst_term t s n)
| _ (f₁ ⟹ f₂)   s n := subst_formula f₁ s n ⟹ subst_formula f₂ s n
| _ (∀' f)       s n := ∀' subst_formula f s (n+1)

localized "notation f `[`:95 s ` /// `:95 n `]`:0 := fol.subst_formula f s n" in fol

lemma subst_formula_equal (t₁ t₂ s : term L) (n : ℕ) :
  (t₁ ≃ t₂)[s /// n] = t₁[s // n] ≃ (t₂[s // n]) :=
by refl

@[simp] lemma subst_formula_biimp (f₁ f₂ : formula L) (s : term L) (n : ℕ) :
  (f₁ ⇔ f₂)[s /// n] = f₁[s /// n] ⇔ (f₂[s /// n]) :=
by refl

lemma lift_at_subst_formula_large : ∀{l} (f : preformula L l) (s : term L) {n₁} (n₂) {m}, m ≤ n₁ →
  (f ↑↑' n₂ # m)[s /// n₁+n₂] = (f [s /// n₁]) ↑↑' n₂ # m
| _ falsum       s n₁ n₂ m h := by refl
| _ (t₁ ≃ t₂)    s n₁ n₂ m h := by simp [*, lift_at_subst_term_large]
| _ (rel R)      s n₁ n₂ m h := by refl
| _ (apprel f t) s n₁ n₂ m h := by simp [*, lift_at_subst_term_large]
| _ (f₁ ⟹ f₂)   s n₁ n₂ m h := by simp*
| _ (∀' f)       s n₁ n₂ m h :=
  begin
    have := lift_at_subst_formula_large f s n₂ (add_le_add_right h 1),
    simp [add_comm, add_left_comm] at this,
    simp [*, add_assoc]
  end

lemma lift_subst_formula_large {l} (f : preformula L l) (s : term L) {n₁ n₂} :
  (f ↑↑ n₂)[s /// n₁+n₂] = (f [s /// n₁]) ↑↑ n₂ :=
lift_at_subst_formula_large f s n₂ n₁.zero_le

lemma lift_subst_formula_large' {l} (f : preformula L l) (s : term L) {n₁ n₂} :
  (f ↑↑ n₂)[s /// n₂+n₁] = (f [s /// n₁]) ↑↑ n₂ :=
by rw [add_comm]; apply lift_subst_formula_large

lemma lift_at_subst_formula_medium : ∀{l} (f : preformula L l) (s : term L) {n₁ n₂ m}, m ≤ n₂ →
  n₂ ≤ m + n₁ → (f ↑↑' n₁+1 # m)[s /// n₂] = f ↑↑' n₁ # m
| _ falsum       s n₁ n₂ m h₁ h₂ := by refl
| _ (t₁ ≃ t₂)    s n₁ n₂ m h₁ h₂ := by simp [*, lift_at_subst_term_medium]
| _ (rel R)      s n₁ n₂ m h₁ h₂ := by refl
| _ (apprel f t) s n₁ n₂ m h₁ h₂ := by simp [*, lift_at_subst_term_medium]
| _ (f₁ ⟹ f₂)   s n₁ n₂ m h₁ h₂ := by simp*
| _ (∀' f)       s n₁ n₂ m h₁ h₂ :=
  begin
    have h : n₂ + 1 ≤ (m + 1) + n₁, from le_trans (add_le_add_right h₂ 1) (by simp [add_right_comm]),
    have := lift_at_subst_formula_medium f s (add_le_add_right h₁ 1) h,
    simp only [fol.subst_formula, fol.lift_formula_at] at this, simp*
  end

lemma lift_subst_formula_medium {l} (f : preformula L l) (s : term L) (n₁ n₂) :
  (f ↑↑ ((n₁ + n₂) + 1))[s /// n₁] = f ↑↑ (n₁ + n₂) :=
lift_at_subst_formula_medium f s n₁.zero_le (by rw [zero_add]; exact n₁.le_add_right n₂)

lemma lift_at_subst_formula_eq {l} (f : preformula L l) (s : term L) (n : ℕ) :
  (f ↑↑' 1 # n)[s /// n] = f :=
begin rw [lift_at_subst_formula_medium f s, lift_formula_at_zero]; refl end

@[simp] lemma lift_formula1_subst {l} (f : preformula L l) (s : term L) : (f ↑↑ 1)[s /// 0] = f :=
lift_at_subst_formula_eq f s 0

lemma lift_at_subst_formula_small : ∀{l} (f : preformula L l) (s : term L) (n₁ n₂ m),
 (f ↑↑' n₁ # (m + n₂ + 1))[s ↑' n₁ # m /// n₂] = (f [s /// n₂]) ↑↑' n₁ # (m + n₂)
| _ falsum       s n₁ n₂ m := by refl
| _ (t₁ ≃ t₂)    s n₁ n₂ m :=
    by dsimp; simp only [lift_at_subst_term_small, eq_self_iff_true, and_self]
| _ (rel R)      s n₁ n₂ m := by refl
| _ (apprel f t) s n₁ n₂ m :=
    by dsimp; simp only [*, lift_at_subst_term_small, eq_self_iff_true, and_self]
| _ (f₁ ⟹ f₂)   s n₁ n₂ m :=
    by dsimp; simp only [*, lift_at_subst_term_small, eq_self_iff_true, and_self]
| _ (∀' f)       s n₁ n₂ m :=
    by have := lift_at_subst_formula_small f s n₁ (n₂+1) m; dsimp; simp at this ⊢; exact this

lemma lift_at_subst_formula_small0 {l} (f : preformula L l) (s : term L) (n₁ m) :
 (f ↑↑' n₁ # (m + 1))[s ↑' n₁ # m /// 0] = (f [s /// 0]) ↑↑' n₁ # m :=
lift_at_subst_formula_small f s n₁ 0 m

lemma subst_formula2 : ∀{l} (f : preformula L l) (s₁ s₂ : term L) (n₁ n₂),
  f [s₁ /// n₁] [s₂ /// n₁ + n₂] = f [s₂ /// n₁ + n₂ + 1] [s₁[s₂ // n₂] /// n₁]
| _ falsum       s₁ s₂ n₁ n₂ := by refl
| _ (t₁ ≃ t₂)    s₁ s₂ n₁ n₂ := by simp [*, subst_term2]
| _ (rel R)      s₁ s₂ n₁ n₂ := by refl
| _ (apprel f t) s₁ s₂ n₁ n₂ := by simp [*, subst_term2]
| _ (f₁ ⟹ f₂)   s₁ s₂ n₁ n₂ := by simp*
| _ (∀' f)       s₁ s₂ n₁ n₂ :=
  by simp *; rw [add_right_comm, subst_formula2 f s₁ s₂ (n₁ + 1) n₂]; simp

lemma subst_formula2_zero {l} (f : preformula L l) (s₁ s₂ : term L) (n) :
  f [s₁ /// 0] [s₂ /// n] = f [s₂ /// n + 1] [s₁[s₂ // n] /// 0] :=
let h := subst_formula2 f s₁ s₂ 0 n in by simp only [fol.subst_formula, zero_add] at h; exact h

lemma lift_subst_formula_cancel : ∀{l} (f : preformula L l) (n : ℕ), (f ↑↑' 1 # (n+1))[&0 /// n] = f
| _ falsum       n := by refl
| _ (t₁ ≃ t₂)    n := by simp [*, lift_subst_term_cancel]
| _ (rel R)      n := by refl
| _ (apprel f t) n := by simp [*, lift_subst_term_cancel]
| _ (f₁ ⟹ f₂)   n := by simp*
| _ (∀' f)       n := by simp*

@[simp] lemma subst_formula_apps_rel {l} (f : preformula L l) (ts : dvector (term L) l) (s : term L)
  (n : ℕ): (apps_rel f ts)[s /// n] = apps_rel (f[s /// n]) (ts.map $ λx, x[s // n]) :=
by induction ts generalizing f;[refl, apply ts_ih (apprel f ts_x)]

@[simp] def count_quantifiers : ∀ {l}, preformula L l → ℕ
| _ falsum       := 0
| _ (t₁ ≃ t₂)    := 0
| _ (rel R)      := 0
| _ (apprel f t) := 0
| _ (f₁ ⟹ f₂)   := count_quantifiers f₁ + count_quantifiers f₂
| _ (∀' f)       := count_quantifiers f + 1

@[simp] def count_quantifiers_succ {l} (f : preformula L (l+1)) : count_quantifiers f = 0 :=
by cases f; refl

@[simp] lemma count_quantifiers_subst : ∀ {l} (f : preformula L l) (s : term L) (n : ℕ),
  count_quantifiers (f[s /// n]) = count_quantifiers f
| _ falsum       s n := by refl
| _ (t₁ ≃ t₂)    s n := by refl
| _ (rel R)      s n := by refl
| _ (apprel f t) s n := by refl
| _ (f₁ ⟹ f₂)   s n := by simp*
| _ (∀' f)       s n := by simp*

def quantifier_free {l} : preformula L l → Prop := λ f, count_quantifiers f = 0

/- Provability
* to decide: should Γ be a list or a set (or finset)?
* We use natural deduction as our deduction system, since that is most convenient to work with.
* All rules are motivated to work well with backwards reasoning.
-/
inductive prf : set (formula L) → formula L → Type u
| axm     {Γ A} (h : A ∈ Γ) : prf Γ A
| impI    {Γ : set $ formula L} {A B} (h : prf (insert A Γ) B) : prf Γ (A ⟹ B)
| impE    {Γ} (A) {B} (h₁ : prf Γ (A ⟹ B)) (h₂ : prf Γ A) : prf Γ B
| falsumE {Γ : set $ formula L} {A} (h : prf (insert ∼A Γ) ⊥) : prf Γ A
| allI    {Γ A} (h : prf (lift_formula1 '' Γ) A) : prf Γ (∀' A)
| allE₂   {Γ} A t (h : prf Γ (∀' A)) : prf Γ (A[t /// 0])
| ref     (Γ t) : prf Γ (t ≃ t)
| subst₂  {Γ} (s t f) (h₁ : prf Γ (s ≃ t)) (h₂ : prf Γ (f[s /// 0])) : prf Γ (f[t /// 0])

export prf
localized "infix ` ⊢ `:51 := fol.prf" in fol -- input: \|- or \vdash

def provable (T : set $ formula L) (f : formula L) := nonempty (T ⊢ f)
localized "infix ` ⊢' `:51 := fol.provable" in fol -- input: \|- or \vdash

def allE {Γ} (A : formula L) (t) {B} (H₁ : Γ ⊢ ∀' A) (H₂ : A[t /// 0] = B) : Γ ⊢ B :=
by induction H₂; exact allE₂ A t H₁

def subst {Γ} {s t} (f₁ : formula L) {f₂} (H₁ : Γ ⊢ s ≃ t) (H₂ : Γ ⊢ f₁[s /// 0])
  (H₃ : f₁[t /// 0] = f₂) : Γ ⊢ f₂ :=
by induction H₃; exact subst₂ s t f₁ H₁ H₂

def axm1 {Γ : set (formula L)} {A : formula L} : insert A Γ ⊢ A := by apply axm; left; refl
def axm2 {Γ : set (formula L)} {A B : formula L} : insert A (insert B Γ) ⊢ B :=
by apply axm; right; left; refl

def weakening {Γ Δ} {f : formula L} (H₁ : Γ ⊆ Δ) (H₂ : Γ ⊢ f) : Δ ⊢ f :=
begin
  induction H₂ generalizing Δ,
  { apply axm, exact H₁ H₂_h, },
  { apply impI, apply H₂_ih, apply insert_subset_insert, apply H₁ },
  { apply impE, apply H₂_ih_h₁, assumption, apply H₂_ih_h₂, assumption },
  { apply falsumE, apply H₂_ih, apply insert_subset_insert, apply H₁ },
  { apply allI, apply H₂_ih, apply image_subset _ H₁ },
  { apply allE₂, apply H₂_ih, assumption },
  { apply ref },
  { apply subst₂, apply H₂_ih_h₁, assumption, apply H₂_ih_h₂, assumption },
end

def prf_lift {Γ} {f : formula L} (n m : ℕ) (H : Γ ⊢ f) : (λf', f' ↑↑' n # m) '' Γ ⊢ f ↑↑' n # m :=
begin
  induction H generalizing m,
  { apply axm, apply mem_image_of_mem _ H_h },
  { apply impI, have h := @H_ih m, rw [image_insert_eq] at h, exact h },
  { apply impE, apply H_ih_h₁, apply H_ih_h₂ },
  { apply falsumE, have h := @H_ih m, rw [image_insert_eq] at h, exact h },
  { apply allI, rw [image_image], have h := @H_ih (m+1), rw [image_image] at h,
    apply cast _ h, congr1, apply image_congr', intro f', symmetry,
    exact lift_formula_at2_small f' _ _ m.zero_le },
  { apply allE _ _ (H_ih m), apply lift_at_subst_formula_small0 },
  { apply ref },
  { apply subst _ (H_ih_h₁ m),
    { have h := @H_ih_h₂ m, rw [←lift_at_subst_formula_small0] at h, exact h},
    rw [lift_at_subst_formula_small0] },
end

def substitution {Γ} {f : formula L} (t n) (H : Γ ⊢ f) : (λx, x[t /// n]) '' Γ ⊢ f[t /// n] :=
begin
  induction H generalizing n,
  { apply axm, apply mem_image_of_mem _ H_h },
  { apply impI, have h := H_ih n, rw [image_insert_eq] at h, exact h },
  { apply impE, apply H_ih_h₁, apply H_ih_h₂ },
  { apply falsumE, have h := H_ih n, rw [image_insert_eq] at h, exact h },
  { apply allI, rw [image_image], have h := @H_ih (n+1), rw [image_image] at h,
    apply cast _ h, congr1, apply image_congr', intro,
    apply lift_subst_formula_large },
  { apply allE _ _ (H_ih n), symmetry, apply subst_formula2_zero },
  { apply ref },
  { apply subst _ (H_ih_h₁ n), { have h := @H_ih_h₂ n, rw [subst_formula2_zero] at h, exact h},
    rw [subst_formula2_zero] },
end

def reflect_prf_lift1 {Γ} {f : formula L} (h : lift_formula1 '' Γ ⊢ f ↑↑ 1) : Γ ⊢ f :=
begin
  have := substitution &0 0 h, simp [image_image] at this, exact this
end

-- def reflect_prf_lift {Γ} {f : formula L} (n m : ℕ) :
--   (λf' : formula L, f' ↑' n # m) '' Γ ⊢ f ↑' n # m → Γ ⊢ f :=
-- begin
--   induction n,
--   { rw [lift_zero] },
--   { }
-- end

def weakening1 {Γ} {f₁ f₂ : formula L} (H : Γ ⊢ f₂) : insert f₁ Γ ⊢ f₂ :=
weakening (subset_insert f₁ Γ) H



def weakening2 {Γ} {f₁ f₂ f₃ : formula L} (H : insert f₁ Γ ⊢ f₂) : insert f₁ (insert f₃ Γ) ⊢ f₂ :=
weakening (insert_subset_insert (subset_insert _ Γ)) H

def deduction {Γ} {A B : formula L} (H : Γ ⊢ A ⟹ B) : insert A Γ ⊢ B :=
impE A (weakening1 H) axm1

def exfalso {Γ} {A : formula L} (H : Γ ⊢ falsum) : Γ ⊢ A :=
falsumE (weakening1 H)

def exfalso' {Γ} {A : formula L} (H : Γ ⊢' falsum) : Γ ⊢' A :=
by {fapply nonempty.map, exact Γ ⊢ falsum, exact exfalso, exact H}

def notI {Γ} {A : formula L} (H : Γ ⊢ A ⟹ falsum) : Γ ⊢ ∼ A :=
  by {rw[not], assumption}

def andI {Γ} {f₁ f₂ : formula L} (H₁ : Γ ⊢ f₁) (H₂ : Γ ⊢ f₂) : Γ ⊢ f₁ ⊓ f₂ :=
begin
  apply impI, apply impE f₂,
  { apply impE f₁, apply axm1, exact weakening1 H₁ },
  { exact weakening1 H₂ }
end

def andE1 {Γ f₁} (f₂ : formula L) (H : Γ ⊢ f₁ ⊓ f₂) : Γ ⊢ f₁ :=
begin
  apply falsumE, apply impE _ (weakening1 H), apply impI, apply exfalso,
  apply impE f₁; [apply axm2, apply axm1]
end

def andE2 {Γ} (f₁ : formula L) {f₂} (H : Γ ⊢ f₁ ⊓ f₂) : Γ ⊢ f₂ :=
begin apply falsumE, apply impE _ (weakening1 H), apply impI, apply axm2 end

def orI1 {Γ} {A B : formula L} (H : Γ ⊢ A) : Γ ⊢ A ⊔ B :=
begin apply impI, apply exfalso, refine impE _ _ (weakening1 H), apply axm1 end

def orI2 {Γ} {A B : formula L} (H : Γ ⊢ B) : Γ ⊢ A ⊔ B :=
impI $ weakening1 H

def orE {Γ} {A B C : formula L} (H₁ : Γ ⊢ A ⊔ B) (H₂ : insert A Γ ⊢ C) (H₃ : insert B Γ ⊢ C) :
  Γ ⊢ C :=
begin
  apply falsumE, apply impE C, { apply axm1 },
  apply impE B, { apply impI, exact weakening2 H₃ },
  apply impE _ (weakening1 H₁),
  apply impI (impE _ axm2 (weakening2 H₂))
end

def biimpI {Γ} {f₁ f₂ : formula L} (H₁ : insert f₁ Γ ⊢ f₂) (H₂ : insert f₂ Γ ⊢ f₁) : Γ ⊢ f₁ ⇔ f₂ :=
by apply andI; apply impI; assumption

def biimpE1 {Γ} {f₁ f₂ : formula L} (H : Γ ⊢ f₁ ⇔ f₂) : insert f₁ Γ ⊢ f₂ := deduction (andE1 _ H)
def biimpE2 {Γ} {f₁ f₂ : formula L} (H : Γ ⊢ f₁ ⇔ f₂) : insert f₂ Γ ⊢ f₁ := deduction (andE2 _ H)

def exI {Γ f} (t : term L) (H : Γ ⊢ f [t /// 0]) : Γ ⊢ ∃' f :=
begin
  apply impI,
  apply impE (f[t /// 0]) _ (weakening1 H),
  apply allE₂ ∼f t axm1,
end

def exE {Γ} {f₁ f₂ : formula L} (H₁ : Γ ⊢ ∃' f₁)
  (H₂ : insert f₁ (lift_formula1 '' Γ) ⊢ lift_formula1 f₂) : Γ ⊢ f₂ :=
begin
  apply falsumE, apply impE _ (weakening1 H₁), apply allI, apply impI,
  rw [image_insert_eq], apply impE _ axm2, apply weakening2 H₂
end

def ex_not_of_not_all {Γ} {f : formula L} (H : Γ ⊢ ∼ ∀' f) : Γ ⊢ ∃' ∼ f :=
begin
  apply falsumE, apply impE _ (weakening1 H), apply allI, apply falsumE,
  rw [image_insert_eq], apply impE _ axm2, apply exI &0,
  rw [lift_subst_formula_cancel], exact axm1
end

def not_and_self {Γ : set (formula L)} {f : formula L} (H : Γ ⊢ f ⊓ ∼f) : Γ ⊢ ⊥ :=
impE f (andE2 f H) (andE1 ∼f H)

-- def andE1 {Γ f₁} (f₂ : formula L) (H : Γ ⊢ f₁ ⊓ f₂) : Γ ⊢ f₁ :=
def symm {Γ} {s t : term L} (H : Γ ⊢ s ≃ t) : Γ ⊢ t ≃ s :=
begin
  apply subst (&0 ≃ s ↑ 1) H; rw [subst_formula_equal, lift_term1_subst_term, subst_term_var0],
  apply ref
end

def trans {Γ} {t₁ t₂ t₃ : term L} (H : Γ ⊢ t₁ ≃ t₂) (H' : Γ ⊢ t₂ ≃ t₃) : Γ ⊢ t₁ ≃ t₃ :=
begin
  apply subst (t₁ ↑ 1 ≃ &0) H'; rw [subst_formula_equal, lift_term1_subst_term, subst_term_var0],
  exact H
end

def congr {Γ} {t₁ t₂ : term L} (s : term L) (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢ s[t₁ // 0] ≃ s[t₂ // 0] :=
begin
  apply subst (s[t₁ // 0] ↑ 1 ≃ s) H,
  { rw [subst_formula_equal, lift_term1_subst_term], apply ref },
  { rw [subst_formula_equal, lift_term1_subst_term] }
end

def app_congr {Γ} {t₁ t₂ : term L} (s : preterm L 1) (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢ app s t₁ ≃ app s t₂ :=
begin
  have h := congr (app (s ↑ 1) &0) H, simp at h, exact h
end

def apprel_congr {Γ} {t₁ t₂ : term L} (f : preformula L 1) (H : Γ ⊢ t₁ ≃ t₂)
  (H₂ : Γ ⊢ apprel f t₁) : Γ ⊢ apprel f t₂ :=
begin
  apply subst (apprel (f ↑↑ 1) &0) H; simp, exact H₂
end

def imp_trans {Γ} {f₁ f₂ f₃ : formula L} (H₁ : Γ ⊢ f₁ ⟹ f₂) (H₂ : Γ ⊢ f₂ ⟹ f₃) : Γ ⊢ f₁ ⟹ f₃ :=
begin
  apply impI, apply impE _ (weakening1 H₂), apply impE _ (weakening1 H₁) axm1
end

def biimp_refl (Γ : set (formula L)) (f : formula L) : Γ ⊢ f ⇔ f :=
by apply biimpI; apply axm1

def biimp_trans {Γ} {f₁ f₂ f₃ : formula L} (H₁ : Γ ⊢ f₁ ⇔ f₂) (H₂ : Γ ⊢ f₂ ⇔ f₃) : Γ ⊢ f₁ ⇔ f₃ :=
begin
  apply andI; apply imp_trans,
  apply andE1 _ H₁, apply andE1 _ H₂, apply andE2 _ H₂, apply andE2 _ H₁
end

def equal_preterms (T : set (formula L)) {l} (t₁ t₂ : preterm L l) : Type u :=
∀(ts : dvector (term L) l), T ⊢ apps t₁ ts ≃ apps t₂ ts

def equal_preterms_app {T : set (formula L)} {l} {t t' : preterm L (l+1)} {s s' : term L}
  (Ht : equal_preterms T t t') (Hs : T ⊢ s ≃ s') : equal_preterms T (app t s) (app t' s') :=
begin
  intro xs,
  apply trans (Ht (xs.cons s)),
  have h := congr (apps (t' ↑ 1) (&0 :: xs.map lift_term1)) Hs,
  simp [dvector.map_congr (λt, lift_term1_subst_term t s')] at h,
  exact h
end

@[refl] def equal_preterms_refl (T : set (formula L)) {l} (t : preterm L l) : equal_preterms T t t :=
λxs, ref T (apps t xs)

def equiv_preformulae (T : set (formula L)) {l} (f₁ f₂ : preformula L l) : Type u :=
∀(ts : dvector (term L) l), T ⊢ apps_rel f₁ ts ⇔ apps_rel f₂ ts

def equiv_preformulae_apprel {T : set (formula L)} {l} {f f' : preformula L (l+1)} {s s' : term L}
  (Ht : equiv_preformulae T f f') (Hs : T ⊢ s ≃ s') :
    equiv_preformulae T (apprel f s) (apprel f' s') :=
begin
  intro xs,
  apply biimp_trans (Ht (xs.cons s)),
  apply subst (apps_rel (f' ↑↑ 1) ((s :: xs).map lift_term1) ⇔
               apps_rel (f' ↑↑ 1) (&0 :: xs.map lift_term1)) Hs;
    simp [dvector.map_congr (λt, lift_term1_subst_term t s')],
  apply biimp_refl
end

@[refl] def equiv_preformulae_refl (T : set (formula L)) {l} (f : preformula L l) :
  equiv_preformulae T f f :=
λxs, biimp_refl T (apps_rel f xs)

def impI' {Γ : set $ formula L} {A B} (h : insert A Γ ⊢' B) : Γ ⊢' (A ⟹ B) := h.map impI
def impE' {Γ} (A : formula L) {B} (h₁ : Γ ⊢' A ⟹ B) (h₂ : Γ ⊢' A) : Γ ⊢' B := h₁.map2 (impE _) h₂
def falsumE' {Γ : set $ formula L} {A} (h : insert ∼A Γ ⊢' ⊥ ) : Γ ⊢' A := h.map falsumE
def allI' {Γ} {A : formula L} (h : lift_formula1 '' Γ ⊢' A) : Γ ⊢' ∀' A := h.map allI
def allE' {Γ} (A : formula L) (t) {B} (H₁ : Γ ⊢' ∀' A) (H₂ : A[t /// 0] = B) : Γ ⊢' B :=
H₁.map (λx, allE _ _ x H₂)
def allE₂' {Γ} {A} {t : term L} (h : Γ ⊢' ∀' A) : Γ ⊢' A[t /// 0] := h.map (λx, allE _ _ x rfl)
def ref' (Γ) (t : term L) : Γ ⊢' (t ≃ t) := ⟨ref Γ t⟩
def subst' {Γ} {s t} (f₁ : formula L) {f₂} (H₁ : Γ ⊢' s ≃ t) (H₂ : Γ ⊢' f₁[s /// 0])
  (H₃ : f₁[t /// 0] = f₂) : Γ ⊢' f₂ :=
H₁.map2 (λx y, subst _ x y H₃) H₂
def subst₂' {Γ} (s t) (f : formula L) (h₁ : Γ ⊢' s ≃ t) (h₂ : Γ ⊢' f[s /// 0]) : Γ ⊢' f[t /// 0] :=
h₁.map2 (subst₂ _ _ _) h₂

def weakening' {Γ Δ} {f : formula L} (H₁ : Γ ⊆ Δ) (H₂ : Γ ⊢' f) : Δ ⊢' f := H₂.map $ weakening H₁
def weakening1' {Γ} {f₁ f₂ : formula L} (H : Γ ⊢' f₂) : insert f₁ Γ ⊢' f₂ := H.map weakening1
def weakening2' {Γ} {f₁ f₂ f₃ : formula L} (H : insert f₁ Γ ⊢' f₂) : insert f₁ (insert f₃ Γ) ⊢' f₂ :=
H.map weakening2

lemma apprel_congr' {Γ} {t₁ t₂ : term L} (f : preformula L 1) (H : Γ ⊢ t₁ ≃ t₂) :
  Γ ⊢' apprel f t₁ ↔ Γ ⊢' apprel f t₂ :=
⟨nonempty.map $ apprel_congr f H, nonempty.map $ apprel_congr f $ symm H⟩

lemma prf_all_iff {Γ : set (formula L)} {f} : Γ ⊢' ∀' f ↔ lift_formula1 '' Γ ⊢' f :=
begin
  split,
  { intro H, rw [←lift_subst_formula_cancel f 0],
    apply allE₂', apply H.map (prf_lift 1 0) },
  { exact allI' }
end

lemma iff_of_biimp {Γ} {f₁ f₂ : formula L} (H : Γ ⊢' f₁ ⇔ f₂) : Γ ⊢' f₁ ↔ Γ ⊢' f₂ :=
⟨impE' _ $ H.map (andE1 _), impE' _ $ H.map (andE2 _)⟩

lemma prf_by_cases {Γ} (f₁) {f₂ : formula L} (H₁ : insert f₁ Γ ⊢' f₂)
  (H₂ : insert ∼f₁ Γ ⊢' f₂) : Γ ⊢' f₂ :=
begin
  apply falsumE', apply impE' _ ⟨axm1⟩,
  refine impE' _ (impI' (weakening2' H₁)) _,
  apply falsumE', apply impE' _ ⟨axm2⟩, apply weakening2' H₂
end

/- model theory -/

/- an L-structure is a type S with interpretations of the functions and relations on S -/
variable (L)
structure Structure :=
(carrier : Type u)
(fun_map : ∀{n}, L.functions n → dvector carrier n → carrier)
(rel_map : ∀{n}, L.relations n → dvector carrier n → Prop)
variable {L}
instance has_coe_Structure : has_coe_to_sort (Structure L) :=
⟨Type u, Structure.carrier⟩

/- realization of terms -/
@[simp] def realize_term {S : Structure L} (v : ℕ → S) :
  ∀{l} (t : preterm L l) (xs : dvector S l), S.carrier
| _ &k          xs := v k
| _ (func f)    xs := S.fun_map f xs
| _ (app t₁ t₂) xs := realize_term t₁ $ realize_term t₂ ([])::xs

lemma realize_term_congr {S : Structure L} {v v' : ℕ → S} (h : ∀n, v n = v' n) :
  ∀{l} (t : preterm L l) (xs : dvector S l), realize_term v t xs = realize_term v' t xs
| _ &k          xs := h k
| _ (func f)    xs := by refl
| _ (app t₁ t₂) xs := by dsimp; rw [realize_term_congr t₁, realize_term_congr t₂]

lemma realize_term_subst {S : Structure L} (v : ℕ → S) : ∀{l} (n : ℕ) (t : preterm L l)
  (s : term L) (xs : dvector S l),
  realize_term (v[realize_term v (s ↑ n) ([]) //' n]) t xs = realize_term v (t[s // n]) xs
| _ n &k          s [] :=
  by apply decidable.lt_by_cases k n; intro h;[simp [h], {subst h; simp}, simp [h]]
| _ n (func f)    s xs := by refl
| _ n (app t₁ t₂) s xs := by dsimp; simp*

lemma realize_term_subst_lift {S : Structure L} (v : ℕ → S) (x : S) (m : ℕ) : ∀{l} (t : preterm L l)
  (xs : dvector S l), realize_term (v [x //' m]) (t ↑' 1 # m) xs = realize_term v t xs
| _ &k          [] :=
  begin
    by_cases h : m ≤ k,
    { have : m < k + 1, from lt_succ_of_le h, simp* },
    { have : k < m, from lt_of_not_ge h, simp* }
  end
| _ (func f)    xs := by refl
| _ (app t₁ t₂) xs := by simp*

/- realization of formulas -/
@[simp] def realize_formula {S : Structure L} : ∀{l}, (ℕ → S) → preformula L l → dvector S l → Prop
| _ v falsum       xs := false
| _ v (t₁ ≃ t₂)    xs := realize_term v t₁ xs = realize_term v t₂ xs
| _ v (rel R)      xs := S.rel_map R xs
| _ v (apprel f t) xs := realize_formula v f $ realize_term v t ([])::xs
| _ v (f₁ ⟹ f₂)   xs := realize_formula v f₁ xs → realize_formula v f₂ xs
| _ v (∀' f)       xs := ∀(x : S), realize_formula (v [x //' 0]) f xs

lemma realize_formula_congr {S : Structure L} : ∀{l} {v v' : ℕ → S} (h : ∀n, v n = v' n)
  (f : preformula L l) (xs : dvector S l), realize_formula v f xs ↔ realize_formula v' f xs
| _ v v' h falsum       xs := by refl
| _ v v' h (t₁ ≃ t₂)    xs := by simp [realize_term_congr h]
| _ v v' h (rel R)      xs := by refl
| _ v v' h (apprel f t) xs := by simp [realize_term_congr h]; rw [realize_formula_congr h]
| _ v v' h (f₁ ⟹ f₂)   xs := by dsimp; rw [realize_formula_congr h, realize_formula_congr h]
| _ v v' h (∀' f)       xs :=
  by apply forall_congr; intro x; apply realize_formula_congr; intro n;
     apply subst_realize_congr h

lemma realize_formula_subst {S : Structure L} : ∀{l} (v : ℕ → S) (n : ℕ) (f : preformula L l)
  (s : term L) (xs : dvector S l),
  realize_formula (v[realize_term v (s ↑ n) ([]) //' n]) f xs ↔ realize_formula v (f[s /// n]) xs
| _ v n falsum       s xs := by refl
| _ v n (t₁ ≃ t₂)    s xs := by simp [realize_term_subst]
| _ v n (rel R)      s xs := by refl
| _ v n (apprel f t) s xs := by simp [realize_term_subst]; rw realize_formula_subst
| _ v n (f₁ ⟹ f₂)   s xs := by apply imp_congr; apply realize_formula_subst
| _ v n (∀' f)       s xs :=
  begin
    apply forall_congr, intro x, rw [←realize_formula_subst], apply realize_formula_congr,
    intro k, rw [subst_realize2_0, ←realize_term_subst_lift v x 0, lift_term_def, lift_term2]
  end

lemma realize_formula_subst0 {S : Structure L} {l} (v : ℕ → S) (f : preformula L l) (s : term L)
  (xs : dvector S l) :
  realize_formula (v[realize_term v s ([]) //' 0]) f xs ↔ realize_formula v (f[s /// 0]) xs :=
by have h := realize_formula_subst v 0 f s; simp at h; exact h xs

lemma realize_formula_subst_lift {S : Structure L} : ∀{l} (v : ℕ → S) (x : S) (m : ℕ)
  (f : preformula L l) (xs : dvector S l),
  realize_formula (v [x //' m]) (f ↑↑' 1 # m) xs = realize_formula v f xs
| _ v x m falsum       xs := by refl
| _ v x m (t₁ ≃ t₂)    xs := by simp [realize_term_subst_lift]
| _ v x m (rel R)      xs := by refl
| _ v x m (apprel f t) xs := by simp [realize_term_subst_lift]; rw realize_formula_subst_lift
| _ v x m (f₁ ⟹ f₂)   xs := by apply imp_eq_congr; apply realize_formula_subst_lift
| _ v x m (∀' f)       xs :=
  begin
    apply forall_eq_congr, intro x',
    rw [realize_formula_congr (subst_realize2_0 _ _ _ _), realize_formula_subst_lift]
  end

/- the following definitions of provability and satisfiability are not exactly how you normally define them, since we define it for formulae instead of sentences. If all the formulae happen to be sentences, then these definitions are equivalent to the normal definitions (the realization of closed terms and sentences are independent of the realizer v).
 -/
def all_prf (T T' : set (formula L)) := ∀{{f}}, f ∈ T' → T ⊢ f
localized "infix ` ⊢'' `:51 := fol.all_prf" in fol -- input: |- or \vdash

def satisfied_in (S : Structure L) (f : formula L) := ∀(v : ℕ → S), realize_formula v f ([])
localized "infix ` ⊨' `:51 := fol.satisfied_in" in fol -- input using \|= or \vDash, but not using \models

def all_satisfied_in (S : Structure L) (T : set (formula L)) := ∀{{f}}, f ∈ T → S ⊨' f
localized "infix ` ⊨=' `:51 := fol.all_satisfied_in" in fol -- input using \|= or \vDash, but not using \models

def satisfied (T : set (formula L)) (f : formula L) :=
∀(S : Structure L) (v : ℕ → S), (∀f' ∈ T, realize_formula v (f' : formula L) ([])) →
  realize_formula v f ([])

localized "infix ` ⊨ `:51 := fol.satisfied" in fol -- input using \|= or \vDash, but not using \models

def all_satisfied (T T' : set (formula L)) := ∀{{f}}, f ∈ T' → T ⊨ f
localized "infix ` ⊨= `:51 := fol.all_satisfied" in fol -- input using \|= or \vDash, but not using \models

def satisfied_in_trans {S : Structure L} {T : set (formula L)} {f : formula L} (H' : S ⊨=' T)
  (H : T ⊨ f) : S ⊨' f :=
λv, H S v $ λf' hf', H' hf' v

def all_satisfied_in_trans  {S : Structure L} {T T' : set (formula L)} (H' : S ⊨=' T) (H : T ⊨= T') :
  S ⊨=' T' :=
λf hf, satisfied_in_trans H' $ H hf

def satisfied_of_mem {T : set (formula L)} {f : formula L} (hf : f ∈ T) : T ⊨ f :=
λS v h, h f hf

def all_satisfied_of_subset {T T' : set (formula L)} (h : T' ⊆ T) : T ⊨= T' :=
λf hf, satisfied_of_mem $ h hf

def satisfied_trans {T₁ T₂ : set (formula L)} {f : formula L} (H' : T₁ ⊨= T₂) (H : T₂ ⊨ f) : T₁ ⊨ f :=
λS v h, H S v $ λf' hf', H' hf' S v h

def all_satisfied_trans {T₁ T₂ T₃ : set (formula L)} (H' : T₁ ⊨= T₂) (H : T₂ ⊨= T₃) : T₁ ⊨= T₃ :=
λf hf, satisfied_trans H' $ H hf

def satisfied_weakening {T T' : set (formula L)} (H : T ⊆ T') {f : formula L} (HT : T ⊨ f) :
  T' ⊨ f :=
λS v h, HT S v $ λf' hf', h f' $ H hf'

/- soundness for a set of formulae -/
lemma formula_soundness {Γ : set (formula L)} {A : formula L} (H : Γ ⊢ A) : Γ ⊨ A :=
begin
  intro S, induction H; intros v h,
  { apply h, apply H_h },
  { intro ha, apply H_ih, intros f hf, induction hf, { subst hf, assumption }, apply h f hf },
  { exact H_ih_h₁ v h (H_ih_h₂ v h) },
  { apply classical.by_contradiction, intro ha,
    apply H_ih v, intros f hf, induction hf, { cases hf, exact ha }, apply h f hf },
  { intro x, apply H_ih, intros f hf, rcases hf with ⟨f, hf, rfl⟩,
    rw [realize_formula_subst_lift v x 0 f], exact h f hf },
  { rw [←realize_formula_subst0], apply H_ih v h (realize_term v H_t ([])) },
  { dsimp, refl },
  { have h' := H_ih_h₁ v h, dsimp at h', rw [←realize_formula_subst0, ←h', realize_formula_subst0],
    apply H_ih_h₂ v h },
end

/- sentences and theories -/
variable (L)
inductive bounded_preterm (n : ℕ) : ℕ → Type u
| bd_var {} : ∀ (k : fin n), bounded_preterm 0
| bd_func {} : ∀ {l : ℕ} (f : L.functions l), bounded_preterm l
| bd_app : ∀ {l : ℕ} (t : bounded_preterm (l + 1)) (s : bounded_preterm 0), bounded_preterm l
export bounded_preterm

def bounded_term   (n) := bounded_preterm L n 0
def closed_preterm (l) := bounded_preterm L 0 l
def closed_term        := closed_preterm L 0
variable {L}

prefix `&`:max := bd_var
def bd_const {n} (c : L.constants) : bounded_term L n := bd_func c

@[simp] def bd_apps' {n} : ∀{l m}, bounded_preterm L n (l + m) → dvector (bounded_term L n) m →
  bounded_preterm L n l
| l 0 t [] := t
| l (m+1) t (x::xs) := bd_apps' (bd_app t x) xs

@[simp] def bd_apps {n} : ∀{l}, bounded_preterm L n l → dvector (bounded_term L n) l →
  bounded_term L n
| _ t []       := t
| _ t (t'::ts) := bd_apps (bd_app t t') ts

namespace bounded_preterm
@[simp] protected def fst {n} : ∀{l}, bounded_preterm L n l → preterm L l
| _ &k           := &k
| _ (bd_func f)  := func f
| _ (bd_app t s) := app (fst t) (fst s)

local attribute [ext] fin.eq_of_veq
@[ext] protected def eq {n} : ∀{l} {t₁ t₂ : bounded_preterm L n l} (h : t₁.fst = t₂.fst),
  t₁ = t₂
| _ &k &k'                        h := by injection h with h'; congr1; ext; exact h'
| _ &k (bd_func f')               h := by injection h
| _ &k (bd_app t₁' t₂')           h := by injection h
| _ (bd_func f) &k'               h := by injection h
| _ (bd_func f) (bd_func f')      h := by injection h with h'; rw h'
| _ (bd_func f) (bd_app t₁' t₂')  h := by injection h
| _ (bd_app t₁ t₂) &k'            h := by injection h
| _ (bd_app t₁ t₂) (bd_func f')   h := by injection h
| _ (bd_app t₁ t₂) (bd_app t₁' t₂') h := by injection h with h₁ h₂; congr1; apply eq; assumption

@[simp] protected def cast {n m} (h : n ≤ m) : ∀ {l} (t : bounded_preterm L n l),
  bounded_preterm L m l
| _ &k           := &(k.cast_le h)
| _ (bd_func f)  := bd_func f
| _ (bd_app t s) := bd_app t.cast s.cast

@[simp] lemma cast_bd_app {n m} (h : n ≤ m) {l} {t : bounded_preterm L n (l+1)}
  {s : bounded_preterm L n 0} : (bd_app t s).cast h = (bd_app (t.cast h) (s.cast h)) := by refl

@[simp] lemma cast_bd_apps {n m } (h : n ≤ m) {l} {t : bounded_preterm L n l}
  {ts : dvector (bounded_term L n) l} :
  (bd_apps t ts).cast h = bd_apps (t.cast h) (ts.map (λ t, t.cast h)) :=
by {induction ts generalizing t, refl, simp*}

-- @[simp] lemma cast_bd_apps_nil {n m} (h : n ≤ m) {l} {t : bounded_preterm L n (l+1)} {s : bounded_preterm L n 0} : (bd_apps t s []).cast h = (bd_app (t.cast h) (s.cast h))

@[simp] lemma cast_irrel {n m } {h h' : n ≤ m} : ∀ {l} (t : bounded_preterm L n l),
  (t.cast h) = (t.cast h') :=
by {intros, refl}

@[simp] lemma cast_rfl {n} {h : n ≤ n} : ∀ {l} (t : bounded_preterm L n l), (t.cast h) = t :=
begin
  intros, induction t,
  {simp, unfold fin.cast_le, unfold fin.cast_lt, cases t, refl}, {refl}, {simp*}
end

protected def cast_eq {n m l} (h : n = m) (t : bounded_preterm L n l) : bounded_preterm L m l :=
t.cast $ le_of_eq h

protected def cast1 {n l} (t : bounded_preterm L n l) : bounded_preterm L (n+1) l :=
t.cast $ n.le_add_right 1

@[simp] lemma cast_fst {n m} (h : n ≤ m) : ∀ {l} (t : bounded_preterm L n l), (t.cast h).fst = t.fst
| _ &k           := by refl
| _ (bd_func f)  := by refl
| _ (bd_app t s) := by dsimp; simp [cast_fst]

@[simp] lemma cast_eq_fst {n m l} (h : n = m) (t : bounded_preterm L n l) :
  (t.cast_eq h).fst = t.fst := t.cast_fst _
@[simp] lemma cast1_fst {n l} (t : bounded_preterm L n l) :
  t.cast1.fst = t.fst := t.cast_fst _

@[simp] lemma cast_eq_rfl {n m l} (h : n = m) (t : bounded_preterm L n l) :
  (t.cast_eq h).cast_eq h.symm = t := by ext; simp

@[simp] lemma cast_eq_irrel {n m l} (h h' : n = m) (t : bounded_preterm L n l) :
  (t.cast_eq h) = (t.cast_eq h') := by refl

@[simp] lemma cast_eq_bd_app {n m} (h : n = m) {l} {t : bounded_preterm L n (l+1)}
  {s : bounded_preterm L n 0} : (bd_app t s).cast_eq h = (bd_app (t.cast_eq h) (s.cast_eq h)) :=
by refl

@[simp] lemma cast_eq_bd_apps {n m } (h : n = m) {l} {t : bounded_preterm L n l}
  {ts : dvector (bounded_term L n) l} :
  (bd_apps t ts).cast_eq h = bd_apps (t.cast_eq h) (ts.map (λ t, t.cast_eq h)) :=
by {induction ts generalizing t, refl, simp*}

end bounded_preterm

namespace closed_preterm

@[reducible]protected def cast0 (n) {l} (t : closed_preterm L l) : bounded_preterm L n l :=
t.cast n.zero_le

@[simp] lemma cast0_fst {n l : ℕ} (t : closed_preterm L l) :
  (t.cast0 n).fst = t.fst :=
cast_fst _ _

@[simp] lemma cast_of_cast0 {n} {l} {t : closed_preterm L l} : t.cast0 n =  t.cast n.zero_le :=
by refl

end closed_preterm

@[elab_as_eliminator] def bounded_term.rec {n} {C : bounded_term L n → Sort v}
  (hvar : ∀(k : fin n), C &k)
  (hfunc : Π {l} (f : L.functions l) (ts : dvector (bounded_term L n) l)
    (ih_ts : ∀t, ts.pmem t → C t), C (bd_apps (bd_func f) ts)) :
  ∀(t : bounded_term L n), C t :=
have h : ∀{l} (t : bounded_preterm L n l) (ts : dvector (bounded_term L n) l)
  (ih_ts : ∀s, ts.pmem s → C s), C (bd_apps t ts),
begin
  intros, induction t; try {rw ts.zero_eq},
  { apply hvar },
  { apply hfunc t_f ts ih_ts },
  { apply t_ih_t (t_s::ts), intros t ht,
    cases ht,
    { induction ht, apply t_ih_s ([]), intros s hs, cases hs },
    { exact ih_ts t ht }},
end,
λt, h t ([]) (by intros s hs; cases hs)

@[elab_as_eliminator] def bounded_term.rec1 {n} {C : bounded_term L (n+1) → Sort v}
  (hvar : ∀(k : fin (n+1)), C &k)
  (hfunc : Π {l} (f : L.functions l) (ts : dvector (bounded_term L (n+1)) l)
    (ih_ts : ∀t, ts.pmem t → C t), C (bd_apps (bd_func f) ts)) :
  ∀(t : bounded_term L (n+1)), C t :=
have h : ∀{l} (t : bounded_preterm L (n+1) l) (ts : dvector (bounded_term L (n+1)) l)
  (ih_ts : ∀s, ts.pmem s → C s), C (bd_apps t ts),
begin
  intros, induction t; try {rw ts.zero_eq},
  { apply hvar },
  { apply hfunc t_f ts ih_ts },
  { apply t_ih_t (t_s::ts), intros t ht,
    cases ht,
    { induction ht, apply t_ih_s ([]), intros s hs, cases hs },
    { exact ih_ts t ht }},
end,
λt, h t ([]) (by intros s hs; cases hs)

lemma lift_bounded_term_irrel {n : ℕ} : ∀{l} (t : bounded_preterm L n l) (n') {m : ℕ}
  (h : n ≤ m), t.fst ↑' n' # m = t.fst
| _ &k           n' m h :=
  have h' : ¬(m ≤ k), from not_le_of_lt (lt_of_lt_of_le k.is_lt h), by simp [h']
| _ (bd_func f)  n' m h := by refl
| _ (bd_app t s) n' m h := by simp [lift_bounded_term_irrel t n' h, lift_bounded_term_irrel s n' h]

lemma subst_bounded_term_irrel {n : ℕ} : ∀{l} (t : bounded_preterm L n l) {n'} (s : term L)
  (h : n ≤ n'), t.fst[s // n'] = t.fst
| _ &k             n' s h := by simp [lt_of_lt_of_le k.is_lt h]
| _ (bd_func f)    n' s h := by refl
| _ (bd_app t₁ t₂) n' s h := by simp*

/--Given a bounded_preterm of bound n and level l, realize it using (v : dvector S n) and (xs : dvector L l) by the following structural induction:

1. Given a free de Bruijn variable &k, replace it with the kth member (indexing starting at 0) of v,

2. given a (bd_func f), replace it with its realization as a function on S, _evaluated_ at xs, and

3. given an application of terms, replace it with a literal application of terms, with the inner term evaluated at xs.
--/

--- note from Mario: replace dvector.nth with dvector.nth''

@[simp] def realize_bounded_term {S : Structure L} {n} (v : dvector S n) :
  ∀{l} (t : bounded_preterm L n l) (xs : dvector S l), S.carrier
| _ &k             xs := v.nth k.1 k.2
| _ (bd_func f)    xs := S.fun_map f xs
| _ (bd_app t₁ t₂) xs := realize_bounded_term t₁ $ realize_bounded_term t₂ ([])::xs

/- S[t ; v] -/
localized "notation S`[`:max t ` ;;; `:95 v`]`:0 := @fol.realize_bounded_term _ S _  v _ t (dvector.nil)" in fol

localized "notation S`[`:max t ` ;;; `:95 v ` ;;; `:90 xs `]`:0 := @fol.realize_bounded_term _ S _  v _ t xs" in fol


@[reducible] def realize_closed_term (S : Structure L) (t : closed_term L) : S :=
realize_bounded_term ([]) t ([])

lemma realize_bounded_term_eq {S : Structure L} {n} {v₁ : dvector S n} {v₂ : ℕ → S}
  (hv : ∀k (hk : k < n), v₁.nth k hk = v₂ k) : ∀{l} (t : bounded_preterm L n l)
  (xs : dvector S l), realize_bounded_term v₁ t xs = realize_term v₂ t.fst xs
| _ &k             xs := hv k.1 k.2
| _ (bd_func f)    xs := by refl
| _ (bd_app t₁ t₂) xs := by dsimp; simp [realize_bounded_term_eq]

lemma realize_bounded_term_irrel' {S : Structure L} {n n'} {v₁ : dvector S n} {v₂ : dvector S n'}
  (h : ∀m (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn')
  {l} (t : bounded_preterm L n l) (t' : bounded_preterm L n' l)
  (ht : t.fst = t'.fst) (xs : dvector S l) :
  realize_bounded_term v₁ t xs = realize_bounded_term v₂ t' xs :=
begin
  induction t; cases t'; injection ht with ht₁ ht₂,
  { simp, cases t'_1 with h1 h2; dsimp at ht₁, subst ht₁, exact h t.val t.2 h2 },
  { subst ht₁, refl },
  { simp [t_ih_t t'_t ht₁, t_ih_s t'_s ht₂] }
end

lemma realize_bounded_term_irrel {S : Structure L} {n} {v₁ : dvector S n}
  (t : bounded_term L n) (t' : closed_term L) (ht : t.fst = t'.fst) (xs : dvector S 0) :
  realize_bounded_term v₁ t xs = realize_closed_term S t' :=
by cases xs; exact realize_bounded_term_irrel'
  (by intros m hm hm'; exfalso; exact not_lt_zero m hm') t t' ht ([])

@[simp] lemma realize_bounded_term_cast_eq_irrel {S : Structure L} {n m l} {h : n = m}
  {v : dvector S m} {t : bounded_preterm L n l} (xs : dvector S l) :
realize_bounded_term v (t.cast_eq h) xs = realize_bounded_term (v.cast h.symm) t xs :=
by {subst h, induction t, refl, refl, simp*}

@[simp] lemma realize_bounded_term_dvector_cast_irrel {S : Structure L} {n m l} {h : n = m}
  {v : dvector S n} {t : bounded_preterm L n l} {xs : dvector S l} :
  realize_bounded_term (v.cast h) (t.cast (le_of_eq h)) xs = realize_bounded_term v t xs :=
by {subst h, simp, refl}

@[simp] def lift_bounded_term_at {n} : ∀{l} (t : bounded_preterm L n l) (n' m : ℕ),
  bounded_preterm L (n + n') l
| _ &k             n' m := if m ≤ k.1 then &(k.add_nat n') else &(k.cast_le $ n.le_add_right n')
| _ (bd_func f)    n' m := bd_func f
| _ (bd_app t₁ t₂) n' m := bd_app (lift_bounded_term_at t₁ n' m) $ lift_bounded_term_at t₂ n' m

localized "notation t ` ↑_' `:90 n ` # `:90 m:90 := fol.lift_bounded_term_at t n m" in fol -- input ↑ with \u or \upa

@[reducible] def lift_bounded_term {n l} (t : bounded_preterm L n l) (n' : ℕ) :
  bounded_preterm L (n + n') l := t ↑_' n' # 0
localized "infix ` ↑_ `:100 := fol.lift_bounded_term" in fol -- input ↑' with \u or \upa

@[reducible, simp] def lift_bounded_term1 {n' l} (t : bounded_preterm L n' l) :
  bounded_preterm L (n'+1) l :=
t ↑_ 1

@[simp] lemma lift_bounded_term_fst {n} : ∀{l} (t : bounded_preterm L n l) (n' m : ℕ),
  (t ↑_' n' # m).fst = t.fst ↑' n' # m
| _ &k             n' m := by by_cases h : m ≤ k; simp [h]; refl
| _ (bd_func f)    n' m := by refl
| _ (bd_app t₁ t₂) n' m := by simp [lift_bounded_term_fst]

-- @[simp] def lift_closed_term_at : ∀{l} (t : closed_preterm L l) (n' m : ℕ),
--   bounded_preterm L n' l
-- | _ &k             n' m := if m ≤ k then _ else &(k.cast_le $ n.le_add_right n')
-- | _ (bd_func f)    n' m := bd_func f
-- | _ (bd_app t₁ t₂) n' m := bd_app (lift_bounded_term_at t₁ n' m) $ lift_bounded_term_at t₂ n' m


-- def lift_bounded_term_at0 {n m l} {t : preterm L l} (ht : bounded_term 0 t) : bounded_term n (t ↑' n # m) :=
-- by have := lift_bounded_term_at n m ht; rw [zero_add] at this; exact this

/-- this is t[s//n] for bounded formulae-/
def subst_bounded_term {n n'} : ∀{l} (t : bounded_preterm L (n+n'+1) l)
  (s : bounded_term L n'), bounded_preterm L (n+n') l
| _ &k             s :=
  if h : k.1 < n then &⟨k.1, lt_of_lt_of_le h $ n.le_add_right n'⟩ else
  if h' : n < k.1 then &⟨k.1-1, (nat.sub_lt_right_iff_lt_add $ one_le_of_lt h').mpr k.2⟩ else
  (s ↑_ n).cast $ le_of_eq $ add_comm n' n
| _ (bd_func f)    s := bd_func f
| _ (bd_app t₁ t₂) s := bd_app (subst_bounded_term t₁ s) (subst_bounded_term t₂ s)

localized "notation t `[`:max s ` //// `:95 n `]`:0 := @_root_.fol.subst_bounded_term _ n _ _ t s" in fol
-- localized "notation t `[`:95 s ` // `:95 n `]`:0 := @fol.subst_bounded_term _ n _ _ t s" in fol
-- localized "notation f `[`:95 s ` // `:95 n `]`:0 := @_root_.fol.subst_bounded_term" in fol

@[simp] lemma subst_bounded_term_var_lt {n n'} (s : bounded_term L n') (k : fin (n+n'+1))
  (h : k.1 < n) : (subst_bounded_term &k s).fst = &k.1 :=
by simp [h, fol.subst_bounded_term]

@[simp] lemma subst_bounded_term_var_gt {n n'} (s : bounded_term L n') (k : fin (n+n'+1))
  (h : n < k.1) : (subst_bounded_term &k s).fst = &(k.1-1) :=
have h' : ¬(k.1 < n), from lt_asymm h,
by simp [h, h', fol.subst_bounded_term]

@[simp] lemma subst_bounded_term_var_eq {n n'} (s : bounded_term L n') (k : fin (n+n'+1))
  (h : k.1 = n) : (subst_bounded_term &k s).fst = s.fst ↑ n :=
have h₂ : ¬(k.1 < n), from λh', lt_irrefl _ $ lt_of_lt_of_le h' $ le_of_eq h.symm,
have h₃ : ¬(n < k.1), from λh', lt_irrefl _ $ lt_of_lt_of_le h' $ le_of_eq h,
by simp [subst_bounded_term, h₂, h₃]

@[simp] lemma subst_bounded_term_bd_app {n n' l} (t₁ : bounded_preterm L (n+n'+1) (l+1))
  (t₂ : bounded_term L (n+n'+1)) (s : bounded_term L n') :
  subst_bounded_term (bd_app t₁ t₂) s = bd_app (subst_bounded_term t₁ s) (subst_bounded_term t₂ s) :=
by refl

@[simp] lemma subst_bounded_term_fst {n n'} : ∀{l} (t : bounded_preterm L (n+n'+1) l)
  (s : bounded_term L n'), (subst_bounded_term t s).fst = t.fst[s.fst//n]
| _ &k             s := by apply decidable.lt_by_cases k n; intro h; simp [h]
| _ (bd_func f)    s := by refl
| _ (bd_app t₁ t₂) s := by simp*

-- @[simp] lemma subst_bounded_term_var_eq' {n n'} (s : bounded_term L n') (h : n < n+n'+1) :
--   (subst_bounded_term &⟨n, h⟩ s).fst = s.fst ↑ n :=
-- by simp [subst_bounded_term]

def subst0_bounded_term {n l} (t : bounded_preterm L (n+1) l)
  (s : bounded_term L n) : bounded_preterm L n l :=
(subst_bounded_term (t.cast_eq $ (n+1).zero_add.symm) s).cast_eq $ n.zero_add

localized "notation t `[`:max s ` /0]`:0 := fol.subst0_bounded_term t s" in fol

@[simp] lemma subst0_bounded_term_fst {n l} (t : bounded_preterm L (n+1) l)
  (s : bounded_term L n) : t[s/0].fst = t.fst[s.fst//0] :=
by simp [subst0_bounded_term]

def substmax_bounded_term {n l} (t : bounded_preterm L (n+1) l)
  (s : closed_term L) : bounded_preterm L n l :=
subst_bounded_term (by exact t) s

@[simp] lemma substmax_bounded_term_bd_app {n l} (t₁ : bounded_preterm L (n+1) (l+1))
  (t₂ : bounded_term L (n+1)) (s : closed_term L) :
  substmax_bounded_term (bd_app t₁ t₂) s =
  bd_app (substmax_bounded_term t₁ s) (substmax_bounded_term t₂ s) :=
by refl

def substmax_eq_subst0_term {l} (t : bounded_preterm L 1 l) (s : closed_term L) :
  t[s/0] = substmax_bounded_term t s :=
by ext; simp [substmax_bounded_term]

def substmax_var_lt {n} (k : fin (n+1)) (s : closed_term L) (h : k.1 < n) :
  substmax_bounded_term &k s = &⟨k.1, h⟩ :=
by ext; simp [substmax_bounded_term, h]

def substmax_var_eq {n} (k : fin (n+1)) (s : closed_term L) (h : k.1 = n) :
  substmax_bounded_term &k s = s.cast0 n :=
begin
  ext, simp [substmax_bounded_term, h],
  dsimp only [lift_term], rw [lift_bounded_term_irrel s _ (le_refl _)]
end

def bounded_term_of_function {l n} (f : L.functions l) :
  arity' (bounded_term L n) (bounded_term L n) l :=
arity'.of_dvector_map $ bd_apps (bd_func f)

@[simp] lemma realize_bounded_term_bd_app {S : Structure L}
  {n l} (t : bounded_preterm L n (l+1)) (s : bounded_term L n) (xs : dvector S n)
  (xs' : dvector S l) :
  realize_bounded_term xs (bd_app t s) xs' =
  realize_bounded_term xs t (realize_bounded_term xs s ([])::xs') :=
by refl

@[simp] lemma realize_closed_term_bd_apps {S : Structure L}
  {l} (t : closed_preterm L l) (ts : dvector (closed_term L) l) :
  realize_closed_term S (bd_apps t ts) =
  realize_bounded_term ([]) t (ts.map (λt', realize_bounded_term ([]) t' ([]))) :=
begin
  induction ts generalizing t, refl, apply ts_ih (bd_app t ts_x)
end
--⟨t.fst[s.fst // n], bounded_term_subst_closed t.snd s.snd⟩

lemma realize_bounded_term_bd_apps {S : Structure L}
  {n l} (xs : dvector S n) (t : bounded_preterm L n l) (ts : dvector (bounded_term L n) l) :
  realize_bounded_term xs (bd_apps t ts) ([]) =
  realize_bounded_term xs t (ts.map (λt, realize_bounded_term xs t ([]))) :=
begin
  induction ts generalizing t, refl, apply ts_ih (bd_app t ts_x)
end

@[simp] lemma realize_cast_bounded_term {S : Structure L} {n m} {h : n ≤ m} {t : bounded_term L n}
  {v : dvector S m} : realize_bounded_term v (t.cast h) dvector.nil =
    realize_bounded_term (v.trunc n h) t dvector.nil :=
begin
  revert t, apply bounded_term.rec,
  {intro k, simp only [dvector.trunc_nth, fol.bounded_preterm.cast, fol.realize_bounded_term,
   dvector.nth, dvector.trunc], refl},
  {simp[realize_bounded_term_bd_apps], intros, congr' 1, apply dvector.map_congr_pmem,
  exact ih_ts}
end

/- When realizing a closed term, we can replace the realizing dvector with [] -/
@[simp] lemma realize_closed_term_v_irrel {S : Structure L} {n} {v : dvector S n}
  {t : bounded_term L 0} :
  realize_bounded_term v (t.cast (by {simp})) ([]) = realize_closed_term S t :=
by simp[realize_cast_bounded_term]


/- this is the same as realize_bounded_term, we should probably have a common generalization of this definition -/
-- @[simp] def substitute_bounded_term {n n'} (v : dvector (bounded_term n') n) :
--   ∀{l} (t : bounded_term L n l, bounded_preterm L n' l
-- | _ _ &k          := v.nth k hk
-- | _ _ (bd_func f)             := bd_func f
-- | _ _ (bd_app t₁ t₂) := bd_app (substitute_bounded_term ht₁) $ substitute_bounded_term ht₂

-- def substitute_bounded_term {n n' l} (t : bounded_preterm L n l)
--   (v : dvector (bounded_term n') n) : bounded_preterm L n' l :=
-- substitute_bounded_term v t.snd

variable (L)
inductive bounded_preformula : ℕ → ℕ → Type u
| bd_falsum {} {n} : bounded_preformula n 0
| bd_equal {n} (t₁ t₂ : bounded_term L n) : bounded_preformula n 0
| bd_rel {n l : ℕ} (R : L.relations l) : bounded_preformula n l
| bd_apprel {n l} (f : bounded_preformula n (l + 1)) (t : bounded_term L n) : bounded_preformula n l
| bd_imp {n} (f₁ f₂ : bounded_preformula n 0) : bounded_preformula n 0
| bd_all {n} (f : bounded_preformula (n+1) 0) : bounded_preformula n 0

export bounded_preformula

@[reducible] def bounded_formula (n : ℕ) := bounded_preformula L n 0
@[reducible] def presentence     (l : ℕ) := bounded_preformula L 0 l
@[reducible] def sentence                := presentence L 0
variable {L}

instance nonempty_bounded_formula (n : ℕ) : nonempty $ bounded_formula L n :=
  nonempty.intro (by constructor)


-- @[reducible, simp] def bd_falsum' {n} : bounded_formula L n := bd_falsum
-- @[reducible, simp] def bd_equal' {n} (t₁ t₂ : bounded_term L n) : bounded_formula L n :=
-- bd_equal t₁ t₂
-- @[reducible, simp] def bd_imp' {n} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
-- bd_imp f₁ f₂
localized "notation `⊥` := fol.bounded_preformula.bd_falsum -- input: \bot" in fol
localized "infix ` ≃ `:88 := fol.bounded_preformula.bd_equal -- input \~- or \simeq" in fol
localized "infixr ` ⟹ `:62 := fol.bounded_preformula.bd_imp -- input \==>" in fol
def bd_not {n} (f : bounded_formula L n) : bounded_formula L n := f ⟹ ⊥
prefix `∼`:max := fol.bd_not -- input \~, the ASCII character ~ has too low precedence
def bd_and {n} (f₁ f₂ : bounded_formula L n) : bounded_formula L n := ∼(f₁ ⟹ ∼f₂)
localized "infixr ` ⊓ ` := fol.bd_and -- input: \sqcap" in fol
def bd_or {n} (f₁ f₂ : bounded_formula L n) : bounded_formula L n := ∼f₁ ⟹ f₂
localized "infixr ` ⊔ ` := fol.bd_or -- input: \sqcup" in fol
def bd_biimp {n} (f₁ f₂ : bounded_formula L n) : bounded_formula L n := (f₁ ⟹ f₂) ⊓ (f₂ ⟹ f₁)
localized "infix ` ⇔ `:61 := fol.bd_biimp -- input \<=>" in fol
prefix `∀'`:110 := fol.bounded_preformula.bd_all
def bd_ex {n} (f : bounded_formula L (n+1)) : bounded_formula L n := ∼ (∀' (∼ f))
prefix `∃'`:110 := fol.bd_ex



def bd_apps_rel : ∀{n l} (f : bounded_preformula L n l) (ts : dvector (bounded_term L n) l),
  bounded_formula L n
| _ _ f []      := f
| _ _ f (t::ts) := bd_apps_rel (bd_apprel f t) ts

@[simp] lemma bd_apps_rel_zero {n} (f : bounded_formula L n) (ts : dvector (bounded_term L n) 0) :
  bd_apps_rel f ts = f :=
by cases ts; refl

namespace bounded_preformula
@[simp] protected def fst : ∀{n l}, bounded_preformula L n l → preformula L l
| _ _ bd_falsum       := ⊥
| _ _ (t₁ ≃ t₂)       := t₁.fst ≃ t₂.fst
| _ _ (bd_rel R)      := rel R
| _ _ (bd_apprel f t) := apprel f.fst t.fst
| _ _ (f₁ ⟹ f₂)      := f₁.fst ⟹ f₂.fst
| _ _ (∀' f)          := ∀' f.fst

@[simp] lemma fst_not {n} {f : bounded_formula L n} :∼(f.fst) = (∼f).fst :=
by refl
@[simp] lemma fst_or {n} {f₁ f₂ : bounded_formula L n} : (f₁ ⊔ f₂).fst = f₁.fst ⊔ f₂.fst :=
by refl
lemma fst_imp {n} {f₁ f₂ : bounded_formula L n} : (f₁ ⟹ f₂).fst = f₁.fst ⟹ f₂.fst :=
by refl
@[simp] lemma fst_and {n} {f₁ f₂ : bounded_formula L n} : (f₁ ⊓ f₂).fst = f₁.fst ⊓ f₂.fst :=
by refl
@[simp] lemma fst_ex {n} {f : bounded_formula L (n+1)} : (∃' f).fst = ∃' f.fst :=
by refl

local attribute [ext] fin.eq_of_veq
@[ext] protected def eq {n l} {f₁ f₂ : bounded_preformula L n l} (h : f₁.fst = f₂.fst) :
  f₁ = f₂ :=
begin
  induction f₁; cases f₂; injection h with h₁ h₂,
  { refl },
  { congr1; apply bounded_preterm.eq; assumption },
  { rw h₁ },
  { congr1, exact f₁_ih h₁, exact bounded_preterm.eq h₂ },
  { congr1, exact f₁_ih_f₁ h₁, exact f₁_ih_f₂ h₂ },
  { rw [f₁_ih h₁] }
end

@[simp] protected def cast : ∀ {n m l} (h : n ≤ m)  (f : bounded_preformula L n l),
  bounded_preformula L m l
| _ _ _ h bd_falsum       := bd_falsum
| _ _ _ h (t₁ ≃ t₂)       := t₁.cast h ≃ t₂.cast h
| _ _ _ h (bd_rel R)      := bd_rel R
| _ _ _ h (bd_apprel f t) := bd_apprel (f.cast h) $ t.cast h
| _ _ _ h (f₁ ⟹ f₂)      := f₁.cast h ⟹ f₂.cast h
| _ _ _ h (∀' f)          := ∀' f.cast (succ_le_succ h)

@[simp] lemma cast_irrel : ∀ {n m l} (h h' : n ≤ m) (f : bounded_preformula L n l),
  (f.cast h) = (f.cast h') :=
by {intros, refl}

@[simp] lemma cast_rfl {n} {h : n ≤ n} : ∀ {l} (f : bounded_preformula L n l), (f.cast h) = f :=
by {intros, induction f; simp*}

protected def cast_eq {n m l} (h : n = m) (f : bounded_preformula L n l) :
  bounded_preformula L m l :=
f.cast $ le_of_eq h

protected def cast_eqr {n m l} (h : n = m) (f : bounded_preformula L m l) :
  bounded_preformula L n l :=
f.cast $ ge_of_eq h

lemma cast_bd_apps_rel {S : Structure L} {n m} {h : n ≤ m} {l} {f : bounded_preformula L n l}
  {ts : dvector (bounded_term L n) l} :
  ((bd_apps_rel f ts).cast h) = bd_apps_rel (f.cast h) (ts.map (λ t, t.cast h)) :=
by {induction ts, refl, apply @ts_ih (bd_apprel f ts_x)}

protected def cast1 {n l} (f : bounded_preformula L n l) : bounded_preformula L (n+1) l :=
f.cast $ n.le_add_right 1

@[simp] lemma cast_fst : ∀ {l n m} (h : n ≤ m) (f : bounded_preformula L n l),
  (f.cast h).fst = f.fst
| _ _ _ h bd_falsum       := by refl
| _ _ _ h (t₁ ≃ t₂)       := by simp
| _ _ _ h (bd_rel R)      := by refl
| _ _ _ h (bd_apprel f t) := by simp*
| _ _ _ h (f₁ ⟹ f₂)      := by simp*
| _ _ _ h (∀' f)          := by simp*

@[simp] lemma cast_eq_fst {l n m} (h : n = m) (f : bounded_preformula L n l) :
  (f.cast_eq h).fst = f.fst := f.cast_fst _
@[simp] lemma cast1_fst {l n} (f : bounded_preformula L n l) :
  f.cast1.fst = f.fst := f.cast_fst _

@[simp] lemma cast_eq_rfl {l n m} (h : n = m) (f : bounded_preformula L n l) :
  (f.cast_eq h).cast_eq h.symm = f := by ext; simp

@[simp] lemma cast_eq_irrel {l n m} (h h' : n = m) (f : bounded_preformula L n l) :
  (f.cast_eq h) = (f.cast_eq h') := by refl

@[simp] lemma cast_eq_all {n m } (h : n = m) {f : bounded_preformula L (n+1) _} :
  (∀' f).cast_eq h = ∀' (f.cast_eq (by {subst h; refl})) := by refl

@[simp] lemma cast_eq_trans {n m o l} {h : n = m} {h' : m = o} {f : bounded_preformula L n l} :
  (f.cast_eq h).cast_eq h' = f.cast_eq (eq.trans h h') := by substs h h'; ext; simp

lemma cast_eq_hrfl {n m l} {h : n = m} {f : bounded_preformula L n l} : f.cast_eq h == f :=
by {subst h, simp only [heq_iff_eq], ext, simp}

/- A bounded_preformula is qf if the underlying preformula is qf -/
def quantifier_free {l n} : bounded_preformula L n l → Prop := λ f, fol.quantifier_free f.fst

end bounded_preformula

namespace presentence

@[reducible]protected def cast0 {l} (n) (f : presentence L l) : bounded_preformula L n l :=
f.cast n.zero_le

@[simp] lemma cast0_fst {l} (n) (f : presentence L l) :
  (f.cast0 n).fst = f.fst := f.cast_fst _

end presentence

lemma lift_bounded_formula_irrel : ∀{n l} (f : bounded_preformula L n l) (n') {m : ℕ}
  (h : n ≤ m), f.fst ↑' n' # m = f.fst
| _ _ bd_falsum       n' m h := by refl
| _ _ (t₁ ≃ t₂)       n' m h := by simp [lift_bounded_term_irrel _ _ h]
| _ _ (bd_rel R)      n' m h := by refl
| _ _ (bd_apprel f t) n' m h := by simp [*, lift_bounded_term_irrel _ _ h]
| _ _ (f₁ ⟹ f₂)      n' m h := by simp*
| _ _ (∀' f)          n' m h := by simp*

lemma lift_sentence_irrel (f : sentence L) : f.fst ↑ 1 = f.fst :=
lift_bounded_formula_irrel f 1 $ le_refl 0

@[simp] lemma subst_bounded_formula_irrel : ∀{n l} (f : bounded_preformula L n l) {n'} (s : term L)
  (h : n ≤ n'), f.fst[s // n'] = f.fst
| _ _ bd_falsum       n' s h := by refl
| _ _ (t₁ ≃ t₂)       n' s h := by simp [subst_bounded_term_irrel _ s h]
| _ _ (bd_rel R)      n' s h := by refl
| _ _ (bd_apprel f t) n' s h := by simp [*, subst_bounded_term_irrel _ s h]
| _ _ (f₁ ⟹ f₂)      n' s h := by simp*
| _ _ (∀' f)          n' s h := by simp*

lemma subst_sentence_irrel (f : sentence L) (n) (s : term L) : f.fst[s // n] = f.fst :=
subst_bounded_formula_irrel f s n.zero_le



@[simp] def realize_bounded_formula {S : Structure L} :
  ∀{n l} (v : dvector S n) (f : bounded_preformula L n l) (xs : dvector S l), Prop
| _ _ v bd_falsum       xs := false
| _ _ v (t₁ ≃ t₂)       xs := realize_bounded_term v t₁ xs = realize_bounded_term v t₂ xs
| _ _ v (bd_rel R)      xs := S.rel_map R xs
| _ _ v (bd_apprel f t) xs := realize_bounded_formula v f $ realize_bounded_term v t ([])::xs
| _ _ v (f₁ ⟹ f₂)      xs := realize_bounded_formula v f₁ xs → realize_bounded_formula v f₂ xs
| _ _ v (∀' f)          xs := ∀(x : S), realize_bounded_formula (x::v) f xs

localized "notation S`[`:95 f ` ;; `:95 v ` ;; `:90 xs `]`:0 := @fol.realize_bounded_formula _ S _ _ v f xs" in fol
localized "notation S`[`:95 f ` ;; `:95 v `]`:0 := @fol.realize_bounded_formula _ S _ 0 v f (dvector.nil)" in fol


@[reducible] def realize_sentence (S : Structure L) (f : sentence L) : Prop :=
realize_bounded_formula ([] : dvector S 0) f ([])

localized "notation S`[`:max f `]`:0 := fol.realize_sentence S f" in fol

lemma realize_bounded_formula_iff {S : Structure L} : ∀{n} {v₁ : dvector S n} {v₂ : ℕ → S}
  (hv : ∀k (hk : k < n), v₁.nth k hk = v₂ k) {l} (t : bounded_preformula L n l)
  (xs : dvector S l), realize_bounded_formula v₁ t xs ↔ realize_formula v₂ t.fst xs
| _ _ _ hv _ bd_falsum       xs := by refl
| _ _ _ hv _ (t₁ ≃ t₂)       xs := by apply eq.congr; apply realize_bounded_term_eq hv
| _ _ _ hv _ (bd_rel R)      xs := by refl
| _ _ _ hv _ (bd_apprel f t) xs :=
  by simp [realize_bounded_term_eq hv, realize_bounded_formula_iff hv]
| _ _ _ hv _ (f₁ ⟹ f₂)      xs :=
  by simp [realize_bounded_formula_iff hv]
| _ _ _ hv _ (∀' f)          xs :=
  begin
    apply forall_congr, intro x, apply realize_bounded_formula_iff,
    intros k hk, cases k, refl, apply hv
  end

lemma realize_bounded_formula_iff_of_fst {S : Structure L} : ∀{n} {v₁ w₁ : dvector S n}
  {v₂ w₂ : ℕ → S} (hv₁ : ∀ k (hk : k < n), v₁.nth k hk = v₂ k)
  (hw₁ : ∀ k (hk : k < n), w₁.nth k hk = w₂ k) {l₁ l₂}
  (t₁ : bounded_preformula L n l₁) (t₂ : bounded_preformula L n l₂) (xs₁ : dvector S l₁)
  (xs₂ : dvector S l₂) (H : realize_formula v₂ t₁.fst xs₁ ↔ realize_formula w₂ t₂.fst xs₂),
  (realize_bounded_formula v₁ t₁ xs₁ ↔ realize_bounded_formula w₁ t₂ xs₂) :=
 by intros; simpa[realize_bounded_formula_iff hv₁ t₁, realize_bounded_formula_iff hw₁ t₂]

@[simp] def lift_bounded_formula_at : ∀{n l} (f : bounded_preformula L n l) (n' m : ℕ),
  bounded_preformula L (n + n') l
| _ _ bd_falsum       n' m := ⊥
| _ _ (t₁ ≃ t₂)       n' m := t₁ ↑' n' # m ≃ t₂ ↑' n' # m
| _ _ (bd_rel R)      n' m := bd_rel R
| _ _ (bd_apprel f t) n' m := bd_apprel (lift_bounded_formula_at f n' m) $ t ↑' n' # m
| _ _ (f₁ ⟹ f₂)      n' m := lift_bounded_formula_at f₁ n' m ⟹ lift_bounded_formula_at f₂ n' m
| _ _ (∀' f)          n' m := ∀' (lift_bounded_formula_at f n' (m+1)).cast (le_of_eq $ succ_add _ _)

localized "notation f ` ↑' `:90 n ` # `:90 m:90 := fol.lift_bounded_formula_at f n m -- input ↑ with \u or \upa" in fol

@[reducible] def lift_bounded_formula {n l} (f : bounded_preformula L n l) (n' : ℕ) :
  bounded_preformula L (n + n') l := f ↑' n' # 0
localized "infix ` ↑ `:100 := fol.lift_bounded_formula -- input ↑' with \u or \upa" in fol

@[reducible, simp] def lift_bounded_formula1 {n' l} (f : bounded_preformula L n' l) :
  bounded_preformula L (n'+1) l :=
f ↑ 1

@[simp] lemma lift_bounded_formula_fst : ∀{n l} (f : bounded_preformula L n l) (n' m : ℕ),
  (f ↑' n' # m).fst = f.fst ↑' n' # m
| _ _ bd_falsum       n' m := by refl
| _ _ (t₁ ≃ t₂)       n' m := by simp
| _ _ (bd_rel R)      n' m := by refl
| _ _ (bd_apprel f t) n' m := by simp*
| _ _ (f₁ ⟹ f₂)      n' m := by simp*
| _ _ (∀' f)          n' m := by simp*

def formula_below {n n' l} (f : bounded_preformula L (n+n'+1) l)
  (s : bounded_term L n') : bounded_preformula L (n+n') l :=
begin
  have : {f' : preformula L l // f.fst = f' } := ⟨f.fst, rfl⟩,
  cases this with f' pf, induction f' generalizing n; cases f; injection pf with pf₁ pf₂,
  { exact ⊥ },
  { exact subst_bounded_term f_t₁ s ≃ subst_bounded_term f_t₂ s },
  { exact bd_rel f_R },
  { exact bd_apprel (f'_ih f_f pf₁) (subst_bounded_term f_t s) },
  { exact f'_ih_f₁ f_f₁ pf₁ ⟹ f'_ih_f₂ f_f₂ pf₂ },
  { refine ∀' (f'_ih (f_f.cast_eq $ congr_arg succ $ (succ_add n n').symm) $
      (f_f.cast_eq_fst _).trans pf₁).cast_eq (succ_add n n') }
end

/- f[s//n] for bounded_formula, requiring an extra proof that (n+n'+1 = n'') -/
@[simp] def subst_bounded_formula : ∀{n n' n'' l} (f : bounded_preformula L n'' l)
  (s : bounded_term L n') (h : n+n'+1 = n''), bounded_preformula L (n+n') l
| _ _ _ _ bd_falsum       s rfl := ⊥
| _ _ _ _ (t₁ ≃ t₂)       s rfl := subst_bounded_term t₁ s ≃ subst_bounded_term t₂ s
| _ _ _ _ (bd_rel R)      s rfl := bd_rel R
| _ _ _ _ (bd_apprel f t) s rfl := bd_apprel (subst_bounded_formula f s rfl) (subst_bounded_term t s)
| _ _ _ _ (f₁ ⟹ f₂)      s rfl := subst_bounded_formula f₁ s rfl ⟹ subst_bounded_formula f₂ s rfl
| _ _ _ _ (∀' f)          s rfl :=
  ∀' (subst_bounded_formula f s $ by simp [succ_add]).cast_eq (succ_add _ _)

localized "notation f `[`:95 s ` // `:95 n ` // `:95 h `]`:0 := @fol.subst_bounded_formula _ n _ _ _ f s h" in fol

@[simp] def subst_bounded_formula_fst : ∀{n n' n'' l} (f : bounded_preformula L n'' l)
  (s : bounded_term L n') (h : n+n'+1 = n''),
  (subst_bounded_formula f s h).fst = f.fst[s.fst//n]
| _ _ _ _ bd_falsum       s rfl := by refl
| _ _ _ _ (t₁ ≃ t₂)       s rfl := by simp
| _ _ _ _ (bd_rel R)      s rfl := by refl
| _ _ _ _ (bd_apprel f t) s rfl := by simp*
| _ _ _ _ (f₁ ⟹ f₂)      s rfl := by simp*
| _ _ _ _ (∀' f)          s rfl := by simp*

lemma realize_bounded_formula_irrel' {S : Structure L} {n n'} {v₁ : dvector S n} {v₂ : dvector S n'}
  (h : ∀m (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn')
  {l} (f : bounded_preformula L n l) (f' : bounded_preformula L n' l)
  (hf : f.fst = f'.fst) (xs : dvector S l) :
  realize_bounded_formula v₁ f xs ↔ realize_bounded_formula v₂ f' xs :=
begin
  induction f generalizing n'; cases f'; injection hf with hf₁ hf₂,
  { refl },
  { simp [realize_bounded_term_irrel' h f_t₁ f'_t₁ hf₁,
          realize_bounded_term_irrel' h f_t₂ f'_t₂ hf₂] },
  { rw [hf₁], refl },
  { simp [realize_bounded_term_irrel' h f_t f'_t hf₂, f_ih _ h f'_f hf₁] },
  { apply imp_congr, apply f_ih_f₁ _ h _ hf₁, apply f_ih_f₂ _ h _ hf₂ },
  { apply forall_congr, intro x, apply f_ih _ _ _ hf₁, intros,
    cases m, refl, apply h }
end

lemma realize_bounded_formula_irrel {S : Structure L} {n} {v₁ : dvector S n}
  (f : bounded_formula L n) (f' : sentence L) (hf : f.fst = f'.fst) (xs : dvector S 0) :
  realize_bounded_formula v₁ f xs ↔ realize_sentence S f' :=
by cases xs; exact realize_bounded_formula_irrel'
  (by intros m hm hm'; exfalso; exact not_lt_zero m hm') f f' hf ([])

@[simp] lemma realize_bounded_formula_cast_eq_irrel {S : Structure L} {n m l} {h : n = m}
  {v : dvector S m} {f : bounded_preformula L n l} {xs : dvector S l} :
realize_bounded_formula v (f.cast_eq h) xs = realize_bounded_formula (v.cast h.symm) f xs :=
  by subst h; induction f; unfold bounded_preformula.cast_eq; finish

def bounded_formula_of_relation {l n} (f : L.relations l) :
  arity' (bounded_term L n) (bounded_formula L n) l :=
arity'.of_dvector_map $ bd_apps_rel (bd_rel f)

@[elab_as_eliminator] def bounded_preformula.rec1 {C : Πn l, bounded_preformula L (n+1) l → Sort v}
  (H0 : Π {n}, C n 0 ⊥)
  (H1 : Π {n} (t₁ t₂ : bounded_term L (n+1)), C n 0 (t₁ ≃ t₂))
  (H2 : Π {n l : ℕ} (R : L.relations l), C n l (bd_rel R))
  (H3 : Π {n l : ℕ} (f : bounded_preformula L (n+1) (l + 1)) (t : bounded_term L (n+1))
    (ih : C n (l + 1) f), C n l (bd_apprel f t))
  (H4 : Π {n} (f₁ f₂ : bounded_formula L (n+1)) (ih₁ : C n 0 f₁) (ih₂ : C n 0 f₂), C n 0 (f₁ ⟹ f₂))
  (H5 : Π {n} (f : bounded_formula L (n+2)) (ih : C (n+1) 0 f), C n 0 (∀' f)) :
  ∀{{n l : ℕ}} (f : bounded_preformula L (n+1) l), C n l f :=
let C' : Πn l, bounded_preformula L n l → Sort v :=
λn, match n with
| 0     := λ l f, punit
| (k+1) := C k
end in
begin
  have : ∀{{n l}} (f : bounded_preformula L n l), C' n l f,
  { intros n l,
    refine bounded_preformula.rec _ _ _ _ _ _; clear n l; intros; cases n; try {exact punit.star},
    apply H0, apply H1, apply H2, apply H3 _ _ ih, apply H4 _ _ ih_f₁ ih_f₂, apply H5 _ ih },
  intros n l f, apply this f
end

@[elab_as_eliminator] def bounded_formula.rec1 {C : Πn, bounded_formula L (n+1) → Sort v}
  (hfalsum : Π {n}, C n ⊥)
  (hequal : Π {n} (t₁ t₂ : bounded_term L (n+1)), C n (t₁ ≃ t₂))
  (hrel : Π {n l : ℕ} (R : L.relations l) (ts : dvector (bounded_term L (n+1)) l),
    C n (bd_apps_rel (bd_rel R) ts))
  (himp : Π {n} {f₁ f₂ : bounded_formula L (n+1)} (ih₁ : C n f₁) (ih₂ : C n f₂), C n (f₁ ⟹ f₂))
  (hall : Π {n} {f : bounded_formula L (n+2)} (ih : C (n+1) f), C n (∀' f))
  {{n : ℕ}} (f : bounded_formula L (n+1)) : C n f :=
have h : ∀{n l} (f : bounded_preformula L (n+1) l) (ts : dvector (bounded_term L (n+1)) l),
  C n (bd_apps_rel f ts),
begin
  refine bounded_preformula.rec1 _ _ _ _ _ _; intros; try {rw ts.zero_eq},
  apply hfalsum, apply hequal, apply hrel, apply ih (t::ts),
  exact himp (ih₁ ([])) (ih₂ ([])), exact hall (ih ([]))
end,
h f ([])

@[elab_as_eliminator] def bounded_formula.rec {C : Πn, bounded_formula L n → Sort v}
  (hfalsum : Π {n}, C n ⊥)
  (hequal : Π {n} (t₁ t₂ : bounded_term L n), C n (t₁ ≃ t₂))
  (hrel : Π {n l : ℕ} (R : L.relations l) (ts : dvector (bounded_term L n) l),
    C n (bd_apps_rel (bd_rel R) ts))
  (himp : Π {n} {f₁ f₂ : bounded_formula L n} (ih₁ : C n f₁) (ih₂ : C n f₂), C n (f₁ ⟹ f₂))
  (hall : Π {n} {f : bounded_formula L (n+1)} (ih : C (n+1) f), C n (∀' f)) :
  ∀{{n : ℕ}} (f : bounded_formula L n), C n f :=
have h : ∀{n l} (f : bounded_preformula L n l) (ts : dvector (bounded_term L n) l),
  C n (bd_apps_rel f ts),
begin
  intros, induction f; try {rw ts.zero_eq},
  apply hfalsum, apply hequal, apply hrel, apply f_ih (f_t::ts),
  exact himp (f_ih_f₁ ([])) (f_ih_f₂ ([])), exact hall (f_ih ([]))
end,
λn f, h f ([])

@[simp] def substmax_bounded_formula {n l} (f : bounded_preformula L (n+1) l) (s : closed_term L) :
  bounded_preformula L n l :=
by apply subst_bounded_formula f s rfl

@[simp] lemma substmax_bounded_formula_fst {n l} (f : bounded_preformula L (n+1) l) (s : closed_term L) : (substmax_bounded_formula f s).fst = f.fst[s.fst//n] :=
by simp [substmax_bounded_formula]

-- @[simp] lemma substmax_bounded_formula_bd_falsum {n} (s : closed_term L) :
--   substmax_bounded_formula (⊥ : bounded_formula L (n+1)) s = ⊥ := by refl
-- @[simp] lemma substmax_bounded_formula_bd_rel {n l} (R : L.relations l) (s : closed_term L) :
--   substmax_bounded_formula (bd_rel R : bounded_preformula L (n+1) l) s = bd_rel R := by refl
-- @[simp] lemma substmax_bounded_formula_bd_apprel {n l} (f : bounded_preformula L (n+1) (l+1))
--   (t : bounded_term L (n+1)) (s : closed_term L) :
--   substmax_bounded_formula (bd_apprel f t) s =
--   bd_apprel (substmax_bounded_formula f s) (substmax_bounded_term t s) := by refl
-- @[simp] lemma substmax_bounded_formula_bd_imp {n} (f₁ f₂ : bounded_formula L (n+1))
--   (s : closed_term L) :
--   substmax_bounded_formula (f₁ ⟹ f₂) s =
--   substmax_bounded_formula f₁ s ⟹ substmax_bounded_formula f₂ s := by refl
@[simp] lemma substmax_bounded_formula_bd_all {n} (f : bounded_formula L (n+2))
  (s : closed_term L) :
  substmax_bounded_formula (∀' f) s = ∀' substmax_bounded_formula f s := by ext; simp

lemma substmax_bounded_formula_bd_apps_rel {n l} (f : bounded_preformula L (n+1) l)
  (t : closed_term L) (ts : dvector (bounded_term L (n+1)) l) :
  substmax_bounded_formula (bd_apps_rel f ts) t =
  bd_apps_rel (substmax_bounded_formula f t) (ts.map $ λt', substmax_bounded_term t' t) :=
begin
  induction ts generalizing f, refl, apply ts_ih (bd_apprel f ts_x)
end

def subst0_bounded_formula {n l} (f : bounded_preformula L (n+1) l) (s : bounded_term L n) :
  bounded_preformula L n l :=
(subst_bounded_formula f s $ zero_add (n+1)).cast_eq $ zero_add n

localized "notation f `[`:max s ` /0]`:0 := fol.subst0_bounded_formula f s" in fol

@[simp] lemma subst0_bounded_formula_fst {n l} (f : bounded_preformula L (n+1) l)
  (s : bounded_term L n) : (subst0_bounded_formula f s).fst = f.fst[s.fst//0] :=
by simp [subst0_bounded_formula]

def substmax_eq_subst0_formula {l} (f : bounded_preformula L 1 l) (t : closed_term L) :
  f[t/0] = substmax_bounded_formula f t :=
by ext; simp [substmax_bounded_formula]


-- def subst0_sentence {n l} (f : bounded_preformula L (n+1) l) (t : closed_term L) :
--   bounded_preformula L n l :=
-- f [bounded_term_of_closed_term t/0]


localized "infix ` ⊨ `:51 := fol.realize_sentence -- input using \|= or \vDash, but not using \models" in fol

@[simp] lemma realize_sentence_false {S : Structure L} : S ⊨ (⊥ : sentence L) ↔ false :=
by refl

@[simp] lemma false_of_satisfied_false {S : Structure L} :  (S ⊨ (⊥ : sentence L)) → false
:= by simp only [realize_sentence_false, imp_self]

@[simp] lemma realize_sentence_imp {S : Structure L} {f₁ f₂ : sentence L} :
  S ⊨ f₁ ⟹ f₂ ↔ (S ⊨ f₁ → S ⊨ f₂) :=
by refl

@[simp] lemma realize_sentence_not {S : Structure L} {f : sentence L} : S ⊨ ∼f ↔ ¬ S ⊨ f :=
by refl

@[simp] lemma realize_sentence_dne {S : Structure L} {f : sentence L} : S ⊨ ∼∼f ↔ S ⊨ f :=
begin
  refine ⟨by apply classical.by_contradiction, _⟩, finish
end

@[simp] lemma realize_sentence_all {S : Structure L} {f : bounded_formula L 1} :
  (S ⊨ ∀'f) ↔ ∀ x : S, realize_bounded_formula([x]) f([]) :=
by refl

@[simp] lemma realize_bounded_formula_imp {L} {S : Structure L} : ∀{n} {v : dvector S n}
  {f g : bounded_formula L n}, realize_bounded_formula v (f ⟹ g) dvector.nil ↔
  (realize_bounded_formula v f dvector.nil -> realize_bounded_formula v g dvector.nil) :=
by finish

@[simp] lemma realize_bounded_formula_and {L} {S : Structure L} : ∀{n} {v : dvector S n}
  {f g : bounded_formula L n}, realize_bounded_formula v (f ⊓ g) dvector.nil ↔
  (realize_bounded_formula v f dvector.nil ∧ realize_bounded_formula v g dvector.nil) :=
begin
    intros,
    have : realize_bounded_formula v f dvector.nil ∧ realize_bounded_formula v g dvector.nil ↔
      ¬(realize_bounded_formula v f dvector.nil → ¬ (realize_bounded_formula v g dvector.nil)),
    by finish, rw[this], refl
end

@[simp] lemma realize_bounded_formula_not {L} {S : Structure L} : ∀{n} {v : dvector S n}
  {f : bounded_formula L n},
  realize_bounded_formula v ∼f dvector.nil ↔ ¬(realize_bounded_formula v f dvector.nil) :=
by {intros, refl}

@[simp] def realize_bounded_formula_ex {L} {S : Structure L} : ∀ {n} {v : dvector S n}
  {f : bounded_formula L (n+1)}, realize_bounded_formula v (∃' f) dvector.nil ↔
    ∃ x, realize_bounded_formula (x::v) f dvector.nil :=
by {intros, unfold bd_ex, simp [realize_bounded_formula_not], finish}

@[simp] lemma realize_sentence_ex {S : Structure L} {f : bounded_formula L 1} :
  S ⊨ ∃' f ↔ ∃ x : S, realize_bounded_formula ([x]) f([]) :=
by {unfold realize_sentence, apply realize_bounded_formula_ex}

@[simp] lemma realize_sentence_and {S : Structure L} {f₁ f₂ : sentence L} :
  S ⊨ f₁ ⊓ f₂ ↔ (S ⊨ f₁ ∧ S ⊨ f₂) :=
    by apply realize_bounded_formula_and

@[simp] lemma realize_bounded_formula_biimp {L} {S : Structure L} : ∀{n} {v : dvector S n}
  {f g : bounded_formula L n}, realize_bounded_formula v (f ⇔ g) dvector.nil ↔
    (realize_bounded_formula v f dvector.nil ↔ realize_bounded_formula v g dvector.nil) :=
by {unfold bd_biimp, tidy}

@[simp] lemma realize_sentence_biimp {S : Structure L} {f₁ f₂ : sentence L} :
  S ⊨ f₁ ⇔ f₂ ↔ (S ⊨ f₁ ↔ S ⊨ f₂) := by apply realize_bounded_formula_biimp

lemma realize_bounded_formula_bd_apps_rel {S : Structure L}
  {n l} (xs : dvector S n) (f : bounded_preformula L n l) (ts : dvector (bounded_term L n) l) :
  realize_bounded_formula xs (bd_apps_rel f ts) ([]) ↔
  realize_bounded_formula xs f (ts.map (λt, realize_bounded_term xs t ([]))) :=
begin
  induction ts generalizing f, refl, apply ts_ih (bd_apprel f ts_x)
end

@[simp] lemma realize_cast_bounded_formula {S : Structure L} {n m} {h : n ≤ m}
  {f : bounded_formula L n} {v : dvector S m} :
  realize_bounded_formula v (f.cast h) dvector.nil =
  realize_bounded_formula (v.trunc n h) f dvector.nil :=
begin
  by_cases n = m,
    by subst h; simp,
    have : n < m, by apply nat.lt_of_le_and_ne; repeat{assumption},
    ext, apply realize_bounded_formula_irrel',
    {intros, simp},
    {simp}
end

lemma realize_sentence_bd_apps_rel' {S : Structure L}
  {l} (f : presentence L l) (ts : dvector (closed_term L) l) :
  S ⊨ bd_apps_rel f ts ↔ realize_bounded_formula ([]) f (ts.map $ realize_closed_term S) :=
realize_bounded_formula_bd_apps_rel ([]) f ts

lemma realize_bd_apps_rel {S : Structure L}
  {l} (R : L.relations l) (ts : dvector (closed_term L) l) :
  S ⊨ bd_apps_rel (bd_rel R) ts ↔ S.rel_map R (ts.map $ realize_closed_term S) :=
by apply realize_bounded_formula_bd_apps_rel ([]) (bd_rel R) ts

lemma realize_sentence_equal {S : Structure L} (t₁ t₂ : closed_term L) :
  S ⊨ t₁ ≃ t₂ ↔ realize_closed_term S t₁ = realize_closed_term S t₂  :=
by refl

lemma realize_sentence_iff {S : Structure L} (v : ℕ → S) (f : sentence L) :
  realize_sentence S f ↔ realize_formula v f.fst ([]) :=
realize_bounded_formula_iff (λk hk, by exfalso; exact not_lt_zero k hk) f _

lemma realize_sentence_of_satisfied_in {S : Structure L} [HS : nonempty S] {f : sentence L}
  (H : S ⊨ f.fst) : S ⊨ f :=
begin unfreezeI, induction HS with x, exact (realize_sentence_iff (λn, x) f).mpr (H _) end

lemma satisfied_in_of_realize_sentence {S : Structure L} {f : sentence L} (H : S ⊨ f) : S ⊨ f.fst :=
λv, (realize_sentence_iff v f).mp H

lemma realize_sentence_iff_satisfied_in {S : Structure L} [HS : nonempty S] {f : sentence L} :
  S ⊨ f ↔ S ⊨ f.fst  :=
⟨satisfied_in_of_realize_sentence, realize_sentence_of_satisfied_in⟩

def dvector_var_lift {m : ℕ} : ∀ {n : ℕ} (v : dvector (fin m) n), dvector (fin (m+1)) n
| _ [] := []
| _ (x::xs) := (⟨x.val+1, by{apply nat.succ_lt_succ, exact x.is_lt}⟩) :: (dvector_var_lift xs)

def dvector_lift_var { m : ℕ} : ∀ {n : ℕ} (v : dvector (fin m) n), dvector (fin (m+1)) (n+1) :=
λ n v, ⟨0, nat.zero_lt_succ(m)⟩ :: (dvector_var_lift v)

def subst_var_bounded_term {n m : ℕ} : ∀ {l : ℕ}, bounded_preterm L n l → dvector (fin m) n →
  bounded_preterm L m l
| _ (&k) v := &(dvector.nth v (k.val) k.is_lt)
| _ (bd_func f) v := bd_func f
| _ (bd_app t s) v := bd_app (subst_var_bounded_term t v) (subst_var_bounded_term s v)

/-What are eqn_compiler lemmas and why don't they generate for this defn? Need to fix this to use defn for simp-/
set_option eqn_compiler.lemmas false
def subst_var_bounded_formula: ∀ {l n m: ℕ}, bounded_preformula L n l → dvector (fin (m)) n →
  bounded_preformula L (m) l
| _ _ _ bd_falsum _ := bd_falsum
| _ _ _ (t₁ ≃ t₂) v := (subst_var_bounded_term t₁ v) ≃ (subst_var_bounded_term t₁ v)
| _ _ _ (bd_rel R) _ := bd_rel R
| _ _ _ (bd_apprel f t) v := bd_apprel (subst_var_bounded_formula f v) (subst_var_bounded_term t v)
| _ _ _ (f₁ ⟹ f₂) v := (subst_var_bounded_formula f₁ v) ⟹ (subst_var_bounded_formula f₂ v)
| _ _ _ (∀' f) v := ∀' (subst_var_bounded_formula f (dvector_lift_var v))
set_option eqn_compiler.lemmas true

localized "infix ` ⊚ `:50 := subst_var_bounded_formula --type with \oo" in fol

/- theories -/

variable (L)
@[reducible] def Theory := set $ sentence L
variable {L}

@[reducible] def Theory.fst (T : Theory L) : set (formula L) := bounded_preformula.fst '' T

lemma lift_Theory_irrel (T : Theory L) : (lift_formula1 '' Theory.fst T) = Theory.fst T :=
by rw[image_image, image_congr' lift_sentence_irrel]

def sprf (T : Theory L) (f : sentence L) := T.fst ⊢ f.fst
localized "infix ` ⊢ `:51 := fol.sprf -- input: \|- or \vdash" in fol

def sprovable (T : Theory L) (f : sentence L) := T.fst ⊢' f.fst
localized "infix ` ⊢' `:51 := fol.sprovable -- input: \|- or \vdash" in fol

def saxm {T : Theory L} {A : sentence L} (H : A ∈ T) : T ⊢ A :=
by apply axm; apply mem_image_of_mem _ H

def saxm1 {T : Theory L} {A : sentence L} : insert A T ⊢ A := by apply saxm; left; refl
def saxm2 {T : Theory L} {A B : sentence L} : insert A (insert B T) ⊢ B :=
by apply saxm; right; left; refl

def simpI {T : Theory L} {A B : sentence L} (H : insert A T ⊢ B) : T ⊢ A ⟹ B :=
begin
  apply impI, simp[sprf, Theory.fst, image_insert_eq] at H, assumption
end

lemma simpI' {T : Theory L} {A B : sentence L} (H : insert A T ⊢' B) : T ⊢' A ⟹ B :=
  H.map simpI

def simpE {T : Theory L} (A : sentence L) {B : sentence L} (H₁ : T ⊢ A ⟹ B) (H₂ : T ⊢ A) :
  T ⊢ B :=
by apply impE A.fst H₁ H₂

def sfalsumE {T : Theory L} {A : sentence L} (H : insert ∼A T ⊢ bd_falsum) : T ⊢ A :=
by { apply falsumE, simp[sprf, Theory.fst, image_insert_eq] at H, assumption }

def snotI {T : Theory L} {A : sentence L} (H : T ⊢ A ⟹ bd_falsum) : T ⊢ ∼A :=
by { apply notI, simp[sprf, Theory.fst, image_insert_eq] at H, assumption }

def sandI {T : Theory L} {A B : sentence L} (H1 : T ⊢ A) (H2 : T ⊢ B) : T ⊢ A ⊓ B :=
by exact andI H1 H2

lemma sandI' {T : Theory L} {A B : sentence L} (H1 : T ⊢' A) (H2 : T ⊢' B) : T ⊢' A ⊓ B :=
begin
  apply @nonempty.map ((T ⊢ A) × (T ⊢ B)) (T ⊢ A ⊓ B),
  intro H, cases H, apply sandI, repeat{assumption},
  simp only [nonempty_prod], apply and.intro, exact H1, exact H2
end

def snot_and_self {T : Theory L} {A : sentence L} (H : T ⊢ A ⊓ ∼ A) : T ⊢ bd_falsum :=
by exact not_and_self H

lemma snot_and_self' {T : Theory L} {A : sentence L} (H : T ⊢' A ⊓ ∼A) : T ⊢' bd_falsum :=
by { apply nonempty.map _ H, apply snot_and_self }

lemma snot_and_self'' {T : Theory L} {A : sentence L} (H₁ : T ⊢' A) (H₂ : T ⊢' ∼A) :
  T ⊢' bd_falsum := snot_and_self' $ sandI' H₁ H₂

lemma sprf_by_cases {Γ} (f₁) {f₂ : sentence L} (H₁ : insert f₁ Γ ⊢' f₂)
  (H₂ : insert ∼f₁ Γ ⊢' f₂) : Γ ⊢' f₂ :=
begin
  simp [sprovable, Theory.fst, set.image_insert_eq] at H₁ H₂,
  exact prf_by_cases f₁.fst H₁ H₂
end

def double_negation_elim {L} {T : Theory L} {f : sentence L} : T ⊢ ∼∼f → T ⊢ f :=
begin
  intro, apply falsumE, apply impE, show preformula L 0, by exact f.fst,
  apply deduction, apply impI, apply axm1, apply exfalso, exact deduction a
end

@[simp] lemma double_negation_elim' {L} {T : Theory L} {f : sentence L} : T ⊢' ∼∼f ↔ T ⊢' f :=
begin
  apply nonempty.iff, exact double_negation_elim, intro P, apply impI,
  apply @not_and_self _ _ f.fst, apply andI, exact weakening1 P,
  apply axm, simp
end

def sweakening {T T' : Theory L} (h_sub : T' ⊆ T) {ψ : sentence L} (h : T' ⊢ ψ) : T ⊢ ψ :=
weakening (image_subset _ h_sub) h

def sweakening1 {T : Theory L} {ψ₁ ψ₂ : sentence L} (h : T ⊢ ψ₂) : insert ψ₁ T ⊢ ψ₂ :=
sweakening (subset_insert ψ₁ T) h

def sweakening2 {T : Theory L} {ψ₁ ψ₂ ψ₃ : sentence L} (h : insert ψ₁ T ⊢ ψ₃) :
  insert ψ₁ (insert ψ₂ T) ⊢ ψ₃ :=
sweakening (insert_subset_insert (subset_insert _ T)) h

def sprovable_of_provable {T : Theory L} {f : sentence L} (h : T.fst ⊢ f.fst) : T ⊢ f := h
def provable_of_sprovable {T : Theory L} {f : sentence L} (h : T ⊢ f) : T.fst ⊢ f.fst := h
def sprovable_of_sprf {T : Theory L} {f : sentence L} (h : T ⊢ f) : T ⊢' f := ⟨h⟩
def sprovable.elim {P : Prop} {T : Theory L} {f : sentence L} (ih : T ⊢ f → P) (h : T ⊢' f) : P :=
by unfreezeI; cases h with h; exact ih h

-- def sprovable_of_sprovable_lift_at {T : Theory L} (n m : ℕ) {f : formula L} (h : T.fst ⊢ f ↑' n # m) :
--   T.fst ⊢ f :=
-- sorry

-- def sprovable_of_sprovable_lift {T : Theory L} {f : formula L} (h : T.fst ⊢ f ↑ 1) : T.fst ⊢ f :=
-- sprovable_of_sprovable_lift_at 1 0 h

def sprovable_lift {T : Theory L} {f : formula L} (h : T.fst ⊢ f) : T.fst ⊢ f ↑ 1 :=
begin
  have := prf_lift 1 0 h, dsimp [Theory.fst] at this,
  rw [image_image, image_congr' lift_sentence_irrel] at this, exact this
end

def all_sprovable (T T' : Theory L) := ∀(f ∈ T'), T ⊢ f
localized "infix ` ⊢ `:51 := fol.all_sprovable -- input: \|- or \vdash" in fol

def all_realize_sentence (S : Structure L) (T : Theory L) := ∀{{f}}, f ∈ T → S ⊨ f
localized "infix ` ⊨ `:51 := fol.all_realize_sentence -- input using \|= or \vDash, but not using \models" in fol

lemma all_realize_sentence_of_subset {S} {T₁ T₂ : Theory L} (H : S ⊨ T₂) (H_sub : T₁ ⊆ T₂) : S ⊨ T₁ :=
λ _ _, H (H_sub ‹_›)

lemma all_realize_sentence_axm {S : Structure L} {f : sentence L} {T : Theory L} : ∀ (H : S ⊨ insert f T), S ⊨ f ∧ S ⊨ T :=
λ H, ⟨by {apply H, exact or.inl rfl}, by {intros ψ hψ, apply H, exact or.inr hψ}⟩

@[simp] lemma all_realize_sentence_axm_rw {S : Structure L} {f : sentence L} {T : Theory L} : (S ⊨ insert f T) ↔ S ⊨ f ∧ S ⊨ T :=
begin
  refine ⟨by apply all_realize_sentence_axm, _⟩, intro H,
  rcases H with ⟨Hf, HT⟩, intros g Hg, rcases Hg with ⟨Hg1, Hg2⟩,
  exact Hf, exact HT Hg
end

@[simp] lemma all_realize_sentence_singleton {S : Structure L} {f : sentence L} : S ⊨ {f} ↔ S ⊨ f :=
⟨by{intro H, apply H, exact or.inl rfl}, by {intros H g Hg, repeat{cases Hg}, assumption}⟩

@[simp]lemma realize_sentence_of_mem {S} {T : Theory L} {f : sentence L} (H : S ⊨ T) (H_mem : f ∈ T) : S ⊨ f := H H_mem

def ssatisfied (T : Theory L) (f : sentence L) :=
∀{{S : Structure L}}, nonempty S → S ⊨ T → S ⊨ f

localized "infix ` ⊨ `:51 := fol.ssatisfied -- input using \|= or \vDash, but not using \models" in fol

def all_ssatisfied (T T' : Theory L) := ∀(f ∈ T'), T ⊨ f
localized "infix ` ⊨ `:51 := fol.all_ssatisfied -- input using \|= or \vDash, but not using \models" in fol

def satisfied_of_ssatisfied {T : Theory L} {f : sentence L} (H : T ⊨ f) : T.fst ⊨ f.fst :=
begin
  intros S v hT, rw [←realize_sentence_iff], apply H ⟨ v 0 ⟩,
  intros f' hf', rw [realize_sentence_iff v], apply hT, apply mem_image_of_mem _ hf'
end

def ssatisfied_of_satisfied {T : Theory L} {f : sentence L} (H : T.fst ⊨ f.fst) : T ⊨ f :=
begin
  intros S hS hT, induction hS with s, rw [realize_sentence_iff (λ_, s)], apply H,
  intros f' hf', rcases hf' with ⟨f', ⟨hf', h⟩⟩, induction h, rw [←realize_sentence_iff],
  exact hT hf'
end

def all_satisfied_of_all_ssatisfied {T T' : Theory L} (H : T ⊨ T') : T.fst ⊨ T'.fst :=
by { intros f hf, rcases hf with ⟨f, ⟨hf, rfl⟩⟩, apply satisfied_of_ssatisfied (H f hf) }

def all_ssatisfied_of_all_satisfied {T T' : Theory L} (H : T.fst ⊨ T'.fst) : T ⊨ T' :=
by { intros f hf, apply ssatisfied_of_satisfied, apply H, exact mem_image_of_mem _ hf }

def satisfied_iff_ssatisfied {T : Theory L} {f : sentence L} : T ⊨ f ↔ T.fst ⊨ f.fst :=
⟨satisfied_of_ssatisfied, ssatisfied_of_satisfied⟩

def all_satisfied_sentences_iff {T T' : Theory L} : T ⊨ T' ↔ T.fst ⊨ T'.fst :=
⟨all_satisfied_of_all_ssatisfied, all_ssatisfied_of_all_satisfied⟩

def ssatisfied_snot {S : Structure L} {f : sentence L} (hS : ¬(S ⊨ f)) : S ⊨ ∼ f :=
by exact hS

def Model (T : Theory L) : Type (u+1) := Σ' (S : Structure L), S ⊨ T

@[reducible] def Model_ssatisfied {T : Theory L} (M : Model T) (ψ : sentence L) := M.fst ⊨ ψ

localized "infix ` ⊨ `:51 := fol.Model_ssatisfied -- input using \|= or \vDash, but not using \models" in fol

@[simp]lemma Model_ssatisfied_of_fst_ssatisfied {T : Theory L} {M : Model T} {ψ : sentence L} : M ⊨ ψ ↔ M.fst ⊨ ψ := by refl

@[simp] lemma false_of_Model_absurd {T : Theory L} (M : Model T) {ψ : sentence L} (h : M ⊨ ψ)
  (h' : M ⊨ ∼ψ) : false :=
by {unfold Model_ssatisfied at *, simp[*,-h'] at h', exact h'}

lemma soundness {T : Theory L} {A : sentence L} (H : T ⊢ A) : T ⊨ A :=
ssatisfied_of_satisfied $ formula_soundness H

/-- Given a model M ⊨ T with M ⊨ ¬ ψ, ¬ T ⊨ ψ--/
@[simp] lemma not_satisfied_of_model_not {T : Theory L} {ψ : sentence L} (M : Model T)
  (hM : M ⊨ ∼ψ) (h_nonempty : nonempty M.fst): ¬ T ⊨ ψ :=
begin
  intro H, suffices : M ⊨ ψ, exact false_of_Model_absurd M this hM,
  exact H h_nonempty M.snd
end

--localized "infix ` ⊨ `:51 := fol.ssatisfied -- input using \|= or \vDash, but not using \models" in fol

/- consistent theories -/
def is_consistent (T : Theory L) := ¬(T ⊢' (⊥ : sentence L))

protected def is_consistent.intro {T : Theory L} (H : ¬ T ⊢' (⊥ : sentence L)) : is_consistent T :=
H

protected def is_consistent.elim {T : Theory L} (H : is_consistent T) : ¬ T ⊢' (⊥ : sentence L)
| H' := H H'

lemma consis_not_of_not_provable {L} {T : Theory L} {f : sentence L} :
  ¬ T ⊢' f → is_consistent (T ∪ {∼f}) :=
begin
  intros h₁ h₂, cases h₂ with h₂, simp only [*, set.union_singleton] at h₂,
  apply h₁, exact ⟨sfalsumE h₂⟩
end

/- complete theories -/
def is_complete (T : Theory L) :=
is_consistent T ∧ ∀(f : sentence L), f ∈ T ∨ ∼ f ∈ T

def mem_of_sprf {T : Theory L} (H : is_complete T) {f : sentence L} (Hf : T ⊢ f) : f ∈ T :=
begin
  cases H.2 f, exact h, exfalso, apply H.1, constructor, refine impE _ _ Hf, apply saxm h
end

def mem_of_sprovable {T : Theory L} (H : is_complete T) {f : sentence L} (Hf : T ⊢' f) : f ∈ T :=
by destruct Hf; exact mem_of_sprf H

def sprovable_of_sprovable_or {T : Theory L} (H : is_complete T) {f₁ f₂ : sentence L}
  (H₂ : T ⊢' f₁ ⊔ f₂) : (T ⊢' f₁) ∨ T ⊢' f₂ :=
begin
  cases H.2 f₁ with h h, { left, exact ⟨saxm h⟩ },
  cases H.2 f₂ with h' h', { right, exact ⟨saxm h'⟩ },
  exfalso, destruct H₂, intro H₂, apply H.1, constructor,
  apply orE H₂; refine impE _ _ axm1; apply weakening1; apply axm;
    [exact mem_image_of_mem _ h, exact mem_image_of_mem _ h']
end

def impI_of_is_complete {T : Theory L} (H : is_complete T) {f₁ f₂ : sentence L}
  (H₂ : T ⊢' f₁ → T ⊢' f₂) : T ⊢' f₁ ⟹ f₂ :=
begin
  apply impI', cases H.2 f₁,
  { apply weakening1', apply H₂, exact ⟨saxm h⟩ },
  apply falsumE', apply weakening1',
  apply impE' _ (weakening1' ⟨by apply saxm h⟩) ⟨axm1⟩
end

def notI_of_is_complete {T : Theory L} (H : is_complete T) {f : sentence L}
  (H₂ : ¬T ⊢' f) : T ⊢' ∼f :=
begin
  apply @impI_of_is_complete _ T H f ⊥,
  intro h, exfalso, exact H₂ h
end

def has_enough_constants (T : Theory L) :=
∃(C : Π(f : bounded_formula L 1), L.constants),
∀(f : bounded_formula L 1), T ⊢' ∃' f ⟹ f[bd_const (C f)/0]

lemma has_enough_constants.intro (T : Theory L)
  (H : ∀(f : bounded_formula L 1), ∃ c : L.constants, T ⊢' ∃' f ⟹ f[bd_const c/0]) :
  has_enough_constants T :=
classical.axiom_of_choice H

def find_counterexample_of_henkin {T : Theory L} (H₁ : is_complete T) (H₂ : has_enough_constants T)
  (f : bounded_formula L 1) (H₃ : ¬ T ⊢' ∀' f) : ∃(t : closed_term L), T ⊢' ∼ f[t/0] :=
begin
  induction H₂ with C HC,
  refine ⟨bd_const (C (∼ f)), _⟩, dsimp [sprovable] at HC,
  apply (HC _).map2 (impE _),
  apply nonempty.map ex_not_of_not_all, apply notI_of_is_complete H₁ H₃
end

variables (T : Theory L) (H₁ : is_complete T) (H₂ : has_enough_constants T)
def term_rel (t₁ t₂ : closed_term L) : Prop := T ⊢' t₁ ≃ t₂

def term_setoid : setoid $ closed_term L :=
⟨term_rel T, λt, ⟨ref _ _⟩, λt t' H, H.map symm, λt₁ t₂ t₃ H₁ H₂, H₁.map2 trans H₂⟩
local attribute [instance] term_setoid

def term_model' : Type u :=
quotient $ term_setoid T

def term_model_fun' {l} (t : closed_preterm L l) (ts : dvector (closed_term L) l) : term_model' T :=
@quotient.mk _ (term_setoid T) $ bd_apps t ts

variable {T}
def term_model_fun_eq {l} (t t' : closed_preterm L (l+1)) (x x' : closed_term L)
  (Ht : equal_preterms T.fst t.fst t'.fst) (Hx : T ⊢ x ≃ x') (ts : dvector (closed_term L) l) :
  term_model_fun' T (bd_app t x) ts = term_model_fun' T (bd_app t' x') ts :=
begin
  induction ts generalizing x x',
  { apply quotient.sound, refine ⟨trans (app_congr t.fst Hx) _⟩, apply Ht ([x'.fst]) },
  { apply ts_ih, apply equal_preterms_app Ht Hx, apply ref }
end

variable (T)
def term_model_fun {l} (t : closed_preterm L l) (ts : dvector (term_model' T) l) : term_model' T :=
begin
  refine ts.quotient_lift (term_model_fun' T t) _, clear ts,
  intros ts ts' hts,
  induction hts,
  { refl },
  { apply (hts_ih _).trans, induction hts_hx with h, apply term_model_fun_eq,
    refl, exact h }
end

def term_model_rel' {l} (f : presentence L l) (ts : dvector (closed_term L) l) : Prop :=
T ⊢' bd_apps_rel f ts

variable {T}
def term_model_rel_iff {l} (f f' : presentence L (l+1)) (x x' : closed_term L)
  (Ht : equiv_preformulae T.fst f.fst f'.fst) (Hx : T ⊢ x ≃ x') (ts : dvector (closed_term L) l) :
  term_model_rel' T (bd_apprel f x) ts ↔ term_model_rel' T (bd_apprel f' x') ts :=
begin
  induction ts generalizing x x',
  { apply iff.trans (apprel_congr' f.fst Hx),
    apply iff_of_biimp, have := Ht ([x'.fst]), exact ⟨this⟩ },
  { apply ts_ih, apply equiv_preformulae_apprel Ht Hx, apply ref }
end

variable (T)
def term_model_rel {l} (f : presentence L l) (ts : dvector (term_model' T) l) : Prop :=
begin
  refine ts.quotient_lift (term_model_rel' T f) _, clear ts,
  intros ts ts' hts,
  induction hts,
  { refl },
  { apply (hts_ih _).trans, induction hts_hx with h, apply propext, apply term_model_rel_iff,
    refl, exact h }
end

def term_model : Structure L :=
⟨term_model' T,
 λn, term_model_fun T ∘ bd_func,
 λn, term_model_rel T ∘ bd_rel⟩

@[reducible] def term_mk : closed_term L → term_model T :=
@quotient.mk _ $ term_setoid T

variable {T}
lemma realize_closed_preterm_term_model {l} (ts : dvector (closed_term L) l)
  (t : closed_preterm L l) :
  realize_bounded_term ([]) t (ts.map $ term_mk T) = (term_mk T (bd_apps t ts)) :=
begin
  induction t,
  { apply fin_zero_elim t },
  { apply dvector.quotient_beta },
  { rw [realize_bounded_term_bd_app],
    have := t_ih_s ([]), dsimp at this, rw this,
    apply t_ih_t (t_s::ts) }
end

@[simp] lemma realize_closed_term_term_model (t : closed_term L) :
  realize_closed_term (term_model T) t = term_mk T t :=
by apply realize_closed_preterm_term_model ([]) t

lemma realize_subst_preterm {S : Structure L} {n l} (t : bounded_preterm L (n+1) l)
  (xs : dvector S l) (s : closed_term L) (v : dvector S n) :
  realize_bounded_term v (substmax_bounded_term t s) xs =
  realize_bounded_term (v.concat (realize_closed_term S s)) t xs :=
begin
  induction t,
  { by_cases h : t.1 < n,
    { rw [substmax_var_lt t s h], dsimp,
      simp only [dvector.map_nth, dvector.concat_nth _ _ _ _ h, dvector.nth'],  },
    { have h' := le_antisymm (le_of_lt_succ t.2) (le_of_not_gt h), simp [h', dvector.nth'],
      rw [substmax_var_eq t s h'],
      apply realize_bounded_term_irrel, simp }},
  { refl },
  { dsimp, rw [substmax_bounded_term_bd_app], dsimp, rw [t_ih_s ([]), t_ih_t] }
end

lemma realize_subst_term {S : Structure L} {n} (v : dvector S n) (s : closed_term L)
  (t : bounded_term L (n+1))  :
  realize_bounded_term v (substmax_bounded_term t s) ([]) =
  realize_bounded_term (v.concat (realize_closed_term S s)) t ([]) :=
by apply realize_subst_preterm t ([]) s v

lemma realize_subst_formula (S : Structure L) {n} (f : bounded_formula L (n+1))
  (t : closed_term L) (v : dvector S n) :
  realize_bounded_formula v (substmax_bounded_formula f t) ([]) ↔
  realize_bounded_formula (v.concat (realize_closed_term S t)) f ([]) :=
begin
  revert n f v, refine bounded_formula.rec1 _ _ _ _ _; intros,
  { simp },
  { apply eq.congr, exact realize_subst_term v t t₁, exact realize_subst_term v t t₂ },
  { rw [substmax_bounded_formula_bd_apps_rel, realize_bounded_formula_bd_apps_rel,
        realize_bounded_formula_bd_apps_rel],
    simp [ts.map_congr (realize_subst_term _ _)] },
  { apply imp_congr, apply ih₁ v, apply ih₂ v },
  { simp, apply forall_congr, intro x, apply ih (x::v) }
end

lemma realize_subst_formula0 (S : Structure L) (f : bounded_formula L 1) (t : closed_term L) :
  S ⊨ f[t/0] ↔ realize_bounded_formula ([realize_closed_term S t]) f ([]) :=
iff.trans (by rw [substmax_eq_subst0_formula]) (by apply realize_subst_formula S f t ([]))

lemma term_model_subst0 (f : bounded_formula L 1) (t : closed_term L) :
  term_model T ⊨ f[t/0] ↔ realize_bounded_formula ([term_mk T t]) f ([]) :=
(realize_subst_formula0 (term_model T) f t).trans (by simp)

include H₂
instance nonempty_term_model : nonempty $ term_model T :=
by { induction H₂ with C, exact ⟨term_mk T (bd_const (C (&0 ≃ &0)))⟩ }

include H₁
def term_model_ssatisfied_iff {n} : ∀{l} (f : presentence L l)
  (ts : dvector (closed_term L) l) (h : count_quantifiers f.fst < n),
  T ⊢' bd_apps_rel f ts ↔ term_model T ⊨ bd_apps_rel f ts :=
begin
  refine nat.strong_induction_on n _, clear n,
  intros n n_ih l f ts hn,
  have : {f' : preformula L l // f.fst = f' } := ⟨f.fst, rfl⟩,
  cases this with f' hf, induction f'; cases f; injection hf with hf₁ hf₂,
  { simp, exact H₁.1.elim },
  { simp, refine iff.trans _ (realize_sentence_equal f_t₁ f_t₂).symm, simp [term_mk], refl },
  { refine iff.trans _ (realize_bd_apps_rel _ _).symm,
    dsimp [term_model, term_model_rel],
    rw [ts.map_congr realize_closed_term_term_model, dvector.quotient_beta], refl },
  { apply f'_ih f_f (f_t::ts) _ hf₁, simp at hn ⊢, exact hn },
  { have ih₁ := f'_ih_f₁ f_f₁ ([]) (lt_of_le_of_lt (nat.le_add_right _ _) hn) hf₁,
    have ih₂ := f'_ih_f₂ f_f₂ ([]) (lt_of_le_of_lt (nat.le_add_left _ _) hn) hf₂, cases ts,
    split; intro h,
    { intro h₁, apply ih₂.mp, apply h.map2 (impE _), refine ih₁.mpr h₁ },
    { simp at h, simp at ih₁, rw [←ih₁] at h, simp at ih₂, rw [←ih₂] at h,
      exact impI_of_is_complete H₁ h }},
  { cases ts, split; intro h,
    { simp at h ⊢,
      apply quotient.ind, intro t,
      apply (term_model_subst0 f_f t).mp,
      cases n with n, { exfalso, exact not_lt_zero _ hn },
      refine (n_ih n (lt.base n) (f_f[t/0]) ([]) _).mp (h.map _),
      simp, exact lt_of_succ_lt_succ hn,
      rw [bd_apps_rel_zero, subst0_bounded_formula_fst],
      exact allE₂ _ _ },
    { apply classical.by_contradiction, intro H,
      cases find_counterexample_of_henkin H₁ H₂ f_f H with t ht,
      apply H₁.left, apply impE' _ ht,
      cases n with n, { exfalso, exact not_lt_zero _ hn },
      refine (n_ih n (lt.base n) (f_f[t/0]) ([]) _).mpr _,
      { simp, exact lt_of_succ_lt_succ hn },
      exact (term_model_subst0 f_f t).mpr (h (term_mk T t)) }},
end

def term_model_ssatisfied : term_model T ⊨ T :=
by { intros f hf, apply (term_model_ssatisfied_iff H₁ H₂ f ([]) (lt.base _)).mp, exact ⟨saxm hf⟩ }

-- completeness for complete theories with enough constants
lemma completeness' {f : sentence L} (H : T ⊨ f) : T ⊢' f :=
begin
  apply (term_model_ssatisfied_iff H₁ H₂ f ([]) (lt.base _)).mpr,
  apply H, exact fol.nonempty_term_model H₂,
  apply term_model_ssatisfied H₁ H₂,
end
omit H₁ H₂

def Th (S : Structure L) : Theory L := { f : sentence L | S ⊨ f }

lemma realize_sentence_Th (S : Structure L) : S ⊨ Th S :=
λf hf, hf

lemma is_complete_Th (S : Structure L) (HS : nonempty S) : is_complete (Th S) :=
⟨λH, by cases H; apply soundness H HS (realize_sentence_Th S),
  λ(f : sentence L), classical.em (S ⊨ f)⟩

def eliminates_quantifiers : Theory L → Prop :=
  λ T, ∀ f ∈ T, ∃ f' , bounded_preformula.quantifier_free f' ∧ (T ⊢' f ⇔ f')

def L_empty : Language :=
  ⟨λ _, empty, λ _, empty⟩

def T_empty (L : Language) : Theory L := ∅

@[reducible] def T_equality : Theory L_empty := T_empty L_empty

@[simp] lemma in_theory_iff_satisfied {S : Structure L} {f : sentence L} : f ∈ Th S ↔ S ⊨ f :=
by refl

section bd_alls

/-- Given a nat k and a 0-formula ψ, return ψ with ∀' applied k times to it --/
@[simp] def alls :  Π n : ℕ, formula L → formula L
--:= nat.iterate all
| 0 f := f
| (n+1) f := ∀' alls n f

/-- generalization of bd_alls where we can apply less than n ∀'s--/
@[simp] def bd_alls' : Π k n : ℕ, bounded_formula L (n + k) → bounded_formula L n
| 0 n         f := f
| (k+1) n     f := bd_alls' k n (∀' f)

@[simp] def bd_alls : Π n : ℕ, bounded_formula L n → sentence L
| 0     f := f
| (n+1) f := bd_alls n (∀' f) -- bd_alls' (n+1) 0 (f.cast_eqr (zero_add (n+1)))

@[simp] lemma alls'_alls : Π n (ψ : bounded_formula L n),
  bd_alls n ψ = bd_alls' n 0 (ψ.cast_eq (zero_add n).symm) :=
by {intros n ψ, induction n, swap, simp[n_ih (∀' ψ)], tidy}

@[simp] lemma alls'_all_commute {n} {k} {f : bounded_formula L (n+k+1)} :
  (bd_alls' k n (∀' f)) = ∀' bd_alls' k (n+1) (f.cast_eq (by simp)) :=
-- by {refine ∀' bd_alls' k (n+1) _, simp, exact f}
by {induction k; dsimp only [bounded_preformula.cast_eq], swap, simp[@k_ih (∀'f)], tidy}

@[simp] lemma bd_alls'_substmax {L} {n} {f : bounded_formula L (n+1)} {t : closed_term L} :
  (bd_alls' n 1 (f.cast_eq (by simp)))[t /0] =
  (bd_alls' n 0 (substmax_bounded_formula (f.cast_eq (by simp)) t)) :=
by {induction n, {tidy}, have := @n_ih (∀' f), simp[bounded_preformula.cast_eq] at *, exact this}

lemma realize_sentence_bd_alls {L} {n} {f : bounded_formula L n} {S : Structure L} :
  S ⊨ (bd_alls n f) ↔ (∀ xs : dvector S n, realize_bounded_formula xs f dvector.nil) :=
begin
  induction n,
    {split; dsimp; intros; try{cases xs}; apply a},
    {have := @n_ih (∀' f),
     cases this with this_mp this_mpr, split,
     {intros H xs, rcases xs with ⟨x,xs⟩, revert xs_xs xs_x, exact this_mp H},
     {intro H, exact this_mpr (by {intros xs x, exact H (x :: xs)})}}
end

@[simp] lemma alls_0 (ψ : formula L) : alls 0 ψ = ψ := by refl

@[simp] lemma alls_all_commute (f : formula L) {k : ℕ} :
  (alls k ∀' f) = (∀' alls k f) :=
by {induction k, refl, dunfold alls, rw[k_ih]}

@[simp] lemma alls_succ_k (f : formula L) {k : ℕ} : alls (k + 1) f = ∀' alls k f :=
by constructor

end bd_alls

end fol
