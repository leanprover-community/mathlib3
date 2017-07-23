/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

List permutations.
-/
import data.list.basic data.list.comb data.list.set

-- TODO(Jeremy): Here is a common idiom: after simplifying, we have a goal 1 + t = nat.succ t
-- and need to say rw [add_comm, reflexivity]. Can we get the simplifier to finish this off?

namespace list
universe variables uu vv
variables {α : Type uu} {β : Type vv}

inductive perm : list α → list α → Prop
| nil   : perm [] []
| skip  : Π (x : α) {l₁ l₂ : list α}, perm l₁ l₂ → perm (x::l₁) (x::l₂)
| swap  : Π (x y : α) (l : list α), perm (y::x::l) (x::y::l)
| trans : Π {l₁ l₂ l₃ : list α}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃

namespace perm
infix ~ := perm

@[refl]
protected theorem refl : ∀ (l : list α), l ~ l
| []      := nil
| (x::xs) := skip x (refl xs)

@[symm]
protected theorem symm {l₁ l₂ : list α} (p : l₁ ~ l₂) : l₂ ~ l₁ :=
perm.rec_on p
  nil
  (λ x l₁ l₂ p₁ r₁, skip x r₁)
  (λ x y l, swap y x l)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₂ r₁)

attribute [trans] perm.trans

theorem eqv (α : Type) : equivalence (@perm α) :=
mk_equivalence (@perm α) (@perm.refl α) (@perm.symm α) (@perm.trans α)

attribute [instance]
protected def is_setoid (α : Type) : setoid (list α) :=
setoid.mk (@perm α) (perm.eqv α)

theorem mem_of_perm {a : α} {l₁ l₂ : list α} (p : l₁ ~ l₂) : a ∈ l₁ → a ∈ l₂ :=
perm.rec_on p
  (λ h, h)
  (λ x l₁ l₂ p₁ r₁ i, or.elim i
    (λ ax, by simp [ax])
    (λ al₁, or.inr (r₁ al₁)))
  (λ x y l ayxl, or.elim ayxl
    (λ ay, by simp [ay])
    (λ axl, or.elim axl
      (λ ax, by simp [ax])
      (λ al, or.inr (or.inr al))))
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂ ainl₁, r₂ (r₁ ainl₁))

theorem not_mem_of_perm {a : α} {l₁ l₂ : list α} : l₁ ~ l₂ → a ∉ l₁ → a ∉ l₂ :=
assume p nainl₁ ainl₂, nainl₁ (mem_of_perm p.symm ainl₂)

theorem mem_iff_mem_of_perm {a : α} {l₁ l₂ : list α} (h : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ :=
iff.intro (mem_of_perm h) (mem_of_perm h.symm)

theorem perm_app_left {l₁ l₂ : list α} (t₁ : list α) (p : l₁ ~ l₂) : (l₁++t₁) ~ (l₂++t₁) :=
perm.rec_on p
  (perm.refl ([] ++ t₁))
  (λ x l₁ l₂ p₁ r₁, skip x r₁)
  (λ x y l, swap x y _)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₁ r₂)

theorem perm_app_right {t₁ t₂ : list α} : ∀ (l : list α), t₁ ~ t₂ → (l++t₁) ~ (l++t₂)
| []      p := p
| (x::xs) p := skip x (perm_app_right xs p)

theorem perm_app {l₁ l₂ t₁ t₂ : list α} : l₁ ~ l₂ → t₁ ~ t₂ → (l₁++t₁) ~ (l₂++t₂) :=
assume p₁ p₂, trans (perm_app_left t₁ p₁) (perm_app_right l₂ p₂)

--theorem perm_app_cons (a : α) {h₁ h₂ t₁ t₂ : list α} :
--  h₁ ~ h₂ → t₁ ~ t₂ → (h₁ ++ (a::t₁)) ~ (h₂ ++ (a::t₂)) :=
--assume p₁ p₂, perm_app p₁ (skip a p₂)

theorem perm_cons_app (a : α) : ∀ (l : list α), (a::l) ~ (l ++ [a])
| []      := perm.refl _
| (x::xs) := trans (swap x a xs) $ skip x (perm_cons_app xs)

@[simp]
theorem perm_cons_app_simp (a : α) (l : list α) : (l ++ [a]) ~ (a::l) :=
perm.symm (perm_cons_app a l)

@[simp]
theorem perm_app_comm : ∀ {l₁ l₂ : list α}, (l₁++l₂) ~ (l₂++l₁)
| []     l₂ := by simp
| (a::t) l₂ := calc
    a::(t++l₂) ~ a::(l₂++t)   : skip a perm_app_comm
          ...  ~ l₂++t++[a]   : perm_cons_app _ _
          ...  = l₂++(t++[a]) : by rw append.assoc
          ...  ~ l₂++(a::t)   : perm_app_right l₂ (perm.symm (perm_cons_app a t))

theorem length_eq_length_of_perm {l₁ l₂ : list α} (p : l₁ ~ l₂) : length l₁ = length l₂ :=
perm.rec_on p
  rfl
  (λ x l₁ l₂ p r, by simp[r])
  (λ x y l, by simp)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, eq.trans r₁ r₂)

theorem eq_nil_of_perm_nil {l₁ : list α} (p : ([] : list α) ~ l₁) : l₁ = ([] : list α) :=
eq_nil_of_length_eq_zero (length_eq_length_of_perm p).symm

theorem not_perm_nil_cons (x : α) (l : list α) : ¬ [] ~ (x::l) :=
assume p, by have h := eq_nil_of_perm_nil p; contradiction

theorem eq_singleton_of_perm {a b : α} (p : [a] ~ [b]) : a = b :=
have a ∈ [b], from mem_of_perm p (by simp),
by simp at this; simp [*]

theorem eq_singleton_of_perm_inv {a : α} {l : list α} (p : [a] ~ l) : l = [a] :=
match l, length_eq_length_of_perm p, p with
| [a'], rfl, p := by simp [eq_singleton_of_perm p]
end

theorem perm_rev : ∀ (l : list α), l ~ (reverse l)
| []      := nil
| (x::xs) := calc
  x::xs ~ x::reverse xs     : skip x (perm_rev xs)
    ... ~ reverse xs ++ [x] : perm_cons_app _ _
    ... = reverse (x::xs)   : by rw [reverse_cons, concat_eq_append]

@[simp]
theorem perm_rev_simp (l : list α) : (reverse l) ~ l :=
perm.symm (perm_rev l)

theorem perm_middle (a : α) (l₁ l₂ : list α) : (a::l₁)++l₂ ~ l₁++(a::l₂) :=
have a::l₁++l₂ ~ l₁++[a]++l₂, from perm_app_left l₂ (perm_cons_app a l₁),
by simp at this; exact this

attribute [simp]
theorem perm_middle_simp (a : α) (l₁ l₂ : list α) : l₁++(a::l₂) ~ (a::l₁)++l₂ :=
perm.symm $ perm_middle a l₁ l₂

theorem perm_cons_app_cons {l l₁ l₂ : list α} (a : α) (p : l ~ l₁++l₂) : a::l ~ l₁++(a::l₂) :=
trans (skip a p) $ perm_middle a l₁ l₂

open decidable
theorem perm_erase [decidable_eq α] {a : α} : ∀ {l : list α}, a ∈ l → l ~ a:: l.erase a
| []     h := false.elim h
| (x::t) h := if ax : x = a then by rw [ax, erase_cons_head] else
  by rw [erase_cons_tail _ ax]; exact
  have aint : a ∈ t, from mem_of_ne_of_mem (assume h, ax h.symm) h,
  trans (skip _ $ perm_erase aint) (swap _ _ _)

@[elab_as_eliminator]
theorem perm_induction_on {P : list α → list α → Prop} {l₁ l₂ : list α} (p : l₁ ~ l₂)
    (h₁ : P [] [])
    (h₂ : ∀ x l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (x::l₁) (x::l₂))
    (h₃ : ∀ x y l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (y::x::l₁) (x::y::l₂))
    (h₄ : ∀ l₁ l₂ l₃, l₁ ~ l₂ → l₂ ~ l₃ → P l₁ l₂ → P l₂ l₃ → P l₁ l₃) :
  P l₁ l₂ :=
have P_refl : ∀ l, P l l, from
  assume l,
  list.rec_on l h₁ (λ x xs ih, h₂ x xs xs (perm.refl xs) ih),
perm.rec_on p h₁ h₂ (λ x y l, h₃ x y l l (perm.refl l) (P_refl l)) h₄

theorem xswap {l₁ l₂ : list α} (x y : α) : l₁ ~ l₂ → x::y::l₁ ~ y::x::l₂ :=
assume p, calc
  x::y::l₁  ~  y::x::l₁  : swap y x l₁
        ... ~  y::x::l₂  : skip y (skip x p)

@[congr]
theorem perm_map (f : α → β) {l₁ l₂ : list α} : l₁ ~ l₂ → map f l₁ ~ map f l₂ :=
assume p, perm_induction_on p
  nil
  (λ x l₁ l₂ p r, skip (f x) r)
  (λ x y l₁ l₂ p r, xswap (f y) (f x) r)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₁ r₂)

/- TODO(Jeremy)
In the next section, the decidability proof works, but gave the following error:

equation compiler failed to generate bytecode for auxiliary declaration 'list.perm.decidable_perm_aux._main'
nested exception message:
code generation failed, inductive predicate 'eq' is not supported

So I will comment it out and give another decidability proof below.
-/

/-
/- permutation is decidable if α has decidable equality -/
section dec
open decidable
variable [Ha : decidable_eq α]
include Ha

def decidable_perm_aux :
  ∀ (n : nat) (l₁ l₂ : list α), length l₁ = n → length l₂ = n → decidable (l₁ ~ l₂)
| 0     l₁      l₂ H₁ H₂ :=
  have l₁n : l₁ = [], from eq_nil_of_length_eq_zero H₁,
  have l₂n : l₂ = [], from eq_nil_of_length_eq_zero H₂,
  begin rw [l₁n, l₂n], exact (is_true perm.nil) end
| (n+1) (x::t₁) l₂ H₁ H₂ :=
  by_cases
    (assume xinl₂ : x ∈ l₂,
      -- TODO(Jeremy): it seems the equation editor abstracts t₂, and loses the def, so
      --               I had to expand it manually
      -- let t₂ : list α := erase x l₂ in
      have len_t₁ : length t₁ = n,
        begin
         simp at H₁,
         have H₁' : nat.succ (length t₁) = nat.succ n, exact H₁,
         injection H₁' with e, exact e
       end,
      have length (erase x l₂) = nat.pred (length l₂), from length_erase_of_mem xinl₂,
      have length (erase x l₂) = n, begin rw [this, H₂], reflexivity end,
      match decidable_perm_aux n t₁ (erase x l₂) len_t₁ this with
      | is_true p  := is_true (calc
          x::t₁ ~ x::erase x l₂   : skip x p
           ...  ~ l₂              : perm.symm (perm_erase xinl₂))
      | is_false np := is_false (λ p : x::t₁ ~ l₂,
        have erase x (x::t₁) ~ erase x l₂, from erase_perm_erase_of_perm x p,
        have t₁ ~ erase x l₂, begin rw [erase_cons_head] at this, exact this end,
        absurd this np)
      end)
    (assume nxinl₂ : x ∉ l₂,
      is_false (λ p : x::t₁ ~ l₂, absurd (mem_of_perm p (mem_cons_self _ _)) nxinl₂))

attribute [instance]
def decidable_perm : ∀ (l₁ l₂ : list α), decidable (l₁ ~ l₂) :=
λ l₁ l₂,
by_cases
  (assume eql : length l₁ = length l₂,
    decidable_perm_aux (length l₂) l₁ l₂ eql rfl)
  (assume neql : length l₁ ≠ length l₂,
    is_false (λ p : l₁ ~ l₂, absurd (length_eq_length_of_perm p) neql))
end dec
-/

section count
variable [decα : decidable_eq α]
include decα

theorem count_eq_count_of_perm {l₁ l₂ : list α} : l₁ ~ l₂ → ∀ a, count a l₁ = count a l₂ :=
assume : l₁ ~ l₂, perm.rec_on this
  (λ a, rfl)
  (λ x l₁ l₂ p h a, begin simp [count_cons', h a] end)
  (λ x y l a, begin simp [count_cons'] end)
  (λ l₁ l₂ l₃ p₁ p₂ h₁ h₂ a, eq.trans (h₁ a) (h₂ a))

theorem perm_of_forall_count_eq : ∀ {l₁ l₂ : list α}, (∀ a, count a l₁ = count a l₂) → l₁ ~ l₂
| [] :=
    assume l₂,
    assume h : ∀ a, count a [] = count a l₂,
    have ∀ a, a ∉ l₂, from assume a, not_mem_of_count_eq_zero (by simp [(h a).symm]),
    have l₂ = [], from eq_nil_of_forall_not_mem this,
    show [] ~ l₂, by rw this
| (b :: l) :=
    assume l₂,
    assume h : ∀ a, count a (b :: l) = count a l₂,
    have b ∈ l₂, from mem_of_count_pos (begin rw [←(h b)], simp, apply nat.succ_pos end),
    have l₂ ~ b :: l₂.erase b, from perm_erase this,
    have ∀ a, count a l = count a (l₂.erase b), from
      assume a,
      if h' : a = b then
        nat.succ_inj (calc
          count a l + 1 = count a (b :: l)         : begin simp [h'], rw add_comm end
                   ... = count a l₂                : by rw h
                   ... = count a (b :: l₂.erase b) : count_eq_count_of_perm (by assumption) a
                   ... = count a (l₂.erase b) + 1  : begin simp [h'], rw add_comm end)
      else
        calc
          count a l = count a (b :: l)          : by simp [h']
                ... = count a l₂                : by rw h
                ... = count a (b :: l₂.erase b) : count_eq_count_of_perm (by assumption) a
                ... = count a (l₂.erase b)      : by simp [h'],
    have l ~ l₂.erase b, from perm_of_forall_count_eq this,
    calc
      b :: l ~ b :: l₂.erase b : skip b this
         ... ~ l₂              : perm.symm (by assumption)

theorem perm_iff_forall_count_eq_count (l₁ l₂ : list α) : l₁ ~ l₂ ↔ ∀ a, count a l₁ = count a l₂ :=
iff.intro count_eq_count_of_perm perm_of_forall_count_eq

-- This next theorem shows that perm is equivalent to a decidable (and efficiently checkable)
-- property.

theorem perm_iff_forall_mem_count_eq_count (l₁ l₂ : list α) :
  l₁ ~ l₂ ↔ ∀ a ∈ erase_dup (l₁ ∪ l₂), count a l₁ = count a l₂ :=
iff.intro
  (assume h : l₁ ~ l₂, assume a, assume ha, count_eq_count_of_perm h a)
  (assume h,
     have ∀ a, count a l₁ = count a l₂, from
       assume a,
       if hl₁ : a ∈ l₁ then
         have a ∈ erase_dup (l₁ ∪ l₂), from mem_erase_dup (mem_union_left hl₁ l₂),
         h a this
       else if hl₂ : a ∈ l₂ then
         have a ∈ erase_dup (l₁ ∪ l₂), from mem_erase_dup (mem_union_right l₁ hl₂),
         h a this
       else
         by simp [hl₁, hl₂],
     perm_of_forall_count_eq this)

instance : ∀ (l₁ l₂ : list α), decidable (l₁ ~ l₂) :=
assume l₁ l₂,
decidable_of_decidable_of_iff (decidable_forall_mem _)
                              (perm_iff_forall_mem_count_eq_count l₁ l₂).symm

end count

-- Auxiliary theorem for performing cases-analysis on l₂.
-- We use it to prove perm_inv_core.
private theorem discr {P : Prop} {a b : α} {l₁ l₂ l₃ : list α} :
    a::l₁ = l₂++(b::l₃)                    →
    (l₂ = [] → a = b → l₁ = l₃ → P)        →
    (∀ t, l₂ = a::t → l₁ = t++(b::l₃) → P) → P :=
match l₂ with
| []   := λ e h₁ h₂, begin simp at e, injection e with e₁ e₂, exact h₁ rfl e₁ e₂ end
| h::t := λ e h₁ h₂,
  begin
    simp at e,
    injection e with e₁ e₂,
    rw e₁ at h₂,
    exact h₂ t rfl e₂
  end
end

-- Auxiliary theorem for performing cases-analysis on l₂.
-- We use it to prove perm_inv_core.
private theorem discr₂ {P : Prop} {a b c : α} {l₁ l₂ l₃ : list α}
    (e : a::b::l₁ = l₂++(c::l₃))
    (H₁ : l₂ = [] → l₃ = b::l₁ → a = c → P)
    (H₂ : l₂ = [a] → b = c → l₁ = l₃ → P)
    (H₃ : ∀ t, l₂ = a::b::t → l₁ = t++(c::l₃) → P) : P :=
discr e (λh₁ h₂ h₃, H₁ h₁ h₃.symm h₂) $ λt h₁ h₂, discr h₂
  (λh₃ h₄, match t, h₃, h₁ with ._, rfl, h₁ := H₂ h₁ h₄ end)
  (λt' h₃ h₄, match t, h₃, h₁ with ._, rfl, h₁ := H₃ t' h₁ h₄ end)

/- quasiequal a l l' means that l' is exactly l, with a added
   once somewhere -/
section qeq

inductive qeq (a : α) : list α → list α → Prop
| qhead : ∀ l, qeq l (a::l)
| qcons : ∀ (b : α) {l l' : list α}, qeq l l' → qeq (b::l) (b::l')

open qeq

notation l' `≈`:50 a `|` l:50 := qeq a l l'

lemma perm_of_qeq {a : α} {l₁ l₂ : list α} : l₁≈a|l₂ → l₁~a::l₂ :=
assume q, qeq.rec_on q
  (λ h, perm.refl (a :: h))
  (λ b t₁ t₂ q₁ r₁, calc
     b::t₂ ~ b::a::t₁ : skip b r₁
       ... ~ a::b::t₁ : swap a b t₁)

theorem qeq_app : ∀ (l₁ : list α) (a : α) (l₂ : list α), l₁ ++ (a :: l₂) ≈ a | l₁ ++ l₂
| ([] : list α) b l₂ := qhead b l₂
| (a::ains)     b l₂ := qcons a (qeq_app ains b l₂)

theorem mem_head_of_qeq {a : α} : ∀ {l₁ l₂ : list α}, l₁ ≈ a | l₂ → a ∈ l₁
| ._ ._ (qhead .(a) l)            := mem_cons_self a l
| ._ ._ (@qcons .(α) .(a) b l l' q) := mem_cons_of_mem b (mem_head_of_qeq q)

theorem mem_tail_of_qeq {a : α} : ∀ {l₁ l₂ : list α}, l₁ ≈ a | l₂ → ∀ {b}, b ∈ l₂ → b ∈ l₁
| ._ ._ (qhead .(a) l)            b bl  := mem_cons_of_mem a bl
| ._ ._ (@qcons .(α) .(a) c l l' q) b bcl :=
  or.elim (eq_or_mem_of_mem_cons bcl)
    (assume bc : b = c,
      begin rw bc, apply mem_cons_self end)
    (assume bl : b ∈ l,
      have bl' : b ∈ l', from mem_tail_of_qeq q bl,
      mem_cons_of_mem c bl')

theorem mem_cons_of_qeq {a : α} : ∀ {l₁ l₂ : list α}, l₁≈a|l₂ → ∀ {b}, b ∈ l₁ → b ∈ a::l₂
| ._ ._ (qhead ._ l)            b bal                  := bal
| ._ ._ (@qcons ._ ._ c l l' q) b (bcl' : b ∈ c :: l') :=
  show b ∈ a :: c :: l, from
    or.elim (eq_or_mem_of_mem_cons bcl')
      (assume bc : b = c,
        begin rw bc, apply mem_cons_of_mem, apply mem_cons_self end)
      (assume bl' : b ∈ l',
        have b ∈ a :: l, from mem_cons_of_qeq q bl',
        or.elim (eq_or_mem_of_mem_cons this)
          (assume ba : b = a,
            begin rw ba, apply mem_cons_self end)
          (assume bl : b ∈ l,
            mem_cons_of_mem a (mem_cons_of_mem c bl)))

theorem length_eq_of_qeq {a : α} {l₁ l₂ : list α} :
  l₁ ≈ a | l₂ → length l₁ = nat.succ (length l₂) :=
begin
  intro q, induction q with l b l l' q ih, simp[nat.one_add], simp [*]
end

theorem qeq_of_mem {a : α} {l : list α} : a ∈ l → (∃ l', l ≈ a | l') :=
list.rec_on l
  (λ h : a ∈ ([] : list α), absurd h (not_mem_nil a))
  (λ b bs r ainbbs, or.elim (eq_or_mem_of_mem_cons ainbbs)
    (λ aeqb  : a = b,
       have ∃ l, b::bs ≈ b | l, from
         exists.intro bs (qhead b bs),
       begin rw aeqb, exact this end)
    (λ ainbs : a ∈ bs,
       have ∃ l', bs ≈ a|l', from r ainbs,
       exists.elim this (assume (l' : list α) (q : bs ≈ a|l'),
         have b::bs ≈ a | b::l', from qcons b q,
         exists.intro (b::l') this)))

theorem qeq_split {a : α} : ∀ {l l' : list α}, l'≈a|l → ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l' = l₁ ++ (a::l₂)
| ._ ._ (qhead ._ l)            := ⟨[], l, by simp⟩
| ._ ._ (@qcons ._ ._ c l l' q) :=
  match (qeq_split q) with
  | ⟨l₁, l₂, h₁, h₂⟩ := ⟨c :: l₁, l₂, by simp [h₁, h₂]⟩
  end

--theorem subset_of_mem_of_subset_of_qeq {a : α} {l : list α} {u v : list α} :
--  a ∉ l → a::l ⊆ v → v≈a|u → l ⊆ u :=
--λ (nainl : a ∉ l) (s : a::l ⊆ v) (q : v≈a|u) (b : α) (binl : b ∈ l),
--  have b ∈ v,    from s (or.inr binl),
--  have b ∈ a::u, from mem_cons_of_qeq q this,
--  or.elim (eq_or_mem_of_mem_cons this)
--    (assume : b = a, begin subst b, contradiction end)
--    (assume : b ∈ u, this)
--end qeq

theorem perm_inv_core {l₁ l₂ : list α} (p' : l₁ ~ l₂) : ∀ {a s₁ s₂}, l₁≈a|s₁ → l₂≈a|s₂ → s₁ ~ s₂ :=
perm_induction_on p'
  (λ a s₁ s₂ e₁ e₂, match e₁ with end)
  (λ x t₁ t₂ p (r : ∀{a s₁ s₂}, t₁≈a|s₁ → t₂≈a|s₂ → s₁ ~ s₂) a s₁ s₂ e₁ e₂,
    match s₁, s₂, qeq_split e₁, qeq_split e₂ with ._, ._, ⟨s₁₁, s₁₂, rfl, C₁⟩, ⟨s₂₁, s₂₂, rfl, C₂⟩ :=
    discr C₁
      (λe₁ xa, match s₁₁, x, e₁, xa, C₂ with ._, ._, rfl, rfl, C₂ := discr C₂
        (λe₁ _ e₂ e₃, match s₁₂, s₂₁, s₂₂, e₁, e₂, e₃ with
        | ._, ._, ._, rfl, rfl, rfl := p end)
        (λt₃ e₁ e₂ e₃, match s₂₁, s₁₂, t₂, e₁, e₂, e₃, p with
        | ._, ._, ._, rfl, rfl, rfl, p := trans p (perm_middle _ _ _).symm end) 
        end)
      (λt₃ e₁ e₂, match s₁₁, t₁, e₁, e₂, C₂, p, @r with ._, ._, rfl, rfl, C₂, p, r := discr C₂
        (λe₁ xa e₂, match x, s₂₁, s₂₂, xa, e₁, e₂ with
        | ._, ._, ._, rfl, rfl, rfl := trans (perm_middle _ _ _) p end)
        (λt₃ e₁ e₂, match s₂₁, t₂, e₁, e₂, @r with
        | ._, ._, rfl, rfl, r := skip x (r (qeq_app _ _ _) (qeq_app _ _ _)) end) 
        end)
    end)
  (λ x y t₁ t₂ p (r : ∀{a s₁ s₂}, t₁≈a|s₁ → t₂≈a|s₂ → s₁ ~ s₂) a s₁ s₂ e₁ e₂,
    match s₁, s₂, qeq_split e₁, qeq_split e₂ with ._, ._, ⟨s₁₁, s₁₂, rfl, C₁⟩, ⟨s₂₁, s₂₂, rfl, C₂⟩ :=
    discr₂ C₁
      (λe₁ e₂ ya, match s₁₁, s₁₂, y, e₁, e₂, ya, C₂ with ._, ._, ._, rfl, rfl, rfl, C₂ := discr₂ C₂
        (λe₁ e₂ xa, match s₂₁, s₂₂, x, e₁, e₂, xa with
        | ._, ._, ._, rfl, rfl, rfl := skip a p end)
        (λe₁ _ e₂, match s₂₁, s₂₂, e₁, e₂ with
        | ._, ._, rfl, rfl := skip x p end)
        (λt₃ e₁ e₂, match s₂₁, t₂, e₁, e₂, p with
        | ._, ._, rfl, rfl, p := skip x (trans p (perm_middle _ _ _).symm) end)
        end)
      (λe₁ xa e₂, match s₁₁, s₁₂, x, e₁, e₂, xa, C₂ with ._, ._, ._, rfl, rfl, rfl, C₂ := discr₂ C₂
        (λe₁ e₂ _, match s₂₁, s₂₂, e₁, e₂ with
        | ._, ._, rfl, rfl := skip y p end)
        (λe₁ ya e₂, match s₂₁, s₂₂, y, e₁, e₂, ya with
        | ._, ._, ._, rfl, rfl, rfl := skip a p end)
        (λt₃ e₁ e₂, match s₂₁, t₂, e₁, e₂, p with
        | ._, ._, rfl, rfl, p := trans (skip y $ trans p (perm_middle _ _ _).symm) (swap _ _ _) end)
        end)
      (λt₃ e₁ e₂, match s₁₁, t₁, e₁, e₂, C₂, p, @r with ._, ._, rfl, rfl, C₂, p, r := discr₂ C₂
        (λe₁ e₂ xa, match s₂₁, s₂₂, x, e₁, e₂, xa with
        | ._, ._, ._, rfl, rfl, rfl := skip y (trans (perm_middle _ _ _) p) end)
        (λe₁ ya e₂, match s₂₁, s₂₂, y, e₁, e₂, ya with
        | ._, ._, ._, rfl, rfl, rfl := trans (swap _ _ _) (skip x $ trans (perm_middle _ _ _) p) end)
        (λt₄ e₁ e₂, match s₂₁, t₂, e₁, e₂, @r with
        | ._, ._, rfl, rfl, r := trans (swap _ _ _) (skip x $ skip y $ r (qeq_app _ _ _) (qeq_app _ _ _)) end)
        end)
    end)
  (λ t₁ t₂ t₃ p₁ p₂
     (r₁ : ∀{a s₁ s₂}, t₁ ≈ a|s₁ → t₂≈a|s₂ → s₁ ~ s₂)
     (r₂ : ∀{a s₁ s₂}, t₂ ≈ a|s₁ → t₃≈a|s₂ → s₁ ~ s₂)
     a s₁ s₂ e₁ e₂,
    let ⟨t₂', e₂'⟩ := qeq_of_mem $ mem_of_perm p₁ $ mem_head_of_qeq e₁ in
    trans (r₁ e₁ e₂') (r₂ e₂' e₂))
end qeq

theorem perm_cons_inv {a : α} {l₁ l₂ : list α} (p : a::l₁ ~ a::l₂) : l₁ ~ l₂ :=
perm_inv_core p (qeq.qhead a l₁) (qeq.qhead a l₂)

theorem perm_app_inv_left {l₁ l₂ : list α} : ∀ {l}, l++l₁ ~ l++l₂ → l₁ ~ l₂
| []     p := p
| (a::l) p := perm_app_inv_left (perm_cons_inv p)

theorem perm_app_inv_right {l₁ l₂ l : list α} (p : l₁++l ~ l₂++l) : l₁ ~ l₂ :=
perm_app_inv_left $ trans perm_app_comm $ trans p perm_app_comm

theorem perm_app_inv {a : α} {l₁ l₂ l₃ l₄ : list α} (p : l₁++(a::l₂) ~ l₃++(a::l₄)) : l₁++l₂ ~ l₃++l₄ :=
perm_cons_inv $ trans (perm_middle _ _ _) $ trans p $ (perm_middle _ _ _).symm

theorem foldl_eq_of_perm {f : β → α → β} {l₁ l₂ : list α} (rcomm : right_commutative f) (p : l₁ ~ l₂) :
  ∀ b, foldl f b l₁ = foldl f b l₂ :=
perm_induction_on p
  (λ b, rfl)
  (λ x t₁ t₂ p r b, r (f b x))
  (λ x y t₁ t₂ p r b, by simp; rw rcomm; exact r (f (f b x) y))
  (λ t₁ t₂ t₃ p₁ p₂ r₁ r₂ b, eq.trans (r₁ b) (r₂ b))

theorem foldr_eq_of_perm {f : α → β → β} {l₁ l₂ : list α} (lcomm : left_commutative f) (p : l₁ ~ l₂) :
  ∀ b, foldr f b l₁ = foldr f b l₂ :=
perm_induction_on p
  (λ b, rfl)
  (λ x t₁ t₂ p r b, by simp; rw [r b])
  (λ x y t₁ t₂ p r b, by simp; rw [lcomm, r b])
  (λ t₁ t₂ t₃ p₁ p₂ r₁ r₂ a, eq.trans (r₁ a) (r₂ a))

-- attribute [congr]
theorem erase_perm_erase_of_perm [decidable_eq α] (a : α) {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  l₁.erase a ~ l₂.erase a :=
if h₁ : a ∈ l₁ then
have h₂ : a ∈ l₂, from mem_of_perm p h₁,
perm_cons_inv $ trans (perm_erase h₁).symm $ trans p (perm_erase h₂)
else
have h₂ : a ∉ l₂, from not_mem_of_perm p h₁,
by rw [erase_of_not_mem h₁, erase_of_not_mem h₂]; exact p

-- attribute [congr]
theorem perm_erase_dup_of_perm [H : decidable_eq α] {l₁ l₂ : list α} :
  l₁ ~ l₂ → erase_dup l₁ ~ erase_dup l₂ :=
assume p, perm_induction_on p
  nil
  (λ x t₁ t₂ p r, by_cases
    (λ xint₁  : x ∈ t₁,
      have xint₂ : x ∈ t₂, from mem_of_mem_erase_dup (mem_of_perm r (mem_erase_dup xint₁)),
      begin rw [erase_dup_cons_of_mem xint₁, erase_dup_cons_of_mem xint₂], exact r end)
    (λ nxint₁ : x ∉ t₁,
      have nxint₂ : x ∉ t₂, from
         assume xint₂ : x ∈ t₂,
         absurd (mem_of_mem_erase_dup (mem_of_perm (perm.symm r) (mem_erase_dup xint₂))) nxint₁,
      begin rw [erase_dup_cons_of_not_mem nxint₂, erase_dup_cons_of_not_mem nxint₁],
            exact (skip x r) end))
  (λ y x t₁ t₂ p r, by_cases
    (λ xinyt₁  : x ∈ y::t₁, by_cases
      (λ yint₁  : y ∈ t₁,
        have yint₂  : y ∈ t₂,    from mem_of_mem_erase_dup (mem_of_perm r (mem_erase_dup yint₁)),
        have yinxt₂ : y ∈ x::t₂, from or.inr (yint₂),
        or.elim (eq_or_mem_of_mem_cons xinyt₁)
          (λ xeqy  : x = y,
            have xint₂ : x ∈ t₂, begin rw [←xeqy] at yint₂, exact yint₂ end,
            begin
              rw [erase_dup_cons_of_mem xinyt₁, erase_dup_cons_of_mem yinxt₂,
                       erase_dup_cons_of_mem yint₁, erase_dup_cons_of_mem xint₂],
              exact r
            end)
          (λ xint₁ : x ∈ t₁,
            have xint₂ : x ∈ t₂, from mem_of_mem_erase_dup (mem_of_perm r (mem_erase_dup xint₁)),
            begin
              rw [erase_dup_cons_of_mem xinyt₁, erase_dup_cons_of_mem yinxt₂,
                       erase_dup_cons_of_mem yint₁, erase_dup_cons_of_mem xint₂],
              exact r
            end))
      (λ nyint₁ : y ∉ t₁,
        have nyint₂ : y ∉ t₂, from
          assume yint₂ : y ∈ t₂,
            absurd (mem_of_mem_erase_dup (mem_of_perm (perm.symm r) (mem_erase_dup yint₂))) nyint₁,
        by_cases
          (λ xeqy  : x = y,
            have nxint₂ : x ∉ t₂, begin rw [←xeqy] at nyint₂, exact nyint₂ end,
            have yinxt₂ : y ∈ x::t₂, begin rw [xeqy], apply mem_cons_self end,
            begin
              rw [erase_dup_cons_of_mem xinyt₁, erase_dup_cons_of_mem yinxt₂,
                       erase_dup_cons_of_not_mem nyint₁, erase_dup_cons_of_not_mem nxint₂, xeqy],
              exact skip y r
            end)
          (λ xney : x ≠ y,
            have x ∈ t₁, from or_resolve_right xinyt₁ xney,
            have x ∈ t₂, from mem_of_mem_erase_dup (mem_of_perm r (mem_erase_dup this)),
            have y ∉ x::t₂, from
              assume : y ∈ x::t₂, or.elim (eq_or_mem_of_mem_cons this)
                (λ h, absurd h (ne.symm xney))
                (λ h, absurd h nyint₂),
            begin
              rw [erase_dup_cons_of_mem xinyt₁, erase_dup_cons_of_not_mem ‹y ∉ x::t₂›,
                       erase_dup_cons_of_not_mem nyint₁, erase_dup_cons_of_mem ‹x ∈ t₂›],
              exact skip y r
            end)))
    (λ nxinyt₁ : x ∉ y::t₁,
      have xney    : x ≠ y,  from ne_of_not_mem_cons nxinyt₁,
      have nxint₁  : x ∉ t₁, from not_mem_of_not_mem_cons nxinyt₁,
      have nxint₂  : x ∉ t₂, from
        assume xint₂ : x ∈ t₂,
          absurd (mem_of_mem_erase_dup (mem_of_perm (perm.symm r) (mem_erase_dup xint₂))) nxint₁,
      by_cases
        (λ yint₁  : y ∈ t₁,
          have yinxt₂ : y ∈ x::t₂,
            from or.inr (mem_of_mem_erase_dup (mem_of_perm r (mem_erase_dup yint₁))),
          begin
            rw [erase_dup_cons_of_not_mem nxinyt₁, erase_dup_cons_of_mem yinxt₂,
                     erase_dup_cons_of_mem yint₁, erase_dup_cons_of_not_mem nxint₂],
            exact skip x r
          end)
        (λ nyint₁ : y ∉ t₁,
          have nyinxt₂ : y ∉ x::t₂, from
            assume yinxt₂ : y ∈ x::t₂, or.elim (eq_or_mem_of_mem_cons yinxt₂)
              (λ h, absurd h (ne.symm xney))
              (λ h, absurd (mem_of_mem_erase_dup (mem_of_perm (r.symm) (mem_erase_dup h))) nyint₁),
          begin
            rw [erase_dup_cons_of_not_mem nxinyt₁, erase_dup_cons_of_not_mem nyinxt₂,
                     erase_dup_cons_of_not_mem nyint₁, erase_dup_cons_of_not_mem nxint₂],
            exact xswap x y r
          end)))
  (λ t₁ t₂ t₃ p₁ p₂ r₁ r₂, trans r₁ r₂)

section perm_union
variable [decidable_eq α]

theorem perm_union_left {l₁ l₂ : list α} (t₁ : list α) (h : l₁ ~ l₂) : (l₁ ∪ t₁) ~ (l₂ ∪ t₁) :=
begin
  induction t₁ with a t ih generalizing l₁ l₂,
  { exact h },
  exact
    if ha₁ : a ∈ l₁ then
      have ha₂ : a ∈ l₂, from mem_of_perm h ha₁,
      begin simp [ha₁, ha₂], apply ih h end
    else
      have ha₂ : a ∉ l₂, from assume otherwise, ha₁ (mem_of_perm h.symm otherwise),
      begin simp [ha₁, ha₂], apply ih, apply perm_app_left, exact h end
end

lemma perm_insert_insert (x y : α) (l : list α) :
  insert x (insert y l) ~ insert y (insert x l) :=
if yl : y ∈ l then
  if xl : x ∈ l then by simp [xl, yl]
  else by simp [xl, yl]
else
  if xl : x ∈ l then by simp [xl, yl]
  else
    if xy : x = y then by simp [xy, xl, yl]
    else
      have h₁ : x ∉ l ++ [y], begin intro h, simp at h, cases h, repeat { contradiction } end,
      have h₂ : y ∉ l ++ [x], begin intro h, simp at h, cases h with h₃, exact xy h₃.symm,
                                    contradiction end,
      begin simp [xl, yl, h₁, h₂], apply perm_app_right, apply perm.swap end

theorem perm_union_right (l : list α) {t₁ t₂ : list α} (h : t₁ ~ t₂) : (l ∪ t₁) ~ (l ∪ t₂) :=
begin
  induction h using list.perm.rec_on generalizing l,
  { refl },
  { apply ih_1 },
  { simp, apply perm_union_left, apply perm_insert_insert },
  { exact perm.trans (ih_1 l) (ih_2 l) }
end

-- attribute [congr]
theorem perm_union {l₁ l₂ t₁ t₂ : list α} : l₁ ~ l₂ → t₁ ~ t₂ → (l₁ ∪ t₁) ~ (l₂ ∪ t₂) :=
assume p₁ p₂, trans (perm_union_left t₁ p₁) (perm_union_right l₂ p₂)
end perm_union

section perm_insert
variable [H : decidable_eq α]
include H

-- attribute [congr]
theorem perm_insert (a : α) {l₁ l₂ : list α} : l₁ ~ l₂ → (insert a l₁) ~ (insert a l₂) :=
assume p,
if al₁ : a ∈ l₁ then
  have al₂ : a ∈ l₂, from mem_of_perm p al₁,
  begin simp [al₁, al₂], exact p end
else
  have al₂ : a ∉ l₂, from assume otherwise, al₁ (mem_of_perm p.symm otherwise),
  begin simp [al₁, al₂], exact perm_app_left _ p end

end perm_insert

section perm_inter
variable [decidable_eq α]

theorem perm_inter_left {l₁ l₂ : list α} (t₁ : list α) : l₁ ~ l₂ → (l₁ ∩ t₁) ~ (l₂ ∩ t₁) :=
assume p, perm.rec_on p
  (perm.refl _)
  (λ x l₁ l₂ p₁ r₁, by_cases
    (λ xint₁  : x ∈ t₁, begin rw [inter_cons_of_mem _ xint₁, inter_cons_of_mem _ xint₁],
                              exact (skip x r₁) end)
    (λ nxint₁ : x ∉ t₁, begin rw [inter_cons_of_not_mem _ nxint₁, inter_cons_of_not_mem _ nxint₁],
                              exact r₁ end))
  (λ x y l, by_cases
    (λ yint  : y ∈ t₁, by_cases
      (λ xint  : x ∈ t₁,
        begin rw [inter_cons_of_mem _ xint, inter_cons_of_mem _ yint,
                  inter_cons_of_mem _ yint, inter_cons_of_mem _ xint],
           apply swap end)
      (λ nxint : x ∉ t₁,
        begin rw [inter_cons_of_mem _ yint, inter_cons_of_not_mem _ nxint,
                    inter_cons_of_not_mem _ nxint, inter_cons_of_mem _ yint] end))
    (λ nyint : y ∉ t₁, by_cases
      (λ xint  : x ∈ t₁,
        by rw [inter_cons_of_mem _ xint, inter_cons_of_not_mem _ nyint,
               inter_cons_of_not_mem _ nyint, inter_cons_of_mem _ xint])
      (λ nxint : x ∉ t₁,
        by rw [inter_cons_of_not_mem _ nxint, inter_cons_of_not_mem _ nyint,
                     inter_cons_of_not_mem _ nyint, inter_cons_of_not_mem _ nxint])))
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₁ r₂)

theorem perm_inter_right (l : list α) {t₁ t₂ : list α} : t₁ ~ t₂ → (l ∩ t₁) ~ (l ∩ t₂) :=
list.rec_on l
  (λ p, by simp [inter_nil])
  (λ x xs r p, by_cases
    (λ xint₁  : x ∈ t₁,
      have xint₂ : x ∈ t₂, from mem_of_perm p xint₁,
      begin rw [inter_cons_of_mem _ xint₁, inter_cons_of_mem _ xint₂], exact (skip _ (r p)) end)
    (λ nxint₁ : x ∉ t₁,
      have nxint₂ : x ∉ t₂, from not_mem_of_perm p nxint₁,
      begin rw [inter_cons_of_not_mem _ nxint₁, inter_cons_of_not_mem _ nxint₂], exact (r p) end))

-- attribute [congr]
theorem perm_inter {l₁ l₂ t₁ t₂ : list α} : l₁ ~ l₂ → t₁ ~ t₂ → (l₁ ∩ t₁) ~ (l₂ ∩ t₂) :=
assume p₁ p₂, trans (perm_inter_left t₁ p₁) (perm_inter_right l₂ p₂)
end perm_inter

/- extensionality -/
section ext

theorem perm_ext : ∀ {l₁ l₂ : list α}, nodup l₁ → nodup l₂ → (∀a, a ∈ l₁ ↔ a ∈ l₂) → l₁ ~ l₂
| []       []       d₁ d₂ e := perm.nil
| []       (a₂::t₂) d₁ d₂ e := absurd (iff.mpr (e a₂) (mem_cons_self _ _)) (not_mem_nil a₂)
| (a₁::t₁) []       d₁ d₂ e := absurd (iff.mp (e a₁) (mem_cons_self _ _)) (not_mem_nil a₁)
| (a₁::t₁) (a₂::t₂) d₁ d₂ e :=
  have a₁ ∈ a₂::t₂, from iff.mp (e a₁) (mem_cons_self _ _),
  have ∃ s₁ s₂, a₂::t₂ = s₁++(a₁::s₂), from mem_split this,
  --  obtain (s₁ s₂ : list α) (t₂_eq : a₂::t₂ = s₁++(a₁::s₂)), from this,
  match this with
  | ⟨ s₁, s₂, (t₂_eq : a₂::t₂ = s₁++(a₁::s₂)) ⟩ :=
  have dt₂'     : nodup (a₁::(s₁++s₂)), from nodup_head (begin rw [t₂_eq] at d₂, exact d₂ end),
  have eqv      : ∀a, a ∈ t₁ ↔ a ∈ s₁++s₂, from
    assume a, iff.intro
      (assume :  a ∈ t₁,
         have a ∈ a₂::t₂,       from iff.mp (e a) (mem_cons_of_mem _ this),
         have a ∈ s₁++(a₁::s₂), begin rw [t₂_eq] at this, exact this end,
         or.elim (mem_or_mem_of_mem_append this)
           (assume : a ∈ s₁, mem_append_left s₂ this)
           (assume : a ∈ a₁::s₂, or.elim (eq_or_mem_of_mem_cons this)
             (assume : a = a₁,
               have a₁ ∉ t₁, from not_mem_of_nodup_cons d₁,
               begin subst a, contradiction end)
             (assume : a ∈ s₂, mem_append_right s₁ this)))
      (assume : a ∈ s₁ ++ s₂, or.elim (mem_or_mem_of_mem_append this)
        (assume : a ∈ s₁,
           have a ∈ a₂::t₂, from begin rw [t₂_eq], exact (mem_append_left _ this) end,
           have a ∈ a₁::t₁, from iff.mpr (e a) this,
           or.elim (eq_or_mem_of_mem_cons this)
             (assume : a = a₁,
                have a₁ ∉ s₁++s₂, from not_mem_of_nodup_cons dt₂',
                have a₁ ∉ s₁,     from not_mem_of_not_mem_append_left this,
                begin subst a, contradiction end)
             (assume : a ∈ t₁, this))
        (assume : a ∈ s₂,
           have a ∈ a₂::t₂, from begin rw [t₂_eq],
                                       exact (mem_append_right _ (mem_cons_of_mem _ this)) end,
           have a ∈ a₁::t₁, from iff.mpr (e a) this,
           or.elim (eq_or_mem_of_mem_cons this)
             (assume : a = a₁,
               have a₁ ∉ s₁++s₂, from not_mem_of_nodup_cons dt₂',
               have a₁ ∉ s₂, from not_mem_of_not_mem_append_right this,
               begin subst a, contradiction end)
             (assume : a ∈ t₁, this))),
  have ds₁s₂ : nodup (s₁++s₂), from nodup_of_nodup_cons dt₂',
  have nodup t₁, from nodup_of_nodup_cons d₁,
  calc a₁::t₁ ~ a₁::(s₁++s₂) : skip a₁ (perm_ext this ds₁s₂ eqv)
         ...  ~ s₁++(a₁::s₂) : perm_middle _ _ _
         ...  = a₂::t₂       : by rw t₂_eq
  end
end ext

theorem nodup_of_perm_of_nodup {l₁ l₂ : list α} : l₁ ~ l₂ → nodup l₁ → nodup l₂ :=
assume h, perm.rec_on h
  (λ h, h)
  (λ a l₁ l₂ p ih nd,
    have nodup l₁, from nodup_of_nodup_cons nd,
    have nodup l₂, from ih this,
    have a ∉ l₁,   from not_mem_of_nodup_cons nd,
    have a ∉ l₂,   from assume : a ∈ l₂, absurd (mem_of_perm (perm.symm p) this) ‹a ∉ l₁›,
    nodup_cons ‹a ∉ l₂› ‹nodup l₂›)
  (λ x y l₁ nd,
    have nodup (x::l₁),    from nodup_of_nodup_cons nd,
    have nodup l₁,         from nodup_of_nodup_cons this,
    have x ∉ l₁,           from not_mem_of_nodup_cons ‹nodup (x::l₁)›,
    have y ∉ x::l₁,        from not_mem_of_nodup_cons nd,
    have x ≠ y,            from assume : x = y,
                                begin subst x, apply absurd (mem_cons_self _ _), apply ‹y ∉ y::l₁› end, -- this line used to be "exact absurd (mem_cons_self _ _) ‹y ∉ y::l₁›, but it's now a syntax error
    have y ∉ l₁,           from not_mem_of_not_mem_cons ‹y ∉ x::l₁›,
    have x ∉ y::l₁,        from not_mem_cons_of_ne_of_not_mem ‹x ≠ y› ‹x ∉ l₁›,
    have nodup (y::l₁),    from nodup_cons ‹y ∉ l₁› ‹nodup l₁›,
    show nodup (x::y::l₁), from nodup_cons ‹x ∉ y::l₁› ‹nodup (y::l₁)›)
  (λ l₁ l₂ l₃ p₁ p₂ ih₁ ih₂ nd, ih₂ (ih₁ nd))

/- product -/
section product
theorem perm_product_left {l₁ l₂ : list α} (t₁ : list β) :
  l₁ ~ l₂ → (product l₁ t₁) ~ (product l₂ t₁) :=
assume p : l₁ ~ l₂, perm.rec_on p
  (perm.refl _)
  (λ x l₁ l₂ p r, perm_app (perm.refl (map _ t₁)) r)
  (λ x y l,
    let m₁ := map (λ b, (x, b)) t₁ in
    let m₂ := map (λ b, (y, b)) t₁ in
    let c  := product l t₁ in
    calc m₂ ++ (m₁ ++ c) = (m₂ ++ m₁) ++ c  : by rw append.assoc
                     ... ~ (m₁ ++ m₂) ++ c  : perm_app perm_app_comm (perm.refl _)
                     ... =  m₁ ++ (m₂ ++ c) : by rw append.assoc)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₁ r₂)

theorem perm_product_right (l : list α) {t₁ t₂ : list β} :
  t₁ ~ t₂ → (product l t₁) ~ (product l t₂) :=
list.rec_on l
  (λ p, by simp [nil_product])
  (λ (a : α) (t : list α) (r : t₁ ~ t₂ → product t t₁ ~ product t t₂) (p : t₁ ~ t₂),
    perm_app (perm_map (λ b : β, (a, b)) p) (r p))

attribute [congr]
theorem perm_product {l₁ l₂ : list α} {t₁ t₂ : list β} :
  l₁ ~ l₂ → t₁ ~ t₂ → (product l₁ t₁) ~ (product l₂ t₂) :=
assume p₁ p₂, trans (perm_product_left t₁ p₁) (perm_product_right l₂ p₂)
end product

/- filter -/
-- attribute [congr]
theorem perm_filter {l₁ l₂ : list α} {p : α → Prop} [decidable_pred p] :
  l₁ ~ l₂ → (filter p l₁) ~ (filter p l₂) :=
assume u, perm.rec_on u
  perm.nil
  (assume x l₁' l₂',
    assume u' : l₁' ~ l₂',
    assume u'' : filter p l₁' ~ filter p l₂',
    decidable.by_cases
      (assume : p x, begin rw [filter_cons_of_pos _ this, filter_cons_of_pos _ this],
                          apply perm.skip, apply u'' end)
      (assume : ¬ p x, begin rw [filter_cons_of_neg _ this, filter_cons_of_neg _ this],
                            apply u'' end))
  (assume x y l,
    decidable.by_cases
      (assume H1 : p x,
        decidable.by_cases
          (assume H2 : p y,
             begin
               rw [filter_cons_of_pos _ H1, filter_cons_of_pos _ H2, filter_cons_of_pos _ H2,
                   filter_cons_of_pos _ H1],
               apply perm.swap
             end)
          (assume H2 : ¬ p y,
             by rw [filter_cons_of_pos _ H1, filter_cons_of_neg _ H2, filter_cons_of_neg _ H2,
                    filter_cons_of_pos _ H1]))
      (assume H1 : ¬ p x,
        decidable.by_cases
          (assume H2 : p y,
             by rw [filter_cons_of_neg _ H1, filter_cons_of_pos _ H2, filter_cons_of_pos _ H2,
                    filter_cons_of_neg _ H1])
          (assume H2 : ¬ p y,
             by rw [filter_cons_of_neg _ H1, filter_cons_of_neg _ H2, filter_cons_of_neg _ H2,
                    filter_cons_of_neg _ H1])))
    (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₁ r₂)
end perm
end list
