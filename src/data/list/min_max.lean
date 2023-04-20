/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Chris Hughes, Mantas Bakšys
-/
import data.list.basic

/-!
# Minimum and maximum of lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

The main definitions are `argmax`, `argmin`, `minimum` and `maximum` for lists.

`argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such that
  `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
  `argmax f []` = none`

`minimum l` returns an `with_top α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`
-/

namespace list

variables {α β : Type*}

section arg_aux
variables (r : α → α → Prop) [decidable_rel r] {l : list α} {o : option α} {a m : α}

/-- Auxiliary definition for `argmax` and `argmin`. -/
def arg_aux (a : option α) (b : α) : option α :=
option.cases_on a (some b) $ λ c, if r b c then some b else some c

@[simp] lemma foldl_arg_aux_eq_none :
  l.foldl (arg_aux r) o = none ↔ l = [] ∧ o = none :=
list.reverse_rec_on l (by simp) $
  (assume tl hd, by simp [arg_aux];
    cases foldl (arg_aux r) o tl; simp; try {split_ifs}; simp)

private lemma foldl_arg_aux_mem (l) : Π (a m : α),
  m ∈ foldl (arg_aux r) (some a) l → m ∈ a :: l :=
list.reverse_rec_on l (by simp [eq_comm])
  begin
    assume tl hd ih a m,
    simp only [foldl_append, foldl_cons, foldl_nil, arg_aux],
    cases hf : foldl (arg_aux r) (some a) tl,
    { simp {contextual := tt} },
    { dsimp only, split_ifs,
      { simp {contextual := tt} },
      { -- `finish [ih _ _ hf]` closes this goal
        rcases ih _ _ hf with rfl | H,
        { simp only [mem_cons_iff, mem_append, mem_singleton, option.mem_def], tauto },
        { apply λ hm, or.inr (list.mem_append.mpr $ or.inl _),
          exact (option.mem_some_iff.mp hm ▸ H)} } }
  end

@[simp] lemma arg_aux_self (hr₀ : irreflexive r) (a : α) : arg_aux r (some a) a = a :=
if_neg $ hr₀ _

lemma not_of_mem_foldl_arg_aux (hr₀ : irreflexive r) (hr₁ : transitive r) :
  Π {a m : α} {o : option α}, a ∈ l → m ∈ foldl (arg_aux r) o l → ¬ r a m :=
begin
  induction l using list.reverse_rec_on with tl a ih,
  { exact λ _ _ _ h, absurd h $ not_mem_nil _ },
  intros b m o hb ho,
  rw [foldl_append, foldl_cons, foldl_nil, arg_aux] at ho,
  cases hf : foldl (arg_aux r) o tl with c,
  { rw [hf] at ho,
    rw [foldl_arg_aux_eq_none] at hf,
    simp [hf.1, hf.2, *, hr₀ _] at * },
  rw [hf, option.mem_def] at ho,
  dsimp only at ho,
  split_ifs at ho with hac hac; cases mem_append.1 hb with h h; subst ho,
  { exact λ hba, ih h hf (hr₁ hba hac) },
  { simp [*, hr₀ _] at * },
  { exact ih h hf },
  { simp * at * }
end

end arg_aux

section preorder
variables [preorder β] [@decidable_rel β (<)] {f : α → β} {l : list α} {o : option α} {a m : α}

/-- `argmax f l` returns `some a`, where `f a` is maximal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f a < f b`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmax f []` = none`. -/
def argmax (f : α → β) (l : list α) : option α := l.foldl (arg_aux $ λ b c, f c < f b) none

/-- `argmin f l` returns `some a`, where `f a` is minimal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f b < f a`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmin f []` = none`. -/
def argmin (f : α → β) (l : list α) := l.foldl (arg_aux $ λ b c, f b < f c) none

@[simp] lemma argmax_nil (f : α → β) : argmax f [] = none := rfl
@[simp] lemma argmin_nil (f : α → β) : argmin f [] = none := rfl

@[simp] lemma argmax_singleton {f : α → β} {a : α} : argmax f [a] = a := rfl
@[simp] lemma argmin_singleton {f : α → β} {a : α} : argmin f [a] = a := rfl

lemma not_lt_of_mem_argmax : a ∈ l → m ∈ argmax f l → ¬ f m < f a :=
not_of_mem_foldl_arg_aux _ (λ _ , lt_irrefl _) $ λ _ _ _, gt_trans

lemma not_lt_of_mem_argmin : a ∈ l → m ∈ argmin f l → ¬ f a < f m :=
not_of_mem_foldl_arg_aux _ (λ _ , lt_irrefl _) $ λ _ _ _, lt_trans

theorem argmax_concat (f : α → β) (a : α) (l : list α) : argmax f (l ++ [a]) =
  option.cases_on (argmax f l) (some a) (λ c, if f c < f a then some a else some c) :=
by rw [argmax, argmax]; simp [arg_aux]

theorem argmin_concat (f : α → β) (a : α) (l : list α) : argmin f (l ++ [a]) =
  option.cases_on (argmin f l) (some a) (λ c, if f a < f c then some a else some c) :=
@argmax_concat _ βᵒᵈ _ _ _ _ _

theorem argmax_mem : Π {l : list α} {m : α}, m ∈ argmax f l → m ∈ l
| [] m       := by simp
| (hd::tl) m := by simpa [argmax, arg_aux] using foldl_arg_aux_mem _ tl hd m

theorem argmin_mem : Π {l : list α} {m : α}, m ∈ argmin f l → m ∈ l := @argmax_mem _ βᵒᵈ _ _ _

@[simp] theorem argmax_eq_none : l.argmax f = none ↔ l = [] := by simp [argmax]
@[simp] theorem argmin_eq_none : l.argmin f = none ↔ l = [] := @argmax_eq_none _ βᵒᵈ _ _ _ _

end preorder

section linear_order
variables [linear_order β] {f : α → β} {l : list α} {o : option α} {a m : α}

theorem le_of_mem_argmax : a ∈ l → m ∈ argmax f l → f a ≤ f m :=
λ ha hm, le_of_not_lt $ not_lt_of_mem_argmax ha hm

theorem le_of_mem_argmin : a ∈ l → m ∈ argmin f l → f m ≤ f a := @le_of_mem_argmax _ βᵒᵈ _ _ _ _ _

theorem argmax_cons (f : α → β) (a : α) (l : list α) : argmax f (a :: l) =
  option.cases_on (argmax f l) (some a) (λ c, if f a < f c then some c else some a) :=
list.reverse_rec_on l rfl $ λ hd tl ih, begin
    rw [← cons_append, argmax_concat, ih, argmax_concat],
    cases h : argmax f hd with m,
    { simp [h] },
    dsimp,
    rw [←apply_ite, ←apply_ite],
    dsimp,
    split_ifs; try { refl },
    { exact absurd (lt_trans ‹f a < f m› ‹_›) ‹_› },
    { cases (‹f a < f tl›.lt_or_lt _).elim ‹_› ‹_› }
  end

theorem argmin_cons (f : α → β) (a : α) (l : list α) : argmin f (a :: l) =
  option.cases_on (argmin f l) (some a) (λ c, if f c < f a then some c else some a) :=
by convert @argmax_cons _ βᵒᵈ _ _ _ _

variables [decidable_eq α]

theorem index_of_argmax : Π {l : list α} {m : α}, m ∈ argmax f l →
  ∀ {a}, a ∈ l → f m ≤ f a → l.index_of m ≤ l.index_of a
| []       m _  _ _  _   := by simp
| (hd::tl) m hm a ha ham := begin
  simp only [index_of_cons, argmax_cons, option.mem_def] at ⊢ hm,
  cases h : argmax f tl,
  { rw h at hm,
    simp * at * },
  rw h at hm,
  dsimp only at hm,
  obtain rfl | ha := ha; split_ifs at hm; subst hm,
  { cases not_le_of_lt ‹_› ‹_› },
  { rw [if_neg, if_neg],
    exact nat.succ_le_succ (index_of_argmax h ha ham),
    { exact ne_of_apply_ne f (lt_of_lt_of_le ‹_› ‹_›).ne' },
    { exact ne_of_apply_ne _ ‹f hd < f val›.ne' } },
  { rw if_pos rfl,
    exact bot_le }
end

theorem index_of_argmin : Π {l : list α} {m : α}, m ∈ argmin f l →
  ∀ {a}, a ∈ l → f a ≤ f m → l.index_of m ≤ l.index_of a :=
@index_of_argmax _ βᵒᵈ _ _ _

theorem mem_argmax_iff :
  m ∈ argmax f l ↔ m ∈ l ∧ (∀ a ∈ l, f a ≤ f m) ∧
    ∀ a ∈ l, f m ≤ f a → l.index_of m ≤ l.index_of a :=
⟨λ hm, ⟨argmax_mem hm, λ a ha, le_of_mem_argmax ha hm, λ _, index_of_argmax hm⟩,
  begin
    rintros ⟨hml, ham, hma⟩,
    cases harg : argmax f l with n,
    { simp * at * },
    { have := le_antisymm (hma n (argmax_mem harg) (le_of_mem_argmax hml harg))
        (index_of_argmax harg hml (ham _ (argmax_mem harg))),
      rw [(index_of_inj hml (argmax_mem harg)).1 this, option.mem_def] }
  end⟩

theorem argmax_eq_some_iff :
  argmax f l = some m ↔ m ∈ l ∧ (∀ a ∈ l, f a ≤ f m) ∧
    ∀ a ∈ l, f m ≤ f a → l.index_of m ≤ l.index_of a := mem_argmax_iff

theorem mem_argmin_iff :
  m ∈ argmin f l ↔ m ∈ l ∧ (∀ a ∈ l, f m ≤ f a) ∧
    ∀ a ∈ l, f a ≤ f m → l.index_of m ≤ l.index_of a :=
@mem_argmax_iff _ βᵒᵈ _ _ _ _ _

theorem argmin_eq_some_iff :
  argmin f l = some m ↔ m ∈ l ∧ (∀ a ∈ l, f m ≤ f a) ∧
    ∀ a ∈ l, f a ≤ f m → l.index_of m ≤ l.index_of a := mem_argmin_iff

end linear_order

section maximum_minimum
section preorder
variables [preorder α] [@decidable_rel α (<)] {l : list α} {a m : α}

/-- `maximum l` returns an `with_bot α`, the largest element of `l` for nonempty lists, and `⊥` for
`[]`  -/
def maximum (l : list α) : with_bot α := argmax id l

/-- `minimum l` returns an `with_top α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`  -/
def minimum (l : list α) : with_top α := argmin id l

@[simp] lemma maximum_nil : maximum ([] : list α) = ⊥ := rfl

@[simp] lemma minimum_nil : minimum ([] : list α) = ⊤ := rfl

@[simp] lemma maximum_singleton (a : α) : maximum [a] = a := rfl

@[simp] lemma minimum_singleton (a : α) : minimum [a] = a := rfl

theorem maximum_mem {l : list α} {m : α} : (maximum l : with_top α) = m → m ∈ l := argmax_mem

theorem minimum_mem {l : list α} {m : α} : (minimum l : with_bot α) = m → m ∈ l := argmin_mem

@[simp] theorem maximum_eq_none {l : list α} : l.maximum = none ↔ l = [] := argmax_eq_none

@[simp] theorem minimum_eq_none {l : list α} : l.minimum = none ↔ l = [] := argmin_eq_none

lemma not_lt_maximum_of_mem : a ∈ l → (maximum l : with_bot α) = m → ¬ m < a := not_lt_of_mem_argmax
lemma minimum_not_lt_of_mem : a ∈ l → (minimum l : with_top α) = m → ¬ a < m := not_lt_of_mem_argmin

theorem not_lt_maximum_of_mem' (ha : a ∈ l) : ¬ maximum l < (a : with_bot α) :=
begin
  cases h : l.maximum,
  { simp * at * },
  { simp_rw [with_bot.some_eq_coe, with_bot.coe_lt_coe, not_lt_maximum_of_mem ha h, not_false_iff] }
end

theorem not_lt_minimum_of_mem' (ha : a ∈ l) : ¬ (a : with_top α) < minimum l :=
@not_lt_maximum_of_mem' αᵒᵈ _ _ _ _ ha

end preorder

section linear_order
variables [linear_order α] {l : list α} {a m : α}

theorem maximum_concat (a : α) (l : list α) : maximum (l ++ [a]) = max (maximum l) a :=
begin
  simp only [maximum, argmax_concat, id],
  cases h : argmax id l,
  { exact (max_eq_right bot_le).symm },
  { simp [option.coe_def, max_def_lt], }
end

lemma le_maximum_of_mem : a ∈ l → (maximum l : with_bot α) = m → a ≤ m := le_of_mem_argmax
lemma minimum_le_of_mem : a ∈ l → (minimum l : with_top α) = m → m ≤ a := le_of_mem_argmin

lemma le_maximum_of_mem' (ha : a ∈ l) : (a : with_bot α) ≤ maximum l :=
le_of_not_lt $ not_lt_maximum_of_mem' ha

lemma le_minimum_of_mem' (ha : a ∈ l) : minimum l ≤ (a : with_top α) :=
@le_maximum_of_mem' αᵒᵈ _ _ _ ha

theorem minimum_concat (a : α) (l : list α) : minimum (l ++ [a]) = min (minimum l) a :=
@maximum_concat αᵒᵈ _ _ _

theorem maximum_cons (a : α) (l : list α) : maximum (a :: l) = max a (maximum l) :=
list.reverse_rec_on l (by simp [@max_eq_left (with_bot α) _ _ _ bot_le])
  (λ tl hd ih, by rw [← cons_append, maximum_concat, ih, maximum_concat, max_assoc])

theorem minimum_cons (a : α) (l : list α) : minimum (a :: l) = min a (minimum l) :=
@maximum_cons αᵒᵈ _ _ _

lemma maximum_eq_coe_iff : maximum l = m ↔ m ∈ l ∧ ∀ a ∈ l, a ≤ m :=
begin
  unfold_coes,
  simp only [maximum, argmax_eq_some_iff, id],
  split,
  { simp only [true_and, forall_true_iff] {contextual := tt} },
  { simp only [true_and, forall_true_iff] {contextual := tt},
    intros h a hal hma,
    rw [le_antisymm hma (h.2 a hal)] }
end

lemma minimum_eq_coe_iff : minimum l = m ↔ m ∈ l ∧ ∀ a ∈ l, m ≤ a :=
@maximum_eq_coe_iff αᵒᵈ _ _ _

end linear_order
end maximum_minimum

section fold
variables [linear_order α]

section order_bot
variables [order_bot α] {l : list α}

@[simp] lemma foldr_max_of_ne_nil (h : l ≠ []) : ↑(l.foldr max ⊥) = l.maximum :=
begin
  induction l with hd tl IH,
  { contradiction },
  { rw [maximum_cons, foldr, with_bot.coe_max],
    by_cases h : tl = [],
    { simp [h] },
    { simp [IH h] } }
end

lemma max_le_of_forall_le (l : list α) (a : α) (h : ∀ x ∈ l, x ≤ a) : l.foldr max ⊥ ≤ a :=
begin
  induction l with y l IH,
  { simp },
  { simpa [h y (mem_cons_self _ _)] using IH (λ x hx, h x $ mem_cons_of_mem _ hx) }
end

lemma le_max_of_le {l : list α} {a x : α} (hx : x ∈ l) (h : a ≤ x) :
  a ≤ l.foldr max ⊥ :=
begin
  induction l with y l IH,
  { exact absurd hx (not_mem_nil _), },
  { obtain rfl | hl := hx,
    simp only [foldr, foldr_cons],
    { exact le_max_of_le_left h, },
    { exact le_max_of_le_right (IH hl) }}
end

end order_bot

section order_top
variables [order_top α] {l : list α}

@[simp] lemma foldr_min_of_ne_nil (h : l ≠ []) : ↑(l.foldr min ⊤) = l.minimum :=
@foldr_max_of_ne_nil αᵒᵈ _ _ _ h

lemma le_min_of_forall_le (l : list α) (a : α) (h : ∀ x ∈ l, a ≤ x) : a ≤ l.foldr min ⊤ :=
@max_le_of_forall_le αᵒᵈ _ _ _ _ h

lemma min_le_of_le (l : list α) (a : α) {x : α} (hx : x ∈ l) (h : x ≤ a) :
  l.foldr min ⊤ ≤ a :=
@le_max_of_le αᵒᵈ _ _ _ _ _ hx h

end order_top
end fold
end list
