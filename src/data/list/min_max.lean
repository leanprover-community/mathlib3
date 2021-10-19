/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Chris Hughes
-/
import data.list.basic
/-!
# Minimum and maximum of lists

## Main definitions

The main definitions are `argmax`, `argmin`, `minimum` and `maximum` for lists.

`argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such that
  `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
  `argmax f []` = none`

`minimum l` returns an `with_top α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`
-/
namespace list
variables {α : Type*} {β : Type*} [linear_order β]

/-- Auxiliary definition to define `argmax` -/
def argmax₂ (f : α → β) (a : option α) (b : α) : option α :=
option.cases_on a (some b) (λ c, if f b ≤ f c then some c else some b)

/-- `argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such
that `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
`argmax f []` = none` -/
def argmax (f : α → β) (l : list α) : option α :=
l.foldl (argmax₂ f) none

/-- `argmin f l` returns `some a`, where `a` of `l` that minimises `f a`. If there are `a b` such
that `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
`argmin f []` = none` -/
def argmin (f : α → β) (l : list α) :=
@argmax _ (order_dual β) _ f l

@[simp] lemma argmax_two_self (f : α → β) (a : α) : argmax₂ f (some a) a = a :=
if_pos (le_refl _)

@[simp] lemma argmax_nil (f : α → β) : argmax f [] = none := rfl

@[simp] lemma argmin_nil (f : α → β) : argmin f [] = none := rfl

@[simp] lemma argmax_singleton {f : α → β} {a : α} : argmax f [a] = some a := rfl

@[simp] lemma argmin_singleton {f : α → β} {a : α} : argmin f [a] = a := rfl

@[simp] lemma foldl_argmax₂_eq_none {f : α → β} {l : list α} {o : option α} :
  l.foldl (argmax₂ f) o = none ↔ l = [] ∧ o = none :=
list.reverse_rec_on l (by simp) $
  (assume tl hd, by simp [argmax₂];
    cases foldl (argmax₂ f) o tl; simp; try {split_ifs}; simp)

private theorem le_of_foldl_argmax₂ {f : α → β} {l} : Π {a m : α} {o : option α}, a ∈ l →
  m ∈ foldl (argmax₂ f) o l → f a ≤ f m :=
list.reverse_rec_on l
  (λ _ _ _ h, absurd h $ not_mem_nil _)
  begin
    intros tl _ ih _ _ _ h ho,
    rw [foldl_append, foldl_cons, foldl_nil, argmax₂] at ho,
    cases hf : foldl (argmax₂ f) o tl,
    { rw [hf] at ho,
      rw [foldl_argmax₂_eq_none] at hf,
      simp [hf.1, hf.2, *] at * },
    rw [hf, option.mem_def] at ho,
    dsimp only at ho,
    cases mem_append.1 h with h h,
    { refine le_trans (ih h hf) _,
      have := @le_of_lt _ _ (f val) (f m),
      split_ifs at ho;
      simp * at * },
    { split_ifs at ho;
      simp * at * }
  end

private theorem foldl_argmax₂_mem (f : α → β) (l) : Π (a m : α),
  m ∈ foldl (argmax₂ f) (some a) l → m ∈ a :: l :=
list.reverse_rec_on l (by simp [eq_comm])
  begin
    assume tl hd ih a m,
    simp only [foldl_append, foldl_cons, foldl_nil, argmax₂],
    cases hf : foldl (argmax₂ f) (some a) tl,
    { simp {contextual := tt} },
    { dsimp only, split_ifs,
      { finish [ih _ _ hf] },
      { simp {contextual := tt} } }
  end

theorem argmax_mem {f : α → β} : Π {l : list α} {m : α}, m ∈ argmax f l → m ∈ l
| [] m       := by simp
| (hd::tl) m := by simpa [argmax, argmax₂] using foldl_argmax₂_mem f tl hd m

theorem argmin_mem {f : α → β} : Π {l : list α} {m : α}, m ∈ argmin f l → m ∈ l :=
@argmax_mem _ (order_dual β) _ _

@[simp] theorem argmax_eq_none {f : α → β} {l : list α} : l.argmax f = none ↔ l = [] :=
by simp [argmax]

@[simp] theorem argmin_eq_none {f : α → β} {l : list α} : l.argmin f = none ↔ l = [] :=
@argmax_eq_none _ (order_dual β) _ _ _

theorem le_argmax_of_mem {f : α → β} {a m : α} {l : list α} : a ∈ l → m ∈ argmax f l → f a ≤ f m :=
le_of_foldl_argmax₂

theorem argmin_le_of_mem {f : α → β} {a m : α} {l : list α} : a ∈ l → m ∈ argmin f l → f m ≤ f a:=
@le_argmax_of_mem _ (order_dual β) _ _ _ _ _

theorem argmax_concat (f : α → β) (a : α) (l : list α) : argmax f (l ++ [a]) =
  option.cases_on (argmax f l) (some a) (λ c, if f a ≤ f c then some c else some a) :=
by rw [argmax, argmax]; simp [argmax₂]

theorem argmin_concat (f : α → β) (a : α) (l : list α) : argmin f (l ++ [a]) =
  option.cases_on (argmin f l) (some a) (λ c, if f c ≤ f a then some c else some a) :=
@argmax_concat _ (order_dual β) _ _ _ _

theorem argmax_cons (f : α → β) (a : α) (l : list α) : argmax f (a :: l) =
  option.cases_on (argmax f l) (some a) (λ c, if f c ≤ f a then some a else some c) :=
list.reverse_rec_on l rfl $
  assume hd tl ih,  begin
    rw [← cons_append, argmax_concat, ih, argmax_concat],
    cases h : argmax f hd with m,
    { simp [h] },
    { simp [h], dsimp,
      by_cases ham : f m ≤ f a,
      { rw if_pos ham, dsimp,
        by_cases htlm : f tl ≤ f m,
        { rw if_pos htlm, dsimp,
          rw [if_pos (le_trans htlm ham), if_pos ham] },
        { rw if_neg htlm } },
      { rw if_neg ham, dsimp,
        by_cases htlm : f tl ≤ f m,
        { rw if_pos htlm, dsimp,
          rw if_neg ham },
        { rw if_neg htlm, dsimp,
          rw [if_neg (not_le_of_gt (lt_trans (lt_of_not_ge ham) (lt_of_not_ge htlm)))] } } }
  end

theorem argmin_cons (f : α → β) (a : α) (l : list α) : argmin f (a :: l) =
  option.cases_on (argmin f l) (some a) (λ c, if f a ≤ f c then some a else some c) :=
@argmax_cons _ (order_dual β) _ _ _ _

theorem index_of_argmax [decidable_eq α] {f : α → β} : Π {l : list α} {m : α}, m ∈ argmax f l →
  ∀ {a}, a ∈ l → f m ≤ f a → l.index_of m ≤ l.index_of a
| []       m _  _ _  _   := by simp
| (hd::tl) m hm a ha ham := begin
  simp only [index_of_cons, argmax_cons, option.mem_def] at ⊢ hm,
  cases h : argmax f tl,
  { rw h at hm,
    simp * at * },
  { rw h at hm,
    dsimp only at hm,
    cases ha with hahd hatl,
    { clear index_of_argmax,
      subst hahd,
      split_ifs at hm,
      { subst hm },
      { subst hm, contradiction } },
    { have := index_of_argmax h hatl, clear index_of_argmax,
      split_ifs at *;
      refl <|> exact nat.zero_le _ <|> simp [*, nat.succ_le_succ_iff, -not_le] at * } }
end

theorem index_of_argmin [decidable_eq α] {f : α → β} : Π {l : list α} {m : α}, m ∈ argmin f l →
  ∀ {a}, a ∈ l → f a ≤ f m → l.index_of m ≤ l.index_of a :=
@index_of_argmax _ (order_dual β) _ _ _

theorem mem_argmax_iff [decidable_eq α] {f : α → β} {m : α} {l : list α} :
  m ∈ argmax f l ↔ m ∈ l ∧ (∀ a ∈ l, f a ≤ f m) ∧
    (∀ a ∈ l, f m ≤ f a → l.index_of m ≤ l.index_of a) :=
⟨λ hm, ⟨argmax_mem hm, λ a ha, le_argmax_of_mem ha hm, λ _, index_of_argmax hm⟩,
  begin
    rintros ⟨hml, ham, hma⟩,
    cases harg : argmax f l with n,
    { simp * at * },
    { have := le_antisymm (hma n (argmax_mem harg) (le_argmax_of_mem hml harg))
        (index_of_argmax harg hml (ham _ (argmax_mem harg))),
      rw [(index_of_inj hml (argmax_mem harg)).1 this, option.mem_def] }
  end⟩

theorem argmax_eq_some_iff [decidable_eq α] {f : α → β} {m : α} {l : list α} :
  argmax f l = some m ↔ m ∈ l ∧ (∀ a ∈ l, f a ≤ f m) ∧
    (∀ a ∈ l, f m ≤ f a → l.index_of m ≤ l.index_of a) := mem_argmax_iff

theorem mem_argmin_iff [decidable_eq α] {f : α → β} {m : α} {l : list α} :
  m ∈ argmin f l ↔ m ∈ l ∧ (∀ a ∈ l, f m ≤ f a) ∧
    (∀ a ∈ l, f a ≤ f m → l.index_of m ≤ l.index_of a) :=
@mem_argmax_iff _ (order_dual β) _ _ _ _ _

theorem argmin_eq_some_iff [decidable_eq α] {f : α → β} {m : α} {l : list α} :
  argmin f l = some m ↔ m ∈ l ∧ (∀ a ∈ l, f m ≤ f a) ∧
    (∀ a ∈ l, f a ≤ f m → l.index_of m ≤ l.index_of a) := mem_argmin_iff

variable [linear_order α]

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

theorem le_maximum_of_mem {a m : α} {l : list α} : a ∈ l → (maximum l : with_bot α) = m → a ≤ m :=
le_argmax_of_mem

theorem minimum_le_of_mem {a m : α} {l : list α} : a ∈ l → (minimum l : with_top α) = m → m ≤ a :=
argmin_le_of_mem

theorem le_maximum_of_mem' {a : α} {l : list α} (ha : a ∈ l) : (a : with_bot α) ≤ maximum l :=
option.cases_on (maximum l) (λ _ h, absurd ha ((h rfl).symm ▸ not_mem_nil _))
  (λ m hm _, with_bot.coe_le_coe.2 $ hm _ rfl)
  (λ m, @le_maximum_of_mem _ _ _ m _ ha)
  (@maximum_eq_none _ _ l).1

theorem le_minimum_of_mem' {a : α} {l : list α} (ha : a ∈ l) : minimum l ≤ (a : with_top α) :=
@le_maximum_of_mem' (order_dual α) _ _ _ ha

theorem maximum_concat (a : α) (l : list α) : maximum (l ++ [a]) = max (maximum l) a :=
begin
  rw max_comm,
  simp only [maximum, argmax_concat, id],
  cases h : argmax id l,
  { rw [max_eq_left], refl, exact bot_le },
  change (coe : α → with_bot α) with some,
  rw [max_comm],
  simp [max_def]
end

theorem minimum_concat (a : α) (l : list α) : minimum (l ++ [a]) = min (minimum l) a :=
@maximum_concat (order_dual α) _ _ _

theorem maximum_cons (a : α) (l : list α) : maximum (a :: l) = max a (maximum l) :=
list.reverse_rec_on l (by simp [@max_eq_left (with_bot α) _ _ _ bot_le])
  (λ tl hd ih, by rw [← cons_append, maximum_concat, ih, maximum_concat, max_assoc])

theorem minimum_cons (a : α) (l : list α) : minimum (a :: l) = min a (minimum l) :=
@maximum_cons (order_dual α) _ _ _

theorem maximum_eq_coe_iff {m : α} {l : list α} :
  maximum l = m ↔ m ∈ l ∧ (∀ a ∈ l, a ≤ m) :=
begin
  unfold_coes,
  simp only [maximum, argmax_eq_some_iff, id],
  split,
  { simp only [true_and, forall_true_iff] {contextual := tt} },
  { simp only [true_and, forall_true_iff] {contextual := tt},
    intros h a hal hma,
    rw [le_antisymm hma (h.2 a hal)] }
end

theorem minimum_eq_coe_iff {m : α} {l : list α} :
  minimum l = m ↔ m ∈ l ∧ (∀ a ∈ l, m ≤ a) :=
@maximum_eq_coe_iff (order_dual α) _ _ _

section fold

variables {M : Type*} [canonically_linear_ordered_add_monoid M]

/-! Note: since there is no typeclass for both `linear_order` and `has_top`, nor a typeclass dual
to `canonically_linear_ordered_add_monoid α` we cannot express these lemmas generally for
`minimum`; instead we are limited to doing so on `order_dual α`. -/

lemma maximum_eq_coe_foldr_max_of_ne_nil (l : list M) (h : l ≠ []) :
  l.maximum = (l.foldr max ⊥ : M) :=
begin
  induction l with hd tl IH,
  { contradiction },
  { rw [maximum_cons, foldr, with_bot.coe_max],
    by_cases h : tl = [],
    { simp [h, -with_top.coe_zero] },
    { simp [IH h] } }
end

lemma minimum_eq_coe_foldr_min_of_ne_nil (l : list (order_dual M)) (h : l ≠ []) :
  l.minimum = (l.foldr min ⊤ : order_dual M) :=
maximum_eq_coe_foldr_max_of_ne_nil l h

lemma maximum_nat_eq_coe_foldr_max_of_ne_nil (l : list ℕ) (h : l ≠ []) :
  l.maximum = (l.foldr max 0 : ℕ) :=
maximum_eq_coe_foldr_max_of_ne_nil l h

lemma max_le_of_forall_le (l : list M) (n : M) (h : ∀ (x ∈ l), x ≤ n) :
  l.foldr max ⊥ ≤ n :=
begin
  induction l with y l IH,
  { simp },
  { specialize IH (λ x hx, h x (mem_cons_of_mem _ hx)),
    have hy : y ≤ n := h y (mem_cons_self _ _),
    simpa [hy] using IH }
end

lemma le_min_of_le_forall (l : list (order_dual M)) (n : (order_dual M))
  (h : ∀ (x ∈ l), n ≤ x) :
  n ≤ l.foldr min ⊤ :=
max_le_of_forall_le l n h

lemma max_nat_le_of_forall_le (l : list ℕ) (n : ℕ) (h : ∀ (x ∈ l), x ≤ n) :
  l.foldr max 0 ≤ n :=
max_le_of_forall_le l n h

end fold

end list
