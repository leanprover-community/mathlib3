/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro

List permutations.
-/
import data.list.basic

namespace list
universe variables uu vv
variables {α : Type uu} {β : Type vv}

/-- `perm l₁ l₂` or `l₁ ~ l₂` asserts that `l₁` and `l₂` are permutations
  of each other. This is defined by induction using pairwise swaps. -/
inductive perm : list α → list α → Prop
| nil   : perm [] []
| skip  : Π (x : α) {l₁ l₂ : list α}, perm l₁ l₂ → perm (x::l₁) (x::l₂)
| swap  : Π (x y : α) (l : list α), perm (y::x::l) (x::y::l)
| trans : Π {l₁ l₂ l₃ : list α}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃
open perm

infix ~ := perm

@[refl] protected theorem perm.refl : ∀ (l : list α), l ~ l
| []      := perm.nil
| (x::xs) := skip x (perm.refl xs)

@[symm] protected theorem perm.symm {l₁ l₂ : list α} (p : l₁ ~ l₂) : l₂ ~ l₁ :=
perm.rec_on p
  perm.nil
  (λ x l₁ l₂ p₁ r₁, skip x r₁)
  (λ x y l, swap y x l)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₂ r₁)

attribute [trans] perm.trans

theorem perm.eqv (α : Type) : equivalence (@perm α) :=
mk_equivalence (@perm α) (@perm.refl α) (@perm.symm α) (@perm.trans α)

instance is_setoid (α : Type) : setoid (list α) :=
setoid.mk (@perm α) (perm.eqv α)

theorem perm_subset {l₁ l₂ : list α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ :=
λ a, perm.rec_on p
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

theorem mem_of_perm {a : α} {l₁ l₂ : list α} (h : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ :=
iff.intro (λ m, perm_subset h m) (λ m, perm_subset h.symm m)

theorem perm_app_left {l₁ l₂ : list α} (t₁ : list α) (p : l₁ ~ l₂) : l₁++t₁ ~ l₂++t₁ :=
perm.rec_on p
  (perm.refl ([] ++ t₁))
  (λ x l₁ l₂ p₁ r₁, skip x r₁)
  (λ x y l, swap x y _)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₁ r₂)

theorem perm_app_right {t₁ t₂ : list α} : ∀ (l : list α), t₁ ~ t₂ → l++t₁ ~ l++t₂
| []      p := p
| (x::xs) p := skip x (perm_app_right xs p)

theorem perm_app {l₁ l₂ t₁ t₂ : list α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁++t₁ ~ l₂++t₂ :=
trans (perm_app_left t₁ p₁) (perm_app_right l₂ p₂)

theorem perm_app_cons (a : α) {h₁ h₂ t₁ t₂ : list α}
  (p₁ : h₁ ~ h₂) (p₂ : t₁ ~ t₂) : h₁ ++ a::t₁ ~ h₂ ++ a::t₂ :=
perm_app p₁ (skip a p₂)

@[simp] theorem perm_middle {a : α} : ∀ {l₁ l₂ : list α}, l₁++a::l₂ ~ a::(l₁++l₂)
| []      l₂ := perm.refl _
| (b::l₁) l₂ := (skip b (@perm_middle l₁ l₂)).trans (swap a b _)

@[simp] theorem perm_cons_app (a : α) (l : list α) : l ++ [a] ~ a::l :=
by simpa using @perm_middle _ a l []

@[simp] theorem perm_app_comm : ∀ {l₁ l₂ : list α}, (l₁++l₂) ~ (l₂++l₁)
| []     l₂ := by simp
| (a::t) l₂ := (skip a perm_app_comm).trans perm_middle.symm

theorem concat_perm (l : list α) (a : α) : concat l a ~ a :: l :=
by simp

theorem perm_length {l₁ l₂ : list α} (p : l₁ ~ l₂) : length l₁ = length l₂ :=
perm.rec_on p
  rfl
  (λ x l₁ l₂ p r, by simp[r])
  (λ x y l, by simp)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, eq.trans r₁ r₂)

theorem eq_nil_of_perm_nil {l₁ : list α} (p : [] ~ l₁) : l₁ = [] :=
eq_nil_of_length_eq_zero (perm_length p).symm

theorem perm_nil {l₁ : list α} : l₁ ~ [] ↔ l₁ = [] :=
⟨λ p, eq_nil_of_perm_nil p.symm, λ e, e ▸ perm.refl _⟩

theorem not_perm_nil_cons (x : α) (l : list α) : ¬ [] ~ x::l
| p := by injection eq_nil_of_perm_nil p

theorem eq_singleton_of_perm {a b : α} (p : [a] ~ [b]) : a = b :=
by simpa using perm_subset p (by simp)

theorem eq_singleton_of_perm_inv {a : α} {l : list α} (p : [a] ~ l) : l = [a] :=
match l, show 1 = _, from perm_length p, p with
| [a'], rfl, p := by rw [eq_singleton_of_perm p]
end

@[simp] theorem reverse_perm : ∀ (l : list α), reverse l ~ l
| []     := perm.nil
| (a::l) := by rw reverse_cons; exact
  (perm_cons_app _ _).trans (skip a $ reverse_perm l)

theorem perm_cons_app_cons {l l₁ l₂ : list α} (a : α) (p : l ~ l₁++l₂) : a::l ~ l₁++(a::l₂) :=
trans (skip a p) perm_middle.symm

@[simp] theorem perm_repeat {a : α} {n : ℕ} {l : list α} : repeat a n ~ l ↔ repeat a n = l :=
⟨λ p, (eq_repeat.2 $ by exact
  ⟨by simpa using (perm_length p).symm,
   λ b m, eq_of_mem_repeat $ perm_subset p.symm m⟩).symm,
 λ h, h ▸ perm.refl _⟩

theorem perm_erase [decidable_eq α] {a : α} {l : list α} (h : a ∈ l) : l ~ a :: l.erase a :=
let ⟨l₁, l₂, _, e₁, e₂⟩ := exists_erase_eq h in
e₂.symm ▸ e₁.symm ▸ perm_middle

@[elab_as_eliminator] theorem perm_induction_on
    {P : list α → list α → Prop} {l₁ l₂ : list α} (p : l₁ ~ l₂)
    (h₁ : P [] [])
    (h₂ : ∀ x l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (x::l₁) (x::l₂))
    (h₃ : ∀ x y l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (y::x::l₁) (x::y::l₂))
    (h₄ : ∀ l₁ l₂ l₃, l₁ ~ l₂ → l₂ ~ l₃ → P l₁ l₂ → P l₂ l₃ → P l₁ l₃) :
  P l₁ l₂ :=
have P_refl : ∀ l, P l l, from
  assume l,
  list.rec_on l h₁ (λ x xs ih, h₂ x xs xs (perm.refl xs) ih),
perm.rec_on p h₁ h₂ (λ x y l, h₃ x y l l (perm.refl l) (P_refl l)) h₄

@[congr] theorem perm_filter_map (f : α → option β) {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  filter_map f l₁ ~ filter_map f l₂ :=
begin
  induction p with x l₂ l₂' p IH  x y l₂  l₂ m₂ r₂ p₁ p₂ IH₁ IH₂,
  { simp },
  { simp [filter_map], cases f x with a; simp [filter_map, IH, skip] },
  { simp [filter_map], cases f x with a; cases f y with b; simp [filter_map, swap] },
  { exact IH₁.trans IH₂ }
end

@[congr] theorem perm_map (f : α → β) {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  map f l₁ ~ map f l₂ :=
by rw ← filter_map_eq_map; apply perm_filter_map _ p

theorem perm_pmap {p : α → Prop} (f : Π a, p a → β)
  {l₁ l₂ : list α} (p : l₁ ~ l₂) {H₁ H₂} : pmap f l₁ H₁ ~ pmap f l₂ H₂ :=
begin
  induction p with x l₂ l₂' p IH  x y l₂  l₂ m₂ r₂ p₁ p₂ IH₁ IH₂,
  { simp },
  { simp [IH, skip] },
  { simp [swap] },
  { refine IH₁.trans IH₂,
    exact λ a m, H₂ a (perm_subset p₂ m) }
end

theorem perm_filter (p : α → Prop) [decidable_pred p]
  {l₁ l₂ : list α} (s : l₁ ~ l₂) : filter p l₁ ~ filter p l₂ :=
by rw ← filter_map_eq_filter; apply perm_filter_map _ s

theorem exists_perm_sublist {l₁ l₂ l₂' : list α}
  (s : l₁ <+ l₂) (p : l₂ ~ l₂') : ∃ l₁' ~ l₁, l₁' <+ l₂' :=
begin
  induction p with x l₂ l₂' p IH  x y l₂  l₂ m₂ r₂ p₁ p₂ IH₁ IH₂ generalizing l₁ s,
  { exact ⟨[], eq_nil_of_sublist_nil s ▸ perm.refl _, nil_sublist _⟩ },
  { cases s with _ _ _ s l₁ _ _ s,
    { exact let ⟨l₁', p', s'⟩ := IH s in ⟨l₁', p', s'.cons _ _ _⟩ },
    { exact let ⟨l₁', p', s'⟩ := IH s in ⟨x::l₁', skip x p', s'.cons2 _ _ _⟩ } },
  { cases s with _ _ _ s l₁ _ _ s; cases s with _ _ _ s l₁ _ _ s,
    { exact ⟨l₁, perm.refl _, (s.cons _ _ _).cons _ _ _⟩ },
    { exact ⟨x::l₁, perm.refl _, (s.cons _ _ _).cons2 _ _ _⟩ },
    { exact ⟨y::l₁, perm.refl _, (s.cons2 _ _ _).cons _ _ _⟩ },
    { exact ⟨x::y::l₁, perm.swap _ _ _, (s.cons2 _ _ _).cons2 _ _ _⟩ } },
  { exact let ⟨m₁, pm, sm⟩ := IH₁ s, ⟨r₁, pr, sr⟩ := IH₂ sm in
          ⟨r₁, pr.trans pm, sr⟩ }
end

section rel
open relator
variables {γ : Type*} {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

local infixr ` ∘r ` : 80 := relation.comp

lemma perm_comp_perm : (perm ∘r perm : list α → list α → Prop) = perm :=
begin
  funext a c, apply propext,
  split,
  { exact assume ⟨b, hab, hba⟩, perm.trans hab hba },
  { exact assume h, ⟨a, perm.refl a, h⟩ }
end

lemma perm_comp_forall₂ {l u v} (hlu : perm l u) (huv : forall₂ r u v) : (forall₂ r ∘r perm) l v :=
begin
  induction hlu generalizing v,
  case perm.nil { cases huv, exact ⟨[], forall₂.nil, perm.nil⟩ },
  case perm.skip : a l u hlu ih {
    cases huv with _ b _ v hab huv',
    rcases ih huv' with ⟨l₂, h₁₂, h₂₃⟩,
    exact ⟨b::l₂, forall₂.cons hab h₁₂, perm.skip _ h₂₃⟩
  },
  case perm.swap : a₁ a₂ l₁ l₂ h₂₃ {
    cases h₂₃ with _ b₁ _ l₂ h₁ hr_₂₃,
    cases hr_₂₃ with _ b₂ _ l₂ h₂ h₁₂,
    exact ⟨b₂::b₁::l₂, forall₂.cons h₂ (forall₂.cons h₁ h₁₂), perm.swap _ _ _⟩
  },
  case perm.trans : la₁ la₂ la₃ _ _ ih₁ ih₂ {
    rcases ih₂ huv with ⟨lb₂, hab₂, h₂₃⟩,
    rcases ih₁ hab₂ with ⟨lb₁, hab₁, h₁₂⟩,
    exact ⟨lb₁, hab₁, perm.trans h₁₂ h₂₃⟩
  }
end

lemma forall₂_comp_perm_eq_perm_comp_forall₂ : forall₂ r ∘r perm = perm ∘r forall₂ r :=
begin
  funext l₁ l₃, apply propext,
  split,
  { assume h, rcases h with ⟨l₂, h₁₂, h₂₃⟩,
    have : forall₂ (flip r) l₂ l₁, from h₁₂.flip ,
    rcases perm_comp_forall₂ h₂₃.symm this with ⟨l', h₁, h₂⟩,
    exact ⟨l', h₂.symm, h₁.flip⟩ },
  { exact assume ⟨l₂, h₁₂, h₂₃⟩, perm_comp_forall₂ h₁₂ h₂₃ }
end

lemma rel_perm_imp (hr : right_unique r) : (forall₂ r ⇒ forall₂ r ⇒ implies) perm perm :=
assume a b h₁ c d h₂ h,
have (flip (forall₂ r) ∘r (perm ∘r forall₂ r)) b d, from ⟨a, h₁, c, h, h₂⟩,
have ((flip (forall₂ r) ∘r forall₂ r) ∘r perm) b d,
  by rwa [← forall₂_comp_perm_eq_perm_comp_forall₂, ← relation.comp_assoc] at this,
let ⟨b', ⟨c', hbc, hcb⟩, hbd⟩ := this in
have b' = b, from right_unique_forall₂ @hr hcb hbc,
this ▸ hbd

lemma rel_perm (hr : bi_unique r) : (forall₂ r ⇒ forall₂ r ⇒ (↔)) perm perm :=
assume a b hab c d hcd, iff.intro
  (rel_perm_imp hr.2 hab hcd)
  (rel_perm_imp (assume a b c, left_unique_flip hr.1) hab.flip hcd.flip)

end rel

section subperm

/-- `subperm l₁ l₂`, denoted `l₁ <+~ l₂`, means that `l₁` is a sublist of
  a permutation of `l₂`. This is an analogue of `l₁ ⊆ l₂` which respects
  multiplicities of elements, and is used for the `≤` relation on multisets. -/
def subperm (l₁ l₂ : list α) : Prop := ∃ l ~ l₁, l <+ l₂

infix ` <+~ `:50 := subperm

theorem perm.subperm_left {l l₁ l₂ : list α} (p : l₁ ~ l₂) : l <+~ l₁ ↔ l <+~ l₂ :=
suffices ∀ {l₁ l₂ : list α}, l₁ ~ l₂ → l <+~ l₁ → l <+~ l₂,
from ⟨this p, this p.symm⟩,
λ l₁ l₂ p ⟨u, pu, su⟩,
  let ⟨v, pv, sv⟩ := exists_perm_sublist su p in
  ⟨v, pv.trans pu, sv⟩

theorem perm.subperm_right {l₁ l₂ l : list α} (p : l₁ ~ l₂) : l₁ <+~ l ↔ l₂ <+~ l :=
⟨λ ⟨u, pu, su⟩, ⟨u, pu.trans p, su⟩,
 λ ⟨u, pu, su⟩, ⟨u, pu.trans p.symm, su⟩⟩

theorem subperm_of_sublist {l₁ l₂ : list α} (s : l₁ <+ l₂) : l₁ <+~ l₂ :=
⟨l₁, perm.refl _, s⟩

theorem subperm_of_perm {l₁ l₂ : list α} (p : l₁ ~ l₂) : l₁ <+~ l₂ :=
⟨l₂, p.symm, sublist.refl _⟩

theorem subperm.refl (l : list α) : l <+~ l := subperm_of_perm (perm.refl _)

theorem subperm.trans {l₁ l₂ l₃ : list α} : l₁ <+~ l₂ → l₂ <+~ l₃ → l₁ <+~ l₃
| s ⟨l₂', p₂, s₂⟩ :=
  let ⟨l₁', p₁, s₁⟩ := p₂.subperm_left.2 s in ⟨l₁', p₁, s₁.trans s₂⟩

theorem length_le_of_subperm {l₁ l₂ : list α} : l₁ <+~ l₂ → length l₁ ≤ length l₂
| ⟨l, p, s⟩ := perm_length p ▸ length_le_of_sublist s

theorem subperm.perm_of_length_le {l₁ l₂ : list α} : l₁ <+~ l₂ → length l₂ ≤ length l₁ → l₁ ~ l₂
| ⟨l, p, s⟩ h :=
  suffices l = l₂, from this ▸ p.symm,
  eq_of_sublist_of_length_le s $ perm_length p.symm ▸ h

theorem subperm.antisymm {l₁ l₂ : list α} (h₁ : l₁ <+~ l₂) (h₂ : l₂ <+~ l₁) : l₁ ~ l₂ :=
h₁.perm_of_length_le (length_le_of_subperm h₂)

theorem subset_of_subperm {l₁ l₂ : list α} : l₁ <+~ l₂ → l₁ ⊆ l₂
| ⟨l, p, s⟩ := subset.trans (perm_subset p.symm) (subset_of_sublist s)

end subperm

theorem exists_perm_append_of_sublist : ∀ {l₁ l₂ : list α}, l₁ <+ l₂ → ∃ l, l₂ ~ l₁ ++ l
| ._ ._ sublist.slnil            := ⟨nil, perm.refl _⟩
| ._ ._ (sublist.cons l₁ l₂ a s) :=
  let ⟨l, p⟩ := exists_perm_append_of_sublist s in
  ⟨a::l, (skip a p).trans perm_middle.symm⟩
| ._ ._ (sublist.cons2 l₁ l₂ a s) :=
  let ⟨l, p⟩ := exists_perm_append_of_sublist s in
  ⟨l, skip a p⟩

theorem perm_countp (p : α → Prop) [decidable_pred p]
  {l₁ l₂ : list α} (s : l₁ ~ l₂) : countp p l₁ = countp p l₂ :=
by rw [countp_eq_length_filter, countp_eq_length_filter];
   exact perm_length (perm_filter _ s)

theorem countp_le_of_subperm (p : α → Prop) [decidable_pred p]
  {l₁ l₂ : list α} : l₁ <+~ l₂ → countp p l₁ ≤ countp p l₂
| ⟨l, p', s⟩ := perm_countp p p' ▸ countp_le_of_sublist s

theorem perm_count [decidable_eq α] {l₁ l₂ : list α}
  (p : l₁ ~ l₂) (a) : count a l₁ = count a l₂ :=
perm_countp _ p

theorem count_le_of_subperm [decidable_eq α] {l₁ l₂ : list α}
  (s : l₁ <+~ l₂) (a) : count a l₁ ≤ count a l₂ :=
countp_le_of_subperm _ s

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

lemma rec_heq_of_perm {β : list α → Sort*} {f : Πa l, β l → β (a::l)} {b : β []} {l l' : list α}
  (hl : perm l l')
  (f_congr : ∀{a l l' b b'}, perm l l' → b == b' → f a l b == f a l' b')
  (f_swap : ∀{a a' l b}, f a (a'::l) (f a' l b) == f a' (a::l) (f a l b)) :
  @list.rec α β b f l == @list.rec α β b f l' :=
begin
  induction hl,
  case list.perm.nil { refl },
  case list.perm.skip : a l l' h ih { exact f_congr h ih },
  case list.perm.swap : a a' l { exact f_swap },
  case list.perm.trans : l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ { exact heq.trans ih₁ ih₂ }
end

section
variables {op : α → α → α} [is_associative α op] [is_commutative α op]
local notation a * b := op a b
local notation l <*> a := foldl op a l

lemma fold_op_eq_of_perm {l₁ l₂ : list α} {a : α} (h : l₁ ~ l₂) : l₁ <*> a = l₂ <*> a :=
foldl_eq_of_perm (right_comm _ (is_commutative.comm _) (is_associative.assoc _)) h _
end

section comm_monoid
open list
variable [comm_monoid α]

@[to_additive list.sum_eq_of_perm]
lemma prod_eq_of_perm {l₁ l₂ : list α} (h : perm l₁ l₂) : prod l₁ = prod l₂ :=
by induction h; simp [*, mul_left_comm]

@[to_additive list.sum_reverse]
lemma prod_reverse (l : list α) : prod l.reverse = prod l :=
prod_eq_of_perm $ reverse_perm l

end comm_monoid

theorem perm_inv_core {a : α} {l₁ l₂ r₁ r₂ : list α} : l₁++a::r₁ ~ l₂++a::r₂ → l₁++r₁ ~ l₂++r₂ :=
begin
  generalize e₁ : l₁++a::r₁ = s₁, generalize e₂ : l₂++a::r₂ = s₂,
  intro p, revert l₁ l₂ r₁ r₂ e₁ e₂,
  refine perm_induction_on p _ (λ x t₁ t₂ p IH, _) (λ x y t₁ t₂ p IH, _) (λ t₁ t₂ t₃ p₁ p₂ IH₁ IH₂, _);
    intros l₁ l₂ r₁ r₂ e₁ e₂,
  { apply (not_mem_nil a).elim, rw ← e₁, simp },
  { cases l₁ with y l₁; cases l₂ with z l₂;
      dsimp at e₁ e₂; injections; subst x,
    { substs t₁ t₂,     exact p },
    { substs z t₁ t₂,   exact p.trans perm_middle },
    { substs y t₁ t₂,   exact perm_middle.symm.trans p },
    { substs z t₁ t₂,   exact skip y (IH rfl rfl) } },
  { rcases l₁ with _|⟨y, _|⟨z, l₁⟩⟩; rcases l₂ with _|⟨u, _|⟨v, l₂⟩⟩;
      dsimp at e₁ e₂; injections; substs x y,
    { substs r₁ r₂,     exact skip a p },
    { substs r₁ r₂,     exact skip u p },
    { substs r₁ v t₂,   exact skip u (p.trans perm_middle) },
    { substs r₁ r₂,     exact skip y p },
    { substs r₁ r₂ y u, exact skip a p },
    { substs r₁ u v t₂, exact (skip y $ p.trans perm_middle).trans (swap _ _ _) },
    { substs r₂ z t₁,   exact skip y (perm_middle.symm.trans p) },
    { substs r₂ y z t₁, exact (swap _ _ _).trans (skip u $ perm_middle.symm.trans p) },
    { substs u v t₁ t₂, exact (swap _ _ _).trans (skip z $ skip y $ IH rfl rfl) } },
  { substs t₁ t₃,
    have : a ∈ t₂ := perm_subset p₁ (by simp),
    rcases mem_split this with ⟨l₂, r₂, e₂⟩,
    subst t₂, exact (IH₁ rfl rfl).trans (IH₂ rfl rfl) }
end

theorem perm_cons_inv {a : α} {l₁ l₂ : list α} : a::l₁ ~ a::l₂ → l₁ ~ l₂ :=
@perm_inv_core _ _ [] [] _ _

theorem perm_cons (a : α) {l₁ l₂ : list α} : a::l₁ ~ a::l₂ ↔ l₁ ~ l₂ :=
⟨perm_cons_inv, skip a⟩

theorem perm_app_left_iff {l₁ l₂ : list α} : ∀ l, l++l₁ ~ l++l₂ ↔ l₁ ~ l₂
| []     := iff.rfl
| (a::l) := (perm_cons a).trans (perm_app_left_iff l)

theorem perm_app_right_iff {l₁ l₂ : list α} (l) : l₁++l ~ l₂++l ↔ l₁ ~ l₂ :=
⟨λ p, (perm_app_left_iff _).1 $ trans perm_app_comm $ trans p perm_app_comm,
 perm_app_left _⟩

theorem subperm_cons (a : α) {l₁ l₂ : list α} : a::l₁ <+~ a::l₂ ↔ l₁ <+~ l₂ :=
⟨λ ⟨l, p, s⟩, begin
  cases s with _ _ _ s' u _ _ s',
  { exact (p.subperm_left.2 $ subperm_of_sublist $ sublist_cons _ _).trans
     (subperm_of_sublist s') },
  { exact ⟨u, perm_cons_inv p, s'⟩ }
end, λ ⟨l, p, s⟩, ⟨a::l, skip a p, s.cons2 _ _ _⟩⟩

theorem cons_subperm_of_mem {a : α} {l₁ l₂ : list α} (d₁ : nodup l₁) (h₁ : a ∉ l₁) (h₂ : a ∈ l₂)
 (s : l₁ <+~ l₂) : a :: l₁ <+~ l₂ :=
begin
  rcases s with ⟨l, p, s⟩,
  induction s generalizing l₁,
  case list.sublist.slnil { cases h₂ },
  case list.sublist.cons : r₁ r₂ b s' ih {
    simp at h₂,
    cases h₂ with e m,
    { subst b, exact ⟨a::r₁, skip a p, s'.cons2 _ _ _⟩ },
    { rcases ih m d₁ h₁ p with ⟨t, p', s'⟩, exact ⟨t, p', s'.cons _ _ _⟩ } },
  case list.sublist.cons2 : r₁ r₂ b s' ih {
    have bm : b ∈ l₁ := (perm_subset p $ mem_cons_self _ _),
    have am : a ∈ r₂ := h₂.resolve_left (λ e, h₁ $ e.symm ▸ bm),
    rcases mem_split bm with ⟨t₁, t₂, rfl⟩,
    have st : t₁ ++ t₂ <+ t₁ ++ b :: t₂ := by simp,
    rcases ih am (nodup_of_sublist st d₁)
      (mt (λ x, subset_of_sublist st x) h₁)
      (perm_cons_inv $ p.trans perm_middle) with ⟨t, p', s'⟩,
    exact ⟨b::t, (skip b p').trans $ (swap _ _ _).trans (skip a perm_middle.symm), s'.cons2 _ _ _⟩ }
end

theorem subperm_app_left {l₁ l₂ : list α} : ∀ l, l++l₁ <+~ l++l₂ ↔ l₁ <+~ l₂
| []     := iff.rfl
| (a::l) := (subperm_cons a).trans (subperm_app_left l)

theorem subperm_app_right {l₁ l₂ : list α} (l) : l₁++l <+~ l₂++l ↔ l₁ <+~ l₂ :=
(perm_app_comm.subperm_left.trans perm_app_comm.subperm_right).trans (subperm_app_left l)

theorem subperm.exists_of_length_lt {l₁ l₂ : list α} :
  l₁ <+~ l₂ → length l₁ < length l₂ → ∃ a, a :: l₁ <+~ l₂
| ⟨l, p, s⟩ h :=
  suffices length l < length l₂ → ∃ (a : α), a :: l <+~ l₂, from
  (this $ perm_length p.symm ▸ h).imp (λ a, (skip a p).subperm_right.1),
  begin
    clear subperm.exists_of_length_lt p h l₁, rename l₂ u,
    induction s with l₁ l₂ a s IH _ _ b s IH; intro h,
    { cases h },
    { cases lt_or_eq_of_le (nat.le_of_lt_succ h : length l₁ ≤ length l₂) with h h,
      { exact (IH h).imp (λ a s, s.trans (subperm_of_sublist $ sublist_cons _ _)) },
      { exact ⟨a, eq_of_sublist_of_length_eq s h ▸ subperm.refl _⟩ } },
    { exact (IH $ nat.lt_of_succ_lt_succ h).imp
        (λ a s, (swap _ _ _).subperm_right.1 $ (subperm_cons _).2 s) }
  end

theorem subperm_of_subset_nodup
  {l₁ l₂ : list α} (d : nodup l₁) (H : l₁ ⊆ l₂) : l₁ <+~ l₂ :=
begin
  induction d with a l₁' h d IH,
  { exact ⟨nil, perm.nil, nil_sublist _⟩ },
  { cases forall_mem_cons.1 H with H₁ H₂,
    simp at h,
    exact cons_subperm_of_mem d h H₁ (IH H₂) }
end

theorem perm_ext {l₁ l₂ : list α} (d₁ : nodup l₁) (d₂ : nodup l₂) : l₁ ~ l₂ ↔ ∀a, a ∈ l₁ ↔ a ∈ l₂ :=
⟨λ p a, mem_of_perm p, λ H, subperm.antisymm
  (subperm_of_subset_nodup d₁ (λ a, (H a).1))
  (subperm_of_subset_nodup d₂ (λ a, (H a).2))⟩

theorem perm_ext_sublist_nodup {l₁ l₂ l : list α} (d : nodup l)
  (s₁ : l₁ <+ l) (s₂ : l₂ <+ l) : l₁ ~ l₂ ↔ l₁ = l₂ :=
⟨λ h, begin
  induction s₂ with l₂ l a s₂ IH l₂ l a s₂ IH generalizing l₁,
  { exact eq_nil_of_perm_nil h.symm },
  { simp at d,
    cases s₁ with _ _ _ s₁ l₁ _ _ s₁,
    { exact IH d.2 s₁ h },
    { apply d.1.elim,
      exact subset_of_subperm ⟨_, h.symm, s₂⟩ (mem_cons_self _ _) } },
  { simp at d,
    cases s₁ with _ _ _ s₁ l₁ _ _ s₁,
    { apply d.1.elim,
      exact subset_of_subperm ⟨_, h, s₁⟩ (mem_cons_self _ _) },
    { rw IH d.2 s₁ (perm_cons_inv h) } }
end, λ h, by rw h⟩

section
variable [decidable_eq α]

-- attribute [congr]
theorem erase_perm_erase (a : α) {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  l₁.erase a ~ l₂.erase a :=
if h₁ : a ∈ l₁ then
have h₂ : a ∈ l₂, from perm_subset p h₁,
perm_cons_inv $ trans (perm_erase h₁).symm $ trans p (perm_erase h₂)
else
have h₂ : a ∉ l₂, from mt (mem_of_perm p).2 h₁,
by rw [erase_of_not_mem h₁, erase_of_not_mem h₂]; exact p

theorem erase_subperm (a : α) (l : list α) : l.erase a <+~ l :=
⟨l.erase a, perm.refl _, erase_sublist _ _⟩

theorem erase_subperm_erase {l₁ l₂ : list α} (a : α) (h : l₁ <+~ l₂) : l₁.erase a <+~ l₂.erase a :=
let ⟨l, hp, hs⟩ := h in ⟨l.erase a, erase_perm_erase _ hp, erase_sublist_erase _ hs⟩

theorem perm_diff_left {l₁ l₂ : list α} (t : list α) (h : l₁ ~ l₂) : l₁.diff t ~ l₂.diff t :=
by induction t generalizing l₁ l₂ h; simp [*, erase_perm_erase]

theorem perm_diff_right (l : list α) {t₁ t₂ : list α} (h : t₁ ~ t₂) : l.diff t₁ = l.diff t₂ :=
by induction h generalizing l; simp [*, erase_perm_erase, erase_comm]
  <|> exact (ih_1 _).trans (ih_2 _)

theorem subperm_cons_diff {a : α} : ∀ {l₁ l₂ : list α}, (a :: l₁).diff l₂ <+~ a :: l₁.diff l₂
| l₁ []      := ⟨a::l₁, by simp⟩
| l₁ (b::l₂) :=
begin
  repeat {rw diff_cons},
  by_cases heq : a = b,
  { by_cases b ∈ l₁,
    { rw perm.subperm_right, apply subperm_cons_diff,
      simp [perm_diff_left, heq, perm_erase h] },
    { simp [subperm_of_sublist, sublist.cons, h, heq] } },
  { simp [heq, subperm_cons_diff] }
end

theorem subset_cons_diff {a : α} {l₁ l₂ : list α} : (a :: l₁).diff l₂ ⊆ a :: l₁.diff l₂ :=
subset_of_subperm subperm_cons_diff

theorem perm_bag_inter_left {l₁ l₂ : list α} (t : list α) (h : l₁ ~ l₂) : l₁.bag_inter t ~ l₂.bag_inter t :=
begin
  induction h with x _ _ _ _ x y _ _ _ _ _ _ ih_1 ih_2 generalizing t, {simp},
  { by_cases x ∈ t; simp [*, skip] },
  { by_cases x = y, {simp [h]},
    by_cases xt : x ∈ t; by_cases yt : y ∈ t,
    { simp [xt, yt, mem_erase_of_ne h, mem_erase_of_ne (ne.symm h), erase_comm, swap] },
    { simp [xt, yt, mt mem_of_mem_erase, skip] },
    { simp [xt, yt, mt mem_of_mem_erase, skip] },
    { simp [xt, yt] } },
  { exact (ih_1 _).trans (ih_2 _) }
end

theorem perm_bag_inter_right (l : list α) {t₁ t₂ : list α} (p : t₁ ~ t₂) : l.bag_inter t₁ = l.bag_inter t₂ :=
begin
  induction l with a l IH generalizing t₁ t₂ p, {simp},
  by_cases a ∈ t₁,
  { simp [h, (mem_of_perm p).1 h, IH (erase_perm_erase _ p)] },
  { simp [h, mt (mem_of_perm p).2 h, IH p] }
end

theorem cons_perm_iff_perm_erase {a : α} {l₁ l₂ : list α} : a::l₁ ~ l₂ ↔ a ∈ l₂ ∧ l₁ ~ l₂.erase a :=
⟨λ h, have a ∈ l₂, from perm_subset h (mem_cons_self a l₁),
      ⟨this, perm_cons_inv $ h.trans $ perm_erase this⟩,
 λ ⟨m, h⟩, trans (skip a h) (perm_erase m).symm⟩

theorem perm_iff_count {l₁ l₂ : list α} : l₁ ~ l₂ ↔ ∀ a, count a l₁ = count a l₂ :=
⟨perm_count, λ H, begin
  induction l₁ with a l₁ IH generalizing l₂,
  { cases l₂ with b l₂, {refl},
    specialize H b, simp at H, contradiction },
  { have : a ∈ l₂ := count_pos.1 (by rw ← H; simp; apply nat.succ_pos),
    refine trans (skip a $ IH $ λ b, _) (perm_erase this).symm,
    specialize H b,
    rw perm_count (perm_erase this) at H,
    by_cases b = a; simp [h] at H ⊢; assumption }
end⟩

instance decidable_perm : ∀ (l₁ l₂ : list α), decidable (l₁ ~ l₂)
| []      []      := is_true $ perm.refl _
| []      (b::l₂) := is_false $ λ h, by have := eq_nil_of_perm_nil h; contradiction
| (a::l₁) l₂      := by haveI := decidable_perm l₁ (l₂.erase a);
                        exact decidable_of_iff' _ cons_perm_iff_perm_erase

-- @[congr]
theorem perm_erase_dup_of_perm {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  erase_dup l₁ ~ erase_dup l₂ :=
perm_iff_count.2 $ λ a,
if h : a ∈ l₁
then by simp [nodup_erase_dup, h, perm_subset p h]
else by simp [h, mt (mem_of_perm p).2 h]

-- attribute [congr]
theorem perm_insert (a : α)
  {l₁ l₂ : list α} (p : l₁ ~ l₂) : insert a l₁ ~ insert a l₂ :=
if h : a ∈ l₁
then by simpa [h, perm_subset p h] using p
else by simpa [h, mt (mem_of_perm p).2 h] using skip a p

theorem perm_insert_swap (x y : α) (l : list α) :
  insert x (insert y l) ~ insert y (insert x l) :=
begin
  by_cases xl : x ∈ l; by_cases yl : y ∈ l; simp [xl, yl],
  by_cases xy : x = y, { simp [xy] },
  simp [not_mem_cons_of_ne_of_not_mem xy xl,
        not_mem_cons_of_ne_of_not_mem (ne.symm xy) yl],
  constructor
end

theorem perm_union_left {l₁ l₂ : list α} (t₁ : list α) (h : l₁ ~ l₂) : l₁ ∪ t₁ ~ l₂ ∪ t₁ :=
begin
  induction h with a _ _ _ ih _ _ _ _ _ _ _ _ ih_1 ih_2; try {simp},
  { exact perm_insert a ih },
  { apply perm_insert_swap },
  { exact ih_1.trans ih_2 }
end

theorem perm_union_right (l : list α) {t₁ t₂ : list α} (h : t₁ ~ t₂) : l ∪ t₁ ~ l ∪ t₂ :=
by induction l; simp [*, perm_insert]

-- @[congr]
theorem perm_union {l₁ l₂ t₁ t₂ : list α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ∪ t₁ ~ l₂ ∪ t₂ :=
trans (perm_union_left t₁ p₁) (perm_union_right l₂ p₂)

theorem perm_inter_left {l₁ l₂ : list α} (t₁ : list α) : l₁ ~ l₂ → l₁ ∩ t₁ ~ l₂ ∩ t₁ :=
perm_filter _

theorem perm_inter_right (l : list α) {t₁ t₂ : list α} (p : t₁ ~ t₂) : l ∩ t₁ = l ∩ t₂ :=
by dsimp [(∩), list.inter]; congr; funext a; rw [mem_of_perm p]

-- @[congr]
theorem perm_inter {l₁ l₂ t₁ t₂ : list α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ∩ t₁ ~ l₂ ∩ t₂ :=
perm_inter_right l₂ p₂ ▸ perm_inter_left t₁ p₁
end

theorem perm_pairwise {R : α → α → Prop} (S : symmetric R) :
  ∀ {l₁ l₂ : list α} (p : l₁ ~ l₂), pairwise R l₁ ↔ pairwise R l₂ :=
suffices ∀ {l₁ l₂}, l₁ ~ l₂ → pairwise R l₁ → pairwise R l₂, from λ l₁ l₂ p, ⟨this p, this p.symm⟩,
λ l₁ l₂ p d, begin
  induction d with a l₁ h d IH generalizing l₂,
  { rw eq_nil_of_perm_nil p, constructor },
  { have : a ∈ l₂ := perm_subset p (mem_cons_self _ _),
    rcases mem_split this with ⟨s₂, t₂, rfl⟩,
    have p' := perm_cons_inv (p.trans perm_middle),
    refine (pairwise_middle S).2 (pairwise_cons.2 ⟨λ b m, _, IH _ p'⟩),
    exact h _ (perm_subset p'.symm m) }
end

theorem perm_nodup {l₁ l₂ : list α} : l₁ ~ l₂ → (nodup l₁ ↔ nodup l₂) :=
perm_pairwise $ @ne.symm α

theorem perm_bind_left {l₁ l₂ : list α} (f : α → list β) (p : l₁ ~ l₂) :
  l₁.bind f ~ l₂.bind f :=
begin
  induction p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂, {simp},
  { simp, exact perm_app_right _ IH },
  { simp, rw [← append_assoc, ← append_assoc], exact perm_app_left _ perm_app_comm },
  { exact trans IH₁ IH₂ }
end

theorem perm_bind_right (l : list α) {f g : α → list β} (h : ∀ a, f a ~ g a) :
  l.bind f ~ l.bind g :=
by induction l with a l IH; simp; exact perm_app (h a) IH

theorem perm_product_left {l₁ l₂ : list α} (t₁ : list β) (p : l₁ ~ l₂) : product l₁ t₁ ~ product l₂ t₁ :=
perm_bind_left _ p

theorem perm_product_right (l : list α) {t₁ t₂ : list β} (p : t₁ ~ t₂) : product l t₁ ~ product l t₂ :=
perm_bind_right _ $ λ a, perm_map _ p

@[congr] theorem perm_product {l₁ l₂ : list α} {t₁ t₂ : list β}
  (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : product l₁ t₁ ~ product l₂ t₂ :=
trans (perm_product_left t₁ p₁) (perm_product_right l₂ p₂)

theorem sublists_cons_perm_append (a : α) (l : list α) :
  sublists (a :: l) ~ sublists l ++ map (cons a) (sublists l) :=
begin
  simp [sublists, sublists_aux_cons_cons],
  refine skip _ ((skip _ _).trans perm_middle.symm),
  induction sublists_aux l cons with b l IH; simp,
  exact skip b ((skip _ IH).trans perm_middle.symm)
end

theorem sublists_perm_sublists' : ∀ l : list α, sublists l ~ sublists' l
| []     := perm.refl _
| (a::l) := let IH := sublists_perm_sublists' l in
  by rw sublists'_cons; exact
  (sublists_cons_perm_append _ _).trans (perm_app IH (perm_map _ IH))

theorem revzip_sublists (l : list α) :
  ∀ l₁ l₂, (l₁, l₂) ∈ revzip l.sublists → l₁ ++ l₂ ~ l :=
begin
  rw revzip,
  apply list.reverse_rec_on l,
  { intros l₁ l₂ h, simp at h, simp [h] },
  { intros l a IH l₁ l₂ h,
    rw [sublists_concat, reverse_append, zip_append, ← map_reverse,
        zip_map_right, zip_map_left] at h; [simp at h, simp],
    rcases h with ⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', l₂, h, rfl, rfl⟩,
    { rw ← append_assoc,
      exact perm_app_left _ (IH _ _ h) },
    { rw append_assoc,
      apply (perm_app_right _ perm_app_comm).trans,
      rw ← append_assoc,
      exact perm_app_left _ (IH _ _ h) } }
end

theorem revzip_sublists' (l : list α) :
  ∀ l₁ l₂, (l₁, l₂) ∈ revzip l.sublists' → l₁ ++ l₂ ~ l :=
begin
  rw revzip,
  induction l with a l IH; intros l₁ l₂ h,
  { simp at h, simp [h] },
  { rw [sublists'_cons, reverse_append, zip_append, ← map_reverse,
        zip_map_right, zip_map_left] at h; [simp at h, simp],
    rcases h with ⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', l₂, h, rfl, rfl⟩,
    { exact perm_middle.trans (skip _ (IH _ _ h)) },
    { exact skip _ (IH _ _ h) } }
end

/- enumerating permutations -/

section permutations

theorem permutations_aux2_fst (t : α) (ts : list α) (r : list β) : ∀ (ys : list α) (f : list α → β),
  (permutations_aux2 t ts r ys f).1 = ys ++ ts
| []      f := rfl
| (y::ys) f := match _, permutations_aux2_fst ys _ : ∀ o : list α × list β, o.1 = ys ++ ts →
      (permutations_aux2._match_1 t y f o).1 = y :: ys ++ ts with
  | ⟨_, zs⟩, rfl := rfl
  end

@[simp] theorem permutations_aux2_snd_nil (t : α) (ts : list α) (r : list β) (f : list α → β) :
  (permutations_aux2 t ts r [] f).2 = r := rfl

@[simp] theorem permutations_aux2_snd_cons (t : α) (ts : list α) (r : list β) (y : α) (ys : list α) (f : list α → β) :
  (permutations_aux2 t ts r (y::ys) f).2 = f (t :: y :: ys ++ ts) ::
    (permutations_aux2 t ts r ys (λx : list α, f (y::x))).2 :=
match _, permutations_aux2_fst t ts r _ _ : ∀ o : list α × list β, o.1 = ys ++ ts →
   (permutations_aux2._match_1 t y f o).2 = f (t :: y :: ys ++ ts) :: o.2 with
| ⟨_, zs⟩, rfl := rfl
end

theorem permutations_aux2_append (t : α) (ts : list α) (r : list β) (ys : list α) (f : list α → β) :
  (permutations_aux2 t ts nil ys f).2 ++ r = (permutations_aux2 t ts r ys f).2 :=
by induction ys generalizing f; simp *

theorem mem_permutations_aux2 {t : α} {ts : list α} {ys : list α} {l l' : list α} :
    l' ∈ (permutations_aux2 t ts [] ys (append l)).2 ↔
    ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l' = l ++ l₁ ++ t :: l₂ ++ ts :=
begin
  induction ys with y ys ih generalizing l,
  { simp {contextual := tt} },
  { rw [permutations_aux2_snd_cons, show (λ (x : list α), l ++ y :: x) = append (l ++ [y]),
        by funext; simp, mem_cons_iff, ih], split; intro h,
    { rcases h with e | ⟨l₁, l₂, l0, ye, _⟩,
      { subst l', exact ⟨[], y::ys, by simp⟩ },
      { substs l' ys, exact ⟨y::l₁, l₂, l0, by simp⟩ } },
    { rcases h with ⟨_ | ⟨y', l₁⟩, l₂, l0, ye, rfl⟩,
      { simp [ye] },
      { simp at ye, rcases ye with ⟨rfl, rfl⟩,
        exact or.inr ⟨l₁, l₂, l0, by simp⟩ } } }
end

theorem mem_permutations_aux2' {t : α} {ts : list α} {ys : list α} {l : list α} :
    l ∈ (permutations_aux2 t ts [] ys id).2 ↔
    ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l = l₁ ++ t :: l₂ ++ ts :=
by rw [show @id (list α) = append nil, by funext; refl]; apply mem_permutations_aux2

theorem length_permutations_aux2 (t : α) (ts : list α) (ys : list α) (f : list α → β) :
  length (permutations_aux2 t ts [] ys f).2 = length ys :=
by induction ys generalizing f; simp *

theorem foldr_permutations_aux2 (t : α) (ts : list α) (r L : list (list α)) :
  foldr (λy r, (permutations_aux2 t ts r y id).2) r L = L.bind (λ y, (permutations_aux2 t ts [] y id).2) ++ r :=
by induction L with l L ih; [refl, {simp [ih], rw ← permutations_aux2_append}]

theorem mem_foldr_permutations_aux2 {t : α} {ts : list α} {r L : list (list α)} {l' : list α} :
  l' ∈ foldr (λy r, (permutations_aux2 t ts r y id).2) r L ↔ l' ∈ r ∨
  ∃ l₁ l₂, l₁ ++ l₂ ∈ L ∧ l₂ ≠ [] ∧ l' = l₁ ++ t :: l₂ ++ ts :=
have (∃ (a : list α), a ∈ L ∧
    ∃ (l₁ l₂ : list α), ¬l₂ = nil ∧ a = l₁ ++ l₂ ∧ l' = l₁ ++ t :: (l₂ ++ ts)) ↔
    ∃ (l₁ l₂ : list α), ¬l₂ = nil ∧ l₁ ++ l₂ ∈ L ∧ l' = l₁ ++ t :: (l₂ ++ ts),
from ⟨λ ⟨a, aL, l₁, l₂, l0, e, h⟩, ⟨l₁, l₂, l0, e ▸ aL, h⟩,
      λ ⟨l₁, l₂, l0, aL, h⟩, ⟨_, aL, l₁, l₂, l0, rfl, h⟩⟩,
by rw foldr_permutations_aux2; simp [mem_permutations_aux2', this,
  or.comm, or.left_comm, or.assoc, and.comm, and.left_comm, and.assoc]

theorem length_foldr_permutations_aux2 (t : α) (ts : list α) (r L : list (list α)) :
  length (foldr (λy r, (permutations_aux2 t ts r y id).2) r L) = sum (map length L) + length r :=
by simp [foldr_permutations_aux2, (∘), length_permutations_aux2]

theorem length_foldr_permutations_aux2' (t : α) (ts : list α) (r L : list (list α))
  (n) (H : ∀ l ∈ L, length l = n) :
  length (foldr (λy r, (permutations_aux2 t ts r y id).2) r L) = n * length L + length r :=
begin
  rw [length_foldr_permutations_aux2, (_ : sum (map length L) = n * length L)],
  induction L with l L ih, {simp},
  simp [ih (λ l m, H l (mem_cons_of_mem _ m)), H l (mem_cons_self _ _), mul_add]
end

theorem perm_of_mem_permutations_aux :
  ∀ {ts is l : list α}, l ∈ permutations_aux ts is → l ~ ts ++ is :=
begin
  refine permutations_aux.rec (by simp) _,
  introv IH1 IH2 m,
  rw [permutations_aux_cons, permutations, mem_foldr_permutations_aux2] at m,
  rcases m with m | ⟨l₁, l₂, m, _, e⟩,
  { exact (IH1 m).trans perm_middle },
  { subst e,
    have p : l₁ ++ l₂ ~ is,
    { simp [permutations] at m,
      cases m with e m, {simp [e]},
      exact is.append_nil ▸ IH2 m },
    exact (perm_app_left _ (perm_middle.trans (skip _ p))).trans (skip _ perm_app_comm) }
end

theorem perm_of_mem_permutations {l₁ l₂ : list α}
  (h : l₁ ∈ permutations l₂) : l₁ ~ l₂ :=
(eq_or_mem_of_mem_cons h).elim (λ e, e ▸ perm.refl _)
  (λ m, append_nil l₂ ▸ perm_of_mem_permutations_aux m)

theorem length_permutations_aux :
  ∀ ts is : list α, length (permutations_aux ts is) + is.length.fact = (length ts + length is).fact :=
begin
  refine permutations_aux.rec (by simp) _,
  intros t ts is IH1 IH2,
  have IH2 : length (permutations_aux is nil) + 1 = is.length.fact,
  { simpa using IH2 },
  simp [-add_comm, nat.fact, nat.add_succ, mul_comm] at IH1,
  rw [permutations_aux_cons,
      length_foldr_permutations_aux2' _ _ _ _ _
        (λ l m, perm_length (perm_of_mem_permutations m)),
      permutations, length, length, IH2,
      nat.succ_add, nat.fact_succ, mul_comm (nat.succ _), ← IH1,
      add_comm (_*_), add_assoc, nat.mul_succ, mul_comm]
end

theorem length_permutations (l : list α) : length (permutations l) = (length l).fact :=
length_permutations_aux l []

theorem mem_permutations_of_perm_lemma {is l : list α}
  (H : l ~ [] ++ is → (∃ ts' ~ [], l = ts' ++ is) ∨ l ∈ permutations_aux is [])
  : l ~ is → l ∈ permutations is :=
by simpa [permutations, perm_nil] using H

theorem mem_permutations_aux_of_perm :
  ∀ {ts is l : list α}, l ~ is ++ ts → (∃ is' ~ is, l = is' ++ ts) ∨ l ∈ permutations_aux ts is :=
begin
  refine permutations_aux.rec (by simp) _,
  intros t ts is IH1 IH2 l p,
  rw [permutations_aux_cons, mem_foldr_permutations_aux2],
  rcases IH1 (p.trans perm_middle) with ⟨is', p', e⟩ | m,
  { clear p, subst e,
    rcases mem_split (perm_subset p'.symm (mem_cons_self _ _)) with ⟨l₁, l₂, e⟩,
    subst is',
    have p := perm_cons_inv (perm_middle.symm.trans p'),
    cases l₂ with a l₂',
    { exact or.inl ⟨l₁, by simpa using p⟩ },
    { exact or.inr (or.inr ⟨l₁, a::l₂',
        mem_permutations_of_perm_lemma IH2 p, by simp⟩) } },
  { exact or.inr (or.inl m) }
end

@[simp] theorem mem_permutations (s t : list α) : s ∈ permutations t ↔ s ~ t :=
⟨perm_of_mem_permutations, mem_permutations_of_perm_lemma mem_permutations_aux_of_perm⟩

end permutations

end list
