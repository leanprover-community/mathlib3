/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Data type for ordered sets, based on weight balanced trees:

 * Stephen Adams, "Efficient sets: a balancing act",
   Journal of Functional Programming 3(4):553-562, October 1993,
   <http://www.swiss.ai.mit.edu/~adams/BB/>.
 * J. Nievergelt and E.M. Reingold,
   "Binary search trees of bounded balance",
   SIAM journal of computing 2(1), March 1973.

Ported from Haskell's `Data.Set`.
-/
import data.list.defs data.nat.basic

universes u

def cmp_le {α} [has_le α] [@decidable_rel α (≤)] (x y : α) : ordering :=
if x ≤ y then
  if y ≤ x then ordering.eq else ordering.lt
else ordering.gt

inductive ordnode (α : Type u) : Type u
| nil {} : ordnode
| node (size : ℕ) (l : ordnode) (x : α) (r : ordnode) : ordnode

namespace ordnode
variable {α : Type u}

instance : has_emptyc (ordnode α) := ⟨nil⟩

def delta := 3
def ratio := 2

@[inline] def singleton (a : α) : ordnode α := node 1 nil a nil

@[inline, simp] def size : ordnode α → ℕ
| nil := 0
| (node sz _ _ _) := sz

@[inline] def empty : ordnode α → bool
| nil := tt
| (node _ _ _ _) := ff

def mem' (x : α) : ordnode α → Prop
| nil := false
| (node _ l y r) := mem' l ∨ x = y ∨ mem' r

instance mem'.decidable [decidable_eq α] (x : α) (t) : decidable (mem' x t) :=
by induction t; dunfold mem'; resetI; apply_instance

def all (P : α → Prop) : ordnode α → Prop
| nil := true
| (node _ l x r) := all l ∧ P x ∧ all r

def node' (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
node (size l + size r + 1) l x r

def balance_l (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
match r, l with
| nil, nil := singleton x
| nil, node _ nil _ nil := node 2 l x nil
| nil, node _ nil lx (node _ _ lrx _) := node 3 (singleton lx) lrx (singleton x)
| nil, node _ ll lx nil := node 3 ll lx (singleton x)
| nil, node ls ll@(node lls _ _ _) lx lr@(node lrs lrl lrx lrr) :=
    if lrs < ratio * lls then
      node (ls+1) ll lx (node (lrs+1) lr x nil)
    else
      node (ls+1) (node (lls + size lrl + 1) ll lx lrl) lrx (node (size lrr + 1) lrr x nil)
| node rs _ _ _, nil := node (rs+1) nil x r
| node rs _ _ _, node ls ll lx lr :=
  if ls > delta * rs then
    match ll, lr with
    | node lls _ _ _, node lrs lrl lrx lrr :=
      if lrs < ratio * lls then
        node (ls + rs + 1) ll lx (node (rs + lrs + 1) lr x r)
      else
        node (ls + rs + 1)
          (node (lls + size lrl + 1) ll lx lrl) lrx
          (node (rs + size lrr + 1) lrr x r)
    | _, _ := nil -- should not happen
    end
  else node (ls + rs + 1) l x r
end

def balance_r (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
match l, r with
| nil, nil := singleton x
| nil, node _ nil _ nil := node 2 nil x r
| nil, node _ nil rx rr := node 3 (singleton x) rx rr
| nil, node _ (node _ _ rlx _) rx nil := node 3 (singleton x) rlx (singleton rx)
| nil, node rs rl@(node rls rll rlx rlr) rx rr@(node rrs _ _ _) :=
    if rls < ratio * rrs then
      node (rs+1) (node (rls+1) nil x rl) rx rr
    else
      node (rs+1) (node (size rll + 1) nil x rll) rlx (node (rrs + size rlr + 1) rlr rx rr)
| node ls _ _ _, nil := node (ls+1) l x nil
| node ls _ _ _, node rs rl rx rr :=
  if rs > delta * ls then
    match rl, rr with
    | node rls rll rlx rlr, node rrs _ _ _ :=
      if rls < ratio * rrs then
        node (ls + rs + 1) (node (ls + rls + 1) l x rl) rx rr
      else
        node (ls + rs + 1)
          (node (ls + size rll + 1) l x rll) rlx
          (node (rrs + size rlr + 1) rlr rx rr)
    | _, _ := nil -- should not happen
    end
  else node (ls + rs + 1) l x r
end

@[simp] def dual : ordnode α → ordnode α
| nil := nil
| (node s l x r) := node s (dual r) x (dual l)

def find_min' : ordnode α → α → α
| nil x := x
| (node _ l x r) _ := find_min' l x

def find_min : ordnode α → option α
| nil := none
| (node _ l x r) := some (find_min' l x)

def find_max' : α → ordnode α → α
| x nil := x
| _ (node _ l x r) := find_max' x r

def find_max : ordnode α → option α
| nil := none
| (node _ l x r) := some (find_max' x r)

def erase_min : ordnode α → ordnode α
| nil := nil
| (node _ nil x r) := r
| (node _ l x r) := balance_r (erase_min l) x r

def erase_max : ordnode α → ordnode α
| nil := nil
| (node _ l x nil) := l
| (node _ l x r) := balance_l l x (erase_max r)

def split_min' : ordnode α → α → ordnode α → α × ordnode α
| nil x r := (x, r)
| (node _ ll xl lr) x r :=
  let (xm, l') := split_min' ll xl lr in
  (xm, balance_r l' x r)

def split_min : ordnode α → option (α × ordnode α)
| nil := none
| (node _ l x r) := split_min' l x r

def split_max' : ordnode α → α → ordnode α → ordnode α × α
| l x nil := (l, x)
| l x (node _ rl xr rr) :=
  let (r', xm) := split_max' rl xr rr in
  (balance_l l x r', xm)

def split_max : ordnode α → option (ordnode α × α)
| nil := none
| (node _ x l r) := split_max' x l r

def glue : ordnode α → ordnode α → ordnode α
| nil r := r
| l nil := l
| l@(node sl ll xl lr) r@(node sr rl xr rr) :=
  if sl > sr then
    let (l', m) := split_max' ll xl lr in balance_r l' m r
  else
    let (m, r') := split_min' ll xl lr in balance_r l m r'

def merge (t₁ t₂ : ordnode α) : ordnode α :=
ordnode.rec_on t₁ (λ t₂, t₂)
  (λ s₁ l₁ x₁ r₁ IHl₁ IHr₁ t₂,
    ordnode.rec_on t₂ t₁ $ λ s₂ l₂ x₂ r₂ IHl₂ IHr₂,
    if delta * s₁ < s₂ then
      balance_l IHl₂ x₂ r₂
    else if delta * s₂ < s₁ then
      balance_r l₁ x₁ (IHr₁ t₂)
    else glue t₁ t₂) t₂

def insert_max : ordnode α → α → ordnode α
| nil x := singleton x
| (node _ l y r) x := balance_r l y (insert_max r x)

def insert_min (x : α) : ordnode α → ordnode α
| nil := singleton x
| (node _ l y r) := balance_r (insert_min l) y r

def link : ordnode α → α → ordnode α → ordnode α
| nil x r := insert_min x r
| l x nil := insert_max l x
| l@(node ls ll lx lr) x r@(node rs rl rx rr) :=
  if delta * ls < rs then
    balance_l (link l x rl) rx rr
  else if delta * rs < ls then
    balance_r ll lx (link lr x r)
  else node' l x r

def filter (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α
| nil := nil
| (node _ l x r) :=
  if p x then link (filter l) x (filter r)
  else merge (filter l) (filter r)

def partition (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α × ordnode α
| nil := (nil, nil)
| (node _ l x r) :=
  let (l₁, l₂) := partition l, (r₁, r₂) := partition r in
  if p x then (link l₁ x r₁, merge l₂ r₂)
  else (merge l₁ r₁, link l₂ x r₂)

def map {β} (f : α → β) : ordnode α → ordnode β
| nil := nil
| (node s l x r) := node s (map l) (f x) (map r)

def fold {β} (z : β) (f : β → α → β → β) : ordnode α → β
| nil := z
| (node _ l x r) := f (fold l) x (fold r)

def foldl {β} (f : β → α → β) : β → ordnode α → β
| z nil := z
| z (node _ l x r) := foldl (f (foldl z l) x) r

def foldr {β} (f : α → β → β) : ordnode α → β → β
| nil z := z
| (node _ l x r) z := foldr l (f x (foldr r z))

def to_list (t : ordnode α) : list α := foldr list.cons t []

def to_rev_list (t : ordnode α) : list α := foldl (flip list.cons) [] t

def equiv (t₁ t₂ : ordnode α) : Prop :=
t₁.size = t₂.size ∧ t₁.to_list = t₂.to_list

instance [decidable_eq α] : decidable_rel (@equiv α) := λ t₁ t₂, and.decidable

def powerset (t : ordnode α) : ordnode (ordnode α) :=
insert_min nil $ foldr (λ x ts, insert_min (singleton x) (map (insert_min x) ts)) t nil

protected def prod {β} (t₁ : ordnode α) (t₂ : ordnode β) : ordnode (α × β) :=
fold nil (λ s₁ a s₂, merge s₁ $ merge (map (prod.mk a) t₂) s₂) t₁

protected def copair {β} (t₁ : ordnode α) (t₂ : ordnode β) : ordnode (α ⊕ β) :=
merge (map sum.inl t₁) (map sum.inr t₂)

def pmap {P : α → Prop} {β} (f : ∀ a, P a → β) : ∀ t : ordnode α, all P t → ordnode β
| nil _ := nil
| (node s l x r) ⟨hl, hx, hr⟩ := node s (pmap l hl) (f x hx) (pmap r hr)

def attach' {P : α → Prop} : ∀ t, all P t → ordnode {a // P a} := pmap subtype.mk

def nth : ordnode α → ℕ → option α
| nil i := none
| (node _ l x r) i :=
  match nat.psub' i (size l) with
  | none         := nth l i
  | some 0       := some x
  | some (j + 1) := nth r j
  end

def remove_nth : ordnode α → ℕ → ordnode α
| nil i := nil
| (node _ l x r) i :=
  match nat.psub' i (size l) with
  | none         := balance_r (remove_nth l i) x r
  | some 0       := glue l r
  | some (j + 1) := balance_l l x (remove_nth r j)
  end

def take_aux : ordnode α → ℕ → ordnode α
| nil i := nil
| (node _ l x r) i :=
  if i = 0 then nil else
  match nat.psub' i (size l) with
  | none         := take_aux l i
  | some 0       := l
  | some (j + 1) := link l x (take_aux r j)
  end

def take (i : ℕ) (t : ordnode α) : ordnode α :=
if size t ≤ i then t else take_aux t i

def drop_aux : ordnode α → ℕ → ordnode α
| nil i := nil
| t@(node _ l x r) i :=
  if i = 0 then t else
  match nat.psub' i (size l) with
  | none         := link (drop_aux l i) x r
  | some 0       := insert_min x r
  | some (j + 1) := drop_aux r j
  end

def drop (i : ℕ) (t : ordnode α) : ordnode α :=
if size t ≤ i then nil else drop_aux t i

def split_at_aux : ordnode α → ℕ → ordnode α × ordnode α
| nil i := (nil, nil)
| t@(node _ l x r) i :=
  if i = 0 then (nil, t) else
  match nat.psub' i (size l) with
  | none         := let (l₁, l₂) := split_at_aux l i in (l₁, link l₂ x r)
  | some 0       := (glue l r, insert_min x r)
  | some (j + 1) := let (r₁, r₂) := split_at_aux r j in (link l x r₁, r₂)
  end

def split_at (i : ℕ) (t : ordnode α) : ordnode α × ordnode α :=
if size t ≤ i then (t, nil) else split_at_aux t i

def take_while (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α
| nil := nil
| (node _ l x r) := if p x then link l x (take_while r) else take_while l

def drop_while (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α
| nil := nil
| (node _ l x r) := if p x then drop_while r else link (drop_while l) x r

def span (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α × ordnode α
| nil := (nil, nil)
| (node _ l x r) :=
  if p x then let (r₁, r₂) := span r in (link l x r₁, r₂)
  else        let (l₁, l₂) := span l in (l₁, link l₂ x r)

section
variables [has_le α] [@decidable_rel α (≤)]

def find (x : α) : ordnode α → option α
| nil := none
| (node _ l y r) :=
  match cmp_le x y with
  | ordering.lt := find l
  | ordering.eq := some y
  | ordering.gt := find r
  end

instance : has_mem α (ordnode α) := ⟨λ x t, ∃ y, y ∈ t.find x⟩

instance mem.decidable (x : α) (t : ordnode α) : decidable (x ∈ t) :=
decidable_of_iff _ option.is_some_iff_exists

def insert (x : α) : ordnode α → ordnode α
| nil := singleton x
| (node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := balance_l (insert l) y r
  | ordering.eq := node sz l x r
  | ordering.gt := balance_r l y (insert r)
  end

def insert' (x : α) : ordnode α → ordnode α
| nil := singleton x
| t@(node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := balance_l (insert' l) y r
  | ordering.eq := t
  | ordering.gt := balance_r l y (insert' r)
  end

def split (x : α) : ordnode α → ordnode α × ordnode α
| nil := (nil, nil)
| (node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := let (lt, gt) := split l in (lt, link gt y r)
  | ordering.eq := (l, r)
  | ordering.gt := let (lt, gt) := split r in (link l y lt, gt)
  end

def split3 (x : α) : ordnode α → ordnode α × option α × ordnode α
| nil := (nil, none, nil)
| (node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := let (lt, f, gt) := split3 l in (lt, f, link gt y r)
  | ordering.eq := (l, some y, r)
  | ordering.gt := let (lt, f, gt) := split3 r in (link l y lt, f, gt)
  end

def erase (x : α) : ordnode α → ordnode α
| nil := nil
| t@(node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := balance_r (erase l) y r
  | ordering.eq := glue l r
  | ordering.gt := balance_l l y (erase r)
  end

def find_lt_aux (x : α) : ordnode α → α → α
| nil best := best
| (node _ l y r) best :=
  if x ≤ y then find_lt_aux l best else find_lt_aux r y

def find_lt (x : α) : ordnode α → option α
| nil := none
| (node _ l y r) :=
  if x ≤ y then find_lt l else some (find_lt_aux x r y)

def find_gt_aux (x : α) : ordnode α → α → α
| nil best := best
| (node _ l y r) best :=
  if y ≤ x then find_gt_aux r best else find_gt_aux l y

def find_gt (x : α) : ordnode α → option α
| nil := none
| (node _ l y r) :=
  if y ≤ x then find_gt r else some (find_gt_aux x l y)

def find_le_aux (x : α) : ordnode α → α → α
| nil best := best
| (node _ l y r) best :=
  match cmp_le x y with
  | ordering.lt := find_le_aux l best
  | ordering.eq := y
  | ordering.gt := find_le_aux r y
  end

def find_le (x : α) : ordnode α → option α
| nil := none
| (node _ l y r) :=
  match cmp_le x y with
  | ordering.lt := find_le l
  | ordering.eq := some y
  | ordering.gt := some (find_le_aux x r y)
  end

def find_ge_aux (x : α) : ordnode α → α → α
| nil best := best
| (node _ l y r) best :=
  match cmp_le x y with
  | ordering.lt := find_ge_aux l y
  | ordering.eq := y
  | ordering.gt := find_ge_aux r best
  end

def find_ge (x : α) : ordnode α → option α
| nil := none
| (node _ l y r) :=
  match cmp_le x y with
  | ordering.lt := some (find_ge_aux x l y)
  | ordering.eq := some y
  | ordering.gt := find_ge r
  end

def find_index_aux (x : α) : ordnode α → ℕ → option ℕ
| nil i := none
| (node _ l y r) i :=
  match cmp_le x y with
  | ordering.lt := find_index_aux l i
  | ordering.eq := some (i + size l)
  | ordering.gt := find_index_aux r (i + size l + 1)
  end

def find_index (x : α) (t : ordnode α) : option ℕ := find_index_aux x t 0

def is_subset_aux : ordnode α → ordnode α → bool
| nil _ := tt
| _ nil := ff
| (node _ l x r) t :=
  let (lt, found, gt) := split3 x t in
  found.is_some && is_subset_aux l lt && is_subset_aux r gt

def is_subset (t₁ t₂ : ordnode α) : bool :=
to_bool (size t₁ ≤ size t₂) && is_subset_aux t₁ t₂

def disjoint : ordnode α → ordnode α → bool
| nil _ := tt
| _ nil := tt
| (node _ l x r) t :=
  let (lt, found, gt) := split3 x t in
  found.is_none && disjoint l lt && disjoint r gt

def union : ordnode α → ordnode α → ordnode α
| t₁ nil := t₁
| nil t₂ := t₂
| t₁@(node s₁ l₁ x₁ r₁) t₂@(node s₂ l₂ x₂ r₂) :=
  if s₂ = 1 then insert' x₂ t₁ else
  if s₁ = 1 then insert x₁ t₂ else
  let (l₂', r₂') := split x₁ t₂ in
  link (union l₁ l₂') x₁ (union r₁ r₂')

def diff : ordnode α → ordnode α → ordnode α
| t₁ nil := t₁
| t₁ t₂@(node _ l₂ x r₂) := cond t₁.empty t₂ $
  let (l₁, r₁) := split x t₁,
      l₁₂ := diff l₁ l₂, r₁₂ := diff r₁ r₂ in
  if size l₁₂ + size r₁₂ = size t₁ then t₁ else
  merge l₁₂ r₁₂

def inter : ordnode α → ordnode α → ordnode α
| nil t₂ := nil
| t₁@(node _ l₁ x r₁) t₂ := cond t₂.empty t₁ $
  let (l₂, y, r₂) := split3 x t₂,
      l₁₂ := inter l₁ l₂, r₁₂ := inter r₁ r₂ in
  cond y.is_some (link l₁₂ x r₁₂) (merge l₁₂ r₁₂)

def of_asc_list_aux₁ : ∀ l : list α, ℕ → ordnode α × {l' : list α // l'.length ≤ l.length}
| [] := λ s, (nil, ⟨[], le_refl _⟩)
| (x :: xs) := λ s,
  if s = 1 then (singleton x, ⟨xs, nat.le_succ _⟩) else
  have _, from nat.lt_succ_self xs.length,
  match of_asc_list_aux₁ xs (s.shiftl 1) with
  | (t, ⟨[], h⟩) := (t, ⟨[], nat.zero_le _⟩)
  | (l, ⟨y :: ys, h⟩) :=
    have _, from nat.le_succ_of_le h,
    let (r, ⟨zs, h'⟩) := of_asc_list_aux₁ ys (s.shiftl 1) in
    (link l y r, ⟨zs, le_trans h' (le_of_lt this)⟩)
  end
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩],
  dec_tac := `[assumption] }

def of_asc_list_aux₂ : list α → ordnode α → ℕ → ordnode α
| [] := λ t s, t
| (x :: xs) := λ l s,
  have _, from nat.lt_succ_self xs.length,
  match of_asc_list_aux₁ xs s with
  | (r, ⟨ys, h⟩) :=
    have _, from nat.lt_succ_of_le h,
    of_asc_list_aux₂ ys (link l x r) (s.shiftl 1)
  end
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩],
  dec_tac := `[assumption] }

def of_asc_list : list α → ordnode α
| [] := nil
| (x :: xs) := of_asc_list_aux₂ xs (singleton x) 1

def of_list (l : list α) : ordnode α := l.foldr insert nil

def of_list' : list α → ordnode α
| [] := nil
| (x :: xs) :=
  if list.chain (λ a b, ¬ b ≤ a) x xs
  then of_asc_list (x :: xs)
  else of_list (x :: xs)

def image {β} [has_le β] [@decidable_rel β (≤)]
  (f : α → β) (t : ordnode α) : ordnode β :=
of_list (t.to_list.map f)

end

end ordnode
