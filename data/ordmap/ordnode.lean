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

private def delta := 3
private def ratio := 2

@[inline] def singleton (a : α) : ordnode α := node 1 nil a nil

@[inline] def size : ordnode α → ℕ
| nil := 0
| (node sz _ _ _) := sz

@[inline] def empty : ordnode α → bool
| nil := tt
| (node _ _ _ _) := ff

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
          (node (ls + size rll + 1) l x rl) rlx
          (node (rrs + size rlr + 1) rlr rx rr)
    | _, _ := nil -- should not happen
    end
  else node (ls + rs + 1) l x r
end

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

def merge : ordnode α → ordnode α → ordnode α
| nil t₂ := t₂
| t₁ nil := t₁
| t₁@(node s₁ l₁ x₁ r₁) t₂@(node s₂ l₂ x₂ r₂) :=
  if delta * s₁ < s₂ then
    balance_l (merge t₁ l₂) x₂ r₂
  else if delta * s₂ < s₁ then
    balance_r l₁ x₁ (merge r₁ t₂)
  else glue t₁ t₂

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

section
variables [has_le α] [@decidable_rel α (≤)]

def find (x : α) : ordnode α → option α
| nil := none
| (node _ l y r) :=
  match cmp_le x y with
  | ordering.lt := find l
  | ordering.gt := find r
  | ordering.eq := some y
  end

def insert (x : α) : ordnode α → ordnode α
| nil := singleton x
| (node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := balance_l (insert l) y r
  | ordering.gt := balance_r l y (insert r)
  | ordering.eq := node sz l x r
  end

def insert' (x : α) : ordnode α → ordnode α
| nil := singleton x
| t@(node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := balance_l (insert' l) y r
  | ordering.gt := balance_r l y (insert' r)
  | ordering.eq := t
  end

def split (x : α) : ordnode α → ordnode α × ordnode α
| nil := (nil, nil)
| (node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := let (lt, gt) := split l in (lt, link gt y r)
  | ordering.gt := let (lt, gt) := split r in (link l y lt, gt)
  | ordering.eq := (l, r)
  end

def split3 (x : α) : ordnode α → ordnode α × option α × ordnode α
| nil := (nil, none, nil)
| (node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := let (lt, f, gt) := split3 l in (lt, f, link gt y r)
  | ordering.gt := let (lt, f, gt) := split3 r in (link l y lt, f, gt)
  | ordering.eq := (l, some y, r)
  end

def erase (x : α) : ordnode α → ordnode α
| nil := nil
| t@(node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := balance_r (erase l) y r
  | ordering.gt := balance_l l y (erase r)
  | ordering.eq := glue l r
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
  | ordering.gt := find_le_aux r y
  | ordering.eq := y
  end

def find_le (x : α) : ordnode α → option α
| nil := none
| (node _ l y r) :=
  match cmp_le x y with
  | ordering.lt := find_le l
  | ordering.gt := some (find_le_aux x r y)
  | ordering.eq := some y
  end

def find_ge_aux (x : α) : ordnode α → α → α
| nil best := best
| (node _ l y r) best :=
  match cmp_le x y with
  | ordering.lt := find_ge_aux l y
  | ordering.gt := find_ge_aux r best
  | ordering.eq := y
  end

def find_ge (x : α) : ordnode α → option α
| nil := none
| (node _ l y r) :=
  match cmp_le x y with
  | ordering.lt := some (find_ge_aux x l y)
  | ordering.gt := find_ge r
  | ordering.eq := some y
  end

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
| nil t₂ := nil
| t₁ nil := t₁
| t₁ t₂@(node _ l₂ x r₂) :=
  let (l₁, r₁) := split x t₁,
      l₁₂ := diff l₁ l₂, r₁₂ := diff r₁ r₂ in
  if size l₁₂ + size r₁₂ = size t₁ then t₁ else
  merge l₁₂ r₁₂

end

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

end ordnode
