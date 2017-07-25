/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Haitao Zhang, Floris van Doorn

List combinators.
-/
import data.list.basic data.bool

universes u v w

namespace list

open nat

variables {α : Type u} {β : Type v} {φ : Type w}

section map_accumr
variable {σ : Type}

-- This runs a function over a list returning the intermediate results and a
-- a final result.
def map_accumr (f : α → σ → σ × β) : list α → σ → (σ × list β)
| [] c := (c, [])
| (y::yr) c :=
  let r := map_accumr yr c in
  let z := f y (prod.fst r) in
  (prod.fst z, prod.snd z :: prod.snd r)

@[simp] theorem length_map_accumr
: ∀ (f : α → σ → σ × β) (x : list α) (s : σ),
  length (prod.snd (map_accumr f x s)) = length x
| f (a::x) s := congr_arg succ (length_map_accumr f x s)
| f [] s := rfl

end map_accumr

section map_accumr₂

-- This runs a function over two lists returning the intermediate results and a
-- a final result.
def map_accumr₂ {α β σ φ : Type} (f : α → β → σ → σ × φ)
  : list α → list β → σ → σ × list φ
| [] _ c := (c,[])
| _ [] c := (c,[])
| (x::xr) (y::yr) c :=
  let r := map_accumr₂ xr yr c in
  let q := f x y (prod.fst r) in
  (prod.fst q, prod.snd q :: (prod.snd r))

@[simp] theorem length_map_accumr₂ {α β σ φ : Type}
: ∀ (f : α → β → σ → σ × φ) x y c,
  length (prod.snd (map_accumr₂ f x y c)) = min (length x) (length y)
| f (a::x) (b::y) c := calc
    succ (length (prod.snd (map_accumr₂ f x y c)))
              = succ (min (length x) (length y))
              : congr_arg succ (length_map_accumr₂ f x y c)
          ... = min (succ (length x)) (succ (length y))
              : eq.symm (min_succ_succ (length x) (length y))
| f (a::x) [] c := rfl
| f [] (b::y) c := rfl
| f [] []     c := rfl
end map_accumr₂

@[simp] theorem foldl_nil (f : α → β → α) (a : α) : foldl f a [] = a := rfl

@[simp] theorem foldl_cons (f : α → β → α) (a : α) (b : β) (l : list β) :
  foldl f a (b::l) = foldl f (f a b) l := rfl

@[simp] theorem foldr_nil (f : α → β → β) (b : β) : foldr f b [] = b := rfl

@[simp] theorem foldr_cons (f : α → β → β) (b : β) (a : α) (l : list α) :
  foldr f b (a::l) = f a (foldr f b l) := rfl

@[simp] theorem foldl_append (f : β → α → β) :
  ∀ (b : β) (l₁ l₂ : list α), foldl f b (l₁++l₂) = foldl f (foldl f b l₁) l₂
| b []      l₂ := rfl
| b (a::l₁) l₂ := by simp [foldl_append]

@[simp] theorem foldr_append (f : α → β → β) :
  ∀ (b : β) (l₁ l₂ : list α), foldr f b (l₁++l₂) = foldr f (foldr f b l₂) l₁
| b []      l₂ := rfl
| b (a::l₁) l₂ := by simp [foldr_append]

theorem foldl_reverse (f : α → β → α) (a : α) (l : list β) : foldl f a (reverse l) = foldr (λx y, f y x) a l :=
by induction l; simp [*, foldl, foldr]

theorem foldr_reverse (f : α → β → β) (a : β) (l : list α) : foldr f a (reverse l) = foldl (λx y, f y x) a l :=
let t := foldl_reverse (λx y, f y x) a (reverse l) in
by rw reverse_reverse l at t; rwa t

end list

-- TODO(Leo): uncomment data.equiv after refactoring
open nat prod decidable function

namespace list

universe variables uu vv ww
variables {α : Type uu} {β : Type vv} {γ : Type ww}

-- TODO(Jeremy): this file is a good testing ground for super and auto

section replicate

-- 'replicate n a' returns the list that contains n copies of a.
def replicate : ℕ → α → list α
| 0 a := []
| (succ n) a := a :: replicate n a

@[simp] theorem length_replicate : ∀ (i : ℕ) (a : α), length (replicate i a) = i
| 0 a := rfl
| (succ i) a := congr_arg succ (length_replicate i a)

end replicate

/- map -/

attribute [simp] map_cons

/-def map₂ (f : α → β → γ) : list α → list β → list γ
| []      _       := []
| _       []      := []
| (x::xs) (y::ys) := f x y :: map₂ xs ys-/

theorem map₂_nil1 (f : α → β → γ) : ∀ (l : list β), map₂ f [] l = []
| []     := rfl
| (a::y) := rfl

theorem map₂_nil2 (f : α → β → γ) : ∀ (l : list α), map₂ f l [] = []
| []     := rfl
| (a::y) := rfl

/- TODO(Jeremy): there is an overload ambiguity between min and nat.min -/
/-theorem length_map₂ : ∀ (f : α → β → γ) x y, length (map₂ f x y) = _root_.min (length x) (length y)
| f []       [] := rfl
| f (xh::xr) [] := rfl
| f [] (yh::yr) := rfl
| f (xh::xr) (yh::yr) := calc
  length (map₂ f (xh::xr) (yh::yr))
          = length (map₂ f xr yr) + 1                 : rfl
      ... = _root_.min (length xr) (length yr) + 1    : by rw length_map₂
      ... = _root_.min (succ (length xr)) (succ (length yr))
                                                      : begin rw min_succ_succ, reflexivity end
      ... = _root_.min (length (xh::xr)) (length (yh::yr)) : rfl-/

section foldl_eq_foldr
  -- foldl and foldr coincide when f is commutative and associative
  variables {f : α → α → α} (hcomm  : ∀ a b, f a b = f b a) (hassoc : ∀ a b c, f (f a b) c = f a (f b c))
  include hcomm hassoc

  theorem foldl_eq_of_comm_of_assoc : ∀ a b l, foldl f a (b::l) = f b (foldl f a l)
  | a b  nil    := hcomm a b
  | a b  (c::l) :=
    begin
      change foldl f (f (f a b) c) l = f b (foldl f (f a c) l),
      rw ←foldl_eq_of_comm_of_assoc,
      change foldl f (f (f a b) c) l = foldl f (f (f a c) b) l,
      have h₁ : f (f a b) c = f (f a c) b, { rw [hassoc, hassoc, hcomm b c] },
      rw h₁
    end

  theorem foldl_eq_foldr : ∀ a l, foldl f a l = foldr f a l
  | a nil      := rfl
  | a (b :: l) :=
    begin
      simp [foldl_eq_of_comm_of_assoc hcomm hassoc],
      change f b (foldl f a l) = f b (foldr f a l),
      rw (foldl_eq_foldr a l)
    end
end foldl_eq_foldr

/- all & any -/

@[simp] theorem all_nil (p : α → bool) : all [] p = tt := rfl

@[simp] theorem all_cons (p : α → bool) (a : α) (l : list α) : all (a::l) p = (p a && all l p) := rfl

theorem all_eq_tt_of_forall {p : α → bool} : ∀ {l : list α}, (∀ a ∈ l, p a = tt) → all l p = tt
| []     h := all_nil p
| (a::l) h := begin
                simp [all_cons, h a],
                rw all_eq_tt_of_forall,
                intros a ha, simp [h a, ha] end

theorem forall_mem_eq_tt_of_all_eq_tt {p : α → bool} :
  ∀ {l : list α}, all l p = tt → ∀ a ∈ l, p a = tt
| []     h := assume a h, absurd h (not_mem_nil a)
| (b::l) h := assume a, assume : a ∈ b::l,
              begin
                simp [bool.band_eq_tt] at h, cases h with h₁ h₂,
                simp at this, cases this with h' h',
                simp [*],
                exact forall_mem_eq_tt_of_all_eq_tt h₂ _ h'
              end

theorem all_eq_tt_iff {p : α → bool} {l : list α} : all l p = tt ↔ ∀ a ∈ l, p a = tt :=
iff.intro forall_mem_eq_tt_of_all_eq_tt all_eq_tt_of_forall

@[simp] theorem any_nil (p : α → bool) : any [] p = ff := rfl

@[simp] theorem any_cons (p : α → bool) (a : α) (l : list α) : any (a::l) p = (p a || any l p) := rfl

theorem any_of_mem {p : α → bool} {a : α} : ∀ {l : list α}, a ∈ l → p a = tt → any l p = tt
| []     i h := absurd i (not_mem_nil a)
| (b::l) i h :=
  or.elim (eq_or_mem_of_mem_cons i)
    (assume : a = b, begin simp [this.symm, bool.bor_eq_tt], exact (or.inl h) end)
    (assume : a ∈ l, begin
                      cases (eq_or_mem_of_mem_cons i) with h' h',
                      { simp [h'.symm, h] },
                      simp [bool.bor_eq_tt, any_of_mem h', h]
                    end)

theorem exists_of_any_eq_tt {p : α → bool} : ∀ {l : list α}, any l p = tt → ∃ a : α, a ∈ l ∧ p a
| []     h := begin simp at h, contradiction end
| (b::l) h := begin
                simp [bool.bor_eq_tt] at h, cases h with h h,
                { existsi b, simp [h]},
                cases (exists_of_any_eq_tt h) with a ha,
                existsi a, apply (and.intro (or.inr ha.left) ha.right)
              end

theorem any_eq_tt_iff {p : α → bool} {l : list α} : any l p = tt ↔ ∃ a : α, a ∈ l ∧ p a = tt :=
iff.intro exists_of_any_eq_tt (begin intro h, cases h with a ha, apply any_of_mem ha.left ha.right end)

/- bounded quantifiers over lists -/

theorem forall_mem_nil (p : α → Prop) : ∀ x ∈ @nil α, p x :=
assume x xnil, absurd xnil (not_mem_nil x)

theorem forall_mem_cons {p : α → Prop} {a : α} {l : list α} (pa : p a) (h : ∀ x ∈ l, p x) :
  ∀ x ∈ a :: l, p x :=
assume x xal, or.elim (eq_or_mem_of_mem_cons xal)
  (assume : x = a, by simp [this, pa])
  (assume : x ∈ l, by simp [this, h])

theorem of_forall_mem_cons {p : α → Prop} {a : α} {l : list α} (h : ∀ x ∈ a :: l, p x) : p a :=
h a (by simp)

theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : list α}
    (h : ∀ x ∈ a :: l, p x) :
  ∀ x ∈ l, p x :=
assume x xl, h x (by simp [xl])

@[simp] theorem forall_mem_cons_iff (p : α → Prop) (a : α) (l : list α) :
  (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x :=
iff.intro
  (λ h, ⟨of_forall_mem_cons h, forall_mem_of_forall_mem_cons h⟩)
  (λ h, forall_mem_cons h.left h.right)

theorem not_exists_mem_nil (p : α → Prop) : ¬ ∃ x ∈ @nil α, p x :=
assume h, bexists.elim h (λ a anil, absurd anil (not_mem_nil a))

theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : list α) (h : p a) :
  ∃ x ∈ a :: l, p x :=
bexists.intro a (by simp) h

theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : list α} (h : ∃ x ∈ l, p x) :
  ∃ x ∈ a :: l, p x :=
bexists.elim h (λ x xl px, bexists.intro x (by simp [xl]) px)

theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : list α} (h : ∃ x ∈ a :: l, p x) :
  p a ∨ ∃ x ∈ l, p x :=
bexists.elim h (λ x xal px,
  or.elim (eq_or_mem_of_mem_cons xal)
    (assume : x = a, begin rw ←this, simp [px] end)
    (assume : x ∈ l, or.inr (bexists.intro x this px)))

@[simp] theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : list α) :
  (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
iff.intro or_exists_of_exists_mem_cons
  (assume h, or.elim h (exists_mem_cons_of l) exists_mem_cons_of_exists)

instance decidable_forall_mem {p : α → Prop} [h : decidable_pred p] :
  ∀ l : list α, decidable (∀ x ∈ l, p x)
| []       := is_true (forall_mem_nil p)
| (a :: l) := decidable_of_decidable_of_iff
                (@and.decidable _ _ _ (decidable_forall_mem l))
                (forall_mem_cons_iff p a l).symm

instance decidable_exists_mem {p : α → Prop} [h : decidable_pred p] :
  ∀ l : list α, decidable (∃ x ∈ l, p x)
| []       := is_false (not_exists_mem_nil p)
| (a :: l) := decidable_of_decidable_of_iff
                (@or.decidable _ _ _ (decidable_exists_mem l))
                (exists_mem_cons_iff p a l).symm

/- zip & unzip -/

@[simp] theorem zip_cons_cons (a : α) (b : β) (l₁ : list α) (l₂ : list β) :
  zip (a :: l₁) (b :: l₂) = (a, b) :: zip l₁ l₂ := rfl

@[simp] theorem zip_nil_left (l : list α) : zip ([] : list β) l = [] := rfl

@[simp] theorem zip_nil_right (l : list α) : zip l ([] : list β) = [] :=
by cases l; refl

@[simp] theorem unzip_nil : unzip (@nil (α × β)) = ([], []) := rfl

theorem unzip_cons' (a : α) (b : β) (l : list (α × β)) :
   unzip ((a, b) :: l) = match (unzip l) with (la, lb) := (a :: la, b :: lb) end := rfl

-- TODO(Jeremy): it seems this version is better for the simplifier
@[simp] theorem unzip_cons (a : α) (b : β) (l : list (α × β)) :
   unzip ((a, b) :: l) = let p := unzip l in (a :: p.1, b :: p.2) :=
by rw unzip_cons'; cases unzip l; refl

theorem zip_unzip : ∀ (l : list (α × β)), zip (unzip l).1 (unzip l).2 = l
| []            := rfl
| ((a, b) :: l) := begin simp [zip_unzip l] end

-- TODO(Jeremy): this is as far as I got

section mapAccumR
variable {S : Type}

-- This runs a function over a list returning the intermediate results and a
-- a final result.
def mapAccumR : (α → S → S × β) → list α → S → (S × list β)
| f [] c := (c, [])
| f (y::yr) c :=
  let r := mapAccumR f yr c in
  let z := f y r.1 in
  (z.1, z.2 :: r.2)

theorem length_mapAccumR :
  ∀ (f : α → S → S × β) (x : list α) (s : S),
    length (mapAccumR f x s).2 = length x
| f (a::x) s := calc
  length (snd (mapAccumR f (a::x) s))
                = length x + 1              : begin rw ←(length_mapAccumR f x s), reflexivity end
            ... = length (a::x)             : rfl
| f [] s := calc  length (snd (mapAccumR f [] s)) = 0 : by reflexivity

end mapAccumR

section mapAccumR₂
variable {S : Type uu}
-- This runs a function over two lists returning the intermediate results and a
-- a final result.
def mapAccumR₂
: (α → β → S → S × γ) → list α → list β → S → S × list γ
| f [] _ c := (c,[])
| f _ [] c := (c,[])
| f (x::xr) (y::yr) c :=
  let r := mapAccumR₂ f xr yr c in
  let q := f x y r.1 in
  (q.1, q.2 :: r.2)

-- TODO(Jeremy) : again the "min" overload

theorem length_mapAccumR₂ : ∀ (f : α → β → S → S × γ) (x : list α) (y : list β) (c : S),
  length (mapAccumR₂ f x y c).2 = _root_.min (length x) (length y)
| f (a::x) (b::y) c := calc
    length (snd (mapAccumR₂ f (a::x) (b::y) c))
              = length (snd (mapAccumR₂ f x y c)) + 1  : rfl
          ... = _root_.min (length x) (length y) + 1             : by rw (length_mapAccumR₂ f x y c)
          ... = _root_.min (succ (length x)) (succ (length y))   : begin rw min_succ_succ end
          ... = _root_.min (length (a::x)) (length (b::y))       : rfl
| f (a::x) [] c := rfl
| f [] (b::y) c := rfl
| f [] []     c := rfl

end mapAccumR₂

/- flat -/
def flat (l : list (list α)) : list α :=
foldl append nil l

/- product -/
section product

def product : list α → list β → list (α × β)
| []      l₂ := []
| (a::l₁) l₂ := map (λ b, (a, b)) l₂ ++ product l₁ l₂

theorem nil_product (l : list β) : product (@nil α) l = [] := rfl

theorem product_cons (a : α) (l₁ : list α) (l₂ : list β)
        : product (a::l₁) l₂ = map (λ b, (a, b)) l₂ ++ product l₁ l₂ := rfl

theorem product_nil : ∀ (l : list α), product l (@nil β) = []
| []     := rfl
| (a::l) := begin rw [product_cons, product_nil], reflexivity end

theorem eq_of_mem_map_pair₁  {a₁ a : α} {b₁ : β} {l : list β} :
  (a₁, b₁) ∈ map (λ b, (a, b)) l → a₁ = a :=
assume ain,
have fst (a₁, b₁) ∈ map fst (map (λ b, (a, b)) l), from mem_map fst ain,
have a₁ ∈ map (λb, a) l, begin revert this, rw [map_map], intro this, assumption end,
eq_of_map_const this

theorem mem_of_mem_map_pair₁ {a₁ a : α} {b₁ : β} {l : list β} :
  (a₁, b₁) ∈ map (λ b, (a, b)) l → b₁ ∈ l :=
assume ain,
have snd (a₁, b₁) ∈ map snd (map (λ b, (a, b)) l), from mem_map snd ain,
have b₁ ∈ map id l, begin rw [map_map] at this, exact this end,
begin rw [map_id] at this, exact this end

theorem mem_product {a : α} {b : β} : ∀ {l₁ l₂}, a ∈ l₁ → b ∈ l₂ → (a, b) ∈ @product α β l₁ l₂
| []      l₂ h₁ h₂ := absurd h₁ (not_mem_nil _)
| (x::l₁) l₂ h₁ h₂ :=
  or.elim (eq_or_mem_of_mem_cons h₁)
    (assume aeqx  : a = x,
      have (a, b) ∈ map (λ b, (a, b)) l₂, from mem_map _ h₂,
      begin rw [←aeqx, product_cons], exact mem_append_left _ this end)
    (assume ainl₁ : a ∈ l₁,
      have (a, b) ∈ product l₁ l₂, from mem_product ainl₁ h₂,
      begin rw [product_cons], exact mem_append_right _ this end)

theorem mem_of_mem_product_left {a : α} {b : β} : ∀ {l₁ l₂}, (a, b) ∈ @product α β l₁ l₂ → a ∈ l₁
| []      l₂ h := absurd h (not_mem_nil _)
| (x::l₁) l₂ h :=
  or.elim (mem_append.1 h)
    (assume : (a, b) ∈ map (λ b, (x, b)) l₂,
       have a = x, from eq_of_mem_map_pair₁ this,
       begin rw this, apply mem_cons_self end)
    (assume : (a, b) ∈ product l₁ l₂,
      have a ∈ l₁, from mem_of_mem_product_left this,
      mem_cons_of_mem _ this)

theorem mem_of_mem_product_right {a : α} {b : β} : ∀ {l₁ l₂}, (a, b) ∈ @product α β l₁ l₂ → b ∈ l₂
| []      l₂ h := absurd h (not_mem_nil ((a, b)))
| (x::l₁) l₂ h :=
  or.elim (mem_append.1 h)
    (assume : (a, b) ∈ map (λ b, (x, b)) l₂,
      mem_of_mem_map_pair₁ this)
    (assume : (a, b) ∈ product l₁ l₂,
      mem_of_mem_product_right this)

theorem length_product :
  ∀ (l₁ : list α) (l₂ : list β), length (product l₁ l₂) = length l₁ * length l₂
| []      l₂ := begin simp, reflexivity end
| (x::l₁) l₂ :=
  have length (product l₁ l₂) = length l₁ * length l₂, from length_product l₁ l₂,
  by rw [product_cons, length_append, length_cons,
              length_map, this, right_distrib, one_mul, add_comm]
end product

-- new for list/comb dependent map theory
def dinj₁ (p : α → Prop) (f : Π a, p a → β) := ∀ ⦃a1 a2⦄ (h1 : p a1) (h2 : p a2), a1 ≠ a2 → (f a1 h1) ≠ (f a2 h2)
def dinj (p : α → Prop) (f : Π a, p a → β) := ∀ ⦃a1 a2⦄ (h1 : p a1) (h2 : p a2), (f a1 h1) = (f a2 h2) → a1 = a2

def dmap (p : α → Prop) [h : decidable_pred p] (f : Π a, p a → β) : list α → list β
| []       := []
| (a::l)   := if P : (p a) then cons (f a P) (dmap l) else (dmap l)

-- properties of dmap
section dmap

variable {p : α → Prop}
variable [h : decidable_pred p]
include h
variable {f : Π a, p a → β}

theorem dmap_nil : dmap p f [] = [] := rfl
theorem dmap_cons_of_pos {a : α} (P : p a) : ∀ l, dmap p f (a::l) = (f a P) :: dmap p f l :=
      λ l, dif_pos P
theorem dmap_cons_of_neg {a : α} (P : ¬ p a) : ∀ l, dmap p f (a::l) = dmap p f l :=
      λ l, dif_neg P

theorem mem_dmap : ∀ {l : list α} {a} (Pa : p a), a ∈ l → (f a Pa) ∈ dmap p f l
| []     := assume a Pa Pinnil, absurd Pinnil (not_mem_nil _)
| (a::l) := assume b Pb Pbin, or.elim (eq_or_mem_of_mem_cons Pbin)
              (assume Pbeqa, begin
                rw [eq.symm Pbeqa, dmap_cons_of_pos Pb],
                apply mem_cons_self
              end)
              (assume Pbinl,
                if pa : p a then
                  begin
                    rw [dmap_cons_of_pos pa],
                    apply mem_cons_of_mem,
                    exact mem_dmap Pb Pbinl
                  end
                else
                  begin
                    rw [dmap_cons_of_neg pa],
                    exact mem_dmap Pb Pbinl
                   end)

theorem exists_of_mem_dmap : ∀ {l : list α} {b : β}, b ∈ dmap p f l → ∃ a P, a ∈ l ∧ b = f a P
| []     := assume b, begin rw dmap_nil, intro h, exact absurd h (not_mem_nil _) end
| (a::l) := assume b,
  if Pa : p a then
    begin
      rw [dmap_cons_of_pos Pa, mem_cons_iff],
      intro Pb, cases Pb with Peq Pin,
      exact exists.intro a (exists.intro Pa (and.intro (mem_cons_self _ _) Peq)),
      have Pex : ∃ (a : α) (P : p a), a ∈ l ∧ b = f a P, exact exists_of_mem_dmap Pin,
      cases Pex with a' Pex', cases Pex' with Pa' P',
      exact exists.intro a' (exists.intro Pa' (and.intro (mem_cons_of_mem a (and.left P'))
         (and.right P')))
    end
  else
    begin
      rw [dmap_cons_of_neg Pa],
      intro Pin,
      have Pex : ∃ (a : α) (P : p a), a ∈ l ∧ b = f a P, exact exists_of_mem_dmap Pin,
      cases Pex with a' Pex', cases Pex' with Pa' P',
      exact exists.intro a' (exists.intro Pa' (and.intro (mem_cons_of_mem a (and.left P'))
          (and.right P')))
    end

theorem map_dmap_of_inv_of_pos {g : β → α} (Pinv : ∀ a (Pa : p a), g (f a Pa) = a) :
                          ∀ {l : list α}, (∀ ⦃a⦄, a ∈ l → p a) → map g (dmap p f l) = l
| []     := assume Pl, by rw [dmap_nil]; reflexivity
| (a::l) := assume Pal,
            have Pa : p a, from Pal (mem_cons_self _ _),
            have Pl : ∀ a, a ∈ l → p a,
              from assume x Pxin, Pal (mem_cons_of_mem a Pxin),
            by rw [dmap_cons_of_pos Pa, map_cons, Pinv, map_dmap_of_inv_of_pos Pl]

theorem mem_of_dinj_of_mem_dmap (Pdi : dinj p f) :
      ∀ {l : list α} {a} (Pa : p a), (f a Pa) ∈ dmap p f l → a ∈ l
| []     := assume a Pa Pinnil, absurd Pinnil (not_mem_nil _)
| (b::l) := assume a Pa Pmap,
              if Pb : p b then
                begin
                  rw (dmap_cons_of_pos Pb) at Pmap,
                  rw mem_cons_iff at Pmap,
                  rw mem_cons_iff,
                  cases Pmap with h h,
                    left, apply Pdi Pa Pb h,
                    right, apply mem_of_dinj_of_mem_dmap Pa h
                end
              else
                begin
                  rw (dmap_cons_of_neg Pb) at Pmap,
                  apply mem_cons_of_mem,
                  exact mem_of_dinj_of_mem_dmap Pa Pmap
                end

theorem not_mem_dmap_of_dinj_of_not_mem (Pdi : dinj p f) {l : list α} {a} (Pa : p a) :
  a ∉ l → (f a Pa) ∉ dmap p f l :=
mt (mem_of_dinj_of_mem_dmap Pdi Pa)

end dmap

/-
section
open equiv
def list_equiv_of_equiv {α β : Type} : α ≃ β → list α ≃ list β
| (mk f g l r) :=
  mk (map f) (map g)
   begin intros, rw [map_map, id_of_left_inverse l, map_id], try reflexivity end
   begin intros, rw [map_map, id_of_right_inverse r, map_id], try reflexivity end

private def to_nat : list nat → nat
| []      := 0
| (x::xs) := succ (mkpair (to_nat xs) x)

open prod.ops

private def of_nat.F : Π (n : nat), (Π m, m < n → list nat) → list nat
| 0        f := []
| (succ n) f := (unpair n).2 :: f (unpair n).1 (unpair_lt n)

private def of_nat : nat → list nat :=
well_founded.fix of_nat.F

private lemma of_nat_zero : of_nat 0 = [] :=
well_founded.fix_eq of_nat.F 0

private lemma of_nat_succ (n : nat)
      : of_nat (succ n) = (unpair n).2 :: of_nat (unpair n).1 :=
well_founded.fix_eq of_nat.F (succ n)

private lemma to_nat_of_nat (n : nat) : to_nat (of_nat n) = n :=
nat.case_strong_induction_on n
 _
 (λ n ih,
  begin
    rw of_nat_succ, unfold to_nat,
    have to_nat (of_nat (unpair n).1) = (unpair n).1, from ih _ (le_of_lt_succ (unpair_lt n)),
    rw this, rw mkpair_unpair
  end)

private lemma of_nat_to_nat : ∀ (l : list nat), of_nat (to_nat l) = l
| []      := rfl
| (x::xs) := begin unfold to_nat, rw of_nat_succ, rw *unpair_mkpair, esimp, congruence, apply of_nat_to_nat end

def list_nat_equiv_nat : list nat ≃ nat :=
mk to_nat of_nat of_nat_to_nat to_nat_of_nat

def list_equiv_self_of_equiv_nat {α : Type} : α ≃ nat → list α ≃ α :=
assume : α ≃ nat, calc
  list α ≃ list nat : list_equiv_of_equiv this
     ... ≃ nat      : list_nat_equiv_nat
     ... ≃ α        : this
end
-/

end list
