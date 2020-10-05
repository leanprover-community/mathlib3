/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- theorems which we should (maybe) backport to mathlib -/

import algebra.ordered_group
import data.set.disjointed
import data.set.countable
import set_theory.cofinality
import topology.opens
-- import topology.maps
import tactic

universe variables u v w w'

inductive dvector (α : Type u) : ℕ → Type u
| nil {} : dvector 0
| cons : ∀{n} (x : α) (xs : dvector n), dvector (n+1)

inductive dfin : ℕ → Type
| fz {n} : dfin (n+1)
| fs {n} : dfin n → dfin (n+1)

instance has_zero_dfin {n} : has_zero $ dfin (n+1) := ⟨dfin.fz⟩

-- note from Mario --- use dfin to synergize with dvector
namespace dvector
section dvectors
local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l
variables {α : Type u} {β : Type v} {γ : Type w} {n : ℕ}

@[simp] protected lemma zero_eq : ∀(xs : dvector α 0), xs = []
| [] := rfl

@[simp] protected def concat : ∀{n : ℕ} (xs : dvector α n) (x : α), dvector α (n+1)
| _ []      x' := [x']
| _ (x::xs) x' := x::concat xs x'

@[simp] protected def nth : ∀{n : ℕ} (xs : dvector α n) (m : ℕ) (h : m < n), α
| _ []      m     h := by { exfalso, exact nat.not_lt_zero m h }
| _ (x::xs) 0     h := x
| _ (x::xs) (m+1) h := nth xs m (lt_of_add_lt_add_right h)

protected lemma nth_cons {n : ℕ} (x : α) (xs : dvector α n) (m : ℕ) (h : m < n) :
  dvector.nth (x::xs) (m+1) (nat.succ_lt_succ h) = dvector.nth xs m h :=
by refl

@[reducible, simp] protected def last {n : ℕ} (xs : dvector α (n+1)) : α :=
  xs.nth n (by {repeat{constructor}})

protected def nth' {n : ℕ} (xs : dvector α n) (m : fin n) : α :=
xs.nth m.1 m.2

protected def nth'' : ∀ {n : ℕ} (xs : dvector α n) (m : dfin n), α
| _ (x::xs) dfin.fz       := x
| _ (x::xs) (dfin.fs (m)) := nth'' xs m

protected def mem : ∀{n : ℕ} (x : α) (xs : dvector α n), Prop
| _ x []       := false
| _ x (x'::xs) := x = x' ∨ mem x xs
instance {n : ℕ} : has_mem α (dvector α n) := ⟨dvector.mem⟩

protected def pmem : ∀{n : ℕ} (x : α) (xs : dvector α n), Type
| _ x []       := empty
| _ x (x'::xs) := psum (x = x') (pmem x xs)

protected lemma mem_of_pmem : ∀{n : ℕ} {x : α} {xs : dvector α n} (hx : xs.pmem x), x ∈ xs
| _ x []       hx := by cases hx
| _ x (x'::xs) hx := by cases hx;[exact or.inl hx, exact or.inr (mem_of_pmem hx)]

@[simp] protected def map (f : α → β) : ∀{n : ℕ}, dvector α n → dvector β n
| _ []      := []
| _ (x::xs) := f x :: map xs

@[simp] protected def map2 (f : α → β → γ) : ∀{n : ℕ}, dvector α n → dvector β n → dvector γ n
| _ []      []      := []
| _ (x::xs) (y::ys) := f x y :: map2 xs ys

@[simp] protected lemma map_id : ∀{n : ℕ} (xs : dvector α n), xs.map (λx, x) = xs
| _ []      := rfl
| _ (x::xs) := by { dsimp, simp* }

@[simp] protected lemma map_congr_pmem {f g : α → β} :
  ∀{n : ℕ} {xs : dvector α n} (h : ∀x, xs.pmem x → f x = g x), xs.map f = xs.map g
| _ []      h := rfl
| _ (x::xs) h :=
  begin
    dsimp, congr' 1, exact h x (psum.inl rfl), apply map_congr_pmem,
    intros x hx, apply h, right, exact hx
  end

@[simp] protected lemma map_congr_mem {f g : α → β} {n : ℕ} {xs : dvector α n}
  (h : ∀x, x ∈ xs → f x = g x) : xs.map f = xs.map g :=
dvector.map_congr_pmem $ λx hx, h x $ dvector.mem_of_pmem hx

@[simp] protected lemma map_congr {f g : α → β} (h : ∀x, f x = g x) :
  ∀{n : ℕ} (xs : dvector α n), xs.map f = xs.map g
| _ []      := rfl
| _ (x::xs) := by { dsimp, simp* }

@[simp] protected lemma map_map (g : β → γ) (f : α → β): ∀{n : ℕ} (xs : dvector α n),
  (xs.map f).map g = xs.map (λx, g (f x))
  | _ []      := rfl
  | _ (x::xs) := by { dsimp, simp* }

protected lemma map_inj {f : α → β} (hf : ∀{{x x'}}, f x = f x' → x = x') {n : ℕ}
  {xs xs' : dvector α n} (h : xs.map f = xs'.map f) : xs = xs' :=
begin
  induction xs; cases xs', refl, simp at h, congr;[apply hf, apply xs_ih]; simp [h]
end

@[simp] protected lemma map_concat (f : α → β) : ∀{n : ℕ} (xs : dvector α n) (x : α),
  (xs.concat x).map f = (xs.map f).concat (f x)
| _ []      x' := by refl
| _ (x::xs) x' := by { dsimp, congr' 1, exact map_concat xs x' }

@[simp] protected lemma map_nth (f : α → β) : ∀{n : ℕ} (xs : dvector α n) (m : ℕ) (h : m < n),
  (xs.map f).nth m h = f (xs.nth m h)
| _ []      m     h := by { exfalso, exact nat.not_lt_zero m h }
| _ (x::xs) 0     h := by refl
| _ (x::xs) (m+1) h := by exact map_nth xs m _

protected lemma concat_nth : ∀{n : ℕ} (xs : dvector α n) (x : α) (m : ℕ) (h' : m < n+1)
  (h : m < n), (xs.concat x).nth m h' = xs.nth m h
| _ []      x' m     h' h := by { exfalso, exact nat.not_lt_zero m h }
| _ (x::xs) x' 0     h' h := by refl
| _ (x::xs) x' (m+1) h' h := by { dsimp, exact concat_nth xs x' m _ _ }

@[simp] protected lemma concat_nth_last : ∀{n : ℕ} (xs : dvector α n) (x : α) (h : n < n+1),
  (xs.concat x).nth n h = x
| _ []      x' h := by refl
| _ (x::xs) x' h := by { dsimp, exact concat_nth_last xs x' _ }

@[simp] protected lemma concat_nth_last' : ∀{n : ℕ} (xs : dvector α n) (x : α) (h : n < n+1),
  (xs.concat x).last = x
:= by apply dvector.concat_nth_last

@[simp] protected def append : ∀{n m : ℕ} (xs : dvector α n) (xs' : dvector α m), dvector α (m+n)
| _ _ []       xs := xs
| _ _ (x'::xs) xs' := x'::append xs xs'

@[simp]protected def insert : ∀{n : ℕ} (x : α) (k : ℕ) (xs : dvector α n), dvector α (n+1)
| n x 0 xs := (x::xs)
| 0 x k xs := (x::xs)
| (n+1) x (k+1) (y::ys) := (y::insert x k ys)

@[simp] protected lemma insert_at_zero : ∀{n : ℕ} (x : α) (xs : dvector α n), dvector.insert x 0 xs = (x::xs) := by {intros, induction n; refl} -- why doesn't {intros, refl} work?

@[simp] protected lemma insert_nth : ∀{n : ℕ} (x : α) (k : ℕ) (xs : dvector α n) (h : k < n+1), (dvector.insert x k xs).nth k h = x
| 0 x k xs h := by {cases h, refl, exfalso, apply nat.not_lt_zero, exact h_a}
| n x 0 xs h := by {induction n, refl, simp*}
| (n+1) x (k+1) (y::ys) h := by simp*

protected lemma insert_cons {n k} {x y : α} {v : dvector α n} : (x::(v.insert y k)) = (x::v).insert y (k+1) :=
by {induction v, refl, simp*}

/- Given a proof that n ≤ m, return the nth initial segment of -/
@[simp]protected def trunc : ∀ (n) {m : ℕ} (h : n ≤ m) (xs : dvector α m), dvector α n
| 0 0 _ xs := []
| 0 (m+1) _ xs := []
| (n+1) 0 _ xs := by {exfalso, cases _x}
| (n+1) (m+1) h (x::xs) := (x::@trunc n m (by { simp at h, exact h }) xs)

@[simp]protected lemma trunc_n_n {n : ℕ} {h : n ≤ n} {v : dvector α n} : dvector.trunc n h v = v :=
  by {induction v, refl, solve_by_elim}

@[simp]protected lemma trunc_0_n {n : ℕ} {h : 0 ≤ n} {v : dvector α n} : dvector.trunc 0 h v = [] :=
  by {induction v, refl, simp}

@[simp]protected lemma trunc_nth {n m l: ℕ} {h : n ≤ m} {h' : l < n} {v : dvector α m} : (v.trunc n h).nth l h' = v.nth l (lt_of_lt_of_le h' h) :=
begin
  induction m generalizing n l, have : n = 0, by cases h; simp, subst this, cases h',
  cases n; cases l, {cases h'}, {cases h'}, {cases v, refl},
  cases v, simp only [m_ih, dvector.nth, dvector.trunc]
end

protected lemma nth_irrel1 : ∀{n k : ℕ} {h : k < n + 1} {h' : k < n + 1 + 1} (v : dvector α (n+1)) (x : α),
  (x :: (v.trunc n (nat.le_succ n))).nth k h = (x::v).nth k h' :=
by {intros, apply @dvector.trunc_nth _ _ _ _ (by simp) h (x::v)}

protected def cast {n m} (p : n = m) : dvector α n → dvector α m :=
by { subst p, exact id }

@[simp] protected lemma cast_irrel {n m} {p p' : n = m} {v : dvector α n} : v.cast p = v.cast p' := by refl

@[simp] protected lemma cast_rfl {n m} {p : n = m} {q : m = n} {v : dvector α n} : (v.cast p).cast q = v := by {subst p, refl}

protected lemma cast_hrfl {n m} {p : n = m} {v : dvector α n} : v.cast p == v :=
by { subst p, refl }

@[simp] protected lemma cast_trans {n m o} {p : n = m} {q : m = o} {v : dvector α n} : (v.cast p).cast q = v.cast (trans p q) :=
by { subst p, subst q, refl }

@[simp] lemma cast_cons {α} : ∀{n m} (h : n + 1 = m + 1) (x : α) (v : dvector α n),
  (x::v).cast h = x :: v.cast (nat.succ.inj h) :=
by { intros, cases h, refl }

@[simp] lemma cast_append_nil {α} : ∀{n} (v : dvector α n) (h : 0 + n = n),
  (v.append ([])).cast h = v
| _ ([])   h := by refl
| _ (x::v) h := by { simp only [true_and, dvector.append, cast_cons, eq_self_iff_true],
  exact cast_append_nil v (by simp only [zero_add]) }

@[simp] protected def remove_mth : ∀ {n : ℕ} (m : ℕ) (xs : dvector α (n+1)) , dvector α (n)
  | 0 _ _  := dvector.nil
  | n 0 (dvector.cons y ys) := ys
  | (n+1) (k+1) (dvector.cons y ys) := dvector.cons y (remove_mth k ys)

@[simp]protected def replace : ∀{n : ℕ} (x : α) (k : ℕ) (xs : dvector α n), dvector α (n)
| n x 0 (y::ys) := (x::ys)
| 0 x k ys := ys
| (n+1) x (k+1) (y::ys) := (y::replace x k ys)

protected lemma insert_nth_lt {α} : ∀{n k l : ℕ} (x : α) (xs : dvector α n) (h : l < n)
  (h' : l < n + 1) (h2 : l < k), (xs.insert x k).nth l h' = xs.nth l h
| n     0     l     x xs h h' h2 := by cases h2
| 0     (k+1) l     x xs h h' h2 := by cases h
| (n+1) (k+1) 0     x (x'::xs) h h' h2 := by refl
| (n+1) (k+1) (l+1) x (x'::xs) h h' h2 :=
  by { simp, apply insert_nth_lt, apply nat.lt_of_succ_lt_succ h2 }

protected lemma insert_nth_gt' {α} : ∀{n k l : ℕ} (x : α) (xs : dvector α n) (h : l - 1 < n)
  (h' : l < n + 1) (h2 : k < l), (xs.insert x k).nth l h' = xs.nth (l-1) h
| n     0     0     x xs h h' h2 := by cases h2
| n     0     (l+1) x xs h h' h2 := by { simp }
| 0     (k+1) 0     x xs h h' h2 := by { cases h }
| 0     (k+1) (l+1) x xs h h' h2 := by { cases h' with _ h', cases h' }
| (n+1) (k+1) 0     x (x'::xs) h h' h2 := by cases h2
| (n+1) (k+1) 1     x (x'::xs) h h' h2 := by { cases h2 with _ h2, cases h2 }
| (n+1) (k+1) (l+2) x (x'::xs) h h' h2 :=
  by { simp, convert insert_nth_gt' x xs _ _ _, apply nat.lt_of_succ_lt_succ h2 }

@[simp] protected lemma insert_nth_gt_simp {α} : ∀{n k l : ℕ} (x : α) (xs : dvector α n)
  (h' : l < n + 1)
  (h2 : k < l), (xs.insert x k).nth l h' =
  xs.nth (l-1) ((nat.sub_lt_right_iff_lt_add (nat.one_le_of_lt h2)).mpr h') :=
λ n k l x xs h' h2, dvector.insert_nth_gt' x xs _ h' h2

protected lemma insert_nth_gt {α} : ∀{n k l : ℕ} (x : α) (xs : dvector α n) (h : l < n) (h' : l + 1 < n + 1)
  (h2 : k < l + 1), (xs.insert x k).nth (l+1) h' = xs.nth l h :=
λ n k l x xs h h' h2, dvector.insert_nth_gt' x xs h h' h2

@[simp]lemma replace_head {n x z} {xs : dvector α n} : (x::xs).replace z 0 = z::xs := rfl

@[simp]lemma replace_neck {n x y z} {xs : dvector α n} : (x::y::xs).replace z 1 = x::z::xs := rfl

@[simp] def foldr (f : α → β → β) (b : β) : ∀{n}, dvector α n → β
| _ []       := b
| _ (a :: l) := f a (foldr l)

@[simp] def zip : ∀{n}, dvector α n → dvector β n → dvector (α × β) n
| _ [] []               := []
| _ (x :: xs) (y :: ys) := ⟨x, y⟩ :: zip xs ys

/-- The finitary infimum -/
def fInf [semilattice_inf_top α] (xs : dvector α n) : α :=
xs.foldr (λ(x b : α), x ⊓ b) ⊤

@[simp] lemma fInf_nil [semilattice_inf_top α] : fInf [] = (⊤ : α) := by refl
@[simp] lemma fInf_cons [semilattice_inf_top α] (x : α) (xs : dvector α n) :
  fInf (x::xs) = x ⊓ fInf xs := by refl

/-- The finitary supremum -/
def fSup [semilattice_sup_bot α] (xs : dvector α n) : α :=
xs.foldr (λ(x b : α), x ⊔ b) ⊥

@[simp] lemma fSup_nil [semilattice_sup_bot α] : fSup [] = (⊥ : α) := by refl
@[simp] lemma fSup_cons [semilattice_sup_bot α] (x : α) (xs : dvector α n) :
  fSup (x::xs) = x ⊔ fSup xs := by refl

/- how to make this protected? -/
inductive rel [setoid α] : ∀{n}, dvector α n → dvector α n → Prop
| rnil : rel [] []
| rcons {n} {x x' : α} {xs xs' : dvector α n} (hx : x ≈ x') (hxs : rel xs xs') :
    rel (x::xs) (x'::xs')
open dvector.rel

protected lemma rel_refl [setoid α] : ∀{n} (xs : dvector α n), xs.rel xs
| _ []      := rnil
| _ (x::xs) := rcons (setoid.refl _) (rel_refl xs)

protected lemma rel_symm [setoid α] {n} {{xs xs' : dvector α n}} (h : xs.rel xs') : xs'.rel xs :=
by { induction h; constructor, exact setoid.symm h_hx, exact h_ih }

protected lemma rel_trans [setoid α] {n} {{xs₁ xs₂ xs₃ : dvector α n}}
  (h₁ : xs₁.rel xs₂) (h₂ : xs₂.rel xs₃) : xs₁.rel xs₃ :=
begin
  induction h₁ generalizing h₂, exact h₂,
  cases h₂, constructor, exact setoid.trans h₁_hx h₂_hx, exact h₁_ih h₂_hxs
end

-- protected def rel [setoid α] : ∀{n}, dvector α n → dvector α n → Prop
-- | _ []      []        := true
-- | _ (x::xs) (x'::xs') := x ≈ x' ∧ rel xs xs'

-- protected def rel_refl [setoid α] : ∀{n} (xs : dvector α n), xs.rel xs
-- | _ []      := trivial
-- | _ (x::xs) := ⟨by refl, rel_refl xs⟩

-- protected def rel_symm [setoid α] : ∀{n} {{xs xs' : dvector α n}}, xs.rel xs' → xs'.rel xs
-- | _ []      []        h := trivial
-- | _ (x::xs) (x'::xs') h := ⟨setoid.symm h.1, rel_symm h.2⟩

-- protected def rel_trans [setoid α] : ∀{n} {{xs₁ xs₂ xs₃ : dvector α n}},
--   xs₁.rel xs₂ → xs₂.rel xs₃ → xs₁.rel xs₃
-- | _ []        []        []        h₁ h₂ := trivial
-- | _ (x₁::xs₁) (x₂::xs₂) (x₃::xs₃) h₁ h₂ := ⟨setoid.trans h₁.1 h₂.1, rel_trans h₁.2 h₂.2⟩

instance setoid [setoid α] : setoid (dvector α n) :=
⟨dvector.rel, dvector.rel_refl, dvector.rel_symm, dvector.rel_trans⟩

def quotient_lift {α : Type u} {β : Sort v} {R : setoid α} : ∀{n} (f : dvector α n → β)
  (h : ∀{{xs xs'}}, xs ≈ xs' → f xs = f xs') (xs : dvector (quotient R) n), β
| _     f h []      := f ([])
| (n+1) f h (x::xs) :=
  begin
    refine quotient.lift
      (λx, quotient_lift (λ xs, f $ x::xs) (λxs xs' hxs, h (rcons (setoid.refl x) hxs)) xs) _ x,
    intros x x' hx, dsimp, congr, apply funext, intro xs, apply h, exact rcons hx xs.rel_refl
  end

lemma quotient_beta {α : Type u} {β : Sort v} {R : setoid α} {n} (f : dvector α n → β)
  (h : ∀{{xs xs'}}, xs ≈ xs' → f xs = f xs') (xs : dvector α n) :
  (xs.map quotient.mk).quotient_lift f h = f xs :=
begin
  induction xs, refl, apply xs_ih
end
end dvectors
end dvector

namespace set
lemma disjoint_iff_eq_empty {α} {s t : set α} : disjoint s t ↔ s ∩ t = ∅ := disjoint_iff

lemma neq_neg_of_nonempty {α : Type*} {P : set α} (H_nonempty : nonempty α) : P ≠ Pᶜ :=
begin
  intro H_eq, let a : α := classical.choice (by apply_instance),
  have := congr_fun H_eq a,
  classical, by_cases HP : P a,
    {from absurd HP (by rwa this at HP)},
    {from absurd (by rwa this) HP}
end

@[simp] lemma subset_bInter_iff {α β} {s : set α} {t : set β} {u : α → set β} :
  t ⊆ (⋂ x ∈ s, u x) ↔ ∀ x ∈ s, t ⊆ u x :=
⟨λ h x hx y hy, by { have := h hy, rw mem_bInter_iff at this, exact this x hx }, subset_bInter⟩

@[simp] lemma subset_sInter_iff {α} {s : set α} {C : set (set α)} :
  s ⊆ ⋂₀ C ↔ ∀ t ∈ C, s ⊆ t :=
by simp [sInter_eq_bInter]

lemma ne_empty_of_subset {α} {s t : set α} (h : s ⊆ t) (hs : s ≠ ∅) : t ≠ ∅ :=
mt (subset_eq_empty h) hs

end set

section topological_space
open filter topological_space set
variables {α : Type u} {β : Type v} {ι : Type w} {π : ι → Type w'} [∀x, topological_space (π x)]

variables [t : topological_space α] [topological_space β]

lemma subbasis_subset_basis {s : set (set α)} :
  s \ {∅} ⊆ ((λf, ⋂₀ f) '' {f:set (set α) | finite f ∧ f ⊆ s ∧ ⋂₀ f ≠ ∅}) :=
begin
  intros o ho, refine ⟨{o}, ⟨finite_singleton o, _, _⟩, _⟩,
  { rw [singleton_subset_iff], exact ho.1 },
  { rw [sInter_singleton], refine mt mem_singleton_iff.mpr ho.2 },
  dsimp only, rw [sInter_singleton]
end

include t

lemma mem_opens {x : α} {o : opens α} : x ∈ o ↔ x ∈ o.1 := by refl

lemma is_open_map_of_is_topological_basis {s : set (set α)}
  (hs : is_topological_basis s) (f : α → β) (hf : ∀x ∈ s, is_open (f '' x)) :
  is_open_map f :=
begin
  intros o ho,
  rcases Union_basis_of_is_open hs ho with ⟨γ, g, rfl, hg⟩,
  rw [image_Union], apply is_open_Union, intro i, apply hf, apply hg
end

lemma interior_bInter_subset {β} {s : set β} (f : β → set α) :
  interior (⋂i ∈ s, f i) ⊆ ⋂i ∈ s, interior (f i) :=
begin
  intros x hx, rw [mem_interior] at hx, rcases hx with ⟨t, h1t, h2t, h3t⟩,
  rw [subset_bInter_iff] at h1t,
  rw [mem_bInter_iff], intros y hy, rw [mem_interior],
  refine ⟨t, h1t y hy, h2t, h3t⟩
end

lemma nonempty_basis_subset {b : set (set α)}
  (hb : is_topological_basis b) {u : set α} (hu : u ≠ ∅) (ou : _root_.is_open u) :
  ∃v ∈ b, v ≠ ∅ ∧ v ⊆ u :=
begin
  simp only [set.ne_empty_iff_nonempty] at hu ⊢, cases hu with x hx,
  rcases mem_basis_subset_of_mem_open hb hx ou with ⟨o, h1o, h2x, h2o⟩,
  exact ⟨o, h1o, ⟨x, h2x⟩, h2o⟩
end

end topological_space

namespace ordinal
variable {σ : Type*}

theorem well_ordering_thm : ∃ (r : σ → σ → Prop), is_well_order σ r :=
⟨_, (rel_embedding.preimage embedding_to_cardinal (<)).is_well_order⟩

theorem enum_typein' {α : Type u} (r : α → α → Prop) [is_well_order α r] (a : α) :
  enum r (typein r a) (typein_lt_type r a) = a :=
enum_typein r a

end ordinal

namespace cardinal

section cardinal_lemmas

local prefix `#`:65 := cardinal.mk

lemma exists_mem_compl_of_mk_lt_mk {α} (P : set α) (H_lt : cardinal.mk P  < cardinal.mk α) : ∃ x : α, x ∈ Pᶜ :=
begin
  classical, by_contra, push_neg at a,
  replace a := (by finish : ∀ x, x ∈ P),
  suffices : mk α ≤ mk P ,
    by {exact absurd H_lt (not_lt.mpr ‹_›)},
  refine mk_le_of_injective _, from λ _, ⟨‹_›, a ‹_›⟩, tidy
end

@[simp]lemma mk_union_countable_of_countable {α} {P Q : set α} (HP : #P ≤ omega) (HQ : #Q ≤ omega) :
  #(P ∪ Q : set α) ≤ omega :=
begin
  have this₁ := @mk_union_add_mk_inter _ (P) (Q),
  transitivity (#↥(P ∪ Q)) + #↥(P ∩ Q),
    { apply cardinal.le_add_right },
    { rw[this₁], rw[<-(add_eq_self (by refl : cardinal.omega ≤ cardinal.omega))],
      refine cardinal.add_le_add _ _; from ‹_› }
end

lemma nonzero_of_regular {κ : cardinal} (H_reg : cardinal.is_regular κ) : 0 < κ.ord :=
by {rw cardinal.lt_ord, from lt_of_lt_of_le omega_pos H_reg.left}

lemma injection_of_mk_le {α β : Type u} (H_le : #α ≤ #β) : ∃ f : α → β, function.injective f :=
begin
  rw cardinal.out_embedding at H_le,
  have := classical.choice H_le,
  cases this with f Hf,
  suffices : ∃ g₁ : α → quotient.out (#α), function.injective g₁ ∧ ∃ g₂ : quotient.out (#β) → β, function.injective g₂,
    by {rcases this with ⟨g₁,Hg₁,g₂,Hg₂⟩, use g₂ ∘ f ∘ g₁, simp [function.injective.comp, *] },
  have this₁ : #(quotient.out (#α)) = #α := mk_out _, have this₂ : #(quotient.out _) = #β := mk_out _,
  erw quotient.eq' at this₁ this₂, replace this₁ := classical.choice this₁, replace this₂ := classical.choice this₂,
  cases this₁, cases this₂,
  refine ⟨this₁_inv_fun, _, this₂_to_fun, _⟩; apply function.left_inverse.injective; from ‹_›
end

end cardinal_lemmas

end cardinal

------------------------------------------------------- maybe not move to mathlib ------------------

/- theorems which we should not backport to mathlib, because they are duplicates or which need to
  be cleaned up first -/

namespace nat
protected lemma pred_lt_iff_lt_succ {m n : ℕ} (H : 1 ≤ m) : pred m < n ↔ m < succ n :=
nat.sub_lt_right_iff_lt_add H

lemma le_of_le_and_ne_succ {x y : ℕ} (H : x ≤ y + 1) (H' : x ≠ y + 1) : x ≤ y :=
by simp only [*, nat.lt_of_le_and_ne, nat.le_of_lt_succ, ne.def, not_false_iff]

end nat

namespace tactic
namespace interactive
/- maybe we should use congr' 1 instead? -/
meta def congr1 : tactic unit :=
do focus1 (congr_core >> all_goals (try reflexivity >> try assumption))

open interactive interactive.types

/-- a variant of `exact` which elaborates its argument before unifying it with the target. This variant might succeed if `exact` fails because a lot of definitional reduction is needed to verify that the term has the correct type. Metavariables which are not synthesized become new subgoals. This is similar to have := q, exact this. Another approach to obtain (rougly) the same is `apply q` -/
meta def rexact (q : parse texpr) : tactic unit :=
do n ← mk_fresh_name,
p ← i_to_expr q,
e ← note n none p,
tactic.exact e

end interactive
end tactic

/- logic -/
namespace classical

noncomputable def psigma_of_exists {α : Type u} {p : α → Prop} (h : ∃x, p x) : Σ' x, p x :=
begin
  haveI : nonempty α := nonempty_of_exists h,
  exact ⟨epsilon p, epsilon_spec h⟩
end

/- this is a special case of `some_spec2` -/
lemma some_eq {α : Type u} {p : α → Prop} {h : ∃ (a : α), p a} (x : α)
  (hx : ∀y, p y → y = x) : classical.some h = x :=
classical.some_spec2 _ hx

lemma or_not_iff_true (p : Prop) : (p ∨ ¬ p) ↔ true :=
⟨λ_, trivial, λ_, or_not⟩

lemma nonempty_of_not_empty {α : Type u} (s : set α) (h : ¬ s = ∅) : s.nonempty :=
set.ne_empty_iff_nonempty.1 h

end classical

namespace list
@[simp] protected def to_set {α : Type u} (l : list α) : set α := { x | x ∈ l }

lemma to_set_map {α : Type u} {β : Type v} (f : α → β) (l : list α) :
  (l.map f).to_set = f '' l.to_set :=
by apply set.ext; intro b; simp [list.to_set]

lemma exists_of_to_set_subset_image {α : Type u} {β : Type v} {f : α → β} {l : list β}
  {t : set α} (h : l.to_set ⊆ f '' t) : ∃(l' : list α), l'.to_set ⊆ t ∧ map f l' = l :=
begin
  induction l,
  { exact ⟨[], set.empty_subset t, rfl⟩ },
  { rcases h (mem_cons_self _ _) with ⟨x, hx, rfl⟩,
    rcases l_ih (λx hx, h $ mem_cons_of_mem _ hx) with ⟨xs, hxs, hxs'⟩,
    exact ⟨x::xs, set.union_subset (λy hy, by induction hy; exact hx) hxs, by simp*⟩ }
end

end list

namespace nat
/- nat.sub_add_comm -/
lemma add_sub_swap {n k : ℕ} (h : k ≤ n) (m : ℕ) : n + m - k = n - k + m :=
by rw [add_comm, nat.add_sub_assoc h, add_comm]

end nat

lemma imp_eq_congr {a b c d : Prop} (h₁ : a = b) (h₂ : c = d) : (a → c) = (b → d) :=
by subst h₁; subst h₂; refl

lemma forall_eq_congr {α : Sort u} {p q : α → Prop} (h : ∀ a, p a = q a) :
  (∀ a, p a) = ∀ a, q a :=
have h' : p = q, from funext h, by subst h'; refl

namespace set
/- Some of these lemmas might be duplicates of those in data.set.lattice -/

variables {α : Type u} {β : Type v} {γ : Type w}

lemma inter_sUnion_ne_empty_of_exists_mem {b : set α} {𝓕 : set $ set α} (H : ∃ f ∈ 𝓕, b ∩ f ≠ ∅) : b ∩ ⋃₀ 𝓕 ≠ ∅ :=
begin
  simp [not_eq_empty_iff_exists] at H ⊢,
  rcases H with ⟨f, hf, x, h1, h2⟩, exact ⟨x, h1, f, hf, h2⟩,
end

@[simp]lemma mem_image_univ {f : α → β} {x} : f x ∈ f '' set.univ := ⟨x, ⟨trivial, rfl⟩⟩

-- todo: only use image_preimage_eq_of_subset
lemma image_preimage_eq_of_subset_image {f : α → β} {s : set β}
  {t : set α} (h : s ⊆ f '' t) : f '' (f ⁻¹' s) = s :=
subset.antisymm
  (image_preimage_subset f s)
  (λ x hx, begin rcases h hx with ⟨a, ha, rfl⟩, apply mem_image_of_mem f, exact hx end)

lemma subset_union_left_of_subset {s t : set α} (h : s ⊆ t) (u : set α) : s ⊆ t ∪ u :=
subset.trans h (subset_union_left t u)

lemma subset_union_right_of_subset {s u : set α} (h : s ⊆ u) (t : set α) : s ⊆ t ∪ u :=
subset.trans h (subset_union_right t u)

/- subset_sUnion_of_mem -/
lemma subset_sUnion {s : set α} {t : set (set α)} (h : s ∈ t) : s ⊆ ⋃₀ t :=
λx hx, ⟨s, ⟨h, hx⟩⟩

lemma subset_union2_left {s t u : set α} : s ⊆ s ∪ t ∪ u :=
subset.trans (subset_union_left _ _) (subset_union_left _ _)

lemma subset_union2_middle {s t u : set α} : t ⊆ s ∪ t ∪ u :=
subset.trans (subset_union_right _ _) (subset_union_left _ _)


def change {π : α → Type*} [decidable_eq α] (f : Πa, π a) {x : α} (z : π x) (y : α) : π y :=
if h : x = y then (@eq.rec _ _ π z _ h) else f y

lemma dif_mem_pi {π : α → Type*} (i : set α) (s : Πa, set (π a)) [decidable_eq α]
  (f : Πa, π a) (hf : f ∈ pi i s) {x : α} (z : π x) (h : x ∈ i → z ∈ s x) :
  change f z ∈ pi i s :=
begin
  intros y hy, dsimp only,
  by_cases hxy : x = y,
  { rw [change, dif_pos hxy], subst hxy, exact h hy },
  { rw [change, dif_neg hxy], apply hf y hy }
end

lemma image_pi_pos {π : α → Type*} (i : set α) (s : Πa, set (π a)) [decidable_eq α]
  (hp : nonempty (pi i s)) (x : α) (hx : x ∈ i) : (λ(f : Πa, π a), f x) '' pi i s = s x :=
begin
  apply subset.antisymm,
  { rintro _ ⟨f, hf, rfl⟩, exact hf x hx },
  intros z hz, have := hp, rcases this with ⟨f, hf⟩,
  refine ⟨_, dif_mem_pi i s f hf z (λ _, hz), _⟩,
  simp only [change, dif_pos rfl]
end

lemma image_pi_neg {π : α → Type*} (i : set α) (s : Πa, set (π a)) [decidable_eq α]
  (hp : nonempty (pi i s)) (x : α) (hx : x ∉ i) : (λ(f : Πa, π a), f x) '' pi i s = univ :=
begin
  rw [eq_univ_iff_forall], intro z, have := hp, rcases this with ⟨f, hf⟩,
  refine ⟨_, dif_mem_pi i s f hf z _, _⟩,
  intro hx', exfalso, exact hx hx',
  simp only [change, dif_pos rfl]
end

end set
open nat


namespace nonempty
variables {α : Sort u} {β : Sort v} {γ : Sort w}

protected lemma iff (mp : α → β) (mpr : β → α) : nonempty α ↔ nonempty β :=
⟨nonempty.map mp, nonempty.map mpr⟩

end nonempty

/-- The type α → (α → ... (α → β)...) with n α's. We require that α and β live in the same universe, otherwise we have to use ulift. -/
def arity' (α β : Type u) : ℕ → Type u
| 0     := β
| (n+1) := α → arity' n

namespace arity'
section arity'
local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l
def arity'_constant {α β : Type u} : ∀{n : ℕ}, β → arity' α β n
| 0     b := b
| (n+1) b := λ_, arity'_constant b

@[simp] def of_dvector_map {α β : Type u} : ∀{l} (f : dvector α l → β), arity' α β l
| 0     f := f ([])
| (l+1) f := λx, of_dvector_map $ λxs, f $ x::xs

@[simp] def arity'_app {α β : Type u} : ∀{l}, arity' α β l → dvector α l → β
| _ b []      := b
| _ f (x::xs) := arity'_app (f x) xs

@[simp] lemma arity'_app_zero {α β : Type u} (f : arity' α β 0) (xs : dvector α 0) :
  arity'_app f xs = f :=
by cases xs; refl

def arity'_postcompose {α β γ : Type u} (g : β → γ) : ∀{n} (f : arity' α β n), arity' α γ n
| 0     b := g b
| (n+1) f := λx, arity'_postcompose (f x)

def arity'_postcompose2 {α β γ δ : Type u} (h : β → γ → δ) :
  ∀{n} (f : arity' α β n) (g : arity' α γ n), arity' α δ n
| 0     b c := h b c
| (n+1) f g := λx, arity'_postcompose2 (f x) (g x)

def arity'_precompose {α β γ : Type u} : ∀{n} (g : arity' β γ n) (f : α → β), arity' α γ n
| 0     c f := c
| (n+1) g f := λx, arity'_precompose (g (f x)) f

inductive arity'_respect_setoid {α β : Type u} [R : setoid α] : ∀{n}, arity' α β n → Type u
| r_zero (b : β) : @arity'_respect_setoid 0 b
| r_succ (n : ℕ) (f : arity' α β (n+1)) (h₁ : ∀{{a a'}}, a ≈ a' → f a = f a')
  (h₂ : ∀a, arity'_respect_setoid (f a)) : arity'_respect_setoid f
open arity'_respect_setoid

instance subsingleton_arity'_respect_setoid {α β : Type u} [R : setoid α] {n} (f : arity' α β n) :
  subsingleton (arity'_respect_setoid f) :=
begin
  constructor, intros h h', induction h generalizing h'; cases h'; try {refl}; congr,
  apply funext, intro x, apply h_ih
end

-- def arity'_quotient_lift {α β : Type u} {R : setoid α} :
--   ∀{n}, (Σ(f : arity' α β n), arity'_respect_setoid f) → arity' (quotient R) β n
-- | _ ⟨_, r_zero b⟩         := b
-- | _ ⟨_, r_succ n f h₁ h₂⟩ :=
--   begin
--     apply quotient.lift (λx, arity'_quotient_lift ⟨f x, h₂ x⟩),
--     intros x x' r, dsimp,
--     apply congr_arg, exact sigma.eq (h₁ r) (subsingleton.elim _ _)
--   end

-- def arity'_quotient_beta {α β : Type u} {R : setoid α} {n} (f : arity' α β n)
--   (hf : arity'_respect_setoid f) (xs : dvector α n) :
--   arity'_app (arity'_quotient_lift ⟨f, hf⟩) (xs.map quotient.mk) = arity'_app f xs :=
-- begin
--   induction hf,
--   { simp [arity'_quotient_lift] },
--   dsimp [arity'_app], sorry
-- end

def for_all {α : Type u} (P : α → Prop) : Prop := ∀x, P x

@[simp] def arity'_map2 {α β : Type u} (q : (α → β) → β) (f : β → β → β) :
  ∀{n}, arity' α β n → arity' α β n → β
| 0     x y := f x y
| (n+1) x y := q (λz, arity'_map2 (x z) (y z))

@[simp] lemma arity'_map2_refl {α : Type} {f : Prop → Prop → Prop} (r : ∀A, f A A) :
  ∀{n} (x : arity' α Prop n), arity'_map2 for_all f x x
| 0     x := r x
| (n+1) x := λy, arity'_map2_refl (x y)

def arity'_imp {α : Type} {n : ℕ} (f₁ f₂ : arity' α Prop n) : Prop :=
arity'_map2 for_all (λP Q, P → Q) f₁ f₂

def arity'_iff {α : Type} {n : ℕ} (f₁ f₂ : arity' α Prop n) : Prop :=
arity'_map2 for_all iff f₁ f₂

lemma arity'_iff_refl {α : Type} {n : ℕ} (f : arity' α Prop n) : arity'_iff f f :=
arity'_map2_refl iff.refl f

lemma arity'_iff_rfl {α : Type} {n : ℕ} {f : arity' α Prop n} : arity'_iff f f :=
arity'_iff_refl f

end arity'
end arity'

@[simp]lemma lt_irrefl' {α} [preorder α] {Γ : α} (H_lt : Γ < Γ) : false := lt_irrefl _ ‹_›

namespace lattice



instance complete_degenerate_boolean_algebra : complete_boolean_algebra unit :=
by refine_struct {le := λ _ _, true, lt := λ _ _, false, ..};
   try { intros, exact () <|> trivial }; simp

class nontrivial_complete_boolean_algebra (α : Type*) extends complete_boolean_algebra α :=
  {bot_lt_top : (⊥ : α) < (⊤ : α)}

@[simp]lemma nontrivial.bot_lt_top {α : Type*} [H : nontrivial_complete_boolean_algebra α] : (⊥ : α) < ⊤ :=
H.bot_lt_top

@[simp]lemma nontrivial.bot_neq_top {α : Type*} [H : nontrivial_complete_boolean_algebra α] : ¬ (⊥ = (⊤ : α)) :=
by {change _ ≠ _, rw[lt_top_iff_ne_top.symm], simp}

@[simp]lemma nontrivial.top_neq_bot {α : Type*} [H : nontrivial_complete_boolean_algebra α] : ¬ (⊤ = (⊥ : α)) :=
λ _, nontrivial.bot_neq_top $ eq.symm ‹_›

def antichain {β : Type*} [bounded_lattice β] (s : set β) :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → x ⊓ y = (⊥ : β)

theorem inf_supr_eq {α ι : Type*} [complete_distrib_lattice α] {a : α} {s : ι → α} :
  a ⊓ (⨆(i:ι), s i) = ⨆(i:ι), a ⊓ s i :=
  eq.trans inf_Sup_eq $
    begin
      rw[<-inf_Sup_eq], suffices : (⨆(i:ι), a ⊓ s i) = ⨆(b∈(set.range s)), a ⊓ b,
      by {rw[this], apply inf_Sup_eq}, simp, apply le_antisymm,
      apply supr_le, intro i, apply le_supr_of_le (s i), apply le_supr_of_le i,
      apply le_supr_of_le rfl, refl,
      repeat{apply supr_le, intro}, rw[<-i_2], apply le_supr_of_le i_1, refl
    end

theorem supr_inf_eq {α ι : Type*} [complete_distrib_lattice α] {a : α} {s : ι → α} :
  (⨆(i:ι), s i) ⊓ a = ⨆(i:ι), (s i ⊓ a) :=
by simp[inf_comm,inf_supr_eq]

theorem sup_infi_eq {α ι : Type*} [complete_distrib_lattice α] {a : α} {s : ι → α} :
  a ⊔ (⨅(i:ι), s i) = ⨅(i:ι), a ⊔ s i :=
  eq.trans sup_Inf_eq $
    begin
      rw[<-sup_Inf_eq], suffices : (⨅(i:ι), a ⊔ s i) = ⨅(b∈(set.range s)), a ⊔ b,
      by {rw[this], apply sup_Inf_eq}, simp, apply le_antisymm,
      repeat{apply le_infi, intro}, rw[<-i_2], apply infi_le_of_le i_1, refl,
      repeat{apply infi_le_of_le}, show ι, from ‹ι›, show α, exact s i, refl, refl
    end

theorem infi_sup_eq {α ι : Type*} [complete_distrib_lattice α] {a : α} {s : ι → α} :
 (⨅(i:ι), s i) ⊔ a = ⨅(i:ι), s i ⊔ a :=
by {rw[sup_comm], conv{to_rhs, simp[sup_comm]}, apply sup_infi_eq}

/- These next two lemmas are duplicates, but with better names -/
@[simp]lemma inf_self {α : Type*} [lattice α] {a : α} : a ⊓ a = a :=
  inf_idem

@[simp]lemma sup_self {α : Type*} [lattice α] {a : α} : a ⊔ a = a :=
  sup_idem

lemma bot_lt_iff_not_le_bot {α} [bounded_lattice α] {a : α} : ⊥ < a ↔ (¬ a ≤ ⊥) :=
by rw[le_bot_iff]; exact bot_lt_iff_ne_bot

lemma false_of_bot_lt_and_le_bot {α} [bounded_lattice α] {a : α} (H_lt : ⊥ < a) (H_le : a ≤ ⊥) : false :=
absurd H_le (bot_lt_iff_not_le_bot.mp ‹_›)

lemma lt_top_iff_not_top_le {α} [bounded_lattice α] {a : α} : a < ⊤ ↔ (¬ ⊤ ≤ a) :=
by rw[top_le_iff]; exact lt_top_iff_ne_top

lemma bot_lt_resolve_left {𝔹} [bounded_lattice 𝔹] {a b : 𝔹} (H_lt' : ⊥ < a ⊓ b) : ⊥ < b :=
begin
  haveI := classical.prop_decidable, by_contra H, rw[bot_lt_iff_not_le_bot] at H H_lt',
  apply H_lt', simp at H, simp*
end

lemma bot_lt_resolve_right {𝔹} [bounded_lattice 𝔹] {a b : 𝔹} (H_lt : ⊥ < b)
  (H_lt' : ⊥ < a ⊓ b) : ⊥ < a :=
by rw[inf_comm] at H_lt'; exact bot_lt_resolve_left ‹_›

lemma le_bot_iff_not_bot_lt {𝔹} [bounded_lattice 𝔹] {a : 𝔹} : ¬ ⊥ < a ↔ a ≤ ⊥ :=
by { rw bot_lt_iff_not_le_bot, tauto! }

/--
  Given an indexed supremum (⨆i, s i) and (H : Γ ≤ ⨆i, s i), there exists some i such that ⊥ < Γ ⊓ s i.
-/
lemma nonzero_inf_of_nonzero_le_supr {α : Type*} [complete_distrib_lattice α] {ι : Type*} {s : ι → α} {Γ : α} (H_nonzero : ⊥ < Γ) (H : Γ ≤ ⨆i, s i) : ∃ i, ⊥ < Γ ⊓ s i :=
begin
  haveI := classical.prop_decidable, by_contra H', push_neg at H',
  simp [bot_lt_iff_not_le_bot, -le_bot_iff] at H', replace H' := supr_le_iff.mpr H',
  have H_absorb : Γ ⊓ (⨆(i : ι), s i) = Γ,
    by {exact _root_.le_antisymm (_root_.inf_le_left) (_root_.le_inf (by refl) ‹_›)},
  suffices this : (Γ ⊓ ⨆ (i : ι), s i) ≤ ⊥,
    by {rw[H_absorb, le_bot_iff] at this, simpa[this] using H_nonzero},
  rwa[inf_supr_eq]
end

/--
  Material implication in a Boolean algebra
-/
def imp {α : Type*} [boolean_algebra α] : α → α → α :=
  λ a₁ a₂, a₁ᶜ ⊔ a₂

local infix ` ⟹ `:65 := lattice.imp

@[reducible, simp]def biimp {α : Type*} [boolean_algebra α] : α → α → α :=
  λ a₁ a₂, (a₁ ⟹ a₂) ⊓ (a₂ ⟹ a₁)

local infix ` ⇔ `:50 := lattice.biimp

lemma biimp_mp {α : Type*} [boolean_algebra α] {a₁ a₂ : α} : (a₁ ⇔ a₂) ≤ (a₁ ⟹ a₂) :=
  by apply inf_le_left

lemma biimp_mpr {α : Type*} [boolean_algebra α] {a₁ a₂ : α} : (a₁ ⇔ a₂) ≤ (a₂ ⟹ a₁) :=
  by apply inf_le_right

lemma biimp_comm {α : Type*} [boolean_algebra α] {a₁ a₂ : α} : (a₁ ⇔ a₂) = (a₂ ⇔ a₁) :=
by {unfold biimp, rw inf_comm}

lemma biimp_symm {α : Type*} [boolean_algebra α] {a₁ a₂ : α} {Γ : α} : Γ ≤ (a₁ ⇔ a₂) ↔ Γ ≤ (a₂ ⇔ a₁) :=
by rw biimp_comm

@[simp]lemma imp_le_of_right_le {α : Type*} [boolean_algebra α] {a a₁ a₂ : α} {h : a₁ ≤ a₂} : a ⟹ a₁ ≤ (a ⟹ a₂) :=
_root_.sup_le (by apply le_sup_left) $ le_sup_right_of_le h

@[simp]lemma imp_le_of_left_le {α : Type*} [boolean_algebra α] {a a₁ a₂ : α} {h : a₂ ≤ a₁} : a₁ ⟹ a ≤ (a₂ ⟹ a) :=
_root_.sup_le (le_sup_left_of_le $ compl_le_compl h) (by apply le_sup_right)

@[simp]lemma imp_le_of_left_right_le {α : Type*} [boolean_algebra α] {a₁ a₂ b₁ b₂ : α}
{h₁ : b₁ ≤ a₁} {h₂ : a₂ ≤ b₂} :
  a₁ ⟹ a₂ ≤ b₁ ⟹ b₂ :=
_root_.sup_le (le_sup_left_of_le (compl_le_compl h₁)) (le_sup_right_of_le h₂)

lemma neg_le_neg' {α : Type*} [boolean_algebra α] {a b : α} : b ≤ aᶜ → a ≤ bᶜ :=
by {intro H, rw[show b = bᶜᶜ, by simp] at H, rwa [<-compl_le_compl_iff_le] }

lemma inf_imp_eq {α : Type*} [boolean_algebra α] {a b c : α} :
  a ⊓ (b ⟹ c) = (a ⟹ b) ⟹ (a ⊓ c) :=
by unfold imp; simp[inf_sup_left]

@[simp]lemma imp_bot {α : Type*} [boolean_algebra α]  {a : α} : a ⟹ ⊥ = aᶜ := by simp[imp]

@[simp]lemma top_imp {α : Type*} [boolean_algebra α] {a : α} : ⊤ ⟹ a = a := by simp[imp]

@[simp]lemma imp_self {α : Type*} [boolean_algebra α] {a : α} : a ⟹ a = ⊤ := by simp[imp]

lemma imp_compl_sdiff {α : Type*} [boolean_algebra α] {a₁ a₂ : α} :  (a₁ ⟹ a₂)ᶜ = a₁ \ a₂ :=
by rw [sdiff_eq, imp]; simp *

lemma inf_eq_of_le {α : Type*} [distrib_lattice α] {a b : α} (h : a ≤ b) : a ⊓ b = a :=
by apply le_antisymm; simp [*, le_inf]

lemma imp_inf_le {α : Type*} [boolean_algebra α] (a b : α) : (a ⟹ b) ⊓ a ≤ b :=
by { unfold imp, rw [inf_sup_right], simp }

lemma le_of_sub_eq_bot {α : Type*} [boolean_algebra α] {a b : α} (h : bᶜ ⊓ a = ⊥) : a ≤ b :=
begin
  apply le_of_inf_eq, rw [← @compl_compl' _ b, ← sdiff_eq],
  apply sdiff_eq_left, rwa [inf_comm]
end

lemma le_neg_of_inf_eq_bot {α : Type*} [boolean_algebra α] {a b : α} (h : b ⊓ a = ⊥) : a ≤ bᶜ :=
by { apply le_of_sub_eq_bot, rwa [compl_compl'] }

lemma sub_eq_bot_of_le {α : Type*} [boolean_algebra α] {a b : α} (h : a ≤ b) : bᶜ ⊓ a = ⊥ :=
by rw [←inf_eq_of_le h, inf_comm, inf_assoc, inf_compl_eq_bot, inf_bot_eq]

lemma inf_eq_bot_of_le_neg {α : Type*} [boolean_algebra α] {a b : α} (h : a ≤ bᶜ) : b ⊓ a = ⊥ :=
by { rw [←@compl_compl' _ b], exact sub_eq_bot_of_le h }

/-- the deduction theorem in β -/
@[simp]lemma imp_top_iff_le {α : Type*} [boolean_algebra α] {a₁ a₂ : α} : (a₁ ⟹ a₂ = ⊤) ↔ a₁ ≤ a₂ :=
begin
  unfold imp, refine ⟨_,_⟩; intro H,
    { have := congr_arg (λ x, x ⊓ a₁) H, rw[sup_comm] at this,
      finish[inf_sup_right] },
    { have := sup_le_sup_right H (a₁ᶜ), finish }
end
/- ∀ {α : Type u_1} [_inst_1 : boolean_algebra α] {a₁ a₂ : α}, a₁ ⟹ a₂ = ⊤ ↔ a₁ ≤ a₂ -/

lemma curry_uncurry {α : Type*} [boolean_algebra α] {a b c : α} : ((a ⊓ b) ⟹ c) = (a ⟹ (b ⟹ c)) :=
  by simp[imp]; ac_refl

/-- the actual deduction theorem in β, thinking of ≤ as a turnstile -/
@[ematch]lemma deduction {α : Type*} [boolean_algebra α] {a b c : α} : a ⊓ b ≤ c ↔ a ≤ (b ⟹ c) :=
  by {[smt] eblast_using [curry_uncurry, imp_top_iff_le]}

lemma deduction_simp {α : Type*} [boolean_algebra α] {a b c : α} : a ≤ (b ⟹ c) ↔ a ⊓ b ≤ c := deduction.symm

lemma imp_top {α : Type*} [complete_boolean_algebra α] (a : α) : a ≤ a ⟹ ⊤ :=
by {rw[<-deduction]; simp}

/-- Given an η : option α → β, where β is a complete lattice, we have that the supremum of η
    is equal to (η none) ⊔ ⨆(a:α) η (some a)-/
@[simp]lemma supr_option {α β : Type*} [complete_lattice β] {η : option α → β} : (⨆(x : option α), η x) = (η none) ⊔ ⨆(a : α), η (some a) :=
begin
  apply le_antisymm, tidy, cases i, apply le_sup_left,
  apply le_sup_right_of_le, apply le_supr (λ x, η (some x)) i, apply le_supr, apply le_supr
end

/-- Given an η : option α → β, where β is a complete lattice, we have that the infimum of η
    is equal to (η none) ⊓ ⨅(a:α) η (some a)-/
@[simp] lemma infi_option {α β : Type*} [complete_lattice β] {η : option α → β} : (⨅(x : option α), η x) = (η none) ⊓ ⨅(a : α), η (some a) :=
begin
  apply le_antisymm, tidy, tactic.rotate 2, cases i, apply inf_le_left,
  apply inf_le_right_of_le, apply infi_le (λ x, η (some x)) i, apply infi_le, apply infi_le
end

lemma supr_option' {α β : Type*} [complete_lattice β] {η : α → β} {b : β} : (⨆(x : option α), (option.rec b η x : β) : β) = b ⊔ ⨆(a : α), η a :=
  by rw[supr_option]

lemma infi_option' {α β : Type*} [complete_lattice β] {η : α → β} {b : β} : (⨅(x : option α), (option.rec b η x : β) : β) = b ⊓ ⨅(a : α), η a :=
  by rw[infi_option]

/-- Let A : α → β such that b = ⨆(a : α) A a. Let c < b. If, for all a : α, A a ≠ b → A a ≤ c,
then there exists some x : α such that A x = b. -/
lemma supr_max_of_bounded {α β : Type*} [complete_lattice β] {A : α → β} {b c : β}
{h : b = ⨆(a:α), A a} {h_lt : c < b} {h_bounded : ∀ a : α, A a ≠ b → A a ≤ c} :
  ∃ x : α, A x = b :=
begin
  haveI : decidable ∃ (x : α), A x = b := classical.prop_decidable _,
  by_contra, rw[h] at a, simp at a,
  suffices : b ≤ c, by {suffices : c < c, by {exfalso, have this' := lt_irrefl,
  show Type*, exact β, show preorder (id β), by {dsimp, apply_instance}, exact this' c this},
  exact lt_of_lt_of_le h_lt this},
  rw[h], apply supr_le, intro a', from h_bounded a' (by convert a a')
end

/-- Let A : α → β such that b ≤ ⨆(a : α) A a. Let c < b. If, for all a : α, A a ≠ b → A a ≤ c,
then there exists some x : α such that b ≤ A x. -/
lemma supr_max_of_bounded' {α β : Type*} [complete_lattice β] {A : α → β} {b c : β}
{h : b ≤ ⨆(a:α), A a} {h_lt : c < b} {h_bounded : ∀ a : α, (¬ b ≤ A a) → A a ≤ c} :
  ∃ x : α, b ≤ A x :=
begin
  haveI : decidable ∃ (x : α), b ≤ A x := classical.prop_decidable _,
  by_contra, simp at a,
  suffices : b ≤ c, by {suffices : c < c, by {exfalso, have this' := lt_irrefl,
  show Type*, exact β, show preorder (id β), by {dsimp, apply_instance}, exact this' c this},
  exact lt_of_lt_of_le h_lt this},
  apply _root_.le_trans h, apply supr_le, intro a', from h_bounded a' (a a')
end

/-- As a consequence of the previous lemma, if ⨆(a : α), A a = ⊤ such that whenever A a ≠ ⊤ → A α = ⊥, there exists some x : α such that A x = ⊤. -/
lemma supr_eq_top_max {α β : Type*} [complete_lattice β] {A : α → β} {h_nondeg : ⊥ < (⊤ : β)}
{h_top : (⨆(a : α), A a) = ⊤} {h_bounded : ∀ a : α, A a ≠ ⊤ → A a = ⊥} : ∃ x : α, A x = ⊤ :=
  by {apply supr_max_of_bounded, cc, exact h_nondeg, tidy}

lemma supr_eq_Gamma_max {α β : Type*} [complete_lattice β] {A : α → β} {Γ : β} (h_nonzero : ⊥ < Γ)
(h_Γ : Γ ≤ (⨆a, A a)) (h_bounded : ∀ a, (¬ Γ ≤ A a) → A a = ⊥) : ∃ x : α, Γ ≤ A x :=
begin
  apply supr_max_of_bounded', from ‹_›, from ‹_›, intros a H,
  specialize h_bounded a ‹_›, rwa[le_bot_iff]
end

/-- "eoc" means the opposite of "coe", of course -/
lemma eoc_supr {ι β : Type*} {s : ι → β} [complete_lattice β] {X : set ι} :
  (⨆(i : X), s i) = ⨆(i ∈ X), s i :=
begin
  apply le_antisymm; repeat{apply supr_le; intro},
  apply le_supr_of_le i.val, apply le_supr_of_le, exact i.property, refl,
  apply le_supr_of_le, swap, use i, assumption, refl
end

/- Can reindex sup over all sets -/
lemma supr_all_sets {ι β : Type*} {s : ι → β} [complete_lattice β] :
  (⨆(i:ι), s i) = ⨆(X : set ι), (⨆(x : X), s x) :=
begin
  apply le_antisymm,
    {apply supr_le, intro i, apply le_supr_of_le {i}, apply le_supr_of_le, swap,
     use i, from set.mem_singleton i, simp},
    {apply supr_le, intro X, apply supr_le, intro i, apply le_supr}
end

lemma supr_all_sets' {ι β : Type*} {s : ι → β} [complete_lattice β] :
  (⨆(i:ι), s i) = ⨆(X : set ι), (⨆(x ∈ X), s x) :=
by {convert supr_all_sets using 1, simp[eoc_supr]}

-- `b ≤ ⨆(i:ι) c i` if there exists an s : set ι such that b ≤ ⨆ (i : s), c s
lemma le_supr_of_le' {ι β : Type*} {s : ι → β} {b : β} [complete_lattice β]
  (H : ∃ X : set ι, b ≤ ⨆(x:X), s x) : b ≤ ⨆(i:ι), s i :=
begin
  rcases H with ⟨X, H_X⟩, apply _root_.le_trans H_X,
  conv{to_rhs, rw[supr_all_sets]},
  from le_supr_of_le X (by refl)
end

lemma le_supr_of_le'' {ι β : Type*} {s : ι → β} {b : β} [complete_lattice β]
  (H : ∃ X : set ι, b ≤ ⨆(x ∈ X), s x) : b ≤ ⨆(i:ι), s i :=
by {apply le_supr_of_le', convert H using 1, simp[eoc_supr]}

lemma infi_congr {ι β : Type*} {s₁ s₂ : ι → β} [complete_lattice β] {h : ∀ i : ι, s₁ i = s₂ i} :
  (⨅(i:ι), s₁ i) = ⨅(i:ι), s₂ i :=
by simp*

@[simp]lemma supr_congr {ι β : Type*} {s₁ s₂ : ι → β} [complete_lattice β] {h : ∀ i : ι, s₁ i = s₂ i} :
  (⨆(i:ι), s₁ i) = ⨆(i:ι), s₂ i :=
by simp*

lemma imp_iff {β : Type*} {a b : β} [complete_boolean_algebra β] : a ⟹ b = aᶜ ⊔ b := by refl

lemma sup_inf_left_right_eq {β} [distrib_lattice β] {a b c d : β} :
  (a ⊓ b) ⊔ (c ⊓ d) = (a ⊔ c) ⊓ (a ⊔ d) ⊓ (b ⊔ c) ⊓ (b ⊔ d) :=
by {rw[sup_inf_right, sup_inf_left, sup_inf_left]; ac_refl}

lemma inf_sup_right_left_eq {β} [distrib_lattice β] {a b c d : β} :
  (a ⊔ b) ⊓ (c ⊔ d) = (a ⊓ c) ⊔ (a ⊓ d) ⊔ (b ⊓ c) ⊔ (b ⊓ d) :=
by {rw[inf_sup_right, inf_sup_left, inf_sup_left], ac_refl}

-- by {[smt] eblast_using[sup_inf_right, sup_inf_left]}
-- interesting, this takes like 5 seconds
-- probably because both of those rules can be applied pretty much everywhere in the goal
-- and eblast is trying all of them

-- lemma eq_neg_of_partition {β} [boolean_algebra β] {a₁ a₂ : β} (h_anti : a₁ ⊓ a₂ = ⊥) (h_partition : a₁ ⊔ a₂ = ⊤) :
--   a₂ = a₁ᶜ :=
-- begin
--   rw[show a₁ᶜ = ⊤ ⊓ a₁ᶜ, by simp], rw [<-sdiff_eq],
--   rw[← h_partition, sdiff_eq], rw [inf_sup_right],
--   simp *, rw ← sdiff_eq, rw[inf_comm] at h_anti,
--   from (sdiff_eq_left h_anti).symm
-- end

-- lemma le_trans' {β} [lattice β] {a₁ a₂ a₃ : β} (h₁ : a₁ ≤ a₂) {h₂ : a₁ ⊓ a₂ ≤ a₃} : a₁ ≤ a₃ :=
-- begin
--   suffices : a₁ ≤ a₁ ⊓ a₂, from le_trans this ‹_›,
--   rw[show a₁ = a₁ ⊓ a₁, by simp], conv {to_rhs, rw[inf_assoc]},
--   apply inf_le_inf, refl, apply le_inf, refl, assumption
-- end

@[simp]lemma top_le_imp_top {β : Type*} {b : β} [boolean_algebra β] : ⊤ ≤ b ⟹ ⊤ :=
by rw[<-deduction]; apply le_top

lemma poset_yoneda_iff {β : Type*} [partial_order β] {a b : β} : a ≤ b ↔ (∀ {Γ : β}, Γ ≤ a → Γ ≤ b) := ⟨λ _, by finish, λ H, by specialize @H a; finish⟩

lemma poset_yoneda_top {β : Type*} [bounded_lattice β] {b : β} : ⊤ ≤ b ↔ (∀ {Γ : β}, Γ ≤ b) := ⟨λ _, by finish, λ H, by apply H⟩

lemma poset_yoneda {β : Type*} [partial_order β] {a b : β} (H : ∀ Γ : β, Γ ≤ a → Γ ≤ b) : a ≤ b :=
by rwa poset_yoneda_iff

lemma poset_yoneda_inv {β : Type*} [partial_order β] {a b : β} (Γ : β) (H : a ≤ b) :
  Γ ≤ a → Γ ≤ b := by rw poset_yoneda_iff at H; apply H

lemma split_context {β : Type*} [lattice β] {a₁ a₂ b : β} {H : ∀ Γ : β, Γ ≤ a₁ ∧ Γ ≤ a₂ → Γ ≤ b} : a₁ ⊓ a₂ ≤ b :=
by {apply poset_yoneda, intros Γ H', apply H, finish}

example {β : Type*} [bounded_lattice β] : ⊤ ⊓ (⊤ : β) ⊓ ⊤ ≤ ⊤ :=
begin
  apply split_context, intros, simp only [le_inf_iff] at a, auto.split_hyps, from ‹_›
end

-- lemma context_Or_elim {β : Type*} [complete_boolean_algebra β] {ι} {s : ι → β} {Γ b : β}
--   (h : Γ ≤ ⨆(i:ι), s i) {h' : ∀ i, s i ⊓ Γ ≤ s i → s i ⊓ Γ ≤ b} : Γ ≤ b :=
-- begin
--   apply le_trans' h, rw[inf_comm], rw[deduction], apply supr_le, intro i, rw[<-deduction],
--   specialize h' i, apply h', apply inf_le_left
-- end

-- lemma context_or_elim {β : Type*} [complete_boolean_algebra β] {Γ a₁ a₂ b : β}
--   (H : Γ ≤ a₁ ⊔ a₂) {H₁ : a₁ ⊓ Γ ≤ a₁ → a₁ ⊓ Γ ≤ b} {H₂ : a₂ ⊓ Γ ≤ a₂ → a₂ ⊓ Γ ≤ b} : Γ ≤ b :=
-- begin
--   apply le_trans' H, rw[inf_comm], rw[deduction], apply sup_le; rw[<-deduction];
--   [apply H₁, apply H₂]; from inf_le_left
-- end

-- lemma bv_em_aux {β : Type*} [complete_boolean_algebra β] (Γ : β) (b : β) : Γ ≤ b ⊔ -b :=
-- le_trans le_top $ by simp

-- lemma bv_em {β : Type*} [complete_boolean_algebra β] {Γ : β} (b : β) : Γ ≤ b ⊔ -b :=
-- bv_em_aux _ _

-- lemma diagonal_supr_le_supr {α} [complete_lattice α] {ι} {s : ι → ι → α} {Γ : α} (H : Γ ≤ ⨆ i, s i i) : Γ ≤ ⨆ i j, s i j :=
--  le_trans H $ supr_le $ λ i,  le_supr_of_le i $ le_supr_of_le i $ by refl

-- lemma diagonal_infi_le_infi {α} [complete_lattice α] {ι} {s : ι → ι → α} {Γ : α} (H : Γ ≤ ⨅ i j, s i j) : Γ ≤ ⨅ i, s i i :=
--   le_trans H $ le_infi $ λ i, infi_le_of_le i $ infi_le_of_le i $ by refl

-- lemma context_and_intro {β : Type*} [lattice β] {Γ} {a₁ a₂ : β}
--   (H₁ : Γ ≤ a₁) (H₂ : Γ ≤ a₂) : Γ ≤ a₁ ⊓ a₂ := le_inf ‹_› ‹_›

-- lemma specialize_context {β : Type*} [partial_order β] {Γ b : β} (Γ' : β) {H_le : Γ' ≤ Γ} (H : Γ ≤ b)
--   : Γ' ≤ b :=
-- le_trans H_le H

-- lemma context_specialize_aux {β : Type*} [complete_boolean_algebra β] {ι : Type*} {s : ι → β}
--   (j : ι) {Γ : β} {H : Γ ≤ (⨅ i, s i)} : Γ ≤ (⨅i, s i) ⟹ s j :=
-- by {apply le_trans H, rw[<-deduction], apply inf_le_right_of_le, apply infi_le}

-- lemma context_specialize {β : Type*} [complete_lattice β] {ι : Type*} {s : ι → β}
--   {Γ : β} (H : Γ ≤ (⨅ i, s i)) (j : ι) : Γ ≤ s j :=
-- le_trans H (infi_le _ _)

-- lemma context_specialize_strict {β : Type*} [complete_lattice β] {ι : Type*} {s : ι → β}
--   {Γ : β} (H : Γ < (⨅ i, s i)) (j : ι) : Γ < s j :=
-- begin
--   apply lt_iff_le_and_ne.mpr, split, from le_trans (le_of_lt H) (infi_le _ _),
--   intro H', apply @lt_irrefl β _ _, show β, from (⨅ i, s i),
--   apply lt_of_le_of_lt, show β, from Γ, rw[H'], apply infi_le, from ‹_›
-- end

lemma context_split_inf_left {β : Type*} [complete_lattice β] {a₁ a₂ Γ: β} (H : Γ ≤ a₁ ⊓ a₂) : Γ ≤ a₁ :=
by {rw[le_inf_iff] at H, finish}

lemma context_split_inf_right {β : Type*} [complete_lattice β] {a₁ a₂ Γ: β} (H : Γ ≤ a₁ ⊓ a₂) :
  Γ ≤ a₂ :=
by {rw[le_inf_iff] at H, finish}

-- lemma context_imp_elim {β : Type*} [complete_boolean_algebra β] {a b Γ: β} (H₁ : Γ ≤ a ⟹ b) (H₂ : Γ ≤ a) : Γ ≤ b :=
-- begin
--   apply le_trans' H₁, apply le_trans, apply inf_le_inf H₂, refl,
--   rw[inf_comm], simp[imp, inf_sup_right]
-- end

-- lemma context_imp_intro {β : Type*} [complete_boolean_algebra β] {a b Γ : β} (H : a ⊓ Γ ≤ a → a ⊓ Γ ≤ b) : Γ ≤ a ⟹ b :=
-- by {rw[<-deduction, inf_comm], from H (inf_le_left)}

-- instance imp_to_pi {β } [complete_boolean_algebra β] {Γ a b : β} : has_coe_to_fun (Γ ≤ a ⟹ b) :=
-- { F := λ x, Γ ≤ a → Γ ≤ b,
--   coe := λ H₁ H₂, by {apply context_imp_elim; from ‹_›}}

instance infi_to_pi {ι β} [complete_boolean_algebra β] {Γ : β} {ϕ : ι → β} : has_coe_to_fun (Γ ≤ infi ϕ) :=
{ F := λ x, Π i : ι, Γ ≤ ϕ i,
  coe := λ H₁ i, by {change Γ ≤ ϕ i, change Γ ≤ _ at H₁, finish}}

-- lemma bv_absurd {β} [boolean_algebra β] {Γ : β} (b : β) (H₁ : Γ ≤ b) (H₂ : Γ ≤ -b) : Γ ≤ ⊥ :=
-- @le_trans _ _ _ (b ⊓ -b) _ (le_inf ‹_› ‹_›) (by simp)

lemma neg_imp {β : Type*} [boolean_algebra β] {a b : β} : (a ⟹ b)ᶜ = a ⊓ (bᶜ) :=
by simp [imp]

lemma nonzero_wit {β : Type*} [complete_lattice β] {ι : Type*} {s : ι → β} :
  (⊥ < (⨆i, s i)) → ∃ j, (⊥ < s j) :=
begin
  intro H, have := bot_lt_iff_not_le_bot.mp ‹_›,
  haveI : decidable (∃ (j : ι), ⊥ < s j) := classical.prop_decidable _,
  by_contra, apply this, apply supr_le, intro i, rw[not_exists] at a,
  specialize a i, haveI : decidable (s i ≤ ⊥) := classical.prop_decidable _,
  by_contra, have := @bot_lt_iff_not_le_bot β _ (s i), tauto
end

-- lemma nonzero_wit' {β : Type*} [complete_distrib_lattice β] {ι : Type*} {s : ι → β} {Γ : β}
--   (H_nonzero : ⊥ < Γ) (H_le : Γ ≤ ⨆ i , s i ):
--   ∃ j, (⊥ < s j ⊓ Γ) :=
-- begin
--   haveI : decidable (∃ j, (⊥ < s j ⊓ Γ)) := classical.prop_decidable _,
--   by_contra H, push_neg at H, simp only [(not_congr bot_lt_iff_not_le_bot)] at H,
--   have this : (⨆j, s j ⊓ Γ) ≤ ⊥ := supr_le (λ i, classical.by_contradiction $ H ‹_›),
--   rw[<-supr_inf_eq] at this,
--   suffices H_bad : Γ ⊓ Γ ≤ ⊥,
--     by {[smt] eblast_using [bot_lt_iff_not_le_bot, inf_self]},
--   exact le_trans (inf_le_inf ‹_› (by refl)) ‹_›,
-- end

def CCC (𝔹 : Type u) [boolean_algebra 𝔹] : Prop :=
  ∀ ι : Type u, ∀ 𝓐 : ι → 𝔹, (∀ i, ⊥ < 𝓐 i) →
    (∀ i j, i ≠ j → 𝓐 i ⊓ 𝓐 j ≤ ⊥) → (cardinal.mk ι) ≤ cardinal.omega

@[reducible]noncomputable def Prop_to_bot_top {𝔹 : Type u} [has_bot 𝔹] [has_top 𝔹] : Prop → 𝔹 :=
λ p, by {haveI : decidable p := classical.prop_decidable _, by_cases p, from ⊤, from ⊥}

@[simp]lemma Prop_to_bot_top_true {𝔹 : Type u} [has_bot 𝔹] [has_top 𝔹] {p : Prop} {H : p} : Prop_to_bot_top p = (⊤ : 𝔹) := by simp[*, Prop_to_bot_top]

@[simp]lemma Prop_to_bot_top_false {𝔹 : Type u} [has_bot 𝔹] [has_top 𝔹] {p : Prop} {H : ¬ p} : Prop_to_bot_top p = (⊥ : 𝔹) := by simp[*, Prop_to_bot_top]

-- lemma bv_by_contra {𝔹} [boolean_algebra 𝔹] {Γ b : 𝔹} (H : Γ ≤ -b ⟹ ⊥) : Γ ≤ b := by simpa using H

-- noncomputable def to_boolean_valued_set {𝔹} [has_bot 𝔹] [has_top 𝔹] {α} : set α → (α → 𝔹) :=
-- λ s, Prop_to_bot_top ∘ s

run_cmd mk_simp_attr `bv_push_neg

attribute [bv_push_neg] compl_infi compl_supr compl_Inf compl_Sup compl_inf compl_sup compl_top compl_bot compl_compl' neg_imp

end lattice

namespace tactic
namespace interactive

meta def back_chaining : tactic unit := local_context >>= tactic.back_chaining_core skip (`[simp*])

section natded_tactics
open tactic interactive tactic.tidy
open lean.parser lean interactive.types

local postfix `?`:9001 := optional
meta def bv_intro : parse ident_? → tactic unit
| none := propagate_tags (`[refine lattice.le_infi _] >> intro1 >> tactic.skip)
| (some n) := propagate_tags (`[refine lattice.le_infi _] >> tactic.intro n >> tactic.skip)

meta def get_name : ∀(e : expr), name
| (expr.const c [])          := c
| (expr.local_const _ c _ _) := c
| _                          := name.anonymous

meta def lhs_rhs_of_le (e : expr) : tactic (expr × expr) :=
do `(%%x ≤ %%y) <- pure e,
   return (x,y)

meta def lhs_of_le (e : expr) : tactic expr :=
lhs_rhs_of_le e >>= λ x, return x.1

meta def rhs_of_le (e : expr) : tactic expr :=
lhs_rhs_of_le e >>= λ x, return x.2

-- meta def lhs_of_le (e : expr) : tactic expr :=
-- do v_a <- mk_mvar,
--    e' <- to_expr ``(%%v_a ≤ _),
--    unify e e',
--    return v_a

meta def goal_is_bot : tactic bool :=
do b <- get_goal >>= rhs_of_le,
   succeeds $ to_expr ``(by refl : %%b = ⊥)

meta def hyp_is_ineq (e : expr) : tactic bool :=
  (do `(%%x ≤ %%y) <- infer_type e,
     return tt)<|> return ff

meta def hyp_is_neg_ineq (e : expr) : tactic bool :=
  (do `(%%x ≤ - %%y) <- infer_type e,
     return tt) <|> return ff

meta def trace_inequalities : tactic unit :=
  (local_context >>= λ l, l.mfilter (hyp_is_ineq)) >>= trace

meta def hyp_is_ineq_sup (e : expr) : tactic bool :=
  (do `(%%x ≤ %%y ⊔ %%z) <- infer_type e,
     return tt)<|> return ff

meta def get_current_context : tactic expr := target >>= lhs_of_le

meta def trace_sup_inequalities : tactic unit :=
  (local_context >>= λ l, l.mfilter (hyp_is_ineq_sup)) >>= trace

meta def specialize_context_at (H : parse ident) (Γ : parse texpr) : tactic unit :=
do e <- resolve_name H,
   tactic.replace H ``(lattice.specialize_context %%Γ %%e),
   swap >> try `[refine lattice.le_top] >> skip

meta def specialize_context_core (Γ_old : expr) : tactic unit :=
do  v_a <- target >>= lhs_of_le,
    tp <- infer_type Γ_old,
    Γ_name <- get_unused_name "Γ",
    v <- mk_mvar, v' <- mk_mvar,
    Γ_new <- pose Γ_name none v,
    -- TODO(jesse) try replacing to_expr with an expression via mk_app instead
    new_goal <- to_expr ``((%%Γ_new : %%tp) ≤ %%v'),
    tactic.change new_goal,
    ctx <- local_context,
    ctx' <- ctx.mfilter
      (λ e, (do infer_type e >>= lhs_of_le >>= λ e', succeeds $ is_def_eq Γ_old e') <|> return ff),
      ctx'.mmap' (λ H, tactic.replace (get_name H) ``(le_trans (by exact inf_le_right <|> simp : %%Γ_new ≤ _) %%H)),
    ctx2 <- local_context,
    ctx2' <- ctx.mfilter (λ e, (do infer_type e >>= lhs_of_le >>= instantiate_mvars >>= λ e', succeeds $ is_def_eq Γ_new e') <|> return ff),
    -- trace ctx2',
    ctx2'.mmap' (λ H, do H_tp <- infer_type H,
                         e'' <- lhs_of_le H_tp,
                         succeeds (unify Γ_new e'') >>
                   tactic.replace (get_name H) ``(_ : %%Γ_new ≤ _) >> swap >> assumption)

meta def specialize_context_core' (Γ_old : expr) : tactic unit :=
do  v_a <- target >>= lhs_of_le,
    tp <- infer_type Γ_old,
    Γ_name <- get_unused_name "Γ",
    v <- mk_mvar, v' <- mk_mvar,
    Γ_new <- pose Γ_name none v,
    -- TODO(jesse) try replacing to_expr with an expression via mk_app instead
    new_goal <- to_expr ``((%%Γ_new : %%tp) ≤ %%v'),
    tactic.change new_goal,
    ctx <- local_context,
    ctx' <- ctx.mfilter
      (λ e, (do infer_type e >>= lhs_of_le >>= λ e', succeeds $ is_def_eq Γ_old e') <|> return ff),
      ctx'.mmap' (λ H, to_expr ``(le_trans (by exact inf_le_right <|> simp : %%Γ_new ≤ _) %%H) >>= λ foo, tactic.note (get_name H) none foo),
    ctx2 <- local_context,
    ctx2' <- ctx.mfilter (λ e, (do infer_type e >>= lhs_of_le >>= instantiate_mvars >>= λ e', succeeds $ is_def_eq Γ_new e') <|> return ff),
    -- trace ctx2',
    ctx2'.mmap' (λ H, do H_tp <- infer_type H,
                         e'' <- lhs_of_le H_tp,
                         succeeds (unify Γ_new e'') >>
                   tactic.replace (get_name H) ``(_ : %%Γ_new ≤ _) >> swap >> assumption)

meta def specialize_context_assumption_core (Γ_old : expr) : tactic unit :=
do  v_a <- target >>= lhs_of_le,
    tp <- infer_type Γ_old,
    Γ_name <- get_unused_name "Γ",
    v <- mk_mvar, v' <- mk_mvar,
    Γ_new <- pose Γ_name none v,
    -- TODO(jesse) try replacing to_expr with an expression via mk_app instead
    new_goal <- to_expr ``((%%Γ_new : %%tp) ≤ %%v'),
    tactic.change new_goal,
    ctx <- local_context,
    ctx' <- ctx.mfilter
      (λ e, (do infer_type e >>= lhs_of_le >>= λ e', succeeds $ is_def_eq Γ_old e') <|> return ff),
      ctx'.mmap' (λ H, tactic.replace (get_name H) ``(le_trans (by exact inf_le_right <|> assumption : %%Γ_new ≤ _) %%H)),
    ctx2 <- local_context,
    ctx2' <- ctx.mfilter (λ e, (do infer_type e >>= lhs_of_le >>= instantiate_mvars >>= λ e', succeeds $ is_def_eq Γ_new e') <|> return ff),
    -- trace ctx2',
    ctx2'.mmap' (λ H, do H_tp <- infer_type H,
                         e'' <- lhs_of_le H_tp,
                         succeeds (unify Γ_new e'') >>
                   tactic.replace (get_name H) ``(_ : %%Γ_new ≤ _) >> swap >> assumption)



/-- If the goal is an inequality `a ≤ b`, extracts `a` and attempts to specialize all
  facts in context of the form `Γ ≤ d` to `a ≤ d` (this requires a ≤ Γ) -/
meta def specialize_context (Γ : parse texpr) : tactic unit :=
do
  Γ_old <- i_to_expr Γ,
  specialize_context_core Γ_old

meta def specialize_context_assumption (Γ : parse texpr) : tactic unit :=
do
  Γ_old <- i_to_expr Γ,
  specialize_context_assumption_core Γ_old

meta def specialize_context' (Γ : parse texpr) : tactic unit :=
do
  Γ_old <- i_to_expr Γ,
  specialize_context_core' Γ_old

example {β : Type u} [bounded_lattice β] {a b : β} {H : ⊤ ≤ b} : a ≤ b :=
by {specialize_context (⊤ : β), assumption}

meta def bv_exfalso : tactic unit :=
  `[refine le_trans _ (_root_.lattice.bot_le)]

meta def bv_cases_at (H : parse ident) (i : parse ident_) (H_i : parse ident?)  : tactic unit :=
do
  e₀ <- resolve_name H,
  e₀' <- to_expr e₀,
  Γ_old <- target >>= lhs_of_le,
  `[refine lattice.context_Or_elim %%e₀'],
  match H_i with
  | none :=  tactic.intro i >> ((get_unused_name H) >>= tactic.intro)
  | (some n) := tactic.intro i >> (tactic.intro n)
  end,
  specialize_context_core Γ_old


meta def bv_cases_at' (H : parse ident) (i : parse ident_) (H_i : parse ident?)  : tactic unit :=
do
  e₀ <- resolve_name H,
  e₀' <- to_expr e₀,
  Γ_old <- target >>= lhs_of_le,
  `[refine lattice.context_Or_elim %%e₀'],
  match H_i with
  | none :=  tactic.intro i >> ((get_unused_name H) >>= tactic.intro)
  | (some n) := tactic.intro i >> (tactic.intro n)
  end,
  specialize_context_core' Γ_old

meta def bv_cases_at'' (H : parse ident) (i : parse ident_)  : tactic unit :=
do
  e₀ <- resolve_name H,
  e₀' <- to_expr e₀,
  Γ_old <- target >>= lhs_of_le,
  `[refine lattice.context_Or_elim %%e₀'],
  tactic.intro i >> ((get_unused_name H) >>= tactic.intro) >>
  skip

-- here `e` is the proof of Γ ≤ a ⊔ b
meta def bv_or_elim_at_core (e : expr) (Γ_old : expr) (n_H : name) : tactic unit :=
do
   n <- get_unused_name (n_H ++ "left"),
   n' <- get_unused_name (n_H ++ "right"),
   `[apply lattice.context_or_elim %%e],
   (tactic.intro n) >> specialize_context_core Γ_old, swap,
   (tactic.intro n') >> specialize_context_core Γ_old, swap

meta def bv_or_elim_at_core' (e : expr) (Γ_old : expr) (n_H : name) : tactic unit :=
do
   n <- get_unused_name (n_H ++ "left"),
   n' <- get_unused_name (n_H ++ "right"),
   `[apply lattice.context_or_elim %%e],
   (tactic.intro n) >> specialize_context_core' Γ_old, swap,
   (tactic.intro n') >> specialize_context_core' Γ_old, swap

meta def bv_or_elim_at_core'' (e : expr) (Γ_old : expr) (n_H : name) : tactic unit :=
do
   n <- get_unused_name (n_H ++ "left"),
   n' <- get_unused_name (n_H ++ "right"),
   `[apply lattice.context_or_elim %%e]; tactic.clear e,
   (tactic.intro n) >> specialize_context_core' Γ_old, swap,
   (tactic.intro n') >> specialize_context_core' Γ_old, swap

meta def bv_or_elim_at (H : parse ident) : tactic unit :=
do Γ_old <- target >>= lhs_of_le,
   e <- resolve_name H >>= to_expr,
   bv_or_elim_at_core e Γ_old H

-- `px` is a term of type `𝔹`; this cases on "`px ∨ ¬ px`"
meta def bv_cases_on (px : parse texpr) (opt_id : parse (tk "with" *> ident)?) : tactic unit :=
do Γ_old ← target >>= lhs_of_le,
   e ← to_expr ``(lattice.bv_em_aux %%Γ_old %%px),
   let nm := option.get_or_else opt_id "H",
   get_unused_name nm >>= bv_or_elim_at_core e Γ_old

meta def bv_or_elim_at' (H : parse ident) : tactic unit :=
do Γ_old <- target >>= lhs_of_le,
   e <- resolve_name H >>= to_expr,
   bv_or_elim_at_core' e Γ_old H

-- `px` is a term of type `𝔹`; this cases on "`px ∨ ¬ px`"
meta def bv_cases_on' (px : parse texpr) (opt_id : parse (tk "with" *> ident)?) : tactic unit :=
do Γ_old ← target >>= lhs_of_le,
   e ← to_expr ``(lattice.bv_em_aux %%Γ_old %%px),
   let nm := option.get_or_else opt_id "H",
   get_unused_name nm >>= bv_or_elim_at_core' e Γ_old

-- example {β : Type*} [lattice.nontrivial_complete_boolean_algebra β] {Γ : β} : Γ ≤ ⊤ :=
-- begin
--   bv_cases_on ⊤,
--     { from ‹_› },
--     { by simp* }
-- end

-- TODO(jesse) debug these
-- meta def auto_or_elim_step : tactic unit :=
-- do  ctx <- local_context >>= (λ l, l.mfilter hyp_is_ineq_sup),
--     if ctx.length > 0 then
--     ctx.mmap' (λ e, do Γ_old <- target >>= lhs_of_le, bv_or_elim_at_core e Γ_old)
--     else tactic.failed

-- meta def auto_or_elim : tactic unit := tactic.repeat auto_or_elim_step

-- example {β ι : Type u} [lattice.complete_boolean_algebra β] {s : ι → β} {H' : ⊤ ≤ ⨆i, s i} {b : β} : b ≤ ⊤ :=
-- by {specialize_context ⊤, bv_cases_at H' i, specialize_context Γ, sorry }

meta def bv_exists_intro (i : parse texpr): tactic unit :=
  `[refine le_supr_of_le %%i _]

def eta_beta_cfg : dsimp_config :=
{ md := reducible,
  max_steps := simp.default_max_steps,
  canonize_instances := tt,
  single_pass := ff,
  fail_if_unchanged := ff,
  eta := tt,
  zeta := ff,
  beta := tt,
  proj := ff,
  iota := ff,
  unfold_reducible := ff,
  memoize := tt }

meta def bv_specialize_at (H : parse ident) (j : parse texpr) : tactic unit :=
do n <- get_unused_name H,
   e_H <- resolve_name H,
   e <- to_expr ``(lattice.context_specialize %%e_H %%j),
   note n none e >>= λ h, dsimp_hyp h none [] eta_beta_cfg

meta def bv_to_pi (H : parse ident) : tactic unit :=
do   e_H <- resolve_name H,
     e_rhs <- to_expr e_H >>= infer_type >>= rhs_of_le,
     (tactic.replace H  ``(lattice.context_specialize %%e_H) <|>
     tactic.replace H ``(lattice.context_imp_elim %%e_H)) <|>
     tactic.fail "target is not a ⨅ or an ⟹"

meta def bv_to_pi' : tactic unit :=
do ctx <- (local_context >>= (λ l, l.mfilter hyp_is_ineq)),
   ctx.mmap' (λ e, try ((tactic.replace (get_name e)  ``(lattice.context_specialize %%e) <|>
     tactic.replace (get_name e) ``(lattice.context_imp_elim %%e))))

meta def bv_split_at (H : parse ident) : tactic unit :=
do e_H <- resolve_name H,
   tactic.replace H ``(lattice.le_inf_iff.mp %%e_H),
   resolve_name H >>= to_expr >>= cases_core

meta def bv_split : tactic unit :=
do ctx <- (local_context >>= (λ l, l.mfilter hyp_is_ineq)),
   ctx.mmap' (λ e, try (tactic.replace (get_name e) ``(lattice.le_inf_iff.mp %%e))),
   auto_cases >> skip

meta def bv_and_intro (H₁ H₂ : parse ident) : tactic unit :=
do
  H₁ <- resolve_name H₁,
  H₂ <- resolve_name H₂,
  e <- to_expr ``(lattice.context_and_intro %%H₁ %%H₂),
   n <- get_unused_name "H",
   note n none e >> skip

meta def bv_imp_elim_at (H₁ : parse ident) (H₂ : parse texpr) : tactic unit :=
do n <- get_unused_name "H",
   e₁ <- resolve_name H₁,
   e <- to_expr ``(lattice.context_imp_elim %%e₁ %%H₂),
   note n none e >>= λ h, dsimp_hyp h none [] eta_beta_cfg

meta def bv_mp (H : parse ident) (H₂ : parse texpr) : tactic unit :=
do
   n <- get_unused_name H,
   e_H <- resolve_name H,
   e_L <- to_expr H₂,
   pr <- to_expr ``(le_trans %%e_H %%e_L),
   note n none pr >>= λ h, dsimp_hyp h none [] eta_beta_cfg

meta def bv_imp_intro (nm : parse $ optional ident_) : tactic unit :=
match nm with
| none := do Γ_old <- target >>= lhs_of_le,
  `[refine lattice.context_imp_intro _] >> (get_unused_name "H" >>= tactic.intro) >> skip,
  specialize_context_core Γ_old
| (some n) := do Γ_old <- target >>= lhs_of_le,
  `[refine lattice.context_imp_intro _] >> (tactic.intro n) >> skip,
  specialize_context_core Γ_old
end

meta def bv_imp_intro' (nm : parse $ optional ident_) : tactic unit :=
match nm with
| none := do Γ_old <- target >>= lhs_of_le,
  `[refine lattice.context_imp_intro _] >> (get_unused_name "H" >>= tactic.intro) >> skip,
  specialize_context_core' Γ_old
| (some n) := do Γ_old <- target >>= lhs_of_le,
  `[refine lattice.context_imp_intro _] >> (tactic.intro n) >> skip,
  specialize_context_core' Γ_old
end

meta def tidy_context_tactics : list (tactic string) :=
[ reflexivity                                 >> pure "refl",
  propositional_goal >> assumption            >> pure "assumption",
  intros1                                     >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  auto_cases,
  `[simp only [_root_.lattice.le_inf_iff] at *]                                >> pure "simp only [le_inf_iff] at *",
  propositional_goal >> (`[solve_by_elim])    >> pure "solve_by_elim"
]

meta def tidy_split_goals_tactics : list (tactic string) :=
[ reflexivity >> pure "refl",
 propositional_goal >> assumption >> pure "assumption",
  propositional_goal >> (`[solve_by_elim])    >> pure "solve_by_elim",
  `[refine lattice.le_inf _ _] >> pure "refine lattice.le_inf _ _",
  `[exact bv_refl]        >> pure "exact bv_refl _",
  `[rw[bSet.bv_eq_symm]] >> assumption >> pure "rw[bSet.bv_eq_symm], assumption",
   bv_intro none >> pure "bv_intro"
]

meta def bv_split_goal (trace : parse $ optional (tk "?")) : tactic unit :=
  tactic.tidy {trace_result := trace.is_some, tactics := tidy_split_goals_tactics}

meta def bv_or_inr : tactic unit := `[refine le_sup_right_of_le _]
meta def bv_or_inl : tactic unit := `[refine le_sup_left_of_le _]

/--
Succeeds on `e` iff `e` can be matched to the pattern x ≤ - y
-/
private meta def is_le_neg (e : expr) : tactic (expr × expr) :=
do `(%%x ≤ - %%y) <- pure e, return (x,y)

-- private meta def le_not (lhs : expr) (rhs : expr) : expr → tactic expr := λ e,
-- do `(%%x ≤ - %%y) <- pure e,
--    is_def_eq x lhs >> is_def_eq y rhs >> return e

/--
Given an expr `e` such that the type of `e` is `x ≤ -y`, succeed if an expression of type `x ≤ y` is in context and return it.
-/
private meta def find_dual_of (ctx_le : list expr) (ctx_le_negated : list expr) (e : expr) : tactic expr :=
do `(%%y₁ ≤ - %%y₂) <- (infer_type e),
   match ctx_le with
   | [] := tactic.fail "there are no hypotheses"
   | hd :: tl := do b <- (succeeds (do `(%%x₁ ≤ %%x₂) <- (infer_type hd),
                                       is_def_eq x₁ y₁, is_def_eq x₂ y₂)),
                    if b then return hd else by exact _match tl
   end

private meta def find_dual (xs : list expr) : tactic (expr × expr) :=
do xs' <- (xs.mfilter (λ x, succeeds (do `(- %%y) <- ((infer_type x) >>= (rhs_of_le)), skip))),
   match xs' with
   | list.nil := tactic.fail "no negated terms found"
   | (hd :: tl) := (do hd' <- find_dual_of xs xs' hd, return (hd', hd)) <|> by exact _match tl
   end

meta def bv_contradiction  : tactic unit :=
do ctx <- (local_context >>= λ l, l.mfilter (hyp_is_ineq)),
   (h₁,h₂) <- find_dual ctx,
   bv_exfalso >> mk_app (`lattice.bv_absurd) [h₁,h₂] >>= tactic.exact

meta structure context_cfg :=
(trace_result : bool := ff)
(trace_result_prefix : string := "/- `tidy_context` says -/ refine poset_yoneda _, ")
(tactics : list(tactic string) := tidy_context_tactics)

meta def cfg_of_context_cfg : context_cfg → cfg :=
λ X, { trace_result := X.trace_result,
  trace_result_prefix := X.trace_result_prefix,
  tactics := X.tactics}

meta def tidy_context (cfg : context_cfg := {}) : tactic unit :=
`[refine _root_.lattice.poset_yoneda _] >> tactic.tidy (cfg_of_context_cfg cfg)

def with_h_asms {𝔹} [lattice 𝔹] (Γ : 𝔹) : Π (xs : list (𝔹)) (g : 𝔹), Prop
 | [] x := Γ ≤ x
 | (x :: xs) y := Γ ≤ x → with_h_asms xs y

-- intended purpose is to make specialized contexts opaque with have-statements

-- suppose we eliminate an existential quantification over S : ι → 𝔹

-- this introduces a new index i : ι into context, and now we have to add additionally the assumption that Γ ≤ S i.

-- Therefore, the next step is to revert all dependences except for i, so that we then have

-- ∀ Γ'', with_h_asms Γ'' [p,q,r,S i] g → (Γ' ≤ p → Γ' ≤ q → Γ' ≤ r → Γ' ≤ S i → Γ' ≤ g)
-- some work still has to be done in showing
-- that Γ' ≤ Γ and applying le_trans, but this should be cleaner because the specific substitutions are no longer accessible.

end natded_tactics
end interactive
end tactic

namespace lattice

local infix ` ⟹ `:75 := lattice.imp

-- example {𝔹} [complete_boolean_algebra 𝔹] {a b c : 𝔹} :
--  ( a ⟹ b ) ⊓ ( b ⟹ c ) ≤ a ⟹ c :=
-- by {tidy_context, bv_imp_intro Ha, exact a_1_right (a_1_left Ha)}
-- tactic state before final step:
-- a b c Γ : β,
-- Γ_1 : β := a ⊓ Γ,
-- a_1_left : Γ_1 ≤ a ⟹ b,
-- a_1_right : Γ_1 ≤ b ⟹ c,
-- Ha : Γ_1 ≤ a
-- ⊢ Γ_1 ≤ c


-- example {β : Type*} [complete_boolean_algebra β] {a b c : β} :
--  ( a ⟹ b ) ⊓ ( b ⟹ c ) ≤ a ⟹ c :=
-- begin
--   rw[<-deduction], unfold imp, rw[inf_sup_right, inf_sup_right],
--   simp only [inf_assoc, sup_assoc], refine sup_le _ _,
--   ac_change (-a ⊓ a) ⊓ (-b ⊔ c) ≤ c,
--   from inf_le_left_of_le (by simp), rw[inf_sup_right],
--   let x := _, let y := _, change b ⊓ (x ⊔ y) ≤ _,
--   rw[inf_sup_left], apply sup_le,
--   { simp[x, inf_assoc.symm] },
--   { from inf_le_right_of_le (by simp) }
-- end

end lattice
