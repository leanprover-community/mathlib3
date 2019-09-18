/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon

Type class for finitely fin_enum types. The property is stronger
than`fintype in that it assigns each element a rank in a finite
enumeration.
-/

import category.monad.basic
import data.list.basic
import data.equiv.basic
import data.finset
import data.fintype

open finset (hiding singleton)

namespace fin

def enum (n : ℕ) : list (fin n) :=
list.of_fn id

@[simp] lemma mem_enum {n} (x : fin n) : x ∈ enum n :=
by simp [enum,list.mem_of_fn_id]; existsi x.1; simp [fin.is_lt]

end fin

class fin_enum (α : Sort*) :=
(card : ℕ)
(equiv : α ≃ fin card)

namespace fin_enum

variables {α : Type*}

instance [fin_enum α] : decidable_eq α :=
equiv.decidable_eq_of_equiv (equiv α)

def of_equiv (α) {β} [fin_enum α] (h : β ≃ α) : fin_enum β :=
{ card := card α,
  equiv := h.trans (equiv α)  }

def of_nodup_list [decidable_eq α] (xs : list α) (h : ∀ x : α, x ∈ xs) (h' : list.nodup xs) : fin_enum α :=
{ card := xs.length,
  equiv := ⟨λ x, ⟨xs.index_of x,by rw [list.index_of_lt_length]; apply h⟩,
           λ ⟨i,h⟩, xs.nth_le _ h,
           λ x, by simp [of_nodup_list._match_1],
           λ ⟨i,h⟩, by simp [of_nodup_list._match_1,*]; rw list.nth_le_index_of; apply list.nodup_erase_dup ⟩ }

def of_list [decidable_eq α] (xs : list α) (h : ∀ x : α, x ∈ xs) : fin_enum α :=
of_nodup_list xs.erase_dup (by simp *) (list.nodup_erase_dup _)

def to_list (α) [fin_enum α] : list α :=
(fin.enum (card α)).map (equiv α).symm

open function

@[simp] lemma mem_to_list [fin_enum α] (x : α) : x ∈ to_list α :=
by simp [to_list]; existsi equiv α x; simp

def of_surjective {β} (f : β → α) [decidable_eq α] [fin_enum β] (h : surjective f) : fin_enum α :=
of_list ((to_list β).map f) (by intro; simp; exact h _)

noncomputable def of_injective {α β} (f : α → β) [inhabited α] [decidable_eq α] [fin_enum β] (h : injective f) : fin_enum α :=
of_surjective (inv_fun f) (inv_fun_surjective h)

instance pempty : fin_enum pempty :=
of_list [] (λ x, pempty.elim x)

instance empty : fin_enum empty :=
of_list [] (λ x, empty.elim x)

instance punit : fin_enum punit :=
of_list [punit.star] (λ x, by cases x; simp)

instance prod {β} [fin_enum α] [fin_enum β] : fin_enum (α × β) :=
of_list ( (to_list α).product (to_list β) ) (λ x, by cases x; simp)

instance sum {β} [fin_enum α] [fin_enum β] : fin_enum (α ⊕ β) :=
of_list ( (to_list α).map sum.inl ++ (to_list β).map sum.inr ) (λ x, by cases x; simp)

instance fin {n} : fin_enum (fin n) :=
of_list (fin.enum _) (by simp)

instance quotient.enum [fin_enum α] (s : setoid α)
  [decidable_rel ((≈) : α → α → Prop)] : fin_enum (quotient s) :=
fin_enum.of_surjective quotient.mk (λ x, quotient.induction_on x (λ x, ⟨x, rfl⟩))

def finset.enum [decidable_eq α] : list α → list (finset α)
| [] := [∅]
| (x :: xs) :=
  do r ← finset.enum xs,
     [r,{x} ∪ r]

@[simp] lemma finset.mem_enum [decidable_eq α] (s : finset α) (xs : list α) : s ∈ finset.enum xs ↔ ∀ x ∈ s, x ∈ xs :=
begin
  induction xs generalizing s; simp [*,finset.enum],
  { simp [finset.eq_empty_iff_forall_not_mem,(∉)], refl },
  { split, rintro ⟨a,h,h'⟩ x hx,
    cases h',
    { right, apply h, subst a, exact hx, },
    { simp [h'] at hx ⊢, cases hx,
      { exact or.inr (h _ hx) },
      exact or.inl hx  },
    intro h, existsi s \ ({xs_hd} : finset α),
    simp, simp [or_iff_not_imp_left] at h,
    existsi h,
    by_cases xs_hd ∈ s,
    { have : finset.singleton xs_hd ⊆ s, simp [(⊆),*],
      simp [union_sdiff_of_subset this], },
    { left, symmetry, simp [sdiff_eq_self],
      intro a, simp, intros h₀ h₁, subst a,
      apply h h₀, } }
end

instance finset.fin_enum [fin_enum α] : fin_enum (finset α) :=
of_list (finset.enum (to_list α)) (by intro; simp)

instance subtype.fin_enum [fin_enum α] (p : α → Prop) [decidable_pred p] : fin_enum {x // p x} :=
of_list ((to_list α).filter_map $ λ x, if h : p x then some ⟨_,h⟩ else none) (by rintro ⟨x,h⟩; simp; existsi x; simp *)

instance (β : α → Type*)
  [fin_enum α] [∀ a, fin_enum (β a)] : fin_enum (sigma β) :=
of_list
  ((to_list α).bind $ λ a, (to_list (β a)).map $ sigma.mk a)
  (by intro x; cases x; simp)

instance psigma.fin_enum {β : α → Type*} [fin_enum α] [∀ a, fin_enum (β a)] :
  fin_enum (Σ' a, β a) :=
fin_enum.of_equiv _ (equiv.psigma_equiv_sigma _)
--   (by intro x; cases x; simp)

instance psigma.fin_enum_prop_left {α : Prop} {β : α → Type*} [∀ a, fin_enum (β a)] [decidable α] :
  fin_enum (Σ' a, β a) :=
if h : α then of_list ((to_list (β h)).map $ psigma.mk h) (λ ⟨a,Ba⟩, by simp)
else of_list [] (λ ⟨a,Ba⟩, (h a).elim)

instance psigma.fin_enum_prop_right {β : α → Prop} [fin_enum α] [∀ a, decidable (β a)] :
  fin_enum (Σ' a, β a) :=
fin_enum.of_equiv {a // β a} ⟨λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, rfl, λ ⟨x, y⟩, rfl⟩

instance psigma.fin_enum_prop_prop {α : Prop} {β : α → Prop} [decidable α] [∀ a, decidable (β a)] :
  fin_enum (Σ' a, β a) :=
if h : ∃ a, β a
  then of_list [⟨h.fst,h.snd⟩] (by rintro ⟨⟩; simp)
  else of_list [] (λ a, (h ⟨a.fst,a.snd⟩).elim)

instance [fin_enum α] : fintype α :=
{ elems := univ.map (equiv α).symm.to_embedding,
  complete := by intros; simp; existsi (equiv α x); simp }

def pi.cons {β : α → Type*} [decidable_eq α] (x : α) (xs : list α) (b : β x)
  (f : Π a, a ∈ xs → β a) :
  Π a, a ∈ (x :: xs : list α) → β a
| y h :=
  if h' : y = x then cast (by rw h') b
    else f y (list.mem_of_ne_of_mem h' h)

def pi.tail {α : Type*} {β : α → Type*} [decidable_eq α] {x : α} {xs : list α}
  (f : Π a, a ∈ (x :: xs : list α) → β a) :
  Π a, a ∈ xs → β a
| a h := f a (list.mem_cons_of_mem _ h)

def pi {α : Type*} {β : α → Type*} [decidable_eq α] : Π xs : list α, (Π a, list (β a)) → list (Π a, a ∈ xs → β a)
| [] fs := [λ x h, h.elim]
| (x :: xs) fs :=
  fin_enum.pi.cons x xs <$> fs x <*> pi xs fs

lemma mem_pi  {α : Type*} {β : α → Type*} [fin_enum α] [∀a, fin_enum (β a)] (xs : list α) (f : Π a, a ∈ xs → β a) :
  f ∈ pi xs (λ x, to_list (β x)) :=
begin
  induction xs; simp [pi,-list.map_eq_map] with monad_norm functor_norm,
  { ext a ⟨ ⟩ },
  { existsi pi.cons xs_hd xs_tl (f _ (list.mem_cons_self _ _)),
    split, exact ⟨_,rfl⟩,
    existsi pi.tail f, split,
    { apply xs_ih, },
    { ext x h, simp [pi.cons], split_ifs, subst x, refl, refl }, }
end

def pi.enum  {α : Type*} (β : α → Type*) [fin_enum α] [∀a, fin_enum (β a)] : list (Π a, β a) :=
(pi (to_list α) (λ x, to_list (β x))).map (λ f x, f x (mem_to_list _))

lemma pi.mem_enum  {α : Type*} {β : α → Type*} [fin_enum α] [∀a, fin_enum (β a)] (f : Π a, β a) : f ∈ pi.enum β :=
by simp [pi.enum]; refine ⟨λ a h, f a, mem_pi _ _, rfl⟩

instance pi.fin_enum {α : Type*} {β : α → Type*}
  [fin_enum α] [∀a, fin_enum (β a)] : fin_enum (Πa, β a) :=
of_list (pi.enum _) (λ x, pi.mem_enum _)

instance pfun_fin_enum (p : Prop) [decidable p] (α : p → Type*)
  [Π hp, fin_enum (α hp)] : fin_enum (Π hp : p, α hp) :=
if hp : p then of_list ( (to_list (α hp)).map $ λ x hp', x ) (by intro; simp; exact ⟨x hp,rfl⟩)
          else of_list [λ hp', (hp hp').elim] (by intro; simp; ext hp'; cases hp hp')

end fin_enum
