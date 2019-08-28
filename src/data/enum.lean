
import category.monad.basic
import data.list.basic
import data.equiv.basic
import data.finset
import data.fintype

open finset (hiding singleton)

namespace fin

def enum (n : ℕ) : list (fin n) :=
(list.range n).attach.map $ λ ⟨i,h⟩, ⟨i,by simpa using h⟩

@[simp] lemma mem_enum {n} (x : fin n) : x ∈ enum n :=
by simp [enum]; existsi x.1; simp [fin.is_lt]

end fin

class enumerable (α : Sort*) :=
(card : ℕ)
(equiv : α ≃ fin card)

namespace enumerable

variables {α : Type*}

instance [enumerable α] : decidable_eq α :=
equiv.decidable_eq_of_equiv (equiv α)

def of_equiv (α) {β} [enumerable α] (h : β ≃ α) : enumerable β :=
{ card := card α,
  equiv := h.trans (equiv α)  }

def of_list [decidable_eq α] (xs : list α) (h : ∀ x : α, x ∈ xs) : enumerable α :=
{ card := xs.erase_dup.length,
  equiv := ⟨λ x, ⟨xs.erase_dup.index_of x,by rw [list.index_of_lt_length,list.mem_erase_dup]; apply h⟩,
           λ ⟨i,h⟩, xs.erase_dup.nth_le _ h,
           λ x, by simp [of_list._match_1],
           λ ⟨i,h⟩, by simp [of_list._match_1,*]; rw list.nth_le_index_of; apply list.nodup_erase_dup ⟩ }

def to_list (α) [enumerable α] : list α :=
(fin.enum (card α)).map (equiv α).symm

open function

@[simp] lemma mem_to_list [enumerable α] (x : α) : x ∈ to_list α :=
by simp [to_list]; existsi equiv α x; simp

def of_surjective {β} (f : β → α) [decidable_eq α] [enumerable β] (h : surjective f) : enumerable α :=
of_list ((to_list β).map f) (by intro; simp; exact h _)

-- def of_injective {α β} (f : β → α) [decidable_eq α] [enum β] (h : injective f) : enum α :=
-- of_list ((to_list β).map f) _

instance pempty : enumerable pempty :=
of_list [] (λ x, pempty.elim x)

instance empty : enumerable empty :=
of_list [] (λ x, empty.elim x)

instance punit : enumerable punit :=
of_list [punit.star] (λ x, by cases x; simp)

instance prod {β} [enumerable α] [enumerable β] : enumerable (α × β) :=
of_list ( (to_list α).product (to_list β) ) (λ x, by cases x; simp)

instance sum {β} [enumerable α] [enumerable β] : enumerable (α ⊕ β) :=
of_list ( (to_list α).map sum.inl ++ (to_list β).map sum.inr ) (λ x, by cases x; simp)

instance fin {n} : enumerable (fin n) :=
of_list (fin.enum _) (by simp)

instance quotient.enum [enumerable α] (s : setoid α)
  [decidable_rel ((≈) : α → α → Prop)] : enumerable (quotient s) :=
enumerable.of_surjective quotient.mk (λ x, quotient.induction_on x (λ x, ⟨x, rfl⟩))

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

instance finset.enumerable [enumerable α] : enumerable (finset α) :=
of_list (finset.enum (to_list α)) (by intro; simp)

instance subtype.enumerable [enumerable α] (p : α → Prop) [decidable_pred p] : enumerable {x // p x} :=
of_list ((to_list α).filter_map $ λ x, if h : p x then some ⟨_,h⟩ else none) (by rintro ⟨x,h⟩; simp; existsi x; simp *)

instance (β : α → Type*)
  [enumerable α] [∀ a, enumerable (β a)] : enumerable (sigma β) :=
of_list
  ((to_list α).bind $ λ a, (to_list (β a)).map $ sigma.mk a)
  (by intro x; cases x; simp)

instance psigma.enumerable {β : α → Type*} [enumerable α] [∀ a, enumerable (β a)] :
  enumerable (Σ' a, β a) :=
enumerable.of_equiv _ (equiv.psigma_equiv_sigma _)
--   (by intro x; cases x; simp)

instance psigma.enumerable_prop_left {α : Prop} {β : α → Type*} [∀ a, enumerable (β a)] [decidable α] :
  enumerable (Σ' a, β a) :=
if h : α then of_list ((to_list (β h)).map $ psigma.mk h) (λ ⟨a,Ba⟩, by simp)
else of_list [] (λ ⟨a,Ba⟩, (h a).elim)

instance psigma.enumerable_prop_right {β : α → Prop} [enumerable α] [∀ a, decidable (β a)] :
  enumerable (Σ' a, β a) :=
enumerable.of_equiv {a // β a} ⟨λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, rfl, λ ⟨x, y⟩, rfl⟩

instance psigma.enumerable_prop_prop {α : Prop} {β : α → Prop} [decidable α] [∀ a, decidable (β a)] :
  enumerable (Σ' a, β a) :=
if h : ∃ a, β a
  then of_list [⟨h.fst,h.snd⟩] (by rintro ⟨⟩; simp)
  else of_list [] (λ a, (h ⟨a.fst,a.snd⟩).elim)

instance [enumerable α] : fintype α :=
{ elems := univ.map (equiv α).symm.to_embedding,
  complete := by intros; simp; existsi (equiv α x); simp }

-- #print instances decidable

-- instance prop.enum : enum Prop :=
-- of_list [true,false] _

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
  enumerable.pi.cons x xs <$> fs x <*> pi xs fs

lemma mem_pi  {α : Type*} {β : α → Type*} [enumerable α] [∀a, enumerable (β a)] (xs : list α) (f : Π a, a ∈ xs → β a) :
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

def pi.enum  {α : Type*} (β : α → Type*) [enumerable α] [∀a, enumerable (β a)] : list (Π a, β a) :=
(pi (to_list α) (λ x, to_list (β x))).map (λ f x, f x (mem_to_list _))

lemma pi.mem_enum  {α : Type*} {β : α → Type*} [enumerable α] [∀a, enumerable (β a)] (f : Π a, β a) : f ∈ pi.enum β :=
by simp [pi.enum]; refine ⟨λ a h, f a, mem_pi _ _, rfl⟩

instance pi.enumerable {α : Type*} {β : α → Type*}
  [enumerable α] [∀a, enumerable (β a)] : enumerable (Πa, β a) :=
of_list (pi.enum _) (λ x, pi.mem_enum _)

instance pfun_enum (p : Prop) [decidable p] (α : p → Type*)
  [Π hp, enumerable (α hp)] : enumerable (Π hp : p, α hp) :=
if hp : p then of_list ( (to_list (α hp)).map $ λ x hp', x ) (by intro; simp; exact ⟨x hp,rfl⟩)
          else of_list [λ hp', (hp hp').elim] (by intro; simp; ext hp'; cases hp hp')

end enumerable
