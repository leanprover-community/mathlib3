/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Additional theorems about the `vector` type.
-/
import data.vector data.list.basic data.sigma data.equiv.basic
       category.traversable

attribute [extensionality] vector.eq

namespace vector
variables {α : Type*} {n : ℕ}

attribute [simp] head_cons tail_cons

instance [inhabited α] : inhabited (vector α n) :=
⟨of_fn (λ _, default α)⟩

theorem to_list_injective : function.injective (@to_list α n) :=
subtype.val_injective

@[simp] theorem to_list_of_fn : ∀ {n} (f : fin n → α), to_list (of_fn f) = list.of_fn f
| 0     f := rfl
| (n+1) f := by rw [of_fn, list.of_fn_succ, to_list_cons, to_list_of_fn]

@[simp] theorem mk_to_list :
  ∀ (v : vector α n) h, (⟨to_list v, h⟩ : vector α n) = v
| ⟨l, h₁⟩ h₂ := rfl

theorem nth_eq_nth_le : ∀ (v : vector α n) (i),
  nth v i = v.to_list.nth_le i.1 (by rw to_list_length; exact i.2)
| ⟨l, h⟩ i := rfl

@[simp] theorem nth_of_fn {n} (f : fin n → α) (i) : nth (of_fn f) i = f i :=
by rw [nth_eq_nth_le, ← list.nth_le_of_fn f];
   congr; apply to_list_of_fn

@[simp] theorem of_fn_nth (v : vector α n) : of_fn (nth v) = v :=
begin
  rcases v with ⟨l, rfl⟩,
  apply to_list_injective,
  change nth ⟨l, eq.refl _⟩ with λ i, nth ⟨l, rfl⟩ i,
  simp [nth, list.of_fn_nth_le]
end

@[simp] theorem nth_tail : ∀ (v : vector α n.succ) (i : fin n),
  nth (tail v) i = nth v i.succ
| ⟨a::l, e⟩ ⟨i, h⟩ := by simp [nth_eq_nth_le]; refl

@[simp] theorem tail_of_fn {n : ℕ} (f : fin n.succ → α) :
  tail (of_fn f) = of_fn (λ i, f i.succ) :=
(of_fn_nth _).symm.trans $ by congr; funext i; simp

theorem head'_to_list : ∀ (v : vector α n.succ),
  (to_list v).head' = some (head v)
| ⟨a::l, e⟩ := rfl

def reverse (v : vector α n) : vector α n :=
⟨v.to_list.reverse, by simp⟩

@[simp] theorem nth_zero : ∀ (v : vector α n.succ), nth v 0 = head v
| ⟨a::l, e⟩ := rfl

@[simp] theorem head_of_fn
  {n : ℕ} (f : fin n.succ → α) : head (of_fn f) = f 0 :=
by rw [← nth_zero, nth_of_fn]

@[simp] theorem nth_cons_zero
  (a : α) (v : vector α n) : nth (a :: v) 0 = a :=
by simp [nth_zero]

@[simp] theorem nth_cons_succ
  (a : α) (v : vector α n) (i : fin n) : nth (a :: v) i.succ = nth v i :=
by rw [← nth_tail, tail_cons]

def {u} m_of_fn {m} [monad m] {α : Type u} : ∀ {n}, (fin n → m α) → m (vector α n)
| 0     f := pure nil
| (n+1) f := do a ← f 0, v ← m_of_fn (λi, f i.succ), pure (a :: v)

theorem m_of_fn_pure {m} [monad m] [is_lawful_monad m] {α} :
  ∀ {n} (f : fin n → α), @m_of_fn m _ _ _ (λ i, pure (f i)) = pure (of_fn f)
| 0     f := rfl
| (n+1) f := by simp [m_of_fn, @m_of_fn_pure n, of_fn]

def {u} mmap {m} [monad m] {α} {β : Type u} (f : α → m β) :
  ∀ {n}, vector α n → m (vector β n)
| _ ⟨[], rfl⟩   := pure nil
| _ ⟨a::l, rfl⟩ := do h' ← f a, t' ← mmap ⟨l, rfl⟩, pure (h' :: t')

@[simp] theorem mmap_nil {m} [monad m] {α β} (f : α → m β) :
  mmap f nil = pure nil := rfl

@[simp] theorem mmap_cons {m} [monad m] {α β} (f : α → m β) (a) :
  ∀ {n} (v : vector α n), mmap f (a::v) =
  do h' ← f a, t' ← mmap f v, pure (h' :: t')
| _ ⟨l, rfl⟩ := rfl

theorem ext : ∀ {v w : vector α n}
  (h : ∀ m : fin n, vector.nth v m = vector.nth w m), v = w
| ⟨v, hv⟩ ⟨w, hw⟩ h := subtype.eq (list.ext_le (by rw [hv, hw]) 
  (λ m hm hn, h ⟨m, hv ▸ hm⟩))

end vector

namespace vector

universes u
variables {n : ℕ}

section traverse

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']

open applicative functor
open list (cons) nat

private def traverse_aux {α β : Type u} (g : α → f β) :
  Π (x : list α), f (vector β x.length)
| [] := pure vector.nil
| (x::xs) := vector.cons <$> g x <*> traverse_aux xs

protected def traverse {α β : Type u} (g : α → f β) :
  vector α n → f (vector β n)
 | ⟨v,Hv⟩ := cast (by rw Hv) $ traverse_aux g v

protected def to_array {α : Type u} {n} : vector α n → array n α
 | ⟨xs,h⟩ := cast (by rw h) xs.to_array

variables [is_lawful_applicative f] [is_lawful_applicative f']
variables {α β η : Type u}

@[simp]
protected lemma traverse_def (g : α → f β) (x : α) (xs : vector α n) :
  vector.traverse g (x :: xs) = cons <$> g x <*> vector.traverse g xs :=
begin
  cases xs, simp!,
  h_generalize _ : _ == i,
  h_generalize _ : _ == j, subst n,
  simp at *, subst i, subst j
end

protected lemma id_traverse (x : vector α n) :
  vector.traverse id.mk x = x :=
begin
  cases x with x, subst n,
  dsimp [vector.traverse,cast],
  induction x with x xs, refl,
  simp! [x_ih], refl
end

open function

protected lemma comp_traverse (g : α → f β) (h : β → f' η) (x : vector α n) :
  vector.traverse (comp.mk ∘ functor.map h ∘ g) x =
  comp.mk (vector.traverse h <$> vector.traverse g x) :=
begin
  cases x with x,
  dunfold vector.traverse, subst n, dsimp [cast],
  induction x with x xs; simp! [cast,*] with functor_norm, refl,
  congr' 2, ext, simp [function.comp,flip]
end

protected lemma map_traverse
   (g : α → f' β) (f : β → η)
   (x : vector α n) :
  map f <$> vector.traverse g x = vector.traverse (functor.map f ∘ g) x :=
begin
  symmetry,
  cases x with x,
  subst n, unfold vector.traverse cast,
  induction x; simp! [*,cast,map,flip,function.comp,vector.map] with functor_norm,
  { refl },
  { congr' 2, ext, cases x_1, refl }
end

protected lemma traverse_map
   (g : α → β) (f : β → f' η)
   (x : vector α n) :
  vector.traverse f (map g x) = vector.traverse (f ∘ g) x :=
begin
  symmetry,
  cases x with x, subst n,
  induction x; simp! [*,map,flip,vector.map] with norm,
  { refl },
  { congr' 1, simp, simp,
    congr' 1, simp, simp,
    { dsimp [list.length],
      rw list.length_map },
    simp [vector.traverse,map] at x_ih,
    transitivity, apply heq_of_eq, apply x_ih,
    apply cast_heq }
end

variable (eta : applicative_transformation f f')

protected lemma naturality {α β : Type*}
  (F : α → f β) (x : vector α n) :
  eta (vector.traverse F x) = vector.traverse (@eta _ ∘ F) x :=
begin
  cases x;
  simp! [vector.traverse] with norm,
  induction x_val with x xs generalizing n,
  { h_generalize Hi : _ == i,
    h_generalize Hj : _ == j,
    simp! at Hi Hj; subst n; cases Hi; cases Hj,
    simp [*] with functor_norm },
  { specialize x_val_ih rfl, subst n,
    revert x_val_ih,
    h_generalize Hi : _ == i, h_generalize _ : _ == j,
    h_generalize _  : _ == k, h_generalize _ : _ == h,
    intros, simp! at *,
    subst k, subst h, simp with functor_norm,
    subst i, subst j, rw [x_val_ih] }
end

end traverse

instance : traversable.{u} (flip vector n) :=
{ traverse := @vector.traverse n
, map := λ α β, @vector.map.{u u} α β n }

instance : is_lawful_traversable.{u} (flip vector n) :=
{ id_traverse := @vector.id_traverse n,
  comp_traverse := @vector.comp_traverse n,
  map_traverse := @vector.map_traverse.{u} n,
  traverse_map := @vector.traverse_map n,
  naturality := @vector.naturality.{u} n,
  id_map := by intros; cases x; simp! [functor.map],
  comp_map := by intros; cases x; simp! [functor.map] }

end vector
