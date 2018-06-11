/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Additional theorems about the `vector` type.
-/
import data.vector data.list.basic data.sigma

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

theorem mk_to_list :
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

end vector