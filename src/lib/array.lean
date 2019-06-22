universes u v z

namespace array

-- TODO Prove well-founded induction

meta def mmap_copy_aux {k : Type v → Type z} [monad k] {α : Type u} {β : Type v} {n m : ℕ} (f : α → k β) : ℕ → array n α → array m β → k (array m β)
| r x y := do if h : r < n ∧ r < m then do
                let fn : fin n := ⟨r, and.elim_left h⟩,
                let fm : fin m := ⟨r, and.elim_right h⟩,
                y ← y.write fm <$> f (x.read fn),
                mmap_copy_aux (r + 1) x y
              else return y

meta def mmap_copy {k : Type v → Type z} [monad k] {α : Type u} {β : Type v} {n m : ℕ} (x : array n α) (y : array m β) (f : α → k β) : k (array m β) :=
  mmap_copy_aux f 0 x y

meta def map_copy_aux {α : Type u} {β : Type v} {n m : ℕ} (f : α → β) : ℕ → array n α → array m β → array m β
| r x y := if h : r < n ∧ r < m then
             let fn : fin n := ⟨r, and.elim_left h⟩ in
             let fm : fin m := ⟨r, and.elim_right h⟩ in
             map_copy_aux (r + 1) x $ y.write fm (f $ x.read fn)
           else y

meta def map_copy {α : Type u} {β : Type v} {n m : ℕ} (x : array n α) (y : array m β) (f : α → β) : array m β :=
  map_copy_aux f 0 x y

meta def copy {α : Type u} {n m : ℕ} (x : array n α) (y : array m α) : array m α :=
  map_copy x y (λ a, a)

def list_map_copy_from {α : Type u} {β : Type v} {n : ℕ} (x : array n β) (fn : α → β) : list α → ℕ → array n β
| [] m := x
| (a :: rest) m := if h : m < n then
                     let f : fin n := ⟨m, h⟩ in
                     (list_map_copy_from rest (m + 1)).write f (fn a)
                   else x

def list_map_copy {α : Type u} {β : Type v} {n : ℕ} (x : array n β) (fn : α → β) (l : list α) : array n β :=
  list_map_copy_from x fn l 0

-- def list_copy {α : Type u} {n : ℕ} (x : array n α) (l : list α) : array n α :=
--   list_map_copy x (λ a, a) l

end array