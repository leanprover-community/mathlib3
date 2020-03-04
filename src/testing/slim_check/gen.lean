import category.liftable
import system.random
import system.random.basic

universes u v

@[reducible]
def gen (α : Type u) := reader_t (ulift ℕ) rand α

-- namespace gen

-- variables {α β γ : Type u}

-- protected def pure (x : α) : gen α :=
-- λ _, pure x

-- protected def bind (x : gen α) (f : α → gen β) : gen β
--  | sz := do
-- i ← x sz,
-- f i sz

-- instance : has_bind gen :=
-- ⟨ @gen.bind ⟩

-- instance : has_pure gen :=
-- ⟨ @gen.pure ⟩

-- lemma bind_assoc (x : gen α) (f : α → gen β) (g : β → gen γ)
-- : x >>= f >>= g = x >>= (λ i, f i >>= g) :=
-- begin
--   funext sz,
--   simp [has_bind.bind],
--   simp [gen.bind,monad.bind_assoc],
-- end

-- lemma pure_bind (x : α) (f : α → gen β)
-- : pure x >>= f = f x :=
-- begin
--   funext i,
--   simp [has_bind.bind],
--   simp [gen.bind,monad.pure_bind],
--   refl
-- end

-- lemma id_map (x : gen α)
-- : x >>= pure ∘ id = x :=
-- begin
--   funext i,
--   simp [has_bind.bind,function.comp,pure,has_pure.pure],
--   simp [gen.bind,gen.pure],
--   rw monad.bind_pure,
--   exact α,
-- end

-- end gen

-- instance : monad gen :=
-- { pure := @gen.pure
-- , bind := @gen.bind
-- , bind_assoc := @gen.bind_assoc
-- , pure_bind  := @gen.pure_bind
-- , id_map := @gen.id_map }

variable (α : Type u)

section random

variable [random α]

def run_gen {α} (x : gen α) (i : ℕ) : io α :=
io.run_rand (x.run ⟨i⟩)

def choose_any : gen α :=
⟨ λ _, random.random α _ ⟩

variables {α}

def choose (x y : α) (p : x ≤ y . check_range) : gen (x .. y) :=
⟨ λ _, random.random_r _ x y p ⟩

end random

open nat (hiding choose)

def choose_nat (x y : ℕ) (p : x ≤ y . check_range) : gen (x .. y) := do
⟨z,h⟩ ← @choose (fin $ succ y) _ ⟨x,succ_le_succ p⟩ ⟨y,lt_succ_self _⟩ p,
have h' : x ≤ z.val ∧ z.val ≤ y,
  by { simp [fin.le_def] at h, apply h },
return ⟨z.val,h'⟩

open nat

-- instance (g : Type) : liftable (rand_g.{u} g) (rand_g.{v} g) :=
-- @state_t.liftable' _ _ _ _ _ _ _ _ _  (equiv.ulift.trans.{u u u u u} equiv.ulift.symm)

namespace gen

variable {α}

instance : liftable gen.{u} gen.{v} :=
reader_t.liftable' (equiv.ulift.trans equiv.ulift.symm)
set_option pp.universes true
-- begin
--    reader_t.liftable
-- end

end gen

variable {α}

def sized (cmd : ℕ → gen α) : gen α :=
⟨ λ ⟨sz⟩, (cmd sz).run ⟨sz⟩ ⟩

def vector_of : ∀ (n : ℕ) (cmd : gen α), gen (vector α n)
 | 0 _ := return vector.nil
 | (succ n) cmd := vector.cons <$> cmd <*> vector_of n cmd

def list_of (cmd : gen α) : gen (list α) :=
sized $ λ sz, do
do ⟨ n ⟩ ← liftable.up' $ choose_nat 0 sz,
   v ← vector_of n.val cmd,
   return v.to_list

open ulift

def one_of (xs : list (gen α)) (pos : 0 < xs.length) : gen α :=
have _inst : random _ := random_fin_of_pos _ pos, do
n ← liftable.up' $ @choose_any (fin xs.length) _inst,
list.nth_le xs (down n).val (down n).is_lt
