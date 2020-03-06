import category.liftable
import system.random
import system.random.basic

universes u v

/-- Gadget to help port instances from definitionally equal types -/
def infer_instance_as (cl : Sort u) [I : cl] : cl := I

/-- Monad to generate random examples to test properties with.
It has a `nat` parameter so that the caller can decide on the
size of the examples -/
@[reducible]
def gen (α : Type u) := reader_t (ulift ℕ) rand α

instance : monad gen :=
infer_instance_as $ monad $ reader_t (ulift ℕ) rand

instance : is_lawful_monad gen :=
infer_instance_as $ is_lawful_monad $ reader_t (ulift ℕ) rand

variable (α : Type u)

section random

variable [random α]

/-- execute a `gen` inside the `io` monad using `i` as the example
size and creating a fresh random number generator -/
def run_gen {α} (x : gen α) (i : ℕ) : io α :=
io.run_rand (x.run ⟨i⟩)

/-- lift `random.random` to the `gen` monad -/
def choose_any : gen α :=
⟨ λ _, random.random α _ ⟩

variables {α}

/-- lift `random.random_r` to the `gen` monad -/
def choose (x y : α) (p : x ≤ y . check_range) : gen (x .. y) :=
⟨ λ _, random.random_r _ x y p ⟩

end random

open nat (hiding choose)

/-- generate a `nat` example between `x` and `y` -/
def choose_nat (x y : ℕ) (p : x ≤ y . check_range) : gen (x .. y) := do
⟨z,h⟩ ← @choose (fin $ succ y) _ ⟨x,succ_le_succ p⟩ ⟨y,lt_succ_self _⟩ p,
have h' : x ≤ z.val ∧ z.val ≤ y,
  by { simp [fin.le_def] at h, apply h },
return ⟨z.val,h'⟩

open nat

namespace gen

instance : liftable gen.{u} gen.{v} :=
reader_t.liftable' (equiv.ulift.trans equiv.ulift.symm)

end gen

variable {α}

/-- Get access to the size parameter of the `gen` monad. For
reasons of universe polymorphism, it is specified in
continuation passing style. -/
def sized (cmd : ℕ → gen α) : gen α :=
⟨ λ ⟨sz⟩, (cmd sz).run ⟨sz⟩ ⟩

/-- create `n` examples using `cmd` -/
def vector_of : ∀ (n : ℕ) (cmd : gen α), gen (vector α n)
| 0 _ := return vector.nil
| (succ n) cmd := vector.cons <$> cmd <*> vector_of n cmd

/-- create a list of examples using `cmd`. The size is controlled
by the size parameter of `gen` -/
def list_of (cmd : gen α) : gen (list α) :=
sized $ λ sz, do
do ⟨ n ⟩ ← liftable.up' $ choose_nat 0 sz,
   v ← vector_of n.val cmd,
   return v.to_list

open ulift

/-- given a list of example generators, choose one to create an example -/
def one_of (xs : list (gen α)) (pos : 0 < xs.length) : gen α :=
have _inst : random _ := random_fin_of_pos _ pos, do
n ← liftable.up' $ @choose_any (fin xs.length) _inst,
list.nth_le xs (down n).val (down n).is_lt
