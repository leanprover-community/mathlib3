import data.set.finite
import data.finset.basic

def s : finset (fin 3) := {0, 1}

example : finset (fin 3) := s.map (equiv.add_left (1 : fin 3)).to_embedding
example : finset (fin 3) := s.map (equiv.add_left (1 : fin 3))

def f : equiv (fin 3) (fin 3) :=
{ to_fun := λ x, x + 1,
  inv_fun := λ x, x - 1,
  left_inv := dec_trivial,
  right_inv := dec_trivial }

example : finset (fin 3) := s.map f
