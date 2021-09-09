import data.finset.basic

/-!
## Miscellaneous examples

Please don't add further content to this file;
it too easily becomes a grab bag of forgotten arcana.

Tactics should have their own file in the `test/` directory.

Examples verifying correct behaviour of simp sets or instances
belong in `src/` near the definitions.

TODO: remove or move the remaining content of this file.
-/

open tactic

universe u
variable {α : Type u}

example (s t u : set ℕ) (h : s ⊆ t ∩ u) (h' : u ⊆ s) : u ⊆ s → true :=
begin
  dunfold has_subset.subset has_inter.inter at *,
--  trace_state,
  intro1, triv
end

example (s t u : set ℕ) (h : s ⊆ t ∩ u) (h' : u ⊆ s) : u ⊆ s → true :=
begin
  delta has_subset.subset has_inter.inter at *,
--  trace_state,
  intro1, triv
end

example (x y z : ℕ) (h'' : true) (h : 0 + y = x) (h' : 0 + y = z) : x = z + 0 :=
begin
  simp at *,
--  trace_state,
  rw [←h, ←h']
end

example (x y z : ℕ) (h'' : true) (h : 0 + y = x) (h' : 0 + y = z) : x = z + 0 :=
begin
  simp at *,
  simp [h] at h',
  simp [*]
end

def my_id (x : α) := x

def my_id_def (x : α) : my_id x = x := rfl

example (x y z : ℕ) (h'' : true) (h : 0 + my_id y = x) (h' : 0 + y = z) : x = z + 0 :=
begin
  simp [my_id_def] at *, simp [h] at h', simp [*]
end

@[simp] theorem mem_set_of {a : α} {p : α → Prop} : a ∈ {a | p a} = p a := rfl

meta example : true :=
begin
   success_if_fail { let := elim_gen_sum_aux },
   trivial
end

import_private elim_gen_sum_aux

meta example : true :=
begin
  let := elim_gen_sum_aux,
  trivial
end


/- tests of has_sep on finset -/

example {α} (s : finset α) (p : α → Prop) [decidable_pred p] : {x ∈ s | p x} = s.filter p :=
by simp

example {α} (s : finset α) (p : α → Prop) [decidable_pred p] :
  {x ∈ s | p x} = @finset.filter α p (λ _, classical.prop_decidable _) s :=
by simp

section
open_locale classical

example {α} (s : finset α) (p : α → Prop) : {x ∈ s | p x} = s.filter p :=
by simp

example (n m k : ℕ) : {x ∈ finset.range n | x < m ∨ x < k } =
  {x ∈ finset.range n | x < m } ∪ {x ∈ finset.range n | x < k } :=
by simp [finset.filter_or]

end
