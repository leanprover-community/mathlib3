import data.multiset data.equiv.basic
#exit
open equiv.perm equiv multiset

variables {α : Type*} {β : Type*} [decidable_eq α]

def perm.cons (e : α ≃ β) (m : multiset α) (a : α) (b : β) (f : α ≃ β) : α ≃ β :=
(swap a (e.symm b)).trans f

def list_to_function : Π (l₁ : list α) (l₂ : list β), l₁.length = l₂.length → Π a ∈ l₁, β
| []      l₂      h₁ a h₂ := absurd h₂ (list.not_mem_nil _)
| (b::l₁) []      h₁ a h₂ := absurd h₁ (nat.succ_ne_zero _)
| (b::l₁) (c::l₂) h₁ a h₂ := if h : a = b then c
  else list_to_function l₁ l₂ (nat.succ_inj h₁) a (list.mem_of_ne_of_mem h h₂)

open list nat

def list_to_perm : Π (l₁ : list α) (l₂ : list β), l₁.length = l₂.length →
  {a // a ∈ l₁} ≃ {b // b ∈ l₂}
| []      []      h := ⟨λ a, (not_mem_nil _ a.2).elim, λ b, (not_mem_nil _ b.2).elim,
  λ a, (not_mem_nil _ a.2).elim, λ b, (not_mem_nil _ b.2).elim⟩
| []      (b::l₂) h := (succ_ne_zero _ h.symm).elim
| (a::l₁) []      h := (succ_ne_zero _ h).elim
| (a::l₁) (b::l₂) h :=
let f := list_to_perm l₁ l₂ (succ_inj h) in
{ to_fun := λ x, if h : x.1 = a then ⟨b, list.mem_cons_self _ _⟩
            else ⟨(f ⟨x, mem_of_ne_of_mem h x.2⟩).1, mem_cons_of_mem _ begin end⟩  }

def multiset.perm (m : multiset α) (t : multiset β) : multiset (α ≃ β) :=
multiset.rec_on m (e :: 0)
  (λ a m ih, m.bind (λ b, ih.map (λ f, begin end)))
  (λ x y s t, heq_of_eq begin
    simp [multiset.map_bind, bind_bind, swap_comm],
    rw [bind_map_comm],

  end)