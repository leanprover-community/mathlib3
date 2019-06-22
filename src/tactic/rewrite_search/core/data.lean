import tactic.rewrite_all

universe u

@[derive decidable_eq]
structure sided_pair (α : Type u) :=
  (l r : α)
namespace sided_pair
variables {α β : Type} (p : sided_pair α)

def get : side → α
| side.L := p.l
| side.R := p.r

def set : side → α → sided_pair α
| side.L v := ⟨v, p.r⟩
| side.R v := ⟨p.l, v⟩

def flip : sided_pair α := ⟨p.r, p.l⟩

def map (f : α → β) : sided_pair β := ⟨f p.l, f p.r⟩

def to_list : list α := [p.l, p.r]

def to_string [has_to_string α] (p : sided_pair α) : string :=
  to_string p.l ++ "-" ++ to_string p.r
instance has_to_string [has_to_string α] : has_to_string (sided_pair α) := ⟨to_string⟩

end sided_pair