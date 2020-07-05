import logic.unique
import tactic.localized
import tactic.push_neg

variables {α : Type*} {β : Type*}

open_locale classical

/-- Predicate typeclass for expressing that a type is not reduced to a single element. In rings,
this is equivalent to `0 ≠ 1`. In vector spaces, this is equivalent to positive dimension. -/
class nontrivial (α : Type*) : Prop :=
(exists_ne : ∃ (x y : α), x ≠ y)

lemma exists_ne (α : Type*) [nontrivial α] :
  ∃ (x y : α), x ≠ y :=
nontrivial.exists_ne

instance nontrivial.to_nonempty {α : Type*} [H : nontrivial α] : nonempty α :=
let ⟨x, _⟩ := exists_ne α in ⟨x⟩

lemma nontrivial_of_ne (x y : α) (h : x ≠ y) : nontrivial α :=
{ exists_ne := ⟨x, y, h⟩ }

/-- An inhabited type is either nontrivial, or has a unique element. -/
noncomputable def nontrivial_psum_unique (α : Type*) [inhabited α] :
  psum (nontrivial α) (unique α) :=
if h : nontrivial α then psum.inl h else psum.inr
{ default := default α,
  uniq := λ (x : α),
  begin
    change x = default α,
    contrapose! h,
    use [x, default α]
  end }

/-- A type is either a subsingleton or nontrivial. -/
lemma subsingleton_or_nontrivial (α : Type*) :  subsingleton α ∨ nontrivial α :=
begin
  classical,
  by_cases h : nontrivial α,
  { right, exact h },
  { left, constructor, assume x y, contrapose! h, exact nontrivial_of_ne x y h },
end

instance nontrivial_prod_left [nontrivial α] [nonempty β] : nontrivial (α × β) :=
begin
  inhabit β,
  rcases exists_ne α with ⟨x, y, h⟩,
  use [(x, default β), (y, default β)],
  contrapose! h,
  exact congr_arg prod.fst h
end

instance nontrivial_prod_right [nontrivial α] [nonempty β] : nontrivial (β × α) :=
begin
  inhabit β,
  rcases exists_ne α with ⟨x, y, h⟩,
  use [(default β, x), (default β, y)],
  contrapose! h,
  exact congr_arg prod.snd h
end

instance option.nontrivial [nonempty α] : nontrivial (option α) :=
by { inhabit α, use [none, some (default α)] }
