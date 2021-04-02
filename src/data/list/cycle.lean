import data.list.rotate
import data.list.erase_dup
import group_theory.perm.sign

namespace list

variables {α β : Type*}

def is_rotated (l l' : list α) : Prop := ∃ n, l.rotate n = l'

infixr ` ~r `:1000 := is_rotated

lemma is_rotated.def {l l' : list α} (h : l ~r l') : ∃ n, l.rotate n = l' := h

lemma is_rotated_iff {l l' : list α} : l ~r l' ↔ ∃ n, l.rotate n = l' := iff.rfl

@[refl] lemma is_rotated.refl (l : list α) : l ~r l :=
⟨0, by simp⟩

@[symm] lemma is_rotated.symm {l l' : list α} (h : l ~r l') : l' ~r l :=
begin
  obtain ⟨n, rfl⟩ := h,
  cases l with hd tl,
  { simp },
  { use (hd :: tl).length * n - n,
    rw [rotate_rotate, nat.add_sub_cancel', rotate_length_mul],
    exact nat.le_mul_of_pos_left (by simp) }
end

lemma is_rotated.symm_iff {l l' : list α} : l ~r l' ↔ l' ~r l :=
⟨is_rotated.symm, is_rotated.symm⟩

@[simp] protected lemma is_rotated.forall (l : list α) (n : ℕ) : l.rotate n ~r l :=
is_rotated.symm ⟨n, rfl⟩

@[trans] lemma is_rotated.trans {l l' l'' : list α} (h : l ~r l') (h' : l' ~r l'') :
  l ~r l'' :=
begin
  obtain ⟨n, rfl⟩ := h.def,
  obtain ⟨m, rfl⟩ := h'.def,
  rw rotate_rotate,
  use (n + m)
end

lemma is_rotated.eqv : equivalence (@is_rotated α) :=
mk_equivalence _ is_rotated.refl (λ _ _, is_rotated.symm) (λ _ _ _, is_rotated.trans)

def is_rotated.setoid : setoid (list α) :=
{ r := is_rotated, iseqv := is_rotated.eqv }

lemma is_rotated.perm {l l' : list α} (h : l ~r l') : l ~ l' :=
exists.elim h (λ _ hl, hl ▸ (rotate_perm _ _).symm)

lemma is_rotated.nodup_iff {l l' : list α} (h : l ~r l') : nodup l ↔ nodup l' :=
h.perm.nodup_iff

lemma nodup.is_rotated {l l' : list α} (h : nodup l) (h' : l ~r l') : nodup l' :=
h'.nodup_iff.mp h

lemma is_rotated.mem_iff {l l' : list α} (h : l ~r l') {a : α} : a ∈ l ↔ a ∈ l' :=
h.perm.mem_iff

@[simp] lemma is_rotated_nil_iff {l : list α} : l ~r [] ↔ l = [] :=
⟨λ ⟨n, hn⟩, by simpa using hn, λ h, h ▸ by refl⟩

@[simp] lemma is_rotated_nil_iff' {l : list α} : [] ~r l ↔ l = [] :=
by rw [is_rotated.symm_iff, is_rotated_nil_iff]

lemma is_rotated_concat (hd : α) (tl : list α) :
  (tl ++ [hd]) ~r (hd :: tl) :=
is_rotated.symm ⟨1, by simp [rotate_cons_succ]⟩

section form_perm

variables [decidable_eq α] (l : list α)

def form_perm : equiv.perm α :=
(zip_with equiv.swap l.erase_dup l.erase_dup.tail).prod

lemma form_perm_rotation_invariant (n : ℕ) :
  form_perm (l.rotate n) = form_perm l :=
sorry

end form_perm

end list

open list

def cycle (α : Type*) : Type* := quotient (@is_rotated.setoid α)

namespace cycle

variables {α β : Type*}

instance : has_coe (list α) (cycle α) := ⟨quot.mk _⟩

@[simp] theorem coe_eq_coe {l₁ l₂ : list α} : (l₁ : cycle α) = l₂ ↔ (l₁ ~r l₂) :=
@quotient.eq _ (is_rotated.setoid) _ _

def mem (a : α) (s : cycle α) : Prop :=
quot.lift_on s (λ l, a ∈ l) (λ l₁ l₂ (e : l₁ ~r l₂), propext $ e.mem_iff)

instance : has_mem α (cycle α) := ⟨mem⟩

end cycle
