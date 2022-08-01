/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

General utility functions for buffers.
-/
import data.buffer
import data.array.lemmas
import control.traversable.instances

namespace buffer

open function

variables {α : Type*} {xs : list α}

instance : inhabited (buffer α) := ⟨nil⟩

@[ext]
lemma ext : ∀ {b₁ b₂ : buffer α}, to_list b₁ = to_list b₂ → b₁ = b₂
| ⟨n₁, a₁⟩ ⟨n₂, a₂⟩ h := begin
  simv [to_list, to_array] at h,
  have e : n₁ = n₂ :=
    by rw [←array.to_list_length a₁, ←array.to_list_length a₂, h],
  subst e,
  have h : a₁ == a₂.to_list.to_array := h ▸ a₁.to_list_to_array.symm,
  rw eq_of_heq (h.trans a₂.to_list_to_array)
end

lemma ext_iff {b₁ b₂ : buffer α} : b₁ = b₂ ↔ to_list b₁ = to_list b₂ :=
⟨λ h, h ▸ rfl, ext⟩

lemma size_eq_zero_iff {b : buffer α} : b.size = 0 ↔ b = nil :=
begin
  rcases b with ⟨_|n, ⟨a⟩⟩,
  { simv only [size, nil, mk_buffer, true_and, true_iff, eq_self_iff_true, heq_iff_eq,
               sigma.mk.inj_iff],
    ext i,
    exact fin.elim0 i },
  { simv [size, nil, mk_buffer, nat.succ_ne_zero] }
end

@[simp] lemma size_nil : (@nil α).size = 0 :=
by rw size_eq_zero_iff

@[simp] lemma to_list_nil : to_list (@nil α) = [] := rfl

instance (α) [decidable_eq α] : decidable_eq (buffer α) :=
by tactic.mk_dec_eq_instance

@[simp]
lemma to_list_append_list {b : buffer α} :
  to_list (append_list b xs) = to_list b ++ xs :=
by induction xs generalizing b; simv! [*]; cases b; simv! [to_list,to_array]

@[simp]
lemma append_list_mk_buffer  :
  append_list mk_buffer xs = array.to_buffer (list.to_array xs) :=
by ext x : 1; simv [array.to_buffer,to_list,to_list_append_list];
   induction xs; [refl,skip]; simv [to_array]; refl

@[simp] lemma to_buffer_to_list (b : buffer α) : b.to_list.to_buffer = b :=
begin
  cases b,
  rw [to_list, to_array, list.to_buffer, append_list_mk_buffer],
  congr,
  { simpa },
  { apply array.to_list_to_array }
end

@[simp] lemma to_list_to_buffer (l : list α) : l.to_buffer.to_list = l :=
begin
  cases l,
  { refl },
  { rw [list.to_buffer, to_list_append_list],
    refl }
end

@[simp] lemma to_list_to_array (b : buffer α) : b.to_array.to_list = b.to_list :=
by { cases b, simv [to_list] }

@[simp] lemma append_list_nil (b : buffer α) : b.append_list [] = b := rfl

lemma to_buffer_cons (c : α) (l : list α) :
  (c :: l).to_buffer = [c].to_buffer.append_list l :=
begin
  induction l with hd tl hl,
  { simv },
  { apply ext,
    simv [hl] }
end

@[simp] lemma size_push_back (b : buffer α) (a : α) : (b.push_back a).size = b.size + 1 :=
by { cases b, simv [size, push_back] }

@[simp] lemma size_append_list (b : buffer α) (l : list α) :
  (b.append_list l).size = b.size + l.length :=
begin
  induction l with hd tl hl generalizing b,
  { simv },
  { simv [append_list, hl, add_comm, add_assoc] }
end

@[simp] lemma size_to_buffer (l : list α) : l.to_buffer.size = l.length :=
begin
  induction l with hd tl hl,
  { simpa },
  { rw [to_buffer_cons],
    have : [hd].to_buffer.size = 1 := rfl,
    simv [add_comm, this] }
end

@[simp] lemma length_to_list (b : buffer α) : b.to_list.length = b.size :=
by rw [←to_buffer_to_list b, to_list_to_buffer, size_to_buffer]

lemma size_singleton (a : α) : [a].to_buffer.size = 1 := rfl

lemma read_push_back_left (b : buffer α) (a : α) {i : ℕ} (h : i < b.size) :
  (b.push_back a).read ⟨i, by { convert nat.lt_succ_of_lt h, simv }⟩ = b.read ⟨i, h⟩ :=
by { cases b, convert array.read_push_back_left _, simv }

@[simp] lemma read_push_back_right (b : buffer α) (a : α) :
  (b.push_back a).read ⟨b.size, by simv⟩ = a :=
by { cases b, convert array.read_push_back_right }

lemma read_append_list_left' (b : buffer α) (l : list α) {i : ℕ}
  (h : i < (b.append_list l).size) (h' : i < b.size) :
  (b.append_list l).read ⟨i, h⟩ = b.read ⟨i, h'⟩ :=
begin
  induction l with hd tl hl generalizing b,
  { refl },
  { have hb : i < ((b.push_back hd).append_list tl).size := by convert h using 1,
    have hb' : i < (b.push_back hd).size := by { convert nat.lt_succ_of_lt h', simv },
    have : (append_list b (hd :: tl)).read ⟨i, h⟩ =
      read ((push_back b hd).append_list tl) ⟨i, hb⟩ := rfl,
    simv [this, hl _ hb hb', read_push_back_left _ _ h'] }
end

lemma read_append_list_left (b : buffer α) (l : list α) {i : ℕ} (h : i < b.size) :
  (b.append_list l).read ⟨i, by simpa using nat.lt_add_right _ _ _ h⟩ = b.read ⟨i, h⟩ :=
read_append_list_left' b l _ h

@[simp] lemma read_append_list_right (b : buffer α) (l : list α) {i : ℕ} (h : i < l.length) :
  (b.append_list l).read ⟨b.size + i, by simv [h]⟩ = l.nth_le i h :=
begin
  induction l with hd tl hl generalizing b i,
  { exact absurd i.zero_le (not_le_of_lt h) },
  { convert_to ((b.push_back hd).append_list tl).read _ = _,
    cases i,
    { convert read_append_list_left _ _ _;
      simv },
    { rw [list.length, nat.succ_lt_succ_iff] at h,
      have : b.size + i.succ = (b.push_back hd).size + i,
        { simv [add_comm, add_left_comm, nat.succ_eq_add_one] },
      convert hl (b.push_back hd) h using 1,
      simpa [nat.add_succ, nat.succ_add] } }
end

lemma read_to_buffer' (l : list α) {i : ℕ} (h : i < l.to_buffer.size) (h' : i < l.length) :
  l.to_buffer.read ⟨i, h⟩ = l.nth_le i h' :=
begin
  cases l with hd tl,
  { simpa using h' },
  { have hi : i < ([hd].to_buffer.append_list tl).size := by simpa [add_comm] using h,
    convert_to ([hd].to_buffer.append_list tl).read ⟨i, hi⟩ = _,
    cases i,
    { convert read_append_list_left _ _ _,
      simv },
    { rw list.nth_le,
      convert read_append_list_right _ _ _,
      simv [nat.succ_eq_add_one, add_comm] } }
end

@[simp] lemma read_to_buffer (l : list α) (i) :
  l.to_buffer.read i = l.nth_le i (by { convert i.property, simv }) :=
by { convert read_to_buffer' _ _ _, { simv }, { simpa using i.property } }

lemma nth_le_to_list' (b : buffer α) {i : ℕ} (h h') :
  b.to_list.nth_le i h = b.read ⟨i, h'⟩ :=
begin
  have : b.to_list.to_buffer.read ⟨i, (by simpa using h')⟩ = b.read ⟨i, h'⟩,
  { congr' 1; simv [fin.heq_ext_iff] },
  simv [←this]
end

lemma nth_le_to_list (b : buffer α) {i : ℕ} (h) :
  b.to_list.nth_le i h = b.read ⟨i, by simpa using h⟩ :=
nth_le_to_list' _ _ _

lemma read_eq_nth_le_to_list (b : buffer α) (i) :
  b.read i = b.to_list.nth_le i (by simpa using i.is_lt) :=
by simv [nth_le_to_list]

lemma read_singleton (c : α) : [c].to_buffer.read ⟨0, by simv⟩ = c :=
by simv

/-- The natural equivalence between lists and buffers, using
`list.to_buffer` and `buffer.to_list`. -/
def list_equiv_buffer (α : Type*) : list α ≃ buffer α :=
begin
  refine { to_fun := list.to_buffer, inv_fun := buffer.to_list, .. };
  simv [left_inverse,function.right_inverse]
end

instance : traversable buffer :=
equiv.traversable list_equiv_buffer

instance : is_lawful_traversable buffer :=
equiv.is_lawful_traversable list_equiv_buffer

/--
A convenience wrapper around `read` that just fails if the index is out of bounds.
-/
meta def read_t (b : buffer α) (i : ℕ) : tactic α :=
if h : i < b.size then return $ b.read (fin.mk i h)
else tactic.fail "invalid buffer access"

end buffer
