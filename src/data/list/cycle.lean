import data.list.rotate
import group_theory.perm.sign

open list

variables {α β : Type*}

def is_rotated (l l' : list α) : Prop := ∃ n, l.rotate n = l'

notation l ` ~r ` l' := is_rotated l l'

lemma is_rotated.def {l l' : list α} (h : l ~r l') : ∃ n, l.rotate n = l' := h

@[refl] lemma is_rotated.refl (l : list α) : l ~r l :=
⟨0, by simp⟩

@[symm] lemma is_rotated.symm {l l' : list α} (h : l ~r l') :
  l' ~r l :=
begin
  obtain ⟨n, rfl⟩ := h.def,
  use l.length - n % l.length,
  cases l.length.zero_le.eq_or_lt with hl hl,
  { simp [eq_nil_of_length_eq_zero hl.symm] },
  { rw [rotate_rotate, ←rotate_mod, nat.add_mod, ←nat.add_mod,
      ←nat.add_sub_assoc (nat.mod_lt _ hl).le, nat.sub_mod_eq_zero_of_mod_eq,
      rotate_zero],
    simp }
end

lemma is_rotated.symm_iff {l l' : list α} : (l ~r l') ↔ (l' ~r l) :=
⟨is_rotated.symm, is_rotated.symm⟩

@[simp] lemma is_rotated.forall (l : list α) (n : ℕ) : l.rotate n ~r l :=
is_rotated.symm ⟨n, rfl⟩

@[trans] lemma is_rotated.trans {l l' l'' : list α} (h : l ~r l') (h' : l' ~r l'') :
  l ~r l'' :=
begin
  obtain ⟨n, rfl⟩ := h.def,
  obtain ⟨m, rfl⟩ := h'.def,
  refine is_rotated.symm _,
  simp [rotate_rotate]
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

@[simp] lemma is_rotated_nil_iff {l : list α} : (l ~r []) ↔ l = [] :=
⟨λ ⟨n, hn⟩, by simpa using hn, λ h, h ▸ by refl⟩

@[simp] lemma is_rotated_nil_iff' {l : list α} : ([] ~r l) ↔ l = [] :=
by rw [is_rotated.symm_iff, is_rotated_nil_iff]

lemma is_rotated_concat (hd : α) (tl : list α) :
  tl ++ [hd] ~r hd :: tl :=
is_rotated.symm ⟨1, by simp [rotate_cons_succ]⟩

lemma is_rotated.foldr_eq {f : α → β → β} {l₁ l₂ : list α} (lcomm : left_commutative f)
  (p : l₁ ~r l₂) :
  ∀ b, foldr f b l₁ = foldr f b l₂ :=
perm_induction_on p
  (λ b, rfl)
  (λ x t₁ t₂ p r b, by simp; rw [r b])
  (λ x y t₁ t₂ p r b, by simp; rw [lcomm, r b])
  (λ t₁ t₂ t₃ p₁ p₂ r₁ r₂ a, eq.trans (r₁ a) (r₂ a))

def cycle (α : Type*) : Type* := quotient (@is_rotated.setoid α)

section cycle_zip_with

variables [decidable_eq α] (l : list α) (f : α → α → β)

def list.cycle_zip_with : list β :=
if h : l = [] then [] else zip_with f (l.last h :: l) l

@[simp] lemma list.cycle_zip_with_nil : list.cycle_zip_with [] f = [] := rfl

@[simp] lemma list.cycle_zip_with_eq_nil_iff {l : list α} {f : α → α → β} :
  list.cycle_zip_with l f = [] ↔ l = [] :=
begin
  rw [list.cycle_zip_with],
  split_ifs with h,
  { simp [h] },
  { simp }
end

end cycle_zip_with

lemma list.cycle_zip_with_rotate_is_rotated [decidable_eq α] (l : list α) (f : α → α → β) (n : ℕ) :
  (l.rotate n).cycle_zip_with f ~r (l.cycle_zip_with f) :=
begin
  induction n with n hn generalizing l,
  { simp },
  { cases l with hd tl,
    { simp },
    { rw [rotate_cons_succ],
      refine (hn _).trans _,
      suffices : is_rotated (zip_with f (hd :: (tl ++ [hd])) (tl ++ [hd]))
        (f ((hd :: tl).last (by simp)) hd :: zip_with f (hd :: tl) tl),
        { simpa [list.cycle_zip_with] },
      refine is_rotated.trans _ (is_rotated_concat _ _),
      convert is_rotated.refl _,
      apply list.ext,
      intro n,
      rw ←cons_append,
      have l0 : tl.length ≤ (hd :: tl).length := by simp,
      rcases lt_trichotomy (hd :: tl).length n with hn|rfl|hn,
      { have : tl.length < n,
          { refine nat.lt_of_succ_lt _,
            simpa using hn },
        obtain ⟨k, hk⟩ : ∃ k, n - tl.length = k + 2,
          { convert nat.exists_eq_add_of_lt hn,
            ext,
            rw [nat.sub_eq_iff_eq_add this.le],
            simp [add_comm, add_assoc, add_left_comm, bit0] },
        rw [nth_append_right, length_zip_with, min_eq_right l0, nth_zip_with,
            nth_append_right hn.le],
        { simp [nat.sub_succ, hk] },
        { simpa using this.le } },
      { rw [nth_append_right, length_zip_with, min_eq_right l0, nth_zip_with, nth_append_right,
            nth_append_right];
        simp, },
      { rcases (nat.le_of_lt_succ hn).eq_or_lt with rfl|H,
        { rw [nth_append_right, length_zip_with, min_eq_right l0, nth_zip_with, nth_append,
              nth_append_right (le_refl _)];
          simp [last_eq_nth_le, nth_le_nth] },
        { rw [nth_append, nth_zip_with, nth_zip_with, nth_append hn, nth_append H],
          simpa } } } }
end

lemma is_rotated.cycle_zip_with [decidable_eq α] {l l' : list α} (h : l ~r l') (f : α → α → β) :
  (l.cycle_zip_with f ~r (l'.cycle_zip_with f)) :=
begin
  obtain ⟨n, rfl⟩ := h.def,
  exact (list.cycle_zip_with_rotate_is_rotated _ _ _).symm
end

namespace cycle

instance : has_coe (list α) (cycle α) := ⟨quot.mk _⟩

@[simp] theorem coe_eq_coe {l₁ l₂ : list α} : (l₁ : cycle α) = l₂ ↔ (l₁ ~r l₂) :=
@quotient.eq _ (is_rotated.setoid) _ _

def mem (a : α) (s : cycle α) : Prop :=
quot.lift_on s (λ l, a ∈ l) (λ l₁ l₂ (e : l₁ ~r l₂), propext $ e.mem_iff)

instance : has_mem α (cycle α) := ⟨mem⟩

variables (l : list α) (f : α → α → β) (b : β)

/-- `fold f H b s` is the lift of the list operation `foldr f b l`,
  which fold `f` over the cycle. It is well defined when `f` is commutative,
  that is, `f a₁ (f a₂ b) = f a₂ (f a₁ b)`. -/
def fold [decidable_eq α] [monoid β] (f : α → α → β) (b : β) (s : cycle α) : β :=
quot.lift_on s (λ l, (list.cycle_zip_with l f).foldr (*) b)
  (λ l₁ l₂ p, (p.cycle_zip_with f).perm.foldr_eq mul_left_comm b)

def equiv.perm.cycle [decidable_eq α] (s : cycle α) : equiv.perm α := s.fold (equiv.swap) 1


end cycle
