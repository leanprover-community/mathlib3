import data.list.rotate
import data.list.erase_dup
import group_theory.perm.sign
import group_theory.perm.cycles
import tactic.slim_check
import dynamics.fixed_points.basic

open slim_check

lemma set.mem_disjoint_imp {α : Type*} {s t : set α} {x : α} (h : x ∈ s) (hd : disjoint s t) :
  x ∉ t :=
λ ht, hd (set.mem_inter h ht)

lemma set.not_mem_compl_iff {α : Type*} (s : set α) (x : α) : x ∉ sᶜ ↔ x ∈ s := set.not_not_mem

@[simp] lemma function.fixed_points.id {α : Type*} : function.fixed_points (@id α) = set.univ :=
by { ext, simpa using function.is_fixed_pt_id _ }

namespace equiv

variables {α : Type*}

end equiv

namespace list

variables {α β : Type*}

lemma exists_mem_of_ne_nil (l : list α) (h : l ≠ []) : ∃ x, x ∈ l :=
exists_mem_of_length_pos (length_pos_of_ne_nil h)

lemma ne_singleton_iff_of_nodup {l : list α} (h : nodup l) (x : α) :
  l ≠ [x] ↔ l = [] ∨ ∃ y ∈ l, y ≠ x :=
begin
  induction l with hd tl hl,
  { simp },
  { specialize hl (nodup_of_nodup_cons h),
    by_cases hx : tl = [x],
    { simpa [hx, and.comm, and_or_distrib_left] using h },
    { rw [←ne.def, hl] at hx,
      rcases hx with rfl | ⟨y, hy, hx⟩,
      { simp },
      { have : tl ≠ [] := ne_nil_of_mem hy,
        suffices : ∃ (y : α) (H : y ∈ hd :: tl), y ≠ x,
          { simpa [ne_nil_of_mem hy] },
        exact ⟨y, mem_cons_of_mem _ hy, hx⟩ } } }
end

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

@[elab_as_eliminator]
def reverse_induction
  {C : list α → Sort*}
  (hn : C [])
  (ha : ∀ (xs : list α) (x : α), C xs → C (xs ++ [x])) :
  Π (l : list α), C l :=
begin
  intro l,
  induction h : l.reverse with hd tl hl generalizing l,
  { simp only [reverse_eq_nil] at h,
    rwa h },
  { have : l = tl.reverse ++ [hd] := by simpa using congr_arg list.reverse h,
    rw this,
    apply ha,
    apply hl,
    simp }
end

@[elab_as_eliminator]
def reverse_induction_on (l : list α) {C : list α → Sort*}
  (hn : C [])
  (ha : ∀ (xs : list α) (x : α), C xs → C (xs ++ [x])) :
  C l :=
reverse_induction hn ha l

@[elab_as_eliminator]
def bidirection_induction
  {C : list α → Sort*}
  (hn : C [])
  (hs : ∀ (x : α), C [x])
  (hca : ∀ (x : α) (xs : list α) (y : α), C (x :: xs) → C (x :: (xs ++ [y]))) :
  Π (l : list α), C l :=
begin
  intro l,
  induction l using list.reverse_induction with xs y IH,
  { exact hn },
  { cases xs with x xs,
    { simpa using hs y },
    { rw cons_append,
      apply hca,
      exact IH } }
end

section form_perm

variables [decidable_eq α] (l : list α)

open equiv equiv.perm

@[simp] lemma zip_with_rotate_one (f : α → α → β) (x y : α) (l : list α) :
  zip_with f (x :: y :: l) ((x :: y :: l).rotate 1) =
  f x y :: zip_with f (y :: l) (l ++ [x]) :=
by simp [rotate_cons_succ]

instance {α : Type*} : mul_action (equiv.perm α) α :=
{ smul := λ e x, e x,
  one_smul := λ _, by simp,
  mul_smul := λ _, by simp }

def form_perm : equiv.perm α :=
(zip_with equiv.swap l (l.rotate 1)).tail.prod

@[simp] lemma form_perm_nil : form_perm ([] : list α) = 1 := rfl

@[simp] lemma form_perm_singleton (x : α) : form_perm [x] = 1 := rfl

-- lemma form_perm_cons_cons (x y : α) (h : nodup (x :: y :: l)) :
--   form_perm (x :: y :: l) = swap y x * form_perm l :=
-- begin
--   induction l with hd tl generalizing x y,
--   { simp [form_perm] },
--   { simp [form_perm], },
-- end


lemma form_perm_rotation_invariant (n : ℕ) (l : list α) (h : nodup l) :
  form_perm (l.rotate n) = form_perm l :=
begin
  -- induction l using list.bidirection_induction with x x xs y IH generalizing n,
  -- { simp },
  -- { simp },
  -- {  },
  -- induction l with hd tl hl generalizing n,
  -- { simp },
  -- { cases tl with hd' tl,
  --   simp,
  --   simp,
  -- },
end
#exit


lemma form_perm_apply_head (hd : α) (tl : list α) (h : nodup (tl ++ [hd])) :
  form_perm (tl ++ [hd]) hd = (tl ++ [hd]).nth_le 0 (by simp) :=
begin
  induction tl using list.reverse_induction with tl hd' hl generalizing hd,
  { simp },
  { rw [form_perm, ←zip_with_tail_comm, tail_cons, rotate_cons_succ, rotate_zero], },
end

lemma is_cycle_form_perm (l : list α) (x y : α) (h : nodup (x :: y :: l)) :
  is_cycle (form_perm (x :: y :: l)) :=
begin
  use x,
  simp,
  -- simp [form_perm, zip_with_rotate_one],
  -- induction l with hd tl hl generalizing x y,
  -- { simp at h,
  --   simpa using is_cycle.swap (ne.symm h) },
  -- { simp,
  --   specialize hl x hd _,
  --   { simp only [mem_cons_iff, nodup_cons] at h ⊢,
  --     refine ⟨_, h.right.right⟩,
  --     push_neg at h ⊢,
  --     exact h.left.right },
  -- },
end

lemma is_cycle_form_perm' {x y : α} (h : x ≠ y) (l : list α) :
  is_cycle (form_perm (l ++ [x, y]).erase_dup) :=
begin
  induction l with hd tl hl generalizing x y,
  { simpa [←erase_dup_eq_self, h, form_perm] using is_cycle.swap h },
  { by_cases hm : hd ∈ (tl ++ [x, y]),
    { simpa [hm] using hl h },
    { simp [hm],
      rw form_perm,
      simp,


    },
  },
end

lemma form_perm_rotation_invariant (n : ℕ) (l : list ℕ) (x : ℕ) :
  form_perm (l.erase_dup.rotate n) x = form_perm l.erase_dup x :=
by slim_check


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
