
variables {α : Sort*} (op : α → α)

@[simp] theorem iterate_zero : op^[0] = id := rfl

theorem iterate_zero_apply (x : α) : op^[0] x = x := rfl

@[simp] theorem iterate_succ (n : ℕ) : op^[succ n] = (op^[n]) ∘ op := rfl

theorem iterate_succ_apply (n : ℕ) (x : α) : op^[succ n] x = (op^[n]) (op x) := rfl

theorem iterate_add : ∀ (m n : ℕ), op^[m + n] = (op^[m]) ∘ (op^[n])
| m 0 := rfl
| m (succ n) := by rw [iterate_succ, iterate_succ, iterate_add]

theorem iterate_add_apply (m n : ℕ) (x : α) : op^[m + n] x = (op^[m] (op^[n] x)) :=
by rw iterate_add

@[simp] theorem iterate_one : op^[1] = op := funext $ λ a, rfl

theorem iterate_succ' (n : ℕ) : op^[succ n] = op ∘ (op^[n]) :=
by rw [← one_add, iterate_add, iterate_one]

theorem iterate_succ_apply' (n : ℕ) (x : α) : op^[succ n] x = op (op^[n] x) :=
by rw [iterate_succ']

lemma iterate_mul (m : ℕ) : ∀ n, op^[m * n] = (op^[m]^[n])
| 0 := by { ext a, simp only [mul_zero, iterate_zero] }
| (n + 1) := by { ext x, simp only [mul_add, mul_one, iterate_one, iterate_add, iterate_mul n] }

@[elab_as_eliminator]
theorem iterate_ind {α : Type u} (f : α → α) {p : (α → α) → Prop} (hf : p f) (hid : p id)
  (hcomp : ∀ ⦃f g⦄, p f → p g → p (f ∘ g)) :
  ∀ n, p (f^[n])
| 0 := hid
| (n+1) := hcomp (iterate_ind n) hf

theorem iterate₀ {α : Type u} {op : α → α} {x : α} (H : op x = x) {n : ℕ} :
  op^[n] x = x :=
by induction n; [simp only [iterate_zero_apply], simp only [iterate_succ_apply', H, *]]

theorem iterate₁ {α : Type u} {β : Type v} {op : α → α} {op' : β → β} {op'' : α → β}
  (H : ∀ x, op' (op'' x) = op'' (op x)) {n : ℕ} {x : α} :
  op'^[n] (op'' x) = op'' (op^[n] x) :=
by induction n; [simp only [iterate_zero_apply], simp only [iterate_succ_apply', H, *]]

theorem iterate₂ {α : Type u} {op : α → α} {op' : α → α → α}
  (H : ∀ x y, op (op' x y) = op' (op x) (op y)) {n : ℕ} {x y : α} :
  op^[n] (op' x y) = op' (op^[n] x) (op^[n] y) :=
by induction n; [simp only [iterate_zero_apply], simp only [iterate_succ_apply', H, *]]

theorem iterate_cancel {α : Type u} {op op' : α → α} (H : ∀ x, op (op' x) = x) {n : ℕ} {x : α} :
  op^[n] (op'^[n] x) = x :=
by induction n; [refl, rwa [iterate_succ_apply, iterate_succ_apply', H]]

theorem injective.iterate {α : Type u} {op : α → α} (Hinj : injective op) :
  ∀ n, injective (op^[n]) :=
nat.iterate_ind op Hinj injective_id $ λ _ _, injective.comp

theorem surjective.iterate {α : Type u} {op : α → α} (Hinj : surjective op) :
  ∀ n, surjective (op^[n]) :=
nat.iterate_ind op Hinj surjective_id $ λ _ _, surjective.comp

theorem bijective.iterate {α : Type u} {op : α → α} (Hinj : bijective op) :
  ∀ n, bijective (op^[n]) :=
nat.iterate_ind op Hinj bijective_id $ λ _ _, bijective.comp

