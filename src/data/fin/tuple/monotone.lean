import data.fin.vec_notation

/-!
-/

open set fin matrix function
variables {α : Type*}

lemma lift_fun_vec_cons {n : ℕ} (r : α → α → Prop) [is_trans α r] {f : fin (n + 1) → α} {a : α} :
  ((<) ⇒ r) (vec_cons a f) (vec_cons a f) ↔ r a (f 0) ∧ ((<) ⇒ r) f f :=
by simp only [lift_fun_iff_succ r, forall_fin_succ, cons_val_succ, cons_val_zero, ← succ_cast_succ,
  cast_succ_zero]

variables [preorder α] {n : ℕ} {f : fin (n + 1) → α} {a : α}

@[simp] lemma strict_mono_vec_cons : strict_mono (vec_cons a f) ↔ a < f 0 ∧ strict_mono f :=
lift_fun_vec_cons (<)

@[simp] lemma monotone_vec_cons : monotone (vec_cons a f) ↔ a ≤ f 0 ∧ monotone f :=
by simpa only [monotone_iff_forall_lt] using @lift_fun_vec_cons α n (≤) _ f a

@[simp] lemma strict_anti_vec_cons : strict_anti (vec_cons a f) ↔ f 0 < a ∧ strict_anti f :=
lift_fun_vec_cons (>)

@[simp] lemma antitone_vec_cons : antitone (vec_cons a f) ↔ f 0 ≤ a ∧ antitone f :=
@monotone_vec_cons αᵒᵈ _ _ _ _

lemma strict_mono.vec_cons (hf : strict_mono f) (ha : a < f 0) :
  strict_mono (vec_cons a f) :=
strict_mono_vec_cons.2 ⟨ha, hf⟩

lemma strict_anti.vec_cons (hf : strict_anti f) (ha : f 0 < a) :
  strict_anti (vec_cons a f) :=
strict_anti_vec_cons.2 ⟨ha, hf⟩

lemma monotone.vec_cons (hf : monotone f) (ha : a ≤ f 0) :
  monotone (vec_cons a f) :=
monotone_vec_cons.2 ⟨ha, hf⟩

lemma antitone.vec_cons (hf : antitone f) (ha : f 0 ≤ a) :
  antitone (vec_cons a f) :=
antitone_vec_cons.2 ⟨ha, hf⟩

variables (α)

lemma fin.exists_strict_mono_of_no_min [nonempty α] [no_min_order α] :
  ∀ n, ∃ f : fin n → α, strict_mono f
| 0 := ⟨fin.elim0, fin.elim0⟩
| 1 := let ⟨x⟩ := ‹nonempty α› in ⟨const _ x, subsingleton.strict_mono _⟩
| (n + 2) := let ⟨f, hf⟩ := fin.exists_strict_mono_of_no_min (n + 1), ⟨a, ha⟩ := exists_lt (f 0)
  in ⟨vec_cons a f, hf.vec_cons ha⟩

lemma fin.exists_strict_anti_of_no_max [nonempty α] [no_max_order α] (n : ℕ) :
  ∃ f : fin n → α, strict_anti f :=
fin.exists_strict_mono_of_no_min αᵒᵈ n

lemma fin.exists_strict_mono_of_no_max [nonempty α] [no_max_order α] (n : ℕ) :
  ∃ f : fin n → α, strict_mono f :=
let ⟨f, hf⟩ := fin.exists_strict_anti_of_no_max α n in ⟨f ∘ reverse, hf.comp strict_anti_reverse⟩

lemma fin.exists_strict_anti_of_no_min [nonempty α] [no_min_order α] (n : ℕ) :
  ∃ f : fin n → α, strict_anti f :=
fin.exists_strict_mono_of_no_max αᵒᵈ n
