import data.list.basic
import tactic.vampire.misc

namespace list

variables {α β : Type}

lemma exists_mem_append {p : α → Prop} {l₁ l₂ : list α} :
  (∃ x ∈ l₁ ++ l₂, p x) ↔ (∃ x ∈ l₁, p x) ∨ (∃ x ∈ l₂, p x) :=
begin
  constructor; intro h0,
  { rcases h0 with ⟨a, h1, h2⟩,
    rw list.mem_append at h1, cases h1,
    { left, refine ⟨_, h1, h2⟩ },
    right, refine ⟨_, h1, h2⟩ },
  cases h0; rcases h0 with ⟨a, h1, h2⟩;
  refine ⟨a, _, h2⟩; rw list.mem_append;
  [left, right]; assumption
end

def rot : nat → list α → list α
| _ [] := []
| 0 (a :: as) := (a :: as)
| (k + 1) (a :: as) :=
  match (rot k as) with
  | [] := (a :: as)
  | (a' :: as') := (a' :: a :: as')
  end

lemma mem_rot {a : α} :
  ∀ {as : list α}, ∀ k : nat, a ∈ as → a ∈ rot k as
| [] _ h0 := by cases h0
| (b :: as) 0 h0 := h0
| (b :: as) (k + 1) h0 :=
  begin
    cases h0; unfold rot;
    cases h1 : (rot k as) with b' as',
    { left, assumption },
    { right, left, assumption },
    { right, assumption },
    have h2 := mem_rot _ h0,
    rw h1 at h2, cases h2,
    { left, assumption },
    right, right, assumption
  end

lemma exists_mem_map_iff
  {p : α → Prop} {q : β → Prop} {f : α → β}
  (h : ∀ a : α, q (f a) ↔ p a) :
  ∀ as : list α,
  ((∃ b ∈ as.map f, q b) ↔ (∃ a ∈ as, p a))
| []        := by constructor; rintro ⟨_, ⟨_⟩, _⟩
| (a :: as) :=
  begin
    rw [list.map_cons],
    simp only [list.exists_mem_cons_iff],
    apply pred_mono_2 (h _),
    apply exists_mem_map_iff
  end

end list
