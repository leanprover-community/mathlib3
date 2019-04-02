import data.list.basic

universes u v

namespace list

lemma split_on_p_spec' {α : Type u} (p : α → Prop) [decidable_pred p]
  (as : list α) (bs : list (α × list α))
  (w₁ : ∀ a ∈ as, ¬ p a)
  (w₂ : ∀ b : α × list α, b ∈ bs → p b.1)
  (w₃ : ∀ b : α × list α, b ∈ bs → ∀ a ∈ b.2, ¬ p a) :
  split_on_p p (as ++ join (bs.map (λ p, p.1 :: p.2))) = as :: bs.map(prod.snd) :=
sorry

lemma split_on_p_length {α : Type u} (p : α → Prop) [decidable_pred p]
  (as : list α) : (split_on_p p as).length = as.countp p + 1 :=
sorry

lemma split_on_not_mem {α : Type u} [decidable_eq α] (a : α) (as : list α) (h : a ∉ as) :
  as.split_on a = [as] :=
begin
  have q := split_on_p_spec' (=a) as [] _ _ _,
  simpa using q,
  { intros a h' p, subst p, exact h h' },
  { intros b h, cases h },
  { intros b h, cases h },
end

lemma split_on_cons_self {α : Type u} [decidable_eq α] (a : α) (tl : list α) :
  ((a :: tl).split_on a) = [] :: tl.split_on a :=
begin
  rw [split_on, split_on_p, split_on_p_aux, if_pos rfl],
  refl,
end

lemma split_on_spec' {α : Type u} [decidable_eq α] (a : α) (as bs : list α) (h : a ∉ as) :
  (as ++ [a] ++ bs).split_on a = as :: (bs.split_on a) :=
sorry

lemma split_on_spec {α : Type u} [decidable_eq α] (a : α) (as : list α) :
  list.intercalate [a] (as.split_on a) = as :=
begin
  have q := split_on_p_spec (=a) as,
  dsimp [intercalate],
  sorry,
end

end list
