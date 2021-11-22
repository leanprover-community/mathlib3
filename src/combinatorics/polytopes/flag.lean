import order.zorn category_theory.conj

open category_theory

universe u

/-- A flag is a maximal chain. -/
@[reducible] def flag (α : Type u) [has_le α] : Type u :=
{c : set α // @zorn.is_max_chain α (≤) c}

namespace flag

instance (α : Type u) [has_le α] : has_mem α (flag α) :=
⟨λ a Φ, a ∈ Φ.val⟩

variables {α : Type u}

instance [has_le α] (Φ : flag α) : has_le Φ :=
⟨λ a b, a.val ≤ b.val⟩

instance [has_le α] [has_lt α] (Φ : flag α) : has_lt Φ :=
⟨λ a b, a.val < b.val⟩

/-- Any two elements of a flag are comparable. -/
protected theorem le_total [preorder α] : ∀ (Φ : flag α) (x y : Φ), x ≤ y ∨ y ≤ x :=
begin
  rintros ⟨_, hΦ, _⟩ x y,
  by_cases heq : x = y,
    { exact or.inl (le_of_eq heq) },
    { cases x with x hx, cases y with y hy,
      rw subtype.mk_eq_mk at heq,
      exact hΦ x hx y hy heq }
end

/-- `<` is trichotomous for partially ordered flags. -/
instance [partial_order α] (Φ : flag α) : is_trichotomous Φ (<) :=
begin
  refine ⟨λ x y, _⟩,
  by_cases heq : x = y, { exact or.inr (or.inl heq) },
  simp_rw lt_iff_le_and_ne,
  cases Φ.le_total x y with hle hle,
    { exact or.inl ⟨hle, heq⟩ },
    { exact or.inr (or.inr ⟨hle, ne.symm heq⟩) },
end

@[priority 900] -- lower priority in case subtype.linear_order comes up with something computable
noncomputable instance [partial_order α] (Φ : flag α) : linear_order Φ :=
{ le_total := Φ.le_total,
  decidable_le := classical.dec_rel (≤),
  ..subtype.partial_order _ }

/-- An element is in a flag iff it is comparable to everything in it. -/
lemma mem_flag_iff_comp [preorder α] (Φ : flag α) (a : α) : a ∈ Φ ↔ ∀ b : Φ, a ≤ ↑b ∨ ↑b ≤ a :=
begin
  refine ⟨λ ha _, Φ.le_total ⟨a, ha⟩ _, λ hh, _⟩,
  by_contra,
  refine Φ.prop.right ⟨set.insert a Φ, _, set.ssubset_insert h⟩,
  exact zorn.chain_insert Φ.prop.left (λ _ hbΦ _, hh ⟨_, hbΦ⟩)
end

end flag
