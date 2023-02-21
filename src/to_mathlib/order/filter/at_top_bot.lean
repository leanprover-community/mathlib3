import order.filter.at_top_bot

open finset filter set
variables {ι α β : Type*}

lemma at_top_dual_eq_at_bot [preorder α] :
  (at_top : filter αᵒᵈ).map order_dual.of_dual = (at_bot : filter α) := rfl
lemma at_bot_dual_eq_at_top [preorder α] :
  (at_bot : filter αᵒᵈ).map order_dual.of_dual = (at_top : filter α) := rfl

lemma tendsto_at_top_at_bot_of_antitone [preorder α] [preorder β] {f : α → β} (hf : antitone f)
  (h : ∀ b, ∃ a, f a ≤ b) :
  tendsto f at_top at_bot :=
begin
  rw [←at_bot_dual_eq_at_top, tendsto_map'_iff],
  exact tendsto_at_bot_at_bot_of_monotone hf.dual_left h,
end

lemma tendsto_at_bot_at_top_of_antitone [preorder α] [preorder β] {f : α → β} (hf : antitone f)
  (h : ∀ b, ∃ a, b ≤ f a) :
  tendsto f at_bot at_top :=
begin
  rw [←at_top_dual_eq_at_bot, tendsto_map'_iff],
  exact tendsto_at_top_at_top_of_monotone hf.dual_left h,
end

lemma tendsto_at_top_at_bot_iff_of_antitone [nonempty α] [semilattice_sup α] [preorder β]
  {f : α → β} (hf : antitone f) :
  tendsto f at_top at_bot ↔ ∀ b : β, ∃ a : α, f a ≤ b :=
tendsto_at_top_at_bot.trans $ forall_congr $ λ b, exists_congr $ λ a,
  ⟨λ h, h a (le_refl a), λ h a' ha', le_trans (hf ha') h⟩

lemma tendsto_at_bot_at_top_iff_of_antitone [nonempty α] [semilattice_inf α] [preorder β]
  {f : α → β} (hf : antitone f) :
  tendsto f at_bot at_top ↔ ∀ b : β, ∃ a : α, b ≤ f a :=
tendsto_at_bot_at_top.trans $ forall_congr $ λ b, exists_congr $ λ a,
  ⟨λ h, h a (le_refl a), λ h a' ha', le_trans h (hf ha')⟩

alias tendsto_at_top_at_bot_of_antitone ← _root_.antitone.tendsto_at_top_at_bot
alias tendsto_at_bot_at_top_of_antitone ← _root_.antitone.tendsto_at_bot_at_top
alias tendsto_at_top_at_bot_iff_of_antitone ← _root_.antitone.tendsto_at_top_at_bot_iff
alias tendsto_at_bot_at_top_iff_of_antitone ← _root_.antitone.tendsto_at_bot_at_top_iff

/-- If `u` is an antitone function with linear ordered codomain and the range of `u` is not bounded
below, then `tendsto u at_top at_bot`. -/
lemma tendsto_at_top_at_bot_of_antitone' [preorder ι] [linear_order α]
  {u : ι → α} (h : antitone u) (H : ¬bdd_below (range u)) :
  tendsto u at_top at_bot :=
begin
  apply h.tendsto_at_top_at_bot,
  intro b,
  rcases not_bdd_below_iff.1 H b with ⟨_, ⟨N, rfl⟩, hN⟩,
  exact ⟨N, le_of_lt hN⟩
end
