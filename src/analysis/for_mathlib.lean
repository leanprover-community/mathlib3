import data.set.basic
import data.list.basic
import data.list.pairwise
import data.list.destutter
import data.set.function
import data.finset.sort

open set

variables {α β : Type*} (x : α)

lemma subtype.map_id_comp_id (α : Type*) (r s t : α → Prop)
  (rs : ∀ x, r x → s x) (st : ∀ x, s x → t x) :
  (subtype.map id st) ∘ (subtype.map id rs) = (subtype.map id $ λ x, (st x) ∘ (rs x)) :=
funext (λ _, rfl)

lemma subtype.coe_comp_map_id (α : Type*) (r s : α → Prop)
  (rs : ∀ x, r x → s x) :
  coe ∘ (subtype.map id rs) = (coe : (subtype r) → α) :=
funext (λ _, rfl)

lemma list.pair_mem_list {a b : β} :
  ∀ (l : list β), a ∈ l → b ∈ l → a = b ∨ [a,b] <+ l ∨ [b,a] <+ l
| [] al bl := by { simpa only [list.not_mem_nil] using al, }
| (x::l) al bl := by
  { simp only [list.mem_cons_iff] at al bl, cases al; cases bl,
    { left, exact al.trans bl.symm, },
    { rw al, right, left, apply list.sublist.cons2,
      simpa only [list.singleton_sublist] using bl, },
    { rw bl, right,  right, apply list.sublist.cons2,
      simpa only [list.singleton_sublist] using al, },
    { rcases list.pair_mem_list l al bl with h|ab|ba,
      { left, exact h, },
      { right, left, apply list.sublist.cons, exact ab, },
      { right, right, apply list.sublist.cons, exact ba, }, }, }

def list.take_while_subtype [preorder α] [decidable_pred (≤x)] (l : list α) : list (subtype (≤x)) :=
(l.take_while (≤x)).attach.map $ subtype.map id $ λ y, list.mem_take_while_imp

lemma list.take_while_subtype_map_coe [preorder α] [decidable_pred (≤x)] (l : list α) :
  (l.take_while_subtype x).map (coe : subtype (≤x) → α) = l.take_while (≤x) :=
begin
  simp only [list.take_while_subtype, list.map_map],
  apply list.attach_map_coe,
end

lemma list.pairwise_le_drop_while_le_not_le  [preorder α] [decidable_pred (≤x)] :
  ∀ (l : list α) (h : l.pairwise (≤)) (y : α), y ∈ l.drop_while (≤x) → ¬y ≤ x
| [] h y hy := by { simpa only [list.drop_while, list.not_mem_nil] using hy, }
| (a::l) h y hy := by
  { dsimp only [list.drop_while] at hy,
    simp only [list.pairwise_cons] at h,
    split_ifs at hy with ax nax,
    { exact list.pairwise_le_drop_while_le_not_le l h.right y hy, },
    { cases hy,
      { cases hy, exact ax },
      { exact λ yx, ax ((h.left y hy).trans yx), }, }, }

def list.drop_while_subtype [preorder α] [decidable_pred (≤x)] (l : list α) (h : l.pairwise (≤)) :
  list (subtype (λ y, ¬ y≤x)) :=
(l.drop_while (≤x)).attach.map $ subtype.map id (λ y, l.pairwise_le_drop_while_le_not_le x h y)

def list.drop_while_subtype_ge [linear_order α]  (l : list α) (h : l.pairwise (≤)) :
  list (subtype (λ y, x≤y)) :=
(l.drop_while_subtype x h).map $ subtype.map id $ λ y h', @le_of_not_le α _ y x h'

lemma list.drop_while_subtype_ge_map_coe [linear_order α] (l : list α) (h : l.pairwise (≤)) :
  (l.drop_while_subtype_ge x h).map coe = l.drop_while (≤x) :=
begin
  simp only [list.drop_while_subtype_ge, list.drop_while_subtype,
             list.map_map, subtype.map_id_comp_id, subtype.coe_comp_map_id, list.attach_map_coe],
end

lemma list.take_while_subtype_pairwise_le [preorder α] [decidable_pred (≤x)] (l : list α) :
  (l.take_while_subtype x).pairwise (≤) := sorry

lemma list.take_while_subtype_le_base [preorder α] [decidable_pred (≤x)] (l : list α) :
  ∀ y ∈ l.take_while_subtype x, ↑y ≤ x := sorry

lemma list.drop_while_subtype_ge_pairwise_le [linear_order α] (l : list α) (h : l.pairwise (≤)) :
  (l.drop_while_subtype_ge x h).pairwise (≤) := sorry

lemma list.drop_while_subtype_ge_ge_base  [linear_order α] (l : list α) (h : l.pairwise (≤)) :
  ∀ y ∈ l.drop_while_subtype_ge x h, x ≤ ↑y := sorry


lemma list.forall_mem.map {α β : Type*}
  {l : list α} (φ : α → β) {s : set α} {t : set β} (φst : s.maps_to φ t)
  (hl : ∀ x ∈ l, x ∈ s) : ∀ x ∈ l.map φ, x ∈ t :=
begin
  simp only [list.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
  rintro x xφl, exact φst (hl x xφl),
end

lemma list.pairwise.map_of_maps_to_of_forall {α β : Type*} [preorder α] [preorder β]
  {l : list α} (φ : α → β) {s : set α} (φm : monotone_on φ s)
  (hl : ∀ x ∈ l, x ∈ s) (lo : l.pairwise (≤)) : (l.map φ).pairwise (≤) := sorry

lemma list.pairwise.map_of_maps_to_of_forall' {α β : Type*} [preorder α] [preorder β]
  {l : list α} (φ : α → β) {s : set α} (φm : antitone_on φ s)
  (hl : ∀ x ∈ l, x ∈ s) (lo : l.pairwise (≥)) : (l.map φ).pairwise (≤) := sorry

lemma list.pairwise_and_nodup_iff {α : Type*} [preorder α] {l : list α} :
  l.pairwise (≤) ∧ l.nodup ↔ l.pairwise (<) := sorry

lemma list.pairwise.destutter {α : Type*} [decidable_eq α] [preorder α] {l : list α}
  (h : l.pairwise (≤)) : (l.destutter (≠)).pairwise (<) := sorry

section

open function set

lemma right_inverse_monotone [linear_order α] [partial_order β]
  (φ : α → β) (mφ : monotone φ) (ψ : β → α) (φψ : right_inverse ψ φ) : monotone ψ :=
begin
  rintro x y l,
  cases le_total (ψ x) (ψ y),
  { exact h },
  { let := mφ h,
    rw [φψ x, φψ y] at this,
    cases le_antisymm l this, refl, },
end

lemma right_inverse_antitone [linear_order α] [partial_order β]
  (φ : α → β) (mφ : antitone φ) (ψ : β → α) (φψ : right_inverse ψ φ) : antitone ψ :=
begin
  rintro x y l,
  cases le_total (ψ y) (ψ x),
  { exact h, },
  { let := mφ h,
    rw [φψ x, φψ y] at this,
    cases le_antisymm l this, refl, },
end

end


@[simp]
theorem finset.sort_mono {α : Type u_1} (r : α → α → Prop)
  [decidable_rel r] [is_trans α r] [is_antisymm α r] [is_total α r] {s t: finset α} (h : s ⊆ t) :
  (s.sort r) <+ (t.sort r) := sorry
