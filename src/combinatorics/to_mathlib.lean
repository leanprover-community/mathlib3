import order.lexicographic
import order.hom.basic
import data.fintype.sort
import data.fin.tuple.basic

noncomputable theory
open option

@[simps] def lex.fst {α β} [preorder α] [preorder β] : lex (α × β) →o α :=
{ to_fun := prod.fst,
  monotone' := λ i j h, by { cases h, { apply le_of_lt, assumption }, { refl } } }

section

variables {α β : Type*} {m : ℕ} [fintype α] [linear_order β] (h : fintype.card α = m) (f : α → β)
include h

/-- Sorting a function. Informally, given an indexed collection of ordered values, we order the
indices to match the values. -/
lemma monotone_replacement_exists : ∃ (e : fin m ≃ α), monotone (f ∘ e) :=
begin
  have e0 : α ≃ fin m := fintype.equiv_fin_of_card_eq h,
  let f' : α → lex (β × fin m) := λ a, (f a, e0 a),
  letI : linear_order α := linear_order.lift f' _,
  swap, { intros a b ab, apply e0.injective, convert congr_arg prod.snd ab },
  have eo : fin m ≃o α := mono_equiv_of_fin _ h,
  refine ⟨eo.to_equiv, monotone.comp _ eo.monotone⟩,
  change monotone (lex.fst ∘ f'),
  exact monotone.comp lex.fst.monotone (λ a b h, h),
end

/-- Given `fintype.card α = m` and `f : α → β`, this is an equivalence `fin m ≃ α` which makes `f`
monotone. -/
def monotone_replacement_equiv : fin m ≃ α := (monotone_replacement_exists h f).some
/-- Given `fintype.card α = m` and `f : α → β`, this is a monotone replacement `fin m → β`. -/
def monotone_replacement_order_hom : fin m →o β :=
⟨_, (monotone_replacement_exists h f).some_spec⟩

@[simp] lemma monotone_replacement_order_hom_apply (i : fin m) :
  monotone_replacement_order_hom h f i = f (monotone_replacement_equiv h f i) := rfl

end

def order_emb_of_card_le {m β} [linear_order β] {s : finset β} (h : m ≤ s.card) : fin m ↪o β :=
(fin.cast_le h).trans (s.order_emb_of_fin rfl)

lemma order_emb_mem {m β} [linear_order β] {s : finset β} (h : m ≤ s.card) (a) :
  order_emb_of_card_le h a ∈ s :=
by simp only [order_emb_of_card_le, rel_embedding.coe_trans, finset.order_emb_of_fin_mem]

def order_hom.succ {m n : ℕ} (f : fin m →o fin n) : fin (m+1) →o fin (n+1) :=
{ to_fun := fin.snoc (λ i, (f i).cast_succ) (fin.last _),
  monotone' := begin
    refine fin.last_cases _ _,
    { intros j ij, cases fin.eq_last_of_not_lt (not_lt_of_le ij), refl },
    intros i, refine fin.last_cases _ _,
    { intro junk, rw [fin.snoc_last], apply fin.le_last },
    intros j ij,
    rw [fin.snoc_cast_succ, fin.snoc_cast_succ, order_embedding.le_iff_le],
    apply f.mono, exact ij,
  end }

@[simp] lemma order_hom.succ_apply_last {m n : ℕ} (f : fin m →o fin n) :
  f.succ (fin.last m) = fin.last n :=
by { unfold order_hom.succ, simp only [order_hom.coe_fun_mk, fin.snoc_last] }

@[simp] lemma order_hom.succ_apply_cast_succ {m n : ℕ} (f : fin m →o fin n) (i : fin m) :
  f.succ (i.cast_succ) = (f i).cast_succ :=
by { unfold order_hom.succ, simp only [order_hom.coe_fun_mk, fin.snoc_cast_succ] }

lemma option.mem_orelse_iff {α} (a b : option α) (x : α) :
  x ∈ a.orelse b ↔ x ∈ a ∨ (a = none ∧ x ∈ b) :=
begin
  cases a,
  { simp only [true_and, false_or, not_mem_none, eq_self_iff_true, none_orelse'] },
  { simp only [some_orelse', or_false, false_and] }
end
