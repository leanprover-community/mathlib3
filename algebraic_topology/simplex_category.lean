import data.fin order.basic

variables {n : ℕ}

namespace fin

instance : linear_order (fin n) :=
{ le               := λ a b, nat.less_than_or_equal a.1 b.1,
  le_refl          := λ a, @nat.le_refl a.1,
  le_trans         := λ a b c, @nat.le_trans a.1 b.1 c.1,
  le_antisymm      := λ a b H1 H2, fin.eq_of_veq $ @nat.le_antisymm a b H1 H2,
  le_total         := λ a b, @nat.le_total a b,
  lt               := λ a b, nat.lt a.1 b.1,
  lt_iff_le_not_le := λ a b, @nat.lt_iff_le_not_le a.1 b.1}

end fin

namespace simplex_category
local notation ` [`n`] ` := fin (n+1)

def δ (i : [n+1]) (a : [n]) : [n+1] :=
if h : i.val ≤ a.val then a.succ else a.raise

def σ (i : [n]) (a : [n+1]) : [n] :=
if h : a.val ≤ i.val
then ⟨a.val, lt_of_le_of_lt h i.is_lt⟩
else ⟨a.val.pred,
  (nat.sub_lt_right_iff_lt_add (lt_of_le_of_lt i.val.zero_le (not_le.mp h))).mpr a.is_lt⟩
  --a.pred sorry

lemma δ_monotone (i : [n+1]) : monotone (δ i) :=
begin
unfold monotone,
intros a b H,
unfold δ,
by_cases ha : (i.val ≤ a.val),
{ rw [dif_pos ha],
  have hb : i.val ≤ b.val := nat.le_trans ha H,
  rw [dif_pos hb],
  show a.succ.val ≤ b.succ.val,
  simp,
  exact nat.succ_le_succ H,},
{ rw [dif_neg ha],
  by_cases hb : (i.val ≤ b.val),
  { rw [dif_pos hb],
    show a.val ≤ b.succ.val,
    simp,
    exact nat.le_trans H (nat.le_succ b)},
  { rw [dif_neg hb],
    exact H }}
end

lemma σ_monotone (i : [n]) : monotone (σ i) :=
begin
unfold monotone,
intros a b H,
unfold σ,
by_cases ha : (a.val ≤ i.val),
{ rw [dif_pos ha],
  by_cases hb : (b.val ≤ i.val),
  { rw [dif_pos hb], exact H },
  { rw [dif_neg hb],
    simp at hb,
    have hb' : i.val ≤ nat.pred b.val :=
    begin
      rw ←nat.pred_succ i.val,
      exact nat.pred_le_pred hb
    end,
    exact nat.le_trans ha hb'}},
{ rw [dif_neg ha],
  have hb : ¬b.val ≤ i.val :=
  begin
    simp at *,
    exact nat.le_trans ha H
  end,
  rw [dif_neg hb],
  exact nat.pred_le_pred H}
end

lemma simplicial_identity₁ (i j : [n+1]) (H : i ≤ j) : δ j.succ ∘ δ i = δ i.raise ∘ δ j :=
begin
apply funext,
intro a,
unfold function.comp,
unfold δ,
by_cases hja : (j.val ≤ a.val),
{ rw [dif_pos hja],
  rw [dif_pos (nat.le_trans H hja)],
  have hja' : ((fin.succ j).val ≤ (fin.succ a).val) :=
  begin
    simp,
    exact nat.succ_le_succ hja,
  end,
  rw [dif_pos hja'],
  have hia : ((fin.raise i).val ≤ (fin.succ a).val) :=
  begin
    simp,
    exact nat.le_trans H (nat.le_trans hja (nat.le_succ a.val))
  end,
  rw [dif_pos hia]},
{ rw [dif_neg hja],
  by_cases hia : (i.val ≤ a.val),
  { rw [dif_pos hia],
    have hia' : ((fin.raise i).val ≤ (fin.raise a).val) :=
    begin
      unfold fin.raise,
      exact hia
    end,
    rw [dif_pos hia'],
    have hja' : ¬(j.succ.val ≤ a.succ.val) :=
    begin
      simp at *,
      exact nat.succ_le_succ hja
    end,
    rw [dif_neg hja'],
    unfold fin.raise,
    apply fin.eq_of_veq,
    simp},
  { rw [dif_neg hia],
    have hja' : ¬(j.succ.val ≤ a.raise.val) :=
    begin
      simp at *,
      exact nat.le_trans hja (nat.le_succ j.val)
    end,
    rw [dif_neg hja'],
    have hia' : ¬((fin.raise i).val ≤ (fin.raise a).val) :=
    begin
      unfold fin.raise, exact hia
    end,
    rw [dif_neg hia']}}
end

end simplex_category