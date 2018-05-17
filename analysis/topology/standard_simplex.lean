import analysis.topology.topological_space analysis.real data.finsupp data.fin order.basic algebra.big_operators data.finset data.fintype
noncomputable theory

open classical



namespace simplex_category

variables {n : ℕ}

@[simp]
lemma val_succ_eq_succ_val (j : fin n) : j.succ.val = j.val.succ := by cases j; simp [fin.succ]

instance : linear_order (fin n) := {le := λ a b, nat.less_than_or_equal a.1 b.1,
  le_refl := λ a, @nat.le_refl a.1,
  le_trans := λ a b c, @nat.le_trans a.1 b.1 c.1,
  le_antisymm := λ a b H1 H2, fin.eq_of_veq $ @nat.le_antisymm a b H1 H2,
  le_total := λ a b, @nat.le_total a b,
  lt := λ a b, nat.lt a.1 b.1,
  lt_iff_le_not_le := λ a b, @nat.lt_iff_le_not_le a.1 b.1}

def δ (i : fin (n + 1)) (a : fin n) : fin (n + 1) :=
if h : i.val ≤ a.val then a.succ else a.raise

def σ (i : fin n) (a : fin (n+1)) : fin n :=
if h : a.val ≤ i.val then
  ⟨a.val, lt_of_le_of_lt h i.is_lt⟩
else
  ⟨a.val.pred, (nat.sub_lt_right_iff_lt_add (lt_of_le_of_lt i.val.zero_le (not_le.mp h))).mpr a.is_lt⟩
  --a.pred sorry

lemma δ_monotone (i : fin (n+1)) : monotone (δ i) :=
begin
unfold monotone,
intros a b H,
unfold δ,
by_cases ha : (i.val ≤ a.val),
    { rw [dif_pos ha], 
    have hb : i.val ≤ b.val := nat.le_trans ha H,
    rw [dif_pos hb], show a.succ.val ≤ b.succ.val,
    simp, exact nat.succ_le_succ H,
    },
    { rw [dif_neg ha], by_cases hb : (i.val ≤ b.val),
        { rw [dif_pos hb], show a.val ≤ b.succ.val,
        simp, exact nat.le_trans H (nat.le_succ b) },
        { rw [dif_neg hb], exact H },
    }
end

lemma σ_monotone (i : fin n) : monotone (σ i) :=
begin
unfold monotone,
intros a b H,
unfold σ,
by_cases ha : (a.val ≤ i.val),
    { rw [dif_pos ha], by_cases hb : (b.val ≤ i.val),
        { rw [dif_pos hb], exact H },
        { rw [dif_neg hb], simp at hb,
        have hb' : i.val ≤ nat.pred b.val := begin
            rw ←nat.pred_succ i.val, exact nat.pred_le_pred hb
        end,
        --show a.val ≤ (b.pred _).val,
        --simp,
        exact nat.le_trans ha hb'
        },
    },
    { rw [dif_neg ha],
    have hb : ¬b.val ≤ i.val := begin simp at *, exact nat.le_trans ha H end,
    rw [dif_neg hb],
    --show (a.pred _).val ≤ (b.pred _).val,
    --simp,
    exact nat.pred_le_pred H,
    }
end


lemma simplicial_identity₁ (i j : fin (n + 1)) (H : i ≤ j) : δ j.succ ∘ δ i = δ i.raise ∘ δ j
:= begin
    apply funext, intro a, unfold function.comp, unfold δ,
    by_cases hja : (j.val ≤ a.val),
    { rw [dif_pos hja],
        rw [dif_pos (nat.le_trans H hja)],
        have hja' : ((fin.succ j).val ≤ (fin.succ a).val) := begin
            simp, exact nat.succ_le_succ hja,
        end,
        rw [dif_pos hja'],
        have hia : ((fin.raise i).val ≤ (fin.succ a).val) := begin
            simp, exact nat.le_trans H (nat.le_trans hja (nat.le_succ a.val))
        end,
        rw [dif_pos hia]
    },
    { rw [dif_neg hja],
        by_cases hia : (i.val ≤ a.val),
        { rw [dif_pos hia],
            have hia' : ((fin.raise i).val ≤ (fin.raise a).val) := begin
                unfold fin.raise, exact hia
            end,
            rw [dif_pos hia'],
            have hja' : ¬(j.succ.val ≤ a.succ.val) := begin
                simp at *, exact nat.succ_le_succ hja
            end,
            rw [dif_neg hja'],
            unfold fin.raise, apply fin.eq_of_veq, simp
        },
        { rw [dif_neg hia],
            have hja' : ¬(j.succ.val ≤ a.raise.val) := begin
                simp at *, exact nat.le_trans hja (nat.le_succ j.val)
            end,
            rw [dif_neg hja'],
            have hia' : ¬((fin.raise i).val ≤ (fin.raise a).val) := begin
                unfold fin.raise, exact hia
            end,
            rw [dif_neg hia']
        }
    }
end

end simplex_category



namespace standard_simplex

open finset

definition type_pow : Type* → ℕ → Type* := λ α n, fin n → α

instance type_pow_instance : has_pow Type* ℕ := ⟨type_pow⟩
 
definition topology_Rn : Π (n : ℕ), topological_space (ℝ^n) :=
begin
intros n, show topological_space (fin n → ℝ), apply_instance,
end

definition standard_simplex (n : ℕ) : set (ℝ^(n+1)) :=
 λ x : fin (n+1) → ℝ, (∀ i, 0 ≤ x i) ∧ (sum univ x = 1)

variable {n : ℕ}

instance : topological_space (standard_simplex n)
 := topological_space.induced subtype.val (@topology_Rn (n+1))

definition finvj {m n : ℕ} (f : fin m → fin n) (j : fin n) : finset (fin m) := univ.filter (λ i, f i = j)

-- definition induced_map {m n : ℕ} (f : fin (m+1) → fin (n+1))
--  : standard_simplex m → standard_simplex n := begin
--  intro x,
--  unfold standard_simplex, let y_val : ℝ^(n+1) := begin
--     show fin (n+1) → ℝ,
--     intro j,
--     exact sum (finvj f j) x.val
--  end,
--  split, show fin (n+1) → ℝ,
--  exact y_val,
--  split,
--  {
--      dsimp [y_val],
--      intro i,
--      admit
--  },
--  {
--      dsimp [y_val], admit
--  }
--  end

end standard_simplex


-- namespace simplicial_complex

-- definition C (n : ℕ) (X : Type*) [topological_space X] :=
--  {f : standard_simplex n → X // continuous f} →₀ ℤ

-- instance (n : ℕ) (X : Type*) [topological_space X]
--  : decidable_eq {f : standard_simplex n → X // continuous f} := sorry

-- instance (n : ℕ) (X : Type*) [topological_space X] : add_comm_group (C n X)
--  := finsupp.add_comm_group

-- definition induced_map {X G : Type*} [add_comm_group G] (b : X → G) (f : X →₀ ℤ) : G
--  := f.support.sum (λ x, gsmul (f x) (b x))

-- definition δ_on_singular_complexes (n : ℕ) (X : Type*) [topological_space X]
--  : {f : standard_simplex (nat.succ n) → X // continuous f} → C n X
--  :=
-- begin
-- intro f, admit
-- -- exact Sum_{i = 0}^n single (f ∘ (face i)) (-1)^i
-- end

-- definition δ {n : ℕ} {X : Type*} [topological_space X] : C (n+1) X → C n X :=
-- induced_map (δ_on_singular_complexes n X)

-- lemma δδis0 (n : ℕ) (X : Type*) [topological_space X] (γ : C (n+2) X) : δ (δ γ) = (_ : C n X)
-- begin
-- admit
-- end

-- end simplicial_complex

-- begin singular_homology

-- definition Hsing (n : ℕ) (X : Type*) [topological_space X] := sorry

-- end singular_homology