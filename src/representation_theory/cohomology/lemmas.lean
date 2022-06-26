#exit
import data.finset.basic
import algebra.group.ulift
import algebra.big_operators.finprod
import data.fin_simplicial_complex
import data.fin.tuple

universes u
noncomputable theory
open_locale classical

/- Todo: delete or move each lemma in here, as appropriate. -/

lemma finset.range_succ' (n : ℕ) :
  finset.range (n + 1) = insert 0 ((finset.range n).image nat.succ) :=
begin
  ext i,
  simp only [finset.mem_insert, finset.mem_image, finset.mem_range],
  cases i with i,
  { exact ⟨λ h, or.inl rfl, λ h, nat.succ_pos _⟩ },
  { exact ⟨λ h, or.inr ⟨i, ⟨nat.succ_lt_succ_iff.1 h, rfl⟩⟩,
    λ h, by obtain ⟨j, ⟨hj, hj'⟩⟩ := h.resolve_left (nat.succ_ne_zero i);
      rwa [←hj', nat.succ_lt_succ_iff]⟩}
end

@[to_additive] lemma ulift.prod_down {α : Type*} {β : Type*} [comm_monoid β] {s : finset α}
  (f : α → ulift β) :
  (s.prod f).down = s.prod (ulift.down ∘ f) :=
begin
  refine s.induction_on _ _,
  { simp only [ulift.one_down, finset.prod_empty] },
  { intros a t ht hf,
    simp only [*, finset.prod_insert, not_false_iff, ulift.mul_down] at *}
end

def fin.dom_one_equiv (α : Type u) : (fin 1 → α) ≃ α :=
{ to_fun := λ f, f 0,
  inv_fun := λ x i, x,
  left_inv := λ x, funext $ λ i, by rw subsingleton.elim i 0,
  right_inv := λ x, rfl }

lemma fin.injective_cons_zero {n : ℕ} {α : fin (n + 1) → Type*} (x : α 0) :
  function.injective (fin.cons x) :=
begin
  intros y z hyz,
  ext i,
  have := congr_fun hyz i.succ,
  dsimp at this,
  rwa [fin.cons_succ, fin.cons_succ] at this,
end

lemma fin.injective_cons_tail {n : ℕ} {α : fin (n + 1) → Type*} (x : Π i : fin n, α i.succ) :
  function.injective (λ y : α 0, fin.cons y x) :=
begin
  intros y z hyz,
  replace hyz := congr_fun hyz 0,
  dsimp at hyz,
  rwa [fin.cons_zero, fin.cons_zero] at hyz,
end

lemma fin.delta_zero_succ (n : ℕ) :
  fin.delta rfl 0 = @fin.succ n :=
begin
  ext,
  unfold fin.delta,
  dsimp,
  rw [if_neg (nat.not_lt_zero _), fin.coe_succ],
end

lemma fin.delta_zero_succ_apply {n : ℕ} (t : fin n) :
  fin.delta rfl 0 t = t.succ :=
congr_fun (fin.delta_zero_succ n) t

lemma fin.cons_delta_zero {n : ℕ} {α : Type*} (x : fin n → α) (y : α) :
  (fin.cons y x ∘ fin.delta rfl 0 : fin n → α) = x :=
begin
  ext j,
  rw [function.comp_app, fin.delta_zero_succ, fin.cons_succ],
end

lemma fin.cons_delta_zero_apply {n : ℕ} {α : Type*} (x : fin n → α)
  (y : α) (t : fin n) :
  (fin.cons y x : fin (n + 1) → α) (fin.delta rfl 0 t) = x t :=
congr_fun (fin.cons_delta_zero x y) t

lemma fin.cons_delta_succ {n : ℕ} {α : Type*} (x : fin (n + 1) → α) (y : α) (m : ℕ) :
  (fin.cons y x ∘ fin.delta rfl m.succ : fin (n + 1) → α) =
  fin.cons y (x ∘ fin.delta rfl m : fin n → α) :=
begin
  ext j,
  refine fin.cases _ (λ i, _) j,
  { rw [fin.cons_zero, function.comp_app],
    convert fin.cons_zero _ _,
    refl },
  { rw fin.cons_succ,
    dsimp,
    convert fin.cons_succ _ _ _,
    { refl },
    { ext,
      unfold fin.delta,
      dsimp,
      by_cases h : (i : ℕ) < m,
      { rw [if_pos h, if_pos, fin.coe_succ],
        { rw fin.coe_succ,
          exact nat.succ_lt_succ_iff.2 h }},
      { rw [if_neg h, if_neg, fin.coe_succ],
        exact (λ hn, h $ by rw fin.coe_succ at hn; exact nat.succ_lt_succ_iff.1 hn) }}},
end

lemma fin.cons_delta_succ_apply {n : ℕ} {α : Type*} (x : fin (n + 1) → α)
  (y : α) (m : ℕ) (t : fin (n + 1)) :
  (fin.cons y x : fin (n + 2) → α) (fin.delta rfl m.succ t) =
  (fin.cons y (x ∘ fin.delta rfl m : fin n → α) : fin (n + 1) → α) t :=
congr_fun (fin.cons_delta_succ x y m) t

lemma cons_delta_two {M : Type*} [monoid M] (f : fin 1 → M) (g : M) :
  (fin.cons g f : fin 2 → M) ∘ (fin.delta rfl 1) = λ i, g :=
begin
  ext,
  rw [subsingleton.elim x 0, function.comp_app],
  dunfold fin.delta,
  convert @fin.cons_zero 1 (λ i, M) _ _,
end

lemma cons_delta_two_apply {M : Type*} [monoid M] (f : fin 1 → M) (g : M) (t : fin 2) :
  (fin.cons g f : fin 2 → M) (fin.delta rfl 1 t) = g :=
congr_fun (cons_delta_two f g) t

@[to_additive] lemma mul_equiv.map_pow {M N : Type*} [monoid M] [monoid N]
  (f : M ≃* N) (x : M) (n : ℕ) :
  f (x ^ n) = (f x) ^ n :=
f.to_monoid_hom.map_pow _ _

lemma mul_equiv.map_zpow {M N : Type*} [group M] [group N]
  (f : M ≃* N) (x : M) (n : ℤ) :
  f (x ^ n) = (f x) ^ n :=
f.to_monoid_hom.map_zpow _ _

lemma add_equiv.map_zsmul {M N : Type*} [add_group M] [add_group N]
  (f : M ≃+ N) (x : M) (n : ℤ) :
  f (n • x) = n • f x :=
f.to_add_monoid_hom.map_zsmul _ _

attribute [to_additive add_equiv.map_zsmul] mul_equiv.map_zpow

lemma int.pred_smul {A : Type*} [add_group A] (a : A) (n : ℤ) :
  (n - 1) • a = n • a - a :=
int.induction_on n
  (by simp)
  (λ _ _, by simp [add_zsmul, one_zsmul])
  (λ x, by {simp [sub_zsmul, ←sub_eq_add_neg] })

lemma distrib_mul_action.smul_nsmul {G : Type*} [monoid G] {M : Type*}
  [add_comm_monoid M] [distrib_mul_action G M] (g : G) (n : ℕ) (m : M) :
  g • n • m = n • g • m :=
nat.rec_on n (by simp) (λ n hn, by simp [nat.succ_eq_add_one, add_smul, smul_add, hn])

lemma distrib_mul_action.smul_zsmul {G : Type*} [monoid G] {M : Type*}
  [add_comm_group M] [distrib_mul_action G M]
  (g : G) (n : ℤ) (m : M) : g • n • m = n • g • m :=
int.induction_on n
  ( by simp)
  ( λ i h, by { simp only [add_smul, smul_add, add_left_inj, one_zsmul, h] })
  ( λ i h, by { simp only [int.pred_smul, smul_sub, smul_neg, neg_inj, sub_left_inj, h] } )

-- used in the two proofs of `d² = 0`.
/-- Sends `(j, k)` to `(k + 1, j)` if `j ≤ k` and `(k, j - 1)` otherwise. -/
def invo : ℕ × ℕ → ℕ × ℕ :=
λ j, if j.1 ≤ j.2 then (j.2 + 1, j.1) else (j.2, j.1 - 1)

lemma invo_pos {j : ℕ × ℕ} (h : j.1 ≤ j.2) :
  invo j = (j.2 + 1, j.1) := if_pos h

lemma invo_neg {j : ℕ × ℕ} (h : ¬j.1 ≤ j.2) :
  invo j = (j.2, j.1 - 1) := if_neg h

lemma invo_invo (j : ℕ × ℕ) : invo (invo j) = j :=
begin
  by_cases h : j.1 ≤ j.2,
  { rw [invo_pos h, invo_neg],
    { exact prod.ext rfl rfl },
    { linarith }},
  { rw [invo_neg h, invo_pos],
    { exact prod.ext (nat.sub_add_cancel (by linarith)) rfl },
    { exact (nat.le_pred_of_lt (not_le.1 h)) }},
end
