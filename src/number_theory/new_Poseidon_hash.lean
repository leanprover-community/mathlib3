import data.matrix.basic
import data.zmod.algebra

variables (p t : ℕ) [fact (p.prime)]

/-- The AddRoundConstant linear step of a single round of the Poseidon permutation -/
def ARC' (c a : fin t → zmod p) : fin t → zmod p := a + c

/-- An `R_f`-round, that is, a full round. -/
def R_f_round' (S_box' : zmod p → zmod p) (c : fin t → zmod p)
  (MDS' : matrix (fin t) (fin t) (zmod p)) (a : fin t → zmod p) : fin t → zmod p :=
matrix.mul_vec MDS' (λ i, S_box' (ARC' p t c a i))

/-- An `R_p`-round, that is, a partial round. -/
def R_p_round' (S_box' : zmod p → zmod p) (c : fin t → zmod p)
(MDS' : matrix (fin t) (fin t) (zmod p)) (a : fin t → zmod p) : fin t → zmod p :=
matrix.mul_vec MDS' (λ i, dite ((i : ℕ) = 0) (λ h, S_box' (ARC' p t c a i)) (λ h, ARC' p t c a i))

/-- The Poseidon permutation function, takes as input `t` elements, and returns `t` elements;
  this is defined in terms of compositions of `R_f_round` and `R_p_round`. -/
def P_perm' (R_f R_p : ℕ) (S_box' : zmod p → zmod p) (c a : fin t → zmod p)
(MDS' : matrix (fin t) (fin t) (zmod p)) : fin t → zmod p :=
(R_f_round' p t S_box' c MDS')^[R_f] ((R_p_round' p t S_box' c MDS')^[R_p]
((R_f_round' p t S_box' c MDS')^[R_f] a))

/-- Adding an `r`-chunk to the state. -/
def add_to_state' (r cap : ℕ) (m : fin r → zmod p) (a : fin t → zmod p) (h : t = r + cap) :
  fin t → zmod p :=
λ i, dite ((i : ℕ) < r) (λ h, a i + m (fin.cast_lt i h)) (λ h, a i)

lemma helper_1 (d r cap : ℕ) (j : fin (d * r + (r + cap))) :
  ↑j + r < d.succ * r + (r + cap) :=
begin
  have h1 : d.succ * r + (r + cap) = d * r + (r + cap) + r,
  { rw [add_assoc, add_comm _ r, ← add_assoc _ _ (r + cap), ← nat.succ_mul], },
  rw h1,
  apply add_lt_add_of_lt_of_le j.prop le_rfl,
end

/-- The Poseidon hash function, takes `N` bits and returns `o` `𝔽_p`-elements. -/
def P_hash' (R_f R_p r o cap : ℕ) (hr : 1 ≤ r) (S_box' : zmod p → zmod p) (c : fin (r + cap) → zmod p)
(MDS' : matrix (fin (r + cap)) (fin (r + cap)) (zmod p)) (ho : o ≤ r + cap)
(k : ℕ) (a : fin (k * r + (r + cap)) → zmod p) : fin o → zmod p :=
@function.comp (fin o) (fin (r + cap)) (zmod p)
  begin induction k with d hd,
  { rw [zero_mul, zero_add] at *,
    refine λ i, P_perm' p (r + cap) R_p R_f S_box' c a MDS' i, },
  { refine λ i, P_perm' p (r + cap) R_p R_f S_box' c (add_to_state' p (r + cap) r cap
      (λ j, a ⟨d.succ + j, add_lt_add_of_le_of_lt ((le_mul_iff_one_le_right (nat.succ_pos _)).2 hr)
      (lt_add_of_lt_of_nonneg j.prop (nat.zero_le _))⟩)
      (hd (λ j, dite ((j : ℕ) < d.succ * r) (λ h, a (fin.cast_lt j (lt_trans h
      ((lt_add_iff_pos_right _).2 (add_pos_of_pos_of_nonneg (nat.pos_of_ne_zero
      (nat.one_le_iff_ne_zero.1 hr)) (nat.zero_le _)))))) (λ h, a ⟨(j : ℕ) + r,
      helper_1 d r cap j⟩))) rfl) MDS' i, }, end
(λ (i : fin o), (⟨(i : ℕ), lt_of_lt_of_le i.prop ho⟩ : fin (r + cap)) : fin o → fin (r + cap))
