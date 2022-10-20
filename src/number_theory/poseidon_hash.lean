import data.matrix.basic
-- import data.bitvec.core
import data.zmod.algebra
-- import combinatorics.composition

-- M = security level; R = no of rounds of the permutation in the hash
variables (p t : ℕ) [fact (p.prime)]

-- open_locale big_operators
-- open bitvec

/-/-- The capacity for Poseidon - 2M. -/
def c : ℕ := 2 * M

/-- The number of bits of `𝔽_p`. -/
def n : ℕ := pos_num.nat_size (pos_num.of_nat p)

/-- The length of the input. -/
def N : ℕ := (n p) * t

-- the condition on N
--variable (h : N p t = r + (c M))

/-- The required composition, n t times. -/
def uniform_composition (ht : t ≠ 0) (hn : 0 < (n p)) : composition (N p t) :=
{ blocks := list.repeat (n p) t,
  blocks_pos := λ i hi, by { rw list.mem_repeat at hi, rw hi.2, assumption, },
  blocks_sum := by { rw list.sum_repeat, rw smul_eq_mul, delta N, rw mul_comm, }, }

namespace bitvec

/-- Removes the last `i` elements(?) -/
def drop (n i : ℕ) (a : bitvec n) : bitvec (n - i) := vector.drop i a

def jth_block (j : fin t) (a : bitvec (N p t)) : bitvec (n p) :=
begin
  have : min (n p) (N p t - ↑j * n p) = (n p),
  { delta N, rw mul_comm ↑j _, rw ← nat.mul_sub_left_distrib,
    rw min_def, rw if_pos, conv { congr, rw ← nat.mul_one (n p), },
    apply nat.mul_le_mul_left,
    change 0 < t - ↑j,
    simp, exact fin.is_lt j, },
  rw ← this,
  apply vector.take (n p) (vector.drop (j * (n p)) a),
end
-- there should be easier code for this!

def split_wrt_composition (ht : t ≠ 0) (hn : 0 < (n p)) (a : bitvec (N p t)) :
  list (bitvec (n p)) :=
begin

  induction t with d hd,
  { exact false.rec (list (bitvec (n p))) (ht rfl), },
  refine list.split_wrt_composition a.to_list (uniform_composition p t ht hn)
end
--generalize!

def ith_block (ht : t ≠ 0) (hn : 0 < (n p)) (a : bitvec (N p t)) (i : ℕ) : bitvec (n p) :=
list.nth_le (list.split_wrt_composition a.to_list (uniform_composition p t ht hn)) i _

end bitvec

/-- The AddRoundConstant linear step of a single round of the Poseidon permutation;
  it uses the XOR gate -/
def ARC (c a : bitvec (N p t)) : bitvec (N p t) := xor c a

-- The S-box function
--variable (S_box : bitvec (n p) → bitvec (n p))

def full_round (S_box : bitvec (n p) → bitvec (n p)) (a : bitvec (N p t)) : bitvec (N p t) :=
begin
  delta N,
  induction t with d hd,
  { rw mul_zero, exact (bitvec.zero 0), },
  { rw nat.mul_succ, apply bitvec.append,
    { convert vector.take (n p * d) a,
      rw min_def, rw if_pos, delta N, rw nat.mul_succ, apply nat.le_add_right, },
    { apply S_box (bitvec.jth_block p d.succ d a), }, },
end

-- The MDS t×t matrix M
variable (MDS : matrix (finset.range t) (finset.range t) (bitvec (n p)))

-- The MDS N × N matrix
def MDS_full (MDS : matrix (fin t) (fin t) (fin p)) :
  matrix (fin (N p t)) (fin (N p t)) bool :=
begin

  sorry
end

instance : non_unital_non_assoc_semiring bool :=
{ add := λ a b, a || b,
  add_assoc := bool.bor_assoc,
  zero := ff,
  zero_add := ff_bor,
  add_zero := bor_ff,
  nsmul := λ a b, (bool.of_nat a) && b,
  nsmul_zero' := dec_trivial,
  nsmul_succ' := λ n x, begin
    rw bool.of_nat, simp, change _ = x || bool.of_nat n && x, rw bool.of_nat,
    cases n, simp, simp, end,
  add_comm := bool.bor_comm,
  mul := λ a b, a && b,
  left_distrib := dec_trivial,
  right_distrib := dec_trivial,
  zero_mul := ff_band,
  mul_zero := band_ff }

/-- An `R_f`-round, that is, a full round. -/
def R_f_round (S_box : bitvec (n p) → bitvec (n p)) (c a : bitvec (N p t))
  (MDS : matrix (fin t) (fin t) (fin p)) : bitvec (N p t) :=
vector.of_fn (matrix.mul_vec (MDS_full p t MDS)
(λ i, vector.nth (full_round p t S_box (ARC p t c a)) i))
-- MDS (full_round p t S_box (ARC p t c a))

/-- An `R_p`-round, that is, a partial round. -/
def R_p_round (a : bitvec (N p t)) : bitvec (N p t) := sorry

/-- The Poseidon permutation function, takes as input `N` bits, and returns `N` bits;
  this is defined in terms of compositions of `R_f_round` and `R_p_round`. -/
def P_perm (a : bitvec (N p t)) : bitvec (N p t) :=
  (R_f_round p t)^[R_f] ((R_p_round p t)^[R_p] ((R_f_round p t)^[R_f] a))

/-- Adding an `r`-chunk to the state. -/
def add_to_state (m : bitvec r) (a : bitvec (N p t)) (h : N p t = r + (c M)) : bitvec (N p t) :=
begin
  rw h,
  apply bitvec.append,
  { sorry, },
  { sorry, },
end -/

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
