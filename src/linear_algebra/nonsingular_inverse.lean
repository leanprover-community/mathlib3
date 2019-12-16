import algebra.big_operators
import data.matrix.basic
import linear_algebra.determinant
import tactic.fin_cases
import tactic.linarith
import tactic.omega
import tactic.ring

/-!
  In this file, we define an inverse for square matrices of full rank.
  This inverse is defined, but doesn't have nice properties,
  if the matrix is not square or not of full rank.
  In that case, a pseudoinverse might be a better choice.
  Unfortunately, defining and proving properties of pseudoinverses takes
  a bit more work, so it isn't implemented yet.

  To make computations easier, we use `fin n.succ` to index the matrices in definitions.
  Conversion from and to an arbitrary `fintype m` can be done by the user if needed.
  (Or just define and use the pseudoinverse!)
-/

namespace matrix
universes u v
variables {n : Type u} [fintype n] [decidable_eq n] {α : Type v}
open_locale matrix
open finset equiv.perm

def replace_column (A : matrix n n α) (i : n) (b : n → α) : matrix n n α :=
λ i' j, if i = i' then b j else A i' j

lemma replace_column_val (A : matrix n n α) (i : n) (b : n → α) (i' j : n) :
  replace_column A i b i' j = if i = i' then b j else A i' j := rfl

lemma replace_column_self (A : matrix n n α) (i : n) (b : n → α) :
  replace_column A i b i = b := by {ext, exact if_pos rfl}

lemma replace_column_ne (A : matrix n n α) (i : n) (b : n → α) (j : n) :
  i ≠ j → replace_column A i b j = A j := by {intro h, ext, exact if_neg h}

def replace_row (A : matrix n n α) (j : n) (b : n → α) : matrix n n α :=
λ i j', if j = j' then b i else A i j'

section cramer
variables [comm_ring α] (A : matrix n n α) (b : n → α)

def cramer_map (i : n) : α := (A.replace_column i b)ᵀ.det
lemma cramer_map_val (i : n) : cramer_map A b i = (A.replace_column i b)ᵀ.det := rfl

lemma vec.smul_val {α} [semiring α] (s : α) (x : n → α) (i : n) : (s • x) i = s * x i := rfl
lemma vec.add_val (x y : n → α) (i : n) : (x + y) i = x i + y i := rfl

lemma cramer_at_is_linear (i : n) : is_linear_map α (λ b, cramer_map A b i) := begin
  have : Π (f : n → n) (i : n) (x : n → α),
    finset.prod univ (λ (i' : n), (replace_column A i x)ᵀ (f i') i')
    = finset.prod univ (λ (i' : n), if i = i' then x (f i') else A i' (f i')),
  { intros, congr },
  split,
  { intros x y,
    rw [cramer_map, det, cramer_map, det, cramer_map, det, ←sum_add_distrib],
    congr, ext σ,
    rw [←mul_add ↑↑(sign σ)],
    congr,
    erw [this _ _ (x + y), this _ _ x, this _ _ y,
      finset.prod_ite _ _ id, finset.prod_ite _ _ id, finset.prod_ite _ _ id,
      finset.filter_eq, if_pos (mem_univ i),
      prod_singleton, prod_singleton, prod_singleton,
      ←add_mul],
    refl
  },
  { intros c x,
    rw [smul_eq_mul, cramer_map, cramer_map, det, det, mul_sum],
    congr, ext σ,
    rw [←mul_assoc, mul_comm c, mul_assoc], congr,
    erw [this _ _ (c • x), this _ _ x,
      finset.prod_ite _ _ id, finset.prod_ite _ _ id,
      finset.filter_eq, if_pos (mem_univ i),
      prod_singleton, prod_singleton, mul_assoc],
    refl
   }
end
def cramer_at (i : n) : (n → α) →ₗ[α] α :=
is_linear_map.mk' (λ b, cramer_map A b i) (cramer_at_is_linear A i)

lemma cramer_at_val (i : n) : (cramer_at A i).to_fun b = cramer_map A b i := rfl

lemma cramer_map_is_linear : is_linear_map α (cramer_map A) := begin
  split; intros; ext i,
  { rw [vec.add_val], apply (cramer_at_is_linear A i).1 },
  { rw [vec.smul_val], apply (cramer_at_is_linear A i).2 }
end
def cramer : (n → α) →ₗ[α] (n → α) := is_linear_map.mk' (cramer_map A) (cramer_map_is_linear A)

lemma cramer_val (i : n) : (cramer A).to_fun b i = cramer_map A b i := rfl

lemma mul_cramer_map_val (c : α) (i : n) : c * cramer_map A b i = cramer_map A (c • b) i :=
by simp [(cramer_map_is_linear A).2]

lemma cramer_column (i : n) : (cramer A).to_fun (A i) = (λ j, if i = j then A.det else 0) := begin
  ext j,
  rw cramer_val,
  by_cases i = j,
  { rw [if_pos h, ←h, cramer_map, det_transpose, replace_column],
    congr, ext i' j,
    by_cases h : i = i', { rw [if_pos h, h] }, { rw [if_neg h]} },
  rw [if_neg h, cramer_map, det_transpose],
  apply det_zero_of_column_eq _ _ _ h,
  rw [replace_column_self, replace_column_ne],
  intro j_eq_i,
  exact h j_eq_i.symm
end

lemma sum_cramer {β} (s : finset β) (i : n) (f : n → β → α) :
  s.sum (λ x, (cramer_at A i).to_fun (λ j, f j x)) = (cramer_at A i).to_fun (λ j, s.sum (λ x, f j x))
:= calc s.sum (λ x, (cramer_at A i).to_fun (λ j, f j x))
    = (cramer_at A i).to_fun (sum s (λ (x : β) (j : n), f j x)) :
  by {erw [←(@linear_map.map_sum _ _ _ _ _ _ _ _ (cramer_at A i) _ _ (λ x j, f j x))], refl}
... = (cramer_at A i).to_fun (λ (j : n), s.sum (λ x, f j x)) :
  by {congr, ext j, apply pi.finset_sum_apply}

end cramer

/-
/-- A useful lemma if you want to rewrite `fin.pred_above`. -/
def fin.pred_above_congr {i i' j j' : fin n.succ} (h : j ≠ i) (hi : i = i') (hj : j = j') :
  fin.pred_above i j h = fin.pred_above i' j' (λ p, h (trans hj (trans p (symm hi)))) := by {congr; finish}

/-- Extend the function `f` by setting `f i = j` and moving the other values out of the way. -/
def fin.insert (i j : fin n.succ) (f : fin n → fin n) (k : fin n.succ) : fin n.succ :=
if h : k = i then j else fin.succ_above j (f (fin.pred_above i k h))

lemma fin.insert_eq {i j : fin n.succ} {f : fin n → fin n} {k : fin n.succ} : k = i ↔ fin.insert i j f k = j
:= begin
  apply iff.intro; intro hi,
  { simp [hi, fin.insert] },
  { by_contradiction hk,
    rw [fin.insert, dif_neg hk] at hi,
    exact fin.succ_above_ne _ _ hi
  }
end

lemma fin.insert_self {i j : fin n.succ} {f : fin n → fin n} : fin.insert i j f i = j
:= fin.insert_eq.mp rfl

lemma fin.insert_ne {i j : fin n.succ} {f : fin n → fin n} {k : fin n.succ} (h : k ≠ i) :
  fin.insert i j f k = fin.succ_above j (f (fin.pred_above i k h)) := dif_neg h

lemma fin.insert_succ_above {i j : fin n.succ} {f : fin n → fin n} {k : fin n} :
  fin.insert i j f (fin.succ_above i k) = fin.succ_above j (f k) :=
by rw [fin.insert_ne (fin.succ_above_ne _ _), fin.pred_above_succ_above]

def fin.delete (i : fin n.succ) (f : fin n.succ → fin n.succ) (h : ∀ k, f k = f i → k = i) (k : fin n) : fin n :=
fin.pred_above (f i) (f (fin.succ_above i k)) (λ p, fin.succ_above_ne _ _ (h _ p))

lemma fin.delete_insert (i j : fin n.succ) (f : fin n → fin n) (k : fin n) :
  fin.delete i (fin.insert i j f) (λ k p, fin.insert_eq.mpr (trans p fin.insert_self)) k = f k
:= calc
fin.delete i (fin.insert i j f) _ k
    = fin.pred_above (fin.insert i j f i) (fin.insert i j f (fin.succ_above i k)) _ : rfl
... = fin.pred_above j (fin.insert i j f (fin.succ_above i k)) _ : fin.pred_above_congr _ fin.insert_self rfl
... = fin.pred_above j (fin.succ_above j (f (fin.pred_above i (fin.succ_above i k) (fin.succ_above_ne _ _)))) _
  : fin.pred_above_congr _ rfl (fin.insert_ne _)
... = f (fin.pred_above i (fin.succ_above i k) (fin.succ_above_ne _ _)) : fin.pred_above_succ_above _ _ _
... = f k : by rw [fin.pred_above_succ_above]

lemma fin.left_inverse_insert (i j : fin n.succ) {f g : fin n → fin n} :
  function.left_inverse g f → function.left_inverse (fin.insert j i g) (fin.insert i j f) := begin
intros linv k,
by_cases k = i,
{ rw [h, fin.insert_self, fin.insert_self] },
have h' : fin.succ_above j (f (fin.pred_above i k h)) ≠ j := fin.succ_above_ne _ _,
rw [fin.insert_ne h, fin.insert_ne h', fin.pred_above_succ_above, linv, fin.succ_above_descend]
end

lemma fin.left_inverse_delete (i : fin n.succ) {f g : fin n.succ → fin n.succ}
  (hf : ∀ k, f k = f i → k = i) (hg : ∀ k, g k = g (f i) → k = f i) :
  function.left_inverse g f → function.left_inverse (fin.delete (f i) g hg) (fin.delete i f hf) := begin
intros linv k, calc
  fin.delete (f i) g hg (fin.delete i f hf k)
      = fin.pred_above (g (f i)) (g (fin.succ_above (f i) (fin.delete i f hf k))) _ : rfl
  ... = fin.pred_above i (g (f (fin.succ_above i _)) ) _
    : fin.pred_above_congr _ (linv i) (by {congr, apply fin.succ_above_descend})
  ... = fin.pred_above i (fin.succ_above i _) _
    : fin.pred_above_congr _ (refl i) (linv _)
  ... = k : fin.pred_above_succ_above _ _ _
end

lemma fin.right_inverse_delete (i : fin n.succ) {f g : fin n.succ → fin n.succ}
  (hf : ∀ k, f k = f i → k = i) (hg : ∀ k, g k = g (f i) → k = f i) :
  function.left_inverse g f → function.right_inverse g f →
  function.right_inverse (fin.delete (f i) g hg) (fin.delete i f hf) := begin
intros linv rinv k, calc -- TODO: cleanup!
  fin.delete i f hf (fin.delete (f i) g hg k) 
      = fin.pred_above (f i) (f (fin.succ_above i (fin.delete (f i) g hg k))) _ : rfl
  ... = fin.pred_above (f i) (f (fin.succ_above i (fin.pred_above (g (f i)) (g (fin.succ_above (f i) k)) _))) _
    : fin.pred_above_congr _ rfl (by {congr})
  ... = fin.pred_above (f i) (f (fin.succ_above i (fin.pred_above i (g (fin.succ_above (f i) k)) _))) _
    : fin.pred_above_congr _ rfl (by {congr' 2, apply fin.pred_above_congr, apply linv, refl})
  ... = fin.pred_above (f i) (f (g (fin.succ_above _ _))) _
    : fin.pred_above_congr _ rfl (by {congr, apply fin.succ_above_descend})
  ... = fin.pred_above (f i) (fin.succ_above (f i) _) _
    : fin.pred_above_congr _ rfl (rinv _)
  ... = k : fin.pred_above_succ_above _ _ (fin.succ_above_ne _ _)
end

def insert (i j : fin n.succ) (σ : equiv.perm (fin n)) : equiv.perm (fin n.succ) :=
⟨ fin.insert i j σ.to_fun
, fin.insert j i σ.inv_fun
, fin.left_inverse_insert i j σ.3
, fin.left_inverse_insert j i σ.4⟩

def delete (i : fin n.succ) (σ : equiv.perm (fin n.succ)) : equiv.perm (fin n) :=
⟨ fin.delete i σ.to_fun (λ k p, function.injective_of_left_inverse σ.3 p)
, fin.delete (σ i) σ.inv_fun (λ k p, function.injective_of_left_inverse σ.4 p)
, fin.left_inverse_delete i _ _ σ.3
, fin.right_inverse_delete i _ _ σ.3 σ.4⟩


lemma insert_to_fun {i j : fin n.succ} {σ : equiv.perm (fin n)} :
  (insert i j σ).to_fun = fin.insert i j (σ.to_fun) := rfl

lemma insert_self {i j : fin n.succ} {σ : equiv.perm (fin n)} : (insert i j σ).to_fun i = j :=
by rw [insert_to_fun, fin.insert_self]
lemma insert_eq {i j k : fin n.succ} {σ : equiv.perm (fin n)} : k = i ↔ (insert i j σ).to_fun k = j :=
fin.insert_eq

lemma insert_succ_above (i j : fin n.succ) (σ : equiv.perm (fin n)) (k : fin n) :
  (insert i j σ).to_fun (fin.succ_above i k) = fin.succ_above j (σ.to_fun k) := fin.insert_succ_above

lemma insert_inj (i j : fin n.succ) : function.injective (insert i j)
:= begin
  intros σ τ hins,
  ext k,
  calc σ.to_fun k
      = fin.pred_above j (fin.succ_above j (σ.to_fun k)) _ : symm (fin.pred_above_succ_above _ _ (fin.succ_above_ne _ _))
  ... = fin.pred_above j ((insert i j σ).to_fun (fin.succ_above i k)) (fin.succ_above_ne _ _ ∘ insert_eq.mpr)
    : by {congr, rw [insert_succ_above]}
  ... = fin.pred_above j ((insert i j τ).to_fun (fin.succ_above i k)) (fin.succ_above_ne _ _ ∘ insert_eq.mpr)
    : by {congr, assumption}
  ... = fin.pred_above j (fin.succ_above j (τ.to_fun k)) _ : fin.pred_above_congr _ rfl (insert_succ_above i j τ k)
  ... = τ.to_fun k : fin.pred_above_succ_above _ _ (fin.succ_above_ne _ _)
end

lemma insert_surj (i : fin n.succ) (σ : equiv.perm (fin n.succ)) : ∃ τ, σ = insert i (σ i) τ :=
⟨delete i σ, begin
  ext k,
  apply symm,
  by_cases k = i,
  { calc (insert i (σ.to_fun i) (delete i σ)).to_fun k
        = σ.to_fun i : dif_pos h
    ... = σ.to_fun k : by rw h },
  calc (insert i (σ.to_fun i) (delete i σ)).to_fun k
      = fin.succ_above (σ.to_fun i) (fin.pred_above (σ.to_fun i) (σ.to_fun (fin.succ_above i (fin.pred_above i k _))) _) : dif_neg h
  ... = σ.to_fun k : by rw [fin.succ_above_descend (σ.to_fun i), fin.succ_above_descend i]
end⟩
-/

section adjugate
variable [comm_ring α]
def adjugate (A : matrix n n α) : matrix n n α := λ i, cramer_map A (λ j, if i = j then 1 else 0)

lemma adjugate_val (A : matrix n n α) (i j : n) :
  adjugate A i j = cramer_map A (λ j, if i = j then 1 else 0) j := rfl

lemma mul_adjugate (A : matrix n n α) : A ⬝adjugate A = A.det • 1 := begin
  ext i j,
  rw [mul_val, smul_val],
  calc
    sum univ (λ (k : n), A i k * adjugate A k j)
        = sum univ (λ (k : n), A i k * (cramer_at A j).to_fun (λ j, if k = j then 1 else 0)) : rfl
    ... = sum univ (λ (k : n), (cramer_at A j).to_fun (λ j, if k = j then A i k else 0))
      : by {congr, ext, rw [cramer_at_val, mul_cramer_map_val], congr, ext,
            simp only [smul_val, smul_eq_mul, mul_ite, pi.smul_apply]}
    ... = (cramer_at A j).to_fun (λ j, sum univ (λ (k : n), if k = j then A i k else 0))
      : @sum_cramer n _ _ α _ A n univ j (λ (j k : n), if k = j then A i k else 0)
    ... = cramer_map A (A i) j : by { rw [cramer_at_val], congr, ext,
      erw [sum_ite (A i) (λ _, 0) id, sum_const_zero, filter_eq', if_pos (mem_univ _), sum_singleton],
      apply add_zero }
    ... = if i = j then det A else 0 : by rw [←cramer_val, cramer_column]
    ... = det A * (1 : matrix n n α) i j : by simp [one_val]
end
end adjugate

section field
variables [field α]

def inv (A : matrix n n α) : matrix n n α := (A.det)⁻¹ • adjugate A

lemma mul_inv (A : matrix n n α) (nonsing : A.det ≠ 0) : A ⬝ inv A = 1 :=
by { rw [inv, mul_smul, mul_adjugate, smul_smul, inv_mul_cancel nonsing],
     -- TODO: why do we need to explicitly construct this instance?
     exact @one_smul α (matrix n n α) _ (@pi.mul_action n (λ _, n → α) α _ (λ _, @pi.mul_action n (λ _, α) α _ (λ _, distrib_mul_action.to_mul_action α α))) (1 : matrix n n α) }

end field
end matrix
