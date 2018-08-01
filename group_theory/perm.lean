/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.mu2

universes u v
open equiv function finset fintype
variables {α : Type u} {β : Type v} [decidable_eq α]

namespace equiv.perm

def lift_fin [fintype α] (f : perm (fin (card α)) → β) 
  (h : ∀ a b : perm (fin (card α)), is_conj a b → f a = f b) (a : perm α) : β :=
trunc.lift (λ e : α ≃ fin (card α), f ((e.symm.trans a).trans e)) 
(λ d e, h _ _ ⟨d.symm.trans e, begin
    refine equiv.ext _ _ (λ x, _),
    rw inv_def,
    simp,
  end⟩)
(equiv_fin α)

instance lift_fin.is_group_hom [fintype α] [group β] 
  (f : perm (fin (card α)) → β) [is_group_hom f]
  (h : ∀ a b : perm (fin (card α)), is_conj a b → f a = f b) :
  is_group_hom (lift_fin f h) :=
⟨begin
  assume a b,
  unfold lift_fin,
  refine trunc.induction_on (equiv_fin α) (λ e, _),
  rw [trunc.lift_beta, trunc.lift_beta, trunc.lift_beta, ← is_group_hom.mul f],
  exact congr_arg f (equiv.ext _ _ (λ x, by simp))
end⟩

lemma swap_mul_swap_mul_swap {x y z : α} (hwz: x ≠ y) (hxz : x ≠ z) : 
  swap y z * swap x y * swap y z = swap z x :=
equiv.ext _ _ $ λ n, by simp only [swap_apply_def, mul_apply]; split_ifs; cc

lemma swap_conj {w x y z : α} (hwx : w ≠ x) (hyz : y ≠ z) : is_conj (swap w x) (swap y z) :=
have h : ∀ {y z : α}, y ≠ z → w ≠ z →
    (swap w y * swap x z) * swap w x * (swap w y * swap x z)⁻¹ = swap y z :=
  λ y z hyz hwz, by rw [mul_inv_rev, swap_inv, swap_inv, mul_assoc (swap w y), 
    mul_assoc (swap w y),  ← mul_assoc _ (swap x z), swap_mul_swap_mul_swap hwx hwz,
    ← mul_assoc, swap_mul_swap_mul_swap hwz.symm hyz.symm],
if hwz : w = z
then have hwy : w ≠ y, by cc,
  ⟨swap w z * swap x y, by rw [swap_comm y z, h hyz.symm hwy]⟩
else ⟨swap w y * swap x z, h hyz hwz⟩

/-- set of all pairs (⟨a, b⟩ : Σ a : fin n, fin n) such that b < a -/
def fin_pairs_lt (n : ℕ) : finset (Σ a : fin n, fin n) :=
(univ : finset (fin n)).sigma (λ a, (range a.1).attach_fin
  (λ m hm, lt_trans (mem_range.1 hm) a.2))

lemma mem_fin_pairs_lt {n : ℕ} {a : Σ a : fin n, fin n} :
  a ∈ fin_pairs_lt n ↔ a.2 < a.1 :=
by simp [fin_pairs_lt, fin.lt_def]

def sign_aux {n : ℕ} (a : perm (fin n)) : mu2 :=
(fin_pairs_lt n).prod
(λ x, if a x.1 ≤ a x.2 then -1 else 1)

@[simp] lemma sign_aux_one (n : ℕ) : sign_aux (1 : perm (fin n)) = 1 :=
begin
  unfold sign_aux,
  conv { to_rhs, rw ← @finset.prod_const_one _ mu2
    (fin_pairs_lt n) },
  exact finset.prod_congr rfl (λ a ha, if_neg 
    (not_le_of_gt (mem_fin_pairs_lt.1 ha)))
end

def sign_bij_aux {n : ℕ} (f : perm (fin n)) (a : Σ a : fin n, fin n) :
  Σ a : fin n, fin n :=
if hxa : f a.2 < f a.1
then ⟨f a.1, f a.2⟩
else ⟨f a.2, f a.1⟩

lemma sign_bij_aux_inj {n : ℕ} {f : perm (fin n)} : ∀ a b : Σ a : fin n, fin n,
   a ∈ fin_pairs_lt n → b ∈ fin_pairs_lt n → 
   sign_bij_aux f a = sign_bij_aux f b → a = b :=
λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb h, begin
  unfold sign_bij_aux at h,
  rw mem_fin_pairs_lt at *,
  have : ¬b₁ < b₂ := not_lt_of_ge (le_of_lt hb),
  split_ifs at h;
  simp [*, injective.eq_iff f.bijective.1, sigma.mk.inj_eq] at *
end

lemma sign_bij_aux_surj {n : ℕ} {f : perm (fin n)} : ∀ a ∈ fin_pairs_lt n,
  ∃ b ∈ fin_pairs_lt n, a = sign_bij_aux f b :=
λ ⟨a₁, a₂⟩ ha,
if hxa : f⁻¹ a₂ < f⁻¹ a₁
then ⟨⟨f⁻¹ a₁, f⁻¹ a₂⟩, mem_fin_pairs_lt.2 hxa,
  by dsimp [sign_bij_aux];
    rw [apply_inv_self, apply_inv_self, dif_pos (mem_fin_pairs_lt.1 ha)]⟩
else ⟨⟨f⁻¹ a₂, f⁻¹ a₁⟩, mem_fin_pairs_lt.2 $ lt_of_le_of_ne
  (le_of_not_gt hxa) $ λ h,
    by simpa [mem_fin_pairs_lt, (f⁻¹).bijective.1 h, lt_irrefl] using ha,
  by dsimp [sign_bij_aux];
    rw [apply_inv_self, apply_inv_self, 
      dif_neg (not_lt_of_ge (le_of_lt (mem_fin_pairs_lt.1 ha)))]⟩

lemma sign_bij_aux_mem {n : ℕ} {f : perm (fin n)}: ∀ a : Σ a : fin n, fin n,
  a ∈ fin_pairs_lt n → sign_bij_aux f a ∈ fin_pairs_lt n :=
λ ⟨a₁, a₂⟩ ha, begin
  unfold sign_bij_aux,
  split_ifs with h,
  { exact mem_fin_pairs_lt.2 h },
  { exact mem_fin_pairs_lt.2
    (lt_of_le_of_ne (le_of_not_gt h)
      (λ h, ne_of_lt (mem_fin_pairs_lt.1 ha) (f.bijective.1 h.symm))) }
end

@[simp] lemma sign_aux_inv {n : ℕ} (f : perm (fin n)) : sign_aux f⁻¹ = sign_aux f :=
prod_bij (λ a ha, sign_bij_aux f⁻¹ a)
sign_bij_aux_mem
(λ ⟨a, b⟩ hab, if h : f⁻¹ b < f⁻¹ a
  then by rw [sign_bij_aux, dif_pos h, if_neg (not_le_of_gt h), apply_inv_self,
    apply_inv_self, if_neg (not_le_of_gt $ mem_fin_pairs_lt.1 hab)]
  else by rw [sign_bij_aux, if_pos (le_of_not_gt h), dif_neg h, apply_inv_self,
    apply_inv_self, if_pos (le_of_lt $ mem_fin_pairs_lt.1 hab)])
sign_bij_aux_inj
sign_bij_aux_surj

lemma sign_aux_mul {n : ℕ} (f g : perm (fin n)) :
  sign_aux (f * g) = sign_aux f * sign_aux g :=
begin
  rw ← sign_aux_inv g,
  unfold sign_aux,
  rw  ← prod_mul_distrib,
  refine prod_bij (λ a ha, sign_bij_aux g a) sign_bij_aux_mem _ 
    sign_bij_aux_inj sign_bij_aux_surj,
  rintros ⟨a, b⟩ hab,
  rw [sign_bij_aux, mul_apply, mul_apply],
  rw mem_fin_pairs_lt at hab,
  by_cases h : g b < g a,
  { rw dif_pos h,
    simp [not_le_of_gt hab]; congr },
  { rw [dif_neg h, inv_apply_self, inv_apply_self, if_pos (le_of_lt hab)],
    by_cases h₁ : f (g b) ≤ f (g a),
    { have : f (g b) ≠ f (g a),
      { rw [ne.def, injective.eq_iff f.bijective.1, 
          injective.eq_iff g.bijective.1];
        exact ne_of_lt hab },
      rw [if_pos h₁, if_neg (not_le_of_gt  (lt_of_le_of_ne h₁ this))],
      refl },
    { rw [if_neg h₁, if_pos (le_of_lt (lt_of_not_ge h₁))],
      refl } }
end

instance sign_aux.is_group_hom {n : ℕ} : is_group_hom (@sign_aux n) := ⟨sign_aux_mul⟩

private lemma sign_aux_swap_zero_one {n : ℕ} (hn : 2 ≤ n) :
  sign_aux (swap (⟨0, lt_of_lt_of_le dec_trivial hn⟩ : fin n) 
  ⟨1, lt_of_lt_of_le dec_trivial hn⟩) = -1 :=
let zero : fin n := ⟨0, lt_of_lt_of_le dec_trivial hn⟩ in
let one : fin n := ⟨1, lt_of_lt_of_le dec_trivial hn⟩ in
have hzo : zero < one := dec_trivial,
show sign_aux (swap zero one) = sign_aux (swap 
  (⟨0, dec_trivial⟩ : fin 2) ⟨1, dec_trivial⟩),
begin
  refine eq.symm (prod_bij_ne_one (λ _ _ _, ⟨one, zero⟩) 
    (λ _ _ _, mem_fin_pairs_lt.2 hzo) dec_trivial
    (λ a ha₁ ha₂, ⟨⟨⟨1, dec_trivial⟩, ⟨0, dec_trivial⟩⟩, dec_trivial, dec_trivial, _⟩)
    dec_trivial),
  replace ha₂ : ite (a.fst = zero) one (ite (a.fst = one) zero (a.fst)) ≤ 
      ite (a.snd = zero) one (ite (a.snd = one) zero (a.snd)) := 
    by_contradiction (λ h, ha₂ (if_neg h)),
  replace ha₁ := mem_fin_pairs_lt.1 ha₁,
  cases a with a₁ a₂,
  have : ¬ one ≤ zero := dec_trivial,
  have : ∀ a : fin n, ¬a < zero := λ a, nat.not_lt_zero a.1,
  have : a₂ < one → a₂ = zero := λ h, fin.eq_of_veq 
    (nat.le_zero_iff.1 (nat.le_of_lt_succ h)),
  have : a₁ ≤ one → a₁ = zero ∨ a₁ = one := fin.cases_on a₁ 
    (λ a, nat.cases_on a (λ _ _, or.inl dec_trivial) 
    (λ a, nat.cases_on a (λ _ _, or.inr dec_trivial)
    (λ _ _ h, absurd h dec_trivial))),
  have : a₁ ≤ zero → a₁ = zero := fin.eq_of_veq ∘ nat.le_zero_iff.1,
  have : a₁ ≤ a₂ → a₂ < a₁ → false := not_lt_of_ge,
  split_ifs at ha₂;
  simp [*, lt_irrefl, -not_lt] at *
end

lemma sign_aux_swap : ∀ {n : ℕ} {x y : fin n} (hxy : x ≠ y),
  sign_aux (swap x y) = -1
| 0 := dec_trivial
| 1 := dec_trivial
| (n+2) := λ x y hxy, 
let ⟨f, hf⟩ := swap_conj (show (⟨0, dec_trivial⟩ : fin (n + 2)) ≠
  ⟨1, dec_trivial⟩, from dec_trivial) hxy in
have h2n : 2 ≤ n + 2 := dec_trivial,
by rw [← hf, sign_aux_mul, sign_aux_mul, sign_aux_swap_zero_one h2n,
  mul_right_comm, ← sign_aux_mul, mul_inv_self, sign_aux_one, one_mul]

/-- `sign` of a permutation returns the signature or parity of a permutation, `1` for e
It is the unique surjective group homomorphism from `perm α` to the group with two elements.-/
def sign [fintype α] (f : perm α) : mu2 :=
lift_fin sign_aux (λ a b h, is_conj_iff_eq.1 (is_group_hom.is_conj sign_aux h)) f

instance sign.is_group_hom [fintype α] :is_group_hom (sign : perm α → mu2) :=
lift_fin.is_group_hom _ _

lemma sign_swap [fintype α] {x y : α} (h : x ≠ y) :
  sign (swap x y) = -1 :=
begin
  unfold sign lift_fin,
  refine trunc.induction_on (fintype.equiv_fin α) (λ f, _),
  rw [trunc.lift_beta, symm_trans_swap_trans, 
    sign_aux_swap (mt (injective.eq_iff f.bijective.1).1 h)]
end

def is_swap (f : perm α) := ∃ x y : α, x ≠ y ∧ f = swap x y

lemma sign_eq_of_is_swap [fintype α] {f : perm α} (h : is_swap f) :
  sign f = -1 :=
let ⟨x, y, hxy⟩ := h in hxy.2.symm ▸ sign_swap hxy.1

def support [fintype α] (f : perm α) := 
(@univ α _).filter (λ x, f x ≠ x)

@[simp] lemma mem_support_iff [fintype α] {f : perm α} {a : α} :
  a ∈ f.support ↔ f a ≠ a := by simp [support]

@[simp] lemma support_eq_empty [fintype α] {f : perm α} :
  f.support = ∅ ↔ f = 1 :=
⟨λ h, equiv.ext _ _ (by simpa [finset.eq_empty_iff_forall_not_mem] using h), 
  λ h, by simp [h, finset.eq_empty_iff_forall_not_mem]⟩

lemma support_swap_mul [fintype α] {f : perm α} {x : α}
  {y : α} (hy : (swap x (f x) * f) y ≠ y) : f y ≠ y ∧ y ≠ x :=
begin
  simp only [swap_apply_def, mul_apply, injective.eq_iff f.bijective.1] at *,
  by_cases h : f y = x,
  { split; intro; simp * at * },
  { split_ifs at hy; cc }
end

def swap_factors_aux [fintype α] : Π (l : list α) (f : perm α), (∀ {x}, f x ≠ x → x ∈ l) →
  l.nodup → {l : list (perm α) // l.prod = f ∧ ∀ g ∈ l, is_swap g}
| []       := λ f h _, ⟨[], equiv.ext _ _ $ λ x, by rw [list.prod_nil];
    exact eq.symm (not_not.1 (mt h (list.not_mem_nil _))),
  by simp⟩
| (x :: l) := λ f h hnd,
let m := swap_factors_aux l (swap x (f x) * f)
  (λ y hy, have f y ≠ y ∧ y ≠ x, from support_swap_mul hy,
  list.mem_of_ne_of_mem this.2 (h this.1))
  (list.nodup_of_nodup_cons hnd) in
⟨if x = f x then m.1 else swap x (f x) :: m.1,
if hxfx : x = f x
  then by have := m.2.1;
    rw [if_pos hxfx, this, ← hxfx, swap_self, ← one_def, one_mul]
  else by rw [if_neg hxfx, list.prod_cons, m.2.1, ← mul_assoc,
    mul_def (swap x (f x)), swap_swap, ← one_def, one_mul], 
λ g hg, begin
  split_ifs at hg with hx hx,
  { exact m.2.2 _ hg },
  { exact ((list.mem_cons_iff _ _ _).1 hg).elim (λ hgx, ⟨x, f x, hx, hgx⟩) (m.2.2 _) }
end⟩

/-- `swap_factors` represents a permutation as a product of a list of transpositions. 
The representation is non unique and depends on the order. For types without linear order
`trunc_swap_factors` can be used -/
def swap_factors [fintype α] [decidable_linear_order α] (f : perm α) :
  {l : list (perm α) // l.prod = f ∧ ∀ g ∈ l, is_swap g} :=
swap_factors_aux ((@univ α _).sort (≤)) f (λ _ _, (mem_sort _).2 (mem_univ _))
(sort_nodup _ _)

def trunc_swap_factors [fintype α] (f : perm α) :
  trunc {l : list (perm α) // l.prod = f ∧ ∀ g ∈ l, is_swap g} :=
quotient.rec_on_subsingleton (@univ α _).1
(λ l h, trunc.mk (swap_factors_aux l f h.2 h.1))
(show (@univ α _).1.nodup ∧ ∀ {x}, f x ≠ x → x ∈ (@univ α _).1, 
  from ⟨(@univ α _).2, λ _ _, mem_univ _⟩)

lemma eq_sign_of_surjective_hom [fintype α] {s : perm α → mu2}
  [is_group_hom s] (hs : surjective s) : s = sign :=
have ∀ {f}, is_swap f → s f = -1 :=
  λ f ⟨x, y, hxy, hxy'⟩, hxy'.symm ▸ classical.by_contradiction (λ h, 
    have ∀ f, is_swap f → s f = 1 := λ f ⟨a, b, hab, hab'⟩,
      is_conj_iff_eq.1 begin
      rw [← mu2.ne_neg_one_iff.1 h, hab'],
      exact is_group_hom.is_conj _ (swap_conj hab hxy),
    end,
  let ⟨g, hg⟩ := hs (-1) in
  let ⟨l, hl⟩ := trunc.out (trunc_swap_factors g) in
  have ∀ a ∈ l.map s, a = (1 : mu2) := λ a ha,
    let ⟨g, hg⟩ := list.mem_map.1 ha in hg.2 ▸ this _ (hl.2 _ hg.1),
  have s l.prod = 1,
    by rw [is_group_hom.prod s, list.eq_repeat'.2 this, list.prod_repeat, one_pow],
  by simp [hl.1.symm, this] at hg;
    contradiction),
funext $ λ f,
let ⟨l, hl₁, hl₂⟩ := trunc.out (trunc_swap_factors f) in
have hsl : ∀ a ∈ l.map s, a = (-1 : mu2) := λ a ha,
  let ⟨g, hg⟩ := list.mem_map.1 ha in hg.2 ▸  this (hl₂ _ hg.1),
have hsignl :  ∀ a ∈ l.map sign, a = (-1 : mu2) := λ a ha,
  let ⟨g, hg⟩ := list.mem_map.1 ha in hg.2 ▸ sign_eq_of_is_swap (hl₂ _ hg.1),
by rw [← hl₁, is_group_hom.prod s, is_group_hom.prod (@sign α _ _),
  list.eq_repeat'.2 hsl, list.eq_repeat'.2 hsignl, list.length_map, list.length_map]

end equiv.perm