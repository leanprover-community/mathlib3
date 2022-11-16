import analysis.special_functions.log.basic
import topology.algebra.order.intermediate_value
import group_theory.perm.fibered
import group_theory.free_group
import algebra.free_prod
import data.bool.count
import algebra.free_monoid.count
import algebra.char_p.two
import data.zmod.parity

/-!
-/

noncomputable theory
open list set function cardinal
open_locale cardinal

local notation `L` := list bool
local notation `ℤ₂` := mul_z2
local notation `σ` := mul_z2.a

namespace grigorchuk_group

@[derive decidable_eq]
inductive generator
| a : generator
| bcd : fin 3 → generator

namespace generator

def to_fun : generator → L → L
| _ [] := []
| a (x::xs) := (!x::xs)
| (bcd n) (ff :: l) := ff :: (if n = 0 then l else to_fun a l)
| (bcd n) (tt :: l) := tt :: to_fun (bcd (n + 1)) l

instance : has_coe_to_fun generator (λ _, L → L) := ⟨to_fun⟩

@[simp] lemma to_fun_eq_coe : to_fun = coe_fn := rfl

def b := bcd 0
def c := bcd 1
def d := bcd 2

@[simp] lemma range_bcd : range bcd = {b, c, d} :=
by { simp only [fin.range_fin_succ, range_unique], refl }

@[simp] lemma apply_nil (x : generator) : x [] = [] := by cases x; refl

@[simp] lemma a_cons (x : bool) (l : L) : a (x :: l) = !x :: l := rfl

protected lemma «forall» {p : generator → Prop} : (∀ x, p x) ↔ p a ∧ ∀ n, p (bcd n) :=
⟨λ h, ⟨h a, λ n, h (bcd n)⟩, λ h, by { rintro (_|n), exacts [h.1, h.2 n] }⟩

protected lemma forall' {p : generator → Prop} : (∀ x, p x) ↔ p a ∧ p b ∧ p c ∧ p d :=
by { rw [generator.forall, fin.forall_fin_succ, fin.forall_fin_two], refl }

protected lemma «exists» {p : generator → Prop} : (∃ x, p x) ↔ p a ∨ ∃ n, p (bcd n) :=
⟨by { rintro ⟨_|n, h⟩, exacts [or.inl h, or.inr ⟨n, h⟩] },
  λ h, h.elim (λ ha, ⟨a, ha⟩) (λ ⟨n, hn⟩, ⟨bcd n, hn⟩)⟩

protected lemma exists' {p : generator → Prop} : (∃ x, p x) ↔ p a ∨ p b ∨ p c ∨ p d :=
by { rw [generator.exists, fin.exists_fin_succ, fin.exists_fin_two], refl }

lemma range_eq {α} (f : generator → α) : range f = {f a, f b, f c, f d} :=
set.ext $ λ y, by { simp only [set.mem_range, generator.exists', @eq_comm _ _ y], refl }

def equiv_with_bot : generator ≃ with_bot (fin 3) :=
{ to_fun := λ x, generator.cases_on x ⊥ coe,
  inv_fun := λ x, with_bot.rec_bot_coe a bcd x,
  left_inv := generator.forall.2 ⟨rfl, λ n, rfl⟩,
  right_inv := option.forall.2 ⟨rfl, λ n, rfl⟩ }

lemma a_ne_bcd (n : fin 3) : a ≠ bcd n .
lemma bcd_ne_a (n : fin 3) : bcd n ≠ a .

instance : fintype generator := @fintype.of_equiv _ _ option.fintype equiv_with_bot.symm
instance : encodable generator := @encodable.of_equiv _ _ option.encodable equiv_with_bot
instance : nontrivial generator := nontrivial_of_ne _ _ (a_ne_bcd 0)

lemma bcd_cons_ff (n : fin 3) (l : L) : bcd n (ff :: l) = ff :: if n = 0 then l else a l :=
rfl

@[simp] lemma bcd_cons_tt (n : fin 3) (l : L) : bcd n (tt :: l) = tt :: bcd (n + 1) l := rfl

@[simp] lemma length_apply : ∀ (x : generator) (l : L),
  length (x l) = length l
| _ [] := by rw [apply_nil]
| a (y::l) := rfl
| (bcd n) (tt::l) := by rw [bcd_cons_tt, length_cons, length_apply, length_cons]
| (bcd n) (ff::l) :=
  by { rw [bcd_cons_ff], split_ifs, { refl }, { rw [length_cons, length_apply, length_cons] } }

protected lemma involutive : ∀ x : generator, involutive x
| _ [] := by rw [apply_nil, apply_nil]
| a (x::l) := by rw [a_cons, a_cons, bnot_bnot]
| (bcd n) (tt::l) := by rw [bcd_cons_tt, bcd_cons_tt, involutive]
| (bcd n) (ff::l) := by { rw [bcd_cons_ff, bcd_cons_ff], split_ifs; simp [involutive a l] }

@[simp] lemma apply_apply (x : generator) (l : L) : x (x l) = l := x.involutive l
@[simp] lemma comp_self (x : generator) : x ∘ x = id := x.involutive.comp_self

protected lemma bijective (x : generator) : bijective x := x.involutive.bijective
protected lemma injective (x : generator) : injective x := x.involutive.injective
protected lemma surjective (x : generator) : surjective x := x.involutive.surjective

@[simp] lemma apply_eq_iff (x : generator) {l₁ l₂ : L} : x l₁ = x l₂ ↔ l₁ = l₂ :=
x.injective.eq_iff

lemma bcd_apply_bcd_of_ne {m n : fin 3} (h : m ≠ n) (l : L) :
  bcd m (bcd n l) = bcd (-m - n) l :=
begin
  induction l with x l ihl generalizing m n, { refl },
  cases x,
  { simp only [bcd_cons_ff], refine ⟨rfl, _⟩,
    have h2 : (2 : fin 3) = -1 := rfl,
    fin_cases n; fin_cases m; try { exact absurd rfl h }; simp only [h2, if_pos rfl, neg_eq_zero,
      neg_neg, if_neg one_ne_zero, sub_zero, sub_self, neg_zero, zero_sub, apply_apply] },
  { replace h : m + 1 ≠ n + 1 := mt add_right_cancel h,
    have h2 : (-1 - 1 : fin 3) = 1 := rfl,
    simp only [bcd_cons_tt, ihl h, neg_add, add_sub_add_comm, h2, eq_self_iff_true, true_and] }
end

lemma bcd_comp_bcd_of_ne {m n : fin 3} (h : m ≠ n) : bcd m ∘ bcd n = bcd (-m -n) :=
funext $ bcd_apply_bcd_of_ne h

@[simp] lemma b_apply_c (l : L) : b (c l) = d l := bcd_apply_bcd_of_ne dec_trivial l
@[simp] lemma c_apply_b (l : L) : c (b l) = d l := bcd_apply_bcd_of_ne dec_trivial l
@[simp] lemma b_apply_d (l : L) : b (d l) = c l := bcd_apply_bcd_of_ne dec_trivial l
@[simp] lemma d_apply_b (l : L) : d (b l) = c l := bcd_apply_bcd_of_ne dec_trivial l
@[simp] lemma c_apply_d (l : L) : c (d l) = b l := bcd_apply_bcd_of_ne dec_trivial l
@[simp] lemma d_apply_c (l : L) : d (c l) = b l := bcd_apply_bcd_of_ne dec_trivial l

@[simp] lemma b_comp_c : b ∘ c = d := bcd_comp_bcd_of_ne dec_trivial
@[simp] lemma c_comp_b : c ∘ b = d := bcd_comp_bcd_of_ne dec_trivial
@[simp] lemma b_comp_d : b ∘ d = c := bcd_comp_bcd_of_ne dec_trivial
@[simp] lemma d_comp_b : d ∘ b = c := bcd_comp_bcd_of_ne dec_trivial
@[simp] lemma c_comp_d : c ∘ d = b := bcd_comp_bcd_of_ne dec_trivial
@[simp] lemma d_comp_c : d ∘ c = b := bcd_comp_bcd_of_ne dec_trivial

@[simp] lemma head'_a : ∀ l : L, head' (a l) = (head' l).map bnot
| [] := rfl
| (x :: l) := rfl

@[simp] lemma head'_bcd (n : fin 3) : ∀ l : L, head' (bcd n l) = head' l
| [] := rfl
| (ff::l) := rfl
| (tt::l) := rfl

lemma coe_ne_id : ∀ x : generator, ⇑x ≠ id
| a := ne_iff.2 ⟨[ff], dec_trivial⟩
| (bcd ⟨0, _⟩) := ne_iff.2 ⟨[tt, ff, tt], dec_trivial⟩
| (bcd ⟨k + 1, _⟩) := ne_iff.2 ⟨[ff, tt], dec_trivial⟩

lemma to_fun_a_ne_bcd (n : fin 3) : ⇑a ≠ bcd n :=
λ h, absurd (congr_fun h [tt]) $ by simp

lemma to_fun_injective : injective to_fun :=
begin
  rintro (_|m) (_|n) h,
  { refl },
  { exact absurd h (to_fun_a_ne_bcd _) },
  { exact absurd h.symm (to_fun_a_ne_bcd _) },
  { rw [to_fun_eq_coe] at h, simp only,
    refine by_contra (λ hne, coe_ne_id (bcd (-m - n)) _),
    rw [← bcd_comp_bcd_of_ne hne, h, comp_self] }
end

instance equiv_like : equiv_like generator L L :=
{ coe := to_fun,
  inv := to_fun,
  left_inv := apply_apply,
  right_inv := apply_apply,
  coe_injective' := λ x y h₁ h₂, to_fun_injective h₁ }

end generator

open generator

@[derive [decidable_eq, group, mul_action (free_monoid (ℤ₂ ⊕ (ℤ₂ × ℤ₂)))]]
def word : Type := free_prod.word ℤ₂ (ℤ₂ × ℤ₂)

def word.fst : word →* ℤ₂ := free_prod.word.fst

def word.even_a : subgroup word := monoid_hom.ker word.fst

@[derive [decidable_eq, group]]
def even_a_word : Type := free_prod.word (ℤ₂ × ℤ₂) (ℤ₂ × ℤ₂)

namespace even_a_word

def equiv_ker : even_a_word ≃* word.even_a := free_prod.word.z2_prod_mker_fst

def proj₁ : ℤ₂ × ℤ₂ →* word := free_prod.word.inl.comp (monoid_hom.fst _ _ * monoid_hom.snd _ _)

def proj₂ : ℤ₂ × ℤ₂ →* word :=
free_prod.word.inr.comp $ (monoid_hom.fst _ _ * monoid_hom.snd _ _).prod (monoid_hom.fst _ _)

def proj : even_a_word →* word × word :=
free_prod.word.lift (proj₁.prod proj₂) (proj₂.prod proj₁)

@[simp] lemma proj_apply_inl (x : ℤ₂ × ℤ₂) : proj (free_prod.word.inl x) = (proj₁ x, proj₂ x) :=
free_prod.word.lift_apply_inl _ _ _

@[simp] lemma proj_apply_inr (x : ℤ₂ × ℤ₂) : proj (free_prod.word.inr x) = (proj₂ x, proj₁ x) :=
free_prod.word.lift_apply_inr _ _ _

lemma proj_apply_mk (l hl hr hc) :
  proj ⟨l, hl, hr, hc⟩ =
    ((l.map $ sum.elim proj₁ proj₂).prod, (l.map $ sum.elim proj₂ proj₁).prod) :=
begin
  rw [proj, free_prod.word.lift_apply_mk],
  clear hl hr hc,
  induction l with x l ihl,
  { refl },
  { cases x; simp only [map_cons, sum.elim_inl, sum.elim_inr, prod_cons, ihl,
      monoid_hom.prod_apply, prod.mk_mul_mk] }
end

lemma proj_apply (w : even_a_word) :
  proj w =
    ((w.1.map $ sum.elim proj₁ proj₂).prod, (w.1.map $ sum.elim proj₂ proj₁).prod) :=
by { cases w, apply proj_apply_mk }

end even_a_word

lemma exists_eta : ∃ η ∈ Ioo (0.81053 : ℝ) 0.81054, η ^ 3 + η ^ 2 + η = (2 : ℝ) :=
mem_image_iff_bex.1 $ intermediate_value_Ioo (by norm_num)
  (continuous.continuous_on $ by continuity) (by norm_num)

def eta : ℝ := exists_eta.some

local notation `η` := grigorchuk_group.eta

lemma eta_gt_081053 : 0.81053 < η := exists_eta.some_spec.fst.1
lemma eta_lt_081054 : η < 0.81054 := exists_eta.some_spec.fst.2
@[simp] lemma eta_def : η ^ 3 + η ^ 2 + η = 2 := exists_eta.some_spec.snd

lemma eta_gt_08 : 0.8 < η := lt_trans (by norm_num) eta_gt_081053
lemma eta_pos : 0 < η := lt_trans (by norm_num) eta_gt_08
lemma eta_nonneg : 0 ≤ η := eta_pos.le
lemma eta_lt_one : η < 1 := eta_lt_081054.trans (by norm_num)
lemma eta_le_one : η ≤ 1 := eta_lt_one.le
lemma eta_lt_two : η < 2 := eta_lt_one.trans one_lt_two

lemma eta_sq_lt_eta : η ^ 2 < η := pow_lt_self_of_lt_one eta_pos eta_lt_one one_lt_two
lemma eta_cube_lt_eta_sq : η ^ 3 < η ^ 2 := pow_lt_pow_of_lt_one eta_pos eta_lt_one dec_trivial
lemma eta_cube_lt_eta : η ^ 3 < η := eta_cube_lt_eta_sq.trans eta_sq_lt_eta

lemma one_lt_two_mul_eta_cube : 1 < 2 * η ^ 3 :=
calc 1 < 2 * 0.8 ^ 3 : by norm_num
   ... ≤ 2 * η ^ 3   :
  mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (by norm_num) eta_gt_08.le _) two_pos.le

lemma one_lt_eta_cube_add_self : 1 < η ^ 3 + η ^ 3 :=
one_lt_two_mul_eta_cube.trans_eq (two_mul _)

lemma one_lt_eta_cube_add_eta_sq : 1 < η ^ 3 + η ^ 2 :=
one_lt_eta_cube_add_self.trans $ add_lt_add_left eta_cube_lt_eta_sq _

lemma one_lt_eta_cube_add_eta : 1 < η ^ 3 + η :=
one_lt_eta_cube_add_eta_sq.trans $ add_lt_add_left eta_sq_lt_eta _

def weight₁ : ℤ₂ ⊕ ℤ₂ × ℤ₂ → ℝ :=
sum.elim (mul_z2.elim 0 (1 - η ^ 3)) $ uncurry $
  mul_z2.elim (mul_z2.elim 0 (η ^ 3)) (mul_z2.elim (1 - η ^ 2) (1 - η))

lemma one_sub_eta_le_weight₁ :
  ∀ {x : ℤ₂ ⊕ ℤ₂ × ℤ₂}, x ≠ sum.inl 1 → x ≠ sum.inr 1 → 1 - η ≤ weight₁ x
| (sum.inl 1) h _ := (h rfl).elim
| (sum.inl σ) _ _ := sub_le_sub_left eta_cube_lt_eta.le _
| (sum.inr (1, 1)) _ h := (h rfl).elim
| (sum.inr (1, σ)) _ _ := sub_le_iff_le_add.2 one_lt_eta_cube_add_eta.le
| (sum.inr (σ, 1)) _ _ := sub_le_sub_left eta_sq_lt_eta.le _
| (sum.inr (σ, σ)) _ _ := le_rfl

lemma weight₁_pos {x : ℤ₂ ⊕ ℤ₂ × ℤ₂} (hl : x ≠ sum.inl 1) (hr : x ≠ sum.inr 1) : 0 < weight₁ x :=
(sub_pos.2 eta_lt_one).trans_le (one_sub_eta_le_weight₁ hl hr)

lemma weight₁_le_eta_cube : ∀ x : ℤ₂ ⊕ ℤ₂ × ℤ₂, weight₁ x ≤ η ^ 3
| (sum.inl 1) := pow_nonneg eta_nonneg _
| (sum.inl σ) := sub_le_iff_le_add.2 one_lt_eta_cube_add_self.le
| (sum.inr (1, 1)) := pow_nonneg eta_nonneg _
| (sum.inr (1, σ)) := le_rfl
| (sum.inr (σ, 1)) := sub_le_iff_le_add.2 one_lt_eta_cube_add_eta_sq.le
| (sum.inr (σ, σ)) := sub_le_iff_le_add.2 one_lt_eta_cube_add_eta.le

lemma weight₁_lt_one (x : ℤ₂ ⊕ ℤ₂ × ℤ₂) : weight₁ x < 1 :=
(weight₁_le_eta_cube x).trans_lt $ pow_lt_one eta_nonneg eta_lt_one three_ne_zero

lemma weight₁_nonneg (x : ℤ₂ ⊕ ℤ₂ × ℤ₂) : 0 ≤ weight₁ x :=
begin
  rcases eq_or_ne x (sum.inl 1) with rfl|hl, { refl },
  rcases eq_or_ne x (sum.inr 1) with rfl|hr, { refl },
  exact (weight₁_pos hl hr).le
end

lemma weight₁_inl_mul_le : ∀ x y : ℤ₂,
  weight₁ (sum.inl (x * y)) ≤ weight₁ (sum.inl x) + weight₁ (sum.inl y) :=
mul_z2.forall.2
  ⟨λ y, by { rw [one_mul], exact (zero_add _).ge },
  mul_z2.forall.2 ⟨(add_zero _).ge, add_nonneg (weight₁_nonneg _) (weight₁_nonneg _)⟩⟩

lemma weight₁_inr_mul_le (x y : ℤ₂ × ℤ₂) :
  weight₁ (sum.inr (x * y)) ≤ weight₁ (sum.inr x) + weight₁ (sum.inr y) :=
begin
  have H₁ : 1 - η ≤ η ^ 3 + (1 - η ^ 2),
    from le_add_of_nonneg_of_le (pow_nonneg eta_nonneg _) (sub_le_sub_left eta_sq_lt_eta.le _),
  have H₂ : η ^ 3 ≤ (1 - η) + (1 - η ^ 2), { have := eta_def, linarith },
  have H₃ : 1 - η ^ 2 ≤ η ^ 3 + (1 - η),
  { have : η ≤ η ^ 3 + η ^ 2, from (eta_lt_one.trans one_lt_eta_cube_add_eta_sq).le,
    linarith },
  rcases eq_or_ne x 1 with rfl|hx, { rw [one_mul], exact (zero_add _).ge },
  rcases eq_or_ne y 1 with rfl|hy, { rw [mul_one], exact (add_zero _).ge },
  rcases eq_or_ne x y with rfl|hxy,
  { rw [show x * x = 1, by ext1; apply mul_z2.mul_self],
    exact add_nonneg (weight₁_nonneg _) (weight₁_nonneg _) },
  fin_cases x; try { exact absurd rfl hx }; fin_cases y; try { exact absurd rfl hy };
    try { exact absurd rfl hxy }; try { assumption }; exact le_of_le_of_eq ‹_› (add_comm _ _)
end

namespace word

@[simp] lemma index_even_a : even_a.index = 2 := by simp [even_a, fst, subgroup.index_ker]

lemma sq_mem_ker (w : word) : w ^ 2 ∈ even_a := subgroup.sq_mem_of_index_two index_even_a w

def weight (w : word) : ℝ := (w.to_list.map weight₁).sum

@[simp] lemma weight_cons' {x : ℤ₂ ⊕ ℤ₂ × ℤ₂} {w : word} (h) :
  weight (w.cons' x h) = weight₁ x + w.weight :=
begin
  simp only [weight, free_prod.word.cons'],
  split_ifs with hx,
  { rw [map_cons, sum_cons] },
  { simp only [ne.def, not_and_distrib, not_not] at hx,
    rw self_eq_add_left,
    rcases hx with rfl|rfl; refl }
end

@[simp] lemma weight_one : weight 1 = 0 := rfl

@[simp] lemma weight_of (x : ℤ₂ ⊕ ℤ₂ × ℤ₂) : weight (free_prod.word.of x) = weight₁ x :=
(weight_cons' _).trans (add_zero _)

lemma weight_nonneg (w : word) : 0 ≤ w.weight :=
sum_nonneg $ forall_mem_map_iff.2 $ λ x _, weight₁_nonneg x

lemma mul_length_le_weight (w : word) : (1 - η) * w.to_list.length ≤ w.weight :=
calc (1 - η) * w.to_list.length = (w.to_list.map weight₁).length • (1 - η) :
  by rw [length_map, nsmul_eq_mul, mul_comm]
... ≤ w.weight : card_nsmul_le_sum _ _ $ forall_mem_map_iff.2 $
  λ x hx, one_sub_eta_le_weight₁ (ne_of_mem_of_not_mem hx w.2) (ne_of_mem_of_not_mem hx w.3)

@[simp] lemma weight_pos {w : word} : 0 < w.weight ↔ w ≠ 1 :=
begin
  split,
  { rintro h rfl, exact h.ne rfl },
  intro hne,
  rw [ne.def, free_prod.word.ext_iff, free_prod.word.to_list_one, ← length_eq_zero] at hne,
  calc 0 < (1 - η) * w.to_list.length :
    mul_pos (sub_pos.2 eta_lt_one) (nat.cast_pos.2 $ pos_iff_ne_zero.2 hne)
  ... ≤ w.weight : mul_length_le_weight w
end

@[simp] lemma weight_eq_zero {w : word} : w.weight = 0 ↔ w = 1 :=
by rw [← weight_pos.not_left, not_lt, w.weight_nonneg.le_iff_eq]

lemma weight_cons_le (x : ℤ₂ ⊕ ℤ₂ × ℤ₂) (w : word) : weight (w.cons x) ≤ weight₁ x + weight w :=
begin
  cases x; rcases w with ⟨(_|⟨(y|y), l⟩), hl, hr, hc⟩;
    simp only [free_prod.word.cons, free_prod.word.cons_one, weight_cons', free_prod.word.tail,
      list.tail, weight_of, free_prod.word.mk_nil, weight_one, add_zero];
    simp only [weight, map_cons, sum_cons, ← add_assoc, add_le_add_iff_right, weight₁_inl_mul_le,
      weight₁_inr_mul_le],
end

lemma weight_smul_le (w₁ : free_monoid (ℤ₂ ⊕ ℤ₂ × ℤ₂)) (w₂ : word) :
  weight (w₁ • w₂) ≤ (w₁.to_list.map weight₁).sum + weight w₂ :=
begin
  induction w₁ using free_monoid.rec_on with x w₁ ihw, { exact (zero_add _).ge },
  calc weight ((free_monoid.of x * w₁) • w₂) ≤ weight₁ x + weight (w₁ • w₂) : weight_cons_le _ _
  ... ≤ weight₁ x + ((w₁.to_list.map weight₁).sum + weight w₂) : add_le_add_left ihw _
  ... = _ : by simp [add_assoc]
end

lemma weight_mul_le (w₁ w₂ : word) : weight (w₁ * w₂) ≤ weight w₁ + weight w₂ :=
weight_smul_le _ _

lemma weight_prod_le : ∀ l : list word, weight l.prod ≤ (l.map weight).sum
| [] := le_rfl
| (w :: l) :=
  begin
    rw [prod_cons, map_cons, sum_cons],
    exact (weight_mul_le _ _).trans (add_le_add_left (weight_prod_le _) _)
  end

/-
def to_conj_even_aux₁ : ∀ (n : ℕ) (l : list (ℤ₂ ⊕ ℤ₂ × ℤ₂)) (h : l.length = n), list (ℤ₂ ⊕ ℤ₂ × ℤ₂)
| 0 l h := l
| 1 l h := l
| (n + 2) (x :: l) h := if even n then x :: l
  else if hx : x.is_left = (l.last $ by { rintro rfl, simpa [bit0, ← add_assoc] using h }).is_left
  then _
  else _

def to_conj_even_aux : ∀ (n : ℕ) (w : word) (h : w.1.length = n),
  {w' : word // is_conj w w' ∧ (even (length w'.1) ∨ length (w'.1) = 1) ∧
    length w'.1 ≤ n ∧ weight w' ≤ weight w}
| 0 w h := ⟨w, is_conj.refl _, or.inl ⟨0, h⟩, h.le, le_rfl⟩
| 1 w h := ⟨w, is_conj.refl _, or.inr h, h.le, le_rfl⟩
| (n + 2) w h :=
  if hn : even n then ⟨w, is_conj.refl _, or.inl $ h.symm ▸ hn.add (even_bit0 _), h.le, le_rfl⟩
  else if hw : w.1.head' = w.1.last' then ⟨⟨init (tail w.1), _, _, _⟩, _⟩ else _
-/

end word

namespace even_a_word

lemma weight_proj₁_add_proj₂_eq {x : ℤ₂ × ℤ₂} (hx : x ≠ 1) :
  (proj₁ x).weight + (proj₂ x).weight = η * (weight₁ (sum.inl σ) + weight₁ (sum.inr x)) :=
begin
  fin_cases x with [(1, 1), (1, σ), (σ, 1), (σ, σ)]; simp only [proj₁, proj₂, monoid_hom.comp_apply,
    monoid_hom.mul_apply, monoid_hom.prod_apply, monoid_hom.coe_fst, monoid_hom.coe_snd, one_mul,
    mul_one, map_one, word.weight_one, zero_add, ← free_prod.word.of_inl, ← free_prod.word.of_inr,
    word.weight_of, mul_z2.mul_self],
  { exact absurd rfl hx },
  show 1 - η ^ 3 + (1 - η ^ 2) = η * (1 - η ^ 3 + η ^ 3),
  { linarith [eta_def] },
  show 1 - η ^ 3 + (1 - η) = η * (1 - η ^ 3 + (1 - η ^ 2)),
  { rw [← add_sub_add_comm, ← add_sub_add_comm, ← bit0, ← eta_def], ring },
  show 0 + η ^ 3 = η * (1 - η ^ 3 + (1 - η)),
  { rw [zero_add, ← add_sub_add_comm, ← bit0, ← eta_def], ring }
end

lemma weight_proj₁_add_proj₂_le (x : ℤ₂ × ℤ₂) :
  (proj₁ x).weight + (proj₂ x).weight ≤ η * (weight₁ (sum.inl σ) + weight₁ (sum.inr x)) :=
begin
  rcases ne_or_eq x 1 with hx|rfl,
  { exact (weight_proj₁_add_proj₂_eq hx).le },
  { refine le_trans _ (mul_nonneg eta_nonneg $ add_nonneg (weight₁_nonneg _) (weight₁_nonneg _)),
    simp }
end

lemma weight_proj_le_eta_mul_weight_add_length (w : even_a_word) :
  (proj w).1.weight + (proj w).2.weight ≤
    η * ((w.1.map $ sum.elim (weight₁ ∘ sum.inr) (weight₁ ∘ sum.inr)).sum +
      w.1.length * weight₁ (sum.inl σ)) :=
calc (proj w).1.weight + (proj w).2.weight
    = (map (sum.elim proj₁ proj₂) w.1).prod.weight + (map (sum.elim proj₂ proj₁) w.1).prod.weight :
  by simp only [proj_apply]
... ≤ ((map (sum.elim proj₁ proj₂) w.1).map word.weight).sum
      + ((map (sum.elim proj₂ proj₁) w.1).map word.weight).sum :
  add_le_add (word.weight_prod_le _) (word.weight_prod_le _)
... = (map (sum.elim (word.weight ∘ proj₁) (word.weight ∘ proj₂)
            + sum.elim (word.weight ∘ proj₂) (word.weight ∘ proj₁)) w.1).sum :
  by simp only [list.map_map, sum.comp_elim, sum_map_add, pi.add_def]
... = (map (sum.elim (word.weight ∘ proj₁ + word.weight ∘ proj₂)
        (word.weight ∘ proj₁ + word.weight ∘ proj₂)) w.1).sum :
  congr_arg _ $ congr_arg2 _ (funext $ sum.forall.2 ⟨λ _, rfl, λ _, add_comm _ _⟩) rfl
... ≤ (map (λ x, η * (weight₁ (sum.inl σ) +
        sum.elim (weight₁ ∘ sum.inr) (weight₁ ∘ sum.inr) x)) w.1).sum :
  sum_le_sum $ sum.forall.2
    ⟨λ x hx, weight_proj₁_add_proj₂_le _, λ x hx, weight_proj₁_add_proj₂_le _⟩
... = _ :
  by simp only [sum_map_mul_left, add_comm, sum_map_add, map_const, sum_repeat, nsmul_eq_mul]

lemma weight_equiv_ker (w : even_a_word) :
  word.weight (equiv_ker w) =
    (w.1.map (sum.elim (weight₁ ∘ sum.inr) (weight₁ ∘ sum.inr))).sum +
      2 * count tt (w.1.map sum.is_left) * weight₁ (sum.inl σ) :=
begin
  cases w with l hl hr hc,
  induction l with x l ihl,
  { simp only [free_prod.word.mk_nil, map_one, subtype.val_eq_coe, submonoid.coe_one,
      word.weight_one, map_nil, sum_nil, count_nil, nat.cast_zero, mul_zero, zero_mul, add_zero] },
  { replace ihl := let w := (free_prod.word.mk (x :: l) hl hr hc).tail in ihl w.2 w.3 w.4,
    simp only [subtype.val_eq_coe, word.weight, equiv_ker, map_cons, list.join,
      free_prod.word.to_list_coe_z2_prod_mker_fst, list.sum_append, map_append, sum_cons]
      at ihl ⊢,
    rw [ihl],
    cases x; simp only [list.map, sum.is_left, sum.elim_inl, sum.elim_inr, sum_cons, sum_nil,
      add_zero, comp_app, count_cons_self, count_cons_of_ne, ne.def, not_false_iff,
      nat.cast_succ]; ring }
end

lemma weight_proj_le (w : even_a_word) :
  (proj w).1.weight + (proj w).2.weight ≤ η * (word.weight (equiv_ker w) +
    (count ff (w.1.map sum.is_left) - count tt (w.1.map sum.is_left)) * weight₁ (sum.inl σ)) :=
w.weight_proj_le_eta_mul_weight_add_length.trans_eq $ by rw [weight_equiv_ker, add_assoc, ← add_mul,
  ← length_map sum.is_left, ← count_tt_add_count_ff, two_mul, add_add_sub_cancel, nat.cast_add]

lemma weight_proj_le_of_even (w : even_a_word) (hw : even w.to_list.length) :
  (proj w).1.weight + (proj w).2.weight ≤ η * word.weight (equiv_ker w) :=
w.weight_proj_le.trans_eq $ by rw [w.chain'_ne_map.count_ff_eq_count_tt (by rwa length_map),
  sub_self, zero_mul, add_zero]

lemma weight_proj_fst_eq_snd (w : word.even_a) (hw : even (length (w : word).1))

end even_a_word

#exit

@[derive [monoid, decidable_eq]] def word : Type := free_monoid generator

local notation `W` := word

namespace word

instance : denumerable W :=
@denumerable.of_encodable_of_infinite _ list.encodable list.infinite

instance : has_coe_t generator W := ⟨free_monoid.of⟩

lemma of_eq_coe : free_monoid.of = (coe : generator → W) := rfl
lemma length_coe (x : generator) : (x : W).to_list.length = 1 := rfl

@[elab_as_eliminator]
protected def rec_on {C : W → Sort*} (w : W) (h1 : C 1)
  (h : ∀ (a : generator) g, C g → C (a * g)) : C w :=
free_monoid.rec_on w h1 h

@[simp] lemma closure_abcd : submonoid.closure (range (coe : generator → W)) = ⊤ :=
free_monoid.closure_range_of

lemma cons_eq_mul (x : generator) (y : W) : x :: y = (x * y : W) := rfl

@[simp] lemma to_list_coe (x : generator) : free_monoid.to_list (x : W) = [x] := rfl

def parity (x : generator) : W →* ℤ₂ :=
(nat.cast_add_monoid_hom (zmod 2)).to_multiplicative.comp (free_monoid.count x)

lemma mem_mker_parity {x : generator} {g : W} : g ∈ (parity x).mker ↔ even (count x g) :=
zmod.eq_zero_iff_even

end word

def ncword_cancel : generator → generator → W
| a a := 1
| a (bcd n) := a * bcd n
| (bcd n) a := bcd n * a
| (bcd m) (bcd n) := if m = n then 1 else bcd (-m - n)

@[simp] lemma ncword_cancel_self (x) : ncword_cancel x x = 1 :=
by { cases x, exacts [rfl, if_pos rfl] }

lemma length_ncword_cancel_le : ∀ x y : generator, (ncword_cancel x y).to_list.length ≤ 2
| a a := zero_le _
| a (bcd n) := le_rfl
| (bcd n) a := le_rfl
| (bcd m) (bcd n) := by rcases eq_or_ne m n with rfl|hmn; simp [ncword_cancel, *]

def ncword_rel (x y : generator) : Prop := xor (x = a) (y = a)

local notation `R` := ncword_rel

lemma ncword_rel_comm {x y : generator} : R x y ↔ R y x := iff_of_eq (xor_comm _ _)

@[symm] lemma ncword_rel.symm {x y : generator} : R x y → R y x := ncword_rel_comm.1

@[simp] lemma ncword_rel_a {x} : R a x ↔ x ≠ a  := by simp [ncword_rel]

@[simp] lemma ncword_rel_bcd {n : fin 3} {x} : R (bcd n) x ↔ x = a :=
by simp [ncword_rel]

lemma ncword_rel_a_bcd {n} : R a (bcd n) := ncword_rel_a.2 (generator.bcd_ne_a n)
lemma ncword_rel_bcd_a {n} : R (bcd n) a := ncword_rel_a_bcd.symm
lemma not_ncword_rel_a_a : ¬R a a := mt ncword_rel_a.1 (λ h, h rfl)

lemma not_ncword_rel_bcd_bcd {m n} : ¬R (bcd m) (bcd n) :=
mt ncword_rel_bcd.1 (generator.bcd_ne_a _)

@[simp] lemma not_ncword_rel_same (x : generator) : ¬R x x := by simp [ncword_rel]

lemma ncword_rel.ne {x y : generator} (h : R x y) : x ≠ y :=
by { rintro rfl, exact not_ncword_rel_same _ h }

lemma forall_ncword_rel {r : generator → generator → Prop} :
  (∀ x y, R x y → r x y) ↔ (∀ n, r a (bcd n) ∧ r (bcd n) a) :=
by simp [generator.forall, ← forall_and_distrib]

lemma forall_not_ncword_rel {r : generator → generator → Prop} :
  (∀ x y, ¬R x y → r x y) ↔ r a a ∧ ∀ m n, r (bcd m) (bcd n) :=
begin
  refine ⟨λ h, ⟨h _ _ (not_ncword_rel_same _), λ m n, h _ _ not_ncword_rel_bcd_bcd⟩, _⟩,
  rintro ⟨ha, hb⟩ (_|m) (_|n); simp *
end

lemma forall_not_ncword_rel' {r : generator → generator → Prop} :
  (∀ x y, ¬R x y → r x y) ↔ (∀ x, r x x) ∧ ∀ m n, m ≠ n → r (bcd m) (bcd n) :=
forall_not_ncword_rel.trans
  ⟨λ h, ⟨λ x, generator.cases_on x h.1 $ λ n, h.2 _ _, λ m n _, h.2 m n⟩,
    λ h, ⟨h.1 _, λ m n, by { rcases eq_or_ne m n with rfl|hne, exacts [h.1 _, h.2 _ _ hne] }⟩⟩

def ncword_data : mul_ncword.group_data generator :=
{ cancel2 := ncword_cancel,
  r := R,
  cancel2_eq_self := forall_ncword_rel.2 $ λ n, ⟨rfl, rfl⟩,
  chain'_r_cancel2 := forall_not_ncword_rel'.2
    ⟨λ x, by simp only [ncword_cancel_self, chain'_nil, free_monoid.to_list_one],
      λ m n hne, by simp only [ncword_cancel, if_neg hne, word.to_list_coe, chain'_singleton]⟩,
  r_last'_cancel2 := forall_not_ncword_rel'.2 $
    ⟨λ _ _, by simp only [last', ncword_cancel_self, free_monoid.to_list_one, option.not_mem_none,
      false_implies_iff],
      λ m n hne y', by { simp only [ncword_cancel, if_neg hne, last', word.to_list_coe,
        option.mem_def, ncword_rel_bcd, forall_eq], rintro rfl, exact ncword_rel_bcd_a }⟩,
  cancel2_smul :=
    begin
      refine forall_not_ncword_rel'.2 ⟨λ x y w hyw hxy, _, λ m n hne z w h hz, _⟩,
      { simp only [ncword_cancel_self, one_smul],
        revert x y hxy hyw,
        refine forall_not_ncword_rel'.2 ⟨λ x hxw, _, λ m n hne hyw, _⟩,
        { simp only [ncword_cancel_self, mul_ncword.of_mul_cons, one_mul, mul_ncword.mk_word],
          exact mul_ncword.cons_eq_mul _ },
        { ext1,
          simp only [mul_ncword.of_mul_cons, ncword_cancel, if_neg hne, mul_ncword.cons_word,
            mul_ncword.mk_cons, mul_ncword.of_mul_cons, ← word.of_eq_coe],
          have : m ≠ -m - n,
          { rwa [← neg_one_mul, show (-1 : fin 3) = 2, from rfl, two_mul, add_sub_assoc, ne.def,
              eq_comm, add_right_eq_self, sub_eq_zero] },
          simp only [ncword_cancel, if_neg this, ← sub_add, sub_self, zero_add] } },
      { cases z with k, { exact (hz ncword_rel_bcd_a).elim },
        ext1,
        simp only [ncword_cancel, if_neg hne, mul_ncword.of_mul_cons, mul_ncword.of_smul,
          ← word.of_eq_coe],
        rcases eq_or_ne n k with rfl|hnk,
        { simp only [if_pos rfl, one_mul, mul_ncword.mk_word],
          rw [← mul_ncword.cons_eq_mul, mul_ncword.cons_word, if_neg, neg_sub, sub_neg_eq_add,
            add_sub_cancel'],
          { rwa [sub_eq_iff_eq_add, ← two_mul, show (2 : fin 3) = -1, from rfl, neg_one_mul,
              neg_inj] },
          { exact h.imp_head (λ z, ncword_rel_bcd.2 ∘ ncword_rel_bcd.1) } },
        { simp only [if_neg hnk, mul_ncword.mk_cons, mul_ncword.of_mul_cons, ncword_cancel,
            ← word.of_eq_coe, sub_eq_iff_eq_add, (@neg_eq_iff_neg_eq _ _ m _).trans eq_comm,
            neg_add_rev, ← sub_eq_add_neg],
          rcases eq_or_ne m k with rfl|hmk,
          { simp only [← sub_add, neg_sub, sub_neg_eq_add, add_sub_cancel, neg_add_cancel_comm] },
          { have : m = -n - k,
            { fin_cases m; fin_cases n; try { exact absurd rfl hne }; fin_cases k;
                try { exact absurd rfl hnk }; try { exact absurd rfl hmk }; refl },
            rw [if_pos this, if_pos this] } } }
    end,
  inv := id,
  r_inv_inv := λ x y h, h.symm,
  cancel2_inv := ncword_cancel_self }

@[derive [group, decidable_eq]] def ncword := mul_ncword ncword_data.to_data

local notation `NC` := ncword

namespace ncword

instance : mul_action W NC := mul_ncword.mul_action
instance : countable NC := @injective.countable _ _ list.countable _ mul_ncword.ext
instance : has_coe_t generator NC := ⟨mul_ncword.of⟩

lemma of_eq_coe : mul_ncword.of = (coe : generator → NC) := rfl

@[simp] lemma coe_mul_self (x : generator) : (x * x : NC) = 1 :=
mul_ncword.ext _ _ $ by simp only [← of_eq_coe, mul_ncword.word_of_mul_of, ncword_data,
  ncword_cancel_self, mul_ncword.one_word]

lemma bcd_mul_bcd {m n : fin 3} (h : m ≠ n) : (bcd m * bcd n : NC) = bcd (-m - n) :=
mul_ncword.ext _ _ $ by simp only [← of_eq_coe, mul_ncword.word_of_mul_of, ncword_data,
  ncword_cancel, if_neg h, mul_ncword.of_word, word.of_eq_coe]

@[simp] lemma b_mul_c : (b * c : NC) = d := bcd_mul_bcd dec_trivial
@[simp] lemma b_mul_d : (b * d : NC) = c := bcd_mul_bcd dec_trivial
@[simp] lemma c_mul_b : (c * b : NC) = d := bcd_mul_bcd dec_trivial
@[simp] lemma c_mul_d : (c * d : NC) = b := bcd_mul_bcd dec_trivial
@[simp] lemma d_mul_b : (d * b : NC) = c := bcd_mul_bcd dec_trivial
@[simp] lemma d_mul_c : (d * c : NC) = b := bcd_mul_bcd dec_trivial
@[simp] lemma inv_coe (x : generator) : (x : NC)⁻¹ = x := rfl

lemma length_smul_le (w : W) (w' : NC) :
  (w • w').word.to_list.length ≤ w.to_list.length + w'.word.to_list.length :=
mul_ncword.length_smul_le (λ x y _, length_ncword_cancel_le x y) _ _

def lift {M : Type*} [monoid M] (f : W →* M) (h : ∀ x : generator, f x * f x = 1)
  (hbcd : ∀ m n, m ≠ n → f (bcd m) * f (bcd n) = f (bcd (-m - n))) :
  NC →* M :=
mul_ncword.mk_hom f $ forall_not_ncword_rel'.2
  ⟨λ x, by simp only [h, word.of_eq_coe, ncword_data, ncword_cancel_self, map_one],
    λ m n hne, by simp only [hbcd m n hne, ncword_data, ncword_cancel, if_neg hne, word.of_eq_coe]⟩

@[simp] lemma lift_apply {M : Type*} [monoid M] (f : W →* M)
  (h : ∀ x : generator, f x * f x = 1)
  (hbcd : ∀ m n, m ≠ n → f (bcd m) * f (bcd n) = f (bcd (-m - n))) (g : NC) :
  lift f h hbcd g = f g.word :=
rfl

def parity_a : NC →* ℤ₂ :=
lift (word.parity a) (λ x, char_two.add_self_eq_zero (count a [x] : zmod 2)) (λ m n hmn, rfl)

@[simp] lemma mem_ker_parity_a {g : NC} : g ∈ parity_a.ker ↔ even (count a g.word) :=
zmod.eq_zero_iff_even

end ncword

namespace word

def cancel : W →* NC := mul_ncword.cancel ncword_data.to_monoid_data

@[simp, norm_cast] lemma cancel_coe (x : generator) : cancel x = x := rfl

lemma cancel_eq_smul_one (w : W) : cancel w = w • 1 :=
mul_ncword.cancel_eq_smul_one w

lemma length_cancel_le (w : W) : length (cancel w).word.to_list ≤ length w.to_list :=
mul_ncword.length_cancel_le (λ x y _, length_ncword_cancel_le _ _) _

end word

@[simp] lemma ncword.cancel_to_word (g : NC) : word.cancel g.word = g := mul_ncword.cancel_word g

lemma word.cancel_surjective : surjective word.cancel :=
left_inverse.surjective ncword.cancel_to_word

namespace ncword

@[simp] lemma mclosure_abcd : submonoid.closure (range (coe : generator → NC)) = ⊤ :=
top_unique $ λ g hg, cancel_to_word g ▸ submonoid.list_prod_mem _
  (forall_mem_map_iff.2 $ λ x hx, submonoid.subset_closure $ mem_range_self _)

@[simp] lemma closure_abcd : subgroup.closure (range (coe : generator → NC)) = ⊤ :=
subgroup.closure_eq_top_of_mclosure_eq_top mclosure_abcd

end ncword

def _root_.grigorchuk_group : subgroup (equiv.perm L) :=
subgroup.closure (range (coe : generator → equiv.perm L))

local notation `G` := grigorchuk_group

instance fun_like : fun_like G L (λ _, L) :=
{ coe := λ f, f.1,
  coe_injective' := λ f g h₁, subtype.ext $ equiv.coe_fn_injective h₁ }

instance : has_coe_t generator G := ⟨λ x, ⟨x, subgroup.subset_closure $ mem_range_self _⟩⟩

@[simp] lemma inv_coe (x : generator) : (x : G)⁻¹ = x := rfl
@[simp] lemma coe_mul_self (x : generator) : (x * x : G) = 1 := fun_like.ext' x.comp_self
@[simp, norm_cast] lemma coe_fn_coe_gen (x : generator) : ⇑(x : G) = x := rfl
@[simp, norm_cast] lemma coe_fn_coe (x : G) : ⇑(x : equiv.perm L) = x := rfl
@[simp, norm_cast] lemma coe_coe (x : generator) : ((x : G) : equiv.perm L) = x := rfl
@[simp] lemma coe_fn_one : ⇑(1 : G) = id := rfl
lemma one_apply (l : L) : (1 : G) l = l := rfl
@[simp] lemma coe_fn_mul (g₁ g₂ : G) : ⇑(g₁ * g₂) = g₁ ∘ g₂ := rfl
lemma mul_apply (g₁ g₂ : G) (l : L) : (g₁ * g₂) l = g₁ (g₂ l) := rfl

lemma bcd_mul_of_ne {m n : fin 3} (h : m ≠ n) : (bcd m * bcd n : G) = bcd (-m - n) :=
fun_like.ext' $ generator.bcd_comp_bcd_of_ne h

@[simp] lemma b_mul_c : (b * c : G) = d := bcd_mul_of_ne dec_trivial
@[simp] lemma c_mul_d : (c * d : G) = b := bcd_mul_of_ne dec_trivial
@[simp] lemma d_mul_b : (d * b : G) = c := bcd_mul_of_ne dec_trivial
@[simp] lemma c_mul_b : (c * b : G) = d := bcd_mul_of_ne dec_trivial
@[simp] lemma d_mul_c : (d * c : G) = b := bcd_mul_of_ne dec_trivial
@[simp] lemma b_mul_d : (b * d : G) = c := bcd_mul_of_ne dec_trivial

def to_perm : G →* equiv.perm L := subgroup.subtype _

@[simp] lemma coe_to_perm : ⇑to_perm = coe := rfl
@[simp] lemma to_perm_range : to_perm.range = G := subgroup.subtype_range G
lemma to_perm_injective : injective to_perm := subtype.coe_injective

@[simp] lemma closure_abcd : subgroup.closure (range (coe : generator → G)) = ⊤ :=
subgroup.map_injective to_perm_injective $ by rw [monoid_hom.map_closure, ← range_comp,
  ← monoid_hom.range_eq_map, to_perm_range, coe_to_perm, (∘), funext coe_coe, grigorchuk_group]

@[simp] lemma mclosure_abcd : submonoid.closure (range (coe : generator → G)) = ⊤ :=
by simp only [← subgroup.top_to_submonoid, ← closure_abcd, subgroup.closure_to_submonoid,
  ← image_inv, ← range_comp, (∘), inv_coe, union_self]

lemma le_length_preserving : G ≤ equiv.perm.fiberwise length :=
(subgroup.closure_le _).2 $ range_subset_iff.2 generator.length_apply

def to_length_preserving : G →* equiv.perm.fiberwise (@length bool) :=
subgroup.inclusion le_length_preserving

@[simp] lemma coe_to_length_preserving (g : G) : ⇑(to_length_preserving g) = g := rfl

@[simp] lemma length_apply (g : G) (l : L) : length (g l) = length l :=
le_length_preserving g.2 l

@[simp] lemma apply_nil (g : G) : g [] = [] := length_eq_zero.1 $ length_apply g _

def head_preserving : subgroup G := (equiv.perm.fiberwise head').comap to_perm

local notation `H` := head_preserving

lemma mem_head_preserving {g : G} : g ∈ H ↔ ∀ l, (g l).head' = l.head' := iff.rfl

namespace word

def to_grigorchuk : W →* G := free_monoid.lift coe

@[simp] lemma to_grigorchuk_coe (x : generator) : to_grigorchuk x = x := rfl

@[simp] lemma to_grigorchuk_cons (x : generator) (l : W) :
  to_grigorchuk (x :: l) = x * to_grigorchuk l :=
list.prod_cons

@[simp] lemma mrange_to_grigorchuk : to_grigorchuk.mrange = ⊤ :=
top_unique $ grigorchuk_group.mclosure_abcd ▸ submonoid.closure_le.2 (range_subset_iff.2 $
  λ x, to_grigorchuk_coe x ▸ mem_range_self _)

lemma to_grigorchuk_surjective : surjective to_grigorchuk :=
monoid_hom.mrange_top_iff_surjective.1 mrange_to_grigorchuk

end word

namespace ncword

def to_grigorchuk : NC →* G :=
lift word.to_grigorchuk grigorchuk_group.coe_mul_self $ λ m n, grigorchuk_group.bcd_mul_of_ne

@[simp] lemma to_grigorchuk_to_word (g : NC) : g.to_word.to_grigorchuk = g.to_grigorchuk := rfl
@[simp] lemma to_grigorchuk_coe (x : generator) : to_grigorchuk x = x := rfl

@[simp] lemma range_to_grigorchuk : to_grigorchuk.range = ⊤ :=
top_unique $ grigorchuk_group.closure_abcd ▸ (subgroup.closure_le _).2 (range_subset_iff.2 $
  λ x, to_grigorchuk_coe x ▸ mem_range_self _)

lemma to_grigorchuk_surjective : surjective to_grigorchuk :=
monoid_hom.range_top_iff_surjective.1 range_to_grigorchuk

@[simp] lemma to_grigorchuk_cons {x : generator} {g : NC} (hxg : chain' R (x :: g.to_word)) :
  to_grigorchuk (cons x g hxg) = x * g.to_grigorchuk :=
g.to_word.to_grigorchuk_cons x

@[simp] lemma to_grigorchuk_comp_cancel : to_grigorchuk.comp word.cancel = word.to_grigorchuk :=
free_monoid.hom_eq $ λ x, rfl

end ncword

instance : countable G := ncword.to_grigorchuk_surjective.countable

namespace word

@[simp] lemma to_grigorchuk_cancel (w : W) : w.cancel.to_grigorchuk = w.to_grigorchuk :=
fun_like.congr_fun ncword.to_grigorchuk_comp_cancel w

lemma head'_to_grigorchuk_apply (g : W) (l : L) :
  (to_grigorchuk g l).head' = l.head'.map (bnot^[count a g]) :=
begin
  induction g using grigorchuk_group.word.rec_on with x g ihg,
  { exact (congr_fun option.map_id l.head').symm },
  { rw [map_mul, to_grigorchuk_coe, mul_apply, coe_fn_coe_gen, ← cons_eq_mul, count_cons'],
    cases x,
    { rw [generator.head'_a, if_pos rfl, iterate_succ', ihg, option.map_map] },
    { rw [generator.head'_bcd, ihg, if_neg, add_zero],
      simp only [not_false_iff] } }
end

lemma to_grigorchuk_mem_head_preserving {g : W} : to_grigorchuk g ∈ H ↔ even (count a g) :=
calc to_grigorchuk g ∈ H ↔ ∀ o : option bool, o.map (bnot ^[count a g]) = id o :
  by simp only [mem_head_preserving, head'_to_grigorchuk_apply, surjective_head'.forall, id]
... ↔ (bnot ^[count a g]) = id : by simp only [← funext_iff, option.map_eq_id]
... ↔ even (count a g) : bool.involutive_bnot.iterate_eq_id bool.bnot_ne_id

lemma comap_to_grigorchuk_head_preserving :
  head_preserving.to_submonoid.comap to_grigorchuk = (parity a).mker :=
set_like.ext $ λ x, to_grigorchuk_mem_head_preserving.trans mem_mker_parity_a.symm

lemma map_to_grigorchuk_mker_parity_a :
  (parity a).mker.map to_grigorchuk = head_preserving.to_submonoid :=
by rw [← comap_to_grigorchuk_head_preserving,
  submonoid.map_comap_eq_of_surjective to_grigorchuk_surjective]

end word

namespace ncword

lemma to_grigorchuk_mem_head_preserving {g : NC} : to_grigorchuk g ∈ H ↔ even (count a g.to_word) :=
word.to_grigorchuk_mem_head_preserving

lemma comap_to_grigorchuk_head_preserving :
  head_preserving.comap to_grigorchuk = parity_a.ker :=
set_like.ext $ λ x, to_grigorchuk_mem_head_preserving.trans mem_ker_parity_a.symm

lemma map_to_grigorchuk_mker_parity_a : parity_a.ker.map to_grigorchuk = H :=
by rw [← comap_to_grigorchuk_head_preserving,
  subgroup.map_comap_eq_self_of_surjective to_grigorchuk_surjective]

@[ext] structure even_a :=
(to_word' : free_monoid (bool × fin 3))
(chain : chain' (≠) (map prod.fst to_word'))

def parity_ker_rec_aux (C : ∀ w : W, chain' R w → even (count a w) → Sort*)
  (h₁ : C [] chain'_nil even_zero)
  (ha : ∀ n g h₁ h₂ h₁' h₂', C g h₁ h₂ → C (a :: bcd n :: a :: g) h₁' h₂')
  (h : ∀ n g h₁ h₂ h₁' h₂', C g h₁ h₂ → C (bcd n :: g) h₁' h₂') :
  ∀ g h₁ h₂, C g h₁ h₂
| [] _ _ := h₁
| [a] h₁ h₂ := absurd h₂ (by simp)
| [a, bcd m] h₁ h₂ := absurd h₂ (by simp)
| (a :: a :: l) h₁ h₂ := absurd h₁.rel_head (not_ncword_rel_a_a)
| (a :: bcd m :: bcd n :: l) h₁ h₂ := absurd h₁.tail.rel_head not_ncword_rel_bcd_bcd
| (bcd m :: l) h₁ h₂ := h m l h₁.tail (by simpa using h₂) _ _ (parity_ker_rec_aux _ _ _)
| (a :: bcd m :: a :: l) h₁ h₂ := ha m l h₁.tail.tail.tail
  (by simpa [count_cons] with parity_simps using h₂) _ _ (parity_ker_rec_aux _ _ _)

@[elab_as_eliminator]
def parity_ker_rec_on {C : parity_a.ker → Sort*} (g : parity_a.ker) (h₁ : C 1)
  (ha : ∀ n g h₁ h₂, C g → C ⟨⟨a :: bcd n :: a :: g.1.1, h₁⟩, h₂⟩)
  (h : ∀ n g h₁ h₂, C g → C ⟨⟨bcd n :: g.1.1, h₁⟩, h₂⟩) :
  C g :=
let ⟨⟨w, hw₁⟩, hw₂⟩ := g in parity_ker_rec_aux (λ w h₁ h₂, C ⟨⟨w, h₁⟩, mem_ker_parity_a.2 h₂⟩) h₁
  (λ n g hg₁ hg₂ hg₁' hg₂' hC, ha n ⟨⟨g, hg₁⟩, mem_ker_parity_a.2 hg₂⟩ _ _ hC)
  (λ n g hg₁ hg₂ hg₁' hg₂' hC, h n ⟨⟨g, hg₁⟩, mem_ker_parity_a.2 hg₂⟩ _ _ hC) _ _
  (mem_ker_parity_a.1 hw₂)

namespace even_a

def atom (x : bool × fin 3) : W := cond x.1 (a * bcd x.2 * a) (bcd x.2)

@[ext] def to_word (w : even_a) : W := free_monoid.lift atom w.to_word'

lemma head'_to_word (w : even_a) :
  head' w.to_word = w.to_word'.head'.map (λ x, cond x.1 a (bcd x.2)) :=
by rcases w with (_|⟨⟨(_|_), _⟩, _⟩); refl

lemma chain'_to_word (w : even_a) : w.to_word.chain' R :=
begin
  cases w with w hw,
  induction w with x w ihw, { exact chain'_nil },
  specialize ihw hw.tail,
  refine chain'.append _ ihw _,
  { rcases x with ⟨(_|_), m⟩; simp },
  { rcases x with ⟨(_|_), m⟩; rcases w with (_|⟨⟨(_|_), n⟩, w⟩);
      try { exact absurd rfl hw.rel_head }; simp }
end

@[simps] def to_ncword (w : even_a) : NC := ⟨w.to_word, w.chain'_to_word⟩

lemma count_a_to_word (w : even_a) :
  count a w.to_word = 2 * count tt (map prod.fst w.to_word') :=
begin
  cases w with w hw,
  simp only [to_word], clear hw,
  induction w with x w ihw,
  { simp only [join, map_nil, count_nil, mul_zero] },
  { rcases x with ⟨(_|_), n⟩; simp only [ihw, join, list.map, bool.cond_ff, bool.cond_tt,
      cons_append, singleton_append, count_cons_of_ne, count_cons_self, ne.def, not_false_iff,
      nat.succ_eq_add_one, mul_add, mul_one] }
end

lemma to_word_mem_mker (w : even_a) : w.to_word ∈ (word.parity a).mker :=
by { rw [word.mem_mker_parity_a, count_a_to_word], apply even_two_mul }

lemma to_ncword_mem_ker (w : even_a) : w.to_ncword ∈ ncword.parity_a.ker := w.to_word_mem_mker

end even_a

def ker_to_even_a (g : parity_a.ker) : {e : even_a // e.to_ncword = g.1}  :=
begin
  refine parity_ker_rec_on g ⟨⟨1, chain'_nil⟩, rfl⟩ (λ n g' h₁ h₂ e, ⟨⟨⟨tt, n⟩ :: e.1.1, _⟩, _⟩)
    (λ n g' h₁ h₂ e, ⟨⟨⟨ff, n⟩ :: e.1.1, _⟩, _⟩);
    clear g; rcases g' with ⟨g, hg⟩; rcases e with ⟨e, rfl : _ = g⟩; try { refl },
  { refine e.chain.cons' _,
    simpa only [even_a.head'_to_word, even_a.to_ncword_to_word, option.forall_mem_map, ncword_rel_a,
      ne.def, bool.cond_eq_ite, ite_eq_left_iff, not_forall, not_false_iff, head'_map,
      @eq_comm _ tt, exists_prop, and_true] using (chain'_cons'.1 h₁.tail.tail).1 },
  { refine e.chain.cons' _,
    simpa only [even_a.head'_to_word, even_a.to_ncword_to_word, option.forall_mem_map,
      ncword_rel_bcd, ne.def, bool.cond_eq_ite, ite_eq_left_iff, not_forall, not_false_iff,
      imp_false, not_not, head'_map, @eq_comm _ ff, exists_prop, and_true, eq_tt_eq_not_eq_ff]
      using (chain'_cons'.1 h₁).1 }
end

namespace even_a

def equiv_ker : even_a ≃ parity_a.ker :=
{ to_fun := λ e, ⟨e.to_ncword, e.to_ncword_mem_ker⟩,
  inv_fun := λ g, ker_to_even_a g,
  left_inv := λ ⟨w, hw⟩, even_a.ext _ _
    begin
      induction w with x w ihw,
      { refl },
      { specialize ihw hw.tail,
        simp only at ihw ⊢,
        conv_rhs { rw [← ihw] },
        rcases x with ⟨(_|_), _⟩; refl }
    end,
  right_inv := λ g, subtype.eq (ker_to_even_a g).2 }

instance : group even_a := equiv_ker.group

def to_ker : even_a ≃* parity_a.ker := equiv_ker.mul_equiv

lemma closure_bcd : closure (range )

def restr_atom (x : bool) (y : bool × fin 3) : W :=
if x = y.1 then if y.2 = 1 then 1 else a else bcd (y.2 + 1)

def restr_to_word (x : bool) (e : even_a) : W := free_monoid.lift (restr_atom x) e.1

end even_a

end ncword

namespace head_preserving

@[simp] lemma coe_mem {x : generator} : (x : G) ∈ H ↔ x ≠ a :=
begin
  rw [← word.to_grigorchuk_coe, word.to_grigorchuk_mem_head_preserving, word.coe_def,
    count_singleton'],
  cases x; simp
end

lemma a_nmem : (a : G) ∉ H := mt coe_mem.1 (not_not.2 rfl)
lemma ne_top : H ≠ ⊤ := λ h, a_nmem $ h.symm ▸ subgroup.mem_top _
lemma bcd_mem (n : fin 3) : (bcd n : G) ∈ H := coe_mem.2 (generator.bcd_ne_a n)

@[simp] lemma mul_mem_iff {g₁ g₂ : G} : g₁ * g₂ ∈ H ↔ (g₁ ∈ H ↔ g₂ ∈ H) :=
begin
  rcases word.to_grigorchuk_surjective g₁ with ⟨g₁, rfl⟩,
  rcases word.to_grigorchuk_surjective g₂ with ⟨g₂, rfl⟩,
  simp_rw [← map_mul, word.to_grigorchuk_mem_head_preserving, free_monoid.mul_def, count_append,
    nat.even_add]
end

instance : subgroup.normal H := ⟨λ g₁ h g₂, by simp [h]⟩

lemma a_mul_mem {g : G} : ↑a * g ∈ H ↔ g ∉ H := by simp
lemma bcd_mul_mem {n : fin 3} {g : G} : ↑(bcd n) * g ∈ H ↔ g ∈ H := by simp

lemma mul_a_mem {g : G} : g * a ∈ H ↔ g ∉ H := by simp
lemma mul_bcd_mem {g : G} {n : fin 3} : g * bcd n ∈ H ↔ g ∈ H := by simp

@[simp] lemma index_eq : subgroup.index H = 2 := subgroup.index_eq_two_iff.2 $ ⟨a, λ g, mul_a_mem⟩

lemma sq_mem (x : G) : x ^ 2 ∈ H := subgroup.sq_mem_of_index_two index_eq _

lemma cons_tail_apply {g : G} (hg : g ∈ H) (x : bool) (l : L) :
  x :: (g (x :: l)).tail = g (x :: l) :=
cons_head'_tail $ by simp only [mem_head_preserving.1 hg, head', option.mem_def]

def atom' (x : bool) (n : fin 3) : free_monoid (fin 4) := cond x [0, n.succ, 0] [n.succ]

@[simp] lemma length_atom' (x : bool) (n : fin 3) : length (atom' x n) = cond x 3 1 :=
by cases x; refl

lemma of_word_atom' (x : bool) (n : fin 3) : of_word (atom' x n) = cond x (a * bcd n * a) (bcd n) :=
by cases x; simp only [atom', cond, of_word_cons, of_word_singleton, a, abcd_succ, mul_assoc]

lemma range_of_word_atom :
  range (of_word ∘ uncurry atom') = {b, c, d, a * b * a, a * c * a, a * d * a} :=
begin
  ext x,
  simp only [set.mem_range, fin.exists_fin_succ, fin.exists_fin_two, prod.exists, bool.exists_bool,
    (∘), uncurry, of_word_atom', set.mem_insert_iff, mem_singleton_iff, mul_assoc, or_assoc,
    @eq_comm _ x],
  refl
end

lemma of_word_atom'_mem (x : bool) (n : fin 3) : of_word (atom' x n) ∈ H := by cases x; simp [atom']

def atom (x : bool) (n : fin 3) : H := ⟨of_word (atom' x n), of_word_atom'_mem x n⟩

lemma coe_fn_atom (x : bool) (n : fin 3) :
  ⇑(atom x n) = (cond x (a * bcd n * a) (bcd n) : G) :=
by cases x; refl

def mk : free_monoid (bool × fin 3) →* H := free_monoid.lift (uncurry atom)

def mk' : free_monoid (bool × fin 3) →* free_monoid (fin 4) := free_monoid.lift (uncurry atom')

lemma of_word_comp_mk' : of_word.comp mk' = (subgroup.subtype _).comp mk :=
by { simp only [mk', mk, free_monoid.comp_lift], refl }

lemma of_word_mk' (l : free_monoid (bool × fin 3)) : of_word (mk' l) = mk l :=
monoid_hom.congr_fun of_word_comp_mk' l

lemma mk'_cons (a : bool × fin 3) (l : free_monoid (bool × fin 3)) :
  mk' (a :: l) = atom' a.1 a.2 * mk' l :=
by simp only [mk', ← free_monoid.of_mul_eq_cons, map_mul, free_monoid.lift_eval_of, uncurry]

lemma mk'_singleton (a : bool × fin 3) : mk' [a] = atom' a.1 a.2 :=
free_monoid.lift_eval_of _ _

lemma mk_cons (a : bool × fin 3) (l : free_monoid (bool × fin 3)) :
  mk (a :: l) = atom a.1 a.2 * mk l :=
by simp only [mk, ← free_monoid.of_mul_eq_cons, map_mul, free_monoid.lift_eval_of, uncurry]

lemma _root_.grigorchuk_group.is_minimal.chain'_ne_fst {l : free_monoid (bool × fin 3)}
  (hl : is_minimal (mk' l)) : l.chain' ((≠) on prod.fst) :=
begin
  induction l with x l ihl, { exact chain'_nil },
  cases l with y l, { exact chain'_singleton _ },
  rw [mk'_cons] at hl,
  specialize ihl (hl.to_infix (suffix_append _ _).is_infix),
  refine ihl.cons (_ : x.1 ≠ y.1),
  rw [mk'_cons, ← mul_assoc] at hl,
  replace hl := hl.to_infix (prefix_append _ _).is_infix,
  rcases ⟨x, y⟩ with ⟨⟨x, n⟩, y, m⟩, rintro (rfl : x = y),
  cases x; simp only [atom, cond, free_monoid.mul_def, cons_append, nil_append] at hl,
  { simpa [fin.succ_ne_zero] using hl.eq_0_or_eq_0 },
  { exact hl.chain'_ne.tail.tail.rel_head rfl }
end

lemma _root_.grigorchuk_group.is_minimal.chain'_ne_map_fst {l : free_monoid (bool × fin 3)}
  (hl : is_minimal (mk' l)) : (map prod.fst l).chain' (≠) :=
(chain'_map _).2 hl.chain'_ne_fst

lemma length_mk' (g : free_monoid (bool × fin 3)) :
  length (mk' g) = length g + 2 * count tt (map prod.fst g) :=
begin
  induction g with x g ihg, { refl },
  rw [mk'_cons, free_monoid.mul_def, length_append, ihg, count, map_cons, countp_cons,
    length_atom'],
  rcases x with ⟨(_|_), _⟩; simp only [cond, if_pos rfl, if_false, length_cons]; ring
end

lemma le_length_mk' (g : free_monoid (bool × fin 3)) : length g ≤ length (mk' g) :=
(length_mk' g).symm ▸ le_add_right le_rfl

@[simp] lemma even_length_mk' {g} : even (length (mk' g)) ↔ even (length g) :=
by simp only [length_mk', nat.even_add, even_two_mul, true_or, iff_true]

lemma exists_mk'_eq : ∀ {g : free_monoid (fin 4)}, is_minimal g → of_word g ∈ H →
  ∃ l, mk' l = g
| [] _ _ := ⟨[], rfl⟩
| (⟨n + 1, hn⟩ :: g) hmin hmem :=
  let ⟨l, hl⟩ := @exists_mk'_eq g hmin.tail (by simpa [fin.ext_iff] using hmem)
  in ⟨(ff, ⟨n, nat.lt_pred_iff.2 hn⟩) :: l,
    hl ▸ by simp only [mk'_cons, atom', cond, free_monoid.mul_def, singleton_append, fin.succ_mk]⟩
| [⟨0, _⟩] _ h := absurd h $ by simp only [fin.mk_zero, of_word_mem, count_singleton,
  nat.not_even_one, not_false_iff]
| (⟨0, _⟩ :: ⟨0, _⟩ :: g) hmin hmem := (hmin.chain'_ne.rel_head rfl).elim
| [⟨0, _⟩, ⟨n + 1, hn⟩] hmin hmem := absurd hmem $
  by simp [count_singleton', fin.ext_iff, n.succ_ne_zero.symm]
| (⟨0, _⟩ :: ⟨n + 1, hn⟩ :: ⟨m + 1, hm⟩ :: g) hmin hmem :=
  absurd hmin.chain'_eq_0.tail.rel_head $ by simp [fin.ext_iff]
| (⟨0, _⟩ :: ⟨n + 1, hn⟩ :: ⟨0, _⟩ :: g) hmin hmem :=
  let ⟨l, hl⟩ := @exists_mk'_eq g hmin.tail.tail.tail
    (by simpa [count_cons, fin.ext_iff, n.succ_ne_zero.symm, nat.even_add_one] using hmem)
  in ⟨(tt, ⟨n, nat.lt_pred_iff.2 hn⟩) :: l, hl ▸ by simp only [mk'_cons, atom', cond,
    free_monoid.mul_def, cons_append, nil_append, fin.mk_zero, fin.succ_mk]⟩

lemma exists_mk_eq (g : H) : ∃ l, mk l = g ∧ is_minimal (mk' l) :=
begin
  cases g with g hg,
  rcases exists_is_minimal_of_word_eq g with ⟨g, hmin, rfl⟩,
  rcases exists_mk'_eq hmin hg with ⟨l, rfl⟩,
  refine ⟨l, subtype.ext _, hmin⟩,
  rw [← of_word_mk', subtype.coe_mk]
end

lemma mk_surjective : surjective mk := λ g, (exists_mk_eq g).imp $ λ l, and.left

@[simp] lemma mclosure_range_atom : submonoid.closure (range $ uncurry atom) = ⊤ :=
begin
  refine top_unique (λ g hg, _), clear hg,
  rcases exists_mk_eq g with ⟨g, rfl, hmin⟩,
  exact list_prod_mem (list.forall_mem_map_iff.2 $
    λ x hx, submonoid.subset_closure $ mem_range_self _)
end

@[simp] lemma closure_range_atom : subgroup.closure (range $ uncurry atom) = ⊤ :=
(subgroup.eq_top_iff' _).2 $
  λ x, subgroup.le_closure_to_submonoid _ (mclosure_range_atom.symm ▸ trivial)

/-- The subgroup of head preserving elements is generated by `b`, `c`, `d`, `a * b * a`,
`a * c * a`, and `a * d * a`. -/
lemma eq_closure : H = subgroup.closure {b, c, d, a * b * a, a * c * a, a * d * a} :=
begin
  rw [← range_of_word_atom, ← subgroup.subtype_range H, monoid_hom.range_eq_map,
    ← closure_range_atom, monoid_hom.map_closure, ← range_comp],
  refl
end

/-- Restrict head preserving elements of the Grigorchuk group to lists with a fixed head. -/
def restr_to_perm (x : bool) : H →* equiv.perm L :=
monoid_hom.to_hom_perm $
{ to_fun := λ g l, (g (x :: l)).tail,
  map_one' := rfl,
  map_mul' := λ g₁ g₂, funext $ λ l, congr_arg tail $ congr_arg g₁ $
    (cons_tail_apply g₂.2 _ _).symm }

lemma restr_to_perm_apply (x : bool) (g : H) (l : L) :
  restr_to_perm x g l = (g (x :: l)).tail :=
rfl

def atom_restr (x y : bool) (n : fin 3) : G :=
if x = y then if n = 1 then 1 else a else bcd (n + 1)

lemma restr_to_perm_atom (x y : bool) (n : fin 3) : restr_to_perm x (atom y n) = atom_restr x y n :=
begin
  refine equiv.ext (λ l, _),
  rw [restr_to_perm_apply, atom_restr, coe_fn_atom],
  cases x; cases y; simp only [a_apply_cons, bnot, cond, coe_bcd_eq_pre, coe_fn_coe, coe_fn_mul,
    (∘), eq_self_iff_true, if_false, if_true, not_true, pre.bcd, tail_cons];
    by_cases hn : n = 1; simp only [if_pos, if_false, hn]; refl
end

lemma restr_to_perm_comp_mk (x : bool) :
  (restr_to_perm x).comp mk =
    (subgroup.subtype G).comp (free_monoid.lift (uncurry $ atom_restr x)) :=
by simp only [mk, free_monoid.comp_lift, (∘), uncurry, restr_to_perm_atom, subgroup.coe_subtype]

lemma restr_to_perm_mk (x : bool) (l : free_monoid (bool × fin 3)) :
  restr_to_perm x (mk l) = (free_monoid.lift (uncurry $ atom_restr x) l : G) :=
monoid_hom.congr_fun (restr_to_perm_comp_mk x) l

lemma restr_to_perm_mem (x : bool) : ∀ g, restr_to_perm x g ∈ G :=
mk_surjective.forall.2 $ λ l, (restr_to_perm_mk x l).symm ▸ set_like.coe_mem _

/-- Restrict a head-preserving element of the Grigorchuk group to lists that start with a given
boolean value. -/
def restr (x : bool) : head_preserving →* G :=
(restr_to_perm x).cod_restrict _ $ restr_to_perm_mem x

@[simp] lemma restr_apply (x : bool) (g : H) (l : L) :
  restr x g l = (g (x :: l)).tail :=
rfl

lemma restr_atom (x y : bool) (n : fin 3) : restr x (atom y n) = atom_restr x y n :=
subtype.ext $ restr_to_perm_atom x y n

lemma restr_mk (x : bool) (l : free_monoid (bool × fin 3)) :
  restr x (mk l) = free_monoid.lift (uncurry $ atom_restr x) l :=
subtype.ext $ restr_to_perm_mk x l

lemma restr_comp_mk (x : bool) : (restr x).comp mk = free_monoid.lift (uncurry $ atom_restr x) :=
monoid_hom.ext $ restr_mk x

@[simp] lemma range_restr (x : bool) : (restr x).range = ⊤ :=
begin
  have : x ≠ !x, by cases x; dec_trivial,
  simp_rw [← top_le_iff, ← closure_abcd, subgroup.closure_le, ← range_bcd, insert_subset,
    range_subset_iff, set_like.mem_coe],
  refine ⟨⟨atom x 0, _⟩, λ n, ⟨atom (!x) (n - 1), _⟩⟩;
    simp only [restr_atom, atom_restr, sub_add_cancel, if_pos rfl, if_neg zero_ne_one, if_neg this]
end

lemma surjective_restr (b : bool) : surjective (restr b) :=
(subgroup.eq_top_iff' _).mp (range_restr b)

lemma card_eq' : #H = #G := le_antisymm (mk_set_le H) (mk_le_of_surjective $ surjective_restr ff)

instance : countable H := subtype.coe_injective.countable

def atom_restr' (x y : bool) (n : fin 3) : free_monoid (fin 4) :=
if x = y then if n = 1 then 1 else [0] else [(n + 1).succ]

lemma length_atom_restr' (x y : bool) (n : fin 3) :
  length (atom_restr' x y n) = if x = y ∧ n = 1 then 0 else 1 :=
by { rw [atom_restr'], by_cases hxy : x = y; by_cases hn : n = 1; simp [*, free_monoid.one_def] }

@[simp] lemma of_word_atom_restr' (x y : bool) (n : fin 3) :
  of_word (atom_restr' x y n) = atom_restr x y n :=
by { rw [atom_restr, atom_restr'], split_ifs; simp only [map_one, of_word_singleton]; refl }

def mk_restr' (x : bool) : free_monoid (bool × fin 3) →* free_monoid (fin 4) :=
free_monoid.lift (uncurry $ atom_restr' x)

lemma of_word_mk_restr' (x : bool) (l : free_monoid (bool × fin 3)) :
  of_word (mk_restr' x l) = restr x (mk l) :=
by simp only [mk_restr', mk, free_monoid.hom_map_lift, (∘), uncurry, of_word_atom_restr',
  restr_atom]

@[simp] lemma length_mk_restr' (x : bool) (g : free_monoid (bool × fin 3)) :
  length (mk_restr' x g) = length g - count (x, 1) g :=
begin
  induction g with y g ihg, { refl }, cases y with y z,
  simp only [mk_restr', free_monoid.lift_apply, map_cons, prod_cons, free_monoid.mul_def, uncurry,
    length_append, length_atom_restr', length, count_cons', prod.mk.inj_iff, @eq_comm (fin 3) 1]
    at ihg ⊢,
  rw [ihg],
  split_ifs,
  { rw [zero_add, nat.succ_sub_succ_eq_sub] },
  { rw [add_zero, add_comm _ 1, nat.add_sub_assoc],
    exact count_le_length _ _ }
end

lemma length_mk_restr'_le (x : bool) (g : free_monoid (bool × fin 3)) :
  length (mk_restr' x g) ≤ length g :=
(length_mk_restr' x g).trans_le tsub_le_self

lemma length_mk_restr'_le_length_mk' (x : bool) (g : free_monoid (bool × fin 3)) :
  length (mk_restr' x g) ≤ length (mk' g) :=
(length_mk_restr'_le x g).trans (le_length_mk' _)

lemma length_mk_restr'_lt_length_mk' {x : bool} {g : free_monoid (bool × fin 3)} :
  length (mk_restr' x g) < length (mk' g) ↔
    tt ∈ map prod.fst g ∨ @has_mem.mem _ (list _) _ (x, (1 : fin 3)) g :=
by rw [length_mk_restr', length_mk', tsub_lt_iff_right (count_le_length _ _), add_assoc,
  lt_add_iff_pos_right, add_pos_iff, count_pos, two_mul, add_pos_iff, or_self, count_pos]

lemma forall_length_mk_restr'_lt_length_mk' {g : free_monoid (bool × fin 3)}
  (hg : is_minimal (mk' g)) :
  (∀ x, length (mk_restr' x g) < length (mk' g)) ↔ g ≠ [] ∧ ∀ n, g ≠ [(ff, n)] :=
begin
  simp only [length_mk_restr'_lt_length_mk'],
  refine ⟨λ h, _, λ h x, _⟩,
  { simp only [ne.def, ← not_exists, ← not_or_distrib],
    rintro (rfl|⟨n, rfl⟩); simpa using h tt },
  { rcases exists_cons_of_ne_nil h.1 with ⟨y, g, rfl⟩,
    left,
    cases g with z g,
    { rw [map_singleton, list.mem_singleton, eq_comm],
      rcases y with ⟨_|_, n⟩,
      exacts [(h.2 n rfl).elim, rfl] },
    { rw [map_cons, map_cons, mem_cons_iff, mem_cons_iff, ← or_assoc],
      left,
      have : y.1 ≠ z.1 := hg.chain'_ne_fst.rel_head,
      cases z.1,
      { left, symmetry, simpa using this },
      { exact or.inr rfl } } }
end

lemma two_mul_length_mk_restr'_le_length_mk'_succ {x : bool} {g : free_monoid (bool × fin 3)}
  (hmin : is_minimal (mk' g)) :
  2 * length (mk_restr' x g) ≤ length (mk' g) + 1 :=
begin
  rw [length_mk_restr', length_mk', mul_tsub, tsub_le_iff_right, add_assoc, add_assoc, two_mul,
    add_le_add_iff_left, ← tsub_le_iff_right],
  refine le_trans _ (hmin.chain'_ne_map_fst.length_sub_one_le_two_mul_count_bool _),
  rw [length_map],
  exact tsub_le_tsub_left (le_add_right le_rfl) _
end

lemma two_mul_length_mk_restr'_le_length_mk' {x : bool} {g : free_monoid (bool × fin 3)}
  (hmin : is_minimal (mk' g)) (he : even (length g)) :
  2 * length (mk_restr' x g) ≤ length (mk' g) :=
begin
  refine nat.lt_succ_iff.1
    (lt_of_le_of_ne (two_mul_length_mk_restr'_le_length_mk'_succ hmin) $ λ h, _),
  rw [← @not_not (even _), ← even_length_mk', ← nat.even_add_one, ← nat.succ_eq_add_one, ← h] at he,
  exact he (even_two_mul _)
end

lemma two_mul_length_mk_restr'_lt_length_mk' {x : bool} {g : free_monoid (bool × fin 3)}
  (hmin : is_minimal (mk' g)) (he : even (length g)) :
  2 * length (mk_restr' x g) < length (mk' g) ↔ @has_mem.mem _ (list (bool × fin 3)) _ (x, 1) g :=
begin
  rw [length_mk_restr', length_mk', mul_tsub,
    tsub_lt_iff_right (mul_le_mul_left' (count_le_length _ _) _), add_assoc, two_mul,
    add_lt_add_iff_left, hmin.chain'_ne_map_fst.two_mul_count_bool_of_even, length_map,
    lt_add_iff_pos_right, two_mul, add_pos_iff, or_self, count_pos],
  rwa [length_map]
end

lemma restr_injective' {g₁ g₂} (h : ∀ x, restr x g₁ = restr x g₂) : g₁ = g₂ :=
begin
  refine subtype.ext (fun_like.ext _ _ $ λ l, _),
  cases l with hd tl, { simp only [apply_nil] },
  erw [← cons_tail_apply g₁.coe_prop, ← cons_tail_apply g₂.coe_prop, ← restr_apply, h,
    ← restr_apply]
end

lemma restr_injective : injective (λ g, (restr ff g, restr tt g)) :=
λ g₁ g₂ h, restr_injective' $ bool.forall_bool.2 (prod.mk.inj_iff.1 h)

end head_preserving

section head_preserving

open head_preserving

instance : infinite G := ⟨λ h, (@mk_set_lt _ h a H a_nmem).ne card_eq'⟩
instance : infinite H := infinite_iff.mpr $ (aleph_0_le_mk G).trans_eq card_eq'.symm
instance : infinite NC :=

lemma of_word_pow_two_pow_length (g : free_monoid (fin 4)) : of_word g ^ (2 ^ length g) = 1 :=
begin
  have Hle : ∀ {g} {k l : ℕ}, k ≤ l → of_word g ^ 2 ^ k = 1 → of_word g ^ 2 ^ l = 1,
  { intros g k l hle h1,
    rw [← add_tsub_cancel_of_le hle, pow_add, pow_mul, h1, one_pow] },
  induction hN : length g using nat.strong_induction_on with N ihN generalizing g,
  replace ihN : ∀ g' : free_monoid (fin 4), length g' < N → of_word g' ^ 2 ^ length g' = 1,
    from λ g' hg', ihN _ hg' _ rfl,
  revert g, -- TODO: use the new `wlog`
  suffices : ∀ g : free_monoid (fin 4), length g = N → is_minimal g → of_word g ^ 2 ^ N = 1,
  { rintro g rfl,
    rcases exists_is_minimal_of_word_eq (of_word g) with ⟨g', hmin, hg'⟩,
    cases (hmin g hg').eq_or_lt with hlen hlt,
    { rw [← hg', this g' hlen hmin] },
    { rw [← hg', Hle hlt.le (ihN _ hlt)] } },
  have hH : ∀ g : free_monoid (fin 4), length g = N → is_minimal g → of_word g ∈ H →
    of_word g ^ 2 ^ N = 1,
  { rintro g rfl hmin hmem,
    rcases exists_mk_eq ⟨of_word g, hmem⟩ with ⟨l, hlg, hl⟩,
    rw [← subtype.coe_inj, subtype.coe_mk, ← of_word_mk'] at hlg,
    rw [hmin.length_eq hl hlg.symm] at ihN ⊢,
    rw [← hlg],
    clear hlg hmin hmem g,
    by_cases hlt : ∀ x, length (mk_restr' x l) < length (mk' l),
    { suffices : mk l ^ 2 ^ length (mk' l) = 1,
        by rw [of_word_mk', ← subgroup.coe_pow, this, subgroup.coe_one],
      refine restr_injective' (λ x, _),
      rw [map_pow, map_one, ← of_word_mk_restr', Hle (hlt _).le (ihN _ (hlt _))] },
    { rw [forall_length_mk_restr'_lt_length_mk' hl, ne.def, ← not_exists, ← not_or_distrib, not_not]
        at hlt,
      rcases hlt with rfl|⟨n, rfl⟩,
      { refl },
      { rw [mk'_singleton, of_word_atom', cond, length_atom', cond, pow_one, sq,
          bcd_mul_self] } } },
  have hnomin : ∀ g : free_monoid (fin 4), length g = N → is_minimal g → ¬is_minimal (g ^ 2) →
    of_word g ^ 2 ^ N = 1,
  { rintro g rfl hmin hmin₂,
    rcases exists_mk_eq ⟨of_word g^2, sq_mem _⟩ with ⟨g', h', hmin'⟩,
    have hlt : length (mk' g') < 2 * length g,
  },


  -- induction; WLOG, `g` is a minimal word
  -- suffices : ∀ g, is_minimal g →
  --   (∀ g' : free_monoid (fin 4), length g' < length g → of_word g' ^ (2 ^ length g') = 1) →
  --   of_word g ^ (2 ^ length g) = 1,
  -- { induction hn : length g using nat.strong_induction_on with n' ihn generalizing g, subst n',
  --   exact ihn _ (hg'.trans_le (length_to_word_of_word_le _)) _ rfl },
  -- clear g, intros g hmin ihg,
  -- -- Trivial cases `g = []` and `g = [_]`
  -- cases lt_or_le (length g) 2 with h₂ h₂,
  -- { cases g with n g, { exact one_pow _ },
  --   cases g with m g, { rw [length_singleton, pow_one, of_word_singleton, sq, abcd_mul_self] },
  --   exact absurd h₂ (by simp [bit0]) },

end

lemma exists_pow_two_pow_eq_one (g : G) : ∃ k : ℕ, g ^ (2 ^ k) = 1 :=
begin


end

end head_preserving

def alpha : ℝ := log 2 / log (2 / η)

local notation `α` := alpha

lemma alpha_lt_one : α < 1 :=
(div_lt_one $ log_pos $ (one_lt_div eta_pos).2 eta_lt_two).2 $
  log_lt_log two_pos $ (lt_div_iff eta_pos).2 $
  calc 2 * η < 2 * 1 : (mul_lt_mul_left two_pos).2 eta_lt_one
  ... = 2 : mul_one _

/-
definitions: normed group, multiplication operation.
definition: equiv. of norms
lemma: for f.g. group, canonical equiv. class of norms

definition: growth of a group = function gamma(n) = #{g in G | |g|<=n}.
definition: gamma ≾, (asymptotic domination) delta if exist C: gamma(n)<=delta(C n). ~ equiv relation.
lemma: independent of choice of metric, for f.g. group

theorem: exp(C n^(1/2)) <= gamma(n) <= exp(C n^alpha)
theorem: exp(n^(1/2)) <~ gamma(n) <~ exp(n^alpha)

-------------------------------------------------
H subgroup of index 2
|.| on G, defined using eta

psi: H -> GxG.

1) psi almost bijection: injective, image has index 8.

2) if psi(h) = (g_0,g_1), then |g_0|+|g_1| <= eta*(|h|+|a|)
              (so: "essentially" gamma(n) <= 1/2 gamma(eta n)^2, by finding good g_0,g_1)
--> upper bound

3) similarly, |h| <= 2(|g_0|+|g_1|) + constant
              (so: "essentially" gamma(n) >= 8gamma(n/2)^2, by finding good h)
--> lower bound

-/

end grigorchuk_group
