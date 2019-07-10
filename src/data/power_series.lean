/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import data.finsupp order.complete_lattice algebra.ordered_group data.mv_polynomial

namespace eq
variables {α : Type*} {a b : α}

@[reducible] def lhs (h : a = b) : α := a

@[reducible] def rhs (h : a = b) : α := b

end eq

-- namespace finset
-- universe u
-- variables {α : Type*} {β : Type*} {γ : Type*}
-- variables [decidable_eq α] [decidable_eq β] [add_comm_monoid γ]

-- #print sum_product

-- -- lemma sum_pi (s : finset α) (i : Πa:α, Type u) (t : Πa, finset (i a)) (f : Πa, i a → β) :
-- --   (finset.pi s t).sum (λ x, s.sum _) =
-- --   s.sum (λ a, (t a).sum (f a))
-- --    := _

-- #print finset.sigma

-- #print sum_sigma

-- lemma sum_pi' (s : finset α) (t : α → finset β) (f : α → β → γ) :
--   (finset.bind s (λ a, (finset.product {a} (t a) : finset (α × β)))).sum (λ p, f p.1 p.2) =
--   s.sum (λ a, (t a).sum (f a)) :=
-- begin
--   rw [sum_bind, sum_congr rfl],
--   { intros a ha,
--     apply sum_bij (λ (p : _ × _) hp, p.2),
--     { rintros ⟨i,j⟩ hij, exact (finset.mem_product.1 hij).2 },
--     { rintros ⟨i,j⟩ hij, simp at hij, rcases hij with ⟨rfl, _⟩, refl },
--     { rintros ⟨i,j⟩ ⟨k,l⟩ hij hkl H, simp at hij hkl H,
--       rw [H, hij.1, hkl.1] },
--     { intros a ha, refine ⟨finset.product {a} (t a), _⟩, },
--      },
--   { intros a ha b hb hab,
--     rw finset.eq_empty_iff_forall_not_mem,
--     rintros ⟨i,j⟩ H, apply hab,
--     simp at H, rcases H with ⟨⟨rfl, _⟩, ⟨rfl, _⟩⟩, refl }
-- end

-- end finset

section

set_option old_structure_cmd true

class canonically_ordered_cancel_monoid (α : Type*) extends
  ordered_cancel_comm_monoid α, canonically_ordered_monoid α.

instance : canonically_ordered_cancel_monoid ℕ :=
{ ..nat.canonically_ordered_comm_semiring,
  ..nat.decidable_linear_ordered_cancel_comm_monoid }

end

namespace multiset
variables {α : Type*} [decidable_eq α]

def to_finsupp (s : multiset α) : α →₀ ℕ :=
{ support := s.to_finset,
  to_fun := λ a, s.count a,
  mem_support_to_fun := λ a,
  begin
    rw mem_to_finset,
    convert not_iff_not_of_iff (count_eq_zero.symm),
    rw not_not
  end }

@[simp] lemma to_finsupp_support (s : multiset α) :
  s.to_finsupp.support = s.to_finset := rfl

@[simp] lemma to_finsupp_apply (s : multiset α) (a : α) :
  s.to_finsupp a = s.count a := rfl

@[simp] lemma to_finsupp_zero :
  to_finsupp (0 : multiset α) = 0 :=
finsupp.ext $ λ a, count_zero a

@[simp] lemma to_finsupp_add (s t : multiset α) :
  to_finsupp (s + t) = to_finsupp s + to_finsupp t :=
finsupp.ext $ λ a, count_add a s t

namespace to_finsupp

instance : is_add_monoid_hom (to_finsupp : multiset α → α →₀ ℕ) :=
{ map_zero := to_finsupp_zero,
  map_add  := to_finsupp_add }

end to_finsupp

@[simp] lemma to_finsupp_to_multiset (s : multiset α) :
  s.to_finsupp.to_multiset = s :=
ext.2 $ λ a, by rw [finsupp.count_to_multiset, to_finsupp_apply]

end multiset

namespace finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ]

instance [preorder α] [has_zero α] : preorder (σ →₀ α) :=
{ le := λ f g, ∀ s, f s ≤ g s,
  le_refl := λ f s, le_refl _,
  le_trans := λ f g h Hfg Hgh s, le_trans (Hfg s) (Hgh s) }

instance [partial_order α] [has_zero α] : partial_order (σ →₀ α) :=
{ le_antisymm := λ f g hfg hgf, finsupp.ext $ λ s, le_antisymm (hfg s) (hgf s),
  .. finsupp.preorder }

instance [ordered_cancel_comm_monoid α] [decidable_eq α] :
  add_left_cancel_semigroup (σ →₀ α) :=
{ add_left_cancel := λ a b c h, finsupp.ext $ λ s,
  by { rw finsupp.ext_iff at h, exact add_left_cancel (h s) },
  .. finsupp.add_monoid }

instance [ordered_cancel_comm_monoid α] [decidable_eq α] :
  add_right_cancel_semigroup (σ →₀ α) :=
{ add_right_cancel := λ a b c h, finsupp.ext $ λ s,
  by { rw finsupp.ext_iff at h, exact add_right_cancel (h s) },
  .. finsupp.add_monoid }

instance [ordered_cancel_comm_monoid α] [decidable_eq α] :
  ordered_cancel_comm_monoid (σ →₀ α) :=
{ add_le_add_left := λ a b h c s, add_le_add_left (h s) (c s),
  le_of_add_le_add_left := λ a b c h s, le_of_add_le_add_left (h s),
  .. finsupp.add_comm_monoid, .. finsupp.partial_order,
  .. finsupp.add_left_cancel_semigroup, .. finsupp.add_right_cancel_semigroup }

attribute [simp] to_multiset_zero to_multiset_add

@[simp] lemma to_multiset_to_finsupp (f : σ →₀ ℕ) :
  f.to_multiset.to_finsupp = f :=
ext $ λ s, by rw [multiset.to_finsupp_apply, count_to_multiset]

def diagonal (f : σ →₀ ℕ) : finset ((σ →₀ ℕ) × (σ →₀ ℕ)) :=
((multiset.diagonal f.to_multiset).map (prod.map multiset.to_finsupp multiset.to_finsupp)).to_finset

lemma mem_diagonal {f : σ →₀ ℕ} {p : (σ →₀ ℕ) × (σ →₀ ℕ)} :
  p ∈ diagonal f ↔ p.1 + p.2 = f :=
begin
  erw [multiset.mem_to_finset, multiset.mem_map],
  split,
  { rintros ⟨⟨a, b⟩, h, rfl⟩,
    rw multiset.mem_diagonal at h,
    simpa using congr_arg multiset.to_finsupp h },
  { intro h,
    refine ⟨⟨p.1.to_multiset, p.2.to_multiset⟩, _, _⟩,
    { simpa using congr_arg to_multiset h },
    { rw [prod.map, to_multiset_to_finsupp, to_multiset_to_finsupp, prod.mk.eta] } }
end

lemma swap_mem_diagonal {n : σ →₀ ℕ} {f} (hf : f ∈ diagonal n) : f.swap ∈ diagonal n :=
by simpa [mem_diagonal, add_comm] using hf

@[simp] lemma diagonal_zero : diagonal (0 : σ →₀ ℕ) = {(0,0)} := rfl

end finsupp

namespace mv_polynomial
open finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [comm_semiring α]

lemma coeff_mul (φ ψ : mv_polynomial σ α) :
  ∀ n, coeff n (φ * ψ) = finset.sum (finsupp.diagonal n) (λ p, coeff p.1 φ * coeff p.2 ψ) :=
begin
  apply mv_polynomial.induction_on φ; clear φ,
  { apply mv_polynomial.induction_on ψ,
    { intros a b n, rw [← C_mul, coeff_C],
      split_ifs,
      { subst n, simp },
      { rw finset.sum_eq_zero, intros p hp,
        simp only [coeff_C],
        rw mem_diagonal at hp,
        split_ifs with h₁ h₂; try {simp * at *; done},
        { rw [← h₁, ← h₂, zero_add] at hp, contradiction } } },
    { intros p q hp hq a, specialize hp a, specialize hq a,
      simp [coeff_C_mul, coeff_add, mul_add, finset.sum_add_distrib, *] at * },
    { intros φ s hφ a n,
      rw [coeff_C_mul],
      have : ((0 : σ →₀ ℕ), n) ∈ diagonal n := by simp [mem_diagonal],
      rw [← finset.insert_erase this, finset.sum_insert (finset.not_mem_erase _ _),
          finset.sum_eq_zero, add_zero],
      { refl },
      { rintros ⟨i,j⟩ h,
        rw [finset.mem_erase, mem_diagonal] at h, cases h with h₁ h₂,
        by_cases H : 0 = i, { subst i, simp * at * },
        rw [coeff_C, if_neg H, zero_mul] } } },
  { intros p q hp hq n,
    rw [add_mul, coeff_add, hp, hq, ← finset.sum_add_distrib],
    apply finset.sum_congr rfl,
    intros m hm, rw [coeff_add, add_mul] },
  { intros φ s hφ n,
    conv_lhs { rw [mul_assoc, mul_comm (X s), ← mul_assoc] },
    rw coeff_mul_X',
    split_ifs,
    { symmetry,
      let T : finset (_ × _) := (diagonal n).filter (λ p, p.1 s > 0),
      have : T ⊆ diagonal n := finset.filter_subset _,
      rw [hφ, ← finset.sum_sdiff this, finset.sum_eq_zero, zero_add],
      { symmetry,
        apply finset.sum_bij (λ (p : _ × _) hp, (p.1 + single s 1, p.2)),
        { rintros ⟨i,j⟩ hij, rw [mem_diagonal] at hij,
          rw [finset.mem_filter, mem_diagonal], dsimp at *,
          split,
          { rw [add_right_comm, hij_1],
            ext t, by_cases hst : s = t,
            { subst t, apply nat.sub_add_cancel, rw [single_apply, if_pos rfl],
              apply nat.pos_of_ne_zero, rwa mem_support_iff at h },
            { change _ - _ + _ = _, simp [single_apply, hst] } },
          { apply nat.add_pos_right, rw [single_apply, if_pos rfl], exact nat.one_pos } },
        { rintros ⟨i,j⟩ hij, rw coeff_mul_X', split_ifs with H,
          { congr' 2, ext t, exact (nat.add_sub_cancel _ _).symm },
          { exfalso, apply H, rw [mem_support_iff, add_apply, single_apply, if_pos rfl],
            exact nat.succ_ne_zero _ } },
        { rintros ⟨i,j⟩ ⟨k,l⟩ hij hkl, rw [prod.mk.inj_iff, add_right_inj, ← prod.mk.inj_iff],
          exact id },
        { rintros ⟨i,j⟩ hij, rw finset.mem_filter at hij, cases hij with h₁ h₂,
          refine ⟨(i - single s 1, j), _, _⟩,
          { rw mem_diagonal at h₁ ⊢, rw ← h₁, ext t, by_cases hst: s = t,
            { subst t, apply (nat.sub_add_comm _).symm,
              rwa [single_apply, if_pos rfl] },
            { apply (nat.sub_add_comm _).symm,
              simp [single_apply, hst] } },
          { congr, ext t, by_cases hst: s = t,
            { subst t, apply (nat.sub_add_cancel _).symm, rwa [single_apply, if_pos rfl] },
            { change _ = _ - _ + _, simp [single_apply, hst] } } } },
      { rintros ⟨i,j⟩ hij, rw finset.mem_sdiff at hij, cases hij with h₁ h₂,
        rw coeff_mul_X', split_ifs with H,
        { exfalso, apply h₂, rw finset.mem_filter, refine ⟨h₁, nat.pos_of_ne_zero _⟩,
          rwa mem_support_iff at H },
        { exact zero_mul _ } } },
    { rw finset.sum_eq_zero,
      rintros ⟨i,j⟩ hij,
      rw [coeff_mul_X', if_neg, zero_mul],
      intro H, apply h,
      rw mem_support_iff at H ⊢,
      rw mem_diagonal at hij,
      rw ← hij, simp * at * } }
end

end mv_polynomial

namespace finsupp
open lattice
variables {σ : Type*} {α : Type*} [decidable_eq σ]

instance [canonically_ordered_cancel_monoid α] [decidable_eq α] : ordered_comm_monoid (σ →₀ α) :=
{ add_le_add_left := λ a b h c s, ordered_comm_monoid.add_le_add_left _ _ (h s) (c s),
  lt_of_add_lt_add_left := λ a b c h,
  ⟨λ s, le_of_add_le_add_left (h.1 s),
   λ H, h.2 $ λ s, add_le_add_left (H s) _⟩,
  .. finsupp.add_comm_monoid,
  .. finsupp.partial_order }

instance [canonically_ordered_monoid α] : order_bot (σ →₀ α) :=
{ bot := 0,
  bot_le := λ f s, zero_le _,
  .. finsupp.partial_order }

instance [canonically_ordered_cancel_monoid α] [decidable_eq α] :
  canonically_ordered_monoid (σ →₀ α) :=
{ le_iff_exists_add := λ a b,
  begin
    split,
    { intro h,
      let c' : σ → α := λ s, classical.some (le_iff_exists_add.1 $ h s),
      let hc : ∀ s, b s = a s + c' s :=
        λ s, classical.some_spec (le_iff_exists_add.1 $ h s),
      let c : σ →₀ α :=
      { support := b.support.filter (λ s, b s ≠ a s),
        to_fun := c',
        mem_support_to_fun := λ s,
        begin
          rw [finset.mem_filter, finsupp.mem_support_iff], split; intro H,
          { intro hcs, apply H.2, simpa [hcs] using hc s },
          { split; intro H'; apply H,
            { suffices ha : a s = 0, by simpa [ha, H'] using (hc s).symm,
              rw ← bot_eq_zero at *,
              simpa [H'] using h s },
            { have := (hc s).symm,
              conv_rhs at this { rw [H', ← add_zero (a s)] },
              exact add_left_cancel this } }
        end },
      use c, ext1 s, exact hc s },
    { rintros ⟨c, rfl⟩ s, exact le_add_right (le_refl _) }
  end,
  .. finsupp.lattice.order_bot,
  .. finsupp.ordered_comm_monoid }

instance [canonically_ordered_cancel_monoid α] [decidable_eq α] :
  canonically_ordered_cancel_monoid (σ →₀ α) :=
{ .. finsupp.ordered_cancel_comm_monoid,
  .. finsupp.canonically_ordered_monoid }

lemma le_iff [canonically_ordered_monoid α] (f g : σ →₀ α) :
  f ≤ g ↔ ∀ s ∈ f.support, f s ≤ g s :=
⟨λ h s hs, h s,
λ h s, if H : s ∈ f.support then h s H else (not_mem_support_iff.1 H).symm ▸ zero_le (g s)⟩

def nat_downset (f : σ →₀ ℕ) : finset (σ →₀ ℕ) :=
(f.support.pi (λ x, finset.range $ f x + 1)).image $
λ g, f.support.attach.sum $ λ i, finsupp.single i.1 $ g i.1 i.2

theorem sum_apply' [decidable_eq α] [add_comm_monoid α] {β : Type*} {f : β → σ →₀ α} {ι : finset β} {i : σ} :
  ι.sum f i = ι.sum (λ x, f x i) :=
by classical; exact finset.induction_on ι rfl (λ x s hxs ih,
by rw [finset.sum_insert hxs, add_apply, ih, finset.sum_insert hxs])

lemma mem_nat_downset_iff_le (f g : σ →₀ ℕ) :
  f ∈ (nat_downset g) ↔ f ≤ g :=
begin
  delta nat_downset, rw finset.mem_image, split,
  { rintros ⟨g', hg', rfl⟩ i,
    rw [finset.mem_pi] at hg',
    rw [sum_apply'],
    by_cases hi : i ∈ g.support,
    { rw finset.sum_eq_single (⟨i, hi⟩ : (↑g.support : set σ)),
      rw [single_apply, if_pos rfl],
      specialize hg' i hi,
      rw [finset.mem_range, nat.lt_succ_iff] at hg',
      exact hg',
      { intros j hj hji, rw [single_apply, if_neg], refine mt _ hji, intros hji', exact subtype.eq hji' },
      { intro hi', exact hi'.elim (finset.mem_attach _ _) } },
    { rw finset.sum_eq_zero, exact nat.zero_le _,
      intros j hj, rw [single_apply, if_neg], rintros rfl, exact hi j.2 } },
  { intros hf, refine ⟨λ i hi, f i, _, _⟩,
    { rw finset.mem_pi, intros i hi, rw [finset.mem_range, nat.lt_succ_iff], exact hf i },
    { ext i, rw sum_apply',
      by_cases hi : i ∈ g.support,
      { rw finset.sum_eq_single (⟨i, hi⟩ : (↑g.support : set σ)),
        rw [single_apply, if_pos rfl],
        { intros j hj hji, rw [single_apply, if_neg], refine mt _ hji, intros hji', exact subtype.eq hji' },
        { intro hi', exact hi'.elim (finset.mem_attach _ _) } },
      { rw finset.sum_eq_zero, rw not_mem_support_iff at hi, symmetry,
        exact nat.eq_zero_of_le_zero (hi ▸ hf i),
        { intros j hj, rw [single_apply, if_neg], rintros rfl, exact hi j.2 } } } }
end

lemma nat_downset_subset (f g : σ →₀ ℕ) (h : f ≤ g) : nat_downset f ⊆ nat_downset g :=
begin
  intro x,
  simp only [mem_nat_downset_iff_le],
  intro hx, exact le_trans hx h
end

@[simp] lemma nat_downset_zero : nat_downset (0 : σ →₀ ℕ) = {0} :=
by { ext a, erw mem_nat_downset_iff_le }

lemma mem_support_iff_single_le (f : σ →₀ ℕ) (s : σ) :
  s ∈ f.support ↔ single s 1 ≤ f :=
begin
  rw le_iff,
  simp only [finsupp.mem_support_iff, finsupp.single_apply],
  split,
  { intros h t ht,
    split_ifs at ht ⊢,
    { subst t, exact nat.pos_of_ne_zero h },
    { exact nat.zero_le _ } },
  { intros h H, specialize h s, simp only [if_pos rfl, H] at h,
    exact nat.not_succ_le_zero 0 (h one_ne_zero) }
end

lemma le_sub_left_iff_add_le {a b c : σ →₀ ℕ} (h : a ≤ c) :
  b ≤ c - a ↔ a + b ≤ c :=
begin
  split; intros H s;
  specialize h s;
  specialize H s,
  { exact (nat.le_sub_left_iff_add_le h).1 H },
  { exact (nat.le_sub_left_iff_add_le h).2 H }
end

lemma sub_le {a b : σ →₀ ℕ} : a - b ≤ a :=
λ s, nat.sub_le (a s) (b s)

end finsupp

/-- Multivariate power series, where `σ` is the index set of the variables
and `α` is the coefficient ring.-/
def mv_power_series (σ : Type*) (α : Type*) := (σ →₀ ℕ) → α

namespace mv_power_series
open finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ] [comm_semiring α]

def coeff (n : σ →₀ ℕ) (φ : mv_power_series σ α) := φ n

@[extensionality] lemma ext {φ ψ : mv_power_series σ α} (h : ∀ n, coeff n φ = coeff n ψ) : φ = ψ :=
funext h

lemma ext_iff {φ ψ : mv_power_series σ α} : φ = ψ ↔ (∀ n, coeff n φ = coeff n ψ) :=
⟨congr_fun, ext⟩

def monomial (n : σ →₀ ℕ) (a : α) : mv_power_series σ α := λ m, if m = n then a else 0

lemma coeff_monomial (m n : σ →₀ ℕ) (a : α) :
  coeff m (monomial n a) = if m = n then a else 0 := rfl

@[simp] lemma coeff_monomial' (n : σ →₀ ℕ) (a : α) :
  coeff n (monomial n a) = a := if_pos rfl

def C (a : α) : mv_power_series σ α := monomial 0 a

lemma coeff_C (n : σ →₀ ℕ) (a : α) :
  coeff n (C a : mv_power_series σ α) = if n = 0 then a else 0 := rfl

@[simp] lemma coeff_C_zero (a : α) : coeff 0 (C a : mv_power_series σ α) = a :=
coeff_monomial' 0 a

@[simp] lemma monomial_zero (a : α) : (monomial 0 a : mv_power_series σ α) = C a := rfl

def X (s : σ) : mv_power_series σ α := monomial (single s 1) 1

lemma coeff_X (n : σ →₀ ℕ) (s : σ) :
  coeff n (X s : mv_power_series σ α) = if n = (single s 1) then 1 else 0 := rfl

lemma coeff_X' (s t : σ) :
  coeff (single t 1) (X s : mv_power_series σ α) = if t = s then 1 else 0 :=
if h : t = s then by simp [h, coeff_X] else
begin
  rw [coeff_X, if_neg h],
  split_ifs with H,
  { have := @finsupp.single_apply σ ℕ _ _ _ t s 1,
    rw [if_neg h, H, finsupp.single_apply, if_pos rfl] at this,
    exfalso, exact one_ne_zero this, },
  { refl }
end

@[simp] lemma coeff_X'' (s : σ) :
  coeff (single s 1) (X s : mv_power_series σ α) = 1 :=
by rw [coeff_X', if_pos rfl]

section ring
variables (σ) (α) (n : σ →₀ ℕ) (φ ψ : mv_power_series σ α)

def zero : mv_power_series σ α := λ n, 0

instance : has_zero (mv_power_series σ α) := ⟨zero σ α⟩

@[simp] lemma coeff_zero : coeff n (0 : mv_power_series σ α) = 0 := rfl

@[simp] lemma C_zero : (C 0 : mv_power_series σ α) = 0 :=
ext $ λ n, if h : n = 0 then by simp [h] else by rw [coeff_C, if_neg h, coeff_zero]

def one : mv_power_series σ α := C 1

instance : has_one (mv_power_series σ α) := ⟨one σ α⟩

@[simp] lemma coeff_one :
  coeff n (1 : mv_power_series σ α) = if n = 0 then 1 else 0 := rfl

@[simp] lemma coeff_one_zero : coeff 0 (1 : mv_power_series σ α) = 1 :=
coeff_C_zero 1

@[simp] lemma C_one : (C 1 : mv_power_series σ α) = 1 := rfl

def add (φ ψ : mv_power_series σ α) : mv_power_series σ α :=
λ n, coeff n φ + coeff n ψ

instance : has_add (mv_power_series σ α) := ⟨add σ α⟩

variables {σ α}

@[simp] lemma coeff_add : coeff n (φ + ψ) = coeff n φ + coeff n ψ := rfl

@[simp] lemma zero_add : (0 : mv_power_series σ α) + φ = φ := ext $ λ n, zero_add _

@[simp] lemma add_zero : φ + 0 = φ := ext $ λ n, add_zero _

lemma add_comm : φ + ψ = ψ + φ := ext $ λ n, add_comm _ _

lemma add_assoc (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ + φ₂) + φ₃ = φ₁ + (φ₂ + φ₃) :=
ext $ λ n, by simp

@[simp] lemma monomial_add (n : σ →₀ ℕ) (a b : α) :
  (monomial n (a + b) : mv_power_series σ α) = monomial n a + monomial n b :=
ext $ λ m, if h : m = n then by simp [h] else by simp [coeff_monomial, if_neg h]

@[simp] lemma C_add (a b : α) : (C (a + b) : mv_power_series σ α) = C a + C b :=
monomial_add 0 a b

variables (σ α)

def mul (φ ψ : mv_power_series σ α) : mv_power_series σ α :=
λ n, (finsupp.diagonal n).sum (λ p, coeff p.1 φ * coeff p.2 ψ)
instance : has_mul (mv_power_series σ α) := ⟨mul σ α⟩

lemma coeff_mul :
  coeff n (φ * ψ) = (finsupp.diagonal n).sum (λ p, coeff p.1 φ * coeff p.2 ψ) := rfl

variables {σ α}

@[simp] lemma zero_mul : (0 : mv_power_series σ α) * φ = 0 :=
ext $ λ n, by simp [coeff_mul]

@[simp] lemma mul_zero : φ * 0 = 0 :=
ext $ λ n, by simp [coeff_mul]

lemma mul_comm : φ * ψ = ψ * φ :=
ext $ λ n, finset.sum_bij (λ p hp, p.swap)
  (λ p hp, swap_mem_diagonal hp)
  (λ p hp, mul_comm _ _)
  (λ p q hp hq H, by simpa using congr_arg prod.swap H)
  (λ p hp, ⟨p.swap, swap_mem_diagonal hp, p.swap_swap.symm⟩)

@[simp] lemma one_mul : (1 : mv_power_series σ α) * φ = φ :=
ext $ λ n,
begin
  have H : ((0 : σ →₀ ℕ), n) ∈ (diagonal n) := by simp [mem_diagonal],
  rw [coeff_mul, ← finset.insert_erase H, finset.sum_insert (finset.not_mem_erase _ _),
    coeff_one_zero, one_mul, finset.sum_eq_zero, _root_.add_zero],
  rintros ⟨i,j⟩ hij,
  rw [finset.mem_erase, mem_diagonal] at hij,
  rw [coeff_one, if_neg, _root_.zero_mul],
  intro H, apply hij.1, simp * at *
end

@[simp] lemma mul_one : φ * 1 = φ :=
by rw [mul_comm, one_mul]

lemma mul_add (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
ext $ λ n, by simp only [coeff_mul, coeff_add, mul_add, finset.sum_add_distrib]

lemma add_mul (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
ext $ λ n, by simp only [coeff_mul, coeff_add, add_mul, finset.sum_add_distrib]

lemma mul_assoc (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ * φ₂) * φ₃ = φ₁ * (φ₂ * φ₃) :=
ext $ λ n,
begin
  simp only [coeff_mul],
  have := @finset.sum_sigma ((σ →₀ ℕ) × (σ →₀ ℕ)) α _ _ (diagonal n)
    (λ p, diagonal (p.1)) (λ x, coeff x.1.1 φ₁ * coeff x.1.2 φ₂ * coeff x.2.2 φ₃),
  convert this.symm using 1; clear this,
  { apply finset.sum_congr rfl,
    intros p hp,
    dsimp,
    apply finset.sum_congr rfl,
    dsimp, }
  -- have bind_left := @finset.sum_bind ((σ →₀ ℕ) × (σ →₀ ℕ)) α (σ →₀ ℕ)
  --   (λ p, (coeff p.2 φ₁ * coeff (p.1-p.2) φ₂) * coeff (n-p.1) φ₃)
  --   _ _ (nat_downset n) (λ m, finset.product {m} (nat_downset m))
  --   begin
  --     intros, dsimp,
  --     rw finset.eq_empty_iff_forall_not_mem,
  --     intros p hp,
  --     simp [finset.mem_inter, finset.mem_product] at hp,
  --     rcases hp with ⟨⟨rfl, _⟩, ⟨rfl, _⟩⟩,
  --     contradiction
  --   end,
  -- have bind_right := @finset.sum_bind ((σ →₀ ℕ) × (σ →₀ ℕ)) α (σ →₀ ℕ)
  --   (λ p, (coeff p.1 φ₁ * coeff (p.2) φ₂) * coeff (n-p.1-p.2) φ₃)
  --   _ _ (nat_downset n) (λ m, finset.product {m} (nat_downset (n-m)))
  --   begin
  --     intros, dsimp,
  --     rw finset.eq_empty_iff_forall_not_mem,
  --     intros p hp,
  --     simp [finset.mem_inter, finset.mem_product] at hp,
  --     rcases hp with ⟨⟨rfl, _⟩, ⟨rfl, _⟩⟩,
  --     contradiction
  --   end,
  -- calc coeff n (φ₁ * φ₂ * φ₃) = bind_left.rhs :
  --   begin
  --     apply finset.sum_congr rfl,
  --     intros m hm,
  --     rw [coeff_mul, finset.sum_mul], symmetry,
  --     apply finset.sum_bij (λ (p : (σ →₀ ℕ) × (σ →₀ ℕ)) hp, p.2),
  --     { intros p hp, exact (finset.mem_product.1 hp).2 },
  --     { intros p hp, erw [finset.mem_product, finset.mem_singleton] at hp, cases hp, subst m },
  --     { rintros ⟨m₁,i₁⟩ ⟨m₂,i₂⟩ h₁ h₂ H, dsimp at *,
  --       erw [finset.mem_product, finset.mem_singleton] at h₁ h₂,
  --       dsimp at *, erw [h₁.1, h₂.1, H] },
  --     { intros i hi, refine ⟨(m,i), _, rfl⟩,
  --       { erw finset.mem_product, exact ⟨finset.mem_singleton_self m, hi⟩ } }
  --   end
  --   ... = bind_left.lhs : bind_left.symm
  --   ... = bind_right.lhs :
  --   begin
  --     apply finset.sum_bij (λ p hp, _),

  --   end
  --   ... = bind_right.rhs : bind_right
  --   ... = _ :
  --   begin

  --   end
end

instance : comm_semiring (mv_power_series σ α) :=
{ mul_one := mul_one,
  one_mul := one_mul,
  add_assoc := add_assoc,
  zero_add := zero_add,
  add_zero := add_zero,
  add_comm := add_comm,
  mul_assoc := mul_assoc,
  mul_zero := mul_zero,
  zero_mul := zero_mul,
  mul_comm := mul_comm,
  left_distrib := mul_add,
  right_distrib := add_mul,
  .. mv_power_series.has_zero σ α,
  .. mv_power_series.has_one σ α,
  .. mv_power_series.has_add σ α,
  .. mv_power_series.has_mul σ α }

end ring

end mv_power_series

namespace mv_polynomial
open finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [comm_semiring α]

def to_mv_power_series (φ : mv_polynomial σ α) : mv_power_series σ α :=
λ n, coeff n φ

@[simp] lemma to_mv_power_series_coeff (φ : mv_polynomial σ α) (n) :
mv_power_series.coeff n (φ.to_mv_power_series) = coeff n φ := rfl

namespace to_mv_power_series

instance : is_semiring_hom (to_mv_power_series : mv_polynomial σ α → mv_power_series σ α) :=
{ map_zero := mv_power_series.ext $ λ n, by simp,
  map_one := mv_power_series.ext $ λ n,
  begin
    rw [to_mv_power_series_coeff, mv_power_series.coeff_one],
    split_ifs; rw ← C_1; simp [-C_1, h],
    { rw ← ne_from_not_eq at h, simp [h.symm] }
  end,
  map_add := λ φ ψ, mv_power_series.ext $ λ n, by simp,
  map_mul := λ φ ψ, mv_power_series.ext $ λ n,
  by simp only [to_mv_power_series_coeff, mv_power_series.coeff_mul, coeff_mul] }

end to_mv_power_series

end mv_polynomial
