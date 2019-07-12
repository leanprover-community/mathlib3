/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import data.finsupp order.complete_lattice algebra.ordered_group data.mv_polynomial
import algebra.order_functions
import ring_theory.ideal_operations
import linear_algebra.basis
import algebra.CommRing.limits

namespace discrete_field
variables {α : Type*} [discrete_field α]

instance : local_ring α :=
{ is_local := λ a,
  if h : a = 0
  then or.inr (by rw [h, sub_zero]; exact is_unit_one)
  else or.inl $ is_unit_of_mul_one a a⁻¹ $ div_self h }

end discrete_field

namespace eq
variables {α : Type*} {a b : α}

@[reducible] def lhs (h : a = b) : α := a

@[reducible] def rhs (h : a = b) : α := b

end eq

namespace finsupp
variables {α : Type*} [decidable_eq α] [add_comm_monoid α]

lemma single_punit_eq (x : punit) (f : punit →₀ α) : single x (f x) = f :=
ext $ λ y,
match x, y with
| punit.star, punit.star := by { rw [single_apply, if_pos rfl] }
end

lemma single_punit_eq_single_punit_iff (x y : punit) (a b : α) :
  single x a = single y b ↔ a = b :=
begin
  rw [single_eq_single_iff],
  split,
  { rintros (⟨_, rfl⟩ | ⟨rfl, rfl⟩); refl },
  { intro h, left, exact ⟨subsingleton.elim _ _, h⟩ }
end

lemma single_punit_eq_zero_iff (x : punit) (a : α) : single x a = 0 ↔ a = 0 :=
by { rw [← single_zero, single_punit_eq_single_punit_iff], exact punit.star }

end finsupp

section algebra
variables {α : Type*} {β : Type*} [comm_ring α] [comm_ring β]
variables {M : Type*} [add_comm_group M] [module β M]

def module.restriction_of_hom (f : α → β) [is_ring_hom f] : module α M :=
{ smul := λ a m, f a • m,
  one_smul := λ m, by simp only [is_ring_hom.map_one f, one_smul],
  mul_smul := λ a b m, by simp only [is_ring_hom.map_mul f, mul_smul],
  smul_add := λ a m n, smul_add _ _ _,
  smul_zero := λ a, smul_zero _,
  add_smul := λ a b m, by simp only [is_ring_hom.map_add f, add_smul],
  zero_smul := λ m, by simp only [is_ring_hom.map_zero f, zero_smul], }

def submodule.restriction_of_hom (f : α → β) [is_ring_hom f] (N : submodule β M) :
  @submodule α M _ _ (module.restriction_of_hom f) :=
{ smul := λ a m hm, N.smul (f a) hm, .. N }

variables (β) [algebra α β]
include β

def module.restriction : module α M :=
module.restriction_of_hom (algebra_map β)

def submodule.restriction : submodule β M → @submodule α M _ _ (module.restriction β) :=
submodule.restriction_of_hom _

omit β
variable {β}

instance ideal.quotient.module (I : ideal β) : module α I.quotient :=
@module.restriction α β _ _ _ _ (submodule.quotient.module I) _

end algebra

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

lemma le_iff [canonically_ordered_monoid α] (f g : σ →₀ α) :
  f ≤ g ↔ ∀ s ∈ f.support, f s ≤ g s :=
⟨λ h s hs, h s,
λ h s, if H : s ∈ f.support then h s H else (not_mem_support_iff.1 H).symm ▸ zero_le (g s)⟩

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

lemma to_multiset_strict_mono : strict_mono (@to_multiset σ _) :=
λ m n h,
begin
  rw lt_iff_le_and_ne at h ⊢, cases h with h₁ h₂,
  split,
  { rw multiset.le_iff_count, intro s, rw [count_to_multiset, count_to_multiset], exact h₁ s },
  { intro H, apply h₂, replace H := congr_arg multiset.to_finsupp H, simpa using H }
end

lemma sum_lt_of_lt (m n : σ →₀ ℕ) (h : m < n) :
  m.sum (λ _, id) < n.sum (λ _, id) :=
begin
  rw [← card_to_multiset, ← card_to_multiset],
  apply multiset.card_lt_of_lt,
  exact to_multiset_strict_mono _ _ h
end

variable (σ)

def lt_wf : well_founded (@has_lt.lt (σ →₀ ℕ) _) :=
subrelation.wf (sum_lt_of_lt) $ inv_image.wf _ nat.lt_wf

instance decidable_lt : decidable_rel (@has_lt.lt (σ →₀ ℕ) _) :=
λ m n,
begin
  have h : _ := _,
  rw lt_iff_le_and_ne, refine @and.decidable _ _ h _,
  rw le_iff, apply_instance
end

end finsupp

namespace mv_polynomial
open finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [comm_semiring α]

lemma coeff_mul (φ ψ : mv_polynomial σ α) (n : σ →₀ ℕ) :
  coeff n (φ * ψ) = finset.sum (diagonal n) (λ p, coeff p.1 φ * coeff p.2 ψ) :=
begin
  rw mul_def,
  have := @finset.sum_sigma (σ →₀ ℕ) α _ _ φ.support (λ _, ψ.support)
    (λ x, if (x.1 + x.2 = n) then coeff x.1 φ * coeff x.2 ψ else 0),
  convert this.symm using 1; clear this,
  { rw [coeff],
    repeat {rw sum_apply, apply finset.sum_congr rfl, intros, dsimp only},
    exact single_apply },
  { have : (diagonal n).filter (λ x, x.1 ∈ φ.support ∧ x.2 ∈ ψ.support) ⊆ (diagonal n) :=
      finset.filter_subset _,
    rw [← finset.sum_sdiff this, finset.sum_eq_zero, zero_add], swap,
    { intros x hx, rw [finset.mem_sdiff, not_iff_not_of_iff (finset.mem_filter),
        not_and, not_and, not_mem_support_iff] at hx,
      by_cases H : x.1 ∈ φ.support,
      { rw [coeff, coeff, hx.2 hx.1 H, mul_zero] },
      { rw not_mem_support_iff at H, rw [coeff, H, zero_mul] } },
    symmetry,
    rw [← finset.sum_sdiff (finset.filter_subset _), finset.sum_eq_zero, zero_add], swap,
    { intros x hx, rw [finset.mem_sdiff, not_iff_not_of_iff (finset.mem_filter), not_and] at hx,
      replace hx := hx.2 hx.1, rw if_neg, exact hx },
    { apply finset.sum_bij, swap 5, { intros x hx, exact (x.1, x.2) },
      { intros x hx, rw [finset.mem_filter, finset.mem_sigma] at hx,
        rw [finset.mem_filter, mem_diagonal],
        dsimp, exact hx.symm },
      { intros x hx, rw finset.mem_filter at hx, rw if_pos hx.2 },
      { rintros ⟨i,j⟩ ⟨k,l⟩ hij hkl, simpa using and.intro },
      { rintros ⟨i,j⟩ hij, refine ⟨⟨i,j⟩, _, _⟩, { apply_instance },
        { rw [finset.mem_filter, mem_diagonal] at hij, rw [finset.mem_filter, finset.mem_sigma],
          exact hij.symm },
        { refl } } },
    all_goals { apply_instance } }
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
variables {σ : Type*} {α : Type*} [decidable_eq σ]

def coeff (n : σ →₀ ℕ) (φ : mv_power_series σ α) := φ n

@[extensionality] lemma ext {φ ψ : mv_power_series σ α} (h : ∀ n, coeff n φ = coeff n ψ) : φ = ψ :=
funext h

lemma ext_iff {φ ψ : mv_power_series σ α} : φ = ψ ↔ (∀ n, coeff n φ = coeff n ψ) :=
⟨λ h n, congr_arg (coeff n) h, ext⟩

variables [comm_semiring α]

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

variables {σ α}

lemma coeff_mul :
  coeff n (φ * ψ) = (finsupp.diagonal n).sum (λ p, coeff p.1 φ * coeff p.2 ψ) := rfl

@[simp] lemma C_mul (a b : α) : (C (a * b) : mv_power_series σ α) = C a * C b :=
ext $ λ n,
begin
  rw [coeff_C, coeff_mul],
  split_ifs,
  { subst n, erw [diagonal_zero, finset.sum_singleton, coeff_C_zero, coeff_C_zero] },
  { rw finset.sum_eq_zero,
    rintros ⟨i,j⟩ hij,
    rw mem_diagonal at hij, rw [coeff_C, coeff_C],
    split_ifs; try {simp * at *; done} }
end

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
    (λ p, diagonal (p.1)) (λ x, coeff x.2.1 φ₁ * coeff x.2.2 φ₂ * coeff x.1.2 φ₃),
  convert this.symm using 1; clear this,
  { apply finset.sum_congr rfl,
    intros p hp, exact finset.sum_mul },
  have := @finset.sum_sigma ((σ →₀ ℕ) × (σ →₀ ℕ)) α _ _ (diagonal n)
    (λ p, diagonal (p.2)) (λ x, coeff x.1.1 φ₁ * (coeff x.2.1 φ₂ * coeff x.2.2 φ₃)),
  convert this.symm using 1; clear this,
  { apply finset.sum_congr rfl, intros p hp, rw finset.mul_sum },
  apply finset.sum_bij,
  swap 5,
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, exact ⟨(k, l+j), (l, j)⟩ },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, simp only [finset.mem_sigma, mem_diagonal] at H ⊢, finish },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, rw mul_assoc },
  { rintros ⟨⟨a,b⟩, ⟨c,d⟩⟩ ⟨⟨i,j⟩, ⟨k,l⟩⟩ H₁ H₂,
    simp only [finset.mem_sigma, mem_diagonal,
      and_imp, prod.mk.inj_iff, add_comm, heq_iff_eq] at H₁ H₂ ⊢,
    finish },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, refine ⟨⟨(i+k, l), (i, k)⟩, _, _⟩;
    { simp only [finset.mem_sigma, mem_diagonal] at H ⊢, finish } }
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

instance C.is_semiring_hom : is_semiring_hom (C : α → mv_power_series σ α) :=
{ map_zero := C_zero _ _,
  map_one := C_one _ _,
  map_add := C_add,
  map_mul := C_mul }

instance coeff.is_add_monoid_hom : is_add_monoid_hom (coeff n : mv_power_series σ α → α) :=
{ map_zero := coeff_zero _ _ _,
  map_add := coeff_add n }

instance : semimodule α (mv_power_series σ α) :=
{ smul := λ a φ, C a * φ,
  one_smul := λ φ, one_mul _,
  mul_smul := λ a b φ, by simp only [C_mul, mul_assoc],
  smul_add := λ a φ ψ, mul_add _ _ _,
  smul_zero := λ a, mul_zero _,
  add_smul := λ a b φ, by simp only [C_add, add_mul],
  zero_smul := λ φ, by simp only [zero_mul, C_zero] }

-- TODO(jmc) map and rename

end ring

-- TODO(jmc): once adic topology lands, show that this is complete

end mv_power_series

namespace mv_power_series
variables {σ : Type*} {α : Type*} [decidable_eq σ] [comm_ring α]

protected def neg (φ : mv_power_series σ α) : mv_power_series σ α := λ n, - coeff n φ

instance : has_neg (mv_power_series σ α) := ⟨mv_power_series.neg⟩

@[simp] lemma coeff_neg (φ : mv_power_series σ α) (n) : coeff n (- φ) = - coeff n φ := rfl

lemma add_left_neg (φ : mv_power_series σ α) : (-φ) + φ = 0 :=
ext $ λ n, by rw [coeff_add, coeff_zero, coeff_neg, add_left_neg]

instance : comm_ring (mv_power_series σ α) :=
{ add_left_neg := add_left_neg,
  .. mv_power_series.has_neg, .. mv_power_series.comm_semiring }

instance C.is_ring_hom : is_ring_hom (C : α → mv_power_series σ α) :=
{ map_one := C_one _ _,
  map_add := C_add,
  map_mul := C_mul }

instance coeff.is_add_group_hom (n : σ →₀ ℕ) :
  is_add_group_hom (coeff n : mv_power_series σ α → α) :=
{ map_add := coeff_add n }

instance : module α (mv_power_series σ α) :=
{ ..mv_power_series.semimodule }

instance : algebra α (mv_power_series σ α) :=
{ to_fun := C,
  commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ c p, rfl,
  .. mv_power_series.module }

def inv_of_unit (φ : mv_power_series σ α) (u : units α) (h : coeff 0 φ = u) : mv_power_series σ α
| n := if n = 0 then ↑u⁻¹ else
- ↑u⁻¹ * finset.sum (n.diagonal) (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if h : x.2 < n then coeff x.1 φ * inv_of_unit x.2 else 0)
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, finsupp.lt_wf σ⟩],
  dec_tac := tactic.assumption }

lemma coeff_inv_of_unit (n : σ →₀ ℕ) (φ : mv_power_series σ α) (u : units α) (h : coeff 0 φ = u) :
  coeff n (inv_of_unit φ u h) = if n = 0 then ↑u⁻¹ else
  - ↑u⁻¹ * finset.sum (n.diagonal) (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if x.2 < n then coeff x.1 φ * inv_of_unit φ u h x.2 else 0) :=
by rw [coeff, inv_of_unit]

@[simp] lemma coeff_zero_inv_of_unit (φ : mv_power_series σ α) (u : units α) (h : coeff 0 φ = u) :
  coeff (0 : σ →₀ ℕ) (inv_of_unit φ u h) = ↑u⁻¹ :=
by rw [coeff_inv_of_unit, if_pos rfl]

lemma mul_inv_of_unit (φ : mv_power_series σ α) (u : units α) (h : coeff 0 φ = u) :
  φ * inv_of_unit φ u h = 1 :=
ext $ λ n,
if H : n = 0 then
by rw [H, coeff_mul, coeff_one_zero, finsupp.diagonal_zero, finset.insert_empty_eq_singleton,
  finset.sum_singleton, coeff_zero_inv_of_unit, h, units.mul_inv]
else
begin
  have : ((0 : σ →₀ ℕ), n) ∈ n.diagonal,
  { rw [finsupp.mem_diagonal], simp },
  rw [coeff_one, if_neg H, coeff_mul,
    ← finset.insert_erase this, finset.sum_insert (finset.not_mem_erase _ _),
    coeff_inv_of_unit, if_neg H, h,
    neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, units.mul_inv_cancel_left,
    ← finset.insert_erase this, finset.sum_insert (finset.not_mem_erase _ _),
    finset.insert_erase this, if_neg (not_lt_of_ge $ le_refl _), _root_.add_comm, _root_.zero_add,
    ← sub_eq_add_neg, sub_eq_zero, finset.sum_congr rfl],
  rintros ⟨i,j⟩ hij, rw [finset.mem_erase, finsupp.mem_diagonal] at hij, cases hij with h₁ h₂,
  subst n, rw if_pos, {refl}, dsimp at *,
  split,
  { intro s, exact nat.le_add_left (j s) (i s) },
  { intro H, apply h₁,
    suffices : i = 0, { simp [this] },
    ext1 s, specialize H s, rw ← _root_.zero_add (j s) at H,
    apply nat.eq_zero_of_le_zero,
    exact (add_le_add_iff_right (j s)).mp H }
end

section local_ring

def is_local_ring (h : is_local_ring α) : is_local_ring (mv_power_series σ α) :=
begin
  split,
  { intro this, apply ‹is_local_ring α›.1, simpa using congr_arg (coeff 0) this },
  { intro φ, let c := coeff 0 φ,
    have : is_unit c ∨ is_unit (1 - c) := ‹is_local_ring α›.2 c,
    cases this with h h; [left, right]; cases h with u h;
    { apply is_unit_of_mul_one _,
      { apply mul_inv_of_unit, { exact h } } } }
end

end local_ring

end mv_power_series

namespace mv_power_series
variables {σ : Type*} {α : Type*} [decidable_eq σ] [local_ring α]

instance : local_ring (mv_power_series σ α) :=
local_of_is_local_ring $ is_local_ring ⟨zero_ne_one, local_ring.is_local⟩

end mv_power_series

def power_series (α : Type*) := mv_power_series unit α

namespace power_series
open finsupp (single)
variable {α : Type*}

def coeff (n : ℕ) : power_series α → α := mv_power_series.coeff (single () n)

@[extensionality] lemma ext {φ ψ : power_series α} (h : ∀ n, coeff n φ = coeff n ψ) : φ = ψ :=
mv_power_series.ext $ λ n,
begin
  have : n = single () (n ()),
  { ext x, exact match x with | () := by { rw [finsupp.single_apply, if_pos rfl] } end },
  convert h (n ())
end

lemma ext_iff {φ ψ : power_series α} : φ = ψ ↔ (∀ n, coeff n φ = coeff n ψ) :=
⟨λ h n, congr_arg (coeff n) h, ext⟩

def mk (f : ℕ → α) : power_series α := λ s, f (s ())

@[simp] lemma coeff_mk (n : ℕ) (f : ℕ → α) : coeff n (mk f) = f n := rfl

section comm_semiring
variable [comm_semiring α]

instance : comm_semiring (power_series α) := by delta power_series; apply_instance

def monomial (n : ℕ) : α → power_series α := mv_power_series.monomial (single () n)

def C : α → power_series α := mv_power_series.C

def X : power_series α := mv_power_series.X ()

lemma coeff_monomial (m n : ℕ) (a : α) :
  coeff m (monomial n a) = if m = n then a else 0 :=
calc coeff m (monomial n a) = _ : mv_power_series.coeff_monomial _ _ _
    ... = if m = n then a else 0 :
if h : m = n then by { subst m, rw [if_pos rfl, if_pos rfl] } else
begin
  rw [if_neg, if_neg h], intro H, apply h,
  rwa finsupp.single_punit_eq_single_punit_iff at H
end

lemma monomial_eq_mk (n : ℕ) (a : α) :
  monomial n a = mk (λ m, if m = n then a else 0) :=
ext $ λ m, coeff_monomial _ _ _

@[simp] lemma coeff_monomial' (n : ℕ) (a : α) :
  coeff n (monomial n a) = a := if_pos rfl

lemma coeff_C (n : ℕ) (a : α) :
  coeff n (C a : power_series α) = if n = 0 then a else 0 :=
calc coeff n (C a) = _ : mv_power_series.coeff_C _ _
    ... = if n = 0 then a else 0 :
if h : n = 0 then
by { rw [if_pos, if_pos h], rwa [finsupp.single_punit_eq_zero_iff] }
else
by { rw [if_neg, if_neg h], rwa [finsupp.single_punit_eq_zero_iff] }

@[simp] lemma coeff_C_zero (a : α) : coeff 0 (C a) = a :=
coeff_monomial' 0 a

@[simp] lemma monomial_zero (a : α) : (monomial 0 a : power_series α) = C a := rfl

lemma coeff_X (n : ℕ) :
  coeff n (X : power_series α) = if n = 1 then 1 else 0 :=
calc coeff n (X : power_series α) = _ : mv_power_series.coeff_X _ _
    ... = if n = 1 then 1 else 0 :
if h : n = 1 then
by { rw [if_pos, if_pos h], rwa [finsupp.single_punit_eq_single_punit_iff] }
else
by { rw [if_neg, if_neg h], rwa [finsupp.single_punit_eq_single_punit_iff] }

@[simp] lemma coeff_X' : coeff 1 (X : power_series α) = 1 :=
by rw [coeff_X, if_pos rfl]

@[simp] lemma coeff_zero (n : ℕ) : coeff n (0 : power_series α) = 0 := rfl

@[simp] lemma C_zero : (C 0 : power_series α) = 0 := mv_power_series.C_zero _ _

@[simp] lemma coeff_one (n : ℕ) :
  coeff n (1 : power_series α) = if n = 0 then 1 else 0 :=
calc coeff n (1 : power_series α) = _ : mv_power_series.coeff_one _ _ _
    ... = if n = 0 then 1 else 0 :
if h : n = 0 then by { rw [if_pos, if_pos h], rwa finsupp.single_punit_eq_zero_iff }
else by { rw [if_neg, if_neg h], rwa finsupp.single_punit_eq_zero_iff }

@[simp] lemma coeff_one_zero : coeff 0 (1 : power_series α) = 1 :=
coeff_C_zero 1

@[simp] lemma C_one : (C 1 : power_series α) = 1 := rfl

@[simp] lemma coeff_add (n : ℕ) (φ ψ : power_series α) :
  coeff n (φ + ψ) = coeff n φ + coeff n ψ := rfl

@[simp] lemma monomial_add (n : ℕ) (a b : α) :
  (monomial n (a + b) : power_series α) = monomial n a + monomial n b :=
mv_power_series.monomial_add _ _ _

@[simp] lemma C_add (a b : α) : (C (a + b) : power_series α) = C a + C b :=
monomial_add 0 a b

-- lemma coeff_mul (n : ℕ) (φ ψ : power_series α) :
--   coeff n (φ * ψ) = (nat.diagonal n).sum (λ p, coeff p.1 φ * coeff p.2 ψ) := rfl

@[simp] lemma C_mul (a b : α) : (C (a * b) : power_series α) = C a * C b :=
mv_power_series.C_mul _ _

instance C.is_semiring_hom : is_semiring_hom (C : α → power_series α) :=
mv_power_series.C.is_semiring_hom

instance coeff.is_add_monoid_hom (n : ℕ) : is_add_monoid_hom (coeff n : power_series α → α) :=
{ map_zero := coeff_zero n,
  map_add := coeff_add n }

instance : semimodule α (power_series α) :=
mv_power_series.semimodule

end comm_semiring

section comm_ring
variables [comm_ring α]

instance : comm_ring (power_series α) := by delta power_series; apply_instance

instance C.is_ring_hom : is_ring_hom (C : α → power_series α) :=
mv_power_series.C.is_ring_hom

instance : module α (power_series α) :=
mv_power_series.module

instance : algebra α (power_series α) :=
mv_power_series.algebra

end comm_ring

section local_ring
variables [comm_ring α] [is_local_ring α]

instance : is_local_ring (power_series α) :=
_

end local_ring

end power_series


#exit

namespace mv_power_series
open category_theory opposite
variables (σ : Type) (α : Type) [comm_ring α]

noncomputable theory

local attribute [instance, priority 1] classical.prop_decidable

section limit

def X_ideal : ideal (mv_power_series σ α) :=
ideal.span $ set.range X

def diagram : ℕᵒᵖ ⥤ CommRing :=
{ obj := λ i, CommRing.of (ideal.quotient ((X_ideal σ α)^(unop i))),
  map := λ i j h, ⟨ideal.quotient.lift _ (ideal.quotient.mk _)
  begin
    intros φ hφ,
    erw ideal.quotient.eq_zero_iff_mem,
    sorry
  end, by apply_instance⟩ }
.

lemma is_basis (n : ℕ) :
  is_basis α (λ m : {m : σ →₀ ℕ // m.sum (λ _, id) ≤ n },
    (ideal.quotient.mk (X_ideal σ α^n) (monomial m 1))) :=
begin
  delta is_basis,
end

@[simp] lemma diagram_obj (i) :
  (diagram σ α).obj i = CommRing.of (ideal.quotient ((X_ideal σ α)^(unop i))) := rfl

def cone : limits.cone (diagram σ α) :=
{ X := CommRing.of (mv_power_series σ α),
  π := { app := λ i, ⟨ideal.quotient.mk _, by apply_instance⟩ } }

def is_limit : limits.is_limit (cone σ α) :=
{ lift := λ c, ⟨λ x n,
  let N : ℕ := n.sum (λ _, id) in
  _, _⟩ }

end limit

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

namespace mv_polynomial
open category_theory opposite
variables (σ : Type) (α : Type) [decidable_eq σ] [decidable_eq α] [comm_ring α]

section limit

def X_ideal : ideal (mv_polynomial σ α) :=
ideal.span $ set.image X set.univ

-- def diagram : ℕᵒᵖ ⥤ CommRing :=
-- { obj := λ i, CommRing.of (ideal.quotient ((X_ideal σ α)^(unop i))),
--   map := λ i j h,
--   ⟨ideal.quotient.lift _ (ideal.quotient.mk ((X_ideal σ α)^(unop j)))
--   begin
--     intros φ hφ,
--     erw ideal.quotient.eq_zero_iff_mem,
--     sorry
--   end, by apply_instance⟩,
--   map_comp' := λ i j k hij hjk,
--   begin
--     sorry
--   end }
-- .

-- def cone : limits.cone (diagram σ α) :=
-- { X := CommRing.of (mv_power_series σ α),
--   π := _ }

end limit

end mv_polynomial
