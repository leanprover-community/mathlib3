/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mitchell Rowett, Scott Morrison
-/
import data.finset algebra.big_operators data.equiv data.set data.nat.basic set_theory.cardinal
  group_theory.submonoid
open set function

variables {α : Type*} {β : Type*} {s : set α} {a a₁ a₂ b c: α}

-- TODO this lemma isn't used anywhere in this file, and should be moved elsewhere.
namespace finset
open finset

lemma mem_range_iff_mem_finset_range_of_mod_eq [decidable_eq α] {f : ℤ → α} {a : α} {n : ℕ}
  (hn : 0 < n) (h : ∀i, f (i % n) = f i) :
  a ∈ set.range f ↔ a ∈ (finset.range n).image (λi, f i) :=
suffices (∃i, f (i % n) = a) ↔ ∃i, i < n ∧ f ↑i = a, by simpa [h],
have hn' : 0 < (n : ℤ), from int.coe_nat_lt.mpr hn,
iff.intro
  (assume ⟨i, hi⟩,
    have 0 ≤ i % ↑n, from int.mod_nonneg _ (ne_of_gt hn'),
    ⟨int.to_nat (i % n),
      by rw [←int.coe_nat_lt, int.to_nat_of_nonneg this]; exact ⟨int.mod_lt_of_pos i hn', hi⟩⟩)
  (assume ⟨i, hi, ha⟩,
    ⟨i, by rw [int.mod_eq_of_lt (int.coe_zero_le _) (int.coe_nat_lt_coe_nat_of_lt hi), ha]⟩)

end finset

section group
variable [group α]

/-- `s` is a subgroup: a set containing 1 and closed under multiplication and inverse. -/
class is_subgroup [group α] (s : set α) extends is_submonoid s : Prop :=
(inv_mem {a} : a ∈ s → a⁻¹ ∈ s)

instance subtype.group {s : set α} [is_subgroup s] : group s :=
{ inv          := λa, ⟨(a.1)⁻¹, is_subgroup.inv_mem a.2⟩,
  mul_left_inv := assume ⟨a, _⟩, subtype.eq $ mul_left_inv _,
  .. subtype.monoid }

theorem is_subgroup.of_div [group α] (s : set α)
  (one_mem : (1:α) ∈ s) (div_mem : ∀{a b:α}, a ∈ s → b ∈ s → a * b⁻¹ ∈ s):
  is_subgroup s :=
have inv_mem : ∀a, a ∈ s → a⁻¹ ∈ s, from
  assume a ha,
  have 1 * a⁻¹ ∈ s, from div_mem one_mem ha,
  by simpa,
{ inv_mem := inv_mem,
  mul_mem := assume a b ha hb,
    have a * b⁻¹⁻¹ ∈ s, from div_mem ha (inv_mem b hb),
    by simpa,
  one_mem := one_mem }

def gpowers (x : α) : set α := {y | ∃i:ℤ, x^i = y}

instance gpowers.is_subgroup (x : α) : is_subgroup (gpowers x) :=
{ one_mem := ⟨(0:ℤ), by simp⟩,
  mul_mem := assume x₁ x₂ ⟨i₁, h₁⟩ ⟨i₂, h₂⟩, ⟨i₁ + i₂, by simp [gpow_add, *]⟩,
  inv_mem := assume x₀ ⟨i, h⟩, ⟨-i, by simp [h.symm]⟩ }

lemma is_subgroup.gpow_mem {a : α} {s : set α} [is_subgroup s] (h : a ∈ s) : ∀{i:ℤ}, a ^ i ∈ s
| (n : ℕ) := is_submonoid.pow_mem h
| -[1+ n] := is_subgroup.inv_mem (is_submonoid.pow_mem h)

end group

namespace is_subgroup
open is_submonoid
variable (s)
variables [group α] [is_subgroup s]

lemma inv_mem_iff : a⁻¹ ∈ s ↔ a ∈ s :=
iff.intro (assume h, have a⁻¹⁻¹ ∈ s, from inv_mem h, by simpa) inv_mem

lemma mul_mem_cancel_left (h : a ∈ s) : b * a ∈ s ↔ b ∈ s :=
iff.intro
  (assume hba,
    have (b * a) * a⁻¹ ∈ s, from mul_mem hba (inv_mem h),
    by simpa)
  (assume hb, mul_mem hb h)

lemma mul_mem_cancel_right (h : a ∈ s) : a * b ∈ s ↔ b ∈ s :=
iff.intro
  (assume hab,
    have a⁻¹ * (a * b) ∈ s, from mul_mem (inv_mem h) hab,
    by simpa)
  (mul_mem h)

end is_subgroup

-- todo use left_cosets
def cosets [group α] (s : set α) : set (set α) := range (λa, (*) a '' s)

lemma injective_mul [group α] {a : α} : injective ((*) a) :=
assume a₁ a₂ h,
have a⁻¹ * a * a₁ = a⁻¹ * a * a₂, by rw [mul_assoc, mul_assoc, h],
by rwa [inv_mul_self, one_mul, one_mul] at this

namespace is_subgroup
open is_submonoid
variable [group α]

lemma mul_image [is_subgroup s] (a : α) (ha : a ∈ s) :
  (*) a '' s = s :=
ext $ assume a', iff.intro
  (assume ⟨a'', ha'', eq⟩, eq ▸ mul_mem ha ha'')
  (assume ha', ⟨a⁻¹ * a', mul_mem (inv_mem ha) ha', by simp⟩)

section
variable (s)
lemma subgroup_mem_cosets [is_subgroup s] : s ∈ cosets s :=
⟨1, mul_image _ (one_mem s)⟩
end

lemma cosets_disjoint [is_subgroup s] :
  ∀{s₁ s₂ : set α}, s₁ ∈ cosets s → s₂ ∈ cosets s → ∀{a}, a ∈ s₁ → a ∈ s₂ → s₁ = s₂
| _ _ ⟨b₁, rfl⟩ ⟨b₂, rfl⟩ a ⟨c₁, hc₁, eq₁⟩ ⟨c₂, hc₂, eq₂⟩ :=
have b_eq : b₁ = b₂ * c₂ * c₁⁻¹, by rw [eq_mul_inv_iff_mul_eq, eq₁, eq₂],
have hc : c₂ * c₁⁻¹ ∈ s, from mul_mem hc₂ (inv_mem hc₁),
calc (*) b₁ '' s = (*) b₂ '' ((*) (c₂ * c₁⁻¹) '' s) :
    by rw [←image_comp, (∘), b_eq]; apply image_congr _; simp [mul_assoc]
  ... = (*) b₂ '' s :
    by rw [mul_image _ hc]

lemma pairwise_cosets_disjoint (hs : is_subgroup s) : pairwise_on (cosets s) disjoint :=
assume s₁ h₁ s₂ h₂ ne, eq_empty_iff_forall_not_mem.mpr $ assume a ⟨ha₁, ha₂⟩,
  ne $ cosets_disjoint h₁ h₂ ha₁ ha₂

lemma cosets_equiv_subgroup (hs : is_subgroup s) : ∀{t : set α}, t ∈ cosets s → nonempty (t ≃ s)
| _ ⟨a, rfl⟩ := ⟨(equiv.set.image ((*) a) s injective_mul).symm⟩

lemma Union_cosets_eq_univ (hs : is_subgroup s) : ⋃₀ cosets s = univ :=
eq_univ_of_forall $ assume a, ⟨(*) a '' s, mem_range_self _, ⟨1, hs.one_mem, mul_one _⟩⟩

lemma group_equiv_cosets_times_subgroup (hs : is_subgroup s) : nonempty (α ≃ (cosets s × s)) :=
⟨calc α ≃ (@set.univ α) :
    (equiv.set.univ α).symm
  ... ≃ (⋃t∈cosets s, t) :
    by rw [←hs.Union_cosets_eq_univ]; simp
  ... ≃ (Σt:cosets s, t) :
    equiv.set.bUnion_eq_sigma_of_disjoint hs.pairwise_cosets_disjoint
  ... ≃ (Σt:cosets s, s) :
    equiv.sigma_congr_right $ λ⟨t, ht⟩, classical.choice $ hs.cosets_equiv_subgroup ht
  ... ≃ (cosets s × s) :
    equiv.sigma_equiv_prod _ _⟩

end is_subgroup

section order_of
variables [group α] [fintype α] [decidable_eq α]

lemma exists_gpow_eq_one (a : α) : ∃i≠0, a ^ (i:ℤ) = 1 :=
have ¬ injective (λi, a ^ i),
  from not_injective_int_fintype,
let ⟨i, j, a_eq, ne⟩ := show ∃(i j : ℤ), a ^ i = a ^ j ∧ i ≠ j,
  by rw [injective] at this; simpa [classical.not_forall] in
have a ^ (i - j) = 1,
  by simp [gpow_add, gpow_neg, a_eq],
⟨i - j, sub_ne_zero.mpr ne, this⟩

lemma exists_pow_eq_one (a : α) : ∃i≠0, a ^ i = 1 :=
let ⟨i, hi, eq⟩ := exists_gpow_eq_one a in
begin
  cases i,
  { exact ⟨i, by simp [int.of_nat_eq_coe, *] at *, eq⟩ },
  { exact ⟨i + 1, dec_trivial, inv_eq_one.1 eq⟩ }
end

/-- `order_of a` is the order of the element, i.e. the `n ≥ 1`, s.t. `a ^ n = 1` -/
def order_of (a : α) : ℕ := nat.find (exists_pow_eq_one a)

lemma pow_order_of_eq_one (a : α) : a ^ order_of a = 1 :=
let ⟨h₁, h₂⟩ := nat.find_spec (exists_pow_eq_one a) in h₂

lemma order_of_ne_zero (a : α) : order_of a ≠ 0 :=
let ⟨h₁, h₂⟩ := nat.find_spec (exists_pow_eq_one a) in h₁

private lemma pow_injective_aux {n m : ℕ} (a : α) (h : n ≤ m)
  (hn : n < order_of a) (hm : m < order_of a) (eq : a ^ n = a ^ m) : n = m :=
decidable.by_contradiction $ assume ne : n ≠ m,
  have h₁ : m - n ≠ 0, by simp [nat.sub_eq_iff_eq_add h, ne.symm],
  have h₂ : a ^ (m - n) = 1, by simp [pow_sub _ h, eq],
  have le : order_of a ≤ m - n, from nat.find_min' (exists_pow_eq_one a) ⟨h₁, h₂⟩,
  have lt : m - n < order_of a,
    from (nat.sub_lt_left_iff_lt_add h).mpr $ nat.lt_add_left _ _ _ hm,
  lt_irrefl _ (lt_of_le_of_lt le lt)

lemma pow_injective_of_lt_order_of {n m : ℕ} (a : α)
  (hn : n < order_of a) (hm : m < order_of a) (eq : a ^ n = a ^ m) : n = m :=
(le_total n m).elim
  (assume h, pow_injective_aux a h hn hm eq)
  (assume h, (pow_injective_aux a h hm hn eq.symm).symm)

lemma order_of_le_card_univ : order_of a ≤ fintype.card α :=
finset.card_le_of_inj_on ((^) a)
  (assume n _, fintype.complete _)
  (assume i j, pow_injective_of_lt_order_of a)

lemma pow_eq_mod_order_of {n : ℕ} : a ^ n = a ^ (n % order_of a) :=
calc a ^ n = a ^ (n % order_of a + order_of a * (n / order_of a)) :
    by rw [nat.mod_add_div]
  ... = a ^ (n % order_of a) :
    by simp [pow_add, pow_mul, pow_order_of_eq_one]

lemma gpow_eq_mod_order_of {i : ℤ} : a ^ i = a ^ (i % order_of a) :=
calc a ^ i = a ^ (i % order_of a + order_of a * (i / order_of a)) :
    by rw [int.mod_add_div]
  ... = a ^ (i % order_of a) :
    by simp [gpow_add, gpow_mul, pow_order_of_eq_one]

lemma mem_range_gpow_iff_mem_range_order_of {a a' : α} :
  a' ∈ range ((^) a : ℤ → α) ↔ a' ∈ (finset.range (order_of a)).image ((^) a : ℕ → α) :=
finset.mem_range_iff_mem_finset_range_of_mod_eq
  (nat.pos_iff_ne_zero.mpr (order_of_ne_zero a))
  (assume i, gpow_eq_mod_order_of.symm)

instance decidable_range_gpow : decidable_pred (range ((^) a : ℤ → α)) :=
assume a', decidable_of_iff'
  (a' ∈ (finset.range (order_of a)).image ((^) a))
  mem_range_gpow_iff_mem_range_order_of

section
local attribute [instance] set_fintype

lemma order_eq_card_range_gpow : order_of a = fintype.card (range ((^) a : ℤ → α)) :=
begin
  refine (finset.card_eq_of_bijective _ _ _ _).symm,
  { exact λn hn, ⟨gpow a n, mem_range_self n⟩ },
  { exact assume ⟨_, i, rfl⟩ _,
      have pos: (0:int) < order_of a,
        from int.coe_nat_lt.mpr $ nat.pos_iff_ne_zero.mpr $ order_of_ne_zero a,
      have 0 ≤ i % (order_of a),
        from int.mod_nonneg _ $ ne_of_gt pos,
      ⟨int.to_nat (i % order_of a),
        by rw [← int.coe_nat_lt, int.to_nat_of_nonneg this];
          exact ⟨int.mod_lt_of_pos _ pos, subtype.eq gpow_eq_mod_order_of.symm⟩⟩ },
  { intros, exact finset.mem_univ _ },
  { exact assume i j hi hj eq, pow_injective_of_lt_order_of a hi hj $ by simpa using eq }
end

section classical
local attribute [instance] classical.prop_decidable

-- TODO: use cardinal theory, or introduce `card : set α → ℕ`
lemma order_of_dvd_card_univ : order_of a ∣ fintype.card α :=
let ⟨equiv⟩ := (gpowers.is_subgroup a).group_equiv_cosets_times_subgroup in
have ft_prod : fintype (cosets (gpowers a) × (gpowers a)),
  from fintype.of_equiv α equiv,
have ft_s : fintype (gpowers a),
  from @fintype.fintype_prod_right _ _ _ ft_prod
    ⟨⟨(gpowers a), @is_subgroup.subgroup_mem_cosets α _ _ (gpowers.is_subgroup a)⟩⟩,
have ft_cosets : fintype (cosets (gpowers a)),
  from @fintype.fintype_prod_left _ _ _ ft_prod ⟨⟨1, is_submonoid.one_mem (gpowers a)⟩⟩,
have ft : fintype (cosets (gpowers a) × (gpowers a)),
  from @prod.fintype _ _ ft_cosets ft_s,
have eq₁ : fintype.card α = @fintype.card _ ft_cosets * @fintype.card _ ft_s,
  from calc fintype.card α = @fintype.card _ ft_prod :
      (@fintype.card_eq _ _ _ ft_prod).2 (gpowers.is_subgroup a).group_equiv_cosets_times_subgroup
    ... = @fintype.card _ (@prod.fintype _ _ ft_cosets ft_s) :
      congr_arg (@fintype.card _) $ subsingleton.elim _ _
    ... = @fintype.card _ ft_cosets * @fintype.card _ ft_s :
      @fintype.card_prod _ _ ft_cosets ft_s,
have eq₂ : order_of a = @fintype.card _ ft_s,
  from calc order_of a = _ : order_eq_card_range_gpow
    ... = _ : congr_arg (@fintype.card _) $ subsingleton.elim _ _,
dvd.intro (@fintype.card (cosets (gpowers a)) ft_cosets) $
  by rw [eq₁, eq₂, mul_comm]

end classical

end

end order_of

class normal_subgroup [group α] (S : set α) extends is_subgroup S : Prop :=
(normal : ∀ n ∈ S, ∀ g : α, g * n * g⁻¹ ∈ S)

namespace is_subgroup
variable [group α]

-- Normal subgroup properties
lemma mem_norm_comm {a b : α} {S : set α} [normal_subgroup S] (hab : a * b ∈ S) : b * a ∈ S :=
have h : a⁻¹ * (a * b) * a⁻¹⁻¹ ∈ S, from normal_subgroup.normal (a * b) hab a⁻¹,
by simp at h; exact h

-- Examples of subgroups
def trivial (α : Type*) [group α] : set α := {1}

lemma eq_one_of_trivial_mem [group α] {g : α} (p : g ∈ trivial α) : g = 1 :=
begin
  cases p,
  assumption,
  cases p,
end

lemma trivial_mem_of_eq_one [group α] {g : α} (p : g = 1) : g ∈ trivial α :=
begin
  rw p,
  unfold trivial,
  simp,
end

instance trivial_normal : normal_subgroup (trivial α) :=
by refine {..}; simp [trivial] {contextual := tt}

instance univ_subgroup : normal_subgroup (@univ α) :=
by refine {..}; simp

def center (α : Type*) [group α] : set α := {z | ∀ g, g * z = z * g}

instance center_normal : normal_subgroup (center α) := {
  one_mem := by simp [center],
  mul_mem :=
    begin
      intros a b ha hb g,
      rw [center, mem_set_of_eq] at *,
      rw [←mul_assoc, ha g, mul_assoc, hb g, ←mul_assoc]
    end,
  inv_mem :=
    begin
      assume a ha g,
      simp [center] at *,
      calc
        g * a⁻¹ = a⁻¹ * (g * a) * a⁻¹     : by simp [ha g]
        ...     = a⁻¹ * g                 : by rw [←mul_assoc, mul_assoc]; simp
    end,
  normal :=
    begin
      simp [center, mem_set_of_eq],
      intros n ha g h,
      calc
        h * (g * n * g⁻¹) = h * n               : by simp [ha g, mul_assoc]
        ...               = g * g⁻¹ * n * h     : by rw ha h; simp
        ...               = g * n * g⁻¹ * h     : by rw [mul_assoc g, ha g⁻¹, ←mul_assoc]
    end
}

end is_subgroup

-- Homomorphism subgroups
namespace is_group_hom
open is_submonoid
open is_subgroup
variables [group α] [group β]

def kernel (f : α → β) [is_group_hom f] : set α := preimage f (trivial β)

lemma mem_ker_one (f : α → β) [is_group_hom f] {x : α} (h : x ∈ kernel f) : f x = 1 := eq_one_of_trivial_mem h

lemma one_ker_inv (f : α → β) [is_group_hom f] {a b : α} (h : f (a * b⁻¹) = 1) : f a = f b := by rw ←inv_inv (f b); rw [mul f, inv f] at h; exact eq_inv_of_mul_eq_one h

lemma inv_ker_one (f : α → β) [is_group_hom f] {a b : α} (h : f a = f b) : f (a * b⁻¹) = 1 :=
have f a * (f b)⁻¹ = 1, by rw h; apply mul_right_inv,
by rw [←inv f, ←mul f] at this; exact this

lemma ker_inv (f : α → β) [is_group_hom f] {a b : α} (h : a * b⁻¹ ∈ kernel f) : f a = f b := one_ker_inv f $ mem_ker_one f h

lemma inv_ker (f : α → β) [is_group_hom f] {a b : α} (h : f a = f b) : a * b⁻¹ ∈ kernel f := by simp [kernel,mem_set_of_eq]; exact trivial_mem_of_eq_one (inv_ker_one f h)

lemma one_iff_ker_inv (f : α → β) [is_group_hom f] (a b : α) : f a = f b ↔ f (a * b⁻¹) = 1 :=
⟨inv_ker_one f, one_ker_inv f⟩

lemma inv_iff_ker (f : α → β) [w : is_group_hom f] (a b : α) : f a = f b ↔ a * b⁻¹ ∈ kernel f :=
/- TODO: I don't understand why I can't just write
    ⟨inv_ker f, ker_inv f⟩
  here. This still gives typeclass errors; it can't find `w`. -/
⟨@inv_ker _ _ _ _ f w _ _, @ker_inv _ _ _ _ f w _ _⟩

instance image_subgroup (f : α → β) [is_group_hom f] (S : set α) [is_subgroup S] : is_subgroup (f '' S) :=
{ mul_mem := assume a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
             ⟨b₁ * b₂, mul_mem hb₁ hb₂, by simp [eq₁, eq₂, mul f]⟩,
  one_mem := ⟨1, one_mem S, one f⟩,
  inv_mem := assume a ⟨b, hb, eq⟩, ⟨b⁻¹, inv_mem hb, by rw inv f; simp *⟩ }

local attribute [simp] one_mem inv_mem mul_mem normal_subgroup.normal

private lemma inv' (f : α → β) [is_group_hom f] (a : α) : (f a)⁻¹ = f a⁻¹ := by rw ←inv f

instance preimage (f : α → β) [is_group_hom f] (S : set β) [is_subgroup S] : is_subgroup (f ⁻¹' S) :=
begin
 refine {..};
 simp [mul f, one f, inv' f] {contextual:=tt},
 intros g w,
 rw inv f,
 exact (inv_mem_iff S).2 w,
end

instance preimage_normal (f : α → β) [is_group_hom f] (S : set β) [normal_subgroup S] :
  normal_subgroup (f ⁻¹' S) :=
begin
 refine {..},
 { simp [one f] },
 { simp [mul f] {contextual:=tt} },
 { simp [inv' f],
   intros g w,
   rw inv f,
   exact (inv_mem_iff S).2 w },
 { simp [mul f, inv f] {contextual:=tt} }
end

instance kernel_normal (f : α → β) [is_group_hom f] : normal_subgroup (kernel f) :=
is_group_hom.preimage_normal f (trivial β)

lemma inj_of_trivial_kernel (f : α → β) [is_group_hom f] (h : kernel f = trivial α) :
  function.injective f :=
begin
  intros a₁ a₂ hfa,
  simp [set_eq_def, kernel, is_subgroup.trivial] at h,
  have ha : a₁ * a₂⁻¹ = 1, by rw ←h; exact inv_ker_one f hfa,
  rw [eq_inv_of_mul_eq_one ha, inv_inv a₂]
end

lemma trivial_kernel_of_inj (f : α → β) [w : is_group_hom f] (h : function.injective f) :
  kernel f = trivial α :=
begin
  apply set.ext,
  intro,
  split,
  { assume hx,
    have hi : f x = f 1,
    { simp [one f]; rw (@mem_ker_one _ _ _ _ f w _ hx) }, -- TODO not finding the typeclass
    apply trivial_mem_of_eq_one,
    simp [h hi, one f] },
  { assume hx, rw eq_one_of_trivial_mem hx, simp }
end

lemma inj_iff_trivial_kernel (f : α → β) [w : is_group_hom f] :
  function.injective f ↔ kernel f = trivial α :=
-- TODO: still not finding the typeclass. ⟨trivial_kernel_of_inj f, inj_of_trivial_kernel f⟩
⟨@trivial_kernel_of_inj _ _ _ _ f w, @inj_of_trivial_kernel _ _ _ _ f w⟩

end is_group_hom

