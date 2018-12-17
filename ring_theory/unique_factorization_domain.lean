/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker

Theory of unique factorization domains.

@TODO: setup the complete lattice structure on `factor_set`.
-/
import ring_theory.associated algebra.gcd_domain

variables {α : Type*}
local infix ` ~ᵤ ` : 50 := associated

/-- Unique factorization domains.

In a unique factorization domain each element (except zero) is uniquely represented as a multiset
of irreducible factors. Uniqueness is only up to associated elements.
-/
class unique_factorization_domain (α : Type*) [integral_domain α] :=
(factors : α → multiset α)
(factors_prod : ∀{a : α}, a ≠ 0 → (factors a).prod ~ᵤ a)
(irreducible_factors : ∀{a : α}, a ≠ 0 →  ∀x∈factors a, irreducible x)
(unique : ∀{f g : multiset α},
  (∀x∈f, irreducible x) → (∀x∈g, irreducible x) → f.prod ~ᵤ g.prod → multiset.rel associated f g)

namespace associates
open unique_factorization_domain associated lattice
variables [integral_domain α] [unique_factorization_domain α] [decidable_eq (associates α)]

/-- `factor_set α` representation elements of unique factorization domain as multisets.

`multiset α` produced by `factors` are only unique up to associated elements, while the multisets in
`factor_set α` are unqiue by equality and restricted to irreducible elements. This gives us a
representation of each element as a unique multisets (or the added ⊤ for 0), which has a complete
lattice struture. Infimum is the greatest common divisor and supremum is the least common multiple.
-/
@[reducible] def {u} factor_set (α : Type u) [integral_domain α] [unique_factorization_domain α] :
  Type u :=
with_top (multiset { a : associates α // irreducible a })

local attribute [instance] associated.setoid

theorem unique' {p q : multiset (associates α)} :
  (∀a∈p, irreducible a) → (∀a∈q, irreducible a) → p.prod = q.prod → p = q :=
begin
  apply multiset.induction_on_multiset_quot p,
  apply multiset.induction_on_multiset_quot q,
  assume s t hs ht eq,
  refine multiset.map_mk_eq_map_mk_of_rel (unique_factorization_domain.unique _ _ _),
  { exact assume a ha, ((irreducible_mk_iff _).1 $ hs _ $ multiset.mem_map_of_mem _ ha) },
  { exact assume a ha, ((irreducible_mk_iff _).1 $ ht _ $ multiset.mem_map_of_mem _ ha) },
  simpa [quot_mk_eq_mk, prod_mk, mk_eq_mk_iff_associated] using eq
end

private theorem forall_map_mk_factors_irreducible (x : α) (hx : x ≠ 0) :
  ∀(a : associates α), a ∈ multiset.map associates.mk (factors x) → irreducible a :=
begin
  assume a ha,
  rcases multiset.mem_map.1 ha with ⟨c, hc, rfl⟩,
  exact (irreducible_mk_iff c).2 (irreducible_factors hx _ hc)
end

theorem prod_le_prod_iff_le {p q : multiset (associates α)}
  (hp : ∀a∈p, irreducible a) (hq : ∀a∈q, irreducible a) :
  p.prod ≤ q.prod ↔ p ≤ q :=
iff.intro
  begin
    rintros ⟨⟨c⟩, eq⟩,
    have : c ≠ 0, from (mt mk_eq_zero_iff_eq_zero.2 $
      assume (hc : quot.mk setoid.r c = 0),
      have (0 : associates α) ∈ q, from prod_eq_zero_iff.1 $ eq ▸ hc.symm ▸ mul_zero _,
      not_irreducible_zero ((irreducible_mk_iff 0).1 $ hq _ this)),
    have : associates.mk (factors c).prod = quot.mk setoid.r c,
      from mk_eq_mk_iff_associated.2 (factors_prod this),

    refine le_iff_exists_add.2 ⟨(factors c).map associates.mk, unique' hq _ _⟩,
    { assume x hx,
      rcases multiset.mem_add.1 hx with h | h,
      exact hp x h,
      exact forall_map_mk_factors_irreducible c ‹c ≠ 0› _ h },
    { simp [multiset.prod_add, prod_mk, *] at * }
  end
  prod_le_prod

@[simp] theorem factor_set.coe_add {a b : multiset { a : associates α // irreducible a }} :
  (↑a + ↑b : factor_set α) = ↑(a + b) :=
with_top.coe_add

lemma factor_set.sup_add_inf_eq_add : ∀(a b : factor_set α), a ⊔ b + a ⊓ b = a + b
| none     b        := show ⊤ ⊔ b + ⊤ ⊓ b = ⊤ + b, by simp
| a        none     := show a ⊔ ⊤ + a ⊓ ⊤ = a + ⊤, by simp
| (some a) (some b) := show (a : factor_set α) ⊔ b + a ⊓ b = a + b, from
  begin
    rw [← with_top.coe_sup, ← with_top.coe_inf, ← with_top.coe_add, ← with_top.coe_add,
      with_top.coe_eq_coe],
    exact multiset.union_add_inter _ _
  end

def factors' (a : α) (ha : a ≠ 0) : multiset { a : associates α // irreducible a } :=
(factors a).pmap (λa ha, ⟨associates.mk a, (irreducible_mk_iff _).2 ha⟩)
  (irreducible_factors $ ha)

@[simp] theorem map_subtype_val_factors' {a : α} (ha : a ≠ 0) :
  (factors' a ha).map subtype.val = (factors a).map associates.mk :=
by simp [factors', multiset.map_pmap, multiset.pmap_eq_map]

theorem factors'_cong {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) (h : a ~ᵤ b) :
  factors' a ha = factors' b hb :=
have multiset.rel associated (factors a) (factors b), from
  unique (irreducible_factors ha) (irreducible_factors hb)
    ((factors_prod ha).trans $ h.trans $ (factors_prod hb).symm),
by simpa [(multiset.map_eq_map subtype.val_injective).symm, rel_associated_iff_map_eq_map.symm]

def factors (a : associates α) : factor_set α :=
begin
  refine (if h : a = 0 then ⊤ else
    quotient.hrec_on a (λx h, some $ factors' x (mt mk_eq_zero_iff_eq_zero.2 h)) _ h),

  assume a b hab,
  apply function.hfunext,
  { have : a ~ᵤ 0 ↔ b ~ᵤ 0, from
      iff.intro (assume ha0, hab.symm.trans ha0) (assume hb0, hab.trans hb0),
    simp [quotient_mk_eq_mk, mk_eq_zero_iff_eq_zero, (associated_zero_iff_eq_zero _).symm, this] },
  exact (assume ha hb eq, heq_of_eq $ congr_arg some $ factors'_cong _ _ hab)
end

@[simp] theorem factors_0 : (0 : associates α).factors = ⊤ :=
dif_pos rfl

@[simp] theorem factors_mk (a : α) (h : a ≠ 0) : (associates.mk a).factors = factors' a h :=
dif_neg (mt mk_eq_zero_iff_eq_zero.1 h)

def factor_set.prod : factor_set α → associates α
| none     := 0
| (some s) := (s.map subtype.val).prod

@[simp] theorem prod_top : (⊤ : factor_set α).prod = 0 := rfl

@[simp] theorem prod_coe {s : multiset { a : associates α // irreducible a }} :
  (s : factor_set α).prod = (s.map subtype.val).prod :=
rfl

theorem prod_factors : ∀(s : factor_set α), s.prod.factors = s
| none     := by simp [factor_set.prod]; refl
| (some s) :=
  begin
    unfold factor_set.prod,
    generalize eq_a : (s.map subtype.val).prod = a,
    rcases a with ⟨a⟩,
    rw quot_mk_eq_mk at *,

    have : (s.map subtype.val).prod ≠ 0, from assume ha,
      let ⟨⟨a, ha⟩, h, eq⟩ := multiset.mem_map.1 (prod_eq_zero_iff.1 ha) in
      have irreducible (0 : associates α), from eq ▸ ha,
      not_irreducible_zero ((irreducible_mk_iff _).1 this),
    have ha : a ≠ 0, by simp [*] at *,
    suffices : (unique_factorization_domain.factors a).map associates.mk = s.map subtype.val,
    { rw [factors_mk a ha],
      apply congr_arg some _,
      simpa [(multiset.map_eq_map subtype.val_injective).symm] },

    refine unique'
      (forall_map_mk_factors_irreducible _ ha)
      (assume a ha, let ⟨⟨x, hx⟩, ha, eq⟩ := multiset.mem_map.1 ha in eq ▸ hx)
      _,
    rw [prod_mk, eq_a, mk_eq_mk_iff_associated],
    exact factors_prod ha
  end

theorem factors_prod (a : associates α) : a.factors.prod = a :=
quotient.induction_on a $ assume a, decidable.by_cases
  (assume : associates.mk a = 0, by simp [quotient_mk_eq_mk, this])
  (assume : associates.mk a ≠ 0,
    have a ≠ 0, by simp * at *,
    by simp [this, quotient_mk_eq_mk, prod_mk, mk_eq_mk_iff_associated.2 (factors_prod this)])

theorem eq_of_factors_eq_factors {a b : associates α} (h : a.factors = b.factors) : a = b :=
have a.factors.prod = b.factors.prod, by rw h,
by rwa [factors_prod, factors_prod] at this

theorem eq_of_prod_eq_prod {a b : factor_set α} (h : a.prod = b.prod) : a = b :=
have a.prod.factors = b.prod.factors, by rw h,
by rwa [prod_factors, prod_factors] at this

@[simp] theorem prod_add : ∀(a b : factor_set α), (a + b).prod = a.prod * b.prod
| none b    := show (⊤ + b).prod = (⊤:factor_set α).prod * b.prod, by simp
| a    none := show (a + ⊤).prod = a.prod * (⊤:factor_set α).prod, by simp
| (some a) (some b) :=
  show (↑a + ↑b:factor_set α).prod = (↑a:factor_set α).prod * (↑b:factor_set α).prod,
    by rw [factor_set.coe_add, prod_coe, prod_coe, prod_coe, multiset.map_add, multiset.prod_add]

theorem prod_mono : ∀{a b : factor_set α}, a ≤ b → a.prod ≤ b.prod
| none b h := have b = ⊤, from top_unique h, by rw [this, prod_top]; exact le_refl _
| a none h := show a.prod ≤ (⊤ : factor_set α).prod, by simp; exact le_top
| (some a) (some b) h := prod_le_prod $ multiset.map_le_map $ with_top.coe_le_coe.1 $ h

@[simp] theorem factors_mul (a b : associates α) : (a * b).factors = a.factors + b.factors :=
eq_of_prod_eq_prod $ eq_of_factors_eq_factors $
  by rw [prod_add, factors_prod, factors_prod, factors_prod]

theorem factors_mono : ∀{a b : associates α}, a ≤ b → a.factors ≤ b.factors
| s t ⟨d, rfl⟩ := by rw [factors_mul] ; exact le_add_of_nonneg_right' bot_le

theorem factors_le {a b : associates α} : a.factors ≤ b.factors ↔ a ≤ b :=
iff.intro
  (assume h, have a.factors.prod ≤ b.factors.prod, from prod_mono h,
    by rwa [factors_prod, factors_prod] at this)
  factors_mono

theorem prod_le {a b : factor_set α} : a.prod ≤ b.prod ↔ a ≤ b :=
iff.intro
  (assume h, have a.prod.factors ≤ b.prod.factors, from factors_mono h,
    by rwa [prod_factors, prod_factors] at this)
  prod_mono

instance : has_sup (associates α) := ⟨λa b, (a.factors ⊔ b.factors).prod⟩
instance : has_inf (associates α) := ⟨λa b, (a.factors ⊓ b.factors).prod⟩

instance : bounded_lattice (associates α) :=
{ sup          := (⊔),
  inf          := (⊓),
  sup_le       :=
    assume a b c hac hbc, factors_prod c ▸ prod_mono (sup_le (factors_mono hac) (factors_mono hbc)),
  le_sup_left  := assume a b,
    le_trans (le_of_eq (factors_prod a).symm) $ prod_mono $ le_sup_left,
  le_sup_right := assume a b,
    le_trans (le_of_eq (factors_prod b).symm) $ prod_mono $ le_sup_right,
  le_inf :=
    assume a b c hac hbc, factors_prod a ▸ prod_mono (le_inf (factors_mono hac) (factors_mono hbc)),
  inf_le_left  := assume a b,
    le_trans (prod_mono inf_le_left) (le_of_eq (factors_prod a)),
  inf_le_right := assume a b,
    le_trans (prod_mono inf_le_right) (le_of_eq (factors_prod b)),
  .. associates.partial_order,
  .. associates.lattice.order_top,
  .. associates.lattice.order_bot }

lemma sup_mul_inf (a b : associates α) : (a ⊔ b) * (a ⊓ b) = a * b :=
show (a.factors ⊔ b.factors).prod * (a.factors ⊓ b.factors).prod = a * b,
begin
  refine eq_of_factors_eq_factors _,
  rw [← prod_add, prod_factors, factors_mul, factor_set.sup_add_inf_eq_add]
end

end associates

section
open associates unique_factorization_domain lattice

/-- `to_gcd_domain` constructs a GCD domain out of a unique factorization domain over a normalization
domain. -/
def unique_factorization_domain.to_gcd_domain
  (α : Type*) [normalization_domain α] [unique_factorization_domain α] [decidable_eq (associates α)] :
  gcd_domain α :=
{ gcd := λa b, (associates.mk a ⊓ associates.mk b).out,
  lcm := λa b, (associates.mk a ⊔ associates.mk b).out,
  gcd_dvd_left := assume a b, (out_dvd_iff a (associates.mk a ⊓ associates.mk b)).2 $ inf_le_left,
  gcd_dvd_right := assume a b, (out_dvd_iff b (associates.mk a ⊓ associates.mk b)).2 $ inf_le_right,
  dvd_gcd := assume a b c hac hab, show a ∣ (associates.mk c ⊓ associates.mk b).out,
    by rw [dvd_out_iff, le_inf_iff, mk_le_mk_iff_dvd_iff, mk_le_mk_iff_dvd_iff]; exact ⟨hac, hab⟩,
  lcm_zero_left := assume a, show (⊤ ⊔ associates.mk a).out = 0, by simp,
  lcm_zero_right := assume a, show (associates.mk a ⊔ ⊤).out = 0, by simp,
  gcd_mul_lcm := assume a b,
    show (associates.mk a ⊓ associates.mk b).out * (associates.mk a ⊔ associates.mk b).out =
      a * b * norm_unit (a * b),
    by rw [← out_mk, ← out_mul, mul_comm, sup_mul_inf]; refl,
  norm_unit_gcd := assume a b, norm_unit_out _,
  .. ‹normalization_domain α› }

end
