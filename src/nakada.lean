/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import algebra.order.group
import algebra.order.with_zero
import group_theory.submonoid.basic
import tactic.tfae

/-!
# Formalization of linear extensions to partially ordered semigroups

Following [PARTIALLY ORDERED ABELIAN SEMIGROUPS]
(https://eprints.lib.hokudai.ac.jp/dspace/bitstream/2115/55970/1/JFSHIU_11_N4_181-189.pdf)
-/

open function (swap)

section page181

variables (S : Type*) [has_mul S] [has_le S]

-- Definition 1
@[to_additive add_nakada_po]
abbreviation nakada_po : Prop :=
covariant_class S S (*) (≤)

variables {S}

@[to_additive add_homogeneity]
lemma homogeneity [nakada_po S] {a b : S} (h : a ≤ b) (c : S) :
  c * a ≤ c * b :=
mul_le_mul_left' h c

variables (S)

-- Definition 2
@[to_additive add_nakada_strong]
abbreviation nakada_strong : Prop :=
contravariant_class S S (*) (≤)

variables {S}

@[to_additive add_strong]
lemma strong [nakada_strong S] {a b c : S} (h : a * b ≤ a * c) : b ≤ c :=
le_of_mul_le_mul_left' h

-- Theorem 1
@[priority 10, to_additive add_group.add_nakada_strong]
instance group.nakada_strong {G : Type*} [group G] [has_le G] [nakada_po G] :
  nakada_strong G :=
⟨λ c a b h, by simpa using homogeneity h c⁻¹⟩

end page181

section page182

variables {S : Type*} [has_mul S] [partial_order S]

-- Theorem 2.1
@[to_additive]
lemma nakada_strong.cancel_left [nakada_strong S] {a b c : S} (h : a * b = a * c) :
  b = c :=
le_antisymm (strong h.le) (strong h.ge)

-- Theorem 2.2
@[to_additive]
instance nakada_strong.contravariant_mul_lt [nakada_strong S] :
  contravariant_class S S (*) (<) :=
⟨λ a b c h, begin
  by_cases H : b = c,
  { simpa [H] using h },
  { simpa [lt_iff_le_and_ne, H] using strong h.le }
end⟩

-- Theorem 2.3
@[to_additive add_nakada_po.covariant_add_lt_of_add_nakada_strong]
instance nakada_po.covariant_mul_lt_of_nakada_strong [nakada_po S] [nakada_strong S] :
  covariant_class S S (*) (<) :=
⟨λ a b c h, begin
  by_cases H : a * b = a * c,
  { rw [nakada_strong.cancel_left H] at h,
    exact absurd h (lt_irrefl _) },
  { simpa [lt_iff_le_and_ne, H] using homogeneity h.le c }
end⟩

-- Theorem 3.1
@[to_additive add_nakada_lo.contravariant_add_lt]
instance nakada_lo.contravariant_mul_lt {S : Type*} [has_mul S] [linear_order S] [nakada_po S] :
  contravariant_class S S (*) (<) :=
⟨λ a b c h, begin
  refine (le_or_lt _ _).resolve_left (λ H, _),
  exact absurd (homogeneity H a) h.not_le
end⟩

-- extra api
attribute [to_additive nsmul_le_nsmul_of_le] pow_le_pow_of_le

-- Theorem 3.2
@[to_additive nsmul_lt_nsmul_cancel]
lemma pow_lt_pow_cancel {S : Type*} [comm_monoid S] [linear_order S] [nakada_po S] {a b : S} {n : ℕ}
  (h : a ^ n < b ^ n) : a < b :=
begin
  refine (le_or_lt _ _).resolve_left (λ H, _),
  exact absurd (pow_le_pow_of_le H) h.not_le,
end

-- Theorem 4
lemma nakada_lo.tfae {S : Type*} [has_mul S] [linear_order S] [nakada_po S] :
  tfae [∀ {a b c : S}, a * b ≤ a * c → b ≤ c,
        ∀ {a b c : S}, a * b = a * c → b = c,
        ∀ {a b : S} (h : a < b) (c : S), c * a < c * b] :=
begin
  tfae_have : 1 → 2,
  { intros H a b c h,
    haveI : nakada_strong S := ⟨λ _ _ _, H⟩,
    exact nakada_strong.cancel_left h },
  tfae_have : 2 → 3,
  { intros H a b h c,
    refine lt_of_le_of_ne (homogeneity h.le c) (λ he, _),
    simpa [H he] using h },
  tfae_have : 3 → 1,
  { intros H a b c,
    contrapose!,
    exact λ h, H h a },
  tfae_finish
end

-- Definition 3
@[ext]
structure add_order_embedding (S S' : Type*) [has_add S] [has_le S] [has_add S'] [has_le S'] extends
  add_hom S S' :=
(inj' : function.injective to_fun)
(map_rel_iff' : ∀ {a b : S}, (to_fun a) ≤ (to_fun b) ↔ a ≤ b)

@[ext, to_additive]
structure mul_order_embedding (S S' : Type*) [has_mul S] [has_le S] [has_mul S'] [has_le S'] extends
  mul_hom S S' :=
(inj' : function.injective to_fun)
(map_rel_iff' : ∀ {a b : S}, (to_fun a) ≤ (to_fun b) ↔ a ≤ b)

namespace mul_order_embedding

variables {M N : Type*} [has_mul M] [has_le M] [has_mul N] [has_le N]

infix ` ↪*o `:25 := mul_order_embedding
infix ` ↪+o `:25 := mul_order_embedding

@[to_additive]
instance : has_coe_to_fun (M ↪*o N) (λ _, M → N) := ⟨λ e, e.to_mul_hom⟩

@[to_additive]
def to_order_embedding (e : M ↪*o N) : M ↪o N := { ..e }

@[refl, to_additive]
def refl (M : Type*) [has_mul M] [has_le M] : M ↪*o M :=
{ map_mul' := λ _ _, rfl,
  ..rel_embedding.refl _ }

@[to_additive]
instance : inhabited (M ↪*o M) := ⟨refl M⟩

@[simp, to_additive]
lemma coe_to_mul_hom (e : M ↪*o N) : (e.to_mul_hom : M → N) = e := rfl

@[simp, to_additive]
lemma coe_to_order_embedding (e : M ↪*o N) : (e.to_order_embedding : M → N) = e := rfl

@[to_additive]
lemma injective (e : M ↪*o N) : function.injective e := e.to_order_embedding.injective

@[to_additive]
instance : mul_hom_class (M ↪*o N) M N :=
{ coe := λ e, e,
  coe_injective' := λ f g h, by { ext, exact congr_fun h _ },
  map_mul := λ e, e.map_mul' }

@[to_additive]
instance {M N : Type*} [has_mul M] [preorder M] [has_mul N] [preorder N] :
  order_hom_class (M ↪*o N) M N :=
{ coe := λ e, e,
  coe_injective' := λ f g h, by { ext x, exact congr_fun h x },
  map_rel := λ e a b, (@mul_order_embedding.map_rel_iff' _ _ _ _ _ _ _ _ _).mpr }

@[simp, to_additive]
lemma map_le_iff (e : M ↪*o N) {a b : M} :
  e a ≤ e b ↔ a ≤ b :=
@mul_order_embedding.map_rel_iff' _ _ _ _ _ _ _ _ _

@[simp, to_additive]
lemma map_lt_iff {M N : Type*} [has_mul M] [preorder M] [has_mul N] [preorder N]
  (e : M ↪*o N) {a b : M} : e a < e b ↔ a < b :=
by simp [lt_iff_le_not_le]

end mul_order_embedding

@[ext]
structure add_order_iso (S S' : Type*) [has_add S] [has_le S] [has_add S'] [has_le S'] extends
  S ≃+ S' :=
(map_rel_iff' : ∀ {a b : S}, (to_fun a) ≤ (to_fun b) ↔ a ≤ b)

@[ext, to_additive]
structure mul_order_iso (S S' : Type*) [has_mul S] [has_le S] [has_mul S'] [has_le S'] extends
  S ≃* S' :=
(map_rel_iff' : ∀ {a b : S}, (to_fun a) ≤ (to_fun b) ↔ a ≤ b)

namespace mul_order_iso

variables {M N : Type*} [has_mul M] [has_le M] [has_mul N] [has_le N]

infix ` ≃*o `:25 := mul_order_iso
infix ` ≃+o `:25 := add_order_iso

@[to_additive]
instance : has_coe_to_fun (M ≃*o N) (λ _, M → N) := ⟨λ e, e.to_mul_equiv⟩

@[to_additive]
def to_order_iso (e : M ≃*o N) : M ≃o N := { ..e }

@[refl, to_additive]
def refl (M : Type*) [has_mul M] [has_le M] : M ≃*o M :=
{ ..mul_equiv.refl _, ..order_iso.refl _ }

@[to_additive]
instance : inhabited (M ≃*o M) := ⟨refl M⟩

@[symm, to_additive]
def symm (e : M ≃*o N) : N ≃*o M :=
{ ..e.to_mul_equiv.symm, ..e.to_order_iso.symm }

@[simp, to_additive]
lemma inv_fun_eq_symm (e : M ≃*o N) : e.inv_fun = e.symm := rfl

@[simp, to_additive]
lemma coe_to_mul_equiv (e : M ≃*o N) : (e.to_mul_equiv : M → N) = e := rfl

@[simp, to_additive]
lemma symm_apply_apply (e : M ≃*o N) (x : M) : e.symm (e x) = x :=
e.to_mul_equiv.symm_apply_apply x

@[simp, to_additive]
lemma apply_symm_apply (e : M ≃*o N) (y : N) : e (e.symm y) = y :=
e.to_mul_equiv.apply_symm_apply y

@[to_additive]
lemma injective (e : M ≃*o N) : function.injective e := e.to_mul_equiv.injective

@[to_additive]
instance : mul_equiv_class (M ≃*o N) M N :=
{ coe := λ e, e, inv := λ e, e.symm,
  left_inv := λ e, e.to_mul_equiv.left_inv,
  right_inv := λ e, e.to_mul_equiv.right_inv,
  coe_injective' := λ f g h₁ h₂, by { ext x, exact congr_fun h₁ x },
  map_mul := λ e, e.map_mul' }

@[to_additive]
instance {M N : Type*} [has_mul M] [preorder M] [has_mul N] [preorder N] :
  order_hom_class (M ≃*o N) M N :=
{ coe := λ e, e,
  coe_injective' := λ f g h, by { ext x, exact congr_fun h x },
  map_rel := λ e a b, (@mul_order_iso.map_rel_iff' _ _ _ _ _ _ _ _ _).mpr }

@[to_additive]
instance mul_order_iso.order_hom_class_rev {M N : Type*} [has_mul M] [preorder M]
  [has_mul N] [preorder N] :
  order_hom_class (M ≃*o N) N M :=
{ coe := λ e, e.symm,
  coe_injective' := λ f g h, by { ext x, have := congr_fun h (g x),
    apply f.symm.to_mul_equiv.injective,
    simp_rw coe_to_mul_equiv at this ⊢,
    simp [this] },
  map_rel := λ e a b, (@mul_order_iso.map_rel_iff' _ _ _ _ _ _ _ _ _).mpr }

@[simp, to_additive]
lemma map_le_iff (e : M ≃*o N) {a b : M} :
  e a ≤ e b ↔ a ≤ b :=
@mul_order_iso.map_rel_iff' _ _ _ _ _ _ _ _ _

@[simp, to_additive]
lemma map_lt_iff {M N : Type*} [has_mul M] [preorder M] [has_mul N] [preorder N]
  (e : M ≃*o N) {a b : M} : e a < e b ↔ a < b :=
by simp [lt_iff_le_not_le]

-- how does `simps` work?
@[to_additive]
def to_mul_order_embedding (e : M ≃*o N) : M ↪*o N :=
{ inj' := equiv_like.injective e, ..e }

@[simp, to_additive]
lemma coe_to_order_iso (e : M ≃*o N) : (e.to_order_iso : M → N) = e := rfl

@[simp, to_additive]
lemma coe_to_mul_order_embedding (e : M ≃*o N) : (e.to_mul_order_embedding : M → N) = e := rfl

@[to_additive]
def of_mul_order_embedding (f : M ↪*o N) (g : N ↪*o M) (h : function.left_inverse f g) :
  M ≃*o N :=
{ to_fun := f,
  inv_fun := g,
  left_inv := λ x, f.to_order_embedding.injective (h (f x)),
  right_inv := h,
  map_mul' := map_mul _,
  map_rel_iff' := f.map_rel_iff' }

end mul_order_iso

-- Theorem 5 (by Theorem 1, we don't need to state that `G` is a group)
@[to_additive add_strong_of_add_order_embedding]
lemma strong_of_mul_order_embedding {S G : Type*} [comm_semigroup S] [has_le S]
  [comm_semigroup G] [has_le G] [nakada_po G] [nakada_strong G] (f : S ↪*o G) : nakada_strong S :=
⟨λ a b c h, begin
  rw ←f.map_rel_iff' at h ⊢,
  simpa using h
end⟩

end page182

section page183

variables {S : Type*} [comm_semigroup S] [partial_order S] [nakada_strong S]

variables (S)
-- we twist the multiplication to simplify refl and symm proofs
-- the definition is equivalent due to the commutativity assumption
@[to_additive]
def mul_pair_setoid : setoid (S × S) :=
{ r := λ p q, p.1 * q.2 = q.1 * p.2,
  iseqv := begin
    refine ⟨λ _, rfl, λ _ _, eq.symm, _⟩,
    intros p q r h h',
    have := congr_arg ((*) p.snd) h',
    rw [mul_left_comm, ←mul_assoc, ←h, mul_comm _ q.snd, mul_comm _ q.snd, ←mul_left_comm,
        mul_assoc] at this,
    rw [nakada_strong.cancel_left this, mul_comm],
  end }

variables {S}

local attribute [instance] mul_pair_setoid

@[simp, to_additive]
lemma mul_pair_equiv_iff (p q : S × S) : p ≈ q ↔ p.1 * q.2 = q.1 * p.2 := iff.rfl

@[to_additive]
lemma mul_pair_left_eq (p : S × S) (x : S) : ⟦(x * p.1, x * p.2)⟧ = ⟦p⟧ :=
by simp only [quotient.eq, mul_pair_equiv_iff, mul_assoc, mul_comm, mul_left_comm]

namespace pair_quotient

local notation `G` := quotient (mul_pair_setoid S)

@[to_additive]
protected def mul : G → G → G :=
quotient.map₂ (*) begin
  rintro ⟨a, a'⟩ ⟨c, c'⟩ hac ⟨b, b'⟩ ⟨d, d'⟩ hbd,
  simp only [mul_pair_equiv_iff, quotient.eq, prod.mk_mul_mk] at hac hbd ⊢,
  rw [mul_left_comm, ←mul_assoc, ←mul_assoc, mul_assoc, hbd, mul_comm c', hac],
  simp [mul_left_comm, mul_assoc, mul_comm]
end

@[to_additive]
instance : has_mul G := ⟨pair_quotient.mul⟩

-- thanks to Eric Wieser who says
-- "The elaborator can't infer the implicit arguments correctly for you
--  unless you unfold things in the right order for it, it seems"
@[simp, to_additive] lemma mk_mul : ∀ (p q : S × S), ⟦p⟧ * ⟦q⟧ = ⟦(p.1 * q.1, p.2 * q.2)⟧ :=
(quotient.map₂_mk _ _ : ∀ p q : S × S, pair_quotient.mul ⟦p⟧ ⟦q⟧ = _)

@[to_additive]
protected lemma mul_comm (x y : G) : x * y = y * x :=
quotient.induction_on₂ x y $ by { intros, simp [mul_comm, mul_assoc, mul_left_comm] }

@[to_additive]
protected lemma mul_assoc (x y z : G) : x * y * z = x * (y * z) :=
quotient.induction_on₃ x y z $ by { intros, simp [mul_comm, mul_assoc, mul_left_comm] }

@[to_additive]
instance comm_semigroup : comm_semigroup G :=
{ mul := (*),
  mul_assoc := pair_quotient.mul_assoc,
  mul_comm := pair_quotient.mul_comm }

@[to_additive]
protected def inv : G → G :=
quotient.map prod.swap $ λ _ _, by simp [mul_comm, eq_comm]

@[to_additive]
instance has_inv : has_inv G := ⟨pair_quotient.inv⟩

@[simp, to_additive] lemma inv_mk (p : S × S) : ⟦p⟧⁻¹ = ⟦p.swap⟧ := rfl

@[to_additive]
lemma mul_rev_inv_eq (x y : G) : x * x⁻¹ = y * y⁻¹ :=
quotient.induction_on₂ x y $ by { intros, simp [mul_comm] }

@[to_additive]
def one (x : S) : G := ⟦(x, x)⟧

@[to_additive]
lemma one_eq (x y : S) : one x = one y :=
by simp [one, mul_comm]

@[to_additive]
instance has_one [inhabited S] : has_one G := ⟨one (default : S)⟩

@[to_additive]
lemma one_def [inhabited S] : (1 : G) = one (default : S) := rfl

@[to_additive]
protected lemma inv_one [inhabited S] : (1 : G)⁻¹ = 1 :=
by simp [one_def, one]

@[to_additive]
instance subsingleton_mul [subsingleton S] : subsingleton G :=
⟨λ a b, quotient.induction_on₂ a b $ by simp⟩

@[to_additive]
instance nonempty_mul [h : nonempty S] : nonempty G :=
nonempty.map one h

@[to_additive]
instance [inhabited S] : comm_group G :=
{ mul := (*),
  one := 1,
  one_mul := λ a, quotient.induction_on a $ by simp [one_def, one, mul_comm, mul_left_comm],
  mul_one := λ a, quotient.induction_on a $ by simp [one_def, one, mul_comm, mul_left_comm],
  inv := pair_quotient.inv,
  mul_left_inv := λ a, begin
    induction a using quotient.induction_on,
    rw [mul_comm, mul_rev_inv_eq ⟦a⟧ 1, pair_quotient.inv_one],
    simp [one_def, one, mul_assoc]
  end,
  ..pair_quotient.comm_semigroup }

variables [nakada_po S]

@[to_additive]
protected def mul_le : G → G → Prop :=
quotient.lift₂ (λ (p q : S × S), p.1 * q.2 ≤ q.1 * p.2) begin
  rintro ⟨a, a'⟩ ⟨b, b'⟩ ⟨c, c'⟩ ⟨d, d'⟩ hac hbd,
  simp only [mul_pair_equiv_iff, eq_iff_iff] at hac hbd ⊢,
  split,
  work_on_goal 1 { rename [a x, a' x', b y, b' y', c a, c' a', d b, d' b'],
                   rename [x c, x' c', y d, y' d'],
                   rw eq_comm at hac hbd },
  all_goals { intro h,
    replace h : c' * (a * b') ≤ c' * (b * a') := homogeneity h c',
    rw [←mul_assoc, mul_comm c', hac, mul_comm b, mul_left_comm, mul_assoc, mul_left_comm] at h,
    replace h : d * (c * b') ≤ d * (c' * b) := homogeneity (strong h) d,
    rw [mul_left_comm, ←hbd, mul_left_comm, mul_comm _ b, mul_left_comm _ b] at h,
    exact strong h }
end

@[to_additive]
instance mul_has_le : has_le G := ⟨pair_quotient.mul_le⟩

@[simp, to_additive] lemma mul_le_def {p q : S × S} : ⟦p⟧ ≤ ⟦q⟧ ↔ p.1 * q.2 ≤ q.1 * p.2 := iff.rfl

@[to_additive]
instance mul_decidable_le [decidable_rel ((≤) : S → S → Prop)] :
  decidable_rel ((≤) : G → G → Prop) :=
λ a b, quotient.rec_on_subsingleton₂ a b (λ p q, decidable_of_iff' _ mul_le_def)

@[to_additive]
instance mul_partial_order : partial_order G :=
{ le := (≤),
  le_refl := λ a, quotient.induction_on a $ by simp,
  le_trans := λ a b c, quotient.induction_on₃ a b c $ begin
    rintro ⟨a, a'⟩ ⟨b, b'⟩ ⟨c, c'⟩ hab hbc,
    simp only [mul_le_def] at *,
    suffices : b' * (a * c') ≤ b' * (c * a'),
    { exact strong this },
    calc b' * (a * c') ≤ c' * (b * a') : by simpa [mul_comm, mul_left_comm] using homogeneity hab c'
    ... ≤ a' * (c * b') : by simpa [mul_comm, mul_left_comm] using homogeneity hbc a'
    ... ≤ b' * (c * a') : by simp only [mul_comm, mul_left_comm]
  end,
  le_antisymm := λ a b, begin
    induction a using quotient.induction_on,
    induction b using quotient.induction_on,
    simpa using le_antisymm
  end }

@[to_additive]
instance mul_nakada_po : nakada_po G :=
⟨λ a b c, quotient.induction_on₃ a b c begin
  rintro ⟨a, a'⟩ ⟨b, b'⟩ ⟨c, c'⟩ hbc,
  simp only [mk_mul, mul_le_def] at hbc,
  simpa only [mul_left_comm, mul_assoc, mk_mul, mul_le_def] using homogeneity (homogeneity hbc a) a'
end⟩

-- Theorem 5, corollary
@[to_additive]
instance mul_linear_order {S : Type*} [comm_semigroup S] [linear_order S]
  [nakada_po S] [nakada_strong S] : linear_order (quotient (mul_pair_setoid S)) :=
{ le_total := λ a b, quotient.induction_on₂ a b $ by
    { rintro ⟨a, a'⟩ ⟨b, b'⟩, simpa using le_total _ _ },
  decidable_le := pair_quotient.mul_decidable_le,
  ..pair_quotient.mul_partial_order }

end pair_quotient

-- Theorem 5, mpr
@[to_additive]
def to_mul_pair_quotient [nakada_po S] (x : S) : S ↪*o (quotient (mul_pair_setoid S)) :=
{ to_fun := λ a, ⟦(a * x, x)⟧,
  map_mul' := λ _ _, by simp [mul_comm, mul_left_comm],
  inj' := λ a b h, begin
    suffices : x * x * a = x * x * b,
    { exact nakada_strong.cancel_left this },
    simpa only [mul_comm, mul_left_comm, quotient.eq, mul_pair_equiv_iff] using h
  end,
  map_rel_iff' := λ _ _, by simp }

@[simp, to_additive] lemma to_mul_pair_quotient_apply [nakada_po S] (x a : S) :
  to_mul_pair_quotient x a = ⟦(a * x, x)⟧ := rfl

@[to_additive] lemma to_mul_pair_quotient_eq [nakada_po S] (x y : S) :
  to_mul_pair_quotient x = to_mul_pair_quotient y :=
by { ext, simp [mul_right_comm] }

-- If only we had subsemigroups
@[to_additive]
def of_mul_pair_quotient' [nakada_po S] [inhabited S] (x : S) :
  submonoid (quotient (mul_pair_setoid S)) :=
submonoid.closure (set.range (to_mul_pair_quotient x))

-- "Uniquely determined by S apart from its order-isomorphism"
@[to_additive]
lemma of_mul_pair_quotient'_eq [nakada_po S] [inhabited S] (x y : S) :
  of_mul_pair_quotient' x = of_mul_pair_quotient' y :=
by rw [of_mul_pair_quotient', of_mul_pair_quotient', to_mul_pair_quotient_eq]

-- Doesn't matter which element we choose by the previous lemma
@[to_additive]
def of_mul_pair_quotient [nakada_po S] [inhabited S] :
  submonoid (quotient (mul_pair_setoid S)) :=
submonoid.closure (set.range (to_mul_pair_quotient default))

-- how to prove minimality and uniqueness?

variables {M G M₀ : Type*} [comm_monoid M] [partial_order M] [nakada_po M] [comm_group G]
  [partial_order G] [nakada_po G] [comm_monoid_with_zero M₀] [partial_order M₀]

-- Theorem 6
@[to_additive]
lemma le_mul_left_iff :
  (∀ a b : M, a ≤ b * a) ↔ (∀ a : M, 1 ≤ a) :=
⟨λ h b, by simpa using h 1 b, λ h a b, by simpa [mul_comm] using homogeneity (h b) a⟩

lemma le_zero_of_forall_le_mul_left (h : ∀ a b : M₀, a ≤ b * a) (a : M₀) : a ≤ 0 :=
by simpa using h a 0

-- Theorem 6, corollary
@[to_additive]
lemma le_mul_left_iff_of_mul_order_embedding {S : Type*} [comm_semigroup S] [partial_order S]
  (f : S ↪*o G) :
  (∀ a b : S, a ≤ b * a) ↔ ∀ a : S, 1 ≤ f a :=
begin
  casesI is_empty_or_nonempty S with H H,
  { exact ⟨λ h a, H.elim a, λ h a, H.elim a⟩ },
  letI : inhabited S := classical.inhabited_of_nonempty H,
  split,
  { intros h a,
    have := h default a,
    rw ←f.map_rel_iff' at this,
    simpa using this },
  { intros h a b,
    have := homogeneity (h b) (f a),
    rwa [mul_one, ←map_mul, f.map_le_iff, mul_comm] at this }
end

-- Theorem 7
@[to_additive]
lemma exists_mul_of_lt_iff [nakada_po S] [nakada_strong S] [inhabited S]
  (f : S ↪*o quotient (mul_pair_setoid S)) (hf : f = to_mul_pair_quotient default) :
  (∀ a b : S, a < b → ∃ c : S, b = c * a) ↔
    ∀ a' : quotient (mul_pair_setoid S), 1 < a' → ∃ as : S, a' = f as :=
begin
  simp_rw [←f.map_lt_iff],
  split,
  { intros h x hx,
    induction H : x using quotient.induction_on with y,
    cases y with a b,
    have : x = f a * (f b)⁻¹,
    { simp [hf, H, mul_comm, mul_left_comm] },
    refine (h b a _).imp _,
    { rintro c rfl,
      simp [←H, this] },
    { rwa [←lt_mul_inv_iff_lt, ←this] } },
  { intros h a b hab,
    rw [←lt_mul_inv_iff_lt] at hab,
    refine (h _ hab).imp _,
    intros c hc,
    simp [←f.injective.eq_iff, ←hc] }
end

end page183
