/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.ordered_monoid_lemmas
import algebra.ordered_group
import data.real.nnreal
import algebra.ordered_ring

/-!  # Relations preserved by an action

We start with the following setup:

*  `M, U, V` are three Types,
*  `f : M → U → V` is a function,
*  `rᵤ` is a relation on `U`,
*  `rᵥ` is a relation on `V`.

We let `cov` be the assertion that if two elements `u₁, u₂` of `U` are related by `rᵤ`, then, for
all elements `m` of `M`, all pairs `f m u₁, f m u₂`, are related by `rᵥ`.

Similarly, we let `conv` be the assertion that if there are an element `m ∈ M` and two elements
`u₁, u₂` of `U` and such that `f m u₁` and `f m u₂` are related by `rᵤ`, then, the elements
`u₁` and `u₂` are related by `rᵥ`.

Intuitively, we can think of `M` as being a family of functions `U → V` that preserve the
respective relations.

Most of the times, we will assume that the relations are transitive.  The main applications that
we have in mind are the cases in which `rᵤ` and `rᵥ` are are partial orders or
equivalence relations.
-/

namespace new

variables {M N U V : Type*}
  (rᵤ : U → U → Prop) (rᵥ : V → V → Prop) (rₙ : N → N → Prop)
  (f : M → U → V)

/--  We let `cov` be the assertion that if two elements `u₁, u₂` of `U` are related by `rᵤ`, then,
for all elements `m` of `M`, all pairs `f m u₁, f m u₂`, are related by `rᵥ`. -/
def cov : Prop := ∀ (m) {u₁ u₂}, rᵤ u₁ u₂ → rᵥ (f m u₁) (f m u₂)

@[simp]
lemma cov_def : cov rᵤ rᵥ f ↔ ∀ (m) {u₁ u₂}, rᵤ u₁ u₂ → rᵥ (f m u₁) (f m u₂) := iff.rfl

lemma covariant_iff_cov (μ : M → N → N) : covariant M N μ rₙ ↔ cov rₙ rₙ μ :=
⟨λ h n₁ n₂ m s12, h _ s12, λ h m n₁ n₂ s12, h _ s12⟩

/--  We let `conv` be the assertion that if there are an element `m ∈ M` and two elements
`u₁, u₂` of `U` and such that `f m u₁` and `f m u₂` are related by `rᵤ`, then, the elements
`u₁` and `u₂` are related by `rᵥ`. -/
def conv : Prop := ∀ (m) {u₁ u₂}, rᵥ (f m u₁) (f m u₂) → rᵤ u₁ u₂

@[simp]
lemma conv_def : conv rᵤ rᵥ f ↔ ∀ (m) {u₁ u₂}, rᵥ (f m u₁) (f m u₂) → rᵤ u₁ u₂ := iff.rfl

lemma contravariant_iff_cov (μ : M → N → N) : contravariant M N μ rₙ ↔ conv rₙ rₙ μ :=
⟨λ h n₁ n₂ m s12, h _ s12, λ h m n₁ n₂ s12, h _ s12⟩


/--  We make `cov` into a Typeclass. -/
class cov_class :=
( var    : cov rᵤ rᵥ f )

instance cov_class.to_covariant_class (μ : M → N → N) [covariant_class M N μ rₙ] :
  cov_class rₙ rₙ μ :=
{ var := λ m a b ab, covariant_class.covc _ ab }


/--  We make `conv` into a Typeclass. -/
class conv_class :=
( convar : conv rᵤ rᵥ f )

instance conv_class.to_contravariant_class (μ : M → N → N) [contravariant_class M N μ rₙ] :
  conv_class rₙ rₙ μ :=
{ convar := λ m a b ab, contravariant_class.covtc _ ab }

variables {rᵤ rᵥ f}
section cov_class
variables [cov_class rᵤ rᵥ f]

lemma act_rel_act_of_rel (m : M) {a b : U} (ab : rᵤ a b) :
  rᵥ (f m a) (f m b) :=
cov_class.var _ ab



/- silly instances
instance preorder.conv_class_le_to_lt [preorder U] [is_refl V rᵥ] [is_antisymm U (≤)]
  [cov_class (<) rᵥ f] :
  cov_class (≤) rᵥ f :=
{ var := λ m a b aleb, by { by_cases ab : a = b,
  { rw ab,
    exact refl (f m b) },
  { refine cov_class.var m (lt_iff_le_not_le.mpr ⟨aleb, λ h, ab (antisymm aleb h)⟩) } } }

instance preorder.conv_class_le_to_lt [preorder U]
  [cov_class (≤) rᵥ f] :
  cov_class (<) rᵥ f :=
{ var := λ m a b ab, act_rel_act_of_rel _ ab.le }

instance partial_order_is_refl.conv_class_lt_to_le [partial_order U] [is_refl V rᵥ]
  [cov_class (<) rᵥ f] :
  cov_class (≤) rᵥ f :=
{ var := λ m a b ab, by { rcases le_iff_eq_or_lt.mp ab with rfl | h,
    { exact refl (f m a) },
    { exact act_rel_act_of_rel _ h } } }
-/

instance partial_order.cov_class.to_conv_class [linear_order U] [linear_order V]
  [cov_class (≤) (≤) f] :
  conv_class (<) (<) f :=
{ convar := λ m a b ab, not_le.mp (λ h, not_le.mpr ab (act_rel_act_of_rel _ h)) }

section is_trans
variables [is_trans V rᵥ] (m : M) {a b : U} {x y : V}

lemma act_rel_of_rel_act_rel (ab : rᵤ a b) (rl : rᵥ (f m b) x) :
  rᵥ (f m a) x :=
trans (act_rel_act_of_rel m ab) rl

lemma rel_act_of_rel_act_rel (ab : rᵤ a b) (rr : rᵥ x (f m a)) :
  rᵥ x (f m b) :=
trans rr (act_rel_act_of_rel _ ab)

end is_trans

section preorder
variables [preorder U] [preorder V]

section cov_class_le
variables [cov_class (≤) (≤) f]

lemma lt_act_of_lt_act_of_le (m : M) {a : V} (b : U) {c : U} (h : a < f m b) (hle : b ≤ c) :
  a < f m c :=
h.trans_le (act_rel_act_of_rel m hle)

lemma act_lt_of_act_lt_of_le (m : M) {a : U} (b : U) {c : V} (h : f m b < c) (hle : a ≤ b) :
  f m a < c :=
(act_rel_act_of_rel m hle : f m a ≤ f m b).trans_lt h

end cov_class_le

section cov_class_lt
variables [cov_class (<) (<) f]

lemma lt_act_of_le_act_of_lt (m : M) {a : V} (b : U) {c : U} (h : a ≤ f m b) (hle : b < c) :
  a < f m c :=
h.trans_lt (act_rel_act_of_rel m hle)

lemma act_lt_of_act_le_of_lt (m) {a} (b) {c} (h : f m b ≤ c) (hle : a < b) :
  f m a < c :=
(act_rel_act_of_rel m hle : f m a < f m b).trans_le h

end cov_class_lt

end preorder

section U_eq_V
variables {sc : M → U → U} [cov_class rᵤ rᵤ sc]

/- This lemma is useful for actions by invertible elements. -/
lemma ind_precise (m n) {a b} (mna : sc n (sc m a) = a) (mnb : sc n (sc m b) = b) :
  rᵤ (sc m a) (sc m b) ↔ rᵤ a b:=
begin
  refine ⟨λ h, _, λ h, act_rel_act_of_rel m h⟩,
  rw [← mna, ← mnb],
  exact act_rel_act_of_rel n h,
end

/- This lemma is useful for actions by invertible elements. -/
lemma ind (m n) {a b} (mn : sc n ∘ (sc m) = id) : rᵤ (sc m a) (sc m b) ↔ rᵤ a b:=
iff.rfl.trans (ind_precise m n (congr_fun mn _) (congr_fun mn _))
/-
begin
  refine ⟨λ h, _, λ h, act_rel_act_of_rel m h⟩,
  convert @act_rel_act_of_rel _ _ _ rᵤ rᵤ sc _ n _ _ h;
  exact congr_fun mn.symm _,
end
-/

/- This lemma is useful for actions by invertible elements. -/
lemma ind_1 (m n) {a b} (mn : ∀ (u : U), sc n (sc m u) = u) : rᵤ (sc m a) (sc m b) ↔ rᵤ a b:=
--⟨λ h, by {rw [← mn a, ← mn b], exact act_rel_act_of_rel n h}, λ h, act_rel_act_of_rel m h⟩,
--ind m n (funext (λ x, mn x))
ind_precise m n (mn a) (mn b)

--lemma with_identity_precise (one : M) (a b c : U) (ma : sc one a = c) (h : rᵤ c b) : rᵤ a (sc a b) :=
--by { nth_rewrite 0 [← ma], exact act_rel_act_of_rel a h }

end U_eq_V

section M_eq_U_eq_V
variable {mu : U → U → U}

section cov_class
variable [cov_class rᵤ rᵤ mu]

lemma with_identity_precise_1 (one a b : U) (ma : mu a one = a) (h : rᵤ one b) : rᵤ a (mu a b) :=
by { nth_rewrite 0 [← ma], exact act_rel_act_of_rel a h }

lemma with_identity_1 (one a b : U) (ide : flip mu one = id) (h : rᵤ one b) : rᵤ a (mu a b) :=
with_identity_precise_1 one a b (congr_fun ide a : _) h

end cov_class

section cov_class_flip
variable [cov_class rᵤ rᵤ (flip mu)]

lemma with_identity_precise_flip (one a b : U) (ma : mu one a = a) (h : rᵤ one b) : rᵤ a (mu b a) :=
@with_identity_precise_1 U rᵤ (flip mu) _ one a b ma h

lemma with_identity_flip (one a b : U) (ide : mu one = id) (h : rᵤ one b) : rᵤ a (mu b a) :=
@with_identity_precise_1 U rᵤ (flip mu) _ one a b (congr_fun ide a : _) h

end cov_class_flip

namespace reprove

variables {P R : Type*} (i : P → R)

class is_inj_pos {P R : Type*} [has_zero R] [has_lt R] (i : P → R) : Prop :=
( inj_pos : function.injective i ∧ ∀ p : P, 0 < i p )

def pos (R : Type*) [has_zero R] [has_lt R] := { r : R // 0 < r }

instance (R : Type*) [has_zero R] [has_lt R] : has_lift_t (pos R) R :=
{ lift := λ p, p.1 }

instance (R : Type*) [has_zero R] [has_lt R] : is_inj_pos (coe : pos R → R) :=
{ inj_pos := and.intro subtype.coe_injective (λ p, p.2) }

section left
instance sca_left [has_zero R] [has_mul R] [has_lt R] [is_inj_pos i] : has_scalar P R :=
{ smul := λ p r, (i p) * r }

section prova
variables [has_zero R] [has_mul R] [has_lt R] [is_inj_pos i] {p : P} {r : R}
#check p • r
end prova

instance pro_left [ordered_semiring R] (h : is_inj_pos i) :
  cov_class (<) (<) ((•) : P → R → R) :=
{ var := λ p a b ab, ordered_semiring.mul_lt_mul_of_pos_left _ _ _ ab (h.2 _) }

lemma mul_le_mul_of_nonneg_left [mul_zero_class R] [preorder R]
  [cov_class (<) (<) ((reprove.sca_left i).smul : P → R → R)] {a b : R} {c : P} :
  a ≤ b → c • a ≤ c • b :=
by classical; exact decidable.mul_le_mul_of_nonneg_left

end left

section right

instance sca_right [has_mul R] : has_scalar P R :=
{ smul := λ p r, flip (*) (i p) r }

instance pro_right [ordered_semiring R] (h : is_inj_pos i) :
  cov_class (<) (<) ((reprove.sca_right i).smul : P → R → R) :=
{ var := λ p a b ab, ordered_semiring.mul_lt_mul_of_pos_right _ _ _ ab (h.2 _) }


end right

section has_mul
variables [has_mul N] [preorder N]

section cov
variables [cov_class (≤) (≤) ((*) : N → N → N)] {a b c d : N} (b)
-- [covariant_class α α (*) (≤)]

@[to_additive]
lemma mul_lt_of_mul_lt_left (h : a * b < c) (hle : d ≤ b) :
  a * d < c :=
act_lt_of_act_lt_of_le a b h hle

@[to_additive]
lemma mul_le_of_mul_le_left (h : a * b ≤ c) (hle : d ≤ b) :
  a * d ≤ c :=
act_rel_of_rel_act_rel a hle h

@[to_additive]
lemma lt_mul_of_lt_mul_left (h : a < b * c) (hle : c ≤ d) :
  a < b * d :=
lt_act_of_lt_act_of_le b c h hle

@[to_additive]
lemma le_mul_of_le_mul_left (h : a ≤ b * c) (hle : c ≤ d) :
  a ≤ b * d :=
rel_act_of_rel_act_rel _ hle h

end cov

section conv

variables [cov_class (≤) (≤) (flip (*) : N → N → N)] {a b c d : N} (a)
-- [covariant_class α α (function.swap (*)) (≤)]

lemma mul_lt_of_mul_lt_right (h : flip (*) a b < c) (hle : d ≤ b) :
  flip (*) a d < c :=
act_lt_of_act_lt_of_le a b h hle


@[to_additive]
lemma mul_lt_of_mul_lt_right (h : a * b < c) (hle : d ≤ a) :
  d * b < c :=
(act_lt_of_act_lt_of_le b a h hle : flip (*) b d < c)

@[to_additive]
lemma mul_le_of_mul_le_right (h : a * b ≤ c) (hle : d ≤ a) :
  d * b ≤ c :=
(act_rel_of_rel_act_rel _ hle h : flip (*) b d ≤ c)

@[to_additive]
lemma lt_mul_of_lt_mul_right (h : a < b * c) (hle : b ≤ d) :
  a < d * c :=
(lt_act_of_lt_act_of_le _ _ h hle : a < flip (*) _ _)

@[to_additive]
lemma le_mul_of_le_mul_right (h : a ≤ b * c) (hle : b ≤ d) :
  a ≤ d * c :=
(rel_act_of_rel_act_rel _ hle h : a ≤ flip (*) _ _)

#exit
end has_mul

end conv

end has_mul


#exit
lemma ind (m n) (mn : f m (f m a) = a)

lemma act_lt_of_act_lt_of_le (h : rᵥ (f m a) x) (hle : rᵤ b a) :
  rᵥ (f m b) x :=
(act_rel_act_of_rel m hle).trans_lt h

lemma lt_act_of_lt_act_of_le (h : a < μ m b) (hle : b ≤ c) :
  a < μ m c :=
h.trans_le (act_rel_act_of_rel m hle)


end cov_class

section conv_class
variables [conv_class rᵤ rᵥ f] (m : M) {a b : U}

lemma rel_of_act_rel_act (ab : rᵥ (f m a) (f m b)) :
  rᵤ a b :=
conv_class.convar _ ab

end conv_class

#exit
/--  `covariant_class` with a reflexive relation `s` is a special case of a `is_rel_tower` on
`(M, =)`, `(N, s)` and `(N, s)`. -/
def infi (μ : M → N → N) [covariant_class M N μ s] : cov_class s s (flip μ) :=
{ var := λ a b c ab, covariant_class.covc _ ab }










#check @is_inj_nonneg
section variants
universes u v

variables {M : Type u} {N : Type v} (μ : M → N → N) (r : N → N → Prop) (m : M) {a b c : N}


variables (M N)

variables {M N} {μ r}
section has_mul

lemma act_rel_act_of_rel [covariant_class M N μ r] (ab : r a b) :
  r (μ m a) (μ m b) :=
covariant_class.covc _ ab

lemma rel_of_act_rel_act [contravariant_class M N μ r]
  (ab : r (μ m a) (μ m b)) :
  r a b :=
contravariant_class.covtc _ ab

section left

section has_mul

variables [preorder N] [covariant_class M N μ (≤)]

lemma act_le_of_act_le_of_le (h : μ m a ≤ b) (hle : c ≤ a) :
  μ m c ≤ b :=
(act_rel_act_of_rel m hle).trans h

lemma le_act_of_le_act_left (h : a ≤ μ m b) (hle : b ≤ c) :
  a ≤ μ m c :=
h.trans (act_rel_act_of_rel m hle)

lemma act_lt_of_act_lt_of_le (h : (μ m a) < b) (hle : c ≤ a) :
  μ m c < b :=
(act_rel_act_of_rel m hle).trans_lt h

lemma lt_act_of_lt_act_of_le (h : a < μ m b) (hle : b ≤ c) :
  a < μ m c :=
h.trans_le (act_rel_act_of_rel m hle)

end has_mul

variables [has_mul N] [preorder N] [covariant_class N N (flip (*)) (≤)]

@[to_additive ppp]
lemma mul_lt_of_mul_lt_left {N : Type*} {b c} [has_mul N] [preorder N] [covariant_class N N (*) (≤)]
  (a) {d : N} (h : b * a < c) (hle : d ≤ a) :
  b * d < c :=
@act_lt_of_act_lt_of_le _ _ (*) _ _ _ _ _ _ h hle
--show (*) b d < c, from act_lt_of_act_lt_of_le b h hle

@[to_additive ppp]
lemma mul_lt_of_mul_lt_right (a) {d : N} (h : a * b < c) (hle : d ≤ a) :
  d * b < c :=
@act_lt_of_act_lt_of_le _ _ (flip (*)) _ _ _ _ _ _ h hle
--show flip (*) b d < c, from act_lt_of_act_lt_of_le b h hle
#check @mul_lt_of_mul_lt_right

/-
variables [preorder N] [has_mul N] [preorder M] (mm : ∀ a : N, monotone (λ x, μ x a))
  [covariant_class M N μ (≤)] {n : M}

include mm
@[to_additive add_le_add]
lemma mul_le_mul' (h₁ : m ≤ n) (h₂ : a ≤ b) : μ m a ≤ μ n b :=
(mm a h₁).trans (act_rel_act_of_rel n h₂)
#lint
--@[to_additive]
--lemma mul_le_mul_three {e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) : a * b * c ≤ d * e * f :=
--mul_le_mul' (mul_le_mul' h₁ h₂) h₃
-/

end left

end has_mul

end variants

variables {M N O : Type*} (r : M → M → Prop) (s : N → N → Prop) (t : O → O → Prop) (f : M → N → O)

variable [is_trans O t]

variables {m₁ m₂ : M} {n₁ n₂ : N} {r s t f}

lemma rel_triple (h₁ : r m₁ m₂) (h₂ : s n₁ n₂) : t (f m₁ n₁) (f m₂ n₂) :=
have one : t (f m₁ n₁) (f m₂ n₁) := is_rel_tower.rl s n₁ h₁,
have two : t (f m₂ n₁) (f m₂ n₂) := is_rel_tower.rr r m₂ h₂,
trans one two



lemma pers {α β : Type*} [has_le α] [preorder β] [has_scalar α β]
  [is_rel_tower (≤) (≤) (≤) ((•) : α → β → β)]
  (a1 a2 : α) (b1 b2 : β) (a12 : a1 ≤ a2) (b12 : b1 ≤ b2) :
  a1 • b1 ≤ a2 • b2 :=
rel_triple a12 b12

end
--covariant_class.covc _ ab

lemma rel_of_act_rel_act [contravariant_class M N μ r]
  (ab : r (μ m a) (μ m b)) :
  r a b :=
contravariant_class.covtc _ ab



#lint
--(mm a h₁).trans (act_rel_act_of_rel n h₂)


end new


#exit

-- here we start using properties of one.
section mul_one_class
variables [mul_one_class N] [covariant_class M N μ r]

@[to_additive le_add_of_nonneg_right]
lemma le_mul_of_one_le_right' (h : 1 ≤ b) : a ≤ a * b :=
#exit
by simpa only [mul_one] using mul_le_mul_left_n a h

@[to_additive add_le_of_nonpos_right]
lemma mul_le_of_le_one_right' (h : b ≤ 1) : a * b ≤ a :=
by simpa only [mul_one] using mul_le_mul_left_n a h

@[to_additive]
lemma lt_of_mul_lt_of_one_le_left (h : a * b < c) (hle : 1 ≤ b) : a < c :=
(le_mul_of_one_le_right' hle).trans_lt h

@[to_additive]
lemma le_of_mul_le_of_one_le_left (h : a * b ≤ c) (hle : 1 ≤ b) : a ≤ c :=
(le_mul_of_one_le_right' hle).trans h

@[to_additive]
lemma lt_of_lt_mul_of_le_one_left (h : a < b * c) (hle : c ≤ 1) : a < b :=
h.trans_le (mul_le_of_le_one_right' hle)

@[to_additive]
lemma le_of_le_mul_of_le_one_left (h : a ≤ b * c) (hle : c ≤ 1) : a ≤ b :=
h.trans (mul_le_of_le_one_right' hle)

end mul_one_class

end left

section right

section preorder
variables [preorder α]

-- here we start using properties of one.
section mul_one_class
variables [mul_one_class α] [covariant_class α α (function.swap (*)) (≤)]

@[to_additive le_add_of_nonneg_left]
lemma le_mul_of_one_le_left' (h : 1 ≤ b) : a ≤ b * a :=
by simpa only [one_mul] using mul_le_mul_right_n a h

@[to_additive add_le_of_nonpos_left]
lemma mul_le_of_le_one_left' (h : b ≤ 1) : b * a ≤ a :=
by simpa only [one_mul] using mul_le_mul_right_n a h

@[to_additive]
lemma lt_of_mul_lt_of_one_le_right (h : a * b < c) (hle : 1 ≤ a) : b < c :=
(le_mul_of_one_le_left' hle).trans_lt h

@[to_additive]
lemma le_of_mul_le_of_one_le_right (h : a * b ≤ c) (hle : 1 ≤ a) : b ≤ c :=
(le_mul_of_one_le_left' hle).trans h

@[to_additive]
lemma lt_of_lt_mul_of_le_one_right (h : a < b * c) (hle : b ≤ 1) : a < c :=
h.trans_le (mul_le_of_le_one_left' hle)

@[to_additive]
lemma le_of_le_mul_of_le_one_right (h : a ≤ b * c) (hle : b ≤ 1) : a ≤ c :=
h.trans (mul_le_of_le_one_left' hle)

end mul_one_class

end preorder

end right

section preorder
variables [preorder α]

section has_mul_left_right
variables [has_mul α]
  [covariant_class α α ((*)) (≤)] [covariant_class α α (function.swap (*)) (≤)]

@[to_additive add_le_add]
lemma mul_le_mul' (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
(mul_le_mul_left_n _ h₂).trans (mul_le_mul_right_n d h₁)

@[to_additive]
lemma mul_le_mul_three {e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) : a * b * c ≤ d * e * f :=
mul_le_mul' (mul_le_mul' h₁ h₂) h₃

end has_mul_left_right

-- here we start using properties of one.
section mul_one_class_left_right
variables [mul_one_class α]

section covariant
variable  [covariant_class α α (*) (≤)]

@[to_additive add_pos_of_pos_of_nonneg]
lemma one_lt_mul_of_lt_of_le' (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
lt_of_lt_of_le ha $ le_mul_of_one_le_right' hb

@[to_additive add_pos]
lemma one_lt_mul' (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
one_lt_mul_of_lt_of_le' ha hb.le

@[to_additive]
lemma lt_mul_of_lt_of_one_le' (hbc : b < c) (ha : 1 ≤ a) :
  b < c * a :=
hbc.trans_le $ le_mul_of_one_le_right' ha

@[to_additive]
lemma lt_mul_of_lt_of_one_lt' (hbc : b < c) (ha : 1 < a) :
  b < c * a :=
lt_mul_of_lt_of_one_le' hbc ha.le

end covariant

section contravariant
variable [covariant_class α α (function.swap (*)) (≤)]

@[to_additive add_pos_of_nonneg_of_pos]
lemma one_lt_mul_of_le_of_lt' (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
lt_of_lt_of_le hb $ le_mul_of_one_le_left' ha

@[to_additive]
lemma lt_mul_of_one_le_of_lt' (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
hbc.trans_le $ le_mul_of_one_le_left' ha

@[to_additive]
lemma lt_mul_of_one_lt_of_lt' (ha : 1 < a) (hbc : b < c) : b < a * c :=
lt_mul_of_one_le_of_lt' ha.le hbc

end contravariant

variables [covariant_class α α (*) (≤)]
  [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma le_mul_of_one_le_of_le (ha : 1 ≤ a) (hbc : b ≤ c) : b ≤ a * c :=
one_mul b ▸ mul_le_mul' ha hbc

@[to_additive]
lemma le_mul_of_le_of_one_le (hbc : b ≤ c) (ha : 1 ≤ a) : b ≤ c * a :=
mul_one b ▸ mul_le_mul' hbc ha

@[to_additive add_nonneg]
lemma one_le_mul (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
le_mul_of_one_le_of_le ha hb

@[to_additive add_nonpos]
lemma mul_le_one' (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
one_mul (1:α) ▸ (mul_le_mul' ha hb)

@[to_additive]
lemma mul_le_of_le_one_of_le' (ha : a ≤ 1) (hbc : b ≤ c) : a * b ≤ c :=
one_mul c ▸ mul_le_mul' ha hbc

@[to_additive]
lemma mul_le_of_le_of_le_one' (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
mul_one c ▸ mul_le_mul' hbc ha

@[to_additive]
lemma mul_lt_one_of_lt_one_of_le_one' (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
(mul_le_of_le_of_le_one' le_rfl hb).trans_lt ha

@[to_additive]
lemma mul_lt_one_of_le_one_of_lt_one' (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
(mul_le_of_le_one_of_le' ha le_rfl).trans_lt hb

@[to_additive]
lemma mul_lt_one' (ha : a < 1) (hb : b < 1) : a * b < 1 :=
mul_lt_one_of_le_one_of_lt_one' ha.le hb

@[to_additive]
lemma mul_lt_of_le_one_of_lt' (ha : a ≤ 1) (hbc : b < c) : a * b < c :=
lt_of_le_of_lt (mul_le_of_le_one_of_le' ha le_rfl) hbc

@[to_additive]
lemma mul_lt_of_lt_of_le_one' (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
lt_of_le_of_lt (mul_le_of_le_of_le_one' le_rfl ha) hbc

@[to_additive]
lemma mul_lt_of_lt_one_of_lt' (ha : a < 1) (hbc : b < c) : a * b < c :=
mul_lt_of_le_one_of_lt' ha.le hbc

@[to_additive]
lemma mul_lt_of_lt_of_lt_one' (hbc : b < c) (ha : a < 1) : b * a < c :=
mul_lt_of_lt_of_le_one' hbc ha.le

end mul_one_class_left_right

end preorder

section partial_order
variables [mul_one_class α] [partial_order α]
  [covariant_class α α (*) (≤)] [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma mul_eq_one_iff' (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
iff.intro
  (assume hab : a * b = 1,
   have a ≤ 1, from hab ▸ le_mul_of_le_of_one_le le_rfl hb,
   have a = 1, from le_antisymm this ha,
   have b ≤ 1, from hab ▸ le_mul_of_one_le_of_le ha le_rfl,
   have b = 1, from le_antisymm this hb,
   and.intro ‹a = 1› ‹b = 1›)
  (assume ⟨ha', hb'⟩, by rw [ha', hb', mul_one])

section mono
variables {β : Type*} [preorder β] {f g : β → α}

@[to_additive monotone.add]
lemma monotone.mul' (hf : monotone f) (hg : monotone g) : monotone (λ x, f x * g x) :=
λ x y h, mul_le_mul' (hf h) (hg h)

@[to_additive monotone.add_const]
lemma monotone.mul_const' (hf : monotone f) (a : α) : monotone (λ x, f x * a) :=
hf.mul' monotone_const

@[to_additive monotone.const_add]
lemma monotone.const_mul' (hf : monotone f) (a : α) : monotone (λ x, a * f x) :=
monotone_const.mul' hf

end mono

end partial_order

@[to_additive le_of_add_le_add_left]
lemma le_of_mul_le_mul_left' [left_cancel_semigroup α] [partial_order α]
  [contravariant_class α α (*) (<)]
  {a b c : α} (bc : a * b ≤ a * c) :
  b ≤ c :=
begin
  cases le_iff_eq_or_lt.mp bc,
  { exact le_iff_eq_or_lt.mpr (or.inl ((mul_right_inj a).mp h)) },
  { exact (lt_of_mul_lt_mul_left' h).le }
end

@[to_additive le_of_add_le_add_right]
lemma le_of_mul_le_mul_right' [partial_order α] [right_cancel_semigroup α]
  [contravariant_class α α (function.swap (*)) (<)]
  {a b c : α} (bc : b * a ≤ c * a) :
  b ≤ c :=
begin
  cases le_iff_eq_or_lt.mp bc,
  { exact le_iff_eq_or_lt.mpr (or.inl ((mul_left_inj a).mp h)) },
  { exact (lt_of_mul_lt_mul_right_n _ h).le }
end

variable [partial_order α]

section left_co_co
variables [left_cancel_monoid α] [covariant_class α α (*) (≤)]

@[to_additive lt_add_of_pos_right]
lemma lt_mul_of_one_lt_right' (a : α) {b : α} (h : 1 < b) : a < a * b :=
have a * 1 < a * b, from mul_lt_mul_left' h a,
by rwa [mul_one] at this

variable  [contravariant_class α α (*) (<)]

/-
lemma add_le_add_iff_left {α : Type*} [add_left_cancel_monoid α] [partial_order α]
   [covariant_class α α (+) (≤)] [contravariant_class α α (+) (<)]
 (a : α) {b c : α} : a + b ≤ a + c ↔ b ≤ c :=
⟨λ h, le_of_add_le_add_left a h, λ h, add_le_add_left a h⟩
--/


@[simp, to_additive]
lemma mul_le_mul_iff_left (a : α) {b c : α} : a * b ≤ a * c ↔ b ≤ c :=
⟨λ h, le_of_mul_le_mul_left_n _ h, λ h, mul_le_mul_left_n a h⟩

@[simp, to_additive]
lemma mul_lt_mul_iff_left (a : α) {b c : α} : a * b < a * c ↔ b < c :=
⟨lt_of_mul_lt_mul_left_n a, λ h, mul_lt_mul_left' h a⟩

@[simp, to_additive le_add_iff_nonneg_right]
lemma le_mul_iff_one_le_right' (a : α) {b : α} : a ≤ a * b ↔ 1 ≤ b :=
have a * 1 ≤ a * b ↔ 1 ≤ b, from mul_le_mul_iff_left a,
by rwa mul_one at this

@[simp, to_additive lt_add_iff_pos_right]
lemma lt_mul_iff_one_lt_right' (a : α) {b : α} : a < a * b ↔ 1 < b :=
have a * 1 < a * b ↔ 1 < b, from mul_lt_mul_iff_left a,
by rwa mul_one at this

@[simp, to_additive add_le_iff_nonpos_right]
lemma mul_le_iff_le_one_right' : a * b ≤ a ↔ b ≤ 1 :=
by { convert mul_le_mul_iff_left a, rw [mul_one] }

@[simp, to_additive add_lt_iff_neg_left]
lemma mul_lt_iff_lt_one_left' : a * b < a ↔ b < 1 :=
by { convert mul_lt_mul_iff_left a, rw [mul_one] }

end left_co_co

section right_cos_cos

variables [right_cancel_monoid α]
  [covariant_class α α (function.swap (*)) (≤)]
  [contravariant_class α α (function.swap (*)) (<)]

@[to_additive]
lemma mul_lt_mul_of_right (h : a < b) (c : α) : a * c < b * c :=
(mul_le_mul_right' h.le _).lt_of_not_le
  (λ j, not_le_of_gt h (le_of_mul_le_mul_right' j))

@[to_additive lt_add_of_pos_left]
lemma lt_mul_of_one_lt_left' (a : α) {b : α} (h : 1 < b) : a < b * a :=
have 1 * a < b * a, from mul_lt_mul_of_right h a,
by rwa [one_mul] at this

@[simp, to_additive]
lemma mul_le_mul_iff_right (c : α) : a * c ≤ b * c ↔ a ≤ b :=
⟨le_of_mul_le_mul_right_n _, λ h, mul_le_mul_right_n _ h⟩

@[simp, to_additive]
lemma mul_lt_mul_iff_right (c : α) : a * c < b * c ↔ a < b :=
⟨lt_of_mul_lt_mul_right_n _, λ h, mul_lt_mul_of_right h c⟩

@[simp, to_additive le_add_iff_nonneg_left]
lemma le_mul_iff_one_le_left' (a : α) {b : α} : a ≤ b * a ↔ 1 ≤ b :=
have 1 * a ≤ b * a ↔ 1 ≤ b, from mul_le_mul_iff_right a,
by rwa one_mul at this

@[simp, to_additive lt_add_iff_pos_left]
lemma lt_mul_iff_one_lt_left' (a : α) {b : α} : a < b * a ↔ 1 < b :=
have 1 * a < b * a ↔ 1 < b, from mul_lt_mul_iff_right a,
by rwa one_mul at this

@[simp, to_additive add_le_iff_nonpos_left]
lemma mul_le_iff_le_one_left' : a * b ≤ b ↔ a ≤ 1 :=
by { convert mul_le_mul_iff_right b, rw [one_mul] }

@[simp, to_additive add_lt_iff_neg_right]
lemma mul_lt_iff_lt_one_right' : a * b < b ↔ a < 1 :=
by { convert mul_lt_mul_iff_right b, rw [one_mul] }

end right_cos_cos

section right_co_cos

variables [right_cancel_monoid α]
  [covariant_class α α (*) (≤)]
  [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma mul_lt_mul_of_lt_of_le (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
lt_of_lt_of_le ((mul_le_mul_right_n c h₁.le).lt_of_ne (λ h, h₁.ne ((mul_left_inj c).mp h)))
  (mul_le_mul_left_n b h₂)

@[to_additive]
lemma mul_lt_one_of_lt_one_of_le_one (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul_of_lt_of_le ha hb)

@[to_additive]
lemma lt_mul_of_one_lt_of_le (ha : 1 < a) (hbc : b ≤ c) : b < a * c :=
one_mul b ▸ mul_lt_mul_of_lt_of_le ha hbc

@[to_additive]
lemma mul_le_of_le_one_of_le (ha : a ≤ 1) (hbc : b ≤ c) : a * b ≤ c :=
one_mul c ▸ mul_le_mul' ha hbc

@[to_additive]
lemma mul_le_of_le_of_le_one (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
mul_one c ▸ mul_le_mul' hbc ha

@[to_additive]
lemma mul_lt_of_lt_one_of_le (ha : a < 1) (hbc : b ≤ c) : a * b < c :=
one_mul c ▸ mul_lt_mul_of_lt_of_le ha hbc

@[to_additive]
lemma lt_mul_of_lt_of_one_le (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
mul_one b ▸ mul_lt_mul_of_lt_of_le hbc ha

@[to_additive]
lemma mul_lt_of_lt_of_le_one (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
mul_one c ▸ mul_lt_mul_of_lt_of_le hbc ha

end right_co_cos

variables [cancel_monoid α]
  [covariant_class α α (*) (≤)]
  [covariant_class α α (function.swap (*)) (≤)]

section special

@[to_additive]
lemma mul_lt_mul_of_le_of_lt (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
(mul_le_mul_right_n _ h₁).trans_lt (mul_lt_mul_left' h₂ b)

@[to_additive]
lemma mul_lt_one_of_le_one_of_lt_one (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul_of_le_of_lt ha hb)

@[to_additive]
lemma lt_mul_of_le_of_one_lt (hbc : b ≤ c) (ha : 1 < a) : b < c * a :=
mul_one b ▸ mul_lt_mul_of_le_of_lt hbc ha

@[to_additive]
lemma mul_lt_of_le_of_lt_one (hbc : b ≤ c) (ha : a < 1) : b * a < c :=
mul_one c ▸ mul_lt_mul_of_le_of_lt hbc ha

@[to_additive]
lemma lt_mul_of_one_le_of_lt (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
one_mul b ▸ mul_lt_mul_of_le_of_lt ha hbc

@[to_additive]
lemma mul_lt_of_le_one_of_lt (ha : a ≤ 1) (hbc : b < c) : a * b < c :=
one_mul c ▸ mul_lt_mul_of_le_of_lt ha hbc

end special

variable [contravariant_class α α (function.swap (*)) (<)]

@[to_additive add_lt_add]
lemma mul_lt_mul''' (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
(mul_lt_mul_of_right h₁ c).trans (mul_lt_mul_left' h₂ b)

@[to_additive]
lemma mul_lt_one (ha : a < 1) (hb : b < 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul''' ha hb)

@[to_additive]
lemma lt_mul_of_one_lt_of_lt (ha : 1 < a) (hbc : b < c) : b < a * c :=
one_mul b ▸ mul_lt_mul''' ha hbc

@[to_additive]
lemma lt_mul_of_lt_of_one_lt (hbc : b < c) (ha : 1 < a) : b < c * a :=
mul_one b ▸ mul_lt_mul''' hbc ha

@[to_additive]
lemma mul_lt_of_lt_one_of_lt (ha : a < 1) (hbc : b < c) : a * b < c :=
one_mul c ▸ mul_lt_mul''' ha hbc

@[to_additive]
lemma mul_lt_of_lt_of_lt_one (hbc : b < c) (ha : a < 1) : b * a < c :=
mul_one c ▸ mul_lt_mul''' hbc ha

end new
