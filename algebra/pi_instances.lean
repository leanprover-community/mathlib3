/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot

Pi instances for algebraic structures.
-/
import order.basic
import algebra.module algebra.group
import data.finset
import tactic.pi_instances

namespace pi
universes u v
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equiped with instances
variables (x y : Π i, f i) (i : I)

instance has_zero [∀ i, has_zero $ f i] : has_zero (Π i : I, f i) := ⟨λ i, 0⟩
@[simp] lemma zero_apply [∀ i, has_zero $ f i] : (0 : Π i, f i) i = 0 := rfl

instance has_one [∀ i, has_one $ f i] : has_one (Π i : I, f i) := ⟨λ i, 1⟩
@[simp] lemma one_apply [∀ i, has_one $ f i] : (1 : Π i, f i) i = 1 := rfl

attribute [to_additive pi.has_zero] pi.has_one
attribute [to_additive pi.zero_apply] pi.one_apply

instance has_add [∀ i, has_add $ f i] : has_add (Π i : I, f i) := ⟨λ x y, λ i, x i + y i⟩
@[simp] lemma add_apply [∀ i, has_add $ f i] : (x + y) i = x i + y i := rfl

instance has_mul [∀ i, has_mul $ f i] : has_mul (Π i : I, f i) := ⟨λ x y, λ i, x i * y i⟩
@[simp] lemma mul_apply [∀ i, has_mul $ f i] : (x * y) i = x i * y i := rfl

attribute [to_additive pi.has_add] pi.has_mul
attribute [to_additive pi.add_apply] pi.mul_apply

instance has_inv [∀ i, has_inv $ f i] : has_inv (Π i : I, f i) := ⟨λ x, λ i, (x i)⁻¹⟩
@[simp] lemma inv_apply [∀ i, has_inv $ f i] : x⁻¹ i = (x i)⁻¹ := rfl

instance has_neg [∀ i, has_neg $ f i] : has_neg (Π i : I, f i) := ⟨λ x, λ i, -(x i)⟩
@[simp] lemma neg_apply [∀ i, has_neg $ f i] : (-x) i = -x i := rfl

attribute [to_additive pi.has_neg] pi.has_inv
attribute [to_additive pi.neg_apply] pi.inv_apply

instance has_scalar {α : Type*} [∀ i, has_scalar α $ f i] : has_scalar α (Π i : I, f i) := ⟨λ s x, λ i, s • (x i)⟩
@[simp] lemma smul_apply {α : Type*} [∀ i, has_scalar α $ f i] (s : α) : (s • x) i = s • x i := rfl

instance semigroup          [∀ i, semigroup          $ f i] : semigroup          (Π i : I, f i) := by pi_instance
instance comm_semigroup     [∀ i, comm_semigroup     $ f i] : comm_semigroup     (Π i : I, f i) := by pi_instance
instance monoid             [∀ i, monoid             $ f i] : monoid             (Π i : I, f i) := by pi_instance
instance comm_monoid        [∀ i, comm_monoid        $ f i] : comm_monoid        (Π i : I, f i) := by pi_instance
instance group              [∀ i, group              $ f i] : group              (Π i : I, f i) := by pi_instance
instance comm_group         [∀ i, comm_group         $ f i] : comm_group         (Π i : I, f i) := by pi_instance
instance add_semigroup      [∀ i, add_semigroup      $ f i] : add_semigroup      (Π i : I, f i) := by pi_instance
instance add_comm_semigroup [∀ i, add_comm_semigroup $ f i] : add_comm_semigroup (Π i : I, f i) := by pi_instance
instance add_monoid         [∀ i, add_monoid         $ f i] : add_monoid         (Π i : I, f i) := by pi_instance
instance add_comm_monoid    [∀ i, add_comm_monoid    $ f i] : add_comm_monoid    (Π i : I, f i) := by pi_instance
instance add_group          [∀ i, add_group          $ f i] : add_group          (Π i : I, f i) := by pi_instance
instance add_comm_group     [∀ i, add_comm_group     $ f i] : add_comm_group     (Π i : I, f i) := by pi_instance
instance ring               [∀ i, ring               $ f i] : ring               (Π i : I, f i) := by pi_instance
instance comm_ring          [∀ i, comm_ring          $ f i] : comm_ring          (Π i : I, f i) := by pi_instance

instance semimodule   (α) {r : semiring α}       [∀ i, add_comm_monoid $ f i] [∀ i, semimodule α $ f i]   : semimodule α (Π i : I, f i)   := by pi_instance
instance module       (α) {r : ring α}           [∀ i, add_comm_group $ f i]  [∀ i, module α $ f i]       : module α (Π i : I, f i)       := {..pi.semimodule α}
instance vector_space (α) {r : discrete_field α} [∀ i, add_comm_group $ f i]  [∀ i, vector_space α $ f i] : vector_space α (Π i : I, f i) := {..pi.module α}

instance left_cancel_semigroup [∀ i, left_cancel_semigroup $ f i] : left_cancel_semigroup (Π i : I, f i) :=
by pi_instance

instance add_left_cancel_semigroup [∀ i, add_left_cancel_semigroup $ f i] : add_left_cancel_semigroup (Π i : I, f i) :=
by pi_instance

instance right_cancel_semigroup [∀ i, right_cancel_semigroup $ f i] : right_cancel_semigroup (Π i : I, f i) :=
by pi_instance

instance add_right_cancel_semigroup [∀ i, add_right_cancel_semigroup $ f i] : add_right_cancel_semigroup (Π i : I, f i) :=
by pi_instance

instance ordered_cancel_comm_monoid [∀ i, ordered_cancel_comm_monoid $ f i] : ordered_cancel_comm_monoid (Π i : I, f i) :=
by pi_instance

attribute [to_additive pi.add_semigroup]              pi.semigroup
attribute [to_additive pi.add_comm_semigroup]         pi.comm_semigroup
attribute [to_additive pi.add_monoid]                 pi.monoid
attribute [to_additive pi.add_comm_monoid]            pi.comm_monoid
attribute [to_additive pi.add_group]                  pi.group
attribute [to_additive pi.add_comm_group]             pi.comm_group
attribute [to_additive pi.add_left_cancel_semigroup]  pi.left_cancel_semigroup
attribute [to_additive pi.add_right_cancel_semigroup] pi.right_cancel_semigroup

@[to_additive pi.list_sum_apply]
lemma list_prod_apply {α : Type*} {β} [monoid β] (a : α) :
  ∀ (l : list (α → β)), l.prod a = (l.map (λf:α → β, f a)).prod
| []       := rfl
| (f :: l) := by simp [mul_apply f l.prod a, list_prod_apply l]

@[to_additive pi.multiset_sum_apply]
lemma multiset_prod_apply {α : Type*} {β} [comm_monoid β] (a : α) (s : multiset (α → β)) :
  s.prod a = (s.map (λf:α → β, f a)).prod :=
quotient.induction_on s $ assume l, begin simp [list_prod_apply a l] end

@[to_additive pi.finset_sum_apply]
lemma finset_prod_apply {α : Type*} {β γ} [comm_monoid β] (a : α) (s : finset γ) (g : γ → α → β) :
  s.prod g a = s.prod (λc, g c a) :=
show (s.val.map g).prod a = (s.val.map (λc, g c a)).prod,
  by rw [multiset_prod_apply, multiset.map_map]

end pi

namespace prod
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {p q : α × β}

instance [has_add α] [has_add β] : has_add (α × β) :=
⟨λp q, (p.1 + q.1, p.2 + q.2)⟩
@[to_additive prod.has_add]
instance [has_mul α] [has_mul β] : has_mul (α × β) :=
⟨λp q, (p.1 * q.1, p.2 * q.2)⟩

@[simp, to_additive prod.fst_add]
lemma fst_mul [has_mul α] [has_mul β] : (p * q).1 = p.1 * q.1 := rfl
@[simp, to_additive prod.snd_add]
lemma snd_mul [has_mul α] [has_mul β] : (p * q).2 = p.2 * q.2 := rfl
@[simp, to_additive prod.mk_add_mk]
lemma mk_mul_mk [has_mul α] [has_mul β] (a₁ a₂ : α) (b₁ b₂ : β) :
  (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂) := rfl

instance [has_zero α] [has_zero β] : has_zero (α × β) := ⟨(0, 0)⟩
@[to_additive prod.has_zero]
instance [has_one α] [has_one β] : has_one (α × β) := ⟨(1, 1)⟩

@[simp, to_additive prod.fst_zero]
lemma fst_one [has_one α] [has_one β] : (1 : α × β).1 = 1 := rfl
@[simp, to_additive prod.snd_zero]
lemma snd_one [has_one α] [has_one β] : (1 : α × β).2 = 1 := rfl
@[to_additive prod.zero_eq_mk]
lemma one_eq_mk [has_one α] [has_one β] : (1 : α × β) = (1, 1) := rfl

instance [has_neg α] [has_neg β] : has_neg (α × β) := ⟨λp, (- p.1, - p.2)⟩
@[to_additive prod.has_neg]
instance [has_inv α] [has_inv β] : has_inv (α × β) := ⟨λp, (p.1⁻¹, p.2⁻¹)⟩

@[simp, to_additive prod.fst_neg]
lemma fst_inv [has_inv α] [has_inv β] : (p⁻¹).1 = (p.1)⁻¹ := rfl
@[simp, to_additive prod.snd_neg]
lemma snd_inv [has_inv α] [has_inv β] : (p⁻¹).2 = (p.2)⁻¹ := rfl
@[to_additive prod.neg_mk]
lemma inv_mk [has_inv α] [has_inv β] (a : α) (b : β) : (a, b)⁻¹ = (a⁻¹, b⁻¹) := rfl

instance [add_semigroup α] [add_semigroup β] : add_semigroup (α × β) :=
{ add_assoc := assume a b c, mk.inj_iff.mpr ⟨add_assoc _ _ _, add_assoc _ _ _⟩,
  .. prod.has_add }
@[to_additive prod.add_semigroup]
instance [semigroup α] [semigroup β] : semigroup (α × β) :=
{ mul_assoc := assume a b c, mk.inj_iff.mpr ⟨mul_assoc _ _ _, mul_assoc _ _ _⟩,
  .. prod.has_mul }

instance [add_monoid α] [add_monoid β] : add_monoid (α × β) :=
{ zero_add := assume a, prod.rec_on a $ λa b, mk.inj_iff.mpr ⟨zero_add _, zero_add _⟩,
  add_zero := assume a, prod.rec_on a $ λa b, mk.inj_iff.mpr ⟨add_zero _, add_zero _⟩,
  .. prod.add_semigroup, .. prod.has_zero }
@[to_additive prod.add_monoid]
instance [monoid α] [monoid β] : monoid (α × β) :=
{ one_mul := assume a, prod.rec_on a $ λa b, mk.inj_iff.mpr ⟨one_mul _, one_mul _⟩,
  mul_one := assume a, prod.rec_on a $ λa b, mk.inj_iff.mpr ⟨mul_one _, mul_one _⟩,
  .. prod.semigroup, .. prod.has_one }

instance [add_group α] [add_group β] : add_group (α × β) :=
{ add_left_neg := assume a, mk.inj_iff.mpr ⟨add_left_neg _, add_left_neg _⟩,
  .. prod.add_monoid, .. prod.has_neg }
@[to_additive prod.add_group]
instance [group α] [group β] : group (α × β) :=
{ mul_left_inv := assume a, mk.inj_iff.mpr ⟨mul_left_inv _, mul_left_inv _⟩,
  .. prod.monoid, .. prod.has_inv }

instance [add_comm_semigroup α] [add_comm_semigroup β] : add_comm_semigroup (α × β) :=
{ add_comm := assume a b, mk.inj_iff.mpr ⟨add_comm _ _, add_comm _ _⟩,
  .. prod.add_semigroup }
@[to_additive prod.add_comm_semigroup]
instance [comm_semigroup α] [comm_semigroup β] : comm_semigroup (α × β) :=
{ mul_comm := assume a b, mk.inj_iff.mpr ⟨mul_comm _ _, mul_comm _ _⟩,
  .. prod.semigroup }

instance [add_comm_monoid α] [add_comm_monoid β] : add_comm_monoid (α × β) :=
{ .. prod.add_comm_semigroup, .. prod.add_monoid }
@[to_additive prod.add_comm_monoid]
instance [comm_monoid α] [comm_monoid β] : comm_monoid (α × β) :=
{ .. prod.comm_semigroup, .. prod.monoid }

instance [add_comm_group α] [add_comm_group β] : add_comm_group (α × β) :=
{ .. prod.add_comm_semigroup, .. prod.add_group }
@[to_additive prod.add_comm_group]
instance [comm_group α] [comm_group β] : comm_group (α × β) :=
{ .. prod.comm_semigroup, .. prod.group }

@[to_additive prod.fst_sum]
lemma fst_prod [comm_monoid α] [comm_monoid β] {t : finset γ} {f : γ → α × β} :
  (t.prod f).1 = t.prod (λc, (f c).1) :=
(finset.prod_hom prod.fst (show (1:α×β).1 = 1, from rfl) $ assume x y, rfl).symm

@[to_additive prod.snd_sum]
lemma snd_prod [comm_monoid α] [comm_monoid β] {t : finset γ} {f : γ → α × β} :
  (t.prod f).2 = t.prod (λc, (f c).2) :=
(finset.prod_hom prod.snd (show (1:α×β).2 = 1, from rfl) $ assume x y, rfl).symm

instance [semiring α] [semiring β] : semiring (α × β) :=
{ zero_mul := λ a, mk.inj_iff.mpr ⟨zero_mul _, zero_mul _⟩,
  mul_zero := λ a, mk.inj_iff.mpr ⟨mul_zero _, mul_zero _⟩,
  left_distrib := λ a b c, mk.inj_iff.mpr ⟨left_distrib _ _ _, left_distrib _ _ _⟩,
  right_distrib := λ a b c, mk.inj_iff.mpr ⟨right_distrib _ _ _, right_distrib _ _ _⟩,
  ..prod.add_comm_monoid, ..prod.monoid }

instance [ring α] [ring β] : ring (α × β) :=
{ ..prod.add_comm_group, ..prod.semiring }

instance [comm_ring α] [comm_ring β] : comm_ring (α × β) :=
{ ..prod.ring, ..prod.comm_monoid }

instance [nonzero_comm_ring α] [comm_ring β] : nonzero_comm_ring (α × β) :=
{ zero_ne_one := mt (congr_arg prod.fst) zero_ne_one,
  ..prod.comm_ring }

/-- Left injection function for the inner product
From a vector space (and also group and module) perspective the product is the same as the sum of
two vector spaces. `inl` and `inr` provide the corresponding injection functions.
-/
def inl [has_zero β] (a : α) : α × β := (a, 0)

/-- Right injection function for the inner product -/
def inr [has_zero α] (b : β) : α × β := (0, b)

lemma injective_inl [has_zero β] : function.injective (inl : α → α × β) :=
assume x y h, (prod.mk.inj_iff.mp h).1

lemma injective_inr [has_zero α] : function.injective (inr : β → α × β) :=
assume x y h, (prod.mk.inj_iff.mp h).2

@[simp] lemma inl_eq_inl [has_zero β] {a₁ a₂ : α} : (inl a₁ : α × β) = inl a₂ ↔ a₁ = a₂ :=
iff.intro (assume h, injective_inl h) (assume h, h ▸ rfl)

@[simp] lemma inr_eq_inr [has_zero α] {b₁ b₂ : β} : (inr b₁ : α × β) = inr b₂ ↔ b₁ = b₂ :=
iff.intro (assume h, injective_inr h) (assume h, h ▸ rfl)

@[simp] lemma inl_eq_inr [has_zero α] [has_zero β] {a : α} {b : β} :
  inl a = inr b ↔ a = 0 ∧ b = 0 :=
by constructor; simp [inl, inr] {contextual := tt}

@[simp] lemma inr_eq_inl [has_zero α] [has_zero β] {a : α} {b : β} :
  inr b = inl a ↔ a = 0 ∧ b = 0 :=
by constructor; simp [inl, inr] {contextual := tt}

@[simp] lemma fst_inl [has_zero β] (a : α) : (inl a : α × β).1 = a := rfl
@[simp] lemma snd_inl [has_zero β] (a : α) : (inl a : α × β).2 = 0 := rfl
@[simp] lemma fst_inr [has_zero α] (b : β) : (inr b : α × β).1 = 0 := rfl
@[simp] lemma snd_inr [has_zero α] (b : β) : (inr b : α × β).2 = b := rfl

instance [has_scalar α β] [has_scalar α γ] : has_scalar α (β × γ) := ⟨λa p, (a • p.1, a • p.2)⟩

@[simp] theorem smul_fst [has_scalar α β] [has_scalar α γ]
  (a : α) (x : β × γ) : (a • x).1 = a • x.1 := rfl
@[simp] theorem smul_snd [has_scalar α β] [has_scalar α γ]
  (a : α) (x : β × γ) : (a • x).2 = a • x.2 := rfl
@[simp] theorem smul_mk [has_scalar α β] [has_scalar α γ]
  (a : α) (b : β) (c : γ) : a • (b, c) = (a • b, a • c) := rfl

instance {r : semiring α} [add_comm_monoid β] [add_comm_monoid γ]
  [semimodule α β] [semimodule α γ] : semimodule α (β × γ) :=
{ smul_add  := assume a p₁ p₂, mk.inj_iff.mpr ⟨smul_add _ _ _, smul_add _ _ _⟩,
  add_smul  := assume a p₁ p₂, mk.inj_iff.mpr ⟨add_smul _ _ _, add_smul _ _ _⟩,
  mul_smul  := assume a₁ a₂ p, mk.inj_iff.mpr ⟨mul_smul _ _ _, mul_smul _ _ _⟩,
  one_smul  := assume ⟨b, c⟩, mk.inj_iff.mpr ⟨one_smul _, one_smul _⟩,
  zero_smul := assume ⟨b, c⟩, mk.inj_iff.mpr ⟨zero_smul _, zero_smul _⟩,
  smul_zero := assume a, mk.inj_iff.mpr ⟨smul_zero _, smul_zero _⟩,
  .. prod.has_scalar }

instance {r : ring α} [add_comm_group β] [add_comm_group γ]
  [module α β] [module α γ] : module α (β × γ) := {}

instance {r : discrete_field α} [add_comm_group β] [add_comm_group γ]
  [vector_space α β] [vector_space α γ] : vector_space α (β × γ) := {}

end prod

namespace finset

@[to_additive finset.prod_mk_sum]
lemma prod_mk_prod {α β γ : Type*} [comm_monoid α] [comm_monoid β] (s : finset γ)
  (f : γ → α) (g : γ → β) : (s.prod f, s.prod g) = s.prod (λ x, (f x, g x)) :=
by haveI := classical.dec_eq γ; exact
finset.induction_on s rfl (by simp [prod.ext_iff] {contextual := tt})

end finset
