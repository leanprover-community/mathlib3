/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import algebra.module
import ring_theory.subring
import ring_theory.prod

/-!
# Pi instances for algebraic structures
-/

namespace pi
universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

instance has_zero [∀ i, has_zero $ f i] : has_zero (Π i : I, f i) := ⟨λ i, 0⟩
@[simp] lemma zero_apply [∀ i, has_zero $ f i] : (0 : Π i, f i) i = 0 := rfl

instance has_one [∀ i, has_one $ f i] : has_one (Π i : I, f i) := ⟨λ i, 1⟩
@[simp] lemma one_apply [∀ i, has_one $ f i] : (1 : Π i, f i) i = 1 := rfl

attribute [to_additive] pi.has_one
attribute [to_additive] pi.one_apply

instance has_add [∀ i, has_add $ f i] : has_add (Π i : I, f i) := ⟨λ x y, λ i, x i + y i⟩
@[simp] lemma add_apply [∀ i, has_add $ f i] : (x + y) i = x i + y i := rfl

instance has_mul [∀ i, has_mul $ f i] : has_mul (Π i : I, f i) := ⟨λ x y, λ i, x i * y i⟩
@[simp] lemma mul_apply [∀ i, has_mul $ f i] : (x * y) i = x i * y i := rfl

attribute [to_additive] pi.has_mul
attribute [to_additive] pi.mul_apply

instance has_inv [∀ i, has_inv $ f i] : has_inv (Π i : I, f i) := ⟨λ x, λ i, (x i)⁻¹⟩
@[simp] lemma inv_apply [∀ i, has_inv $ f i] : x⁻¹ i = (x i)⁻¹ := rfl

instance has_neg [∀ i, has_neg $ f i] : has_neg (Π i : I, f i) := ⟨λ x, λ i, -(x i)⟩
@[simp] lemma neg_apply [∀ i, has_neg $ f i] : (-x) i = -x i := rfl

attribute [to_additive] pi.has_inv
attribute [to_additive] pi.inv_apply

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
instance semiring           [∀ i, semiring           $ f i] : semiring           (Π i : I, f i) := by pi_instance
instance ring               [∀ i, ring               $ f i] : ring               (Π i : I, f i) := by pi_instance
instance comm_ring          [∀ i, comm_ring          $ f i] : comm_ring          (Π i : I, f i) := by pi_instance

instance mul_action (α) {m : monoid α} [∀ i, mul_action α $ f i] :
  @mul_action α (Π i : I, f i) m :=
{ smul := λ c f i, c • f i,
  mul_smul := λ r s f, funext $ λ i, mul_smul _ _ _,
  one_smul := λ f, funext $ λ i, one_smul α _ }

instance distrib_mul_action (α) {m : monoid α} {n : ∀ i, add_monoid $ f i} [∀ i, distrib_mul_action α $ f i] :
  @distrib_mul_action α (Π i : I, f i) m (@pi.add_monoid I f n) :=
{ smul_zero := λ c, funext $ λ i, smul_zero _,
  smul_add := λ c f g, funext $ λ i, smul_add _ _ _,
  ..pi.mul_action _ }

variables (I f)

instance semimodule (α) {r : semiring α} {m : ∀ i, add_comm_monoid $ f i} [∀ i, semimodule α $ f i] :
  @semimodule α (Π i : I, f i) r (@pi.add_comm_monoid I f m) :=
{ add_smul := λ c f g, funext $ λ i, add_smul _ _ _,
  zero_smul := λ f, funext $ λ i, zero_smul α _,
  ..pi.distrib_mul_action _ }

variables {I f}

instance left_cancel_semigroup [∀ i, left_cancel_semigroup $ f i] :
  left_cancel_semigroup (Π i : I, f i) :=
by pi_instance

instance add_left_cancel_semigroup [∀ i, add_left_cancel_semigroup $ f i] :
  add_left_cancel_semigroup (Π i : I, f i) :=
by pi_instance

instance right_cancel_semigroup [∀ i, right_cancel_semigroup $ f i] :
  right_cancel_semigroup (Π i : I, f i) :=
by pi_instance

instance add_right_cancel_semigroup [∀ i, add_right_cancel_semigroup $ f i] :
  add_right_cancel_semigroup (Π i : I, f i) :=
by pi_instance

instance ordered_cancel_comm_monoid [∀ i, ordered_cancel_add_comm_monoid $ f i] :
  ordered_cancel_add_comm_monoid (Π i : I, f i) :=
by pi_instance

instance ordered_add_comm_group [∀ i, ordered_add_comm_group $ f i] :
  ordered_add_comm_group (Π i : I, f i) :=
{ add_le_add_left := λ x y hxy c i, add_le_add_left (hxy i) _,
  ..pi.add_comm_group,
  ..pi.partial_order }

attribute [to_additive add_semigroup]              pi.semigroup
attribute [to_additive add_comm_semigroup]         pi.comm_semigroup
attribute [to_additive add_monoid]                 pi.monoid
attribute [to_additive add_comm_monoid]            pi.comm_monoid
attribute [to_additive add_group]                  pi.group
attribute [to_additive add_comm_group]             pi.comm_group
attribute [to_additive add_left_cancel_semigroup]  pi.left_cancel_semigroup
attribute [to_additive add_right_cancel_semigroup] pi.right_cancel_semigroup

@[simp] lemma sub_apply [∀ i, add_group $ f i] : (x - y) i = x i - y i := rfl

@[to_additive]
lemma list_prod_apply {α : Type*} {β : α → Type*} [∀a, monoid (β a)] (a : α) :
  ∀ (l : list (Πa, β a)), l.prod a = (l.map (λf:Πa, β a, f a)).prod
| []       := rfl
| (f :: l) := by simp [mul_apply f l.prod a, list_prod_apply l]

@[to_additive]
lemma multiset_prod_apply {α : Type*} {β : α → Type*} [∀a, comm_monoid (β a)] (a : α)
  (s : multiset (Πa, β a)) : s.prod a = (s.map (λf:Πa, β a, f a)).prod :=
quotient.induction_on s $ assume l, begin simp [list_prod_apply a l] end

@[to_additive]
lemma finset_prod_apply {α : Type*} {β : α → Type*} {γ} [∀a, comm_monoid (β a)] (a : α)
  (s : finset γ) (g : γ → Πa, β a) : s.prod g a = s.prod (λc, g c a) :=
show (s.val.map g).prod a = (s.val.map (λc, g c a)).prod,
  by rw [multiset_prod_apply, multiset.map_map]

/-- A family of ring homomorphisms `f a : γ →+* β a` defines a ring homomorphism
`pi.ring_hom f : γ →+* Π a, β a` given by `pi.ring_hom f x b = f b x`. -/
protected def ring_hom
  {α : Type u} {β : α → Type v} [R : Π a : α, semiring (β a)]
  {γ : Type w} [semiring γ] (f : Π a : α, γ →+* β a) :
  γ →+* Π a, β a :=
{ to_fun := λ x b, f b x,
  map_add' := λ x y, funext $ λ z, (f z).map_add x y,
  map_mul' := λ x y, funext $ λ z, (f z).map_mul x y,
  map_one' := funext $ λ z, (f z).map_one,
  map_zero' := funext $ λ z, (f z).map_zero }

instance is_ring_hom_pi
  {α : Type u} {β : α → Type v} [R : Π a : α, ring (β a)]
  {γ : Type w} [ring γ]
  (f : Π a : α, γ → β a) [Rh : Π a : α, is_ring_hom (f a)] :
  is_ring_hom (λ x b, f b x) :=
(show γ →+* Π a, β a, from pi.ring_hom (λ a, ring_hom.of (f a))).is_ring_hom

-- Note that we only define `single` here for dependent functions with additive fibres.
section
variables [decidable_eq I]
variables [Π i, has_zero (f i)]

/-- The function supported at `i`, with value `x` there. -/
def single (i : I) (x : f i) : Π i, f i :=
λ i', if h : i' = i then (by { subst h, exact x }) else 0

@[simp]
lemma single_eq_same (i : I) (x : f i) : single i x i = x :=
begin
  dsimp [single],
  split_ifs,
  { refl, },
  { exfalso, exact h rfl, }
end
@[simp]
lemma single_eq_of_ne {i i' : I} (h : i' ≠ i) (x : f i) : single i x i' = 0 :=
begin
  dsimp [single],
  split_ifs with h',
  { exfalso, exact h h', },
  { refl, }
end

end

end pi

section
universes u v
variable {I : Type u}     -- The indexing type
variable (f : I → Type v) -- The family of types already equipped with instances
variables [Π i, monoid (f i)]

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism. -/
@[to_additive "Evaluation of functions into an indexed collection of additive monoids at a point
is an additive monoid homomorphism."]
def monoid_hom.apply (i : I) : (Π i, f i) →* f i :=
{ to_fun := λ g, g i,
  map_one' := rfl,
  map_mul' := λ x y, rfl, }

@[simp, to_additive]
lemma monoid_hom.apply_apply (i : I) (g : Π i, f i) : (monoid_hom.apply f i) g = g i := rfl
end

section
universes u v
variable {I : Type u}     -- The indexing type
variable (f : I → Type v) -- The family of types already equipped with instances
variables [Π i, semiring (f i)]

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid homomorphism. -/
def ring_hom.apply (i : I) : (Π i, f i) →+* f i :=
{ ..(monoid_hom.apply f i),
  ..(add_monoid_hom.apply f i) }

@[simp]
lemma ring_hom.apply_apply (i : I) (g : Π i, f i) : (ring_hom.apply f i) g = g i := rfl
end

section
variables {I : Type*} (Z : I → Type*)
variables [Π i, comm_monoid (Z i)]

@[simp, to_additive]
lemma finset.prod_apply {γ : Type*} {s : finset γ} (h : γ → (Π i, Z i)) (i : I) :
  (s.prod h) i = s.prod (λ g, h g i) :=
begin
  classical,
  induction s using finset.induction_on with b s nmem ih,
  { simp only [finset.prod_empty], refl },
  { simp only [nmem, finset.prod_insert, not_false_iff],
    rw pi.mul_apply (h b) _ i,
    rw ih, }
end
end

section
-- As we only defined `single` into `add_monoid`, we only prove the `finset.sum` version here.
variables {I : Type*} [decidable_eq I] {Z : I → Type*}
variables [Π i, add_comm_monoid (Z i)]

lemma finset.univ_sum_single [fintype I] (f : Π i, Z i) :
  finset.univ.sum (λ i, pi.single i (f i)) = f :=
begin
  ext a,
  rw [finset.sum_apply, finset.sum_eq_single a],
  { simp, },
  { intros b _ h, simp [h.symm], },
  { intro h, exfalso, simpa using h, },
end
end

section
open pi

variables {I : Type*} [decidable_eq I]
variable (f : I → Type*)

section
variables [Π i, add_monoid (f i)]

/-- The additive monoid homomorphism including a single additive monoid
into a dependent family of additive monoids, as functions supported at a point. -/
def add_monoid_hom.single (i : I) : f i →+ Π i, f i :=
{ to_fun := λ x, single i x,
  map_zero' :=
  begin
    ext i', by_cases h : i' = i,
    { subst h, simp only [single_eq_same], refl, },
    { simp only [h, single_eq_of_ne, ne.def, not_false_iff], refl, },
  end,
  map_add' := λ x y,
  begin
    ext i', by_cases h : i' = i,
    -- FIXME in the next two `simp only`s,
    -- it would be really nice to not have to provide the arguments to `add_apply`.
    { subst h, simp only [single_eq_same, add_apply (single i' x) (single i' y) i'], },
    { simp only [h, add_zero, single_eq_of_ne, add_apply (single i x) (single i y) i', ne.def, not_false_iff], },
  end, }

@[simp]
lemma add_monoid_hom.single_apply {i : I} (x : f i) : (add_monoid_hom.single f i) x = single i x := rfl
end

section
variables {f}
variables [Π i, add_comm_monoid (f i)]

@[ext]
lemma add_monoid_hom.functions_ext [fintype I] (G : Type*) [add_comm_monoid G] (g h : (Π i, f i) →+ G)
  (w : ∀ (i : I) (x : f i), g (single i x) = h (single i x)) : g = h :=
begin
  ext k,
  rw [←finset.univ_sum_single k, add_monoid_hom.map_sum, add_monoid_hom.map_sum],
  apply finset.sum_congr rfl,
  intros,
  apply w,
end
end

section
variables {f}
variables [Π i, semiring (f i)]

-- it is somewhat unfortunate that we can't easily use `add_monoid_hom.functions_ext` here
@[ext]
lemma ring_hom.functions_ext [fintype I] (G : Type*) [semiring G] (g h : (Π i, f i) →+* G)
  (w : ∀ (i : I) (x : f i), g (single i x) = h (single i x)) : g = h :=
begin
  ext k,
  rw [←finset.univ_sum_single k, ring_hom.map_sum, ring_hom.map_sum],
  apply finset.sum_congr rfl,
  intros,
  apply w,
end
end
end

namespace prod

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {p q : α × β}
@[to_additive is_add_monoid_hom]
lemma fst.is_monoid_hom [monoid α] [monoid β] : is_monoid_hom (prod.fst : α × β → α) :=
{ map_mul := λ _ _, rfl, map_one := rfl }
@[to_additive is_add_monoid_hom]
lemma snd.is_monoid_hom [monoid α] [monoid β] : is_monoid_hom (prod.snd : α × β → β) :=
{ map_mul := λ _ _, rfl, map_one := rfl }

@[to_additive is_add_group_hom]
lemma fst.is_group_hom [group α] [group β] : is_group_hom (prod.fst : α × β → α) :=
{ map_mul := λ _ _, rfl }
@[to_additive is_add_group_hom]
lemma snd.is_group_hom [group α] [group β] : is_group_hom (prod.snd : α × β → β) :=
{ map_mul := λ _ _, rfl }

attribute [instance] fst.is_monoid_hom fst.is_add_monoid_hom snd.is_monoid_hom snd.is_add_monoid_hom
fst.is_group_hom fst.is_add_group_hom snd.is_group_hom snd.is_add_group_hom

@[to_additive]
lemma fst_prod [comm_monoid α] [comm_monoid β] {t : finset γ} {f : γ → α × β} :
  (t.prod f).1 = t.prod (λc, (f c).1) :=
(monoid_hom.fst α β).map_prod f t

@[to_additive]
lemma snd_prod [comm_monoid α] [comm_monoid β] {t : finset γ} {f : γ → α × β} :
  (t.prod f).2 = t.prod (λc, (f c).2) :=
(monoid_hom.snd α β).map_prod f t

instance fst.is_semiring_hom [semiring α] [semiring β] : is_semiring_hom (prod.fst : α × β → α) :=
(ring_hom.fst α β).is_semiring_hom
instance snd.is_semiring_hom [semiring α] [semiring β] : is_semiring_hom (prod.snd : α × β → β) :=
(ring_hom.snd α β).is_semiring_hom

instance fst.is_ring_hom [ring α] [ring β] : is_ring_hom (prod.fst : α × β → α) :=
(ring_hom.fst α β).is_ring_hom
instance snd.is_ring_hom [ring α] [ring β] : is_ring_hom (prod.snd : α × β → β) :=
(ring_hom.snd α β).is_ring_hom

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
  one_smul  := assume ⟨b, c⟩, mk.inj_iff.mpr ⟨one_smul _ _, one_smul _ _⟩,
  zero_smul := assume ⟨b, c⟩, mk.inj_iff.mpr ⟨zero_smul _ _, zero_smul _ _⟩,
  smul_zero := assume a, mk.inj_iff.mpr ⟨smul_zero _, smul_zero _⟩,
  .. prod.has_scalar }

section substructures
variables (s : set α) (t : set β)

@[to_additive is_add_submonoid]
instance [monoid α] [monoid β] [is_submonoid s] [is_submonoid t] :
  is_submonoid (s.prod t) :=
{ one_mem := by rw set.mem_prod; split; apply is_submonoid.one_mem,
  mul_mem := by intros; rw set.mem_prod at *; split; apply is_submonoid.mul_mem; tauto }

@[to_additive prod.is_add_subgroup.prod]
instance is_subgroup.prod [group α] [group β] [is_subgroup s] [is_subgroup t] :
  is_subgroup (s.prod t) :=
{ inv_mem := by intros; rw set.mem_prod at *; split; apply is_subgroup.inv_mem; tauto,
  .. prod.is_submonoid s t }

instance is_subring.prod [ring α] [ring β] [is_subring s] [is_subring t] :
  is_subring (s.prod t) :=
{ .. prod.is_submonoid s t, .. prod.is_add_subgroup.prod s t }

end substructures

end prod

namespace finset

@[to_additive prod_mk_sum]
lemma prod_mk_prod {α β γ : Type*} [comm_monoid α] [comm_monoid β] (s : finset γ)
  (f : γ → α) (g : γ → β) : (s.prod f, s.prod g) = s.prod (λ x, (f x, g x)) :=
by haveI := classical.dec_eq γ; exact
finset.induction_on s rfl (by simp [prod.ext_iff] {contextual := tt})

end finset
