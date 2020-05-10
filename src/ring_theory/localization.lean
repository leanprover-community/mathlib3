/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin
-/
import ring_theory.ideal_operations

universes u v

local attribute [instance, priority 10] is_ring_hom.comp

namespace localization
variables (α : Type u) [comm_ring α] (S : set α)

def r (x y : α × S) : Prop :=
∃ t ∈ S, ((x.2 : α) * y.1 - y.2 * x.1) * t = 0

local infix ≈ := r α S

theorem symm (x y : α × S) : x ≈ y → y ≈ x :=
λ ⟨t, hts, ht⟩, ⟨t, hts, by rw [← neg_sub, ← neg_mul_eq_neg_mul, ht, neg_zero]⟩

variable [is_submonoid S]

section
variables {α S}
theorem r_of_eq {a₀ a₁ : α × S} (h : (a₀.2 : α) * a₁.1 = a₁.2 * a₀.1) : a₀ ≈ a₁ :=
⟨1, is_submonoid.one_mem, by rw [h, sub_self, mul_one]⟩
end

theorem refl (x : α × S) : x ≈ x := r_of_eq rfl

theorem trans : ∀ (x y z : α × S), x ≈ y → y ≈ z → x ≈ z :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨t, hts, ht⟩ ⟨t', hts', ht'⟩,
⟨s₂ * t' * t, is_submonoid.mul_mem (is_submonoid.mul_mem hs₂ hts') hts,
  calc (s₁ * r₃ - s₃ * r₁) * (s₂ * t' * t) =
    t' * s₃ * ((s₁ * r₂ - s₂ * r₁) * t) + t * s₁ * ((s₂ * r₃ - s₃ * r₂) * t') : by ring
    ... = 0 : by simp only [subtype.coe_mk] at ht ht'; rw [ht, ht']; simp⟩

instance : setoid (α × S) :=
⟨r α S, refl α S, symm α S, trans α S⟩

end localization

/-- The localization of a ring at a submonoid:
 the elements of the submonoid become invertible in the localization.-/
def localization (α : Type u) [comm_ring α] (S : set α) [is_submonoid S] :=
quotient $ localization.setoid α S

namespace localization
variables (α : Type u) [comm_ring α] (S : set α) [is_submonoid S]

instance : has_add (localization α S) :=
⟨quotient.lift₂
  (λ x y : α × S, (⟦⟨x.2 * y.1 + y.2 * x.1, x.2 * y.2⟩⟧ : localization α S)) $
  λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨r₄, s₄, hs₄⟩ ⟨t₅, hts₅, ht₅⟩ ⟨t₆, hts₆, ht₆⟩,
  quotient.sound ⟨t₆ * t₅, is_submonoid.mul_mem hts₆ hts₅,
    calc (s₁ * s₂ * (s₃ * r₄ + s₄ * r₃) - s₃ * s₄ * (s₁ * r₂ + s₂ * r₁)) * (t₆ * t₅) =
      s₁ * s₃ * ((s₂ * r₄ - s₄ * r₂) * t₆) * t₅ + s₂ * s₄ * ((s₁ * r₃ - s₃ * r₁) * t₅) * t₆ : by ring
      ... = 0 : by simp only [subtype.coe_mk] at ht₅ ht₆; rw [ht₆, ht₅]; simp⟩⟩

instance : has_neg (localization α S) :=
⟨quotient.lift (λ x : α × S, (⟦⟨-x.1, x.2⟩⟧ : localization α S)) $
  λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩,
  quotient.sound ⟨t, hts,
    calc (s₁ * -r₂ - s₂ * -r₁) * t = -((s₁ * r₂ - s₂ * r₁) * t) : by ring
      ... = 0 : by simp only [subtype.coe_mk] at ht; rw ht; simp⟩⟩

instance : has_mul (localization α S) :=
⟨quotient.lift₂
  (λ x y : α × S, (⟦⟨x.1 * y.1, x.2 * y.2⟩⟧ : localization α S)) $
  λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨r₄, s₄, hs₄⟩ ⟨t₅, hts₅, ht₅⟩ ⟨t₆, hts₆, ht₆⟩,
  quotient.sound ⟨t₆ * t₅, is_submonoid.mul_mem hts₆ hts₅,
    calc ((s₁ * s₂) * (r₃ * r₄) - (s₃ * s₄) * (r₁ * r₂)) * (t₆ * t₅) =
      t₆ * ((s₁ * r₃ - s₃ * r₁) * t₅) * r₂ * s₄ + t₅ * ((s₂ * r₄ - s₄ * r₂) * t₆) * r₃ * s₁ :
        by ring
      ... = 0 : by simp only [subtype.coe_mk] at ht₅ ht₆; rw [ht₅, ht₆]; simp⟩⟩

variables {α S}

def mk (r : α) (s : S) : localization α S := ⟦(r, s)⟧

/-- The natural map from the ring to the localization.-/
def of (r : α) : localization α S := mk r 1

instance : comm_ring (localization α S) :=
by refine
{ add            := has_add.add,
  add_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  zero           := of 0,
  zero_add       := quotient.ind _,
  add_zero       := quotient.ind _,
  neg            := has_neg.neg,
  add_left_neg   := quotient.ind _,
  add_comm       := quotient.ind₂ _,
  mul            := has_mul.mul,
  mul_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  one            := of 1,
  one_mul        := quotient.ind _,
  mul_one        := quotient.ind _,
  left_distrib   := λ m n k, quotient.induction_on₃ m n k _,
  right_distrib  := λ m n k, quotient.induction_on₃ m n k _,
  mul_comm       := quotient.ind₂ _ };
{ intros,
  try {rcases a with ⟨r₁, s₁, hs₁⟩},
  try {rcases b with ⟨r₂, s₂, hs₂⟩},
  try {rcases c with ⟨r₃, s₃, hs₃⟩},
  refine (quotient.sound $ r_of_eq _),
  simp only [is_submonoid.coe_mul, is_submonoid.coe_one, subtype.coe_mk],
  ring }

instance : inhabited (localization α S) := ⟨0⟩

instance of.is_ring_hom : is_ring_hom (of : α → localization α S) :=
{ map_add := λ x y, quotient.sound $ by simp [add_comm],
  map_mul := λ x y, quotient.sound $ by simp [add_comm],
  map_one := rfl }

variables {S}

instance : has_coe_t α (localization α S) := ⟨of⟩ -- note [use has_coe_t]

instance coe.is_ring_hom : is_ring_hom (coe : α → localization α S) :=
localization.of.is_ring_hom

/-- The natural map from the submonoid to the unit group of the localization.-/
def to_units (s : S) : units (localization α S) :=
{ val := s,
  inv := mk 1 s,
  val_inv := quotient.sound $ r_of_eq $ mul_assoc _ _ _,
  inv_val := quotient.sound $ r_of_eq $ show s.val * 1 * 1 = 1 * (1 * s.val), by simp }

@[simp] lemma to_units_coe (s : S) :
  ((to_units s) : localization α S) = ((s : α) : localization α S) := rfl

section
variables (α S) (x y : α) (n : ℕ)
@[simp] lemma of_zero : (of 0 : localization α S) = 0 := rfl
@[simp] lemma of_one : (of 1 : localization α S) = 1 := rfl
@[simp] lemma of_add : (of (x + y) : localization α S) = of x + of y :=
by apply is_ring_hom.map_add

@[simp] lemma of_sub : (of (x - y) : localization α S) = of x - of y :=
by apply is_ring_hom.map_sub

@[simp] lemma of_mul : (of (x * y) : localization α S) = of x * of y :=
by apply is_ring_hom.map_mul

@[simp] lemma of_neg : (of (-x) : localization α S) = -of x :=
by apply is_ring_hom.map_neg

@[simp] lemma of_pow : (of (x ^ n) : localization α S) = (of x) ^ n :=
by apply is_semiring_hom.map_pow

@[simp] lemma of_is_unit' (s ∈ S) : is_unit (of s : localization α S) :=
is_unit_unit $ to_units ⟨s, ‹s ∈ S›⟩

@[simp] lemma of_is_unit (s : S) : is_unit (of s : localization α S) :=
is_unit_unit $ to_units s

@[simp] lemma coe_zero : ((0 : α) : localization α S) = 0 := rfl
@[simp] lemma coe_one : ((1 : α) : localization α S) = 1 := rfl
@[simp] lemma coe_add : (↑(x + y) : localization α S) = x + y := of_add _ _ _ _
@[simp] lemma coe_sub : (↑(x - y) : localization α S) = x - y := of_sub _ _ _ _
@[simp] lemma coe_mul : (↑(x * y) : localization α S) = x * y := of_mul _ _ _ _
@[simp] lemma coe_neg : (↑(-x) : localization α S) = -x := of_neg _ _ _
@[simp] lemma coe_pow : (↑(x ^ n) : localization α S) = x ^ n := of_pow _ _ _ _
@[simp] lemma coe_is_unit' (s ∈ S) : is_unit ((s : α) : localization α S) := of_is_unit' _ _ _ ‹s ∈ S›
@[simp] lemma coe_is_unit (s : S) : is_unit ((s : α) : localization α S) := of_is_unit _ _ _
end

lemma mk_self {x : α} {hx : x ∈ S} :
  (mk x ⟨x, hx⟩ : localization α S) = 1 :=
quotient.sound ⟨1, is_submonoid.one_mem,
by simp only [subtype.coe_mk, is_submonoid.coe_one, mul_one, one_mul, sub_self]⟩

lemma mk_self' {s : S} :
  (mk s s : localization α S) = 1 :=
by cases s; exact mk_self

lemma mk_self'' {s : S} :
  (mk s.1 s : localization α S) = 1 :=
mk_self'

-- This lemma does not apply with simp, since (mk r s) simplifies to (r * s⁻¹).
-- However, it could apply with dsimp.
@[simp, nolint simp_nf]
lemma coe_mul_mk (x y : α) (s : S) :
  ↑x * mk y s = mk (x * y) s :=
quotient.sound $ r_of_eq $ by rw one_mul

lemma mk_eq_mul_mk_one (r : α) (s : S) :
  mk r s = r * mk 1 s :=
by rw [coe_mul_mk, mul_one]

-- This lemma does not apply with simp, since (mk r s) simplifies to (r * s⁻¹).
-- However, it could apply with dsimp.
@[simp, nolint simp_nf]
lemma mk_mul_mk (x y : α) (s t : S) :
  mk x s * mk y t = mk (x * y) (s * t) := rfl

lemma mk_mul_cancel_left (r : α) (s : S) :
  mk (↑s * r) s = r :=
by rw [mk_eq_mul_mk_one, mul_comm ↑s, coe_mul,
       mul_assoc, ← mk_eq_mul_mk_one, mk_self', mul_one]

lemma mk_mul_cancel_right (r : α) (s : S) :
  mk (r * s) s = r :=
by rw [mul_comm, mk_mul_cancel_left]

@[simp] lemma mk_eq (r : α) (s : S) :
  mk r s = r * ((to_units s)⁻¹ : units _) :=
quotient.sound $ by simp

@[elab_as_eliminator]
protected theorem induction_on {C : localization α S → Prop} (x : localization α S)
  (ih : ∀ r s, C (mk r s : localization α S)) : C x :=
by rcases x with ⟨r, s⟩; exact ih r s

section
variables {β : Type v} [comm_ring β] {T : set β} [is_submonoid T] (f : α → β) [is_ring_hom f]

@[elab_with_expected_type]
def lift' (g : S → units β) (hg : ∀ s, (g s : β) = f s) (x : localization α S) : β :=
quotient.lift_on x (λ p, f p.1 * ((g p.2)⁻¹ : units β)) $ λ ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨t, hts, ht⟩,
show f r₁ * ↑(g s₁)⁻¹ = f r₂ * ↑(g s₂)⁻¹, from
calc  f r₁ * ↑(g s₁)⁻¹
    = (f r₁ * g s₂ + ((g s₁ * f r₂ - g s₂ * f r₁) * g ⟨t, hts⟩) * ↑(g ⟨t, hts⟩)⁻¹)
      * ↑(g s₁)⁻¹ * ↑(g s₂)⁻¹ :
  by simp only [hg, subtype.coe_mk, (is_ring_hom.map_mul f).symm, (is_ring_hom.map_sub f).symm,
                ht, is_ring_hom.map_zero f, zero_mul, add_zero];
     rw [is_ring_hom.map_mul f, ← hg, mul_right_comm,
         mul_assoc (f r₁), ← units.coe_mul, mul_inv_self];
     rw [units.coe_one, mul_one]
... = f r₂ * ↑(g s₂)⁻¹ :
  by rw [mul_assoc, mul_assoc, ← units.coe_mul, mul_inv_self, units.coe_one,
         mul_one, mul_comm ↑(g s₂), add_sub_cancel'_right];
     rw [mul_comm ↑(g s₁), ← mul_assoc, mul_assoc (f r₂), ← units.coe_mul,
         mul_inv_self, units.coe_one, mul_one]

instance lift'.is_ring_hom (g : S → units β) (hg : ∀ s, (g s : β) = f s) :
  is_ring_hom (localization.lift' f g hg) :=
{ map_one := have g 1 = 1, from units.ext (by rw hg; exact is_ring_hom.map_one f),
    show f 1 * ↑(g 1)⁻¹ = 1, by rw [this, one_inv, units.coe_one, mul_one, is_ring_hom.map_one f],
  map_mul := λ x y, localization.induction_on x $ λ r₁ s₁,
    localization.induction_on y $ λ r₂ s₂,
    have g (s₁ * s₂) = g s₁ * g s₂,
      from units.ext (by simp only [hg, units.coe_mul]; exact is_ring_hom.map_mul f),
    show _ * ↑(g (_ * _))⁻¹ = (_ * _) * (_ * _),
    by simp only [subtype.coe_mk, mul_one, one_mul, subtype.coe_eta, this, mul_inv_rev];
       rw [is_ring_hom.map_mul f, units.coe_mul, ← mul_assoc, ← mul_assoc];
       simp only [mul_right_comm],
  map_add := λ x y, localization.induction_on x $ λ r₁ s₁,
    localization.induction_on y $ λ r₂ s₂,
    have g (s₁ * s₂) = g s₁ * g s₂,
      from units.ext (by simp only [hg, units.coe_mul]; exact is_ring_hom.map_mul f),
    show _ * ↑(g (_ * _))⁻¹ = _ * _ + _ * _,
    by simp only [subtype.coe_mk, mul_one, one_mul, subtype.coe_eta, this, mul_inv_rev];
       simp only [is_ring_hom.map_mul f, is_ring_hom.map_add f, add_mul, (hg _).symm];
       simp only [mul_assoc, mul_comm, mul_left_comm, (units.coe_mul _ _).symm];
       rw [mul_inv_cancel_left, mul_left_comm, ← mul_assoc, mul_inv_cancel_right, add_comm] }

noncomputable def lift (h : ∀ s ∈ S, is_unit (f s)) :
  localization α S → β :=
localization.lift' f (λ s, classical.some $ h s.1 s.2)
  (λ s, by rw [← classical.some_spec (h s.1 s.2)]; refl)

instance lift.is_ring_hom (h : ∀ s ∈ S, is_unit (f s)) :
  is_ring_hom (lift f h) :=
lift'.is_ring_hom _ _ _

-- This lemma does not apply with simp, since (mk r s) simplifies to (r * s⁻¹).
-- However, it could apply with dsimp.
@[simp, nolint simp_nf]
lemma lift'_mk (g : S → units β) (hg : ∀ s, (g s : β) = f s) (r : α) (s : S) :
  lift' f g hg (mk r s) = f r * ↑(g s)⁻¹ := rfl

@[simp] lemma lift'_of (g : S → units β) (hg : ∀ s, (g s : β) = f s) (a : α) :
  lift' f g hg (of a) = f a :=
have g 1 = 1, from units.ext_iff.2 $ by simp [hg, is_ring_hom.map_one f],
by simp [lift', quotient.lift_on_beta, of, mk, this]

@[simp] lemma lift'_coe (g : S → units β) (hg : ∀ s, (g s : β) = f s) (a : α) :
  lift' f g hg a = f a := lift'_of _ _ _ _

@[simp] lemma lift_of (h : ∀ s ∈ S, is_unit (f s)) (a : α) :
  lift f h (of a) = f a := lift'_of _ _ _ _

@[simp] lemma lift_coe (h : ∀ s ∈ S, is_unit (f s)) (a : α) :
  lift f h a = f a := lift'_of _ _ _ _

@[simp] lemma lift'_comp_of (g : S → units β) (hg : ∀ s, (g s : β) = f s) :
  lift' f g hg ∘ of = f := funext $ λ a, lift'_of _ _ _ a

@[simp] lemma lift_comp_of (h : ∀ s ∈ S, is_unit (f s)) :
  lift f h ∘ of = f := lift'_comp_of _ _ _

@[simp] lemma lift'_apply_coe (f : localization α S → β) [is_ring_hom f]
  (g : S → units β) (hg : ∀ s, (g s : β) = f s) :
  lift' (λ a : α, f a) g hg = f :=
have g = (λ s, (units.map' f : units (localization α S) → units β) (to_units s)),
  from funext $ λ x, units.ext $ (hg x).symm ▸ rfl,
funext $ λ x, localization.induction_on x
  (λ r s, by subst this; rw [lift'_mk, ← (units.map' f).map_inv, units.coe_map'];
    simp [is_ring_hom.map_mul f])

@[simp] lemma lift_apply_coe (f : localization α S → β) [is_ring_hom f] :
  lift (λ a : α, f a)
    (λ s hs, is_unit.map' f (is_unit_unit (to_units ⟨s, hs⟩))) = f :=
by rw [lift, lift'_apply_coe]

/-- Function extensionality for localisations:
 two functions are equal if they agree on elements that are coercions.-/
protected lemma funext (f g : localization α S → β) [is_ring_hom f] [is_ring_hom g]
  (h : ∀ a : α, f a = g a) : f = g :=
begin
  rw [← lift_apply_coe f, ← lift_apply_coe g],
  congr' 1,
  exact funext h
end

variables {α S T}

def map (hf : ∀ s ∈ S, f s ∈ T) : localization α S → localization β T :=
lift' (of ∘ f) (to_units ∘ subtype.map f hf) (λ s, rfl)

instance map.is_ring_hom (hf : ∀ s ∈ S, f s ∈ T) : is_ring_hom (map f hf) :=
lift'.is_ring_hom _ _ _

@[simp] lemma map_of (hf : ∀ s ∈ S, f s ∈ T) (a : α) :
  map f hf (of a) = of (f a) := lift'_of _ _ _ _

@[simp] lemma map_coe (hf : ∀ s ∈ S, f s ∈ T) (a : α) :
  map f hf a = (f a) := lift'_of _ _ _ _

@[simp] lemma map_comp_of (hf : ∀ s ∈ S, f s ∈ T) :
  map f hf ∘ of = of ∘ f := funext $ λ a, map_of _ _ _

@[simp] lemma map_id : map id (λ s (hs : s ∈ S), hs) = id :=
localization.funext _ _ $ map_coe _ _

lemma map_comp_map {γ : Type*} [comm_ring γ]  (hf : ∀ s ∈ S, f s ∈ T) (U : set γ)
  [is_submonoid U] (g : β → γ) [is_ring_hom g] (hg : ∀ t ∈ T, g t ∈ U) :
  map g hg ∘ map f hf = map (λ x, g (f x)) (λ s hs, hg _ (hf _ hs)) :=
localization.funext _ _ $ by simp

lemma map_map {γ : Type*} [comm_ring γ]  (hf : ∀ s ∈ S, f s ∈ T) (U : set γ)
  [is_submonoid U] (g : β → γ) [is_ring_hom g] (hg : ∀ t ∈ T, g t ∈ U) (x) :
  map g hg (map f hf x) = map (λ x, g (f x)) (λ s hs, hg _ (hf _ hs)) x :=
congr_fun (map_comp_map _ _ _ _ _) x

def equiv_of_equiv (h₁ : α ≃+* β) (h₂ : h₁ '' S = T) :
  localization α S ≃+* localization β T :=
{ to_fun := map h₁ $ λ s hs, h₂ ▸ set.mem_image_of_mem _ hs,
  inv_fun := map h₁.symm $ λ t ht,
    by simp [h₁.image_eq_preimage, set.preimage, set.ext_iff, *] at *,
  left_inv := λ _, by simp only [map_map, h₁.symm_apply_apply]; erw map_id; refl,
  right_inv := λ _, by simp only [map_map, h₁.apply_symm_apply]; erw map_id; refl,
  map_mul' := λ _ _, is_ring_hom.map_mul _,
  map_add' := λ _ _, is_ring_hom.map_add _ }

end

section away
variables {β : Type v} [comm_ring β] (f : α → β) [is_ring_hom f]

@[reducible] def away (x : α) := localization α (powers x)

@[simp] def away.inv_self (x : α) : away x :=
mk 1 ⟨x, 1, pow_one x⟩

@[elab_with_expected_type]
noncomputable def away.lift {x : α} (hfx : is_unit (f x)) : away x → β :=
localization.lift' f (λ s, classical.some hfx ^ classical.some s.2) $ λ s,
by rw [units.coe_pow, ← classical.some_spec hfx,
       ← is_semiring_hom.map_pow f, classical.some_spec s.2]; refl

instance away.lift.is_ring_hom {x : α} (hfx : is_unit (f x)) :
  is_ring_hom (localization.away.lift f hfx) :=
lift'.is_ring_hom _ _ _

@[simp] lemma away.lift_of {x : α} (hfx : is_unit (f x)) (a : α) :
  away.lift f hfx (of a) = f a := lift'_of _ _ _ _

@[simp] lemma away.lift_coe {x : α} (hfx : is_unit (f x)) (a : α) :
  away.lift f hfx a = f a := lift'_of _ _ _ _

@[simp] lemma away.lift_comp_of {x : α} (hfx : is_unit (f x)) :
  away.lift f hfx ∘ of = f := lift'_comp_of _ _ _

noncomputable def away_to_away_right (x y : α) : away x → away (x * y) :=
localization.away.lift coe $
is_unit_of_mul_eq_one x (y * away.inv_self (x * y)) $
by rw [away.inv_self, coe_mul_mk, coe_mul_mk, mul_one, mk_self]

instance away_to_away_right.is_ring_hom (x y : α) :
  is_ring_hom (away_to_away_right x y) :=
away.lift.is_ring_hom _ _

end away

section at_prime

variables (P : ideal α) [hp : ideal.is_prime P]
include hp

instance prime.is_submonoid :
  is_submonoid (-P : set α) :=
{ one_mem := P.ne_top_iff_one.1 hp.1,
  mul_mem := λ x y hnx hny hxy, or.cases_on (hp.2 hxy) hnx hny }

@[reducible] def at_prime := localization α (-P)

instance at_prime.local_ring : local_ring (at_prime P) :=
local_of_nonunits_ideal
  (λ hze,
    let ⟨t, hts, ht⟩ := quotient.exact hze in
    hts $ have htz : t = 0, by simpa using ht,
      suffices (0:α) ∈ P, by rwa htz,
      P.zero_mem)
  (begin
    rintro ⟨⟨r₁, s₁, hs₁⟩⟩ ⟨⟨r₂, s₂, hs₂⟩⟩ hx hy hu,
    rcases is_unit_iff_exists_inv.1 hu with ⟨⟨⟨r₃, s₃, hs₃⟩⟩, hz⟩,
    rcases quotient.exact hz with ⟨t, hts, ht⟩,
    simp at ht,
    have : ∀ {r s hs}, (⟦⟨r, s, hs⟩⟧ : at_prime P) ∈ nonunits (at_prime P) → r ∈ P,
    { haveI := classical.dec,
      exact λ r s hs, not_imp_comm.1 (λ nr,
        is_unit_iff_exists_inv.2 ⟨⟦⟨s, r, nr⟩⟧,
          quotient.sound $ r_of_eq $ by simp [mul_comm]⟩) },
    have hr₃ := (hp.mem_or_mem_of_mul_eq_zero ht).resolve_right hts,
    have := (ideal.add_mem_iff_left _ _).1 hr₃,
    { exact not_or (mt hp.mem_or_mem (not_or hs₁ hs₂)) hs₃ (hp.mem_or_mem this) },
    { exact P.neg_mem (P.mul_mem_right
        (P.add_mem (P.mul_mem_left (this hy)) (P.mul_mem_left (this hx)))) }
  end)

end at_prime

variable (α)

def non_zero_divisors : set α := {x | ∀ z, z * x = 0 → z = 0}

instance non_zero_divisors.is_submonoid : is_submonoid (non_zero_divisors α) :=
{ one_mem := λ z hz, by rwa mul_one at hz,
  mul_mem := λ x₁ x₂ hx₁ hx₂ z hz,
    have z * x₁ * x₂ = 0, by rwa mul_assoc,
    hx₁ z $ hx₂ (z * x₁) this }

@[simp] lemma non_zero_divisors_one_val : (1 : non_zero_divisors α).val = 1 := rfl

/-- The field of fractions of an integral domain.-/
@[reducible] def fraction_ring := localization α (non_zero_divisors α)

namespace fraction_ring
open function
variables {β : Type u} [integral_domain β]

lemma eq_zero_of_ne_zero_of_mul_eq_zero {x y : β} :
  x ≠ 0 → y * x = 0 → y = 0 :=
λ hnx hxy, or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

lemma mem_non_zero_divisors_iff_ne_zero {x : β} :
  x ∈ non_zero_divisors β ↔ x ≠ 0 :=
⟨λ hm hz, zero_ne_one (hm 1 $ by rw [hz, one_mul]).symm,
 λ hnx z, eq_zero_of_ne_zero_of_mul_eq_zero hnx⟩

variables (β) [de : decidable_eq β]
include de

def inv_aux (x : β × (non_zero_divisors β)) : fraction_ring β :=
if h : x.1 = 0 then 0 else ⟦⟨x.2, x.1, mem_non_zero_divisors_iff_ne_zero.mpr h⟩⟧

instance : has_inv (fraction_ring β) :=
⟨quotient.lift (inv_aux β) $
  λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩,
  begin
    have hrs : s₁ * r₂ = 0 + s₂ * r₁,
      from sub_eq_iff_eq_add.1 (hts _ ht),
    by_cases hr₁ : r₁ = 0;
    by_cases hr₂ : r₂ = 0;
    simp [hr₁, hr₂] at hrs;
    simp only [inv_aux, hr₁, hr₂, dif_pos, dif_neg, not_false_iff, subtype.coe_mk, quotient.eq],
    { exfalso,
      exact mem_non_zero_divisors_iff_ne_zero.mp hs₁ hrs },
    { exfalso,
      exact mem_non_zero_divisors_iff_ne_zero.mp hs₂ hrs },
    { apply r_of_eq,
      simpa [mul_comm] using hrs.symm }
  end⟩

lemma mk_inv {r s} :
  (mk r s : fraction_ring β)⁻¹ =
  if h : r = 0 then 0 else ⟦⟨s, r, mem_non_zero_divisors_iff_ne_zero.mpr h⟩⟧ := rfl

lemma mk_inv' :
  ∀ (x : β × (non_zero_divisors β)), (⟦x⟧⁻¹ : fraction_ring β) =
  if h : x.1 = 0 then 0 else ⟦⟨x.2.val, x.1, mem_non_zero_divisors_iff_ne_zero.mpr h⟩⟧
| ⟨r,s,hs⟩ := rfl

instance : decidable_eq (fraction_ring β) :=
@quotient.decidable_eq (β × non_zero_divisors β) (localization.setoid β (non_zero_divisors β)) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, show decidable (∃ t ∈ non_zero_divisors β, (s₁ * r₂ - s₂ * r₁) * t = 0),
from decidable_of_iff (s₁ * r₂ - s₂ * r₁ = 0)
⟨λ H, ⟨1, λ y, (mul_one y).symm ▸ id, H.symm ▸ zero_mul _⟩,
λ ⟨t, ht1, ht2⟩, or.resolve_right (mul_eq_zero.1 ht2) $ λ ht,
  one_ne_zero (ht1 1 ((one_mul t).symm ▸ ht))⟩

instance : field (fraction_ring β) :=
by refine
{ inv            := has_inv.inv,
  zero_ne_one    := λ hzo,
    let ⟨t, hts, ht⟩ := quotient.exact hzo in
    zero_ne_one (by simpa using hts _ ht : 0 = 1),
  mul_inv_cancel := quotient.ind _,
  inv_zero := dif_pos rfl,
  .. localization.comm_ring };
{ intros x hnx,
  rcases x with ⟨x, z, hz⟩,
  have : x ≠ 0,
    from assume hx, hnx (quotient.sound $ r_of_eq $ by simp [hx]),
  simp only [has_inv.inv, inv_aux, quotient.lift_beta, dif_neg this],
  exact (quotient.sound $ r_of_eq $ by simp [mul_comm]) }

lemma mk_eq_div {r s} : (mk r s : fraction_ring β) = (r / s : fraction_ring β) :=
by simp [div_eq_mul_inv]

variables {β}

@[simp] lemma mk_eq_div' (x : β × (non_zero_divisors β)) :
  (⟦x⟧ : fraction_ring β) = ((x.1) / ((x.2).val) : fraction_ring β) :=
by erw ← mk_eq_div; cases x; refl

lemma eq_zero_of (x : β) (h : (of x : fraction_ring β) = 0) : x = 0 :=
begin
  rcases quotient.exact h with ⟨t, ht, ht'⟩,
  simpa [mem_non_zero_divisors_iff_ne_zero.mp ht] using ht'
end

omit de

lemma of.injective : function.injective (of : β → fraction_ring β) :=
(is_add_group_hom.injective_iff _).mpr $ by { classical, exact eq_zero_of }

section map
open function is_ring_hom
variables {A : Type u} [integral_domain A]
variables {B : Type v} [integral_domain B]
variables (f : A → B) [is_ring_hom f]

def map (hf : injective f) : fraction_ring A → fraction_ring B :=
localization.map f $ λ s h,
  by rw [mem_non_zero_divisors_iff_ne_zero, ← map_zero f, ne.def, hf.eq_iff];
    exact mem_non_zero_divisors_iff_ne_zero.1 h

@[simp] lemma map_of (hf : injective f) (a : A) : map f hf (of a) = of (f a) :=
localization.map_of _ _ _

@[simp] lemma map_coe (hf : injective f) (a : A) : map f hf a = f a :=
localization.map_coe _ _ _

@[simp] lemma map_comp_of (hf : injective f) :
  map f hf ∘ (of : A → fraction_ring A) = (of : B → fraction_ring B) ∘ f :=
localization.map_comp_of _ _

instance map.is_ring_hom (hf : injective f) : is_ring_hom (map f hf) :=
localization.map.is_ring_hom _ _

def equiv_of_equiv (h : A ≃+* B) : fraction_ring A ≃+* fraction_ring B :=
localization.equiv_of_equiv h
begin
  ext b,
  rw [h.image_eq_preimage, set.preimage, set.mem_set_of_eq,
    mem_non_zero_divisors_iff_ne_zero, mem_non_zero_divisors_iff_ne_zero, ne.def],
  exact h.symm.map_ne_zero_iff
end

end map

end fraction_ring

section ideals

theorem map_comap (J : ideal (localization α S)) :
  ideal.map (ring_hom.of coe) (ideal.comap (ring_hom.of (coe : α → localization α S)) J) = J :=
le_antisymm (ideal.map_le_iff_le_comap.2 (le_refl _)) $ λ x,
localization.induction_on x $ λ r s hJ, (submodule.mem_coe _).2 $
mul_one r ▸ coe_mul_mk r 1 s ▸ (ideal.mul_mem_right _ $ ideal.mem_map_of_mem $
have _ := @ideal.mul_mem_left (localization α S) _ _ s _ hJ,
by rwa [coe_coe, coe_mul_mk, mk_mul_cancel_left] at this)

def le_order_embedding :
  ((≤) : ideal (localization α S) → ideal (localization α S) → Prop) ≼o
  ((≤) : ideal α → ideal α → Prop) :=
{ to_fun := λ J, ideal.comap (ring_hom.of coe) J,
  inj'   := function.injective_of_left_inverse (map_comap α),
  ord'   := λ J₁ J₂, ⟨ideal.comap_mono, λ hJ,
    map_comap α J₁ ▸ map_comap α J₂ ▸ ideal.map_mono hJ⟩ }

end ideals

section module
/-! ### `module` section

  Localizations form an algebra over `α` induced by the embedding `coe : α → localization α S`.
-/


variables (α S)

instance : algebra α (localization α S) := (ring_hom.of coe).to_algebra

lemma of_smul (c x : α) : (of (c • x) : localization α S) = c • of x :=
by { simp, refl }

lemma coe_smul (c x : α) : (coe (c • x) : localization α S) = c • coe x :=
of_smul α S c x

lemma coe_mul_eq_smul (c : α) (x : localization α S) : coe c * x = c • x :=
rfl

lemma mul_coe_eq_smul (c : α) (x : localization α S) : x * coe c = c • x :=
mul_comm x (coe c)

/-- The embedding `coe : α → localization α S` induces a linear map. -/
def lin_coe : α →ₗ[α] localization α S := ⟨coe, coe_add α S, coe_smul α S⟩

@[simp] lemma lin_coe_apply (a : α) : lin_coe α S a = coe a := rfl

instance coe_submodules : has_coe (ideal α) (submodule α (localization α S)) :=
⟨submodule.map (lin_coe _ _)⟩

@[simp] lemma of_id (a : α) : (algebra.of_id α (localization α S) : α → localization α S) a = ↑a :=
rfl

end module

section is_integer

/-- `a : localization α S` is an integer if it is an element of the original ring `α` -/
def is_integer (S : set α) [is_submonoid S] (a : localization α S) : Prop :=
a ∈ set.range (coe : α → localization α S)

lemma is_integer_coe (a : α) : is_integer α S a :=
⟨a, rfl⟩

lemma is_integer_add {a b} (ha : is_integer α S a) (hb : is_integer α S b) :
  is_integer α S (a + b) :=
begin
  rcases ha with ⟨a', ha⟩,
  rcases hb with ⟨b', hb⟩,
  use a' + b',
  rw [coe_add, ha, hb]
end

lemma is_integer_mul {a b} (ha : is_integer α S a) (hb : is_integer α S b) :
  is_integer α S (a * b) :=
begin
  rcases ha with ⟨a', ha⟩,
  rcases hb with ⟨b', hb⟩,
  use a' * b',
  rw [coe_mul, ha, hb]
end

lemma is_integer_smul {a : α} {b} (hb : is_integer α S b) :
  is_integer α S (a • b) :=
begin
  rcases hb with ⟨b', hb⟩,
  use a * b',
  rw [←hb, ←coe_smul, smul_eq_mul]
end

end is_integer

end localization
