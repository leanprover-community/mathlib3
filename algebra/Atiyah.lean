import algebra.ring algebra.field data.set.basic order.zorn tactic.norm_num tactic.ring

universes u v w

-- page 1

class zero_ring (α : Type u) [comm_ring α] : Prop :=
(eq_zero : ∀ x:α, x = 0)

instance zero_ring_of_zero_eq_one {α : Type u} [comm_ring α] : (0:α)=1 → zero_ring α
| h := ⟨λ x, calc
  x = x * 1   : by simp
  ... = x * 0 : by rw h
  ... = 0     : by simp⟩


-- page 2

class is_hom {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] (f : α → β) : Prop :=
(map_add : ∀ {x y}, f (x + y) = f x + f y)
(map_mul : ∀ {x y}, f (x * y) = f x * f y)
(map_one : f 1 = 1)

namespace is_hom

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables (f : α → β) [is_hom f] {x y : α}

attribute [simp] map_add
attribute [simp] map_mul
attribute [simp] map_one

@[simp] lemma map_zero : f 0 = 0 :=
calc f 0 = f (0 + 0) - f 0 : by rw [map_add f]; simp
     ... = 0 : by simp

@[simp] lemma map_neg : f (-x) = -f x :=
calc f (-x) = f (-x + x) - f x : by rw [map_add f]; simp
        ... = -f x : by simp [map_zero f]

@[simp] lemma map_sub : f (x - y) = f x - f y :=
by simp [map_add f, map_neg f]

end is_hom

class subring (α : Type u) [comm_ring α] (S : set α) : Prop :=
(add_mem : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S)
(neg_mem : ∀ {x}, x ∈ S → -x ∈ S)
(mul_mem : ∀ {x y}, x ∈ S → y ∈ S → x * y ∈ S)
(one_mem : (1:α) ∈ S)

namespace subring

variables (α : Type u) [comm_ring α] (S : set α) [subring α S]

instance : comm_ring S :=
{ add            := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x + y, add_mem hx hy⟩,
  add_assoc      := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ add_assoc x y z,
  zero           := ⟨0, eq.subst (add_neg_self (1:α)) $ add_mem (one_mem S) $ neg_mem $ one_mem S⟩,
  zero_add       := λ ⟨x, hx⟩, subtype.eq $ zero_add x,
  add_zero       := λ ⟨x, hx⟩, subtype.eq $ add_zero x,
  neg            := λ ⟨x, hx⟩, ⟨-x, neg_mem hx⟩,
  add_left_neg   := λ ⟨x, hx⟩, subtype.eq $ add_left_neg x,
  add_comm       := λ ⟨x, hx⟩ ⟨y, hy⟩, subtype.eq $ add_comm x y,
  mul            := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x * y, mul_mem hx hy⟩,
  mul_assoc      := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ mul_assoc x y z,
  one            := ⟨1, one_mem S⟩,
  one_mul        := λ ⟨x, hx⟩, subtype.eq $ one_mul x,
  mul_one        := λ ⟨x, hx⟩, subtype.eq $ mul_one x,
  left_distrib   := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ left_distrib x y z,
  right_distrib  := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ right_distrib x y z,
  mul_comm       := λ ⟨x, hx⟩ ⟨y, hy⟩, subtype.eq $ mul_comm x y }

@[simp] lemma add (x y : α) (hx : x ∈ S) (hy : y ∈ S) :
(⟨x, hx⟩ : S) + ⟨y, hy⟩ = ⟨x + y, add_mem hx hy⟩ := rfl

@[simp] lemma mul (x y : α) (hx : x ∈ S) (hy : y ∈ S) :
(⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩ := rfl

instance is_hom : is_hom ((λ x, x) : S → α) :=
{ map_add := λ x y, by cases x; cases y; refl,
  map_mul := λ x y, by cases x; cases y; refl,
  map_one := rfl }

end subring

instance is_hom.comp (α : Type u) (β : Type v) (γ : Type w)
[comm_ring α] [comm_ring β] [comm_ring γ]
(g : β → γ) (f : α → β) [is_hom g] [is_hom f] : is_hom (g ∘ f) :=
{ map_add := λ x y, by simp [function.comp, is_hom.map_add f, is_hom.map_add g],
  map_mul := λ x y, by simp [function.comp, is_hom.map_mul f, is_hom.map_mul g],
  map_one := by simp [function.comp, is_hom.map_one f, is_hom.map_one g] }

class is_ideal (α : Type u) [comm_ring α] (S : set α) : Prop :=
(zero_mem : (0 : α) ∈ S)
(add_mem : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S)
(mul_mem : ∀ {x y}, x ∈ S → x * y ∈ S)

namespace is_ideal

variables {α : Type u} [comm_ring α] {S : set α} [is_ideal α S] {x y z : α}
include S

attribute [simp] zero_mem
lemma neg_mem : x ∈ S → -x ∈ S :=
λ hx, have h : x * -1 ∈ S, from is_ideal.mul_mem hx, by simpa using h
lemma sub_mem : x ∈ S → y ∈ S → x - y ∈ S :=
λ hx hy, have h : x + -y ∈ S, from add_mem hx $ neg_mem hy, by simpa using h

variables (S x y z)

@[simp, reducible] def r : α → α → Prop :=
λ x y, x - y ∈ S

lemma refl : r S x x :=
by simp [sub_self]

lemma symm : r S x y → r S y x :=
λ hxy, have h : -(x - y) ∈ S, from neg_mem hxy, by simpa using h

lemma trans : r S x y → r S y z → r S x z :=
λ hxy hyz, have h : (x - y) + (y - z) ∈ S, from add_mem hxy hyz, by simpa using h

instance : setoid α :=
⟨r S, refl S, symm S, trans S⟩

variables (α)

@[simp, reducible] def coset := quotient (is_ideal.setoid S)

variables {α}

instance : comm_ring (quotient (is_ideal.setoid S)) :=
by refine
{ add            := quotient.lift₂ (λ m n, ⟦m + n⟧) (λ m₁ m₂ n₁ n₂ h₁ h₂, quot.sound $ calc
    (m₁ + m₂) - (n₁ + n₂) = (m₁ - n₁) + (m₂ - n₂) : by norm_num
                      ... ∈ S                     : add_mem h₁ h₂),
  add_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  zero           := ⟦0⟧,
  zero_add       := quotient.ind _,
  add_zero       := quotient.ind _,
  neg            := quotient.lift (λ m, ⟦-m⟧) (λ m n h, quot.sound $ calc
    (-m) - (-n) = (m - n)*-1 : by norm_num
            ... ∈ S          : mul_mem h),
  add_left_neg   := quotient.ind _,
  add_comm       := quotient.ind₂ _,
  mul            := quotient.lift₂ (λ m n, ⟦m * n⟧) (λ m₁ m₂ n₁ n₂ h₁ h₂, quot.sound $ calc
    (m₁ * m₂) - (n₁ * n₂) = (m₂ - n₂) * m₁ + (m₁ - n₁) * n₂ : by ring
                      ... ∈ S : add_mem (mul_mem h₂) (mul_mem h₁)),
  mul_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  one            := ⟦1⟧,
  one_mul        := quotient.ind _,
  mul_one        := quotient.ind _,
  left_distrib   := λ m n k, quotient.induction_on₃ m n k _,
  right_distrib  := λ m n k, quotient.induction_on₃ m n k _,
  mul_comm       := quotient.ind₂ _ };
{ intros, apply quotient.sound, ring }

@[reducible] def to_coset (x : α) : coset α S := quotient.mk x

instance to_quotient : is_hom (to_coset S) :=
by refine {..}; intros; refl

infix / := coset

variable {S}

@[simp] lemma sub_mem_iff_r : x ≈ y ↔ x - y ∈ S := iff.refl _
@[simp] lemma sub_mem_iff_coset_eq : ⟦x⟧ = ⟦y⟧ ↔ x - y ∈ S :=
by rw quotient.eq; exact sub_mem_iff_r x y

variable S

@[simp] lemma add_coset : ⟦x⟧ + ⟦y⟧ = ⟦x + y⟧ := rfl
@[simp] lemma sub_coset : ⟦x⟧ - ⟦y⟧ = ⟦x - y⟧ := rfl
@[simp] lemma mul_coset : ⟦x⟧ * ⟦y⟧ = ⟦x * y⟧ := rfl
@[simp] lemma neg_coset : -⟦x⟧ = ⟦-x⟧ := rfl
@[simp] lemma one_coset : (1:α/S) = ⟦(1:α)⟧ := rfl

lemma coset_zero_of_mem : x ∈ S → ⟦x⟧ = 0 :=
λ hx, quotient.sound $ by simp [hx]

lemma mem_of_coset_zero : ⟦x⟧ = 0 → x ∈ S :=
λ hx, by simpa using quotient.exact hx

lemma mem_iff_coset_zero : x ∈ S ↔ ⟦x⟧ = 0 :=
⟨coset_zero_of_mem S x, mem_of_coset_zero S x⟩

lemma coset_zero_iff_mem : ⟦x⟧ = 0 ↔ x ∈ S :=
⟨mem_of_coset_zero S x, coset_zero_of_mem S x⟩

variable {S}

theorem coset_rep (x : α/S) : ∃ y, ⟦y⟧ = x := quotient.exists_rep x

end is_ideal


@[reducible] def zero_ideal (α : Type u) [comm_ring α] : set α := {(0:α)}
instance zero_ideal.is_ideal (α : Type u) [comm_ring α] : is_ideal α $ zero_ideal α :=
by refine {..}; intros; simp [mem_singleton_iff] at *; simp [*]

@[reducible] def univ_ideal (α : Type u) [comm_ring α] : set α := set.univ
instance univ_ideal.is_ideal (α : Type u) [comm_ring α] : is_ideal α $ univ_ideal α :=
by refine {..}; intros; trivial

instance is_ideal.hom_preimage {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
(f : α → β) [is_hom f] (S : set β) [is_ideal β S] : is_ideal α (f ⁻¹' S) :=
{ zero_mem := by simp [is_hom.map_zero f],
  add_mem  := λ x y (hx : f x ∈ S) hy, by simp [is_hom.map_add f, is_ideal.add_mem hx hy],
  mul_mem  := λ x y (hx : f x ∈ S), by simp [is_hom.map_mul f, is_ideal.mul_mem hx] }

-- Proposition 1.1 start

section prop_1_1

variables {α : Type u} [comm_ring α] (S : set α) [is_ideal α S]
variables (T T₁ T₂ : set α) [is_ideal α T] [is_ideal α T₁] [is_ideal α T₂]
variables (T' : set (α/S)) [is_ideal (α/S) T']

@[reducible] def ideal_to_quotient : set (α/S) := is_ideal.to_coset S '' T
@[reducible] def quotient_to_ideal : set α := is_ideal.to_coset S ⁻¹' T'

instance ideal_to_quotient.is_ideal : is_ideal (α/S) (ideal_to_quotient S T) :=
{ zero_mem := ⟨0, is_ideal.zero_mem T, rfl⟩,
  add_mem  := λ x y ⟨m, hm1, hm2⟩ ⟨n, hn1, hn2⟩,
    ⟨m + n, is_ideal.add_mem hm1 hn1, by rw [← hm2, ← hn2]; refl⟩,
  mul_mem  := λ x y ⟨m, hm1, hm2⟩,
    let ⟨n, hn⟩ := is_ideal.coset_rep y in
      ⟨m * n, is_ideal.mul_mem hm1, by rw [← hm2, ← hn]; refl⟩ }

def quotient_to_ideal.is_ideal : is_ideal α (quotient_to_ideal S T') :=
is_ideal.hom_preimage (is_ideal.to_coset S) T'

theorem quotient_to_ideal.contains : S ⊆ quotient_to_ideal S T' :=
λ x hx, calc ⟦x⟧ = 0 : is_ideal.coset_zero_of_mem S x hx
             ... ∈ T' : is_ideal.zero_mem T'

theorem contains_to_quotient_to_contains : S ⊆ T → quotient_to_ideal S (ideal_to_quotient S T) = T :=
λ h, set.ext $ λ x,
  ⟨λ ⟨z, hz1, hz2⟩, by simpa using (is_ideal.sub_mem hz1 $ h (by simpa using hz2 : z - x ∈ S)),
   λ hx, ⟨x, hx, rfl⟩⟩

theorem quotient_to_contains_to_quotient : ideal_to_quotient S (quotient_to_ideal S T') = T' :=
set.ext $ λ x,
  ⟨λ ⟨z, hz1, hz2⟩, by rwa ← hz2,
   λ hx, let ⟨z, hz⟩ := is_ideal.coset_rep x in ⟨z, by rwa ← hz at hx, hz⟩⟩

theorem ideal_to_quotient.subset : T₁ ⊆ T₂ → ideal_to_quotient S T₁ ⊆ ideal_to_quotient S T₂ :=
λ h z ⟨w, hw1, hw2⟩, ⟨w, h hw1, hw2⟩

theorem ideal_to_quotient.univ : ideal_to_quotient S (univ_ideal α) = univ_ideal (α/S) :=
set.ext $ λ x, ⟨λ hx, trivial, λ hx, by simpa using is_ideal.coset_rep x⟩

theorem quotient_to_ideal.subset (T₁ : set (α/S)) [is_ideal (α/S) T₁] (T₂ : set (α/S)) [is_ideal (α/S) T₂] :
  T₁ ⊆ T₂ → quotient_to_ideal S T₁ ⊆ quotient_to_ideal S T₂ :=
λ h z hz, h hz

theorem quotient_to_ideal.zero : quotient_to_ideal S (zero_ideal $ α/S) = S :=
set.ext $ λ x, by simp [is_ideal.coset_zero_iff_mem S x]

theorem quotient_to_ideal.univ : quotient_to_ideal S (univ_ideal $ α/S) = univ_ideal α :=
set.ext $ λ x, ⟨λ hx, trivial, λ hx, trivial⟩

end prop_1_1

-- Proposition 1.1 end

namespace is_hom

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] (f : α → β) [is_hom f]

@[reducible] def ker : set α := f⁻¹' (zero_ideal β)
instance ker.is_ideal : is_ideal α (ker f) := is_ideal.hom_preimage f $ zero_ideal β

@[reducible] def im : set β := { y | ∃ x, f x = y }
instance im.subring : subring β (im f) :=
{ add_mem := λ x y ⟨m, hm⟩ ⟨n, hn⟩, ⟨m + n, by simp [map_add f, hm, hn]⟩,
  neg_mem := λ x ⟨m, hm⟩, ⟨-m, by simp [map_neg f, hm]⟩,
  mul_mem := λ x y ⟨m, hm⟩ ⟨n, hn⟩, ⟨m * n, by simp [map_mul f, hm, hn]⟩,
  one_mem := ⟨(1:α), map_one f⟩ }

instance im.comm_ring : comm_ring (im f) := subring.comm_ring β (im f)

end is_hom

structure isomorphism (α : Type u) (β : Type v) [comm_ring α] [comm_ring β] :=
(f : α → β) (hf : is_hom f)
(g : β → α) (hg : is_hom g)
(hfg : ∀ x, f (g x) = x)
(hgf : ∀ x, g (f x) = x)

infix `≅`:70 := isomorphism

@[simp] lemma quotient.lift_beta {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift f h (quotient.mk x) = f x := rfl

@[simp] lemma quotient.lift_on_beta {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift_on (quotient.mk x) f h = f x := rfl

noncomputable def first_isom (α : Type u) (β : Type v) [comm_ring α] [comm_ring β] (f : α → β) [is_hom f] :
(α / (is_hom.ker f)) ≅ (is_hom.im f) :=
{ f := λ x, quotient.lift_on x (λ x, ⟨f x, x, rfl⟩ : α → is_hom.im f) (λ x y hxy, subtype.eq $ calc
    f x = f (y + (x - y)) : by norm_num
    ... = f y + f (x - y) : is_hom.map_add f
    ... = f y             : by simp [has_equiv.equiv, setoid.r] at hxy; simp [hxy]),
  hf :=
    { map_add := λ x y, quotient.induction_on₂ x y (λ m n, by simp [is_hom.map_add f]; refl),
      map_mul := λ x y, quotient.induction_on₂ x y (λ m n, by simp [is_hom.map_mul f]; refl),
      map_one := by simp [is_hom.map_one f]; refl },
  g := λ ⟨y, hy⟩, ⟦classical.some hy⟧,
  hg :=
    { map_add :=
        begin
          intros x y,
          cases x with x hx,
          cases y with y hy,
          simp [first_isom._match_1],
          have hm := classical.some_spec hx,
          have hn := classical.some_spec hy,
          have hmn := classical.some_spec (subring.add_mem hx hy),
          simp [is_hom.map_add f, is_hom.map_neg f, hm, hn, hmn]
        end,
      map_mul :=
        begin
          intros x y,
          cases x with x hx,
          cases y with y hy,
          simp [first_isom._match_1],
          have hm := classical.some_spec hx,
          have hn := classical.some_spec hy,
          have hmn := classical.some_spec (subring.mul_mem hx hy),
          simp [is_hom.map_add f, is_hom.map_neg f, is_hom.map_mul f, hm, hn, hmn]
        end,
      map_one :=
        begin
          apply quotient.sound,
          have h := classical.some_spec (subring.one_mem $ is_hom.im f),
          simp [is_hom.map_add f, is_hom.map_neg f, h, is_hom.map_one f]
        end },
  hfg := λ ⟨x, hx⟩, subtype.eq (by simp [first_isom._match_1]; simpa using classical.some_spec hx),
  hgf :=
    begin
      intro x,
      cases is_ideal.coset_rep x with y hy,
      rw ← hy,
      simp [first_isom._match_1],
      have hz := @classical.some_spec _ (λ z, f z = f y) ⟨y, rfl⟩,
      simp [is_hom.map_add f, hz, is_hom.map_neg f]
    end
}

local infix `^` := monoid.pow

def nilpotents (α : Type u) [comm_ring α] : set α := { x | ∃ n, x^(nat.succ n) = 0 }
def is_unit {α : Type u} [comm_ring α] (x : α) := ∃ y, x * y = 1
def nonunits (α : Type u) [comm_ring α] : set α := { x | ¬∃ y, x * y = 1 }


-- page 3

section principal_ideal

variables {α : Type u} [comm_ring α] (x : α)

def principal_ideal : set α := { y | ∃ z, x * z = y }

instance principal_ideal.is_ideal : is_ideal α $ principal_ideal x :=
{ zero_mem := ⟨0, mul_zero x⟩,
  add_mem  := λ y₁ y₂ ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩, ⟨z₁ + z₂, by simp [left_distrib, hz₁, hz₂]⟩,
  mul_mem  := λ y₁ y₂ ⟨z₁, hz₁⟩, ⟨z₁ * y₂, by simp [hz₁.symm, mul_assoc]⟩ }

variable (α)

theorem principal_ideal_one_eq_univ : principal_ideal (1:α) = univ_ideal α :=
set.ext $ λ x, ⟨λ hx, trivial, λ hx, ⟨x, one_mul x⟩⟩

variable {α}

@[simp] lemma mem_principal_ideal : x ∈ principal_ideal x :=
⟨1, mul_one x⟩

theorem unit_iff_principal_ideal_eq_one : is_unit x ↔ principal_ideal x = principal_ideal 1 :=
⟨λ ⟨y, hy⟩, set.ext $ λ z, ⟨λ hz, ⟨z, one_mul z⟩, λ hz, ⟨y * z, by rw [← mul_assoc, hy, one_mul]⟩⟩,
 λ hx, show (1:α) ∈ principal_ideal x, by simp [hx]⟩

variable {x}

theorem principal_ideal.subset_of_mem {S : set α} [is_ideal α S] : x ∈ S → principal_ideal x ⊆ S :=
λ h z ⟨w, hw⟩, set.mem_of_eq_of_mem hw.symm $ is_ideal.mul_mem h

variable (α)

theorem principal_ideal_zero_eq_zero_ideal : principal_ideal (0:α) = zero_ideal α :=
set.ext $ λ x, ⟨λ ⟨y, hy⟩, by rw [← hy]; simpa [zero_mul], λ hx, ⟨0, by rw [eq_of_mem_singleton hx, zero_mul]⟩⟩

end principal_ideal

theorem is_ideal.eq_univ_of_contains_unit {α : Type u} [comm_ring α] (S : set α) [is_ideal α S] :
(∃ x:α, x ∈ S ∧ is_unit x) → S = set.univ :=
λ ⟨x, hx, y, hy⟩, set.ext $ λ z, ⟨λ hz, trivial, λ hz, calc
   z = (x * y) * z : by simp [hy]
 ... = x * (y * z) : mul_assoc x y z
 ... ∈ S : is_ideal.mul_mem hx⟩

theorem is_ideal.univ_of_one_mem {α : Type u} [comm_ring α] (S : set α) [is_ideal α S] :
(1:α) ∈ S → S = set.univ :=
λ h, set.ext $ λ z, ⟨λ hz, trivial, λ hz, by simpa using (is_ideal.mul_mem h : 1 * z ∈ S)⟩


-- Proposition 1.2 start

section prop_1_2

variables (α : Type u) [comm_ring α] (zero_ne_one : (0:α) ≠ 1)

class is_field : Prop :=
(h : ∀ {x:α}, x ≠ 0 → is_unit x)
(zero_ne_one : (0:α) ≠ 1)

class ideal_eq_zero_or_univ : Prop :=
(h : ∀ (S : set α) [is_ideal α S], S = zero_ideal α ∨ S = univ_ideal α)

class hom_inj : Prop :=
(h : ∀ (β : Type u) [comm_ring β] (zero_ne_one₂ : (0:β) ≠ 1) (f : α → β) [is_hom f] (x y : α), f x = f y → x = y)

include zero_ne_one

theorem is_field.to_ideal_eq_zero_or_univ : is_field α → ideal_eq_zero_or_univ α :=
begin
  intro hf,
  cases hf,
  constructor,
  intros S _,
  cases classical.em (∃ x, x ≠ (0:α) ∧ x ∈ S),
  right,
  cases h with x hx,
  apply is_ideal.eq_univ_of_contains_unit S,
  exact ⟨x, hx.2, hf_h hx.1⟩,
  left,
  apply set.ext,
  intro x,
  split,
  intro hx,
  apply mem_singleton_of_eq,
  apply @of_not_not _ (classical.prop_decidable _),
  intro hnx,
  exact h ⟨x, hnx, hx⟩,
  intro hx,
  unfold zero_ideal at hx,
  rw mem_singleton_iff at hx,
  rw hx,
  exact is_ideal.zero_mem S
end

theorem ideal_eq_zero_or_univ.to_hom_inj : ideal_eq_zero_or_univ α → hom_inj α :=
λ ⟨h⟩, ⟨λ β _ hne f _ x y hxy, begin
  cases h (is_hom.ker f) with hkz hku,
  { have : x - y ∈ is_hom.ker f,
    { by simp [is_hom.ker, is_hom.map_add f, is_hom.map_neg f, hxy] },
    simpa [hkz, add_neg_eq_zero] using this },
  { have : (1:α) ∈ is_hom.ker f,
    { by rw hku; trivial },
    simp [is_hom.map_one f] at this,
    cc }
end⟩

theorem hom_inj.to_is_field : hom_inj α → is_field α :=
begin
  intro h,
  cases h,
  constructor,
  intros x hx,
  specialize h (α / principal_ideal x),
  cases classical.em ((0 : α / principal_ideal x) = 1) with h1 h1,
  have := @quotient.exact _ (is_ideal.setoid $ principal_ideal x) _ _ h1,
  change (0:α) - 1 ∈ principal_ideal x at this,
  have : (1:α) ∈ principal_ideal x := calc
    (1:α) = (0 - 1) * (-1) : by norm_num
      ... ∈ principal_ideal x : is_ideal.mul_mem this,
  exact this,
  specialize @h h1 _ (is_ideal.to_quotient $ principal_ideal x) x 0,
  exfalso,
  apply hx,
  apply h,
  apply is_ideal.coset_zero_of_mem,
  exact mem_principal_ideal x,
  exact zero_ne_one
end

end prop_1_2

-- Proposition 1.2 end


section prime_ideals_and_maximal_ideals

variables {α : Type u} [comm_ring α] (S : set α) [is_ideal α S]

class is_prime_ideal : Prop :=
(ne_univ_ideal : S ≠ univ_ideal α)
(mem_or_mem_of_mul_mem : ∀ {x y : α}, x * y ∈ S → x ∈ S ∨ y ∈ S)

class is_maximal_ideal : Prop :=
(ne_univ_ideal : S ≠ univ_ideal α)
(no_between : ∀ (T : set α) [is_ideal α T], S ⊆ T → T = S ∨ T = univ_ideal α)

variable α

class is_integral_domain : Prop :=
(zero_ne_one : 0 ≠ (1:α))
(zero_or_zero_of_mul_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0)

variable {α}

theorem prime_iff_quotient_integral_domain : is_prime_ideal S ↔ is_integral_domain (α/S) :=
⟨λ ⟨hne, hmul⟩,
   ⟨λ hzo, hne $ is_ideal.univ_of_one_mem S 
      (by simpa [is_ideal.mem_iff_coset_zero S] using hzo.symm),
    λ x y, let ⟨m, hm⟩ := is_ideal.coset_rep x,
               ⟨n, hn⟩ := is_ideal.coset_rep y in
      by rw [← hm, ← hn]; simpa [is_ideal.coset_zero_iff_mem S] using hmul⟩,
 λ ⟨hne, hmul⟩,
   ⟨λ hsu, hne $ eq.symm $ is_ideal.coset_zero_of_mem S 1 $ by rw hsu; trivial,
    λ x y, by simpa [is_ideal.mem_iff_coset_zero S] using hmul ⟦x⟧ ⟦y⟧⟩⟩

theorem maximal_iff_quotient_field : is_maximal_ideal S ↔ is_field (α/S) :=
begin
  split,
  intro h,
  cases h,
  have zero_ne_one : (0:α/S) ≠ 1,
    intro hz,
    apply h_ne_univ_ideal,
    apply is_ideal.univ_of_one_mem S,
    exact is_ideal.mem_of_coset_zero S 1 hz.symm,
  apply hom_inj.to_is_field _ zero_ne_one,
  apply ideal_eq_zero_or_univ.to_hom_inj _ zero_ne_one,
  constructor,
  intros T _,
  specialize h_no_between (quotient_to_ideal S T) (quotient_to_ideal.contains S T),
  cases h_no_between with h h;
    rw [set.set_eq_def, quotient_to_ideal, set.preimage, set_of] at h,
  left,
    apply set.ext,
    intro x,
    rw mem_singleton_iff,
    cases is_ideal.coset_rep x with y hy,
    rw ← hy at *,
    specialize h y,
    rwa is_ideal.coset_zero_iff_mem,
  right,
    apply set.ext,
    intro x,
    cases is_ideal.coset_rep x with y hy,
    rw ← hy at *,
    specialize h y,
    simpa using h,
  intro h,
  have h2 := is_field.to_ideal_eq_zero_or_univ (α/S) h.2 h,
  cases h2,
  constructor,
  intro h3,
  apply h.2.symm,
  apply is_ideal.coset_zero_of_mem,
  rw h3,
  constructor,
  intros T _ hs,
  specialize h2 (ideal_to_quotient S T),
  cases h2;
    unfold ideal_to_quotient at h2,
  left,
    apply set.ext,
    rw set.set_eq_def at h2,
    simp at h2,
    intro x,
    specialize h2 (is_ideal.to_coset S x),
    simp [is_ideal.to_coset] at h2,
    rw is_ideal.coset_zero_iff_mem at h2,
    split,
    intro hx,
    rw ← h2,
    exact ⟨x, hx, @setoid.refl _ (is_ideal.setoid S) x⟩,
    exact λ hx, hs hx,
  right,
    apply set.ext,
    intro x,
    rw set.set_eq_def at h2,
    simp at *,
    specialize h2 (is_ideal.to_coset S x),
    cases h2 with y hy,
    cases hy with hy1 hy2,
    rw ← sub_eq_zero at hy2,
    simp at hy2,
    calc x = y - (y + -x) : by norm_num
       ... ∈ T : is_ideal.sub_mem hy1 (hs $ is_ideal.mem_of_coset_zero _ _ hy2)
end

variable α

def quotient_zero_isomorphism : α/(zero_ideal α) ≅ α :=
{ f   := @quotient.lift α α (is_ideal.setoid $ zero_ideal α) id
    (λ x y hxy, by simpa [add_neg_eq_zero] using hxy),
  g   := is_ideal.to_coset (zero_ideal α),
  hf  := by refine
    { map_add := λ x y, _,
      map_mul := λ x y, _,
      map_one := rfl };
    { cases is_ideal.coset_rep x with m hm,
      cases is_ideal.coset_rep y with n hn,
      rw [← hm, ← hn],
      simp },
  hg  := is_ideal.to_quotient (zero_ideal α),
  hfg := λ x, rfl,
  hgf := λ x, let ⟨m, hm⟩ := is_ideal.coset_rep x in
    by rw ← hm; refl }

def zero_prime_iff_integral_domain : is_prime_ideal (zero_ideal α) ↔ is_integral_domain α :=
⟨λ ⟨hne, hmul⟩, ⟨λ hzo, hne $ set.ext $ by simpa using (zero_ring_of_zero_eq_one hzo).eq_zero,
   λ x y, by simpa using hmul⟩,
 λ ⟨hne, hmul⟩, ⟨λ hzu, hne $ by simp [set.set_eq_def] at hzu; rw hzu 1, by simpa⟩⟩

instance is_prime_ideal.hom_preimage {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
(f : α → β) [is_hom f] (S : set β) [is_ideal β S] [is_prime_ideal S] :
  @is_prime_ideal α _ ((f)⁻¹' S) (is_ideal.hom_preimage f S) :=
let ⟨hnu, hmul⟩ := _inst_7 in
⟨λ h, have (1:α) ∈ f ⁻¹' S, by rw h; trivial,
   hnu $ is_ideal.univ_of_one_mem S $ by simpa [is_hom.map_one f] using this,
 λ x y, by simpa [is_hom.map_mul f] using hmul⟩

theorem is_field.to_is_integral_domain : is_field α → is_integral_domain α :=
begin
  intro h,
  cases h,
  constructor,
  exact h_zero_ne_one,
  intros x y hxy,
  rw @@or_iff_not_and_not (classical.prop_decidable _) (classical.prop_decidable _),
  intro h,
  cases h with hx hy,
  apply hx,
  specialize h_h hy,
  cases h_h with z hz,
  exact calc
      x = x * 1 : eq.symm (mul_one x)
    ... = x * (y * z) : congr_arg _ hz.symm
    ... = (x * y) * z : eq.symm (mul_assoc x y z)
    ... = 0 * z : congr_arg (λ m, m * z) hxy
    ... = 0 : zero_mul z
end

variable {α}

theorem is_maximal_ideal.to_is_prime_ideal : is_maximal_ideal S → is_prime_ideal S :=
by rw [maximal_iff_quotient_field, prime_iff_quotient_integral_domain]; exact is_field.to_is_integral_domain (α/S)

theorem not_unit_of_mem_maximal_ideal : is_maximal_ideal S → S ⊆ nonunits α :=
λ hs x hx hxy, @@is_maximal_ideal.ne_univ_ideal _ S _ hs $ is_ideal.eq_univ_of_contains_unit S ⟨x, hx, hxy⟩

end prime_ideals_and_maximal_ideals

-- Proposition 1.3 start

section prop_1_3

variables (α : Type u) [comm_ring α]

def ideals : set (set α) := { S | is_ideal α S }

instance ideals.sUnion (A : set (set α)) (h : A ⊆ ideals α) (S : set α) (hs : S ∈ A)
(total : ∀ {T₁ T₂ : set α}, T₁ ∈ A → T₂ ∈ A → T₁ ⊆ T₂ ∨ T₂ ⊆ T₁) : ⋃₀ A ∈ ideals α :=
{ zero_mem := ⟨S, hs, @@is_ideal.zero_mem _ S (h hs)⟩,
  add_mem  := λ x y ⟨T₁, ht₁, hx⟩ ⟨T₂, ht₂, hy⟩,
    or.cases_on (total ht₁ ht₂)
    (λ ht12, ⟨T₂, ht₂, @is_ideal.add_mem _ _ T₂ (h ht₂) x y (ht12 hx) hy⟩)
    (λ ht21, ⟨T₁, ht₁, @is_ideal.add_mem _ _ T₁ (h ht₁) x y hx (ht21 hy)⟩),
  mul_mem  := λ x y ⟨T₁, ht₁, hx⟩,
    ⟨T₁, ht₁, @is_ideal.mul_mem _ _ T₁ (h ht₁) x y hx⟩ }

def ideals_not_univ : set (set α) := { S | is_ideal α S ∧ (1:α) ∉ S }

theorem ideals_not_univ.sUnion (A : set (set α)) (h : A ⊆ ideals_not_univ α) (S : set α) (hs : S ∈ A)
(total : ∀ {T₁ T₂ : set α}, T₁ ∈ A → T₂ ∈ A → T₁ ⊆ T₂ ∨ T₂ ⊆ T₁) : ⋃₀ A ∈ ideals_not_univ α :=
⟨ideals.sUnion α A (λ i hi, and.elim_left $ h hi) S hs (λ T₁ T₂ ht₁ ht₂, total ht₁ ht₂),
   λ ⟨T, ht, ht2⟩, (h ht).2 ht2⟩

theorem zero_ne_one.to_maximal_ideal : (0:α) ≠ 1 → ∃ (S : set α) (hs : is_ideal α S), @is_maximal_ideal _ _ S hs :=
begin
  intro hz,
  have z := @zorn.zorn,
  specialize @z (ideals_not_univ α),
  specialize @z (λ T₁ T₂, T₁.1 ⊆ T₂.1),
  specialize z (λ c hc,
    begin
      simp [zorn.chain, set.pairwise_on] at hc,
      let U : set (set α) := { S | ∃ T : ideals_not_univ α, T ∈ c ∧ T.1 = S },
      have hu := ideals_not_univ.sUnion α U,
      specialize hu (λ S ⟨⟨T, ht⟩, _, hts⟩, by rwa ← hts),
      cases classical.em (∃ S, S ∈ c) with h h,
      cases h with S h,
      cases S with S hs,
      specialize hu S ⟨⟨S, hs⟩, h, rfl⟩,
      specialize hu (λ T₁ T₂ ⟨⟨t₁, ht1⟩, htc1, hts1⟩ ⟨⟨t₂, ht2⟩, htc2, hts2⟩,
        begin
          specialize hc t₁ ht1 htc1 t₂ ht2 htc2,
          rw [← hts1, ← hts2] at *,
          cases classical.em (subtype.mk t₁ ht1 = subtype.mk t₂ ht2) with ht12 ht12,
          have := subtype.mk.inj ht12,
          rw set.set_eq_def at this,
          left, exact (λ x hx, (this x).1 hx),
          specialize hc ht12,
          exact hc
        end),
      let ub : ↥(ideals_not_univ α) := ⟨⋃₀ U, hu⟩,
      existsi ub,
      intros T htc x hx,
      cases T with T ht,
      exact ⟨T, ⟨⟨T, ht⟩, htc, rfl⟩, hx⟩,
      let ub : ↥(ideals_not_univ α) := ⟨zero_ideal α, zero_ideal.is_ideal α, by simpa using hz.symm⟩,
      existsi ub,
      intros T htc,
      exfalso,
      exact h ⟨T, htc⟩
    end),
  specialize z (λ A B C hab hbc x hx, hbc $ hab hx),
  cases z with m z,
  cases m with m hm1,
  cases hm1 with h1 h2,
  existsi m,
  existsi h1,
  constructor,
  intro h, apply h2, rw h, trivial,
  intros T _ ht,
  cases classical.em ((1:α) ∈ T),
  right, exact is_ideal.univ_of_one_mem T h,
  specialize z ⟨T, _inst_3, h⟩,
  specialize z ht,
  left, exact set.eq_of_subset_of_subset z ht
end

end prop_1_3

-- Proposition 1.3 end


-- Corollary 1.4 start

theorem ideals_not_univ.to_maximal_ideal {α : Type u} [comm_ring α] (S : set α) [is_ideal α S] :
S ∈ ideals_not_univ α → ∃ (m : set α) (hm : is_ideal α m), @is_maximal_ideal _ _ m hm ∧ S ⊆ m :=
begin
  intro h,
  cases h with h1 h2,
  have z := zero_ne_one.to_maximal_ideal (α/S),
  specialize z (λ h, h2 $ is_ideal.mem_of_coset_zero S 1 h.symm),
  cases z with m hm,
  cases hm with h1 h2,
  existsi quotient_to_ideal S m,
  existsi quotient_to_ideal.is_ideal S m,
  have hsm : S ⊆ quotient_to_ideal S m,
    intro x,
    simp [is_ideal.mem_iff_coset_zero S,is_ideal.to_coset],
    intro hx,
    rw hx,
    apply is_ideal.zero_mem,
  split,
  cases h2,
  constructor,
  intro h,
  apply h2_ne_univ_ideal,
  rw [set.set_eq_def] at h,
  apply set.ext,
  intro x,
  cases is_ideal.coset_rep x with y hy,
  rw ← hy,
  specialize h y,
  simp at *,
  exact h,
  intros T _ ht,
  have hst : S ⊆ T := set.subset.trans hsm ht,
  specialize h2_no_between (ideal_to_quotient S T),
  have ht2 := ideal_to_quotient.subset S _ _ ht,
  rw quotient_to_contains_to_quotient at ht2,
  specialize h2_no_between ht2,
  cases h2_no_between with h h,
  left,
  apply set.eq_of_subset_of_subset,
  rw set.subset.antisymm_iff at h,
  have h3 := quotient_to_ideal.subset S _ _ h.1,
  rw contains_to_quotient_to_contains at h3,
  exact h3,
  exact hst,
  exact ht,
  right,
  apply set.ext,
  rw set.set_eq_def at h,
  intro x,
  specialize h (is_ideal.to_coset S x),
  simp at *,
  cases h with y hy,
  cases hy with hy1 hy2,
  calc x = y - (y - x) : by norm_num
     ... ∈ T : is_ideal.sub_mem hy1 (hst hy2),
  exact hsm
end

-- Corollary 1.4 end


-- Corollary 1.5 start

theorem not_unit.to_maximal_ideal {α : Type u} [comm_ring α] (x : α) (h : x ∈ nonunits α) :
∃ (m : set α) (hm : is_ideal α m), @is_maximal_ideal _ _ m hm ∧ x ∈ m :=
begin
  have z := ideals_not_univ.to_maximal_ideal (principal_ideal x),
  specialize z
    (begin
      split,
      exact principal_ideal.is_ideal x,
      intro hx,
      have := is_ideal.univ_of_one_mem _ hx,
      apply h,
      apply (unit_iff_principal_ideal_eq_one x).2,
      rw this,
      rw principal_ideal_one_eq_univ
    end),
  cases z with m z,
  cases z with hm z,
  existsi m,
  existsi hm,
  split, exact z.1,
  apply set.mem_of_mem_of_subset _ z.2,
  exact mem_principal_ideal x
end

-- Corollary 1.5 end


def is_local (α : Type u) [comm_ring α] : Prop :=
∀ S T [is_ideal α S] [is_ideal α T] [@@is_maximal_ideal _ S _inst_2] [@@is_maximal_ideal _ T _inst_3], S = T

theorem list.sum_singleton {α : Type u} [semiring α] (x : α) : list.sum [x] = x :=
by simp

theorem list.sum_mul {α : Type u} [semiring α] :
∀ (L : list α) (x : α), (L.map (λ b, b * x)).sum = L.sum * x
| []     x := by simp; rw [list.sum_nil]
| (h::t) x := by simp [list.sum_mul t x, add_mul]

section generate

variables {α : Type u} [comm_ring α] (S S₁ S₂ T : set α) (x : α) [is_ideal α T]

def span : set α := { x | ∃ L : list α, (∀ x ∈ L, ∃ y z, y ∈ S ∧ y * z = x) ∧ L.sum = x }

instance span.is_ideal : is_ideal α (span S) :=
{ zero_mem := ⟨[], λ x, false.elim, list.sum_nil⟩,
  add_mem  := λ x y ⟨Lx, hxLS, hx⟩ ⟨Ly, hyLS, hy⟩,
    ⟨Lx ++ Ly,
     λ z hz, or.cases_on (list.mem_append.1 hz) (hxLS z) (hyLS z),
     hx ▸ hy ▸ list.sum_append⟩,
  mul_mem  := λ x y ⟨Lx, ⟨hxLS, hx⟩⟩,
    ⟨Lx.map (λ b, b * y),
     λ z hz, let ⟨m, hm, hmyz⟩ := list.exists_of_mem_map hz,
                 ⟨n, p, hn, hnpm⟩ := hxLS m hm in
       ⟨n, p * y, hn, by rw ← mul_assoc; simpa [hnpm] using hmyz⟩,
     hx ▸ list.sum_mul Lx y⟩ }

variables {S x}

theorem mem_span_of_mem : x ∈ S → x ∈ span S :=
λ hx, ⟨[x], λ y hy, ⟨x, 1, hx, by simp at hy; simp [hy]⟩, list.sum_singleton x⟩

theorem span.ext : (∀ x, x ∈ S₁ ↔ x ∈ S₂) → span S₁ = span S₂ :=
λ h, congr_arg span $ set.ext h

variables (S x)

def generate : set α := { x | ∀ (T : set α) [is_ideal α T], S ⊆ T → x ∈ T }

instance generate.is_ideal : is_ideal α (generate S) :=
{ zero_mem := λ T ht hst, @@is_ideal.zero_mem _ T ht,
  add_mem  := λ x y hx hy T ht hst, @@is_ideal.add_mem _ ht (@hx T ht hst) (@hy T ht hst),
  mul_mem  := λ x y hx T ht hst, @@is_ideal.mul_mem _ ht (@hx T ht hst) }

theorem singleton_generate_principal : generate {x} = principal_ideal x :=
set.ext $ λ y,
  ⟨λ hy, hy (principal_ideal x) (λ z hz, ⟨1, eq.symm $ by simpa using hz⟩),
    λ ⟨z, hz⟩ T ht hst, by simp at hst; rw ← hz; exact is_ideal.mul_mem hst⟩

theorem subset_generate : S ⊆ generate S :=
λ x hx T ht hst, hst hx

variables {S S₁ S₂ T x}

theorem generate_subset_ideal : S ⊆ T → generate S ⊆ T :=
λ h x hx, hx T h

theorem generate.ext : (∀ x, x ∈ S₁ ↔ x ∈ S₂) → generate S₁ = generate S₂ :=
λ h, congr_arg generate $ set.ext h

variables (T)

theorem is_ideal.sum_mem : ∀ L : list α, (∀ x ∈ L, x ∈ T) → L.sum ∈ T
| []     H := by simp [is_ideal.zero_mem T]
| (h::t) H := by simp [is_ideal.add_mem (H h $ or.inl rfl)
    (is_ideal.sum_mem t $ λ x hx, H x $ or.inr hx)]

theorem mem_generate_of_mem_span : x ∈ span S → x ∈ generate S :=
λ ⟨L, hx, hLx⟩ T ht hst,
  have h : list.sum L ∈ T,
  from @@is_ideal.sum_mem _ T ht L $ λ p hp,
    let ⟨y, z, hy, hyzx⟩ := hx p hp in
    by rw ← hyzx; simp [is_ideal.mul_mem (hst hy)],
  hLx ▸ h

theorem mem_span_of_mem_generate : x ∈ generate S → x ∈ span S :=
λ hx, hx (span S) (λ z, mem_span_of_mem)

theorem mem_span_iff_mem_generate : x ∈ span S ↔ x ∈ generate S :=
⟨mem_generate_of_mem_span, mem_span_of_mem_generate⟩

theorem mem_generate_iff_mem_span : x ∈ generate S ↔ x ∈ span S :=
⟨mem_span_of_mem_generate, mem_generate_of_mem_span⟩

variables (S S₁ S₂ T x)

theorem span_eq_generate : span S = generate S :=
set.ext $ λ x, mem_span_iff_mem_generate

theorem generate_eq_span : generate S = span S :=
set.ext $ λ x, mem_generate_iff_mem_span

theorem singleton_span_principal : span {x} = principal_ideal x :=
by simp [span_eq_generate, singleton_generate_principal]

theorem subset_span : S ⊆ span S :=
by simp [span_eq_generate, subset_generate]

end generate

namespace is_ideal

section operations_on_ideals

variables {α : Type u} [comm_ring α] (S₁ S₂ : set α)
variables [is_ideal α S₁] [is_ideal α S₂]

@[reducible] def add : set α :=
{ x | ∃ y z, y ∈ S₁ ∧ z ∈ S₂ ∧ x = y + z }

infix + := add

instance add.is_ideal : is_ideal α (S₁ + S₂) :=
{ zero_mem := ⟨0, 0, zero_mem S₁, zero_mem S₂, by simp⟩,
  add_mem  := λ x₁ x₂ ⟨y₁, z₁, hy₁, hz₁, hx₁⟩ ⟨y₂, z₂, hy₂, hz₂, hx₂⟩,
    ⟨y₁ + y₂, z₁ + z₂, add_mem hy₁ hy₂, add_mem hz₁ hz₂, by simp [hx₁, hx₂]⟩,
  mul_mem  := λ x₁ x₂ ⟨y, z, hy, hz, hx⟩,
    ⟨y * x₂, z * x₂, mul_mem hy, mul_mem hz, by simp [hx, add_mul]⟩ }

theorem add_eq_generate_union : S₁ + S₂ = generate (S₁ ∪ S₂) :=
set.ext $ λ x,
⟨λ ⟨y, z, hy, hz, hx⟩ S h hs,
   hx.symm ▸ @@add_mem _ h (hs $ or.inl hy) (hs $ or.inr hz),
 λ hx, hx (S₁ + S₂) $ λ p hp, or.cases_on hp
   (λ hp1, ⟨p, 0, hp1, zero_mem S₂, eq.symm $ add_zero p⟩)
   (λ hp2, ⟨0, p, zero_mem S₁, hp2, eq.symm $ zero_add p⟩)⟩

variables {S₁ S₂}

theorem subset_add_left : S₁ ⊆ S₁ + S₂ :=
λ x hx, ⟨x, 0, hx, is_ideal.zero_mem S₂, eq.symm $ add_zero x⟩

theorem subset_add_right : S₂ ⊆ S₁ + S₂ :=
λ x hx, ⟨0, x, is_ideal.zero_mem S₁, hx, eq.symm $ zero_add x⟩

theorem add_self : S₁ + S₁ = S₁ :=
set.ext $ λ x,
  ⟨λ ⟨y, z, hy, hz, hx⟩, set.mem_of_eq_of_mem hx $ is_ideal.add_mem hy hz,
    λ hx, subset_add_left hx⟩

end operations_on_ideals

end is_ideal

-- Proposition 1.6 start

theorem nonunits_ideal_to_local {α : Type u} [comm_ring α] : is_ideal α (nonunits α) → is_local α :=
λ h S T hs ht hms hmt,
  or.cases_on (@@is_maximal_ideal.no_between _ hs hms (nonunits α) h $ λ z hz, @@not_unit_of_mem_maximal_ideal _ S hs hms hz)
    (λ h1, or.cases_on (@@is_maximal_ideal.no_between _ ht hmt (nonunits α) h $ λ z hz, @@not_unit_of_mem_maximal_ideal _ T ht hmt hz)
      (λ h2, h1.symm.trans h2)
      (λ h2, false.elim $ ((set.set_eq_def _ _).1 h2 1).2 trivial ⟨1, by simp⟩))
    (λ h1, false.elim $ ((set.set_eq_def _ _).1 h1 1).2 trivial ⟨1, by simp⟩)

theorem maximal_ideal_one_add_unit_to_local {α : Type u} [comm_ring α]
  (m : set α) [is_ideal α m] [is_maximal_ideal m] :
  (∀ x:α, x ∈ m → is_unit (1 + x)) → is_local α :=
λ h, have hm : m = nonunits α, from set.ext $ λ x,
  ⟨λ hx, not_unit_of_mem_maximal_ideal m _inst_3 hx,
    λ hx, or.cases_on (is_maximal_ideal.no_between (m + principal_ideal x) (is_ideal.subset_add_left))
      (λ h1, ((set.set_eq_def _ _).1 h1 x).1 ⟨0, x, is_ideal.zero_mem m, mem_principal_ideal x, by simp⟩)
      (λ h1, let ⟨y, z, hy, ⟨p, hz⟩, hyz⟩ := ((set.set_eq_def _ _).1 h1 1).2 trivial in
       let ⟨q, hq⟩ := h (-y) (is_ideal.neg_mem hy) in
       false.elim $ hx ⟨p * q, calc
         x * (p * q) = (1 + -y) * q : by rw [hyz, ← hz]; ring
                 ... = 1 : hq⟩)⟩,
by rw hm at _inst_2; exact nonunits_ideal_to_local _inst_2

-- Proposition 1.6 end


class is_pid (α : Type u) [comm_ring α] extends is_integral_domain α : Prop :=
(h : ∀ S [is_ideal α S], ∃ x, S = principal_ideal x)

instance maximal_of_pid_of_prime_of_nonzero (α : Type u) [comm_ring α] [is_pid α]
(S : set α) [is_ideal α S] [is_prime_ideal S] : S ≠ zero_ideal α → is_maximal_ideal S :=
begin
  intro h,
  constructor,
  apply is_prime_ideal.ne_univ_ideal,
  intros T _ hst,
  cases is_pid.h S with s hs,
  cases is_pid.h T with t ht,
  rw [hs,ht] at *,
  cases hst (mem_principal_ideal s) with z hz,
  have h1 : t * z ∈ S := by rw [hs,hz]; exact mem_principal_ideal s,
  cases is_prime_ideal.mem_or_mem_of_mul_mem h1 with p p,
  left,
    apply set.eq_of_subset_of_subset _ hst,
    apply principal_ideal.subset_of_mem,
    rwa hs at p,
  right,
    rw [← principal_ideal_one_eq_univ],
    rw [← unit_iff_principal_ideal_eq_one],
    rw hs at p,
    cases p with n hn,
    have : z * (t * n - 1) = 0 := calc
      z * (t * n - 1) = s * n - z : by rw ← hz; ring
                  ... = 0 : by simp [hn],
    cases is_integral_domain.zero_or_zero_of_mul_zero z (t * n - 1) this with p p,
    simp [p] at hz,
    exfalso,
    apply h,
    rw [← hz],
    apply principal_ideal_zero_eq_zero_ideal,
    rw sub_eq_zero at p,
    exact ⟨n, p⟩
end

@[simp] lemma pow_coset {α : Type u} [comm_ring α] {S : set α} [is_ideal α S] (x : α) :
Π (n : nat), ⟦x⟧^n = ⟦x^n⟧
| 0            := rfl
| (nat.succ n) := by unfold monoid.pow; simp [pow_coset n]

-- for lack of a [better] name (or a name at all)
def nil_aux_1 {α : Type u} [comm_ring α] (x y : α) : nat → α
| 0            := 0
| (nat.succ n) := (x + y)^n + nil_aux_1 n * y

theorem nil_aux_2 {α : Type u} [comm_ring α] (x y : α) : Π n:nat, (x + y)^n - y^n = x * nil_aux_1 x y n
| 0            := by simp [nil_aux_1]
| (nat.succ n) := calc (x + y)^nat.succ n - y^nat.succ n
      = x * (x + y)^n + y * (x * nil_aux_1 x y n) : by unfold monoid.pow; rw ← nil_aux_2 n; ring
  ... = x * nil_aux_1 x y (nat.succ n)            : by unfold nil_aux_1; ring

-- Proposition 1.7 start

instance nilpotents.is_ideal (α : Type u) [comm_ring α] : is_ideal α (nilpotents α) :=
{ zero_mem := ⟨0, zero_mul (1:α)⟩,
  add_mem  := λ x y ⟨m, hm⟩ ⟨n, hn⟩, ⟨m*n + m + n, calc
          (x + y)^nat.succ (m*n + m + n)
        = (x + y)^(nat.succ n * nat.succ m) : by simp [nat.succ_eq_add_one]; ring
    ... = ((x + y)^nat.succ n - y^nat.succ n)^nat.succ m : by simp [pow_mul, hn]
    ... = 0 : by simp [nil_aux_2, mul_pow, hm]⟩,
  mul_mem  := λ x y ⟨m, hm⟩, ⟨m, by simp [mul_pow,hm]⟩ }

theorem quotient_nilpotents_zero_of_nilpotents {α : Type u} [comm_ring α]
(x : α/nilpotents α) : x ∈ nilpotents (α/nilpotents α) → x = 0 :=
λ ⟨n, hn⟩,
begin
  cases (is_ideal.coset_rep x) with y hy,
  rw [← hy, is_ideal.coset_zero_iff_mem],
  rw [← hy, pow_coset, is_ideal.coset_zero_iff_mem] at hn,
  cases hn with z hz,
  existsi n * z + n + z,
  rw [nat.succ_eq_add_one],
  rw [nat.succ_eq_add_one, nat.succ_eq_add_one, ← pow_mul] at hz,
  simp only [add_mul, mul_add, one_mul, mul_one] at hz,
  simpa using hz
end

-- Proposition 1.7 end


-- Proposition 1.8 start

theorem nilpotent_eq_intersection_of_prime_ideals (α : Type u) [comm_ring α] :
nilpotents α = ⋂₀ { S | ∃ (h : is_ideal α S), @@is_prime_ideal _ S h } :=
begin
  apply set.ext,
  intro z,
  split,
  intros hz S hs,
  cases hs with _ _,
  cases hz with n hn,
  have p : ∀ m, z^m ∈ S → z ∈ S,
    intro m,
    induction m with m hm,
    intro hz,
    unfold monoid.pow at hz,
    apply set.mem_of_eq_of_mem,
    exact eq.symm (one_mul z),
    apply is_ideal.mul_mem hz,
    intro hz,
    unfold monoid.pow at hz,
    have p := is_prime_ideal.mem_or_mem_of_mul_mem hz,
    cases p, exact p, exact hm p,
  specialize p (nat.succ n),
  specialize p (set.mem_of_eq_of_mem hn $ is_ideal.zero_mem S),
  exact p,
  intro hz,
  apply @of_not_not _ (classical.prop_decidable _),
  intro h,
  have h := forall_not_of_not_exists h,
  let S : set (set α) := { S | ∃ (h : is_ideal α S), ∀ n, z^nat.succ n ∉ S },
  have Z := @zorn.zorn,
  specialize @Z S,
  specialize @Z (λ T₁ T₂, T₁.val ⊆ T₂.val),
  specialize @Z (λ c hc,
    begin
      let U : set (set α) := { T | ∃ X : ↥S, X.val = T ∧ X ∈ c },
      cases classical.em (∃ T, T ∈ U) with ht ht,
      fapply exists.intro,
      fapply subtype.mk,
      exact ⋃₀ U,
      have hu := ideals.sUnion α U,
      specialize hu (λ x ⟨⟨A, h, h2⟩, hx, hc⟩, by rwa ← hx),
      cases ht with T ht,
      specialize hu T ht,
      specialize hu (λ T₁ T₂ ⟨⟨t₁, ht1⟩, ht2, ht3⟩ ⟨⟨t₂, ht4⟩, ht5, ht6⟩,
        begin
          specialize hc _ ht3 _ ht6,
          rw [← ht2, ← ht5],
          cases classical.em (subtype.mk t₁ ht1 = subtype.mk t₂ ht4),
          rw h_1,
          left, intro x, exact id,
          specialize hc h_1,
          exact hc
        end),
      existsi hu,
      intros n hn,
      cases hn with B hn,
      cases hn with hb hn,
      cases hb with C hc,
      cases C with C hc,
      cases hc with hc1 hc2,
      cases hc with _ hc3,
      rw ← hc1 at hn,
      apply hc3 n hn,
      intros A H x hx,
      cases A with A ha,
      exact ⟨A, ⟨⟨A, ha⟩, rfl, H⟩, hx⟩,
      fapply exists.intro,
      fapply subtype.mk,
      exact zero_ideal α,
      exact ⟨zero_ideal.is_ideal α, λ n hn, h n $ eq_of_mem_singleton hn⟩,
      intros A ha,
      exfalso,
      exact ht ⟨A.val, A, rfl, ha⟩
    end),
  specialize Z (λ A B C hab hbc x hx, hbc $ hab hx),
  cases Z with m Z,
  cases m with m hm1,
  cases hm1 with h1 h2,
  specialize hz m,
  have : is_prime_ideal m,
  constructor,
  intro hm,
  apply h2 0,
  rw hm,
  trivial,
  intros x y hxy,
  let X : set α := quotient_to_ideal m (principal_ideal ⟦x⟧),
  let Y : set α := quotient_to_ideal m (principal_ideal ⟦y⟧),
  cases classical.em (∃ n, z^nat.succ n ∈ X) with hX hX,
  cases classical.em (∃ n, z^nat.succ n ∈ Y) with hY hY,
  cases hX with p hp,
  cases hp with b hb,
  cases hY with q hq,
  cases hq with d hd,
  cases is_ideal.coset_rep b with c hc,
  rw [← hc, is_ideal.mul_coset] at hb,
  cases is_ideal.coset_rep d with e he,
  rw [← he, is_ideal.mul_coset] at hd,
  exfalso,
  apply h2 (p + q + 1),
  exact calc
          z^nat.succ (p + q + 1)
        = z^(nat.succ p + nat.succ q) : by simp [nat.succ_eq_add_one]
    ... = z^nat.succ p * z^nat.succ q : pow_add _ _ _
    ... = z^nat.succ p * (y * e - (y * e - z^nat.succ q)) : by norm_num
    ... = z^nat.succ p * (y * e) - z^nat.succ p * (y * e - z^nat.succ q) : mul_sub _ _ _
    ... = z^nat.succ p * (y * e) - (y * e - z^nat.succ q) * z^nat.succ p : by ac_refl
    ... = (x * c - (x * c - z^nat.succ p)) * (y * e) - (y * e - z^nat.succ q) * z^nat.succ p : by norm_num
    ... = (x * c) * (y * e) - (x * c - z^nat.succ p) * (y * e) - (y * e - z^nat.succ q) * z^nat.succ p : by rw sub_mul
    ... = (x * y) * (c * e) - (x * c - z^nat.succ p) * (y * e) - (y * e - z^nat.succ q) * z^nat.succ p : by ac_refl
    ... ∈ m : is_ideal.sub_mem (is_ideal.sub_mem (is_ideal.mul_mem hxy) (is_ideal.mul_mem $ quotient.exact hb)) (is_ideal.mul_mem $ quotient.exact hd),
  have z1 := Z ⟨Y, _, forall_not_of_not_exists hY⟩ (quotient_to_ideal.contains _ _),
  right,
    apply set.mem_of_mem_of_subset _ z1,
    apply quotient_to_ideal.is_ideal,
    apply mem_principal_ideal,
  have z1 := Z ⟨X, _, forall_not_of_not_exists hX⟩ (quotient_to_ideal.contains _ _),
  left,
    apply set.mem_of_mem_of_subset _ z1,
    apply quotient_to_ideal.is_ideal,
    apply mem_principal_ideal,
  specialize hz ⟨h1, this⟩,
  apply h2 0,
  simpa [monoid.pow, one_mul] using hz
end

-- Proposition 1.8 end


def jacobson (α : Type u) [comm_ring α] : set α :=
⋂₀ { S : set α | ∃ (h : is_ideal α S), @@is_maximal_ideal _ S h }

-- Proposition 1.9 start

theorem mem_jacobson_iff_multiple_add_one_unit {α : Type u} [comm_ring α]
(x : α) : x ∈ jacobson α ↔ ∀ y, is_unit (1 + x * y) :=
begin
  split,
  intros hx y,
  apply @@of_not_not (classical.prop_decidable _),
  intro h,
  cases not_unit.to_maximal_ideal _ h with m hm,
  cases hm with _inst_1 hm,
  cases hm with _inst_2 hm,
  specialize hx m ⟨_inst_1, _inst_2⟩,
  apply is_maximal_ideal.ne_univ_ideal m,
  apply is_ideal.univ_of_one_mem m,
  exact calc
      1 = (1 + x * y) - x * y : eq.symm (add_sub_cancel _ _)
    ... ∈ m : is_ideal.sub_mem hm (is_ideal.mul_mem hx),
  intros h m hm,
  cases hm with _inst_1 _inst_2,
  apply @@of_not_not (classical.prop_decidable _),
  intro hx,
  have _inst_3 := (maximal_iff_quotient_field m).1 _inst_2,
  rw is_ideal.mem_iff_coset_zero m at hx,
  cases is_field.h hx with y hy,
  cases is_ideal.coset_rep y with z hz,
  rw [← hz, is_ideal.mul_coset] at hy,
  apply is_maximal_ideal.ne_univ_ideal m,
  apply is_ideal.eq_univ_of_contains_unit m,
  existsi x * z - 1,
  split,
  exact quotient.exact hy,
  cases h (-z) with w hw,
  existsi -w,
  exact calc
    (x * z - 1) * -w = (1 + x * -z) * w : by ring
                 ... = 1 : hw
end

-- Proposition 1.9 end

namespace is_ideal

section operations_on_ideals

variables {α : Type u} [comm_ring α] (S S₁ S₂ S₃ S₄ : set α)
variables [is_ideal α S] [is_ideal α S₁] [is_ideal α S₂] [is_ideal α S₃] [is_ideal α S₄]

@[reducible] def mul : set α :=
generate { x | ∃ y z, y ∈ S₁ ∧ z ∈ S₂ ∧ x = y * z}

infix * := mul

instance mul.is_ideal : is_ideal α (S₁ * S₂) :=
generate.is_ideal _

instance inter.is_ideal : is_ideal α (S₁ ∩ S₂) :=
{ zero_mem := ⟨zero_mem S₁, zero_mem S₂⟩,
  add_mem  := λ x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩, ⟨add_mem hx1 hy1, add_mem hx2 hy2⟩,
  mul_mem  := λ x y ⟨hx1, hx2⟩, ⟨mul_mem hx1, mul_mem hx2⟩ }

instance sInter.is_ideal (S : set $ set α) (h : ∀ A ∈ S, is_ideal α A) : is_ideal α (⋂₀ S) :=
{ zero_mem := λ A ha, @@zero_mem _ A (h A ha),
  add_mem  := λ x y hx hy A ha, @@add_mem _ (h A ha) (hx A ha) (hy A ha),
  mul_mem  := λ x y hx A ha, @@mul_mem _ (h A ha) (hx A ha) }

variables {S₁ S₂ S₃ S₄}

theorem mem_add {x y : α} : x ∈ S₁ → y ∈ S₂ → x + y ∈ S₁ + S₂ :=
λ hx hy, ⟨x, y, hx, hy, rfl⟩

theorem mem_mul {x y : α} : x ∈ S₁ → y ∈ S₂ → x * y ∈ S₁ * S₂ :=
λ hx hy, subset_generate _ ⟨x, y, hx, hy, rfl⟩

theorem add_comm : S₁ + S₂ = S₂ + S₁ :=
set.ext $ λ x, ⟨
  λ ⟨y, z, hy, hz, hx⟩, ⟨z, y, hz, hy, add_comm y z ▸ hx⟩,
  λ ⟨y, z, hy, hz, hx⟩, ⟨z, y, hz, hy, add_comm y z ▸ hx⟩⟩

theorem mul_comm : S₁ * S₂ = S₂ * S₁ :=
generate.ext $ λ x, 
  ⟨λ ⟨y, z, hy, hz, hx⟩, ⟨z, y, hz, hy, mul_comm y z ▸ hx⟩,
    λ ⟨y, z, hy, hz, hx⟩, ⟨z, y, hz, hy, mul_comm y z ▸ hx⟩⟩

theorem add_assoc : (S₁ + S₂) + S₃ = S₁ + (S₂ + S₃) :=
set.ext $ λ x, ⟨
  λ ⟨pq, r, ⟨p, q, hp, hq, hpq⟩, hr, hx⟩, ⟨p, q + r, hp, ⟨q, r, hq, hr, rfl⟩, add_assoc p q r ▸ hpq ▸ hx⟩,
  λ ⟨p, qr, hp, ⟨q, r, hq, hr, hqr⟩, hx⟩, ⟨p + q, r, ⟨p, q, hp, hq, rfl⟩, hr, (add_assoc p q r).symm ▸ hqr ▸ hx⟩⟩

theorem mul_subset_left : S₁ * S₂ ⊆ S₁ :=
λ x hx, hx S₁ $ λ z ⟨p, q, hp, hq, hz⟩, calc
    z = p * q : hz
  ... ∈ S₁    : is_ideal.mul_mem hp

theorem mul_subset_right : S₁ * S₂ ⊆ S₂ :=
λ x hx, hx S₂ $ λ z ⟨p, q, hp, hq, hz⟩, calc
    z = p * q : hz
  ... = q * p : comm_ring.mul_comm p q
  ... ∈ S₂    : is_ideal.mul_mem hq

theorem mul_subset_inter : S₁ * S₂ ⊆ S₁ ∩ S₂ :=
λ x hx, ⟨mul_subset_left hx, mul_subset_right hx⟩

theorem add_univ : S₁ + (univ_ideal α) = univ_ideal α :=
set.ext $ λ x, ⟨λ hx, trivial, λ hx, subset_add_right hx⟩

theorem univ_add : (univ_ideal α) + S₁ = univ_ideal α :=
set.ext $ λ x, ⟨λ hx, trivial, λ hx, subset_add_left hx⟩

theorem add_zero : S₁ + (zero_ideal α) = S₁ :=
set.ext $ λ x,
  ⟨λ ⟨y, z, hy, hz, hx⟩, by simp [zero_ideal] at hz; simp [hz] at hx; simpa [hx],
    λ hx, subset_add_left hx⟩

theorem zero_add : (zero_ideal α) + S₁ = S₁ :=
set.ext $ λ x,
  ⟨λ ⟨y, z, hy, hz, hx⟩, by simp [zero_ideal] at hy; simp [hy] at hx; simpa [hx],
    λ hx, subset_add_right hx⟩

theorem mul_univ : S₁ * (univ_ideal α) = S₁ :=
set.ext $ λ x,
  ⟨λ hx, mul_subset_left hx,
   λ hx S s hs, hs ⟨x, 1, hx, trivial, eq.symm $ mul_one x⟩⟩

theorem univ_mul : (univ_ideal α) * S₁ = S₁ :=
set.ext $ λ x,
  ⟨λ hx, mul_subset_right hx,
   λ hx S s hs, hs ⟨1, x, trivial, hx, eq.symm $ one_mul x⟩⟩

theorem mul_zero : S₁ * (zero_ideal α) = zero_ideal α :=
set.ext $ λ x,
  ⟨λ hx, hx (zero_ideal α) $ λ z ⟨p, q, hp, hq, hz⟩, by simp [zero_ideal] at *; simp [hz, hq],
   λ hx, by simp [zero_ideal] at *; rw hx; exact is_ideal.zero_mem _⟩

theorem zero_mul : (zero_ideal α) * S₁ = zero_ideal α :=
set.ext $ λ x,
  ⟨λ hx, hx (zero_ideal α) $ λ z ⟨p, q, hp, hq, hz⟩, by simp [zero_ideal] at *; simp [hz, hp],
   λ hx, by simp [zero_ideal] at *; rw hx; exact is_ideal.zero_mem _⟩

theorem mul_assoc : (S₁ * S₂) * S₃ = S₁ * (S₂ * S₃) :=
set.ext $ λ x,
⟨λ hx, hx (S₁ * (S₂ * S₃)) $ λ z ⟨pq, r, hpq, hr, hz⟩,
   let ⟨L, hL, hLpq⟩ := mem_span_of_mem_generate hpq in
   have h : list.sum (list.map (λ b, b * r) L) ∈ S₁ * (S₂ * S₃) :=
     λ S hs hss, @@is_ideal.sum_mem _ S hs (list.map (λ b, b * r) L) $ λ x hx,
       let ⟨y, hyL, hyrx⟩ := list.exists_of_mem_map hx,
           ⟨m, n, ⟨p, q, hp, hq, hmpq⟩, hmny⟩ := hL y hyL in
       hss ⟨p, (q * r) * n,
         hp,
         λ T ht htt, @@is_ideal.mul_mem _ ht $ htt ⟨q, r, hq, hr, rfl⟩,
         by rw [← hyrx, ← hmny, hmpq]; ac_refl⟩,
   by rw [list.sum_mul, hLpq] at h; rwa hz,
 λ hx, hx ((S₁ * S₂) * S₃) $ λ z ⟨p, qr, hp, hqr, hz⟩,
   let ⟨L, hL, hLqr⟩ := mem_span_of_mem_generate hqr in
   have h : list.sum (list.map (λ b, b * p) L) ∈ (S₁ * S₂) * S₃ :=
     λ S hs hss, @@is_ideal.sum_mem _ S hs (list.map (λ b, b * p) L) $ λ x hx,
       let ⟨y, hyL, hypx⟩ := list.exists_of_mem_map hx,
           ⟨m, n, ⟨q, r, hq, hr, hmqr⟩, hmny⟩ := hL y hyL in
       hss ⟨(p * q) * n, r,
         λ T ht htt, @@is_ideal.mul_mem _ ht $ htt ⟨p, q, hp, hq, rfl⟩,
         hr,
         by rw [← hypx, ← hmny, hmqr]; ac_refl⟩,
    by rw [list.sum_mul, hLqr, comm_ring.mul_comm] at h; rwa hz⟩

theorem mul_add_subset : (S₁ * S₂) + (S₁ * S₃) ⊆ S₁ * (S₂ + S₃) :=
λ x ⟨y, z, hy, hz, hx⟩,
let ⟨Ly, hy, hLy⟩ := mem_span_of_mem_generate hy,
    ⟨Lz, hz, hLz⟩ := mem_span_of_mem_generate hz in
mem_generate_of_mem_span ⟨Ly ++ Lz,
  λ p hp, or.cases_on (list.mem_append.1 hp)
    (λ hpy, let ⟨py, pz, ⟨pyy, pyz, hpyy, hpyz, hpyyz⟩, hpyzp⟩ := hy p hpy in
       ⟨py, pz, ⟨pyy, pyz, hpyy, subset_add_left hpyz, hpyyz⟩, hpyzp⟩)
    (λ hpz, let ⟨py, pz, ⟨pzy, pzz, hpzy, hpzz, hpzyz⟩, hpyzp⟩ := hz p hpz in
       ⟨py, pz, ⟨pzy, pzz, hpzy, subset_add_right hpzz, hpzyz⟩, hpyzp⟩),
  by simp [list.sum_append, *]⟩

theorem mul_add : S₁ * (S₂ + S₃) = (S₁ * S₂) + (S₁ * S₃) :=
set.ext $ λ x,
⟨λ hx, let ⟨L, hx, hLx⟩ := mem_span_of_mem_generate hx in
   (list.rec_on L
     (λ x hx hLx, by rw ← hLx; exact is_ideal.zero_mem _)
     (λ hd tl ih x hx hLx, have h : hd + list.sum tl ∈ S₁ * S₂ + S₁ * S₃,
       from is_ideal.add_mem
         (let ⟨y, z, ⟨m, n, hm, ⟨ny, nz, hny, hnz, hnyz⟩, hymn⟩, hyz⟩ := hx hd (or.inl rfl) in
            ⟨m * ny * z, m * nz * z,
             is_ideal.mul_mem $ subset_generate _ ⟨m, ny, by simp [*]⟩,
             is_ideal.mul_mem $ subset_generate _ ⟨m, nz, by simp [*]⟩,
             by rw [← hyz, hymn, hnyz, mul_add, add_mul]⟩)
         (ih (list.sum tl) (λ z hz, hx z (or.inr hz)) rfl),
            by simp at hLx; rwa hLx at h))
   x hx hLx,
 λ hx, mul_add_subset hx⟩

theorem add_congr : S₁ = S₂ → S₃ = S₄ → S₁ + S₃ = S₂ + S₄ :=
λ h12 h34, calc
  S₁ + S₃ = S₂ + S₃ : @eq.subst _ (λ T, ∀ H:is_ideal α T, S₁ + S₃ = @@add _ T S₃ H _) S₁ S₂ h12 (λ H, rfl) _
      ... = S₂ + S₄ : @eq.subst _ (λ T, ∀ H:is_ideal α T, S₂ + S₃ = @@add _ S₂ T _ H) S₃ S₄ h34 (λ H, rfl) _

theorem add_mul : (S₁ + S₂) * S₃ = (S₁ * S₃) + (S₂ * S₃) :=
calc (S₁ + S₂) * S₃
      = S₃ * (S₁ + S₂) : mul_comm
  ... = (S₃ * S₁) + (S₃ * S₂) : mul_add
  ... = (S₁ * S₃) + (S₂ * S₃) : add_congr mul_comm mul_comm

theorem mul_congr : S₁ = S₂ → S₃ = S₄ → S₁ * S₃ = S₂ * S₄ :=
λ h12 h34, calc
  S₁ * S₃ = S₂ * S₃ : @eq.subst _ (λ T, ∀ H:is_ideal α T, S₁ * S₃ = @@mul _ T S₃ H _) S₁ S₂ h12 (λ H, rfl) _
      ... = S₂ * S₄ : @eq.subst _ (λ T, ∀ H:is_ideal α T, S₂ * S₃ = @@mul _ S₂ T _ H) S₃ S₄ h34 (λ H, rfl) _

theorem mul_subset_of_subset : S₂ ⊆ S₃ → S₁ * S₂ ⊆ S₁ * S₃ :=
λ h x hx S s hs, @@hx S s $ λ z ⟨p, q, hp, hq, hz⟩, hs ⟨p, q, hp, h hq, hz⟩

theorem mul_subset_of_subset_of_subset : S₁ ⊆ S₂ → S₃ ⊆ S₄ → S₁ * S₃ ⊆ S₂ * S₄ :=
λ h12 h34 x hx S s hs, @@hx S s $ λ z ⟨p, q, hp, hq, hz⟩, hs ⟨p, q, h12 hp, h34 hq, hz⟩

theorem add_subset : S₁ ⊆ S₃ → S₂ ⊆ S₃ → S₁ + S₂ ⊆ S₃ :=
λ h13 h23 x ⟨y, z, hy, hz, hx⟩, set.mem_of_eq_of_mem hx
  $ add_mem (h13 hy) (h23 hz)

theorem add_subset_of_subset_of_subset : S₁ ⊆ S₂ → S₃ ⊆ S₄ → S₁ + S₃ ⊆ S₂ + S₄ :=
λ h12 h34 x ⟨y, z, hy, hz, hx⟩, set.mem_of_eq_of_mem hx
  $ add_mem (subset_add_left $ h12 hy) (subset_add_right $ h34 hz)

theorem add_mul_inter_subset_mul : (S₁ + S₂) * (S₁ ∩ S₂) ⊆ S₁ * S₂ :=
calc
  (S₁ + S₂) * (S₁ ∩ S₂) = S₁ * (S₁ ∩ S₂) + S₂ * (S₁ ∩ S₂) : add_mul
                    ... ⊆ S₁ * S₂ + S₂ * S₁ : add_subset_of_subset_of_subset
                                                (mul_subset_of_subset_of_subset (λ x, id) (λ x hx, hx.2))
                                                (mul_subset_of_subset_of_subset (λ x, id) (λ x hx, hx.1))
                    ... = S₁ * S₂ + S₁ * S₂ : add_congr rfl mul_comm
                    ... = S₁ * S₂ : add_self

variables (S₁ S₂)

def coprime : Prop := S₁ + S₂ = principal_ideal 1

variables {S₁ S₂}

theorem inter_eq_mul_of_coprime : coprime S₁ S₂ → S₁ ∩ S₂ = S₁ * S₂ :=
λ h, set.eq_of_subset_of_subset
(calc
  S₁ ∩ S₂ = (univ_ideal α) * (S₁ ∩ S₂) : univ_mul.symm
      ... = (principal_ideal 1) * (S₁ ∩ S₂) : mul_congr (principal_ideal_one_eq_univ α).symm rfl
      ... = (S₁ + S₂) * (S₁ ∩ S₂) : mul_congr h.symm rfl
      ... ⊆ S₁ * S₂ : add_mul_inter_subset_mul)
mul_subset_inter

end operations_on_ideals

end is_ideal

def tuple : list Type.{u} → Type u
 | [] := punit
 | (t₀ :: []) := t₀
 | (t₀ :: t₁ :: ts) := t₀ × tuple (t₁ :: ts)

namespace product

def add : Π L : list Σ t : Type.{u}, comm_ring t, tuple (list.map sigma.fst L) → tuple (list.map sigma.fst L) → tuple (list.map sigma.fst L)
 | [] punit.star punit.star := punit.star
 | (t₀ :: []) x₀ y₀ := @comm_ring.add t₀.1 t₀.2 x₀ y₀
 | (t₀ :: t₁ :: ts) (x₀, xs) (y₀, ys) := (@comm_ring.add t₀.1 t₀.2 x₀ y₀, add (t₁ :: ts) xs ys)

theorem add_assoc : Π (L : list Σ t : Type.{u}, comm_ring t) (x y z : tuple (list.map sigma.fst L)), (add L (add L x y) z) = (add L x (add L y z))
 | [] punit.star punit.star punit.star := rfl
 | (t₀ :: []) x₀ y₀ z₀ := @comm_ring.add_assoc t₀.1 t₀.2 x₀ y₀ z₀
 | (t₀ :: t₁ :: ts) (x₀, xs) (y₀, ys) (z₀, zs) := prod.mk.inj_iff.2 ⟨@comm_ring.add_assoc t₀.1 t₀.2 x₀ y₀ z₀, add_assoc (t₁ :: ts) xs ys zs⟩

def zero : Π L : list Σ t : Type.{u}, comm_ring t, tuple (list.map sigma.fst L)
 | [] := punit.star
 | (t₀ :: []) := @comm_ring.zero t₀.1 t₀.2
 | (t₀ :: t₁ :: ts) := (@comm_ring.zero t₀.1 t₀.2, zero (t₁ :: ts))

theorem zero_add : Π (L : list Σ t : Type.{u}, comm_ring t) (x : tuple (list.map sigma.fst L)), (add L (zero L) x) = x
 | [] punit.star := rfl
 | (t₀ :: []) x₀ := @comm_ring.zero_add t₀.1 t₀.2 x₀
 | (t₀ :: t₁ :: ts) (x₀, xs) := prod.mk.inj_iff.2 ⟨@comm_ring.zero_add t₀.1 t₀.2 x₀, zero_add (t₁ :: ts) xs⟩

theorem add_zero : Π (L : list Σ t : Type.{u}, comm_ring t) (x : tuple (list.map sigma.fst L)), (add L x (zero L)) = x
 | [] punit.star := rfl
 | (t₀ :: []) x₀ := @comm_ring.add_zero t₀.1 t₀.2 x₀
 | (t₀ :: t₁ :: ts) (x₀, xs) := prod.mk.inj_iff.2 ⟨@comm_ring.add_zero t₀.1 t₀.2 x₀, add_zero (t₁ :: ts) xs⟩

def neg : Π L : list Σ t : Type.{u}, comm_ring t, tuple (list.map sigma.fst L) → tuple (list.map sigma.fst L)
 | [] punit.star := punit.star
 | (t₀ :: []) x₀ := @comm_ring.neg t₀.1 t₀.2 x₀
 | (t₀ :: t₁ :: ts) (x₀, xs) := (@comm_ring.neg t₀.1 t₀.2 x₀, neg (t₁ :: ts) xs)

theorem add_left_neg : Π (L : list Σ t : Type.{u}, comm_ring t) (x : tuple (list.map sigma.fst L)), (add L (neg L x) x) = zero L
 | [] punit.star := rfl
 | (t₀ :: []) x₀ := @comm_ring.add_left_neg t₀.1 t₀.2 x₀
 | (t₀ :: t₁ :: ts) (x₀, xs) := prod.mk.inj_iff.2 ⟨@comm_ring.add_left_neg t₀.1 t₀.2 x₀, add_left_neg (t₁ :: ts) xs⟩

theorem add_comm : Π (L : list Σ t : Type.{u}, comm_ring t) (x y : tuple (list.map sigma.fst L)), add L x y = add L y x
 | [] punit.star punit.star := rfl
 | (t₀ :: []) x₀ y₀ := @comm_ring.add_comm t₀.1 t₀.2 x₀ y₀
 | (t₀ :: t₁ :: ts) (x₀, xs) (y₀, ys) := prod.mk.inj_iff.2 ⟨(@comm_ring.add_comm t₀.1 t₀.2 x₀ y₀), (add_comm (t₁ :: ts) xs ys)⟩

def mul : Π L : list Σ t : Type.{u}, comm_ring t, tuple (list.map sigma.fst L) → tuple (list.map sigma.fst L) → tuple (list.map sigma.fst L)
 | [] punit.star punit.star := punit.star
 | (t₀ :: []) x₀ y₀ := @comm_ring.mul t₀.1 t₀.2 x₀ y₀
 | (t₀ :: t₁ :: ts) (x₀, xs) (y₀, ys) := (@comm_ring.mul t₀.1 t₀.2 x₀ y₀, mul (t₁ :: ts) xs ys)

theorem mul_assoc : Π (L : list Σ t : Type.{u}, comm_ring t) (x y z : tuple (list.map sigma.fst L)), (mul L (mul L x y) z) = (mul L x (mul L y z))
 | [] punit.star punit.star punit.star := rfl
 | (t₀ :: []) x₀ y₀ z₀ := @comm_ring.mul_assoc t₀.1 t₀.2 x₀ y₀ z₀
 | (t₀ :: t₁ :: ts) (x₀, xs) (y₀, ys) (z₀, zs) := prod.mk.inj_iff.2 ⟨@comm_ring.mul_assoc t₀.1 t₀.2 x₀ y₀ z₀, mul_assoc (t₁ :: ts) xs ys zs⟩

def one : Π L : list Σ t : Type.{u}, comm_ring t, tuple (list.map sigma.fst L)
 | [] := punit.star
 | (t₀ :: []) := @comm_ring.one t₀.1 t₀.2
 | (t₀ :: t₁ :: ts) := (@comm_ring.one t₀.1 t₀.2, one (t₁ :: ts))

theorem one_mul : Π (L : list Σ t : Type.{u}, comm_ring t) (x : tuple (list.map sigma.fst L)), (mul L (one L) x) = x
 | [] punit.star := rfl
 | (t₀ :: []) x₀ := @comm_ring.one_mul t₀.1 t₀.2 x₀
 | (t₀ :: t₁ :: ts) (x₀, xs) := prod.mk.inj_iff.2 ⟨@comm_ring.one_mul t₀.1 t₀.2 x₀, one_mul (t₁ :: ts) xs⟩

theorem mul_one : Π (L : list Σ t : Type.{u}, comm_ring t) (x : tuple (list.map sigma.fst L)), (mul L x (one L)) = x
 | [] punit.star := rfl
 | (t₀ :: []) x₀ := @comm_ring.mul_one t₀.1 t₀.2 x₀
 | (t₀ :: t₁ :: ts) (x₀, xs) := prod.mk.inj_iff.2 ⟨@comm_ring.mul_one t₀.1 t₀.2 x₀, mul_one (t₁ :: ts) xs⟩

theorem left_distrib : Π (L : list Σ t : Type.{u}, comm_ring t) (x y z : tuple (list.map sigma.fst L)), (mul L x (add L y z)) = add L (mul L x y) (mul L x z)
 | [] punit.star punit.star punit.star := rfl
 | (t₀ :: []) x₀ y₀ z₀ := @comm_ring.left_distrib t₀.1 t₀.2 x₀ y₀ z₀
 | (t₀ :: t₁ :: ts) (x₀, xs) (y₀, ys) (z₀, zs) := prod.mk.inj_iff.2 ⟨@comm_ring.left_distrib t₀.1 t₀.2 x₀ y₀ z₀, left_distrib (t₁ :: ts) xs ys zs⟩

theorem right_distrib : Π (L : list Σ t : Type.{u}, comm_ring t) (x y z : tuple (list.map sigma.fst L)), (mul L (add L x y) z) = add L (mul L x z) (mul L y z)
 | [] punit.star punit.star punit.star := rfl
 | (t₀ :: []) x₀ y₀ z₀ := @comm_ring.right_distrib t₀.1 t₀.2 x₀ y₀ z₀
 | (t₀ :: t₁ :: ts) (x₀, xs) (y₀, ys) (z₀, zs) := prod.mk.inj_iff.2 ⟨@comm_ring.right_distrib t₀.1 t₀.2 x₀ y₀ z₀, right_distrib (t₁ :: ts) xs ys zs⟩

theorem mul_comm : Π (L : list Σ t : Type.{u}, comm_ring t) (x y : tuple (list.map sigma.fst L)), mul L x y = mul L y x
 | [] punit.star punit.star := rfl
 | (t₀ :: []) x₀ y₀ := @comm_ring.mul_comm t₀.1 t₀.2 x₀ y₀
 | (t₀ :: t₁ :: ts) (x₀, xs) (y₀, ys) := prod.mk.inj_iff.2 ⟨(@comm_ring.mul_comm t₀.1 t₀.2 x₀ y₀), (mul_comm (t₁ :: ts) xs ys)⟩

instance (L : list Σ t : Type.{u}, comm_ring t) : comm_ring $ tuple (list.map sigma.fst L) :=
{ add            := add L,
  add_assoc      := add_assoc L,
  zero           := zero L,
  zero_add       := zero_add L,
  add_zero       := add_zero L,
  neg            := neg L,
  add_left_neg   := add_left_neg L,
  add_comm       := add_comm L,
  mul            := mul L,
  mul_assoc      := mul_assoc L,
  one            := one L,
  one_mul        := one_mul L,
  mul_one        := mul_one L,
  left_distrib   := left_distrib L,
  right_distrib  := right_distrib L,
  mul_comm       := mul_comm L }

end product

namespace indexed_product

variables {I : Type u} (β : I → Type u) (H : ∀ i:I, comm_ring $ β i) (z : I)
variables (α : Type u) [comm_ring α]

structure tuple :=
(coordinate : Π i:I, β i)

variables {β}

theorem tuple.ext : Π {f g : tuple β}, (∀ i, f.coordinate i = g.coordinate i) → f = g
| ⟨f⟩ ⟨g⟩ h := congr_arg tuple.mk $ funext h

variables (β)

variables (f g h : tuple β)

def add : tuple β → tuple β → tuple β :=
λ f g, ⟨λ i, @comm_ring.add (β i) (H i) (f.coordinate i) (g.coordinate i)⟩

theorem add_assoc : add β H (add β H f g) h = add β H f (add β H g h) :=
tuple.ext $ λ i, @comm_ring.add_assoc (β i) (H i) (f.coordinate i) (g.coordinate i) (h.coordinate i)

def zero : tuple β :=
⟨λ i, @comm_ring.zero (β i) (H i)⟩

theorem zero_add : add β H (zero β H) f = f :=
tuple.ext $ λ i, @comm_ring.zero_add (β i) (H i) (f.coordinate i)

theorem add_zero : add β H f (zero β H) = f :=
tuple.ext $ λ i, @comm_ring.add_zero (β i) (H i) (f.coordinate i)

def neg : tuple β → tuple β :=
λ f, ⟨λ i, @comm_ring.neg (β i) (H i) (f.coordinate i)⟩

theorem add_left_neg : add β H (neg β H f) f = zero β H :=
tuple.ext $ λ i, @comm_ring.add_left_neg (β i) (H i) (f.coordinate i)

theorem add_comm : add β H f g = add β H g f :=
tuple.ext $ λ i, @comm_ring.add_comm (β i) (H i) (f.coordinate i) (g.coordinate i)

def mul : tuple β → tuple β → tuple β :=
λ f g, ⟨λ i, @comm_ring.mul (β i) (H i) (f.coordinate i) (g.coordinate i)⟩

theorem mul_assoc : mul β H (mul β H f g) h = mul β H f (mul β H g h) :=
tuple.ext $ λ i, @comm_ring.mul_assoc (β i) (H i) (f.coordinate i) (g.coordinate i) (h.coordinate i)

def one : tuple β :=
⟨λ i, @comm_ring.one (β i) (H i)⟩

theorem one_mul : mul β H (one β H) f = f :=
tuple.ext $ λ i, @comm_ring.one_mul (β i) (H i) (f.coordinate i)

theorem mul_one : mul β H f (one β H) = f :=
tuple.ext $ λ i, @comm_ring.mul_one (β i) (H i) (f.coordinate i)

theorem left_distrib : mul β H f (add β H g h) = add β H (mul β H f g) (mul β H f h) :=
tuple.ext $ λ i, @comm_ring.left_distrib (β i) (H i) (f.coordinate i) (g.coordinate i) (h.coordinate i)

theorem right_distrib : mul β H (add β H f g) h = add β H (mul β H f h) (mul β H g h) :=
tuple.ext $ λ i, @comm_ring.right_distrib (β i) (H i) (f.coordinate i) (g.coordinate i) (h.coordinate i)

theorem mul_comm : mul β H f g = mul β H g f :=
tuple.ext $ λ i, @comm_ring.mul_comm (β i) (H i) (f.coordinate i) (g.coordinate i)

instance : comm_ring (tuple β) :=
{ add            := add β H,
  add_assoc      := add_assoc β H,
  zero           := zero β H,
  zero_add       := zero_add β H,
  add_zero       := add_zero β H,
  neg            := neg β H,
  add_left_neg   := add_left_neg β H,
  add_comm       := add_comm β H,
  mul            := mul β H,
  mul_assoc      := mul_assoc β H,
  one            := one β H,
  one_mul        := one_mul β H,
  mul_one        := mul_one β H,
  left_distrib   := left_distrib β H,
  right_distrib  := right_distrib β H,
  mul_comm       := mul_comm β H }

def proj : tuple β → β z :=
λ f, f.coordinate z

instance proj.is_hom : @@is_hom (indexed_product.comm_ring β H) (H z) (proj β z) :=
by refine {..}; intros; refl

variable (I)

def diagonal : α → tuple (λ i:I, α) :=
λ x, ⟨λ i, x⟩

variable {I}

instance diagonal.is_hom : @@is_hom _ (indexed_product.comm_ring (λ i, α) (λ i, _inst_1)) (diagonal I α) :=
by refine {..}; intros; refl

def factor {γ : Type u} : (Π i:I, γ → β i) → (γ → tuple β)
| f := λ x, ⟨λ i, f i x⟩

def factor.comm (γ : Type u) (f : Π i:I, γ → β i) : ∀ i:I, f i = (proj β i) ∘ (factor β f) :=
λ i, rfl

def factor.unique (γ : Type u) (f : Π i:I, γ → β i) (factor' : γ → tuple β) : (∀ i:I, f i = (proj β i) ∘ factor') → factor' = factor β f :=
λ h, funext $ λ x, tuple.ext $ λ i, eq.symm $ @congr_fun _ _ _ _ (h i) x

end indexed_product
