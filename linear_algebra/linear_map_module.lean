/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau

Type of linear functions
-/
import linear_algebra.basic
  linear_algebra.prod_module
  linear_algebra.quotient_module
  linear_algebra.subtype_module
noncomputable theory
local attribute [instance] classical.prop_decidable

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace classical

lemma some_spec2 {α : Type u} {p : α → Prop} {h : ∃a, p a} (q : α → Prop) (hpq : ∀a, p a → q a) :
  q (some h) :=
hpq _ $ some_spec _

end classical

/-- The type of linear maps `β → γ` between α-modules β and γ -/
def linear_map {α : Type u} (β : Type v) (γ : Type w) [ring α] [module α β] [module α γ] :=
subtype (@is_linear_map α β γ _ _ _)

namespace linear_map
variables [ring α] [module α β] [module α γ]
variables {r : α} {A B C : linear_map β γ} {x y : β}
include α

instance : has_coe_to_fun (linear_map β γ) := ⟨_, subtype.val⟩

theorem ext (h : ∀ x, A x = B x) : A = B := subtype.eq $ funext h

lemma is_linear_map_coe : is_linear_map A := A.property

@[simp] lemma map_add  : A (x + y) = A x + A y := is_linear_map_coe.add x y
@[simp] lemma map_smul : A (r • x) = r • A x := is_linear_map_coe.smul r x
@[simp] lemma map_zero : A 0 = 0 := is_linear_map_coe.zero
@[simp] lemma map_neg  : A (-x) = -A x := is_linear_map_coe.neg _
@[simp] lemma map_sub  : A (x - y) = A x - A y := is_linear_map_coe.sub _ _

/- kernel -/

/-- Kernel of a linear map, i.e. the set of vectors mapped to zero by the map -/
def ker (A : linear_map β γ) : set β := {y | A y = 0}

section ker

@[simp] lemma mem_ker : x ∈ A.ker ↔ A x = 0 := iff.rfl

theorem ker_of_map_eq_map (h : A x = A y) : x - y ∈ A.ker :=
by rw [mem_ker, map_sub]; exact sub_eq_zero_of_eq h

theorem inj_of_trivial_ker (H : A.ker ⊆ {0}) (h : A x = A y) : x = y :=
eq_of_sub_eq_zero $ set.eq_of_mem_singleton $ H $ ker_of_map_eq_map h

variables (α A)

instance ker.is_submodule : is_submodule A.ker :=
{ zero_ := map_zero,
  add_ := λ x y HU HV, by rw mem_ker at *; simp [HU, HV, mem_ker],
  smul := λ r x HV, by rw mem_ker at *; simp [HV] }

theorem sub_ker (HU : x ∈ A.ker) (HV : y ∈ A.ker) : x - y ∈ A.ker :=
is_submodule.sub HU HV

end ker

/- image -/

/-- Image of a linear map, the set of vectors of the form `A x` for some β -/
def im (A : linear_map β γ) : set γ := {x | ∃ y, A y = x}

@[simp] lemma mem_im {A : linear_map β γ} {z : γ} :
  z ∈ A.im ↔ ∃ y, A y = z := iff.rfl

instance im.is_submodule : is_submodule A.im :=
{ zero_ := ⟨0, map_zero⟩,
  add_ := λ a b ⟨x, hx⟩ ⟨y, hy⟩, ⟨x + y, by simp [hx, hy]⟩,
  smul := λ r a ⟨x, hx⟩, ⟨r • x, by simp [hx]⟩ }

/- equivalences -/
section
open is_submodule

/-- first isomorphism law -/
def quot_ker_equiv_im (f : linear_map β γ) : (quotient β f.ker) ≃ₗ f.im :=
{ to_fun     := is_submodule.quotient.lift _
    (is_linear_map_subtype_mk f.1 f.2 $ assume b, ⟨b, rfl⟩) (assume b eq, subtype.eq eq),
  inv_fun    := λb, @quotient.mk _ (quotient_rel _) (classical.some b.2),
  left_inv   := assume b', @quotient.induction_on _ (quotient_rel _) _ b' $
    begin
      assume b,
      apply quotient.sound,
      apply classical.some_spec2 (λa, f (a - b) = 0),
      show (∀a, f a = f b → f (a - b) = 0), simp {contextual := tt}
    end,
  right_inv  := assume c, subtype.eq $ classical.some_spec2 (λa, f a = c) $ assume b, id,
  linear_fun :=
    is_linear_map_quotient_lift _ $ @is_linear_map_subtype_mk _ _ _ _ _ _ f.im _ f f.2 _ }

lemma is_submodule.add_left_iff {s : set β} [is_submodule s] {b₁ b₂ : β} (h₂ : b₂ ∈ s) :
  b₁ + b₂ ∈ s ↔ b₁ ∈ s :=
iff.intro
  (assume h,
    have b₁ + b₂ - b₂ ∈ s, from is_submodule.sub h h₂,
    by rwa [add_sub_cancel] at this)
  (assume h₁, is_submodule.add h₁ h₂)

lemma is_submodule.neg_iff {s : set β} [is_submodule s] {b : β} :
  - b ∈ s ↔ b ∈ s :=
iff.intro
  (assume h,
    have - - b ∈ s, from is_submodule.neg h,
    by rwa [neg_neg] at this)
  is_submodule.neg

/-- second isomorphism law -/
def union_quotient_equiv_quotient_inter {s t : set β} [is_submodule s] [is_submodule t] :
  quotient s (subtype.val ⁻¹' (s ∩ t)) ≃ₗ quotient (span (s ∪ t)) (subtype.val ⁻¹' t) :=
let sel₁ : s → span (s ∪ t) := λb, ⟨b.1, subset_span $ or.inl b.2⟩ in
have sel₁_val : ∀b:s, (sel₁ b).1 = b.1, from assume b, rfl,
have ∀b'∈span (s ∪ t), ∃x:s, ∃y∈t, b' = x.1 + y,
  by simp [span_union, span_eq_of_is_submodule, _inst_4, _inst_5] {contextual := tt},
let sel₂ : span (s ∪ t) → s := λb', classical.some (this b'.1 b'.2) in
have sel₂_spec : ∀b':span (s ∪ t), ∃y∈t, b'.1 = (sel₂ b').1 + y,
  from assume b', classical.some_spec (this b'.1 b'.2),
{ to_fun :=
  begin
    intro b,
    fapply @quotient.lift_on _ _ (quotient_rel _) b,
    { intro b', apply quotient.mk, exact (sel₁ b') },
    { intros b₁ b₂ h, apply quotient.sound, simp [quotient_rel_eq, *] at * }
  end,
  inv_fun :=
  begin
    intro b,
    fapply @quotient.lift_on _ _ (quotient_rel _) b,
    { intro b', apply quotient.mk, exact sel₂ b' },
    { intros b₁ b₂ h,
      rcases (sel₂_spec b₁) with ⟨c₁, hc₁, eq_c₁⟩,
      rcases (sel₂_spec b₂) with ⟨c₂, hc₂, eq_c₂⟩,
      have : ((sel₂ b₁).1 - (sel₂ b₂).1) + (c₁ - c₂) ∈ t,
      { simpa [quotient_rel_eq, eq_c₁, eq_c₂, add_comm, add_left_comm, add_assoc] using h },
      have ht : (sel₂ b₁).1 - (sel₂ b₂).1 ∈ t,
      { rwa [is_submodule.add_left_iff (is_submodule.sub hc₁ hc₂)] at this },
      have hs : (sel₂ b₁).1 - (sel₂ b₂).1 ∈ s,
      { from is_submodule.sub (sel₂ b₁).2 (sel₂ b₂).2 },
      apply quotient.sound,
      simp [quotient_rel_eq, *] at * }
  end,
  right_inv := assume b', @quotient.induction_on _ (quotient_rel _) _ b'
  begin
    intro b, apply quotient.sound,
    rcases (sel₂_spec b) with ⟨c, hc, eq_c⟩,
    simp [quotient_rel_eq, eq_c, hc, is_submodule.neg_iff]
  end,
  left_inv := assume b', @quotient.induction_on _ (quotient_rel _) _ b'
  begin
    intro b, apply quotient.sound,
    rcases (sel₂_spec (sel₁ b)) with ⟨c, hc, eq⟩,
    have b_eq : b.1 = c + (sel₂ (sel₁ b)).1,
    { simpa [sel₁_val] using eq },
    have : b.1 ∈ s, from b.2,
    have hcs : c ∈ s,
    { rwa [b_eq, is_submodule.add_left_iff (sel₂ (sel₁ b)).2] at this },
    show (sel₂ (sel₁ b) - b).1 ∈ s ∩ t, { simp [eq, hc, hcs, is_submodule.neg_iff] }
  end,
  linear_fun :=  is_linear_map_quotient_lift _ $ (is_linear_map_quotient_mk _).comp $
    is_linear_map_subtype_mk _ (is_linear_map_subtype_val is_linear_map.id) _ }

end

section add_comm_group

instance : has_add (linear_map β γ) := ⟨λhf hg, ⟨_, hf.2.map_add hg.2⟩⟩
instance : has_zero (linear_map β γ) := ⟨⟨_, is_linear_map.map_zero⟩⟩
instance : has_neg (linear_map β γ) := ⟨λhf, ⟨_, hf.2.map_neg⟩⟩

@[simp] lemma add_app : (A + B) x = A x + B x := rfl
@[simp] lemma zero_app : (0 : linear_map β γ) x = 0 := rfl
@[simp] lemma neg_app : (-A) x = -A x := rfl

instance : add_comm_group (linear_map β γ) :=
by refine {add := (+), zero := 0, neg := has_neg.neg, ..}; { intros, apply ext, simp }

end add_comm_group

end linear_map

namespace linear_map
variables [comm_ring α] [module α β] [module α γ]

instance : has_scalar α (linear_map β γ) := ⟨λr f, ⟨λb, r • f b, f.2.map_smul_right⟩⟩

@[simp] lemma smul_app {r : α} {x : β} {A : linear_map β γ} : (r • A) x = r • (A x) := rfl

variables (α β γ)

instance : module α (linear_map β γ) :=
by refine {smul := (•), ..linear_map.add_comm_group, ..};
  { intros, apply ext, simp [smul_add, add_smul, mul_smul] }

end linear_map

namespace module
variables [ring α] [module α β]
include α β

instance : has_one (linear_map β β) := ⟨⟨id, is_linear_map.id⟩⟩
instance : has_mul (linear_map β β) := ⟨λf g, ⟨_, is_linear_map.comp f.2 g.2⟩⟩

@[simp] lemma one_app (x : β) : (1 : linear_map β β) x = x := rfl
@[simp] lemma mul_app (A B : linear_map β β) (x : β) : (A * B) x = A (B x) := rfl

variables (α β)

-- declaring this an instance breaks `real.lean` with reaching max. instance resolution depth
def endomorphism_ring : ring (linear_map β β) :=
by refine {mul := (*), one := 1, ..linear_map.add_comm_group, ..};
  { intros, apply linear_map.ext, simp }

/-- The group of invertible linear maps from `β` to itself -/
def general_linear_group :=
by haveI := endomorphism_ring α β; exact units (linear_map β β)

end module
