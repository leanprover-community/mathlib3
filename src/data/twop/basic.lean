/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.field
import category_theory.concrete_category.bundled
import category_theory.monoidal.category
import category_theory.category.Bipointed
import data.fintype.basic
import data.real.basic
import data.sum.basic
import data.two_pointing
import order.bounded_order

/-!
# Pointed sum and two-pointed types

## TODO

`card (two_pointing α) = card α * (card α - 1)`
-/

open category_theory function set sum

universes u
variables {α β γ δ ε F : Type*}

/-! ### Pointed sum -/

namespace pointed_sum
variables {𝒶 a : α} {𝒷 b : β} {x y z : α ⊕ β}

/-- Glues `sum.inl 𝒶` and `sum.inr 𝒷` and nothing else. -/
inductive rel (𝒶 : α) (𝒷 : β) : α ⊕ β → α ⊕ β → Prop
| refl (x : α ⊕ β) : rel x x
| inl_inr : rel (inl 𝒶) (inr 𝒷)
| inr_inl : rel (inr 𝒷) (inl 𝒶)

attribute [refl] rel.refl

lemma rel.rfl : rel 𝒶 𝒷 x x := rel.refl _

@[symm] lemma rel.symm : rel 𝒶 𝒷 x y → rel 𝒶 𝒷 y x := by rintro (_ | _ | _); constructor

lemma rel_comm : rel 𝒶 𝒷 x y ↔ rel 𝒶 𝒷 y x := ⟨rel.symm, rel.symm⟩

@[trans] lemma rel.trans : ∀ {x y z}, rel 𝒶 𝒷 x y → rel 𝒶 𝒷 y z → rel 𝒶 𝒷 x z
| _ _ _ (rel.refl _) (rel.refl _)   := rel.refl _
| _ _ _ (rel.refl _) rel.inl_inr  := rel.inl_inr
| _ _ _ (rel.refl _) rel.inr_inl  := rel.inr_inl
| _ _ _ rel.inl_inr  (rel.refl _) := rel.inl_inr
| _ _ _ rel.inr_inl  (rel.refl _) := rel.inr_inl
| _ _ _ rel.inl_inr  rel.inr_inl  := rel.refl _
| _ _ _ rel.inr_inl  rel.inl_inr  := rel.refl _

lemma rel.equivalence : equivalence (rel 𝒶 𝒷) := by tidy; apply rel.trans; assumption

@[simp] lemma rel_inl_inl_iff {a b : α} : rel 𝒶 𝒷 (inl a) (inl b) ↔ a = b :=
⟨λ h, by { cases h, refl }, by { rintro rfl, exact rel.refl _ }⟩

@[simp] lemma rel_inl_inr_iff {a : α} {b : β} : rel 𝒶 𝒷 (inl a) (inr b) ↔ a = 𝒶 ∧ b = 𝒷 :=
⟨λ h, by { cases h, exact ⟨rfl, rfl⟩ }, by { rintro ⟨rfl, rfl⟩, exact rel.inl_inr }⟩

@[simp] lemma rel_inr_inl_iff {a : α} {b : β} : rel 𝒶 𝒷 (inr b) (inl a) ↔ a = 𝒶 ∧ b = 𝒷 :=
⟨λ h, by { cases h, exact ⟨rfl, rfl⟩ }, by { rintro ⟨rfl, rfl⟩, exact rel.inr_inl }⟩

@[simp] lemma rel_inr_inr_iff {a b : β} : rel 𝒶 𝒷 (inr a) (inr b) ↔ a = b :=
⟨λ h, by { cases h, refl }, by { rintro rfl, exact rel.refl _ }⟩

variables (𝒶 𝒷)

instance [decidable_eq α] [decidable_eq β] : decidable_rel (rel 𝒶 𝒷)
| (sum.inl a) (sum.inl b) := decidable_of_iff' _ rel_inl_inl_iff
| (sum.inl a) (sum.inr b) := decidable_of_iff' _ rel_inl_inr_iff
| (sum.inr a) (sum.inl b) := decidable_of_iff' _ rel_inr_inl_iff
| (sum.inr a) (sum.inr b) := decidable_of_iff' _ rel_inr_inr_iff

/-- The quotient of `α ⊕ β` by `sum.inl 𝒶 = sum.inr 𝒷`. -/
def rel.setoid : setoid (α ⊕ β) := ⟨rel 𝒶 𝒷, rel.equivalence⟩

/-- The sum of `α` and `β` pointed at `𝒶` and `𝒷`. -/
def _root_.pointed_sum : Type* := quotient (pointed_sum.rel.setoid 𝒶 𝒷)

notation 𝒶 ` ⊕ₚ `:30 𝒷:29 := pointed_sum 𝒶 𝒷

/-- The map to the left component of `𝒶 ⊕ₚ 𝒷`. -/
def inl (a : α) : 𝒶 ⊕ₚ 𝒷 := @quotient.mk _ (rel.setoid _ _) (inl a)

/-- The map to the right component of `𝒶 ⊕ₚ 𝒷`. -/
def inr (b : β) : 𝒶 ⊕ₚ 𝒷 := @quotient.mk _ (rel.setoid _ _) (inr b)

instance : inhabited (𝒶 ⊕ₚ 𝒷) := ⟨inl 𝒶 𝒷 𝒶⟩

instance [decidable_eq α] [decidable_eq β] : decidable_eq (𝒶 ⊕ₚ 𝒷) :=
@quotient.decidable_eq _ (pointed_sum.rel.setoid 𝒶 𝒷) $ rel.decidable_rel _ _

variables {𝒶 𝒷 a b}

@[simp] lemma inl_inj {b : α} : inl 𝒶 𝒷 a = inl 𝒶 𝒷 b ↔ a = b :=
(@quotient.eq _ (rel.setoid 𝒶 𝒷) _ _).trans rel_inl_inl_iff

@[simp] lemma inl_eq_inr_iff : inl 𝒶 𝒷 a = inr 𝒶 𝒷 b ↔ a = 𝒶 ∧ b = 𝒷 :=
(@quotient.eq _ (rel.setoid 𝒶 𝒷) _ _).trans rel_inl_inr_iff

@[simp] lemma inr_inj {a b : β} : inr 𝒶 𝒷 a = inr 𝒶 𝒷 b ↔ a = b :=
(@quotient.eq _ (rel.setoid 𝒶 𝒷) _ _).trans rel_inr_inr_iff

@[simp] lemma inr_eq_inl_iff : inr 𝒶 𝒷 b = inl 𝒶 𝒷 a ↔ a = 𝒶 ∧ b = 𝒷 :=
(@quotient.eq _ (rel.setoid 𝒶 𝒷) _ _).trans rel_inr_inl_iff

lemma inl_injective : injective (inl 𝒶 𝒷) := λ _ _, inl_inj.1
lemma inr_injective : injective (inr 𝒶 𝒷) := λ _ _, inr_inj.1

lemma inl_eq_inr : inl 𝒶 𝒷 𝒶 = inr 𝒶 𝒷 𝒷 := @quotient.sound _ (rel.setoid 𝒶 𝒷) _ _ rel.inl_inr
lemma inr_eq_inl : inr 𝒶 𝒷 𝒷 = inl 𝒶 𝒷 𝒶 := @quotient.sound _ (rel.setoid 𝒶 𝒷) _ _ rel.inr_inl

lemma inl_ne_inr_left (h : a ≠ 𝒶) : inl 𝒶 𝒷 a ≠ inr 𝒶 𝒷 b := λ hab, h (inl_eq_inr_iff.1 hab).1
lemma inl_ne_inr_right (h : b ≠ 𝒷) : inl 𝒶 𝒷 a ≠ inr 𝒶 𝒷 b := λ hab, h (inl_eq_inr_iff.1 hab).2

@[elab_as_eliminator]
protected lemma ind {f : 𝒶 ⊕ₚ 𝒷 → Prop} (h𝒶 : ∀ a, f (inl 𝒶 𝒷 a)) (h𝒷 : ∀ b, f (inr 𝒶 𝒷 b)) :
  ∀ i, f i :=
@quotient.ind _ (rel.setoid 𝒶 𝒷) _ $ by { refine sum.rec _ _, exacts [h𝒶, h𝒷] }

section fintype
variables (α 𝒷) [decidable_eq α] [decidable_eq β] [fintype α] [fintype β]

instance : fintype (𝒶 ⊕ₚ 𝒷) := @quotient.fintype _ _ (rel.setoid 𝒶 𝒷) $ rel.decidable_rel 𝒶 𝒷

-- lemma _root_.fintype.card_pointed_sum :
--   fintype.card (𝒶 ⊕ₚ 𝒷) = fintype.card α + fintype.card β - 1 :=
-- begin
--   sorry
-- end

end fintype

section lift_rel
variables (𝒶 𝒷) (r : α → α → Prop) (s : β → β → Prop)

/-- Lifts a relation to `𝒶 ⊕ₚ 𝒷` summand-wise. -/
inductive lift_rel : 𝒶 ⊕ₚ 𝒷 → 𝒶 ⊕ₚ 𝒷 → Prop
| inl {a b} : r a b → lift_rel (inl _ _ a) (inl _ _ b)
| inr {a b} : s a b → lift_rel (inr _ _ a) (inr _ _ b)

end lift_rel

section lift_trans_rel
variables (𝒶 𝒷) (r : α → α → Prop) (s : β → β → Prop)

/-- Lifts a relation to `𝒶 ⊕ₚ 𝒷` summand-wise while making sure it stays transitive. -/
inductive lift_trans_rel : 𝒶 ⊕ₚ 𝒷 → 𝒶 ⊕ₚ 𝒷 → Prop
| inl {a b} : r a b → lift_trans_rel (inl _ _ a) (inl _ _ b)
| inr {a b} : s a b → lift_trans_rel (inr _ _ a) (inr _ _ b)
| inl_inr {a b} : r a 𝒶 → s 𝒷 b → lift_trans_rel (inl _ _ a) (inr _ _ b)
| inr_inl {a b} : s b 𝒷 → r 𝒶 a → lift_trans_rel (inr _ _ b) (inl _ _ a)

variables {𝒶 𝒷 r s}

-- instance [is_refl α r] [is_refl β s] : is_refl (𝒶 ⊕ₚ 𝒷) (lift_trans_rel 𝒶 𝒷 r s) :=
-- ⟨λ x, begin
--   sorry
-- end⟩

-- instance [is_irrefl α r] [is_irrefl β s] : is_irrefl (𝒶 ⊕ₚ 𝒷) (lift_trans_rel 𝒶 𝒷 r s) :=
-- ⟨λ a h, match a, h with
--   | _, lift_trans_rel.inl h := sorry
--   | _, lift_trans_rel.inr h := sorry
-- end⟩

-- @[trans] lemma lift_trans_rel.trans [is_trans α r] [is_trans β s] :
--   ∀ {a b c}, lift_trans_rel 𝒶 𝒷 r s a b → lift_trans_rel 𝒶 𝒷 r s b c → lift_trans_rel 𝒶 𝒷 r s a c
-- -- | _ _ _ (lift_trans_rel.inl hab) (lift_trans_rel.inl hbc) := lift_trans_rel.inl $ trans hab hbc
-- -- | _ _ _ (lift_trans_rel.inr hab) (lift_trans_rel.inr hbc) := lift_trans_rel.inr $ trans hab hbc
-- := sorry

-- instance [is_trans α r] [is_trans β s] : is_trans (𝒶 ⊕ₚ 𝒷) (lift_trans_rel 𝒶 𝒷 r s) :=
-- ⟨λ _ _ _, lift_trans_rel.trans _ _⟩

-- instance [is_antisymm α r] [is_antisymm β s] : is_antisymm (𝒶 ⊕ₚ 𝒷) (lift_trans_rel 𝒶 𝒷 r s) :=
-- ⟨sorry⟩

end lift_trans_rel

variables {𝒸 : γ} {𝒹 : δ}

/-- Maps a pointed sum summand-wise. -/
def map (f : α → γ) (g : β → δ) (hf : f 𝒶 = 𝒸) (hg : g 𝒷 = 𝒹) : 𝒶 ⊕ₚ 𝒷 → 𝒸 ⊕ₚ 𝒹 :=
quot.map (sum.map f g) $ begin
  rintro x y (h | h | h),
  { exact pointed_sum.rel.rfl },
  { rw [map_inl, map_inr, hf, hg],
    exact pointed_sum.rel.inl_inr },
  { rw [map_inl, map_inr, hf, hg],
    exact pointed_sum.rel.inr_inl }
end

variables (f : α → γ) (g : β → δ) {hf : f 𝒶 = 𝒸} {hg : g 𝒷 = 𝒹}

@[simp] lemma map_inl (a : α) : map f g hf hg (inl _ _ a) = inl _ _ (f a) := rfl
@[simp] lemma map_inr (b : β) : map f g hf hg (inr _ _ b) = inr _ _ (g b) := rfl

@[simp] lemma map_id_id (𝒶 𝒷) : map (@id α) (@id β) (eq.refl 𝒶) (eq.refl 𝒷) = id :=
funext $ λ x, quotient.induction_on' x $ λ x, sum.rec_on x (λ _, rfl) (λ _, rfl)

@[simp] lemma map_map {ℯ : ε} {𝒻 : F} (f₁ : γ → ε) (g₁ : δ → F) (f₂ : α → γ) (g₂ : β → δ)
  {hf₁ : f₁ 𝒸 = ℯ} {hg₁ : g₁ 𝒹 = 𝒻} {hf₂ : f₂ 𝒶 = 𝒸} {hg₂ : g₂ 𝒷 = 𝒹} (x : 𝒶 ⊕ₚ 𝒷) :
  (x.map f₂ g₂ hf₂ hg₂).map f₁ g₁ hf₁ hg₁ =
    x.map (f₁ ∘ f₂) (g₁ ∘ g₂) ((congr_arg _ hf₂).trans hf₁) ((congr_arg _ hg₂).trans hg₁) :=
quotient.induction_on' x $ λ x, sum.rec_on x (λ a, rfl) (λ b, rfl)

@[simp] lemma map_comp_map {ℯ : ε} {𝒻 : F} (f₁ : γ → ε) (g₁ : δ → F) (f₂ : α → γ) (g₂ : β → δ)
  {hf₁ : f₁ 𝒸 = ℯ} {hg₁ : g₁ 𝒹 = 𝒻} {hf₂ : f₂ 𝒶 = 𝒸} {hg₂ : g₂ 𝒷 = 𝒹} :
  (map f₁ g₁ hf₁ hg₁) ∘ (map f₂ g₂ hf₂ hg₂) =
    map (f₁ ∘ f₂) (g₁ ∘ g₂) ((congr_arg _ hf₂).trans hf₁) ((congr_arg _ hg₂).trans hg₁) :=
funext $ map_map _ _ _ _

end pointed_sum

open pointed_sum

namespace prod
variables (p : α × α) (q : β × β)

/-- The pointed sum of two two-pointings is the pointed sum in the second point of the left and first point of the right two-pointed at the first point from the left and the second point from the
right. -/
@[simps] protected def pointed_sum : (p.snd ⊕ₚ q.fst) × (p.snd ⊕ₚ q.fst) :=
⟨inl _ _ p.fst, inr _ _ q.snd⟩

end prod

namespace two_pointing
variables (p : two_pointing α) (q : two_pointing β)

/-- The pointed sum of two two-pointings is the pointed sum in the second point of the left and first point of the right two-pointed at the first point from the left and the second point from the
right. -/
@[simps] protected def pointed_sum : two_pointing (p.snd ⊕ₚ q.fst) :=
⟨p.to_prod.pointed_sum q.to_prod, inl_ne_inr_left p.fst_ne_snd⟩

@[simp] lemma pointed_sum_fst : (p.pointed_sum q).fst = inl _ _ p.fst := rfl
@[simp] lemma pointed_sum_snd : (p.pointed_sum q).snd = inr _ _ q.snd := rfl

end two_pointing

/-- Two-points a bounded order at its bottom and top elements. -/
@[reducible] -- See note [reducible non instances]
def bounded_order.to_two_pointing [partial_order α] [bounded_order α] [nontrivial α] :
  two_pointing α :=
{ fst := ⊥,
  snd := ⊤,
  fst_ne_snd := bot_ne_top }

section order
variables (𝒶 : α) (𝒷 : β)

instance [has_le α] [has_le β] : has_le (𝒶 ⊕ₚ 𝒷) := ⟨lift_trans_rel _ _ (≤) (≤)⟩
instance [has_lt α] [has_lt β] : has_lt (𝒶 ⊕ₚ 𝒷) := ⟨lift_trans_rel _ _ (<) (<)⟩

-- instance [preorder α] [preorder β] : preorder (𝒶 ⊕ₚ 𝒷) :=
-- { le := (≤),
--   lt := (<),
--   le_refl := refl_of (lift_trans_rel _ _ (≤) (≤)),
--   le_trans := λ _ _ _, trans_of (lift_trans_rel _ _ (≤) (≤)),
--   lt_iff_le_not_le := λ a b, begin
--     sorry
--   end }

-- instance [partial_order α] [partial_order β] : partial_order (𝒶 ⊕ₚ 𝒷) :=
-- { le := (≤),
--   lt := (<),
--   le_antisymm := λ _ _, antisymm_of (lift_trans_rel _ _ (≤) (≤)),
--   .. pointed_sum.preorder 𝒶 𝒷 }

end order

/-! ### Bipointed -/

namespace Bipointed

instance : monoidal_category Bipointed :=
{ tensor_obj := λ X Y, ⟨_, X.to_prod.pointed_sum Y.to_prod⟩,
  tensor_hom := λ X₁ Y₁ X₂ Y₂ f g,
    ⟨pointed_sum.map _ _ f.map_snd g.map_fst,
      by simp_rw [prod.pointed_sum_fst, pointed_sum.map_inl, f.map_fst],
      by simp_rw [prod.pointed_sum_snd, pointed_sum.map_inr, g.map_snd]⟩,
  tensor_id' := λ X Y, hom.ext _ _ $ pointed_sum.map_id_id _ _,
  tensor_comp' := λ X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂,
    hom.ext _ _ (pointed_sum.map_comp_map _ _ _ _).symm,
  tensor_unit := ⟨_, ((), ())⟩,
  associator := λ X Y Z, begin
    dsimp,
  end,
  associator_naturality' := _,
  left_unitor := λ X, begin
    dsimp,
  end,
  left_unitor_naturality' := _,
  right_unitor := _,
  right_unitor_naturality' := _,
  pentagon' := _,
  triangle' := _ }

end Bipointed

#exit

/-! ### Twop -/

/-- The category of two-pointed types. -/
def Twop : Type* := bundled two_pointing

instance : inhabited Twop := ⟨bundled.of bool⟩

instance : category Twop :=
{ hom := λ α β, α.1 → β.1,
  id := λ α, id,
  comp := λ α β γ f g, g ∘ f }

def Twop.wedge : Twop × Twop ⥤ Twop := sorry

/-- A square coalgebra on a two-pointed type `α` is a map `α → α ⊕ₚₚ α`. -/
structure sq_coalgebra (α : Type*) extends two_pointing α :=
(double_map : α → snd ⊕ₚ fst)

/-- `pointed_sum.inl` as a square coalgebra. -/
def sq_coalgebra.inl (α : Type*) [two_pointing α] : sq_coalgebra α := ⟨pointed_sum.inl _ _⟩

/-- `pointed_sum.inr` as a square coalgebra. -/
def sq_coalgebra.inr (α : Type*) [two_pointing α] : sq_coalgebra α := ⟨pointed_sum.inl _ _⟩

instance [two_pointing α] : inhabited (sq_coalgebra α) := ⟨sq_coalgebra.inl α⟩

/-- The category of square coalgebras. -/
def SqCoalgebra : Type* := bundled sq_coalgebra

instance : inhabited SqCoalgebra := ⟨@bundled.of _ bool default⟩

instance : category SqCoalgebra :=
{ hom := λ α β, α.1 → β.1,
  id := λ α, id,
  comp := λ α β γ f g, g ∘ f }

namespace SqCoalgebra

/-- The unit interval along with its doubling map as a square coalgebra. -/
def unit_interval (α : Type*) [linear_ordered_field α] : SqCoalgebra :=
{ α := Icc (0 : α) 1,
  str := begin
    refine ⟨⟨⟨0, left_mem_Icc.2 zero_le_one⟩, ⟨1, right_mem_Icc.2 zero_le_one⟩,
      ne_of_apply_ne subtype.val zero_ne_one⟩, λ a, if h : (a : α) ≤ 1/2 then _ else _⟩,
    sorry, sorry, -- insert doubling map here
  end }

lemma is_initial_unit_interval_ℚ : is_initial (unit_interval ℚ) := sorry

lemma is_terminal_unit_interval_ℝ : is_terminal (unit_interval ℝ) := sorry

end SqCoalgebra
