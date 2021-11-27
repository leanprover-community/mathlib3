/-
Copyright (c) 2021 Grayson Burton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Violeta Hernández Palacios.
-/
import tactic
import order.lattice_intervals
import order.zorn
import category_theory.conj
import data.fin.basic

/-!
# Flags of polytopes

In this file we define flags, which are maximal chains of a partial order. We prove that
automorphisms of posets induces a group action on flags. We also prove that flags contain elements
of each possible grade.
-/

open category_theory

universe u

/-- A flag is a maximal chain. -/
@[reducible] def polytope.flag (α : Type u) [has_lt α] : Type u :=
{c : set α // @zorn.is_max_chain α (<) c}

/-- The category of posets of type `α`. -/
@[instance]
private def Poset (α : Type u) [has_le α] : category (partial_order α) :=
{ hom  := λ a b, a.le →r b.le,
  id   := λ a, rel_hom.id a.le,
  comp := λ a b c hab hbc, rel_hom.comp hbc hab }

/-- The type of automorphisms of a poset. -/
def polytope.automorphism (α : Type u) [p : partial_order α] :=
@Aut (partial_order α) (Poset α) p

/-- One element covers another when there's no other element strictly in between. -/
def polytope.covers {α : Type u} [preorder α] (y x : α) : Prop :=
x < y ∧ ∀ z, ¬ z ∈ set.Ioo x y

notation x ` ⋗ `:50 y:50 := polytope.covers x y
notation x ` ⋖ `:50 y:50 := polytope.covers y x

/-- A graded order is an order homomorphism into ℕ such that:
    * `⊥` has grade 0
    * the homomorphism respects covering. -/
@[protect_proj]
class polytope.graded (α : Type u) [preorder α] extends order_bot α : Type u :=
(grade : α → ℕ)
(grade_bot : grade ⊥ = 0)
(strict_mono : strict_mono grade)
(hcovers : ∀ {x y}, x ⋖ y → grade y = grade x + 1)

/-- An abbreviation for the grade function of a graded order. -/
abbreviation polytope.grade {α : Type u} [preorder α] [polytope.graded α] : α → ℕ :=
polytope.graded.grade

/-- Grade is a relation homomorphism. -/
def polytope.graded.rel_hom (α : Type u) [preorder α] [bg : polytope.graded α] :
  @rel_hom α ℕ (<) (<) :=
⟨_, bg.strict_mono⟩

/-- If a natural covers another, it must be a successor. -/
lemma nat.succ_of_cover (m n : ℕ) : m ⋖ n → n = m + 1 := begin
  rintro ⟨hmnl, hmnr⟩,
  cases le_or_gt n (m + 1) with hnm hnm,
  exact antisymm hnm (nat.succ_le_of_lt hmnl),
  exact (hmnr _ ⟨lt_add_one m, hnm⟩).elim,
end

instance : polytope.graded ℕ :=
⟨id, rfl, strict_mono_id, nat.succ_of_cover⟩

/-- Two `fin`s cover each other iff their values do. -/
lemma fin.cover_iff_cover {n : ℕ} (a b : fin n) : a ⋖ b ↔ a.val ⋖ b.val :=
  ⟨ λ ⟨hl, hr⟩, ⟨hl, λ c hc, (hr ⟨c, lt_trans hc.right b.property⟩) hc⟩,
  λ ⟨hl, hr⟩, ⟨hl, λ c hc, hr c hc⟩ ⟩

instance (n : ℕ) : polytope.graded (fin (n + 1)) :=
{ grade := λ n, n,
  grade_bot := refl _,
  strict_mono := strict_mono_id,
  hcovers := begin
    intros x y,
    rw fin.cover_iff_cover,
    exact nat.succ_of_cover _ _,
  end }

open polytope

namespace polytope.flag

instance (α : Type u) [has_lt α] : has_mem α (flag α) :=
⟨λ a Φ, a ∈ Φ.val⟩

variables {α : Type u}

instance [has_le α] [has_lt α] (Φ : flag α) : has_le Φ :=
⟨λ a b, a.val ≤ b.val⟩

instance [has_lt α] (Φ : flag α) : has_lt Φ :=
⟨λ a b, a.val < b.val⟩

instance [has_lt α] : inhabited (flag α) :=
⟨⟨_, zorn.max_chain_spec⟩⟩

/-- Any two elements of a flag are comparable. -/
protected theorem le_total [preorder α] : ∀ (Φ : flag α) (x y : Φ), x ≤ y ∨ y ≤ x :=
begin
  rintros ⟨_, hΦ, _⟩ x y,
  by_cases heq : x = y,
    { exact or.inl (le_of_eq heq) },
    { cases x with x hx, cases y with y hy,
      rw subtype.mk_eq_mk at heq,
      cases hΦ x hx y hy heq with h h, { exact or.inl (le_of_lt h) },
      exact or.inr (le_of_lt h) }
end

/-- `<` is trichotomous for flags. -/
instance [preorder α] (Φ : flag α) : is_trichotomous Φ (<) :=
begin
  refine ⟨λ x y, _⟩,
  by_cases heq : x = y, { exact or.inr (or.inl heq) },
  cases x with x hx,
  cases y with y hy,
  cases (Φ.prop.left x hx y hy) (λ h, heq (subtype.ext h)) with hle hle,
    { exact or.inl hle },
    { exact or.inr (or.inr hle) },
end

@[priority 900] -- lower priority in case subtype.linear_order comes up with something computable
noncomputable instance [partial_order α] (Φ : flag α) : linear_order Φ :=
{ le_total := Φ.le_total,
  decidable_le := classical.dec_rel (≤),
  ..subtype.partial_order _ }

/-- An element belongs to a flag iff it's comparable with everything in it. -/
lemma mem_flag_iff_comp [preorder α] (Φ : flag α) {a : α} :
  a ∈ Φ ↔ ∀ b : Φ, a ≠ ↑b → a < ↑b ∨ ↑b < a :=
begin
  split,
    { exact λ ha ⟨b, hb⟩ hne, Φ.property.left a ha b hb hne },
  intro H,
  by_contra ha,
  exact Φ.prop.right
    ⟨_, zorn.chain_insert Φ.prop.left (λ b hb hne, H ⟨b, hb⟩ hne.symm), set.ssubset_insert ha⟩,
end

variables [partial_order α] (Φ : flag α)

/-- `⊥` belongs to every flag. -/
theorem bot_in_flag [order_bot α] : (⊥ : α) ∈ Φ :=
by rw mem_flag_iff_comp; exact λ b hb, or.inl (bot_lt_iff_ne_bot.mpr hb.symm)

instance [order_bot α] : order_bot Φ :=
subtype.order_bot Φ.bot_in_flag

/-- `⊤` belongs to every flag. -/
theorem top_in_flag [order_top α] : (⊤ : α) ∈ Φ :=
by rw mem_flag_iff_comp; exact λ b hb, or.inr (lt_top_iff_ne_top.mpr hb.symm)

instance [order_top α] : order_top Φ :=
subtype.order_top Φ.top_in_flag

instance [bounded_order α] : bounded_order Φ :=
{ ..Φ.order_top, ..Φ.order_bot }

end polytope.flag

namespace polytope.automorphism

/-- The automorphism group of a poset. -/
instance (α : Type u) [p : partial_order α] : group (automorphism α) :=
@Aut.group (partial_order α) (Poset α) p

variables {α : Type u} [partial_order α]

/-- Any automorphism is a relation isomorphism. -/
def to_rel_iso (γ : automorphism α) : ((≤) : α → α → Prop) ≃r (≤) :=
{ to_fun := γ.hom,
  inv_fun := γ.inv,
  left_inv := λ x, by change (γ.hom ≫ _) _ = _; rw γ.hom_inv_id; refl,
  right_inv := λ x, by change (γ.inv ≫ _) _ = _; rw γ.inv_hom_id; refl,
  map_rel_iff' := begin
    intros,
    change γ.hom a ≤ γ.hom b ↔ a ≤ b,
    refine ⟨λ h, _, λ h, γ.hom.map_rel h⟩,
    have : (γ.hom ≫ γ.inv) a ≤ (γ.hom ≫ γ.inv) b := γ.inv.map_rel h,
    rwa γ.hom_inv_id at this
  end }

/-- Inverse automorphism. -/
@[reducible]
def symm (γ : automorphism α) : automorphism α :=
γ.symm

@[simp]
theorem symm_invo : function.involutive (@symm α _) :=
λ ⟨_, _, _, _⟩, rfl

@[simp]
theorem symm_hom (γ : automorphism α) : γ.symm.hom = γ.inv :=
rfl

@[simp]
theorem symm_inv (γ : automorphism α) : γ.symm.inv = γ.hom :=
rfl

/-- Automorphisms preserve `≤`. -/
@[simp]
lemma hom_map_le (γ : automorphism α) (a b : α) : γ.hom a ≤ γ.hom b ↔ a ≤ b :=
γ.to_rel_iso.map_rel_iff

/-- Automorphisms preserve `=`. -/
@[simp]
lemma hom_map_eq (γ : automorphism α) (a b : α) : γ.hom a = γ.hom b ↔ a = b :=
γ.to_rel_iso.eq_iff_eq

/-- Automorphisms preserve `≠`. -/
lemma hom_map_ne (γ : automorphism α) (a b : α) : γ.hom a ≠ γ.hom b ↔ a ≠ b :=
by simp only [ne.def, hom_map_eq]

/-- Automorphisms and their inverses give the identity. -/
@[simp]
lemma hom_inv (γ : automorphism α) (a : α) : γ.hom (γ.inv a) = a :=
γ.to_rel_iso.right_inv a

/-- Inverse automorphisms preserve `≤`. -/
@[simp]
lemma inv_map_le (γ : automorphism α) (a b : α) : γ.inv a ≤ γ.inv b ↔ a ≤ b :=
γ.to_rel_iso.symm.map_rel_iff

/-- Inverse automorphisms preserve `=`. -/
@[simp]
lemma inv_map_eq (γ : automorphism α) (a b : α) : γ.inv a = γ.inv b ↔ a = b :=
γ.to_rel_iso.symm.eq_iff_eq

/-- Inverse automorphisms preserve `≠`. -/
lemma inv_map_ne (γ : automorphism α) (a b : α) : γ.inv a ≠ γ.inv b ↔ a ≠ b :=
by simp only [ne.def, inv_map_eq]

/-- Automorphisms and their inverses give the identity. -/
@[simp]
lemma inv_hom (γ : automorphism α) (a : α) : γ.inv (γ.hom a) = a :=
γ.to_rel_iso.left_inv a

/-- Automorphisms preserve `<`. -/
@[simp]
lemma hom_map_lt (γ : automorphism α) (a b : α) : γ.hom a < γ.hom b ↔ a < b :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  all_goals { rw lt_iff_le_and_ne at h ⊢, cases h with h h', refine ⟨_, _⟩ },
    { rwa γ.hom_map_le at h },
    { rwa γ.hom_map_ne at h' },
    { rwa ←γ.hom_map_le at h },
    { rwa ←γ.hom_map_ne at h' },
end

/-- Inverse automorphisms preserve `<`. -/
@[simp]
lemma inv_map_lt (γ : automorphism α) (a b : α) : γ.inv a < γ.inv b ↔ a < b :=
by rw ←γ.symm_hom; apply γ.symm.hom_map_lt

/-- Scalar multiplication of automorphisms by flags. -/
@[reducible]
def smul_def (γ : automorphism α) (Φ : flag α) : set α :=
γ.hom '' Φ.val

/-- Definition of scalar multiplication of automorphisms by flags. -/
@[simp]
theorem smul_def.eq (γ : automorphism α) (Φ : flag α) : γ.smul_def Φ = γ.hom '' Φ.val :=
rfl

/-- Automorphisms map flags to chains. -/
lemma smul_is_chain (γ : automorphism α) (Φ : flag α) : zorn.chain (<) (γ.smul_def Φ) :=
begin
  rcases Φ with ⟨Φf, hΦ, hΦ'⟩,
  rintros a ⟨aw, ha, ha'⟩ b ⟨bw, hb, hb'⟩,
  induction ha', induction hb',
  simp only [hom_map_lt, hom_map_ne],
  exact hΦ _ ha _ hb
end

/-- Automorphisms map flags to flags. -/
theorem smul_is_max_chain (γ : automorphism α) (Φ : flag α) :
  @zorn.is_max_chain _ (<) (γ.smul_def Φ) :=
begin
  refine ⟨γ.smul_is_chain Φ, _⟩,
  rcases Φ with ⟨Φf, hΦ, hΦ'⟩,
  rintros ⟨w, hwl, hwr⟩,
  rcases set.exists_of_ssubset hwr with ⟨a, ha, hna⟩,
  refine hΦ' ⟨set.insert (γ.inv a) Φf, _⟩,
  split,
    { rintros x (hx : _ ∨ _) y (hy : _ ∨ _) hne,
      have hxyne : x ≠ γ.inv a ∨ y ≠ γ.inv a,
        { rw ←not_and_distrib,
          rintro ⟨hl, hr⟩,
          exact hne (hl.trans hr.symm) },
      by_cases hxy : x ∈ Φf ∧ y ∈ Φf, { exact hΦ _ hxy.left _ hxy.right hne },
      wlog h : x = γ.inv a ∧ y ∈ Φf using [x y, y x],
        { cases hx,
            { exact or.inl ⟨hx, hy.resolve_left (hxyne.resolve_left $ not_not_intro hx)⟩ },
          cases hy,
            { exact or.inr ⟨hy, hx⟩ },
            { exact (hxy ⟨hx, hy⟩).elim } },
      cases h with hx' hy',
      replace hx' := hx'.symm,
      induction hx',
      rw [←γ.hom_map_lt y, ←γ.hom_map_lt, γ.hom_inv],
      replace hne : a ≠ γ.hom y := by rw ←γ.inv_map_ne; simpa,
      apply hwl _ ha _ _ hne,
      replace hy' := set.mem_image_of_mem γ.hom hy',
      exact hwr.left hy' },
    { apply set.ssubset_insert,
      intro h,
      replace h := set.mem_image_of_mem γ.hom h,
      rw γ.hom_inv at h,
      exact hna h },
end

instance : has_scalar (automorphism α) (flag α) :=
⟨λ γ Φ, ⟨γ.smul_def Φ, γ.smul_is_max_chain Φ⟩⟩

@[simp]
theorem smul_def.eq' (γ : automorphism α) (Φ : flag α) : (γ • Φ).val = γ.hom '' Φ.val :=
rfl

/-- The group action of the automorphism group of a poset on its flags. -/
instance : mul_action (automorphism α) (flag α) :=
{ one_smul := λ ⟨b, _⟩, subtype.eq (set.image_id b),
  mul_smul := begin
    rintros γ γ' ⟨b, _⟩,
    apply subtype.eq,
    change (γ'.hom ≫ γ.hom) '' b = γ.hom '' (γ'.hom '' b),
    rw ←set.image_comp,
    refl
  end }

end polytope.automorphism

/-- Covering is irreflexive. -/
instance covers.is_irrefl {α : Type u} [preorder α] : is_irrefl α covers :=
⟨ λ _ ha, ne_of_lt ha.left (refl _) ⟩

/-- A natural covers another iff it's a successor. -/
lemma nat.cover_iff_succ (m n : ℕ) : m ⋖ n ↔ n = m + 1 :=
begin
  split,
  { rintro ⟨hmnl, hmnr⟩,
    cases le_or_gt n (m + 1) with hnm hnm,
    exact antisymm hnm (nat.succ_le_of_lt hmnl),
    exact (hmnr _ ⟨lt_add_one m, hnm⟩).elim },
  intro hnm,
  split,
  { rw hnm,
    exact lt_add_one m },
  rintros r ⟨hrl, hrr⟩,
  rw hnm at hrr,
  exact nat.lt_irrefl _ (lt_of_le_of_lt (nat.succ_le_of_lt hrl) hrr),
end

namespace graded

instance (α : Type u) [preorder α] [ot : order_top α] [g : graded α] : bounded_order α :=
{ ..ot, ..g }

/-- An abbreviation for the grade of `⊤`. -/
abbreviation grade_top (α : Type u) [preorder α] [order_top α] [graded α] : ℕ :=
grade (⊤ : α)

lemma grade_le_grade_top {α : Type u} [partial_order α] [order_top α] [graded α] (a : α) :
  grade a ≤ grade_top α :=
graded.strict_mono.monotone le_top

lemma dual_cover_iff_cover {α : Type u} [preorder α] (a b : α) :
  a ⋖ b ↔ @polytope.covers (order_dual α) _ a b :=
by split; repeat { exact λ ⟨habl, habr⟩, ⟨habl, λ c ⟨hcl, hcr⟩, habr c ⟨hcr, hcl⟩⟩ }

instance (α : Type u) [partial_order α] [order_top α] [graded α] : graded (order_dual α) :=
{ grade := λ a : α, grade_top α - grade a,
  grade_bot := nat.sub_self _,
  strict_mono := begin
    refine λ (a b : α) hab, _,
    have : grade a > grade b := graded.strict_mono hab,
    have := grade_le_grade_top a,
    have := grade_le_grade_top b,
    linarith,
  end,
  hcovers := begin
    refine λ (x y : α) hxy, _,
    change grade x with graded.grade x,
    rw ←dual_cover_iff_cover at hxy,
    rw [graded.hcovers hxy, ←nat.sub_sub,
        nat.sub_add_cancel (tsub_pos_of_lt (graded.strict_mono (lt_of_lt_of_le hxy.left le_top)))]
  end }

/-- `grade` is injective for linearly ordered `α`. -/
theorem grade.inj (α : Type u) [linear_order α] [graded α] : function.injective (grade : α → ℕ) :=
graded.strict_mono.injective

variables {α : Type u}

/-- An element has grade 0 iff it is the bottom element. -/
@[simp]
theorem eq_zero_iff_eq_bot [partial_order α] [graded α] (x : α) : grade x = 0 ↔ x = ⊥ :=
begin
  refine ⟨λ h, _, λ h, by cases h; exact graded.grade_bot⟩,
  rw ←@graded.grade_bot α at h,
  by_contra hx,
  change _ ≠ _ at hx,
  rw ←bot_lt_iff_ne_bot at hx,
  exact not_le_of_lt (graded.strict_mono hx) (le_of_eq h)
end

/-- An element has the top grade iff it is the top element. -/
@[simp]
theorem eq_grade_top_iff_eq_top [partial_order α] [order_top α] [graded α] (x : α) :
  grade x = grade_top α ↔ x = ⊤ :=
begin
  refine ⟨λ h, _, λ h, by cases h; refl⟩,
  by_contra hx,
  change _ ≠ _ at hx,
  rw ←lt_top_iff_ne_top at hx,
  exact not_le_of_lt (graded.strict_mono hx) (ge_of_eq h)
end

section
variables [linear_order α] [graded α]

lemma grade_le_iff_le (x y : α) : grade x ≤ grade y ↔ x ≤ y :=
begin
  split,
    { contrapose,
      exact λ hxy, not_le_of_gt (graded.strict_mono (lt_of_not_ge hxy)), },
  exact λ hxy, graded.strict_mono.monotone hxy,
end

/-- `grade` is an order embedding into ℕ for linearly ordered `α`. -/
def oem_nat : α ↪o ℕ :=
{ to_fun := _,
  inj' := grade.inj α,
  map_rel_iff' := grade_le_iff_le }

lemma grade_lt_iff_lt (x y : α) : grade x < grade y ↔ x < y :=
order_embedding.lt_iff_lt oem_nat

lemma grade_eq_iff_eq (x y : α) : grade x = grade y ↔ x = y :=
order_embedding.eq_iff_eq oem_nat

lemma grade_ne_iff_ne (x y : α) : grade x ≠ grade y ↔ x ≠ y :=
not_congr (grade_eq_iff_eq x y)

/-- A grade function into `fin` for `α` with a top element. -/
def grade_fin [order_top α] (x : α) : fin (grade_top α + 1) :=
⟨grade x, by rw nat.lt_add_one_iff; exact grade_le_grade_top _⟩

@[simp]
theorem grade_fin.val_eq [order_top α] (x : α) : (grade_fin x).val = grade x :=
rfl

theorem grade_fin.strict_mono [order_top α] : strict_mono (grade_fin : α → fin (grade_top α + 1)) :=
graded.strict_mono

theorem grade_fin.inj [order_top α] : function.injective (grade_fin : α → fin (grade_top α + 1)) :=
grade_fin.strict_mono.injective

/-- `grade_fin` is an order embedding into `fin` for linearly ordered `α` with a top element. -/
def oem_fin [order_top α] : α ↪o fin (grade_top α + 1) :=
{ to_fun := grade_fin,
  inj' := grade_fin.inj,
  map_rel_iff' := grade_le_iff_le }

/-- In linear orders, `hcovers` is an equivalence. -/
lemma covers_iff_grade_eq_succ_grade (a b : α) : a ⋖ b ↔ grade b = grade a + 1 :=
begin
  refine ⟨graded.hcovers, λ hba, _⟩,
  have := nat.lt_of_succ_le (le_of_eq hba.symm),
  rw graded.grade_lt_iff_lt at this,
  refine ⟨this, λ z, _⟩,
  rintros ⟨hzl, hzr⟩,
  rw ←nat.cover_iff_succ at hba,
  rw ←graded.grade_lt_iff_lt at hzl,
  rw ←graded.grade_lt_iff_lt at hzr,
  exact hba.right _ ⟨hzl, hzr⟩,
end

/-- Two elements in a linear order cover each other iff their grades do. -/
theorem cover_iff_nat_cover (a b : α) : a ⋖ b ↔ grade a ⋖ grade b :=
begin
  split, { rw nat.cover_iff_succ, exact graded.hcovers },
  intro hab,
  rw nat.cover_iff_succ at hab,
  rwa graded.covers_iff_grade_eq_succ_grade
end

end
end graded

/-- A closed non-empty interval of a graded poset is a graded poset. -/
def set.Icc.graded {α : Type u} [partial_order α] [graded α] {x y : α} (h : x ≤ y) :
  graded (set.Icc x y) :=
{ grade := λ a, grade a.val - grade x,
  strict_mono := λ a b h,
    nat.sub_mono_left_strict (graded.strict_mono.monotone a.prop.left) (graded.strict_mono h),
  grade_bot := tsub_eq_zero_iff_le.mpr (refl _),
  hcovers := begin
    rintros ⟨a, ha⟩ ⟨b, hb⟩ ⟨hab, hcov⟩,
    suffices this : ∀ z, z ∉ set.Ioo a b,
    have : grade b = grade a + 1 := graded.hcovers ⟨hab, this⟩,
    change grade b - grade x = grade a - grade x + 1,
    rw [this, nat.sub_add_comm],
    exact graded.strict_mono.monotone ha.left,
    intros z h,
    simp at hcov,
    apply hcov z (ha.left.trans (le_of_lt h.left)) ((le_of_lt h.right).trans hb.right),
    exact h.left,
    exact h.right
  end,
  ..set.Icc.order_bot h }

/-- If an element covers another, they define an empty open interval. -/
theorem set.Ioo_is_empty_of_covers {α : Type u} [preorder α] {x y : α} : x ⋖ y → set.Ioo x y = ∅ :=
λ ⟨_, hr⟩, set.eq_empty_iff_forall_not_mem.mpr hr

namespace chain
section

variables {α : Type u} [has_lt α]

/-- The empty set is vacuously a chain. -/
lemma empty : @zorn.chain α (<) ∅ :=
λ _ h, h.elim

/-- Any singleton is a chain. -/
lemma singleton (x : α) : @zorn.chain α (<) (set.insert x ∅) :=
by refine zorn.chain_insert _ _ ; repeat { exact λ _ h, h.elim }

/-- Any pair of incident elements is a chain. -/
lemma pair {x y : α} (hxy : x < y ∨ y < x) :
  @zorn.chain α (<) (set.insert x (set.insert y ∅)) :=
begin
  apply zorn.chain_insert (singleton _),
  intros _ hb _,
  rwa ←(list.mem_singleton.mp hb) at hxy,
end

end
end chain

namespace flag
section

/-- A point subdivides an interval into three. -/
private lemma ioo_tricho {a b c : ℕ} (hc : c ∈ set.Ioo a b) (d: ℕ) :
  c = d ∨ c ∈ set.Ioo a d ∨ c ∈ set.Ioo d b :=
begin
  cases eq_or_ne c d with hcd hcd,
    { exact or.inl hcd },
  cases ne.lt_or_lt hcd with ha hb,
    { exact or.inr (or.inl ⟨and.left hc, ha⟩) },
    { exact or.inr (or.inr ⟨hb, and.right hc⟩) }
end

/-- A set of nats without gaps is an interval. The sizes of the gaps and intervals we consider are
    bounded by `n`, so that we may induct on it. -/
private lemma all_ioo_of_ex_ioo {P : ℕ → Prop} (n : ℕ)
  (hP : ∀ a b, b ≤ a + n → P a → P b → nonempty (set.Ioo a b) → ∃ c ∈ set.Ioo a b, P c) (a b : ℕ) :
  b ≤ a + n → P a → P b → ∀ c ∈ set.Ioo a b, P c :=
begin
  revert a b,
  induction n with n hP',
    { exact λ _ _ hba _ _ _ hci, ((not_lt_of_ge hba) (lt_trans hci.left hci.right)).elim },
  intros a b hba ha hb _ hci,
  rcases hP a b hba ha hb (nonempty.intro ⟨_, hci⟩) with ⟨d, ⟨hdil, hdir⟩, hd⟩,
  cases ioo_tricho hci d with hcd hdb, { rwa ←hcd at hd },
  have hxy : ∃ x y, P x ∧ P y ∧ c ∈ set.Ioo x y ∧ y ≤ x + n := begin
    cases hdb with hcad hcdb,
      { refine ⟨a, d, ha, hd, hcad, _⟩,
        have := lt_of_lt_of_le hdir hba,
        rw nat.add_succ at this,
        exact nat.le_of_lt_succ this },
      { refine ⟨d, b, hd, hb, hcdb, _⟩,
        have := nat.add_le_add hdil rfl.le,
        rw nat.succ_add a n at this,
        exact le_trans hba this }
  end,
  rcases hxy with ⟨x, y, hx, hy, hxy, hyx⟩,
  exact hP' (λ _ _ hba, hP _ _ (hba.trans (nat.le_succ _))) x y hyx hx hy c hxy,
end

/-- A set of nats without gaps is an interval. -/
lemma all_icc_of_ex_ioo {P : ℕ → Prop}
  (hP : ∀ a b, P a → P b → (nonempty (set.Ioo a b)) → ∃ c ∈ set.Ioo a b, P c) (a b : ℕ) :
  P a → P b → ∀ c ∈ set.Icc a b, P c :=
begin
  rintros ha hb c ⟨hac, hcb⟩,
  cases eq_or_lt_of_le hac with hac hac,
    { rwa ←hac },
  cases eq_or_lt_of_le hcb with hcb hcb,
    { rwa  hcb },
  exact all_ioo_of_ex_ioo b (λ c d _, hP c d) _ _ le_add_self ha hb _ ⟨hac, hcb⟩
end

variables {α : Type u} [partial_order α]

/-- Every chain is contained in a flag. -/
theorem flag_of_chain (c : set α) (hc : zorn.chain (<) c) : ∃ Φ : flag α, c ⊆ Φ :=
begin
  let all_chains := {s : set α | c ⊆ s ∧ zorn.chain (<) s},
  have := zorn.zorn_subset_nonempty all_chains _ c ⟨rfl.subset, hc⟩, {
    rcases this with ⟨Φ, hΦ₀, hΦ₁, hΦ₂⟩,
    refine ⟨⟨Φ, hΦ₀.right, λ h, _⟩, hΦ₁⟩,
    rcases h with ⟨d, hd, hdΦ₀, hdΦ₁⟩,
    have := hΦ₂ d _ hdΦ₀,
    induction this,
      { exact hdΦ₁ hdΦ₀ },
    change c ⊆ Φ with c ≤ Φ at hΦ₁,
    exact ⟨le_trans hΦ₁ hdΦ₀, hd⟩,
  },
  rintros cs hcs₀ hcs₁ ⟨s, hs⟩,
  refine ⟨⋃₀ cs, ⟨λ _ ha, set.mem_sUnion_of_mem ((hcs₀ hs).left ha) hs, _⟩,
    λ _, set.subset_sUnion_of_mem⟩,
  rintros y ⟨sy, hsy, hysy⟩ z ⟨sz, hsz, hzsz⟩ hyz,
  by_cases hsseq : sy = sz,
    { induction hsseq,
      apply (hcs₀ hsy).right,
      all_goals { assumption } },
  cases hcs₁ _ hsy _ hsz hsseq with h h,
    { exact (hcs₀ hsz).right _ (h hysy) _ hzsz hyz },
    { exact (hcs₀ hsy).right _ hysy _ (h hzsz) hyz },
end

/-- Every element belongs to some flag. -/
theorem ex_flag_mem (x : α) : ∃ Φ : flag α, x ∈ Φ :=
by cases flag_of_chain _ (chain.singleton x) with Φ hΦ; exact ⟨Φ, hΦ (set.mem_insert x ∅)⟩

/-- Every pair of incident elements belongs to some flag. -/
theorem ex_flag_both_mem (x y : α) (hxy : x < y ∨ y < x) : ∃ Φ : flag α, x ∈ Φ ∧ y ∈ Φ :=
begin
  cases flag_of_chain _ (chain.pair hxy) with Φ hΦ,
  exact ⟨Φ, hΦ (set.mem_insert _ _), hΦ (set.mem_insert_of_mem _ (set.mem_insert _ _))⟩
end

/-- An element covers another iff they do so in the flag. -/
@[simp]
theorem cover_iff_flag_cover {Φ : flag α} (x y : Φ) : x ⋖ y ↔ x.val ⋖ y.val :=
begin
  refine ⟨λ h, ⟨h.left, λ z hzi, _⟩, λ ⟨hxy, hz⟩, ⟨hxy, λ _, hz _⟩⟩,
  cases h with hxy h,
  refine h ⟨z, _⟩ hzi,
  cases hzi with hxz hzy,
  refine Φ.mem_flag_iff_comp.mpr (λ w hzw, _),
  have hwi := h w,
  simp only [set.mem_Ioo, not_and, not_lt] at hwi,
  rcases lt_trichotomy x w with hxw | hxw | hxw,
    { exact or.inl (lt_of_lt_of_le hzy (hwi hxw)) },
    { induction hxw, exact or.inr hxz },
    { exact or.inr (lt_trans hxw hxz) }
end

variable [graded α]

instance (Φ : flag α) : graded Φ :=
{ grade := λ a, grade a.val,
  grade_bot := graded.grade_bot,
  strict_mono := λ _ _ h, graded.strict_mono h,
  hcovers := λ _ _ hcov, graded.hcovers $ (cover_iff_flag_cover _ _).mp hcov }

/-- A number is a grade of some element in a flag. -/
private abbreviation is_grade (Φ : flag α) (n : ℕ) : Prop :=
∃ a : Φ, grade a = n

/-- If `x < y` but `y` does not cover `x`, then there's an element in between. -/
private lemma between_of_ncover {x y : α} (hnxy : ¬x ⋖ y) (hxy : x < y) :
  ∃ z, x < z ∧ z < y :=
by by_contra hne; push_neg at hne; exact hnxy ⟨hxy, λ z ⟨hl, hr⟩, hne z hl hr⟩

/-- The set of grades in a flag has no gaps. -/
lemma grade_ioo (Φ : flag α) (m n : ℕ) :
  is_grade Φ m → is_grade Φ n → nonempty (set.Ioo m n) → ∃ r ∈ set.Ioo m n, is_grade Φ r :=
begin
  rintros ⟨a, ham⟩ ⟨b, hbn⟩ ⟨r, hr⟩,

  have hnab : ¬a ⋖ b := begin
    have : ¬m ⋖ n := λ hmn, (hmn.right r) hr,
    rwa [←ham, ←hbn, ←graded.cover_iff_nat_cover] at this,
  end,

  have hab : a < b := begin
    rw [←graded.grade_lt_iff_lt, ham, hbn],
    exact lt_trans hr.left hr.right,
  end,

  rcases between_of_ncover hnab hab with ⟨c, hac, hcb⟩,
  refine ⟨grade c, ⟨_, ⟨c, rfl⟩⟩⟩,
  split,
    { rw ←ham,
      exact graded.strict_mono hac },
  rw ←hbn,
  exact graded.strict_mono hcb
end

/-- If a flag contains two elements, it contains elements with all grades in between. -/
private lemma flag_grade_aux {Φ : flag α} (a b : Φ) (j ∈ set.Icc (grade a) (grade b)) :
  ∃ c : Φ, grade c = j :=
(all_icc_of_ex_ioo (grade_ioo Φ)) (grade a) (grade b) ⟨a, rfl⟩ ⟨b, rfl⟩ j H

variables [order_top α] (j : fin (graded.grade_top α + 1)) (Φ : flag α)

/-- A flag has an element of grade `j` when `j ≤ grade ⊤`. -/
theorem ex_of_grade_in_flag : ∃ a : Φ, grade a = j :=
begin
  refine (flag_grade_aux ⊥ ⊤ j) ⟨_, nat.le_of_lt_succ j.property⟩,
  have : grade (⊥ : Φ) = 0 := graded.grade_bot,
  rw this,
  exact zero_le j
end

/-- A flag has a unique element of grade `j` when `j ≤ grade ⊤`. -/
theorem ex_unique_of_grade_in_flag : ∃! a : Φ, grade a = j :=
begin
  cases ex_of_grade_in_flag j Φ with a ha,
  use [a, ha],
  intros b hb,
  apply graded.grade.inj _,
  rw [ha, hb]
end

/-- The element of a certain grade in a flag. -/
noncomputable def idx : Φ :=
classical.some (ex_of_grade_in_flag j Φ)

/-- The defining property of `flag.idx`. -/
@[simp]
theorem grade_idx : grade (idx j Φ) = j :=
classical.some_spec (ex_of_grade_in_flag j Φ)

/-- The defining property of `flag.idx`. -/
@[simp]
theorem grade_fin_idx : graded.grade_fin (idx j Φ) = j :=
subtype.ext $ grade_idx j Φ

/-- `flag_idx j Φ` is the unique element of grade `j` in the flag. -/
theorem grade_eq_iff_flag_idx (a : Φ) : grade a = j ↔ a = idx j Φ :=
begin
  have idx := grade_idx j Φ,
  split,
  { intro ha,
    rcases ex_unique_of_grade_in_flag j Φ with ⟨_, _, h⟩,
    rw [(h _ ha), (h _ idx)] },
  intro h,
  rw h,
  exact idx
end

/-- `grade_fin` is an order isomorphism for linearly ordered `α` with a top element. -/
noncomputable def order_iso_fin {α : Type u} [partial_order α] [order_top α] [graded α]
  (Φ : flag α) : Φ ≃o fin (graded.grade_top α + 1) :=
rel_iso.of_surjective graded.oem_fin $ λ x, ⟨idx x Φ, by simp [graded.oem_fin]⟩

noncomputable instance {α : Type u} [partial_order α] [order_top α] [graded α] (Φ : flag α) :
  fintype Φ :=
fintype.of_bijective (order_iso_fin Φ).inv_fun (order_iso_fin Φ).symm.bijective

@[simp]
theorem fincard_eq_gt {α : Type u} [partial_order α] [order_top α] [graded α] (Φ : flag α) :
  fintype.card Φ = graded.grade_top Φ + 1 :=
begin
  cases hfc : fintype.card Φ, { rw fintype.card_eq_zero_iff at hfc, exact hfc.elim' ⊤ },
  rw fintype.card_of_bijective (flag.order_iso_fin Φ).bijective at hfc,
  rw [←hfc, fintype.card_fin],
  refl
end

variables (Ψ : flag α)

/-- Two flags are j-adjacent iff they share all but their j-th element. Note that a flag is never
    adjacent to itself. -/
def j_adjacent : Prop :=
∀ i, (idx i Φ).val = (idx i Ψ).val ↔ i ≠ j

/-- Two flags are adjacent when they're j-adjacent for some j. Note that a flag is never adjacent to
    itself. -/
-- Todo(Vi): It should be possible to restate this in a way that doesn't depend on `[graded α]`.
def adjacent : Prop :=
∃ j, j_adjacent j Φ Ψ

instance : is_irrefl (flag α) (j_adjacent j) :=
⟨λ _ h, (h j).mp rfl rfl⟩

instance : is_irrefl (flag α) adjacent :=
⟨λ _ ⟨j, h⟩, (@irrefl _ (j_adjacent j) _ _) h⟩

/-- j-adjacency is symmetric. -/
theorem j_adjacent.symm : j_adjacent j Φ Ψ → j_adjacent j Ψ Φ :=
by intros h i; rw ←(h i); exact eq_comm

/-- Adjacency is symmetric. -/
theorem adjacent.symm : adjacent Φ Ψ → adjacent Ψ Φ :=
λ ⟨j, h⟩, ⟨j, (j_adjacent.symm j _ _) h⟩

end
end flag

/-- Two elements of a type are connected by a relation when there exists a path of connected
    elements. This is essentially an inductive version of an equivalence closure. -/
 -- Todo(Vi): If someone else comes up with connected graphs sometime, we might want to rework this.
inductive polytope.path {α : Type u} (r : α → α → Prop) : α → α → Prop
| start (x : α) : polytope.path x x
| next (x y z : α) : polytope.path x y → r y z → polytope.path x z

namespace path
section

variables {α : Type u} {r : α → α → Prop} {a b c : α}

/-- Connectivity is reflexive. -/
@[refl]
theorem refl : path r a a :=
path.start a

/-- Comparable proper elements are connected. -/
theorem from_rel : r a b → path r a b :=
(path.next a a b) (path.refl)

/-- If `a` and `b` are related, and `b` and `c` are connected, then `a` and `c` are connected. -/
lemma append_left (hab : r a b) (hbc : path r b c) : path r a c :=
begin
  induction hbc with _ _ _ _ _ hcd h,
    { exact path.from_rel hab },
    { exact path.next _ _ _ (h hab) hcd }
end

/-- Connectedness with a symmetric relation is symmetric. -/
@[symm]
theorem symm [is_symm α r] (hab : path r a b) : path r b a :=
begin
  induction hab with _ _ _ _ _ hbc hba,
    { exact path.refl },
    { exact path.append_left (is_symm.symm _ _ hbc) hba, }
end

/-- Connectedness is transitive. -/
theorem trans (hab : path r a b) (hbc : path r b c) : path r a c :=
begin
  induction hab with a a d b had hdb h,
    { exact hbc },
    { exact h (path.append_left hdb hbc) }
end

/-- If `a` and `b` are connected, and `b` and `c` are related, then `a` and `c` are connected. -/
lemma append_right (hab : path r a b) (hbc : r b c) : path r a c :=
trans hab (from_rel hbc)

end
end path

/-- Proper elements are those that are neither `⊥` nor `⊤`. -/
def is_proper {α : Type u} [preorder α] [bounded_order α] (a : α) : Prop :=
a ≠ ⊥ ∧ a ≠ ⊤

/-- An element is proper iff it has a grade between the bottom and top element. -/
lemma proper_iff_grade_iio {α : Type u} [partial_order α] [order_top α] [graded α] (a : α) :
  is_proper a ↔ grade a ∈ set.Ioo 0 (graded.grade_top α) :=
begin
  split, {
    rintro ⟨hal, har⟩,
    cases eq_or_lt_of_le (zero_le (grade a)) with h hl,
      { replace h := eq.symm h,
        rw graded.eq_zero_iff_eq_bot at h,
        exact (hal h).elim },
    cases eq_or_lt_of_le (graded.grade_le_grade_top a) with h hr,
      { rw graded.eq_grade_top_iff_eq_top at h,
        exact (har h).elim },
    exact ⟨hl, hr⟩,
  },
  rintro ⟨hl, hr⟩,
  split,
    { intro ha,
      rw ←graded.eq_zero_iff_eq_bot at ha,
      exact (ne_of_lt hl) (eq.symm ha) },
  intro ha,
  rw ←graded.eq_grade_top_iff_eq_top at ha,
  exact (ne_of_lt hr) ha
end

/-- The subtype of proper elements. -/
@[reducible]
def polytope.proper (α : Type u) [preorder α] [bounded_order α] : Type u :=
{a : α // is_proper a}

/-- Elements are incident when they're comparable. -/
abbreviation polytope.incident {α : Type u} [preorder α] [bounded_order α]
  (a b : polytope.proper α) : Prop :=
a.val ≠ b.val → a.val < b.val ∨ b.val < a.val

/-- Proper elements are connected when they're related by a sequence of pairwise incident proper
    elements. -/
abbreviation polytope.connected {α : Type u} [preorder α] [bounded_order α]
  (a b : polytope.proper α) : Prop :=
path polytope.incident a b

/-- Flags are connected when they're related by a sequence of pairwise adjacent flags. -/
abbreviation polytope.flag_connected {α : Type u} [partial_order α] [order_top α] [graded α]
  (Φ Ψ : flag α) : Prop :=
path (@flag.adjacent α _ _ _) Φ Ψ

/-- A `graded` with top grade 1 or less has no proper elements. -/
theorem proper.empty {α : Type u} [partial_order α] [order_top α] [graded α] :
  graded.grade_top α ≤ 1 → is_empty (polytope.proper α) :=
begin
  intro h,
  split,
  rintro ⟨a, ha⟩,
  rw proper_iff_grade_iio at ha,
  refine (not_le_of_lt (lt_of_le_of_lt _ ha.right)) h,
  exact ha.left
end

/-- A `graded` with top grade 2 or more has some proper element. -/
lemma proper.nonempty (α : Type u) [partial_order α] [order_top α] [graded α]
  (h : 2 ≤ graded.grade_top α) :
  nonempty (polytope.proper α) :=
begin
  let a := (flag.idx ⟨1, nat.lt.step h⟩ (default (flag α))).val,
  have : grade a = 1 := flag.grade_idx _ _,
  use a,
  rw [proper_iff_grade_iio, this],
  exact ⟨nat.one_pos, nat.lt_of_succ_le h⟩
end

open polytope

namespace graded

/-- A `graded` is connected when it's of grade 2, or any two proper elements are connected. -/
protected def connected (α : Type u) [preorder α] [order_top α] [graded α] : Prop :=
grade_top α = 2 ∨ ∀ a b : proper α, connected a b

/-- Any `graded` of top grade less or equal to 2 is connected. -/
theorem connected_of_grade_le_two (α : Type u) [partial_order α] [order_top α] [graded α] :
  grade_top α ≤ 2 → graded.connected α :=
begin
  intro h,
  cases eq_or_lt_of_le h with ha ha, { exact or.inl ha },
  have := (proper.empty (nat.le_of_lt_succ ha)).false,
  exact or.inr (λ a, (this a).elim)
end

/-- A `graded` is flag-connected when any two flags are connected. -/
protected def flag_connected (α : Type u) [partial_order α] [order_top α] [graded α] : Prop :=
∀ Φ Ψ : flag α, flag_connected Φ Ψ

/-- Two adjacent flags have a proper element in common, as long as their grade exceeds 2, and a few
    other simple conditions hold. -/
private lemma proper_flag_intersect_of_grade {α : Type u} [partial_order α] [order_top α] [graded α]
{Φ Ψ : flag α} (hg : 2 < grade_top α) {j : fin (grade_top α + 1)} (hΦΨ : flag.j_adjacent j Φ Ψ)
(k ∈ set.Ioo 0 (grade_top α)) (hjk : j.val ≠ k) :
  ∃ c : proper α, c.val ∈ Φ.val ∩ Ψ.val :=
begin
  let k : fin (grade_top α + 1) := ⟨k, nat.lt.step H.right⟩,
  let idx := flag.idx k Φ,
  use idx.val,
    { rw proper_iff_grade_iio,
      change grade idx.val with grade idx,
      rw flag.grade_idx,
      exact H },
  use idx.prop,
  have hidx : idx.val = (flag.idx k Ψ).val := begin
    rw hΦΨ,
    intro h,
    rw ←h at hjk,
    exact hjk (refl _),
  end,
  rw hidx,
  exact subtype.mem (flag.idx k Ψ),
end

/-- If two flags are connected, then any two elements in these flags are connected, as long as the
    grade exceeds 2. -/
lemma connected_of_mem_flag_connected {α : Type u} [partial_order α] [order_top α] [graded α]
{Φ Ψ : flag α} (hg : 2 < grade_top α) (h : flag_connected Φ Ψ) {a b : proper α} :
  a.val ∈ Φ → b.val ∈ Ψ → connected a b :=
begin
  intros ha hb,
  induction h with Φ' Φ Ψ Ϝ hΦΨ hΨϜ hab generalizing a b,
    { apply (path.next a a) _ path.refl,
      exact (Φ'.prop.left a.val ha b.val hb), },
  suffices hc : ∃ c : proper α, c.val ∈ Ψ.val ∩ Ϝ.val,
    { rcases hc with ⟨c, ⟨hcl, hcr⟩⟩,
      exact path.append_right (hab ha hcl) (Ϝ.prop.left c.val hcr b hb) },
  cases hΨϜ with j hj,
  by_cases hj' : j = ⟨1, lt_trans (nat.succ_lt_succ zero_lt_two) (nat.succ_lt_succ hg)⟩,
    { apply proper_flag_intersect_of_grade hg hj 2, { exact ⟨zero_lt_two, hg⟩ },
      rw hj',
      exact nat.one_ne_bit0 1 },
  exact proper_flag_intersect_of_grade hg hj 1
    (⟨zero_lt_one, lt_trans one_lt_two hg⟩)
    (λ h, hj' (subtype.ext_val h))
end

/-- Flag connectedness implies connectedness. Note that the converse is false: a counterexample
    is given by the hexagrammic antiprism. -/
theorem connected_of_flag_connected (α : Type u) [partial_order α] [order_top α] [graded α] :
  graded.flag_connected α → graded.connected α :=
begin
  intro h,
  by_cases hg : grade_top α ≤ 2,
    { exact connected_of_grade_le_two α hg },
  right,
  intros a b,
  cases flag.ex_flag_mem a.val with Φ hΦ,
  cases flag.ex_flag_mem b.val with Ψ hΨ,
  exact connected_of_mem_flag_connected (lt_of_not_ge hg) (h Φ Ψ) hΦ hΨ,
end

/-- A section of a pre-polytope is connected. -/
@[reducible]
def section_connected {α : Type u} [partial_order α] [graded α] {x y : α} (hxy : x ≤ y) : Prop :=
@graded.connected _ _ (set.Icc.order_top hxy) (set.Icc.graded hxy)

end graded
