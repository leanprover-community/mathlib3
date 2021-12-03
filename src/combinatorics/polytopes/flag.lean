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
import combinatorics.polytopes.graded

/-!
# Flags of polytopes

In this file we define flags, maximal chains of a preorder. We prove that isomorphisms preserve
flags, and as such, automorphisms of posets induce a group action on flags. We also define
flag-adjacency and (strong) flag-connectedness.

Flags turn out to be crucial in proving a critical theorem: every graded partial order has elements
of each possible grade. As such, various important theorems that don't directly reference flags are
also proven in this file.

## Main definitions

* `polytope.flag`: a flag of a graded preorder.
* `graded.idx`: returns some element of a given grade.

## Main results

* `graded.ex_of_grade`: there's an element of any possible grade in a graded poset.
* `graded.scon_iff_sfcon`: strong connectedness and strong flag-connectedness are equivalent.

There's a few more of both I'm missing.
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
    { exact λ ha ⟨b, hb⟩ hne, Φ.prop.left a ha b hb hne },
  intro H,
  by_contra ha,
  exact Φ.prop.right
    ⟨_, zorn.chain_insert Φ.prop.left (λ b hb hne, H ⟨b, hb⟩ hne.symm), set.ssubset_insert ha⟩,
end

variables [partial_order α] (Φ : flag α)

/-- `⊥` belongs to every flag. -/
theorem bot_in_flag [order_bot α] : (⊥ : α) ∈ Φ :=
by rw mem_flag_iff_comp; exact λ _ h, or.inl (bot_lt_iff_ne_bot.mpr h.symm)

instance [order_bot α] : order_bot Φ :=
subtype.order_bot Φ.bot_in_flag

/-- `⊤` belongs to every flag. -/
theorem top_in_flag [order_top α] : (⊤ : α) ∈ Φ :=
by rw mem_flag_iff_comp; exact λ _ h, or.inr (lt_top_iff_ne_top.mpr h.symm)

instance [order_top α] : order_top Φ :=
subtype.order_top Φ.top_in_flag

instance [bounded_order α] : bounded_order Φ :=
{ ..Φ.order_top, ..Φ.order_bot }

end polytope.flag

namespace polytope.automorphism

/-- The automorphism group of a poset. -/
instance (α : Type u) [p : partial_order α] : group (automorphism α) :=
@Aut.group (partial_order α) (Poset α) p

instance (α : Type u) [p : partial_order α] : inhabited (automorphism α) :=
⟨iso.refl _⟩

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
  use γ.smul_is_chain Φ,
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

section preorder

variables {α : Type u} [preorder α]

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
theorem ex_flag_both_mem (x y : α) (hxy : x < y ∨ y < x) :
  ∃ Φ : flag α, x ∈ Φ ∧ y ∈ Φ :=
begin
  cases flag_of_chain _ (chain.pair hxy) with Φ hΦ,
  exact ⟨Φ, hΦ (set.mem_insert _ _), hΦ (set.mem_insert_of_mem _ (set.mem_insert _ _))⟩
end

end preorder

section partial_order

variables {α : Type u} [partial_order α]

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

instance [graded α] (Φ : flag α) : graded Φ :=
{ grade := λ a, grade a.val,
  grade_bot := graded.grade_bot,
  strict_mono := λ _ _ h, graded.strict_mono h,
  hcovers := λ _ _ hcov, graded.hcovers $ (cover_iff_flag_cover _ _).mp hcov }

end partial_order
end flag

namespace graded

section partial_order

variables {α : Type u} [partial_order α] [order_top α] [graded α]
(j : fin (graded.grade_top α + 1))

/-- A graded partial order has an element of grade `j` when `j ≤ grade ⊤`. -/
theorem ex_of_grade : is_grade α j :=
begin
  let Φ : flag α := default _,
  cases @graded.ex_of_grade_lin Φ _ _ _ j with a ha,
  exact ⟨a.val, ha⟩,
end

/-- The element of a certain grade in a graded partial order. -/
noncomputable def idx : α :=
classical.some (ex_of_grade j)

/-- Like `idx`, but allows specifying the type explicitly. -/
noncomputable abbreviation idx' (α : Type u) [partial_order α] [graded α] [order_top α]
(j : fin (graded.grade_top α + 1)) : α :=
idx j

/-- The defining property of `idx`. -/
@[simp]
theorem grade_idx : grade (idx j) = j :=
classical.some_spec (ex_of_grade j)

/-- The defining property of `idx`. -/
@[simp]
theorem grade_fin_idx : graded.grade_fin (idx j) = j :=
subtype.ext $ grade_idx j

end partial_order

section order_iso

variables {α β : Type u} [partial_order α] [order_top α] [graded α] [partial_order β] [order_top β]
[graded β]

-- Todo(Vi): Generalize! This doesn't actually require `order_top`.
private lemma grade_le_of_order_iso {oiso : α ≃o β} {n : ℕ} :
  ∀ x, grade x = n → grade x ≤ grade (oiso x) :=
begin
  apply nat.strong_induction_on n,
  intros n H x,
  induction n with n,
  { intro hg,
    rw hg,
    exact zero_le _ },
  intro hgx,
  suffices : ∃ y, grade y = n ∧ y < x,
    { rcases this with ⟨y, hgy, h⟩,
      rw [hgx, ←hgy],
      exact nat.succ_le_of_lt
        (lt_of_le_of_lt (H n (lt_add_one n) y hgy) (graded.strict_mono (oiso.lt_iff_lt.mpr h))) },
  cases flag.ex_flag_mem x with Φ hx,
  let x' : Φ := ⟨x, hx⟩,
  have hn : n < grade_top Φ + 1 := begin
    refine nat.lt_succ_of_le (le_trans (nat.le_succ n) _),
    rw ←hgx,
    exact grade_le_grade_top x,
  end,
  let n' : fin _ := ⟨n, hn⟩,
  let y := graded.idx' Φ n',
  use y,
  have hgy : grade y = n := graded.grade_idx n',
  use hgy,
  change ↑y < x with y < x',
  rw ←grade_lt_iff_lt,
  have : grade x' = grade x := rfl,
  rw [this, hgx, hgy],
  exact lt_add_one n,
end

/-- Order isomorphisms preserve grades. In other words, grade functions are unique when they
exist. -/
-- Todo(Vi): Generalize! This doesn't actually require `order_top`.
theorem grade_eq_of_order_iso (oiso : α ≃o β) (x : α) : grade x = grade (oiso x) :=
begin
  rw eq_iff_le_not_lt,
  split, { exact (grade_le_of_order_iso _ (refl _)) },
  have : grade x = grade (oiso.symm (oiso x)) := by rw (order_iso.symm_apply_apply _ _),
  rw this,
  exact not_lt_of_ge (grade_le_of_order_iso _ (refl _))
end

/-- Order isomorphisms preserve top grades. -/
lemma grade_top_eq_of_order_iso (oiso : α ≃o β) : grade_top α = grade_top β :=
begin
  change grade_top α with grade (⊤ : α),
  change grade_top β with grade (⊤ : β),
  rw ←oiso.map_top,
  exact grade_eq_of_order_iso oiso ⊤
end

/-- Order isomorphisms preserve total connectedness. -/
private lemma tcon_order_iso_of_tcon (oiso : α ≃o β) : total_connected β → total_connected α :=
begin
  intros hb,
  cases hb with hb hb,
    { left,
      rwa grade_top_eq_of_order_iso oiso },
  exact or.inr (λ x y, (con_order_iso_iff_con oiso x y).mpr (hb _ _)),
end

/-- Order isomorphisms preserve total connectedness. -/
theorem tcon_order_iso_iff_tcon (oiso : α ≃o β) : total_connected α ↔ total_connected β :=
⟨tcon_order_iso_of_tcon oiso.symm, tcon_order_iso_of_tcon oiso⟩

/-- Order isomorphisms preserve strong connectedness. -/
private lemma scon_order_iso_of_scon (oiso : α ≃o β) :
  graded.strong_connected β → graded.strong_connected α :=
begin
  intros hb x y hxy,
  have hxy' := order_iso.monotone oiso hxy,
  exact (@tcon_order_iso_iff_tcon _ _ _ (set.Icc.order_top hxy) (set.Icc.graded hxy) _
    (set.Icc.order_top hxy') (set.Icc.graded hxy') (oiso.Icc _ _)).mpr (hb hxy')
end

/-- Order isomorphisms preserve strong connectedness. -/
theorem scon_order_iso_iff_scon (oiso : α ≃o β) :
  graded.strong_connected α ↔ graded.strong_connected β :=
⟨scon_order_iso_of_scon oiso.symm, scon_order_iso_of_scon oiso⟩

/-- Strong connectedness implies total connectedness. -/
theorem tcon_of_scon (α : Type u) [partial_order α] [order_top α] [graded α] :
  strong_connected α → total_connected α :=
λ h, (@tcon_order_iso_iff_tcon α (set.Icc ⊥ (⊤ : α)) _ _ _ _ (set.Icc.order_top bot_le)
  (set.Icc.graded bot_le) (set.Icc.self_order_iso_bot_top α)).mpr (h bot_le)

end order_iso

section linear_order

variables {α : Type u} [linear_order α] [order_top α] [graded α] (j : fin (graded.grade_top α + 1))

/-- `idx j` is the unique element of grade `j` in the linear order. -/
theorem grade_eq_iff_idx (a : α) : grade a = j ↔ a = graded.idx j :=
begin
  have idx := graded.grade_idx j,
  split,
    { intro ha,
      rcases graded.ex_unique_of_grade j with ⟨_, _, h⟩,
      rw [(h _ ha), (h _ idx)] },
  intro h,
  rwa h,
end

/-- `grade_fin` is an order isomorphism for linearly ordered `α` with a top element. -/
noncomputable def order_iso_fin : α ≃o fin (graded.grade_top α + 1) :=
rel_iso.of_surjective graded.oem_fin $ λ x, ⟨graded.idx x, by simp [graded.oem_fin]⟩

@[priority 900]
noncomputable instance : fintype α :=
fintype.of_bijective (order_iso_fin).inv_fun order_iso_fin.symm.bijective

@[simp]
theorem fincard_eq_gt : fintype.card α = graded.grade_top α + 1 :=
begin
  cases hfc : fintype.card α, { rw fintype.card_eq_zero_iff at hfc, exact hfc.elim' ⊤ },
  rw fintype.card_of_bijective order_iso_fin.bijective at hfc,
  --rw [←hfc, fintype.card_fin],
  --refl
  repeat { sorry }
end

end linear_order
end graded

namespace flag

section

variable {α : Type u}

/-- Two flags are adjacent when there's exactly one element in one but not in the other. This isn't
quite the usual definition, and we've made it more general than necessary for reasons of
convenience, but we prove it to be equivalent to the usual one in the case of graded posets (see
`adjacent_iff_ex_j_adjacent`). -/
def adjacent [has_lt α] (Φ Ψ : flag α) : Prop :=
∃! a, a ∈ Φ.val \ Ψ.val

instance [has_lt α] : is_irrefl (flag α) adjacent :=
⟨λ _ ⟨_, ⟨hl, hr⟩, _⟩, hr hl⟩

variables [partial_order α] [order_top α] [graded α]

/-- If the indices of two flags are equal, all elements of one are in the other. -/
private lemma eq_of_eq_idx {Φ Ψ : flag α} :
  (∀ j, (graded.idx' Φ j).val = (graded.idx' Ψ j).val) → ∀ a, a ∈ Φ → a ∈ Ψ :=
begin
  intros h a ha,
  let a' : Φ := ⟨a, ha⟩,
  let ga := graded.grade_fin a',
  change a with a'.val,
  have heq := h ga,
  have hga : (graded.idx' Φ ga) = a' := begin
    symmetry,
    apply (graded.grade_eq_iff_idx ga a').mp,
    refl,
  end,
  rw hga at heq,
  rw heq,
  exact (graded.idx' Ψ ga).prop,
end

/-- Two flags are equal iff their elements of all grades are equal. -/
lemma eq_iff_eq_idx (Φ Ψ : flag α) : Φ = Ψ ↔ ∀ j, (graded.idx' Φ j).val = (graded.idx' Ψ j).val :=
⟨λ h _, (by rw h), λ h, subtype.ext_val
  (set.ext (λ _, ⟨eq_of_eq_idx h _, eq_of_eq_idx (λ j, (h j).symm) _⟩))⟩

/-- Two flags are j-adjacent iff they share all but their j-th element. Note that a flag is never
adjacent to itself. -/
def j_adjacent (j : fin (graded.grade_top α + 1)) (Φ Ψ : flag α) : Prop :=
∀ i, (graded.idx' Φ i).val = (graded.idx' Ψ i).val ↔ i ≠ j

instance (j : fin (graded.grade_top α + 1)) : is_irrefl (flag α) (j_adjacent j) :=
⟨λ _ h, (h j).mp rfl rfl⟩

/-- j-adjacency is symmetric. -/
theorem j_adjacent.symm {j : fin (graded.grade_top α + 1)} {Φ Ψ : flag α} :
  j_adjacent j Φ Ψ → j_adjacent j Ψ Φ :=
by intros h i; rw ←(h i); exact eq_comm

/-- Two flags in a graded poset are adjacent iff they're j-adjacent for some j. -/
theorem adjacent_iff_ex_j_adjacent {Φ Ψ : flag α} : adjacent Φ Ψ ↔ ∃ j, j_adjacent j Φ Ψ :=
begin
  split, {
    intros hΦΨ,
    cases hΦΨ with a ha,
    have : a ∈ Φ.val := sorry,
    let a' : Φ := ⟨a, this⟩,
    let j := graded.grade_fin a',
    use graded.grade_fin a',
    intro j,
    split, {
      intros hj hja,
      symmetry' at hja,
      rw subtype.ext_iff_val at hja,
      have : grade a' = j := sorry,
      rw graded.grade_eq_iff_idx at this,
      --rw ←this at hj,
      sorry,
    },
    sorry,
  },
  intro h,
  sorry,
end

/-- Adjacency is symmetric in a graded poset. -/
theorem adjacent.symm {Φ Ψ : flag α} : adjacent Φ Ψ → adjacent Ψ Φ :=
by repeat { rw adjacent_iff_ex_j_adjacent }; exact λ ⟨j, hj⟩, ⟨j, hj.symm⟩

end
end flag

/-- Flags are connected when they're related by a sequence of pairwise adjacent flags. -/
abbreviation polytope.flag_connected {α : Type u} [preorder α] (Φ Ψ : flag α) : Prop :=
path flag.adjacent Φ Ψ

open polytope

namespace graded
section

/-- A `graded` is totally flag-connected when any two flags are connected.

Here we deviate from standard nomenclature: mathematicians would just call this flag-connectedness.
However, by doing this, it makes it unambiguous when we're talking about two flags being connected,
and when we're talking about a polytope being totally flag-connected. -/
def total_flag_connected (α : Type u) [preorder α] : Prop :=
∀ Φ Ψ : flag α, flag_connected Φ Ψ

/-- Any graded poset of top grade less or equal to 1 has a single flag. -/
lemma flag_eq_of_grade_le_two (α : Type u) [partial_order α] [order_top α] [graded α]
(Φ Ψ : flag α) :
  grade_top α ≤ 1 → Φ = Ψ :=
begin
  intro h,
  rw flag.eq_iff_eq_idx,
  intro j,
  cases j with j hj,
  have := nat.le_of_lt_succ hj,
  have := le_trans this h,
  cases eq_or_lt_of_le this, {
    -- It's the top element
    sorry
  },
  -- It's the bottom element
  sorry
end

/-- Any graded poset of top grade less or equal to 2 is totally flag-connected. -/
theorem tfcon_of_grade_le_two (α : Type u) [partial_order α] [order_top α] [graded α] :
  grade_top α ≤ 2 → total_flag_connected α :=
begin
  intro h,
  cases eq_or_lt_of_le h with h h, {
    sorry,
  },
  intros Φ Ψ,
  sorry
end

/-- Two adjacent flags have a proper element in common, as long as their grade exceeds 2, and a few
other simple conditions hold. -/
private lemma proper_flag_intersect_of_grade {α : Type u} [partial_order α] [order_top α] [graded α]
{Φ Ψ : flag α} (hg : 2 < grade_top α) {j : fin (grade_top α + 1)} (hΦΨ : flag.j_adjacent j Φ Ψ)
(k ∈ set.Ioo 0 (grade_top α)) (hjk : j.val ≠ k) :
  ∃ c : proper α, c.val ∈ Φ.val ∩ Ψ.val :=
begin
  let k : fin (grade_top α + 1) := ⟨k, nat.lt.step H.right⟩,
  let idx := idx' Φ k,
  refine ⟨⟨idx.val, _⟩, idx.prop, _⟩,
    { rw proper_iff_grade_iio,
      change grade idx.val with grade idx,
      rw grade_idx,
      exact H },
  suffices : idx.val = (idx' Ψ k).val,
    { rw this,
      exact subtype.mem (idx' Ψ k) },
  rw hΦΨ,
  intro h,
  rw ←h at hjk,
  exact hjk (refl _),
end

/-- If two flags are flag-connected, then any two elements in these flags are connected, as long as the
grade exceeds 2. -/
lemma con_of_mem_fcon {α : Type u} [partial_order α] [order_top α] [graded α]
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
  rw flag.adjacent_iff_ex_j_adjacent at hΨϜ,
  cases hΨϜ with j hj,
  by_cases hj' : j = ⟨1, lt_trans (nat.succ_lt_succ zero_lt_two) (nat.succ_lt_succ hg)⟩,
    { apply proper_flag_intersect_of_grade hg hj 2, { exact ⟨zero_lt_two, hg⟩ },
      rw hj',
      exact nat.one_ne_bit0 1 },
  exact proper_flag_intersect_of_grade hg hj 1
    (⟨zero_lt_one, lt_trans one_lt_two hg⟩)
    (λ h, hj' (subtype.ext_val h))
end

/-- Total flag-connectedness implies total connectedness. Note that the converse is false: a
counterexample is given by the hexagrammic antiprism (this proof hasn't been written down yet). -/
theorem tcon_of_tfcon (α : Type u) [partial_order α] [order_top α] [graded α] :
  total_flag_connected α → total_connected α :=
begin
  intro h,
  by_cases hg : grade_top α ≤ 2,
    { exact tcon_of_grade_le_two α hg },
  right,
  intros a b,
  cases flag.ex_flag_mem a.val with Φ hΦ,
  cases flag.ex_flag_mem b.val with Ψ hΨ,
  exact con_of_mem_fcon (lt_of_not_ge hg) (h Φ Ψ) hΦ hΨ,
end

/-- Asserts that a section of a graded poset is totally flag-connected. -/
def section_total_flag_connected {α : Type u} [preorder α] (x y : α) : Prop :=
total_flag_connected (set.Icc x y)

/-- A graded poset is strongly flag-connected when all sections are totally flag-connected. -/
def strong_flag_connected (α : Type u) [preorder α] : Prop :=
∀ {x y : α}, section_total_flag_connected x y

/-- Strong flag-connectedness implies total flag-connectedness. -/
theorem tfcon_of_sfcon (α : Type u) [partial_order α] [order_top α] [graded α] :
  strong_flag_connected α → total_flag_connected α :=
begin
  intros h Φ Ψ,
  sorry
end

/-- Strong flag connectedness implies strong connectedness. -/
private lemma scon_of_sfcon (α : Type u) [partial_order α] [graded α] :
  strong_flag_connected α → strong_connected α :=
λ hsc _ _ hxy, @tcon_of_tfcon _ _ (set.Icc.order_top hxy) (set.Icc.graded hxy) hsc

-- Working title.
private lemma super_duper_flag_lemma {α : Type u} [partial_order α] [order_bot α] [order_top α]
{Φ Ψ : flag α} (x : proper α) (hΦ : x.val ∈ Φ.val) (hΨ : x.val ∈ Ψ.val)
(h1 : section_total_flag_connected ⊥ x.val) (h2 : section_total_flag_connected x.val ⊤) :
  flag_connected Φ Ψ :=
sorry

/-- Strong connectedness is equivalent to strong flag connectedness, up to a given top grade. -/
private lemma scon_iff_sfcon_aux {α : Type u} [partial_order α] [order_top α] [graded α] {n : ℕ} :
  grade_top α ≤ n → strong_connected α → strong_flag_connected α :=
begin
  /-
  induction n with n hn, {
    intros hg _ x y hxy,
    apply flag_connected_of_grade_le_two,
    have : @grade_top _ _ (set.Icc.order_top hxy) (set.Icc.graded hxy) = grade y - grade x :=
    by refl,
    rw this,
    have : grade y ≤ 2 := begin
      have := le_trans (grade_le_grade_top y) hg,
      linarith,
    end,
    exact le_trans (nat.sub_le_sub_right this (grade x)) (nat.sub_le 2 (grade x)),
  },
  -/
  sorry
end

/-- Strong connectedness is equivalent to strong flag-connectedness. -/
theorem scon_iff_sfcon {α : Type u} [partial_order α] [order_top α] [graded α] :
  strong_flag_connected α ↔ strong_connected α :=
begin
  refine ⟨scon_of_sfcon _, λ h, _⟩,
  apply scon_iff_sfcon_aux (le_of_eq rfl),
  repeat { assumption },
end

end
end graded
