/-
Copyright (c) 2021 Grayson Burton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Yaël Dillies, Violeta Hernández Palacios
-/
import order.zorn
import .grade

/-!
# Flags of polytopes

In this file we prove that isomorphisms preserve flags, and as such, automorphisms of orders induce
a group action on flags. We also define flag-adjacency and (strong) flag-connectedness.

Flags turn out to be crucial in proving a critical theorem: every graded partial order has elements
of each possible grade. As such, various important theorems that don't directly reference flags are
also proven in this file.

## Main definitions

* `polytope.flag`: a flag of a graded preorder.
* `graded.idx`: returns some element of a given grade.

## Main results

* `graded.ex_of_grade`: there's an element of any possible grade in a graded order.
* `graded.flag_card_eq`: all flags of a graded order have the same cardinality.
* `graded.scon_iff_sfcon`: strong connectedness and strong flag-connectedness are equivalent.

There's a few more of both I'm missing.
-/

universe u
variables {𝕆 α β : Type*}

instance [fintype α] [preorder α] [decidable_pred (@is_max_chain α (<))] : fintype (flag α) :=
sorry

-- first get `fintype (flags α × fin (grade ⊤ + 1))`,
-- then the obvious injection `α → flags α × fin (grade ⊤ + 1)`
-- noncomputable
def fintype.of_flag [partial_order α] [bounded_order α] [fintype (flag α)] : fintype α := sorry

namespace flag

instance [preorder α] : inhabited (flag α) := ⟨⟨max_chain (≤), max_chain_spec.1, max_chain_spec.2⟩⟩

/-- An element belongs to a flag iff it's comparable with everything in it. -/
lemma mem_flag_iff_comp [partial_order α] (Φ : flag α) {a : α} :
  a ∈ Φ ↔ ∀ b : Φ, a ≠ ↑b → a < ↑b ∨ ↑b < a :=
begin
  refine ⟨λ ha b hne, Φ.chain_lt ha b.2 hne, λ H, _⟩,
  by_contra ha,
  sorry
  -- exact Φ.max_chain.2 (Φ.chain_lt.insert (λ _ hb hne, H ⟨_, hb⟩ hne), set.ssubset_insert ha),
end

end flag

namespace order_iso

variables [partial_order α]

/-- Scalar multiplication of automorphisms by flags. -/
@[reducible]
def smul_def (γ : α ≃o α) (Φ : flag α) : set α := γ '' Φ

/-- Definition of scalar multiplication of automorphisms by flags. -/
@[simp]
lemma smul_def.eq (γ : α ≃o α) (Φ : flag α) : γ.smul_def Φ = γ '' Φ := rfl

/-- Automorphisms map flags to chains. -/
lemma smul_is_chain (γ : α ≃o α) (Φ : flag α) : is_chain (<) (γ.smul_def Φ) :=
begin
  rcases Φ with ⟨Φf, hΦ, hΦ'⟩,
  rintro a ⟨aw, ha, ha'⟩ b ⟨bw, hb, hb'⟩,
  induction ha', induction hb',
  exact hΦ ha hb,
end

/-- Automorphisms map flags to flags. -/
lemma smul_is_max_chain (γ : α ≃o α) (Φ : flag α) : is_max_chain (<) (γ.smul_def Φ) :=
begin
  use γ.smul_is_chain Φ,
  rcases Φ with ⟨Φf, hΦ, hΦ'⟩,
  rintro ⟨w, hwl, hwr⟩,
  rcases set.exists_of_ssubset hwr with ⟨a, ha, hna⟩,
  refine hΦ' ⟨set.insert (γ.inv a) Φf, _⟩,
  split,
  { rintro x (hx : _ ∨ _) y (hy : _ ∨ _) hne,
    have hxyne : x ≠ γ.inv a ∨ y ≠ γ.inv a,
    { rw ←not_and_distrib,
      rintro ⟨hl, hr⟩,
      exact hne (hl.trans hr.symm) },
    by_cases hxy : x ∈ Φf ∧ y ∈ Φf, { exact hΦ hxy.left hxy.right hne },
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
    refine hwl ha _ hne,
    replace hy' := set.mem_image_of_mem γ.hom hy',
    exact hwr.left hy' },
  { apply set.ssubset_insert,
    intro h,
    replace h := set.mem_image_of_mem γ.hom h,
    rw γ.hom_inv at h,
    exact hna h },
end

instance : has_scalar (α ≃o α) (flag α) :=
⟨λ γ Φ, ⟨γ.smul_def Φ, sorry, sorry⟩⟩

@[simp] lemma coe_smul (γ : α ≃o α) (Φ : flag α) : (↑(γ • Φ) : set α) = γ '' Φ := rfl

/-- The group action of the automorphism group of a order on its flags. -/
instance : mul_action (α ≃o α) (flag α) :=
{ one_smul := λ _, flag.ext $ set.image_id _,
  mul_smul := λ _ _ _, flag.ext $ by simp [←set.image_comp] }

end order_iso

section

/-- Chains of intervals are chains. -/
lemma chain_of_chain [preorder α] {x y : α} (c : set (set.Icc x y)) :
  is_chain (<) c → is_chain (<) (subtype.val '' c)  :=
begin
  intros hc a ha b hb hne,
  have hz : ∀ {z}, z ∈ subtype.val '' c → z ∈ set.Icc x y := begin
    intros _ hz,
    rcases hz with ⟨z', _, hz'⟩,
    rw ←hz',
    exact subtype.mem z',
  end,
  refine @hc ⟨a, hz ha⟩ _ ⟨b, hz hb⟩ _ _,
  rcases ha with ⟨a', _, ha'⟩,
  suffices : a' = ⟨a, _⟩, by rwa ←this,
  swap,
  rcases hb with ⟨b', _, hb'⟩,
  suffices : b' = ⟨b, _⟩, by rwa ←this,
  repeat { apply subtype.eq, assumption },
  exact λ h, hne (subtype.mk.inj h),
end

/-- One can build a chain by concatenating two others. -/
lemma chain_of_chains [preorder α] {x y z : α} (c : set (set.Icc x y)) (d : set (set.Ioc y z)) :
  is_chain (<) c → is_chain (<) d → is_chain (<) (subtype.val '' c ∪ subtype.val '' d) :=
begin
  intros hc hd a ha b hb hne,
  obtain ⟨a', hac, ha⟩ | ⟨a', had, ha⟩ := ha,
  all_goals { obtain ⟨b', hbc, hb⟩ | ⟨b', hbd, hb⟩ := hb },
  all_goals { rw [←ha, ←hb] },
  { exact or.imp id id (hc hac hbc (subtype.ne_of_val_ne $ by rwa [ha, hb])) },
  { exact or.inl (lt_of_le_of_lt a'.prop.right b'.prop.left) },
  { exact or.inr (lt_of_le_of_lt b'.prop.right a'.prop.left) },
  { exact or.imp id id (hd had hbd (subtype.ne_of_val_ne $ by rwa [ha, hb])) },
end

end

namespace flag
section preorder
variables [preorder α]

/-- Every chain is contained in a flag. -/
theorem flag_of_chain (c : set α) (hc : is_chain (<) c) : ∃ Φ : flag α, c ⊆ Φ :=
begin
  let all_chains := {s : set α | c ⊆ s ∧ is_chain (<) s},
  obtain ⟨Φ, ⟨_, hΦ₀⟩, hΦ₁, hΦ₂⟩ := zorn_subset_nonempty all_chains _ c ⟨rfl.subset, hc⟩,
    { refine ⟨⟨Φ, hΦ₀, _⟩, hΦ₁⟩,
      rintros ⟨d, hd, hdΦ₀, hdΦ₁⟩,
      have := hΦ₂ d _ hdΦ₀,
      induction this,
        { exact hdΦ₁ hdΦ₀ },
      change c ⊆ Φ with c ≤ Φ at hΦ₁,
      exact ⟨le_trans hΦ₁ hdΦ₀, hd⟩ },
  rintros cs hcs₀ hcs₁ ⟨s, hs⟩,
  refine ⟨⋃₀ cs, ⟨λ _ ha, set.mem_sUnion_of_mem ((hcs₀ hs).left ha) hs, _⟩,
    λ _, set.subset_sUnion_of_mem⟩,
  rintro y ⟨sy, hsy, hysy⟩ z ⟨sz, hsz, hzsz⟩ hyz,
  by_cases hsseq : sy = sz,
  { induction hsseq,
    apply (hcs₀ hsy).right,
    all_goals { assumption } },
  cases hcs₁ hsy hsz hsseq with h h,
  { exact (hcs₀ hsz).right (h hysy) hzsz hyz },
  { exact (hcs₀ hsy).right hysy (h hzsz) hyz }
end

/-- Every element belongs to some flag. -/
theorem ex_flag_mem (x : α) : ∃ Φ : flag α, x ∈ Φ :=
let ⟨Φ, hΦ⟩ := flag_of_chain {x} $ set.subsingleton.chain $ set.subsingleton_singleton in
⟨Φ, hΦ rfl⟩

/-- Every pair of incident elements belongs to some flag. -/
theorem ex_flag_both_mem (x y : α) (hxy : x < y ∨ y < x) : ∃ Φ : flag α, x ∈ Φ ∧ y ∈ Φ :=
begin
  wlog hxy := hxy using x y,
  obtain ⟨Φ, hΦ⟩ := flag_of_chain _ (is_chain_pair _ hxy),
  exact ⟨Φ, hΦ (set.mem_insert _ _), hΦ (set.mem_insert_of_mem _ rfl)⟩,
end

end preorder

section partial_order
variables [partial_order α]

/-- An element covers another iff they do so in the flag. -/
@[simp]
theorem cover_iff_flag_cover {Φ : flag α} (x y : Φ) : x ⋖ y ↔ x.val ⋖ y.val :=
begin
  refine ⟨λ h, ⟨h.left, λ z hzi, _⟩, λ ⟨hxy, hz⟩, ⟨hxy, λ _, hz _⟩⟩,
  cases h with hxy h,
  refine h ⟨z, _⟩ hzi,
  cases hzi with hxz hzy,
  refine Φ.mem_flag_iff_comp.2 (λ w hzw, _),
  have hwi := h w,
  simp only [set.mem_Ioo, not_and, not_lt] at hwi,
  rcases lt_trichotomy x w with hxw | hxw | hxw,
  { exact or.inl (lt_of_lt_of_le hzy (hwi hxw)) },
  { induction hxw, exact or.inr hxz },
  { exact or.inr (lt_trans hxw hxz) }
end

instance [preorder 𝕆] [order_bot α] [grade_order 𝕆 α] (Φ : flag α) : grade_order 𝕆 Φ :=
{ grade := λ a, grade 𝕆 a.val,
  grade_bot := grade_bot,
  strict_mono := λ _ _ h, grade_strict_mono h,
  hcovers := λ _ _ hcov, ((cover_iff_flag_cover _ _).1 hcov).grade }

end partial_order
end flag

namespace graded
section partial_order
variables [preorder 𝕆] [partial_order α] [bounded_order α] [grade_order 𝕆 α]
  (j : fin (grade 𝕆 (⊤ : α) + 1))

/-- A graded partial order has an element of grade `j` when `j ≤ grade 𝕆 ⊤`. -/
theorem ex_of_grade : is_grade α j :=
begin
  cases @ex_of_grade_lin (default _ : flag α) _ _ _ j with _ ha,
  exact ⟨_, ha⟩,
end

/-- The element of a certain grade in a graded partial order. -/
noncomputable def idx : α := classical.some (ex_of_grade j)

/-- Like `idx`, but allows specifying the type explicitly. -/
noncomputable abbreviation idx' (α : Type*) [partial_order α] [bounded_order α] [grade_order 𝕆 α]
  (j : fin (grade ⊤ + 1)) : α :=
idx j

/-- The defining property of `idx`. -/
@[simp]
theorem grade_idx : grade (idx j) = j := classical.some_spec (ex_of_grade j)

/-- The defining property of `idx`. -/
@[simp]
theorem grade_fin_idx : grade_fin (idx j) = j := subtype.ext $ grade_idx j

end partial_order

section order_iso
variables [partial_order α] [bounded_order α] [grade_order 𝕆 α] [partial_order β]
  [bounded_order β] [grade_order 𝕆 β]

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
        (lt_of_le_of_lt (H n (lt_add_one n) y hgy) (grade_strict_mono (oiso.lt_iff_lt.2 h))) },
  cases flag.ex_flag_mem x with Φ hx,
  let x' : Φ := ⟨x, hx⟩,
  have hn : n < grade (⊤ : Φ) + 1 := begin
    refine nat.lt_succ_of_le (le_trans (nat.le_succ n) _),
    rw ←hgx,
    exact grade_le_grade_top x,
  end,
  let n' : fin _ := ⟨n, hn⟩,
  let y := graded.idx' Φ n',
  use y,
  have hgy : grade y = n := grade_idx n',
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
  refine ⟨grade_le_of_order_iso _ rfl, _⟩,
  rw (by rw (order_iso.symm_apply_apply _ _) : grade x = grade (oiso.symm (oiso x))),
  exact not_lt_of_ge (grade_le_of_order_iso _ rfl)
end

/-- Order isomorphisms preserve top grades. -/
lemma grade_top_eq_of_order_iso (oiso : α ≃o β) : grade (⊤ : α) = grade (⊤ : β) :=
by { rw ←oiso.map_top, exact grade_eq_of_order_iso oiso ⊤ }

/-- Order isomorphisms preserve total connectedness. -/
private lemma tcon_order_iso_of_tcon (oiso : α ≃o β) : total_connected β → total_connected α :=
begin
  intros hb,
  cases hb with hb hb,
    { left, rwa grade_top_eq_of_order_iso oiso },
  exact or.inr (λ _ _, (con_order_iso_iff_con oiso _ _).2 (hb _ _)),
end

/-- Order isomorphisms preserve total connectedness. -/
theorem tcon_order_iso_iff_tcon (oiso : α ≃o β) : total_connected α ↔ total_connected β :=
⟨tcon_order_iso_of_tcon oiso.symm, tcon_order_iso_of_tcon oiso⟩

/-- Order isomorphisms preserve strong connectedness. -/
private lemma scon_order_iso_of_scon (oiso : α ≃o β) :
  graded.strong_connected β → graded.strong_connected α :=
λ hb _ _ hxy, (@tcon_order_iso_iff_tcon _ _ _ (set.Icc.bounded_order hxy) (set.Icc.graded _) _
  (set.Icc.bounded_order (oiso.monotone hxy)) (set.Icc.graded _) (oiso.Icc _ _)).2 (hb _)

/-- Order isomorphisms preserve strong connectedness. -/
theorem scon_order_iso_iff_scon (oiso : α ≃o β) :
  graded.strong_connected α ↔ graded.strong_connected β :=
⟨scon_order_iso_of_scon oiso.symm, scon_order_iso_of_scon oiso⟩

/-- Strong connectedness implies total connectedness. -/
theorem tcon_of_scon (α : Type*) [partial_order α] [bounded_order α] [grade_order 𝕆 α] :
  strong_connected α → total_connected α :=
λ h, (@tcon_order_iso_iff_tcon α (@set.Icc α _ ⊥ ⊤) _ _ _ _ (set.Icc.bounded_order bot_le)
  (set.Icc.graded bot_le) (set.Icc.self_order_iso_bot_top α)).2 (h bot_le)

end order_iso

section linear_order
variables [linear_order α] [bounded_order α] [grade_order 𝕆 α] (j : fin (grade (⊤ : α) + 1))

/-- `idx j` is the unique element of grade `j` in the linear order. -/
theorem grade_eq_iff_idx (a : α) : grade a = j ↔ a = graded.idx j :=
begin
  have idx := grade_idx j,
  refine ⟨λ ha, _, λ h, by rwa h⟩,
  obtain ⟨_, _, h⟩ := ex_unique_of_grade j,
  rw [(h _ ha), (h _ idx)]
end

/-- `grade_fin` is an order isomorphism for linearly ordered `α` with a top element. -/
noncomputable def order_iso_fin : α ≃o fin (grade ⊤ + 1) :=
rel_iso.of_surjective order_embedding.grade_fin $ λ x,
  ⟨graded.idx x, by simp [order_embedding.grade_fin]⟩

@[reducible]
noncomputable def grade_order.to_fintype : fintype α :=
fintype.of_bijective (order_iso_fin).inv_fun order_iso_fin.symm.bijective

/-- The cardinality of a linear order is its top grade plus one. -/
@[simp]
theorem fincard_eq_gt [fintype α] : fintype.card α = grade (⊤ : α) + 1 :=
begin
  cases hfc : fintype.card α, { rw fintype.card_eq_zero_iff at hfc, exact hfc.elim' ⊤ },
  rw [fintype.card_of_bijective order_iso_fin.bijective,
      fintype.card_fin (grade (⊤ : α) + 1)] at hfc,
  rw ←hfc
end

end linear_order

section partial_order
variables [partial_order α] [bounded_order α] [grade_order 𝕆 α] [fintype α]

/-- The cardinality of any flag is the grade of the top element. In other words, in a graded order,
all flags have the same cardinality. -/
theorem flag_card_eq_top_grade_succ (Φ : flag α) [fintype Φ] : fintype.card Φ = grade (⊤ : α) + 1 :=
fincard_eq_gt

/-- Any two flags have the same cardinality. -/
theorem flag_card_eq (Φ Ψ : flag α) [fintype Φ] [fintype Ψ] : fintype.card Φ = fintype.card Ψ :=
by repeat { rw flag_card_eq_top_grade_succ }

end partial_order

def Icc_foo [preorder α] [Π Φ : flag α, fintype Φ] (x y : α) :
  Π Φ : flag (set.Icc x y), fintype Φ :=
begin
  intro Φ,
  --apply fintype.of_injective ,
  sorry
end

def foo [preorder α] [order_bot α] [Π Φ : flag α, fintype Φ]
  (hf : ∀ (Φ Ψ : flag α), fintype.card Φ = fintype.card Ψ) :
  grade_order 𝕆 α :=
sorry

end graded

namespace flag
section

/-- Two flags are adjacent when there's exactly one element in one but not in the other. This isn't
quite the usual definition, and we've made it more general than necessary for reasons of
convenience, but we prove it to be equivalent to the usual one in the case of graded orders (see
`adjacent_iff_ex_j_adjacent`). -/
def adjacent [has_lt α] (Φ Ψ : flag α) : Prop := ∃! a, a ∈ Φ \ Ψ.val

instance [has_lt α] : is_irrefl (flag α) adjacent := ⟨λ _ ⟨_, ⟨hl, hr⟩, _⟩, hr hl⟩

variables [partial_order α] [bounded_order α] [grade_order 𝕆 α]

/-- If the indices of two flags are equal, all elements of one are in the other. -/
private lemma eq_of_eq_idx {Φ Ψ : flag α} :
  (∀ j, (graded.idx' Φ j).val = (graded.idx' Ψ j).val) → ∀ a, a ∈ Φ → a ∈ Ψ :=
begin
  intros h a ha,
  let a' : Φ := ⟨a, ha⟩,
  let ga := grade_fin a',
  change a with a'.val,
  have heq := h ga,
  have hga : (graded.idx' Φ ga) = a' := begin
    symmetry,
    apply (graded.grade_eq_iff_idx ga a').1,
    refl,
  end,
  rw hga at heq,
  rw heq,
  exact (graded.idx' Ψ ga).prop,
end

/-- Two flags are equal iff their elements of all grades are equal. -/
lemma eq_iff_eq_idx (Φ Ψ : flag α) : Φ = Ψ ↔ ∀ j, (graded.idx' Φ j).val = (graded.idx' Ψ j).val :=
⟨λ h _, by rw h, λ h, subtype.ext_val
  (set.ext (λ _, ⟨eq_of_eq_idx h _, eq_of_eq_idx (λ j, (h j).symm) _⟩))⟩

/-- Two flags are j-adjacent iff they share all but their j-th element. Note that a flag is never
adjacent to itself. -/
def j_adjacent (j : fin (grade ⊤ + 1)) (Φ Ψ : flag α) : Prop :=
∀ i, (graded.idx' Φ i).val = (graded.idx' Ψ i).val ↔ i ≠ j

instance (j : fin (grade ⊤ + 1)) : is_irrefl (flag α) (j_adjacent j) :=
⟨λ _ h, (h j).1 rfl rfl⟩

/-- j-adjacency is symmetric. -/
theorem j_adjacent.symm {j : fin (grade ⊤ + 1)} {Φ Ψ : flag α} :
  j_adjacent j Φ Ψ → j_adjacent j Ψ Φ :=
by { intros h i, rw ←(h i), exact eq_comm }

/-- Two flags in a graded order are adjacent iff they're j-adjacent for some j. -/
theorem adjacent_iff_ex_j_adjacent {Φ Ψ : flag α} : adjacent Φ Ψ ↔ ∃ j, j_adjacent j Φ Ψ :=
begin
  split, {
    intros hΦΨ,
    cases hΦΨ with a ha,
    have : a ∈ Φ := sorry,
    let a' : Φ := ⟨a, this⟩,
    let j := grade_fin a',
    use grade_fin a',
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

/-- Adjacency is symmetric in a graded order. -/
theorem adjacent.symm {Φ Ψ : flag α} : adjacent Φ Ψ → adjacent Ψ Φ :=
by repeat { rw adjacent_iff_ex_j_adjacent }; exact λ ⟨j, hj⟩, ⟨j, hj.symm⟩

end
end flag

/-- Flags are connected when they're related by a sequence of pairwise adjacent flags. -/
abbreviation polytope.flag_connected [preorder α] (Φ Ψ : flag α) : Prop := path flag.adjacent Φ Ψ

open polytope

namespace graded
section

/-- A `graded` is totally flag-connected when any two flags are connected.

Here we deviate from standard nomenclature: mathematicians would just call this flag-connectedness.
However, by doing this, it makes it unambiguous when we're talking about two flags being connected,
and when we're talking about a polytope being totally flag-connected. -/
def total_flag_connected (α : Type*) [preorder α] : Prop :=
∀ Φ Ψ : flag α, flag_connected Φ Ψ

/-- Any graded order of top grade less or equal to 1 has a single flag. -/
lemma flag_eq_of_grade_le_two (α : Type*) [partial_order α] [bounded_order α] [grade_order 𝕆 α]
  (Φ Ψ : flag α) :
  grade (⊤ : α) ≤ 1 → Φ = Ψ :=
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

/-- Any graded order of top grade less or equal to 2 is totally flag-connected. -/
theorem tfcon_of_grade_le_two (α : Type*) [partial_order α] [bounded_order α] [grade_order 𝕆 α] :
  grade (⊤ : α) ≤ 2 → total_flag_connected α :=
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
private lemma proper_flag_intersect_of_grade [partial_order α] [bounded_order α] [grade_order 𝕆 α]
  {Φ Ψ : flag α} (hg : 2 < grade (⊤ : α)) {j : fin (grade ⊤ + 1)} (hΦΨ : flag.j_adjacent j Φ Ψ)
  (k ∈ set.Ioo 0 (grade (⊤ : α))) (hjk : j.val ≠ k) :
  ∃ c : proper α, c.val ∈ Φ ∩ Ψ.val :=
begin
  let k : fin (grade ⊤ + 1) := ⟨k, nat.lt.step H.right⟩,
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
  exact hjk rfl,
end

/-- If two flags are flag-connected, then any two elements in these flags are connected, as long as
the grade exceeds 2. -/
lemma con_of_mem_fcon [partial_order α] [bounded_order α] [grade_order 𝕆 α]
  {Φ Ψ : flag α} (hg : 2 < grade (⊤ : α)) (h : flag_connected Φ Ψ) {a b : proper α} :
  a.val ∈ Φ → b.val ∈ Ψ → connected a b :=
begin
  intros ha hb,
  induction h with Φ' Φ Ψ Ϝ hΦΨ hΨϜ hab generalizing a b,
    { apply (path.next a a) _ path.refl,
      exact (Φ'.prop.left ha hb), },
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
theorem tcon_of_tfcon (α : Type*) [partial_order α] [bounded_order α] [grade_order 𝕆 α] :
  total_flag_connected α → total_connected α :=
begin
  intro h,
  by_cases hg : grade ⊤ ≤ 2,
    { exact tcon_of_grade_le_two α hg },
  refine or.inr (λ a b, _),
  cases flag.ex_flag_mem a.val with Φ hΦ,
  cases flag.ex_flag_mem b.val with Ψ hΨ,
  exact con_of_mem_fcon (lt_of_not_ge hg) (h Φ Ψ) hΦ hΨ,
end

/-- Asserts that a section of a graded order is totally flag-connected. -/
def section_total_flag_connected [preorder α] (x y : α) : Prop := total_flag_connected (set.Icc x y)

/-- A graded order is strongly flag-connected when all sections are totally flag-connected. -/
def strong_flag_connected (α : Type*) [preorder α] : Prop :=
∀ {x y : α}, section_total_flag_connected x y

/-- Strong flag-connectedness implies total flag-connectedness. -/
theorem tfcon_of_sfcon (α : Type*) [partial_order α] [order_top α] [order_bot α] [grade_order 𝕆 α] :
  strong_flag_connected α → total_flag_connected α :=
begin
  intros h Φ Ψ,
  sorry
end

/-- Strong flag connectedness implies strong connectedness. -/
private lemma scon_of_sfcon (α : Type*) [partial_order α] [order_bot α] [grade_order 𝕆 α] :
  strong_flag_connected α → strong_connected α :=
λ hsc _ _ hxy, @tcon_of_tfcon _ _ (set.Icc.bounded_order hxy) (set.Icc.graded hxy) hsc

-- Working title.
private lemma super_duper_flag_lemma [partial_order α] [bounded_order α]
  {Φ Ψ : flag α} (x : proper α) (hΦ : x.val ∈ Φ) (hΨ : x.val ∈ Ψ)
(h1 : section_total_flag_connected ⊥ x.val) (h2 : section_total_flag_connected x.val ⊤) :
  flag_connected Φ Ψ :=
sorry

/-- Strong connectedness is equivalent to strong flag connectedness, up to a given top grade. -/
private lemma scon_iff_sfcon_aux [partial_order α] [bounded_order α] [grade_order 𝕆 α] {n : ℕ} :
  grade 𝕆 (⊤ : α) ≤ n → strong_connected α → strong_flag_connected α :=
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
theorem scon_iff_sfcon [partial_order α] [bounded_order α] [grade_order 𝕆 α] :
  strong_flag_connected α ↔ strong_connected α :=
begin
  refine ⟨scon_of_sfcon _, λ h, _⟩,
  apply scon_iff_sfcon_aux (le_of_eq rfl),
  repeat { assumption },
end

end
end graded
