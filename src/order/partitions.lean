/-
Copyright (c) 2019 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/

import data.set.lattice order.order_iso

open function

variable {α : Type*}

namespace set

theorem disjoint_left {s t : set α} : disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t :=
by { simp only [disjoint, subset_def, ext_iff, lattice.le_bot_iff],
change (∀ x, x ∈ s ∩ t ↔ x ∈ ∅) ↔ _, simp }

end set

namespace order_iso
variables {β : Type*} {γ : Type*} [preorder β] [preorder γ] (oi : @order_iso β γ (≤) (≤))

theorem to_galois_connection : galois_connection oi oi.symm :=
λ b g, by rw [ord' oi, apply_inverse_apply]

protected def to_galois_insertion : @galois_insertion β γ _ _ (oi) (oi.symm) :=
{ choice := λ b h, oi b,
  gc := to_galois_connection oi,
  le_l_u := λ g, le_of_eq (oi.right_inv g).symm,
  choice_eq := λ b h, rfl }

end order_iso

namespace setoid

lemma sub_of_gen_sub (x : α → α → Prop) (s : setoid α) (H : ∀ a b : α, x a b → @setoid.r _ s a b) :
∀ a b : α, (eqv_gen x) a b → @setoid.r _ s a b :=
λ a b H2, eqv_gen.rec_on H2 H
  (@setoid.iseqv α s).1
  (λ x y _ H3, (@setoid.iseqv α s).2.1 H3)
  (λ x y z _ _ H4 H5,(@setoid.iseqv α s).2.2 H4 H5)

def top : setoid α :=
{ r := λ s₁ s₂, true,
  iseqv := ⟨λ _, trivial, λ _ _ _, trivial, λ _ _ _ _ _, trivial⟩ }

def bot : setoid α :=
{ r := (=),
  iseqv := ⟨λ _, rfl, λ _ _ h, h.symm, λ _ _ _ h₁ h₂, eq.trans h₁ h₂⟩ }

theorem eq_iff_r_eq : ∀ {r₁ r₂ : setoid α}, r₁ = r₂ ↔ r₁.r = r₂.r
| ⟨r1, e1⟩ ⟨r2, e2⟩ :=
iff.intro (λ h, by injection h) (λ h, by dsimp at h; subst h)

theorem eq_iff_eqv_class_eq {r₁ r₂ : setoid α} :
  r₁ = r₂ ↔ (∀ a, let r1 := r₁.r in let r2 := r₂.r in {b | r1 a b} = {b | r2 a b}) :=
by rw eq_iff_r_eq; exact iff.intro (by { intros h a r1 r2, have : r1 = r2 := h, rw this })
  (λ h, by apply funext; exact h)

instance : has_subset (setoid α) :=
⟨λ r₁ r₂, ∀ (a : α), let r1 := r₁.r in let r2 := r₂.r in {b | r1 a b} ⊆ {b | r2 a b}⟩

theorem subset_def (r₁ r₂ : setoid α) : r₁ ⊆ r₂ ↔ ∀ (a : α), let r1 := r₁.r in
  let r2 := r₂.r in {b | r1 a b} ⊆ {b | r2 a b} :=
iff.rfl

@[simp] theorem subset.refl (r : setoid α) : r ⊆ r :=
by rw [subset_def]; exact λ _, set.subset.refl _

theorem subset.trans {r₁ r₂ r₃ : setoid α} : r₁ ⊆ r₂ → r₂ ⊆ r₃ → r₁ ⊆ r₃ :=
by iterate { rw [subset_def] }; exact λ h₁ h₂ a, set.subset.trans (h₁ a) (h₂ a)

theorem subset.antisymm {r₁ r₂ : setoid α} (H₁ : r₁ ⊆ r₂) (H₂ : r₂ ⊆ r₁) : r₁ = r₂ :=
begin
  rw subset_def at H₁ H₂,
  rw eq_iff_eqv_class_eq,
  intro a,
  exact set.subset.antisymm (H₁ a) (H₂ a)
end

instance : has_ssubset (setoid α) :=
⟨λa b, a ⊆ b ∧ ¬ b ⊆ a⟩

def rel_union (r₁ r₂ : setoid α) : α → α → Prop :=
λ s₁ s₂, let r1 := r₁.r in let r2 := r₂.r in r1 s₁ s₂ ∨ r2 s₁ s₂

protected def union (r₁ r₂ : setoid α) : setoid α :=
eqv_gen.setoid $ rel_union r₁ r₂

instance : has_union (setoid α) :=
⟨setoid.union⟩

theorem union_def {r₁ r₂ : setoid α} : r₁ ∪ r₂ = eqv_gen.setoid (rel_union r₁ r₂) :=
rfl

@[simp] theorem subset_union_left (s t : setoid α) : s ⊆ s ∪ t :=
by simp only [subset_def, set.subset_def]; exact λ a x h, eqv_gen.rel a x (or.inl h)

@[simp] theorem subset_union_right (s t : setoid α) : t ⊆ s ∪ t :=
by simp only [subset_def, set.subset_def]; exact λ a x h, eqv_gen.rel a x (or.inr h)

theorem union_subset {r₁ r₂ r₃ : setoid α} (h13 : r₁ ⊆ r₃) (h23 : r₂ ⊆ r₃) : r₁ ∪ r₂ ⊆ r₃ :=
by simp only [subset_def, set.subset_def, set.mem_set_of_eq] at h13 h23 ⊢;
exact λ a x h, sub_of_gen_sub (rel_union r₁ r₂) r₃
  (λ x' y' h', or.elim h' (h13 x' y') (h23 x' y')) a x h

protected def inter (r₁ r₂ : setoid α) : setoid α :=
{ r := λ s₁ s₂, let r1 := r₁.r in let r2 := r₂.r in r1 s₁ s₂ ∧ r2 s₁ s₂,
  iseqv := ⟨λ x, ⟨r₁.2.1 x, r₂.2.1 x⟩, (λ x y h, ⟨r₁.2.2.1 h.1, r₂.2.2.1 h.2⟩),
      λ x y z h₁ h₂, ⟨r₁.2.2.2 h₁.1 h₂.1, r₂.2.2.2 h₁.2 h₂.2⟩⟩ }

instance : has_inter (setoid α) :=
⟨setoid.inter⟩

theorem inter_def {r₁ r₂ : setoid α} : r₁ ∩ r₂ =
  { r := λ s₁ s₂, let r1 := r₁.r in let r2 := r₂.r in r1 s₁ s₂ ∧ r2 s₁ s₂,
    iseqv := ⟨λ x, ⟨r₁.2.1 x, r₂.2.1 x⟩, (λ x y h, ⟨r₁.2.2.1 h.1, r₂.2.2.1 h.2⟩),
      λ x y z h₁ h₂, ⟨r₁.2.2.2 h₁.1 h₂.1, r₂.2.2.2 h₁.2 h₂.2⟩⟩ } :=
rfl

@[simp] theorem inter_subset_left (r₁ r₂ : setoid α) : r₁ ∩ r₂ ⊆ r₁ :=
by simp only [subset_def, set.subset_def]; exact λ a x h, and.left h

@[simp] theorem inter_subset_right (r₁ r₂ : setoid α) : r₁ ∩ r₂ ⊆ r₂ :=
by simp only [subset_def, set.subset_def]; exact λ a x h, and.right h

theorem subset_inter {s t r : setoid α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
by rw [subset_def] at rs rt ⊢; exact λ a, set.subset_inter (rs a) (rt a)

theorem le_top (r : setoid α) : r ⊆ top :=
by simp only [subset_def, set.subset_def];
exact λ a x h, trivial

theorem bot_le (r : setoid α) : bot ⊆ r :=
by simp only [subset_def, bot, set.subset_def, set.mem_set_of_eq];
exact λ a x h, h.symm ▸ (r.2.1 x)

def Sup (s : set (setoid α)) : setoid α :=
eqv_gen.setoid $ λ (x y : α), ∃ r' : setoid α, r' ∈ s ∧ @r α r' x y

lemma le_Sup (s : set (setoid α)) : ∀ a ∈ s, a ⊆ Sup s :=
by simp only [subset_def, set.subset_def];
exact λ a H _ _ h, eqv_gen.rel _ _ (exists.intro a ⟨H, h⟩)

lemma Sup_le (s : set (setoid α)) (a : setoid α) : (∀ b ∈ s, b ⊆ a) → Sup s ⊆ a :=
by simp only [subset_def, set.subset_def, set.mem_set_of_eq, Sup];
exact λ H x y h, let rsup := λ x y, ∃ r', r' ∈ s ∧ @r α r' x y in
  sub_of_gen_sub rsup a (λ x' y' h', exists.elim h' (λ b' hb', H b' hb'.1 x' y' hb'.2)) x y h

def Inf (s : set (setoid α)) : setoid α :=
eqv_gen.setoid $ λ (x y : α), ∀ r' : setoid α, r' ∈ s → @r α r' x y

lemma Inf_le (s : set (setoid α)) : ∀ a ∈ s, Inf s ⊆ a :=
by simp only [subset_def, set.subset_def, set.mem_set_of_eq, Inf];
exact λ a H x y h, let rinf := λ x y, ∀ r', r' ∈ s → @r α r' x y in
  sub_of_gen_sub rinf a (λ x' y' h', h' a H) x y h

lemma le_Inf (s : set (setoid α)) (a : setoid α) : (∀ b ∈ s, a ⊆ b) → a ⊆ Inf s :=
by simp only [subset_def, set.subset_def, set.mem_set_of_eq, Inf];
exact λ H x y h, eqv_gen.rel x y (λ r' hr', H r' hr' x y h)

instance lattice_setoid : lattice.complete_lattice (setoid α) :=
{ lattice.complete_lattice .
  le           := (⊆),
  le_refl      := subset.refl,
  le_trans     := λ a b c, subset.trans,
  le_antisymm  := λ a b, subset.antisymm,

  lt           := (⊂),
  lt_iff_le_not_le := λ x y, iff.refl _,

  sup          := (∪),
  le_sup_left  := subset_union_left,
  le_sup_right := subset_union_right,
  sup_le       := λ a b c, union_subset,

  inf          := (∩),
  inf_le_left  := inter_subset_left,
  inf_le_right := inter_subset_right,
  le_inf       := λ a b c, subset_inter,

  top          := top,
  le_top       := le_top,

  bot          := bot,
  bot_le       := bot_le,

  Sup          := Sup,
  le_Sup       := le_Sup,
  Sup_le       := Sup_le,

  Inf          := Inf,
  le_Inf       := le_Inf,
  Inf_le       := Inf_le }

variables (α) (𝔯 : setoid α)

/- We define a partition as a family of nonempty sets such that any element of α is contained in
a unique set. -/

/- Is there a way to set this up so that we talk about the equivalence classes via quot? -/
structure partition :=
(blocks : set (set α))
(empty_not_mem_blocks : ∅ ∉ blocks)
(blocks_partition : ∀ a, ∃ b, b ∈ blocks ∧ a ∈ b ∧ ∀ b' ∈ blocks, a ∈ b' → b = b')

variable {α}

theorem disjoint_union_of_partition (P : partition α) :
  set.sUnion P.1 = @set.univ α ∧ ∀ b₁ b₂, b₁ ∈ P.1 → b₂ ∈ P.1 → b₁ ≠ b₂ → disjoint b₁ b₂ :=
by simp [set.ext_iff];
  exact ⟨λ a, exists.elim (P.blocks_partition a) $ λ b hb, exists.intro b ⟨hb.1, hb.2.1⟩,
  by { intros b₁ b₂ hb₁ hb₂ h,
    rw ←set.ext_iff at h,
    have HP : ∅ ∉ P.blocks := P.empty_not_mem_blocks,
    have Hb₁ : b₁ ≠ ∅ := λ h', (h'.symm ▸ HP) hb₁,
    refine set.disjoint_left.mpr _,
    intros a ha,
    exact exists.elim (P.blocks_partition a) (λ b' hb' h',
      have Hb' : b₁ = b' := ((hb'.2.2 b₁ hb₁) ha).symm,
      h (eq.trans Hb' $ hb'.2.2 b₂ hb₂ $ Hb' ▸ h')) }⟩

def partition_of_disjoint_union {P : set (set α)} (h₁ : ∅ ∉ P) (h₂ : set.sUnion P = @set.univ α)
  (h₃ : ∀ (b₁ b₂), b₁ ∈ P → b₂ ∈ P → b₁ ≠ b₂ → disjoint b₁ b₂) : partition α :=
by simp [set.ext_iff] at h₂;
exact { blocks := P,
  empty_not_mem_blocks := h₁,
  blocks_partition := λ a, by exact exists.elim (h₂ a) (λ b hb, and.elim hb $ λ hb hab,
    exists.intro b ⟨hb, hab, λ b' hb' hab',
      by { have : ¬disjoint b b' → ¬b ≠ b' := mt (h₃ b b' hb hb'),
        haveI := classical.prop_decidable,
        simp at this, refine this (mt disjoint_iff.mp _),
        exact @set.ne_empty_of_mem _ (b ∩ b') a (set.mem_inter hab hab') }⟩) }

namespace partition
variables {α} (P : partition α)

theorem eq_of_blocks_eq : ∀ {P₁ P₂ : partition α}, P₁ = P₂ ↔ P₁.blocks = P₂.blocks
| ⟨_, _, _⟩ ⟨_, _, _⟩ :=
by simp

theorem ext {P₁ P₂ : partition α} : P₁ = P₂ ↔ ∀ b, b ∈ P₁.1 ↔ b ∈ P₂.1 :=
by simp only [eq_of_blocks_eq, set.ext_iff]

@[extensionality]
theorem ext' {P₁ P₂ : partition α} : (∀ b, b ∈ P₁.1 ↔ b ∈ P₂.1) → P₁ = P₂ :=
ext.2

theorem setoid_blocks_partition : ∀ a : α, ∃ b : set α, b ∈ {t | ∃ a : α, {b | a ≈ b} = t} ∧
  a ∈ b ∧ ∀ b' ∈ {t | ∃ a : α, {b | a ≈ b} = t}, a ∈ b' → b = b' :=
let r' := 𝔯.r in λ a, exists.intro {b | a ≈ b}
  ⟨exists.intro a rfl, by simp,
  by simp only [set.ext_iff, set.mem_set_of_eq];
    exact λ x h₁ h₂ a', exists.elim h₁ $ λ y hy,
      have ha : y ≈ a := (hy a).mpr h₂, have ha' : y ≈ a' ↔ a' ∈ x := hy a',
      iff.intro (λ H, ha'.mp (setoid.trans ha H)) $
        λ H, setoid.trans (setoid.symm ha) $ ha'.mpr H⟩

def coe_of_setoid : partition α :=
let r' := 𝔯.r in
{ blocks := {t | ∃ a, {b | a ≈ b} = t},
  empty_not_mem_blocks := by rw [set.nmem_set_of_eq]; exact λ h, exists.elim h
    (λ a ha, by simp [set.eq_empty_iff_forall_not_mem] at ha; exact ha a (setoid.refl a)),
  blocks_partition := setoid_blocks_partition 𝔯 }

def setoid_of_partition : setoid α :=
{ r := λ x y, ∃ b, b ∈ P.blocks ∧ x ∈ b ∧ y ∈ b,
  iseqv := ⟨λ x, exists.elim (P.blocks_partition x) (λ b h, exists.intro b ⟨h.1, h.2.1, h.2.1⟩),
    λ x y H, exists.elim H $ λ b hb, exists.intro b ⟨hb.1, hb.2.2, hb.2.1⟩,
    λ x y z hxy hyz, exists.elim hxy $ λ b hb, exists.elim hyz $
      λ b' hb', exists.elim (P.blocks_partition y) $
        λ b'' hb'', have Hb : b'' = b := hb''.2.2 b hb.1 hb.2.2,
          have Hb' : b'' = b' := hb''.2.2 b' hb'.1 hb'.2.1,
          exists.intro b'' ⟨hb''.1, Hb.symm ▸ hb.2.1, Hb'.symm ▸ hb'.2.2⟩⟩ }

theorem setoid_partition_setoid : setoid_of_partition (coe_of_setoid 𝔯) = 𝔯 :=
by unfold setoid_of_partition coe_of_setoid; simp only [eq_iff_r_eq];
ext x y;
exact iff.intro
(λ H, exists.elim H $ λ b hb, exists.elim hb.1 $ λ a ha,
  have hax : x ≈ a := by { have := ha.substr hb.2.1, rw [set.mem_set_of_eq] at this,
    exact setoid.symm this },
  have hay : a ≈ y := by { have := ha.substr hb.2.2, rwa [set.mem_set_of_eq] at this },
  setoid.trans hax $ hay)
(λ H, exists.elim (setoid_blocks_partition 𝔯 x) $ λ b h, exists.intro b
  ⟨exists.intro x $ exists.elim h.1 $ λ y' hy',
    by simp only [set.ext_iff, set.mem_set_of_eq] at hy' ⊢;
    exact λ a, have Hy'x : y' ≈ x := (hy' x).mpr h.2.1,
      iff.intro (λ ha, (hy' a).mp $ setoid.trans Hy'x ha) $
        λ ha, setoid.trans (setoid.symm Hy'x) $ (hy' a).mpr ha,
  h.2.1, exists.elim h.1 $ λ y' hy', by simp only [set.ext_iff] at hy';
    exact (hy' y).mp (setoid.trans ((hy' x).mpr h.2.1) H : y' ≈ y)⟩)

theorem partition_setoid_partition : coe_of_setoid (setoid_of_partition P) = P :=
by unfold setoid_of_partition coe_of_setoid; simp only [eq_of_blocks_eq];
ext x; simp only [set.mem_set_of_eq];
exact iff.intro
  (λ H, exists.elim H $ λ a ha, exists.elim (P.blocks_partition a) $
    λ x' hx', have x = x' := by rw ←ha;
      ext y; rw [set.mem_set_of_eq];
        exact iff.intro
          (λ hy, exists.elim hy $ λ b' hb', (hx'.2.2 b' hb'.1 hb'.2.1).substr hb'.2.2)
          (λ hy, exists.intro x' ⟨hx'.1, hx'.2.1, hy⟩),
      this.symm ▸ hx'.1)
  (λ H, have xne : x ≠ ∅ := λ h, (h.symm ▸ P.empty_not_mem_blocks) H,
    exists.elim (set.exists_mem_of_ne_empty xne) $ λ a ha, exists.intro a $
      by ext y; simp only [set.mem_set_of_eq];
        exact iff.intro
          (λ hy, exists.elim hy $ λ b hb, exists.elim (P.blocks_partition a)
            (λ b' hb', have hb'b : b' = b := hb'.2.2 b hb.1 hb.2.1,
              have hb'x : b' = x := hb'.2.2 x H ha,
              (eq.trans hb'b.symm hb'x).subst hb.2.2))
          (λ hy, exists.intro x ⟨H, ha, hy⟩))

instance : has_subset (partition α) :=
⟨λ P₁ P₂, ∀ p ∈ P₁.1, ∃ q, q ∈ P₂.1 ∧ p ⊆ q⟩

theorem subset_def (P₁ P₂ : partition α) : P₁ ⊆ P₂ ↔ ∀ p ∈ P₁.1, ∃ q, q ∈ P₂.1 ∧ p ⊆ q :=
iff.rfl

@[simp] theorem subset.refl (P : partition α) : P ⊆ P :=
by rw [subset_def]; exact λ p H, exists.intro p ⟨H, set.subset.refl p⟩

theorem subset.trans {s₁ s₂ s₃ : partition α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
by iterate { rw subset_def }; exact λ h₁ h₂ p hp, exists.elim (h₁ p hp)
  (λ p' hp', exists.elim (h₂ p' hp'.1) $
    λ p'' hp'', exists.intro p'' ⟨hp''.1, set.subset.trans hp'.2 hp''.2⟩)

theorem subset.antisymm {s₁ s₂ : partition α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
begin
  haveI := classical.prop_decidable,
  have hs₁ := disjoint_union_of_partition s₁, have hs₂ := disjoint_union_of_partition s₂,
  ext, rw subset_def at H₁ H₂,
  exact iff.intro
    (λ h, exists.elim (H₁ b h) $ λ b' hb', exists.elim (H₂ b' hb'.1) $ λ b'' hb'',
      by { replace hs₁ := mt (hs₁.2 b b'' h hb''.1), simp at hs₁,
        have : b = b'' := by { refine hs₁ _,
          have : b ⊆ b'' := set.subset.trans hb'.2 hb''.2,
          have hinter : b ∩ b'' = b := set.inter_eq_self_of_subset_left this,
          have hbne : b ≠ ∅ := by { by_contra H, simp at H,
            exact s₁.empty_not_mem_blocks (H ▸ h) },
          replace hinter := hinter.substr hbne, simpa [disjoint] },
        have b'b : b' = b := set.subset.antisymm (this.symm ▸ hb''.2) (hb'.2),
        exact b'b ▸ hb'.1 })
    (λ h, exists.elim (H₂ b h) $ λ b' hb', exists.elim (H₁ b' hb'.1) $ λ b'' hb'',
      by { replace hs₂ := mt (hs₂.2 b b'' h hb''.1), simp at hs₂,
        have : b = b'' := by { refine hs₂ _,
          have : b ⊆ b'' := set.subset.trans hb'.2 hb''.2,
          have hinter : b ∩ b'' = b := set.inter_eq_self_of_subset_left this,
          have hbne : b ≠ ∅ := by { by_contra H, simp at H,
            exact s₂.empty_not_mem_blocks (H ▸ h) },
          replace hinter := hinter.substr hbne, simpa [disjoint] },
        have b'b : b' = b := set.subset.antisymm (this.symm ▸ hb''.2) (hb'.2),
        exact b'b ▸ hb'.1 })
end

instance : has_ssubset (partition α) :=
⟨λa b, a ⊆ b ∧ ¬ b ⊆ a⟩

instance partial_order_of_partitions : partial_order (partition α) :=
{ le := (⊆),
  lt := (⊂),
  le_refl := subset.refl,
  le_trans := @subset.trans _,
  le_antisymm := @subset.antisymm _ }

theorem setoid_of_partition_order_preserving (s₁ s₂ : setoid α) :
  s₁ ⊆ s₂ ↔ coe_of_setoid s₁ ⊆ coe_of_setoid s₂ :=
by simp [coe_of_setoid, subset_def, setoid.subset_def, set.ext_iff, set.subset_def];
exact iff.intro
  (λ H p x hx, exists.intro {x' | @r α s₂ x x'}
    ⟨exists.intro x $ λ y, by trivial, λ y hy, H x y $ (hx y).mpr hy⟩)
  (λ H x y hxy, exists.elim (H {x' | @r α s₁ x x'} x (λ x', by trivial)) $
    λ q hq, have Hx : x ∈ q := hq.2 x (s₁.2.1 x), have Hy : y ∈ q := hq.2 y hxy,
      exists.elim hq.1 $ λ a ha, have hax : @r α s₂ a x := (ha x).mpr Hx,
        have hay : @r α s₂ a y := (ha y).mpr Hy, s₂.2.2.2 (s₂.2.2.1 hax) hay)

def order_iso_setoid_partition : @order_iso (setoid α) (partition α) (≤) (≤) :=
{ to_fun := coe_of_setoid,
  inv_fun := setoid_of_partition,
  left_inv := setoid_partition_setoid,
  right_inv := partition_setoid_partition,
  ord := setoid_of_partition_order_preserving }

instance : lattice.complete_lattice (partition α) :=
(order_iso.to_galois_insertion order_iso_setoid_partition).lift_complete_lattice

end partition

end setoid
