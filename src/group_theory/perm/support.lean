/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
import data.set.finite
import group_theory.perm.basic
import dynamics.fixed_points.basic

/-!
# Support of a permutation

## Main definitions

In the following, `f g : equiv.perm α`.

* `equiv.perm.support`: the elements `x : α` that are not fixed by `f`.
* `equiv.perm.disjoint`: two permutations `f` and `g` are `disjoint` iff their `support`
  are disjoint.

## Implementation details

A perm's `support` need not necessarily be finite. To facilitate this, `f.support` is provided
as a `set` rather than a `finset`. However, often we want to deal with the cardinality of a
`support`. Since one can have finite support even if the underlying type if not `fintype`,
instead of juggling `[fintype ↥(f.support)]`, we use instead `set.finite f.support`. That leads
to lemma statements that mention `(h : set.finite f.support).to_finset.card`, and sometimes
`letI : fintype ↥(f.support) := h.fintype` in proofs.

-/

lemma set.to_finset_image_embedding {α β : Type*} (s : set α) (f : α ↪ β)
  [fintype s] [fintype (f '' s)] :
  (f '' s).to_finset = s.to_finset.map f :=
by { ext, simp }

lemma set.to_finset_image_equiv {α β : Type*} (s : set α) (f : α ≃ β)
  [fintype s] [h : fintype (f '' s)] :
  (f '' s).to_finset = s.to_finset.map f.to_embedding :=
begin
  letI : fintype ((f.to_embedding) '' s) := h,
  convert s.to_finset_image_embedding f.to_embedding
end

open equiv set

namespace equiv.perm

variables {α β : Type*}

section support

/-- The `set` of nonfixed points of a permutation. -/
def support (f : perm α) : set α := (function.fixed_points f)ᶜ

@[simp] lemma mem_support {f : perm α} {x : α} : x ∈ f.support ↔ f x ≠ x := iff.rfl

lemma not_mem_support {f : perm α} {x : α} : x ∉ f.support ↔ f x = x := by simp

@[simp] lemma support_eq_empty_iff {σ : perm α} : σ.support = ∅ ↔ σ = 1 :=
by simp [set.ext_iff, equiv.perm.ext_iff]

@[simp] lemma support_one : (1 : perm α).support = ∅ :=
by rw support_eq_empty_iff

@[simp] lemma support_refl : support (equiv.refl α) = ∅ := support_one

lemma support_congr {f g : perm α} (h : f.support = g.support)
  (h' : ∀ x ∈ f.support, f x = g x) : f = g :=
begin
  ext x,
  by_cases hx : x ∈ f.support,
  { exact h' x hx },
  { have : x ∉ g.support := h ▸ hx,
    rw [not_mem_support.mp hx, not_mem_support.mp this] }
end

lemma support_mul_le (f g : perm α) :
  (f * g).support ≤ f.support ⊔ g.support :=
λ x, begin
  rw [sup_eq_union, mem_union, mem_support, mem_support,
      mem_support, mul_apply, ←not_and_distrib, not_imp_not],
  rintro ⟨hf, hg⟩,
  rw [hg, hf]
end

lemma support_prod_le (l : list (perm α)) :
  l.prod.support ≤ (l.map support).foldr (⊔) ⊥ :=
begin
  induction l with hd tl hl,
  { simp },
  { rw [list.prod_cons, list.map_cons, list.foldr_cons],
    refine (support_mul_le hd tl.prod).trans _,
    exact sup_le_sup (le_refl _) hl }
end

lemma exists_mem_support_of_mem_support_prod {l : list (perm α)} {x : α}
  (hx : x ∈ l.prod.support) :
  ∃ f : perm α, f ∈ l ∧ x ∈ f.support :=
begin
  contrapose! hx,
  simp_rw [mem_support, not_not] at hx ⊢,
  induction l with f l ih generalizing hx,
  { refl },
  { rw [list.prod_cons, mul_apply, ih (λ g hg, hx g (or.inr hg)), hx f (or.inl rfl)] },
end

@[simp] lemma support_inv (σ : perm α) : support (σ⁻¹) = σ.support :=
by simp [set.ext_iff, (inv_eq_iff_eq).trans eq_comm]

lemma support_pow_le (σ : perm α) (n : ℕ) :
  (σ ^ n).support ≤ σ.support :=
begin
  induction n with n hn,
  { simp },
  { rw [pow_succ],
    refine (support_mul_le σ (σ ^ n)).trans _,
    exact sup_le (le_refl _) hn }
end

lemma support_gpow_le (σ : perm α) (n : ℤ) :
  (σ ^ n).support ≤ σ.support :=
by { cases n; simpa using support_pow_le _ _ }

@[simp]
lemma apply_mem_support {f : perm α} {x : α} :
  f x ∈ f.support ↔ x ∈ f.support :=
by rw [mem_support, mem_support, ne.def, ne.def, not_iff_not, apply_eq_iff_eq]

@[simp]
lemma pow_apply_mem_support {f : perm α} {n : ℕ} {x : α} :
  (f ^ n) x ∈ f.support ↔ x ∈ f.support :=
begin
  induction n with n ih,
  { refl },
  rw [pow_succ, perm.mul_apply, apply_mem_support, ih]
end

@[simp]
lemma gpow_apply_mem_support {f : perm α} {n : ℤ} {x : α} :
  (f ^ n) x ∈ f.support ↔ x ∈ f.support :=
begin
  cases n,
  { rw [int.of_nat_eq_coe, gpow_coe_nat, pow_apply_mem_support] },
  { rw [gpow_neg_succ_of_nat, ← support_inv, ← inv_pow, pow_apply_mem_support] }
end

lemma support_swap [decidable_eq α] {x y : α} (h : x ≠ y) : support (swap x y) = {x, y} :=
begin
  ext z,
  by_cases hx : z = x;
  by_cases hy : z = y,
  any_goals { simpa [hx, hy] using h.symm },
  { simp [swap_apply_of_ne_of_ne, hx, hy] }
end

lemma support_swap_iff [decidable_eq α] (x y : α) :
  support (swap x y) = {x, y} ↔ x ≠ y :=
begin
  refine ⟨λ h H, _, support_swap⟩,
  subst H,
  simp only [swap_self, support_refl, pair_eq_singleton] at h,
  have : x ∈ ∅,
    { rw h,
      exact mem_singleton _ },
  simpa
end

lemma support_swap_mul_swap [decidable_eq α] {x y z : α} (h : list.nodup [x, y, z]) :
  support (swap x y * swap y z) = {x, y, z} :=
begin
  simp only [list.not_mem_nil, and_true, list.mem_cons_iff, not_false_iff, list.nodup_cons,
             list.mem_singleton, and_self, list.nodup_nil] at h,
  push_neg at h,
  apply le_antisymm,
  { convert support_mul_le _ _,
    rw [support_swap h.left.left, support_swap h.right],
    ext,
    simp [or.comm, or.left_comm] },
  { rintro w (rfl | rfl | rfl | _);
    simp [swap_apply_of_ne_of_ne, h.left.left, h.left.left.symm, h.left.right, h.left.right.symm,
          h.right.symm] }
end

lemma support_swap_mul_ge_support_diff [decidable_eq α] (f : perm α) (x y : α) :
  f.support \ {x, y} ≤ (swap x y * f).support :=
begin
  intro,
  simp only [and_imp, perm.coe_mul, mem_singleton_iff, mem_insert_iff, function.comp_app, ne.def,
             mem_diff, mem_support],
  push_neg,
  rintro ha ⟨hx, hy⟩ H,
  rw [swap_apply_eq_iff, swap_apply_of_ne_of_ne hx hy] at H,
  exact ha H
end

lemma support_swap_mul_eq [decidable_eq α] (f : perm α) (x : α) (h : f (f x) ≠ x) :
  (swap x (f x) * f).support = f.support \ {x} :=
begin
  by_cases hx : f x = x,
  { simp [hx] },
  ext z,
  by_cases hzx : z = x,
  { simp [hzx] },
  by_cases hzf : z = f x,
  { simp [hzf, hx, h, swap_apply_of_ne_of_ne], },
  by_cases hzfx : f z = x,
  { simp [ne.symm hzx, hzx, ne.symm hzf, hzfx] },
  { simp [ne.symm hzx, hzx, ne.symm hzf, hzfx, f.injective.ne hzx, swap_apply_of_ne_of_ne] }
end

lemma mem_support_swap_mul_imp_mem_support_ne [decidable_eq α] {f : perm α} {x y : α}
  (hy : y ∈ support (swap x (f x) * f)) : y ∈ support f ∧ y ≠ x :=
begin
  simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff] at *,
  by_cases h : f y = x,
  { split; intro; simp only [*, if_true, eq_self_iff_true, not_true, ne.def] at * },
  { split_ifs at hy; cc }
end

@[simp]
lemma support_extend_domain {p : β → Prop} [decidable_pred p]
  (f : α ≃ subtype p) {g : perm α} :
  support (g.extend_domain f) = g.support.image f.as_embedding :=
begin
  ext b,
  simp only [exists_prop, to_embedding_apply, mem_image, ne.def, mem_support],
  by_cases pb : p b,
  { rw [extend_domain_apply_subtype _ _ pb],
    split,
    { rintro h,
      refine ⟨f.symm ⟨b, pb⟩, _, by simp⟩,
      contrapose! h,
      simp [h] },
    { rintro ⟨a, ha, hb⟩,
      contrapose! ha,
      obtain rfl : a = f.symm ⟨b, pb⟩,
      { rw eq_symm_apply,
        exact subtype.coe_injective hb },
      rw eq_symm_apply,
      exact subtype.coe_injective ha } },
  { rw [extend_domain_apply_not_subtype _ _ pb],
    simp only [not_exists, false_iff, not_and, eq_self_iff_true, not_true],
    rintros a ha rfl,
    exact pb (subtype.prop _) }
end

lemma pow_apply_eq_self_of_apply_eq_self {f : perm α} {x : α} (hfx : f x = x) (n : ℕ) :
  (f ^ n) x = x :=
begin
  rw ←not_mem_support at hfx ⊢,
  exact λ H, hfx (support_pow_le _ _ H)
end

lemma gpow_apply_eq_self_of_apply_eq_self {f : perm α} {x : α} (hfx : f x = x) (n : ℤ) :
  (f ^ n) x = x :=
begin
  rw ←not_mem_support at hfx ⊢,
  exact λ H, hfx (support_gpow_le _ _ H)
end

lemma pow_apply_eq_of_apply_apply_eq_self {f : perm α} {x : α} (hffx : f (f x) = x) (n : ℕ) :
  (f ^ n) x = x ∨ (f ^ n) x = f x :=
begin
  induction n with n hn,
  { simp },
  { cases hn;
    simp [pow_succ, hn, hffx] }
end

lemma gpow_apply_eq_of_apply_apply_eq_self {f : perm α} {x : α} (hffx : f (f x) = x) (n : ℤ) :
  (f ^ n) x = x ∨ (f ^ n) x = f x :=
begin
  cases n,
  { simpa using pow_apply_eq_of_apply_apply_eq_self hffx _ },
  { cases pow_apply_eq_of_apply_apply_eq_self hffx n.succ with h h,
    { simp [apply_eq_iff_eq_symm_apply, ←inv_def, h] },
    { replace h := congr_arg f h,
      rw [hffx, ←mul_apply, ←pow_succ, pow_succ', mul_apply] at h,
      simp [apply_eq_iff_eq_symm_apply, inv_def, h] } }
end

section finite

variables {f : perm α} (hf : f.support.finite)
include hf

@[simp]
lemma card_support_eq_zero :
  hf.to_finset.card = 0 ↔ f = 1 :=
by simp

lemma one_lt_card_support_of_ne_one (h : f ≠ 1) :
  1 < hf.to_finset.card :=
begin
  simp_rw [finset.one_lt_card_iff, finite.mem_to_finset, mem_support, ←not_or_distrib],
  contrapose! h,
  ext a,
  specialize h (f a) a,
  rwa [apply_eq_iff_eq, or_self, or_self] at h,
end

lemma card_support_ne_one : hf.to_finset.card ≠ 1 :=
begin
  by_cases h : f = 1,
  { exact ne_of_eq_of_ne ((card_support_eq_zero hf).mpr h) zero_ne_one },
  { exact ne_of_gt (one_lt_card_support_of_ne_one hf h) }
end

@[simp] lemma card_support_le_one : hf.to_finset.card ≤ 1 ↔ f = 1 :=
begin
  rw [le_iff_lt_or_eq, nat.lt_succ_iff, nat.le_zero_iff, card_support_eq_zero,
      or_iff_not_imp_right, imp_iff_right],
  exact card_support_ne_one hf
end

lemma two_le_card_support_of_ne_one (h : f ≠ 1) :
  2 ≤ hf.to_finset.card :=
one_lt_card_support_of_ne_one hf h

lemma card_support_swap_mul [decidable_eq α] {x : α} (h : finite ((swap x (f x) * f).support))
  (hx : f x ≠ x) : h.to_finset.card < hf.to_finset.card :=
begin
  apply finset.card_lt_card,
  split,
  { intros z hz,
    rw finite.mem_to_finset at hz ⊢,
    exact (mem_support_swap_mul_imp_mem_support_ne hz).left },
  { rw ←mem_support at hx,
    have : x ∉ (swap x (f x) * f).support := by simp,
    rw finite.to_finset_mono,
    exact λ H, this (H hx) }
end

lemma support_extend_domain_finite {β : Type*} {p : β → Prop} [decidable_pred p]
  (g : α ≃ subtype p) :
  (f.extend_domain g).support.finite :=
by simpa using hf.image _

omit hf

lemma support_swap_finite [decidable_eq α] (x y : α) : finite (swap x y).support :=
begin
  by_cases h : x = y,
  { simp [h] },
  { simp [support_swap h] }
end

lemma card_support_swap [decidable_eq α] {x y : α} (hxy : x ≠ y) :
  (support_swap_finite x y).to_finset.card = 2 :=
begin
  letI := (support_swap_finite x y).fintype,
  simp_rw [finite.card_to_finset, ←to_finset_card, support_swap hxy],
  convert congr_arg finset.card (@set.insert_to_finset _ _ x {y} _),
  rw finset.card_insert_of_not_mem;
  simp [hxy]
end

lemma card_support_extend_domain {p : β → Prop} [decidable_pred p]
  (f : α ≃ subtype p) {g : perm α} (hg : g.support.finite) :
  (support_extend_domain_finite hg f).to_finset.card = hg.to_finset.card :=
begin
  letI := hg.fintype,
  letI := (support_extend_domain_finite hg f).fintype,
  simp_rw [finite.card_to_finset, ←to_finset_card, support_extend_domain,
           set.to_finset_image_embedding],
  simp
end

end finite

instance [decidable_eq α] {f : perm α} : decidable_pred f.support :=
set.decidable_set_of (λ (a : α), a ∉ function.fixed_points ⇑f)

instance [fintype α] [decidable_eq α] {f : perm α} : fintype f.support := set_fintype _

end support

section disjoint

/-- Two permutations `f` and `g` are `disjoint` if their supports are disjoint, i.e.,
every element is fixed either by `f`, or by `g`. -/
def disjoint (f g : perm α) := disjoint f.support g.support

variables {f g : perm α}

lemma disjoint_iff_disjoint_support :
  disjoint f g ↔ _root_.disjoint f.support g.support := iff.rfl

lemma disjoint.def (h : disjoint f g) : ∀ (x : α), f x = x ∨ g x = x :=
begin
  intro x,
  contrapose! h,
  rw [←mem_support, ←mem_support] at h,
  exact λ H, H h
end

lemma disjoint_iff_eq_or_eq : disjoint f g ↔ ∀ (x : α), f x = x ∨ g x = x :=
begin
  refine ⟨disjoint.def, λ h x, _⟩,
  cases h x with hx hx;
  simp [hx]
end

@[symm] lemma disjoint.symm {f g : perm α} (h : disjoint f g) : disjoint g f :=
begin
  rw disjoint_iff_disjoint_support at h ⊢,
  exact h.symm
end

lemma disjoint_comm {f g : perm α} : disjoint f g ↔ disjoint g f :=
⟨disjoint.symm, disjoint.symm⟩

lemma disjoint.mul_comm {f g : perm α} (h : disjoint f g) : f * g = g * f :=
equiv.ext $ λ x, (h.def x).elim
  (λ hf, (h.def (g x)).elim (λ hg, by simp [mul_apply, hf, hg])
    (λ hg, by simp [mul_apply, hf, g.injective hg]))
  (λ hg, (h.def (f x)).elim (λ hf, by simp [mul_apply, f.injective hf, hg])
    (λ hf, by simp [mul_apply, hf, hg]))

@[simp] lemma disjoint_one_left (f : perm α) : disjoint 1 f :=
by simp [disjoint_iff_eq_or_eq]

@[simp] lemma disjoint_one_right (f : perm α) : disjoint f 1 :=
by simp [disjoint_iff_eq_or_eq]

@[simp] lemma disjoint_refl_iff {f : perm α} : disjoint f f ↔ f = 1 :=
begin
  refine ⟨λ h, _, λ h, h.symm ▸ disjoint_one_left 1⟩,
  ext x,
  cases h.def x with hx hx;
  simp [hx]
end

lemma disjoint.mul_left {f g h : perm α} (H1 : disjoint f h) (H2 : disjoint g h) :
  disjoint (f * g) h :=
begin
  rw disjoint_iff_eq_or_eq at H1 H2 ⊢,
  intro x,
  cases H1 x;
  cases H2 x;
  simp *
end

lemma disjoint.mul_right {f g h : perm α} (H1 : disjoint f g) (H2 : disjoint f h) :
  disjoint f (g * h) :=
by { rw disjoint_comm, exact H1.symm.mul_left H2.symm }

lemma disjoint_prod_right (l : list (perm α))
  (h : ∀ g ∈ l, disjoint f g) : disjoint f l.prod :=
begin
  induction l with g l ih,
  { exact disjoint_one_right _ },
  { rw list.prod_cons,
    exact (h _ (list.mem_cons_self _ _)).mul_right (ih (λ g hg, h g (list.mem_cons_of_mem _ hg))) }
end

lemma disjoint_prod_perm {l₁ l₂ : list (perm α)} (hl : l₁.pairwise disjoint)
  (hp : l₁ ~ l₂) : l₁.prod = l₂.prod :=
hp.prod_eq' $ hl.imp $ λ f g, disjoint.mul_comm

lemma disjoint.disjoint_support (h : disjoint f g) :
  _root_.disjoint f.support g.support :=
disjoint_iff_disjoint_support.1 h

lemma disjoint.support_mul (h : disjoint f g) :
  (f * g).support = f.support ∪ g.support :=
begin
  refine le_antisymm (support_mul_le _ _) (λ a, _),
  rw [mem_union, mem_support, mem_support, mem_support, mul_apply, ←not_and_distrib, not_imp_not],
  exact (h.def a).elim (λ hf h, ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩)
    (λ hg h, ⟨(congr_arg f hg).symm.trans h, hg⟩),
end

lemma disjoint.inv_left (h : disjoint f g) : disjoint f⁻¹ g :=
by simpa [disjoint_iff_disjoint_support]

lemma disjoint.inv_right (h : disjoint f g) : disjoint f g⁻¹ :=
h.symm.inv_left.symm

@[simp] lemma disjoint_inv_left_iff : disjoint f⁻¹ g ↔  disjoint f g :=
begin
  refine ⟨λ h, _, disjoint.inv_left⟩,
  convert h.inv_left,
  exact (inv_inv _).symm
end

@[simp] lemma disjoint_inv_right_iff : disjoint f g⁻¹ ↔ disjoint f g :=
by rw [disjoint_comm, disjoint_inv_left_iff, disjoint_comm]

lemma support_prod_of_pairwise_disjoint (l : list (perm α)) (h : l.pairwise disjoint) :
  l.prod.support = (l.map support).foldr (⊔) ⊥ :=
begin
  induction l with hd tl hl,
  { simp },
  { rw [list.pairwise_cons] at h,
    have : disjoint hd tl.prod := disjoint_prod_right _ h.left,
    simp [this.support_mul, hl h.right] }
end

lemma disjoint.card_support_mul (h : disjoint f g) (hf : f.support.finite) (hg : g.support.finite)
  (hfg : (f * g).support.finite) :
  hfg.to_finset.card = hf.to_finset.card + hg.to_finset.card :=
begin
  letI := hf.fintype,
  letI := hg.fintype,
  letI := hfg.fintype,
  simp_rw [finite.card_to_finset, ←to_finset_card],
  classical,
  rw ←finset.card_disjoint_union,
  { congr,
    ext,
    simp [h.support_mul] },
  { simpa using h.disjoint_support }
end

lemma card_support_prod_list_of_pairwise_disjoint {l : list (perm α)} (hf : l.prod.support.finite)
  (hl : ∀ (s : set α), s ∈ (l.map support) → s.finite)
  (h : l.pairwise disjoint) :
  hf.to_finset.card =
  list.sum (list.map finset.card (list.pmap (λ (s : set α) (hs : s.finite),
    hs.to_finset) (l.map support) hl)) :=
begin
  unfreezingI
  { induction l with a t ih,
    { simp },
    { obtain ⟨ha, ht⟩ := list.pairwise_cons.1 h,
      have hd : a.disjoint t.prod := disjoint_prod_right t ha,
      have htf : t.prod.support.finite,
        { suffices : ((t.map support).foldr (⊔) ∅).finite,
            { exact this.subset (support_prod_le t) },
          apply list.foldr_rec_on,
          { simp },
          { intros b hbf a haf,
            exact (hl a (list.mem_cons_of_mem _ haf)).sup hbf } },
      have haf : a.support.finite,
        { apply hl,
          simp },
      have hpf : (a * t.prod).support.finite :=
        set.finite.subset (haf.sup htf) (support_mul_le _ _),
      specialize ih htf (λ s hs, hl s (list.mem_cons_of_mem _ hs)) ht,
      simpa [←ih] using hd.card_support_mul _ _ _ } }
end

lemma nodup_of_pairwise_disjoint {l : list (perm α)} (h1 : (1 : perm α) ∉ l)
  (h2 : l.pairwise disjoint) : l.nodup :=
begin
  refine list.pairwise.imp_of_mem _ h2,
  rintros σ - h_mem - h_disjoint rfl,
  rw disjoint_refl_iff at h_disjoint,
  exact h1 (h_disjoint ▸ h_mem)
end

lemma disjoint.mul_apply_eq_iff {σ τ : perm α} (hστ : disjoint σ τ) {a : α} :
  (σ * τ) a = a ↔ σ a = a ∧ τ a = a :=
begin
  refine ⟨λ h, _, λ h, by rw [mul_apply, h.2, h.1]⟩,
  cases hστ.def a with hσ hτ,
  { exact ⟨hσ, σ.injective (h.trans hσ.symm)⟩ },
  { exact ⟨(congr_arg σ hτ).symm.trans h, hτ⟩ },
end

lemma disjoint.mul_eq_one_iff {σ τ : perm α} (hστ : disjoint σ τ) :
  σ * τ = 1 ↔ σ = 1 ∧ τ = 1 :=
by simp_rw [ext_iff, one_apply, hστ.mul_apply_eq_iff, forall_and_distrib]

lemma disjoint.gpow_disjoint_gpow {σ τ : perm α} (hστ : disjoint σ τ) (m n : ℤ) :
  disjoint (σ ^ m) (τ ^ n) :=
begin
  rw disjoint_iff_eq_or_eq,
  exact λ x, or.imp (λ h, gpow_apply_eq_self_of_apply_eq_self h m)
    (λ h, gpow_apply_eq_self_of_apply_eq_self h n) (hστ.def x)
end

lemma disjoint.pow_disjoint_pow {σ τ : perm α} (hστ : disjoint σ τ) (m n : ℕ) :
  disjoint (σ ^ m) (τ ^ n) :=
begin
  rw disjoint_iff_eq_or_eq,
  exact λ x, or.imp (λ h, pow_apply_eq_self_of_apply_eq_self h m)
    (λ h, pow_apply_eq_self_of_apply_eq_self h n) (hστ.def x)
end

lemma disjoint.extend_domain {α β : Type*} {p : β → Prop} [decidable_pred p]
  (f : α ≃ subtype p) {σ τ : perm α} (h : disjoint σ τ) :
  disjoint (σ.extend_domain f) (τ.extend_domain f) :=
begin
  rw disjoint_iff_eq_or_eq,
  intro b,
  by_cases pb : p b,
  { refine (h.def (f.symm ⟨b, pb⟩)).imp _ _;
    { intro h,
      rw [extend_domain_apply_subtype _ _ pb, h, apply_symm_apply, subtype.coe_mk] } },
  { left,
    rw [extend_domain_apply_not_subtype _ _ pb] }
end

end disjoint

end equiv.perm
