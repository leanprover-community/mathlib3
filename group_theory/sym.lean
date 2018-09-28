/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import data.fintype data.fin group_theory.subgroup

variable (n : ℕ)

def Sym : Type :=
equiv.perm (fin n)

instance : has_coe_to_fun (Sym n) :=
equiv.has_coe_to_fun

@[extensionality] theorem Sym.ext (σ τ : Sym n)
  (H : ∀ i, σ i = τ i) : σ = τ :=
equiv.ext _ _ H

theorem Sym.ext_iff (σ τ : Sym n) :
  σ = τ ↔ ∀ i, σ i = τ i :=
⟨λ H i, H ▸ rfl, Sym.ext _ _ _⟩

instance : decidable_eq (Sym n) :=
λ σ τ, decidable_of_iff' _ (Sym.ext_iff _ _ _)

instance : group (Sym n) :=
equiv.perm.perm_group

variable {n}

section perm

def Sym.to_list (σ : Sym n) : list (fin n) :=
list.of_fn σ

theorem Sym.to_list_perm (σ : Sym n) :
  σ.to_list ~ list.of_fn (1 : Sym n) :=
(list.perm_ext
  (list.nodup_of_fn $ σ.bijective.1)
  (list.nodup_of_fn $ (1 : Sym n).bijective.1)).2 $ λ f,
by rw [list.of_fn_eq_pmap, list.of_fn_eq_pmap, list.mem_pmap, list.mem_pmap]; from
⟨λ _, ⟨f.1, by simp [f.2], fin.eq_of_veq rfl⟩,
λ _, ⟨(σ⁻¹ f).1, by simp [(σ⁻¹ f).2], by convert equiv.apply_inverse_apply σ f;
  from congr_arg _ (fin.eq_of_veq rfl)⟩⟩

def list.to_sym (L : list (fin n))
  (HL : L ~ list.of_fn (1 : Sym n)) : Sym n :=
{ to_fun := λ f, list.nth_le L f.1 $
    by rw [list.perm_length HL, list.length_of_fn]; from f.2,
  inv_fun := λ f, ⟨list.index_of f L,
    begin
      convert list.index_of_lt_length.2 _,
      { rw [list.perm_length HL, list.length_of_fn] },
      { rw [list.mem_of_perm HL, list.mem_iff_nth_le],
        refine ⟨f.1, _, _⟩,
        { rw list.length_of_fn,
          exact f.2 },
        { apply list.nth_le_of_fn } }
    end⟩,
  left_inv := λ f, fin.eq_of_veq $ list.nth_le_index_of
    ((list.perm_nodup HL).2 $ list.nodup_of_fn $ λ _ _, id) _ _,
  right_inv := λ f, list.index_of_nth_le $ list.index_of_lt_length.2 $
    (list.mem_of_perm HL).2 $ list.mem_iff_nth_le.2 $
    ⟨f.1, by rw list.length_of_fn; from f.2,
      list.nth_le_of_fn _ _⟩ }

@[simp] lemma list.to_sym_apply (L : list (fin n))
  (HL : L ~ list.of_fn (1 : Sym n)) (i) :
  (L.to_sym HL) i = L.nth_le i.1 (by simp [list.perm_length HL, i.2]) :=
rfl

@[simp] lemma Sym.to_list_to_sym (σ : Sym n) :
  σ.to_list.to_sym σ.to_list_perm = σ :=
Sym.ext _ _ _ $ λ i, fin.eq_of_veq $ by simp [Sym.to_list]

end perm

namespace Sym

def equiv_0 : Sym 0 ≃ fin (0:ℕ).fact :=
{ to_fun    := λ _, ⟨0, dec_trivial⟩,
  inv_fun   := λ _, 1,
  left_inv  := λ _, ext _ _ _ $ λ ⟨n, H⟩, by cases H,
  right_inv := λ ⟨n, H⟩, fin.eq_of_veq $
    by cases H with H1 H1; [refl, cases H1] }

def descend (σ : Sym (n+1)) : Sym n :=
{ to_fun    := λ i, (σ 0).descend (σ i.succ)
    (λ H, by cases i; from nat.no_confusion
      (fin.veq_of_eq (σ.bijective.1 H))),
  inv_fun   := λ i, (σ.symm ((σ 0).ascend i)).pred $ λ H,
    fin.ascend_ne (σ 0) i $ by simpa using H,
  left_inv  := λ i, fin.eq_of_veq $ by dsimp; rw [fin.pred_val];
    apply nat.pred_eq_of_eq_succ; rw [← fin.succ_val];
    apply fin.veq_of_eq; simp,
  right_inv := λ i, fin.eq_of_veq $ by simp }

def ascend (σ : Sym n) (k : fin (n+1)) : Sym (n+1) :=
{ to_fun    := λ i, if H : i = 0 then k
    else k.ascend $ σ $ i.pred H,
  inv_fun   := λ i, if H : i = k then 0
    else (σ.symm $ k.descend i H).succ,
  left_inv  := λ i, fin.eq_of_veq $ begin
      dsimp,
      by_cases h1 : i = 0,
      { simp [h1] },
      { rw [dif_neg h1],
        rw [dif_neg (fin.ascend_ne k (σ (i.pred h1)))],
        simp }
    end,
  right_inv := λ i, fin.eq_of_veq $ begin
      dsimp,
      by_cases h1 : i = k,
      { simp [h1] },
      { rw [dif_neg h1, dif_neg], { simp },
        intro H,
        replace H := fin.veq_of_eq H,
        simp at H,
        exact nat.no_confusion H }
    end }

@[simp] lemma descend_ascend (σ : Sym n) (k : fin (n+1)) :
  descend (ascend σ k) = σ :=
begin
  ext i,
  dsimp [ascend, descend],
  have H : i.succ ≠ 0,
  { intro H,
    replace H := fin.veq_of_eq H,
    simp at H, injections },
  simp [H]
end

def equiv_succ (ih : Sym n ≃ fin n.fact) :
  Sym (n+1) ≃ (fin (n+1) × fin n.fact) :=
{ to_fun    := λ σ, (σ 0, ih $ descend σ),
  inv_fun   := λ F, ascend (ih.symm F.2) F.1,
  left_inv  := λ σ, ext _ _ _ $ λ i, begin
    dsimp, rw [equiv.inverse_apply_apply ih],
    dsimp [descend, ascend],
    split_ifs, {subst h},
    simp
  end,
  right_inv := λ F, prod.ext
      (fin.eq_of_veq $ by dsimp [ascend]; simp) $
    fin.eq_of_veq $ by simp }

protected def equiv : Sym n ≃ fin n.fact :=
nat.rec_on n equiv_0 $ λ n ih,
calc  Sym (n+1)
    ≃ (fin (n+1) × fin n.fact) : equiv_succ ih
... ≃ fin (n+1).fact : fin_prod

instance : fintype (Sym n) :=
fintype.of_equiv _ Sym.equiv.symm

theorem card : fintype.card (Sym n) = nat.fact n :=
(fintype.of_equiv_card Sym.equiv.symm).trans $
fintype.card_fin _

theorem Cayley (α : Type*) [group α] [fintype α] :
  ∃ f : α → Sym (fintype.card α), function.injective f ∧ is_group_hom f :=
nonempty.rec_on (fintype.card_eq.1 $ fintype.card_fin $ fintype.card α) $ λ φ,
⟨λ x, ⟨λ i, φ.symm (x * φ i), λ i, φ.symm (x⁻¹ * φ i),
  λ i, by simp, λ i, by simp⟩,
λ x y H, have H1 : _ := congr_fun (equiv.mk.inj H).1 (φ.symm 1), by simpa using H1,
⟨λ x y, ext _ _ _ $ λ i, by simp [mul_assoc]⟩⟩


@[simp] lemma mul_apply (σ τ : Sym n) (i : fin n) :
  (σ * τ) i = σ (τ i) :=
rfl

@[simp] lemma one_apply (i : fin n) :
  (1 : Sym n) i = i :=
rfl

@[simp] lemma inv_apply (σ : Sym n) (i : fin n) :
  σ⁻¹ i = σ.symm i :=
rfl

def swap (i j : fin n) : Sym n :=
{ to_fun    := λ k, if k = i then j
    else if k = j then i else k,
  inv_fun   := λ k, if k = i then j
    else if k = j then i else k,
  left_inv  := λ k, by dsimp; split_ifs; cc,
  right_inv := λ k, by dsimp; split_ifs; cc }

@[simp] lemma swap_left (i j : fin n) :
  swap i j i = j :=
by dsimp [swap]; cc

@[simp] lemma swap_right (i j : fin n) :
  swap i j j = i :=
by dsimp [swap]; split_ifs; cc

@[simp] lemma swap_mul_self (i j : fin n) :
  swap i j * swap i j = 1 :=
ext _ _ _ $ λ k, by dsimp [swap]; split_ifs; cc

theorem swap_comm (i j : fin n) :
  swap i j = swap j i :=
ext _ _ _ $ λ k, by dsimp [swap]; split_ifs; cc

theorem swap_canonical (i j : fin n)
  (H1 H2 : ({i, j} : finset (fin n)) ≠ ∅) :
  swap (finset.min' _ H1) (finset.max' _ H2) = swap i j :=
begin
  have H3 := finset.min'_mem _ H1,
  have H4 : finset.min' _ H1 = j ∨ finset.min' _ H1 = i,
  { simpa using H3 },
  have H5 := finset.max'_mem _ H2,
  have H6 : finset.max' _ H2 = j ∨ finset.max' _ H2 = i,
  { simpa using H5 },
  cases H4; cases H6,
  { rw [H4, H6],
    have H7 := finset.min'_le _ H1 i (by simp),
    have H8 := finset.le_max' _ H2 i (by simp),
    rw H4 at H7, rw H6 at H8,
    have H9 := le_antisymm H7 H8,
    subst H9 },
  { rw [H4, H6, swap_comm] },
  { rw [H4, H6] },
  { rw [H4, H6],
    have H7 := finset.min'_le _ H1 j (by simp),
    have H8 := finset.le_max' _ H2 j (by simp),
    rw H4 at H7, rw H6 at H8,
    have H9 := le_antisymm H7 H8,
    subst H9 }
end

@[simp] theorem swap_self (i : fin n) :
  swap i i = 1 :=
ext _ _ _ $ λ k, by dsimp [swap]; split_ifs; cc

def support (σ : Sym n) : finset (fin n) :=
finset.filter (λ i, σ i ≠ i) finset.univ

theorem support_def {σ : Sym n} {i : fin n} :
  i ∈ σ.support ↔ σ i ≠ i :=
⟨λ H, (finset.mem_filter.1 H).2, λ H, finset.mem_filter.2 ⟨finset.mem_univ _, H⟩⟩

def support_choice (σ : Sym n) (H : σ.support ≠ ∅) :
  { i // i ∈ σ.support } :=
⟨σ.support.min' H, finset.min'_mem _ _⟩

theorem support_swap {i j : fin n} (H : i ≠ j) :
  (swap i j).support = {i, j} :=
begin
  ext k, split,
  { intro H1,
    simp [support_def, swap] at H1,
    split_ifs at H1 with h1 h2 h3 h4,
    { subst h1, simp },
    { subst h2, simp },
    cc },
  { intro H1,
    simp at H1,
    cases H1 with H1 H1;
    subst H1;
    simp [support_def, swap, H.symm, H] }
end

theorem support_swap_mul {σ : Sym n} {i : fin n}
  (H : i ∈ σ.support) : (swap (σ i) i * σ).support < σ.support :=
begin
  split,
  { intros j h1,
    simp [support_def, swap] at *,
    split_ifs at h1,
    { intro h2, rw ← h2 at h, subst h, cc },
    { cc },
    { cc } },
  intro H1,
  specialize H1 H,
  simp [support_def, swap] at H1,
  apply H1
end

@[simp] lemma support_one : support (1 : Sym n) = ∅ :=
finset.eq_empty_of_forall_not_mem $ λ i H,
support_def.1 H rfl

variable (n)
@[derive decidable_eq]
structure step : Type :=
(fst : fin n)
(snd : fin n)
(lt  : fst < snd)
variable {n}

instance step.fintype : fintype (step n) :=
@fintype.of_surjective { i : fin n × fin n // i.1 < i.2 } _ _ _
  (λ i, (⟨i.1.1, i.1.2, i.2⟩ : step n)) $ λ s,
⟨⟨(s.1, s.2), s.3⟩, by cases s; refl⟩

instance : has_mem (fin n) (step n) :=
⟨λ i s, i = s.1 ∨ i = s.2⟩

@[extensionality] theorem step.ext (s t : step n)
  (H1 : s.1 = t.1) (H2 : s.2 = t.2) : s = t :=
by cases s; cases t; congr; assumption

def step.mk' (i j : fin n) (H : i ≠ j) : step n :=
if h : i < j then ⟨i, j, h⟩ else
⟨j, i, (eq_or_lt_of_not_lt h).resolve_left H⟩

def step.eval (s : step n) : Sym n :=
swap s.1 s.2

@[simp] lemma step.eval_mul_self (s : step n) :
  s.eval * s.eval = 1 :=
by simp [step.eval]

@[simp] lemma step.eval_mk' (i j : fin n) (H : i ≠ j) :
  (step.mk' i j H).eval = swap i j :=
by unfold step.mk'; split_ifs; simp [step.eval, swap_comm]

theorem choice.aux (σ : Sym n)
  (H : ∃ i j, i ≠ j ∧ σ = swap i j) :
  σ.support ≠ ∅ :=
let ⟨i, j, h1, h2⟩ := H in by
  refine finset.ne_empty_of_mem (_ : j ∈ σ.support);
  rw [h2, support_swap h1];
  apply finset.mem_insert_self

def choice (σ : Sym n)
  (H : ∃ i j, i ≠ j ∧ σ = swap i j) : step n :=
{ fst := σ.support.min' $ choice.aux _ H,
  snd := σ.support.max' $ choice.aux _ H,
  lt  := by rcases H with ⟨i, j, h1, h2⟩; subst h2; dsimp;
    refine finset.min'_lt_max' _ _ _ _ h1;
    simp [support_swap h1] }

theorem eval_choice (σ : Sym n)
  (H : ∃ i j, i ≠ j ∧ σ = swap i j) :
  (σ.choice H).eval = σ :=
begin
  rcases H with ⟨i, j, h1, h2⟩,
  subst h2, unfold step.eval choice, dsimp,
  convert swap_canonical i j _ _;
  simp [support_swap h1]
end

theorem choice_eval (s : step n)
  (H : ∃ i j, i ≠ j ∧ s.eval = swap i j) :
  s.eval.choice H = s :=
begin
  ext; dsimp [step.eval, choice],
  { apply le_antisymm,
    { apply finset.min'_le,
      simp [support_swap (ne_of_lt s.3)] },
    { apply finset.le_min',
      intros y h1,
      simp [support_swap (ne_of_lt s.3)] at h1,
      cases h1; subst h1,
      apply le_of_lt s.3 } },
  { apply le_antisymm,
    { apply finset.max'_le,
      intros y h1,
      simp [support_swap (ne_of_lt s.3)] at h1,
      cases h1; subst h1,
      apply le_of_lt s.3 },
    { apply finset.le_max',
      simp [support_swap (ne_of_lt s.3)] } }
end

def list_step.aux : has_well_founded (Sym n) :=
{ r := inv_image (<) support,
  wf := inv_image.wf _ finset.lt_wf }

local attribute [instance] list_step.aux
attribute [elab_as_eliminator] well_founded.fix
attribute [elab_as_eliminator] well_founded.induction

def list_step (σ : Sym n) : list (step n) :=
by refine well_founded.fix list_step.aux.wf _ σ; from
λ σ ih, if H : σ.support = ∅ then []
  else let ⟨i, hi⟩ := σ.support_choice H in
    step.mk' (σ i) i (support_def.1 hi)
    :: ih (swap (σ i) i * σ) (support_swap_mul hi)

@[simp] lemma list_step_prod (σ : Sym n) :
  (σ.list_step.map step.eval).prod = σ :=
well_founded.induction list_step.aux.wf σ $ λ σ ih,
begin
  dsimp [list_step],
  rw [well_founded.fix_eq],
  split_ifs,
  { ext, by_contra H,
    suffices : i ∈ (∅ : finset (fin n)),
    { simp at this, cc },
    rw [← h, support_def],
    exact mt eq.symm H },
  cases support_choice σ h with i hi,
  unfold list_step._match_1,
  specialize ih _ (support_swap_mul hi),
  dsimp [list_step] at ih,
  rw [list.map_cons, list.prod_cons, ih, ← mul_assoc],
  rw [step.eval_mk', swap_mul_self, one_mul]
end

theorem mem_step_iff_mem_support (s : step n) (i : fin n) :
  i ∈ s ↔ i ∈ s.eval.support :=
begin
  unfold step.eval,
  simp [support_swap (ne_of_lt s.3)],
  rw [or_comm], refl
end

theorem support_eq_of_mul_eq_one {σ τ : Sym n} (H : σ * τ = 1) :
  σ.support = τ.support :=
begin
  ext i, simp [support_def, not_iff_not],
  rw [eq_comm, iff.comm],
  convert equiv.symm_apply_eq,
  symmetry,
  rw [equiv.symm_apply_eq, ← mul_apply, H, one_apply],
end

theorem of_mem_mul_support {σ τ : Sym n} {i}
  (H : i ∈ (σ * τ).support) :
  i ∈ σ.support ∨ i ∈ τ.support :=
by_contradiction $ λ H2,
by simp [support_def, not_or_distrib] at H H2;
simp [H2] at H; cc

theorem of_not_mem_mul_support {σ τ : Sym n} {i}
  (H : i ∉ (σ * τ).support) :
  i ∈ σ.support ↔ i ∈ τ.support :=
begin
  simp [support_def] at H ⊢,
  split,
  { intros H2 H3, rw H3 at H, cc },
  { intros H2 H3, rw ← H3 at H,
    replace H := σ.bijective.1 H,
    rw H3 at H, cc }
end

theorem not_mem_mul_support {σ τ : Sym n} {i}
  (H1 : i ∉ σ.support) (H2 : i ∉ τ.support) :
  i ∉ (σ * τ).support :=
begin
  simp [support_def] at H1 H2 ⊢,
  rw [H2, H1]
end

@[simp] lemma mem_mk' {i j k : fin n} (H : i ≠ j) :
  k ∈ step.mk' i j H ↔ k = i ∨ k = j :=
begin
  unfold step.mk',
  split_ifs,
  { refl },
  { apply or_comm }
end

-- (ab)(cd) = (cd)(ab)
theorem sgn_aux5 (s t : step n)
  (H1 : s.1 ≠ t.1) (H2 : s.1 ≠ t.2)
  (H3 : s.2 ≠ t.1) (H4 : s.2 ≠ t.2) :
  s.eval * t.eval = t.eval * s.eval :=
begin
  have := ne_of_lt s.3,
  have := ne_of_lt t.3,
  dsimp [step.eval, swap], ext k,
  dsimp at *,
  split_ifs; cc
end

-- (ab)(ac) = (bc)(ab)
theorem sgn_aux4a (s t : step n)
  (H1 : s.1 = t.1) (H4 : s.2 ≠ t.2) :
  s.eval * t.eval = (step.mk' s.2 t.2 H4).eval * s.eval :=
begin
  have := ne_of_lt s.3,
  have := ne_of_lt t.3,
  unfold step.eval step.mk',
  simp [swap], ext k,
  dsimp at *,
  split_ifs; cc
end

-- (ab)(ca) = (cb)(ab)
theorem sgn_aux4b (s t : step n) (H1 : s.1 = t.2)
  (H2 : t.1 < s.2) :
  s.eval * t.eval = (⟨t.1, s.2, H2⟩ : step n).eval * s.eval :=
begin
  have := ne_of_lt s.3,
  have := ne_of_lt t.3,
  have := ne_of_lt H2,
  dsimp [step.eval, swap], ext k,
  dsimp at *,
  split_ifs; cc
end

-- (ab)(ac) = (ac)(bc)
theorem sgn_aux4c (s t : step n)
  (H1 : s.1 = t.1) (H4 : s.2 ≠ t.2) :
  s.eval * t.eval = t.eval * (step.mk' s.2 t.2 H4).eval :=
begin
  have := ne_of_lt s.3,
  have := ne_of_lt t.3,
  unfold step.eval step.mk',
  simp [swap], ext k,
  dsimp at *,
  split_ifs; cc
end

-- (ab)(ca) = (ca)(cb)
theorem sgn_aux4d (s t : step n)
  (H1 : s.1 = t.2) (H4 : t.1 < s.2) :
  s.eval * t.eval = t.eval * (⟨t.1, s.2, H4⟩ : step n).eval :=
begin
  have := ne_of_lt s.3,
  have := ne_of_lt t.3,
  have := ne_of_lt H4,
  simp [step.eval, swap], ext k,
  dsimp at *,
  split_ifs; cc
end

-- (ab)(bc) = (bc)(ac)
theorem sgn_aux3a (s t : step n) (H1 : s.2 = t.1)
  (H2 : s.1 < t.2) :
  s.eval * t.eval = t.eval * (⟨s.1, t.2, H2⟩ : step n).eval :=
begin
  have := ne_of_lt s.3,
  have := ne_of_lt t.3,
  have := ne_of_lt H2,
  dsimp [step.eval, swap], ext k,
  dsimp at *,
  split_ifs; cc
end

-- (ab)(cb) = (cb)(ac)
theorem sgn_aux3b (s t : step n) (H1 : s.2 = t.2)
  (H2 : s.1 ≠ t.1) :
  s.eval * t.eval = t.eval * (step.mk' s.1 t.1 H2).eval :=
begin
  have := ne_of_lt s.3,
  have := ne_of_lt t.3,
  unfold step.eval step.mk',
  simp [swap], ext k,
  dsimp at *,
  split_ifs; cc
end

-- (ab)(bc) = (ac)(ab)
theorem sgn_aux3c (s t : step n) (H1 : s.2 = t.1)
  (H2 : s.1 < t.2) :
  s.eval * t.eval = (⟨s.1, t.2, H2⟩ : step n).eval * s.eval :=
begin
  have := ne_of_lt s.3,
  have := ne_of_lt t.3,
  have := ne_of_lt H2,
  dsimp [step.eval, swap], ext k,
  dsimp at *,
  split_ifs; cc
end

-- (ab)(cb) = (ac)(ab)
theorem sgn_aux3d (s t : step n) (H1 : s.2 = t.2)
  (H2 : s.1 ≠ t.1) :
  s.eval * t.eval = (step.mk' s.1 t.1 H2).eval * s.eval :=
begin
  have := ne_of_lt s.3,
  have := ne_of_lt t.3,
  unfold step.eval step.mk',
  simp [swap], ext k,
  dsimp at *,
  split_ifs; cc
end

theorem sgn_aux2 (s t : step n) (i) (H : i ∈ s) :
  s = t ∨ ∃ s' t' : step n, s.eval * t.eval = s'.eval * t'.eval
    ∧ i ∉ s' ∧ i ∈ t' :=
begin
  cases H with H H; subst H,
  { by_cases H2 : s.1 = t.1,
    { by_cases H3 : s.2 = t.2,
      { left, ext; assumption },
      right, -- (ab)(ac) = (bc)(ab)
      refine ⟨step.mk' s.2 t.2 H3, s, _, _⟩,
      { exact sgn_aux4a _ _ H2 _ },
      rw [mem_mk'],
      exact ⟨λ H, or.cases_on H
        (ne_of_lt s.3) (H2.symm ▸ (ne_of_lt t.3)),
      or.inl rfl⟩ },
    right,
    by_cases H3 : s.1 = t.2,
    { -- (ab)(ca) = (cb)(ab)
      have H4 : t.1 < s.2 := lt_trans t.3 (H3 ▸ s.3),
      refine ⟨⟨t.1, s.2, H4⟩, s, _, _⟩,
      { exact sgn_aux4b _ _ H3 _ },
      exact ⟨λ H, or.cases_on H
        H2 (ne_of_lt s.3),
      or.inl rfl⟩ },
    by_cases H4 : s.2 = t.1,
    { -- (ab)(bc) = (bc)(ac)
      have H5 : s.1 < t.2 := lt_trans s.3 (H4.symm ▸ t.3),
      refine ⟨t, ⟨s.1, t.2, H5⟩, _, _⟩,
      { exact sgn_aux3a _ _ H4 _ },
      exact ⟨λ H, or.cases_on H
        H2 (ne_of_lt H5),
      or.inl rfl⟩ },
    by_cases H5 : s.2 = t.2,
    { -- (ab)(cb) = (cb)(ac)
      refine ⟨t, step.mk' s.1 t.1 H2, _, _⟩,
      { exact sgn_aux3b _ _ H5 _ },
      exact ⟨λ H, or.cases_on H
        H2 H3,
      by simp⟩ },
    -- (ab)(cd) = (cd)(ab)
    refine ⟨t, s, _, _⟩,
    { exact sgn_aux5 _ _ H2 H3 H4 H5 },
    exact ⟨λ H, or.cases_on H
      H2 H3,
    or.inl rfl⟩ },
  by_cases H2 : s.1 = t.1,
  { by_cases H3 : s.2 = t.2,
    { left, ext; assumption },
    right, -- (ab)(ac) = (ac)(bc)
    refine ⟨t, step.mk' s.2 t.2 H3, _, _⟩,
    { exact sgn_aux4c _ _ H2 _ },
    rw [mem_mk'],
    exact ⟨λ H, or.cases_on H
      (H2 ▸ ne_of_gt s.3) H3,
    or.inl rfl⟩ },
  right,
  by_cases H3 : s.1 = t.2,
  { -- (ab)(ca) = (ca)(cb)
    have H4 : t.1 < s.2 := lt_trans t.3 (H3 ▸ s.3),
    refine ⟨t, ⟨t.1, s.2, H4⟩, _, _⟩,
    { exact sgn_aux4d _ _ H3 _ },
    exact ⟨λ H, or.cases_on H
      (ne_of_gt H4) (H3 ▸ ne_of_gt s.3),
    or.inr rfl⟩ },
  by_cases H4 : s.2 = t.1,
  { -- (ab)(bc) = (ac)(ab)
    have H5 : s.1 < t.2 := lt_trans s.3 (H4.symm ▸ t.3),
    refine ⟨⟨s.1, t.2, H5⟩, s, _, _⟩,
    { exact sgn_aux3c _ _ H4 _ },
    exact ⟨λ H, or.cases_on H
      (ne_of_gt s.3) (H4.symm ▸ ne_of_lt t.3),
    or.inr rfl⟩ },
  by_cases H5 : s.2 = t.2,
  { -- (ab)(cb) = (ac)(ab)
    refine ⟨step.mk' s.1 t.1 H2, s, _, _⟩,
    { exact sgn_aux3d _ _ H5 _ },
    rw [mem_mk'],
    exact ⟨λ H, or.cases_on H
      (ne_of_gt s.3) (H5.symm ▸ ne_of_gt t.3),
    or.inr rfl⟩ },
  refine ⟨t, s, _, _⟩,
  { exact sgn_aux5 _ _ H2 H3 H4 H5 },
  exact ⟨λ H, or.cases_on H
    H4 H5,
  or.inr rfl⟩
end

theorem sgn_aux (L1 : list (step n)) (s : step n) (L2 : list (step n)) (i : fin n)
  (H1 : (L1.map step.eval).prod * s.eval * (L2.map step.eval).prod = 1)
  (H2 : i ∈ s) (H3 : i ∉ (L1.map step.eval).prod.support) :
  ∃ (L : list (step n)),
    (L.map step.eval).prod = 1
    ∧ L.length + 2 = L1.length + 1 + L2.length :=
begin
  induction L2 with hd tl ih generalizing L1 s,
  { simp at H1,
    simp [mem_step_iff_mem_support] at H2,
    rw support_eq_of_mul_eq_one H1 at H3,
    cc },
  simp [mul_assoc] at H1,
  simp [mem_step_iff_mem_support] at H2,
  have H4 := H3,
  rw [support_eq_of_mul_eq_one H1] at H4,
  replace H4 := of_not_mem_mul_support H4,
  replace H4 := H4.1 H2,
  rw [← mem_step_iff_mem_support] at H2,
  rcases sgn_aux2 s hd i H2 with H5 | ⟨s', t', H5, H6, H7⟩,
  { subst H5,
    rw [← mul_assoc s.eval, step.eval_mul_self, one_mul] at H1,
    rw [← list.prod_append, ← list.map_append] at H1,
    refine ⟨_, H1, _⟩,
    simp, unfold bit0, ac_refl },
  specialize ih (L1 ++ [s']) t' _ H7 _,
  rcases ih with ⟨L, H8, H9⟩,
  refine ⟨L, H8, _⟩,
  { simp [H9] },
  { simp at H5 ⊢,
    rw [mul_assoc (L1.map step.eval).prod, ← H5],
    simpa [mul_assoc] using H1 },
  simpa using not_mem_mul_support H3 _,
  simpa [mem_step_iff_mem_support] using H6
end

theorem length_even_of_prod_one (L : list (step n))
  (H : (L.map step.eval).prod = 1) :
  L.length % 2 = 0 :=
begin
  generalize H1 : L.length = k,
  revert L,
  apply nat.strong_induction_on k,
  intros k ih L H H1,
  cases k with k, { refl },
  cases k with k,
  { exfalso,
    rw list.length_eq_one at H1,
    cases H1 with s H2,
    subst H2,
    replace H := congr_arg support H,
    simp [step.eval, support_swap (ne_of_lt s.3)] at H,
    exact H },
  cases L with hd tl, { simp at H1, injections },
  rcases sgn_aux [] hd tl hd.1 _ (or.inl rfl) _ with ⟨L, H2, H3⟩,
  specialize ih k _ L H2 _,
  change (k + 2) % 2 = 0,
  { rw [nat.add_mod_right, ih] },
  { constructor, constructor },
  { simp at H1 H3,
    rw ← H3 at H1,
    exact nat.succ_inj (nat.succ_inj H1) },
  { simpa using H },
  simp
end

theorem length_mod_two_eq (L1 L2 : list (step n))
  (H : (L1.map step.eval).prod = (L2.map step.eval).prod) :
  L1.length % 2 = L2.length % 2 :=
have H1 : (L2.map step.eval).reverse.prod = (L2.map step.eval).prod⁻¹,
  from list.rec_on L2 (by simp) $ λ hd tl ih,
    by simp [ih, eq_inv_iff_mul_eq_one],
have H2 : _,
  from length_even_of_prod_one (L1 ++ L2.reverse) $
    by simp [H1, H],
have H3 : 2 ∣ L1.length + L2.length,
  by simpa [nat.dvd_iff_mod_eq_zero] using H2,
calc  L1.length % 2
    = (L1.length + L2.length + L2.length) % 2 :
  by rw [add_assoc, ← mul_two, nat.add_mul_mod_self_right]
... = L2.length % 2 :
  by cases H3 with k H4; rw [H4, add_comm, nat.add_mul_mod_self_left]

end Sym

@[derive decidable_eq]
inductive mu2 : Type
| plus_one : mu2
| minus_one : mu2

namespace mu2

definition neg : mu2 → mu2
| plus_one := minus_one
| minus_one := plus_one

instance : has_one mu2 := ⟨plus_one⟩
instance : has_neg mu2 := ⟨neg⟩

instance : comm_group mu2 :=
{ mul := λ x y, mu2.rec_on x (mu2.rec_on y 1 (-1)) (mu2.rec_on y (-1) 1),
  mul_assoc := λ x y z, by cases x; cases y; cases z; refl,
  mul_one := λ x, by cases x; refl,
  one_mul := λ x, by cases x; refl,
  inv := id,
  mul_left_inv := λ x, by cases x; refl,
  mul_comm := λ x y, by cases x; cases y; refl,
  .. mu2.has_one }

instance : fintype mu2 :=
{ elems := {1, -1},
  complete := λ x, mu2.cases_on x (or.inr $ or.inl rfl) (or.inl rfl) }

theorem card : fintype.card mu2 = 2 :=
rfl

theorem neg_one_pow {n} : (-1 : mu2) ^ n = (-1 : mu2) ^ (n%2) :=
have H : (-1 : mu2) ^ 2 = 1, from rfl,
by rw [← nat.mod_add_div n 2, pow_add, pow_mul, H, one_pow, mul_one, nat.mod_add_div n 2]

@[simp] lemma mul_self_eq_one (x : mu2) : x * x = 1 :=
by cases x; refl

@[simp] lemma inv_eq_self (x : mu2) : x⁻¹ = x :=
rfl

@[simp] protected lemma mul_neg_one (x : mu2) : x * -1 = -x :=
by cases x; refl

@[simp] protected lemma neg_one_mul (x : mu2) : -1 * x = -x :=
by cases x; refl

@[simp] lemma neg_mul_self (x : mu2) : -x * x = -1 :=
by cases x; refl

@[simp] lemma mul_neg (x y : mu2) : x * -y = -x * y :=
by cases x; cases y; refl

end mu2

namespace Sym

def sgn (σ : Sym n) : mu2 :=
(-1) ^ σ.list_step.length

instance sgn.is_group_hom : is_group_hom (@sgn n) :=
begin
  constructor,
  intros σ τ,
  unfold sgn,
  rw [← pow_add, ← list.length_append],
  rw [mu2.neg_one_pow, eq_comm, mu2.neg_one_pow],
  refine congr_arg _ _,
  apply length_mod_two_eq,
  simp
end

@[simp] lemma sgn_step (s : step n) :
  sgn s.eval = -1 :=
suffices s.eval.list_step.length % 2 = [s].length % 2,
  by unfold sgn; rw [mu2.neg_one_pow, this]; refl,
length_mod_two_eq _ _ $ by simp

@[simp] lemma sgn_mul (σ τ : Sym n) :
  sgn (σ * τ) = sgn σ * sgn τ :=
is_group_hom.mul sgn _ _

@[simp] lemma sgn_one :
  sgn (1 : Sym n) = 1 :=
is_group_hom.one sgn

@[simp] lemma sgn_inv (σ : Sym n) :
  sgn σ⁻¹ = sgn σ :=
is_group_hom.inv sgn _

def eq_sgn_aux4 (s t : step n) : Sym n :=
swap (swap s.1 t.1 s.2) t.2 * swap s.1 t.1

theorem eq_sgn_aux3 (s t : step n) :
  eq_sgn_aux4 s t s.1 = t.1 :=
begin
  dsimp [eq_sgn_aux4, swap],
  have := ne_of_lt s.3,
  have := ne_of_lt t.3,
  simp, split_ifs; cc
end

theorem eq_sgn_aux2 (s t : step n) :
  eq_sgn_aux4 s t s.2 = t.2 :=
begin
  dsimp [eq_sgn_aux4, swap],
  simp
end

theorem eq_sgn_aux (s t : step n) :
  eq_sgn_aux4 s t * s.eval * (eq_sgn_aux4 s t)⁻¹ = t.eval :=
begin
  ext k,
  by_cases H1 : k = t.1,
  { subst H1,
    dsimp [step.eval],
    simp [equiv.symm_apply_eq.2 (eq_sgn_aux3 s t).symm, eq_sgn_aux2] },
  by_cases H2 : k = t.2,
  { subst H2,
    dsimp [step.eval],
    simp [equiv.symm_apply_eq.2 (eq_sgn_aux2 s t).symm, eq_sgn_aux3] },
  dsimp [step.eval, swap],
  simp [H1, H2, eq_sgn_aux2, eq_sgn_aux3]
end

theorem eq_sgn (f : Sym n → mu2) [is_group_hom f]
  (s : step n) (H1 : f s.eval = -1) (σ : Sym n) :
  f σ = sgn σ :=
begin
  have H2 : ∀ t : step n, f t.eval = -1,
  { intro t,
    rw [← eq_sgn_aux s t],
    simp [is_group_hom.mul f, is_group_hom.inv f, H1] },
  have H3 := list_step_prod σ,
  revert H3, generalize : list_step σ = L, intro H3, subst H3,
  induction L with hd tl ih, { simp [is_group_hom.one f] },
  simp [is_group_hom.mul f, ih, H2]
end

section inversions

def step.map (s : step n) (σ : Sym n) : step n :=
step.mk' (σ s.1) (σ s.2) $ λ H, ne_of_lt s.3 $
σ.bijective.1 H

@[simp] lemma step.map_map_inv (s : step n) (σ : Sym n) :
  (s.map σ).map σ⁻¹ = s :=
begin
  unfold step.map step.mk',
  by_cases H1 : σ s.1 < σ s.2,
  { rw [dif_pos H1], dsimp,
    rw dif_pos, ext; simp,
    simp [s.3] },
  rw [dif_neg H1], dsimp,
  rw dif_neg, ext; simp,
  simp [le_of_lt s.3]
end

@[simp] lemma step.map_inv_map (s : step n) (σ : Sym n) :
  (s.map σ⁻¹).map σ = s :=
by simpa using step.map_map_inv s σ⁻¹

def inversion (σ : Sym n) (s : step n) : mu2 :=
if σ s.1 > σ s.2 then -1 else 1

def inversions (σ : Sym n) : mu2 :=
finset.prod finset.univ $ inversion σ

theorem inversion_mul (σ τ : Sym n) (s : step n) :
  inversion (σ * τ) s = inversion σ (s.map τ) * inversion τ s :=
begin
  unfold inversion step.map step.mk',
  split_ifs with h1 h2 h3 h3 h4 h4 h2 h3 h3 h4 h4; try { refl },
  { exfalso, apply lt_asymm h2 h3 },
  { exfalso, apply lt_asymm h1 h3 },
  { simp at *, exfalso,
    exact ne_of_lt s.3 (τ.bijective.1 $ le_antisymm h4 h2) },
  { exfalso, apply lt_asymm h2 h3 },
  { simp at *, exfalso,
    exact ne_of_lt s.3 (τ.bijective.1 $ le_antisymm h4 h2) },
  { simp at *, exfalso,
    exact ne_of_lt s.3 (τ.bijective.1 $ σ.bijective.1 $ le_antisymm h1 h3) }
end

instance : is_group_hom (@inversions n) :=
⟨λ σ τ, calc
      inversions (σ * τ)
    = finset.prod finset.univ (inversion (σ * τ)) : rfl
... = finset.prod finset.univ (λ s : step n,
        inversion σ (s.map τ) * inversion τ s) :
  congr_arg _ $ funext $ inversion_mul σ τ
... = finset.prod finset.univ (λ s : step n,
        inversion σ (s.map τ)) * inversions τ :
  finset.prod_mul_distrib
... = finset.prod finset.univ (inversion σ) * inversions τ :
  congr_arg (λ z, z * inversions τ) $ finset.prod_bij
    (λ s _, step.map s τ) (λ _ _, finset.mem_univ _) (λ _ _, rfl)
    (λ s t _ _ H, by simpa using congr_arg (λ z, step.map z τ⁻¹) H)
    (λ s _, ⟨s.map τ⁻¹, finset.mem_univ _, by simp⟩)⟩

variable (n)
def step01 : step (n+2) :=
⟨⟨0, nat.zero_lt_succ _⟩, ⟨1, nat.succ_lt_succ $ nat.zero_lt_succ _⟩, dec_trivial⟩
variable {n}

theorem inversions_step01 : inversions (step01 n).eval = -1 :=
show _ = finset.prod {step01 n} (inversion (step01 n).eval), from
eq.symm $ finset.prod_subset (finset.subset_univ _) $ λ s _ H1, begin
  unfold inversion step.eval swap step01; dsimp at *, rw if_neg,
  by_cases H2 : s.1.1 = 0,
  { rw [if_pos, if_neg, if_neg],
    { intro H3,
      replace H3 := nat.le_of_lt_succ H3,
      replace H3 := nat.eq_zero_of_le_zero H3,
      exact ne_of_lt s.3 (fin.eq_of_veq $ H2.trans H3.symm) },
    { intro H3, apply H1, simp, ext, exact fin.eq_of_veq H2, exact H3 },
    { exact ne_of_gt (H2 ▸ s.3 : s.2.1 > 0), },
    { exact fin.eq_of_veq H2 } },
  by_cases H3 : s.1.1 = 1,
  { rw [if_neg, if_pos], exact nat.not_lt_zero _,
    exact fin.eq_of_veq H3, exact mt fin.veq_of_eq H2 },
  rw [if_neg, if_neg, if_neg, if_neg],
  { exact lt_asymm s.3 },
  { intro H4, have H5 := s.3, rw H4 at H5,
    replace H5 := nat.le_of_lt_succ H5,
    replace H5 := nat.eq_zero_of_le_zero H5,
    cc },
  { intro H4, have H5 := s.3, rw H4 at H5,
    cases H5 },
  { exact mt fin.veq_of_eq H3 },
  { exact mt fin.veq_of_eq H2 }
end

theorem inversions_eq_sgn : ∀ σ : Sym n, inversions σ = sgn σ :=
nat.cases_on n dec_trivial $ λ n,
nat.cases_on n dec_trivial $ λ n σ,
eq_sgn inversions (step01 n) inversions_step01 σ

end inversions

end Sym

variable (n)
def Alt : Type :=
is_group_hom.ker (@Sym.sgn n)

instance : group (Alt n) :=
by unfold Alt; apply_instance