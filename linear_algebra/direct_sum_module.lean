/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Direct sum of modules over commutative rings,
indexed by a discrete type.
-/

import linear_algebra.subtype_module
import algebra.pi_instances

universes u v w u₁

variables (R : Type u) [comm_ring R]
variables (ι : Type v) [decidable_eq ι] (β : ι → Type w)
variables [Π i, module R (β i)]
include R

protected def direct_sum.finset (s : finset ι) : Type* :=
Π i : s.to_set, β i.1

instance (s : finset ι) : module R (direct_sum.finset R ι β s) :=
pi.module

def direct_sum.finset_to_finset (s t : finset ι) :
  direct_sum.finset R ι β s → direct_sum.finset R ι β t :=
λ f i, if h : i.1 ∈ s then f ⟨i.1, h⟩ else 0

@[simp] lemma direct_sum.finset_id (s : finset ι)
  (x : direct_sum.finset R ι β s) :
  direct_sum.finset_to_finset _ _ _ s s x = x :=
funext $ λ ⟨i, hi⟩, dif_pos _

theorem direct_sum.finset_comp (s t u : finset ι)
  (x : direct_sum.finset R ι β s) (Hst : s ⊆ t) (Htu : t ⊆ u) :
  direct_sum.finset_to_finset _ _ _ t u (direct_sum.finset_to_finset _ _ _ s t x)
  = direct_sum.finset_to_finset _ _ _ s u x :=
begin
  funext i,
  cases i with i hi,
  dsimp [direct_sum.finset_to_finset],
  split_ifs;
  cc <|> solve_by_elim
end

theorem direct_sum.finset_linear (s t : finset ι) :
  is_linear_map (direct_sum.finset_to_finset R ι β s t) :=
{ add  := λ x y, by funext i; change dite _ _ _ = dite _ _ _ + dite _ _ _;
    split_ifs; [refl, simp],
  smul := λ c x, by funext i; change dite _ _ _ = c • dite _ _ _;
    split_ifs; [refl, simp] }

def direct_sum.pre : Type* :=
Σ s, direct_sum.finset R ι β s

instance direct_sum.setoid : setoid (direct_sum.pre R ι β) :=
{ r := λ f g, ∃ s, f.1 ⊆ s ∧ g.1 ⊆ s ∧
      direct_sum.finset_to_finset R ι β f.1 s f.2
    = direct_sum.finset_to_finset R ι β g.1 s g.2,
  iseqv := ⟨λ f, ⟨f.1, by simp⟩,
    λ f g ⟨s, hs1, hs2, hs3⟩, ⟨s, hs2, hs1, hs3.symm⟩,
    λ f g h ⟨s, hs1, hs2, hs3⟩ ⟨t, ht1, ht2, ht3⟩,
    ⟨s ∪ t, finset.subset.trans hs1 finset.subset_union_left,
      finset.subset.trans ht2 finset.subset_union_right,
    calc  direct_sum.finset_to_finset R ι β (f.fst) (s ∪ t) (f.snd)
        = _ : eq.symm (direct_sum.finset_comp _ _ _ _ s _ _ hs1 finset.subset_union_left)
    ... = _ : by rw hs3
    ... = _ : direct_sum.finset_comp _ _ _ g.1 s _ _ hs2 finset.subset_union_left
    ... = _ : eq.symm (direct_sum.finset_comp _ _ _ _ t _ _ ht1 finset.subset_union_right)
    ... = _ : by rw ht3
    ... = _ : direct_sum.finset_comp _ _ _ _ t _ _ ht2 finset.subset_union_right⟩⟩ }

def direct_sum : Type* :=
quotient (direct_sum.setoid R ι β)

namespace direct_sum

variables {R ι β}
def mk (s : finset ι) (f : direct_sum.finset _ _ _ s) : direct_sum R ι β :=
⟦⟨s, f⟩⟧

instance direct_sum.module : module R (direct_sum R ι β) :=
{ add := λ f g, quotient.lift_on₂ f g
    (λ x y, mk (x.1 ∪ y.1)
      (finset_to_finset _ _ _ _ _ x.2 + finset_to_finset _ _ _ _ _ y.2)) $
    begin
      rintros x1 x2 y1 y2 ⟨s, hs1, hs2, hs3⟩ ⟨t, ht1, ht2, ht3⟩,
      refine quotient.sound ⟨s ∪ t, _, _, _⟩,
      { refine finset.union_subset _ _,
        exact finset.subset.trans hs1 finset.subset_union_left,
        exact finset.subset.trans ht1 finset.subset_union_right },
      { refine finset.union_subset _ _,
        exact finset.subset.trans hs2 finset.subset_union_left,
        exact finset.subset.trans ht2 finset.subset_union_right },
      dsimp,
      rw [(finset_linear _ _ _ _ _).add, (finset_linear _ _ _ _ _).add],
      rw [finset_comp, finset_comp, finset_comp, finset_comp],
      rw [← finset_comp _ _ _ x1.1 s, hs3, finset_comp],
      rw [← finset_comp _ _ _ x2.1 t, ht3, finset_comp],
      all_goals
      { apply finset.union_subset
        <|> assumption
        <|> exact finset.subset_union_left
        <|> exact finset.subset_union_right },
      all_goals
      { apply finset.subset.trans hs1
        <|> apply finset.subset.trans hs2
        <|> apply finset.subset.trans ht1
        <|> apply finset.subset.trans ht2,
        exact finset.subset_union_left
        <|> exact finset.subset_union_right }
    end,
  zero := mk ∅ 0,
  neg := λ f, quotient.lift_on f (λ x, mk x.1 (-x.2)) $
    begin
      rintros x y ⟨s, hs1, hs2, hs3⟩,
      refine quotient.sound ⟨s, hs1, hs2, _⟩,
      dsimp,
      rw [(finset_linear _ _ _ _ _).neg, (finset_linear _ _ _ _ _).neg, hs3]
    end,
  smul := λ c f, quotient.lift_on f (λ x, mk x.1 (c • x.2)) $
    begin
      rintros x y ⟨s, hs1, hs2, hs3⟩,
      refine quotient.sound ⟨s, hs1, hs2, _⟩,
      dsimp,
      rw [(finset_linear _ _ _ _ _).smul, (finset_linear _ _ _ _ _).smul, hs3]
    end,
  add_assoc := λ f g h, quotient.induction_on₃ f g h $ λ x y z,
    quotient.sound ⟨_, finset.subset_union_left, finset.subset_union_right,
    by dsimp; repeat { rw (finset_linear _ _ _ _ _).add };
    repeat { rw finset_comp };
    { apply add_assoc
      <|> exact finset.subset_union_left
      <|> exact finset.subset_union_right
      <|> exact finset.subset.trans finset.subset_union_left finset.subset_union_left
      <|> exact finset.subset.trans finset.subset_union_right finset.subset_union_left
      <|> exact finset.subset.trans finset.subset_union_left finset.subset_union_right
      <|> exact finset.subset.trans finset.subset_union_right finset.subset_union_right }⟩,
  zero_add := λ f, quotient.induction_on f $ λ x,
    quotient.sound ⟨∅ ∪ x.1, by simp, by simp, by dsimp;
    rw [(finset_linear _ _ _ _ _).add, (finset_linear _ _ _ _ _).zero];
    rw [(finset_linear _ _ _ _ _).zero, zero_add, finset_comp]; simp⟩,
  add_zero := λ f, quotient.induction_on f $ λ x,
    quotient.sound ⟨x.1 ∪ ∅, by simp, by simp, by dsimp;
    rw [(finset_linear _ _ _ _ _).add, (finset_linear _ _ _ _ _).zero];
    rw [(finset_linear _ _ _ _ _).zero, add_zero, finset_comp]; simp⟩,
  add_left_neg := λ f, quotient.induction_on f $ λ x,
    quotient.sound ⟨x.1, by simp, by simp, by dsimp;
    rw [(finset_linear _ _ _ _ _).neg, add_left_neg];
    rw [(finset_linear _ _ _ _ _).zero, (finset_linear _ _ _ _ _).zero]⟩,
  add_comm := λ f g, quotient.induction_on₂ f g $ λ x y,
    quotient.sound ⟨x.1 ∪ y.1, by simp, by simp, by dsimp;
    rw [finset.union_comm x.1 y.1, add_comm]⟩,
  smul_add := λ c f g, quotient.induction_on₂ f g $ λ x y,
    quotient.sound ⟨x.1 ∪ y.1, by simp, by simp, by dsimp;
    repeat { rw (finset_linear _ _ _ _ _).add
      <|> rw (finset_linear _ _ _ _ _).smul };
    apply smul_add⟩,
  add_smul := λ c d f, quotient.induction_on f $ λ x,
    quotient.sound ⟨x.1 ∪ x.1, by simp, by simp, by dsimp;
    repeat { rw (finset_linear _ _ _ _ _).add
      <|> rw (finset_linear _ _ _ _ _).smul
      <|> rw finset_comp };
    simp [add_smul]⟩,
  mul_smul := λ c d f, quotient.induction_on f $ λ x,
    quotient.sound ⟨x.1, by simp, by simp, by dsimp;
    repeat { rw (finset_linear _ _ _ _ _).smul };
    simp [mul_smul]⟩,
  one_smul := λ f, quotient.induction_on f $ λ x,
    quotient.sound ⟨x.1, by simp, by simp, by dsimp;
    simp [one_smul]⟩ }

theorem mk_linear (s : finset ι) : is_linear_map (@mk _ _ _ _ β _ s) :=
{ add := λ x y, quotient.sound ⟨s, by simp, by simp,
    by dsimp; rw [finset.union_self]; simp⟩,
  smul := λ c x, quotient.sound ⟨s, by simp, by simp,
    by dsimp; simp⟩ }

theorem mk_inj (s : finset ι) : function.injective (@mk _ _ _ _ β _ s) :=
λ x y H, let ⟨t, ht1, ht2, ht3⟩ := quotient.exact H in
funext $ λ ⟨i, (hi : i ∈ s)⟩, have ht4 : _ := congr_fun ht3 ⟨i, ht1 hi⟩,
by dsimp [finset_to_finset] at ht4; rw [dif_pos hi, dif_pos hi] at ht4; exact ht4

def of (i : ι) (x : β i) : direct_sum R ι β :=
mk {i} $ λ j, eq.rec_on (eq.symm $ finset.mem_singleton.1 j.2) x

theorem of_linear (i : ι) : is_linear_map (@of _ _ _ _ β _ i) :=
{ add := λ x y, quotient.sound ⟨{i}, by simp, by simp,
    funext $ λ ⟨j, (hj : j ∈ {i})⟩, by dsimp; rw [finset.union_self]; simp at hj ⊢;
    clear _fun_match; subst hj; refl⟩,
  smul := λ c x, quotient.sound ⟨{i}, by simp, by simp,
    by dsimp; funext j; cases j with j hj; simp [finset.to_set] at hj;
    subst hj; simp⟩ }

@[simp] lemma of_add (i : ι) (x y : β i) : of i (x + y) = of i x + of i y :=
(of_linear _).add _ _

@[simp] lemma of_zero (i : ι) : of i (0 : β i) = 0 :=
(of_linear _).zero

@[simp] lemma of_neg (i : ι) (x : β i) : of i (-x) = -of i x :=
(of_linear _).neg _

@[simp] lemma of_sub (i : ι) (x y : β i) : of i (x - y) = of i x - of i y :=
(of_linear _).sub _ _

@[simp] lemma of_smul (c : R) (i : ι) (x : β i) : of i (c • x) = c • of i x :=
(of_linear _).smul _ _

theorem of_inj (i : ι) : function.injective (@of _ _ _ _ β _ i) :=
λ x y H, congr_fun (mk_inj _ H) ⟨i, by simp [finset.to_set]⟩

theorem finset_insert (i : ι) (s : finset ι) (Hs : i ∉ s)
  (f : direct_sum.finset R ι β (insert i s)) :
  f = finset_to_finset _ _ _ s _ (λ i, f ⟨i, finset.mem_insert_of_mem i.2⟩)
      + finset_to_finset _ _ _ {i} _ (λ j, f ⟨j, finset.mem_insert.2 $ or.inl $ finset.mem_singleton.1 j.2⟩) :=
begin
  funext j,
  cases j with j h1,
  change _ = _ + _,
  dsimp [finset_to_finset],
  dsimp [finset.to_set] at h1,
  cases finset.mem_insert.1 h1 with h2 h2,
  { have h3 : j ∉ s,
    { rw h2, exact Hs },
    have h4 : j ∈ finset.singleton i,
    { simp [h2] },
    rw [dif_neg h3, dif_pos h4, zero_add] },
  have h3 : j ∉ finset.singleton i,
  { intro H, simp at H, subst H, exact Hs h2 },
  rw [dif_pos h2, dif_neg h3, add_zero]
end

theorem mk_eq_mk_add_of (i : ι) (s : finset ι) (Hs : i ∉ s)
  (f : direct_sum.finset R ι β (insert i s)) :
    mk (insert i s) f
  = mk s (λ i, f ⟨i.1, finset.mem_insert_of_mem i.2⟩)
    + of i (f ⟨i, finset.mem_insert_self _ _⟩) :=
begin
  have h1 : s ∪ finset.singleton i = insert i s,
  { rw [finset.union_comm, finset.insert_eq], refl },
  apply quotient.sound,
  refine ⟨insert i s, by simp, _, _⟩,
  { simp [h1] },
  dsimp,
  rw [h1, finset_id, finset_id],
  convert finset_insert i s Hs f,
  funext j,
  cases j with j h2,
  simp [finset.to_set] at h2,
  subst h2,
  refl
end

@[elab_as_eliminator]
protected theorem induction_on {C : direct_sum R ι β → Prop}
  (x : direct_sum R ι β) (H_zero : C 0)
  (H_basic : ∀ i x, C (of i x))
  (H_plus : ∀ x y, C x → C y → C (x + y)) : C x :=
begin
  apply quotient.induction_on x,
  rintro ⟨s, f⟩,
  revert f,
  apply finset.induction_on s,
  { intro f,
    refine cast (congr_arg C $ quotient.sound ⟨∅, _, _, _⟩) H_zero,
    simp, simp,
    funext i,
    exact false.elim i.2 },
  intros i s h1 h2 h3,
  change C (mk _ _),
  rw mk_eq_mk_add_of _ _ h1,
  exact H_plus _ _ (h2 _) (H_basic _ _)
end

variables {γ : Type u₁} [module R γ]
variables (φ : Π i, β i → γ) (hφ : Π i, is_linear_map (φ i))

def finset.to_module (s : finset ι) (f : direct_sum.finset R ι β s) : γ :=
s.sum $ λ i, if h : i ∈ s then φ i $ f ⟨i, h⟩ else 0

theorem finset.to_module.insert (i : ι) (s : finset ι) (Hs : i ∉ s)
  (f : direct_sum.finset R ι β (insert i s)) :
    finset.to_module φ _ f
  = finset.to_module φ s (finset_to_finset _ _ _ _ _ f) + φ i (f ⟨i, finset.mem_insert_self _ _⟩) :=
begin
  dsimp [finset.to_module],
  simp [finset.sum_insert Hs],
  suffices : finset.sum s (λ j, dite (j ∈ insert i s) (λ h, φ j (f ⟨j, h⟩)) (λ _, 0))
    = finset.sum s (λ j, dite (j ∈ s) (λ h, φ j (finset_to_finset R ι β (insert i s) s f ⟨j, h⟩)) (λ _, 0)),
  { rw [this, add_comm] },
  fapply finset.sum_bij,
  { exact λ i _, i },
  { exact λ _, id },
  { intros j hj,
    rw [dif_pos (finset.mem_insert_of_mem hj), dif_pos hj],
    dsimp [finset_to_finset],
    rw dif_pos (finset.mem_insert_of_mem hj) },
  { intros, assumption },
  { exact λ j hj, ⟨j, hj, rfl⟩ }
end

include hφ
variables {φ}

theorem finset.to_module.comp (s t : finset ι) (Hst : s ⊆ t)
  (f : direct_sum.finset R ι β s) :
  finset.to_module φ t (finset_to_finset _ _ _ s _ f)
  = finset.to_module φ s f :=
begin
  fapply finset.sum_bij_ne_zero,
  { exact λ i _ _, i },
  { intros i h1 h2,
    by_contra h,
    rw dif_pos h1 at h2,
    dsimp [finset_to_finset] at h2,
    rw dif_neg h at h2,
    exact h2 (hφ i).zero },
  { intros, assumption },
  { intros i h1 h2,
    refine ⟨i, Hst h1, _, rfl⟩,
    rw dif_pos h1 at h2,
    rw [dif_pos (Hst h1)],
    dsimp [finset_to_finset],
    rwa dif_pos h1 },
  intros i h1 h2,
  rw dif_pos h1,
  dsimp [finset_to_finset],
  split_ifs, {refl},
  exact (hφ i).zero
end

theorem finset.to_module.linear (s : finset ι) :
  is_linear_map (finset.to_module φ s) :=
begin
  constructor,
  { apply finset.induction_on s,
    { intros, simp [finset.to_module] },
    intros i s h1 ih f g,
    simp [finset.to_module.insert _ _ _ h1],
    rw [(finset_linear _ _ _ _ _).add, ih],
    change φ i (_ + _) + _ = _,
    rw [(hφ i).add],
    ac_refl },
  apply finset.induction_on s,
  { intros, simp [finset.to_module] },
  intros i s h1 ih c f,
  simp [finset.to_module.insert _ _ _ h1],
  rw [(finset_linear _ _ _ _ _).smul, ih, (hφ i).smul, smul_add],
  ac_refl
end

variables (φ)
def to_module (f : direct_sum R ι β) : γ :=
quotient.lift_on f (λ x, finset.to_module φ x.1 x.2) $
λ ⟨x1, x2⟩ ⟨y1, y2⟩ ⟨s, hs1, hs2, hs3⟩,
calc  finset.to_module φ x1 x2
    = finset.to_module φ s (finset_to_finset _ _ _ x1 s x2) :
  eq.symm $ finset.to_module.comp hφ _ _ hs1 _
... = finset.to_module φ s (finset_to_finset _ _ _ y1 s y2) :
  congr_arg _ hs3
... = finset.to_module φ y1 y2 :
  finset.to_module.comp hφ _ _ hs2 _
variables {φ}

theorem to_module.linear : is_linear_map (to_module φ hφ) :=
{ add  := λ f g, quotient.induction_on₂ f g $ λ x y,
    show finset.to_module _ _ _ = finset.to_module _ _ _ + finset.to_module _ _ _,
    by dsimp; rw [(finset.to_module.linear hφ _).add];
    rw [finset.to_module.comp hφ _ _ finset.subset_union_left];
    rw [finset.to_module.comp hφ _ _ finset.subset_union_right],
  smul := λ c f, quotient.induction_on f $ λ x,
    (finset.to_module.linear hφ _).smul _ _ }

@[simp] lemma to_module.of (i x) : to_module φ hφ (of i x) = φ i x :=
show finset.to_module _ _ _ = _,
by dsimp [finset.to_module]; simp

@[simp] lemma to_module.add (f g) : to_module φ hφ (f + g) = to_module φ hφ f + to_module φ hφ g :=
(to_module.linear _).add _ _

@[simp] lemma to_module.zero : to_module φ hφ 0 = 0 :=
(to_module.linear _).zero

@[simp] lemma to_module.neg (f) : to_module φ hφ (-f) = -to_module φ hφ f :=
(to_module.linear _).neg _

@[simp] lemma to_module.sub (f g) : to_module φ hφ (f - g) = to_module φ hφ f - to_module φ hφ g :=
(to_module.linear _).sub _ _

@[simp] lemma to_module.smul (c f) : to_module φ hφ (c • f) = c • to_module φ hφ f :=
(to_module.linear _).smul _ _

variables (ψ : direct_sum R ι β → γ) (hψ : is_linear_map ψ)
variables (H1 : ∀ i x, ψ (of i x) = to_module φ hφ (of i x))

theorem to_module.unique (f : direct_sum R ι β) : ψ f = to_module φ hφ f :=
direct_sum.induction_on f
  (hψ.zero.trans (to_module.linear _).zero.symm) H1 $ λ f g ihf ihg,
by rw [hψ.add, (to_module.linear _).add, ihf, ihg]

variables (ψ' : direct_sum R ι β → γ) (hψ' : is_linear_map ψ')
variables (H2 : ∀ i x, ψ (of i x) = ψ' (of i x))
omit hφ

theorem to_module.ext (f : direct_sum R ι β) : ψ f = ψ' f :=
direct_sum.induction_on f
  (hψ.zero.trans hψ'.zero.symm) H2 $ λ f g ihf ihg,
by rw [hψ.add, hψ'.add, ihf, ihg]

def set_to_set (S T : set ι) (H : S ⊆ T)
  (f : direct_sum R S (β ∘ subtype.val)) :
  direct_sum R T (β ∘ subtype.val) :=
to_module (λ (i : S) x, of ⟨i.1, H i.2⟩ x) (λ _, of_linear _) f

protected def id (M : Type v) [module R M] :
  direct_sum R punit (λ _, M) ≃ₗ M :=
{ to_fun := to_module (λ _, id) (λ _, is_linear_map.id),
  inv_fun := λ x, of punit.star x,
  left_inv := λ x, by refine to_module.ext _
      (is_linear_map.comp (of_linear _) (to_module.linear _)) _
      is_linear_map.id (λ u _, _) x;
    cases u; simp,
  right_inv := λ x, by simp,
  linear_fun := to_module.linear _ }

end direct_sum