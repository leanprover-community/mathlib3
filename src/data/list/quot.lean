/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import data.list.basic
import logic.function.n_ary

/-!
# Quotients indexed by a `list`

In this file, we define lifting and recursion principle for quotients indexed by a `list`.
-/

universes u v

namespace list
variables {ι : Type*}

section
variables {α : ι → Sort*} {β : Sort*}

lemma pi_mem_eq {l₁ l₂ : list ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂) :
  (Π i ∈ l₁, α i) = (Π i ∈ l₂, α i) :=
pi_congr (λ _, by rw [hl])

lemma fun_pi_mem_eq {l₁ l₂ : list ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂) :
  ((Π i ∈ l₁, α i) → β) = ((Π i ∈ l₂, α i) → β) :=
by rw [pi_mem_eq hl]

-- @[elab_as_eliminator]
def mem_rec (C : (ι → Prop) → Sort*)
  {l₁ l₂ : list ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂)
  (h : C (∈ l₁)) : C (∈ l₂) :=
by { convert h, simp_rw [hl] }

end

variables [dec : decidable_eq ι] {α : ι → Type u} [S : Π i, setoid (α i)] {β : Sort v}

include dec

namespace pi_mem_cons

def mk {i : ι} {l : list ι} (a : α i) (as : Π j ∈ l, α j) :
  Π j ∈ (i::l), α j :=
λ j hj, if H : j = i then (congr_arg α H).mpr a else as j (hj.resolve_left H)

omit dec

def head {i : ι} {l : list ι} (a : Π j ∈ (i::l), α j) :
  α i :=
a i (mem_cons_self _ _)

def tail {i : ι} {l : list ι} (a : Π j ∈ (i::l), α j) :
  Π j ∈ l, α j :=
λ j hj, a j (mem_cons_of_mem _ hj)

include dec

@[simp] lemma eta {i : ι} {l : list ι} (a : Π j ∈ (i::l), α j) :
  mk (head a) (tail a) = a :=
by { ext j hj, dsimp [mk], split_ifs with H, { cases H, refl }, { refl } }

@[simp] lemma head_mk {i : ι} {l : list ι} (a : α i) (as : Π j ∈ l, α j) :
  head (mk a as) = a :=
by simp [head, mk]

lemma tail_mk {i : ι} {l : list ι} (hl : (i::l).nodup) (a : α i) (as : Π j ∈ l, α j) :
  tail (mk a as) = as :=
by { ext j hj, obtain ⟨hl, _⟩ := pairwise_cons.mp hl, simpa [tail, mk, (hl j hj).symm] }

@[simp] lemma mk_apply {i : ι} {l : list ι} (a : α i) (as : Π j ∈ l, α j)
  {α' : ι → Type*} (f : ∀ ⦃j⦄, α j → α' j):
  mk (f a) (λ j hj, f (as j hj)) = λ j hj, f ((mk a as) j hj) :=
by { ext j hj, dsimp [pi_mem_cons.mk], split_ifs with H, { cases H, refl }, { refl }, }

include S

lemma setoid_congr {i : ι} {l : list ι} {a b : α i} {as bs : Π j ∈ l, α j}
  (h : a ≈ b) (hs : ∀ (i : ι) (hi : i ∈ l), as i hi ≈ bs i hi) :
  ∀ j hj, mk a as j hj ≈ mk b bs j hj :=
by { intros j hj, dsimp [mk], split_ifs with H, { cases H, exact h }, { exact hs _ _, } }

end pi_mem_cons

@[simp] def curry : Π {l : list ι} (f : (Π i ∈ l, α i) → β),
  function_of'.{v} α (ulift $ plift β) l
| []     f := ulift.up $ plift.up $ f (λ i hi, hi.elim)
| (i::l) f := λ a, curry (λ as, f (pi_mem_cons.mk a as))

include S

lemma curry_equiv_curry : Π {l : list ι} (f g : (Π i ∈ l, α i) → β),
  (∀ (as bs : Π i ∈ l, α i), (∀ i (hi : i ∈ l), as i hi ≈ bs i hi) → f as = g bs) →
  (curry f).equiv (curry g)
| []     f g hf := ulift.ext _ _ $ plift.down_inj.1 $ hf _ _ (λ i hi, hi.elim)
| (i::l) f g hf := λ a b h, curry_equiv_curry _ _ (λ _ _ hs, hf _ _ (pi_mem_cons.setoid_congr h hs))

omit dec S

@[simp] def uncurry : Π {l : list ι} (f : function_of'.{v} α (ulift $ plift β) l),
  (Π i ∈ l, α i) → β
| []      f := λ _, f.down.down
| (i::tl) f := λ as, uncurry (f (pi_mem_cons.head as)) (pi_mem_cons.tail as)

include dec

lemma uncurry_curry : Π {l : list ι} (f : (Π i ∈ l, α i) → β), uncurry (curry f) = f
| []      _ := by { ext, dsimp, congr', ext j hj, exact hj.elim }
| (i::tl) f := by { dsimp, ext, rw [uncurry_curry, pi_mem_cons.eta] }

lemma curry_uncurry : Π {l : list ι} (hl : l.nodup) (f : function_of'.{v} α (ulift $ plift β) l),
  curry (uncurry f) = f
| []      _                    _ := ulift.ext _ _ $ plift.down_inj.1 $ rfl
| (i::tl) (pairwise.cons h hs) f := begin
    dsimp, ext a,
    simp_rw [pi_mem_cons.head_mk, pi_mem_cons.tail_mk (pairwise.cons h hs)],
    exact curry_uncurry hs _,
  end

lemma curry_left_inverse {l : list ι} : function.left_inverse (@uncurry _ α β l) curry :=
uncurry_curry

def curry_equiv {l : list ι} (hl : l.nodup) :
  ((Π i ∈ l, α i) → β) ≃ function_of'.{v} α (ulift $ plift β) l :=
{ to_fun := curry,
  inv_fun := uncurry,
  left_inv := uncurry_curry,
  right_inv := curry_uncurry hl, }

lemma curry_inj {l : list ι} : function.injective (@curry _ _ α β l) :=
curry_left_inverse.injective

omit dec

lemma uncurry_inj {l : list ι} (hl : l.nodup) : function.injective (@uncurry _ α β l) :=
by { classical, exact (curry_equiv hl).symm.injective }

include dec

/-- Lift a function on `Π i ∈ l, α i` to `Π i ∈ l, quotient (S i)`. -/
def quotient_lift {l : list ι} (f : (Π i ∈ l, α i) → β)
  (h : ∀ (a b : Π i ∈ l, α i), (∀ i (hi : i ∈ l), a i hi ≈ b i hi) → f a = f b)
  (q : Π i ∈ l, quotient (S i)) : β :=
uncurry (function_of'.quotient_lift (curry f) (curry_equiv_curry _ _ h)) q

/-- Lift a function on `Π i ∈ l, α i` to `Π i ∈ l, quotient (S i)`. -/
def quotient_lift_on {l : list ι} (q : Π i ∈ l, quotient (S i)) (f : (Π i ∈ l, α i) → β)
  (h : ∀ (a b : Π i ∈ l, α i), (∀ i (hi : i ∈ l), a i hi ≈ b i hi) → f a = f b) : β :=
quotient_lift f h q

include S

@[simp] lemma quotient_lift_nil (f : (Π i ∈ ([] : list ι), α i) → β) (h) :
  quotient_lift f h = λ q, f (λ i hi, hi.elim) :=
rfl

@[simp] lemma quotient_lift_mk : Π {l : list ι} (f : (Π i ∈ l, α i) → β)
  (h : ∀ (a b : Π i ∈ l, α i), (∀ i (hi : i ∈ l), a i hi ≈ b i hi) → f a = f b)
  (a : Π i ∈ l, α i), quotient_lift f h (λ i hi, ⟦a i hi⟧) = f a
| []     f h a := by { dsimp, congr', ext j hj, exact hj.elim, }
| (i::l) f h a := begin
    conv_rhs { rw [← pi_mem_cons.eta a] },
    exact quotient_lift_mk _ (λ a' b' h', h _ _ (pi_mem_cons.setoid_congr (setoid.refl _) h')) _,
  end

@[simp] lemma quotient_lift_on_nil (q : Π i ∈ ([] : list ι), quotient (S i)) :
  @quotient_lift_on _ _ _ _ β _ q = λ f h, f (λ i hi, hi.elim) :=
rfl

@[simp] lemma quotient_lift_on_mk {l : list ι} (a : Π i ∈ l, α i) :
  @quotient_lift_on _ _ _ _ β _ (λ i hi, ⟦a i hi⟧) = λ f h, f a :=
by { ext f h, exact quotient_lift_mk f h a, }

/-- Choice-free induction principle for quotients indexed by a `list`. -/
@[nolint decidable_classical, elab_as_eliminator]
lemma quotient_ind : Π {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Prop}
  (f : ∀ a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧)) (q : Π i ∈ l, quotient (S i)), C q
| []     C f q := cast (congr_arg _ (funext₂ (λ i hi, hi.elim))) (f (λ i hi, hi.elim))
| (i::l) C f q := begin
    rw [← pi_mem_cons.eta q],
    induction (pi_mem_cons.head q) using quotient.ind,
    refine @quotient_ind _ (λ q, C (pi_mem_cons.mk ⟦a⟧ q)) _ (pi_mem_cons.tail q),
    intros as,
    rw [pi_mem_cons.mk_apply a as],
    exact f _,
  end

/-- Choice-free induction principle for quotients indexed by a `list`. -/
@[nolint decidable_classical, elab_as_eliminator]
lemma quotient_induction_on {l : list ι}
  {C : (Π i ∈ l, quotient (S i)) → Prop}
  (q : Π i ∈ l, quotient (S i)) (f : ∀ a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧)) :
  C q :=
quotient_ind f q

omit S

section quotient_rec
variables {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Sort*}
  (f : ∀ a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧))

omit dec

attribute [reducible]
private def quotient_rec_indep
  (a : Π i ∈ l, α i) : psigma C :=
⟨λ i hi, ⟦a i hi⟧, f a⟩

variables (h : ∀ (a b : Π i ∈ l, α i) (h : ∀ i hi, a i hi ≈ b i hi), (eq.rec (f a)
  (funext₂ (λ i hi, quotient.sound (h i hi)) : (λ i hi, ⟦a i hi⟧) = (λ i hi, ⟦b i hi⟧)) :
    C (λ i hi, ⟦b i hi⟧)) = f b)

private lemma quotient_rec_indep_coherent :
  ∀ a b : Π i ∈ l, α i, (∀ i hi, a i hi ≈ b i hi) →
    quotient_rec_indep f a = quotient_rec_indep f b :=
λ a b e, psigma.eq (funext₂ (λ i hi, quotient.sound (e i hi))) (h a b e)

include h dec

private lemma quotient_rec_lift_indep_pr1 (q : Π i ∈ l, quotient (S i)) :
  (quotient_lift (quotient_rec_indep f) (quotient_rec_indep_coherent f h) q).1 = q :=
quotient_ind (λ a, funext₂ (λ i hi, by rw [quotient_lift_mk])) q

end quotient_rec

/-- Recursion principle for quotients indexed by a `list`. -/
@[elab_as_eliminator] def quotient_rec {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Sort*}
  (f : Π a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧))
  (h : ∀ (a b : Π i ∈ l, α i) (h : ∀ i hi, a i hi ≈ b i hi), (eq.rec (f a)
    (funext₂ (λ i hi, quotient.sound (h i hi)) : (λ i hi, ⟦a i hi⟧) = (λ i hi, ⟦b i hi⟧)) :
      C (λ i hi, ⟦b i hi⟧)) = f b)
  (q : Π i ∈ l, quotient (S i)) :
  C q :=
eq.rec_on (quotient_rec_lift_indep_pr1 f h q)
  ((quotient_lift (quotient_rec_indep f) (quotient_rec_indep_coherent f h) q).2)

/-- Recursion principle for quotients indexed by a `list`. -/
@[elab_as_eliminator] def quotient_rec_on {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Sort*}
  (q : Π i ∈ l, quotient (S i))
  (f : Π a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧))
  (h : ∀ (a b : Π i ∈ l, α i) (h : ∀ i hi, a i hi ≈ b i hi), (eq.rec (f a)
    (funext₂ (λ i hi, quotient.sound (h i hi)) : (λ i hi, ⟦a i hi⟧) = (λ i hi, ⟦b i hi⟧)) :
      C (λ i hi, ⟦b i hi⟧)) = f b) :
  C q :=
quotient_rec f h q

/-- Recursion principle for quotients indexed by a `list`. -/
@[elab_as_eliminator] def quotient_hrec_on {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Sort*}
  (q : Π i ∈ l, quotient (S i))
  (f : Π a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧))
  (h : ∀ (a b : Π i ∈ l, α i) (h : ∀ i hi, a i hi ≈ b i hi), f a == f b) :
  C q :=
quotient_rec_on q f (λ a b p, eq_of_heq ((eq_rec_heq _ (f a)).trans (h a b p)))

@[simp] lemma quotient_rec_mk {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Sort*}
  (f : Π a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧))
  (h) (a : Π i ∈ l, α i) :
  @quotient_rec _ _ _ _ _ C f h (λ i hi, ⟦a i hi⟧) = f a :=
begin
  dsimp [quotient_rec], refine eq_of_heq ((eq_rec_heq _ _).trans _),
  rw [quotient_lift_mk (quotient_rec_indep f) (quotient_rec_indep_coherent f h) a],
end

@[simp] lemma quotient_rec_on_mk {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Sort*}
  (a : Π i ∈ l, α i) :
  @quotient_rec_on _ _ _ _ _ C (λ i hi, ⟦a i hi⟧) = λ f h, f a :=
by { ext f h, exact quotient_rec_mk _ _ _, }

include S

lemma quotient_lift_inj {l : list ι} (f₁ f₂ : (Π i ∈ l, α i) → β) (h₁ h₂) :
  quotient_lift f₁ h₁ = quotient_lift f₂ h₂ → f₁ = f₂ :=
λ h, funext $ λ _, by rw [← quotient_lift_mk f₁ h₁, ← quotient_lift_mk f₂ h₂, h]

lemma quotient_lift_inj_iff {l : list ι} (f₁ f₂ : (Π i ∈ l, α i) → β) (h₁ h₂) :
  quotient_lift f₁ h₁ = quotient_lift f₂ h₂ ↔ f₁ = f₂ :=
⟨quotient_lift_inj _ _ h₁ h₂, λ h, by simp_rw [h]⟩

-- TODO: Can lean compute the motive? Or maybe a tactic (extension) is needed?
-- Or there are some better proofs?
-- (This may because of the order of arguments of `has_mem.mem`)?

lemma quotient_lift_on_heq {l₁ l₂ : list ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂) :
  @quotient_lift_on _ _ α _ β l₁ == @quotient_lift_on _ _ α _ β l₂ :=
begin
  ext1, { exact pi_mem_eq hl }, intros q₁ q₂,
  apply list.quotient_induction_on q₂,
  apply list.quotient_induction_on q₁,
  simp_rw [quotient_lift_on_mk],
  apply mem_rec (λ meml₂, -- TODO
    ∀ (a₁ : Π i ∈ l₁, α i) (a₂ : Π i, meml₂ i → α i),
        ((λ i hi, ⟦a₁ i hi⟧) == λ i hi, ⟦a₂ i hi⟧) →
      ((λ (f : (Π i ∈ l₁, α i) → β)
          (h : ∀ (a b : Π i ∈ l₁, α i), (∀ i hi, a i hi ≈ b i hi) → f a = f b), f a₁) ==
        (λ (f : (Π i, meml₂ i → α i) → β)
          (h : ∀ (a b : Π i, meml₂ i → α i),  (∀ i hi, a i hi ≈ b i hi) → f a = f b), f a₂))) hl,
  intros a₁ a₂ ha, rw [heq_iff_eq] at *,
  ext f h, apply h, exact λ i hi, quotient.exact (congr_fun₂ ha i hi),
end

lemma quotient_rec_on_heq {l₁ l₂ : list ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂) :
  @quotient_rec_on _ _ α _ l₁ == @quotient_rec_on _ _ α _ l₂ :=
begin
  ext1, { exact fun_pi_mem_eq hl }, intros C₁ C₂ hC,
  ext1, { exact pi_mem_eq hl }, intros q₁ q₂,
  apply list.quotient_induction_on q₂,
  apply list.quotient_induction_on q₁,
  simp_rw [quotient_rec_on_mk],
  revert C₁ C₂ hC,
  apply mem_rec (λ meml₂, -- TODO
    ∀ (C₁ : (Π i ∈ l₁, quotient (S i)) → Sort*)
      (C₂ : (Π i, meml₂ i → quotient (S i)) → Sort*),
      C₁ == C₂ →
    ∀ (a₁ : Π i ∈ l₁, α i) (a₂ : Π i, meml₂ i → α i),
      ((λ i hi, ⟦a₁ i hi⟧) == λ i hi, ⟦a₂ i hi⟧) →
      ((λ (f : Π (a : Π i ∈ l₁, α i), C₁ (λ i hi, ⟦a i hi⟧))
        (h : ∀ (a b : Π i ∈ l₁, α i) (h : ∀ i hi, a i hi ≈ b i hi), (eq.rec (f a)
          (funext₂ (λ i hi, quotient.sound (h i hi)) : (λ i hi, ⟦a i hi⟧) = (λ i hi, ⟦b i hi⟧)) :
          C₁ (λ i hi, ⟦b i hi⟧)) = f b),
        f a₁) ==
      (λ (f : Π (a : Π i, meml₂ i → α i), C₂ (λ i hi, ⟦a i hi⟧))
        (h : ∀ (a b : Π i, meml₂ i → α i) (h : ∀ i hi, a i hi ≈ b i hi), (eq.rec (f a)
          (funext₂ (λ i hi, quotient.sound (h i hi)) : (λ i hi, ⟦a i hi⟧) = (λ i hi, ⟦b i hi⟧)) :
          C₂ (λ i hi, ⟦b i hi⟧)) = f b),
        f a₂))) hl,
  intros C₁ C₂ hC, cases hC,
  intros a₁ a₂ ha, rw [heq_iff_eq] at *,
  ext1, { refl }, intros f _ hf, cases hf,
  ext1, { refl }, intros h _ _,
  exact heq_of_eq_rec_left _ (h a₁ a₂ $ λ i hi, quotient.exact (congr_fun₂ ha i hi)),
end

end list
