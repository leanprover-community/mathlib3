/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import group_theory.subgroup.basic
import group_theory.congruence

/-!
-/

open function set list free_monoid

variables {α : Type*}

local notation `of'` := free_monoid.of

structure ncword.data (α : Type*) :=
(cancel2 : α → α → free_monoid α)
(r : α → α → Prop)
(cancel2_eq_self : ∀ {x y}, r x y → cancel2 x y = of x * of y)
(chain'_r_cancel2 : ∀ x y, chain' r (cancel2 x y).to_list)
(r_last'_cancel2 : ∀ {x y}, r x y → ∀ {z z'}, z' ∈ (cancel2 z x).to_list.last' → r z' y)

@[ext] structure _root_.ncword (d : ncword.data α) :=
(word : free_monoid α)
(chain : chain' d.r word.to_list)

namespace ncword

variables {d : data α}

@[simps] def of (x : α) : ncword d := ⟨of x, chain'_singleton _⟩

instance : has_one (ncword d) := ⟨⟨1, list.chain'_nil⟩⟩

@[simp] lemma one_word : (1 : ncword d).word = 1 := rfl

instance : mul_action (free_monoid α) (ncword d) :=
free_monoid.mk_mul_action $ λ x w,
  ⟨list.cases_on w.word.to_list (of' x) (λ y l, d.cancel2 x y * l),
  begin
    cases w with w hw,
    induction w using free_monoid.cases_on with y l,
    { exact list.chain'_singleton _ },
    { rw [free_monoid.to_list_of_mul, list.chain'_cons'] at hw,
      refine list.chain'.append (d.chain'_r_cancel2 _ _) hw.2 _,
      exact λ x' hx' y' hy', d.r_last'_cancel2 (hw.1 y' hy') hx' }
  end⟩

instance : has_mul (ncword d) := ⟨λ w₁ w₂, w₁.word • w₂⟩

@[simp] lemma word_smul (w₁ w₂ : ncword d) : w₁.word • w₂ = w₁ * w₂ := rfl
@[simp] lemma of_smul (x : α) (w : ncword d) : of' x • w = of x * w := rfl

lemma word_mk (w hw) : word (mk w hw : ncword d) = w := rfl

lemma mk_word (w : ncword d) (h : chain' d.r w.word.to_list := w.2) : mk w.word h = w :=
ext _ _ rfl

@[simps] def cons (x : α) (w : ncword d) (h : chain' d.r (of' x * word w).to_list) : ncword d :=
⟨of' x * word w, h⟩

@[simp] lemma cons_one (x : α) (h : chain' d.r (of' x * 1).to_list := chain'_singleton _) :
  cons x 1 h = of x :=
rfl

@[elab_as_eliminator] def rec_on_cons {C : ncword d → Sort*} (w : ncword d) (h₁ : C 1)
  (hcons : ∀ {x} {w : ncword d} (h : chain' d.r (of' x * w.word).to_list),
    C w → C (cons x w h)) :
  C w :=
ncword.rec_on w $ λ l, free_monoid.rec_on l (λ _, h₁) $ λ x w ihw hw, hcons _ (ihw hw.tail)

@[elab_as_eliminator] def cases_on_cons {C : ncword d → Sort*} (w : ncword d) (h₁ : C 1)
  (hcons : ∀ {x} {w : ncword d} (h : chain' d.r (of' x * w.word).to_list), C (cons x w h)) :
  C w :=
rec_on_cons w h₁ (λ x w h _, hcons h)

@[simp] lemma word_of_mul_cons (x : α) {y w} (hyw : chain' d.r (of' y * word w).to_list) :
  (of x * cons y w hyw).word = d.cancel2 x y * word w :=
rfl

@[simp] lemma word_of_mul_of (x y : α) :
  (of x * of y : ncword d).word = d.cancel2 x y :=
by rw [← cons_one y, word_of_mul_cons, one_word, mul_one]

lemma cons_eq_mul {x : α} {w : ncword d} (h : chain' d.r (of' x * word w).to_list) :
  cons x w h = of x * w :=
begin
  induction w using ncword.cases_on_cons with y w ihw,
  { refl },
  { ext1, rw [word_of_mul_cons, d.cancel2_eq_self h.rel_head, cons_word, cons_word, mul_assoc] }
end

lemma cons_mul {x} {w} (h : chain' d.r (of' x * word w).to_list) (w' : ncword d) :
  cons x w h * w' = of x * (w * w') :=
rfl

instance : mul_one_class (ncword d) :=
{ one_mul := λ ⟨w, hw⟩, rfl,
  mul_one := λ w,
    begin
      induction w using ncword.rec_on_cons with x w hw ihw, { refl },
      rw [← word_smul, cons_word, mul_smul, word_smul, ihw, cons_eq_mul, of_smul]
    end,
  .. ncword.has_one, .. ncword.has_mul }

structure monoid_data (α : Type*) extends data α :=
(cancel2_smul : ∀ x y (w : ncword to_data), ¬to_data.r x y →
  to_data.cancel2 x y • w = (of' x * of' y) • w)

lemma cancel2_smul {d : monoid_data α} (x y : α) (w : ncword d.to_data) :
  d.cancel2 x y • w = of x * (of y * w) :=
begin
  by_cases hr : d.r x y,
  { rw [d.cancel2_eq_self hr, mul_smul, of_smul, of_smul] },
  { exact d.cancel2_smul _ _ _ hr }
end

instance (d : monoid_data α) :
  is_scalar_tower (free_monoid α) (ncword d.to_data) (ncword d.to_data) :=
is_scalar_tower.of_mclosure_eq_top free_monoid.closure_range_of $ forall_range_iff.2 $ λ x w₁ w₂,
  begin
    rw [smul_eq_mul, smul_eq_mul, of_smul, of_smul],
    induction w₁ using ncword.rec_on_cons with y w₁ hyw₁ ihw₁ generalizing x,
    { rw [one_mul, mul_one], },
    { rw [← word_smul, word_of_mul_cons, mul_smul, word_smul, cancel2_smul, cons_mul] }
  end

instance (d : monoid_data α) : monoid (ncword d.to_data) :=
{ mul_assoc := λ x y z, smul_mul_assoc x.word y z,
  .. ncword.mul_one_class }

variable {md : monoid_data α}

def cancel (d : monoid_data α) : free_monoid α →* ncword d.to_data := free_monoid.lift of

@[simp] lemma cancel_of (x : α) : cancel md (of' x) = of x := rfl

lemma cancel_eq_smul_one (l : free_monoid α) : cancel md l = l • 1 :=
by { rw [cancel, free_monoid.lift_apply, list.prod_eq_foldr, foldr_map], refl }

@[simp] lemma cancel_word (w : ncword md.to_data) : cancel md w.word = w :=
by rw [cancel_eq_smul_one, word_smul, mul_one]

lemma cancel_surjective : surjective (cancel md) := left_inverse.surjective cancel_word

@[simp] lemma mclosure_range_of (d : monoid_data α) :
  submonoid.closure (range (of : α → ncword d.to_data)) = ⊤ :=
top_unique $ λ g hg, cancel_word g ▸ submonoid.list_prod_mem _
  (forall_mem_map_iff.2 $ λ x hx, submonoid.subset_closure $ mem_range_self _)

lemma con_word_of_mul (c : con (free_monoid α))
  (hc : ∀ x y, ¬md.r x y → c (of' x * of' y) (md.cancel2 x y))
  (x : α) (w : ncword md.to_data) : c (of x * w).word (of' x * w.word) :=
begin
  induction w using ncword.cases_on_cons with y w hw,
  { exact c.refl _ },
  { rw [word_of_mul_cons, cons_word, ← mul_assoc],
    refine c.mul (c.symm $ _) (c.refl _),
    by_cases hr : md.r x y,
    { rw [md.cancel2_eq_self hr],
      exact c.refl _ },
    { exact hc x y hr } }
end

lemma con_word_cancel (c : con (free_monoid α))
  (hc : ∀ x y, ¬md.r x y → c (of' x * of' y) (md.cancel2 x y))
  (w : free_monoid α) : c (cancel md w).word w :=
begin
  induction w using free_monoid.rec_on with x w ihw,
  { exact c.refl _ },
  { rw [map_mul, cancel_of],
    exact c.trans (con_word_of_mul c hc x _) (c.mul (c.refl _) ihw) }
end

lemma is_least_con_ker_cancel :
  is_least {c : con (free_monoid α) | ∀ x y, c (of' x * of' y) (md.cancel2 x y)}
    (con.ker (cancel md)) :=
begin
  refine ⟨λ x y, _, λ c hc w₁ w₂ hw, _⟩,
  { rw [con.ker_rel, map_mul, cancel_of, cancel_of, ext_iff, ← word_of_mul_of, cancel_word] },
  { have := con_word_cancel c (λ x y _, hc x y),
    refine c.trans (c.symm $ this _) (c.trans _ $ this _),
    rw [(con.ker_rel _).1 hw],
    exact c.refl _ }
end

lemma con_ker_cancel :
  con.ker (cancel md) = Inf {c | ∀ x y, c (of' x * of' y) (md.cancel2 x y)} :=
(@is_least_con_ker_cancel α md).is_glb.Inf_eq.symm

def mk_hom {M : Type*} [monoid M] (f : α → M)
  (hc : ∀ ⦃x y⦄, ¬md.r x y → f x * f y = free_monoid.lift f (md.cancel2 x y)) :
  ncword md.to_data →* M :=
monoid_hom.of_mclosure_eq_top_left (free_monoid.lift f ∘ word) (mclosure_range_of _) rfl $
begin
  refine forall_range_iff.2 (λ x w, _),
  simp only [comp_app, ← map_mul, ← con.ker_rel, of_word],
  refine con_word_of_mul _ (λ x y hr, _) _ _,
  simp only [con.ker_rel, map_mul, lift_eval_of, hc hr]
end

structure group_data (α : Type*) extends monoid_data α :=
(inv : α → α)
(r_inv_inv : ∀ ⦃x y⦄, r x y → r (inv y) (inv x))
(cancel2_inv : ∀ x, cancel2 (inv x) x = 1)

variables {gd : group_data α}

instance (d : group_data α) : has_inv (ncword d.to_data) :=
⟨λ w, ⟨free_monoid.to_list.symm $ list.reverse $ (free_monoid.map d.inv w.word).to_list,
  list.chain'_reverse.2 (chain'_map_of_chain' _ d.r_inv_inv w.chain)⟩⟩

lemma inv_word (w : ncword gd.to_data) :
  (w⁻¹).word = to_list.symm (list.map gd.inv w.word.to_list).reverse :=
rfl

instance (d : group_data α) : group (ncword d.to_data) :=
{ mul_left_inv := λ w,
    begin
      induction w using ncword.rec_on_cons with x w hw ihw, { refl },
      rw [← word_smul, inv_word, cons_word, to_list_of_mul, map_cons, reverse_cons,
        of_list_append, of_list_singleton, ← inv_word, mul_smul, of_smul, cons_eq_mul,
        ← cancel2_smul, d.cancel2_inv, one_smul, word_smul, ihw]
    end,
  .. ncword.monoid _, .. ncword.has_inv _ }

end ncword
