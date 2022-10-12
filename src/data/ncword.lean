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

structure add_ncword.data (α : Type*) :=
(cancel2 : α → α → free_add_monoid α)
(r : α → α → Prop)
(cancel2_eq_self : ∀ {x y}, r x y → cancel2 x y = of x + of y)
(chain'_r_cancel2 : ∀ {x y}, ¬r x y → chain' r (cancel2 x y).to_list)
(r_last'_cancel2 : ∀ {x y}, ¬r x y → ∀ {y'}, y' ∈ (cancel2 x y).to_list.last' →
  ∀ {z}, r y z → r y' z)

@[to_additive add_ncword.data]
structure mul_ncword.data (α : Type*) :=
(cancel2 : α → α → free_monoid α)
(r : α → α → Prop)
(cancel2_eq_self : ∀ {x y}, r x y → cancel2 x y = of x * of y)
(chain'_r_cancel2 : ∀ x y, ¬r x y → chain' r (cancel2 x y).to_list)
(r_last'_cancel2 : ∀ {x y}, ¬r x y → ∀ {y'}, y' ∈ (cancel2 x y).to_list.last' →
  ∀ {z}, r y z → r y' z)

@[ext] structure add_ncword (d : add_ncword.data α) :=
(word : free_add_monoid α)
(chain : chain' d.r word.to_list)

@[ext, to_additive]
structure mul_ncword (d : mul_ncword.data α) :=
(word : free_monoid α)
(chain : chain' d.r word.to_list)


namespace mul_ncword

variables {d : data α}

@[to_additive] instance [decidable_eq α] : decidable_eq (mul_ncword d) :=
λ x y, decidable_of_iff _ (ext_iff x y).symm

@[to_additive, simps]
def of (x : α) : mul_ncword d := ⟨of x, chain'_singleton _⟩

@[to_additive] lemma word_mk (w hw) : word (mk w hw : mul_ncword d) = w := rfl

@[to_additive] instance : has_one (mul_ncword d) := ⟨⟨1, list.chain'_nil⟩⟩

@[simp, to_additive] lemma one_word : (1 : mul_ncword d).word = 1 := rfl

@[to_additive] lemma chain'_r_cancel2 (x y : α) : chain' d.r (d.cancel2 x y).to_list :=
flip classical.by_cases (d.chain'_r_cancel2 x y) $ λ hr, by simp [d.cancel2_eq_self, hr]

@[to_additive] lemma chain'_r_cancel2_mul (x y : α) (w : free_monoid α)
  (h : chain' d.r (of' y * w).to_list) : chain' d.r (d.cancel2 x y * w).to_list :=
begin
  by_cases hr : d.r x y,
  { rw [d.cancel2_eq_self hr],
    exact h.cons hr },
  rw [free_monoid.to_list_of_mul, list.chain'_cons'] at h,
  refine list.chain'.append (chain'_r_cancel2 _ _) h.2 _,
  exact λ x' hx' y' hy', d.r_last'_cancel2 hr hx' (h.1 _ hy')
end

@[to_additive, simps]
def cons (x : α) (w : mul_ncword d) (h : chain' d.r (of' x * word w).to_list) : mul_ncword d :=
⟨of' x * word w, h⟩

@[simp, to_additive]
lemma mk_cons (x : α) (l : free_monoid α) (h : chain' d.r (of' x * l).to_list) :
  mk (of' x * l) h = cons x (mk l h.tail) h :=
rfl

@[simp, to_additive]
lemma cons_one (x : α) (h : chain' d.r (of' x * 1).to_list := chain'_singleton _) :
  cons x 1 h = of x :=
rfl

@[elab_as_eliminator, to_additive]
def rec_on_cons {C : mul_ncword d → Sort*} (w : mul_ncword d) (h₁ : C 1)
  (hcons : ∀ {x} {w : mul_ncword d} (h : chain' d.r (of' x * w.word).to_list),
    C w → C (cons x w h)) :
  C w :=
mul_ncword.rec_on w $ λ l, free_monoid.rec_on l (λ _, h₁) $ λ x w ihw hw, hcons _ (ihw hw.tail)

@[elab_as_eliminator, to_additive]
def cases_on_cons {C : mul_ncword d → Sort*} (w : mul_ncword d) (h₁ : C 1)
  (hcons : ∀ {x} {w : mul_ncword d} (h : chain' d.r (of' x * w.word).to_list), C (cons x w h)) :
  C w :=
rec_on_cons w h₁ (λ x w h _, hcons h)

@[to_additive] instance : mul_action (free_monoid α) (mul_ncword d) :=
free_monoid.mk_mul_action $ λ x w, mul_ncword.cases_on_cons w (of x)
  (λ y w' h, ⟨d.cancel2 x y * w'.word, chain'_r_cancel2_mul _ _ _ h⟩)

@[to_additive] instance : has_mul (mul_ncword d) := ⟨λ w₁ w₂, w₁.word • w₂⟩

@[simp, to_additive] lemma word_smul (w₁ w₂ : mul_ncword d) : w₁.word • w₂ = w₁ * w₂ := rfl
@[simp, to_additive] lemma of_smul (x : α) (w : mul_ncword d) : of' x • w = of x * w := rfl

@[to_additive] lemma mk_word (w : mul_ncword d) (h : chain' d.r w.word.to_list := w.2) :
  mk w.word h = w :=
ext _ _ rfl

@[to_additive]
lemma of_mul_cons (x : α) {y w} (hyw : chain' d.r (of' y * word w).to_list) :
  of x * cons y w hyw = ⟨d.cancel2 x y * word w, chain'_r_cancel2_mul _ _ _ hyw⟩ :=
rfl

@[simp, to_additive]
lemma word_of_mul_cons (x : α) {y w} (hyw : chain' d.r (of' y * word w).to_list) :
  (of x * cons y w hyw).word = d.cancel2 x y * word w :=
rfl

@[simp, to_additive]
lemma word_of_mul_of (x y : α) :
  (of x * of y : mul_ncword d).word = d.cancel2 x y :=
mul_one (d.cancel2 x y)

@[to_additive]
lemma cons_eq_mul {x : α} {w : mul_ncword d} (h : chain' d.r (of' x * word w).to_list) :
  cons x w h = of x * w :=
begin
  induction w using mul_ncword.cases_on_cons with y w ihw,
  { refl },
  { ext1, rw [word_of_mul_cons, d.cancel2_eq_self h.rel_head, cons_word, cons_word, mul_assoc] }
end

@[to_additive]
lemma cons_mul {x} {w} (h : chain' d.r (of' x * word w).to_list) (w' : mul_ncword d) :
  cons x w h * w' = of x * (w * w') :=
rfl

@[to_additive] lemma smul_eq_of_chain' {w₁ : free_monoid α} {w₂ : mul_ncword d}
  (h : chain' d.r (w₁ * w₂.word).to_list) :
  w₁ • w₂ = mk (w₁ * w₂.word) h :=
begin
  induction w₁ using free_monoid.rec_on with x w ihw, { cases w₂, refl },
  rw [mul_smul, ihw h.tail, of_smul, ← cons_eq_mul],
  refl
end

@[to_additive]
instance : mul_one_class (mul_ncword d) :=
{ one_mul := λ ⟨w, hw⟩, rfl,
  mul_one := λ w, ext _ _ $
    begin
      rw [← word_smul, smul_eq_of_chain', word_mk, one_word, mul_one],
      rw [one_word, mul_one],
      exact w.2
    end,
  .. mul_ncword.has_one, .. mul_ncword.has_mul }

structure _root_.add_ncword.add_monoid_data (α : Type*) extends add_ncword.data α :=
(cancel2_vadd : ∀ x y, ¬r x y → ∀ {z : α} {w : add_ncword to_data} h, ¬r y z →
  to_data.cancel2 x y +ᵥ w.cons z h = add_ncword.of x + (add_ncword.of y + w.cons z h))

@[to_additive]
structure monoid_data (α : Type*) extends data α :=
(cancel2_smul : ∀ x y, ¬r x y → ∀ {z : α} {w : mul_ncword to_data} h, ¬r y z →
  to_data.cancel2 x y • cons z w h = of x * (of y * cons z w h))

@[to_additive]
lemma cancel2_smul {d : monoid_data α} (x y : α) (w : mul_ncword d.to_data) :
  d.cancel2 x y • w = of x * (of y * w) :=
begin
  by_cases hr : d.r x y,
  { rw [d.cancel2_eq_self hr, mul_smul, of_smul, of_smul] },
  { induction w using mul_ncword.cases_on_cons with z w hzw,
    { rw [mul_one, ← word_of_mul_of, word_smul, mul_one] },
    { by_cases hyz : d.r y z,
      { rw [smul_eq_of_chain', ← @cons_eq_mul _ _ y, of_mul_cons],
        exact hzw.cons hyz },
      { exact d.cancel2_smul _ _ hr _ hyz } } }
end

@[to_additive] instance (d : monoid_data α) :
  is_scalar_tower (free_monoid α) (mul_ncword d.to_data) (mul_ncword d.to_data) :=
is_scalar_tower.of_mclosure_eq_top free_monoid.closure_range_of $ forall_range_iff.2 $ λ x w₁ w₂,
  begin
    rw [smul_eq_mul, smul_eq_mul, of_smul, of_smul],
    induction w₁ using mul_ncword.rec_on_cons with y w₁ hyw₁ ihw₁ generalizing x,
    { rw [one_mul, mul_one], },
    { rw [← word_smul, word_of_mul_cons, mul_smul, word_smul, cancel2_smul, cons_mul] }
  end

@[to_additive]
instance (d : monoid_data α) : monoid (mul_ncword d.to_data) :=
{ mul_assoc := λ x y z, smul_mul_assoc x.word y z,
  .. mul_ncword.mul_one_class }

variable {md : monoid_data α}

@[to_additive] def cancel (d : monoid_data α) : free_monoid α →* mul_ncword d.to_data :=
free_monoid.lift of

@[simp, to_additive] lemma cancel_of (x : α) : cancel md (of' x) = of x := rfl

@[to_additive] lemma cancel_eq_smul_one (l : free_monoid α) : cancel md l = l • 1 :=
by { rw [cancel, free_monoid.lift_apply, list.prod_eq_foldr, foldr_map], refl }

@[simp, to_additive] lemma cancel_word (w : mul_ncword md.to_data) : cancel md w.word = w :=
by rw [cancel_eq_smul_one, word_smul, mul_one]

@[to_additive] lemma cancel_surjective : surjective (cancel md) := left_inverse.surjective cancel_word

@[simp, to_additive] lemma mclosure_range_of (d : monoid_data α) :
  submonoid.closure (range (of : α → mul_ncword d.to_data)) = ⊤ :=
top_unique $ λ g hg, cancel_word g ▸ submonoid.list_prod_mem _
  (forall_mem_map_iff.2 $ λ x hx, submonoid.subset_closure $ mem_range_self _)

@[to_additive] lemma con_word_of_mul (c : con (free_monoid α))
  (hc : ∀ x y, ¬md.r x y → c (of' x * of' y) (md.cancel2 x y))
  (x : α) (w : mul_ncword md.to_data) : c (of x * w).word (of' x * w.word) :=
begin
  induction w using mul_ncword.cases_on_cons with y w hw,
  { exact c.refl _ },
  { rw [word_of_mul_cons, cons_word, ← mul_assoc],
    refine c.mul (c.symm $ _) (c.refl _),
    by_cases hr : md.r x y,
    { rw [md.cancel2_eq_self hr],
      exact c.refl _ },
    { exact hc x y hr } }
end

@[to_additive] lemma con_word_cancel (c : con (free_monoid α))
  (hc : ∀ x y, ¬md.r x y → c (of' x * of' y) (md.cancel2 x y))
  (w : free_monoid α) : c (cancel md w).word w :=
begin
  induction w using free_monoid.rec_on with x w ihw,
  { exact c.refl _ },
  { rw [map_mul, cancel_of],
    exact c.trans (con_word_of_mul c hc x _) (c.mul (c.refl _) ihw) }
end

@[to_additive] lemma is_least_con_ker_cancel :
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

@[to_additive] lemma con_ker_cancel :
  con.ker (cancel md) = Inf {c | ∀ x y, c (of' x * of' y) (md.cancel2 x y)} :=
(@is_least_con_ker_cancel α md).is_glb.Inf_eq.symm

@[to_additive] def mk_hom {M : Type*} [monoid M] (f : α → M)
  (hc : ∀ ⦃x y⦄, ¬md.r x y → f x * f y = free_monoid.lift f (md.cancel2 x y)) :
  mul_ncword md.to_data →* M :=
monoid_hom.of_mclosure_eq_top_left (free_monoid.lift f ∘ word) (mclosure_range_of _) rfl $
begin
  refine forall_range_iff.2 (λ x w, _),
  simp only [comp_app, ← map_mul, ← con.ker_rel, of_word],
  refine con_word_of_mul _ (λ x y hr, _) _ _,
  simp only [con.ker_rel, map_mul, lift_eval_of, hc hr]
end

structure _root_.add_ncword.add_group_data (α : Type*)
  extends add_ncword.add_monoid_data α :=
(neg : α → α)
(r_neg_neg : ∀ ⦃x y⦄, r x y → r (neg y) (neg x))
(cancel2_neg : ∀ x, cancel2 (neg x) x = 0)

@[to_additive] structure group_data (α : Type*) extends monoid_data α :=
(inv : α → α)
(r_inv_inv : ∀ ⦃x y⦄, r x y → r (inv y) (inv x))
(cancel2_inv : ∀ x, cancel2 (inv x) x = 1)

variables {gd : group_data α}

@[to_additive] instance (d : group_data α) : has_inv (mul_ncword d.to_data) :=
⟨λ w, ⟨free_monoid.of_list $ list.reverse $ (free_monoid.map d.inv w.word).to_list,
  list.chain'_reverse.2 (chain'_map_of_chain' _ d.r_inv_inv w.chain)⟩⟩

@[to_additive] lemma inv_word (w : mul_ncword gd.to_data) :
  (w⁻¹).word = of_list (list.map gd.inv w.word.to_list).reverse :=
rfl

@[to_additive] instance (d : group_data α) : group (mul_ncword d.to_data) :=
{ mul_left_inv := λ w,
    begin
      induction w using mul_ncword.rec_on_cons with x w hw ihw, { refl },
      rw [← word_smul, inv_word, cons_word, to_list_of_mul, map_cons, reverse_cons,
        of_list_append, of_list_singleton, ← inv_word, mul_smul, of_smul, cons_eq_mul,
        ← cancel2_smul, d.cancel2_inv, one_smul, word_smul, ihw]
    end,
  .. mul_ncword.monoid _, .. mul_ncword.has_inv _ }

end mul_ncword
