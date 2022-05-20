/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Joachim Breitner
-/
import algebra.free_monoid
import group_theory.congruence
import group_theory.is_free_group
import group_theory.subgroup.pointwise
import data.list.chain
import set_theory.cardinal.ordinal
/-!
# The free product of groups or monoids

Given an `ι`-indexed family `M` of monoids, we define their free product (categorical coproduct)
`free_product M`. When `ι` and all `M i` have decidable equality, the free product bijects with the
type `word M` of reduced words. This bijection is constructed by defining an action of
`free_product M` on `word M`.

When `M i` are all groups, `free_product M` is also a group (and the coproduct in the category of
groups).

## Main definitions

- `free_product M`: the free product, defined as a quotient of a free monoid.
- `free_product.of {i} : M i →* free_product M`.
- `free_product.lift : (Π {i}, M i →* N) ≃ (free_product M →* N)`: the universal property.
- `free_product.word M`: the type of reduced words.
- `free_product.word.equiv M : free_product M ≃ word M`.
- `free_product.neword M i j`: an inductive description of non-empty words with first letter from
  `M i` and last letter from `M j`, together with an API (`singleton`, `append`, `head`, `tail`,
  `to_word`, `prod`, `inv`). Used in the proof of the Ping-Pong-lemma.
- `free_product.lift_injective_of_ping_pong`: The Ping-Pong-lemma, proving injectivity of the
  `lift`. See the documentation of that theorem for more information.

## Remarks

There are many answers to the question "what is the free product of a family `M` of monoids?", and
they are all equivalent but not obviously equivalent. We provide two answers. The first, almost
tautological answer is given by `free_product M`, which is a quotient of the type of words in the
alphabet `Σ i, M i`. It's straightforward to define and easy to prove its universal property. But
this answer is not completely satisfactory, because it's difficult to tell when two elements
`x y : free_product M` are distinct since `free_product M` is defined as a quotient.

The second, maximally efficient answer is given by `word M`. An element of `word M` is a word in the
alphabet `Σ i, M i`, where the letter `⟨i, 1⟩` doesn't occur and no adjacent letters share an index
`i`. Since we only work with reduced words, there is no need for quotienting, and it is easy to tell
when two elements are distinct. However it's not obvious that this is even a monoid!

We prove that every element of `free_product M` can be represented by a unique reduced word, i.e.
`free_product M` and `word M` are equivalent types. This means that `word M` can be given a monoid
structure, and it lets us tell when two elements of `free_product M` are distinct.

There is also a completely tautological, maximally inefficient answer given by
`algebra.category.Mon.colimits`. Whereas `free_product M` at least ensures that (any instance of)
associativity holds by reflexivity, in this answer associativity holds because of quotienting. Yet
another answer, which is constructively more satisfying, could be obtained by showing that
`free_product.rel` is confluent.

## References

[van der Waerden, *Free products of groups*][MR25465]

-/

variables {ι : Type*} (M : Π i : ι, Type*) [Π i, monoid (M i)]

/-- A relation on the free monoid on alphabet `Σ i, M i`, relating `⟨i, 1⟩` with `1` and
`⟨i, x⟩ * ⟨i, y⟩` with `⟨i, x * y⟩`. -/
inductive free_product.rel : free_monoid (Σ i, M i) → free_monoid (Σ i, M i) → Prop
| of_one (i : ι) : free_product.rel (free_monoid.of ⟨i, 1⟩) 1
| of_mul {i : ι} (x y : M i) : free_product.rel (free_monoid.of ⟨i, x⟩ * free_monoid.of ⟨i, y⟩)
  (free_monoid.of ⟨i, x * y⟩)

/-- The free product (categorical coproduct) of an indexed family of monoids. -/
@[derive [monoid, inhabited]]
def free_product : Type* := (con_gen (free_product.rel M)).quotient

namespace free_product

/-- The type of reduced words. A reduced word cannot contain a letter `1`, and no two adjacent
letters can come from the same summand. -/
@[ext] structure word :=
(to_list : list (Σ i, M i))
(ne_one : ∀ l ∈ to_list, sigma.snd l ≠ 1)
(chain_ne : to_list.chain' (λ l l', sigma.fst l ≠ sigma.fst l'))

variable {M}

/-- The inclusion of a summand into the free product. -/
def of {i : ι} : M i →* free_product M :=
{ to_fun   := λ x, con.mk' _ (free_monoid.of $ sigma.mk i x),
  map_one' := (con.eq _).mpr (con_gen.rel.of _ _ (free_product.rel.of_one i)),
  map_mul' := λ x y, eq.symm $ (con.eq _).mpr (con_gen.rel.of _ _ (free_product.rel.of_mul x y)) }

lemma of_apply {i} (m : M i) : of m = con.mk' _ (free_monoid.of $ sigma.mk i m) := rfl

variables {N : Type*} [monoid N]

/-- See note [partially-applied ext lemmas]. -/
@[ext] lemma ext_hom (f g : free_product M →* N) (h : ∀ i, f.comp (of : M i →* _) = g.comp of) :
  f = g :=
(monoid_hom.cancel_right con.mk'_surjective).mp $ free_monoid.hom_eq $ λ ⟨i, x⟩,
  by rw [monoid_hom.comp_apply, monoid_hom.comp_apply, ←of_apply,
    ←monoid_hom.comp_apply, ←monoid_hom.comp_apply, h]

/-- A map out of the free product corresponds to a family of maps out of the summands. This is the
universal property of the free product, charaterizing it as a categorical coproduct. -/
@[simps symm_apply]
def lift : (Π i, M i →* N) ≃ (free_product M →* N) :=
{ to_fun := λ fi, con.lift _ (free_monoid.lift $ λ p : Σ i, M i, fi p.fst p.snd) $ con.con_gen_le
    begin
      simp_rw [con.rel_eq_coe, con.ker_rel],
      rintros _ _ (i | ⟨i, x, y⟩),
      { change free_monoid.lift _ (free_monoid.of _) = free_monoid.lift _ 1,
        simp only [monoid_hom.map_one, free_monoid.lift_eval_of], },
      { change free_monoid.lift _ (free_monoid.of _ * free_monoid.of _) =
          free_monoid.lift _ (free_monoid.of _),
        simp only [monoid_hom.map_mul, free_monoid.lift_eval_of], }
    end,
  inv_fun := λ f i, f.comp of,
  left_inv := by { intro fi, ext i x,
    rw [monoid_hom.comp_apply, of_apply, con.lift_mk', free_monoid.lift_eval_of], },
  right_inv := by { intro f, ext i x,
    simp only [monoid_hom.comp_apply, of_apply, con.lift_mk', free_monoid.lift_eval_of], } }

@[simp] lemma lift_of {N} [monoid N] (fi : Π i, M i →* N) {i} (m : M i) :
  lift fi (of m) = fi i m :=
by conv_rhs { rw [←lift.symm_apply_apply fi, lift_symm_apply, monoid_hom.comp_apply] }

@[elab_as_eliminator]
lemma induction_on {C : free_product M → Prop}
  (m : free_product M)
  (h_one : C 1)
  (h_of : ∀ (i) (m : M i), C (of m))
  (h_mul : ∀ (x y), C x → C y → C (x * y)) :
  C m :=
begin
  let S : submonoid (free_product M) := submonoid.mk (set_of C) h_mul h_one,
  convert subtype.prop (lift (λ i, of.cod_mrestrict S (h_of i)) m),
  change monoid_hom.id _ m = S.subtype.comp _ m,
  congr,
  ext,
  simp [monoid_hom.cod_mrestrict],
end

lemma of_left_inverse [decidable_eq ι] (i : ι) :
  function.left_inverse (lift $ pi.mul_single i (monoid_hom.id (M i))) of :=
λ x, by simp only [lift_of, pi.mul_single_eq_same, monoid_hom.id_apply]

lemma of_injective (i : ι) : function.injective ⇑(of : M i →* _) :=
by { classical, exact (of_left_inverse i).injective }

lemma lift_mrange_le {N} [monoid N] (f : Π i, M i →* N) {s : submonoid N}
  (h : ∀ i, (f i).mrange ≤ s) : (lift f).mrange ≤ s :=
begin
  rintros _ ⟨x, rfl⟩,
  induction x using free_product.induction_on with i x x y hx hy,
  { exact s.one_mem, },
  { simp only [lift_of, set_like.mem_coe], exact h i (set.mem_range_self x), },
  { simp only [map_mul, set_like.mem_coe], exact s.mul_mem hx hy, },
end

lemma mrange_eq_supr {N} [monoid N] (f : Π i, M i →* N) :
  (lift f).mrange = ⨆ i, (f i).mrange :=
begin
  apply le_antisymm (lift_mrange_le f (λ i, le_supr _ i)),
  apply supr_le _,
  rintros i _ ⟨x, rfl⟩,
  exact ⟨of x, by simp only [lift_of]⟩
end

section group

variables (G : ι → Type*) [Π i, group (G i)]

instance : has_inv (free_product G) :=
{ inv := mul_opposite.unop ∘
    lift (λ i, (of : G i →* _).op.comp (mul_equiv.inv' (G i)).to_monoid_hom) }

lemma inv_def (x : free_product G) : x⁻¹ = mul_opposite.unop
  (lift (λ i, (of : G i →* _).op.comp (mul_equiv.inv' (G i)).to_monoid_hom) x) := rfl

instance : group (free_product G) :=
{ mul_left_inv := begin
    intro m,
    rw inv_def,
    apply m.induction_on,
    { rw [monoid_hom.map_one, mul_opposite.unop_one, one_mul], },
    { intros i m, change of m⁻¹ * of m = 1, rw [←of.map_mul, mul_left_inv, of.map_one], },
    { intros x y hx hy,
      rw [monoid_hom.map_mul, mul_opposite.unop_mul, mul_assoc, ← mul_assoc _ x y, hx,
        one_mul, hy], },
  end,
  ..free_product.has_inv G,
  ..free_product.monoid G }

lemma lift_range_le {N} [group N] (f : Π i, G i →* N) {s : subgroup N}
  (h : ∀ i, (f i).range ≤ s) : (lift f).range ≤ s :=
begin
  rintros _ ⟨x, rfl⟩,
  induction x using free_product.induction_on with i x x y hx hy,
  { exact s.one_mem, },
  { simp only [lift_of, set_like.mem_coe], exact h i (set.mem_range_self x), },
  { simp only [map_mul, set_like.mem_coe], exact s.mul_mem hx hy, },
end

lemma range_eq_supr {N} [group N] (f : Π i, G i →* N) :
  (lift f).range = ⨆ i, (f i).range :=
begin
  apply le_antisymm (lift_range_le _ f (λ i, le_supr _ i)),
  apply supr_le _,
  rintros i _ ⟨x, rfl⟩,
  exact ⟨of x, by simp only [lift_of]⟩
end

end group

namespace word

/-- The empty reduced word. -/
def empty : word M := { to_list := [], ne_one := λ _, false.elim, chain_ne := list.chain'_nil }

instance : inhabited (word M) := ⟨empty⟩

/-- A reduced word determines an element of the free product, given by multiplication. -/
def prod (w : word M) : free_product M :=
list.prod (w.to_list.map $ λ l, of l.snd)

@[simp] lemma prod_empty : prod (empty : word M) = 1 := rfl

/-- `fst_idx w` is `some i` if the first letter of `w` is `⟨i, m⟩` with `m : M i`. If `w` is empty
then it's `none`. -/
def fst_idx (w : word M) : option ι := w.to_list.head'.map sigma.fst

lemma fst_idx_ne_iff {w : word M} {i} :
  fst_idx w ≠ some i ↔ ∀ l ∈ w.to_list.head', i ≠ sigma.fst l :=
not_iff_not.mp $ by simp [fst_idx]

variable (M)

/-- Given an index `i : ι`, `pair M i` is the type of pairs `(head, tail)` where `head : M i` and
`tail : word M`, subject to the constraint that first letter of `tail` can't be `⟨i, m⟩`.
By prepending `head` to `tail`, one obtains a new word. We'll show that any word can be uniquely
obtained in this way. -/
@[ext] structure pair (i : ι) :=
(head : M i)
(tail : word M)
(fst_idx_ne : fst_idx tail ≠ some i)

instance (i : ι) : inhabited (pair M i) := ⟨⟨1, empty, by tauto⟩⟩

variable {M}

variables [∀ i, decidable_eq (M i)]

/-- Given a pair `(head, tail)`, we can form a word by prepending `head` to `tail`, except if `head`
is `1 : M i` then we have to just return `word` since we need the result to be reduced. -/
def rcons {i} (p : pair M i) : word M :=
if h : p.head = 1 then p.tail
else { to_list  := ⟨i, p.head⟩ :: p.tail.to_list,
       ne_one   := by { rintros l (rfl | hl), exact h, exact p.tail.ne_one l hl },
       chain_ne := p.tail.chain_ne.cons' (fst_idx_ne_iff.mp p.fst_idx_ne) }

/-- Given a word of the form `⟨l :: ls, h1, h2⟩`, we can form a word of the form `⟨ls, _, _⟩`,
dropping the first letter. -/
private def mk_aux {l} (ls : list (Σ i, M i)) (h1 : ∀ l' ∈ l :: ls, sigma.snd l' ≠ 1)
  (h2 : (l :: ls).chain' _) : word M :=
⟨ls, λ l' hl, h1 _ (list.mem_cons_of_mem _ hl), h2.tail⟩

lemma cons_eq_rcons {i} {m : M i} {ls h1 h2} :
  word.mk (⟨i, m⟩ :: ls) h1 h2 = rcons ⟨m, mk_aux ls h1 h2, fst_idx_ne_iff.mpr h2.rel_head'⟩ :=
by { rw [rcons, dif_neg], refl, exact h1 ⟨i, m⟩ (ls.mem_cons_self _) }

@[simp] lemma prod_rcons {i} (p : pair M i) :
  prod (rcons p) = of p.head * prod p.tail :=
if hm : p.head = 1 then by rw [rcons, dif_pos hm, hm, monoid_hom.map_one, one_mul]
else by rw [rcons, dif_neg hm, prod, list.map_cons, list.prod_cons, prod]

lemma rcons_inj {i} : function.injective (rcons : pair M i → word M) :=
begin
  rintros ⟨m, w, h⟩ ⟨m', w', h'⟩ he,
  by_cases hm : m = 1;
  by_cases hm' : m' = 1,
  { simp only [rcons, dif_pos hm, dif_pos hm'] at he, cc, },
  { exfalso, simp only [rcons, dif_pos hm, dif_neg hm'] at he, rw he at h, exact h rfl },
  { exfalso, simp only [rcons, dif_pos hm', dif_neg hm] at he, rw ←he at h', exact h' rfl, },
  { have : m = m' ∧ w.to_list = w'.to_list,
    { simpa only [rcons, dif_neg hm, dif_neg hm', true_and, eq_self_iff_true, subtype.mk_eq_mk,
      heq_iff_eq, ←subtype.ext_iff_val] using he },
    rcases this with ⟨rfl, h⟩,
    congr, exact word.ext _ _ h, }
end

variable [decidable_eq ι]

/-- Given `i : ι`, any reduced word can be decomposed into a pair `p` such that `w = rcons p`. -/
-- This definition is computable but not very nice to look at. Thankfully we don't have to inspect
-- it, since `rcons` is known to be injective.
private def equiv_pair_aux (i) : Π w : word M, { p : pair M i // rcons p = w }
| w@⟨[], _, _⟩             := ⟨⟨1, w, by rintro ⟨⟩⟩, dif_pos rfl⟩
| w@⟨⟨j, m⟩ :: ls, h1, h2⟩ := if ij : i = j then
  { val := { head := ij.symm.rec m,
             tail := mk_aux ls h1 h2,
             fst_idx_ne := by cases ij; exact fst_idx_ne_iff.mpr h2.rel_head' },
    property := by cases ij; exact cons_eq_rcons.symm }
else ⟨⟨1, w, (option.some_injective _).ne (ne.symm ij)⟩, dif_pos rfl⟩

/-- The equivalence between words and pairs. Given a word, it decomposes it as a pair by removing
the first letter if it comes from `M i`. Given a pair, it prepends the head to the tail. -/
def equiv_pair (i) : word M ≃ pair M i :=
{ to_fun := λ w, (equiv_pair_aux i w).val,
  inv_fun := rcons,
  left_inv := λ w, (equiv_pair_aux i w).property,
  right_inv := λ p, rcons_inj (equiv_pair_aux i _).property }

lemma equiv_pair_symm (i) (p : pair M i) : (equiv_pair i).symm p = rcons p := rfl

lemma equiv_pair_eq_of_fst_idx_ne {i} {w : word M} (h : fst_idx w ≠ some i) :
  equiv_pair i w = ⟨1, w, h⟩ :=
(equiv_pair i).apply_eq_iff_eq_symm_apply.mpr $ eq.symm (dif_pos rfl)

instance summand_action (i) : mul_action (M i) (word M) :=
{ smul     := λ m w, rcons { head := m * (equiv_pair i w).head, ..equiv_pair i w },
  one_smul := λ w, by { simp_rw [one_mul], apply (equiv_pair i).symm_apply_eq.mpr, ext; refl },
  mul_smul := λ m m' w, by simp only [mul_assoc, ←equiv_pair_symm, equiv.apply_symm_apply], }

instance : mul_action (free_product M) (word M) :=
mul_action.of_End_hom (lift (λ i, mul_action.to_End_hom))

lemma of_smul_def (i) (w : word M) (m : M i) :
  of m • w = rcons { head := m * (equiv_pair i w).head, ..equiv_pair i w } := rfl

lemma cons_eq_smul {i} {m : M i} {ls h1 h2} :
  word.mk (⟨i, m⟩ :: ls) h1 h2 = of m • mk_aux ls h1 h2 :=
by rw [cons_eq_rcons, of_smul_def, equiv_pair_eq_of_fst_idx_ne _]; simp only [mul_one]

lemma smul_induction {C : word M → Prop}
  (h_empty : C empty)
  (h_smul : ∀ i (m : M i) w, C w → C (of m • w))
  (w : word M) : C w :=
begin
  cases w with ls h1 h2,
  induction ls with l ls ih,
  { exact h_empty },
  cases l with i m,
  rw cons_eq_smul,
  exact h_smul _ _ _ (ih _ _),
end

@[simp] lemma prod_smul (m) : ∀ w : word M, prod (m • w) = m * prod w :=
begin
  apply m.induction_on,
  { intro, rw [one_smul, one_mul] },
  { intros, rw [of_smul_def, prod_rcons, of.map_mul, mul_assoc, ←prod_rcons,
      ←equiv_pair_symm, equiv.symm_apply_apply] },
  { intros x y hx hy w, rw [mul_smul, hx, hy, mul_assoc] },
end

/-- Each element of the free product corresponds to a unique reduced word. -/
def equiv : free_product M ≃ word M :=
{ to_fun := λ m, m • empty,
  inv_fun := λ w, prod w,
  left_inv := λ m, by dsimp only; rw [prod_smul, prod_empty, mul_one],
  right_inv := begin
    apply smul_induction,
    { dsimp only, rw [prod_empty, one_smul], },
    { dsimp only, intros i m w ih, rw [prod_smul, mul_smul, ih], },
  end }

instance : decidable_eq (word M) := function.injective.decidable_eq word.ext
instance : decidable_eq (free_product M) := word.equiv.decidable_eq

end word

variable (M)

/-- A `neword M i j` is a representation of a non-empty reduced words where the first letter comes
from `M i` and the last letter comes from `M j`. It can be constructed from singletons and via
concatentation, and thus provides a useful induction principle. -/
@[nolint has_inhabited_instance]
inductive neword : ι → ι → Type (max u_1 u_2)
| singleton : ∀ {i} (x : M i) (hne1 : x ≠ 1), neword i i
| append : ∀ {i j k l} (w₁ : neword i j) (hne : j ≠ k) (w₂ : neword k l), neword i l
variable {M}

namespace neword

open word

/-- The list represented by a given `neword` -/
@[simp]
def to_list : Π {i j} (w : neword M i j), list (Σ i, M i)
| i _ (singleton x hne1) := [⟨i, x⟩]
| _ _ (append w₁ hne w₂) := w₁.to_list ++ w₂.to_list

lemma to_list_ne_nil {i j} (w : neword M i j) : w.to_list ≠ list.nil :=
by { induction w, { rintros ⟨rfl⟩ }, { apply list.append_ne_nil_of_ne_nil_left, assumption } }

/--  The first letter of a `neword` -/
@[simp]
def head : Π {i j} (w : neword M i j), M i
| i _ (singleton x hne1) := x
| _ _ (append w₁ hne w₂) := w₁.head

/--  The last letter of a `neword` -/
@[simp]
def last : Π {i j} (w : neword M i j), M j
| i _ (singleton x hne1) := x
| _ _ (append w₁ hne w₂) := w₂.last

@[simp]
lemma to_list_head' {i j} (w : neword M i j) :
  w.to_list.head' = option.some ⟨i, w.head⟩ :=
begin
  rw ← option.mem_def,
  induction w,
  { rw option.mem_def, reflexivity, },
  { exact list.head'_append w_ih_w₁, },
end

@[simp]
lemma to_list_last' {i j} (w : neword M i j) :
  w.to_list.last' = option.some ⟨j, w.last⟩ :=
begin
  rw ← option.mem_def,
  induction w,
  { rw option.mem_def, reflexivity, },
  { exact list.last'_append w_ih_w₂, },
end

/-- The `word M` represented by a `neword M i j` -/
def to_word {i j} (w : neword M i j) : word M :=
{ to_list := w.to_list,
  ne_one :=
  begin
    induction w,
    { rintros ⟨k,x⟩ ⟨rfl, rfl⟩,
      exact w_hne1,
      exfalso, apply H, },
    { intros l h,
      simp only [to_list, list.mem_append] at h,
      cases h,
      { exact w_ih_w₁ _ h, },
      { exact w_ih_w₂ _ h, }, },
  end,
  chain_ne := begin
    induction w,
    { exact list.chain'_singleton _, },
    { apply list.chain'.append w_ih_w₁ w_ih_w₂,
      intros x hx y hy,
      rw [w_w₁.to_list_last', option.mem_some_iff] at hx,
      rw [w_w₂.to_list_head', option.mem_some_iff] at hy,
      subst hx, subst hy,
      exact w_hne, },
  end, }

/-- Every nonempty `word M` can be constructed as a `neword M i j` -/
lemma of_word (w : word M) (h : w ≠ empty) :
  ∃ i j (w' : neword M i j), w'.to_word = w :=
begin
  suffices : ∃ i j (w' : neword M i j), w'.to_word.to_list = w.to_list,
  { obtain ⟨i, j, w, h⟩ := this, refine ⟨i, j, w, _⟩, ext, rw h, },
  cases w with l hnot1 hchain,
  induction l with x l hi,
  { contradiction, },
  { rw list.forall_mem_cons at hnot1,
    cases l with y l,
    { refine ⟨x.1, x.1, singleton x.2 hnot1.1, _ ⟩,
      simp [to_word], },
    { rw list.chain'_cons at hchain,
      specialize hi hnot1.2 hchain.2 (by rintros ⟨rfl⟩),
      obtain ⟨i, j, w', hw' : w'.to_list = y :: l⟩ := hi,
      obtain rfl : y = ⟨i, w'.head⟩, by simpa [hw'] using w'.to_list_head',
      refine ⟨x.1, j, append (singleton x.2 hnot1.1) hchain.1 w', _⟩,
      { simpa [to_word] using hw', } } }
end

/-- A non-empty reduced word determines an element of the free product, given by multiplication. -/
def prod {i j} (w : neword M i j) := w.to_word.prod

@[simp]
lemma singleton_head {i} (x : M i) (hne_one : x ≠ 1) :
  (singleton x hne_one).head = x := rfl

@[simp]
lemma singleton_last {i} (x : M i) (hne_one : x ≠ 1) :
  (singleton x hne_one).last = x := rfl

@[simp] lemma prod_singleton {i} (x : M i) (hne_one : x ≠ 1) :
  (singleton x hne_one).prod = of x :=
by simp [to_word, prod, word.prod]

@[simp]
lemma append_head {i j k l} {w₁ : neword M i j} {hne : j ≠ k} {w₂ : neword M k l} :
  (append w₁ hne w₂).head = w₁.head := rfl

@[simp]
lemma append_last {i j k l} {w₁ : neword M i j} {hne : j ≠ k} {w₂ : neword M k l} :
  (append w₁ hne w₂).last = w₂.last := rfl

@[simp]
lemma append_prod {i j k l} {w₁ : neword M i j} {hne : j ≠ k} {w₂ : neword M k l} :
  (append w₁ hne w₂).prod = w₁.prod * w₂.prod :=
by simp [to_word, prod, word.prod]

/-- One can replace the first letter in a non-empty reduced word by an element of the same
group -/
def replace_head : Π {i j : ι} (x : M i) (hnotone : x ≠ 1) (w : neword M i j), neword M i j
| _ _ x h (singleton _ _) := singleton x h
| _ _ x h (append w₁ hne w₂) := append (replace_head x h w₁) hne w₂

@[simp]
lemma replace_head_head {i j : ι} (x : M i) (hnotone : x ≠ 1) (w : neword M i j) :
  (replace_head x hnotone w).head = x :=
by { induction w, refl, exact w_ih_w₁ _ _, }

/-- One can multiply an element from the left to a non-empty reduced word if it does not cancel
with the first element in the word. -/
def mul_head {i j : ι} (w : neword M i j) (x : M i) (hnotone : x * w.head ≠ 1) :
  neword M i j := replace_head (x * w.head) hnotone w

@[simp]
lemma mul_head_head {i j : ι} (w : neword M i j) (x : M i) (hnotone : x * w.head ≠ 1) :
   (mul_head w x hnotone).head = x * w.head :=
by { induction w, refl, exact w_ih_w₁ _ _, }

@[simp]
lemma mul_head_prod {i j : ι} (w : neword M i j) (x : M i) (hnotone : x * w.head ≠ 1) :
  (mul_head w x hnotone).prod = of x * w.prod :=
begin
  unfold mul_head,
  induction w,
  { simp [mul_head, replace_head], },
  { specialize w_ih_w₁ _ hnotone, clear w_ih_w₂,
    simp [replace_head, ← mul_assoc] at *,
    congr' 1, }
end

section group

variables {G : ι → Type*} [Π i, group (G i)]

/-- The inverse of a non-empty reduced word -/
def inv : Π {i j} (w : neword G i j), neword G j i
| _ _ (singleton x h) := singleton x⁻¹ (mt inv_eq_one.mp h)
| _ _ (append w₁ h w₂) := append w₂.inv h.symm w₁.inv

@[simp]
lemma inv_prod {i j} (w : neword G i j) : w.inv.prod = w.prod⁻¹ :=
by induction w; simp [inv, *]

@[simp]
lemma inv_head {i j} (w : neword G i j) : w.inv.head = w.last⁻¹ :=
by induction w; simp [inv, *]

@[simp]
lemma inv_last {i j} (w : neword G i j) : w.inv.last = w.head⁻¹ :=
by induction w; simp [inv, *]

end group

end neword

section ping_pong_lemma

open_locale pointwise
open_locale cardinal

variables [hnontriv : nontrivial ι]
variables {G : Type*} [group G]
variables {H : ι → Type*} [∀ i, group (H i)]
variables (f : Π i, H i →* G)

-- We need many groups or one group with many elements
variables (hcard : 3 ≤ # ι ∨ ∃ i, 3 ≤ # (H i))

-- A group action on α, and the ping-pong sets
variables {α : Type*} [mul_action G α]
variables (X : ι → set α)
variables (hXnonempty : ∀ i, (X i).nonempty)
variables (hXdisj : pairwise (λ i j, disjoint (X i) (X j)))
variables (hpp : pairwise (λ i j, ∀ h : H i, h ≠ 1 → f i h • X j ⊆ X i))

include hpp

lemma lift_word_ping_pong {i j k} (w : neword H i j) (hk : j ≠ k) :
  lift f w.prod • X k ⊆ X i :=
begin
  rename [i → i', j → j', k → m, hk → hm],
  induction w with i x hne_one i j k l w₁ hne w₂  hIw₁ hIw₂ generalizing m; clear i' j',
  { simpa using hpp _ _ hm _ hne_one, },
  { calc lift f (neword.append w₁ hne w₂).prod • X m
        = lift f w₁.prod • lift f w₂.prod • X m : by simp [mul_action.mul_smul]
    ... ⊆ lift f w₁.prod • X k : set_smul_subset_set_smul_iff.mpr (hIw₂ hm)
    ... ⊆ X i : hIw₁ hne },
end

include X hXnonempty hXdisj

lemma lift_word_prod_nontrivial_of_other_i {i j k} (w : neword H i j)
  (hhead : k ≠ i) (hlast : k ≠ j) : lift f w.prod ≠ 1 :=
begin
  intro heq1,
  have : X k ⊆ X i,
    by simpa [heq1] using lift_word_ping_pong f X hpp w hlast.symm,
  obtain ⟨x, hx⟩ := hXnonempty k,
  exact hXdisj k i hhead ⟨hx, this hx⟩,
end

include hnontriv

lemma lift_word_prod_nontrivial_of_head_eq_last {i} (w : neword H i i) :
  lift f w.prod ≠ 1 :=
begin
  obtain ⟨k, hk⟩ := exists_ne i,
  exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w hk hk,
end

lemma lift_word_prod_nontrivial_of_head_card {i j} (w : neword H i j)
  (hcard : 3 ≤ # (H i)) (hheadtail : i ≠ j) : lift f w.prod ≠ 1 :=
begin
  obtain ⟨h, hn1, hnh⟩ := cardinal.three_le hcard 1 (w.head⁻¹),
  have hnot1 : h * w.head ≠ 1, by { rw ← div_inv_eq_mul, exact div_ne_one_of_ne hnh },
  let w' : neword H i i := neword.append
    (neword.mul_head w h hnot1) hheadtail.symm
    (neword.singleton h⁻¹ (inv_ne_one.mpr hn1)),
  have hw' : lift f w'.prod ≠ 1 :=
    lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w',
  intros heq1, apply hw', simp [w', heq1]
end

include hcard
lemma lift_word_prod_nontrivial_of_not_empty {i j} (w : neword H i j) :
  lift f w.prod ≠ 1 :=
begin
  classical,
  cases hcard,
  { obtain ⟨i, h1, h2⟩ := cardinal.three_le hcard i j,
    exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w h1 h2, },
  { cases hcard with k hcard,
    by_cases hh : i = k; by_cases hl : j = k,
    { subst hh, subst hl,
      exact lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w, },
    { subst hh,
      change j ≠ i at hl,
      exact lift_word_prod_nontrivial_of_head_card f X hXnonempty hXdisj hpp w hcard hl.symm, },
    { subst hl,
      change i ≠ j at hh,
      have : lift f w.inv.prod ≠ 1 :=
        lift_word_prod_nontrivial_of_head_card f X hXnonempty hXdisj hpp w.inv hcard hh.symm,
      intros heq, apply this, simpa using heq, },
    { change i ≠ k at hh,
      change j ≠ k at hl,
      obtain ⟨h, hn1, -⟩ := cardinal.three_le hcard 1 1,
      let w' : neword H k k := neword.append
        (neword.append (neword.singleton h hn1) hh.symm w)
        hl (neword.singleton h⁻¹ (inv_ne_one.mpr hn1)) ,
      have hw' : lift f w'.prod ≠ 1 :=
        lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w',
      intros heq1, apply hw', simp [w', heq1], }, }
end

lemma empty_of_word_prod_eq_one {w : word H} (h : lift f w.prod = 1) :
  w = word.empty :=
begin
  by_contradiction hnotempty,
  obtain ⟨i, j, w, rfl⟩ := neword.of_word w hnotempty,
  exact lift_word_prod_nontrivial_of_not_empty f hcard X hXnonempty hXdisj hpp w h,
end

/--
The Ping-Pong-Lemma.

Given a group action of `G` on `X` so that the `H i` acts in a specific way on disjoint subsets
`X i` we can prove that `lift f` is injective, and thus the image of `lift f` is isomorphic to the
direct product of the `H i`.

Often the Ping-Pong-Lemma is stated with regard to subgroups `H i` that generate the whole group;
we generalize to arbitrary group homomorphisms `f i : H i →* G` and do not require the group to be
generated by the images.

Usually the Ping-Pong-Lemma requires that one group `H i` has at least three elements. This
condition is only needed if `# ι = 2`, and we accept `3 ≤ # ι` as an alternative.
-/
theorem lift_injective_of_ping_pong:
  function.injective (lift f) :=
begin
  classical,
  apply (injective_iff_map_eq_one (lift f)).mpr,
  rw (free_product.word.equiv : _ ≃ word H).forall_congr_left',
  { intros w Heq,
    dsimp [word.equiv] at *,
    { rw empty_of_word_prod_eq_one f hcard X hXnonempty hXdisj hpp Heq,
      reflexivity, }, },
end

end ping_pong_lemma

/-- The free product of free groups is itself a free group -/
@[simps]
instance {ι : Type*} (G : ι → Type*) [∀ i, group (G i)] [hG : ∀ i, is_free_group (G i)] :
  is_free_group (free_product G) :=
{ generators := Σ i, is_free_group.generators (G i),
  mul_equiv :=
  monoid_hom.to_mul_equiv
    (free_group.lift (λ (x : Σ i, is_free_group.generators (G i)),
      free_product.of (is_free_group.of x.2 : G x.1)))
    (free_product.lift (λ (i : ι),
      (is_free_group.lift (λ (x : is_free_group.generators (G i)),
        free_group.of (⟨i, x⟩ : Σ i, is_free_group.generators (G i)))
        : G i →* (free_group (Σ i, is_free_group.generators (G i))))))
    (by {ext, simp, })
   (by {ext, simp, }) }

/-- A free group is a free product of copies of the free_group over one generator. -/

-- NB: One might expect this theorem to be phrased with ℤ, but ℤ is an additive group,
-- and using `multiplicative ℤ` runs into diamond issues.
@[simps]
def _root_.free_group_equiv_free_product {ι : Type u_1} :
  free_group ι ≃* free_product (λ (_ : ι), free_group unit) :=
begin
  refine monoid_hom.to_mul_equiv _ _ _ _,
  exact free_group.lift (λ i, @free_product.of ι _ _ i (free_group.of unit.star)),
  exact free_product.lift (λ i, free_group.lift (λ pstar, free_group.of i)),
  { ext i, refl, },
  { ext i a, cases a, refl, },
end

section ping_pong_lemma

open_locale pointwise cardinal

variables [nontrivial ι]
variables {G : Type u_1} [group G] (a : ι → G)

-- A group action on α, and the ping-pong sets
variables {α : Type*} [mul_action G α]
variables (X Y : ι → set α)
variables (hXnonempty : ∀ i, (X i).nonempty)
variables (hXdisj : pairwise (λ i j, disjoint (X i) (X j)))
variables (hYdisj : pairwise (λ i j, disjoint (Y i) (Y j)))
variables (hXYdisj : ∀ i j, disjoint (X i) (Y j))
variables (hX : ∀ i, a i • (Y i)ᶜ ⊆ X i)
variables (hY : ∀ i, a⁻¹ i • (X i)ᶜ ⊆ Y i)

include hXnonempty hXdisj hYdisj hXYdisj hX hY

/--
The Ping-Pong-Lemma.

Given a group action of `G` on `X` so that the generators of the free groups act in specific
ways on disjoint subsets `X i` and `Y i` we can prove that `lift f` is injective, and thus the image
of `lift f` is isomorphic to the free group.

Often the Ping-Pong-Lemma is stated with regard to group elements that generate the whole group;
we generalize to arbitrary group homomorphisms from the free group to `G`  and do not require the
group to be generated by the elements.
-/
theorem _root_.free_group.injective_lift_of_ping_pong :
  function.injective (free_group.lift a) :=
begin
  -- Step one: express the free group lift via the free product lift
  have : free_group.lift a =
    (free_product.lift (λ i, free_group.lift (λ _, a i))).comp
    (((@free_group_equiv_free_product ι)).to_monoid_hom),
  { ext i, simp, },
  rw this, clear this,
  refine function.injective.comp _ (mul_equiv.injective _),

  -- Step two: Invoke the ping-pong lemma for free products
  show function.injective (lift (λ (i : ι), free_group.lift (λ _, a i))),

  -- Prepare to instantiate lift_injective_of_ping_pong
  let H : ι → Type _ := λ i, free_group unit,
  let f : Π i, H i →* G := λ i, free_group.lift (λ _, a i),
  let X' : ι → set α := λ i, X i ∪ Y i,

  apply lift_injective_of_ping_pong f _ X',

  show _ ∨ ∃ i, 3 ≤ # (H i),
  { inhabit ι,
    right, use arbitrary ι,
    simp only [H],
    rw [free_group.free_group_unit_equiv_int.cardinal_eq, cardinal.mk_denumerable],
    apply le_of_lt,
    simp },

  show ∀ i, (X' i).nonempty,
  { exact (λ i, set.nonempty.inl (hXnonempty i)), },

  show pairwise (λ i j, disjoint (X' i) (X' j)),
  { intros i j hij,
    simp only [X'],
    apply disjoint.union_left; apply disjoint.union_right,
    { exact hXdisj i j hij, },
    { exact hXYdisj i j, },
    { exact (hXYdisj j i).symm, },
    { exact hYdisj i j hij, }, },

  show pairwise (λ i j, ∀ h : H i, h ≠ 1 → f i h • X' j ⊆ X' i),
  { rintros i j hij,
    -- use free_group unit ≃ ℤ
    refine free_group.free_group_unit_equiv_int.forall_congr_left'.mpr _,
    intros n hne1,
    change free_group.lift (λ _, a i) (free_group.of () ^ n) • X' j ⊆ X' i,
    simp only [map_zpow, free_group.lift.of],
    change a i ^ n • X' j ⊆ X' i,
    have hnne0 : n ≠ 0, { rintro rfl, apply hne1, simpa, }, clear hne1,
    simp only [X'],

    -- Positive and negative powers separately
    cases (lt_or_gt_of_ne hnne0).swap with hlt hgt,
    { have h1n : 1 ≤ n := hlt,
      calc a i ^ n • X' j ⊆ a i ^ n • (Y i)ᶜ : set_smul_subset_set_smul_iff.mpr $
        set.disjoint_iff_subset_compl_right.mp $
          disjoint.union_left (hXYdisj j i) (hYdisj j i hij.symm)
      ... ⊆ X i :
      begin
        refine int.le_induction _ _ _ h1n,
        { rw zpow_one, exact hX i, },
        { intros n hle hi,
          calc (a i ^ (n + 1)) • (Y i)ᶜ
                = (a i ^ n * a i) • (Y i)ᶜ : by rw [zpow_add, zpow_one]
            ... = a i ^ n • (a i • (Y i)ᶜ) : mul_action.mul_smul _ _ _
            ... ⊆ a i ^ n • X i : set_smul_subset_set_smul_iff.mpr $ hX i
            ... ⊆ a i ^ n • (Y i)ᶜ : set_smul_subset_set_smul_iff.mpr $
              set.disjoint_iff_subset_compl_right.mp (hXYdisj i i)
            ... ⊆ X i : hi, },
      end
      ... ⊆ X' i : set.subset_union_left _ _, },
    { have h1n : n ≤ -1, { apply int.le_of_lt_add_one, simpa using hgt, },
      calc a i ^ n • X' j ⊆ a i ^ n • (X i)ᶜ : set_smul_subset_set_smul_iff.mpr $
        set.disjoint_iff_subset_compl_right.mp $
          disjoint.union_left (hXdisj j i hij.symm) (hXYdisj i j).symm
      ... ⊆ Y i :
      begin
        refine int.le_induction_down _ _ _ h1n,
        { rw [zpow_neg, zpow_one], exact hY i, },
        { intros n hle hi,
          calc (a i ^ (n - 1)) • (X i)ᶜ
                = (a i ^ n * (a i)⁻¹) • (X i)ᶜ : by rw [zpow_sub, zpow_one]
            ... = a i ^ n • ((a i)⁻¹ • (X i)ᶜ) : mul_action.mul_smul _ _ _
            ... ⊆ a i ^ n • Y i : set_smul_subset_set_smul_iff.mpr $ hY i
            ... ⊆ a i ^ n • (X i)ᶜ : set_smul_subset_set_smul_iff.mpr $
              set.disjoint_iff_subset_compl_right.mp (hXYdisj i i).symm
            ... ⊆ Y i : hi, },
      end
      ... ⊆ X' i : set.subset_union_right _ _, }, },
end

end ping_pong_lemma

end free_product
