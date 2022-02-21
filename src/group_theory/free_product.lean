/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import algebra.free_monoid
import algebra.pointwise
import group_theory.congruence
import group_theory.subgroup.basic
import group_theory.subgroup.pointwise
import data.list.chain
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
  let S : submonoid (free_product M) := ⟨set_of C, h_one, h_mul⟩,
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
def neword := { w : word M // w ≠ word.empty }
variable {M}

namespace neword

open word

def singleton {i} (x : M i) (hne_one : x ≠ 1) : neword M :=
{ val := {
    to_list := [⟨i, x⟩],
    ne_one := λ _ , by { rintros (rfl|absurd), exact hne_one, exfalso, apply absurd, },
    chain_ne := list.chain'_singleton _, },
  property := by rintros ⟨rfl, _, _ ⟩, }

def head (w : neword M) : Σ i, M i :=
begin
  haveI : inhabited ι, begin
    cases w with w h,
    cases w with l, cases l with x ,
    { exfalso, apply h, refl, },
    { exact ⟨x.1⟩, }
  end,
  haveI : inhabited (M default), exact ⟨1⟩,
  exact w.val.to_list.head,
end

lemma to_list_eq_nil_iff_word_eq_empty {w : word M } :
  w.to_list = list.nil ↔ w = empty :=
begin
  split; intro h,
  { ext, rw h, reflexivity, },
  { subst h, reflexivity, }
end

def last (w : neword M) : Σ i, M i :=
w.val.to_list.last (λ h', w.property (to_list_eq_nil_iff_word_eq_empty.mp h'))

@[simp]
lemma singleton_head {i} (x : M i) (hne_one : x ≠ 1) :
  (singleton x hne_one).head = ⟨i, x⟩ := rfl

@[simp]
lemma singleton_last {i} (x : M i) (hne_one : x ≠ 1) :
  (singleton x hne_one).last = ⟨i, x⟩ := rfl

section cons

variables {i : ι} (x : M i) (w : neword M) (hne_one : x ≠ 1) (hne : i ≠ w.head.1)
include hne_one hne

def cons : neword M :=
{ val :=
  { to_list := ⟨i, x⟩ :: w.val.to_list,
    ne_one := λ _ , by { rintros (rfl|hrest), exact hne_one, exact w.val.ne_one _ hrest, },
    chain_ne := begin
      apply list.chain'_cons'.mpr, split,
      {
        intros y hy,
        unfold neword.head at hne,
        rw list.head_eq_head' at hne,
        cases w.val.to_list.head' with y', contradiction,
        obtain rfl : y' = y := by { simp at hy, exact hy },
        exact hne,
      },
      { exact w.val.chain_ne, }
    end
  },
  property :=  by rintros ⟨rfl,_,_⟩ }

@[simp]
lemma cons_head : (cons x w hne_one hne).head = ⟨i, x⟩ := rfl

@[simp]
lemma cons_last : (cons x w hne_one hne).last = w.last :=
by { simp [cons,last], rw list.last_cons }

end cons

/-- An induction principle for non-empty reduced words, with cases for singleton and concatentation
to the front -/
@[elab_as_eliminator]
lemma cons_induction
  (P : neword M -> Prop)
  (hsingleton : ∀ {i} (x : M i) (hne_one : x ≠ 1),
    P (singleton x hne_one))
  (hcons : ∀ {i} (x : M i) (w : neword M) (hne_one : x ≠ 1) (hne : i ≠ w.head.1) (hind : P w),
    P (cons x w hne_one hne))
  (w : neword M) :
  P w :=
begin
  cases w with w hnotempty,
  cases w with l hne_one hne,
  induction l with x l hi,
  { exfalso, apply hnotempty, refl, },
  { cases x with i x,
    rw list.forall_mem_cons at hne_one,
    cases l with y' l,
    { exact hsingleton x hne_one.1, },
    { cases y' with j y,
      rw list.chain'_cons at hne,
      refine hcons x ⟨⟨⟨j,y⟩::l,hne_one.2,hne.2⟩, _⟩ hne_one.1 hne.1 (hi _ _ _),
      rintro ⟨rfl⟩, } }
end

def prod (w : neword M) := w.val.prod

@[simp] lemma prod_singleton {i} (x : M i) (hne_one : x ≠ 1) :
  (singleton x hne_one).prod = of x :=
by simp [singleton, neword.prod, word.prod]

@[simp] lemma prod_cons {i} (x : M i) (w : neword M)
   (hne_one : x ≠ 1) (hne : i ≠ w.head.1) :
  (cons x w hne_one hne).prod = of x * w.val.prod :=
by simp [cons, neword.prod, word.prod]

end neword

section ping_pong_lemma

open_locale pointwise

variables [nontrivial ι]
variables [inhabited ι]
variables {G : Type*} [group G]
variables {H : ι → Type*} [∀ i, inhabited (H i)] [∀ i, group (H i)]
variables (f : Π i, H i →* G) (hinj : ∀ i, function.injective (f i))

-- One group, the one with index i₃, has at least three members
variables (i₃ : ι) (h₃₁ : H i₃) (h₃₂ : H i₃)
variables (hcard1 : h₃₁ ≠ 1) (hcard2 : h₃₂ ≠ 1) (hcard3 : h₃₁ ≠ h₃₂)

-- A group action on α, and the ping-pong sets
variables {α : Type*} [mul_action G α]
variables (X : ι → set α)
variables (hXnonempty : ∀ i, (X i).nonempty)
variables (hXdisj : pairwise (λ i j, disjoint (X i) (X j)))
variables (hpp : pairwise (λ i j, ∀ h : H i, h ≠ 1 → f i h • X j ⊆ X i))

include hpp

lemma lift_word_ping_pong (i) {w : neword H}
  (hi : i ≠ w.last.1) :
  lift f w.prod • X i ⊆ X w.head.1 :=
begin
  -- why not
  -- induction w using neword.cons_induction,
  revert w hi,
  refine neword.cons_induction
    (λ w , i ≠ w.last.1 → (lift f) w.prod • X i ⊆ X w.head.1)
     _ _,
  { intros j x hne_one hj,
    have hji : j ≠ i, { symmetry, simpa using hj, },
    simpa using hpp _ _ hji _ hne_one, },
  {
    intros j x w hne_one hj hI hi,
    specialize hI (by simpa using hi), clear hi,
    have := calc
      (f j) x • (lift f) w.prod • X i ⊆ (f j) x • X w.head.fst :
      set_smul_subset_set_smul_iff.mpr hI
      ... ⊆ X j : hpp _ _ hj _ hne_one
    ,
    simpa [mul_action.mul_smul] using this, }
end

include X hXnonempty hXdisj

lemma lift_word_prod_nontrivial_of_other_i (i) {w : neword H}
  (hhead : i ≠ w.head.1)
  (hlast : i ≠ w.last.1) :
  lift f w.prod ≠ 1 :=
begin
  intro heq1,
  have : X i ⊆ X w.head.fst,
    by simpa [heq1] using lift_word_ping_pong f X hpp i hlast,
  obtain ⟨x, hx⟩ := hXnonempty i,
  exact hXdisj i w.head.fst hhead ⟨hx, this hx⟩,
end

lemma lift_word_prod_nontrivial_of_head_last {w : neword H}
  (hheadtail : w.head.1 = w.last.1) :
  lift f w.prod ≠ 1 :=
begin
  obtain ⟨k, hk⟩ := exists_ne w.last.1,
  have hk' : k ≠ w.head.1, by simpa [hheadtail] using hk,
  exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp k hk' hk,
end

lemma lift_word_prod_nontrivial_of_not_empty (w : neword H) :
  lift f w.prod ≠ 1 :=
sorry

lemma empty_of_word_prod_eq_one {w : word H} (h : lift f w.prod = 1) :
  w = word.empty :=
begin
  by_contradiction hnotempty,
  exact lift_word_prod_nontrivial_of_not_empty f X hXnonempty hXdisj hpp ⟨w, hnotempty⟩ h,
end


lemma lift_subgroups_injective :
  function.injective (lift f) :=
begin
  classical,
  apply (monoid_hom.injective_iff (lift f)).mpr,
  rw free_product.word.equiv.forall_congr_left',
  intros w Heq,
  dsimp [word.equiv] at *,
  { rw empty_of_word_prod_eq_one f X hXnonempty hXdisj hpp Heq,
    reflexivity,
  },
  apply_instance,
  apply_instance,
end

end ping_pong_lemma

end free_product
