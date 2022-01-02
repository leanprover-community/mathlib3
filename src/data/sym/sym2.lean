/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import data.sym.basic
import tactic.linarith

/-!
# The symmetric square

This file defines the symmetric square, which is `α × α` modulo
swapping.  This is also known as the type of unordered pairs.

More generally, the symmetric square is the second symmetric power
(see `data.sym.basic`). The equivalence is `sym2.equiv_sym`.

From the point of view that an unordered pair is equivalent to a
multiset of cardinality two (see `sym2.equiv_multiset`), there is a
`has_mem` instance `sym2.mem`, which is a `Prop`-valued membership
test.  Given `h : a ∈ z` for `z : sym2 α`, then `h.other` is the other
element of the pair, defined using `classical.choice`.  If `α` has
decidable equality, then `h.other'` computably gives the other element.

The universal property of `sym2` is provided as `sym2.lift`, which
states that functions from `sym2 α` are equivalent to symmetric
two-argument functions from `α`.

Recall that an undirected graph (allowing self loops, but no multiple
edges) is equivalent to a symmetric relation on the vertex type `α`.
Given a symmetric relation on `α`, the corresponding edge set is
constructed by `sym2.from_rel` which is a special case of `sym2.lift`.

## Notation

The symmetric square has a setoid instance, so `⟦(a, b)⟧` denotes a
term of the symmetric square.

## Tags

symmetric square, unordered pairs, symmetric powers
-/

open finset fintype function sym

universe u
variables {α β γ : Type*}

namespace sym2

/--
This is the relation capturing the notion of pairs equivalent up to permutations.
-/
inductive rel (α : Type u) : (α × α) → (α × α) → Prop
| refl (x y : α) : rel (x, y) (x, y)
| swap (x y : α) : rel (x, y) (y, x)

attribute [refl] rel.refl

@[symm] lemma rel.symm {x y : α × α} : rel α x y → rel α y x :=
by rintro ⟨_, _⟩; constructor

@[trans] lemma rel.trans {x y z : α × α} : rel α x y → rel α y z → rel α x z :=
by { intros a b, cases_matching* rel _ _ _; apply rel.refl <|> apply rel.swap }

lemma rel.is_equivalence : equivalence (rel α) := by tidy; apply rel.trans; assumption

instance rel.setoid (α : Type u) : setoid (α × α) := ⟨rel α, rel.is_equivalence⟩

end sym2

/--
`sym2 α` is the symmetric square of `α`, which, in other words, is the
type of unordered pairs.

It is equivalent in a natural way to multisets of cardinality 2 (see
`sym2.equiv_multiset`).
-/
@[reducible]
def sym2 (α : Type u) := quotient (sym2.rel.setoid α)

namespace sym2

@[elab_as_eliminator]
protected lemma ind {f : sym2 α → Prop} (h : ∀ x y, f ⟦(x, y)⟧) : ∀ i, f i :=
quotient.ind $ prod.rec $ by exact h

@[elab_as_eliminator]
protected lemma induction_on {f : sym2 α → Prop} (i : sym2 α) (hf : ∀ x y, f ⟦(x,y)⟧) : f i :=
i.ind hf

protected lemma «exists» {α : Sort*} {f : sym2 α → Prop} :
  (∃ (x : sym2 α), f x) ↔ ∃ x y, f ⟦(x, y)⟧ :=
(surjective_quotient_mk _).exists.trans prod.exists

protected lemma «forall» {α : Sort*} {f : sym2 α → Prop} :
  (∀ (x : sym2 α), f x) ↔ ∀ x y, f ⟦(x, y)⟧ :=
(surjective_quotient_mk _).forall.trans prod.forall

lemma eq_swap {a b : α} : ⟦(a, b)⟧ = ⟦(b, a)⟧ :=
by { rw quotient.eq, apply rel.swap }

lemma congr_right {a b c : α} : ⟦(a, b)⟧ = ⟦(a, c)⟧ ↔ b = c :=
by { split; intro h, { rw quotient.eq at h, cases h; refl }, rw h }

lemma congr_left {a b c : α} : ⟦(b, a)⟧ = ⟦(c, a)⟧ ↔ b = c :=
by { split; intro h, { rw quotient.eq at h, cases h; refl }, rw h }

lemma eq_iff {x y z w : α} :
  ⟦(x, y)⟧ = ⟦(z, w)⟧ ↔ (x = z ∧ y = w) ∨ (x = w ∧ y = z) :=
begin
  split; intro h,
  { rw quotient.eq at h, cases h; tidy },
  { cases h; rw [h.1, h.2], rw eq_swap }
end

/-- The universal property of `sym2`; symmetric functions of two arguments are equivalent to
functions from `sym2`. Note that when `β` is `Prop`, it can sometimes be more convenient to use
`sym2.from_rel` instead. -/
def lift : {f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁} ≃ (sym2 α → β) :=
{ to_fun := λ f, quotient.lift (uncurry ↑f) $ by { rintro _ _ ⟨⟩, exacts [rfl, f.prop _ _] },
  inv_fun := λ F, ⟨curry (F ∘ quotient.mk), λ a₁ a₂, congr_arg F eq_swap⟩,
  left_inv := λ f, subtype.ext rfl,
  right_inv := λ F, funext $ sym2.ind $ by exact λ x y, rfl }

@[simp]
lemma lift_mk (f : {f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁}) (a₁ a₂ : α) :
  lift f ⟦(a₁, a₂)⟧ = (f : α → α → β) a₁ a₂ := rfl

@[simp]
lemma coe_lift_symm_apply (F : sym2 α → β) (a₁ a₂ : α) :
  (lift.symm F : α → α → β) a₁ a₂ = F ⟦(a₁, a₂)⟧ := rfl

/--
The functor `sym2` is functorial, and this function constructs the induced maps.
-/
def map (f : α → β) : sym2 α → sym2 β :=
quotient.map (prod.map f f)
  (by { rintros _ _ h, cases h, { refl }, apply rel.swap })

@[simp]
lemma map_id : sym2.map (@id α) = id := by tidy

lemma map_comp {g : β → γ} {f : α → β} : sym2.map (g ∘ f) = sym2.map g ∘ sym2.map f := by tidy

lemma map_map {g : β → γ} {f : α → β} (x : sym2 α) :
  map g (map f x) = map (g ∘ f) x := by tidy

@[simp]
lemma map_pair_eq (f : α → β) (x y : α) : map f ⟦(x, y)⟧ = ⟦(f x, f y)⟧ := rfl

lemma map.injective {f : α → β} (hinj : injective f) : injective (map f) :=
begin
  intros z z',
  refine quotient.ind₂ (λ z z', _) z z',
  cases z with x y,
  cases z' with x' y',
  repeat { rw [map_pair_eq, eq_iff] },
  rintro (h|h); simp [hinj h.1, hinj h.2],
end

section membership

/-! ### Declarations about membership -/

/--
This is a predicate that determines whether a given term is a member of a term of the
symmetric square.  From this point of view, the symmetric square is the subtype of
cardinality-two multisets on `α`.
-/
def mem (x : α) (z : sym2 α) : Prop :=
∃ (y : α), z = ⟦(x, y)⟧

instance : has_mem α (sym2 α) := ⟨mem⟩

lemma mem_mk_left (x y : α) : x ∈ ⟦(x, y)⟧ := ⟨y, rfl⟩
lemma mem_mk_right (x y : α) : y ∈ ⟦(x, y)⟧ := eq_swap.subst $ mem_mk_left y x

/--
Given an element of the unordered pair, give the other element using `classical.some`.
See also `mem.other'` for the computable version.
-/
noncomputable def mem.other {a : α} {z : sym2 α} (h : a ∈ z) : α :=
classical.some h

@[simp]
lemma other_spec {a : α} {z : sym2 α} (h : a ∈ z) : ⟦(a, h.other)⟧ = z :=
by erw ← classical.some_spec h

@[simp] lemma mem_iff {a b c : α} : a ∈ ⟦(b, c)⟧ ↔ a = b ∨ a = c :=
{ mp  := by { rintro ⟨_, h⟩, rw eq_iff at h, tidy },
  mpr := by { rintro ⟨_⟩; subst a, { apply mem_mk_left }, apply mem_mk_right } }

lemma other_mem {a : α} {z : sym2 α} (h : a ∈ z) : h.other ∈ z :=
by { convert mem_mk_right a h.other, rw other_spec h }

lemma mem_and_mem_iff {x y : α} {z : sym2 α} (hne : x ≠ y) : x ∈ z ∧ y ∈ z ↔ z = ⟦(x, y)⟧ :=
begin
  refine ⟨quotient.rec_on_subsingleton z _, _⟩,
  { rintro ⟨z₁, z₂⟩ ⟨hx, hy⟩,
    rw eq_iff,
    cases mem_iff.mp hx with hx hx; cases mem_iff.mp hy with hy hy; subst x; subst y;
    try { exact (hne rfl).elim };
    simp only [true_or, eq_self_iff_true, and_self, or_true] },
  { rintro rfl, simp },
end

@[ext]
protected lemma ext (z z' : sym2 α) (h : ∀ x, x ∈ z ↔ x ∈ z') : z = z' :=
begin
  refine quotient.rec_on_subsingleton z (λ w, _) h,
  refine quotient.rec_on_subsingleton z' (λ w', _),
  intro h,
  cases w with x y, cases w' with x' y',
  simp only [mem_iff] at h,
  apply eq_iff.mpr,
  have hx := h x, have hy := h y, have hx' := h x', have hy' := h y',
  simp only [true_iff, true_or, eq_self_iff_true, iff_true, or_true] at hx hy hx' hy',
  cases hx; subst x; cases hy; subst y; cases hx'; try { subst x' }; cases hy'; try { subst y' };
  simp only [eq_self_iff_true, and_self, or_self, true_or, or_true],
end

instance mem.decidable [decidable_eq α] (x : α) (z : sym2 α) : decidable (x ∈ z) :=
quotient.rec_on_subsingleton z (λ ⟨y₁, y₂⟩, decidable_of_iff' _ mem_iff)

end membership

/--
A type `α` is naturally included in the diagonal of `α × α`, and this function gives the image
of this diagonal in `sym2 α`.
-/
def diag (x : α) : sym2 α := ⟦(x, x)⟧

lemma diag_injective : function.injective (sym2.diag : α → sym2 α) :=
λ x y h, by cases quotient.exact h; refl

/--
A predicate for testing whether an element of `sym2 α` is on the diagonal.
-/
def is_diag : sym2 α → Prop :=
lift ⟨eq, λ _ _, propext eq_comm⟩

lemma mk_is_diag_iff {x y : α} : is_diag ⟦(x, y)⟧ ↔ x = y := iff.rfl

@[simp]
lemma is_diag_iff_proj_eq (z : α × α) : is_diag ⟦z⟧ ↔ z.1 = z.2 :=
prod.rec_on z $ λ _ _, mk_is_diag_iff

@[simp]
lemma diag_is_diag (a : α) : is_diag (diag a) := eq.refl a

lemma is_diag.mem_range_diag {z : sym2 α} : is_diag z → z ∈ set.range (@diag α) :=
begin
  induction z using quotient.induction_on,
  cases z,
  rintro (rfl : z_fst = z_snd),
  exact ⟨z_fst, rfl⟩,
end

lemma is_diag_iff_mem_range_diag (z : sym2 α) : is_diag z ↔ z ∈ set.range (@diag α) :=
⟨is_diag.mem_range_diag, λ ⟨i, hi⟩, hi ▸ diag_is_diag i⟩

instance is_diag.decidable_pred (α : Type u) [decidable_eq α] : decidable_pred (@is_diag α) :=
by { refine λ z, quotient.rec_on_subsingleton z (λ a, _), erw is_diag_iff_proj_eq, apply_instance }

lemma other_ne {a : α} {z : sym2 α} (hd : ¬is_diag z) (h : a ∈ z) : h.other ≠ a :=
begin
  intro hn, apply hd,
  have h' := sym2.other_spec h,
  rw hn at h',
  rw ←h',
  simp,
end

section relations

/-! ### Declarations about symmetric relations -/

variables {r : α → α → Prop}

/--
Symmetric relations define a set on `sym2 α` by taking all those pairs
of elements that are related.
-/
def from_rel (sym : symmetric r) : set (sym2 α) :=
set_of (lift ⟨r, λ x y, propext ⟨λ h, sym h, λ h, sym h⟩⟩)

@[simp]
lemma from_rel_proj_prop {sym : symmetric r} {z : α × α} : ⟦z⟧ ∈ from_rel sym ↔ r z.1 z.2 := iff.rfl

@[simp]
lemma from_rel_prop {sym : symmetric r} {a b : α} : ⟦(a, b)⟧ ∈ from_rel sym ↔ r a b := iff.rfl

lemma from_rel_irreflexive {sym : symmetric r} :
  irreflexive r ↔ ∀ {z}, z ∈ from_rel sym → ¬is_diag z :=
{ mp  := λ h, sym2.ind $ by { rintros a b hr (rfl : a = b), exact h _ hr },
  mpr := λ h x hr, h (from_rel_prop.mpr hr) rfl }

lemma mem_from_rel_irrefl_other_ne {sym : symmetric r} (irrefl : irreflexive r)
  {a : α} {z : sym2 α} (hz : z ∈ from_rel sym) (h : a ∈ z) : h.other ≠ a :=
other_ne (from_rel_irreflexive.mp irrefl hz) h

instance from_rel.decidable_pred (sym : symmetric r) [h : decidable_rel r] :
  decidable_pred (∈ sym2.from_rel sym) :=
λ z, quotient.rec_on_subsingleton z (λ x, h _ _)

/-- The inverse to `sym2.from_rel`. Given a set on `sym2 α`, give a symmetric relation on `α`
(see `sym2.to_rel_symmetric`). -/
def to_rel (s : set (sym2 α)) (x y : α) : Prop := ⟦(x, y)⟧ ∈ s

@[simp] lemma to_rel_prop (s : set (sym2 α)) (x y : α) : to_rel s x y ↔ ⟦(x, y)⟧ ∈ s := iff.rfl

lemma to_rel_symmetric (s : set (sym2 α)) : symmetric (to_rel s) := λ x y, by simp [eq_swap]

lemma to_rel_from_rel (sym : symmetric r) : to_rel (from_rel sym) = r := rfl

lemma from_rel_to_rel (s : set (sym2 α)) : from_rel (to_rel_symmetric s) = s :=
set.ext (λ z, sym2.ind (λ x y, iff.rfl) z)

end relations

section sym_equiv

/-! ### Equivalence to the second symmetric power -/

local attribute [instance] vector.perm.is_setoid

private def from_vector : vector α 2 → α × α
| ⟨[a, b], h⟩ := (a, b)

private lemma perm_card_two_iff {a₁ b₁ a₂ b₂ : α} :
  [a₁, b₁].perm [a₂, b₂] ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ a₁ = b₂ ∧ b₁ = a₂ :=
{ mp  := by { simp [← multiset.coe_eq_coe, ← multiset.cons_coe, multiset.cons_eq_cons]; tidy },
  mpr := by { intro h, cases h; rw [h.1, h.2], apply list.perm.swap', refl } }

/--
The symmetric square is equivalent to length-2 vectors up to permutations.
-/
def sym2_equiv_sym' : equiv (sym2 α) (sym' α 2) :=
{ to_fun := quotient.map
    (λ (x : α × α), ⟨[x.1, x.2], rfl⟩)
    (by { rintros _ _ ⟨_⟩, { refl }, apply list.perm.swap', refl }),
  inv_fun := quotient.map from_vector (begin
    rintros ⟨x, hx⟩ ⟨y, hy⟩ h,
    cases x with _ x, { simpa using hx, },
    cases x with _ x, { simpa using hx, },
    cases x with _ x, swap, { exfalso, simp at hx, linarith [hx] },
    cases y with _ y, { simpa using hy, },
    cases y with _ y, { simpa using hy, },
    cases y with _ y, swap, { exfalso, simp at hy, linarith [hy] },
    rcases perm_card_two_iff.mp h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩, { refl },
    apply sym2.rel.swap,
  end),
  left_inv := by tidy,
  right_inv := λ x, begin
    refine quotient.rec_on_subsingleton x (λ x, _),
    { cases x with x hx,
      cases x with _ x, { simpa using hx, },
      cases x with _ x, { simpa using hx, },
      cases x with _ x, swap, { exfalso, simp at hx, linarith [hx] },
      refl },
  end }

/--
The symmetric square is equivalent to the second symmetric power.
-/
def equiv_sym (α : Type*) : sym2 α ≃ sym α 2 :=
equiv.trans sym2_equiv_sym' sym_equiv_sym'.symm

/--
The symmetric square is equivalent to multisets of cardinality
two. (This is currently a synonym for `equiv_sym`, but it's provided
in case the definition for `sym` changes.)
-/
def equiv_multiset (α : Type*) : sym2 α ≃ {s : multiset α // s.card = 2} :=
equiv_sym α

end sym_equiv

section decidable

/--
An algorithm for computing `sym2.rel`.
-/
def rel_bool [decidable_eq α] (x y : α × α) : bool :=
if x.1 = y.1 then x.2 = y.2 else
  if x.1 = y.2 then x.2 = y.1 else ff

lemma rel_bool_spec [decidable_eq α] (x y : α × α) : ↥(rel_bool x y) ↔ rel α x y :=
begin
  cases x with x₁ x₂, cases y with y₁ y₂,
  dsimp [rel_bool], split_ifs;
  simp only [false_iff, bool.coe_sort_ff, bool.of_to_bool_iff],
  rotate 2, { contrapose! h, cases h; cc },
  all_goals { subst x₁, split; intro h1,
    { subst h1; apply sym2.rel.swap },
    { cases h1; cc } }
end

/--
Given `[decidable_eq α]` and `[fintype α]`, the following instance gives `fintype (sym2 α)`.
-/
instance (α : Type*) [decidable_eq α] : decidable_rel (sym2.rel α) :=
λ x y, decidable_of_bool (rel_bool x y) (rel_bool_spec x y)

/-! ### The other element of an element of the symmetric square -/

/--
A function that gives the other element of a pair given one of the elements.  Used in `mem.other'`.
-/
private def pair_other [decidable_eq α] (a : α) (z : α × α) : α := if a = z.1 then z.2 else z.1

/--
Get the other element of the unordered pair using the decidable equality.
This is the computable version of `mem.other`.
-/
def mem.other' [decidable_eq α] {a : α} {z : sym2 α} (h : a ∈ z) : α :=
quot.rec (λ x h', pair_other a x) (begin
  clear h z,
  intros x y h,
  ext hy,
  convert_to pair_other a x = _,
  { have h' : ∀ {c e h}, @eq.rec _ ⟦x⟧ (λ s, a ∈ s → α)
      (λ _, pair_other a x) c e h = pair_other a x,
    { intros _ e _, subst e },
    apply h', },
  have h' := (rel_bool_spec x y).mpr h,
  cases x with x₁ x₂, cases y with y₁ y₂,
  cases mem_iff.mp hy with hy'; subst a; dsimp [rel_bool] at h';
    split_ifs at h'; try { rw bool.of_to_bool_iff at h', subst x₁, subst x₂ }; dsimp [pair_other],
  simp only [ne.symm h_1, if_true, eq_self_iff_true, if_false],
  exfalso, exact bool.not_ff h',
  simp only [h_1, if_true, eq_self_iff_true, if_false],
  exfalso, exact bool.not_ff h',
end) z h

@[simp]
lemma other_spec' [decidable_eq α] {a : α} {z : sym2 α} (h : a ∈ z) : ⟦(a, h.other')⟧ = z :=
begin
  induction z, cases z with x y,
  have h' := mem_iff.mp h,
  dsimp [mem.other', quot.rec, pair_other],
  cases h'; subst a,
  { simp only [if_true, eq_self_iff_true], refl, },
  { split_ifs, subst h_1, refl, rw eq_swap, refl, },
  refl,
end

@[simp]
lemma other_eq_other' [decidable_eq α] {a : α} {z : sym2 α} (h : a ∈ z) : h.other = h.other' :=
by rw [←congr_right, other_spec' h, other_spec]

lemma other_mem' [decidable_eq α] {a : α} {z : sym2 α} (h : a ∈ z) : h.other' ∈ z :=
by { rw ←other_eq_other', exact other_mem h }

lemma other_invol' [decidable_eq α] {a : α} {z : sym2 α} (ha : a ∈ z) (hb : ha.other' ∈ z) :
  hb.other' = a :=
begin
  induction z, cases z with x y,
  dsimp [mem.other', quot.rec, pair_other] at hb,
  split_ifs at hb; dsimp [mem.other', quot.rec, pair_other],
  simp only [h, if_true, eq_self_iff_true],
  split_ifs, assumption, refl,
  simp only [h, if_false, if_true, eq_self_iff_true],
  exact ((mem_iff.mp ha).resolve_left h).symm,
  refl,
end

lemma other_invol {a : α} {z : sym2 α} (ha : a ∈ z) (hb : ha.other ∈ z) : hb.other = a :=
begin
  classical,
  rw other_eq_other' at hb ⊢,
  convert other_invol' ha hb,
  rw other_eq_other',
end

lemma filter_image_quotient_mk_is_diag [decidable_eq α] (s : finset α) :
  ((s.product s).image quotient.mk).filter is_diag = s.diag.image quotient.mk :=
begin
  ext z,
  induction z using quotient.induction_on,
  rcases z with ⟨x, y⟩,
  simp only [mem_image, mem_diag, exists_prop, mem_filter, prod.exists, mem_product],
  split,
  { rintro ⟨⟨a, b, ⟨ha, hb⟩, h⟩, hab⟩,
    rw [←h, sym2.mk_is_diag_iff] at hab,
    exact ⟨a, b, ⟨ha, hab⟩, h⟩ },
  { rintro ⟨a, b, ⟨ha, rfl⟩, h⟩,
    rw ←h,
    exact ⟨⟨a, a, ⟨ha, ha⟩, rfl⟩, rfl⟩ }
end

lemma filter_image_quotient_mk_not_is_diag [decidable_eq α] (s : finset α) :
  ((s.product s).image quotient.mk).filter (λ a : sym2 α, ¬a.is_diag) =
    s.off_diag.image quotient.mk :=
begin
  ext z,
  induction z using quotient.induction_on,
  rcases z with ⟨x, y⟩,
  simp only [mem_image, mem_off_diag, exists_prop, mem_filter, prod.exists, mem_product],
  split,
  { rintro ⟨⟨a, b, ⟨ha, hb⟩, h⟩, hab⟩,
    rw [←h, sym2.mk_is_diag_iff] at hab,
    exact ⟨a, b, ⟨ha, hb, hab⟩, h⟩ },
  { rintro ⟨a, b, ⟨ha, hb, hab⟩, h⟩,
    rw [ne.def, ←sym2.mk_is_diag_iff, h] at hab,
    exact ⟨⟨a, b, ⟨ha, hb⟩, h⟩, hab⟩ }
end

end decidable

instance [subsingleton α] : subsingleton (sym2 α) :=
(equiv_sym α).injective.subsingleton

instance [unique α] : unique (sym2 α) := unique.mk' _

instance [is_empty α] : is_empty (sym2 α) := (equiv_sym α).is_empty

instance [nontrivial α] : nontrivial (sym2 α) := diag_injective.nontrivial

end sym2
