/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/

import order.rel_iso.set
import order.well_founded

/-!
# Initial and principal segments

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines initial and principal segments.

## Main definitions

* `initial_seg r s`: type of order embeddings of `r` into `s` for which the range is an initial
  segment (i.e., if `b` belongs to the range, then any `b' < b` also belongs to the range).
  It is denoted by `r ≼i s`.
* `principal_seg r s`: Type of order embeddings of `r` into `s` for which the range is a principal
  segment, i.e., an interval of the form `(-∞, top)` for some element `top`. It is denoted by
  `r ≺i s`.

## Notations

These notations belong to the `initial_seg` locale.

* `r ≼i s`: the type of initial segment embeddings of `r` into `s`.
* `r ≺i s`: the type of principal segment embeddings of `r` into `s`.
-/

/-!
### Initial segments

Order embeddings whose range is an initial segment of `s` (i.e., if `b` belongs to the range, then
any `b' < b` also belongs to the range). The type of these embeddings from `r` to `s` is called
`initial_seg r s`, and denoted by `r ≼i s`.
-/

variables {α : Type*} {β : Type*} {γ : Type*}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

open function

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≼i s` is an order
embedding whose range is an initial segment. That is, whenever `b < f a` in `β` then `b` is in the
range of `f`. -/
structure initial_seg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s :=
(init' : ∀ a b, s b (to_rel_embedding a) → ∃ a', to_rel_embedding a' = b)

localized "infix (name := initial_seg) ` ≼i `:25 := initial_seg" in initial_seg

namespace initial_seg

instance : has_coe (r ≼i s) (r ↪r s) := ⟨initial_seg.to_rel_embedding⟩

instance : embedding_like (r ≼i s) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' :=
    begin
      rintro ⟨f, hf⟩ ⟨g, hg⟩ h,
      congr' with x,
      exact congr_fun h x
    end,
  injective' := λ f, f.inj' }

@[ext] lemma ext {f g : r ≼i s} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

@[simp] theorem coe_fn_mk (f : r ↪r s) (o) :
  (@initial_seg.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_rel_embedding (f : r ≼i s) : (f.to_rel_embedding : α → β) = f := rfl

@[simp] theorem coe_coe_fn (f : r ≼i s) : ((f : r ↪r s) : α → β) = f := rfl

theorem init (f : r ≼i s) {a : α} {b : β} : s b (f a) → ∃ a', f a' = b :=
f.init' _ _

theorem map_rel_iff (f : r ≼i s) {a b : α} : s (f a) (f b) ↔ r a b := f.1.map_rel_iff

theorem init_iff (f : r ≼i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
⟨λ h, let ⟨a', e⟩ := f.init h in ⟨a', e, f.map_rel_iff.1 (e.symm ▸ h)⟩,
 λ ⟨a', e, h⟩, e ▸ f.map_rel_iff.2 h⟩

/-- An order isomorphism is an initial segment -/
def of_iso (f : r ≃r s) : r ≼i s :=
⟨f, λ a b h, ⟨f.symm b, rel_iso.apply_symm_apply f _⟩⟩

/-- The identity function shows that `≼i` is reflexive -/
@[refl] protected def refl (r : α → α → Prop) : r ≼i r :=
⟨rel_embedding.refl _, λ a b h, ⟨_, rfl⟩⟩

instance (r : α → α → Prop) : inhabited (r ≼i r) := ⟨initial_seg.refl r⟩

/-- Composition of functions shows that `≼i` is transitive -/
@[trans] protected def trans (f : r ≼i s) (g : s ≼i t) : r ≼i t :=
⟨f.1.trans g.1, λ a c h, begin
  simp at h ⊢,
  rcases g.2 _ _ h with ⟨b, rfl⟩, have h := g.map_rel_iff.1 h,
  rcases f.2 _ _ h with ⟨a', rfl⟩, exact ⟨a', rfl⟩
end⟩

@[simp] theorem refl_apply (x : α) : initial_seg.refl r x = x := rfl

@[simp] theorem trans_apply (f : r ≼i s) (g : s ≼i t) (a : α) : (f.trans g) a = g (f a) := rfl

theorem unique_of_trichotomous_of_irrefl [is_trichotomous β s] [is_irrefl β s] :
  well_founded r → subsingleton (r ≼i s) | ⟨h⟩ :=
⟨λ f g, begin
  ext a,
  have := h a, induction this with a H IH,
  refine extensional_of_trichotomous_of_irrefl s (λ x, _),
  simp only [f.init_iff, g.init_iff],
  exact exists_congr (λ x, and_congr_left $ λ hx, IH _ hx ▸ iff.rfl)
end⟩

instance [is_well_order β s] : subsingleton (r ≼i s) :=
⟨λ a, @subsingleton.elim _ (unique_of_trichotomous_of_irrefl
  (@rel_embedding.well_founded _ _ r s a is_well_founded.wf)) a⟩

protected theorem eq [is_well_order β s] (f g : r ≼i s) (a) : f a = g a :=
by rw subsingleton.elim f g

theorem antisymm.aux [is_well_order α r] (f : r ≼i s) (g : s ≼i r) : left_inverse g f :=
initial_seg.eq (f.trans g) (initial_seg.refl _)

/-- If we have order embeddings between `α` and `β` whose images are initial segments, and `β`
is a well-order then `α` and `β` are order-isomorphic. -/
def antisymm [is_well_order β s] (f : r ≼i s) (g : s ≼i r) : r ≃r s :=
by haveI := f.to_rel_embedding.is_well_order; exact
⟨⟨f, g, antisymm.aux f g, antisymm.aux g f⟩, λ _ _, f.map_rel_iff'⟩

@[simp] theorem antisymm_to_fun [is_well_order β s]
  (f : r ≼i s) (g : s ≼i r) : (antisymm f g : α → β) = f := rfl

@[simp] theorem antisymm_symm [is_well_order α r] [is_well_order β s]
  (f : r ≼i s) (g : s ≼i r) : (antisymm f g).symm = antisymm g f :=
rel_iso.coe_fn_injective rfl

theorem eq_or_principal [is_well_order β s] (f : r ≼i s) :
  surjective f ∨ ∃ b, ∀ x, s x b ↔ ∃ y, f y = x :=
or_iff_not_imp_right.2 $ λ h b,
acc.rec_on (is_well_founded.wf.apply b : acc s b) $ λ x H IH,
not_forall_not.1 $ λ hn,
h ⟨x, λ y, ⟨(IH _), λ ⟨a, e⟩, by rw ← e; exact
  (trichotomous _ _).resolve_right
  (not_or (hn a) (λ hl, not_exists.2 hn (f.init hl)))⟩⟩

/-- Restrict the codomain of an initial segment -/
def cod_restrict (p : set β) (f : r ≼i s) (H : ∀ a, f a ∈ p) : r ≼i subrel s p :=
⟨rel_embedding.cod_restrict p f H, λ a ⟨b, m⟩ (h : s b (f a)),
  let ⟨a', e⟩ := f.init h in ⟨a', by clear _let_match; subst e; refl⟩⟩

@[simp] theorem cod_restrict_apply (p) (f : r ≼i s) (H a) : cod_restrict p f H a = ⟨f a, H a⟩ := rfl

/-- Initial segment from an empty type. -/
def of_is_empty (r : α → α → Prop) (s : β → β → Prop) [is_empty α] : r ≼i s :=
⟨rel_embedding.of_is_empty r s, is_empty_elim⟩

/-- Initial segment embedding of an order `r` into the disjoint union of `r` and `s`. -/
def le_add (r : α → α → Prop) (s : β → β → Prop) : r ≼i sum.lex r s :=
⟨⟨⟨sum.inl, λ _ _, sum.inl.inj⟩, λ a b, sum.lex_inl_inl⟩,
  λ a b, by cases b; [exact λ _, ⟨_, rfl⟩, exact false.elim ∘ sum.lex_inr_inl]⟩

@[simp] theorem le_add_apply (r : α → α → Prop) (s : β → β → Prop)
  (a) : le_add r s a = sum.inl a := rfl

end initial_seg

/-!
### Principal segments

Order embeddings whose range is a principal segment of `s` (i.e., an interval of the form
`(-∞, top)` for some element `top` of `β`). The type of these embeddings from `r` to `s` is called
`principal_seg r s`, and denoted by `r ≺i s`. Principal segments are in particular initial
segments.
-/

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≺i s` is an order
embedding whose range is an open interval `(-∞, top)` for some element `top` of `β`. Such order
embeddings are called principal segments -/
@[nolint has_nonempty_instance]
structure principal_seg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s :=
(top : β)
(down' : ∀ b, s b top ↔ ∃ a, to_rel_embedding a = b)

localized "infix (name := principal_seg) ` ≺i `:25 := principal_seg" in initial_seg

namespace principal_seg

instance : has_coe (r ≺i s) (r ↪r s) := ⟨principal_seg.to_rel_embedding⟩
instance : has_coe_to_fun (r ≺i s) (λ _, α → β) := ⟨λ f, f⟩

@[simp] theorem coe_fn_mk (f : r ↪r s) (t o) :
  (@principal_seg.mk _ _ r s f t o : α → β) = f := rfl

@[simp] theorem coe_fn_to_rel_embedding (f : r ≺i s) : (f.to_rel_embedding : α → β) = f := rfl

@[simp] theorem coe_coe_fn (f : r ≺i s) : ((f : r ↪r s) : α → β) = f := rfl

theorem down (f : r ≺i s) : ∀ {b : β}, s b f.top ↔ ∃ a, f a = b := f.down'

theorem lt_top (f : r ≺i s) (a : α) : s (f a) f.top := f.down.2 ⟨_, rfl⟩

theorem init [is_trans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a)) : ∃ a', f a' = b :=
f.down.1 $ trans h $ f.lt_top _

/-- A principal segment is in particular an initial segment. -/
instance has_coe_initial_seg [is_trans β s] : has_coe (r ≺i s) (r ≼i s) :=
⟨λ f, ⟨f.to_rel_embedding, λ a b, f.init⟩⟩

theorem coe_coe_fn' [is_trans β s] (f : r ≺i s) : ((f : r ≼i s) : α → β) = f := rfl

theorem init_iff [is_trans β s] (f : r ≺i s) {a : α} {b : β} :
  s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
@initial_seg.init_iff α β r s f a b

theorem irrefl {r : α → α → Prop} [is_well_order α r] (f : r ≺i r) : false :=
begin
  have := f.lt_top f.top,
  rw [show f f.top = f.top, from
      initial_seg.eq ↑f (initial_seg.refl r) f.top] at this,
  exact irrefl _ this
end

instance (r : α → α → Prop) [is_well_order α r] : is_empty (r ≺i r) := ⟨λ f, f.irrefl⟩

/-- Composition of a principal segment with an initial segment, as a principal segment -/
def lt_le (f : r ≺i s) (g : s ≼i t) : r ≺i t :=
⟨@rel_embedding.trans _ _ _ r s t f g, g f.top, λ a,
 by simp only [g.init_iff, f.down', exists_and_distrib_left.symm,
   exists_swap, rel_embedding.trans_apply, exists_eq_right']; refl⟩

@[simp] theorem lt_le_apply (f : r ≺i s) (g : s ≼i t) (a : α) : (f.lt_le g) a = g (f a) :=
rel_embedding.trans_apply _ _ _

@[simp] theorem lt_le_top (f : r ≺i s) (g : s ≼i t) : (f.lt_le g).top = g f.top := rfl

/-- Composition of two principal segments as a principal segment -/
@[trans] protected def trans [is_trans γ t] (f : r ≺i s) (g : s ≺i t) : r ≺i t :=
lt_le f g

@[simp] theorem trans_apply [is_trans γ t] (f : r ≺i s) (g : s ≺i t) (a : α) :
  (f.trans g) a = g (f a) :=
lt_le_apply _ _ _

@[simp] theorem trans_top [is_trans γ t] (f : r ≺i s) (g : s ≺i t) :
  (f.trans g).top = g f.top := rfl

/-- Composition of an order isomorphism with a principal segment, as a principal segment -/
def equiv_lt (f : r ≃r s) (g : s ≺i t) : r ≺i t :=
⟨@rel_embedding.trans _ _ _ r s t f g, g.top, λ c,
 suffices (∃ (a : β), g a = c) ↔ ∃ (a : α), g (f a) = c, by simpa [g.down],
 ⟨λ ⟨b, h⟩, ⟨f.symm b, by simp only [h, rel_iso.apply_symm_apply, rel_iso.coe_coe_fn]⟩,
  λ ⟨a, h⟩, ⟨f a, h⟩⟩⟩

/-- Composition of a principal segment with an order isomorphism, as a principal segment -/
def lt_equiv {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
  (f : principal_seg r s) (g : s ≃r t) : principal_seg r t :=
⟨@rel_embedding.trans _ _ _ r s t f g, g f.top,
  begin
    intro x,
    rw [← g.apply_symm_apply x, g.map_rel_iff, f.down', exists_congr],
    intro y, exact ⟨congr_arg g, λ h, g.to_equiv.bijective.1 h⟩
  end⟩

@[simp] theorem equiv_lt_apply (f : r ≃r s) (g : s ≺i t) (a : α) : (equiv_lt f g) a = g (f a) :=
rel_embedding.trans_apply _ _ _

@[simp] theorem equiv_lt_top (f : r ≃r s) (g : s ≺i t) : (equiv_lt f g).top = g.top := rfl

/-- Given a well order `s`, there is a most one principal segment embedding of `r` into `s`. -/
instance [is_well_order β s] : subsingleton (r ≺i s) :=
⟨λ f g, begin
  have ef : (f : α → β) = g,
  { show ((f : r ≼i s) : α → β) = g,
    rw @subsingleton.elim _ _ (f : r ≼i s) g, refl },
  have et : f.top = g.top,
  { refine extensional_of_trichotomous_of_irrefl s (λ x, _),
    simp only [f.down, g.down, ef, coe_fn_to_rel_embedding] },
  cases f, cases g,
  have := rel_embedding.coe_fn_injective ef; congr'
end⟩

theorem top_eq [is_well_order γ t]
  (e : r ≃r s) (f : r ≺i t) (g : s ≺i t) : f.top = g.top :=
by rw subsingleton.elim f (principal_seg.equiv_lt e g); refl

lemma top_lt_top {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
  [is_well_order γ t]
  (f : principal_seg r s) (g : principal_seg s t) (h : principal_seg r t) : t h.top g.top :=
by { rw [subsingleton.elim h (f.trans g)], apply principal_seg.lt_top }

/-- Any element of a well order yields a principal segment -/
def of_element {α : Type*} (r : α → α → Prop) (a : α) : subrel r {b | r b a} ≺i r :=
⟨subrel.rel_embedding _ _, a, λ b,
  ⟨λ h, ⟨⟨_, h⟩, rfl⟩, λ ⟨⟨_, h⟩, rfl⟩, h⟩⟩

@[simp] theorem of_element_apply {α : Type*} (r : α → α → Prop) (a : α) (b) :
  of_element r a b = b.1 := rfl

@[simp] theorem of_element_top {α : Type*} (r : α → α → Prop) (a : α) :
  (of_element r a).top = a := rfl

/-- Restrict the codomain of a principal segment -/
def cod_restrict (p : set β) (f : r ≺i s)
  (H : ∀ a, f a ∈ p) (H₂ : f.top ∈ p) : r ≺i subrel s p :=
⟨rel_embedding.cod_restrict p f H, ⟨f.top, H₂⟩, λ ⟨b, h⟩,
  f.down.trans $ exists_congr $ λ a,
  show (⟨f a, H a⟩ : p).1 = _ ↔ _, from ⟨subtype.eq, congr_arg _⟩⟩

@[simp]
theorem cod_restrict_apply (p) (f : r ≺i s) (H H₂ a) : cod_restrict p f H H₂ a = ⟨f a, H a⟩ := rfl

@[simp]
theorem cod_restrict_top (p) (f : r ≺i s) (H H₂) : (cod_restrict p f H H₂).top = ⟨f.top, H₂⟩ := rfl

/-- Principal segment from an empty type into a type with a minimal element. -/
def of_is_empty (r : α → α → Prop) [is_empty α] {b : β} (H : ∀ b', ¬ s b' b) : r ≺i s :=
{ top := b,
  down' := by simp [H],
  ..rel_embedding.of_is_empty r s }

@[simp] theorem of_is_empty_top (r : α → α → Prop) [is_empty α] {b : β} (H : ∀ b', ¬ s b' b) :
  (of_is_empty r H).top = b := rfl

/-- Principal segment from the empty relation on `pempty` to the empty relation on `punit`. -/
@[reducible] def pempty_to_punit : @empty_relation pempty ≺i @empty_relation punit :=
@of_is_empty _ _ empty_relation _ _ punit.star $ λ x, not_false

end principal_seg

/-! ### Properties of initial and principal segments -/

/-- To an initial segment taking values in a well order, one can associate either a principal
segment (if the range is not everything, hence one can take as top the minimum of the complement
of the range) or an order isomorphism (if the range is everything). -/
noncomputable def initial_seg.lt_or_eq [is_well_order β s] (f : r ≼i s) : (r ≺i s) ⊕ (r ≃r s) :=
begin
  by_cases h : surjective f,
  { exact sum.inr (rel_iso.of_surjective f h) },
  { have h' : _, from (initial_seg.eq_or_principal f).resolve_left h,
    exact sum.inl ⟨f, classical.some h', classical.some_spec h'⟩ }
end

theorem initial_seg.lt_or_eq_apply_left [is_well_order β s]
  (f : r ≼i s) (g : r ≺i s) (a : α) : g a = f a :=
@initial_seg.eq α β r s _ g f a

theorem initial_seg.lt_or_eq_apply_right [is_well_order β s]
  (f : r ≼i s) (g : r ≃r s) (a : α) : g a = f a :=
initial_seg.eq (initial_seg.of_iso g) f a

/-- Composition of an initial segment taking values in a well order and a principal segment. -/
noncomputable def initial_seg.le_lt [is_well_order β s] [is_trans γ t] (f : r ≼i s) (g : s ≺i t) :
  r ≺i t :=
match f.lt_or_eq with
| sum.inl f' := f'.trans g
| sum.inr f' := principal_seg.equiv_lt f' g
end

@[simp] theorem initial_seg.le_lt_apply [is_well_order β s] [is_trans γ t]
  (f : r ≼i s) (g : s ≺i t) (a : α) : (f.le_lt g) a = g (f a) :=
begin
  delta initial_seg.le_lt, cases h : f.lt_or_eq with f' f',
  { simp only [principal_seg.trans_apply, f.lt_or_eq_apply_left] },
  { simp only [principal_seg.equiv_lt_apply, f.lt_or_eq_apply_right] }
end

namespace rel_embedding

/-- Given an order embedding into a well order, collapse the order embedding by filling the
gaps, to obtain an initial segment. Here, we construct the collapsed order embedding pointwise,
but the proof of the fact that it is an initial segment will be given in `collapse`. -/
noncomputable def collapse_F [is_well_order β s] (f : r ↪r s) : Π a, {b // ¬ s (f a) b} :=
(rel_embedding.well_founded f $ is_well_founded.wf).fix $ λ a IH, begin
  let S := {b | ∀ a h, s (IH a h).1 b},
  have : f a ∈ S, from λ a' h, ((trichotomous _ _)
    .resolve_left $ λ h', (IH a' h).2 $ trans (f.map_rel_iff.2 h) h')
    .resolve_left $ λ h', (IH a' h).2 $ h' ▸ f.map_rel_iff.2 h,
  exact ⟨is_well_founded.wf.min S ⟨_, this⟩,
   is_well_founded.wf.not_lt_min _ _ this⟩
end

theorem collapse_F.lt [is_well_order β s] (f : r ↪r s) {a : α}
   : ∀ {a'}, r a' a → s (collapse_F f a').1 (collapse_F f a).1 :=
show (collapse_F f a).1 ∈ {b | ∀ a' (h : r a' a), s (collapse_F f a').1 b}, begin
  unfold collapse_F, rw well_founded.fix_eq,
  apply well_founded.min_mem _ _
end

theorem collapse_F.not_lt [is_well_order β s] (f : r ↪r s) (a : α)
   {b} (h : ∀ a' (h : r a' a), s (collapse_F f a').1 b) : ¬ s b (collapse_F f a).1 :=
begin
  unfold collapse_F, rw well_founded.fix_eq,
  exact well_founded.not_lt_min _ _ _
    (show b ∈ {b | ∀ a' (h : r a' a), s (collapse_F f a').1 b}, from h)
end

/-- Construct an initial segment from an order embedding into a well order, by collapsing it
to fill the gaps. -/
noncomputable def collapse [is_well_order β s] (f : r ↪r s) : r ≼i s :=
by haveI := rel_embedding.is_well_order f; exact
⟨rel_embedding.of_monotone
  (λ a, (collapse_F f a).1) (λ a b, collapse_F.lt f),
λ a b, acc.rec_on (is_well_founded.wf.apply b : acc s b) (λ b H IH a h, begin
  let S := {a | ¬ s (collapse_F f a).1 b},
  have : S.nonempty := ⟨_, asymm h⟩,
  existsi (is_well_founded.wf : well_founded r).min S this,
  refine ((@trichotomous _ s _ _ _).resolve_left _).resolve_right _,
  { exact (is_well_founded.wf : well_founded r).min_mem S this },
  { refine collapse_F.not_lt f _ (λ a' h', _),
    by_contradiction hn,
    exact is_well_founded.wf.not_lt_min S this hn h' }
end) a⟩

theorem collapse_apply [is_well_order β s] (f : r ↪r s)
  (a) : collapse f a = (collapse_F f a).1 := rfl

end rel_embedding
