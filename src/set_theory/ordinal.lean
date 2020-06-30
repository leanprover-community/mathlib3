/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import set_theory.cardinal

/-!
# Ordinal arithmetic

Ordinals are defined as equivalences of well-ordered sets by order isomorphism.
-/

noncomputable theory

open function cardinal set equiv
open_locale classical cardinal

universes u v w
variables {α : Type*} {β : Type*} {γ : Type*}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≼i s` is an order
embedding whose range is an initial segment. That is, whenever `b < f a` in `β` then `b` is in the
range of `f`. -/
structure initial_seg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ≼o s :=
(init : ∀ a b, s b (to_order_embedding a) → ∃ a', to_order_embedding a' = b)

local infix ` ≼i `:25 := initial_seg

namespace initial_seg

instance : has_coe (r ≼i s) (r ≼o s) := ⟨initial_seg.to_order_embedding⟩
instance : has_coe_to_fun (r ≼i s) := ⟨λ _, α → β, λ f x, (f : r ≼o s) x⟩

@[simp] theorem coe_fn_mk (f : r ≼o s) (o) :
  (@initial_seg.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_order_embedding (f : r ≼i s) : (f.to_order_embedding : α → β) = f := rfl

@[simp] theorem coe_coe_fn (f : r ≼i s) : ((f : r ≼o s) : α → β) = f := rfl

theorem init' (f : r ≼i s) {a : α} {b : β} : s b (f a) → ∃ a', f a' = b :=
f.init _ _

theorem init_iff (f : r ≼i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
⟨λ h, let ⟨a', e⟩ := f.init' h in ⟨a', e, (f : r ≼o s).ord.2 (e.symm ▸ h)⟩,
 λ ⟨a', e, h⟩, e ▸ (f : r ≼o s).ord.1 h⟩

/-- An order isomorphism is an initial segment -/
def of_iso (f : r ≃o s) : r ≼i s :=
⟨f, λ a b h, ⟨f.symm b, order_iso.apply_symm_apply f _⟩⟩

/-- The identity function shows that `≼i` is reflexive -/
@[refl] protected def refl (r : α → α → Prop) : r ≼i r :=
⟨order_embedding.refl _, λ a b h, ⟨_, rfl⟩⟩

/-- Composition of functions shows that `≼i` is transitive -/
@[trans] protected def trans (f : r ≼i s) (g : s ≼i t) : r ≼i t :=
⟨f.1.trans g.1, λ a c h, begin
  simp at h ⊢,
  rcases g.2 _ _ h with ⟨b, rfl⟩, have h := g.1.ord.2 h,
  rcases f.2 _ _ h with ⟨a', rfl⟩, exact ⟨a', rfl⟩
end⟩

@[simp] theorem refl_apply (x : α) : initial_seg.refl r x = x := rfl

@[simp] theorem trans_apply (f : r ≼i s) (g : s ≼i t) (a : α) : (f.trans g) a = g (f a) := rfl

theorem unique_of_extensional [is_extensional β s] :
  well_founded r → subsingleton (r ≼i s) | ⟨h⟩ :=
⟨λ f g, begin
  suffices : (f : α → β) = g, { cases f, cases g,
    congr, exact order_embedding.coe_fn_inj this },
  funext a, have := h a, induction this with a H IH,
  refine @is_extensional.ext _ s _ _ _ (λ x, ⟨λ h, _, λ h, _⟩),
  { rcases f.init_iff.1 h with ⟨y, rfl, h'⟩,
    rw IH _ h', exact (g : r ≼o s).ord.1 h' },
  { rcases g.init_iff.1 h with ⟨y, rfl, h'⟩,
    rw ← IH _ h', exact (f : r ≼o s).ord.1 h' }
end⟩

instance [is_well_order β s] : subsingleton (r ≼i s) :=
⟨λ a, @subsingleton.elim _ (unique_of_extensional
  (@order_embedding.well_founded _ _ r s a is_well_order.wf)) a⟩

protected theorem eq [is_well_order β s] (f g : r ≼i s) (a) : f a = g a :=
by rw subsingleton.elim f g

theorem antisymm.aux [is_well_order α r] (f : r ≼i s) (g : s ≼i r) : left_inverse g f :=
initial_seg.eq (f.trans g) (initial_seg.refl _)

/-- If we have order embeddings between `α` and `β` whose images are initial segments, and `β`
is a well-order then `α` and `β` are order-isomorphic. -/
def antisymm [is_well_order β s] (f : r ≼i s) (g : s ≼i r) : r ≃o s :=
by haveI := f.to_order_embedding.is_well_order; exact
⟨⟨f, g, antisymm.aux f g, antisymm.aux g f⟩, f.ord'⟩

@[simp] theorem antisymm_to_fun [is_well_order β s]
  (f : r ≼i s) (g : s ≼i r) : (antisymm f g : α → β) = f := rfl

@[simp] theorem antisymm_symm [is_well_order α r] [is_well_order β s]
  (f : r ≼i s) (g : s ≼i r) : (antisymm f g).symm = antisymm g f :=
order_iso.coe_fn_injective rfl

theorem eq_or_principal [is_well_order β s] (f : r ≼i s) :
  surjective f ∨ ∃ b, ∀ x, s x b ↔ ∃ y, f y = x :=
or_iff_not_imp_right.2 $ λ h b,
acc.rec_on (is_well_order.wf.apply b : acc s b) $ λ x H IH,
not_forall_not.1 $ λ hn,
h ⟨x, λ y, ⟨(IH _), λ ⟨a, e⟩, by rw ← e; exact
  (trichotomous _ _).resolve_right
  (not_or (hn a) (λ hl, not_exists.2 hn (f.init' hl)))⟩⟩

/-- Restrict the codomain of an initial segment -/
def cod_restrict (p : set β) (f : r ≼i s) (H : ∀ a, f a ∈ p) : r ≼i subrel s p :=
⟨order_embedding.cod_restrict p f H, λ a ⟨b, m⟩ (h : s b (f a)),
  let ⟨a', e⟩ := f.init' h in ⟨a', by clear _let_match; subst e; refl⟩⟩

@[simp] theorem cod_restrict_apply (p) (f : r ≼i s) (H a) : cod_restrict p f H a = ⟨f a, H a⟩ := rfl

def le_add (r : α → α → Prop) (s : β → β → Prop) : r ≼i sum.lex r s :=
⟨⟨⟨sum.inl, λ _ _, sum.inl.inj⟩, λ a b, sum.lex_inl_inl.symm⟩,
  λ a b, by cases b; [exact λ _, ⟨_, rfl⟩, exact false.elim ∘ sum.lex_inr_inl]⟩

@[simp] theorem le_add_apply (r : α → α → Prop) (s : β → β → Prop)
  (a) : le_add r s a = sum.inl a := rfl

end initial_seg

structure principal_seg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ≼o s :=
(top : β)
(down : ∀ b, s b top ↔ ∃ a, to_order_embedding a = b)

local infix ` ≺i `:25 := principal_seg

namespace principal_seg

instance : has_coe (r ≺i s) (r ≼o s) := ⟨principal_seg.to_order_embedding⟩
instance : has_coe_to_fun (r ≺i s) := ⟨λ _, α → β, λ f, f⟩

@[simp] theorem coe_fn_mk (f : r ≼o s) (t o) :
  (@principal_seg.mk _ _ r s f t o : α → β) = f := rfl

@[simp] theorem coe_fn_to_order_embedding (f : r ≺i s) : (f.to_order_embedding : α → β) = f := rfl

@[simp] theorem coe_coe_fn (f : r ≺i s) : ((f : r ≼o s) : α → β) = f := rfl

theorem down' (f : r ≺i s) {b : β} : s b f.top ↔ ∃ a, f a = b :=
f.down _

theorem lt_top (f : r ≺i s) (a : α) : s (f a) f.top :=
f.down'.2 ⟨_, rfl⟩

theorem init [is_trans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a)) : ∃ a', f a' = b :=
f.down'.1 $ trans h $ f.lt_top _

instance has_coe_initial_seg [is_trans β s] : has_coe (r ≺i s) (r ≼i s) :=
⟨λ f, ⟨f.to_order_embedding, λ a b, f.init⟩⟩

theorem coe_coe_fn' [is_trans β s] (f : r ≺i s) : ((f : r ≼i s) : α → β) = f := rfl

theorem init_iff [is_trans β s] (f : r ≺i s) {a : α} {b : β} :
  s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
@initial_seg.init_iff α β r s f a b

theorem irrefl (r : α → α → Prop) [is_well_order α r] (f : r ≺i r) : false :=
begin
  have := f.lt_top f.top,
  rw [show f f.top = f.top, from
      initial_seg.eq ↑f (initial_seg.refl r) f.top] at this,
  exact irrefl _ this
end

def lt_le (f : r ≺i s) (g : s ≼i t) : r ≺i t :=
⟨@order_embedding.trans _ _ _ r s t f g, g f.top, λ a,
 by simp only [g.init_iff, f.down', exists_and_distrib_left.symm,
   exists_swap, order_embedding.trans_apply, exists_eq_right']; refl⟩

@[simp] theorem lt_le_apply (f : r ≺i s) (g : s ≼i t) (a : α) : (f.lt_le g) a = g (f a) :=
order_embedding.trans_apply _ _ _

@[simp] theorem lt_le_top (f : r ≺i s) (g : s ≼i t) : (f.lt_le g).top = g f.top := rfl

@[trans] protected def trans [is_trans γ t] (f : r ≺i s) (g : s ≺i t) : r ≺i t :=
lt_le f g

@[simp] theorem trans_apply [is_trans γ t] (f : r ≺i s) (g : s ≺i t) (a : α) :
  (f.trans g) a = g (f a) :=
lt_le_apply _ _ _

@[simp] theorem trans_top [is_trans γ t] (f : r ≺i s) (g : s ≺i t) :
  (f.trans g).top = g f.top := rfl

def equiv_lt (f : r ≃o s) (g : s ≺i t) : r ≺i t :=
⟨@order_embedding.trans _ _ _ r s t f g, g.top, λ c,
 suffices (∃ (a : β), g a = c) ↔ ∃ (a : α), g (f a) = c, by simpa [g.down],
 ⟨λ ⟨b, h⟩, ⟨f.symm b, by simp only [h, order_iso.apply_symm_apply, order_iso.coe_coe_fn]⟩,
  λ ⟨a, h⟩, ⟨f a, h⟩⟩⟩

def lt_equiv {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
  (f : principal_seg r s) (g : s ≃o t) : principal_seg r t :=
⟨@order_embedding.trans _ _ _ r s t f g, g f.top,
  begin
    intro x,
    rw [← g.apply_symm_apply x, ← g.ord, f.down', exists_congr],
    intro y, exact ⟨congr_arg g, λ h, g.to_equiv.bijective.1 h⟩
  end⟩

@[simp] theorem equiv_lt_apply (f : r ≃o s) (g : s ≺i t) (a : α) : (equiv_lt f g) a = g (f a) :=
order_embedding.trans_apply _ _ _

@[simp] theorem equiv_lt_top (f : r ≃o s) (g : s ≺i t) : (equiv_lt f g).top = g.top := rfl

instance [is_well_order β s] : subsingleton (r ≺i s) :=
⟨λ f g, begin
  have ef : (f : α → β) = g,
  { show ((f : r ≼i s) : α → β) = g,
    rw @subsingleton.elim _ _ (f : r ≼i s) g, refl },
  have et : f.top = g.top,
  { refine @is_extensional.ext _ s _ _ _ (λ x, _),
    simp only [f.down, g.down, ef, coe_fn_to_order_embedding] },
  cases f, cases g,
  have := order_embedding.coe_fn_inj ef; congr'
end⟩

theorem top_eq [is_well_order γ t]
  (e : r ≃o s) (f : r ≺i t) (g : s ≺i t) : f.top = g.top :=
by rw subsingleton.elim f (principal_seg.equiv_lt e g); refl

lemma top_lt_top {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
  [is_well_order γ t]
  (f : principal_seg r s) (g : principal_seg s t) (h : principal_seg r t) : t h.top g.top :=
by { rw [subsingleton.elim h (f.trans g)], apply principal_seg.lt_top }

/-- Any element of a well order yields a principal segment -/
def of_element {α : Type*} (r : α → α → Prop) (a : α) : subrel r {b | r b a} ≺i r :=
⟨subrel.order_embedding _ _, a, λ b,
  ⟨λ h, ⟨⟨_, h⟩, rfl⟩, λ ⟨⟨_, h⟩, rfl⟩, h⟩⟩

@[simp] theorem of_element_apply {α : Type*} (r : α → α → Prop) (a : α) (b) :
  of_element r a b = b.1 := rfl

@[simp] theorem of_element_top {α : Type*} (r : α → α → Prop) (a : α) :
  (of_element r a).top = a := rfl

/-- Restrict the codomain of a principal segment -/
def cod_restrict (p : set β) (f : r ≺i s)
  (H : ∀ a, f a ∈ p) (H₂ : f.top ∈ p) : r ≺i subrel s p :=
⟨order_embedding.cod_restrict p f H, ⟨f.top, H₂⟩, λ ⟨b, h⟩,
  f.down'.trans $ exists_congr $ λ a,
  show (⟨f a, H a⟩ : p).1 = _ ↔ _, from ⟨subtype.eq, congr_arg _⟩⟩

@[simp]
theorem cod_restrict_apply (p) (f : r ≺i s) (H H₂ a) : cod_restrict p f H H₂ a = ⟨f a, H a⟩ := rfl

@[simp]
theorem cod_restrict_top (p) (f : r ≺i s) (H H₂) : (cod_restrict p f H H₂).top = ⟨f.top, H₂⟩ := rfl

end principal_seg

def initial_seg.lt_or_eq [is_well_order β s] (f : r ≼i s) :
  (r ≺i s) ⊕ (r ≃o s) :=
if h : surjective f then sum.inr (order_iso.of_surjective f h) else
have h' : _, from (initial_seg.eq_or_principal f).resolve_left h,
sum.inl ⟨f, classical.some h', classical.some_spec h'⟩

theorem initial_seg.lt_or_eq_apply_left [is_well_order β s]
  (f : r ≼i s) (g : r ≺i s) (a : α) : g a = f a :=
@initial_seg.eq α β r s _ g f a

theorem initial_seg.lt_or_eq_apply_right [is_well_order β s]
  (f : r ≼i s) (g : r ≃o s) (a : α) : g a = f a :=
initial_seg.eq (initial_seg.of_iso g) f a

def initial_seg.le_lt [is_well_order β s] [is_trans γ t] (f : r ≼i s) (g : s ≺i t) : r ≺i t :=
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

namespace order_embedding

def collapse_F [is_well_order β s] (f : r ≼o s) : Π a, {b // ¬ s (f a) b} :=
(order_embedding.well_founded f $ is_well_order.wf).fix $ λ a IH, begin
  let S := {b | ∀ a h, s (IH a h).1 b},
  have : f a ∈ S, from λ a' h, ((trichotomous _ _)
    .resolve_left $ λ h', (IH a' h).2 $ trans (f.ord.1 h) h')
    .resolve_left $ λ h', (IH a' h).2 $ h' ▸ f.ord.1 h,
  exact ⟨is_well_order.wf.min S ⟨_, this⟩,
   is_well_order.wf.not_lt_min _ _ this⟩
end

theorem collapse_F.lt [is_well_order β s] (f : r ≼o s) {a : α}
   : ∀ {a'}, r a' a → s (collapse_F f a').1 (collapse_F f a).1 :=
show (collapse_F f a).1 ∈ {b | ∀ a' (h : r a' a), s (collapse_F f a').1 b}, begin
  unfold collapse_F, rw well_founded.fix_eq,
  apply well_founded.min_mem _ _
end

theorem collapse_F.not_lt [is_well_order β s] (f : r ≼o s) (a : α)
   {b} (h : ∀ a' (h : r a' a), s (collapse_F f a').1 b) : ¬ s b (collapse_F f a).1 :=
begin
  unfold collapse_F, rw well_founded.fix_eq,
  exact well_founded.not_lt_min _ _ _
    (show b ∈ {b | ∀ a' (h : r a' a), s (collapse_F f a').1 b}, from h)
end

/-- Construct an initial segment from an order embedding. -/
def collapse [is_well_order β s] (f : r ≼o s) : r ≼i s :=
by haveI := order_embedding.is_well_order f; exact
⟨order_embedding.of_monotone
  (λ a, (collapse_F f a).1) (λ a b, collapse_F.lt f),
λ a b, acc.rec_on (is_well_order.wf.apply b : acc s b) (λ b H IH a h, begin
  let S := {a | ¬ s (collapse_F f a).1 b},
  have : S.nonempty := ⟨_, asymm h⟩,
  existsi (is_well_order.wf : well_founded r).min S this,
  refine ((@trichotomous _ s _ _ _).resolve_left _).resolve_right _,
  { exact (is_well_order.wf : well_founded r).min_mem S this },
  { refine collapse_F.not_lt f _ (λ a' h', _),
    by_contradiction hn,
    exact is_well_order.wf.not_lt_min S this hn h' }
end) a⟩

theorem collapse_apply [is_well_order β s] (f : r ≼o s)
  (a) : collapse f a = (collapse_F f a).1 := rfl

end order_embedding

section well_ordering_thm
parameter {σ : Type u}
open function

theorem nonempty_embedding_to_cardinal : nonempty (σ ↪ cardinal.{u}) :=
embedding.total.resolve_left $ λ ⟨⟨f, hf⟩⟩,
  let g : σ → cardinal.{u} := inv_fun f in
  let ⟨x, (hx : g x = 2 ^ sum g)⟩ := inv_fun_surjective hf (2 ^ sum g) in
  have g x ≤ sum g, from le_sum.{u u} g x,
  not_le_of_gt (by rw hx; exact cantor _) this

/-- An embedding of any type to the set of cardinals. -/
def embedding_to_cardinal : σ ↪ cardinal.{u} := classical.choice nonempty_embedding_to_cardinal

/-- The relation whose existence is given by the well-ordering theorem -/
def well_ordering_rel : σ → σ → Prop := embedding_to_cardinal ⁻¹'o (<)

instance well_ordering_rel.is_well_order : is_well_order σ well_ordering_rel :=
(order_embedding.preimage _ _).is_well_order

end well_ordering_thm

structure Well_order : Type (u+1) :=
(α : Type u)
(r : α → α → Prop)
(wo : is_well_order α r)

attribute [instance] Well_order.wo

namespace Well_order

instance : inhabited Well_order := ⟨⟨pempty, _, empty_relation.is_well_order⟩⟩

end Well_order

instance ordinal.is_equivalent : setoid Well_order :=
{ r     := λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, nonempty (r ≃o s),
  iseqv := ⟨λ⟨α, r, _⟩, ⟨order_iso.refl _⟩,
    λ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨e⟩, ⟨e.symm⟩,
    λ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨e₁⟩ ⟨e₂⟩, ⟨e₁.trans e₂⟩⟩ }

/-- `ordinal.{u}` is the type of well orders in `Type u`,
  quotient by order isomorphism. -/
def ordinal : Type (u + 1) := quotient ordinal.is_equivalent

namespace ordinal

/-- The order type of a well order is an ordinal. -/
def type (r : α → α → Prop) [wo : is_well_order α r] : ordinal :=
⟦⟨α, r, wo⟩⟧

/-- The order type of an element inside a well order. -/
def typein (r : α → α → Prop) [is_well_order α r] (a : α) : ordinal :=
type (subrel r {b | r b a})

theorem type_def (r : α → α → Prop) [wo : is_well_order α r] :
  @eq ordinal ⟦⟨α, r, wo⟩⟧ (type r) := rfl

@[simp] theorem type_def' (r : α → α → Prop) [is_well_order α r] {wo} :
  @eq ordinal ⟦⟨α, r, wo⟩⟧ (type r) := rfl

theorem type_eq {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] :
  type r = type s ↔ nonempty (r ≃o s) := quotient.eq

@[simp] lemma type_out (o : ordinal) : type o.out.r = o :=
by { refine eq.trans _ (by rw [←quotient.out_eq o]), cases quotient.out o, refl }

@[elab_as_eliminator] theorem induction_on {C : ordinal → Prop}
  (o : ordinal) (H : ∀ α r [is_well_order α r], C (type r)) : C o :=
quot.induction_on o $ λ ⟨α, r, wo⟩, @H α r wo

/-- Ordinal less-equal is defined such that
  well orders `r` and `s` satisfy `type r ≤ type s` if there exists
  a function embedding `r` as an initial segment of `s`. -/
protected def le (a b : ordinal) : Prop :=
quotient.lift_on₂ a b (λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, nonempty (r ≼i s)) $
λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
propext ⟨
  λ ⟨h⟩, ⟨(initial_seg.of_iso f.symm).trans $
    h.trans (initial_seg.of_iso g)⟩,
  λ ⟨h⟩, ⟨(initial_seg.of_iso f).trans $
    h.trans (initial_seg.of_iso g.symm)⟩⟩

instance : has_le ordinal := ⟨ordinal.le⟩

theorem type_le {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] :
  type r ≤ type s ↔ nonempty (r ≼i s) := iff.rfl

theorem type_le' {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] : type r ≤ type s ↔ nonempty (r ≼o s) :=
⟨λ ⟨f⟩, ⟨f⟩, λ ⟨f⟩, ⟨f.collapse⟩⟩

/-- Ordinal less-than is defined such that
  well orders `r` and `s` satisfy `type r < type s` if there exists
  a function embedding `r` as a principal segment of `s`. -/
def lt (a b : ordinal) : Prop :=
quotient.lift_on₂ a b (λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, nonempty (r ≺i s)) $
λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
by exactI propext ⟨
  λ ⟨h⟩, ⟨principal_seg.equiv_lt f.symm $
    h.lt_le (initial_seg.of_iso g)⟩,
  λ ⟨h⟩, ⟨principal_seg.equiv_lt f $
    h.lt_le (initial_seg.of_iso g.symm)⟩⟩

instance : has_lt ordinal := ⟨ordinal.lt⟩

@[simp] theorem type_lt {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] :
  type r < type s ↔ nonempty (r ≺i s) := iff.rfl

instance : partial_order ordinal :=
{ le := (≤),
  lt := (<),
  le_refl := quot.ind $ by exact λ ⟨α, r, wo⟩, ⟨initial_seg.refl _⟩,
  le_trans := λ a b c, quotient.induction_on₃ a b c $
    λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ ⟨g⟩, ⟨f.trans g⟩,
  lt_iff_le_not_le := λ a b, quotient.induction_on₂ a b $
    λ ⟨α, r, _⟩ ⟨β, s, _⟩, by exactI
      ⟨λ ⟨f⟩, ⟨⟨f⟩, λ ⟨g⟩, (f.lt_le g).irrefl _⟩,
      λ ⟨⟨f⟩, h⟩, sum.rec_on f.lt_or_eq (λ g, ⟨g⟩)
       (λ g, (h ⟨initial_seg.of_iso g.symm⟩).elim)⟩,
  le_antisymm := λ x b, show x ≤ b → b ≤ x → x = b, from
    quotient.induction_on₂ x b $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨h₁⟩ ⟨h₂⟩,
    by exactI quot.sound ⟨initial_seg.antisymm h₁ h₂⟩ }

def initial_seg_out {α β : ordinal} (h : α ≤ β) : initial_seg α.out.r β.out.r :=
begin
  rw [←quotient.out_eq α, ←quotient.out_eq β] at h, revert h,
  cases quotient.out α, cases quotient.out β, exact classical.choice
end

def principal_seg_out {α β : ordinal} (h : α < β) : principal_seg α.out.r β.out.r :=
begin
  rw [←quotient.out_eq α, ←quotient.out_eq β] at h, revert h,
  cases quotient.out α, cases quotient.out β, exact classical.choice
end

def order_iso_out {α β : ordinal} (h : α = β) : order_iso α.out.r β.out.r :=
begin
  rw [←quotient.out_eq α, ←quotient.out_eq β] at h, revert h,
  cases quotient.out α, cases quotient.out β, exact classical.choice ∘ quotient.exact
end

theorem typein_lt_type (r : α → α → Prop) [is_well_order α r]
  (a : α) : typein r a < type r :=
⟨principal_seg.of_element _ _⟩

@[simp] theorem typein_top {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (f : r ≺i s) :
  typein s f.top = type r :=
eq.symm $ quot.sound ⟨order_iso.of_surjective
  (order_embedding.cod_restrict _ f f.lt_top)
  (λ ⟨a, h⟩, by rcases f.down'.1 h with ⟨b, rfl⟩; exact ⟨b, rfl⟩)⟩

@[simp] theorem typein_apply {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (f : r ≼i s) (a : α) :
  ordinal.typein s (f a) = ordinal.typein r a :=
eq.symm $ quotient.sound ⟨order_iso.of_surjective
  (order_embedding.cod_restrict _
    ((subrel.order_embedding _ _).trans f)
    (λ ⟨x, h⟩, by rw [order_embedding.trans_apply]; exact f.to_order_embedding.ord.1 h))
  (λ ⟨y, h⟩, by rcases f.init' h with ⟨a, rfl⟩;
    exact ⟨⟨a, f.to_order_embedding.ord.2 h⟩, subtype.eq $ order_embedding.trans_apply _ _ _⟩)⟩

@[simp] theorem typein_lt_typein (r : α → α → Prop) [is_well_order α r]
  {a b : α} : typein r a < typein r b ↔ r a b :=
⟨λ ⟨f⟩, begin
  have : f.top.1 = a,
  { let f' := principal_seg.of_element r a,
    let g' := f.trans (principal_seg.of_element r b),
    have : g'.top = f'.top, {rw subsingleton.elim f' g'},
    exact this },
  rw ← this, exact f.top.2
end, λ h, ⟨principal_seg.cod_restrict _
  (principal_seg.of_element r a)
  (λ x, @trans _ r _ _ _ _ x.2 h) h⟩⟩

theorem typein_surj (r : α → α → Prop) [is_well_order α r]
  {o} (h : o < type r) : ∃ a, typein r a = o :=
induction_on o (λ β s _ ⟨f⟩, by exactI ⟨f.top, typein_top _⟩) h

lemma typein_injective (r : α → α → Prop) [is_well_order α r] : injective (typein r) :=
injective_of_increasing r (<) (typein r) (λ x y, (typein_lt_typein r).2)

theorem typein_inj (r : α → α → Prop) [is_well_order α r]
  {a b} : typein r a = typein r b ↔ a = b :=
injective.eq_iff (typein_injective r)

/-- `enum r o h` is the `o`-th element of `α` ordered by `r`.
  That is, `enum` maps an initial segment of the ordinals, those
  less than the order type of `r`, to the elements of `α`. -/
def enum (r : α → α → Prop) [is_well_order α r] (o) : o < type r → α :=
quot.rec_on o (λ ⟨β, s, _⟩ h, (classical.choice h).top) $
λ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨h⟩, begin
  resetI, refine funext (λ (H₂ : type t < type r), _),
  have H₁ : type s < type r, {rwa type_eq.2 ⟨h⟩},
  have : ∀ {o e} (H : o < type r), @@eq.rec
   (λ (o : ordinal), o < type r → α)
   (λ (h : type s < type r), (classical.choice h).top)
     e H = (classical.choice H₁).top, {intros, subst e},
  exact (this H₂).trans (principal_seg.top_eq h
    (classical.choice H₁) (classical.choice H₂))
end

theorem enum_type {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (f : s ≺i r)
  {h : type s < type r} : enum r (type s) h = f.top :=
principal_seg.top_eq (order_iso.refl _) _ _

@[simp] theorem enum_typein (r : α → α → Prop) [is_well_order α r] (a : α)
  {h : typein r a < type r} : enum r (typein r a) h = a :=
enum_type (principal_seg.of_element r a)

@[simp] theorem typein_enum (r : α → α → Prop) [is_well_order α r]
  {o} (h : o < type r) : typein r (enum r o h) = o :=
let ⟨a, e⟩ := typein_surj r h in
by clear _let_match; subst e; rw enum_typein

def typein_iso (r : α → α → Prop) [is_well_order α r] : r ≃o subrel (<) (< type r) :=
⟨⟨λ x, ⟨typein r x, typein_lt_type r x⟩, λ x, enum r x.1 x.2, λ y, enum_typein r y,
 λ ⟨y, hy⟩, subtype.eq (typein_enum r hy)⟩,
  λ a b, (typein_lt_typein r).symm⟩

theorem enum_lt {r : α → α → Prop} [is_well_order α r]
  {o₁ o₂ : ordinal} (h₁ : o₁ < type r) (h₂ : o₂ < type r) :
  r (enum r o₁ h₁) (enum r o₂ h₂) ↔ o₁ < o₂ :=
by rw [← typein_lt_typein r, typein_enum, typein_enum]

lemma order_iso_enum' {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s]
  (f : order_iso r s) (o : ordinal) : ∀(hr : o < type r) (hs : o < type s),
  f (enum r o hr) = enum s o hs :=
begin
  refine induction_on o _, rintros γ t wo ⟨g⟩ ⟨h⟩,
  resetI, rw [enum_type g, enum_type (principal_seg.lt_equiv g f)], refl
end

lemma order_iso_enum {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s]
  (f : order_iso r s) (o : ordinal) (hr : o < type r) :
  f (enum r o hr) =
  enum s o (by {convert hr using 1, apply quotient.sound, exact ⟨f.symm⟩ }) :=
order_iso_enum' _ _ _ _

theorem wf : @well_founded ordinal (<) :=
⟨λ a, induction_on a $ λ α r wo, by exactI
suffices ∀ a, acc (<) (typein r a), from
⟨_, λ o h, let ⟨a, e⟩ := typein_surj r h in e ▸ this a⟩,
λ a, acc.rec_on (wo.wf.apply a) $ λ x H IH, ⟨_, λ o h, begin
  rcases typein_surj r (lt_trans h (typein_lt_type r _)) with ⟨b, rfl⟩,
  exact IH _ ((typein_lt_typein r).1 h)
end⟩⟩

instance : has_well_founded ordinal := ⟨(<), wf⟩

/-- The cardinal of an ordinal is the cardinal of any
  set with that order type. -/
def card (o : ordinal) : cardinal :=
quot.lift_on o (λ ⟨α, r, _⟩, mk α) $
λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨e⟩, quotient.sound ⟨e.to_equiv⟩

@[simp] theorem card_type (r : α → α → Prop) [is_well_order α r] :
  card (type r) = mk α := rfl

lemma card_typein {r : α → α → Prop} [wo : is_well_order α r] (x : α) :
  mk {y // r y x} = (typein r x).card := rfl

theorem card_le_card {o₁ o₂ : ordinal} : o₁ ≤ o₂ → card o₁ ≤ card o₂ :=
induction_on o₁ $ λ α r _, induction_on o₂ $ λ β s _ ⟨⟨⟨f, _⟩, _⟩⟩, ⟨f⟩

instance : has_zero ordinal :=
⟨⟦⟨pempty, empty_relation, by apply_instance⟩⟧⟩

instance : inhabited ordinal := ⟨0⟩

theorem zero_eq_type_empty : 0 = @type empty empty_relation _ :=
quotient.sound ⟨⟨empty_equiv_pempty.symm, λ _ _, iff.rfl⟩⟩

@[simp] theorem card_zero : card 0 = 0 := rfl

theorem zero_le (o : ordinal) : 0 ≤ o :=
induction_on o $ λ α r _,
⟨⟨⟨embedding.of_not_nonempty $ λ ⟨a⟩, a.elim,
  λ a, a.elim⟩, λ a, a.elim⟩⟩

@[simp] theorem le_zero {o : ordinal} : o ≤ 0 ↔ o = 0 :=
by simp only [le_antisymm_iff, zero_le, and_true]

theorem pos_iff_ne_zero {o : ordinal} : 0 < o ↔ o ≠ 0 :=
by simp only [lt_iff_le_and_ne, zero_le, true_and, ne.def, eq_comm]

instance : has_one ordinal :=
⟨⟦⟨punit, empty_relation, by apply_instance⟩⟧⟩

theorem one_eq_type_unit : 1 = @type unit empty_relation _ :=
quotient.sound ⟨⟨punit_equiv_punit, λ _ _, iff.rfl⟩⟩

@[simp] theorem card_one : card 1 = 1 := rfl

instance : has_add ordinal.{u} :=
⟨λo₁ o₂, quotient.lift_on₂ o₁ o₂
  (λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, ⟦⟨α ⊕ β, sum.lex r s, by exactI sum.lex.is_well_order⟩⟧
    : Well_order → Well_order → ordinal) $
λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
quot.sound ⟨order_iso.sum_lex_congr f g⟩⟩

@[simp] theorem type_add {α β : Type u} (r : α → α → Prop) (s : β → β → Prop)
  [is_well_order α r] [is_well_order β s] : type r + type s = type (sum.lex r s) := rfl

/-- The ordinal successor is the smallest ordinal larger than `o`.
  It is defined as `o + 1`. -/
def succ (o : ordinal) : ordinal := o + 1

theorem succ_eq_add_one (o) : succ o = o + 1 := rfl

theorem lt_succ_self (o : ordinal.{u}) : o < succ o :=
induction_on o $ λ α r _, ⟨⟨⟨⟨λ x, sum.inl x, λ _ _, sum.inl.inj⟩,
  λ _ _, sum.lex_inl_inl.symm⟩,
sum.inr punit.star, λ b, sum.rec_on b
  (λ x, ⟨λ _, ⟨x, rfl⟩, λ _, sum.lex.sep _ _⟩)
  (λ x, sum.lex_inr_inr.trans ⟨false.elim, λ ⟨x, H⟩, sum.inl_ne_inr H⟩)⟩⟩

theorem succ_pos (o : ordinal) : 0 < succ o :=
lt_of_le_of_lt (zero_le _) (lt_succ_self _)

theorem succ_ne_zero (o : ordinal) : succ o ≠ 0 :=
ne_of_gt $ succ_pos o

theorem succ_le {a b : ordinal} : succ a ≤ b ↔ a < b :=
⟨lt_of_lt_of_le (lt_succ_self _),
induction_on a $ λ α r hr, induction_on b $ λ β s hs ⟨⟨f, t, hf⟩⟩, begin
  refine ⟨⟨@order_embedding.of_monotone (α ⊕ punit) β _ _
    (@sum.lex.is_well_order _ _ _ _ hr _).1.1
    (@is_asymm_of_is_trans_of_is_irrefl _ _ hs.1.2.2 hs.1.2.1)
    (sum.rec _ _) (λ a b, _), λ a b, _⟩⟩,
  { exact f }, { exact λ _, t },
  { rcases a with a|_; rcases b with b|_,
    { simpa only [sum.lex_inl_inl] using f.ord.1 },
    { intro _, rw hf, exact ⟨_, rfl⟩ },
    { exact false.elim ∘ sum.lex_inr_inl },
    { exact false.elim ∘ sum.lex_inr_inr.1 } },
  { rcases a with a|_,
    { intro h, have := @principal_seg.init _ _ _ _ hs.1.2.2 ⟨f, t, hf⟩ _ _ h,
      cases this with w h, exact ⟨sum.inl w, h⟩ },
    { intro h, cases (hf b).1 h with w h, exact ⟨sum.inl w, h⟩ } }
end⟩

@[simp] theorem card_add (o₁ o₂ : ordinal) : card (o₁ + o₂) = card o₁ + card o₂ :=
induction_on o₁ $ λ α r _, induction_on o₂ $ λ β s _, rfl

@[simp] theorem card_succ (o : ordinal) : card (succ o) = card o + 1 :=
by simp only [succ, card_add, card_one]

@[simp] theorem card_nat (n : ℕ) : card.{u} n = n :=
by induction n; [refl, simp only [card_add, card_one, nat.cast_succ, *]]

theorem nat_cast_succ (n : ℕ) : (succ n : ordinal) = n.succ := rfl

instance : add_monoid ordinal.{u} :=
{ add       := (+),
  zero      := 0,
  zero_add  := λ o, induction_on o $ λ α r _, eq.symm $ quotient.sound
    ⟨⟨(pempty_sum α).symm, λ a b, sum.lex_inr_inr.symm⟩⟩,
  add_zero  := λ o, induction_on o $ λ α r _, eq.symm $ quotient.sound
    ⟨⟨(sum_pempty α).symm, λ a b, sum.lex_inl_inl.symm⟩⟩,
  add_assoc := λ o₁ o₂ o₃, quotient.induction_on₃ o₁ o₂ o₃ $
    λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩, quot.sound
    ⟨⟨sum_assoc _ _ _, λ a b,
    begin rcases a with ⟨a|a⟩|a; rcases b with ⟨b|b⟩|b;
      simp only [sum_assoc_apply_in1, sum_assoc_apply_in2, sum_assoc_apply_in3,
        sum.lex_inl_inl, sum.lex_inr_inr, sum.lex.sep, sum.lex_inr_inl] end⟩⟩ }

theorem add_succ (o₁ o₂ : ordinal) : o₁ + succ o₂ = succ (o₁ + o₂) :=
(add_assoc _ _ _).symm

@[simp] theorem succ_zero : succ 0 = 1 := zero_add _

theorem one_le_iff_pos {o : ordinal} : 1 ≤ o ↔ 0 < o :=
by rw [← succ_zero, succ_le]

theorem one_le_iff_ne_zero {o : ordinal} : 1 ≤ o ↔ o ≠ 0 :=
by rw [one_le_iff_pos, pos_iff_ne_zero]

theorem add_le_add_left {a b : ordinal} : a ≤ b → ∀ c, c + a ≤ c + b :=
induction_on a $ λ α₁ r₁ _, induction_on b $ λ α₂ r₂ _ ⟨⟨⟨f, fo⟩, fi⟩⟩ c,
induction_on c $ λ β s _,
⟨⟨⟨(embedding.refl _).sum_congr f,
  λ a b, match a, b with
    | sum.inl a, sum.inl b := sum.lex_inl_inl.trans sum.lex_inl_inl.symm
    | sum.inl a, sum.inr b := by apply iff_of_true; apply sum.lex.sep
    | sum.inr a, sum.inl b := by apply iff_of_false; exact sum.lex_inr_inl
    | sum.inr a, sum.inr b := sum.lex_inr_inr.trans $ fo.trans sum.lex_inr_inr.symm
    end⟩,
  λ a b H, match a, b, H with
    | _,         sum.inl b, _ := ⟨sum.inl b, rfl⟩
    | sum.inl a, sum.inr b, H := (sum.lex_inr_inl H).elim
    | sum.inr a, sum.inr b, H := let ⟨w, h⟩ := fi _ _ (sum.lex_inr_inr.1 H) in
        ⟨sum.inr w, congr_arg sum.inr h⟩
  end⟩⟩

theorem le_add_right (a b : ordinal) : a ≤ a + b :=
by simpa only [add_zero] using add_le_add_left (zero_le b) a

theorem add_le_add_iff_left (a) {b c : ordinal} : a + b ≤ a + c ↔ b ≤ c :=
⟨induction_on a $ λ α r hr, induction_on b $ λ β₁ s₁ hs₁, induction_on c $ λ β₂ s₂ hs₂ ⟨f⟩, ⟨
  have fl : ∀ a, f (sum.inl a) = sum.inl a := λ a,
    by simpa only [initial_seg.trans_apply, initial_seg.le_add_apply]
      using @initial_seg.eq _ _ _ _ (@sum.lex.is_well_order _ _ _ _ hr hs₂)
        ((initial_seg.le_add r s₁).trans f) (initial_seg.le_add r s₂) a,
  have ∀ b, {b' // f (sum.inr b) = sum.inr b'}, begin
    intro b, cases e : f (sum.inr b),
    { rw ← fl at e, have := f.inj' e, contradiction },
    { exact ⟨_, rfl⟩ }
  end,
  let g (b) := (this b).1 in
  have fr : ∀ b, f (sum.inr b) = sum.inr (g b), from λ b, (this b).2,
  ⟨⟨⟨g, λ x y h, by injection f.inj'
    (by rw [fr, fr, h] : f (sum.inr x) = f (sum.inr y))⟩,
    λ a b, by simpa only [sum.lex_inr_inr, fr, order_embedding.coe_fn_to_embedding,
        initial_seg.coe_fn_to_order_embedding, function.embedding.coe_fn_mk]
      using @order_embedding.ord _ _ _ _ f.to_order_embedding (sum.inr a) (sum.inr b)⟩,
    λ a b H, begin
      rcases f.init' (by rw fr; exact sum.lex_inr_inr.2 H) with ⟨a'|a', h⟩,
      { rw fl at h, cases h },
      { rw fr at h, exact ⟨a', sum.inr.inj h⟩ }
    end⟩⟩,
λ h, add_le_add_left h _⟩

theorem add_left_cancel (a) {b c : ordinal} : a + b = a + c ↔ b = c :=
by simp only [le_antisymm_iff, add_le_add_iff_left]

/-- The universe lift operation for ordinals, which embeds `ordinal.{u}` as
  a proper initial segment of `ordinal.{v}` for `v > u`. -/
def lift (o : ordinal.{u}) : ordinal.{max u v} :=
quotient.lift_on o (λ ⟨α, r, wo⟩,
  @type _ _ (@order_embedding.is_well_order _ _ (@equiv.ulift.{u v} α ⁻¹'o r) r
    (order_iso.preimage equiv.ulift.{u v} r) wo)) $
λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨f⟩,
quot.sound ⟨(order_iso.preimage equiv.ulift r).trans $
  f.trans (order_iso.preimage equiv.ulift s).symm⟩

theorem lift_type {α} (r : α → α → Prop) [is_well_order α r] :
  ∃ wo', lift (type r) = @type _ (@equiv.ulift.{u v} α ⁻¹'o r) wo' :=
⟨_, rfl⟩

theorem lift_umax : lift.{u (max u v)} = lift.{u v} :=
funext $ λ a, induction_on a $ λ α r _,
quotient.sound ⟨(order_iso.preimage equiv.ulift r).trans (order_iso.preimage equiv.ulift r).symm⟩

theorem lift_id' (a : ordinal) : lift a = a :=
induction_on a $ λ α r _,
quotient.sound ⟨order_iso.preimage equiv.ulift r⟩

@[simp] theorem lift_id : ∀ a, lift.{u u} a = a := lift_id'.{u u}

@[simp]
theorem lift_lift (a : ordinal) : lift.{(max u v) w} (lift.{u v} a) = lift.{u (max v w)} a :=
induction_on a $ λ α r _,
quotient.sound ⟨(order_iso.preimage equiv.ulift _).trans $
  (order_iso.preimage equiv.ulift _).trans (order_iso.preimage equiv.ulift _).symm⟩

theorem lift_type_le {α : Type u} {β : Type v} {r s} [is_well_order α r] [is_well_order β s] :
  lift.{u (max v w)} (type r) ≤ lift.{v (max u w)} (type s) ↔ nonempty (r ≼i s) :=
⟨λ ⟨f⟩, ⟨(initial_seg.of_iso (order_iso.preimage equiv.ulift r).symm).trans $
    f.trans (initial_seg.of_iso (order_iso.preimage equiv.ulift s))⟩,
 λ ⟨f⟩, ⟨(initial_seg.of_iso (order_iso.preimage equiv.ulift r)).trans $
    f.trans (initial_seg.of_iso (order_iso.preimage equiv.ulift s).symm)⟩⟩

theorem lift_type_eq {α : Type u} {β : Type v} {r s} [is_well_order α r] [is_well_order β s] :
  lift.{u (max v w)} (type r) = lift.{v (max u w)} (type s) ↔ nonempty (r ≃o s) :=
quotient.eq.trans
⟨λ ⟨f⟩, ⟨(order_iso.preimage equiv.ulift r).symm.trans $
    f.trans (order_iso.preimage equiv.ulift s)⟩,
 λ ⟨f⟩, ⟨(order_iso.preimage equiv.ulift r).trans $
    f.trans (order_iso.preimage equiv.ulift s).symm⟩⟩

theorem lift_type_lt {α : Type u} {β : Type v} {r s} [is_well_order α r] [is_well_order β s] :
  lift.{u (max v w)} (type r) < lift.{v (max u w)} (type s) ↔ nonempty (r ≺i s) :=
by haveI := @order_embedding.is_well_order _ _ (@equiv.ulift.{u (max v w)} α ⁻¹'o r)
     r (order_iso.preimage equiv.ulift.{u (max v w)} r) _;
   haveI := @order_embedding.is_well_order _ _ (@equiv.ulift.{v (max u w)} β ⁻¹'o s)
     s (order_iso.preimage equiv.ulift.{v (max u w)} s) _; exact
⟨λ ⟨f⟩, ⟨(f.equiv_lt (order_iso.preimage equiv.ulift r).symm).lt_le
    (initial_seg.of_iso (order_iso.preimage equiv.ulift s))⟩,
 λ ⟨f⟩, ⟨(f.equiv_lt (order_iso.preimage equiv.ulift r)).lt_le
    (initial_seg.of_iso (order_iso.preimage equiv.ulift s).symm)⟩⟩

@[simp] theorem lift_le {a b : ordinal} : lift.{u v} a ≤ lift b ↔ a ≤ b :=
induction_on a $ λ α r _, induction_on b $ λ β s _,
by rw ← lift_umax; exactI lift_type_le

@[simp] theorem lift_inj {a b : ordinal} : lift a = lift b ↔ a = b :=
by simp only [le_antisymm_iff, lift_le]

@[simp] theorem lift_lt {a b : ordinal} : lift a < lift b ↔ a < b :=
by simp only [lt_iff_le_not_le, lift_le]

@[simp] theorem lift_zero : lift 0 = 0 :=
quotient.sound ⟨(order_iso.preimage equiv.ulift _).trans
 ⟨pempty_equiv_pempty, λ a b, iff.rfl⟩⟩

theorem zero_eq_lift_type_empty : 0 = lift.{0 u} (@type empty empty_relation _) :=
by rw [← zero_eq_type_empty, lift_zero]

@[simp] theorem lift_one : lift 1 = 1 :=
quotient.sound ⟨(order_iso.preimage equiv.ulift _).trans
 ⟨punit_equiv_punit, λ a b, iff.rfl⟩⟩

theorem one_eq_lift_type_unit : 1 = lift.{0 u} (@type unit empty_relation _) :=
by rw [← one_eq_type_unit, lift_one]

@[simp] theorem lift_add (a b) : lift (a + b) = lift a + lift b :=
quotient.induction_on₂ a b $ λ ⟨α, r, _⟩ ⟨β, s, _⟩,
quotient.sound ⟨(order_iso.preimage equiv.ulift _).trans
 (order_iso.sum_lex_congr (order_iso.preimage equiv.ulift _)
   (order_iso.preimage equiv.ulift _)).symm⟩

@[simp] theorem lift_succ (a) : lift (succ a) = succ (lift a) :=
by unfold succ; simp only [lift_add, lift_one]

@[simp] theorem lift_card (a) : (card a).lift = card (lift a) :=
induction_on a $ λ α r _, rfl

theorem lift_down' {a : cardinal.{u}} {b : ordinal.{max u v}}
  (h : card b ≤ a.lift) : ∃ a', lift a' = b :=
let ⟨c, e⟩ := cardinal.lift_down h in
quotient.induction_on c (λ α, induction_on b $ λ β s _ e', begin
  resetI,
  rw [mk_def, card_type, ← cardinal.lift_id'.{(max u v) u} (mk β),
      ← cardinal.lift_umax.{u v}, lift_mk_eq.{u (max u v) (max u v)}] at e',
  cases e' with f,
  have g := order_iso.preimage f s,
  haveI := (g : ⇑f ⁻¹'o s ≼o s).is_well_order,
  have := lift_type_eq.{u (max u v) (max u v)}.2 ⟨g⟩,
  rw [lift_id, lift_umax.{u v}] at this,
  exact ⟨_, this⟩
end) e

theorem lift_down {a : ordinal.{u}} {b : ordinal.{max u v}}
  (h : b ≤ lift a) : ∃ a', lift a' = b :=
@lift_down' (card a) _ (by rw lift_card; exact card_le_card h)

theorem le_lift_iff {a : ordinal.{u}} {b : ordinal.{max u v}} :
  b ≤ lift a ↔ ∃ a', lift a' = b ∧ a' ≤ a :=
⟨λ h, let ⟨a', e⟩ := lift_down h in ⟨a', e, lift_le.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_le.2 h⟩

theorem lt_lift_iff {a : ordinal.{u}} {b : ordinal.{max u v}} :
  b < lift a ↔ ∃ a', lift a' = b ∧ a' < a :=
⟨λ h, let ⟨a', e⟩ := lift_down (le_of_lt h) in
      ⟨a', e, lift_lt.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_lt.2 h⟩

/-- `ω` is the first infinite ordinal, defined as the order type of `ℕ`. -/
def omega : ordinal.{u} := lift $ @type ℕ (<) _

localized "notation `ω` := ordinal.omega.{0}" in ordinal

theorem card_omega : card omega = cardinal.omega := rfl

@[simp] theorem lift_omega : lift omega = omega := lift_lift _

theorem add_le_add_right {a b : ordinal} : a ≤ b → ∀ c, a + c ≤ b + c :=
induction_on a $ λ α₁ r₁ hr₁, induction_on b $ λ α₂ r₂ hr₂ ⟨⟨⟨f, fo⟩, fi⟩⟩ c,
induction_on c $ λ β s hs, (@type_le' _ _ _ _
  (@sum.lex.is_well_order _ _ _ _ hr₁ hs)
  (@sum.lex.is_well_order _ _ _ _ hr₂ hs)).2
⟨⟨embedding.sum_congr f (embedding.refl _), λ a b, begin
  split; intro H,
  { cases H; constructor; [rwa ← fo, assumption] },
  { cases a with a a; cases b with b b; cases H; constructor; [rwa fo, assumption] }
end⟩⟩

theorem le_add_left (a b : ordinal) : a ≤ b + a :=
by simpa only [zero_add] using add_le_add_right (zero_le b) a

theorem le_total (a b : ordinal) : a ≤ b ∨ b ≤ a :=
match lt_or_eq_of_le (le_add_left b a), lt_or_eq_of_le (le_add_right a b) with
| or.inr h, _ := by rw h; exact or.inl (le_add_right _ _)
| _, or.inr h := by rw h; exact or.inr (le_add_left _ _)
| or.inl h₁, or.inl h₂ := induction_on a (λ α₁ r₁ _,
  induction_on b $ λ α₂ r₂ _ ⟨f⟩ ⟨g⟩, begin
    resetI,
    rw [← typein_top f, ← typein_top g, le_iff_lt_or_eq,
        le_iff_lt_or_eq, typein_lt_typein, typein_lt_typein],
    rcases trichotomous_of (sum.lex r₁ r₂) g.top f.top with h|h|h;
    [exact or.inl (or.inl h), {left, right, rw h}, exact or.inr (or.inl h)]
  end) h₁ h₂
end

instance : decidable_linear_order ordinal :=
{ le_total     := le_total,
  decidable_le := classical.dec_rel _,
  ..ordinal.partial_order }

@[simp] lemma typein_le_typein (r : α → α → Prop) [is_well_order α r] {x x' : α} :
  typein r x ≤ typein r x' ↔ ¬r x' x :=
by rw [←not_lt, typein_lt_typein]

lemma enum_le_enum (r : α → α → Prop) [is_well_order α r] {o o' : ordinal}
  (ho : o < type r) (ho' : o' < type r) : ¬r (enum r o' ho') (enum r o ho) ↔ o ≤ o' :=
by rw [←@not_lt _ _ o' o, enum_lt ho']

theorem lt_succ {a b : ordinal} : a < succ b ↔ a ≤ b :=
by rw [← not_le, succ_le, not_lt]

theorem add_lt_add_iff_left (a) {b c : ordinal} : a + b < a + c ↔ b < c :=
by rw [← not_le, ← not_le, add_le_add_iff_left]

theorem lt_of_add_lt_add_right {a b c : ordinal} : a + b < c + b → a < c :=
lt_imp_lt_of_le_imp_le (λ h, add_le_add_right h _)

@[simp] theorem succ_lt_succ {a b : ordinal} : succ a < succ b ↔ a < b :=
by rw [lt_succ, succ_le]

@[simp] theorem succ_le_succ {a b : ordinal} : succ a ≤ succ b ↔ a ≤ b :=
le_iff_le_iff_lt_iff_lt.2 succ_lt_succ

theorem succ_inj {a b : ordinal} : succ a = succ b ↔ a = b :=
by simp only [le_antisymm_iff, succ_le_succ]

theorem add_le_add_iff_right {a b : ordinal} (n : ℕ) : a + n ≤ b + n ↔ a ≤ b :=
by induction n with n ih; [rw [nat.cast_zero, add_zero, add_zero],
  rw [← nat_cast_succ, add_succ, add_succ, succ_le_succ, ih]]

theorem add_right_cancel {a b : ordinal} (n : ℕ) : a + n = b + n ↔ a = b :=
by simp only [le_antisymm_iff, add_le_add_iff_right]

@[simp] theorem card_eq_zero {o} : card o = 0 ↔ o = 0 :=
⟨induction_on o $ λ α r _ h, begin
  refine le_antisymm (le_of_not_lt $
    λ hn, ne_zero_iff_nonempty.2 _ h) (zero_le _),
  rw [← succ_le, succ_zero] at hn, cases hn with f,
  exact ⟨f punit.star⟩
end, λ e, by simp only [e, card_zero]⟩

theorem type_ne_zero_iff_nonempty [is_well_order α r] : type r ≠ 0 ↔ nonempty α :=
(not_congr (@card_eq_zero (type r))).symm.trans ne_zero_iff_nonempty

@[simp] theorem type_eq_zero_iff_empty [is_well_order α r] : type r = 0 ↔ ¬ nonempty α :=
(not_iff_comm.1 type_ne_zero_iff_nonempty).symm

instance : nonzero ordinal.{u} :=
{ zero_ne_one := ne.symm $ type_ne_zero_iff_nonempty.2 ⟨punit.star⟩ }

theorem zero_lt_one : (0 : ordinal) < 1 :=
lt_iff_le_and_ne.2 ⟨zero_le _, zero_ne_one⟩

/-- The ordinal predecessor of `o` is `o'` if `o = succ o'`,
  and `o` otherwise. -/
def pred (o : ordinal.{u}) : ordinal.{u} :=
if h : ∃ a, o = succ a then classical.some h else o

@[simp] theorem pred_succ (o) : pred (succ o) = o :=
by have h : ∃ a, succ o = succ a := ⟨_, rfl⟩;
   simpa only [pred, dif_pos h] using (succ_inj.1 $ classical.some_spec h).symm

theorem pred_le_self (o) : pred o ≤ o :=
if h : ∃ a, o = succ a then let ⟨a, e⟩ := h in
by rw [e, pred_succ]; exact le_of_lt (lt_succ_self _)
else by rw [pred, dif_neg h]

theorem pred_eq_iff_not_succ {o} : pred o = o ↔ ¬ ∃ a, o = succ a :=
⟨λ e ⟨a, e'⟩, by rw [e', pred_succ] at e; exact ne_of_lt (lt_succ_self _) e,
 λ h, dif_neg h⟩

theorem pred_lt_iff_is_succ {o} : pred o < o ↔ ∃ a, o = succ a :=
iff.trans (by simp only [le_antisymm_iff, pred_le_self, true_and, not_le])
  (iff_not_comm.1 pred_eq_iff_not_succ).symm

theorem succ_pred_iff_is_succ {o} : succ (pred o) = o ↔ ∃ a, o = succ a :=
⟨λ e, ⟨_, e.symm⟩, λ ⟨a, e⟩, by simp only [e, pred_succ]⟩

theorem succ_lt_of_not_succ {o} (h : ¬ ∃ a, o = succ a) {b} : succ b < o ↔ b < o :=
⟨lt_trans (lt_succ_self _), λ l,
  lt_of_le_of_ne (succ_le.2 l) (λ e, h ⟨_, e.symm⟩)⟩

theorem lt_pred {a b} : a < pred b ↔ succ a < b :=
if h : ∃ a, b = succ a then let ⟨c, e⟩ := h in
by rw [e, pred_succ, succ_lt_succ]
else by simp only [pred, dif_neg h, succ_lt_of_not_succ h]

theorem pred_le {a b} : pred a ≤ b ↔ a ≤ succ b :=
le_iff_le_iff_lt_iff_lt.2 lt_pred

@[simp] theorem lift_is_succ {o} : (∃ a, lift o = succ a) ↔ (∃ a, o = succ a) :=
⟨λ ⟨a, h⟩,
  let ⟨b, e⟩ := lift_down $ show a ≤ lift o, from le_of_lt $
    h.symm ▸ lt_succ_self _ in
  ⟨b, lift_inj.1 $ by rw [h, ← e, lift_succ]⟩,
 λ ⟨a, h⟩, ⟨lift a, by simp only [h, lift_succ]⟩⟩

@[simp] theorem lift_pred (o) : lift (pred o) = pred (lift o) :=
if h : ∃ a, o = succ a then
by cases h with a e; simp only [e, pred_succ, lift_succ]
else by rw [pred_eq_iff_not_succ.2 h,
            pred_eq_iff_not_succ.2 (mt lift_is_succ.1 h)]

/-- A limit ordinal is an ordinal which is not zero and not a successor. -/
def is_limit (o : ordinal) : Prop := o ≠ 0 ∧ ∀ a < o, succ a < o

theorem not_zero_is_limit : ¬ is_limit 0
| ⟨h, _⟩ := h rfl

theorem not_succ_is_limit (o) : ¬ is_limit (succ o)
| ⟨_, h⟩ := lt_irrefl _ (h _ (lt_succ_self _))

theorem not_succ_of_is_limit {o} (h : is_limit o) : ¬ ∃ a, o = succ a
| ⟨a, e⟩ := not_succ_is_limit a (e ▸ h)

theorem succ_lt_of_is_limit {o} (h : is_limit o) {a} : succ a < o ↔ a < o :=
⟨lt_trans (lt_succ_self _), h.2 _⟩

theorem le_succ_of_is_limit {o} (h : is_limit o) {a} : o ≤ succ a ↔ o ≤ a :=
le_iff_le_iff_lt_iff_lt.2 $ succ_lt_of_is_limit h

theorem limit_le {o} (h : is_limit o) {a} : o ≤ a ↔ ∀ x < o, x ≤ a :=
⟨λ h x l, le_trans (le_of_lt l) h,
 λ H, (le_succ_of_is_limit h).1 $ le_of_not_lt $ λ hn,
  not_lt_of_le (H _ hn) (lt_succ_self _)⟩

theorem lt_limit {o} (h : is_limit o) {a} : a < o ↔ ∃ x < o, a < x :=
by simpa only [not_ball, not_le] using not_congr (@limit_le _ h a)

@[simp] theorem lift_is_limit (o) : is_limit (lift o) ↔ is_limit o :=
and_congr (not_congr $ by simpa only [lift_zero] using @lift_inj o 0)
⟨λ H a h, lift_lt.1 $ by simpa only [lift_succ] using H _ (lift_lt.2 h),
 λ H a h, let ⟨a', e⟩ := lift_down (le_of_lt h) in
   by rw [← e, ← lift_succ, lift_lt];
      rw [← e, lift_lt] at h; exact H a' h⟩

theorem is_limit.pos {o : ordinal} (h : is_limit o) : 0 < o :=
lt_of_le_of_ne (zero_le _) h.1.symm

theorem is_limit.one_lt {o : ordinal} (h : is_limit o) : 1 < o :=
by simpa only [succ_zero] using h.2 _ h.pos

theorem is_limit.nat_lt {o : ordinal} (h : is_limit o) : ∀ n : ℕ, (n : ordinal) < o
| 0     := h.pos
| (n+1) := h.2 _ (is_limit.nat_lt n)

theorem zero_or_succ_or_limit (o : ordinal) :
  o = 0 ∨ (∃ a, o = succ a) ∨ is_limit o :=
if o0 : o = 0 then or.inl o0 else
if h : ∃ a, o = succ a then or.inr (or.inl h) else
or.inr $ or.inr ⟨o0, λ a, (succ_lt_of_not_succ h).2⟩

instance : is_well_order ordinal (<) := ⟨wf⟩

@[elab_as_eliminator] def limit_rec_on {C : ordinal → Sort*}
  (o : ordinal) (H₁ : C 0) (H₂ : ∀ o, C o → C (succ o))
  (H₃ : ∀ o, is_limit o → (∀ o' < o, C o') → C o) : C o :=
wf.fix (λ o IH,
  if o0 : o = 0 then by rw o0; exact H₁ else
  if h : ∃ a, o = succ a then
    by rw ← succ_pred_iff_is_succ.2 h; exact
    H₂ _ (IH _ $ pred_lt_iff_is_succ.2 h)
  else H₃ _ ⟨o0, λ a, (succ_lt_of_not_succ h).2⟩ IH) o

@[simp] theorem limit_rec_on_zero {C} (H₁ H₂ H₃) : @limit_rec_on C 0 H₁ H₂ H₃ = H₁ :=
by rw [limit_rec_on, well_founded.fix_eq, dif_pos rfl]; refl

@[simp] theorem limit_rec_on_succ {C} (o H₁ H₂ H₃) :
  @limit_rec_on C (succ o) H₁ H₂ H₃ = H₂ o (@limit_rec_on C o H₁ H₂ H₃) :=
begin
  have h : ∃ a, succ o = succ a := ⟨_, rfl⟩,
  rw [limit_rec_on, well_founded.fix_eq,
      dif_neg (succ_ne_zero o), dif_pos h],
  generalize : limit_rec_on._proof_2 (succ o) h = h₂,
  generalize : limit_rec_on._proof_3 (succ o) h = h₃,
  revert h₂ h₃, generalize e : pred (succ o) = o', intros,
  rw pred_succ at e, subst o', refl
end

@[simp] theorem limit_rec_on_limit {C} (o H₁ H₂ H₃ h) :
  @limit_rec_on C o H₁ H₂ H₃ = H₃ o h (λ x h, @limit_rec_on C x H₁ H₂ H₃) :=
by rw [limit_rec_on, well_founded.fix_eq,
       dif_neg h.1, dif_neg (not_succ_of_is_limit h)]; refl

lemma has_succ_of_is_limit {α} {r : α → α → Prop} [wo : is_well_order α r]
  (h : (type r).is_limit) (x : α) : ∃y, r x y :=
begin
  use enum r (typein r x).succ (h.2 _ (typein_lt_type r x)),
  convert (enum_lt (typein_lt_type r x) _).mpr (lt_succ_self _), rw [enum_typein]
end

lemma type_subrel_lt (o : ordinal.{u}) :
  type (subrel (<) {o' : ordinal | o' < o}) = ordinal.lift.{u u+1} o :=
begin
  refine quotient.induction_on o _,
  rintro ⟨α, r, wo⟩, resetI, apply quotient.sound,
  constructor, symmetry, refine (order_iso.preimage equiv.ulift r).trans (typein_iso r)
end

lemma mk_initial_seg (o : ordinal.{u}) :
  #{o' : ordinal | o' < o} = cardinal.lift.{u u+1} o.card :=
by rw [lift_card, ←type_subrel_lt, card_type]

/-- A normal ordinal function is a strictly increasing function which is
  order-continuous. -/
def is_normal (f : ordinal → ordinal) : Prop :=
(∀ o, f o < f (succ o)) ∧ ∀ o, is_limit o → ∀ a, f o ≤ a ↔ ∀ b < o, f b ≤ a

theorem is_normal.limit_le {f} (H : is_normal f) : ∀ {o}, is_limit o →
  ∀ {a}, f o ≤ a ↔ ∀ b < o, f b ≤ a := H.2

theorem is_normal.limit_lt {f} (H : is_normal f) {o} (h : is_limit o) {a} :
  a < f o ↔ ∃ b < o, a < f b :=
not_iff_not.1 $ by simpa only [exists_prop, not_exists, not_and, not_lt] using H.2 _ h a

theorem is_normal.lt_iff {f} (H : is_normal f) {a b} : f a < f b ↔ a < b :=
strict_mono.lt_iff_lt $ λ a b,
limit_rec_on b (not.elim (not_lt_of_le $ zero_le _))
  (λ b IH h, (lt_or_eq_of_le (lt_succ.1 h)).elim
    (λ h, lt_trans (IH h) (H.1 _))
    (λ e, e ▸ H.1 _))
  (λ b l IH h, lt_of_lt_of_le (H.1 a)
    ((H.2 _ l _).1 (le_refl _) _ (l.2 _ h)))

theorem is_normal.le_iff {f} (H : is_normal f) {a b} : f a ≤ f b ↔ a ≤ b :=
le_iff_le_iff_lt_iff_lt.2 H.lt_iff

theorem is_normal.inj {f} (H : is_normal f) {a b} : f a = f b ↔ a = b :=
by simp only [le_antisymm_iff, H.le_iff]

theorem is_normal.le_self {f} (H : is_normal f) (a) : a ≤ f a :=
limit_rec_on a (zero_le _)
  (λ a IH, succ_le.2 $ lt_of_le_of_lt IH (H.1 _))
  (λ a l IH, (limit_le l).2 $ λ b h,
    le_trans (IH b h) $ H.le_iff.2 $ le_of_lt h)

theorem is_normal.le_set {f} (H : is_normal f) (p : ordinal → Prop)
  (p0 : ∃ x, p x) (S)
  (H₂ : ∀ o, S ≤ o ↔ ∀ a, p a → a ≤ o) {o} :
  f S ≤ o ↔ ∀ a, p a → f a ≤ o :=
⟨λ h a pa, le_trans (H.le_iff.2 ((H₂ _).1 (le_refl _) _ pa)) h,
λ h, begin
  revert H₂, apply limit_rec_on S,
  { intro H₂,
     cases p0 with x px,
     have := le_zero.1 ((H₂ _).1 (zero_le _) _ px),
     rw this at px, exact h _ px },
  { intros S _ H₂,
    rcases not_ball.1 (mt (H₂ S).2 $ not_le_of_lt $ lt_succ_self _) with ⟨a, h₁, h₂⟩,
    exact le_trans (H.le_iff.2 $ succ_le.2 $ not_le.1 h₂) (h _ h₁) },
  { intros S L _ H₂, apply (H.2 _ L _).2, intros a h',
    rcases not_ball.1 (mt (H₂ a).2 (not_le.2 h')) with ⟨b, h₁, h₂⟩,
    exact le_trans (H.le_iff.2 $ le_of_lt $ not_le.1 h₂) (h _ h₁) }
end⟩

theorem is_normal.le_set' {f} (H : is_normal f) (p : α → Prop) (g : α → ordinal)
  (p0 : ∃ x, p x) (S)
  (H₂ : ∀ o, S ≤ o ↔ ∀ a, p a → g a ≤ o) {o} :
  f S ≤ o ↔ ∀ a, p a → f (g a) ≤ o :=
(H.le_set (λ x, ∃ y, p y ∧ x = g y)
  (let ⟨x, px⟩ := p0 in ⟨_, _, px, rfl⟩) _
  (λ o, (H₂ o).trans ⟨λ H a ⟨y, h1, h2⟩, h2.symm ▸ H y h1,
    λ H a h1, H (g a) ⟨a, h1, rfl⟩⟩)).trans
⟨λ H a h, H (g a) ⟨a, h, rfl⟩, λ H a ⟨y, h1, h2⟩, h2.symm ▸ H y h1⟩

theorem is_normal.refl : is_normal id :=
⟨λ x, lt_succ_self _, λ o l a, limit_le l⟩

theorem is_normal.trans {f g} (H₁ : is_normal f) (H₂ : is_normal g) :
  is_normal (λ x, f (g x)) :=
⟨λ x, H₁.lt_iff.2 (H₂.1 _),
 λ o l a, H₁.le_set' (< o) g ⟨_, l.pos⟩ _ (λ c, H₂.2 _ l _)⟩

theorem is_normal.is_limit {f} (H : is_normal f) {o} (l : is_limit o) :
  is_limit (f o) :=
⟨ne_of_gt $ lt_of_le_of_lt (zero_le _) $ H.lt_iff.2 l.pos,
λ a h, let ⟨b, h₁, h₂⟩ := (H.limit_lt l).1 h in
  lt_of_le_of_lt (succ_le.2 h₂) (H.lt_iff.2 h₁)⟩

theorem add_le_of_limit {a b c : ordinal.{u}}
  (h : is_limit b) : a + b ≤ c ↔ ∀ b' < b, a + b' ≤ c :=
⟨λ h b' l, le_trans (add_le_add_left (le_of_lt l) _) h,
λ H, le_of_not_lt $
induction_on a (λ α r _, induction_on b $ λ β s _ h H l, begin
  resetI,
  suffices : ∀ x : β, sum.lex r s (sum.inr x) (enum _ _ l),
  { cases enum _ _ l with x x,
    { cases this (enum s 0 h.pos) },
    { exact irrefl _ (this _) } },
  intros x,
  rw [← typein_lt_typein (sum.lex r s), typein_enum],
  have := H _ (h.2 _ (typein_lt_type s x)),
  rw [add_succ, succ_le] at this,
  refine lt_of_le_of_lt (type_le'.2
    ⟨order_embedding.of_monotone (λ a, _) (λ a b, _)⟩) this,
  { rcases a with ⟨a | b, h⟩,
    { exact sum.inl a },
    { exact sum.inr ⟨b, by cases h; assumption⟩ } },
  { rcases a with ⟨a | a, h₁⟩; rcases b with ⟨b | b, h₂⟩; cases h₁; cases h₂;
      rintro ⟨⟩; constructor; assumption }
end) h H⟩

theorem add_is_normal (a : ordinal) : is_normal ((+) a) :=
⟨λ b, (add_lt_add_iff_left a).2 (lt_succ_self _),
 λ b l c, add_le_of_limit l⟩

theorem add_is_limit (a) {b} : is_limit b → is_limit (a + b) :=
(add_is_normal a).is_limit

def typein.principal_seg {α : Type u} (r : α → α → Prop) [is_well_order α r] :
  @principal_seg α ordinal.{u} r (<) :=
⟨order_embedding.of_monotone (typein r)
  (λ a b, (typein_lt_typein r).2), type r, λ b,
    ⟨λ h, ⟨enum r _ h, typein_enum r h⟩,
    λ ⟨a, e⟩, e ▸ typein_lt_type _ _⟩⟩

@[simp] theorem typein.principal_seg_coe (r : α → α → Prop) [is_well_order α r] :
  (typein.principal_seg r : α → ordinal) = typein r := rfl

/-- The minimal element of a nonempty family of ordinals -/
def min {ι} (I : nonempty ι) (f : ι → ordinal) : ordinal :=
wf.min (set.range f) (let ⟨i⟩ := I in ⟨_, set.mem_range_self i⟩)

theorem min_eq {ι} (I) (f : ι → ordinal) : ∃ i, min I f = f i :=
let ⟨i, e⟩ := wf.min_mem (set.range f) _ in ⟨i, e.symm⟩

theorem min_le {ι I} (f : ι → ordinal) (i) : min I f ≤ f i :=
le_of_not_gt $ wf.not_lt_min (set.range f) _ (set.mem_range_self i)

theorem le_min {ι I} {f : ι → ordinal} {a} : a ≤ min I f ↔ ∀ i, a ≤ f i :=
⟨λ h i, le_trans h (min_le _ _),
 λ h, let ⟨i, e⟩ := min_eq I f in e.symm ▸ h i⟩

/-- The minimal element of a nonempty set of ordinals -/
def omin (S : set ordinal.{u}) (H : ∃ x, x ∈ S) : ordinal.{u} :=
@min.{(u+2) u} S (let ⟨x, px⟩ := H in ⟨⟨x, px⟩⟩) subtype.val

theorem omin_mem (S H) : omin S H ∈ S :=
let ⟨⟨i, h⟩, e⟩ := @min_eq S _ _ in
(show omin S H = i, from e).symm ▸ h

theorem le_omin {S H a} : a ≤ omin S H ↔ ∀ i ∈ S, a ≤ i :=
le_min.trans set_coe.forall

theorem omin_le {S H i} (h : i ∈ S) : omin S H ≤ i :=
le_omin.1 (le_refl _) _ h

@[simp] theorem lift_min {ι} (I) (f : ι → ordinal) : lift (min I f) = min I (lift ∘ f) :=
le_antisymm (le_min.2 $ λ a, lift_le.2 $ min_le _ a) $
let ⟨i, e⟩ := min_eq I (lift ∘ f) in
by rw e; exact lift_le.2 (le_min.2 $ λ j, lift_le.1 $
by have := min_le (lift ∘ f) j; rwa e at this)

def lift.initial_seg : @initial_seg ordinal.{u} ordinal.{max u v} (<) (<) :=
⟨⟨⟨lift.{u v}, λ a b, lift_inj.1⟩, λ a b, lift_lt.symm⟩,
  λ a b h, lift_down (le_of_lt h)⟩

@[simp] theorem lift.initial_seg_coe : (lift.initial_seg : ordinal → ordinal) = lift := rfl

/-- `univ.{u v}` is the order type of the ordinals of `Type u` as a member
  of `ordinal.{v}` (when `u < v`). It is an inaccessible cardinal. -/
def univ := lift.{(u+1) v} (@type ordinal.{u} (<) _)

theorem univ_id : univ.{u (u+1)} = @type ordinal.{u} (<) _ := lift_id _

@[simp] theorem lift_univ : lift.{_ w} univ.{u v} = univ.{u (max v w)} := lift_lift _

theorem univ_umax : univ.{u (max (u+1) v)} = univ.{u v} := congr_fun lift_umax _

def lift.principal_seg : @principal_seg ordinal.{u} ordinal.{max (u+1) v} (<) (<) :=
⟨↑lift.initial_seg.{u (max (u+1) v)}, univ.{u v}, begin
  refine λ b, induction_on b _, introsI β s _,
  rw [univ, ← lift_umax], split; intro h,
  { rw ← lift_id (type s) at h ⊢,
    cases lift_type_lt.1 h with f, cases f with f a hf,
    existsi a, revert hf,
    apply induction_on a, introsI α r _ hf,
    refine lift_type_eq.{u (max (u+1) v) (max (u+1) v)}.2
      ⟨(order_iso.of_surjective (order_embedding.of_monotone _ _) _).symm⟩,
    { exact λ b, enum r (f b) ((hf _).2 ⟨_, rfl⟩) },
    { refine λ a b h, (typein_lt_typein r).1 _,
      rw [typein_enum, typein_enum],
      exact f.ord.1 h },
    { intro a', cases (hf _).1 (typein_lt_type _ a') with b e,
      existsi b, simp, simp [e] } },
  { cases h with a e, rw [← e],
    apply induction_on a, introsI α r _,
    exact lift_type_lt.{u (u+1) (max (u+1) v)}.2
      ⟨typein.principal_seg r⟩ }
end⟩

@[simp] theorem lift.principal_seg_coe :
  (lift.principal_seg.{u v} : ordinal → ordinal) = lift.{u (max (u+1) v)} := rfl

@[simp] theorem lift.principal_seg_top : lift.principal_seg.top = univ := rfl

theorem lift.principal_seg_top' :
  lift.principal_seg.{u (u+1)}.top = @type ordinal.{u} (<) _ :=
by simp only [lift.principal_seg_top, univ_id]

/-- `a - b` is the unique ordinal satisfying
  `b + (a - b) = a` when `b ≤ a`. -/
def sub (a b : ordinal.{u}) : ordinal.{u} :=
omin {o | a ≤ b+o} ⟨a, le_add_left _ _⟩

instance : has_sub ordinal := ⟨sub⟩

theorem le_add_sub (a b : ordinal) : a ≤ b + (a - b) :=
omin_mem {o | a ≤ b+o} _

theorem sub_le {a b c : ordinal} : a - b ≤ c ↔ a ≤ b + c :=
⟨λ h, le_trans (le_add_sub a b) (add_le_add_left h _),
 λ h, omin_le h⟩

theorem lt_sub {a b c : ordinal} : a < b - c ↔ c + a < b :=
lt_iff_lt_of_le_iff_le sub_le

theorem add_sub_cancel (a b : ordinal) : a + b - a = b :=
le_antisymm (sub_le.2 $ le_refl _)
  ((add_le_add_iff_left a).1 $ le_add_sub _ _)

theorem sub_eq_of_add_eq {a b c : ordinal} (h : a + b = c) : c - a = b :=
h ▸ add_sub_cancel _ _

theorem sub_le_self (a b : ordinal) : a - b ≤ a :=
sub_le.2 $ le_add_left _ _

theorem add_sub_cancel_of_le {a b : ordinal} (h : b ≤ a) : b + (a - b) = a :=
le_antisymm begin
  rcases zero_or_succ_or_limit (a-b) with e|⟨c,e⟩|l,
  { simp only [e, add_zero, h] },
  { rw [e, add_succ, succ_le, ← lt_sub, e], apply lt_succ_self },
  { exact (add_le_of_limit l).2 (λ c l, le_of_lt (lt_sub.1 l)) }
end (le_add_sub _ _)

@[simp] theorem sub_zero (a : ordinal) : a - 0 = a :=
by simpa only [zero_add] using add_sub_cancel 0 a

@[simp] theorem zero_sub (a : ordinal) : 0 - a = 0 :=
by rw ← le_zero; apply sub_le_self

@[simp] theorem sub_self (a : ordinal) : a - a = 0 :=
by simpa only [add_zero] using add_sub_cancel a 0

theorem sub_eq_zero_iff_le {a b : ordinal} : a - b = 0 ↔ a ≤ b :=
⟨λ h, by simpa only [h, add_zero] using le_add_sub a b,
 λ h, by rwa [← le_zero, sub_le, add_zero]⟩

theorem sub_sub (a b c : ordinal) : a - b - c = a - (b + c) :=
eq_of_forall_ge_iff $ λ d, by rw [sub_le, sub_le, sub_le, add_assoc]

theorem add_sub_add_cancel (a b c : ordinal) : a + b - (a + c) = b - c :=
by rw [← sub_sub, add_sub_cancel]

theorem sub_is_limit {a b} (l : is_limit a) (h : b < a) : is_limit (a - b) :=
⟨ne_of_gt $ lt_sub.2 $ by rwa add_zero,
 λ c h, by rw [lt_sub, add_succ]; exact l.2 _ (lt_sub.1 h)⟩

@[simp] theorem one_add_omega : 1 + omega.{u} = omega :=
begin
  refine le_antisymm _ (le_add_left _ _),
  rw [omega, one_eq_lift_type_unit, ← lift_add, lift_le, type_add],
  have : is_well_order unit empty_relation := by apply_instance,
  refine ⟨order_embedding.collapse (order_embedding.of_monotone _ _)⟩,
  { apply sum.rec, exact λ _, 0, exact nat.succ },
  { intros a b, cases a; cases b; intro H; cases H with _ _ H _ _ H;
    [cases H, exact nat.succ_pos _, exact nat.succ_lt_succ H] }
end

@[simp, priority 990]
theorem one_add_of_omega_le {o} (h : omega ≤ o) : 1 + o = o :=
by rw [← add_sub_cancel_of_le h, ← add_assoc, one_add_omega]

instance : monoid ordinal.{u} :=
{ mul := λ a b, quotient.lift_on₂ a b
      (λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, ⟦⟨β × α, prod.lex s r, by exactI prod.lex.is_well_order⟩⟧
        : Well_order → Well_order → ordinal) $
    λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
    quot.sound ⟨order_iso.prod_lex_congr g f⟩,
  one := 1,
  mul_assoc := λ a b c, quotient.induction_on₃ a b c $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩,
    eq.symm $ quotient.sound ⟨⟨prod_assoc _ _ _, λ a b, begin
      rcases a with ⟨⟨a₁, a₂⟩, a₃⟩,
      rcases b with ⟨⟨b₁, b₂⟩, b₃⟩,
      simp [prod.lex_def, and_or_distrib_left, or_assoc, and_assoc]
    end⟩⟩,
  mul_one := λ a, induction_on a $ λ α r _, quotient.sound
    ⟨⟨punit_prod _, λ a b, by rcases a with ⟨⟨⟨⟩⟩, a⟩; rcases b with ⟨⟨⟨⟩⟩, b⟩;
    simp only [prod.lex_def, empty_relation, false_or];
    simp only [eq_self_iff_true, true_and]; refl⟩⟩,
  one_mul := λ a, induction_on a $ λ α r _, quotient.sound
    ⟨⟨prod_punit _, λ a b, by rcases a with ⟨a, ⟨⟨⟩⟩⟩; rcases b with ⟨b, ⟨⟨⟩⟩⟩;
    simp only [prod.lex_def, empty_relation, and_false, or_false]; refl⟩⟩ }

@[simp] theorem type_mul {α β : Type u} (r : α → α → Prop) (s : β → β → Prop)
  [is_well_order α r] [is_well_order β s] : type r * type s = type (prod.lex s r) := rfl

@[simp] theorem lift_mul (a b) : lift (a * b) = lift a * lift b :=
quotient.induction_on₂ a b $ λ ⟨α, r, _⟩ ⟨β, s, _⟩,
quotient.sound ⟨(order_iso.preimage equiv.ulift _).trans
 (order_iso.prod_lex_congr (order_iso.preimage equiv.ulift _)
   (order_iso.preimage equiv.ulift _)).symm⟩

@[simp] theorem card_mul (a b) : card (a * b) = card a * card b :=
quotient.induction_on₂ a b $ λ ⟨α, r, _⟩ ⟨β, s, _⟩,
mul_comm (mk β) (mk α)

@[simp] theorem mul_zero (a : ordinal) : a * 0 = 0 :=
induction_on a $ λ α _ _, by exactI
type_eq_zero_iff_empty.2 (λ ⟨⟨e, _⟩⟩, e.elim)

@[simp] theorem zero_mul (a : ordinal) : 0 * a = 0 :=
induction_on a $ λ α _ _, by exactI
type_eq_zero_iff_empty.2 (λ ⟨⟨_, e⟩⟩, e.elim)

theorem mul_add (a b c : ordinal) : a * (b + c) = a * b + a * c :=
quotient.induction_on₃ a b c $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩,
quotient.sound ⟨⟨sum_prod_distrib _ _ _, begin
  rintro ⟨a₁|a₁, a₂⟩ ⟨b₁|b₁, b₂⟩; simp only [prod.lex_def,
    sum.lex_inl_inl, sum.lex.sep, sum.lex_inr_inl, sum.lex_inr_inr,
    sum_prod_distrib_apply_left, sum_prod_distrib_apply_right];
  simp only [sum.inl.inj_iff, true_or, false_and, false_or]
end⟩⟩

@[simp] theorem mul_add_one (a b : ordinal) : a * (b + 1) = a * b + a :=
by simp only [mul_add, mul_one]

@[simp] theorem mul_succ (a b : ordinal) : a * succ b = a * b + a := mul_add_one _ _

theorem mul_le_mul_left {a b} (c : ordinal) : a ≤ b → c * a ≤ c * b :=
quotient.induction_on₃ a b c $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩, begin
  resetI,
  refine type_le'.2 ⟨order_embedding.of_monotone
    (λ a, (f a.1, a.2))
    (λ a b h, _)⟩, clear_,
  cases h with a₁ b₁ a₂ b₂ h' a b₁ b₂ h',
  { exact prod.lex.left _ _ (f.to_order_embedding.ord.1 h') },
  { exact prod.lex.right _ h' }
end

theorem mul_le_mul_right {a b} (c : ordinal) : a ≤ b → a * c ≤ b * c :=
quotient.induction_on₃ a b c $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩, begin
  resetI,
  refine type_le'.2 ⟨order_embedding.of_monotone
    (λ a, (a.1, f a.2))
    (λ a b h, _)⟩,
  cases h with a₁ b₁ a₂ b₂ h' a b₁ b₂ h',
  { exact prod.lex.left _ _ h' },
  { exact prod.lex.right _ (f.to_order_embedding.ord.1 h') }
end

theorem mul_le_mul {a b c d : ordinal} (h₁ : a ≤ c) (h₂ : b ≤ d) : a * b ≤ c * d :=
le_trans (mul_le_mul_left _ h₂) (mul_le_mul_right _ h₁)

private lemma mul_le_of_limit_aux {α β r s} [is_well_order α r] [is_well_order β s]
  {c} (h : is_limit (type s)) (H : ∀ b' < type s, type r * b' ≤ c)
  (l : c < type r * type s) : false :=
begin
  suffices : ∀ a b, prod.lex s r (b, a) (enum _ _ l),
  { cases enum _ _ l with b a, exact irrefl _ (this _ _) },
  intros a b,
  rw [← typein_lt_typein (prod.lex s r), typein_enum],
  have := H _ (h.2 _ (typein_lt_type s b)),
  rw [mul_succ] at this,
  have := lt_of_lt_of_le ((add_lt_add_iff_left _).2
    (typein_lt_type _ a)) this,
  refine lt_of_le_of_lt _ this,
  refine (type_le'.2 _),
  constructor,
  refine order_embedding.of_monotone (λ a, _) (λ a b, _),
  { rcases a with ⟨⟨b', a'⟩, h⟩,
    by_cases e : b = b',
    { refine sum.inr ⟨a', _⟩,
      subst e, cases h with _ _ _ _ h _ _ _ h,
      { exact (irrefl _ h).elim },
      { exact h } },
    { refine sum.inl (⟨b', _⟩, a'),
      cases h with _ _ _ _ h _ _ _ h,
      { exact h }, { exact (e rfl).elim } } },
  { rcases a with ⟨⟨b₁, a₁⟩, h₁⟩,
    rcases b with ⟨⟨b₂, a₂⟩, h₂⟩,
    intro h, by_cases e₁ : b = b₁; by_cases e₂ : b = b₂,
    { substs b₁ b₂,
      simpa only [subrel_val, prod.lex_def, @irrefl _ s _ b, true_and, false_or, eq_self_iff_true,
        dif_pos, sum.lex_inr_inr] using h },
    { subst b₁,
      simp only [subrel_val, prod.lex_def, e₂, prod.lex_def, dif_pos, subrel_val, eq_self_iff_true,
        or_false, dif_neg, not_false_iff, sum.lex_inr_inl, false_and] at h ⊢,
      cases h₂; [exact asymm h h₂_h, exact e₂ rfl] },
    { simp only [e₂, dif_pos, eq_self_iff_true, dif_neg e₁, not_false_iff, sum.lex.sep] },
    { simpa only [dif_neg e₁, dif_neg e₂, prod.lex_def, subrel_val, subtype.mk_eq_mk,
        sum.lex_inl_inl] using h } }
end

theorem mul_le_of_limit {a b c : ordinal.{u}}
  (h : is_limit b) : a * b ≤ c ↔ ∀ b' < b, a * b' ≤ c :=
⟨λ h b' l, le_trans (mul_le_mul_left _ (le_of_lt l)) h,
λ H, le_of_not_lt $ induction_on a (λ α r _, induction_on b $ λ β s _,
  by exactI mul_le_of_limit_aux) h H⟩

theorem mul_is_normal {a : ordinal} (h : 0 < a) : is_normal ((*) a) :=
⟨λ b, by rw mul_succ; simpa only [add_zero] using (add_lt_add_iff_left (a*b)).2 h,
 λ b l c, mul_le_of_limit l⟩

theorem lt_mul_of_limit {a b c : ordinal.{u}}
  (h : is_limit c) : a < b * c ↔ ∃ c' < c, a < b * c' :=
by simpa only [not_ball, not_le] using not_congr (@mul_le_of_limit b c a h)

theorem mul_lt_mul_iff_left {a b c : ordinal} (a0 : 0 < a) : a * b < a * c ↔ b < c :=
(mul_is_normal a0).lt_iff

theorem mul_le_mul_iff_left {a b c : ordinal} (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
(mul_is_normal a0).le_iff

theorem mul_lt_mul_of_pos_left {a b c : ordinal}
  (h : a < b) (c0 : 0 < c) : c * a < c * b :=
(mul_lt_mul_iff_left c0).2 h

theorem mul_pos {a b : ordinal} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a * b :=
by simpa only [mul_zero] using mul_lt_mul_of_pos_left h₂ h₁

theorem mul_ne_zero {a b : ordinal} : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
by simpa only [pos_iff_ne_zero] using mul_pos

theorem le_of_mul_le_mul_left {a b c : ordinal}
  (h : c * a ≤ c * b) (h0 : 0 < c) : a ≤ b :=
le_imp_le_of_lt_imp_lt (λ h', mul_lt_mul_of_pos_left h' h0) h

theorem mul_right_inj {a b c : ordinal} (a0 : 0 < a) : a * b = a * c ↔ b = c :=
(mul_is_normal a0).inj

theorem mul_is_limit {a b : ordinal}
  (a0 : 0 < a) : is_limit b → is_limit (a * b) :=
(mul_is_normal a0).is_limit

theorem mul_is_limit_left {a b : ordinal}
  (l : is_limit a) (b0 : 0 < b) : is_limit (a * b) :=
begin
  rcases zero_or_succ_or_limit b with rfl|⟨b,rfl⟩|lb,
  { exact (lt_irrefl _).elim b0 },
  { rw mul_succ, exact add_is_limit _ l },
  { exact mul_is_limit l.pos lb }
end

protected lemma div_aux (a b : ordinal.{u}) (h : b ≠ 0) : set.nonempty {o | a < b * succ o} :=
⟨a, succ_le.1 $
  by simpa only [succ_zero, one_mul]
    using mul_le_mul_right (succ a) (succ_le.2 (pos_iff_ne_zero.2 h))⟩

/-- `a / b` is the unique ordinal `o` satisfying
  `a = b * o + o'` with `o' < b`. -/
protected def div (a b : ordinal.{u}) : ordinal.{u} :=
if h : b = 0 then 0 else omin {o | a < b * succ o} (ordinal.div_aux a b h)

instance : has_div ordinal := ⟨ordinal.div⟩

@[simp] theorem div_zero (a : ordinal) : a / 0 = 0 := dif_pos rfl

lemma div_def (a) {b : ordinal} (h : b ≠ 0) :
  a / b = omin {o | a < b * succ o} (ordinal.div_aux a b h) := dif_neg h

theorem lt_mul_succ_div (a) {b : ordinal} (h : b ≠ 0) : a < b * succ (a / b) :=
by rw div_def a h; exact omin_mem {o | a < b * succ o} _

theorem lt_mul_div_add (a) {b : ordinal} (h : b ≠ 0) : a < b * (a / b) + b :=
by simpa only [mul_succ] using lt_mul_succ_div a h

theorem div_le {a b c : ordinal} (b0 : b ≠ 0) : a / b ≤ c ↔ a < b * succ c :=
⟨λ h, lt_of_lt_of_le (lt_mul_succ_div a b0) (mul_le_mul_left _ $ succ_le_succ.2 h),
 λ h, by rw div_def a b0; exact omin_le h⟩

theorem lt_div {a b c : ordinal} (c0 : c ≠ 0) : a < b / c ↔ c * succ a ≤ b :=
by rw [← not_le, div_le c0, not_lt]

theorem le_div {a b c : ordinal} (c0 : c ≠ 0) :
  a ≤ b / c ↔ c * a ≤ b :=
begin
  apply limit_rec_on a,
  { simp only [mul_zero, zero_le] },
  { intros, rw [succ_le, lt_div c0] },
  { simp only [mul_le_of_limit, limit_le, iff_self, forall_true_iff] {contextual := tt} }
end

theorem div_lt {a b c : ordinal} (b0 : b ≠ 0) :
  a / b < c ↔ a < b * c :=
lt_iff_lt_of_le_iff_le $ le_div b0

theorem div_le_of_le_mul {a b c : ordinal} (h : a ≤ b * c) : a / b ≤ c :=
if b0 : b = 0 then by simp only [b0, div_zero, zero_le] else
(div_le b0).2 $ lt_of_le_of_lt h $
mul_lt_mul_of_pos_left (lt_succ_self _) (pos_iff_ne_zero.2 b0)

theorem mul_lt_of_lt_div {a b c : ordinal} : a < b / c → c * a < b :=
lt_imp_lt_of_le_imp_le div_le_of_le_mul

@[simp] theorem zero_div (a : ordinal) : 0 / a = 0 :=
le_zero.1 $ div_le_of_le_mul $ zero_le _

theorem mul_div_le (a b : ordinal) : b * (a / b) ≤ a :=
if b0 : b = 0 then by simp only [b0, zero_mul, zero_le] else (le_div b0).1 (le_refl _)

theorem mul_add_div (a) {b : ordinal} (b0 : b ≠ 0) (c) : (b * a + c) / b = a + c / b :=
begin
  apply le_antisymm,
  { apply (div_le b0).2,
    rw [mul_succ, mul_add, add_assoc, add_lt_add_iff_left],
    apply lt_mul_div_add _ b0 },
  { rw [le_div b0, mul_add, add_le_add_iff_left],
    apply mul_div_le }
end

theorem div_eq_zero_of_lt {a b : ordinal} (h : a < b) : a / b = 0 :=
by rw [← le_zero, div_le $ pos_iff_ne_zero.1 $ lt_of_le_of_lt (zero_le _) h];
   simpa only [succ_zero, mul_one] using h

@[simp] theorem mul_div_cancel (a) {b : ordinal} (b0 : b ≠ 0) : b * a / b = a :=
by simpa only [add_zero, zero_div] using mul_add_div a b0 0

@[simp] theorem div_one (a : ordinal) : a / 1 = a :=
by simpa only [one_mul] using mul_div_cancel a one_ne_zero

@[simp] theorem div_self {a : ordinal} (h : a ≠ 0) : a / a = 1 :=
by simpa only [mul_one] using mul_div_cancel 1 h

theorem mul_sub (a b c : ordinal) : a * (b - c) = a * b - a * c :=
if a0 : a = 0 then by simp only [a0, zero_mul, sub_self] else
eq_of_forall_ge_iff $ λ d,
by rw [sub_le, ← le_div a0, sub_le, ← le_div a0, mul_add_div _ a0]

theorem is_limit_add_iff {a b} : is_limit (a + b) ↔ is_limit b ∨ (b = 0 ∧ is_limit a) :=
begin
  split; intro h,
  { by_cases h' : b = 0,
    { rw [h', add_zero] at h, right, exact ⟨h', h⟩ },
      left, rw [←add_sub_cancel a b], apply sub_is_limit h,
      suffices : a + 0 < a + b, simpa only [add_zero],
      rwa [add_lt_add_iff_left, pos_iff_ne_zero] },
  rcases h with h|⟨rfl, h⟩, exact add_is_limit a h, simpa only [add_zero]
end

/-- Divisibility is defined by right multiplication:
  `a ∣ b` if there exists `c` such that `b = a * c`. -/
instance : has_dvd ordinal := ⟨λ a b, ∃ c, b = a * c⟩

theorem dvd_def {a b : ordinal} : a ∣ b ↔ ∃ c, b = a * c := iff.rfl

theorem dvd_mul (a b : ordinal) : a ∣ a * b := ⟨_, rfl⟩

theorem dvd_trans : ∀ {a b c : ordinal}, a ∣ b → b ∣ c → a ∣ c
| a _ _ ⟨b, rfl⟩ ⟨c, rfl⟩ := ⟨b * c, mul_assoc _ _ _⟩

theorem dvd_mul_of_dvd {a b : ordinal} (c) (h : a ∣ b) : a ∣ b * c :=
dvd_trans h (dvd_mul _ _)

theorem dvd_add_iff : ∀ {a b c : ordinal}, a ∣ b → (a ∣ b + c ↔ a ∣ c)
| a _ c ⟨b, rfl⟩ :=
 ⟨λ ⟨d, e⟩, ⟨d - b, by rw [mul_sub, ← e, add_sub_cancel]⟩,
  λ ⟨d, e⟩, by rw [e, ← mul_add]; apply dvd_mul⟩

theorem dvd_add {a b c : ordinal} (h₁ : a ∣ b) : a ∣ c → a ∣ b + c :=
(dvd_add_iff h₁).2

theorem dvd_zero (a : ordinal) : a ∣ 0 := ⟨_, (mul_zero _).symm⟩

theorem zero_dvd {a : ordinal} : 0 ∣ a ↔ a = 0 :=
⟨λ ⟨h, e⟩, by simp only [e, zero_mul], λ e, e.symm ▸ dvd_zero _⟩

theorem one_dvd (a : ordinal) : 1 ∣ a := ⟨a, (one_mul _).symm⟩

theorem div_mul_cancel : ∀ {a b : ordinal}, a ≠ 0 → a ∣ b → a * (b / a) = b
| a _ a0 ⟨b, rfl⟩ := by rw [mul_div_cancel _ a0]

theorem le_of_dvd : ∀ {a b : ordinal}, b ≠ 0 → a ∣ b → a ≤ b
| a _ b0 ⟨b, rfl⟩ := by simpa only [mul_one] using mul_le_mul_left a
  (one_le_iff_ne_zero.2 (λ h : b = 0, by simpa only [h, mul_zero] using b0))

theorem dvd_antisymm {a b : ordinal} (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b :=
if a0 : a = 0 then by subst a; exact (zero_dvd.1 h₁).symm else
if b0 : b = 0 then by subst b; exact zero_dvd.1 h₂ else
le_antisymm (le_of_dvd b0 h₁) (le_of_dvd a0 h₂)

/-- `a % b` is the unique ordinal `o'` satisfying
  `a = b * o + o'` with `o' < b`. -/
instance : has_mod ordinal := ⟨λ a b, a - b * (a / b)⟩

theorem mod_def (a b : ordinal) : a % b = a - b * (a / b) := rfl

@[simp] theorem mod_zero (a : ordinal) : a % 0 = a :=
by simp only [mod_def, div_zero, zero_mul, sub_zero]

theorem mod_eq_of_lt {a b : ordinal} (h : a < b) : a % b = a :=
by simp only [mod_def, div_eq_zero_of_lt h, mul_zero, sub_zero]

@[simp] theorem zero_mod (b : ordinal) : 0 % b = 0 :=
by simp only [mod_def, zero_div, mul_zero, sub_self]

theorem div_add_mod (a b : ordinal) : b * (a / b) + a % b = a :=
add_sub_cancel_of_le $ mul_div_le _ _

theorem mod_lt (a) {b : ordinal} (h : b ≠ 0) : a % b < b :=
(add_lt_add_iff_left (b * (a / b))).1 $
by rw div_add_mod; exact lt_mul_div_add a h

@[simp] theorem mod_self (a : ordinal) : a % a = 0 :=
if a0 : a = 0 then by simp only [a0, zero_mod] else
by simp only [mod_def, div_self a0, mul_one, sub_self]

@[simp] theorem mod_one (a : ordinal) : a % 1 = 0 :=
by simp only [mod_def, div_one, one_mul, sub_self]

end ordinal

namespace cardinal
open ordinal

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. -/
def ord (c : cardinal) : ordinal :=
begin
  let ι := λ α, {r // is_well_order α r},
  have : Π α, ι α := λ α, ⟨well_ordering_rel, by apply_instance⟩,
  let F := λ α, ordinal.min ⟨this _⟩ (λ i:ι α, ⟦⟨α, i.1, i.2⟩⟧),
  refine quot.lift_on c F _,
  suffices : ∀ {α β}, α ≈ β → F α ≤ F β,
  from λ α β h, le_antisymm (this h) (this (setoid.symm h)),
  intros α β h, cases h with f, refine ordinal.le_min.2 (λ i, _),
  haveI := @order_embedding.is_well_order _ _
    (f ⁻¹'o i.1) _ ↑(order_iso.preimage f i.1) i.2,
  rw ← show type (f ⁻¹'o i.1) = ⟦⟨β, i.1, i.2⟩⟧, from
    quot.sound ⟨order_iso.preimage f i.1⟩,
  exact ordinal.min_le (λ i:ι α, ⟦⟨α, i.1, i.2⟩⟧) ⟨_, _⟩
end

@[nolint def_lemma doc_blame] -- TODO: This should be a theorem but Lean fails to synthesize the placeholder
def ord_eq_min (α : Type u) : ord (mk α) =
  @ordinal.min _ _ (λ i:{r // is_well_order α r}, ⟦⟨α, i.1, i.2⟩⟧) := rfl

theorem ord_eq (α) : ∃ (r : α → α → Prop) [wo : is_well_order α r],
  ord (mk α) = @type α r wo :=
let ⟨⟨r, wo⟩, h⟩ := @ordinal.min_eq {r // is_well_order α r}
  ⟨⟨well_ordering_rel, by apply_instance⟩⟩
  (λ i:{r // is_well_order α r}, ⟦⟨α, i.1, i.2⟩⟧) in
⟨r, wo, h⟩

theorem ord_le_type (r : α → α → Prop) [is_well_order α r] : ord (mk α) ≤ ordinal.type r :=
@ordinal.min_le {r // is_well_order α r}
  ⟨⟨well_ordering_rel, by apply_instance⟩⟩
  (λ i:{r // is_well_order α r}, ⟦⟨α, i.1, i.2⟩⟧) ⟨r, _⟩

theorem ord_le {c o} : ord c ≤ o ↔ c ≤ o.card :=
quotient.induction_on c $ λ α, induction_on o $ λ β s _,
let ⟨r, _, e⟩ := ord_eq α in begin
  resetI, simp only [mk_def, card_type], split; intro h,
  { rw e at h, exact let ⟨f⟩ := h in ⟨f.to_embedding⟩ },
  { cases h with f,
    have g := order_embedding.preimage f s,
    haveI := order_embedding.is_well_order g,
    exact le_trans (ord_le_type _) (type_le'.2 ⟨g⟩) }
end

theorem lt_ord {c o} : o < ord c ↔ o.card < c :=
by rw [← not_le, ← not_le, ord_le]

@[simp] theorem card_ord (c) : (ord c).card = c :=
quotient.induction_on c $ λ α,
let ⟨r, _, e⟩ := ord_eq α in by simp only [mk_def, e, card_type]

theorem ord_card_le (o : ordinal) : o.card.ord ≤ o :=
ord_le.2 (le_refl _)

lemma lt_ord_succ_card (o : ordinal) : o < o.card.succ.ord :=
by { rw [lt_ord], apply cardinal.lt_succ_self }

@[simp] theorem ord_le_ord {c₁ c₂} : ord c₁ ≤ ord c₂ ↔ c₁ ≤ c₂ :=
by simp only [ord_le, card_ord]

@[simp] theorem ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂ :=
by simp only [lt_ord, card_ord]

@[simp] theorem ord_zero : ord 0 = 0 :=
le_antisymm (ord_le.2 $ zero_le _) (ordinal.zero_le _)

@[simp] theorem ord_nat (n : ℕ) : ord n = n :=
le_antisymm (ord_le.2 $ by simp only [card_nat]) $ begin
  induction n with n IH,
  { apply ordinal.zero_le },
  { exact (@ordinal.succ_le n _).2 (lt_of_le_of_lt IH $
    ord_lt_ord.2 $ nat_cast_lt.2 (nat.lt_succ_self n)) }
end

@[simp] theorem lift_ord (c) : (ord c).lift = ord (lift c) :=
eq_of_forall_ge_iff $ λ o, le_iff_le_iff_lt_iff_lt.2 $ begin
  split; intro h,
  { rcases ordinal.lt_lift_iff.1 h with ⟨a, e, h⟩,
    rwa [← e, lt_ord, ← lift_card, lift_lt, ← lt_ord] },
  { rw lt_ord at h,
    rcases lift_down' (le_of_lt h) with ⟨o, rfl⟩,
    rw [← lift_card, lift_lt] at h,
    rwa [ordinal.lift_lt, lt_ord] }
end

lemma mk_ord_out (c : cardinal) : mk c.ord.out.α = c :=
by rw [←card_type c.ord.out.r, type_out, card_ord]

lemma card_typein_lt (r : α → α → Prop) [is_well_order α r] (x : α)
  (h : ord (mk α) = type r) : card (typein r x) < mk α :=
by { rw [←ord_lt_ord, h], refine lt_of_le_of_lt (ord_card_le _) (typein_lt_type r x) }

lemma card_typein_out_lt (c : cardinal) (x : c.ord.out.α) : card (typein c.ord.out.r x) < c :=
by { convert card_typein_lt c.ord.out.r x _, rw [mk_ord_out], rw [type_out, mk_ord_out] }

lemma ord_injective : injective ord :=
by { intros c c' h, rw [←card_ord c, ←card_ord c', h] }

def ord.order_embedding : @order_embedding cardinal ordinal (<) (<) :=
order_embedding.of_monotone cardinal.ord $ λ a b, cardinal.ord_lt_ord.2

@[simp] theorem ord.order_embedding_coe :
  (ord.order_embedding : cardinal → ordinal) = ord := rfl

/-- The cardinal `univ` is the cardinality of ordinal `univ`, or
  equivalently the cardinal of `ordinal.{u}`, or `cardinal.{u}`,
  as an element of `cardinal.{v}` (when `u < v`). -/
def univ := lift.{(u+1) v} (mk ordinal)

theorem univ_id : univ.{u (u+1)} = mk ordinal := lift_id _

@[simp] theorem lift_univ : lift.{_ w} univ.{u v} = univ.{u (max v w)} := lift_lift _

theorem univ_umax : univ.{u (max (u+1) v)} = univ.{u v} := congr_fun lift_umax _

theorem lift_lt_univ (c : cardinal) : lift.{u (u+1)} c < univ.{u (u+1)} :=
by simpa only [lift.principal_seg_coe, lift_ord, lift_succ, ord_le, succ_le] using le_of_lt
  (lift.principal_seg.{u (u+1)}.lt_top (succ c).ord)

theorem lift_lt_univ' (c : cardinal) : lift.{u (max (u+1) v)} c < univ.{u v} :=
by simpa only [lift_lift, lift_univ, univ_umax] using
  lift_lt.{_ (max (u+1) v)}.2 (lift_lt_univ c)

@[simp] theorem ord_univ : ord univ.{u v} = ordinal.univ.{u v} :=
le_antisymm (ord_card_le _) $ le_of_forall_lt $ λ o h,
lt_ord.2 begin
  rcases lift.principal_seg.{u v}.down'.1
    (by simpa only [lift.principal_seg_coe] using h) with ⟨o', rfl⟩,
  simp only [lift.principal_seg_coe], rw [← lift_card],
  apply lift_lt_univ'
end

theorem lt_univ {c} : c < univ.{u (u+1)} ↔ ∃ c', c = lift.{u (u+1)} c' :=
⟨λ h, begin
  have := ord_lt_ord.2 h,
  rw ord_univ at this,
  cases lift.principal_seg.{u (u+1)}.down'.1
    (by simpa only [lift.principal_seg_top]) with o e,
  have := card_ord c,
  rw [← e, lift.principal_seg_coe, ← lift_card] at this,
  exact ⟨_, this.symm⟩
end, λ ⟨c', e⟩, e.symm ▸ lift_lt_univ _⟩

theorem lt_univ' {c} : c < univ.{u v} ↔ ∃ c', c = lift.{u (max (u+1) v)} c' :=
⟨λ h, let ⟨a, e, h'⟩ := lt_lift_iff.1 h in begin
  rw [← univ_id] at h',
  rcases lt_univ.{u}.1 h' with ⟨c', rfl⟩,
  exact ⟨c', by simp only [e.symm, lift_lift]⟩
end, λ ⟨c', e⟩, e.symm ▸ lift_lt_univ' _⟩

end cardinal

namespace ordinal

@[simp] theorem card_univ : card univ = cardinal.univ := rfl

/-- The supremum of a family of ordinals -/
def sup {ι} (f : ι → ordinal) : ordinal :=
omin {c | ∀ i, f i ≤ c}
  ⟨(sup (cardinal.succ ∘ card ∘ f)).ord, λ i, le_of_lt $
    cardinal.lt_ord.2 (lt_of_lt_of_le (cardinal.lt_succ_self _) (le_sup _ _))⟩

theorem le_sup {ι} (f : ι → ordinal) : ∀ i, f i ≤ sup f :=
omin_mem {c | ∀ i, f i ≤ c} _

theorem sup_le {ι} {f : ι → ordinal} {a} : sup f ≤ a ↔ ∀ i, f i ≤ a :=
⟨λ h i, le_trans (le_sup _ _) h, λ h, omin_le h⟩

theorem lt_sup {ι} {f : ι → ordinal} {a} : a < sup f ↔ ∃ i, a < f i :=
by simpa only [not_forall, not_le] using not_congr (@sup_le _ f a)

theorem is_normal.sup {f} (H : is_normal f)
  {ι} {g : ι → ordinal} (h : nonempty ι) : f (sup g) = sup (f ∘ g) :=
eq_of_forall_ge_iff $ λ a,
by rw [sup_le, comp, H.le_set' (λ_:ι, true) g (let ⟨i⟩ := h in ⟨i, ⟨⟩⟩)];
  intros; simp only [sup_le, true_implies_iff]

theorem sup_ord {ι} (f : ι → cardinal) : sup (λ i, (f i).ord) = (cardinal.sup f).ord :=
eq_of_forall_ge_iff $ λ a, by simp only [sup_le, cardinal.ord_le, cardinal.sup_le]

lemma sup_succ {ι} (f : ι → ordinal) : sup (λ i, succ (f i)) ≤ succ (sup f) :=
by { rw [ordinal.sup_le], intro i, rw ordinal.succ_le_succ, apply ordinal.le_sup }

lemma unbounded_range_of_sup_ge {α β : Type u} (r : α → α → Prop) [is_well_order α r] (f : β → α)
  (h : sup.{u u} (typein r ∘ f) ≥ type r) : unbounded r (range f) :=
begin
  apply (not_bounded_iff _).mp, rintro ⟨x, hx⟩, apply not_lt_of_ge h,
  refine lt_of_le_of_lt _ (typein_lt_type r x), rw [sup_le], intro y,
  apply le_of_lt, rw typein_lt_typein, apply hx, apply mem_range_self
end

/-- The supremum of a family of ordinals indexed by the set
  of ordinals less than some `o : ordinal.{u}`.
  (This is not a special case of `sup` over the subtype,
  because `{a // a < o} : Type (u+1)` and `sup` only works over
  families in `Type u`.) -/
def bsup (o : ordinal.{u}) : (Π a < o, ordinal.{max u v}) → ordinal.{max u v} :=
match o, o.out, o.out_eq with
| _, ⟨α, r, _⟩, rfl, f := by exactI sup (λ a, f (typein r a) (typein_lt_type _ _))
end

theorem bsup_le {o f a} : bsup.{u v} o f ≤ a ↔ ∀ i h, f i h ≤ a :=
match o, o.out, o.out_eq, f :
 ∀ o w (e : ⟦w⟧ = o) (f : Π (a : ordinal.{u}), a < o → ordinal.{(max u v)}),
   bsup._match_1 o w e f ≤ a ↔ ∀ i h, f i h ≤ a with
| _, ⟨α, r, _⟩, rfl, f := by rw [bsup._match_1, sup_le]; exactI
  ⟨λ H i h, by simpa only [typein_enum] using H (enum r i h), λ H b, H _ _⟩
end

theorem bsup_type (r : α → α → Prop) [is_well_order α r] (f) :
  bsup (type r) f = sup (λ a, f (typein r a) (typein_lt_type _ _)) :=
eq_of_forall_ge_iff $ λ o,
by rw [bsup_le, sup_le]; exact
  ⟨λ H b, H _ _, λ H i h, by simpa only [typein_enum] using H (enum r i h)⟩

theorem le_bsup {o} (f : Π a < o, ordinal) (i h) : f i h ≤ bsup o f :=
bsup_le.1 (le_refl _) _ _

theorem lt_bsup {o : ordinal} {f : Π a < o, ordinal}
  (hf : ∀{a a'} (ha : a < o) (ha' : a' < o), a < a' → f a ha < f a' ha')
  (ho : o.is_limit) (i h) : f i h < bsup o f :=
lt_of_lt_of_le (hf _ _ $ lt_succ_self i) (le_bsup f i.succ $ ho.2 _ h)

theorem bsup_id {o} (ho : is_limit o) : bsup.{u u} o (λ x _, x) = o :=
begin
  apply le_antisymm, rw [bsup_le], intro i, apply le_of_lt,
  rw [←not_lt], intro h, apply lt_irrefl (bsup.{u u} o (λ x _, x)),
  apply lt_of_le_of_lt _ (lt_bsup _ ho _ h), refl, intros, assumption
end

theorem is_normal.bsup {f} (H : is_normal f)
  {o : ordinal} : ∀ (g : Π a < o, ordinal) (h : o ≠ 0),
  f (bsup o g) = bsup o (λ a h, f (g a h)) :=
induction_on o $ λ α r _ g h,
by resetI; rw [bsup_type,
     H.sup (type_ne_zero_iff_nonempty.1 h), bsup_type]

theorem is_normal.bsup_eq {f} (H : is_normal f) {o : ordinal} (h : is_limit o) :
  bsup.{u} o (λx _, f x) = f o :=
by { rw [←is_normal.bsup.{u u} H (λ x _, x) h.1, bsup_id h] }

/-- The ordinal exponential, defined by transfinite recursion. -/
def power (a b : ordinal) : ordinal :=
if a = 0 then 1 - b else
limit_rec_on b 1 (λ _ IH, IH * a) (λ b _, bsup.{u u} b)

instance : has_pow ordinal ordinal := ⟨power⟩
local infixr ^ := @pow ordinal ordinal ordinal.has_pow

theorem zero_power' (a : ordinal) : 0 ^ a = 1 - a :=
by simp only [pow, power, if_pos rfl]

@[simp] theorem zero_power {a : ordinal} (a0 : a ≠ 0) : 0 ^ a = 0 :=
by rwa [zero_power', sub_eq_zero_iff_le, one_le_iff_ne_zero]

@[simp] theorem power_zero (a : ordinal) : a ^ 0 = 1 :=
by by_cases a = 0; [simp only [pow, power, if_pos h, sub_zero],
simp only [pow, power, if_neg h, limit_rec_on_zero]]

@[simp] theorem power_succ (a b : ordinal) : a ^ succ b = a ^ b * a :=
if h : a = 0 then by subst a; simp only [zero_power (succ_ne_zero _), mul_zero]
else by simp only [pow, power, limit_rec_on_succ, if_neg h]

theorem power_limit {a b : ordinal} (a0 : a ≠ 0) (h : is_limit b) :
  a ^ b = bsup.{u u} b (λ c _, a ^ c) :=
by simp only [pow, power, if_neg a0]; rw limit_rec_on_limit _ _ _ _ h; refl

theorem power_le_of_limit {a b c : ordinal} (a0 : a ≠ 0) (h : is_limit b) :
  a ^ b ≤ c ↔ ∀ b' < b, a ^ b' ≤ c :=
by rw [power_limit a0 h, bsup_le]

theorem lt_power_of_limit {a b c : ordinal} (b0 : b ≠ 0) (h : is_limit c) :
  a < b ^ c ↔ ∃ c' < c, a < b ^ c' :=
by rw [← not_iff_not, not_exists]; simp only [not_lt, power_le_of_limit b0 h, exists_prop, not_and]

@[simp] theorem power_one (a : ordinal) : a ^ 1 = a :=
by rw [← succ_zero, power_succ]; simp only [power_zero, one_mul]

@[simp] theorem one_power (a : ordinal) : 1 ^ a = 1 :=
begin
  apply limit_rec_on a,
  { simp only [power_zero] },
  { intros _ ih, simp only [power_succ, ih, mul_one] },
  refine λ b l IH, eq_of_forall_ge_iff (λ c, _),
  rw [power_le_of_limit one_ne_zero l],
  exact ⟨λ H, by simpa only [power_zero] using H 0 l.pos,
         λ H b' h, by rwa IH _ h⟩,
end

theorem power_pos {a : ordinal} (b)
  (a0 : 0 < a) : 0 < a ^ b :=
begin
  have h0 : 0 < a ^ 0, {simp only [power_zero, zero_lt_one]},
  apply limit_rec_on b,
  { exact h0 },
  { intros b IH, rw [power_succ],
    exact mul_pos IH a0 },
  { exact λ b l _, (lt_power_of_limit (pos_iff_ne_zero.1 a0) l).2
      ⟨0, l.pos, h0⟩ },
end

theorem power_ne_zero {a : ordinal} (b)
  (a0 : a ≠ 0) : a ^ b ≠ 0 :=
pos_iff_ne_zero.1 $ power_pos b $ pos_iff_ne_zero.2 a0

theorem power_is_normal {a : ordinal} (h : 1 < a) : is_normal ((^) a) :=
have a0 : 0 < a, from lt_trans zero_lt_one h,
⟨λ b, by simpa only [mul_one, power_succ] using
  (mul_lt_mul_iff_left (power_pos b a0)).2 h,
 λ b l c, power_le_of_limit (ne_of_gt a0) l⟩

theorem power_lt_power_iff_right {a b c : ordinal}
  (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c :=
(power_is_normal a1).lt_iff

theorem power_le_power_iff_right {a b c : ordinal}
  (a1 : 1 < a) : a ^ b ≤ a ^ c ↔ b ≤ c :=
(power_is_normal a1).le_iff

theorem power_right_inj {a b c : ordinal}
  (a1 : 1 < a) : a ^ b = a ^ c ↔ b = c :=
(power_is_normal a1).inj

theorem power_is_limit {a b : ordinal}
  (a1 : 1 < a) : is_limit b → is_limit (a ^ b) :=
(power_is_normal a1).is_limit

theorem power_is_limit_left {a b : ordinal}
  (l : is_limit a) (hb : b ≠ 0) : is_limit (a ^ b) :=
begin
  rcases zero_or_succ_or_limit b with e|⟨b,rfl⟩|l',
  { exact absurd e hb },
  { rw power_succ,
    exact mul_is_limit (power_pos _ l.pos) l },
  { exact power_is_limit l.one_lt l' }
end

theorem power_le_power_right {a b c : ordinal}
  (h₁ : 0 < a) (h₂ : b ≤ c) : a ^ b ≤ a ^ c :=
begin
  cases lt_or_eq_of_le (one_le_iff_pos.2 h₁) with h₁ h₁,
  { exact (power_le_power_iff_right h₁).2 h₂ },
  { subst a, simp only [one_power] }
end

theorem power_le_power_left {a b : ordinal} (c)
  (ab : a ≤ b) : a ^ c ≤ b ^ c :=
begin
  by_cases a0 : a = 0,
  { subst a, by_cases c0 : c = 0,
    { subst c, simp only [power_zero] },
    { simp only [zero_power c0, zero_le] } },
  { apply limit_rec_on c,
    { simp only [power_zero] },
    { intros c IH, simpa only [power_succ] using mul_le_mul IH ab },
    { exact λ c l IH, (power_le_of_limit a0 l).2
        (λ b' h, le_trans (IH _ h) (power_le_power_right
          (lt_of_lt_of_le (pos_iff_ne_zero.2 a0) ab) (le_of_lt h))) } }
end

theorem le_power_self {a : ordinal} (b) (a1 : 1 < a) : b ≤ a ^ b :=
(power_is_normal a1).le_self _

theorem power_lt_power_left_of_succ {a b c : ordinal}
  (ab : a < b) : a ^ succ c < b ^ succ c :=
by rw [power_succ, power_succ]; exact
lt_of_le_of_lt
  (mul_le_mul_right _ $ power_le_power_left _ $ le_of_lt ab)
  (mul_lt_mul_of_pos_left ab (power_pos _ (lt_of_le_of_lt (zero_le _) ab)))

theorem power_add (a b c : ordinal) : a ^ (b + c) = a ^ b * a ^ c :=
begin
  by_cases a0 : a = 0,
  { subst a,
    by_cases c0 : c = 0, {simp only [c0, add_zero, power_zero, mul_one]},
    have : b+c ≠ 0 := ne_of_gt (lt_of_lt_of_le
      (pos_iff_ne_zero.2 c0) (le_add_left _ _)),
    simp only [zero_power c0, zero_power this, mul_zero] },
  cases eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with a1 a1,
  { subst a1, simp only [one_power, mul_one] },
  apply limit_rec_on c,
  { simp only [add_zero, power_zero, mul_one] },
  { intros c IH,
    rw [add_succ, power_succ, IH, power_succ, mul_assoc] },
  { intros c l IH,
    refine eq_of_forall_ge_iff (λ d, (((power_is_normal a1).trans
      (add_is_normal b)).limit_le l).trans _),
    simp only [IH] {contextual := tt},
    exact (((mul_is_normal $ power_pos b (pos_iff_ne_zero.2 a0)).trans
      (power_is_normal a1)).limit_le l).symm }
end

theorem power_dvd_power (a) {b c : ordinal}
  (h : b ≤ c) : a ^ b ∣ a ^ c :=
by rw [← add_sub_cancel_of_le h, power_add]; apply dvd_mul

theorem power_dvd_power_iff {a b c : ordinal}
  (a1 : 1 < a) : a ^ b ∣ a ^ c ↔ b ≤ c :=
⟨λ h, le_of_not_lt $ λ hn,
  not_le_of_lt ((power_lt_power_iff_right a1).2 hn) $
   le_of_dvd (power_ne_zero _ $ one_le_iff_ne_zero.1 $ le_of_lt a1) h,
power_dvd_power _⟩

theorem power_mul (a b c : ordinal) : a ^ (b * c) = (a ^ b) ^ c :=
begin
  by_cases b0 : b = 0, {simp only [b0, zero_mul, power_zero, one_power]},
  by_cases a0 : a = 0,
  { subst a,
    by_cases c0 : c = 0, {simp only [c0, mul_zero, power_zero]},
    simp only [zero_power b0, zero_power c0, zero_power (mul_ne_zero b0 c0)] },
  cases eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with a1 a1,
  { subst a1, simp only [one_power] },
  apply limit_rec_on c,
  { simp only [mul_zero, power_zero] },
  { intros c IH,
    rw [mul_succ, power_add, IH, power_succ] },
  { intros c l IH,
    refine eq_of_forall_ge_iff (λ d, (((power_is_normal a1).trans
      (mul_is_normal (pos_iff_ne_zero.2 b0))).limit_le l).trans _),
    simp only [IH] {contextual := tt},
    exact (power_le_of_limit (power_ne_zero _ a0) l).symm }
end

/-- The ordinal logarithm is the solution `u` to the equation
  `x = b ^ u * v + w` where `v < b` and `w < b`. -/
def log (b : ordinal) (x : ordinal) : ordinal :=
if h : 1 < b then pred $
  omin {o | x < b^o} ⟨succ x, succ_le.1 (le_power_self _ h)⟩
else 0

@[simp] theorem log_not_one_lt {b : ordinal} (b1 : ¬ 1 < b) (x : ordinal) : log b x = 0 :=
by simp only [log, dif_neg b1]

theorem log_def {b : ordinal} (b1 : 1 < b) (x : ordinal) : log b x =
  pred (omin {o | x < b^o} (log._proof_1 b x b1)) :=
by simp only [log, dif_pos b1]

@[simp] theorem log_zero (b : ordinal) : log b 0 = 0 :=
if b1 : 1 < b then
  by rw [log_def b1, ← le_zero, pred_le];
     apply omin_le; change 0<b^succ 0;
     rw [succ_zero, power_one];
     exact lt_trans zero_lt_one b1
else by simp only [log_not_one_lt b1]

theorem succ_log_def {b x : ordinal} (b1 : 1 < b) (x0 : 0 < x) : succ (log b x) =
  omin {o | x < b^o} (log._proof_1 b x b1) :=
begin
  let t := omin {o | x < b^o} (log._proof_1 b x b1),
  have : x < b ^ t := omin_mem {o | x < b^o} _,
  rcases zero_or_succ_or_limit t with h|h|h,
  { refine (not_lt_of_le (one_le_iff_pos.2 x0) _).elim,
    simpa only [h, power_zero] },
  { rw [show log b x = pred t, from log_def b1 x,
        succ_pred_iff_is_succ.2 h] },
  { rcases (lt_power_of_limit (ne_of_gt $ lt_trans zero_lt_one b1) h).1 this with ⟨a, h₁, h₂⟩,
    exact (not_le_of_lt h₁).elim (le_omin.1 (le_refl t) a h₂) }
end

theorem lt_power_succ_log {b : ordinal} (b1 : 1 < b) (x : ordinal) :
  x < b ^ succ (log b x) :=
begin
  cases lt_or_eq_of_le (zero_le x) with x0 x0,
  { rw [succ_log_def b1 x0], exact omin_mem {o | x < b^o} _ },
  { subst x, apply power_pos _ (lt_trans zero_lt_one b1) }
end

theorem power_log_le (b) {x : ordinal} (x0 : 0 < x) :
  b ^ log b x ≤ x :=
begin
  by_cases b0 : b = 0,
  { rw [b0, zero_power'],
    refine le_trans (sub_le_self _ _) (one_le_iff_pos.2 x0) },
  cases lt_or_eq_of_le (one_le_iff_ne_zero.2 b0) with b1 b1,
  { refine le_of_not_lt (λ h, not_le_of_lt (lt_succ_self (log b x)) _),
    have := @omin_le {o | x < b^o} _ _ h,
    rwa ← succ_log_def b1 x0 at this },
  { rw [← b1, one_power], exact one_le_iff_pos.2 x0 }
end

theorem le_log {b x c : ordinal} (b1 : 1 < b) (x0 : 0 < x) :
  c ≤ log b x ↔ b ^ c ≤ x :=
⟨λ h, le_trans ((power_le_power_iff_right b1).2 h) (power_log_le b x0),
 λ h, le_of_not_lt $ λ hn,
   not_le_of_lt (lt_power_succ_log b1 x) $
   le_trans ((power_le_power_iff_right b1).2 (succ_le.2 hn)) h⟩

theorem log_lt {b x c : ordinal} (b1 : 1 < b) (x0 : 0 < x) :
  log b x < c ↔ x < b ^ c :=
lt_iff_lt_of_le_iff_le (le_log b1 x0)

theorem log_le_log (b) {x y : ordinal} (xy : x ≤ y) :
  log b x ≤ log b y :=
if x0 : x = 0 then by simp only [x0, log_zero, zero_le] else
have x0 : 0 < x, from pos_iff_ne_zero.2 x0,
if b1 : 1 < b then
  (le_log b1 (lt_of_lt_of_le x0 xy)).2 $ le_trans (power_log_le _ x0) xy
else by simp only [log_not_one_lt b1, zero_le]

theorem log_le_self (b x : ordinal) : log b x ≤ x :=
if x0 : x = 0 then by simp only [x0, log_zero, zero_le] else
if b1 : 1 < b then
  le_trans (le_power_self _ b1) (power_log_le b (pos_iff_ne_zero.2 x0))
else by simp only [log_not_one_lt b1, zero_le]

@[simp] theorem nat_cast_mul {m n : ℕ} : ((m * n : ℕ) : ordinal) = m * n :=
by induction n with n IH; [simp only [nat.cast_zero, nat.mul_zero, mul_zero],
  rw [nat.mul_succ, nat.cast_add, IH, nat.cast_succ, mul_add_one]]

@[simp] theorem nat_cast_power {m n : ℕ} : ((pow m n : ℕ) : ordinal) = m ^ n :=
by induction n with n IH; [simp only [nat.pow_zero, nat.cast_zero, power_zero, nat.cast_one],
  rw [nat.pow_succ, nat_cast_mul, IH, nat.cast_succ, ← succ_eq_add_one, power_succ]]

@[simp] theorem nat_cast_le {m n : ℕ} : (m : ordinal) ≤ n ↔ m ≤ n :=
by rw [← cardinal.ord_nat, ← cardinal.ord_nat,
       cardinal.ord_le_ord, cardinal.nat_cast_le]

@[simp] theorem nat_cast_lt {m n : ℕ} : (m : ordinal) < n ↔ m < n :=
by simp only [lt_iff_le_not_le, nat_cast_le]

@[simp] theorem nat_cast_inj {m n : ℕ} : (m : ordinal) = n ↔ m = n :=
by simp only [le_antisymm_iff, nat_cast_le]

@[simp] theorem nat_cast_eq_zero {n : ℕ} : (n : ordinal) = 0 ↔ n = 0 :=
@nat_cast_inj n 0

theorem nat_cast_ne_zero {n : ℕ} : (n : ordinal) ≠ 0 ↔ n ≠ 0 :=
not_congr nat_cast_eq_zero

@[simp] theorem nat_cast_pos {n : ℕ} : (0 : ordinal) < n ↔ 0 < n :=
@nat_cast_lt 0 n

@[simp] theorem nat_cast_sub {m n : ℕ} : ((m - n : ℕ) : ordinal) = m - n :=
(_root_.le_total m n).elim
  (λ h, by rw [nat.sub_eq_zero_iff_le.2 h, sub_eq_zero_iff_le.2 (nat_cast_le.2 h)]; refl)
  (λ h, (add_left_cancel n).1 $ by rw [← nat.cast_add,
     nat.add_sub_cancel' h, add_sub_cancel_of_le (nat_cast_le.2 h)])

@[simp] theorem nat_cast_div {m n : ℕ} : ((m / n : ℕ) : ordinal) = m / n :=
if n0 : n = 0 then by simp only [n0, nat.div_zero, nat.cast_zero, div_zero] else
have n0':_, from nat_cast_ne_zero.2 n0,
le_antisymm
  (by rw [le_div n0', ← nat_cast_mul, nat_cast_le, mul_comm];
      apply nat.div_mul_le_self)
  (by rw [div_le n0', succ, ← nat.cast_succ, ← nat_cast_mul,
          nat_cast_lt, mul_comm, ← nat.div_lt_iff_lt_mul _ _ (nat.pos_of_ne_zero n0)];
      apply nat.lt_succ_self)

@[simp] theorem nat_cast_mod {m n : ℕ} : ((m % n : ℕ) : ordinal) = m % n :=
by rw [← add_left_cancel (n*(m/n)), div_add_mod, ← nat_cast_div, ← nat_cast_mul, ← nat.cast_add,
       add_comm, nat.mod_add_div]

@[simp] theorem nat_le_card {o} {n : ℕ} : (n : cardinal) ≤ card o ↔ (n : ordinal) ≤ o :=
⟨λ h, by rwa [← cardinal.ord_le, cardinal.ord_nat] at h,
 λ h, card_nat n ▸ card_le_card h⟩

@[simp] theorem nat_lt_card {o} {n : ℕ} : (n : cardinal) < card o ↔ (n : ordinal) < o :=
by rw [← succ_le, ← cardinal.succ_le, ← cardinal.nat_succ, nat_le_card]; refl

@[simp] theorem card_lt_nat {o} {n : ℕ} : card o < n ↔ o < n :=
lt_iff_lt_of_le_iff_le nat_le_card

@[simp] theorem card_le_nat {o} {n : ℕ} : card o ≤ n ↔ o ≤ n :=
le_iff_le_iff_lt_iff_lt.2 nat_lt_card

@[simp] theorem card_eq_nat {o} {n : ℕ} : card o = n ↔ o = n :=
by simp only [le_antisymm_iff, card_le_nat, nat_le_card]

@[simp] theorem type_fin (n : ℕ) : @type (fin n) (<) _ = n :=
by rw [← card_eq_nat, card_type, mk_fin]

@[simp] theorem lift_nat_cast (n : ℕ) : lift n = n :=
by induction n with n ih; [simp only [nat.cast_zero, lift_zero],
  simp only [nat.cast_succ, lift_add, ih, lift_one]]

theorem lift_type_fin (n : ℕ) : lift (@type (fin n) (<) _) = n :=
by simp only [type_fin, lift_nat_cast]

theorem fintype_card (r : α → α → Prop) [is_well_order α r] [fintype α] : type r = fintype.card α :=
by rw [← card_eq_nat, card_type, fintype_card]

end ordinal

namespace cardinal
open ordinal

@[simp] theorem ord_omega : ord.{u} omega = ordinal.omega :=
le_antisymm (ord_le.2 $ le_refl _) $
le_of_forall_lt $ λ o h, begin
  rcases ordinal.lt_lift_iff.1 h with ⟨o, rfl, h'⟩,
  rw [lt_ord, ← lift_card, ← lift_omega.{0 u},
      lift_lt, ← typein_enum (<) h'],
  exact lt_omega_iff_fintype.2 ⟨set.fintype_lt_nat _⟩
end

@[simp] theorem add_one_of_omega_le {c} (h : omega ≤ c) : c + 1 = c :=
by rw [add_comm, ← card_ord c, ← card_one,
       ← card_add, one_add_of_omega_le];
   rwa [← ord_omega, ord_le_ord]

end cardinal

namespace ordinal

theorem lt_omega {o : ordinal.{u}} : o < omega ↔ ∃ n : ℕ, o = n :=
by rw [← cardinal.ord_omega, cardinal.lt_ord, lt_omega]; simp only [card_eq_nat]

theorem nat_lt_omega (n : ℕ) : (n : ordinal) < omega :=
lt_omega.2 ⟨_, rfl⟩

theorem omega_pos : 0 < omega := nat_lt_omega 0

theorem omega_ne_zero : omega ≠ 0 := ne_of_gt omega_pos

theorem one_lt_omega : 1 < omega := by simpa only [nat.cast_one] using nat_lt_omega 1

theorem omega_is_limit : is_limit omega :=
⟨omega_ne_zero, λ o h,
  let ⟨n, e⟩ := lt_omega.1 h in
  by rw [e]; exact nat_lt_omega (n+1)⟩

theorem omega_le {o : ordinal.{u}} : omega ≤ o ↔ ∀ n : ℕ, (n : ordinal) ≤ o :=
⟨λ h n, le_trans (le_of_lt (nat_lt_omega _)) h,
 λ H, le_of_forall_lt $ λ a h,
   let ⟨n, e⟩ := lt_omega.1 h in
   by rw [e, ← succ_le]; exact H (n+1)⟩

theorem nat_lt_limit {o} (h : is_limit o) : ∀ n : ℕ, (n : ordinal) < o
| 0     := lt_of_le_of_ne (zero_le o) h.1.symm
| (n+1) := h.2 _ (nat_lt_limit n)

theorem omega_le_of_is_limit {o} (h : is_limit o) : omega ≤ o :=
omega_le.2 $ λ n, le_of_lt $ nat_lt_limit h n

theorem add_omega {a : ordinal} (h : a < omega) : a + omega = omega :=
begin
  rcases lt_omega.1 h with ⟨n, rfl⟩,
  clear h, induction n with n IH,
  { rw [nat.cast_zero, zero_add] },
  { rw [nat.cast_succ, add_assoc, one_add_of_omega_le (le_refl _), IH] }
end

theorem add_lt_omega {a b : ordinal} (ha : a < omega) (hb : b < omega) : a + b < omega :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat.cast_add]; apply nat_lt_omega
end

theorem mul_lt_omega {a b : ordinal} (ha : a < omega) (hb : b < omega) : a * b < omega :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat_cast_mul]; apply nat_lt_omega
end

theorem is_limit_iff_omega_dvd {a : ordinal} : is_limit a ↔ a ≠ 0 ∧ omega ∣ a :=
begin
  refine ⟨λ l, ⟨l.1, ⟨a / omega, le_antisymm _ (mul_div_le _ _)⟩⟩, λ h, _⟩,
  { refine (limit_le l).2 (λ x hx, le_of_lt _),
    rw [← div_lt omega_ne_zero, ← succ_le, le_div omega_ne_zero,
        mul_succ, add_le_of_limit omega_is_limit],
    intros b hb,
    rcases lt_omega.1 hb with ⟨n, rfl⟩,
    exact le_trans (add_le_add_right (mul_div_le _ _) _)
      (le_of_lt $ lt_sub.1 $ nat_lt_limit (sub_is_limit l hx) _) },
  { rcases h with ⟨a0, b, rfl⟩,
    refine mul_is_limit_left omega_is_limit
      (pos_iff_ne_zero.2 $ mt _ a0),
    intro e, simp only [e, mul_zero] }
end

local infixr ^ := @pow ordinal ordinal ordinal.has_pow

theorem power_lt_omega {a b : ordinal} (ha : a < omega) (hb : b < omega) : a ^ b < omega :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat_cast_power]; apply nat_lt_omega
end

theorem add_omega_power {a b : ordinal} (h : a < omega ^ b) : a + omega ^ b = omega ^ b :=
begin
  refine le_antisymm _ (le_add_left _ _),
  revert h, apply limit_rec_on b,
  { intro h, rw [power_zero, ← succ_zero, lt_succ, le_zero] at h,
    rw [h, zero_add] },
  { intros b _ h, rw [power_succ] at h,
    rcases (lt_mul_of_limit omega_is_limit).1 h with ⟨x, xo, ax⟩,
    refine le_trans (add_le_add_right (le_of_lt ax) _) _,
    rw [power_succ, ← mul_add, add_omega xo] },
  { intros b l IH h, rcases (lt_power_of_limit omega_ne_zero l).1 h with ⟨x, xb, ax⟩,
    refine (((add_is_normal a).trans (power_is_normal one_lt_omega))
      .limit_le l).2 (λ y yb, _),
    let z := max x y,
    have := IH z (max_lt xb yb)
      (lt_of_lt_of_le ax $ power_le_power_right omega_pos (le_max_left _ _)),
    exact le_trans (add_le_add_left (power_le_power_right omega_pos (le_max_right _ _)) _)
      (le_trans this (power_le_power_right omega_pos $ le_of_lt $ max_lt xb yb)) }
end

theorem add_lt_omega_power {a b c : ordinal} (h₁ : a < omega ^ c) (h₂ : b < omega ^ c) :
  a + b < omega ^ c :=
by rwa [← add_omega_power h₁, add_lt_add_iff_left]

theorem add_absorp {a b c : ordinal} (h₁ : a < omega ^ b) (h₂ : omega ^ b ≤ c) : a + c = c :=
by rw [← add_sub_cancel_of_le h₂, ← add_assoc, add_omega_power h₁]

theorem add_absorp_iff {o : ordinal} (o0 : o > 0) : (∀ a < o, a + o = o) ↔ ∃ a, o = omega ^ a :=
⟨λ H, ⟨log omega o, begin
  refine ((lt_or_eq_of_le (power_log_le _ o0))
    .resolve_left $ λ h, _).symm,
  have := H _ h,
  have := lt_power_succ_log one_lt_omega o,
  rw [power_succ, lt_mul_of_limit omega_is_limit] at this,
  rcases this with ⟨a, ao, h'⟩,
  rcases lt_omega.1 ao with ⟨n, rfl⟩, clear ao,
  revert h', apply not_lt_of_le,
  suffices e : omega ^ log omega o * ↑n + o = o,
  { simpa only [e] using le_add_right (omega ^ log omega o * ↑n) o },
  induction n with n IH, {simp only [nat.cast_zero, mul_zero, zero_add]},
  simp only [nat.cast_succ, mul_add_one, add_assoc, this, IH]
end⟩,
λ ⟨b, e⟩, e.symm ▸ λ a, add_omega_power⟩

theorem add_mul_limit_aux {a b c : ordinal} (ba : b + a = a)
  (l : is_limit c)
  (IH : ∀ c' < c, (a + b) * succ c' = a * succ c' + b) :
  (a + b) * c = a * c :=
le_antisymm
  ((mul_le_of_limit l).2 $ λ c' h, begin
    apply le_trans (mul_le_mul_left _ (le_of_lt $ lt_succ_self _)),
    rw IH _ h,
    apply le_trans (add_le_add_left _ _),
    { rw ← mul_succ, exact mul_le_mul_left _ (succ_le.2 $ l.2 _ h) },
    { rw ← ba, exact le_add_right _ _ }
  end)
  (mul_le_mul_right _ (le_add_right _ _))

theorem add_mul_succ {a b : ordinal} (c) (ba : b + a = a) :
  (a + b) * succ c = a * succ c + b :=
begin
  apply limit_rec_on c,
  { simp only [succ_zero, mul_one] },
  { intros c IH,
    rw [mul_succ, IH, ← add_assoc, add_assoc _ b, ba, ← mul_succ] },
  { intros c l IH,
    have := add_mul_limit_aux ba l IH,
    rw [mul_succ, add_mul_limit_aux ba l IH, mul_succ, add_assoc] }
end

theorem add_mul_limit {a b c : ordinal} (ba : b + a = a)
  (l : is_limit c) : (a + b) * c = a * c :=
add_mul_limit_aux ba l (λ c' _, add_mul_succ c' ba)

theorem mul_omega {a : ordinal} (a0 : 0 < a) (ha : a < omega) : a * omega = omega :=
le_antisymm
  ((mul_le_of_limit omega_is_limit).2 $ λ b hb, le_of_lt (mul_lt_omega ha hb))
  (by simpa only [one_mul] using mul_le_mul_right omega (one_le_iff_pos.2 a0))

theorem mul_lt_omega_power {a b c : ordinal}
  (c0 : 0 < c) (ha : a < omega ^ c) (hb : b < omega) : a * b < omega ^ c :=
if b0 : b = 0 then by simp only [b0, mul_zero, power_pos _ omega_pos] else begin
  rcases zero_or_succ_or_limit c with rfl|⟨c,rfl⟩|l,
  { exact (lt_irrefl _).elim c0 },
  { rw power_succ at ha,
    rcases ((mul_is_normal $ power_pos _ omega_pos).limit_lt
      omega_is_limit).1 ha with ⟨n, hn, an⟩,
    refine lt_of_le_of_lt (mul_le_mul_right _ (le_of_lt an)) _,
    rw [power_succ, mul_assoc, mul_lt_mul_iff_left (power_pos _ omega_pos)],
    exact mul_lt_omega hn hb },
  { rcases ((power_is_normal one_lt_omega).limit_lt l).1 ha with ⟨x, hx, ax⟩,
    refine lt_of_le_of_lt (mul_le_mul (le_of_lt ax) (le_of_lt hb)) _,
    rw [← power_succ, power_lt_power_iff_right one_lt_omega],
    exact l.2 _ hx }
end

theorem mul_omega_dvd {a : ordinal}
  (a0 : 0 < a) (ha : a < omega) : ∀ {b}, omega ∣ b → a * b = b
| _ ⟨b, rfl⟩ := by rw [← mul_assoc, mul_omega a0 ha]

theorem mul_omega_power_power {a b : ordinal} (a0 : 0 < a) (h : a < omega ^ omega ^ b) :
  a * omega ^ omega ^ b = omega ^ omega ^ b :=
begin
  by_cases b0 : b = 0, {rw [b0, power_zero, power_one] at h ⊢, exact mul_omega a0 h},
  refine le_antisymm _ (by simpa only [one_mul] using mul_le_mul_right (omega^omega^b) (one_le_iff_pos.2 a0)),
  rcases (lt_power_of_limit omega_ne_zero (power_is_limit_left omega_is_limit b0)).1 h
    with ⟨x, xb, ax⟩,
  refine le_trans (mul_le_mul_right _ (le_of_lt ax)) _,
  rw [← power_add, add_omega_power xb]
end

theorem power_omega {a : ordinal} (a1 : 1 < a) (h : a < omega) : a ^ omega = omega :=
le_antisymm
  ((power_le_of_limit (one_le_iff_ne_zero.1 $ le_of_lt a1) omega_is_limit).2
    (λ b hb, le_of_lt (power_lt_omega h hb)))
  (le_power_self _ a1)

theorem CNF_aux {b o : ordinal} (b0 : b ≠ 0) (o0 : o ≠ 0) :
  o % b ^ log b o < o :=
lt_of_lt_of_le
  (mod_lt _ $ power_ne_zero _ b0)
  (power_log_le _ $ pos_iff_ne_zero.2 o0)

@[elab_as_eliminator] noncomputable def CNF_rec {b : ordinal} (b0 : b ≠ 0)
  {C : ordinal → Sort*}
  (H0 : C 0)
  (H : ∀ o, o ≠ 0 → o % b ^ log b o < o → C (o % b ^ log b o) → C o)
  : ∀ o, C o
| o :=
  if o0 : o = 0 then by rw o0; exact H0 else
  have _, from CNF_aux b0 o0,
  H o o0 this (CNF_rec (o % b ^ log b o))
using_well_founded {dec_tac := `[assumption]}

@[simp] theorem CNF_rec_zero {b} (b0) {C H0 H} : @CNF_rec b b0 C H0 H 0 = H0 :=
by rw [CNF_rec, dif_pos rfl]; refl

@[simp] theorem CNF_rec_ne_zero {b} (b0) {C H0 H o} (o0) :
  @CNF_rec b b0 C H0 H o = H o o0 (CNF_aux b0 o0) (@CNF_rec b b0 C H0 H _) :=
by rw [CNF_rec, dif_neg o0]

/-- The Cantor normal form of an ordinal is the list of coefficients
  in the base-`b` expansion of `o`.

    CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)] -/
def CNF (b := omega) (o : ordinal) : list (ordinal × ordinal) :=
if b0 : b = 0 then [] else
CNF_rec b0 [] (λ o o0 h IH, (log b o, o / b ^ log b o) :: IH) o

@[simp] theorem zero_CNF (o) : CNF 0 o = [] :=
dif_pos rfl

@[simp] theorem CNF_zero (b) : CNF b 0 = [] :=
if b0 : b = 0 then dif_pos b0 else
(dif_neg b0).trans $ CNF_rec_zero _

theorem CNF_ne_zero {b o : ordinal} (b0 : b ≠ 0) (o0 : o ≠ 0) :
  CNF b o = (log b o, o / b ^ log b o) :: CNF b (o % b ^ log b o) :=
by unfold CNF; rw [dif_neg b0, dif_neg b0, CNF_rec_ne_zero b0 o0]

theorem one_CNF {o : ordinal} (o0 : o ≠ 0) :
  CNF 1 o = [(0, o)] :=
by rw [CNF_ne_zero one_ne_zero o0, log_not_one_lt (lt_irrefl _), power_zero, mod_one, CNF_zero, div_one]

theorem CNF_foldr {b : ordinal} (b0 : b ≠ 0) (o) :
  (CNF b o).foldr (λ p r, b ^ p.1 * p.2 + r) 0 = o :=
CNF_rec b0 (by rw CNF_zero; refl)
  (λ o o0 h IH, by rw [CNF_ne_zero b0 o0, list.foldr_cons, IH, div_add_mod]) o

theorem CNF_pairwise_aux (b := omega) (o) :
  (∀ p ∈ CNF b o, prod.fst p ≤ log b o) ∧
  (CNF b o).pairwise (λ p q, q.1 < p.1) :=
begin
  by_cases b0 : b = 0,
  { simp only [b0, zero_CNF, list.pairwise.nil, and_true], exact λ _, false.elim },
  cases lt_or_eq_of_le (one_le_iff_ne_zero.2 b0) with b1 b1,
  { refine CNF_rec b0 _ _ o,
    { simp only [CNF_zero, list.pairwise.nil, and_true], exact λ _, false.elim },
    intros o o0 H IH, cases IH with IH₁ IH₂,
    simp only [CNF_ne_zero b0 o0, list.forall_mem_cons, list.pairwise_cons, IH₂, and_true],
    refine ⟨⟨le_refl _, λ p m, _⟩, λ p m, _⟩,
    { exact le_trans (IH₁ p m) (log_le_log _ $ le_of_lt H) },
    { refine lt_of_le_of_lt (IH₁ p m) ((log_lt b1 _).2 _),
      { rw pos_iff_ne_zero, intro e,
        rw e at m, simpa only [CNF_zero] using m },
      { exact mod_lt _ (power_ne_zero _ b0) } } },
  { by_cases o0 : o = 0,
    { simp only [o0, CNF_zero, list.pairwise.nil, and_true], exact λ _, false.elim },
    rw [← b1, one_CNF o0],
    simp only [list.mem_singleton, log_not_one_lt (lt_irrefl _), forall_eq, le_refl, true_and, list.pairwise_singleton] }
end

theorem CNF_pairwise (b := omega) (o) :
  (CNF b o).pairwise (λ p q, prod.fst q < p.1) :=
(CNF_pairwise_aux _ _).2

theorem CNF_fst_le_log (b := omega) (o) :
  ∀ p ∈ CNF b o, prod.fst p ≤ log b o :=
(CNF_pairwise_aux _ _).1

theorem CNF_fst_le (b := omega) (o) (p ∈ CNF b o) : prod.fst p ≤ o :=
le_trans (CNF_fst_le_log _ _ p H) (log_le_self _ _)

theorem CNF_snd_lt {b : ordinal} (b1 : 1 < b) (o) :
  ∀ p ∈ CNF b o, prod.snd p < b :=
begin
  have b0 := ne_of_gt (lt_trans zero_lt_one b1),
  refine CNF_rec b0 (λ _, by rw [CNF_zero]; exact false.elim) _ o,
  intros o o0 H IH,
  simp only [CNF_ne_zero b0 o0, list.mem_cons_iff, list.forall_mem_cons', iff_true_intro IH, and_true],
  rw [div_lt (power_ne_zero _ b0), ← power_succ],
  exact lt_power_succ_log b1 _,
end

theorem CNF_sorted (b := omega) (o) :
  ((CNF b o).map prod.fst).sorted (>) :=
by rw [list.sorted, list.pairwise_map]; exact CNF_pairwise b o

/-- The next fixed point function, the least fixed point of the
  normal function `f` above `a`. -/
def nfp (f : ordinal → ordinal) (a : ordinal) :=
sup (λ n : ℕ, f^[n] a)

theorem iterate_le_nfp (f a n) : f^[n] a ≤ nfp f a :=
le_sup _ n

theorem le_nfp_self (f a) : a ≤ nfp f a :=
iterate_le_nfp f a 0

theorem is_normal.lt_nfp {f} (H : is_normal f) {a b} :
  f b < nfp f a ↔ b < nfp f a :=
lt_sup.trans $ iff.trans
  (by exact
   ⟨λ ⟨n, h⟩, ⟨n, lt_of_le_of_lt (H.le_self _) h⟩,
    λ ⟨n, h⟩, ⟨n+1, by rw iterate_succ'; exact H.lt_iff.2 h⟩⟩)
  lt_sup.symm

theorem is_normal.nfp_le {f} (H : is_normal f) {a b} :
  nfp f a ≤ f b ↔ nfp f a ≤ b :=
le_iff_le_iff_lt_iff_lt.2 H.lt_nfp

theorem is_normal.nfp_le_fp {f} (H : is_normal f) {a b}
  (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
sup_le.2 $ λ i, begin
  induction i with i IH generalizing a, {exact ab},
  exact IH (le_trans (H.le_iff.2 ab) h),
end

theorem is_normal.nfp_fp {f} (H : is_normal f) (a) : f (nfp f a) = nfp f a :=
begin
  refine le_antisymm _ (H.le_self _),
  cases le_or_lt (f a) a with aa aa,
  { rwa le_antisymm (H.nfp_le_fp (le_refl _) aa) (le_nfp_self _ _) },
  rcases zero_or_succ_or_limit (nfp f a) with e|⟨b, e⟩|l,
  { refine @le_trans _ _ _ (f a) _ (H.le_iff.2 _) (iterate_le_nfp f a 1),
    simp only [e, zero_le] },
  { have : f b < nfp f a := H.lt_nfp.2 (by simp only [e, lt_succ_self]),
    rw [e, lt_succ] at this,
    have ab : a ≤ b,
    { rw [← lt_succ, ← e],
      exact lt_of_lt_of_le aa (iterate_le_nfp f a 1) },
    refine le_trans (H.le_iff.2 (H.nfp_le_fp ab this))
      (le_trans this (le_of_lt _)),
    simp only [e, lt_succ_self] },
  { exact (H.2 _ l _).2 (λ b h, le_of_lt (H.lt_nfp.2 h)) }
end

theorem is_normal.le_nfp {f} (H : is_normal f) {a b} :
  f b ≤ nfp f a ↔ b ≤ nfp f a :=
⟨le_trans (H.le_self _), λ h,
  by simpa only [H.nfp_fp] using H.le_iff.2 h⟩

theorem nfp_eq_self {f : ordinal → ordinal} {a} (h : f a = a) : nfp f a = a :=
le_antisymm (sup_le.mpr $ λ i, by rw [iterate_fixed h]) (le_nfp_self f a)

/-- The derivative of a normal function `f` is
  the sequence of fixed points of `f`. -/
def deriv (f : ordinal → ordinal) (o : ordinal) : ordinal :=
limit_rec_on o (nfp f 0)
  (λ a IH, nfp f (succ IH))
  (λ a l, bsup.{u u} a)

@[simp] theorem deriv_zero (f) : deriv f 0 = nfp f 0 := limit_rec_on_zero _ _ _

@[simp] theorem deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
limit_rec_on_succ _ _ _ _

theorem deriv_limit (f) {o} : is_limit o →
  deriv f o = bsup.{u u} o (λ a _, deriv f a) :=
limit_rec_on_limit _ _ _ _

theorem deriv_is_normal (f) : is_normal (deriv f) :=
⟨λ o, by rw [deriv_succ, ← succ_le]; apply le_nfp_self,
 λ o l a, by rw [deriv_limit _ l, bsup_le]⟩

theorem is_normal.deriv_fp {f} (H : is_normal f) (o) : f (deriv.{u} f o) = deriv f o :=
begin
  apply limit_rec_on o,
  { rw [deriv_zero, H.nfp_fp] },
  { intros o ih, rw [deriv_succ, H.nfp_fp] },
  intros o l IH,
  rw [deriv_limit _ l, is_normal.bsup.{u u u} H _ l.1],
  refine eq_of_forall_ge_iff (λ c, _),
  simp only [bsup_le, IH] {contextual:=tt}
end

theorem is_normal.fp_iff_deriv {f} (H : is_normal f)
  {a} : f a ≤ a ↔ ∃ o, a = deriv f o :=
⟨λ ha, begin
  suffices : ∀ o (_:a ≤ deriv f o), ∃ o, a = deriv f o,
  from this a ((deriv_is_normal _).le_self _),
  intro o, apply limit_rec_on o,
  { intros h₁,
    refine ⟨0, le_antisymm h₁ _⟩,
    rw deriv_zero,
    exact H.nfp_le_fp (zero_le _) ha },
  { intros o IH h₁,
    cases le_or_lt a (deriv f o), {exact IH h},
    refine ⟨succ o, le_antisymm h₁ _⟩,
    rw deriv_succ,
    exact H.nfp_le_fp (succ_le.2 h) ha },
  { intros o l IH h₁,
    cases eq_or_lt_of_le h₁, {exact ⟨_, h⟩},
    rw [deriv_limit _ l, ← not_le, bsup_le, not_ball] at h,
    exact let ⟨o', h, hl⟩ := h in IH o' h (le_of_not_le hl) }
end, λ ⟨o, e⟩, e.symm ▸ le_of_eq (H.deriv_fp _)⟩

end ordinal

namespace cardinal
section using_ordinals
open ordinal

theorem ord_is_limit {c} (co : omega ≤ c) : (ord c).is_limit :=
begin
  refine ⟨λ h, omega_ne_zero _, λ a, lt_imp_lt_of_le_imp_le _⟩,
  { rw [← ordinal.le_zero, ord_le] at h,
    simpa only [card_zero, le_zero] using le_trans co h },
  { intro h, rw [ord_le] at h ⊢,
    rwa [← @add_one_of_omega_le (card a), ← card_succ],
    rw [← ord_le, ← le_succ_of_is_limit, ord_le],
    { exact le_trans co h },
    { rw ord_omega, exact omega_is_limit } }
end

def aleph_idx.initial_seg : @initial_seg cardinal ordinal (<) (<) :=
@order_embedding.collapse cardinal ordinal (<) (<) _ cardinal.ord.order_embedding

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)  -/
def aleph_idx : cardinal → ordinal := aleph_idx.initial_seg

@[simp] theorem aleph_idx.initial_seg_coe :
  (aleph_idx.initial_seg : cardinal → ordinal) = aleph_idx := rfl

@[simp] theorem aleph_idx_lt {a b} : aleph_idx a < aleph_idx b ↔ a < b :=
aleph_idx.initial_seg.to_order_embedding.ord.symm

@[simp] theorem aleph_idx_le {a b} : aleph_idx a ≤ aleph_idx b ↔ a ≤ b :=
by rw [← not_lt, ← not_lt, aleph_idx_lt]

theorem aleph_idx.init {a b} : b < aleph_idx a → ∃ c, aleph_idx c = b :=
aleph_idx.initial_seg.init _ _

def aleph_idx.order_iso : @order_iso cardinal.{u} ordinal.{u} (<) (<) :=
@order_iso.of_surjective cardinal.{u} ordinal.{u} (<) (<) aleph_idx.initial_seg.{u} $
(initial_seg.eq_or_principal aleph_idx.initial_seg.{u}).resolve_right $
λ ⟨o, e⟩, begin
  have : ∀ c, aleph_idx c < o := λ c, (e _).2 ⟨_, rfl⟩,
  refine ordinal.induction_on o _ this, introsI α r _ h,
  let s := sup.{u u} (λ a:α, inv_fun aleph_idx (ordinal.typein r a)),
  apply not_le_of_gt (lt_succ_self s),
  have I : injective aleph_idx := aleph_idx.initial_seg.to_embedding.injective,
  simpa only [typein_enum, left_inverse_inv_fun I (succ s)] using
    le_sup.{u u} (λ a, inv_fun aleph_idx (ordinal.typein r a))
      (ordinal.enum r _ (h (succ s))),
end

@[simp] theorem aleph_idx.order_iso_coe :
  (aleph_idx.order_iso : cardinal → ordinal) = aleph_idx := rfl

@[simp] theorem type_cardinal : @ordinal.type cardinal (<) _ = ordinal.univ.{u (u+1)} :=
by rw ordinal.univ_id; exact quotient.sound ⟨aleph_idx.order_iso⟩

@[simp] theorem mk_cardinal : mk cardinal = univ.{u (u+1)} :=
by simpa only [card_type, card_univ] using congr_arg card type_cardinal

def aleph'.order_iso := cardinal.aleph_idx.order_iso.symm

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = ℵ₁, etc. -/
def aleph' : ordinal → cardinal := aleph'.order_iso

@[simp] theorem aleph'.order_iso_coe :
  (aleph'.order_iso : ordinal → cardinal) = aleph' := rfl

@[simp] theorem aleph'_lt {o₁ o₂ : ordinal.{u}} : aleph' o₁ < aleph' o₂ ↔ o₁ < o₂ :=
aleph'.order_iso.ord.symm

@[simp] theorem aleph'_le {o₁ o₂ : ordinal.{u}} : aleph' o₁ ≤ aleph' o₂ ↔ o₁ ≤ o₂ :=
le_iff_le_iff_lt_iff_lt.2 aleph'_lt

@[simp] theorem aleph'_aleph_idx (c : cardinal.{u}) : aleph' c.aleph_idx = c :=
cardinal.aleph_idx.order_iso.to_equiv.symm_apply_apply c

@[simp] theorem aleph_idx_aleph' (o : ordinal.{u}) : (aleph' o).aleph_idx = o :=
cardinal.aleph_idx.order_iso.to_equiv.apply_symm_apply o

@[simp] theorem aleph'_zero : aleph' 0 = 0 :=
by rw [← le_zero, ← aleph'_aleph_idx 0, aleph'_le];
   apply ordinal.zero_le

@[simp] theorem aleph'_succ {o : ordinal.{u}} : aleph' o.succ = (aleph' o).succ :=
le_antisymm
 (cardinal.aleph_idx_le.1 $
  by rw [aleph_idx_aleph', ordinal.succ_le, ← aleph'_lt, aleph'_aleph_idx];
     apply cardinal.lt_succ_self)
 (cardinal.succ_le.2 $ aleph'_lt.2 $ ordinal.lt_succ_self _)

@[simp] theorem aleph'_nat : ∀ n : ℕ, aleph' n = n
| 0     := aleph'_zero
| (n+1) := show aleph' (ordinal.succ n) = n.succ,
           by rw [aleph'_succ, aleph'_nat, nat_succ]

theorem aleph'_le_of_limit {o : ordinal.{u}} (l : o.is_limit) {c} :
  aleph' o ≤ c ↔ ∀ o' < o, aleph' o' ≤ c :=
⟨λ h o' h', le_trans (aleph'_le.2 $ le_of_lt h') h,
 λ h, begin
  rw [← aleph'_aleph_idx c, aleph'_le, ordinal.limit_le l],
  intros x h',
  rw [← aleph'_le, aleph'_aleph_idx],
  exact h _ h'
end⟩

@[simp] theorem aleph'_omega : aleph' ordinal.omega = omega :=
eq_of_forall_ge_iff $ λ c, begin
  simp only [aleph'_le_of_limit omega_is_limit, ordinal.lt_omega, exists_imp_distrib, omega_le],
  exact forall_swap.trans (forall_congr $ λ n, by simp only [forall_eq, aleph'_nat]),
end

/-- aleph' and aleph_idx form an equivalence between `ordinal` and `cardinal` -/
@[simp] def aleph'_equiv : ordinal ≃ cardinal :=
⟨aleph', aleph_idx, aleph_idx_aleph', aleph'_aleph_idx⟩

/-- The `aleph` function gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ω`, `aleph 1 = succ ω` is the first
  uncountable cardinal, and so on. -/
def aleph (o : ordinal) : cardinal := aleph' (ordinal.omega + o)

@[simp] theorem aleph_lt {o₁ o₂ : ordinal.{u}} : aleph o₁ < aleph o₂ ↔ o₁ < o₂ :=
aleph'_lt.trans (ordinal.add_lt_add_iff_left _)

@[simp] theorem aleph_le {o₁ o₂ : ordinal.{u}} : aleph o₁ ≤ aleph o₂ ↔ o₁ ≤ o₂ :=
le_iff_le_iff_lt_iff_lt.2 aleph_lt

@[simp] theorem aleph_succ {o : ordinal.{u}} : aleph o.succ = (aleph o).succ :=
by rw [aleph, ordinal.add_succ, aleph'_succ]; refl

@[simp] theorem aleph_zero : aleph 0 = omega :=
by simp only [aleph, add_zero, aleph'_omega]

theorem omega_le_aleph' {o : ordinal} : omega ≤ aleph' o ↔ ordinal.omega ≤ o :=
by rw [← aleph'_omega, aleph'_le]

theorem omega_le_aleph (o : ordinal) : omega ≤ aleph o :=
by rw [aleph, omega_le_aleph']; apply ordinal.le_add_right

theorem ord_aleph_is_limit (o : ordinal) : is_limit (aleph o).ord :=
ord_is_limit $ omega_le_aleph _

theorem exists_aleph {c : cardinal} : omega ≤ c ↔ ∃ o, c = aleph o :=
⟨λ h, ⟨aleph_idx c - ordinal.omega,
  by rw [aleph, ordinal.add_sub_cancel_of_le, aleph'_aleph_idx];
     rwa [← omega_le_aleph', aleph'_aleph_idx]⟩,
 λ ⟨o, e⟩, e.symm ▸ omega_le_aleph _⟩

theorem aleph'_is_normal : is_normal (ord ∘ aleph') :=
⟨λ o, ord_lt_ord.2 $ aleph'_lt.2 $ ordinal.lt_succ_self _,
 λ o l a, by simp only [ord_le, aleph'_le_of_limit l]⟩

theorem aleph_is_normal : is_normal (ord ∘ aleph) :=
aleph'_is_normal.trans $ add_is_normal ordinal.omega

/- properties of mul -/

theorem mul_eq_self {c : cardinal} (h : omega ≤ c) : c * c = c :=
begin
  refine le_antisymm _
    (by simpa only [mul_one] using mul_le_mul_left c (le_trans (le_of_lt one_lt_omega) h)),
  refine acc.rec_on (cardinal.wf.apply c) (λ c _,
    quotient.induction_on c $ λ α IH ol, _) h,
  rcases ord_eq α with ⟨r, wo, e⟩, resetI,
  letI := decidable_linear_order_of_STO' r,
  haveI : is_well_order α (<) := wo,
  let g : α × α → α := λ p, max p.1 p.2,
  let f : α × α ↪ ordinal × (α × α) :=
    ⟨λ p:α×α, (typein (<) (g p), p), λ p q, congr_arg prod.snd⟩,
  let s := f ⁻¹'o (prod.lex (<) (prod.lex (<) (<))),
  haveI : is_well_order _ s := (order_embedding.preimage _ _).is_well_order,
  suffices : type s ≤ type r, {exact card_le_card this},
  refine le_of_forall_lt (λ o h, _),
  rcases typein_surj s h with ⟨p, rfl⟩,
  rw [← e, lt_ord],
  refine lt_of_le_of_lt (_ : _ ≤ card (typein (<) (g p)).succ * card (typein (<) (g p)).succ) _,
  { have : {q|s q p} ⊆ (insert (g p) {x | x < (g p)}).prod (insert (g p) {x | x < (g p)}),
    { intros q h,
      simp only [s, embedding.coe_fn_mk, order.preimage, typein_lt_typein, prod.lex_def, typein_inj] at h,
      exact max_le_iff.1 (le_iff_lt_or_eq.2 $ h.imp_right and.left) },
    suffices H : (insert (g p) {x | r x (g p)} : set α) ≃ ({x | r x (g p)} ⊕ punit),
    { exact ⟨(set.embedding_of_subset _ _ this).trans
        ((equiv.set.prod _ _).trans (H.prod_congr H)).to_embedding⟩ },
    refine (equiv.set.insert _).trans
      ((equiv.refl _).sum_congr punit_equiv_punit),
    apply @irrefl _ r },
  cases lt_or_ge (card (typein (<) (g p)).succ) omega with qo qo,
  { exact lt_of_lt_of_le (mul_lt_omega qo qo) ol },
  { suffices, {exact lt_of_le_of_lt (IH _ this qo) this},
    rw ← lt_ord, apply (ord_is_limit ol).2,
    rw [mk_def, e], apply typein_lt_type }
end

end using_ordinals

theorem mul_eq_max {a b : cardinal} (ha : omega ≤ a) (hb : omega ≤ b) : a * b = max a b :=
le_antisymm
  (mul_eq_self (le_trans ha (le_max_left a b)) ▸
    mul_le_mul (le_max_left _ _) (le_max_right _ _)) $
max_le
  (by simpa only [mul_one] using mul_le_mul_left a (le_trans (le_of_lt one_lt_omega) hb))
  (by simpa only [one_mul] using mul_le_mul_right b (le_trans (le_of_lt one_lt_omega) ha))

theorem mul_lt_of_lt {a b c : cardinal} (hc : omega ≤ c)
  (h1 : a < c) (h2 : b < c) : a * b < c :=
lt_of_le_of_lt (mul_le_mul (le_max_left a b) (le_max_right a b)) $
(lt_or_le (max a b) omega).elim
  (λ h, lt_of_lt_of_le (mul_lt_omega h h) hc)
  (λ h, by rw mul_eq_self h; exact max_lt h1 h2)

lemma mul_le_max_of_omega_le_left {a b : cardinal} (h : omega ≤ a) : a * b ≤ max a b :=
begin
  convert mul_le_mul (le_max_left a b) (le_max_right a b), rw [mul_eq_self],
  refine le_trans h (le_max_left a b)
end

lemma mul_eq_max_of_omega_le_left {a b : cardinal} (h : omega ≤ a) (h' : b ≠ 0) : a * b = max a b :=
begin
  apply le_antisymm, apply mul_le_max_of_omega_le_left h,
  cases le_or_gt omega b with hb hb, rw [mul_eq_max h hb],
  have : b ≤ a, exact le_trans (le_of_lt hb) h,
  rw [max_eq_left this], convert mul_le_mul_left _ (one_le_iff_ne_zero.mpr h'), rw [mul_one],
end

lemma mul_eq_left {a b : cardinal} (ha : omega ≤ a) (hb : b ≤ a) (hb' : b ≠ 0) : a * b = a :=
by { rw [mul_eq_max_of_omega_le_left ha hb', max_eq_left hb] }

lemma mul_eq_right {a b : cardinal} (hb : omega ≤ b) (ha : a ≤ b) (ha' : a ≠ 0) : a * b = b :=
by { rw [mul_comm, mul_eq_left hb ha ha'] }

lemma le_mul_left {a b : cardinal} (h : b ≠ 0) : a ≤ b * a :=
by { convert mul_le_mul_right _ (one_le_iff_ne_zero.mpr h), rw [one_mul] }

lemma le_mul_right {a b : cardinal} (h : b ≠ 0) : a ≤ a * b :=
by { rw [mul_comm], exact le_mul_left h }

lemma mul_eq_left_iff {a b : cardinal} : a * b = a ↔ ((max omega b ≤ a ∧ b ≠ 0) ∨ b = 1 ∨ a = 0) :=
begin
  rw [max_le_iff], split,
  { intro h,
    cases (le_or_lt omega a) with ha ha,
    { have : a ≠ 0, { rintro rfl, exact not_lt_of_le ha omega_pos },
      left, use ha,
      { rw [← not_lt], intro hb, apply ne_of_gt _ h, refine lt_of_lt_of_le hb (le_mul_left this) },
      { rintro rfl, apply this, rw [_root_.mul_zero] at h, subst h }},
    right, by_cases h2a : a = 0, { right, exact h2a },
    have hb : b ≠ 0, { rintro rfl, apply h2a, rw [mul_zero] at h, subst h },
    left, rw [← h, mul_lt_omega_iff, lt_omega, lt_omega] at ha,
    rcases ha with rfl|rfl|⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩, contradiction, contradiction,
    rw [← ne] at h2a, rw [← one_le_iff_ne_zero] at h2a hb, norm_cast at h2a hb h ⊢,
    apply le_antisymm _ hb, rw [← not_lt], intro h2b,
    apply ne_of_gt _ h, rw [gt], conv_lhs { rw [← mul_one n] },
    rwa [mul_lt_mul_left], apply nat.lt_of_succ_le h2a },
  { rintro (⟨⟨ha, hab⟩, hb⟩|rfl|rfl),
    { rw [mul_eq_max_of_omega_le_left ha hb, max_eq_left hab] },
    all_goals {simp}}
end

/- properties of add -/

theorem add_eq_self {c : cardinal} (h : omega ≤ c) : c + c = c :=
le_antisymm
  (by simpa only [nat.cast_bit0, nat.cast_one, mul_eq_self h, two_mul] using
     mul_le_mul_right c (le_trans (le_of_lt $ nat_lt_omega 2) h))
  (le_add_left c c)

theorem add_eq_max {a b : cardinal} (ha : omega ≤ a) : a + b = max a b :=
le_antisymm
  (add_eq_self (le_trans ha (le_max_left a b)) ▸
    add_le_add (le_max_left _ _) (le_max_right _ _)) $
max_le (le_add_right _ _) (le_add_left _ _)

theorem add_lt_of_lt {a b c : cardinal} (hc : omega ≤ c)
  (h1 : a < c) (h2 : b < c) : a + b < c :=
lt_of_le_of_lt (add_le_add (le_max_left a b) (le_max_right a b)) $
(lt_or_le (max a b) omega).elim
  (λ h, lt_of_lt_of_le (add_lt_omega h h) hc)
  (λ h, by rw add_eq_self h; exact max_lt h1 h2)

lemma eq_of_add_eq_of_omega_le {a b c : cardinal} (h : a + b = c) (ha : a < c) (hc : omega ≤ c) :
  b = c :=
begin
  apply le_antisymm,
  { rw [← h], apply cardinal.le_add_left },
  rw[← not_lt], intro hb,
  have : a + b < c := add_lt_of_lt hc ha hb,
  simpa [h, lt_irrefl] using this
end

lemma add_eq_left {a b : cardinal} (ha : omega ≤ a) (hb : b ≤ a) : a + b = a :=
by { rw [add_eq_max ha, max_eq_left hb] }

lemma add_eq_right {a b : cardinal} (hb : omega ≤ b) (ha : a ≤ b) : a + b = b :=
by { rw [add_comm, add_eq_left hb ha] }

lemma add_eq_left_iff {a b : cardinal} : a + b = a ↔ (max omega b ≤ a ∨ b = 0) :=
begin
  rw [max_le_iff], split,
  { intro h, cases (le_or_lt omega a) with ha ha,
    { left, use ha, rw [← not_lt], intro hb, apply ne_of_gt _ h,
      exact lt_of_lt_of_le hb (le_add_left b a) },
    right, rw [← h, add_lt_omega_iff, lt_omega, lt_omega] at ha,
    rcases ha with ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩, norm_cast at h ⊢,
    rw [← add_right_inj, h, add_zero] },
  { rintro (⟨h1, h2⟩|h3), rw [add_eq_max h1, max_eq_left h2], rw [h3, add_zero] }
end

lemma add_eq_right_iff {a b : cardinal} : a + b = b ↔ (max omega a ≤ b ∨ a = 0) :=
by { rw [add_comm, add_eq_left_iff] }

lemma add_one_eq {a : cardinal} (ha : omega ≤ a) : a + 1 = a :=
have 1 ≤ a, from le_trans (le_of_lt one_lt_omega) ha,
add_eq_left ha this

protected lemma eq_of_add_eq_add_left {a b c : cardinal} (h : a + b = a + c) (ha : a < omega) :
  b = c :=
begin
  cases le_or_lt omega b with hb hb,
  { have : a < b := lt_of_lt_of_le ha hb,
    rw [add_eq_right hb (le_of_lt this), eq_comm] at h,
    rw [eq_of_add_eq_of_omega_le h this hb] },
  { have hc : c < omega,
    { rw [← not_le], intro hc,
      apply lt_irrefl omega, apply lt_of_le_of_lt (le_trans hc (le_add_left _ a)),
      rw [← h], apply add_lt_omega ha hb },
    rw [lt_omega] at *,
    rcases ha with ⟨n, rfl⟩, rcases hb with ⟨m, rfl⟩, rcases hc with ⟨k, rfl⟩,
    norm_cast at h ⊢, apply add_left_cancel h }
end

protected lemma eq_of_add_eq_add_right {a b c : cardinal} (h : a + b = c + b) (hb : b < omega) :
  a = c :=
by { rw [add_comm a b, add_comm c b] at h, exact cardinal.eq_of_add_eq_add_left h hb }

/- properties about power -/

theorem pow_le {κ μ : cardinal.{u}} (H1 : omega ≤ κ) (H2 : μ < omega) : κ ^ μ ≤ κ :=
let ⟨n, H3⟩ := lt_omega.1 H2 in
H3.symm ▸ (quotient.induction_on κ (λ α H1, nat.rec_on n
  (le_of_lt $ lt_of_lt_of_le (by rw [nat.cast_zero, power_zero];
    from one_lt_omega) H1)
  (λ n ih, trans_rel_left _
    (by rw [nat.cast_succ, power_add, power_one];
      from mul_le_mul_right _ ih)
    (mul_eq_self H1))) H1)

lemma power_self_eq {c : cardinal} (h : omega ≤ c) : c ^ c = 2 ^ c :=
begin
  apply le_antisymm,
  { apply le_trans (power_le_power_right $ le_of_lt $ cantor c), rw [power_mul, mul_eq_self h] },
  { convert power_le_power_right (le_trans (le_of_lt $ nat_lt_omega 2) h), apply nat.cast_two.symm }
end

lemma power_nat_le {c : cardinal.{u}} {n : ℕ} (h  : omega ≤ c) : c ^ (n : cardinal.{u}) ≤ c :=
pow_le h (nat_lt_omega n)

lemma powerlt_omega {c : cardinal} (h : omega ≤ c) : c ^< omega = c :=
begin
  apply le_antisymm,
  { rw [powerlt_le], intro c', rw [lt_omega], rintro ⟨n, rfl⟩, apply power_nat_le h },
  convert le_powerlt one_lt_omega, rw [power_one]
end
lemma powerlt_omega_le (c : cardinal) : c ^< omega ≤ max c omega :=
begin
  cases le_or_gt omega c,
  { rw [powerlt_omega h], apply le_max_left },
  rw [powerlt_le], intros c' hc',
  refine le_trans (le_of_lt $ power_lt_omega h hc') (le_max_right _ _)
end

/- compute cardinality of various types -/

theorem mk_list_eq_mk {α : Type u} (H1 : omega ≤ mk α) : mk (list α) = mk α :=
eq.symm $ le_antisymm ⟨⟨λ x, [x], λ x y H, (list.cons.inj H).1⟩⟩ $
calc  mk (list α)
    = sum (λ n : ℕ, mk α ^ (n : cardinal.{u})) : mk_list_eq_sum_pow α
... ≤ sum (λ n : ℕ, mk α) : sum_le_sum _ _ $ λ n, pow_le H1 $ nat_lt_omega n
... = sum (λ n : ulift.{u} ℕ, mk α) : quotient.sound
  ⟨@sigma_congr_left _ _ (λ _, quotient.out (mk α)) equiv.ulift.symm⟩
... = omega * mk α : sum_const _ _
... = max (omega) (mk α) : mul_eq_max (le_refl _) H1
... = mk α : max_eq_right H1

lemma mk_bounded_set_le_of_omega_le (α : Type u) (c : cardinal) (hα : omega ≤ mk α) :
  mk {t : set α // mk t ≤ c} ≤ mk α ^ c :=
begin
  refine le_trans _ (by rw [←add_one_eq hα]), refine quotient.induction_on c _, clear c, intro β,
  fapply mk_le_of_surjective,
  { intro f, use sum.inl ⁻¹' range f,
    refine le_trans (mk_preimage_of_injective _ _ (λ x y, sum.inl.inj)) _,
    apply mk_range_le },
  rintro ⟨s, ⟨g⟩⟩,
  use λ y, if h : ∃(x : s), g x = y then sum.inl (classical.some h).val else sum.inr ⟨⟩,
  apply subtype.eq, ext,
  split,
  { rintro ⟨y, h⟩, dsimp only at h, by_cases h' : ∃ (z : s), g z = y,
    { rw [dif_pos h'] at h, cases sum.inl.inj h, exact (classical.some h').2 },
    { rw [dif_neg h'] at h, cases h }},
  { intro h, have : ∃(z : s), g z = g ⟨x, h⟩, exact ⟨⟨x, h⟩, rfl⟩,
    use g ⟨x, h⟩, dsimp only, rw [dif_pos this], congr',
    suffices : classical.some this = ⟨x, h⟩, exact congr_arg subtype.val this,
    apply g.2, exact classical.some_spec this }
end

lemma mk_bounded_set_le (α : Type u) (c : cardinal) :
  mk {t : set α // mk t ≤ c} ≤ max (mk α) omega ^ c :=
begin
  transitivity mk {t : set (ulift.{u} nat ⊕ α) // mk t ≤ c},
  { refine ⟨embedding.subtype_map _ _⟩, apply embedding.image,
    use sum.inr, apply sum.inr.inj, intros s hs, exact le_trans mk_image_le hs },
  refine le_trans
    (mk_bounded_set_le_of_omega_le (ulift.{u} nat ⊕ α) c (le_add_right omega (mk α))) _,
  rw [max_comm, ←add_eq_max]; refl
end

lemma mk_bounded_subset_le {α : Type u} (s : set α) (c : cardinal.{u}) :
  mk {t : set α // t ⊆ s ∧ mk t ≤ c} ≤ max (mk s) omega ^ c :=
begin
  refine le_trans _ (mk_bounded_set_le s c),
  refine ⟨embedding.cod_restrict _ _ _⟩,
  use λ t, coe ⁻¹' t.1,
  { rintros ⟨t, ht1, ht2⟩ ⟨t', h1t', h2t'⟩ h, apply subtype.eq, dsimp only at h ⊢,
    refine (preimage_eq_preimage' _ _).1 h; rw [subtype.range_coe]; assumption },
  rintro ⟨t, h1t, h2t⟩, exact le_trans (mk_preimage_of_injective _ _ subtype.val_injective) h2t
end

/- compl -/

lemma mk_compl_of_omega_le {α : Type*} (s : set α) (h : omega ≤ #α) (h2 : #s < #α) :
  #(sᶜ : set α) = #α :=
by { refine eq_of_add_eq_of_omega_le _ h2 h, exact mk_sum_compl s }

lemma mk_compl_finset_of_omega_le {α : Type*} (s : finset α) (h : omega ≤ #α) :
  #((↑s)ᶜ : set α) = #α :=
by { apply mk_compl_of_omega_le _ h, exact lt_of_lt_of_le (finset_card_lt_omega s) h }

lemma mk_compl_eq_mk_compl_infinite {α : Type*} {s t : set α} (h : omega ≤ #α) (hs : #s < #α)
  (ht : #t < #α) : #(sᶜ : set α) = #(tᶜ : set α) :=
by { rw [mk_compl_of_omega_le s h hs, mk_compl_of_omega_le t h ht] }

lemma mk_compl_eq_mk_compl_finite_lift {α : Type u} {β : Type v} {s : set α} {t : set β}
  (hα : #α < omega) (h1 : lift.{u (max v w)} (#α) = lift.{v (max u w)} (#β))
  (h2 : lift.{u (max v w)} (#s) = lift.{v (max u w)} (#t)) :
  lift.{u (max v w)} (#(sᶜ : set α)) = lift.{v (max u w)} (#(tᶜ : set β)) :=
begin
  have hα' := hα, have h1' := h1,
  rw [← mk_sum_compl s, ← mk_sum_compl t] at h1,
  rw [← mk_sum_compl s, add_lt_omega_iff] at hα,
  lift #s to ℕ using hα.1 with n hn,
  lift #(sᶜ : set α) to ℕ using hα.2 with m hm,
  have : #(tᶜ : set β) < omega,
  { refine lt_of_le_of_lt (mk_subtype_le _) _,
    rw [← lift_lt, lift_omega, ← h1', ← lift_omega.{u (max v w)}, lift_lt], exact hα' },
  lift #(tᶜ : set β) to ℕ using this with k hk,
  simp [nat_eq_lift_eq_iff] at h2, rw [nat_eq_lift_eq_iff.{v (max u w)}] at h2,
  simp [h2.symm] at h1 ⊢, norm_cast at h1, simp at h1, exact h1
end

lemma mk_compl_eq_mk_compl_finite {α β : Type u} {s : set α} {t : set β}
  (hα : #α < omega) (h1 : #α = #β) (h : #s = #t) : #(sᶜ : set α) = #(tᶜ : set β) :=
by { rw [← lift_inj], apply mk_compl_eq_mk_compl_finite_lift hα; rw [lift_inj]; assumption }

lemma mk_compl_eq_mk_compl_finite_same {α : Type*} {s t : set α} (hα : #α < omega)
  (h : #s = #t) : #(sᶜ : set α) = #(tᶜ : set α) :=
mk_compl_eq_mk_compl_finite hα rfl h

/- extend an injection to an equiv -/

theorem extend_function {α β : Type*} {s : set α} (f : s ↪ β)
  (h : nonempty ((sᶜ : set α) ≃ ((range f)ᶜ : set β))) :
  ∃ (g : α ≃ β), ∀ x : s, g x = f x :=
begin
  intros, have := h, cases this with g,
  let h : α ≃ β := (set.sum_compl (s : set α)).symm.trans
    ((sum_congr (equiv.set.range f f.2) g).trans
    (set.sum_compl (range f))),
  refine ⟨h, _⟩, rintro ⟨x, hx⟩, simp [set.sum_compl_symm_apply_of_mem, hx]
end

theorem extend_function_finite {α β : Type*} {s : set α} (f : s ↪ β)
  (hs : #α < omega) (h : nonempty (α ≃ β)) : ∃ (g : α ≃ β), ∀ x : s, g x = f x :=
begin
  apply extend_function f,
  have := h, cases this with g,
  rw [← lift_mk_eq] at h,
  rw [←lift_mk_eq, mk_compl_eq_mk_compl_finite_lift hs h],
  rw [mk_range_eq_lift], exact f.2
end

theorem extend_function_of_lt {α β : Type*} {s : set α} (f : s ↪ β) (hs : #s < #α)
  (h : nonempty (α ≃ β)) : ∃ (g : α ≃ β), ∀ x : s, g x = f x :=
begin
  cases (le_or_lt omega (#α)) with hα hα,
  { apply extend_function f, have := h, cases this with g, rw [← lift_mk_eq] at h,
    cases cardinal.eq.mp (mk_compl_of_omega_le s hα hs) with g2,
    cases cardinal.eq.mp (mk_compl_of_omega_le (range f) _ _) with g3,
    { constructor, exact g2.trans (g.trans g3.symm) },
    { rw [← lift_le, ← h], refine le_trans _ (lift_le.mpr hα), simp },
    rwa [← lift_lt, ← h, mk_range_eq_lift, lift_lt], exact f.2 },
  { exact extend_function_finite f hα h }
end

end cardinal
