/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import order.filter.basic

/-!
# Minimum and maximum w.r.t. a filter and on a aet

## Main Definitions

This file defines six predicates of the form `is_A_B`, where `A` is `min`, `max`, or `extr`,
and `B` is `filter` or `on`.

* `is_min_filter f l a` means that `f a ≤ f x` in some `l`-neighborhood of `a`;
* `is_max_filter f l a` means that `f x ≤ f a` in some `l`-neighborhood of `a`;
* `is_extr_filter f l a` means `is_min_filter f l a` or `is_max_filter f l a`.

Similar predicates with `_on` suffix are particular cases for `l = 𝓟 s`.

## Main statements

### Change of the filter (set) argument

* `is_*_filter.filter_mono` : replace the filter with a smaller one;
* `is_*_filter.filter_inf` : replace a filter `l` with `l ⊓ l'`;
* `is_*_on.on_subset` : restrict to a smaller set;
* `is_*_on.inter` : replace a set `s` wtih `s ∩ t`.

### Composition

* `is_*_*.comp_mono` : if `x` is an extremum for `f` and `g` is a monotone function,
  then `x` is an extremum for `g ∘ f`;
* `is_*_*.comp_antitone` : similarly for the case of antitone `g`;
* `is_*_*.bicomp_mono` : if `x` is an extremum of the same type for `f` and `g`
  and a binary operation `op` is monotone in both arguments, then `x` is an extremum
  of the same type for `λ x, op (f x) (g x)`.
* `is_*_filter.comp_tendsto` : if `g x` is an extremum for `f` w.r.t. `l'` and `tendsto g l l'`,
  then `x` is an extremum for `f ∘ g` w.r.t. `l`.
* `is_*_on.on_preimage` : if `g x` is an extremum for `f` on `s`, then `x` is an extremum
  for `f ∘ g` on `g ⁻¹' s`.

### Algebraic operations

* `is_*_*.add` : if `x` is an extremum of the same type for two functions,
  then it is an extremum of the same type for their sum;
* `is_*_*.neg` : if `x` is an extremum for `f`, then it is an extremum
  of the opposite type for `-f`;
* `is_*_*.sub` : if `x` is an a minimum for `f` and a maximum for `g`,
  then it is a minimum for `f - g` and a maximum for `g - f`;
* `is_*_*.max`, `is_*_*.min`, `is_*_*.sup`, `is_*_*.inf` : similarly for `is_*_*.add`
  for pointwise `max`, `min`, `sup`, `inf`, respectively.


### Miscellaneous definitions

* `is_*_*_const` : any point is both a minimum and maximum for a constant function;
* `is_min/max_*.is_ext` : any minimum/maximum point is an extremum;
* `is_*_*.dual`, `is_*_*.undual`: conversion between codomains `α` and `dual α`;

## Missing features (TODO)

* Multiplication and division;
* `is_*_*.bicompl` : if `x` is a minimum for `f`, `y` is a minimum for `g`, and `op` is a monotone
  binary operation, then `(x, y)` is a minimum for `uncurry (bicompl op f g)`. From this point
  of view, `is_*_*.bicomp` is a composition
* It would be nice to have a tactic that specializes `comp_(anti)mono` or `bicomp_mono`
  based on a proof of monotonicity of a given (binary) function. The tactic should maintain a `meta`
  list of known (anti)monotone (binary) functions with their names, as well as a list of special
  types of filters, and define the missing lemmas once one of these two lists grows.
-/

universes u v w x

variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open set filter
open_locale filter

section preorder

variables [preorder β] [preorder γ]

variables (f : α → β) (s : set α) (l : filter α) (a : α)

/-! ### Definitions -/

/-- `is_min_filter f l a` means that `f a ≤ f x` in some `l`-neighborhood of `a` -/
def is_min_filter : Prop := ∀ᶠ x in l, f a ≤ f x

/-- `is_max_filter f l a` means that `f x ≤ f a` in some `l`-neighborhood of `a` -/
def is_max_filter : Prop := ∀ᶠ x in l, f x ≤ f a

/-- `is_extr_filter f l a` means `is_min_filter f l a` or `is_max_filter f l a` -/
def is_extr_filter : Prop := is_min_filter f l a ∨ is_max_filter f l a

/-- `is_min_on f s a` means that `f a ≤ f x` for all `x ∈ a`. Note that we do not assume `a ∈ s`. -/
def is_min_on := is_min_filter f (𝓟 s) a

/-- `is_max_on f s a` means that `f x ≤ f a` for all `x ∈ a`. Note that we do not assume `a ∈ s`. -/
def is_max_on := is_max_filter f (𝓟 s) a

/-- `is_extr_on f s a` means `is_min_on f s a` or `is_max_on f s a` -/
def is_extr_on : Prop := is_extr_filter f (𝓟 s) a

variables {f s a l} {t : set α} {l' : filter α}

lemma is_extr_on.elim {p : Prop} :
  is_extr_on f s a → (is_min_on f s a → p) → (is_max_on f s a → p) → p :=
or.elim

lemma is_min_on_iff : is_min_on f s a ↔ ∀ x ∈ s, f a ≤ f x := iff.rfl

lemma is_max_on_iff : is_max_on f s a ↔ ∀ x ∈ s, f x ≤ f a := iff.rfl

lemma is_min_on_univ_iff : is_min_on f univ a ↔ ∀ x, f a ≤ f x :=
univ_subset_iff.trans eq_univ_iff_forall

lemma is_max_on_univ_iff : is_max_on f univ a ↔ ∀ x, f x ≤ f a :=
univ_subset_iff.trans eq_univ_iff_forall

lemma is_min_filter.tendsto_principal_Ici (h : is_min_filter f l a) :
  tendsto f l (𝓟 $ Ici (f a)) :=
tendsto_principal.2 h

lemma is_max_filter.tendsto_principal_Iic (h : is_max_filter f l a) :
  tendsto f l (𝓟 $ Iic (f a)) :=
tendsto_principal.2 h

/-! ### Conversion to `is_extr_*` -/

lemma is_min_filter.is_extr : is_min_filter f l a → is_extr_filter f l a := or.inl

lemma is_max_filter.is_extr : is_max_filter f l a → is_extr_filter f l a := or.inr

lemma is_min_on.is_extr (h : is_min_on f s a) : is_extr_on f s a := h.is_extr

lemma is_max_on.is_extr (h : is_max_on f s a) : is_extr_on f s a := h.is_extr

/-! ### Constant function -/

lemma is_min_filter_const {b : β} : is_min_filter (λ _, b) l a :=
univ_mem' $ λ _, le_refl _

lemma is_max_filter_const {b : β} : is_max_filter (λ _, b) l a :=
univ_mem' $ λ _, le_refl _

lemma is_extr_filter_const {b : β} : is_extr_filter (λ _, b) l a := is_min_filter_const.is_extr

lemma is_min_on_const {b : β} : is_min_on (λ _, b) s a := is_min_filter_const

lemma is_max_on_const {b : β} : is_max_on (λ _, b) s a := is_max_filter_const

lemma is_extr_on_const {b : β} : is_extr_on (λ _, b) s a := is_extr_filter_const

/-! ### Order dual -/

lemma is_min_filter_dual_iff : @is_min_filter α (order_dual β) _ f l a ↔ is_max_filter f l a :=
iff.rfl

lemma is_max_filter_dual_iff : @is_max_filter α (order_dual β) _ f l a ↔ is_min_filter f l a :=
iff.rfl

lemma is_extr_filter_dual_iff : @is_extr_filter α (order_dual β) _ f l a ↔ is_extr_filter f l a :=
or_comm _ _

alias is_min_filter_dual_iff ↔ is_min_filter.undual is_max_filter.dual
alias is_max_filter_dual_iff ↔ is_max_filter.undual is_min_filter.dual
alias is_extr_filter_dual_iff ↔ is_extr_filter.undual is_extr_filter.dual

lemma is_min_on_dual_iff : @is_min_on α (order_dual β) _ f s a ↔ is_max_on f s a := iff.rfl
lemma is_max_on_dual_iff : @is_max_on α (order_dual β) _ f s a ↔ is_min_on f s a := iff.rfl
lemma is_extr_on_dual_iff : @is_extr_on α (order_dual β) _ f s a ↔ is_extr_on f s a := or_comm _ _

alias is_min_on_dual_iff ↔ is_min_on.undual is_max_on.dual
alias is_max_on_dual_iff ↔ is_max_on.undual is_min_on.dual
alias is_extr_on_dual_iff ↔ is_extr_on.undual is_extr_on.dual

/-! ### Operations on the filter/set -/

lemma is_min_filter.filter_mono (h : is_min_filter f l a) (hl : l' ≤ l) :
  is_min_filter f l' a := hl h

lemma is_max_filter.filter_mono (h : is_max_filter f l a) (hl : l' ≤ l) :
  is_max_filter f l' a := hl h

lemma is_extr_filter.filter_mono (h : is_extr_filter f l a) (hl : l' ≤ l) :
  is_extr_filter f l' a :=
h.elim (λ h, (h.filter_mono hl).is_extr) (λ h, (h.filter_mono hl).is_extr)

lemma is_min_filter.filter_inf (h : is_min_filter f l a) (l') : is_min_filter f (l ⊓ l') a :=
h.filter_mono inf_le_left

lemma is_max_filter.filter_inf (h : is_max_filter f l a) (l') : is_max_filter f (l ⊓ l') a :=
h.filter_mono inf_le_left

lemma is_extr_filter.filter_inf (h : is_extr_filter f l a) (l') : is_extr_filter f (l ⊓ l') a :=
h.filter_mono inf_le_left

lemma is_min_on.on_subset (hf : is_min_on f t a) (h : s ⊆ t) : is_min_on f s a :=
hf.filter_mono $ principal_mono.2 h

lemma is_max_on.on_subset (hf : is_max_on f t a) (h : s ⊆ t) : is_max_on f s a :=
hf.filter_mono $ principal_mono.2 h

lemma is_extr_on.on_subset (hf : is_extr_on f t a) (h : s ⊆ t) : is_extr_on f s a :=
hf.filter_mono $ principal_mono.2 h

lemma is_min_on.inter (hf : is_min_on f s a) (t) : is_min_on f (s ∩ t) a :=
hf.on_subset (inter_subset_left s t)

lemma is_max_on.inter (hf : is_max_on f s a) (t) : is_max_on f (s ∩ t) a :=
hf.on_subset (inter_subset_left s t)

lemma is_extr_on.inter (hf : is_extr_on f s a) (t) : is_extr_on f (s ∩ t) a :=
hf.on_subset (inter_subset_left s t)

/-! ### Composition with (anti)monotone functions -/

lemma is_min_filter.comp_mono (hf : is_min_filter f l a) {g : β → γ} (hg : monotone g) :
  is_min_filter (g ∘ f) l a :=
mem_of_superset hf $ λ x hx, hg hx

lemma is_max_filter.comp_mono (hf : is_max_filter f l a) {g : β → γ} (hg : monotone g) :
  is_max_filter (g ∘ f) l a :=
mem_of_superset hf $ λ x hx, hg hx

lemma is_extr_filter.comp_mono (hf : is_extr_filter f l a) {g : β → γ} (hg : monotone g) :
  is_extr_filter (g ∘ f) l a :=
hf.elim (λ hf, (hf.comp_mono hg).is_extr)  (λ hf, (hf.comp_mono hg).is_extr)

lemma is_min_filter.comp_antitone (hf : is_min_filter f l a) {g : β → γ}
  (hg : antitone g) :
  is_max_filter (g ∘ f) l a :=
hf.dual.comp_mono (λ x y h, hg h)

lemma is_max_filter.comp_antitone (hf : is_max_filter f l a) {g : β → γ}
  (hg : antitone g) :
  is_min_filter (g ∘ f) l a :=
hf.dual.comp_mono (λ x y h, hg h)

lemma is_extr_filter.comp_antitone (hf : is_extr_filter f l a) {g : β → γ}
  (hg : antitone g) :
  is_extr_filter (g ∘ f) l a :=
hf.dual.comp_mono (λ x y h, hg h)

lemma is_min_on.comp_mono (hf : is_min_on f s a) {g : β → γ} (hg : monotone g) :
  is_min_on (g ∘ f) s a :=
hf.comp_mono hg

lemma is_max_on.comp_mono (hf : is_max_on f s a) {g : β → γ} (hg : monotone g) :
  is_max_on (g ∘ f) s a :=
hf.comp_mono hg

lemma is_extr_on.comp_mono (hf : is_extr_on f s a) {g : β → γ} (hg : monotone g) :
  is_extr_on (g ∘ f) s a :=
hf.comp_mono hg

lemma is_min_on.comp_antitone (hf : is_min_on f s a) {g : β → γ}
  (hg : antitone g) :
  is_max_on (g ∘ f) s a :=
hf.comp_antitone hg

lemma is_max_on.comp_antitone (hf : is_max_on f s a) {g : β → γ}
  (hg : antitone g) :
  is_min_on (g ∘ f) s a :=
hf.comp_antitone hg

lemma is_extr_on.comp_antitone (hf : is_extr_on f s a) {g : β → γ}
  (hg : antitone g) :
  is_extr_on (g ∘ f) s a :=
hf.comp_antitone hg

lemma is_min_filter.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_min_filter f l a) {g : α → γ} (hg : is_min_filter g l a) :
  is_min_filter (λ x, op (f x) (g x)) l a :=
mem_of_superset (inter_mem hf hg) $ λ x ⟨hfx, hgx⟩, hop hfx hgx

lemma is_max_filter.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_max_filter f l a) {g : α → γ} (hg : is_max_filter g l a) :
  is_max_filter (λ x, op (f x) (g x)) l a :=
mem_of_superset (inter_mem hf hg) $ λ x ⟨hfx, hgx⟩, hop hfx hgx

-- No `extr` version because we need `hf` and `hg` to be of the same kind

lemma is_min_on.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_min_on f s a) {g : α → γ} (hg : is_min_on g s a) :
  is_min_on (λ x, op (f x) (g x)) s a :=
hf.bicomp_mono hop hg

lemma is_max_on.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_max_on f s a) {g : α → γ} (hg : is_max_on g s a) :
  is_max_on (λ x, op (f x) (g x)) s a :=
hf.bicomp_mono hop hg

/-! ### Composition with `tendsto` -/

lemma is_min_filter.comp_tendsto {g : δ → α} {l' : filter δ} {b : δ} (hf : is_min_filter f l (g b))
  (hg : tendsto g l' l) :
  is_min_filter (f ∘ g) l' b :=
hg hf

lemma is_max_filter.comp_tendsto {g : δ → α} {l' : filter δ} {b : δ} (hf : is_max_filter f l (g b))
  (hg : tendsto g l' l) :
  is_max_filter (f ∘ g) l' b :=
hg hf

lemma is_extr_filter.comp_tendsto {g : δ → α} {l' : filter δ} {b : δ}
  (hf : is_extr_filter f l (g b)) (hg : tendsto g l' l) :
  is_extr_filter (f ∘ g) l' b :=
hf.elim (λ hf, (hf.comp_tendsto hg).is_extr) (λ hf, (hf.comp_tendsto hg).is_extr)

lemma is_min_on.on_preimage (g : δ → α) {b : δ} (hf : is_min_on f s (g b)) :
  is_min_on (f ∘ g) (g ⁻¹' s) b :=
hf.comp_tendsto (tendsto_principal_principal.mpr $ subset.refl _)

lemma is_max_on.on_preimage (g : δ → α) {b : δ} (hf : is_max_on f s (g b)) :
  is_max_on (f ∘ g) (g ⁻¹' s) b :=
hf.comp_tendsto (tendsto_principal_principal.mpr $ subset.refl _)

lemma is_extr_on.on_preimage (g : δ → α) {b : δ} (hf : is_extr_on f s (g b)) :
  is_extr_on (f ∘ g) (g ⁻¹' s) b :=
hf.elim (λ hf, (hf.on_preimage g).is_extr) (λ hf, (hf.on_preimage g).is_extr)

end preorder

/-! ### Pointwise addition -/
section ordered_add_comm_monoid

variables [ordered_add_comm_monoid β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_min_filter.add (hf : is_min_filter f l a) (hg : is_min_filter g l a) :
  is_min_filter (λ x, f x + g x) l a :=
show is_min_filter (λ x, f x + g x) l a,
from hf.bicomp_mono (λ x x' hx y y' hy, add_le_add hx hy) hg

lemma is_max_filter.add (hf : is_max_filter f l a) (hg : is_max_filter g l a) :
  is_max_filter (λ x, f x + g x) l a :=
show is_max_filter (λ x, f x + g x) l a,
from hf.bicomp_mono (λ x x' hx y y' hy, add_le_add hx hy) hg

lemma is_min_on.add (hf : is_min_on f s a) (hg : is_min_on g s a) :
  is_min_on (λ x, f x + g x) s a :=
hf.add hg

lemma is_max_on.add (hf : is_max_on f s a) (hg : is_max_on g s a) :
  is_max_on (λ x, f x + g x) s a :=
hf.add hg

end ordered_add_comm_monoid

/-! ### Pointwise negation and subtraction -/

section ordered_add_comm_group

variables [ordered_add_comm_group β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_min_filter.neg (hf : is_min_filter f l a) : is_max_filter (λ x, -f x) l a :=
hf.comp_antitone (λ x y hx, neg_le_neg hx)

lemma is_max_filter.neg (hf : is_max_filter f l a) : is_min_filter (λ x, -f x) l a :=
hf.comp_antitone (λ x y hx, neg_le_neg hx)

lemma is_extr_filter.neg (hf : is_extr_filter f l a) : is_extr_filter (λ x, -f x) l a :=
hf.elim (λ hf, hf.neg.is_extr) (λ hf, hf.neg.is_extr)

lemma is_min_on.neg (hf : is_min_on f s a) : is_max_on (λ x, -f x) s a :=
hf.comp_antitone (λ x y hx, neg_le_neg hx)

lemma is_max_on.neg (hf : is_max_on f s a) : is_min_on (λ x, -f x) s a :=
hf.comp_antitone (λ x y hx, neg_le_neg hx)

lemma is_extr_on.neg (hf : is_extr_on f s a) : is_extr_on (λ x, -f x) s a :=
hf.elim (λ hf, hf.neg.is_extr) (λ hf, hf.neg.is_extr)

lemma is_min_filter.sub (hf : is_min_filter f l a) (hg : is_max_filter g l a) :
  is_min_filter (λ x, f x - g x) l a :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma is_max_filter.sub (hf : is_max_filter f l a) (hg : is_min_filter g l a) :
  is_max_filter (λ x, f x - g x) l a :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma is_min_on.sub (hf : is_min_on f s a) (hg : is_max_on g s a) :
  is_min_on (λ x, f x - g x) s a :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma is_max_on.sub (hf : is_max_on f s a) (hg : is_min_on g s a) :
  is_max_on (λ x, f x - g x) s a :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

end ordered_add_comm_group

/-! ### Pointwise `sup`/`inf` -/

section semilattice_sup

variables [semilattice_sup β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_min_filter.sup (hf : is_min_filter f l a) (hg : is_min_filter g l a) :
  is_min_filter (λ x, f x ⊔ g x) l a :=
show is_min_filter (λ x, f x ⊔ g x) l a,
from hf.bicomp_mono (λ x x' hx y y' hy, sup_le_sup hx hy) hg

lemma is_max_filter.sup (hf : is_max_filter f l a) (hg : is_max_filter g l a) :
  is_max_filter (λ x, f x ⊔ g x) l a :=
show is_max_filter (λ x, f x ⊔ g x) l a,
from hf.bicomp_mono (λ x x' hx y y' hy, sup_le_sup hx hy) hg

lemma is_min_on.sup (hf : is_min_on f s a) (hg : is_min_on g s a) :
  is_min_on (λ x, f x ⊔ g x) s a :=
hf.sup hg

lemma is_max_on.sup (hf : is_max_on f s a) (hg : is_max_on g s a) :
  is_max_on (λ x, f x ⊔ g x) s a :=
hf.sup hg

end semilattice_sup

section semilattice_inf

variables [semilattice_inf β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_min_filter.inf (hf : is_min_filter f l a) (hg : is_min_filter g l a) :
  is_min_filter (λ x, f x ⊓ g x) l a :=
show is_min_filter (λ x, f x ⊓ g x) l a,
from hf.bicomp_mono (λ x x' hx y y' hy, inf_le_inf hx hy) hg

lemma is_max_filter.inf (hf : is_max_filter f l a) (hg : is_max_filter g l a) :
  is_max_filter (λ x, f x ⊓ g x) l a :=
show is_max_filter (λ x, f x ⊓ g x) l a,
from hf.bicomp_mono (λ x x' hx y y' hy, inf_le_inf hx hy) hg

lemma is_min_on.inf (hf : is_min_on f s a) (hg : is_min_on g s a) :
  is_min_on (λ x, f x ⊓ g x) s a :=
hf.inf hg

lemma is_max_on.inf (hf : is_max_on f s a) (hg : is_max_on g s a) :
  is_max_on (λ x, f x ⊓ g x) s a :=
hf.inf hg

end semilattice_inf

/-! ### Pointwise `min`/`max` -/

section linear_order

variables [linear_order β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_min_filter.min (hf : is_min_filter f l a) (hg : is_min_filter g l a) :
  is_min_filter (λ x, min (f x) (g x)) l a :=
show is_min_filter (λ x, min (f x) (g x)) l a,
from hf.bicomp_mono (λ x x' hx y y' hy, min_le_min hx hy) hg

lemma is_max_filter.min (hf : is_max_filter f l a) (hg : is_max_filter g l a) :
  is_max_filter (λ x, min (f x) (g x)) l a :=
show is_max_filter (λ x, min (f x) (g x)) l a,
from hf.bicomp_mono (λ x x' hx y y' hy, min_le_min hx hy) hg

lemma is_min_on.min (hf : is_min_on f s a) (hg : is_min_on g s a) :
  is_min_on (λ x, min (f x) (g x)) s a :=
hf.min hg

lemma is_max_on.min (hf : is_max_on f s a) (hg : is_max_on g s a) :
  is_max_on (λ x, min (f x) (g x)) s a :=
hf.min hg

lemma is_min_filter.max (hf : is_min_filter f l a) (hg : is_min_filter g l a) :
  is_min_filter (λ x, max (f x) (g x)) l a :=
show is_min_filter (λ x, max (f x) (g x)) l a,
from hf.bicomp_mono (λ x x' hx y y' hy, max_le_max hx hy) hg

lemma is_max_filter.max (hf : is_max_filter f l a) (hg : is_max_filter g l a) :
  is_max_filter (λ x, max (f x) (g x)) l a :=
show is_max_filter (λ x, max (f x) (g x)) l a,
from hf.bicomp_mono (λ x x' hx y y' hy, max_le_max hx hy) hg

lemma is_min_on.max (hf : is_min_on f s a) (hg : is_min_on g s a) :
  is_min_on (λ x, max (f x) (g x)) s a :=
hf.max hg

lemma is_max_on.max (hf : is_max_on f s a) (hg : is_max_on g s a) :
  is_max_on (λ x, max (f x) (g x)) s a :=
hf.max hg

end linear_order

section eventually

/-! ### Relation with `eventually` comparisons of two functions -/

lemma filter.eventually_le.is_max_filter {α β : Type*} [preorder β] {f g : α → β} {a : α}
  {l : filter α} (hle : g ≤ᶠ[l] f) (hfga : f a = g a) (h : is_max_filter f l a) :
  is_max_filter g l a :=
begin
  refine hle.mp (h.mono $ λ x hf hgf, _),
  rw ← hfga,
  exact le_trans hgf hf
end

lemma is_max_filter.congr {α β : Type*} [preorder β] {f g : α → β} {a : α} {l : filter α}
  (h : is_max_filter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) :
  is_max_filter g l a :=
heq.symm.le.is_max_filter hfga h

lemma filter.eventually_eq.is_max_filter_iff {α β : Type*} [preorder β] {f g : α → β} {a : α}
  {l : filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) :
  is_max_filter f l a ↔ is_max_filter g l a :=
⟨λ h, h.congr heq hfga, λ h, h.congr heq.symm hfga.symm⟩

lemma filter.eventually_le.is_min_filter {α β : Type*} [preorder β] {f g : α → β} {a : α}
  {l : filter α} (hle : f ≤ᶠ[l] g) (hfga : f a = g a) (h : is_min_filter f l a) :
  is_min_filter g l a :=
@filter.eventually_le.is_max_filter _ (order_dual β) _ _ _ _ _ hle hfga h

lemma is_min_filter.congr {α β : Type*} [preorder β] {f g : α → β} {a : α} {l : filter α}
  (h : is_min_filter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) :
  is_min_filter g l a :=
heq.le.is_min_filter hfga h

lemma filter.eventually_eq.is_min_filter_iff {α β : Type*} [preorder β] {f g : α → β} {a : α}
  {l : filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) :
  is_min_filter f l a ↔ is_min_filter g l a :=
⟨λ h, h.congr heq hfga, λ h, h.congr heq.symm hfga.symm⟩

lemma is_extr_filter.congr {α β : Type*} [preorder β] {f g : α → β} {a : α} {l : filter α}
  (h : is_extr_filter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) :
  is_extr_filter g l a :=
begin
  rw is_extr_filter at *,
  rwa [← heq.is_max_filter_iff hfga, ← heq.is_min_filter_iff hfga],
end

lemma filter.eventually_eq.is_extr_filter_iff {α β : Type*} [preorder β] {f g : α → β} {a : α}
  {l : filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) :
  is_extr_filter f l a ↔ is_extr_filter g l a :=
⟨λ h, h.congr heq hfga, λ h, h.congr heq.symm hfga.symm⟩

end eventually
