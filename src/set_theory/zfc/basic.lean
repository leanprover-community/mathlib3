/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.set.lattice
import logic.small.basic
import order.well_founded

/-!
# A model of ZFC

In this file, we model Zermelo-Fraenkel set theory (+ Choice) using Lean's underlying type theory.
We do this in four main steps:
* Define pre-sets inductively.
* Define extensional equivalence on pre-sets and give it a `setoid` instance.
* Define ZFC sets by quotienting pre-sets by extensional equivalence.
* Define classes as sets of ZFC sets.
Then the rest is usual set theory.

## The model

* `pSet`: Pre-set. A pre-set is inductively defined by its indexing type and its members, which are
  themselves pre-sets.
* `Set`: ZFC set. Defined as `pSet` quotiented by `pSet.equiv`, the extensional equivalence.
* `Class`: Class. Defined as `set Set`.
* `Set.choice`: Axiom of choice. Proved from Lean's axiom of choice.

## Other definitions

* `arity α n`: `n`-ary function `α → α → ... → α`. Defined inductively.
* `arity.const a n`: `n`-ary constant function equal to `a`.
* `pSet.type`: Underlying type of a pre-set.
* `pSet.func`: Underlying family of pre-sets of a pre-set.
* `pSet.equiv`: Extensional equivalence of pre-sets. Defined inductively.
* `pSet.omega`, `Set.omega`: The von Neumann ordinal `ω` as a `pSet`, as a `Set`.
* `pSet.arity.equiv`: Extensional equivalence of `n`-ary `pSet`-valued functions. Extension of
  `pSet.equiv`.
* `pSet.resp`: Collection of `n`-ary `pSet`-valued functions that respect extensional equivalence.
* `pSet.eval`: Turns a `pSet`-valued function that respect extensional equivalence into a
  `Set`-valued function.
* `classical.all_definable`: All functions are classically definable.
* `Set.is_func` : Predicate that a ZFC set is a subset of `x × y` that can be considered as a ZFC
  function `x → y`. That is, each member of `x` is related by the ZFC set to exactly one member of
  `y`.
* `Set.funs`: ZFC set of ZFC functions `x → y`.
* `Set.hereditarily p x`: Predicate that every set in the transitive closure of `x` has property
  `p`.
* `Class.iota`: Definite description operator.

## Notes

To avoid confusion between the Lean `set` and the ZFC `Set`, docstrings in this file refer to them
respectively as "`set`" and "ZFC set".

## TODO

Prove `Set.map_definable_aux` computably.
-/

universes u v

/-- The type of `n`-ary functions `α → α → ... → α`. -/
def arity (α : Type u) : ℕ → Type u
| 0     := α
| (n+1) := α → arity n

@[simp] theorem arity_zero (α : Type u) : arity α 0 = α := rfl
@[simp] theorem arity_succ (α : Type u) (n : ℕ) : arity α n.succ = (α → arity α n) := rfl

namespace arity

/-- Constant `n`-ary function with value `a`. -/
def const {α : Type u} (a : α) : ∀ n, arity α n
| 0     := a
| (n+1) := λ _, const n

@[simp] theorem const_zero {α : Type u} (a : α) : const a 0 = a := rfl
@[simp] theorem const_succ {α : Type u} (a : α) (n : ℕ) : const a n.succ = λ _, const a n := rfl
theorem const_succ_apply {α : Type u} (a : α) (n : ℕ) (x : α) : const a n.succ x = const a n := rfl

instance arity.inhabited {α n} [inhabited α] : inhabited (arity α n) := ⟨const default _⟩

end arity

/-- The type of pre-sets in universe `u`. A pre-set
  is a family of pre-sets indexed by a type in `Type u`.
  The ZFC universe is defined as a quotient of this
  to ensure extensionality. -/
inductive pSet : Type (u+1)
| mk (α : Type u) (A : α → pSet) : pSet

namespace pSet

/-- The underlying type of a pre-set -/
def type : pSet → Type u
| ⟨α, A⟩ := α

/-- The underlying pre-set family of a pre-set -/
def func : Π (x : pSet), x.type → pSet
| ⟨α, A⟩ := A

@[simp] theorem mk_type (α A) : type ⟨α, A⟩ = α := rfl
@[simp] theorem mk_func (α A) : func ⟨α, A⟩ = A := rfl

@[simp] theorem eta : Π (x : pSet), mk x.type x.func = x
| ⟨α, A⟩ := rfl

/-- Two pre-sets are extensionally equivalent if every element of the first family is extensionally
equivalent to some element of the second family and vice-versa. -/
def equiv (x y : pSet) : Prop :=
pSet.rec (λ α z m ⟨β, B⟩, (∀ a, ∃ b, m a (B b)) ∧ (∀ b, ∃ a, m a (B b))) x y

theorem equiv_iff : Π {x y : pSet}, equiv x y ↔
  (∀ i, ∃ j, equiv (x.func i) (y.func j)) ∧ (∀ j, ∃ i, equiv (x.func i) (y.func j))
| ⟨α, A⟩ ⟨β, B⟩ := iff.rfl

theorem equiv.exists_left {x y : pSet} (h : equiv x y) : ∀ i, ∃ j, equiv (x.func i) (y.func j) :=
(equiv_iff.1 h).1

theorem equiv.exists_right {x y : pSet} (h : equiv x y) : ∀ j, ∃ i, equiv (x.func i) (y.func j) :=
(equiv_iff.1 h).2

@[refl] protected theorem equiv.refl (x) : equiv x x :=
pSet.rec_on x $ λ α A IH, ⟨λ a, ⟨a, IH a⟩, λ a, ⟨a, IH a⟩⟩

protected theorem equiv.rfl : ∀ {x}, equiv x x := equiv.refl

protected theorem equiv.euc {x} : Π {y z}, equiv x y → equiv z y → equiv x z :=
pSet.rec_on x $ λ α A IH y, pSet.cases_on y $ λ β B ⟨γ, Γ⟩ ⟨αβ, βα⟩ ⟨γβ, βγ⟩,
⟨λ a, let ⟨b, ab⟩ := αβ a, ⟨c, bc⟩ := βγ b in ⟨c, IH a ab bc⟩,
  λ c, let ⟨b, cb⟩ := γβ c, ⟨a, ba⟩ := βα b in ⟨a, IH a ba cb⟩⟩

@[symm] protected theorem equiv.symm {x y} : equiv x y → equiv y x :=
(equiv.refl y).euc

protected theorem equiv.comm {x y} : equiv x y ↔ equiv y x :=
⟨equiv.symm, equiv.symm⟩

@[trans] protected theorem equiv.trans {x y z} (h1 : equiv x y) (h2 : equiv y z) : equiv x z :=
h1.euc h2.symm

protected theorem equiv_of_is_empty (x y : pSet) [is_empty x.type] [is_empty y.type] : equiv x y :=
equiv_iff.2 $ by simp

instance setoid : setoid pSet :=
⟨pSet.equiv, equiv.refl, λ x y, equiv.symm, λ x y z, equiv.trans⟩

/-- A pre-set is a subset of another pre-set if every element of the first family is extensionally
equivalent to some element of the second family.-/
protected def subset (x y : pSet) : Prop := ∀ a, ∃ b, equiv (x.func a) (y.func b)

instance : has_subset pSet := ⟨pSet.subset⟩

instance : is_refl pSet (⊆) := ⟨λ x a, ⟨a, equiv.refl _⟩⟩

instance : is_trans pSet (⊆) :=
⟨λ x y z hxy hyz a, begin
  cases hxy a with b hb,
  cases hyz b with c hc,
  exact ⟨c, hb.trans hc⟩
end⟩

theorem equiv.ext : Π (x y : pSet), equiv x y ↔ (x ⊆ y ∧ y ⊆ x)
| ⟨α, A⟩ ⟨β, B⟩ :=
  ⟨λ ⟨αβ, βα⟩, ⟨αβ, λ b, let ⟨a, h⟩ := βα b in ⟨a, equiv.symm h⟩⟩,
    λ ⟨αβ, βα⟩, ⟨αβ, λ b, let ⟨a, h⟩ := βα b in ⟨a, equiv.symm h⟩⟩⟩

theorem subset.congr_left : Π {x y z : pSet}, equiv x y → (x ⊆ z ↔ y ⊆ z)
| ⟨α, A⟩ ⟨β, B⟩ ⟨γ, Γ⟩ ⟨αβ, βα⟩ :=
  ⟨λ αγ b, let ⟨a, ba⟩ := βα b, ⟨c, ac⟩ := αγ a in ⟨c, (equiv.symm ba).trans ac⟩,
    λ βγ a, let ⟨b, ab⟩ := αβ a, ⟨c, bc⟩ := βγ b in ⟨c, equiv.trans ab bc⟩⟩

theorem subset.congr_right : Π {x y z : pSet}, equiv x y → (z ⊆ x ↔ z ⊆ y)
| ⟨α, A⟩ ⟨β, B⟩ ⟨γ, Γ⟩ ⟨αβ, βα⟩ :=
  ⟨λ γα c, let ⟨a, ca⟩ := γα c, ⟨b, ab⟩ := αβ a in ⟨b, ca.trans ab⟩,
    λ γβ c, let ⟨b, cb⟩ := γβ c, ⟨a, ab⟩ := βα b in ⟨a, cb.trans (equiv.symm ab)⟩⟩

/-- `x ∈ y` as pre-sets if `x` is extensionally equivalent to a member of the family `y`. -/
protected def mem (x y : pSet.{u}) : Prop := ∃ b, equiv x (y.func b)

instance : has_mem pSet pSet := ⟨pSet.mem⟩

theorem mem.mk {α : Type u} (A : α → pSet) (a : α) : A a ∈ mk α A :=
⟨a, equiv.refl (A a)⟩

theorem func_mem (x : pSet) (i : x.type) : x.func i ∈ x :=
by { cases x, apply mem.mk }

theorem mem.ext : Π {x y : pSet.{u}}, (∀ w : pSet.{u}, w ∈ x ↔ w ∈ y) → equiv x y
| ⟨α, A⟩ ⟨β, B⟩ h := ⟨λ a, (h (A a)).1 (mem.mk A a),
    λ b, let ⟨a, ha⟩ := (h (B b)).2 (mem.mk B b) in ⟨a, ha.symm⟩⟩

theorem mem.congr_right : Π {x y : pSet.{u}}, equiv x y → (∀ {w : pSet.{u}}, w ∈ x ↔ w ∈ y)
| ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ w :=
  ⟨λ ⟨a, ha⟩, let ⟨b, hb⟩ := αβ a in ⟨b, ha.trans hb⟩,
    λ ⟨b, hb⟩, let ⟨a, ha⟩ := βα b in ⟨a, hb.euc ha⟩⟩

theorem equiv_iff_mem {x y : pSet.{u}} : equiv x y ↔ (∀ {w : pSet.{u}}, w ∈ x ↔ w ∈ y) :=
⟨mem.congr_right, match x, y with
| ⟨α, A⟩, ⟨β, B⟩, h := ⟨λ a, h.1 (mem.mk A a), λ b,
  let ⟨a, h⟩ := h.2 (mem.mk B b) in ⟨a, h.symm⟩⟩
end⟩

theorem mem.congr_left : Π {x y : pSet.{u}}, equiv x y → (∀ {w : pSet.{u}}, x ∈ w ↔ y ∈ w)
| x y h ⟨α, A⟩ := ⟨λ ⟨a, ha⟩, ⟨a, h.symm.trans ha⟩, λ ⟨a, ha⟩, ⟨a, h.trans ha⟩⟩

private theorem mem_wf_aux : Π {x y : pSet.{u}}, equiv x y → acc (∈) y
| ⟨α, A⟩ ⟨β, B⟩ H := ⟨_, begin
  rintros ⟨γ, C⟩ ⟨b, hc⟩,
  cases H.exists_right b with a ha,
  have H := ha.trans hc.symm,
  rw mk_func at H,
  exact mem_wf_aux H
end⟩

theorem mem_wf : @well_founded pSet (∈) := ⟨λ x, mem_wf_aux $ equiv.refl x⟩

instance : has_well_founded pSet := ⟨_, mem_wf⟩
instance : is_asymm pSet (∈) := mem_wf.is_asymm

theorem mem_asymm {x y : pSet} : x ∈ y → y ∉ x := asymm
theorem mem_irrefl (x : pSet) : x ∉ x := irrefl x

/-- Convert a pre-set to a `set` of pre-sets. -/
def to_set (u : pSet.{u}) : set pSet.{u} := {x | x ∈ u}

@[simp] theorem mem_to_set (a u : pSet.{u}) : a ∈ u.to_set ↔ a ∈ u := iff.rfl

/-- A nonempty set is one that contains some element. -/
protected def nonempty (u : pSet) : Prop := u.to_set.nonempty

theorem nonempty_def (u : pSet) : u.nonempty ↔ ∃ x, x ∈ u := iff.rfl

theorem nonempty_of_mem {x u : pSet} (h : x ∈ u) : u.nonempty := ⟨x, h⟩

@[simp] theorem nonempty_to_set_iff {u : pSet} : u.to_set.nonempty ↔ u.nonempty := iff.rfl

theorem nonempty_type_iff_nonempty {x : pSet} : nonempty x.type ↔ pSet.nonempty x :=
⟨λ ⟨i⟩, ⟨_, func_mem _ i⟩, λ ⟨i, j, h⟩, ⟨j⟩⟩

theorem nonempty_of_nonempty_type (x : pSet) [h : nonempty x.type] : pSet.nonempty x :=
nonempty_type_iff_nonempty.1 h

/-- Two pre-sets are equivalent iff they have the same members. -/
theorem equiv.eq {x y : pSet} : equiv x y ↔ to_set x = to_set y :=
equiv_iff_mem.trans set.ext_iff.symm

instance : has_coe pSet (set pSet) := ⟨to_set⟩

/-- The empty pre-set -/
protected def empty : pSet := ⟨_, pempty.elim⟩

instance : has_emptyc pSet := ⟨pSet.empty⟩

instance : inhabited pSet := ⟨∅⟩

instance : is_empty (type (∅)) := pempty.is_empty

@[simp] theorem not_mem_empty (x : pSet.{u}) : x ∉ (∅ : pSet.{u}) := is_empty.exists_iff.1

@[simp] theorem to_set_empty : to_set ∅ = ∅ := by simp [to_set]

@[simp] theorem empty_subset (x : pSet.{u}) : (∅ : pSet) ⊆ x := λ x, x.elim

@[simp] theorem not_nonempty_empty : ¬ pSet.nonempty ∅ := by simp [pSet.nonempty]

protected theorem equiv_empty (x : pSet) [is_empty x.type] : equiv x ∅ :=
pSet.equiv_of_is_empty x _

/-- Insert an element into a pre-set -/
protected def insert (x y : pSet) : pSet := ⟨option y.type, λ o, option.rec x y.func o⟩

instance : has_insert pSet pSet := ⟨pSet.insert⟩

instance : has_singleton pSet pSet := ⟨λ s, insert s ∅⟩

instance : is_lawful_singleton pSet pSet := ⟨λ _, rfl⟩

instance (x y : pSet) : inhabited (insert x y).type := option.inhabited _

/-- The n-th von Neumann ordinal -/
def of_nat : ℕ → pSet
| 0     := ∅
| (n+1) := insert (of_nat n) (of_nat n)

/-- The von Neumann ordinal ω -/
def omega : pSet := ⟨ulift ℕ, λ n, of_nat n.down⟩

/-- The pre-set separation operation `{x ∈ a | p x}` -/
protected def sep (p : pSet → Prop) (x : pSet) : pSet := ⟨{a // p (x.func a)}, λ y, x.func y.1⟩

instance : has_sep pSet pSet := ⟨pSet.sep⟩

/-- The pre-set powerset operator -/
def powerset (x : pSet) : pSet := ⟨set x.type, λ p, ⟨{a // p a}, λ y, x.func y.1⟩⟩

@[simp] theorem mem_powerset : Π {x y : pSet}, y ∈ powerset x ↔ y ⊆ x
| ⟨α, A⟩ ⟨β, B⟩ := ⟨λ ⟨p, e⟩, (subset.congr_left e).2 $ λ ⟨a, pa⟩, ⟨a, equiv.refl (A a)⟩,
  λ βα, ⟨{a | ∃ b, equiv (B b) (A a)}, λ b, let ⟨a, ba⟩ := βα b in ⟨⟨a, b, ba⟩, ba⟩,
    λ ⟨a, b, ba⟩, ⟨b, ba⟩⟩⟩

/-- The pre-set union operator -/
def sUnion (a : pSet) : pSet := ⟨Σ x, (a.func x).type, λ ⟨x, y⟩, (a.func x).func y⟩

prefix (name := pSet.sUnion) `⋃₀ `:110 := pSet.sUnion

@[simp] theorem mem_sUnion : Π {x y : pSet.{u}}, y ∈ ⋃₀ x ↔ ∃ z ∈ x, y ∈ z
| ⟨α, A⟩ y :=
  ⟨λ ⟨⟨a, c⟩, (e : equiv y ((A a).func c))⟩,
    have func (A a) c ∈ mk (A a).type (A a).func, from mem.mk (A a).func c,
    ⟨_, mem.mk _ _, (mem.congr_left e).2 (by rwa eta at this)⟩,
  λ ⟨⟨β, B⟩, ⟨a, (e : equiv (mk β B) (A a))⟩, ⟨b, yb⟩⟩,
    by { rw ←(eta (A a)) at e, exact
    let ⟨βt, tβ⟩ := e, ⟨c, bc⟩ := βt b in ⟨⟨a, c⟩, yb.trans bc⟩ }⟩

@[simp] theorem to_set_sUnion (x : pSet.{u}) : (⋃₀ x).to_set = ⋃₀ (to_set '' x.to_set) :=
by { ext, simp }

/-- The image of a function from pre-sets to pre-sets. -/
def image (f : pSet.{u} → pSet.{u}) (x : pSet.{u}) : pSet := ⟨x.type, f ∘ x.func⟩

theorem mem_image {f : pSet.{u} → pSet.{u}} (H : ∀ {x y}, equiv x y → equiv (f x) (f y)) :
  Π {x y : pSet.{u}}, y ∈ image f x ↔ ∃ z ∈ x, equiv y (f z)
| ⟨α, A⟩ y := ⟨λ ⟨a, ya⟩, ⟨A a, mem.mk A a, ya⟩, λ ⟨z, ⟨a, za⟩, yz⟩, ⟨a, yz.trans (H za)⟩⟩

/-- Universe lift operation -/
protected def lift : pSet.{u} → pSet.{max u v}
| ⟨α, A⟩ := ⟨ulift α, λ ⟨x⟩, lift (A x)⟩

/-- Embedding of one universe in another -/
@[nolint check_univs] -- intended to be used with explicit universe parameters
def embed : pSet.{max (u+1) v} := ⟨ulift.{v u+1} pSet, λ ⟨x⟩, pSet.lift.{u (max (u+1) v)} x⟩

theorem lift_mem_embed : Π (x : pSet.{u}), pSet.lift.{u (max (u+1) v)} x ∈ embed.{u v} :=
λ x, ⟨⟨x⟩, equiv.rfl⟩

/-- Function equivalence is defined so that `f ~ g` iff `∀ x y, x ~ y → f x ~ g y`. This extends to
equivalence of `n`-ary functions. -/
def arity.equiv : Π {n}, arity pSet.{u} n → arity pSet.{u} n → Prop
| 0     a b := equiv a b
| (n+1) a b := ∀ x y, equiv x y → arity.equiv (a x) (b y)

lemma arity.equiv_const {a : pSet.{u}} : ∀ n, arity.equiv (arity.const a n) (arity.const a n)
| 0     := equiv.rfl
| (n+1) := λ x y h, arity.equiv_const _

/-- `resp n` is the collection of n-ary functions on `pSet` that respect
  equivalence, i.e. when the inputs are equivalent the output is as well. -/
def resp (n) := {x : arity pSet.{u} n // arity.equiv x x}

instance resp.inhabited {n} : inhabited (resp n) :=
⟨⟨arity.const default _, arity.equiv_const _⟩⟩

/-- The `n`-ary image of a `(n + 1)`-ary function respecting equivalence as a function respecting
equivalence. -/
def resp.f {n} (f : resp (n+1)) (x : pSet) : resp n :=
⟨f.1 x, f.2 _ _ $ equiv.refl x⟩

/-- Function equivalence for functions respecting equivalence. See `pSet.arity.equiv`. -/
def resp.equiv {n} (a b : resp n) : Prop := arity.equiv a.1 b.1

protected theorem resp.equiv.refl {n} (a : resp n) : resp.equiv a a := a.2

protected theorem resp.equiv.euc : Π {n} {a b c : resp n},
  resp.equiv a b → resp.equiv c b → resp.equiv a c
| 0     a b c hab hcb := equiv.euc hab hcb
| (n+1) a b c hab hcb := λ x y h,
  @resp.equiv.euc n (a.f x) (b.f y) (c.f y) (hab _ _ h) (hcb _ _ $ equiv.refl y)

protected theorem resp.equiv.symm {n} {a b : resp n} : resp.equiv a b → resp.equiv b a :=
(resp.equiv.refl b).euc

protected theorem resp.equiv.trans {n} {x y z : resp n}
  (h1 : resp.equiv x y) (h2 : resp.equiv y z) : resp.equiv x z :=
h1.euc h2.symm

instance resp.setoid {n} : setoid (resp n) :=
⟨resp.equiv, resp.equiv.refl, λ x y, resp.equiv.symm, λ x y z, resp.equiv.trans⟩

end pSet

/-- The ZFC universe of sets consists of the type of pre-sets,
  quotiented by extensional equivalence. -/
def Set : Type (u+1) := quotient pSet.setoid.{u}

namespace pSet

namespace resp

/-- Helper function for `pSet.eval`. -/
def eval_aux : Π {n}, {f : resp n → arity Set.{u} n // ∀ (a b : resp n), resp.equiv a b → f a = f b}
| 0     := ⟨λ a, ⟦a.1⟧, λ a b h, quotient.sound h⟩
| (n+1) := let F : resp (n + 1) → arity Set (n + 1) := λ a, @quotient.lift _ _ pSet.setoid
    (λ x, eval_aux.1 (a.f x)) (λ b c h, eval_aux.2 _ _ (a.2 _ _ h)) in
  ⟨F, λ b c h, funext $ @quotient.ind _ _ (λ q, F b q = F c q) $ λ z,
  eval_aux.2 (resp.f b z) (resp.f c z) (h _ _ (pSet.equiv.refl z))⟩

/-- An equivalence-respecting function yields an n-ary ZFC set function. -/
def eval (n) : resp n → arity Set.{u} n := eval_aux.1

theorem eval_val {n f x} : (@eval (n+1) f : Set → arity Set n) ⟦x⟧ = eval n (resp.f f x) := rfl

end resp

/-- A set function is "definable" if it is the image of some n-ary pre-set
  function. This isn't exactly definability, but is useful as a sufficient
  condition for functions that have a computable image. -/
class inductive definable (n) : arity Set.{u} n → Type (u+1)
| mk (f) : definable (resp.eval n f)

attribute [instance] definable.mk

/-- The evaluation of a function respecting equivalence is definable, by that same function. -/
def definable.eq_mk {n} (f) : Π {s : arity Set.{u} n} (H : resp.eval _ f = s), definable n s
| ._ rfl := ⟨f⟩

/-- Turns a definable function into a function that respects equivalence. -/
def definable.resp {n} : Π (s : arity Set.{u} n) [definable n s], resp n
| ._ ⟨f⟩ := f

theorem definable.eq {n} :
  Π (s : arity Set.{u} n) [H : definable n s], (@definable.resp n s H).eval _ = s
| ._ ⟨f⟩ := rfl

end pSet

namespace classical
open pSet

/-- All functions are classically definable. -/
noncomputable def all_definable : Π {n} (F : arity Set.{u} n), definable n F
| 0     F := let p := @quotient.exists_rep pSet _ F in
              definable.eq_mk ⟨some p, equiv.rfl⟩ (some_spec p)
| (n+1) (F : arity Set.{u} (n + 1)) := begin
    have I := λ x, (all_definable (F x)),
    refine definable.eq_mk ⟨λ x : pSet, (@definable.resp _ _ (I ⟦x⟧)).1, _⟩ _,
    { dsimp [arity.equiv],
      introsI x y h,
      rw @quotient.sound pSet _ _ _ h,
      exact (definable.resp (F ⟦y⟧)).2 },
    refine funext (λ q, quotient.induction_on q $ λ x, _),
    simp_rw [resp.eval_val, resp.f, subtype.val_eq_coe, subtype.coe_eta],
    exact @definable.eq _ (F ⟦x⟧) (I ⟦x⟧),
  end

end classical

namespace Set
open pSet

/-- Turns a pre-set into a ZFC set. -/
def mk : pSet → Set := quotient.mk

@[simp] theorem mk_eq (x : pSet) : @eq Set ⟦x⟧ (mk x) := rfl
@[simp] theorem mk_out : ∀ x : Set, mk x.out = x := quotient.out_eq
theorem eq {x y : pSet} : mk x = mk y ↔ equiv x y := quotient.eq
theorem sound {x y : pSet} (h : pSet.equiv x y) : mk x = mk y := quotient.sound h
theorem exact {x y : pSet} : mk x = mk y → pSet.equiv x y := quotient.exact

@[simp] lemma eval_mk {n f x} :
  (@resp.eval (n+1) f : Set → arity Set n) (mk x) = resp.eval n (resp.f f x) :=
rfl

/-- The membership relation for ZFC sets is inherited from the membership relation for pre-sets. -/
protected def mem : Set → Set → Prop :=
quotient.lift₂ pSet.mem
  (λ x y x' y' hx hy, propext ((mem.congr_left hx).trans (mem.congr_right hy)))

instance : has_mem Set Set := ⟨Set.mem⟩

@[simp] theorem mk_mem_iff {x y : pSet} : mk x ∈ mk y ↔ x ∈ y := iff.rfl

/-- Convert a ZFC set into a `set` of ZFC sets -/
def to_set (u : Set.{u}) : set Set.{u} := {x | x ∈ u}

@[simp] theorem mem_to_set (a u : Set.{u}) : a ∈ u.to_set ↔ a ∈ u := iff.rfl

instance small_to_set (x : Set.{u}) : small.{u} x.to_set :=
quotient.induction_on x $ λ a, begin
  let f : a.type → (mk a).to_set := λ i, ⟨mk $ a.func i, func_mem a i⟩,
  suffices : function.surjective f,
  { exact small_of_surjective this },
  rintro ⟨y, hb⟩,
  induction y using quotient.induction_on,
  cases hb with i h,
  exact ⟨i, subtype.coe_injective (quotient.sound h.symm)⟩
end

/-- A nonempty set is one that contains some element. -/
protected def nonempty (u : Set) : Prop := u.to_set.nonempty

theorem nonempty_def (u : Set) : u.nonempty ↔ ∃ x, x ∈ u := iff.rfl

theorem nonempty_of_mem {x u : Set} (h : x ∈ u) : u.nonempty := ⟨x, h⟩

@[simp] theorem nonempty_to_set_iff {u : Set} : u.to_set.nonempty ↔ u.nonempty := iff.rfl

/-- `x ⊆ y` as ZFC sets means that all members of `x` are members of `y`. -/
protected def subset (x y : Set.{u}) :=
∀ ⦃z⦄, z ∈ x → z ∈ y

instance has_subset : has_subset Set :=
⟨Set.subset⟩

lemma subset_def {x y : Set.{u}} : x ⊆ y ↔ ∀ ⦃z⦄, z ∈ x → z ∈ y := iff.rfl

instance : is_refl Set (⊆) := ⟨λ x a, id⟩
instance : is_trans Set (⊆) := ⟨λ x y z hxy hyz a ha, hyz (hxy ha)⟩

@[simp] theorem subset_iff : Π {x y : pSet}, mk x ⊆ mk y ↔ x ⊆ y
| ⟨α, A⟩ ⟨β, B⟩ := ⟨λ h a, @h ⟦A a⟧ (mem.mk A a),
  λ h z, quotient.induction_on z (λ z ⟨a, za⟩, let ⟨b, ab⟩ := h a in ⟨b, za.trans ab⟩)⟩

@[simp] theorem to_set_subset_iff {x y : Set} : x.to_set ⊆ y.to_set ↔ x ⊆ y :=
by simp [subset_def, set.subset_def]

@[ext] theorem ext {x y : Set.{u}} : (∀ z : Set.{u}, z ∈ x ↔ z ∈ y) → x = y :=
quotient.induction_on₂ x y (λ u v h, quotient.sound (mem.ext (λ w, h ⟦w⟧)))

theorem ext_iff {x y : Set.{u}} : x = y ↔ (∀ z : Set.{u}, z ∈ x ↔ z ∈ y) :=
⟨λ h, by simp [h], ext⟩

theorem to_set_injective : function.injective to_set := λ x y h, ext $ set.ext_iff.1 h

@[simp] theorem to_set_inj {x y : Set} : x.to_set = y.to_set ↔ x = y :=
to_set_injective.eq_iff

instance : is_antisymm Set (⊆) := ⟨λ a b hab hba, ext $ λ c, ⟨@hab c, @hba c⟩⟩

/-- The empty ZFC set -/
protected def empty : Set := mk ∅
instance : has_emptyc Set := ⟨Set.empty⟩
instance : inhabited Set := ⟨∅⟩

@[simp] theorem not_mem_empty (x) : x ∉ (∅ : Set.{u}) :=
quotient.induction_on x pSet.not_mem_empty

@[simp] theorem to_set_empty : to_set ∅ = ∅ := by simp [to_set]

@[simp] theorem empty_subset (x : Set.{u}) : (∅ : Set) ⊆ x :=
quotient.induction_on x $ λ y, subset_iff.2 $ pSet.empty_subset y

@[simp] theorem not_nonempty_empty : ¬ Set.nonempty ∅ := by simp [Set.nonempty]

@[simp] theorem nonempty_mk_iff {x : pSet} : (mk x).nonempty ↔ x.nonempty :=
begin
  refine ⟨_, λ ⟨a, h⟩, ⟨mk a, h⟩⟩,
  rintro ⟨a, h⟩,
  induction a using quotient.induction_on,
  exact ⟨a, h⟩
end

theorem eq_empty (x : Set.{u}) : x = ∅ ↔ ∀ y : Set.{u}, y ∉ x := by { rw ext_iff, simp }

theorem eq_empty_or_nonempty (u : Set) : u = ∅ ∨ u.nonempty :=
by { rw [eq_empty, ←not_exists], apply em' }

/-- `insert x y` is the set `{x} ∪ y` -/
protected def insert : Set → Set → Set :=
resp.eval 2 ⟨pSet.insert, λ u v uv ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩,
  ⟨λ o, match o with
   | some a := let ⟨b, hb⟩ := αβ a in ⟨some b, hb⟩
   | none := ⟨none, uv⟩
   end, λ o, match o with
   | some b := let ⟨a, ha⟩ := βα b in ⟨some a, ha⟩
   | none := ⟨none, uv⟩
   end⟩⟩

instance : has_insert Set Set := ⟨Set.insert⟩

instance : has_singleton Set Set := ⟨λ x, insert x ∅⟩

instance : is_lawful_singleton Set Set := ⟨λ x, rfl⟩

@[simp] theorem mem_insert_iff {x y z : Set.{u}} : x ∈ insert y z ↔ x = y ∨ x ∈ z :=
quotient.induction_on₃ x y z
 (λ x y ⟨α, A⟩, show x ∈ pSet.mk (option α) (λ o, option.rec y A o) ↔
    mk x = mk y ∨ x ∈ pSet.mk α A, from
  ⟨λ m, match m with
  | ⟨some a, ha⟩ := or.inr ⟨a, ha⟩
  | ⟨none, h⟩ := or.inl (quotient.sound h)
  end, λ m, match m with
  | or.inr ⟨a, ha⟩ := ⟨some a, ha⟩
  | or.inl h := ⟨none, quotient.exact h⟩
  end⟩)

theorem mem_insert (x y : Set) : x ∈ insert x y := mem_insert_iff.2 $ or.inl rfl
theorem mem_insert_of_mem {y z : Set} (x) (h : z ∈ y): z ∈ insert x y := mem_insert_iff.2 $ or.inr h

@[simp] theorem to_set_insert (x y : Set) : (insert x y).to_set = insert x y.to_set :=
by { ext, simp }

@[simp] theorem mem_singleton {x y : Set.{u}} : x ∈ @singleton Set.{u} Set.{u} _ y ↔ x = y :=
iff.trans mem_insert_iff ⟨λ o, or.rec (λ h, h) (λ n, absurd n (not_mem_empty _)) o, or.inl⟩

@[simp] theorem to_set_singleton (x : Set) : ({x} : Set).to_set = {x} :=
by { ext, simp }

theorem insert_nonempty (u v : Set) : (insert u v).nonempty := ⟨u, mem_insert u v⟩

theorem singleton_nonempty (u : Set) : Set.nonempty {u} := insert_nonempty u ∅

@[simp] theorem mem_pair {x y z : Set.{u}} : x ∈ ({y, z} : Set) ↔ x = y ∨ x = z :=
iff.trans mem_insert_iff $ or_congr iff.rfl mem_singleton

/-- `omega` is the first infinite von Neumann ordinal -/
def omega : Set := mk omega

@[simp] theorem omega_zero : ∅ ∈ omega :=
⟨⟨0⟩, equiv.rfl⟩

@[simp] theorem omega_succ {n} : n ∈ omega.{u} → insert n n ∈ omega.{u} :=
quotient.induction_on n (λ x ⟨⟨n⟩, h⟩, ⟨⟨n+1⟩, Set.exact $
  show insert (mk x) (mk x) = insert (mk $ of_nat n) (mk $ of_nat n), { rw Set.sound h, refl } ⟩)

/-- `{x ∈ a | p x}` is the set of elements in `a` satisfying `p` -/
protected def sep (p : Set → Prop) : Set → Set :=
resp.eval 1 ⟨pSet.sep (λ y, p (mk y)), λ ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩,
  ⟨λ ⟨a, pa⟩, let ⟨b, hb⟩ := αβ a in ⟨⟨b, by rwa [mk_func, ←Set.sound hb]⟩, hb⟩,
   λ ⟨b, pb⟩, let ⟨a, ha⟩ := βα b in ⟨⟨a, by rwa [mk_func, Set.sound ha]⟩, ha⟩⟩⟩

instance : has_sep Set Set := ⟨Set.sep⟩

@[simp] theorem mem_sep {p : Set.{u} → Prop} {x y : Set.{u}} : y ∈ {y ∈ x | p y} ↔ y ∈ x ∧ p y :=
quotient.induction_on₂ x y (λ ⟨α, A⟩ y,
  ⟨λ ⟨⟨a, pa⟩, h⟩, ⟨⟨a, h⟩, by rwa (@quotient.sound pSet _ _ _ h)⟩,
  λ ⟨⟨a, h⟩, pa⟩, ⟨⟨a, by { rw mk_func at h, rwa [mk_func, ←Set.sound h] }⟩, h⟩⟩)

@[simp] theorem to_set_sep (a : Set) (p : Set → Prop) :
  {x ∈ a | p x}.to_set = {x ∈ a.to_set | p x} :=
by { ext, simp }

/-- The powerset operation, the collection of subsets of a ZFC set -/
def powerset : Set → Set :=
resp.eval 1 ⟨powerset, λ ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩,
  ⟨λ p, ⟨{b | ∃ a, p a ∧ equiv (A a) (B b)},
    λ ⟨a, pa⟩, let ⟨b, ab⟩ := αβ a in ⟨⟨b, a, pa, ab⟩, ab⟩,
    λ ⟨b, a, pa, ab⟩, ⟨⟨a, pa⟩, ab⟩⟩,
   λ q, ⟨{a | ∃ b, q b ∧ equiv (A a) (B b)},
    λ ⟨a, b, qb, ab⟩, ⟨⟨b, qb⟩, ab⟩,
    λ ⟨b, qb⟩, let ⟨a, ab⟩ := βα b in ⟨⟨a, b, qb, ab⟩, ab⟩⟩⟩⟩

@[simp] theorem mem_powerset {x y : Set.{u}} : y ∈ powerset x ↔ y ⊆ x :=
quotient.induction_on₂ x y ( λ ⟨α, A⟩ ⟨β, B⟩,
  show (⟨β, B⟩ : pSet.{u}) ∈ (pSet.powerset.{u} ⟨α, A⟩) ↔ _,
    by simp [mem_powerset, subset_iff])

theorem sUnion_lem {α β : Type u} (A : α → pSet) (B : β → pSet) (αβ : ∀ a, ∃ b, equiv (A a) (B b)) :
  ∀ a, ∃ b, (equiv ((sUnion ⟨α, A⟩).func a) ((sUnion ⟨β, B⟩).func b))
| ⟨a, c⟩ := let ⟨b, hb⟩ := αβ a in
  begin
    induction ea : A a with γ Γ,
    induction eb : B b with δ Δ,
    rw [ea, eb] at hb,
    cases hb with γδ δγ,
    exact
    let c : type (A a) := c, ⟨d, hd⟩ := γδ (by rwa ea at c) in
    have pSet.equiv ((A a).func c) ((B b).func (eq.rec d (eq.symm eb))), from
    match A a, B b, ea, eb, c, d, hd with ._, ._, rfl, rfl, x, y, hd := hd end,
    ⟨⟨b, by { rw mk_func, exact eq.rec d (eq.symm eb) }⟩, this⟩
  end

/-- The union operator, the collection of elements of elements of a ZFC set -/
def sUnion : Set → Set :=
resp.eval 1 ⟨pSet.sUnion, λ ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩,
  ⟨sUnion_lem A B αβ, λ a, exists.elim (sUnion_lem B A (λ b,
    exists.elim (βα b) (λ c hc, ⟨c, pSet.equiv.symm hc⟩)) a) (λ b hb, ⟨b, pSet.equiv.symm hb⟩)⟩⟩

prefix (name := Set.sUnion) `⋃₀ `:110 := Set.sUnion

@[simp] theorem mem_sUnion {x y : Set.{u}} : y ∈ ⋃₀ x ↔ ∃ z ∈ x, y ∈ z :=
quotient.induction_on₂ x y (λ x y, iff.trans mem_sUnion
  ⟨λ ⟨z, h⟩, ⟨⟦z⟧, h⟩, λ ⟨z, h⟩, quotient.induction_on z (λ z h, ⟨z, h⟩) h⟩)

theorem mem_sUnion_of_mem {x y z : Set} (hy : y ∈ z) (hz : z ∈ x) : y ∈ ⋃₀ x :=
mem_sUnion.2 ⟨z, hz, hy⟩

@[simp] theorem sUnion_empty : ⋃₀ (∅ : Set.{u}) = ∅ := by { ext, simp }

@[simp] theorem sUnion_singleton {x : Set.{u}} : ⋃₀ ({x} : Set) = x :=
ext $ λ y, by simp_rw [mem_sUnion, exists_prop, mem_singleton, exists_eq_left]

@[simp] theorem to_set_sUnion (x : Set.{u}) : (⋃₀ x).to_set = ⋃₀ (to_set '' x.to_set) :=
by { ext, simp }

theorem singleton_injective : function.injective (@singleton Set Set _) :=
λ x y H, let this := congr_arg sUnion H in by rwa [sUnion_singleton, sUnion_singleton] at this

@[simp] theorem singleton_inj {x y : Set} : ({x} : Set) = {y} ↔ x = y := singleton_injective.eq_iff

/-- The binary union operation -/
protected def union (x y : Set.{u}) : Set.{u} := ⋃₀ {x, y}

/-- The binary intersection operation -/
protected def inter (x y : Set.{u}) : Set.{u} := {z ∈ x | z ∈ y}

/-- The set difference operation -/
protected def diff (x y : Set.{u}) : Set.{u} := {z ∈ x | z ∉ y}

instance : has_union Set := ⟨Set.union⟩
instance : has_inter Set := ⟨Set.inter⟩
instance : has_sdiff Set := ⟨Set.diff⟩

@[simp] theorem to_set_union (x y : Set.{u}) : (x ∪ y).to_set = x.to_set ∪ y.to_set :=
by { unfold has_union.union, rw Set.union, simp }

@[simp] theorem to_set_inter (x y : Set.{u}) : (x ∩ y).to_set = x.to_set ∩ y.to_set :=
by { unfold has_inter.inter, rw Set.inter, ext, simp }

@[simp] theorem to_set_sdiff (x y : Set.{u}) : (x \ y).to_set = x.to_set \ y.to_set :=
by { change {z ∈ x | z ∉ y}.to_set = _, ext, simp }

@[simp] theorem mem_union {x y z : Set.{u}} : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y :=
by { rw ←mem_to_set, simp }

@[simp] theorem mem_inter {x y z : Set.{u}} : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y :=
@@mem_sep (λ z : Set.{u}, z ∈ y)

@[simp] theorem mem_diff {x y z : Set.{u}} : z ∈ x \ y ↔ z ∈ x ∧ z ∉ y :=
@@mem_sep (λ z : Set.{u}, z ∉ y)

/-- Induction on the `∈` relation. -/
@[elab_as_eliminator]
theorem induction_on {p : Set → Prop} (x) (h : ∀ x, (∀ y ∈ x, p y) → p x) : p x :=
quotient.induction_on x $ λ u, pSet.rec_on u $ λ α A IH, h _ $ λ y,
show @has_mem.mem _ _ Set.has_mem y ⟦⟨α, A⟩⟧ → p y, from
quotient.induction_on y (λ v ⟨a, ha⟩, by { rw (@quotient.sound pSet _ _ _ ha), exact IH a })

theorem mem_wf : @well_founded Set (∈) := ⟨λ x, induction_on x acc.intro⟩

instance : has_well_founded Set := ⟨_, mem_wf⟩

instance : is_asymm Set (∈) := mem_wf.is_asymm

theorem mem_asymm {x y : Set} : x ∈ y → y ∉ x := asymm
theorem mem_irrefl (x : Set) : x ∉ x := irrefl x

theorem regularity (x : Set.{u}) (h : x ≠ ∅) : ∃ y ∈ x, x ∩ y = ∅ :=
classical.by_contradiction $ λ ne, h $ (eq_empty x).2 $ λ y,
induction_on y $ λ z (IH : ∀ w : Set.{u}, w ∈ z → w ∉ x), show z ∉ x, from λ zx,
ne ⟨z, zx, (eq_empty _).2 (λ w wxz, let ⟨wx, wz⟩ := mem_inter.1 wxz in IH w wz wx)⟩

/-- The image of a (definable) ZFC set function -/
def image (f : Set → Set) [H : definable 1 f] : Set → Set :=
let r := @definable.resp 1 f _ in
resp.eval 1 ⟨image r.1, λ x y e, mem.ext $ λ z,
  iff.trans (mem_image r.2) $ iff.trans (by exact
   ⟨λ ⟨w, h1, h2⟩, ⟨w, (mem.congr_right e).1 h1, h2⟩,
    λ ⟨w, h1, h2⟩, ⟨w, (mem.congr_right e).2 h1, h2⟩⟩) $
  iff.symm (mem_image r.2)⟩

theorem image.mk :
  Π (f : Set.{u} → Set.{u}) [H : definable 1 f] (x) {y} (h : y ∈ x), f y ∈ @image f H x
| ._ ⟨F⟩ x y := quotient.induction_on₂ x y $ λ ⟨α, A⟩ y ⟨a, ya⟩, ⟨a, F.2 _ _ ya⟩

@[simp] theorem mem_image : Π {f : Set.{u} → Set.{u}} [H : definable 1 f] {x y : Set.{u}},
  y ∈ @image f H x ↔ ∃ z ∈ x, f z = y
| ._ ⟨F⟩ x y := quotient.induction_on₂ x y $ λ ⟨α, A⟩ y,
  ⟨λ ⟨a, ya⟩, ⟨⟦A a⟧, mem.mk A a, eq.symm $ quotient.sound ya⟩,
  λ ⟨z, hz, e⟩, e ▸ image.mk _ _ hz⟩

@[simp] theorem to_set_image (f : Set → Set) [H : definable 1 f] (x : Set) :
  (image f x).to_set = f '' x.to_set :=
by { ext, simp }

/-- The range of an indexed family of sets. The universes allow for a more general index type
  without manual use of `ulift`. -/
noncomputable def range {α : Type u} (f : α → Set.{max u v}) : Set.{max u v} :=
⟦⟨ulift α, quotient.out ∘ f ∘ ulift.down⟩⟧

@[simp] theorem mem_range {α : Type u} {f : α → Set.{max u v}} {x : Set.{max u v}} :
  x ∈ range f ↔ x ∈ set.range f :=
quotient.induction_on x (λ y, begin
  split,
  { rintro ⟨z, hz⟩,
    exact ⟨z.down, quotient.eq_mk_iff_out.2 hz.symm⟩ },
  { rintro ⟨z, hz⟩,
    use z,
    simpa [hz] using pSet.equiv.symm (quotient.mk_out y) }
end)

@[simp] theorem to_set_range {α : Type u} (f : α → Set.{max u v}) :
  (range f).to_set = set.range f :=
by { ext, simp }

/-- Kuratowski ordered pair -/
def pair (x y : Set.{u}) : Set.{u} := {{x}, {x, y}}

@[simp] theorem to_set_pair (x y : Set.{u}) : (pair x y).to_set = {{x}, {x, y}} := by simp [pair]

/-- A subset of pairs `{(a, b) ∈ x × y | p a b}` -/
def pair_sep (p : Set.{u} → Set.{u} → Prop) (x y : Set.{u}) : Set.{u} :=
{z ∈ powerset (powerset (x ∪ y)) | ∃ a ∈ x, ∃ b ∈ y, z = pair a b ∧ p a b}

@[simp] theorem mem_pair_sep {p} {x y z : Set.{u}} :
  z ∈ pair_sep p x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = pair a b ∧ p a b :=
begin
  refine mem_sep.trans ⟨and.right, λ e, ⟨_, e⟩⟩,
  rcases e with ⟨a, ax, b, bY, rfl, pab⟩,
  simp only [mem_powerset, subset_def, mem_union, pair, mem_pair],
  rintros u (rfl|rfl) v; simp only [mem_singleton, mem_pair],
  { rintro rfl, exact or.inl ax },
  { rintro (rfl|rfl); [left, right]; assumption }
end

theorem pair_injective : function.injective2 pair :=
λ x x' y y' H, begin
  have ae := ext_iff.1 H,
  simp only [pair, mem_pair] at ae,
  obtain rfl : x = x',
  { cases (ae {x}).1 (by simp) with h h,
    { exact singleton_injective h },
    { have m : x' ∈ ({x} : Set),
      { simp [h] },
      rw mem_singleton.mp m } },
  have he : x = y → y = y',
  { rintro rfl,
    cases (ae {x, y'}).2 (by simp only [eq_self_iff_true, or_true]) with xy'x xy'xx,
    { rw [eq_comm, ←mem_singleton, ←xy'x, mem_pair],
      exact or.inr rfl },
    { simpa [eq_comm] using (ext_iff.1 xy'xx y').1 (by simp) } },
  obtain xyx | xyy' := (ae {x, y}).1 (by simp),
  { obtain rfl := mem_singleton.mp ((ext_iff.1 xyx y).1 $ by simp),
    simp [he rfl] },
  { obtain rfl | yy' := mem_pair.mp ((ext_iff.1 xyy' y).1 $ by simp),
    { simp [he rfl] },
    { simp [yy'] } }
end

@[simp] theorem pair_inj {x y x' y' : Set} : pair x y = pair x' y' ↔ x = x' ∧ y = y' :=
pair_injective.eq_iff

/-- The cartesian product, `{(a, b) | a ∈ x, b ∈ y}` -/
def prod : Set.{u} → Set.{u} → Set.{u} := pair_sep (λ a b, true)

@[simp] theorem mem_prod {x y z : Set.{u}} : z ∈ prod x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = pair a b :=
by simp [prod]

@[simp] theorem pair_mem_prod {x y a b : Set.{u}} : pair a b ∈ prod x y ↔ a ∈ x ∧ b ∈ y :=
⟨λ h, let ⟨a', a'x, b', b'y, e⟩ := mem_prod.1 h in
  match a', b', pair_injective e, a'x, b'y with ._, ._, ⟨rfl, rfl⟩, ax, bY := ⟨ax, bY⟩ end,
λ ⟨ax, bY⟩, mem_prod.2 ⟨a, ax, b, bY, rfl⟩⟩

/-- `is_func x y f` is the assertion that `f` is a subset of `x × y` which relates to each element
of `x` a unique element of `y`, so that we can consider `f`as a ZFC function `x → y`. -/
def is_func (x y f : Set.{u}) : Prop :=
f ⊆ prod x y ∧ ∀ z : Set.{u}, z ∈ x → ∃! w, pair z w ∈ f

/-- `funs x y` is `y ^ x`, the set of all set functions `x → y` -/
def funs (x y : Set.{u}) : Set.{u} :=
{f ∈ powerset (prod x y) | is_func x y f}

@[simp] theorem mem_funs {x y f : Set.{u}} : f ∈ funs x y ↔ is_func x y f :=
by simp [funs, is_func]

-- TODO(Mario): Prove this computably
noncomputable instance map_definable_aux (f : Set → Set) [H : definable 1 f] :
  definable 1 (λ y, pair y (f y)) :=
@classical.all_definable 1 _

/-- Graph of a function: `map f x` is the ZFC function which maps `a ∈ x` to `f a` -/
noncomputable def map (f : Set → Set) [H : definable 1 f] : Set → Set :=
image (λ y, pair y (f y))

@[simp] theorem mem_map {f : Set → Set} [H : definable 1 f] {x y : Set} :
  y ∈ map f x ↔ ∃ z ∈ x, pair z (f z) = y :=
mem_image

theorem map_unique {f : Set.{u} → Set.{u}} [H : definable 1 f] {x z : Set.{u}} (zx : z ∈ x) :
  ∃! w, pair z w ∈ map f x :=
⟨f z, image.mk _ _ zx, λ y yx, let ⟨w, wx, we⟩ := mem_image.1 yx, ⟨wz, fy⟩ := pair_injective we in
  by rw[←fy, wz]⟩

@[simp] theorem map_is_func {f : Set → Set} [H : definable 1 f] {x y : Set} :
  is_func x y (map f x) ↔ ∀ z ∈ x, f z ∈ y :=
⟨λ ⟨ss, h⟩ z zx, let ⟨t, t1, t2⟩ := h z zx in
  (t2 (f z) (image.mk _ _ zx)).symm ▸ (pair_mem_prod.1 (ss t1)).right,
λ h, ⟨λ y yx, let ⟨z, zx, ze⟩ := mem_image.1 yx in ze ▸ pair_mem_prod.2 ⟨zx, h z zx⟩,
     λ z, map_unique⟩⟩

/-- Given a predicate `p` on ZFC sets. `hereditarily p x` means that `x` has property `p` and the
members of `x` are all `hereditarily p`. -/
def hereditarily (p : Set → Prop) : Set → Prop
| x := p x ∧ ∀ y ∈ x, hereditarily y
using_well_founded { dec_tac := `[assumption] }

section hereditarily

variables {p : Set.{u} → Prop} {x y : Set.{u}}

lemma hereditarily_iff :
  hereditarily p x ↔ p x ∧ ∀ y ∈ x, hereditarily p y :=
by rw [← hereditarily]

alias hereditarily_iff ↔ hereditarily.def _

lemma hereditarily.self (h : x.hereditarily p) : p x := h.def.1
lemma hereditarily.mem (h : x.hereditarily p) (hy : y ∈ x) : y.hereditarily p := h.def.2 _ hy

lemma hereditarily.empty : hereditarily p x → p ∅ :=
begin
  apply x.induction_on,
  intros y IH h,
  rcases Set.eq_empty_or_nonempty y with (rfl|⟨a, ha⟩),
  { exact h.self },
  { exact IH a ha (h.mem ha) }
end

end hereditarily

end Set

/-- The collection of all classes.

We define `Class` as `set Set`, as this allows us to get many instances automatically. However, in
practice, we treat it as (the definitionally equal) `Set → Prop`. This means, the preferred way to
state that `x : Set` belongs to `A : Class` is to write `A x`. -/
@[derive [has_subset, has_sep Set, has_emptyc, inhabited, has_insert Set, has_union, has_inter,
  has_compl, has_sdiff]]
def Class := set Set

namespace Class

/-- Coerce a ZFC set into a class -/
def of_Set (x : Set.{u}) : Class.{u} := {y | y ∈ x}
instance : has_coe Set Class := ⟨of_Set⟩

/-- The universal class -/
def univ : Class := set.univ

/-- Assert that `A` is a ZFC set satisfying `B` -/
def to_Set (B : Class.{u}) (A : Class.{u}) : Prop := ∃ x, ↑x = A ∧ B x

/-- `A ∈ B` if `A` is a ZFC set which satisfies `B` -/
protected def mem (A B : Class.{u}) : Prop := to_Set.{u} B A
instance : has_mem Class Class := ⟨Class.mem⟩

theorem mem_def (A B : Class.{u}) : A ∈ B ↔ ∃ x, ↑x = A ∧ B x := iff.rfl

@[simp] theorem not_mem_empty (x : Class.{u}) : x ∉ (∅ : Class.{u}) := λ ⟨_, _, h⟩, h

@[simp] theorem not_empty_hom (x : Set.{u}) : ¬ (∅ : Class.{u}) x := id

@[simp] theorem mem_univ {A : Class.{u}} : A ∈ univ.{u} ↔ ∃ x : Set.{u}, ↑x = A :=
exists_congr $ λ x, and_true _

@[simp] theorem mem_univ_hom (x : Set.{u}) : univ.{u} x := trivial

theorem eq_univ_iff_forall {A : Class.{u}} : A = univ ↔ ∀ x : Set, A x := set.eq_univ_iff_forall
theorem eq_univ_of_forall {A : Class.{u}} : (∀ x : Set, A x) → A = univ := set.eq_univ_of_forall

theorem mem_wf : @well_founded Class.{u} (∈) :=
⟨begin
  have H : ∀ x : Set.{u}, @acc Class.{u} (∈) ↑x,
  { refine λ a, Set.induction_on a (λ x IH, ⟨x, _⟩),
    rintros A ⟨z, rfl, hz⟩,
    exact IH z hz },
  { refine λ A, ⟨A, _⟩,
    rintros B ⟨x, rfl, hx⟩,
    exact H x }
end⟩

instance : has_well_founded Class := ⟨_, mem_wf⟩
instance : is_asymm Class (∈) := mem_wf.is_asymm

theorem mem_asymm {x y : Class} : x ∈ y → y ∉ x := asymm
theorem mem_irrefl (x : Class) : x ∉ x := irrefl x

/-- **There is no universal set.**

This is stated as `univ ∉ univ`, meaning that `univ` (the class of all sets) is proper (does not
belong to the class of all sets). -/
theorem univ_not_mem_univ : univ ∉ univ := mem_irrefl _

/-- Convert a conglomerate (a collection of classes) into a class -/
def Cong_to_Class (x : set Class.{u}) : Class.{u} := {y | ↑y ∈ x}

@[simp] theorem Cong_to_Class_empty : Cong_to_Class ∅ = ∅ :=
by { ext, simp [Cong_to_Class] }

/-- Convert a class into a conglomerate (a collection of classes) -/
def Class_to_Cong (x : Class.{u}) : set Class.{u} := {y | y ∈ x}

@[simp] theorem Class_to_Cong_empty : Class_to_Cong ∅ = ∅ :=
by { ext, simp [Class_to_Cong] }

/-- The power class of a class is the class of all subclasses that are ZFC sets -/
def powerset (x : Class) : Class := Cong_to_Class (set.powerset x)

/-- The union of a class is the class of all members of ZFC sets in the class -/
def sUnion (x : Class) : Class := ⋃₀ (Class_to_Cong x)

prefix (name := Class.sUnion) `⋃₀ `:110 := Class.sUnion

theorem of_Set.inj {x y : Set.{u}} (h : (x : Class.{u}) = y) : x = y :=
Set.ext $ λ z, by { change (x : Class.{u}) z ↔ (y : Class.{u}) z, rw h }

@[simp] theorem to_Set_of_Set (A : Class.{u}) (x : Set.{u}) : to_Set A x ↔ A x :=
⟨λ ⟨y, yx, py⟩, by rwa of_Set.inj yx at py, λ px, ⟨x, rfl, px⟩⟩

@[simp] theorem mem_hom_left (x : Set.{u}) (A : Class.{u}) : (x : Class.{u}) ∈ A ↔ A x :=
to_Set_of_Set _ _

@[simp] theorem mem_hom_right (x y : Set.{u}) : (y : Class.{u}) x ↔ x ∈ y := iff.rfl

@[simp] theorem subset_hom (x y : Set.{u}) : (x : Class.{u}) ⊆ y ↔ x ⊆ y := iff.rfl

@[simp] theorem sep_hom (p : Class.{u}) (x : Set.{u}) :
  (↑{y ∈ x | p y} : Class.{u}) = {y ∈ x | p y} :=
set.ext $ λ y, Set.mem_sep

@[simp] theorem empty_hom : ↑(∅ : Set.{u}) = (∅ : Class.{u}) :=
set.ext $ λ y, (iff_false _).2 (Set.not_mem_empty y)

@[simp] theorem insert_hom (x y : Set.{u}) : (@insert Set.{u} Class.{u} _ x y) = ↑(insert x y) :=
set.ext $ λ z, iff.symm Set.mem_insert_iff

@[simp] theorem union_hom (x y : Set.{u}) : (x : Class.{u}) ∪ y = (x ∪ y : Set.{u}) :=
set.ext $ λ z, iff.symm Set.mem_union

@[simp] theorem inter_hom (x y : Set.{u}) : (x : Class.{u}) ∩ y = (x ∩ y : Set.{u}) :=
set.ext $ λ z, iff.symm Set.mem_inter

@[simp] theorem diff_hom (x y : Set.{u}) : (x : Class.{u}) \ y = (x \ y : Set.{u}) :=
set.ext $ λ z, iff.symm Set.mem_diff

@[simp] theorem powerset_hom (x : Set.{u}) : powerset.{u} x = Set.powerset x :=
set.ext $ λ z, iff.symm Set.mem_powerset

@[simp] theorem sUnion_hom (x : Set.{u}) : ⋃₀ (x : Class.{u}) = ⋃₀ x :=
set.ext $ λ z, by { refine iff.trans _ Set.mem_sUnion.symm, exact
⟨λ ⟨._, ⟨a, rfl, ax⟩, za⟩, ⟨a, ax, za⟩, λ ⟨a, ax, za⟩, ⟨_, ⟨a, rfl, ax⟩, za⟩⟩ }

@[ext] theorem ext {x y : Class.{u}} : (∀ z : Class.{u}, z ∈ x ↔ z ∈ y) → x = y :=
begin
  refine λ h, set.ext (λ z, _),
  change x z ↔ y z,
  rw [←mem_hom_left z x, ←mem_hom_left z y],
  exact h z
end

theorem ext_iff {x y : Class.{u}} : x = y ↔ (∀ z : Class.{u}, z ∈ x ↔ z ∈ y) :=
⟨λ h, by simp [h], ext⟩

theorem coe_mem_powerset {x : Class.{u}} {y : Set.{u}} : powerset x y ↔ ↑y ⊆ x := iff.rfl

@[simp] theorem mem_sUnion {x y : Class.{u}} : y ∈ ⋃₀ x ↔ ∃ z, z ∈ x ∧ y ∈ z :=
begin
  split,
  { rintro ⟨w, rfl, ⟨z, hzx, hwz⟩⟩,
    exact ⟨z, hzx, (mem_hom_left _ _).2 hwz⟩ },
  { rintro ⟨w, hwx, ⟨z, rfl, hwz⟩⟩,
    exact ⟨z, rfl, ⟨w, hwx, hwz⟩⟩ }
end

@[simp] theorem sUnion_empty : ⋃₀ (∅ : Class.{u}) = (∅ : Class.{u}) :=
by { ext, simp }

/-- An induction principle for sets. If every subset of a class is a member, then the class is
  universal. -/
theorem eq_univ_of_powerset_subset {A : Class} (hA : powerset A ⊆ A) : A = univ :=
eq_univ_of_forall begin
  by_contra' hnA,
  exact well_founded.min_mem Set.mem_wf _ hnA (hA $ λ x hx, not_not.1 $
    λ hB, well_founded.not_lt_min Set.mem_wf _ hnA hB $ (mem_hom_right _ _).1 hx)
end

/-- The definite description operator, which is `{x}` if `{y | A y} = {x}` and `∅` otherwise. -/
def iota (A : Class) : Class := ⋃₀ {x | ∀ y, A y ↔ y = x}

theorem iota_val (A : Class) (x : Set) (H : ∀ y, A y ↔ y = x) : iota A = ↑x :=
set.ext $ λ y, ⟨λ ⟨._, ⟨x', rfl, h⟩, yx'⟩, by rwa ←((H x').1 $ (h x').2 rfl),
  λ yx, ⟨_, ⟨x, rfl, H⟩, yx⟩⟩

/-- Unlike the other set constructors, the `iota` definite descriptor
  is a set for any set input, but not constructively so, so there is no
  associated `Class → Set` function. -/
theorem iota_ex (A) : iota.{u} A ∈ univ.{u} :=
mem_univ.2 $ or.elim (classical.em $ ∃ x, ∀ y, A y ↔ y = x)
 (λ ⟨x, h⟩, ⟨x, eq.symm $ iota_val A x h⟩)
 (λ hn, ⟨∅, set.ext (λ z, empty_hom.symm ▸ ⟨false.rec _, λ ⟨._, ⟨x, rfl, H⟩, zA⟩, hn ⟨x, H⟩⟩)⟩)

/-- Function value -/
def fval (F A : Class.{u}) : Class.{u} := iota (λ y, to_Set (λ x, F (Set.pair x y)) A)
infixl ` ′ `:100 := fval

theorem fval_ex (F A : Class.{u}) : F ′ A ∈ univ.{u} := iota_ex _

end Class

namespace Set

@[simp] theorem map_fval {f : Set.{u} → Set.{u}} [H : pSet.definable 1 f]
  {x y : Set.{u}} (h : y ∈ x) :
  (Set.map f x ′ y : Class.{u}) = f y :=
Class.iota_val _ _ (λ z, by { rw [Class.to_Set_of_Set, Class.mem_hom_right, mem_map], exact
  ⟨λ ⟨w, wz, pr⟩, let ⟨wy, fw⟩ := Set.pair_injective pr in by rw[←fw, wy],
  λ e, by { subst e, exact ⟨_, h, rfl⟩ }⟩ })

variables (x : Set.{u}) (h : ∅ ∉ x)

/-- A choice function on the class of nonempty ZFC sets. -/
noncomputable def choice : Set :=
@map (λ y, classical.epsilon (λ z, z ∈ y)) (classical.all_definable _) x

include h
theorem choice_mem_aux (y : Set.{u}) (yx : y ∈ x) : classical.epsilon (λ z : Set.{u}, z ∈ y) ∈ y :=
@classical.epsilon_spec _ (λ z : Set.{u}, z ∈ y) $ classical.by_contradiction $ λ n, h $
by rwa ←((eq_empty y).2 $ λ z zx, n ⟨z, zx⟩)

theorem choice_is_func : is_func x (⋃₀ x) (choice x) :=
(@map_is_func _ (classical.all_definable _) _ _).2 $
  λ y yx, mem_sUnion.2 ⟨y, yx, choice_mem_aux x h y yx⟩

theorem choice_mem (y : Set.{u}) (yx : y ∈ x) : (choice x ′ y : Class.{u}) ∈ (y : Class.{u}) :=
begin
  delta choice,
  rw [map_fval yx, Class.mem_hom_left, Class.mem_hom_right],
  exact choice_mem_aux x h y yx
end

end Set
