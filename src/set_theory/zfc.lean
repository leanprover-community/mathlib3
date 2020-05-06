/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

A model of ZFC in Lean.
-/
import data.set.basic

universes u v

/-- The type of `n`-ary functions `α → α → ... → α`. -/
def arity (α : Type u) : nat → Type u
| 0     := α
| (n+1) := α → arity n

namespace arity

/-- Constant `n`-ary function with value `a`. -/
def const {α : Type u} (a : α) : ∀ n, arity α n
| 0 := a
| (n+1) := λ _, const n

instance arity.inhabited {α n} [inhabited α] : inhabited (arity α n) :=
⟨const (default _) _⟩

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

theorem mk_type_func : Π (x : pSet), mk x.type x.func = x
| ⟨α, A⟩ := rfl

/-- Two pre-sets are extensionally equivalent if every
  element of the first family is extensionally equivalent to
  some element of the second family and vice-versa. -/
def equiv (x y : pSet) : Prop :=
pSet.rec (λα z m ⟨β, B⟩, (∀a, ∃b, m a (B b)) ∧ (∀b, ∃a, m a (B b))) x y

theorem equiv.refl (x) : equiv x x :=
pSet.rec_on x $ λα A IH, ⟨λa, ⟨a, IH a⟩, λa, ⟨a, IH a⟩⟩

theorem equiv.euc {x} : Π {y z}, equiv x y → equiv z y → equiv x z :=
pSet.rec_on x $ λα A IH y, pSet.cases_on y $ λβ B ⟨γ, Γ⟩ ⟨αβ, βα⟩ ⟨γβ, βγ⟩,
⟨λa, let ⟨b, ab⟩ := αβ a, ⟨c, bc⟩ := βγ b in ⟨c, IH a ab bc⟩,
  λc, let ⟨b, cb⟩ := γβ c, ⟨a, ba⟩ := βα b in ⟨a, IH a ba cb⟩⟩

theorem equiv.symm {x y} : equiv x y → equiv y x :=
equiv.euc (equiv.refl y)

theorem equiv.trans {x y z} (h1 : equiv x y) (h2 : equiv y z) : equiv x z :=
equiv.euc h1 (equiv.symm h2)

instance setoid : setoid pSet :=
⟨pSet.equiv, equiv.refl, λx y, equiv.symm, λx y z, equiv.trans⟩

protected def subset : pSet → pSet → Prop
| ⟨α, A⟩ ⟨β, B⟩ := ∀a, ∃b, equiv (A a) (B b)

instance : has_subset pSet := ⟨pSet.subset⟩

theorem equiv.ext : Π (x y : pSet), equiv x y ↔ (x ⊆ y ∧ y ⊆ x)
| ⟨α, A⟩ ⟨β, B⟩ :=
  ⟨λ⟨αβ, βα⟩, ⟨αβ, λb, let ⟨a, h⟩ := βα b in ⟨a, equiv.symm h⟩⟩,
    λ⟨αβ, βα⟩, ⟨αβ, λb, let ⟨a, h⟩ := βα b in ⟨a, equiv.symm h⟩⟩⟩

theorem subset.congr_left : Π {x y z : pSet}, equiv x y → (x ⊆ z ↔ y ⊆ z)
| ⟨α, A⟩ ⟨β, B⟩ ⟨γ, Γ⟩ ⟨αβ, βα⟩ :=
  ⟨λαγ b, let ⟨a, ba⟩ := βα b, ⟨c, ac⟩ := αγ a in ⟨c, equiv.trans (equiv.symm ba) ac⟩,
    λβγ a, let ⟨b, ab⟩ := αβ a, ⟨c, bc⟩ := βγ b in ⟨c, equiv.trans ab bc⟩⟩

theorem subset.congr_right : Π {x y z : pSet}, equiv x y → (z ⊆ x ↔ z ⊆ y)
| ⟨α, A⟩ ⟨β, B⟩ ⟨γ, Γ⟩ ⟨αβ, βα⟩ :=
  ⟨λγα c, let ⟨a, ca⟩ := γα c, ⟨b, ab⟩ := αβ a in ⟨b, equiv.trans ca ab⟩,
    λγβ c, let ⟨b, cb⟩ := γβ c, ⟨a, ab⟩ := βα b in ⟨a, equiv.trans cb (equiv.symm ab)⟩⟩

/-- `x ∈ y` as pre-sets if `x` is extensionally equivalent to a member
  of the family `y`. -/
def mem : pSet → pSet → Prop
| x ⟨β, B⟩ := ∃b, equiv x (B b)
instance : has_mem pSet.{u} pSet.{u} := ⟨mem⟩

theorem mem.mk {α: Type u} (A : α → pSet) (a : α) : A a ∈ mk α A :=
show mem (A a) ⟨α, A⟩, from ⟨a, equiv.refl (A a)⟩

theorem mem.ext : Π {x y : pSet.{u}}, (∀w:pSet.{u}, w ∈ x ↔ w ∈ y) → equiv x y
| ⟨α, A⟩ ⟨β, B⟩ h := ⟨λa, (h (A a)).1 (mem.mk A a),
    λb, let ⟨a, ha⟩ := (h (B b)).2 (mem.mk B b) in ⟨a, equiv.symm ha⟩⟩

theorem mem.congr_right : Π {x y : pSet.{u}}, equiv x y → (∀{w:pSet.{u}}, w ∈ x ↔ w ∈ y)
| ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ w :=
  ⟨λ⟨a, ha⟩, let ⟨b, hb⟩ := αβ a in ⟨b, equiv.trans ha hb⟩,
    λ⟨b, hb⟩, let ⟨a, ha⟩ := βα b in ⟨a, equiv.euc hb ha⟩⟩

theorem equiv_iff_mem {x y : pSet.{u}} : equiv x y ↔ (∀{w:pSet.{u}}, w ∈ x ↔ w ∈ y) :=
⟨mem.congr_right, match x, y with
| ⟨α, A⟩, ⟨β, B⟩, h := ⟨λ a, h.1 (mem.mk A a), λ b,
  let ⟨a, h⟩ := h.2 (mem.mk B b) in ⟨a, h.symm⟩⟩
end⟩

theorem mem.congr_left : Π {x y : pSet.{u}}, equiv x y → (∀{w : pSet.{u}}, x ∈ w ↔ y ∈ w)
| x y h ⟨α, A⟩ := ⟨λ⟨a, ha⟩, ⟨a, equiv.trans (equiv.symm h) ha⟩, λ⟨a, ha⟩, ⟨a, equiv.trans h ha⟩⟩

/-- Convert a pre-set to a `set` of pre-sets. -/
def to_set (u : pSet.{u}) : set pSet.{u} := {x | x ∈ u}

/-- Two pre-sets are equivalent iff they have the same members. -/
theorem equiv.eq {x y : pSet} : equiv x y ↔ to_set x = to_set y :=
equiv_iff_mem.trans set.ext_iff.symm

instance : has_coe pSet (set pSet) := ⟨to_set⟩

/-- The empty pre-set -/
protected def empty : pSet := ⟨ulift empty, λe, match e with end⟩

instance : has_emptyc pSet := ⟨pSet.empty⟩

instance : inhabited pSet := ⟨∅⟩

theorem mem_empty (x : pSet.{u}) : x ∉ (∅:pSet.{u}) := λe, match e with end

/-- Insert an element into a pre-set -/
protected def insert : pSet → pSet → pSet
| u ⟨α, A⟩ := ⟨option α, λo, option.rec u A o⟩

instance : has_insert pSet pSet := ⟨pSet.insert⟩

/-- The n-th von Neumann ordinal -/
def of_nat : ℕ → pSet
| 0     := ∅
| (n+1) := pSet.insert (of_nat n) (of_nat n)

/-- The von Neumann ordinal ω -/
def omega : pSet := ⟨ulift ℕ, λn, of_nat n.down⟩

/-- The separation operation `{x ∈ a | p x}` -/
protected def sep (p : set pSet) : pSet → pSet
| ⟨α, A⟩ := ⟨{a // p (A a)}, λx, A x.1⟩

instance : has_sep pSet pSet := ⟨pSet.sep⟩

/-- The powerset operator -/
def powerset : pSet → pSet
| ⟨α, A⟩ := ⟨set α, λp, ⟨{a // p a}, λx, A x.1⟩⟩

theorem mem_powerset : Π {x y : pSet}, y ∈ powerset x ↔ y ⊆ x
| ⟨α, A⟩ ⟨β, B⟩ := ⟨λ⟨p, e⟩, (subset.congr_left e).2 $ λ⟨a, pa⟩, ⟨a, equiv.refl (A a)⟩,
  λβα, ⟨{a | ∃b, equiv (B b) (A a)}, λb, let ⟨a, ba⟩ := βα b in ⟨⟨a, b, ba⟩, ba⟩,
    λ⟨a, b, ba⟩, ⟨b, ba⟩⟩⟩

/-- The set union operator -/
def Union : pSet → pSet
| ⟨α, A⟩ := ⟨Σx, (A x).type, λ⟨x, y⟩, (A x).func y⟩

theorem mem_Union : Π {x y : pSet.{u}}, y ∈ Union x ↔ ∃ z:pSet.{u}, ∃_:z ∈ x, y ∈ z
| ⟨α, A⟩ y :=
  ⟨λ⟨⟨a, c⟩, (e : equiv y ((A a).func c))⟩,
    have func (A a) c ∈ mk (A a).type (A a).func, from mem.mk (A a).func c,
    ⟨_, mem.mk _ _, (mem.congr_left e).2 (by rwa mk_type_func at this)⟩,
  λ⟨⟨β, B⟩, ⟨a, (e:equiv (mk β B) (A a))⟩, ⟨b, yb⟩⟩,
    by rw ←(mk_type_func (A a)) at e; exact
    let ⟨βt, tβ⟩ := e, ⟨c, bc⟩ := βt b in ⟨⟨a, c⟩, equiv.trans yb bc⟩⟩

/-- The image of a function -/
def image (f : pSet.{u} → pSet.{u}) : pSet.{u} → pSet
| ⟨α, A⟩ := ⟨α, λa, f (A a)⟩

theorem mem_image {f : pSet.{u} → pSet.{u}} (H : ∀{x y}, equiv x y → equiv (f x) (f y)) :
  Π {x y : pSet.{u}}, y ∈ image f x ↔ ∃z ∈ x, equiv y (f z)
| ⟨α, A⟩ y := ⟨λ⟨a, ya⟩, ⟨A a, mem.mk A a, ya⟩, λ⟨z, ⟨a, za⟩, yz⟩, ⟨a, equiv.trans yz (H za)⟩⟩

/-- Universe lift operation -/
protected def lift : pSet.{u} → pSet.{max u v}
| ⟨α, A⟩ := ⟨ulift α, λ⟨x⟩, lift (A x)⟩

/-- Embedding of one universe in another -/
def embed : pSet.{max (u+1) v} := ⟨ulift.{v u+1} pSet, λ⟨x⟩, pSet.lift.{u (max (u+1) v)} x⟩

theorem lift_mem_embed : Π (x : pSet.{u}), pSet.lift.{u (max (u+1) v)} x ∈ embed.{u v} :=
λx, ⟨⟨x⟩, equiv.refl _⟩

/-- Function equivalence is defined so that `f ~ g` iff
  `∀ x y, x ~ y → f x ~ g y`. This extends to equivalence of n-ary
  functions. -/
def arity.equiv : Π {n}, arity pSet.{u} n → arity pSet.{u} n → Prop
| 0     a b := equiv a b
| (n+1) a b := ∀ x y, equiv x y → arity.equiv (a x) (b y)

lemma arity.equiv_const {a : pSet.{u}} : ∀ n, arity.equiv (arity.const a n) (arity.const a n)
| 0 := equiv.refl _
| (n+1) := λ x y h, arity.equiv_const _

/-- `resp n` is the collection of n-ary functions on `pSet` that respect
  equivalence, i.e. when the inputs are equivalent the output is as well. -/
def resp (n) := { x : arity pSet.{u} n // arity.equiv x x }

instance resp.inhabited {n} : inhabited (resp n) :=
⟨⟨arity.const (default _) _, arity.equiv_const _⟩⟩

def resp.f {n} (f : resp (n+1)) (x : pSet) : resp n :=
⟨f.1 x, f.2 _ _ $ equiv.refl x⟩

def resp.equiv {n} (a b : resp n) : Prop := arity.equiv a.1 b.1

theorem resp.refl {n} (a : resp n) : resp.equiv a a := a.2

theorem resp.euc : Π {n} {a b c : resp n}, resp.equiv a b → resp.equiv c b → resp.equiv a c
| 0     a b c hab hcb := equiv.euc hab hcb
| (n+1) a b c hab hcb := by delta resp.equiv; simp [arity.equiv]; exact λx y h,
  @resp.euc n (a.f x) (b.f y) (c.f y) (hab _ _ h) (hcb _ _ $ equiv.refl y)

instance resp.setoid {n} : setoid (resp n) :=
⟨resp.equiv, resp.refl, λx y h, resp.euc (resp.refl y) h, λx y z h1 h2, resp.euc h1 $ resp.euc (resp.refl z) h2⟩

end pSet

/-- The ZFC universe of sets consists of the type of pre-sets,
  quotiented by extensional equivalence. -/
def Set : Type (u+1) := quotient pSet.setoid.{u}

namespace pSet

namespace resp

def eval_aux : Π {n}, { f : resp n → arity Set.{u} n // ∀ (a b : resp n), resp.equiv a b → f a = f b }
| 0     := ⟨λa, ⟦a.1⟧, λa b h, quotient.sound h⟩
| (n+1) := let F : resp (n + 1) → arity Set (n + 1) := λa, @quotient.lift _ _ pSet.setoid
    (λx, eval_aux.1 (a.f x)) (λb c h, eval_aux.2 _ _ (a.2 _ _ h)) in
  ⟨F, λb c h, funext $ @quotient.ind _ _ (λq, F b q = F c q) $ λz,
  eval_aux.2 (resp.f b z) (resp.f c z) (h _ _ (equiv.refl z))⟩

/-- An equivalence-respecting function yields an n-ary Set function. -/
def eval (n) : resp n → arity Set.{u} n := eval_aux.1

theorem eval_val {n f x} : (@eval (n+1) f : Set → arity Set n) ⟦x⟧ = eval n (resp.f f x) := rfl

end resp

/-- A set function is "definable" if it is the image of some n-ary pre-set
  function. This isn't exactly definability, but is useful as a sufficient
  condition for functions that have a computable image. -/
@[class] inductive definable (n) : arity Set.{u} n → Type (u+1)
| mk (f) : definable (resp.eval _ f)
attribute [instance] definable.mk

def definable.eq_mk {n} (f) : Π {s : arity Set.{u} n} (H : resp.eval _ f = s), definable n s
| ._ rfl := ⟨f⟩

def definable.resp {n} : Π (s : arity Set.{u} n) [definable n s], resp n
| ._ ⟨f⟩ := f

theorem definable.eq {n} : Π (s : arity Set.{u} n) [H : definable n s], (@definable.resp n s H).eval _ = s
| ._ ⟨f⟩ := rfl

end pSet

namespace classical
open pSet

noncomputable def all_definable : Π {n} (F : arity Set.{u} n), definable n F
| 0     F := let p := @quotient.exists_rep pSet _ F in
              definable.eq_mk ⟨some p, equiv.refl _⟩ (some_spec p)
| (n+1) (F : arity Set.{u} (n + 1)) := begin
    have I := λx, (all_definable (F x)),
    refine definable.eq_mk ⟨λx:pSet, (@definable.resp _ _ (I ⟦x⟧)).1, _⟩ _,
    { dsimp [arity.equiv],
      introsI x y h,
      rw @quotient.sound pSet _ _ _ h,
      exact (definable.resp (F ⟦y⟧)).2 },
    exact funext (λq, quotient.induction_on q $ λx,
      by simp [resp.eval_val, resp.f]; exact @definable.eq _ (F ⟦x⟧) (I ⟦x⟧))
  end

end classical

namespace Set
open pSet

def mk : pSet → Set := quotient.mk

@[simp] theorem mk_eq (x : pSet) : @eq Set ⟦x⟧ (mk x) := rfl

@[simp] lemma eval_mk {n f x} :
  (@resp.eval (n+1) f : Set → arity Set n) (mk x) = resp.eval n (resp.f f x) :=
rfl

def mem : Set → Set → Prop :=
quotient.lift₂ pSet.mem
  (λx y x' y' hx hy, propext (iff.trans (mem.congr_left hx) (mem.congr_right hy)))

instance : has_mem Set Set := ⟨mem⟩

/-- Convert a ZFC set into a `set` of sets -/
def to_set (u : Set.{u}) : set Set.{u} := {x | x ∈ u}

protected def subset (x y : Set.{u}) :=
∀ ⦃z⦄, z ∈ x → z ∈ y

instance has_subset : has_subset Set :=
⟨Set.subset⟩

theorem subset_iff : Π (x y : pSet), mk x ⊆ mk y ↔ x ⊆ y
| ⟨α, A⟩ ⟨β, B⟩ := ⟨λh a, @h ⟦A a⟧ (mem.mk A a),
  λh z, quotient.induction_on z (λz ⟨a, za⟩, let ⟨b, ab⟩ := h a in ⟨b, equiv.trans za ab⟩)⟩

theorem ext {x y : Set.{u}} : (∀z:Set.{u}, z ∈ x ↔ z ∈ y) → x = y :=
quotient.induction_on₂ x y (λu v h, quotient.sound (mem.ext (λw, h ⟦w⟧)))

theorem ext_iff {x y : Set.{u}} : (∀z:Set.{u}, z ∈ x ↔ z ∈ y) ↔ x = y :=
⟨ext, λh, by simp [h]⟩

/-- The empty set -/
def empty : Set := mk ∅
instance : has_emptyc Set := ⟨empty⟩
instance : inhabited Set := ⟨∅⟩

@[simp] theorem mem_empty (x) : x ∉ (∅:Set.{u}) :=
quotient.induction_on x pSet.mem_empty

theorem eq_empty (x : Set.{u}) : x = ∅ ↔ ∀y:Set.{u}, y ∉ x :=
⟨λh, by rw h; exact mem_empty,
λh, ext (λy, ⟨λyx, absurd yx (h y), λy0, absurd y0 (mem_empty _)⟩)⟩

/-- `insert x y` is the set `{x} ∪ y` -/
protected def insert : Set → Set → Set :=
resp.eval 2 ⟨pSet.insert, λu v uv ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩,
  ⟨λo, match o with
   | some a := let ⟨b, hb⟩ := αβ a in ⟨some b, hb⟩
   | none := ⟨none, uv⟩
   end, λo, match o with
   | some b := let ⟨a, ha⟩ := βα b in ⟨some a, ha⟩
   | none := ⟨none, uv⟩
   end⟩⟩

instance : has_insert Set Set := ⟨Set.insert⟩

@[simp] theorem mem_insert {x y z : Set.{u}} : x ∈ insert y z ↔ x = y ∨ x ∈ z :=
quotient.induction_on₃ x y z
 (λx y ⟨α, A⟩, show x ∈ pSet.mk (option α) (λo, option.rec y A o) ↔
    mk x = mk y ∨ x ∈ pSet.mk α A, from
  ⟨λm, match m with
  | ⟨some a, ha⟩ := or.inr ⟨a, ha⟩
  | ⟨none, h⟩ := or.inl (quotient.sound h)
  end, λm, match m with
  | or.inr ⟨a, ha⟩ := ⟨some a, ha⟩
  | or.inl h := ⟨none, quotient.exact h⟩
  end⟩)

@[simp] theorem mem_singleton {x y : Set.{u}} : x ∈ @singleton Set.{u} Set.{u} _ _ y ↔ x = y :=
iff.trans mem_insert ⟨λo, or.rec (λh, h) (λn, absurd n (mem_empty _)) o, or.inl⟩

@[simp] theorem mem_singleton' {x y : Set.{u}} : x ∈ @insert Set.{u} Set.{u} _ y ∅ ↔ x = y := mem_singleton

@[simp] theorem mem_pair {x y z : Set.{u}} : x ∈ ({y, z} : Set) ↔ x = y ∨ x = z :=
iff.trans mem_insert $ iff.trans or.comm $ let m := @mem_singleton x y in ⟨or.imp_left m.1, or.imp_left m.2⟩

/-- `omega` is the first infinite von Neumann ordinal -/
def omega : Set := mk omega

@[simp] theorem omega_zero : ∅ ∈ omega :=
show pSet.mem ∅ pSet.omega, from ⟨⟨0⟩, equiv.refl _⟩

@[simp] theorem omega_succ {n} : n ∈ omega.{u} → insert n n ∈ omega.{u} :=
quotient.induction_on n (λx ⟨⟨n⟩, h⟩, ⟨⟨n+1⟩,
  have Set.insert ⟦x⟧ ⟦x⟧ = Set.insert ⟦of_nat n⟧ ⟦of_nat n⟧, by rw (@quotient.sound pSet _ _ _ h),
  quotient.exact this⟩)

/-- `{x ∈ a | p x}` is the set of elements in `a` satisfying `p` -/
protected def sep (p : Set → Prop) : Set → Set :=
resp.eval 1 ⟨pSet.sep (λy, p ⟦y⟧), λ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩,
  ⟨λ⟨a, pa⟩, let ⟨b, hb⟩ := αβ a in ⟨⟨b, by rwa ←(@quotient.sound pSet _ _ _ hb)⟩, hb⟩,
   λ⟨b, pb⟩, let ⟨a, ha⟩ := βα b in ⟨⟨a, by rwa (@quotient.sound pSet _ _ _ ha)⟩, ha⟩⟩⟩

instance : has_sep Set Set := ⟨Set.sep⟩

@[simp] theorem mem_sep {p : Set.{u} → Prop} {x y : Set.{u}} : y ∈ {y ∈ x | p y} ↔ y ∈ x ∧ p y :=
quotient.induction_on₂ x y (λ⟨α, A⟩ y,
  ⟨λ⟨⟨a, pa⟩, h⟩, ⟨⟨a, h⟩, by rw (@quotient.sound pSet _ _ _ h); exact pa⟩,
  λ⟨⟨a, h⟩, pa⟩, ⟨⟨a, by rw ←(@quotient.sound pSet _ _ _ h); exact pa⟩, h⟩⟩)

/-- The powerset operation, the collection of subsets of a set -/
def powerset : Set → Set :=
resp.eval 1 ⟨powerset, λ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩,
  ⟨λp, ⟨{b | ∃a, p a ∧ equiv (A a) (B b)},
    λ⟨a, pa⟩, let ⟨b, ab⟩ := αβ a in ⟨⟨b, a, pa, ab⟩, ab⟩,
    λ⟨b, a, pa, ab⟩, ⟨⟨a, pa⟩, ab⟩⟩,
   λq, ⟨{a | ∃b, q b ∧ equiv (A a) (B b)},
    λ⟨a, b, qb, ab⟩, ⟨⟨b, qb⟩, ab⟩,
    λ⟨b, qb⟩, let ⟨a, ab⟩ := βα b in ⟨⟨a, b, qb, ab⟩, ab⟩⟩⟩⟩

@[simp] theorem mem_powerset {x y : Set} : y ∈ powerset x ↔ y ⊆ x :=
quotient.induction_on₂ x y (λ⟨α, A⟩ ⟨β, B⟩,
  show (⟨β, B⟩ : pSet) ∈ (pSet.powerset ⟨α, A⟩) ↔ _,
    by simp [mem_powerset, subset_iff])

theorem Union_lem {α β : Type u} (A : α → pSet) (B : β → pSet)
  (αβ : ∀a, ∃b, equiv (A a) (B b)) : ∀a, ∃b, (equiv ((Union ⟨α, A⟩).func a) ((Union ⟨β, B⟩).func b))
| ⟨a, c⟩ := let ⟨b, hb⟩ := αβ a in
  begin
    induction ea : A a with γ Γ,
    induction eb : B b with δ Δ,
    rw [ea, eb] at hb,
    cases hb with γδ δγ,
    exact
    let c : type (A a) := c, ⟨d, hd⟩ := γδ (by rwa ea at c) in
    have equiv ((A a).func c) ((B b).func (eq.rec d (eq.symm eb))), from
    match A a, B b, ea, eb, c, d, hd with ._, ._, rfl, rfl, x, y, hd := hd end,
    ⟨⟨b, eq.rec d (eq.symm eb)⟩, this⟩
  end

/-- The union operator, the collection of elements of elements of a set -/
def Union : Set → Set :=
resp.eval 1 ⟨pSet.Union, λ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩,
  ⟨Union_lem A B αβ, λa, exists.elim (Union_lem B A (λb,
    exists.elim (βα b) (λc hc, ⟨c, equiv.symm hc⟩)) a) (λb hb, ⟨b, equiv.symm hb⟩)⟩⟩

notation `⋃` := Union

@[simp] theorem mem_Union {x y : Set.{u}} : y ∈ Union x ↔ ∃ z ∈ x, y ∈ z :=
quotient.induction_on₂ x y (λx y, iff.trans mem_Union
  ⟨λ⟨z, h⟩, ⟨⟦z⟧, h⟩, λ⟨z, h⟩, quotient.induction_on z (λz h, ⟨z, h⟩) h⟩)

@[simp] theorem Union_singleton {x : Set.{u}} : Union {x} = x :=
ext $ λy, by simp; exact ⟨λ⟨z, zx, yz⟩, by subst z; exact yz, λyx, ⟨x, by simp, yx⟩⟩

theorem singleton_inj {x y : Set.{u}} (H : ({x} : Set) = {y}) : x = y :=
let this := congr_arg Union H in by rwa [Union_singleton, Union_singleton] at this

/-- The binary union operation -/
protected def union (x y : Set.{u}) : Set.{u} := ⋃ {x, y}

/-- The binary intersection operation -/
protected def inter (x y : Set.{u}) : Set.{u} := {z ∈ x | z ∈ y}

/-- The set difference operation -/
protected def diff (x y : Set.{u}) : Set.{u} := {z ∈ x | z ∉ y}

instance : has_union Set := ⟨Set.union⟩
instance : has_inter Set := ⟨Set.inter⟩
instance : has_sdiff Set := ⟨Set.diff⟩

@[simp] theorem mem_union {x y z : Set.{u}} : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y :=
iff.trans mem_Union
 ⟨λ⟨w, wxy, zw⟩, match mem_pair.1 wxy with
  | or.inl wx := or.inl (by rwa ←wx)
  | or.inr wy := or.inr (by rwa ←wy)
  end, λzxy, match zxy with
  | or.inl zx := ⟨x, mem_pair.2 (or.inl rfl), zx⟩
  | or.inr zy := ⟨y, mem_pair.2 (or.inr rfl), zy⟩
  end⟩

@[simp] theorem mem_inter {x y z : Set.{u}} : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y :=
@@mem_sep (λz:Set.{u}, z ∈ y)

@[simp] theorem mem_diff {x y z : Set.{u}} : z ∈ x \ y ↔ z ∈ x ∧ z ∉ y :=
@@mem_sep (λz:Set.{u}, z ∉ y)

theorem induction_on {p : Set → Prop} (x) (h : ∀x, (∀y ∈ x, p y) → p x) : p x :=
quotient.induction_on x $ λu, pSet.rec_on u $ λα A IH, h _ $ λy,
show @has_mem.mem _ _ Set.has_mem y ⟦⟨α, A⟩⟧ → p y, from
quotient.induction_on y (λv ⟨a, ha⟩, by rw (@quotient.sound pSet _ _ _ ha); exact IH a)

theorem regularity (x : Set.{u}) (h : x ≠ ∅) : ∃ y ∈ x, x ∩ y = ∅ :=
classical.by_contradiction $ λne, h $ (eq_empty x).2 $ λy,
induction_on y $ λz (IH : ∀w:Set.{u}, w ∈ z → w ∉ x), show z ∉ x, from λzx,
ne ⟨z, zx, (eq_empty _).2 (λw wxz, let ⟨wx, wz⟩ := mem_inter.1 wxz in IH w wz wx)⟩

/-- The image of a (definable) set function -/
def image (f : Set → Set) [H : definable 1 f] : Set → Set :=
let r := @definable.resp 1 f _ in
resp.eval 1 ⟨image r.1, λx y e, mem.ext $ λz,
  iff.trans (mem_image r.2) $ iff.trans (by exact
   ⟨λ⟨w, h1, h2⟩, ⟨w, (mem.congr_right e).1 h1, h2⟩,
    λ⟨w, h1, h2⟩, ⟨w, (mem.congr_right e).2 h1, h2⟩⟩) $
  iff.symm (mem_image r.2)⟩

theorem image.mk : Π (f : Set.{u} → Set.{u}) [H : definable 1 f] (x) {y} (h : y ∈ x), f y ∈ @image f H x
| ._ ⟨F⟩ x y := quotient.induction_on₂ x y $ λ⟨α, A⟩ y ⟨a, ya⟩, ⟨a, F.2 _ _ ya⟩

@[simp] theorem mem_image : Π {f : Set.{u} → Set.{u}} [H : definable 1 f] {x y : Set.{u}}, y ∈ @image f H x ↔ ∃z ∈ x, f z = y
| ._ ⟨F⟩ x y := quotient.induction_on₂ x y $ λ⟨α, A⟩ y,
  ⟨λ⟨a, ya⟩, ⟨⟦A a⟧, mem.mk A a, eq.symm $ quotient.sound ya⟩,
  λ⟨z, hz, e⟩, e ▸ image.mk _ _ hz⟩

/-- Kuratowski ordered pair -/
def pair (x y : Set.{u}) : Set.{u} := {{x}, {x, y}}

/-- A subset of pairs `{(a, b) ∈ x × y | p a b}` -/
def pair_sep (p : Set.{u} → Set.{u} → Prop) (x y : Set.{u}) : Set.{u} :=
{z ∈ powerset (powerset (x ∪ y)) | ∃a ∈ x, ∃b ∈ y, z = pair a b ∧ p a b}

@[simp] theorem mem_pair_sep {p} {x y z : Set.{u}} : z ∈ pair_sep p x y ↔ ∃a ∈ x, ∃b ∈ y, z = pair a b ∧ p a b := by
refine iff.trans mem_sep ⟨and.right, λe, ⟨_, e⟩⟩; exact
let ⟨a, ax, b, bY, ze, pab⟩ := e in by rw ze; exact
mem_powerset.2 (λu uz, mem_powerset.2 $ (mem_pair.1 uz).elim
  (λua, by rw ua; exact λv vu, by rw mem_singleton.1 vu; exact mem_union.2 (or.inl ax))
  (λuab, by rw uab; exact λv vu, (mem_pair.1 vu).elim
    (λva, by rw va; exact mem_union.2 (or.inl ax))
    (λvb, by rw vb; exact mem_union.2 (or.inr bY))))

theorem pair_inj {x y x' y' : Set.{u}} (H : pair x y = pair x' y') : x = x' ∧ y = y' := begin
  have ae := ext_iff.2 H,
  simp [pair] at ae,
  have : x = x',
  { cases (ae {x}).1 (by simp) with h h,
    { exact singleton_inj h },
    { have m : x' ∈ ({x} : Set),
      { rw h, simp },
      simp at m, simp [*] } },
  subst x',
  have he : y = x → y = y',
  { intro yx, subst y,
    cases (ae {x, y'}).2 (by simp) with xy'x xy'xx,
    { have y'x : y' ∈ ({x} : Set) := by rw ← xy'x; simp,
      simp at y'x, simp [*] },
    { have yxx := (ext_iff.2 xy'xx y').1 (by simp),
      simp at yxx, subst y' } },
  have xyxy' := (ae {x, y}).1 (by simp),
  cases xyxy' with xyx xyy',
  { have yx := (ext_iff.2 xyx y).1 (by simp),
    simp at yx, simp [he yx] },
  { have yxy' := (ext_iff.2 xyy' y).1 (by simp),
    simp at yxy',
    cases yxy' with yx yy',
    { simp [he yx] },
    { simp [yy'] } }
end

/-- The cartesian product, `{(a, b) | a ∈ x, b ∈ y}` -/
def prod : Set.{u} → Set.{u} → Set.{u} := pair_sep (λa b, true)

@[simp] theorem mem_prod {x y z : Set.{u}} : z ∈ prod x y ↔ ∃a ∈ x, ∃b ∈ y, z = pair a b :=
by simp [prod]

@[simp] theorem pair_mem_prod {x y a b : Set.{u}} : pair a b ∈ prod x y ↔ a ∈ x ∧ b ∈ y :=
⟨λh, let ⟨a', a'x, b', b'y, e⟩ := mem_prod.1 h in
  match a', b', pair_inj e, a'x, b'y with ._, ._, ⟨rfl, rfl⟩, ax, bY := ⟨ax, bY⟩ end,
λ⟨ax, bY⟩, by simp; exact ⟨a, ax, b, bY, rfl⟩⟩

/-- `is_func x y f` is the assertion `f : x → y` where `f` is a ZFC function
  (a set of ordered pairs) -/
def is_func (x y f : Set.{u}) : Prop :=
f ⊆ prod x y ∧ ∀z:Set.{u}, z ∈ x → ∃! w, pair z w ∈ f

/-- `funs x y` is `y ^ x`, the set of all set functions `x → y` -/
def funs (x y : Set.{u}) : Set.{u} :=
{f ∈ powerset (prod x y) | is_func x y f}

@[simp] theorem mem_funs {x y f : Set.{u}} : f ∈ funs x y ↔ is_func x y f :=
by simp [funs]; exact and_iff_right_of_imp and.left

-- TODO(Mario): Prove this computably
noncomputable instance map_definable_aux (f : Set → Set) [H : definable 1 f] : definable 1 (λy, pair y (f y)) :=
@classical.all_definable 1 _

/-- Graph of a function: `map f x` is the ZFC function which maps `a ∈ x` to `f a` -/
noncomputable def map (f : Set → Set) [H : definable 1 f] : Set → Set :=
image (λy, pair y (f y))

@[simp] theorem mem_map {f : Set → Set} [H : definable 1 f] {x y : Set} : y ∈ map f x ↔ ∃z ∈ x, pair z (f z) = y :=
mem_image

theorem map_unique {f : Set.{u} → Set.{u}} [H : definable 1 f] {x z : Set.{u}} (zx : z ∈ x) : ∃! w, pair z w ∈ map f x :=
⟨f z, image.mk _ _ zx, λy yx, let ⟨w, wx, we⟩ := mem_image.1 yx, ⟨wz, fy⟩ := pair_inj we in by rw[←fy, wz]⟩

@[simp] theorem map_is_func {f : Set → Set} [H : definable 1 f] {x y : Set} : is_func x y (map f x) ↔ ∀z ∈ x, f z ∈ y :=
⟨λ⟨ss, h⟩ z zx, let ⟨t, t1, t2⟩ := h z zx in by rw (t2 (f z) (image.mk _ _ zx)); exact (pair_mem_prod.1 (ss t1)).right,
λh, ⟨λy yx, let ⟨z, zx, ze⟩ := mem_image.1 yx in by rw ←ze; exact pair_mem_prod.2 ⟨zx, h z zx⟩,
     λz, map_unique⟩⟩

end Set

def Class := set Set

namespace Class

instance : has_subset Class     := ⟨set.subset⟩
instance : has_sep Set Class    := ⟨set.sep⟩
instance : has_emptyc Class     := ⟨λ a, false⟩
instance : inhabited Class      := ⟨∅⟩
instance : has_insert Set Class := ⟨set.insert⟩
instance : has_union Class      := ⟨set.union⟩
instance : has_inter Class      := ⟨set.inter⟩
instance : has_neg Class        := ⟨set.compl⟩
instance : has_sdiff Class      := ⟨set.diff⟩

/-- Coerce a set into a class -/
def of_Set (x : Set.{u}) : Class.{u} := {y | y ∈ x}
instance : has_coe Set Class := ⟨of_Set⟩

/-- The universal class -/
def univ : Class := set.univ

/-- Assert that `A` is a set satisfying `p` -/
def to_Set (p : Set.{u} → Prop) (A : Class.{u}) : Prop := ∃x, ↑x = A ∧ p x

/-- `A ∈ B` if `A` is a set which is a member of `B` -/
protected def mem (A B : Class.{u}) : Prop := to_Set.{u} B A
instance : has_mem Class Class := ⟨Class.mem⟩

theorem mem_univ {A : Class.{u}} : A ∈ univ.{u} ↔ ∃ x : Set.{u}, ↑x = A :=
exists_congr $ λx, and_true _

/-- Convert a conglomerate (a collection of classes) into a class -/
def Cong_to_Class (x : set Class.{u}) : Class.{u} := {y | ↑y ∈ x}

/-- Convert a class into a conglomerate (a collection of classes) -/
def Class_to_Cong (x : Class.{u}) : set Class.{u} := {y | y ∈ x}

/-- The power class of a class is the class of all subclasses that are sets -/
def powerset (x : Class) : Class := Cong_to_Class (set.powerset x)

/-- The union of a class is the class of all members of sets in the class -/
def Union (x : Class) : Class := set.sUnion (Class_to_Cong x)
notation `⋃` := Union

theorem of_Set.inj {x y : Set.{u}} (h : (x : Class.{u}) = y) : x = y :=
Set.ext $ λz, by change (x : Class.{u}) z ↔ (y : Class.{u}) z; simp [*]

@[simp] theorem to_Set_of_Set (p : Set.{u} → Prop) (x : Set.{u}) : to_Set p x ↔ p x :=
⟨λ⟨y, yx, py⟩, by rwa of_Set.inj yx at py, λpx, ⟨x, rfl, px⟩⟩

@[simp] theorem mem_hom_left (x : Set.{u}) (A : Class.{u}) : (x : Class.{u}) ∈ A ↔ A x :=
to_Set_of_Set _ _

@[simp] theorem mem_hom_right (x y : Set.{u}) : (y : Class.{u}) x ↔ x ∈ y := iff.rfl

@[simp] theorem subset_hom (x y : Set.{u}) : (x : Class.{u}) ⊆ y ↔ x ⊆ y := iff.rfl

@[simp] theorem sep_hom (p : Set.{u} → Prop) (x : Set.{u}) : (↑{y ∈ x | p y} : Class.{u}) = {y ∈ x | p y} :=
set.ext $ λy, Set.mem_sep

@[simp] theorem empty_hom : ↑(∅ : Set.{u}) = (∅ : Class.{u}) :=
set.ext $ λy, show _ ↔ false, by simp; exact Set.mem_empty y

@[simp] theorem insert_hom (x y : Set.{u}) : (@insert Set.{u} Class.{u} _ x y) = ↑(insert x y) :=
set.ext $ λz, iff.symm Set.mem_insert

@[simp] theorem union_hom (x y : Set.{u}) : (x : Class.{u}) ∪ y = (x ∪ y : Set.{u}) :=
set.ext $ λz, iff.symm Set.mem_union

@[simp] theorem inter_hom (x y : Set.{u}) : (x : Class.{u}) ∩ y = (x ∩ y : Set.{u}) :=
set.ext $ λz, iff.symm Set.mem_inter

@[simp] theorem diff_hom (x y : Set.{u}) : (x : Class.{u}) \ y = (x \ y : Set.{u}) :=
set.ext $ λz, iff.symm Set.mem_diff

@[simp] theorem powerset_hom (x : Set.{u}) : powerset.{u} x = Set.powerset x :=
set.ext $ λz, iff.symm Set.mem_powerset

@[simp] theorem Union_hom (x : Set.{u}) : Union.{u} x = Set.Union x :=
set.ext $ λz, by refine iff.trans _ (iff.symm Set.mem_Union); exact
⟨λ⟨._, ⟨a, rfl, ax⟩, za⟩, ⟨a, ax, za⟩, λ⟨a, ax, za⟩, ⟨_, ⟨a, rfl, ax⟩, za⟩⟩

/-- The definite description operator, which is {x} if `{a | p a} = {x}`
  and ∅ otherwise -/
def iota (p : Set → Prop) : Class := Union {x | ∀y, p y ↔ y = x}

theorem iota_val (p : Set → Prop) (x : Set) (H : ∀y, p y ↔ y = x) : iota p = ↑x :=
set.ext $ λy, ⟨λ⟨._, ⟨x', rfl, h⟩, yx'⟩, by rwa ←((H x').1 $ (h x').2 rfl), λyx, ⟨_, ⟨x, rfl, H⟩, yx⟩⟩

/-- Unlike the other set constructors, the `iota` definite descriptor
  is a set for any set input, but not constructively so, so there is no
  associated `(Set → Prop) → Set` function. -/
theorem iota_ex (p) : iota.{u} p ∈ univ.{u} :=
mem_univ.2 $ or.elim (classical.em $ ∃x, ∀y, p y ↔ y = x)
 (λ⟨x, h⟩, ⟨x, eq.symm $ iota_val p x h⟩)
 (λhn, ⟨∅, by simp; exact set.ext (λz, ⟨false.rec _, λ⟨._, ⟨x, rfl, H⟩, zA⟩, hn ⟨x, H⟩⟩)⟩)

/-- Function value -/
def fval (F A : Class.{u}) : Class.{u} := iota (λy, to_Set (λx, F (Set.pair x y)) A)
infixl `′`:100 := fval

theorem fval_ex (F A : Class.{u}) : F ′ A ∈ univ.{u} := iota_ex _

end Class

namespace Set

@[simp] theorem map_fval {f : Set.{u} → Set.{u}} [H : pSet.definable 1 f] {x y : Set.{u}} (h : y ∈ x) :
  (Set.map f x ′ y : Class.{u}) = f y :=
Class.iota_val _ _ (λz, by simp; exact
  ⟨λ⟨w, wz, pr⟩, let ⟨wy, fw⟩ := Set.pair_inj pr in by rw[←fw, wy],
  λe, by cases e; exact ⟨_, h, rfl⟩⟩)

variables (x : Set.{u}) (h : ∅ ∉ x)

/-- A choice function on the set of nonempty sets `x` -/
noncomputable def choice : Set := @map (λy, classical.epsilon (λz, z ∈ y)) (classical.all_definable _) x

include h
theorem choice_mem_aux (y : Set.{u}) (yx : y ∈ x) : classical.epsilon (λz:Set.{u}, z ∈ y) ∈ y :=
@classical.epsilon_spec _ (λz:Set.{u}, z ∈ y) $ classical.by_contradiction $ λn, h $
by rwa ←((eq_empty y).2 $ λz zx, n ⟨z, zx⟩)

theorem choice_is_func : is_func x (Union x) (choice x) :=
(@map_is_func _ (classical.all_definable _) _ _).2 $ λy yx, by simp; exact ⟨y, yx, choice_mem_aux x h y yx⟩

theorem choice_mem (y : Set.{u}) (yx : y ∈ x) : (choice x ′ y : Class.{u}) ∈ (y : Class.{u}) :=
by delta choice; rw map_fval yx; simp [choice_mem_aux x h y yx]

end Set
