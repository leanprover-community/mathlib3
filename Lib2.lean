import order.basic
import data.nat.basic

namespace prisoner

def name := string

inductive expr
| app : expr → expr → expr
| abs : option name → expr → expr
| free : name → expr
| con : string → expr
| bound : ℕ → expr

open expr

@[pattern] def Uapp (f : string) (x : expr) : expr := app (con f) x
@[pattern] def Bapp (f : string) (x y : expr) : expr := app (app (con f) x) y
@[pattern] def And (x y : expr) : expr := Bapp "and" x y
@[pattern] def Or (x y : expr) : expr := Bapp "or" x y
@[pattern] def Imp (x y : expr) : expr := Bapp "imp" x y
@[pattern] def Not (x : expr) : expr := Uapp "not" x
@[pattern] def Eq (x y : expr) : expr := Bapp "eq" x y
@[pattern] def «Forall» (x) (y) : expr := Uapp "forall" (abs x y)
@[pattern] def «Exists» (x) (y) : expr := Uapp "exists" (abs x y)

def name_to (n : name) : ℕ → expr → expr
| i (app f x) := app (name_to i f) (name_to i x)
| i (abs nm b) := abs nm (name_to (i+1) b)
| i t@(free m) := if m = n then bound i else t
| i t := t

lemma name_to_free_self (n : name) (i : ℕ) : name_to n i (free n) = bound i := if_pos rfl

def replace (im : expr) : ℕ → expr → expr
| i (app f x) := app (replace i f) (replace i x)
| i (abs nm m) := abs nm (replace (i+1) m)
| i t@(bound m) := if i = m then im else t
| i t := t

lemma replace_bound_self (im : expr) (i : ℕ) : replace im i (bound i) = im := if_pos rfl

def abstract (n : name) (e : expr) : expr := name_to n 0 e
def instantiate (im : expr) (t : expr) : expr := replace im 0 t

def expr.is_valid_under : ℕ → expr → Prop
| i (app f x) := f.is_valid_under i ∧ x.is_valid_under i
| i (abs _ m) := m.is_valid_under (i+1)
| i (bound j) := j < i
| i _ := true

def expr.is_valid : expr → Prop := expr.is_valid_under 0
def expr.is_valid_scope : expr → Prop := expr.is_valid_under 1

lemma expr.is_valid_under.mono : ∀ {m n} {e : expr}, m ≤ n → e.is_valid_under m → e.is_valid_under n
| m n (app f x) hmn ⟨h₁, h₂⟩ := ⟨h₁.mono hmn, h₂.mono hmn⟩
| m n (abs _ b) hmn h := h.mono (nat.succ_le_succ hmn)
| m n (bound j) hmn h := hmn.trans' h
| m n (free i) hmn h := trivial
| m n (con s) hmn h := trivial

@[simp] lemma app_is_valid (e₁ e₂ : expr) : (e₁.app e₂).is_valid ↔ e₁.is_valid ∧ e₂.is_valid :=
iff.rfl

-- @[simp] lemma free_is_valid {i} : (free i).is_valid := trivial
-- @[simp] lemma con_is_valid {i} : (con i).is_valid := trivial

lemma valid_under_name_to (nm : name) :
  ∀ {n : ℕ} {e : expr}, e.is_valid_under n → (name_to nm n e).is_valid_under (n+1)
| n (app f x) ⟨h₁, h₂⟩ := ⟨valid_under_name_to h₁, valid_under_name_to h₂⟩
| n (abs _ m) h := @valid_under_name_to _ m h
| n (bound j) h := h.mono n.le_succ
| n (free j) h :=
  begin
    rcases eq_or_ne nm j with rfl | hj,
    { rw name_to_free_self,
      exact n.lt_succ_self },
    rwa [name_to, if_neg hj.symm],
  end
| n (con j) h := trivial

lemma valid_under_replace (im : expr) :
  ∀ {n : ℕ} {e : expr}, im.is_valid_under n → e.is_valid_under (n+1) →
    (replace im n e).is_valid_under n
| n (app f x) i ⟨h₁, h₂⟩ := ⟨valid_under_replace i h₁, valid_under_replace i h₂⟩
| n (abs _ m) i h := valid_under_replace (i.mono n.le_succ) h
| n (bound j) i h :=
  begin
    rcases nat.lt_succ_iff_lt_or_eq.1 h with hj | rfl,
    { rwa [replace, if_neg hj.ne'] },
    { rwa replace_bound_self }
  end
| n (free j) i h := trivial
| n (con j) i h := trivial

lemma abstract_valid_scope {n : name} {e : expr} : e.is_valid → (abstract n e).is_valid_scope :=
valid_under_name_to n

lemma instantiate_valid (im t : expr) : im.is_valid → t.is_valid_scope →
  (instantiate im t).is_valid :=
valid_under_replace _

def «forall» (x : name) : expr → expr := Forall (some x)

end prisoner
