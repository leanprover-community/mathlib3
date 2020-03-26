import tactic.lint

def f : ℕ → ℕ := default _
def c : ℕ := default _
def d : ℕ := default _

@[simp] lemma c_eq_d : c = d := rfl

-- The following lemma never applies when using simp, because c is first rewritten to d
@[simp] lemma f_c : f c = 0 := rfl

example : f c = 0 :=
begin
  simp,
  guard_target f d = 0, -- does not apply f_c
  refl
end

open tactic
#eval do
decl ← get_decl ``f_c,
res ← linter.simp_nf.test decl,
-- linter complains
guard $ res.is_some


-- also works with `coe_to_fun`

structure morphism :=
(f : ℕ → ℕ)

instance : has_coe_to_fun morphism :=
⟨_, morphism.f⟩

def h : morphism := ⟨default _⟩

-- Also never applies
@[simp] lemma h_c : h c = 0 := rfl

example : h c = 0 :=
begin
  simp,
  guard_target h d = 0, -- does not apply h_c
  refl
end

open tactic
#eval do
decl ← get_decl ``h_c,
res ← linter.simp_nf.test decl,
-- linter complains
guard $ res.is_some


-- and the same for a general equivalence relation

def equiv (a b : ℕ) := true

@[refl] lemma equiv.refl (a : ℕ) : equiv a a := ⟨⟩
@[trans] lemma equiv.trans (a b c : ℕ) : equiv a b → equiv b c → equiv b c := λ _ _, ⟨⟩

def a : ℕ := default _
def b : ℕ := default _
def e : ℕ := default _

@[simp] lemma a_equiv_e : equiv a e := by refl
@[simp] lemma a_equiv_b : equiv a b := by refl

#eval do
decl ← get_decl ``a_equiv_e,
res ← linter.simp_nf.test decl,
-- linter complains
guard res.is_some
