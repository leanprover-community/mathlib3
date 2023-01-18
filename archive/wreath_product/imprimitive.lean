import .defs

section imprimitive_explicit

variables (A : Type*) (B : Type*) (L : Type*) (M : Type*) [group A] [group B] [mul_action A L]

def imprimitive_smul (h : mul_action B M) : has_smul (B ≀[L] A) (M × L) :=
{ smul := (λ g x, ⟨g.left (g.right • x.2) • x.1, g.right • x.2⟩)}

def imprimitive_smul_def (h : mul_action B M) (g : (B ≀[L] A))(m : M) (l : L) :
  (imprimitive_smul A B L M h).smul g (m,l) = (g.left (g.right • l) • m, g.right • l) := rfl

def imprimitive (h : mul_action B M) : mul_action (B ≀[L] A) (M × L) :=
{
  to_has_smul := imprimitive_smul A B L M h,
  one_smul := begin
    rintros ⟨m, l⟩,
    rw imprimitive_smul_def,
    simp,
  end,
  mul_smul := begin
    rintros g h ⟨m, l⟩,
    repeat {rw imprimitive_smul_def},
    simp [mul_smul],
  end,
}

end imprimitive_explicit
