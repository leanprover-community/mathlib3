import tactic.norm_cast

structure hom (α β : Type) :=
(to_fun : α → β)

instance {α β} : has_coe_to_fun (hom α β) (λ _, α → β) :=
⟨hom.to_fun⟩

structure hom_plus (α β) extends hom α β

instance {α β} : has_coe (hom_plus α β) (hom α β) :=
⟨hom_plus.to_hom⟩

instance {α β} : has_coe_to_fun (hom_plus α β) (λ _, α → β) := ⟨λ f, f⟩

@[norm_cast] lemma hom_plus.coe_fn (α β : Type) (a : α) (h : hom_plus α β) :
  (h : hom α β) a = h a :=
rfl

example (α β : Type) (a : α) (h : hom_plus α β) :
  (h : hom α β) a = h a :=
by norm_cast

def f1 (n : ℕ) : hom_plus ℕ ℕ := ⟨⟨λ m, m + n⟩⟩
def f2 : hom ℕ (hom ℕ ℕ) := ⟨λ n, f1 n⟩

@[norm_cast] lemma coe_f1 (n : ℕ) :
  (f1 n : hom ℕ ℕ) = f2 n :=
rfl
