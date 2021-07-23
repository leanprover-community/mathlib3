import order.boolean_algebra
import algebra.algebra.basic

variables (α : Type*)

class huntington_algebra extends has_sup α, has_compl α, inhabited α :=
[sup_commutative : is_commutative α (⊔)]
[sup_associative : is_associative α (⊔)]
(h3 (x y : α) : (xᶜ ⊔ yᶜ)ᶜ ⊔ (xᶜ ⊔ y)ᶜ = x)

namespace huntington_algebra

variables {α} [huntington_algebra α] (x y z : α)
local attribute [instance] sup_commutative sup_associative

instance : has_inf α := ⟨λ x y, (xᶜ ⊔ yᶜ)ᶜ⟩
instance : has_top α := ⟨default _ ⊔ (default _)ᶜ⟩
instance : has_bot α := ⟨⊤ᶜ⟩

lemma inf_def : x ⊓ y = (xᶜ ⊔ yᶜ)ᶜ := rfl
lemma top_def : (⊤ : α) = default _ ⊔ (default _)ᶜ := rfl
lemma bot_def : (⊥ : α) = ⊤ᶜ := rfl

@[simp] lemma top_compl : (⊤ : α)ᶜ = ⊥ := rfl

lemma sup_comm : x ⊔ y = y ⊔ x := by ac_refl
lemma sup_assoc : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by ac_refl
lemma p12 : x ⊔ xᶜ = xᶜ ⊔ xᶜᶜ :=
calc x ⊔ xᶜ = ((xᶜ ⊔ xᶜᶜᶜ)ᶜ ⊔ (xᶜ ⊔ xᶜᶜ)ᶜ) ⊔ ((xᶜᶜ ⊔ xᶜᶜᶜ)ᶜ ⊔ (xᶜᶜ ⊔ xᶜᶜ)ᶜ) : by rw [h3, h3]
        ... = ((xᶜᶜ ⊔ xᶜᶜ)ᶜ ⊔ (xᶜᶜ ⊔ xᶜ)ᶜ) ⊔ ((xᶜᶜᶜ ⊔ xᶜᶜ)ᶜ ⊔ (xᶜᶜᶜ ⊔ xᶜ)ᶜ) : by ac_refl
        ... = xᶜ ⊔ xᶜᶜ : by rw [h3, h3]

@[simp] lemma p13 : xᶜᶜ = x :=
calc xᶜᶜ = (xᶜᶜᶜ ⊔ xᶜᶜ)ᶜ ⊔ (xᶜᶜᶜ ⊔ xᶜ)ᶜ : (h3 _ _).symm
     ... = (xᶜ ⊔ xᶜᶜᶜ)ᶜ ⊔ (xᶜ ⊔ xᶜᶜ)ᶜ : by rw [sup_comm, sup_comm xᶜᶜᶜ, sup_comm xᶜᶜᶜ, ←p12 xᶜ]
     ... = x : h3 x xᶜᶜ

@[simp] lemma bot_compl : (⊥ : α)ᶜ = ⊤ := p13 _

lemma p14 (h : xᶜ = yᶜ) : x = y := by simpa using congr_arg has_compl.compl h

lemma p151 : (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ := by simp [inf_def]
lemma p152 : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ := by simp [inf_def]
lemma p16 : (xᶜ ⊓ yᶜ)ᶜ = x ⊔ y := by simp [inf_def]
lemma p17 : (x ⊓ y) ⊔ (x ⊓ yᶜ) = x := by rw [inf_def, inf_def, sup_comm, h3]
lemma inf_comm : x ⊓ y = y ⊓ x := by simp [inf_def, sup_comm] -- p18
lemma inf_assoc : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by simp [inf_def, sup_assoc] -- p19

lemma inf_commutative : is_commutative α (⊓) := ⟨inf_comm⟩
lemma inf_associative : is_associative α (⊓) := ⟨inf_assoc⟩

local attribute [instance] inf_commutative inf_associative

lemma p20 : x ⊔ xᶜ = y ⊔ yᶜ :=
calc x ⊔ xᶜ = ((xᶜ ⊔ yᶜᶜ)ᶜ ⊔ (xᶜ ⊔ yᶜ)ᶜ) ⊔ ((xᶜᶜ ⊔ yᶜᶜ)ᶜ ⊔ (xᶜᶜ ⊔ yᶜ)ᶜ) : by rw [h3, h3]
        ... = ((yᶜ ⊔ xᶜᶜ)ᶜ ⊔ (yᶜ ⊔ xᶜ)ᶜ) ⊔ ((yᶜᶜ ⊔ xᶜᶜ)ᶜ ⊔ (yᶜᶜ ⊔ xᶜ)ᶜ) : by ac_refl
        ... = y ⊔ yᶜ : by rw [h3, h3]

lemma sup_compl : x ⊔ xᶜ = ⊤ := by rw [←p20 (default α), top_def]
lemma compl_sup : xᶜ ⊔ x = ⊤ := by rw [sup_comm, sup_compl]
lemma p21 : x ⊓ xᶜ = ⊥ := by rw [inf_def, sup_compl, top_compl]

lemma sup_bot : x ⊔ ⊥ = x :=
begin
  have eq1 : (⊤ ⊔ ⊤)ᶜ ⊔ ⊤ᶜ = (⊤ : α)ᶜ,
  { have := h3 (⊥ : α) ⊥,
    rwa [sup_comm ⊥ᶜ ⊥, sup_compl, bot_compl] at this },
  have eq2 : (⊤ : α) ⊔ (⊤ ⊔ ⊤)ᶜ = ⊤,
  { have : (⊤ ⊔ ⊤ᶜ) ⊔ (⊤ ⊔ ⊤)ᶜ = (⊤ : α) ⊔ ((⊤ ⊔ ⊤)ᶜ ⊔ ⊤ᶜ) := by ac_refl,
    rwa [eq1, sup_compl] at this },
  have eq3 : (⊤ : α) ⊔ ⊤ = ⊤,
  { have : ⊤ ⊔ (⊤ ⊔ (⊤ ⊔ ⊤)ᶜ) = ((⊤ : α) ⊔ ⊤) ⊔ (⊤ ⊔ ⊤)ᶜ := by ac_refl,
    rwa [sup_compl, eq2] at this },
  have eq4 : (⊥ : α) ⊔ ⊥ = ⊥,
  { simpa [eq3] using eq1 },
  rw [←h3 x x, compl_sup, top_compl, sup_assoc, eq4],
end

lemma p222 : x ⊓ ⊤ = x := by rw [inf_def, top_compl, sup_bot, p13]
lemma p232 : x ⊓ x = x := by simpa [compl_sup, top_compl, sup_bot] using h3 x x
lemma p231 : x ⊔ x = x := by simp [←p16, p232]
lemma p242 : x ⊔ ⊤ = ⊤ := by rw [←sup_compl x, ←sup_assoc, p231]
lemma p241 : x ⊓ ⊥ = ⊥ := by rw [inf_def, bot_compl, p242, top_compl]

lemma p25 : x ⊔ (x ⊓ y) = x :=
calc _ = (xᶜ ⊔ yᶜ)ᶜ ⊔ (xᶜ ⊔ y)ᶜ ⊔ (xᶜ ⊔ yᶜ)ᶜ : by rw h3
   ... = (xᶜ ⊔ yᶜ)ᶜ ⊔ (xᶜ ⊔ yᶜ)ᶜ ⊔ (xᶜ ⊔ y)ᶜ : by ac_refl
   ... = x : by rw [p231, h3]

lemma p26 : x ⊓ (x ⊔ y) = x := by rw [inf_def, p151 x, p25, p13]
lemma p27 : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z :=
calc x ⊓ (y ⊔ z) = x ⊓ (y ⊔ z) ⊓ y ⊔ x ⊓ (y ⊔ z) ⊓ yᶜ : (p17 _ _).symm
    ... = x ⊓ y ⊔ x ⊓ (y ⊔ z) ⊓ yᶜ : by rw [inf_assoc, ←inf_comm y, p26]
    ... = x ⊓ y ⊓ z ⊔ x ⊓ y ⊓ zᶜ ⊔ (x ⊓ (y ⊔ z) ⊓ yᶜ ⊓ z ⊔ x ⊓ (y ⊔ z) ⊓ yᶜ ⊓ zᶜ) : by rw [p17, p17]
    ... = x ⊓ y ⊓ z ⊔ x ⊓ y ⊓ zᶜ ⊔ (x ⊓ yᶜ ⊓ (z ⊓ (z ⊔ y)) ⊔ x ⊓ (y ⊔ z) ⊓ yᶜ ⊓ zᶜ) : by ac_refl
    ... = x ⊓ y ⊓ z ⊔ x ⊓ y ⊓ zᶜ ⊔ (x ⊓ yᶜ ⊓ z ⊔ x ⊓ (y ⊔ z) ⊓ yᶜ ⊓ zᶜ) : by rw p26
    ... = x ⊓ y ⊓ z ⊔ x ⊓ y ⊓ zᶜ ⊔ (x ⊓ yᶜ ⊓ z ⊔ x ⊓ ((y ⊔ z) ⊓ (y ⊔ z)ᶜ)) : by { rw p151, ac_refl }
    ... = x ⊓ y ⊓ z ⊔ x ⊓ y ⊓ zᶜ ⊔ x ⊓ yᶜ ⊓ z : by rw [p21, p241, sup_bot]
    ... = x ⊓ y ⊓ z ⊔ x ⊓ y ⊓ z ⊔ x ⊓ y ⊓ zᶜ ⊔ x ⊓ yᶜ ⊓ z : by rw p231
    ... = x ⊓ y ⊓ z ⊔ x ⊓ y ⊓ zᶜ ⊔ (x ⊓ z ⊓ y ⊔ x ⊓ z ⊓ yᶜ) : by ac_refl
    ... = x ⊓ y ⊔ x ⊓ z : by rw [p17, p17]
lemma p28 : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z) := by rw [inf_def, ←p16, p13, p27, p151, p16, p16]

instance lattice_of_huntingdon_algebra : lattice α :=
lattice.mk' sup_comm sup_assoc inf_comm inf_assoc p25 p26

def boolean_algebra_of_huntingdon_algebra : boolean_algebra α :=
boolean_algebra.of_core
{ le_sup_inf := λ x y z, (p28 x y z).ge,
  le_top := p242,
  bot_le := λ x,
  begin
    rw ←sup_eq_left,
    apply sup_bot,
  end,
  inf_compl_le_bot := λ x, (p21 _).le,
  top_le_sup_compl := λ x, (sup_compl _).ge,
  ..(by apply_instance : lattice α),
  ..(by apply_instance : has_top α),
  ..(by apply_instance : has_bot α),
  ..(by apply_instance : has_compl α) }

end huntington_algebra

class robbins_algebra extends has_sup α, has_compl α, inhabited α :=
[sup_commutative : is_commutative α (⊔)]
[sup_associative : is_associative α (⊔)]
(r3 (x y : α) : ((x ⊔ y)ᶜ ⊔ (x ⊔ yᶜ)ᶜ)ᶜ = x)

namespace robbins_algebra

variables [robbins_algebra α] (x y z u : α)

def nat_smul : ℕ → α → α
| 0 x := (default _ ⊔ (default _)ᶜ)ᶜ -- will be the bot, but we don't know that
| 1 x := x
| (n+2) x := nat_smul (n+1) x ⊔ x

def nat_smul_notation : has_scalar ℕ α :=
{ smul := nat_smul _ }

local attribute [instance] nat_smul_notation

@[simp] lemma one_smul : 1 • x = x := rfl
lemma two_smul : 2 • x = x ⊔ x := rfl
lemma three_smul : 3 • x = x ⊔ x ⊔ x := rfl
lemma four_smul : 4 • x = x ⊔ x ⊔ x ⊔ x := rfl
lemma five_smul : 5 • x = x ⊔ x ⊔ x ⊔ x ⊔ x := rfl

def w_minus_two : Prop := ∀ (x : α), xᶜᶜ = x
def w_minus_one : Prop := ∃ (zero : α), ∀ x, x ⊔ zero = x
def w_zero : Prop := ∃ (a : α), a ⊔ a = a
def w_one : Prop := ∃ (a b : α), a ⊔ b = b
def w_two : Prop := ∃ (a b : α), (a ⊔ b)ᶜ = bᶜ

variables {α}

local attribute [instance] sup_commutative sup_associative

lemma sup_comm : x ⊔ y = y ⊔ x := by ac_refl
lemma sup_assoc : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by ac_refl

def p30 (hw_minus_two : w_minus_two α) : huntington_algebra α :=
{ h3 := λ x y, by rw [←hw_minus_two ((xᶜ ⊔ yᶜ)ᶜ ⊔ (xᶜ ⊔ y)ᶜ), sup_comm, r3 xᶜ y, hw_minus_two] }

lemma p31 (hw_minus_one : w_minus_one α) : w_minus_two α :=
begin
  rcases hw_minus_one with ⟨zero, h_zero⟩,
  have eq_6 := λ x, r3 zero x,
  simp only [sup_comm zero, h_zero] at eq_6,
  have eq_7 := λ (x : α), r3 xᶜ xᶜᶜ,
  simp only [eq_6, sup_comm zero, h_zero] at eq_7,
  have eq_8 := λ (x : α), r3 xᶜᶜᶜ xᶜ,
  simp_rw [sup_comm _ᶜᶜᶜ _ᶜᶜ, eq_6 _ᶜ, h_zero, sup_comm, eq_7] at eq_8,
  intro x,
  rw [←r3 x zero, ←eq_8]
end

lemma p32 (hw_zero : w_zero α) : w_minus_one α :=
begin
  rcases hw_zero with ⟨a, ha⟩,
  let zero := (a ⊔ aᶜ)ᶜ,
  refine ⟨zero, _⟩,
  have eq_7 : (aᶜ ⊔ zero)ᶜ = a := by simpa [ha] using r3 a a,
  have eq_8 : ∀ x, ((a ⊔ x)ᶜ ⊔ (a ⊔ x ⊔ aᶜ)ᶜ)ᶜ = a ⊔ x,
  { intro x, by simpa [ha, sup_comm, ←sup_assoc a] using r3 (a ⊔ x) a },
  have eq_9 : ∀ x, ((x ⊔ aᶜ ⊔ zero)ᶜ ⊔ (x ⊔ a)ᶜ)ᶜ = x,
  { intro x, simpa [eq_7, sup_assoc] using r3 x (aᶜ ⊔ zero) },
  have eq_10 : ((a ⊔ aᶜ ⊔ aᶜ)ᶜ ⊔ a)ᶜ = aᶜ,
  { simpa [eq_7, sup_comm aᶜ (a ⊔ _)] using r3 aᶜ (a ⊔ aᶜ) },
  have eq_11 : ((a ⊔ aᶜ ⊔ zero)ᶜ ⊔ aᶜ)ᶜ = a,
  { simpa [ha] using eq_9 a },
  have eq_12 : ((a ⊔ aᶜ ⊔ aᶜ)ᶜ ⊔ aᶜ)ᶜ = a,
  { have := r3 a (a ⊔ aᶜ ⊔ aᶜ),
    rwa [←sup_comm (a ⊔ aᶜ ⊔ aᶜ)ᶜ, eq_10, ←sup_assoc, ←sup_assoc, ha] at this },
  have eq_13 : (a ⊔ aᶜ ⊔ aᶜ)ᶜ = zero,
  { simpa [eq_10, eq_12, sup_comm aᶜ a] using (r3 (a ⊔ aᶜ ⊔ aᶜ)ᶜ a).symm },
  have eq_14 : (a ⊔ zero)ᶜ = aᶜ,
  { rw [←eq_13, sup_comm, eq_10] },
  have eq_15 : a ⊔ zero = a,
  { have := eq_8 zero,
    rw [eq_14, sup_comm aᶜ, sup_assoc, sup_comm zero, ←sup_assoc, eq_11] at this,
    rw ←this },
  intro x,
  rw [←r3 (x ⊔ zero) a, sup_assoc, sup_comm zero a, eq_15, sup_assoc, sup_comm zero, ←sup_assoc,
    sup_comm _ᶜ _ᶜ, eq_9 x],
end

lemma p33 (a b c : α) (h : (a ⊔ (b ⊔ c)ᶜ)ᶜ = (a ⊔ b ⊔ cᶜ)ᶜ) : a ⊔ b = a :=
by rw [←r3 (a ⊔ b) c, ←h, sup_assoc a b c, r3 a (b ⊔ c)]

lemma p34 (a b c : α) (h : (a ⊔ (b ⊔ c)ᶜ)ᶜ = (b ⊔ (a ⊔ c)ᶜ)ᶜ) : a = b :=
by rw [←r3 a (b ⊔ c), h, ←sup_assoc, sup_comm a b, sup_assoc, r3]

lemma p35 (a b c : α) (h : (a ⊔ bᶜ)ᶜ = c) : ((a ⊔ b)ᶜ ⊔ c)ᶜ = a :=
by rw [←h, r3]

lemma p36 (a b c : α) (h : (a ⊔ bᶜ)ᶜ = c) (k : ℕ) :
  (a ⊔ (b ⊔ (k+1) • (a ⊔ c))ᶜ)ᶜ = c :=
begin
  let b_ : ℕ → α := λ n, nat.iterate (⊔ (a ⊔ c)) n b,
  have b_eq : ∀ (n : ℕ), b_ n.succ = c ⊔ (a ⊔ b_ n),
  { intro n,
    rw [←sup_assoc, sup_comm, sup_comm c a],
    apply function.iterate_succ_apply' },
  have : ∀ n, (a ⊔ (b_ n)ᶜ)ᶜ = c,
  { intro n,
    induction n with n ih,
    { exact h },
    { have := r3 c (a ⊔ b_ n),
      rwa [←b_eq, sup_comm c, p35 _ _ _ ih, sup_comm] at this } },
  have b_eq' : ∀ n, b_ (n+1) = b ⊔ (n+1) • (a ⊔ c),
  { intro n,
    induction n with n ih,
    { refl },
    rw [b_eq, ih],
    change _ = b ⊔ ((n + 1) • (a ⊔ c) ⊔ (a ⊔ c)),
    ac_refl },
  rw ←b_eq',
  apply this _,
end

lemma p37 (a b : α) (h : ((a ⊔ bᶜ)ᶜ ⊔ bᶜ)ᶜ = a) (k : ℕ) :
  (b ⊔ (k+1) • (a ⊔ (a ⊔ bᶜ)ᶜ))ᶜ = bᶜ :=
begin
  set c := (a ⊔ bᶜ)ᶜ,
  apply p34 _ _ c,
  rw [sup_comm bᶜ c, h, ←sup_comm a, p36 _ _ _ rfl, sup_comm, ←sup_comm c, sup_comm a c,
    p36 _ _ _ h k],
end

lemma p38 (a b : α) (h : (a ⊔ b)ᶜ = bᶜ) (k : ℕ) :
  (b ⊔ (k+1) • (a ⊔ (a ⊔ bᶜ)ᶜ))ᶜ = bᶜ :=
begin
  apply p37,
  simpa [h, sup_comm] using r3 a b,
end

lemma p39 (a b : α) (h₁ : (2 • a ⊔ b)ᶜ = bᶜ) (h₂ : (3 • a ⊔ b)ᶜ = bᶜ) :
  2 • a ⊔ b = 3 • a ⊔ b :=
begin
  suffices : 2 • a ⊔ b ⊔ a = 2 • a ⊔ b,
  { rw [←this],
    simp only [two_smul, three_smul],
    ac_refl },
  apply p33 (2 • a ⊔ b) a (a ⊔ bᶜ),
  have := p38 (2 • a) b h₁ 0,
  rw [one_smul, two_smul, ←sup_assoc] at this,
  rw [two_smul, sup_comm _ b, ←sup_assoc a, this],
  have : (a ⊔ (2 • a ⊔ b))ᶜ = (2 • a ⊔ b)ᶜ,
  { rw [←sup_assoc, h₁, sup_comm a],
    apply h₂ },
  have := p38 a (2 • a ⊔ b) this 0,
  rw [one_smul, h₁, sup_comm _ b, ←sup_assoc] at this,
  exact this.symm
end

lemma p401 (a b : α) (h : (a ⊔ b)ᶜ = bᶜ) :
  b ⊔ 2 • (a ⊔ (a ⊔ bᶜ)ᶜ) = b ⊔ 3 • (a ⊔ (a ⊔ bᶜ)ᶜ) :=
begin
  rw [sup_comm b, sup_comm b],
  apply p39 (a ⊔ (a ⊔ bᶜ)ᶜ) b,
  { rw [←sup_comm b],
    apply p38 _ _ h },
  { rw [←sup_comm b],
    apply p38 _ _ h },
end
lemma p402 (a b : α) (h : ((a ⊔ bᶜ)ᶜ ⊔ bᶜ)ᶜ = a) :
  b ⊔ 2 • (a ⊔ (a ⊔ bᶜ)ᶜ) = b ⊔ 3 • (a ⊔ (a ⊔ bᶜ)ᶜ) :=
begin
  rw [sup_comm b, sup_comm b],
  apply p39 (a ⊔ (a ⊔ bᶜ)ᶜ) b,
  { rw [←sup_comm b],
    apply p37 _ _ h },
  { rw [←sup_comm b],
    apply p37 _ _ h },
end

lemma p41 (hw_one : w_one α) : w_zero α :=
begin
  rcases hw_one with ⟨a, b, hab⟩,
  let c := b ⊔ 2 • (a ⊔ bᶜ)ᶜ,
  let d := c ⊔ (c ⊔ cᶜ)ᶜ,
  refine ⟨3 • d, _⟩,
  have eq_16 : a ⊔ c = c,
  { rw [←sup_assoc, hab] },
  have eq_17 : bᶜ = cᶜ,
  { rw [←p38 a b _ 1, two_smul],
    { simp only [←sup_assoc, sup_comm _ a],
      rw [sup_assoc a a b, hab, hab, sup_assoc, ←two_smul] },
    { rw hab } },
  have eq_18 : c ⊔ (a ⊔ cᶜ)ᶜ = c,
  calc c ⊔ (a ⊔ cᶜ)ᶜ = b ⊔ 2 • (a ⊔ bᶜ)ᶜ ⊔ (a ⊔ bᶜ)ᶜ : by rw ←eq_17
                 ... = b ⊔ 3 • (a ⊔ bᶜ)ᶜ : by { rw [three_smul, two_smul], ac_refl }
                 ... = (a ⊔ (a ⊔ (a ⊔ b))) ⊔ 3 • (a ⊔ bᶜ)ᶜ : by simp only [hab]
                 ... = b ⊔ 3 • (a ⊔ (a ⊔ bᶜ)ᶜ) : by { simp only [three_smul], ac_refl }
                 ... = b ⊔ 2 • (a ⊔ (a ⊔ bᶜ)ᶜ) : (p401 a b (by rw hab)).symm
                 ... = (a ⊔ (a ⊔ b)) ⊔ 2 • (a ⊔ bᶜ)ᶜ : by { simp only [two_smul], ac_refl }
                 ... = b ⊔ 2 • (a ⊔ bᶜ)ᶜ : by rw [hab, hab],
  have eq_19 : ((c ⊔ cᶜ)ᶜ ⊔ cᶜ)ᶜ = c,
  { have := r3 c (a ⊔ cᶜ),
    rwa [eq_18, ←sup_assoc, sup_comm c a, eq_16] at this },
  have eq_20 : c ⊔ 2 • d = c ⊔ 3 • d := p402 c c eq_19,
  have : 3 • d ⊔ d = 3 • d,
  { rw [sup_comm, sup_assoc c, sup_comm _ᶜ, ←sup_assoc, ←eq_20, sup_assoc c, ←sup_comm _ᶜ,
      ←sup_assoc c, sup_comm],
    refl },
  change 3 • d ⊔ (d ⊔ d ⊔ d) = _,
  rw [←sup_assoc, ←sup_assoc _ d d, this, this, this],
end

lemma p43 : ((xᶜ ⊔ y)ᶜ ⊔ (x ⊔ y)ᶜ)ᶜ = y := by rw [sup_comm, sup_comm x y, sup_comm xᶜ y, r3 y x]

lemma p44 : (((x ⊔ y)ᶜ ⊔ xᶜ ⊔ y)ᶜ ⊔ y)ᶜ = (x ⊔ y)ᶜ :=
begin
  have := p43 (xᶜ ⊔ y) (x ⊔ y)ᶜ,
  rwa [p43 x y, sup_comm y, sup_comm (xᶜ ⊔ y), ←sup_assoc] at this,
end

lemma p45 : (((xᶜ ⊔ y)ᶜ ⊔ x ⊔ y)ᶜ ⊔ y)ᶜ = (xᶜ ⊔ y)ᶜ :=
begin
  have := p43 (x ⊔ y) (xᶜ ⊔ y)ᶜ,
  rwa [sup_comm (x ⊔ y)ᶜ, p43, sup_comm, sup_comm (x ⊔ y), ←sup_assoc] at this,
end

lemma p46 : (((xᶜ ⊔ y)ᶜ ⊔ x ⊔ y ⊔ y)ᶜ ⊔ (xᶜ ⊔ y)ᶜ)ᶜ = y :=
begin
  have := p43 ((xᶜ ⊔ y)ᶜ ⊔ x ⊔ y) y,
  rwa [p45, sup_comm] at this,
end

lemma p47 : ((((xᶜ ⊔ y)ᶜ ⊔ x ⊔ y ⊔ y)ᶜ ⊔ (xᶜ ⊔ y)ᶜ ⊔ z)ᶜ ⊔ (y ⊔ z)ᶜ)ᶜ = z :=
begin
  set w := ((xᶜ ⊔ y)ᶜ ⊔ x ⊔ y ⊔ y)ᶜ ⊔ (xᶜ ⊔ y)ᶜ,
  have : wᶜ = y := p46 _ _,
  rw [←this, sup_comm, p43 w z],
end

lemma p48 : ((((xᶜ ⊔ y)ᶜ ⊔ x ⊔ y ⊔ y)ᶜ ⊔ (xᶜ ⊔ y)ᶜ ⊔ (y ⊔ z)ᶜ ⊔ z)ᶜ ⊔ z)ᶜ = (y ⊔ z)ᶜ :=
begin
  have := p43 (((xᶜ ⊔ y)ᶜ ⊔ x ⊔ y ⊔ y)ᶜ ⊔ (xᶜ ⊔ y)ᶜ ⊔ z) (y ⊔ z)ᶜ,
  rwa [p47, sup_comm z, sup_assoc, sup_comm z, ←sup_assoc] at this,
end

lemma p49 :
  (((((xᶜ ⊔ y)ᶜ ⊔ x ⊔ y ⊔ y)ᶜ ⊔ (xᶜ ⊔ y)ᶜ ⊔ (y ⊔ z)ᶜ ⊔ z)ᶜ ⊔ z ⊔ u)ᶜ ⊔ ((y ⊔ z)ᶜ ⊔ u)ᶜ)ᶜ = u :=
begin
  set w := (((xᶜ ⊔ y)ᶜ ⊔ x ⊔ y ⊔ y)ᶜ ⊔ (xᶜ ⊔ y)ᶜ ⊔ (y ⊔ z)ᶜ ⊔ z)ᶜ ⊔ z,
  have := p43 w u,
  rwa [p48 x y z, sup_comm] at this,
end

lemma three_plus_two : 5 • x = 3 • x ⊔ 2 • x :=
by rw [five_smul, three_smul, two_smul, ←sup_assoc]

lemma one_plus_two : 3 • x = x ⊔ 2 • x :=
by rw [three_smul, two_smul, ←sup_assoc]

lemma p50 : ((((3•x)ᶜ ⊔ x)ᶜ ⊔ (3•x)ᶜ)ᶜ ⊔ (((3•x)ᶜ ⊔ x)ᶜ ⊔ 5•x)ᶜ)ᶜ = ((3•x)ᶜ ⊔ x)ᶜ :=
begin
  have eq_21 :
    (((((3•x)ᶜ ⊔ x)ᶜ ⊔ 5•x)ᶜ ⊔ (3•x)ᶜ ⊔ (((3•x)ᶜ ⊔ x)ᶜ ⊔ 2•x))ᶜ ⊔ (((3•x)ᶜ ⊔ x)ᶜ ⊔ 2•x))ᶜ =
      (((3•x)ᶜ ⊔ x)ᶜ ⊔ 5•x)ᶜ,
  { have threes : 3•x ⊔ (((3•x)ᶜ ⊔ x)ᶜ ⊔ 2•x) = ((3•x)ᶜ ⊔ x)ᶜ ⊔ 5•x,
    { rw [sup_comm, sup_assoc, sup_comm (2•x), ←three_plus_two] },
    have := p44 (3•x) (((3•x)ᶜ ⊔ x)ᶜ ⊔ (2•x)),
    rwa threes at this },
  rw [sup_comm, sup_comm ((3 • x)ᶜ ⊔ x)ᶜ (3 • x)ᶜ, ←eq_21],
  have := p49 (3•x) x (2•x) ((3•x)ᶜ ⊔ x)ᶜ,
  rw [←one_plus_two, sup_assoc _ x x, ←two_smul, sup_assoc _ (3 • x), ←three_plus_two] at this,
  rw [sup_comm _ᶜ (2 • x), ←sup_assoc],
  convert this using 7,
  ac_refl
end

lemma p51 : (((3•x)ᶜ ⊔ x)ᶜ ⊔ 5•x)ᶜ = (3•x)ᶜ :=
begin
  have eq_22 := p43 (((3•x)ᶜ ⊔ x)ᶜ ⊔ (3•x)ᶜ) (((3•x)ᶜ ⊔ x)ᶜ ⊔ 5•x)ᶜ,
  rw p50 at eq_22,
  have eq_23 := p47 (3•x) x (3•x)ᶜ,
  rw [sup_assoc _ x x, ←two_smul, sup_assoc _ (3 • x), ←three_plus_two] at eq_23,
  rw ←eq_22,
  convert eq_23 using 2,
  ac_refl
end

lemma p52 : ((((3•x)ᶜ ⊔ x)ᶜ ⊔ (3•x)ᶜ ⊔ 2•x)ᶜ ⊔ (3•x)ᶜ)ᶜ = ((3•x)ᶜ ⊔ x)ᶜ ⊔ 2•x :=
begin
  have := p43 (3•x) (((3•x)ᶜ ⊔ x)ᶜ ⊔ 2•x),
  rwa [sup_comm _ᶜ (2•x), ←sup_assoc (3•x), ←three_plus_two, sup_comm (5•x), p51,
    sup_comm (2•x), ←sup_assoc, sup_comm (3•x)ᶜ] at this,
end

lemma four_plus_one : 5 • x = 4 • x ⊔ x := rfl
lemma three_plus_one : 4 • x = 3 • x ⊔ x := rfl

lemma p53 : (((3•x)ᶜ ⊔ x)ᶜ ⊔ (3•x)ᶜ)ᶜ = x :=
begin
  have eq_24 := p43 (((3•x)ᶜ ⊔ x)ᶜ ⊔ 4•x) x,
  rw [sup_assoc, ←four_plus_one, p51] at eq_24,
  have eq_25 := p45 (3•x) x,
  rw [sup_assoc, ←three_plus_one] at eq_25,
  rw eq_25 at eq_24,
  rw eq_24,
end

lemma p54 : ((((3•x)ᶜ ⊔ x)ᶜ ⊔ (3•x)ᶜ ⊔ y)ᶜ ⊔ (x ⊔ y)ᶜ)ᶜ = y :=
begin
  have := p43 (((3•x)ᶜ ⊔ x)ᶜ ⊔ (3•x)ᶜ) y,
  rwa [p53, sup_comm] at this,
end

lemma p55 : w_one α :=
begin
  let x := default α,
  refine ⟨((3•x)ᶜ ⊔ x)ᶜ, 2•x, _⟩,
  have e := p54 x (2•x),
  rw ←one_plus_two at e,
  have := p52 x,
  rw e at this,
  rw ←this
end

def robbins_conjecture {α : Type*} [has_sup α] [has_compl α] [inhabited α]
  [is_commutative α (⊔)] [is_associative α (⊔)]
  (robbins_axiom : ∀ (x y : α), ((x ⊔ y)ᶜ ⊔ (x ⊔ yᶜ)ᶜ)ᶜ = x) :
  boolean_algebra α :=
begin
  haveI : robbins_algebra α := { r3 := robbins_axiom },
  have : w_one α := p55,
  replace := p41 this,
  replace := p32 this,
  replace := p31 this,
  replace := p30 this,
  exactI huntington_algebra.boolean_algebra_of_huntingdon_algebra,
end

end robbins_algebra
