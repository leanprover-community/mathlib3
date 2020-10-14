import algebra.group_action_hom

set_option old_structure_cmd true

section
variables (M : Type*) [monoid M]

/-- A (left) Ore set in a monoid `M` is a submonoid `S` of `M`
satisfying the "(left) Ore conditions".
In order to make operations on the localization at `S` compute,
we store choices of witnesses in `trunc`s.
When `S` is central, for example, there is a canonical choice.
Since `ore_set` is a bundled structure anyways it seems harmless
to keep this additional data.

Reference: https://ncatlab.org/nlab/show/Ore+set
-/
structure ore_set (M : Type*) [monoid M] extends submonoid M :=
(left_cancel : trunc (Π n m (s ∈ carrier), n * s = m * s → Σ' s' ∈ carrier, s' * n = s' * m))
(left_ore : trunc (Π m (s ∈ carrier), Σ' m' (s' ∈ carrier), s' * m = m' * s))

variables {M}

lemma ore_set.ext (s t : ore_set M) (h : s.carrier = t.carrier) : s = t :=
by { cases s, cases t, cases h, cc }  

instance : has_coe (ore_set M) (set M) := ⟨ore_set.carrier⟩

instance : has_coe_to_sort (ore_set M) := ⟨Type*, λ S, S.carrier⟩

instance : has_mem M (ore_set M) := ⟨λ m S, m ∈ (S : set M)⟩

-- Is this how this is supposed to work?
instance ore_set.monoid (S : ore_set M) : monoid S :=
show monoid S.to_submonoid, by apply_instance

-- Is this a good idea?
instance ore_set.has_scalar (S : ore_set M) (X : Type*) [has_scalar M X] :
  has_scalar S X :=
{ smul := λ s x, (s : M) • x }

/-- Propositional version of `ore_set.left_cancel`, for use in proofs. -/
lemma ore_set.exists_left_cancel (S : ore_set M) (n m s : M) (hs : s ∈ S)
  (h : n * s = m * s) : ∃ s' ∈ S, s' * n = s' * m :=
S.left_cancel.lift
  (λ f, let ⟨s', hs', h⟩ := f n m s hs h in ⟨s', hs', h⟩)
  (by { intros, refl })

/-- Propositional version of `ore_set.left_ore`, for use in proofs. -/
lemma ore_set.exists_left_ore (S : ore_set M) (m s : M) (hs : s ∈ S) :
  ∃ m' (s' ∈ S), s' * m = m' * s :=
S.left_ore.lift
  (λ f, let ⟨m', s', hs', h⟩ := f m s hs in ⟨m', s', hs', h⟩)
  (by { intros, refl })

end

namespace ore_set

/-- If `M` is commutative, then every submonoid is an Ore set. -/
def of_comm {M : Type*} [comm_monoid M] (S : submonoid M) : ore_set M :=
{ left_cancel := trunc.mk $ λ n m s hs h, ⟨s, hs, by rwa [mul_comm s n, mul_comm s m]⟩,
  left_ore := trunc.mk $ λ m s hs, ⟨m, s, hs, by rw mul_comm⟩,
  .. S }

-- TODO: More generally, if S ⊆ M is a *central* submonoid,
-- then it is an Ore set.

-- If x ∈ M is central, then the submonoid formed by its powers is central
-- and therefore an Ore set.

end ore_set

-- Localization of an M-module X at a left Ore set S ⊆ M.

variables {M : Type*} [monoid M] (S : ore_set M)
variables (X Y : Type*) [mul_action M X] [mul_action M Y]

namespace action                -- TODO: better name?

/-- A map `f : X → Y` of `M`-modules is a localization at `S`
if it satisfies the following conditions:
* Each `s ∈ S` acts invertibly on `Y`.
* For any `y : Y`, we can "clear denominators" by acting by some `s ∈ S`
  to produce an element in the image of `f`.
* Two elements of `X` become equal in `Y` if and only if
  they become equal when acted upon by some `s ∈ S`. -/
@[nolint has_inhabited_instance]
structure localization_map extends mul_action_hom M X Y :=
(acts_invertibly' : ∀ s ∈ S, function.bijective (λ (y : Y), s • y))
(surj' : ∀ y, ∃ (s ∈ S) x, s • y = to_fun x)
(eq_iff_exists' : ∀ x x', to_fun x = to_fun x' ↔ ∃ s ∈ S, s • x = s • x')

-- TODO: to_additive?

-- TODO:
-- * Construct a localization of any `M`-module `X`,
--   as a quotient of `S × X` by a certain relation.

section construction

variables {S X}

-- We'll build the localization of `X` at `S` as a quotient of `S × X`
-- by a certain relation. We think of an element `(s, x) : S × X`
-- as representing the product `s⁻¹ • x`. Then, we need to identify
-- two pairs when they represent the same element of any `M`-module
-- with a map from `X` on which `S` acts invertibly.

-- The relation (not an equivalence relation) we will quotient `S × X` by
-- to construct the localization. Note that we do *not* require `t`
-- to belong to `S`. However, when `s` belongs to `S`, `t` will be inverted
-- by a map that inverts `S` if and only if `t * s` is. So, there is no harm
-- in also treating such `t` as invertible.
inductive g : S × X → S × X → Prop
| mk (s : S) (t : M) (h : t * s ∈ S) (x : X) : g (s, x) (⟨t * s, h⟩, t • x)
-- TODO: would it be a good idea to add more equality hypotheses
-- (e.g. `t * s = s'`) in an attempt to rely less on `convert`?

lemma g_reflexive : reflexive (g : S × X → S × X → Prop) :=
begin
  rintro ⟨⟨s, hs⟩, x⟩,
  convert g.mk ⟨s, hs⟩ 1 _ x; simp; exact hs
end

lemma g_transitive : transitive (g : S × X → S × X → Prop) :=
begin
  rintro _ _ _ ⟨s₁, t₁, h₁, x₁⟩ ⟨_, t₂, h₂, _⟩,
  convert g.mk s₁ (t₂ * t₁) _ x₁ using 2,
  { ext, exact (mul_assoc _ _ _).symm },
  { rw smul_smul },
  { convert h₂ using 1,
    apply mul_assoc }
end

-- Church-Rosser property
lemma g_join (q q₁ q₂ : S × X) (h₁ : g q q₁) (h₂ : g q q₂) : relation.join g q₁ q₂ :=
begin
  cases h₁ with s t₁ t₁s x,
  cases h₂ with _ t₂ t₂s _,
  obtain ⟨u₂, u₁, hu₁, hu⟩ := S.exists_left_ore (t₁ * s) (t₂ * s) t₂s,
  obtain ⟨s', hs', hs'ut⟩ :=
    S.exists_left_cancel (u₁ * t₁) (u₂ * t₂) s s.property (by assoc_rw hu),
  have s'u₁t₁s : s' * u₁ * (t₁ * s) ∈ S :=
    S.to_submonoid.mul_mem (S.to_submonoid.mul_mem hs' hu₁) t₁s,
  have e : s' * u₁ * (t₁ * s) = s' * u₂ * (t₂ * s),
  { assoc_rw hs'ut, repeat { rw mul_assoc } },
  have s'u₂t₂s : s' * u₂ * (t₂ * s) ∈ S, { rwa ←e },
  refine ⟨(⟨s' * u₁ * (t₁ * s), s'u₁t₁s⟩, (s' * u₁) • t₁ • x), _, _⟩,
  { apply g.mk },
  { convert g.mk ⟨t₂ * s, t₂s⟩ (s' * u₂) s'u₂t₂s (t₂ • x) using 2,
    { ext, exact e },
    { rw [smul_smul, smul_smul],
      congr' 1,
      assoc_rw hs'ut } }
end

lemma eqv_gen_g_eq_join_g : eqv_gen (g : S × X → S × X → Prop) = relation.join g :=
begin
  have : equivalence (relation.join (g : S × X → S × X → Prop)) :=
    relation.equivalence_join g_reflexive g_transitive g_join,
  ext q₁ q₂,
  split,
  { rw ←relation.eqv_gen_iff_of_equivalence this,
    apply relation.eqv_gen_mono,
    intros,
    apply relation.join_of_single g_reflexive,
    assumption },
  { exact relation.join_of_equivalence (eqv_gen.is_equivalence _) eqv_gen.rel }
end

variables (S X)

def localization : Type* := quot (g : S × X → S × X → Prop)

variables {S X}

def right_frac (s : S) (x : X) : localization S X :=
quot.mk g (s, x)

local infixr ` \ `:73 := right_frac
-- Same precedence as ` • `.
-- So `m • s \ x = m • (s \ x)` and `s \ m • x = s \ (m • x)`,
-- just like `m • m' • x = m • (m' • x)`.

lemma localization.eq_iff {s₁ s₂ : S} {x₁ x₂ : X} :
  s₁ \ x₁ = s₂ \ x₂ ↔ relation.join g (s₁, x₁) (s₂, x₂) :=
begin
  unfold right_frac,
  rw [quot.eq, eqv_gen_g_eq_join_g]
end

lemma g_one_iff {x x' : X} {s' : S} :
  g ((1 : S), x) (s', x') ↔ x' = s' • x :=
begin
  split,
  { rintro ⟨_, _, _, _⟩,
    congr,
    exact (mul_one _).symm },
  { rintro rfl,
    convert g.mk 1 (s'.val) (by { convert s'.property, apply mul_one }) x,
    ext,
    exact (mul_one _).symm }
end

lemma localization.pure_eq_iff {x₁ x₂ : X} :
  (1 : S) \ x₁ = (1 : S) \ x₂ ↔ ∃ s ∈ S, s • x₁ = s • x₂ :=
begin
  rw localization.eq_iff,
  split,
  { rintros ⟨⟨s, x⟩, h₁, h₂⟩,
    rw g_one_iff at h₁ h₂,
    exact ⟨s, s.property, h₁.symm.trans h₂⟩ },
  { rintros ⟨s, hs, h⟩,
    refine ⟨⟨⟨s, hs⟩, s • x₁⟩, _, _⟩,
    { rw g_one_iff, refl },
    { rw g_one_iff, exact h } }
end

lemma quot_smul_eq_quot_smul (s : S) (t : M) (h : t * s ∈ S) (m : M) (x : X) :
  s \ m • x = ⟨t * s, h⟩ \ (t * m) • x :=
calc
  s \ m • x = ⟨t * s, h⟩ \ t • (m • x) : quot.sound (by apply g.mk)
...         = ⟨t * s, h⟩ \ (t * m) • x : by rw smul_smul

lemma smul_invariant
  (m : M) {s : S} (t : M) (h : t * s ∈ S) (x : X)
  (m₁ s₁ : M) (hs₁ : s₁ ∈ S) (h₁ : s₁ * m = m₁ * s)
  (m₂ s₂ : M) (hs₂ : s₂ ∈ S) (h₂ : s₂ * m = m₂ * (t * s)) :
  ⟨s₁, hs₁⟩ \ m₁ • x = ⟨s₂, hs₂⟩ \ m₂ • t • x :=
begin
  obtain ⟨s₁', s₂', hs₂', h₃⟩ := S.exists_left_ore s₁ s₂ hs₂,
  -- Note: s₁' might not actually belong to S.
  -- But we have h₁.symm : s₁' * s₂ = s₂' * s₁ ∈ S,
  -- so s₁' is at least a quotient of two elements of S.
  have commutes : (s₁' * m₂ * t) * s = (s₂' * m₁) * s,
  { rw ←mul_assoc at h₂,
    -- TODO: `assoc_rw ←h₂` claims to work, but didn't
    assoc_rw [h₂.symm, h₃.symm, h₁] },
  obtain ⟨s', hs', commutes'⟩ := S.exists_left_cancel _ _ s s.property commutes,
  have hs's₂'s₁ : s' * s₂' * s₁ ∈ S :=
    S.to_submonoid.mul_mem (S.to_submonoid.mul_mem hs' hs₂') hs₁,
  have : s' * s₂' * s₁ = s' * s₁'* s₂, { assoc_rw h₃ },
  have hs's₁'s₂ : s' * s₁'* s₂ ∈ S, { rwa ←this },
  calc  ⟨s₁, hs₁⟩ \ m₁ • x
      = ⟨s' * s₂' * s₁, hs's₂'s₁⟩ \ (s' * s₂' * m₁) • x
      : by apply quot_smul_eq_quot_smul
  ... = ⟨s' * s₁' * s₂, hs's₁'s₂⟩ \ (s' * s₁' * m₂ * t) • x
      : by { congr' 2, { exact this }, { assoc_rw commutes' } }
  ... = ⟨s₂, hs₂⟩ \ m₂ • (t • x)
      : _,
  have := (quot_smul_eq_quot_smul ⟨s₂, hs₂⟩ (s' * s₁') hs's₁'s₂ (m₂ * t) x).symm,
  convert this using 2,
  { repeat { rw mul_assoc } },
  { rw smul_smul }
end

lemma smul_invariant'
  (m : M) (s : S) (x : X)
  (m₁ s₁ : M) (hs₁ : s₁ ∈ S) (h₁ : s₁ * m = m₁ * s)
  (m₂ s₂ : M) (hs₂ : s₂ ∈ S) (h₂ : s₂ * m = m₂ * s) :
  ⟨s₁, hs₁⟩ \ m₁ • x = ⟨s₂, hs₂⟩ \ m₂ • x :=
begin
  convert smul_invariant m 1 _ x m₁ s₁ hs₁ h₁ m₂ s₂ hs₂ _,
  { rw one_smul },
  { convert s.property, rw one_mul, refl },
  { convert h₂, rw one_mul }
end

-- TODO: name?
-- TODO: with the new type how does this compare to quot.lift_on₂?
-- TODO: This seems like it would work, however, it also seems too awkward?
-- actually, now I'm not sure why I thought that?
@[elab_as_eliminator]
def quot_trunc_lift_on₂ {α : Sort*} {β : α → Sort*} {γ : Sort*} {r : α → α → Prop}
  (p : quot r) (q : trunc (Π a, β a)) (f : Π (a : α), β a → γ)
  (hr : reflexive r) (hf : ∀ a₁ a₂ b₁ b₂, r a₁ a₂ → f a₁ b₁ = f a₂ b₂) : γ :=
quot.lift_on p
  (λ a, trunc.lift_on q (λ w, f a (w a)) (λ w₁ w₂, hf _ _ _ _ (hr a)))
  (λ a₁ a₂ h, show q.lift_on _ _ = q.lift_on _ _,
   begin
     induction q using trunc.ind,
     exact hf _ _ _ _ h,
   end)

def quot_trunc_lift_on_beta₂ {α : Sort*} {β : α → Sort*} {γ : Sort*}
  {r : α → α → Prop} (a : α) (w : Π a, β a) (f : Π (a : α), β a → γ)
  (hr : reflexive r) (hf : ∀ a₁ a₂ b₁ b₂, r a₁ a₂ → f a₁ b₁ = f a₂ b₂) :
  quot_trunc_lift_on₂ (quot.mk r a) (trunc.mk w) f hr hf = f a (w a) :=
rfl

instance : has_scalar M (localization S X) :=
{ smul := λ m f, 
  begin
    refine quot_trunc_lift_on₂ f
      (S.left_ore.map (λ H q, H m q.1.1 q.1.2))
      (λ q p, ⟨p.2.1, p.2.2.1⟩ \ p.1 • q.2) _ _,
    { rintro ⟨s, x⟩,
      apply g_reflexive },
    rintros _ _ ⟨m'₁, s'₁, hs'₁, h₁⟩ ⟨m'₂, s'₂, hs'₂, h₂⟩ ⟨s, t, h, x⟩,
    apply smul_invariant m _ h x _ _ _ h₁ _ _ _ h₂,
  end }

lemma smul_eq (s : S) (m : M) {x : X} (s' : S) (m' : M)
  (h : (s' : M) * m = m' * s) :
  m • s \ x = s' \ m' • x :=
begin
  unfold has_scalar.smul,
  change quot_trunc_lift_on₂ _ (trunc.lift_on _ _ _) _ _ _ = _,
  rcases S.left_ore with ⟨f⟩,
  cases s with s hs,
  change ⟨(f m s hs).snd.fst, _⟩ \ (f m s hs).fst • x = s' \ m' • x,
  dsimp only [],                -- magic?
  rcases f m s hs with ⟨m'', s'', hs'', h''⟩,
  cases s' with s' hs',
  exact (smul_invariant' m ⟨s, hs⟩ x m'' s'' _ h'' m' s' hs' h : _),
end

instance : mul_action M (localization S X) :=
{ one_smul := begin
    rintro ⟨⟨s, x⟩⟩,
    change (1 : M) • (s \ x) = s \ x,
    rw [smul_eq s 1 s 1, one_smul],
    rw [mul_one, one_mul]
  end,
  mul_smul := begin
    rintro m₁ m₂ ⟨⟨⟨s, hs⟩, x⟩⟩,
    change (m₁ * m₂) • (⟨s, hs⟩ \ x) = m₁ • m₂ • (⟨s, hs⟩ \ x),
    obtain ⟨m₂', s', hs', h₂⟩ := S.exists_left_ore m₂ s hs,
    obtain ⟨m₁', s'', hs'', h₁⟩ := S.exists_left_ore m₁ s' hs',
    have : s'' * (m₁ * m₂) = (m₁' * m₂') * s, { assoc_rw [h₁, h₂] },
    rw smul_eq ⟨s, hs⟩ m₂ ⟨s', hs'⟩ m₂' h₂,
    rw smul_eq ⟨s', hs'⟩ m₁ ⟨s'', hs''⟩ m₁' h₁,
    rw smul_eq ⟨s, hs⟩ (m₁ * m₂) ⟨s'', hs''⟩ _ this,
    rw smul_smul
  end }

/-- `localization S X` also supports a "division by `s ∈ S`" operator
which is inverse to `s • -`. -/
def right_divide (s : S) (q : localization S X) : localization S X :=
quot.lift_on q (λ p, (p.1 * s) \ p.2) $ begin
  rintros _ _ ⟨s', t, h, x⟩,
  apply quot.sound,
  convert g.mk _ t _ _,
  { ext, apply mul_assoc },
  { convert S.to_submonoid.mul_mem h s.property using 1,
    exact (mul_assoc _ _ _).symm }
end

lemma smul_right_divide {s : S} {q : localization S X} :
  s • right_divide s q = q :=
begin
  rcases q with ⟨⟨s', x⟩⟩,
  change s • (s' * s) \ x = s' \ x,
  convert smul_eq (s' * s) s s' 1 (by { rw one_mul, refl }),
  rw one_smul
end

lemma right_divide_smul {s : S} {q : localization S X} :
  right_divide s (s • q) = q :=
begin
  rcases q with ⟨⟨s₁, x⟩⟩,
  change right_divide s (↑s • s₁ \ x) = s₁ \ x,
  obtain ⟨m', s', hs', h⟩ := S.exists_left_ore s s₁ s₁.property,
  rw smul_eq s₁ s ⟨s', hs'⟩ _ h,
  change _ \ _ = s₁ \ x,
  symmetry,
  apply quot.sound,
  dsimp,
  convert g.mk s₁ m' _ x,
  { ext, exact h },
  { rw ←h,
    exact S.to_submonoid.mul_mem hs' s.property }
end

def smul_equiv (s : S) : localization S X ≃ localization S X :=
{ to_fun := λ q, s • q,
  inv_fun := right_divide s,
  left_inv := λ q, right_divide_smul,
  right_inv := λ q, smul_right_divide }

variables (S X)

def to_localization_aux : mul_action_hom M X (localization S X) :=
{ to_fun := λ x, 1 \ x,
  map_smul' := begin
    intros m x,
    rw smul_eq 1 m 1 m,
    change 1 * m = m * 1,
    rw [one_mul, mul_one]
  end }

def to_localization : localization_map S X (localization S X) :=
{ acts_invertibly' := λ s hs, (smul_equiv ⟨s, hs⟩).bijective,
  surj' := begin
    rintro ⟨⟨s, x⟩⟩,
    refine ⟨s, s.property, x, _⟩,
    change s.val • (s \ x) = 1 \ x,
    rw smul_eq s s.val s s.val rfl,
    symmetry,
    apply quot.sound,
    convert ← g.mk 1 (s : M) (by { convert s.property, apply mul_one }) x,
    ext,
    apply mul_one
  end,
  eq_iff_exists' := begin
    intros x x',
    apply localization.pure_eq_iff
  end,
  .. to_localization_aux S X }

-- when we build an `ore_set` from a central submonoid,
-- `smul` computes: `m • (s \ x) = s \ (m • x)` by rfl
-- (up to `cases s` at least)
example {M : Type*} [comm_monoid M] [mul_action M X] (S : submonoid M)
  (m : M) (s : ore_set.of_comm S) (x : X) : m • (s \ x) = s \ (m • x) :=
begin
  cases s,
  refl,
end

end construction

-- TODO:
-- * universal property of the localization
-- * (look at original localization for other properties)
-- * S⁻¹ M is a monoid
-- * S⁻¹ (X × Y) ≃ S⁻¹ X × S⁻¹ Y
-- * When `X` has extra structure (e.g., additive),
--   this structure is inherited by the localization.

end action
