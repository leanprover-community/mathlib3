import data.finset data.set.finite algebra.big_operators algebra.module algebra.pi_instances

universes u u₁ u₂ v v₁ v₂ v₃ w x y l

variables (ι : Type u) (β : ι → Type v)

def decidable_zero_symm {γ : Type w} [has_zero γ] [decidable_pred (eq (0 : γ))] : decidable_pred (λ x, x = (0:γ)) :=
λ x, decidable_of_iff (0 = x) eq_comm
local attribute [instance] decidable_zero_symm

namespace dfinsupp

@[reducible] protected def finset (s : finset ι) : Type* :=
Π i : (↑s : set ι), β i.1

def pre : Type* :=
Σ s, dfinsupp.finset ι β s

variable [Π i, has_zero (β i)]

def rel (f g : pre ι β) : Prop :=
(∀ i (h1 : i ∈ f.1) (h2 : i ∈ g.1), f.2 ⟨i, h1⟩ = g.2 ⟨i, h2⟩)
∧ (∀ i (h1 : i ∈ f.1) (h2 : i ∉ g.1), f.2 ⟨i, h1⟩ = 0)
∧ (∀ i (h1 : i ∉ f.1) (h2 : i ∈ g.1), g.2 ⟨i, h2⟩ = 0)

instance : setoid (pre ι β) :=
{ r := relation.trans_gen (rel ι β),
  iseqv := ⟨λ f, relation.trans_gen.single
      ⟨λ _ _ _, rfl, by split; intros; cc⟩,
    λ f g H, relation.trans_gen.rec_on H
      (λ g H, relation.trans_gen.single
        ⟨λ _ _ _, (H.1 _ _ _).symm,
        λ _ _ h2, H.2.2 _ h2 _,
        λ _ h2 _, H.2.1 _ _ h2⟩)
      (λ b c h1 h2 h3, relation.trans_gen.head
        (⟨λ _ _ _, (h2.1 _ _ _).symm,
          λ _ _ h4, h2.2.2 _ h4 _,
          λ _ h4 _, h2.2.1 _ _ h4⟩) h3),
    λ x y z, relation.trans_gen.trans⟩ }

end dfinsupp

variable {ι}
def dfinsupp [Π i, has_zero (β i)] : Type* :=
quotient (dfinsupp.setoid ι β)
variable {β}

notation `Π₀` binders `, ` r:(scoped f, dfinsupp f) := r
infix ` →ₚ `:25 := dfinsupp

namespace dfinsupp

section basic
variables [Π i, has_zero (β i)]
variables {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
variables [Π i, has_zero (β₁ i)] [Π i, has_zero (β₂ i)]

def mk (s : finset ι) (x : dfinsupp.finset ι β s) : Π₀ i, β i :=
⟦⟨s, x⟩⟧

instance : has_zero (Π₀ i, β i) := ⟨mk ∅ $ λ _, 0⟩

instance : inhabited (Π₀ i, β i) := ⟨0⟩

protected def lift_on {γ : Sort l} (f : Π₀ i, β i)
  (φ : Π (s : finset ι) (x : dfinsupp.finset ι β s), γ)
  (hφ : ∀ s t x y, rel ι β ⟨s, x⟩ ⟨t, y⟩ → φ s x = φ t y) : γ :=
quotient.lift_on f (λ z, φ z.1 z.2) $ λ z₁ z₂ H,
relation.trans_gen.rec_on H (λ b, hφ _ _ _ _) $ λ b c h1 h2 h3,
h3.trans $ hφ _ _ _ _ h2

protected def induction_on {C : (Π₀ i, β i) → Prop} (f : Π₀ i, β i)
  (H : ∀ s x, C (mk s x)) : C f :=
quotient.induction_on f $ λ ⟨s, x⟩, H s x

@[simp] protected lemma lift_on_beta {γ : Sort l}
  (φ : Π (s : finset ι) (x : dfinsupp.finset ι β s), γ) (hφ s x) :
  dfinsupp.lift_on (mk s x) φ hφ = φ s x :=
rfl

/-- `single i b` is the finitely supported function which has
  value `b` at `i` and zero otherwise. -/
def single (i : ι) (b : β i) : Π₀ i, β i :=
mk (finset.singleton i) $ λ j, eq.rec_on (finset.mem_singleton.1 j.2).symm b

@[simp] lemma single_zero {i} : (single i 0 : Π₀ i, β i) = 0 :=
begin
  refine quotient.sound (relation.trans_gen.single ⟨λ j h1 h2, _, λ j h1 h2, _, λ j h1 h2, _⟩),
  { exact h2.elim },
  { simp at h1, subst h1 },
  { exact h2.elim }
end

/-- `on_finset s f hf` is the dfinsupp function representing `f` restricted to the set `s`.
The function needs to be 0 outside of `s`. Use this when the set needs filtered anyway, otherwise
often better set representation is available. -/
def on_finset (s : finset ι) (f : Π i, β i) : Π₀ i, β i :=
mk s $ λ i, f i.1

/-- The composition of `f : β₁ → β₂` and `g : Π₀ i, β₁ i` is
  `map_range f hf g : Π₀ i, β₂ i`, well defined when `f 0 = 0`. -/
def map_range (f : Π i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (g : Π₀ i, β₁ i) : Π₀ i, β₂ i :=
dfinsupp.lift_on g (λ s x, mk s $ λ i, f i.1 (x i)) $
begin
  rintros s t x y ⟨hs1, hs2, hs3⟩,
  refine quotient.sound (relation.trans_gen.single ⟨λ i h1 h2, _, λ i h1 h2, _, λ i h1 h2, _⟩),
  { specialize hs1 i h1 h2, dsimp at hs1 ⊢, simp [hs1] },
  { specialize hs2 i h1 h2, dsimp at hs2 ⊢, simp [hs2, hf] },
  { specialize hs3 i h1 h2, dsimp at hs3 ⊢, simp [hs3, hf] }
end

/-- `filter p f` is the function which is `f i` if `p i` is true and 0 otherwise. -/
def filter (p : ι → Prop) [decidable_pred p] (f : Π₀ i, β i) : Π₀ i, β i :=
dfinsupp.lift_on f (λ s x, mk (s.filter p) $ λ i, x ⟨i.1, (finset.mem_filter.1 i.2).1⟩) $
begin
  rintros s t x y ⟨hs1, hs2, hs3⟩,
  refine quotient.sound (relation.trans_gen.single ⟨λ i h1 h2, _, λ i h1 h2, _, λ i h1 h2, _⟩),
  { cases finset.mem_filter.1 h1 with h3 h4,
    cases finset.mem_filter.1 h2 with h5 h6,
    exact hs1 _ _ _ },
  { cases finset.mem_filter.1 h1 with h3 h4,
    have h5 : i ∉ t := mt (λ H, finset.mem_filter.2 ⟨H, h4⟩) h2,
    exact hs2 _ _ h5 },
  { cases finset.mem_filter.1 h2 with h3 h4,
    have h5 : i ∉ s := mt (λ H, finset.mem_filter.2 ⟨H, h4⟩) h1,
    exact hs3 _ h5 _ }
end

/-- `subtype_domain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
def subtype_domain (p : ι → Prop) [decidable_pred p]
  (f : Π₀ i, β i) : Π₀ i : subtype p, β i.1 :=
dfinsupp.lift_on f (λ s x, mk (s.subtype p) $ λ i, x ⟨i.1, finset.mem_subtype.1 i.2⟩) $
begin
  rintros s t x y ⟨hs1, hs2, hs3⟩,
  refine quotient.sound (relation.trans_gen.single ⟨λ i h1 h2, _, λ i h1 h2, _, λ i h1 h2, _⟩),
  { exact hs1 _ _ _ },
  { have h5 : i.1 ∉ t := mt finset.mem_subtype.2 h2,
    exact hs2 _ _ h5 },
  { have h5 : i.1 ∉ s := mt finset.mem_subtype.2 h1,
    exact hs3 _ h5 _ }
end

@[simp] lemma subtype_domain_zero {p : ι → Prop} [decidable_pred p] :
  subtype_domain p (0 : Π₀ i, β i) = 0 :=
rfl

end basic

section algebra

instance [Π i, add_group (β i)] : has_neg (Π₀ i, β i) :=
⟨λ f, f.map_range (λ _, has_neg.neg) (λ _, neg_zero)⟩

def to_has_scalar' {γ : Type w} [ring γ] [Π i, module γ (β i)] : has_scalar γ (Π₀ i, β i) :=
⟨λc v, v.map_range (λ _, (•) c) (λ _, smul_zero)⟩

end algebra

variable [decidable_eq ι]

section basic
variable [Π i, has_zero (β i)]

def finset_to_finset (s t : finset ι) (x : dfinsupp.finset ι β s) : dfinsupp.finset ι β t :=
λ i, if h : i.1 ∈ s then x ⟨i.1, h⟩ else 0

@[simp] lemma finset_id {s : finset ι} {x : dfinsupp.finset ι β s} :
  finset_to_finset s s x = x :=
funext $ λ ⟨i, hi⟩, dif_pos hi

@[simp] lemma finset_comp {s t : finset ι} (hst : s ⊆ t)
  (u : finset ι) {x : dfinsupp.finset ι β s} :
  finset_to_finset t u (finset_to_finset s t x) = finset_to_finset s u x :=
begin
  funext i,
  cases i with i hi,
  dsimp [finset_to_finset],
  by_cases h1 : i ∈ s,
  { simp [h1, hst h1] },
  by_cases h2 : i ∈ t;
  simp [h1, h2]
end

@[simp] lemma finset_apply {s t : finset ι} {x : dfinsupp.finset ι β s} {i} :
  finset_to_finset s t x i = if h : i.1 ∈ s then x ⟨i.1, h⟩ else 0 :=
rfl

lemma rel_iff {s t : finset ι} {x : dfinsupp.finset ι β s} {y : dfinsupp.finset ι β t} :
  rel ι β ⟨s, x⟩ ⟨t, y⟩ ↔ finset_to_finset s (s ∪ t) x = finset_to_finset t (s ∪ t) y :=
begin
  split,
  { rintro ⟨hs1, hs2, hs3⟩,
    ext i,
    by_cases h1 : i.1 ∈ s; by_cases h2 : i.1 ∈ t,
    { simpa [h1, h2] using hs1 i h1 h2 },
    { simpa [h1, h2] using hs2 i h1 h2 },
    { simpa [h1, h2] using (hs3 i h1 h2).symm },
    simp [h1, h2] },
  { intro hs, refine ⟨λ i h1 h2, _, λ i h1 h2, _, λ i h1 h2, _⟩,
    { dsimp at *, simpa [h1, h2] using congr_fun hs ⟨i, finset.mem_union_left _ h1⟩ },
    { dsimp at *, simpa [h1, h2] using congr_fun hs ⟨i, finset.mem_union_left _ h1⟩ },
    { dsimp at *, simpa [h1, h2] using (congr_fun hs ⟨i, finset.mem_union_right _ h2⟩).symm } }
end

protected def lift_on' {γ : Sort l} (f : Π₀ i, β i)
  (φ : Π (s : finset ι) (x : dfinsupp.finset ι β s), γ)
  (hφ : ∀ s t x, s ⊆ t → φ s x = φ t (finset_to_finset s t x)) : γ :=
dfinsupp.lift_on f φ $ λ s t x y H,
calc  φ s x
    = φ (s ∪ t) (finset_to_finset _ _ x) : hφ _ _ _ finset.subset_union_left
... = φ (s ∪ t) (finset_to_finset _ _ y) : congr_arg _ (rel_iff.1 H)
... = φ t y : (hφ _ _ _ finset.subset_union_right).symm

@[simp] protected theorem lift_on'_beta {γ : Sort l}
  (φ : Π (s : finset ι) (x : dfinsupp.finset ι β s), γ) (hφ s x) :
  dfinsupp.lift_on' (mk s x) φ hφ = φ s x :=
rfl

instance : has_coe_to_fun (Π₀ i, β i) :=
⟨λ_, Π i, β i, λ f, dfinsupp.lift_on' f
  (λ s x i, if H : i ∈ s then x ⟨i, H⟩ else 0) $
begin
  rintros s t x hst,
  ext i,
  by_cases h1 : i ∈ s,
  { simp [h1, hst h1] },
  by_cases h2 : i ∈ t; simp [h1, h2]
end⟩

@[simp] lemma mk_apply {s : finset ι} {x : dfinsupp.finset ι β s} {i : ι} :
  (mk s x : Π i, β i) i = if H : i ∈ s then x ⟨i, H⟩ else 0 :=
rfl

@[simp] lemma zero_apply {i : ι} : (0 : Π₀ i, β i) i = 0 := rfl

@[extensionality]
lemma ext {f g : Π₀ i, β i} : (∀ i, f i = g i) → f = g :=
begin
  refine dfinsupp.induction_on f (λ s x, _),
  refine dfinsupp.induction_on g (λ t y, _),
  refine λ H, quotient.sound (relation.trans_gen.single ⟨λ i h1 h2, _, λ i h1 h2, _, λ i h1 h2, _⟩),
  { dsimp at *, simpa [h1, h2] using H i },
  { dsimp at *, simpa [h1, h2] using H i },
  { dsimp at *, simpa [h1, h2] using (H i).symm }
end

theorem mk_inj (s : finset ι) : function.injective (@mk ι β _ s) :=
begin
  intros x y H,
  ext i,
  have h1 : (mk s x : Π i, β i) i = (mk s y : Π i, β i) i, {rw H},
  cases i with i hi,
  change i ∈ s at hi,
  dsimp at h1,
  simpa [hi] using h1
end

theorem mk_eq_of_subset {s : finset ι} (t : finset ι) (x : dfinsupp.finset ι β s) (hst : s ⊆ t) :
  mk s x = mk t (finset_to_finset s t x) :=
begin
  ext i, by_cases h1 : i ∈ s; by_cases h2 : i ∈ t; simp [h1, h2], solve_by_elim
end


@[simp] lemma single_apply {i i' b} : (single i b : Π₀ i, β i) i' = (if h : i = i' then eq.rec_on h b else 0) :=
begin
  dsimp [single],
  by_cases h : i = i',
  { have h1 : i' ∈ finset.singleton i, { simp [h] },
    simp [h, h1] },
  { have h1 : i' ∉ finset.singleton i, { simp [ne.symm h] },
    simp [h, h1] }
end

@[simp] lemma single_eq_same {i b} : (single i b : Π₀ i, β i) i = b :=
by simp

@[simp] lemma single_eq_of_ne {i i' b} (h : i ≠ i') : (single i b : Π₀ i, β i) i' = 0 :=
by simp [h]

@[simp] lemma on_finset_apply {s : finset ι} {f : Π i, β i} {i} :
  (on_finset s f : Π₀ i, β i) i = if i ∈ s then f i else 0 :=
by dsimp [on_finset]; split_ifs; refl

section

variables {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
variables [Π i, has_zero (β₁ i)] [Π i, has_zero (β₂ i)]

@[simp] lemma map_range_apply
  {f : Π i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} {i : ι} :
  map_range f hf g i = f i (g i) :=
dfinsupp.induction_on g $ by intros; dsimp [map_range]; split_ifs; simp [hf]

/-- `zip_with f hf g₁ g₂` is the finitely supported function satisfying
  `zip_with f hf g₁ g₂ i = f i (g₁ i) (g₂ i)`, and well defined when `f 0 0 = 0`. -/
def zip_with (f : Π i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) (g₁ : Π₀ i, β₁ i) (g₂ : Π₀ i, β₂ i) : (Π₀ i, β i) :=
begin
  refine dfinsupp.lift_on' g₁ (λ s x, dfinsupp.lift_on' g₂ (λ t y, mk (s ∪ t)
    (λ i, f i.1 (finset_to_finset _ _ x _) (finset_to_finset _ _ y _))) _) _,
  { intros t₁ t₂ y ht,
    refine quotient.sound (relation.trans_gen.single ⟨λ i h1 h2, _, λ i h1 h2, _, λ i h1 h2, _⟩),
    { rw finset_comp ht, refl },
    { exact (h2 $ (finset.mem_union.1 h1).elim
        (finset.mem_union_left _) (finset.mem_union_right _ ∘ @ht i)).elim },
    { rw finset_comp ht,
      have h3 := mt (finset.mem_union_left _) h1,
      have h4 := mt (finset.mem_union_right _) h1,
      simp [h3, h4, hf] } },
  { intros s₁ s₂ x hs,
    refine dfinsupp.induction_on.{u v₂} g₂ (λ t y, _),
    refine quotient.sound (relation.trans_gen.single ⟨λ i h1 h2, _, λ i h1 h2, _, λ i h1 h2, _⟩),
    { rw finset_comp hs, refl },
    { exact (h2 $ (finset.mem_union.1 h1).elim
        (finset.mem_union_left _ ∘ @hs i) (finset.mem_union_right _)).elim },
    { rw finset_comp hs,
      have h3 := mt (finset.mem_union_left _) h1,
      have h4 := mt (finset.mem_union_right _) h1,
      simp [h3, h4, hf] } }
end

@[simp] lemma zip_with_apply
  {f : Π i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i} {g₂ : Π₀ i, β₂ i} {i : ι} :
  zip_with f hf g₁ g₂ i = f i (g₁ i) (g₂ i) :=
begin
  refine dfinsupp.induction_on g₁ (λ s x, _),
  refine dfinsupp.induction_on.{u v₂} g₂ (λ t y, _),
  dsimp [zip_with],
  by_cases h : i ∈ s ∪ t,
  { exact dif_pos h },
  have h1 := mt (finset.mem_union_left _) h,
  have h2 := mt (finset.mem_union_right _) h,
  simp [h, h1, h2, hf]
end

end

def erase (i : ι) (f : Π₀ i, β i) : Π₀ i, β i :=
dfinsupp.lift_on' f (λ s x, mk (s.erase i) (finset_to_finset _ _ x)) $
begin
  intros s t x hst,
  refine quotient.sound (relation.trans_gen.single ⟨λ j h1 h2, _, λ j h1 h2, _, λ j h1 h2, _⟩),
  { rw finset_comp hst, refl },
  { cases finset.mem_erase.1 h1 with h3 h4,
    exact (h2 (finset.mem_erase.2 ⟨h3, hst h4⟩)).elim },
  { rw finset_comp hst,
    cases finset.mem_erase.1 h2 with h3 h4,
    have h5 := mt (finset.mem_erase.2 ∘ and.intro h3) h1,
    simp [h5] }
end

@[simp] lemma erase_apply {i j : ι} {f : Π₀ i, β i} :
  (f.erase i) j = if j = i then 0 else f j :=
begin
  refine dfinsupp.induction_on f (λ s x, _),
  dsimp [erase],
  by_cases h1 : j = i,
  { simp [h1] },
  by_cases h2 : j ∈ s;
  simp [h1, h2]
end

@[simp] lemma erase_same {i : ι} {f : Π₀ i, β i} : (f.erase i) i = 0 :=
by simp

@[simp] lemma erase_ne {i i' : ι} {f : Π₀ i, β i} (h : i' ≠ i) : (f.erase i) i' = f i' :=
by simp [h]

end basic

section add_monoid

variable [Π i, add_monoid (β i)]

instance : has_add (Π₀ i, β i) :=
⟨zip_with (λ i, (+)) (λ i, add_zero 0)⟩

@[simp] lemma add_apply [Π i, add_monoid (β i)] {g₁ g₂ : Π₀ i, β i} {i : ι} : (g₁ + g₂) i = g₁ i + g₂ i :=
zip_with_apply

@[simp] lemma single_add {i : ι} {b₁ b₂ : β i} : single i (b₁ + b₂) = single i b₁ + single i b₂ :=
ext $ assume i',
begin
  by_cases h : i = i',
  { subst h, rw [add_apply, single_eq_same, single_eq_same, single_eq_same] },
  { rw [add_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, zero_add] }
end

instance : add_monoid (Π₀ i, β i) :=
{ zero      := 0,
  add       := (+),
  add_assoc := λ x y z, ext $ by simp,
  zero_add  := λ x, ext $ by simp,
  add_zero  := λ x, ext $ by simp }

lemma single_add_erase {i : ι} {f : Π₀ i, β i} : single i (f i) + f.erase i = f :=
ext $ λ i',
if h : i = i' then by subst h; simp
else by simp [ne.symm h, h]

lemma erase_add_single {i : ι} {f : Π₀ i, β i} : f.erase i + single i (f i) = f :=
ext $ λ i',
if h : i = i' then by subst h; simp
else by simp [ne.symm h, h]

protected theorem induction {p : (Π₀ i, β i) → Prop} (f : Π₀ i, β i)
  (h0 : p 0) (ha : ∀i b (f : Π₀ i, β i), f i = 0 → b ≠ 0 → p f → p (single i b + f)) :
  p f :=
begin
  refine dfinsupp.induction_on f (λ s, _),
  apply finset.induction_on s,
  { intro x, convert h0, ext i, exact i.2.elim },
  intros i s hs ih x,
  rw ← (single_add_erase : single i _ + _ = mk (insert i s) x),
  dsimp [erase],
  rw [finset.erase_insert hs, dif_pos (finset.mem_insert_self i s)],
  generalize hz : x ⟨i, _⟩ = z,
  cases classical.em (z = 0) with H H,
  { rw [H, single_zero, zero_add], apply ih },
  exact ha _ _ _ (by simp [hs]) H (ih _)
end

lemma induction₂ {p : (Π₀ i, β i) → Prop} (f : Π₀ i, β i)
  (h0 : p 0) (ha : ∀i b (f : Π₀ i, β i), f i = 0 → b ≠ 0 → p f → p (f + single i b)) :
  p f :=
dfinsupp.induction f h0 $ λ i b f h1 h2 h3,
have h4 : f + single i b = single i b + f,
{ ext j, by_cases H : i = j,
  { subst H, simp [h1] },
  { simp [H] } },
eq.rec_on h4 $ ha i b f h1 h2 h3

end add_monoid

instance [Π i, add_comm_monoid (β i)] : add_comm_monoid (Π₀ i, β i) :=
{ add_comm := λ x y, ext $ by simp,
  .. dfinsupp.add_monoid }

@[simp] lemma neg_apply [Π i, add_group (β i)] {g : Π₀ i, β i} {i : ι} : (- g) i = - g i :=
map_range_apply

instance [Π i, add_group (β i)] : add_group (Π₀ i, β i) :=
{ add_left_neg := λ f, ext $ by simp,
  .. dfinsupp.add_monoid,
  .. (infer_instance : has_neg (Π₀ i, β i)) }

@[simp] lemma sub_apply [Π i, add_group (β i)] {g₁ g₂ : Π₀ i, β i} {i : ι} : (g₁ - g₂) i = g₁ i - g₂ i :=
by rw [sub_eq_add_neg]; simp

instance [Π i, add_comm_group (β i)] : add_comm_group (Π₀ i, β i) :=
{ add_comm := λ _ _, ext $ by simp, ..dfinsupp.add_group }

@[simp] lemma filter_apply [Π i, has_zero (β i)]
  {p : ι → Prop} [decidable_pred p] {i : ι} {f : Π₀ i, β i} :
  f.filter p i = if p i then f i else 0 :=
begin
  refine dfinsupp.induction_on f (λ s x, _),
  dsimp [filter],
  by_cases h1 : p i; by_cases h2 : i ∈ s; simp [h1, h2]
end

@[simp] lemma filter_apply_pos [Π i, has_zero (β i)]
  {p : ι → Prop} [decidable_pred p] {f : Π₀ i, β i} {i : ι} (h : p i) :
  f.filter p i = f i :=
by simp [h]

@[simp] lemma filter_apply_neg [Π i, has_zero (β i)]
  {p : ι → Prop} [decidable_pred p] {f : Π₀ i, β i} {i : ι} (h : ¬ p i) :
  f.filter p i = 0 :=
by simp [h]

lemma filter_pos_add_filter_neg [Π i, add_monoid (β i)] {f : Π₀ i, β i}
  {p : ι → Prop} [decidable_pred p] :
  f.filter p + f.filter (λi, ¬ p i) = f :=
dfinsupp.ext $ assume i, by by_cases p i; simp *

@[simp] lemma subtype_domain_apply [Π i, has_zero (β i)] {p : ι → Prop} [decidable_pred p]
  {i : subtype p} {v : Π₀ i, β i} :
  (subtype_domain p v) i = v (i.val) :=
begin
  refine dfinsupp.induction_on v (λ s x, _),
  by_cases h1 : i.1 ∈ s,
  { dsimp [subtype_domain], simp [h1], refl },
  { dsimp [subtype_domain], simp [h1] }
end

@[simp] lemma subtype_domain_add [Π i, add_monoid (β i)] {p : ι → Prop} [decidable_pred p] {v v' : Π₀ i, β i} :
  (v + v').subtype_domain p = v.subtype_domain p + v'.subtype_domain p :=
ext $ by simp

@[simp] lemma subtype_domain_neg [Π i, add_group (β i)] {p : ι → Prop} [decidable_pred p] {v : Π₀ i, β i} :
  (- v).subtype_domain p = - v.subtype_domain p :=
ext $ by simp

@[simp] lemma subtype_domain_sub [Π i, add_group (β i)] {p : ι → Prop} [decidable_pred p] {v v' : Π₀ i, β i} :
  (v - v').subtype_domain p = v.subtype_domain p - v'.subtype_domain p :=
ext $ by simp

local attribute [instance] to_has_scalar'

@[simp] lemma smul_apply' {γ : Type w} [ring γ] [Π i, module γ (β i)] {i : ι} {b : γ} {v : Π₀ i, β i} :
  (b • v) i = b • (v i) :=
map_range_apply

def to_module {γ : Type w} [ring γ] [Π i, module γ (β i)] : module γ (Π₀ i, β i) :=
{ smul_add := assume i x y, dfinsupp.ext $ by simp [smul_add],
  add_smul := assume i x y, dfinsupp.ext $ by simp [add_smul],
  one_smul := assume x, dfinsupp.ext $ by simp,
  mul_smul := assume r s x, dfinsupp.ext $ by simp [smul_smul],
  .. dfinsupp.add_comm_group,
  .. (infer_instance : has_scalar γ (Π₀ i, β i)) }

lemma finite_supp [Π i, has_zero (β i)] (f : Π₀ i, β i) : set.finite {i | f i ≠ 0} :=
begin
  refine dfinsupp.induction_on f (λ s x, _),
  apply set.finite_subset (set.finite_mem_finset s),
  intros i h1,
  by_contra h2,
  change i ∉ s at h2,
  simpa [h2] using h1
end

section support_basic

variables [Π i, has_zero (β i)] [Π i, decidable_pred (eq (0 : β i))]

def support (f : Π₀ i, β i) : finset ι :=
dfinsupp.lift_on' f (λ s x, s.filter $ λ i, ∃ h : i ∈ s, x ⟨i, h⟩ ≠ 0) $
begin
  intros s t x hst,
  ext i, split,
  { intro H,
    rcases finset.mem_filter.1 H with ⟨h1, h2, h3⟩,
    exact finset.mem_filter.2 ⟨hst h1, hst h1, by simp [h1, h3]⟩ },
  { intro H,
    rcases finset.mem_filter.1 H with ⟨h1, h2, h3⟩,
    have h4 : i ∈ s,
    { by_contra h4, simpa [h4] using h3 },
    exact finset.mem_filter.2 ⟨h4, h4, by simpa [h4] using h3⟩ }
end

@[simp] theorem support_mk_subset {s : finset ι} {x : dfinsupp.finset ι β s} : (mk s x).support ⊆ s :=
finset.filter_subset _

@[simp] theorem mem_support_to_fun (f : Π₀ i, β i) (i) : i ∈ f.support ↔ f i ≠ 0 :=
begin
  refine dfinsupp.induction_on f (λ s x, _),
  by_cases h1 : i ∈ s; simp [h1, support]
end

theorem eq_mk_support (f : Π₀ i, β i) : f = mk f.support (λ i, f i.1) :=
by ext i; by_cases h : f i = 0; try {simp at h}; simp [h]

@[simp] lemma support_zero : (0 : Π₀ i, β i).support = ∅ := rfl

@[simp] lemma mem_support_iff (f : Π₀ i, β i) : ∀i:ι, i ∈ f.support ↔ f i ≠ 0 :=
f.mem_support_to_fun

@[simp] lemma support_eq_empty {f : Π₀ i, β i} : f.support = ∅ ↔ f = 0 :=
⟨λ H, ext $ by simpa [finset.ext] using H, by simp {contextual:=tt}⟩

instance decidable_zero : decidable_pred (eq (0 : Π₀ i, β i)) :=
λ f, decidable_of_iff _ $ support_eq_empty.trans eq_comm

lemma support_subset_iff {s : set ι} {f : Π₀ i, β i} :
  ↑f.support ⊆ s ↔ (∀i∉s, f i = 0) :=
by simp [set.subset_def];
   exact forall_congr (assume i, @not_imp_comm _ _ (classical.dec _) (classical.dec _))

lemma support_single_ne_zero {i : ι} {b : β i} (hb : b ≠ 0) : (single i b).support = {i} :=
begin
  ext j, by_cases h : i = j,
  { subst h, simp [hb] },
  simp [ne.symm h, h]
end

lemma support_single_subset {i : ι} {b : β i} : (single i b).support ⊆ {i} :=
support_mk_subset

@[simp] lemma support_on_finset_subset {s : finset ι} {f : Π i, β i} :
  (on_finset s f).support ⊆ s :=
support_mk_subset

section map_range_and_zip_with

variables {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
variables [Π i, has_zero (β₁ i)] [Π i, has_zero (β₂ i)]
variables [Π i, decidable_pred (eq (0 : β₁ i))] [Π i, decidable_pred (eq (0 : β₂ i))]

lemma map_range_def {f : Π i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} :
  map_range f hf g = mk g.support (λ i, f i.1 (g i.1)) :=
begin
  ext i,
  by_cases h : g i = 0,
  { simp [h, hf] },
  { simp at h, simp [h, hf] }
end

lemma support_map_range {f : Π i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} :
  (map_range f hf g).support ⊆ g.support :=
by simp [map_range_def]

@[simp] lemma map_range_single {f : Π i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {i : ι} {b : β₁ i} :
  map_range f hf (single i b) = single i (f i b) :=
dfinsupp.ext $ λ i', by by_cases i = i'; [{subst i', simp}, simp [h, hf]]

lemma zip_with_def {f : Π i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i} {g₂ : Π₀ i, β₂ i} :
  zip_with f hf g₁ g₂ = mk (g₁.support ∪ g₂.support) (λ i, f i.1 (g₁ i.1) (g₂ i.1)) :=
begin
  ext i,
  by_cases h1 : g₁ i = 0; by_cases h2 : g₂ i = 0;
  try {simp at h1 h2}; simp [h1, h2, hf]
end

lemma support_zip_with {f : Π i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i} {g₂ : Π₀ i, β₂ i} :
  (zip_with f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support :=
by simp [zip_with_def]

end map_range_and_zip_with

lemma erase_def (i : ι) (f : Π₀ i, β i) :
  f.erase i = mk (f.support.erase i) (λ j, f j.1) :=
begin
  ext j,
  by_cases h1 : j = i; by_cases h2 : f j = 0;
  try {simp at h2}; simp [h1, h2]
end

@[simp] lemma support_erase (i : ι) (f : Π₀ i, β i) :
  (f.erase i).support = f.support.erase i :=
begin
  ext j,
  by_cases h1 : j = i; by_cases h2 : f j = 0;
  try {simp at h2}; simp [h1, h2]
end

section filter_and_subtype_domain

variables {p : ι → Prop} [decidable_pred p]

lemma filter_def (f : Π₀ i, β i) :
  f.filter p = mk (f.support.filter p) (λ i, f i.1) :=
by ext i; by_cases h1 : p i; by_cases h2 : f i = 0;
try {simp at h2}; simp [h1, h2]

@[simp] lemma support_filter (f : Π₀ i, β i) :
  (f.filter p).support = f.support.filter p :=
by ext i; by_cases h : p i; simp [h]

lemma subtype_domain_def (f : Π₀ i, β i) :
  f.subtype_domain p = mk (f.support.subtype p) (λ i, f i.1) :=
by ext i; cases i with i hi;
by_cases h1 : p i; by_cases h2 : f i = 0;
try {simp at h2}; dsimp; simp [h1, h2]

@[simp] lemma support_subtype_domain {f : Π₀ i, β i} :
  (subtype_domain p f).support = f.support.subtype p :=
by ext i; cases i with i hi;
by_cases h1 : p i; by_cases h2 : f i = 0;
try {simp at h2}; dsimp; simp [h1, h2]

end filter_and_subtype_domain

end support_basic

lemma support_add [Π i, add_monoid (β i)] [Π i, decidable_pred (eq (0 : β i))] {g₁ g₂ : Π₀ i, β i} :
  (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support :=
support_zip_with

@[simp] lemma support_neg [Π i, add_group (β i)] [Π i, decidable_pred (eq (0 : β i))] {f : Π₀ i, β i} :
  support (-f) = support f :=
by ext i; simp

instance [decidable_eq ι] [Π i, has_zero (β i)] [Π i, decidable_eq (β i)] : decidable_eq (Π₀ i, β i) :=
assume f g, decidable_of_iff (f.support = g.support ∧ (∀i∈f.support, f i = g i))
  ⟨assume ⟨h₁, h₂⟩, ext $ assume i,
      if h : i ∈ f.support then h₂ i h else
        have hf : f i = 0, by rwa [f.mem_support_iff, not_not] at h,
        have hg : g i = 0, by rwa [h₁, g.mem_support_iff, not_not] at h,
        by rw [hf, hg],
    by intro h; subst h; simp⟩

section prod_and_sum

variables {γ : Type w}

-- [to_additive dfinsupp.sum] for dfinsupp.prod doesn't work, the equation lemmas are not generated
/-- `sum f g` is the sum of `g i (f i)` over the support of `f`. -/
def sum [Π i, has_zero (β i)] [Π i, decidable_pred (eq (0 : β i))] [add_comm_monoid γ]
  (f : Π₀ i, β i) (g : Π i, β i → γ) : γ :=
f.support.sum (λi, g i (f i))

/-- `prod f g` is the product of `g i (f i)` over the support of `f`. -/
@[to_additive dfinsupp.sum]
def prod [Π i, has_zero (β i)] [Π i, decidable_pred (eq (0 : β i))] [comm_monoid γ]
  (f : Π₀ i, β i) (g : Π i, β i → γ) : γ :=
f.support.prod (λi, g i (f i))
attribute [to_additive dfinsupp.sum.equations._eqn_1] dfinsupp.prod.equations._eqn_1

@[to_additive dfinsupp.sum_map_range_index]
lemma prod_map_range_index {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
  [Π i, has_zero (β₁ i)] [Π i, has_zero (β₂ i)]
  [Π i, decidable_pred (eq (0 : β₁ i))] [Π i, decidable_pred (eq (0 : β₂ i))] [comm_monoid γ]
  {f : Π i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} {h : Π i, β₂ i → γ} (h0 : ∀i, h i 0 = 1) :
  (map_range f hf g).prod h = g.prod (λi b, h i (f i b)) :=
begin
  rw [map_range_def],
  refine (finset.prod_subset support_mk_subset _).trans _,
  { intros i h1 h2,
    dsimp, simp [h1] at h2, dsimp at h2,
    simp [h1, h2, h0] },
  { refine finset.prod_congr rfl _,
    intros i h1,
    simp [h1] }
end

@[to_additive dfinsupp.sum_zero_index]
lemma prod_zero_index [Π i, add_comm_monoid (β i)] [Π i, decidable_pred (eq (0 : β i))] [comm_monoid γ]
  {h : Π i, β i → γ} : (0 : Π₀ i, β i).prod h = 1 :=
rfl

@[to_additive dfinsupp.sum_single_index]
lemma prod_single_index [Π i, has_zero (β i)] [Π i, decidable_pred (eq (0 : β i))] [comm_monoid γ]
  {i : ι} {b : β i} {h : Π i, β i → γ} (h_zero : h i 0 = 1) :
  (single i b).prod h = h i b :=
begin
  by_cases h : b = 0,
  { simp [h, prod_zero_index, h_zero], refl },
  { simp [dfinsupp.prod, support_single_ne_zero h] }
end

@[to_additive dfinsupp.sum_neg_index]
lemma prod_neg_index [Π i, add_group (β i)] [Π i, decidable_pred (eq (0 : β i))] [comm_monoid γ]
  {g : Π₀ i, β i} {h : Π i, β i → γ} (h0 : ∀i, h i 0 = 1) :
  (-g).prod h = g.prod (λi b, h i (- b)) :=
prod_map_range_index h0

@[simp] lemma sum_apply {ι₁ : Type u₁} [decidable_eq ι₁] {β₁ : ι₁ → Type v₁}
  [Π i₁, has_zero (β₁ i₁)] [Π i, decidable_pred (eq (0 : β₁ i))]
  [Π i, add_comm_monoid (β i)]
  {f : Π₀ i₁, β₁ i₁} {g : Π i₁, β₁ i₁ → Π₀ i, β i} {i₂ : ι} :
  (f.sum g) i₂ = f.sum (λi₁ b, g i₁ b i₂) :=
(finset.sum_hom (λf : Π₀ i, β i, f i₂) rfl (assume i b, add_apply)).symm

lemma support_sum {ι₁ : Type u₁} [decidable_eq ι₁] {β₁ : ι₁ → Type v₁}
  [Π i₁, has_zero (β₁ i₁)] [Π i, decidable_pred (eq (0 : β₁ i))]
  [Π i, add_comm_monoid (β i)] [Π i, decidable_pred (eq (0 : β i))]
  {f : Π₀ i₁, β₁ i₁} {g : Π i₁, β₁ i₁ → Π₀ i, β i} :
  (f.sum g).support ⊆ f.support.bind (λi, (g i (f i)).support) :=
have ∀i₁ : ι, f.sum (λ (i : ι₁) (b : β₁ i), (g i b) i₁) ≠ 0 →
    (∃ (i : ι₁), f i ≠ 0 ∧ ¬ (g i (f i)) i₁ = 0),
  from assume i₁ h,
  let ⟨i, hi, ne⟩ := finset.exists_ne_zero_of_sum_ne_zero h in
  ⟨i, (f.mem_support_iff i).mp hi, ne⟩,
by simpa [finset.subset_iff, mem_support_iff, finset.mem_bind, sum_apply] using this

@[simp] lemma sum_zero [Π i, add_comm_monoid (β i)] [Π i, decidable_pred (eq (0 : β i))]
  [add_comm_monoid γ] {f : Π₀ i, β i} :
  f.sum (λi b, (0 : γ)) = 0 :=
finset.sum_const_zero

@[simp] lemma sum_add [Π i, add_comm_monoid (β i)] [Π i, decidable_pred (eq (0 : β i))]
  [add_comm_monoid γ] {f : Π₀ i, β i} {h₁ h₂ : Π i, β i → γ} :
  f.sum (λi b, h₁ i b + h₂ i b) = f.sum h₁ + f.sum h₂ :=
finset.sum_add_distrib

@[simp] lemma sum_neg [Π i, add_comm_monoid (β i)] [Π i, decidable_pred (eq (0 : β i))]
  [add_comm_group γ] {f : Π₀ i, β i} {h : Π i, β i → γ} :
  f.sum (λi b, - h i b) = - f.sum h :=
finset.sum_hom (@has_neg.neg γ _) neg_zero (assume i b, neg_add _ _)

@[to_additive dfinsupp.sum_add_index]
lemma prod_add_index [Π i, add_comm_monoid (β i)] [Π i, decidable_pred (eq (0 : β i))]
  [comm_monoid γ] {f g : Π₀ i, β i}
  {h : Π i, β i → γ} (h_zero : ∀i, h i 0 = 1) (h_add : ∀i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
  (f + g).prod h = f.prod h * g.prod h :=
have f_eq : (f.support ∪ g.support).prod (λi, h i (f i)) = f.prod h,
  from (finset.prod_subset finset.subset_union_left $
    by simp [mem_support_iff, h_zero] {contextual := tt}).symm,
have g_eq : (f.support ∪ g.support).prod (λi, h i (g i)) = g.prod h,
  from (finset.prod_subset finset.subset_union_right $
    by simp [mem_support_iff, h_zero] {contextual := tt}).symm,
calc (f + g).support.prod (λi, h i ((f + g) i)) =
      (f.support ∪ g.support).prod (λi, h i ((f + g) i)) :
    finset.prod_subset support_add $
      by simp [mem_support_iff, h_zero] {contextual := tt}
  ... = (f.support ∪ g.support).prod (λi, h i (f i)) *
      (f.support ∪ g.support).prod (λi, h i (g i)) :
    by simp [h_add, finset.prod_mul_distrib]
  ... = _ : by rw [f_eq, g_eq]

lemma sum_sub_index [Π i, add_comm_group (β i)] [Π i, decidable_pred (eq (0 : β i))]
  [add_comm_group γ] {f g : Π₀ i, β i}
  {h : Π i, β i → γ} (h_sub : ∀i b₁ b₂, h i (b₁ - b₂) = h i b₁ - h i b₂) :
  (f - g).sum h = f.sum h - g.sum h :=
have h_zero : ∀i, h i 0 = 0,
  from assume i,
  have h i (0 - 0) = h i 0 - h i 0, from h_sub i 0 0,
  by simpa using this,
have h_neg : ∀i b, h i (- b) = - h i b,
  from assume i b,
  have h i (0 - b) = h i 0 - h i b, from h_sub i 0 b,
  by simpa [h_zero] using this,
have h_add : ∀i b₁ b₂, h i (b₁ + b₂) = h i b₁ + h i b₂,
  from assume i b₁ b₂,
  have h i (b₁ - (- b₂)) = h i b₁ - h i (- b₂), from h_sub i b₁ (-b₂),
  by simpa [h_neg] using this,
by simp [@sum_add_index ι β _ γ _ _ _ f (-g) h h_zero h_add];
simp [@sum_neg_index ι β _ γ _ _ _ g h h_zero, h_neg];
simp [@sum_neg ι β _ γ _ _ _ g h]

@[to_additive dfinsupp.sum_finset_sum_index]
lemma prod_finset_sum_index {γ : Type w} {α : Type x}
  [Π i, add_comm_monoid (β i)] [Π i, decidable_pred (eq (0 : β i))]
  [comm_monoid γ] [decidable_eq α]
  {s : finset α} {g : α → Π₀ i, β i}
  {h : Π i, β i → γ} (h_zero : ∀i, h i 0 = 1) (h_add : ∀i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂):
  s.prod (λi, (g i).prod h) = (s.sum g).prod h :=
finset.induction_on s
  (by simp [prod_zero_index])
  (by simp [prod_add_index, h_zero, h_add] {contextual := tt})

@[to_additive dfinsupp.sum_sum_index]
lemma prod_sum_index  {ι₁ : Type u₁} [decidable_eq ι₁] {β₁ : ι₁ → Type v₁}
  [Π i₁, has_zero (β₁ i₁)] [Π i, decidable_pred (eq (0 : β₁ i))]
  [Π i, add_comm_monoid (β i)] [Π i, decidable_pred (eq (0 : β i))]
  [comm_monoid γ]
  {f : Π₀ i₁, β₁ i₁} {g : Π i₁, β₁ i₁ → Π₀ i, β i}
  {h : Π i, β i → γ} (h_zero : ∀i, h i 0 = 1) (h_add : ∀i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂):
  (f.sum g).prod h = f.prod (λi b, (g i b).prod h) :=
(prod_finset_sum_index h_zero h_add).symm

@[simp] lemma sum_single [Π i, add_comm_monoid (β i)]
  [Π i, decidable_pred (eq (0 : β i))] {f : Π₀ i, β i} :
  f.sum single = f :=
begin
  apply dfinsupp.induction f, {rw [sum_zero_index]},
  intros i b f H hb ih,
  rw [sum_add_index, ih, sum_single_index],
  all_goals { intros, simp }
end

@[to_additive dfinsupp.sum_subtype_domain_index]
lemma prod_subtype_domain_index [Π i, has_zero (β i)] [Π i, decidable_pred (eq (0 : β i))]
  [comm_monoid γ] {v : Π₀ i, β i} {p : ι → Prop} [decidable_pred p]
  {h : Π i, β i → γ} (hp : ∀x∈v.support, p x) :
  (v.subtype_domain p).prod (λi b, h i.1 b) = v.prod h :=
finset.prod_bij (λp _, p.val)
  (by simp)
  (by simp)
  (assume ⟨a₀, ha₀⟩ ⟨a₁, ha₁⟩, by simp)
  (λ i hi, ⟨⟨i, hp i hi⟩, by simpa using hi, rfl⟩)

lemma subtype_domain_sum [Π i, add_comm_monoid (β i)] [Π i, decidable_pred (eq (0 : β i))]
  {s : finset γ} {h : γ → Π₀ i, β i} {p : ι → Prop} [decidable_pred p] :
  (s.sum h).subtype_domain p = s.sum (λc, (h c).subtype_domain p) :=
eq.symm (finset.sum_hom _ subtype_domain_zero $ assume v v', subtype_domain_add)

lemma subtype_domain_finsupp_sum {δ : γ → Type x} [decidable_eq γ]
  [Π c, has_zero (δ c)] [Π c, decidable_pred (eq (0 : δ c))]
  [Π i, add_comm_monoid (β i)] [Π i, decidable_pred (eq (0 : β i))]
  {p : ι → Prop} [decidable_pred p]
  {s : Π₀ c, δ c} {h : Π c, δ c → Π₀ i, β i} :
  (s.sum h).subtype_domain p = s.sum (λc d, (h c d).subtype_domain p) :=
subtype_domain_sum

end prod_and_sum

end dfinsupp