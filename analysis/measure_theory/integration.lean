import analysis.measure_theory.measure_space algebra.pi_instances
noncomputable theory
open lattice set
local attribute [instance] classical.prop_decidable

namespace measure_theory
variables {α : Type*} [measure_space α] {β : Type*} {γ : Type*}

structure {u v} simple_func' (α : Type u) [measure_space α] (β : Type v) :=
(to_fun : α → β)
(measurable_sn : ∀ x, is_measurable (to_fun ⁻¹' {x}))
(finite : (set.range to_fun).finite)
local infixr ` →ₛ `:25 := simple_func'

namespace simple_func'

instance has_coe_to_fun : has_coe_to_fun (α →ₛ β) := ⟨_, to_fun⟩

@[extensionality] theorem ext {f g : α →ₛ β} (H : ∀ a, f a = g a) : f = g :=
by cases f; cases g; congr; exact funext H

protected def range (f : α →ₛ β) := f.finite.to_finset

@[simp] theorem mem_range {f : α →ₛ β} {b} :
  b ∈ f.range ↔ ∃ a, f a = b := finite.mem_to_finset

def itg (f : α →ₛ ennreal) : ennreal :=
f.range.sum (λ x, x * volume (f ⁻¹' {x}))

def const (b : β) : α →ₛ β :=
⟨λ a, b, λ x, is_measurable.const _,
  finite_subset (set.finite_singleton b) $ by rintro _ ⟨a, rfl⟩; simp⟩

@[simp] theorem const_apply (a : α) (b : β) : (const b : α →ₛ β) a = b := rfl

lemma is_measurable_cut (p : α → β → Prop) (f : α →ₛ β)
  (h : ∀b, is_measurable {a | p a b}) : is_measurable {a | p a (f a)} :=
begin
  rw (_ : {a | p a (f a)} = ⋃ b ∈ set.range f, {a | p a b} ∩ f ⁻¹' {b}),
  { exact is_measurable.bUnion (countable_finite f.finite)
      (λ b _, is_measurable.inter (h b) (f.measurable_sn _)) },
  ext a, simp,
  exact ⟨λ h, ⟨_, ⟨a, rfl⟩, h, rfl⟩, λ ⟨_, ⟨a', rfl⟩, h', e⟩, e.symm ▸ h'⟩
end

theorem preimage_measurable (f : α →ₛ β) (s) : is_measurable (f ⁻¹' s) :=
is_measurable_cut (λ _ b, b ∈ s) f (λ b, by simp [is_measurable.const])

theorem measurable [measurable_space β] (f : α →ₛ β) : measurable f :=
λ s _, preimage_measurable f s

def ite {s : set α} (hs : is_measurable s) (f g : α →ₛ β) : α →ₛ β :=
⟨λ a, if a ∈ s then f a else g a,
 λ x, by letI : measurable_space β := ⊤; exact
   measurable.if hs f.measurable g.measurable _ trivial,
 finite_subset (finite_union f.finite g.finite) begin
   rintro _ ⟨a, rfl⟩,
   by_cases a ∈ s; simp [h],
   exacts [or.inl ⟨_, rfl⟩, or.inr ⟨_, rfl⟩]
 end⟩

@[simp] theorem ite_apply {s : set α} (hs : is_measurable s)
  (f g : α →ₛ β) (a) : ite hs f g a = if a ∈ s then f a else g a := rfl

def bind (f : α →ₛ β) (g : β → α →ₛ γ) : α →ₛ γ :=
⟨λa, g (f a) a,
 λ c, is_measurable_cut (λa b, g b a ∈ ({c} : set γ)) f (λ b, (g b).measurable_sn c),
 finite_subset (finite_bUnion f.finite (λ b, (g b).finite)) $
 by rintro _ ⟨a, rfl⟩; simp; exact ⟨_, ⟨a, rfl⟩, _, rfl⟩⟩

@[simp] theorem bind_apply (f : α →ₛ β) (g : β → α →ₛ γ) (a) :
  f.bind g a = g (f a) a := rfl

def restrict [has_zero β] (f : α →ₛ β) (s : set α) : α →ₛ β :=
if hs : is_measurable s then ite hs f (const 0) else const 0

@[simp] theorem restrict_apply [has_zero β]
  (f : α →ₛ β) {s : set α} (hs : is_measurable s) (a) :
  restrict f s a = if a ∈ s then f a else 0 :=
by unfold_coes; simp [restrict, hs]; apply ite_apply hs

theorem restrict_preimage [has_zero β]
  (f : α →ₛ β) {s : set α} (hs : is_measurable s)
  {t : set β} (ht : (0:β) ∉ t) : restrict f s ⁻¹' t = s ∩ f ⁻¹' t :=
by ext a; dsimp; rw [restrict_apply]; by_cases a ∈ s; simp [h, hs, ht]

def map (g : β → γ) (f : α →ₛ β) : α →ₛ γ := bind f (const ∘ g)

@[simp] theorem map_apply (g : β → γ) (f : α →ₛ β) (a) : f.map g a = g (f a) := rfl

def seq (f : α →ₛ (β → γ)) (g : α →ₛ β) : α →ₛ γ := _

def pair (f : α →ₛ β) (g : α →ₛ γ) : α →ₛ (β × γ) := _

@[simp] theorem map_apply (g : β → γ) (f : α →ₛ β) (a) : f.map g a = g (f a) := rfl

theorem bind_const (f : α →ₛ β) : f.bind const = f := by ext; simp

lemma bind_itg (f : α →ₛ β) (g : β → α →ₛ ennreal) :
  (f.bind g).itg = f.range.sum (λ b, (restrict (g b) (f ⁻¹' {b})).itg) :=
_

lemma map_itg (g : β → ennreal) (f : α →ₛ β) :
  (f.map g).itg = f.range.sum (λ x, g x * volume (f ⁻¹' {x})) :=
_
#check (by apply_instance : canonically_ordered_monoid ℕ)
#exit
lemma seq_itg (f : α →ₛ (β → ennreal)) (g : α →ₛ β) :
  (f.seq g).itg = f.range.sum (λ b,
    g.range.sum $ λ a, b a * volume (f ⁻¹' {b} ∩ g ⁻¹' {a})) :=
_

lemma bind_sum_measure (f : α →ₛ β) (g : β → (α →ₛ ennreal)) :
  (f.bind g).itg = ∑ b x, x * volume (f ⁻¹' {b} ∩ g b ⁻¹' {x}) :=
_

theorem coe_def (f : simple_func' α) : coe_fn f = (f.map indicator.to_fun).sum := rfl

instance : add_comm_monoid (simple_func' α) :=
by unfold simple_func'; apply_instance

instance : has_mem (indicator α) (simple_func' α) :=
by unfold simple_func'; apply_instance

instance : preorder (simple_func' α) :=
{ le := λ f g, ∀ a, f a ≤ g a,
  le_refl := λ f a, le_refl _,
  le_trans := λ f g h h₁ h₂ a, le_trans (h₁ a) (h₂ a) }

theorem le_def {f g : simple_func' α} : f ≤ g ↔ ∀ a, f a ≤ g a := iff.rfl
theorem coe_le_coe {f g : simple_func' α} : f ≤ g ↔ ⇑f ≤ g := iff.rfl

end simple_func'

structure indicator (α : Type*) [measure_space α] :=
(height : ennreal)
(val : set α)
(measurable : is_measurable val)

def indicator.size (I : indicator α) : ennreal :=
I.height * volume I.val

def indicator.to_fun (I : indicator α) (a : α) : ennreal :=
if a ∈ I.val then I.height else 0

instance indicator.has_coe_to_fun : has_coe_to_fun (indicator α) := ⟨_, indicator.to_fun⟩

theorem indicator.to_fun_val (I : indicator α) (a : α) :
  I a = if a ∈ I.val then I.height else 0 := rfl

def simple_func (α) [measure_space α] := multiset (indicator α)

namespace simple_func

def itg (f : simple_func α) : ennreal := (f.map indicator.size).sum

def to_fun (f : simple_func α) : α → ennreal := (f.map indicator.to_fun).sum

instance has_coe_to_fun : has_coe_to_fun (simple_func α) := ⟨_, to_fun⟩

theorem coe_def (f : simple_func α) : coe_fn f = (f.map indicator.to_fun).sum := rfl

instance : add_comm_monoid (simple_func α) :=
by unfold simple_func; apply_instance

instance : has_mem (indicator α) (simple_func α) :=
by unfold simple_func; apply_instance

instance : preorder (simple_func α) :=
{ le := λ f g, ∀ a, f a ≤ g a,
  le_refl := λ f a, le_refl _,
  le_trans := λ f g h h₁ h₂ a, le_trans (h₁ a) (h₂ a) }

theorem le_def {f g : simple_func α} : f ≤ g ↔ ∀ a, f a ≤ g a := iff.rfl
theorem coe_le_coe {f g : simple_func α} : f ≤ g ↔ ⇑f ≤ g := iff.rfl

instance : setoid (simple_func α) :=
{ r := λ f g, f.to_fun = g.to_fun,
  iseqv := preimage_equivalence _ eq_equivalence }

theorem equiv_def {f g : simple_func α} : f ≈ g ↔ ⇑f = g := iff.rfl

theorem equiv_iff {f g : simple_func α} : f ≈ g ↔ ∀ x, f x = g x :=
function.funext_iff

theorem le_antisymm {f g : simple_func α}
  (h₁ : f ≤ g) (h₂ : g ≤ f) : f ≈ g :=
le_antisymm h₁ h₂

theorem le_antisymm_iff {f g : simple_func α} :
  f ≈ g ↔ f ≤ g ∧ g ≤ f := le_antisymm_iff

@[simp] theorem coe_add (f g : simple_func α) (a) : (f + g) a = f a + g a :=
by simp [coe_def]

theorem add_congr {f₁ f₂ g₁ g₂ : simple_func α}
  (h₁ : f₁ ≈ f₂) (h₂ : g₁ ≈ g₂) : f₁ + g₁ ≈ f₂ + g₂ :=
by simp [equiv_iff, *] at *

theorem le_of_multiset_le {f g : simple_func α}
  (h : @has_le.le (multiset _) _ f g) : f ≤ g :=
begin
  rcases le_iff_exists_add.1 h with ⟨k, rfl⟩,
  intro a, simp [ennreal.le_add_right]
end

theorem itg_zero : itg (0 : simple_func α) = 0 := rfl

theorem itg_add (f g) : itg (f + g : simple_func α) = itg f + itg g :=
by simp [itg]

protected def inter (f : simple_func α) (s : set α) : simple_func α :=
let ⟨s, hs⟩ := (if hs : is_measurable s then ⟨s, hs⟩ else ⟨_, is_measurable.empty⟩ :
  {s:set α // is_measurable s}) in
f.map (λ ⟨a, v, hv⟩, ⟨a, v ∩ s, hv.inter hs⟩)

/-
def refines (f g : simple_func α) : Prop :=
∀ I₁ I₂ : indicator α, I₁ ∈ f → I₂ ∈ g →
  I₂.val ⊆ I₁.val ∨ disjoint I₁.val I₂.val

local infix ` ≼ `:50 := refines

def refined (f g : simple_func α) : simple_func α :=
(multiset.diagonal f).bind $ λ ⟨s, t⟩,
g.inter ((s.map indicator.val).inf ∩
  (t.map (λ I:indicator α, -I.val)).inf)

theorem refined_zero (g : simple_func α) : refined 0 g = g :=
begin
  simp [refined],
end
theorem refined_equiv (f g : simple_func α) : refined f g ≈ g :=
equiv_iff.2 $ λ a, begin
  let s := f.filter (λ I:indicator α, a ∈ I.val),
  let t := (by exact f) - s,

end

theorem refines.trans {f g h : simple_func α}
  (h₁ : f ≼ g) (h₂ : g ≼ h) : f ≼ h :=
_
-/

theorem preimage_measurable (f : simple_func α) : ∀ s, is_measurable (f ⁻¹' s) :=
begin
  refine multiset.induction_on f (λ s, is_measurable.const (0 ∈ s)) (λ I f IH s, _),
  convert ((IH {x | I.height + x ∈ s}).inter I.measurable).union
    ((IH s).diff I.measurable),
  simp [ext_iff, coe_def, indicator.to_fun],
  intro a, by_cases a ∈ I.val; simp [h]
end

theorem measurable [measurable_space ennreal] (f : simple_func α) : measurable f :=
λ s _, preimage_measurable f s

def of_fun (f : α → ennreal) : simple_func α :=
if H : (∀ a, is_measurable (f ⁻¹' {a})) ∧ (range f).finite then
  H.2.to_finset.1.map (λ a, ⟨a, f ⁻¹' {a}, H.1 a⟩)
else 0

theorem of_fun_val {f : α → ennreal}
  (hf : ∀ a, is_measurable (f ⁻¹' {a})) (ff : (range f).finite) :
  of_fun f = ff.to_finset.1.map (λ a, ⟨a, f ⁻¹' {a}, hf a⟩) :=
dif_pos ⟨hf, ff⟩

theorem of_fun_apply (f : α → ennreal)
  (hf : ∀ a, is_measurable (f ⁻¹' {a})) (ff : (range f).finite) (a) :
  (of_fun f : α → ennreal) a = f a :=
begin
  rw [of_fun_val hf ff, ← multiset.cons_erase
    (finite.mem_to_finset.2 ⟨a, rfl⟩ : f a ∈ ff.to_finset.1)],
  simp [coe_def],
  suffices : ∀ (s : multiset ennreal) (_:f a ∉ s),
    (s.map (λ a, indicator.to_fun ⟨a, f ⁻¹' {a}, hf a⟩)).sum a = 0,
  { rw this, {simp [indicator.to_fun]},
    exact finset.not_mem_erase (f a) _ },
  refine λ s, multiset.induction_on s (λ _, rfl) (λ I s IH h, _),
  rw [multiset.mem_cons, not_or_distrib] at h,
  simp [indicator.to_fun, h.1, IH h.2]
end

theorem finite_range (f : simple_func α) : (set.range f).finite :=
begin
  refine multiset.induction_on f _ (λ I f IH, _),
  { refine finite_subset (finite_singleton 0) _,
    rintro _ ⟨a, rfl⟩, simp, refl },
  { refine finite_subset (finite_union IH (finite_image ((+) I.height) IH)) _,
    rintro _ ⟨a, rfl⟩,
    by_cases a ∈ I.val; simp [coe_def, indicator.to_fun, h, -add_comm],
    { exact or.inr ⟨_, ⟨_, rfl⟩, rfl⟩ },
    { exact or.inl ⟨_, rfl⟩ } }
end

def lift₂ (F : ennreal → ennreal → ennreal) (f g : simple_func α) :
  simple_func α := of_fun (λ a, F (f a) (g a))

lemma lift₂_is_measurable {F : ennreal → ennreal → ennreal}
  {f g : simple_func α} (x : ennreal) :
  is_measurable ((λ a, F (f a) (g a)) ⁻¹' {x}) :=
begin
  rw (_ : ((λ a, F (f a) (g a)) ⁻¹' {x}) =
    ⋃ (a ∈ range f) (b ∈ range g) (h : F a b = x), f ⁻¹' {a} ∩ g ⁻¹' {b}),
  { refine is_measurable.bUnion (countable_finite (finite_range _)) (λ a ha, _),
    refine is_measurable.bUnion (countable_finite (finite_range _)) (λ b hb, _),
    refine is_measurable.Union_Prop (λ h,
      (preimage_measurable _ _).inter (preimage_measurable _ _)) },
  simp [ext_iff],
  exact λ a, ⟨λ h, ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, h, rfl, rfl⟩,
    λ ⟨_, ⟨b, rfl⟩, _, ⟨c, rfl⟩, h, h₁, h₂⟩, by clear_; cc⟩
end

lemma lift₂_finite {F : ennreal → ennreal → ennreal}
  {f g : simple_func α} : (set.range (λ a, F (f a) (g a))).finite :=
finite_subset (finite_image (function.uncurry F) $
    finite_prod (finite_range f) (finite_range g)) $
by rintro _ ⟨a, rfl⟩;
   exact ⟨(f a, g a), mem_prod.1 ⟨⟨a, rfl⟩, ⟨a, rfl⟩⟩, rfl⟩

@[simp] theorem lift₂_val (F : ennreal → ennreal → ennreal)
  (f g : simple_func α) : ∀ a, lift₂ F f g a = F (f a) (g a) :=
of_fun_apply _ lift₂_is_measurable lift₂_finite

instance : has_sub (simple_func α) := ⟨lift₂ has_sub.sub⟩

@[simp] theorem sub_val (f g : simple_func α) (a : α) : (f - g) a = f a - g a :=
lift₂_val _ _ _ _

theorem add_sub_cancel_of_le {f g : simple_func α} (h : f ≤ g) : f + (g - f) ≈ g :=
by simp [equiv_iff, λ x, ennreal.add_sub_cancel_of_le (h x)]

theorem sub_add_cancel_of_le {f g : simple_func α} (h : f ≤ g) : g - f + f ≈ g :=
by rw add_comm; exact add_sub_cancel_of_le h

-- `simple_func` is not a `canonically_ordered_monoid` because it is not a partial order
theorem le_iff_exists_add {s t : simple_func α} : s ≤ t ↔ ∃ u, t ≈ s + u :=
⟨λ h, ⟨_, setoid.symm (add_sub_cancel_of_le h)⟩,
 λ ⟨u, e⟩, le_trans (by intro; simp [ennreal.le_add_right]) (le_antisymm_iff.1 e).2⟩

def itg' (f : α → ennreal) : ennreal := ∑ x, x * volume (f ⁻¹' {x})

theorem itg'_eq_sum_of_subset {f : α → ennreal}
  (s : finset ennreal) (H : set.range f ⊆ ↑s) :
  itg' f = s.sum (λ x, x * volume (f ⁻¹' {x})) :=
tsum_eq_sum $ λ x h,
have f ⁻¹' {x} = ∅, from
  eq_empty_iff_forall_not_mem.2 $
  by rintro a (rfl | ⟨⟨⟩⟩); exact h (H ⟨a, rfl⟩),
by simp [this]

theorem itg'_eq_sum {f : α → ennreal} (hf : (set.range f).finite) :
  itg' f = hf.to_finset.sum (λ x, x * volume (f ⁻¹' {x})) :=
itg'_eq_sum_of_subset _ (by simp)

theorem itg'_zero : itg' (λ a : α, 0) = 0 :=
begin
  refine (congr_arg tsum _ : _).trans tsum_zero,
  funext x,
  by_cases x = 0, {simp [h]},
  suffices : (λ (a : α), (0:ennreal)) ⁻¹' {x} = ∅, {simp [this]},
  rw eq_empty_iff_forall_not_mem,
  rintro a (rfl | ⟨⟨⟩⟩), exact h rfl
end

theorem itg'_indicator (I : indicator α) : itg' I = I.size :=
begin
  refine (itg'_eq_sum_of_subset {0, I.height} _).trans _,
  { rintro _ ⟨a, rfl⟩, unfold_coes,
    by_cases a ∈ I.val; simp [indicator.to_fun, finset.to_set, *] },
  by_cases h : a,
  { simpa [indicator.size] },
end

theorem itg'_add (f g : α → ennreal) :
  itg' (f + g) = itg' f + itg' g :=
_

theorem itg'_mono {f g : α → ennreal}
  (h : ∀ x, f x ≤ g x) : itg' f ≤ itg' g :=
begin
  refine (congr_arg tsum _ : _).trans tsum_zero,
  funext x,
  by_cases x = 0, {simp [h]},
  suffices : (λ (a : α), (0:ennreal)) ⁻¹' {x} = ∅, {simp [this]},
  rw eq_empty_iff_forall_not_mem,
  rintro a (rfl | ⟨⟨⟩⟩), exact h rfl
end

theorem itg_mono {s t : simple_func α}
  (h : s ≤ t) : s.itg ≤ t.itg :=
begin

end

end simple_func

def upper_itg (f : α → ennreal) :=
⨅ (s : simple_func α) (hf : f ≤ s), s.itg

def upper_itg_def_subtype (f : α → ennreal) :
  upper_itg f = ⨅ (s : {s : simple_func α // f ≤ s}), s.itg :=
by simp [upper_itg, infi_subtype]

local notation `∫` binders `, ` r:(scoped f, upper_itg f) := r

theorem upper_itg_add_le (f g : α → ennreal) : (∫ a, f a + g a) ≤ (∫ a, f a) + (∫ a, g a) :=
begin
  simp [upper_itg, ennreal.add_infi, ennreal.infi_add],
  refine λ s hf t hg, infi_le_of_le (s + t) (infi_le_of_le _ _),
  { refine λ a, le_trans (add_le_add' (hf a) (hg a)) _, simp },
  { simp }
end

theorem simple_itg_eq (s : multiset (indicator α)) : (s.map indicator.size).sum = ∑ i,  :=

theorem upper_itg_simple (s : multiset (indicator α)) : upper_itg (s.map indicator.to_fun).sum = (s.map indicator.size).sum :=
begin
  refine le_antisymm (infi_le_of_le s (infi_le _ (le_refl _)))
    (le_infi $ λ t, le_infi $ λ st, _),

  simp [upper_itg, ennreal.add_infi, ennreal.infi_add],
  refine λ s hf t hg, infi_le_of_le (s + t) (infi_le_of_le _ _),
  { refine λ a, le_trans (add_le_add' (hf a) (hg a)) _, simp },
  { simp }
end

end measure_theory