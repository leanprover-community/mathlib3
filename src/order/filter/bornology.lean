/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import order.filter.cofinite

/-!
# Basic theory of bornological spaces.

We develop the basic theory of bornological spaces. Instead of axiomatizing bounded sets and
defining bornological spaces in terms of those, we recognize that the cobounded sets form a filter
and define a bornological space as a filter of cobounded sets which contains the cofinite filter.
This allows us to make use of the extensive library for filters, but we also provide the relevant
connecting results for bounded sets.
-/

open set filter

variables {α β γ : Type*}


/-!
### Bornological spaces
-/

/-- A **bornological space** is a filter of cobounded sets which is under the cofinite filter.
Such spaces are equivalently specified by their bounded sets, see `bornological_space.of_bounded`
and `bornological_space.eq_iff_is_bounded`-/
@[protect_proj]
structure bornological_space (α : Type*) :=
(cobounded : filter α)
(le_cofinite : cobounded ≤ cofinite)

attribute [class] bornological_space

/-- A constructor for bornologies by specifying the bounded sets,
and showing that they satisfy the appropriate conditions. -/
def bornological_space.of_bounded {α : Type*} (B : set (set α))
  (empty_mem : ∅ ∈ B) (subset_mem : ∀ s₁ ∈ B, ∀ s₂ : set α, s₂ ⊆ s₁ → s₂ ∈ B)
  (union_mem : ∀ s₁ s₂ ∈ B, s₁ ∪ s₂ ∈ B) (sUnion_univ : ⋃₀ B = univ) :
  bornological_space α :=
{ cobounded :=
  { sets := {s : set α | sᶜ ∈ B},
    univ_sets := by { rwa ←compl_univ at empty_mem },
    sets_of_superset := λ x y hx hy, subset_mem xᶜ hx yᶜ (compl_subset_compl.mpr hy),
    inter_sets := λ x y hx hy, by simpa [compl_inter] using union_mem xᶜ hx yᶜ hy, },
  le_cofinite :=
  begin
    refine le_def.mpr (λ s, _),
    simp only [mem_set_of_eq, mem_cofinite, filter.mem_mk],
    generalize : sᶜ = s',
    refine λ h, h.dinduction_on _ (λ x t hx ht h, _),
    { exact empty_mem, },
    { refine insert_eq x t ▸ union_mem _ _ _ h,
      obtain ⟨b, hb : b ∈ B, hxb : x ∈ b⟩ :=
        mem_sUnion.mp (by simpa [←sUnion_univ] using mem_univ x),
      exact subset_mem _ hb _ (singleton_subset_iff.mpr hxb) },
  end }

section bornological_space

@[ext]
lemma bornological_space.eq : ∀ {f g : bornological_space α}, f.cobounded = g.cobounded → f = g
| ⟨a, _⟩ ⟨b, _⟩ rfl := rfl

section
variables [t : bornological_space α] {s₁ s₂ : set α}
include t

/-- `cobounded` is the filter of complements of bounded sets in the ambient bornological
space on `α` -/
def cobounded : filter α := bornological_space.cobounded t

/-- `is_bounded` is the predicate that `s` is bounded relative to the ambient bornological
space on `α`. -/
def is_bounded (s : set α) : Prop := sᶜ ∈ (cobounded : filter α)

@[simp] lemma le_cofinite : cobounded ≤ (cofinite : filter α) :=
bornological_space.le_cofinite t

lemma is_bounded_def {s : set α} : is_bounded s ↔ sᶜ ∈ t.cobounded := iff.rfl

lemma is_bounded_compl_iff {s : set α} : is_bounded sᶜ ↔ s ∈ t.cobounded :=
by rw [is_bounded_def, compl_compl]

@[simp]
lemma is_bounded_empty : is_bounded (∅ : set α) :=
by { rw [is_bounded_def, compl_empty], exact univ_mem}

lemma is_bounded.union (h₁ : is_bounded s₁) (h₂ : is_bounded s₂) : is_bounded (s₁ ∪ s₂) :=
by { rw [is_bounded_def, compl_union], exact t.cobounded.inter_sets h₁ h₂ }

lemma is_bounded.subset (h₁ : is_bounded s₂) (h₂ : s₁ ⊆ s₂) : is_bounded s₁ :=
by { rw [is_bounded_def], exact t.cobounded.sets_of_superset h₁ (compl_subset_compl.mpr h₂) }

@[simp]
lemma sUnion_bounded_univ : (⋃₀ {s : set α | is_bounded s}) = set.univ :=
univ_subset_iff.mp $ λ x hx, mem_sUnion_of_mem (mem_singleton x)
  $ le_def.mp t.le_cofinite {x}ᶜ $ (set.finite_singleton x).compl_mem_cofinite

end

end bornological_space

namespace bornological_space

lemma eq_iff {t t' : bornological_space α} :
  t = t' ↔ ∀ s, (@cobounded α t).sets s ↔ (@cobounded α t').sets s :=
⟨λ h s, h ▸ iff.rfl, λ h, by { ext, exact h _ }⟩

lemma eq_iff_is_bounded {t t' : bornological_space α} :
  t = t' ↔ ∀ s, @is_bounded α t s ↔ @is_bounded α t' s :=
⟨λ h s, h ▸ iff.rfl, λ h, by { ext, simpa only [is_bounded_def, compl_compl] using h sᶜ, }⟩

variables [bornological_space α] [bornological_space β] [bornological_space γ]

lemma is_bounded_sUnion {s : set (set α)} (hs : finite s) :
  (∀ t ∈ s, is_bounded t) → is_bounded (⋃₀ s) :=
finite.induction_on hs (λ _, by rw sUnion_empty; exact is_bounded_empty) $
λ a s has hs ih h, by rw sUnion_insert; exact
is_bounded.union (h _ $ mem_insert _ _) (ih $ λ t, h t ∘ mem_insert_of_mem _)

lemma is_bounded_bUnion {s : set β} {f : β → set α} (hs : finite s) :
  (∀ i ∈ s, is_bounded (f i)) → is_bounded (⋃ i ∈ s, f i) :=
finite.induction_on hs
  (λ _, by rw bUnion_empty; exact is_bounded_empty)
  (λ a s has hs ih h, by rw bUnion_insert; exact
    is_bounded.union (h a (mem_insert _ _)) (ih (λ i hi, h i (mem_insert_of_mem _ hi))))

lemma is_bounded_Union [fintype β] {s : β → set α}
  (h : ∀ i, is_bounded (s i)) : is_bounded (⋃ i, s i) :=
suffices is_bounded (⋃ (i : β) (hi : i ∈ @univ β), s i), by simpa,
is_bounded_bUnion finite_univ (λ i _, h i)

/-!  ### Bornology morphisms (bounded maps)

A morphism in the category of bornologies is a map for which the image of any bounded set is
bounded. However, because of our implementation of bornologies in terms of the filter of cobounded
sets, our definition is instead `f : α → β` is a bornology morphism (i.e., a `bounded_hom`) if
`comap f cobounded ≤ cobounded`. That is, the filter generated by preimages of coboundeded sets in
`β` contains the cobounded sets in `α`.
-/

/-- A morphism of bornologies is a map for which every cobounded set in the domain contains the
preimage of a cobounded set in the codomain. Equivalently, a morphism maps bounded sets to
bounded sets, see `bounded_home_iff_is_bounded_image` and `bounded_hom.image` -/
structure bounded_hom (f : α → β) : Prop :=
(comap_le : comap f cobounded ≤ cobounded)

lemma bounded_hom_def {f : α → β} : bounded_hom f ↔ comap f cobounded ≤ cobounded :=
⟨λ h, h.comap_le, λ h, ⟨h⟩⟩

lemma bounded_hom_iff_preimage_cobounded {f : α → β} :
  bounded_hom f ↔ ∀ s ∈ (cobounded : filter α), (∃ t ∈ (cobounded : filter β), f ⁻¹' t ⊆ s) :=
by { rw [bounded_hom_def, le_def], exact iff.rfl }

lemma bounded_hom.image {f : α → β} (hf : bounded_hom f) {s : set α} (hs : is_bounded s) :
  is_bounded (f '' s) :=
begin
  rcases bounded_hom_iff_preimage_cobounded.mp hf sᶜ hs with ⟨t, t_co, ht⟩,
  rw [subset_compl_comm, ←preimage_compl] at ht,
  exact cobounded.sets_of_superset t_co (subset_compl_comm.mp
    (le_trans (monotone_image ht) (set.image_preimage.l_u_le tᶜ))),
end

lemma bounded_hom_iff_is_bounded_image {f : α → β} :
  bounded_hom f ↔ ∀ {s : set α}, is_bounded s → is_bounded (f '' s) :=
begin
  refine iff.intro (λ hf s hs, bounded_hom.image hf hs)  (λ h, _),
  rw bounded_hom_iff_preimage_cobounded,
  refine λ s hs, ⟨(f '' sᶜ)ᶜ, ⟨h (is_bounded_compl_iff.mpr hs), _⟩⟩,
  simpa only [preimage_compl, compl_subset_comm] using set.image_preimage.le_u_l sᶜ,
end

lemma bounded_hom.congr {f g : α → β} (h : bounded_hom f) (h' : ∀ x, g x = f x) :
  bounded_hom g :=
by { convert h, exact funext h' }

lemma bounded_hom_id : bounded_hom (id : α → α) :=
{ comap_le := comap_id.le }

lemma bounded_hom.comp {g : β → γ} {f : α → β} (hg : bounded_hom g) (hf : bounded_hom f) :
  bounded_hom (g ∘ f) :=
{ comap_le := by simpa [comap_comap] using le_trans (comap_mono hg.comap_le) hf.comap_le }

lemma bounded_hom.iterate {f : α → α} (h : bounded_hom f) (n : ℕ) : bounded_hom (f^[n]) :=
nat.rec_on n bounded_hom_id (λ n ihn, ihn.comp h)

end bornological_space
