import .mathlib
import .normed_group
import .isom_action

/-!
# Marked groups
-/

set_option old_structure_cmd true

noncomputable theory
open function nat list real set

namespace geometric_group_theory
variables (G S : Type*) [group G]

/-- A marking of a group is a generating family of elements. -/
structure marking extends free_group S →* G :=
(to_fun_surjective : surjective to_fun)

namespace marking
variables {G S}

instance : monoid_hom_class (marking G S) (free_group S) G :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_mul := λ f, f.map_mul',
  map_one := λ f, f.map_one' }

lemma map_surjective (m : marking G S) : surjective m := m.to_fun_surjective

end marking

/-- The trivial marking. -/
def marking.refl : marking G G :=
{ to_fun_surjective := λ x, ⟨free_group.of x, free_group.lift.of⟩,
  ..free_group.lift id }

variables {G S} {m : marking G S}

/-- A type synonym of `G`, tagged with a marking of the group. -/
@[derive group] def marked (m : marking G S) : Type* := G

instance : add_group (marked m) := additive.add_group

/-- "Identity" isomorphism between `G` and a marking of it. -/
def to_marked : G ≃* marked m := mul_equiv.refl _

/-- "Identity" isomorphism between a marking of `G` and itself. -/
def of_marked : marked m ≃* G := mul_equiv.refl _




@[simp] lemma to_marked_symm_eq : (to_marked : G ≃* marked m).symm = of_marked := rfl
@[simp] lemma of_marked_symm_eq : (of_marked : marked m ≃* G).symm = to_marked := rfl
@[simp] lemma to_marked_of_marked (a) : to_marked (of_marked (a : marked m)) = a := rfl
@[simp] lemma of_marked_to_marked (a) : of_marked (to_marked a : marked m) = a := rfl
@[simp] lemma to_marked_inj {a b} : (to_marked a : marked m) = to_marked b ↔ a = b := iff.rfl
@[simp] lemma of_marked_inj {a b : marked m} : of_marked a = of_marked b ↔ a = b := iff.rfl

variables (α : Type*)

instance [has_smul G α] : has_smul (marked m) α :=
‹has_smul G α›

instance [inhabited G] : inhabited (marked m) :=
‹inhabited G›

@[simp] lemma to_marked_smul (g : G) (x : α) [has_smul G α] : (to_marked g : marked m) • x = g • x := rfl
@[simp] lemma of_marked_smul (g : marked m) (x : α) [has_smul G α] : of_marked g • x = g • x := rfl


variables (X : Type*) [pseudo_metric_space X]

instance [isom_action G X] : isom_action (marked m) X :=
‹isom_action G X›

lemma aux [decidable_eq S] (x : marked m) :
  ∃ n (l : free_group S), m l = x ∧ l.to_word.length ≤ n :=
by { classical, obtain ⟨l, rfl⟩ := m.map_surjective x, exact ⟨_, _, rfl, le_rfl⟩ }

instance : normed_mul_group (marked m) :=
group_norm.to_normed_mul_group _
{ to_fun := λ x, by classical; exact nat.find (aux x),
  map_one' := cast_eq_zero.2 $ (find_eq_zero $ aux _).2 ⟨1, map_one _, le_rfl⟩,
  nonneg' := λ _, cast_nonneg _,
  mul_le' := λ x y, begin
    norm_cast,
    obtain ⟨a, rfl, ha⟩ := nat.find_spec (aux x),
    obtain ⟨b, rfl, hb⟩ := nat.find_spec (aux y),
    refine find_le ⟨a * b, map_mul _ _ _, _⟩,
    refine (a.to_word_mul_sublist _).length.trans _,
    rw length_append,
    exact add_le_add ha hb,
  end,
  inv' := begin
    suffices : ∀ {x : marked m}, nat.find (aux x⁻¹) ≤ nat.find (aux x),
    { refine λ _, congr_arg coe (this.antisymm _),
      convert this,
      simp_rw inv_inv },
    refine λ x, find_mono (λ n, _),
    rintro ⟨l, hl, h⟩,
    exact ⟨l⁻¹, by simp [hl], h.trans_eq' $ by simp⟩,
  end,
  eq_one_of_to_fun := λ x hx, begin
    obtain ⟨l, rfl, hl⟩ := (find_eq_zero $ aux _).1 (cast_eq_zero.1 hx),
    rw [nat.le_zero_iff, length_eq_zero] at hl,
    have hl2 : l.to_word = (1:free_group S).to_word := by tauto,
    have hl3 := free_group.to_word.inj l 1 hl2,
    finish
  end }

-- we need a lemma which translates between the general Type setting and the subset setting.


lemma zero_norm_iff_one (g : marked m) : ∥g∥ = 0 ↔ g = 1 := sorry

lemma dist_to_norm (g : marked m) : dist 1 g = ∥g∥ := sorry

@[simp] lemma one_norm : ∥(1 : marked m)∥ = 0 := sorry

lemma gen_norm_le_one (s : S) : 1 = ∥((to_marked (m (free_group.of s))) : marked m)∥ := sorry


@[simp] lemma dist_inv (a g h : marked m) : dist (a⁻¹*g) h = dist g (a*h):=
sorry

@[simp] lemma dist_inv' (a g h : marked m) : dist g (a⁻¹*h) = dist (a*g) h:=
sorry

lemma gen_set_mul_right (x : marked m) (s : S)
: ∥ (to_marked (of_marked x * m (free_group.of s)) : marked m) ∥ ≤ ∥x∥+1 :=
sorry

lemma gen_set_mul_right' (x : marked m) {n : ℝ} (hx : ∥x∥ ≤ n) (s : S)
: ∥ (to_marked (of_marked x * m (free_group.of s)) : marked m) ∥ ≤ n+1 :=
sorry


lemma gen_set_mul_left (x : marked m) (s : S)
: ∥ (to_marked ( m (free_group.of s) * of_marked x) : marked m) ∥ ≤ ∥x∥+1 :=
sorry

lemma gen_set_mul_left' (x : marked m) {n : ℝ} (hx : ∥x∥ ≤ n) (s : S)
: ∥ (to_marked ( m (free_group.of s) * of_marked x) : marked m) ∥ ≤ n+1 :=
sorry

lemma dist_one_iff (x y : marked m) :
dist x y = 1 ↔ (∃ s : S, x * m (free_group.of s) = y) ∨ ∃ s : S, y * m (free_group.of s) = x :=
sorry

lemma gen_set_div (x : marked m) (hx : x ≠ 1) : ∃ y : marked m, dist x y = 1 ∧ ∥y∥ = ∥x∥ - 1 :=
sorry

lemma gen_div_left (x : marked m) (hx : x ≠ 1) :
  ∃ y : marked m, ((∃ s : S, (m (free_group.of s)) * y = x) ∨ (∃ s : S, m (free_group.of s)⁻¹ * y = x)) ∧ ∥y∥ = ∥x∥ - 1 :=
sorry

-- same lemmas but for subsets

lemma gen_norm_le_one_sub {H : set G}  {m' : marking G H} {s : marked m'} (sh : s ∈ H)
 : ∥s∥ ≤ 1 := sorry

lemma gen_set_mul_right_sub {H : set G} {s : G} {m' : marking G H} (sh : s ∈ H) (g : marked m')
: ∥g * s∥ ≤ ∥g∥+1 :=
  sorry

lemma gen_set_mul_right'_sub {H : set G} {s : G} {m' : marking G H} (sh : s ∈ H) (g : marked m') {n : ℝ}
  (hg : ∥g∥ ≤ n) : ∥g * s∥ ≤ n+1 :=
  sorry

lemma gen_set_mul_left_sub {H : set G} {m' : marking G H} (g s: marked m') (sh : s ∈ H)
: ∥s * g∥ ≤ ∥g∥+1 :=
  sorry

lemma gen_set_mul_left'_sub {H : set G} {m' : marking G H} (g s : marked m')  (sh : s ∈ H) {n : ℝ}
  (hg : ∥g∥ ≤ n) : ∥s * g∥ ≤ n+1 :=
  sorry

lemma dist_one_iff_sub {H : set G} {m' : marking G H} (x y : marked m') :
dist x y = 1 ↔ ((∃ s ∈ H, x * s = y) ∨ ∃ s ∈ H, y * s = x) :=
sorry

lemma gen_div_left_sub {H : set G} {m' : marking G H} (x : marked m') (hx : x ≠ 1) :
  ∃ y : marked m', ((∃ s ∈ H, s * y = x) ∨ (∃ s ∈ H, s⁻¹ * y = x)) ∧ ∥y∥ = ∥x∥ - 1 :=
sorry

/- comments by Sébastien Gouëzel:

If you want to register your group as a metric space (where the distance depends on S), you will need to embrace the type synonym trick. Instead of a class, define a structure marking S G as you did. And then given a group G and a marking m, define a new type marked_group m G := G. On this new type, you can register the same group structure as on G, but you can also register a distance as m is now available to the system when you consider x y : marked_group m G.

    First, work with normed groups, and prove whatever you like here. Possibly adding new typeclass assumptions that say that the distance is proper or hyperbolic or whatever.
    Then, to construct instances of such normed groups, do it on type synonyms. For instance, given two types S and G with [group G], define marking S G as the space of markings of G parameterized by S. Then, given a group G and a marking m, define a typemarked_group G m := G as a copy of G, then define on it the group structure coming from G (with @[derive ...]) and the norm associated to m. Then marked_group G m will be an instance of a normed group.

-/

end geometric_group_theory
