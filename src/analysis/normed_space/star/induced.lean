import analysis.normed_space.basic

section induced
open function

variables {𝓕 : Type*} (E F : Type*)

/-- A group homomorphism from a `group` to a `seminormed_group` induces a `seminormed_group`
structure on the domain. -/
@[reducible, -- See note [reducible non-instances]
to_additive "A group homomorphism from an `add_group` to a `seminormed_add_group` induces a
`seminormed_add_group` structure on the domain."]
def seminormed_group.induced' [group E] [seminormed_group F] [monoid_hom_class 𝓕 E F] (f : 𝓕) :
  seminormed_group E :=
{ norm := λ x, ∥f x∥,
  dist_eq := λ x y, by simpa only [map_div, ←dist_eq_norm_div],
  ..pseudo_metric_space.induced f _ }

/-- A group homomorphism from a `comm_group` to a `seminormed_group` induces a
`seminormed_comm_group` structure on the domain. -/
@[reducible, -- See note [reducible non-instances]
to_additive "A group homomorphism from an `add_comm_group` to a `seminormed_add_group` induces a
`seminormed_add_comm_group` structure on the domain."]
def seminormed_comm_group.induced' [comm_group E] [seminormed_group F] [monoid_hom_class 𝓕 E F]
  (f : 𝓕) : seminormed_comm_group E :=
{ ..seminormed_group.induced' E F f }

/-- An injective group homomorphism from a `group` to a `normed_group` induces a `normed_group`
structure on the domain. -/
@[reducible,  -- See note [reducible non-instances].
to_additive "An injective group homomorphism from an `add_group` to a `normed_add_group` induces a
`normed_add_group` structure on the domain."]
def normed_group.induced' [group E] [normed_group F] [monoid_hom_class 𝓕 E F] (f : 𝓕)
  (h : injective f) : normed_group E :=
{ ..seminormed_group.induced' E F f, ..metric_space.induced f h _ }

/-- An injective group homomorphism from an `comm_group` to a `normed_group` induces a
`normed_comm_group` structure on the domain. -/
@[reducible,  -- See note [reducible non-instances].
to_additive "An injective group homomorphism from an `comm_group` to a `normed_comm_group` induces a
`normed_comm_group` structure on the domain."]
def normed_comm_group.induced' [comm_group E] [normed_group F] [monoid_hom_class 𝓕 E F] (f : 𝓕)
  (h : injective f) : normed_comm_group E :=
{ ..seminormed_group.induced' E F f, ..metric_space.induced f h _ }

end induced

section induced

variables {F : Type*} (R S : Type*)

/-- A non-unital ring homomorphism from an `non_unital_ring` to a `non_unital_semi_normed_ring`
induces a `non_unital_semi_normed_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def non_unital_semi_normed_ring.induced [non_unital_ring R] [non_unital_semi_normed_ring S]
  [non_unital_ring_hom_class F R S] (f : F) : non_unital_semi_normed_ring R :=
{ norm_mul := λ x y, by { unfold norm, exact (map_mul f x y).symm ▸ norm_mul_le (f x) (f y) },
  .. seminormed_add_comm_group.induced' R S f }

/-- An injective non-unital ring homomorphism from an `non_unital_ring` to a
`non_unital_normed_ring` induces a `non_unital_normed_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def non_unital_normed_ring.induced [non_unital_ring R] [non_unital_normed_ring S]
  [non_unital_ring_hom_class F R S] (f : F) (hf : function.injective f) :
  non_unital_normed_ring R :=
{ .. non_unital_semi_normed_ring.induced R S f,
  .. normed_add_comm_group.induced' R S f hf }

/-- A non-unital ring homomorphism from an `ring` to a `semi_normed_ring` induces a
`semi_normed_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def semi_normed_ring.induced [ring R] [semi_normed_ring S] [non_unital_ring_hom_class F R S]
  (f : F) : semi_normed_ring R :=
{ .. non_unital_semi_normed_ring.induced R S f,
  .. seminormed_add_comm_group.induced' R S f }

/-- An injective non-unital ring homomorphism from an `ring` to a `normed_ring` induces a
`normed_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def normed_ring.induced [ring R] [normed_ring S] [non_unital_ring_hom_class F R S] (f : F)
  (hf : function.injective f) : normed_ring R :=
{ .. non_unital_semi_normed_ring.induced R S f,
  .. normed_add_comm_group.induced' R S f hf }

/-- A non-unital ring homomorphism from a `comm_ring` to a `semi_normed_ring` induces a
`semi_normed_comm_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def semi_normed_comm_ring.induced [comm_ring R] [semi_normed_ring S]
  [non_unital_ring_hom_class F R S] (f : F) : semi_normed_comm_ring R :=
{ mul_comm := mul_comm,
  .. non_unital_semi_normed_ring.induced R S f,
  .. seminormed_add_comm_group.induced' R S f }

/-- An injective non-unital ring homomorphism from an `comm_ring` to a `normed_ring` induces a
`normed_comm_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def normed_comm_ring.induced [comm_ring R] [normed_ring S] [non_unital_ring_hom_class F R S] (f : F)
  (hf : function.injective f) : normed_comm_ring R :=
{ .. semi_normed_comm_ring.induced R S f,
  .. normed_add_comm_group.induced' R S f hf }

/-- An injective non-unital ring homomorphism from an `division_ring` to a `normed_ring` induces a
`normed_division_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def normed_division_ring.induced [division_ring R] [normed_division_ring S]
  [non_unital_ring_hom_class F R S] (f : F) (hf : function.injective f) : normed_division_ring R :=
{ norm_mul' := λ x y, by { unfold norm, exact (map_mul f x y).symm ▸ norm_mul (f x) (f y) },
  .. normed_add_comm_group.induced' R S f hf }

/-- An injective non-unital ring homomorphism from an `field` to a `normed_ring` induces a
`normed_field` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def normed_field.induced [field R] [normed_field S]
  [non_unital_ring_hom_class F R S] (f : F) (hf : function.injective f) : normed_field R :=
{ .. normed_division_ring.induced R S f hf }

/-- A ring homomorphism from a `ring R` to a `semi_normed_ring S` which induces the norm structure
`semi_normed_ring.induced` makes `R` satisfy `∥(1 : R)∥ = 1` whenever `∥(1 : S)∥ = 1`.

See note [reducible non-instances] -/
lemma norm_one_class.induced {F : Type*} (R S : Type*) [ring R] [semi_normed_ring S]
  [norm_one_class S] [ring_hom_class F R S] (f : F) :
  @norm_one_class R (semi_normed_ring.induced R S f).to_has_norm _ :=
{ norm_one := (congr_arg norm (map_one f)).trans norm_one }

end induced

/-- A linear map from a `module` to a `normed_space` induces a `normed_space` structure on the
domain, using the `seminormed_add_comm_group.induced` norm.
See note [reducible non-instances] -/
@[reducible]
def normed_space.induced {F : Type*} (α β γ : Type*) [normed_field α] [add_comm_group β]
  [module α β] [seminormed_add_comm_group γ] [normed_space α γ] [linear_map_class F α β γ]
  (f : F) : @normed_space α β _ (seminormed_add_comm_group.induced' β γ f) :=
{ norm_smul_le := λ a b, by {unfold norm, exact (map_smul f a b).symm ▸ (norm_smul a (f b)).le } }

/-- A non-unital algebra homomorphism from an `algebra` to a `normed_algebra` induces a
`normed_algebra` structure on the domain, using the `semi_normed_ring.induced` norm.
See note [reducible non-instances] -/
@[reducible]
def normed_algebra.induced {F : Type*} (α β γ : Type*) [normed_field α] [ring β]
  [algebra α β] [semi_normed_ring γ] [normed_algebra α γ] [non_unital_alg_hom_class F α β γ]
  (f : F) : @normed_algebra α β _ (semi_normed_ring.induced β γ f) :=
{ norm_smul_le := λ a b, by {unfold norm, exact (map_smul f a b).symm ▸ (norm_smul a (f b)).le } }
