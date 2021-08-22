import algebra.algebra.operations
open_locale pointwise
open submodule

lemma submodule.mul_eq_span_mul_set {R A} [comm_semiring R] [semiring A] [algebra R A]
  (s t : submodule R A) : s * t = span R ((s : set A) * (t : set A)) :=
by rw [← span_mul_span, span_eq, span_eq]

@[to_additive]
lemma set.Union_mul {α ι : Type*} [has_mul α] (s : ι → set α) (t : set α) :
  (⋃ i, s i) * t = ⋃ i, (s i * t) := set.image2_Union_left _ _ _

@[to_additive]
lemma set.mul_Union {α ι : Type*} [has_mul α] (s : ι → set α) (t : set α) :
  t * (⋃ i, s i) = ⋃ i, (t * s i) := set.image2_Union_right _ _ _

lemma submodule.supr_mul {ι R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  (s : ι → submodule R A) (t : submodule R A) : (⨆ i, s i) * t = ⨆ i, (s i * t) :=
begin
  conv_rhs { simp only [submodule.mul_eq_span_mul_set], },
  rw [← (submodule.gi R A).gc.l_supr, set.supr_eq_Union, ← set.Union_mul, ← set.supr_eq_Union,
    ← span_eq (span R ((⨆ (i : ι), ↑(s i)) * ↑t)), ← submodule.span_mul_span, span_eq, span_eq,
    ← (submodule.gi R A).l_supr_u],
end

lemma submodule.mul_supr {ι R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  (s : ι → submodule R A) (t : submodule R A) : t * (⨆ i, s i) = ⨆ i, (t * s i) :=
begin
  conv_rhs { simp only [submodule.mul_eq_span_mul_set], },
  rw [← (submodule.gi R A).gc.l_supr, set.supr_eq_Union, ← set.mul_Union, ← set.supr_eq_Union,
    ← span_eq (span R (↑t * (⨆ (i : ι), ↑(s i)))), ← submodule.span_mul_span, span_eq, span_eq,
    ← (submodule.gi R A).l_supr_u],
end
