import topology.order
import topology.continuous_function.basic

noncomputable theory

variables {X:Type*} [t : topological_space X] [t0 : t0_space X]

instance : topological_space (Π(a : {u : set X | t.is_open u}), Prop) :=
  @Pi.topological_space _ (λ u, Prop) (λ a, sierpinski_space)

def i (X :Type*) [t : topological_space X] : continuous_map X
  (Π (a : {u : set X | t.is_open u}), Prop) := {
  to_fun := λ x, (λ u, x ∈ (u:set X) ),
  continuous_to_fun := continuous_pi_iff.2 (λ i, continuous_Prop.2 (by simpa using subtype.mem i))
}

include t0
lemma i_injective : function.injective
  (λ (x : X) (u : {u : set X | t.is_open u}), x ∈ (u: set X)) :=
begin
  rw function.injective,
  intros x1 x2 h,
  by_cases c : x1 = x2, -- `by_contradiction` was slow
  { exact c },
  { exfalso,
    cases (t0_space_def X).1 t0 x1 x2 (by refine c) with u hu,
    apply (xor_iff_not_iff _ _).1 hu.2,
    simpa only [eq_iff_iff, subtype.coe_mk] using congr_fun h ⟨u, hu.1⟩ },
 end
 omit t0

lemma eq_induced_by_maps_to_sierpinski : t = ⨅ (u : {u : set X | t.is_open u}),
   topological_space.induced ((λ x, x ∈ (u:set X)) : X → Prop) sierpinski_space :=
begin
  apply le_antisymm,
  { suffices h :  ∀ (u : {u : set X | t.is_open u}), t ≤ topological_space.induced
    (λ (x : X), x ∈ ↑u) sierpinski_space,
    apply le_infi_iff.2 h,
    exact λ u, continuous.le_induced (is_open_iff_continuous_mem.1 u.2) },
  { apply is_open_implies_is_open_iff.mp,
    intros u h,
    apply is_open_implies_is_open_iff.mpr _ u _,
    { exact topological_space.induced (λ (x : X), x ∈ u) sierpinski_space },
    { exact infi_le_of_le ⟨u,h⟩ (by simp) },
    { apply is_open_induced_iff'.mpr,
      exact ⟨{true}, ⟨is_open_singleton_true,by simp [set.preimage]⟩⟩ } }
end

include t
lemma i_inducing : inducing (i X).to_fun :=
begin
  simp only [i],
  let f : {u : set X | t.is_open u} → X → Prop := λ u, (λx, x∈ (u:set X)),
  refine {induced := _},
  apply (eq_induced_by_maps_to_sierpinski).trans,
  erw induced_infi, -- same steps as the proof of `inducing_infi_to_pi`
  congr' 1,
  funext,
  erw induced_compose,
end

-- would `embedding_into_prod_sierpinski_of_t0` be good name?
theorem i_embedding : embedding (i X) :=
  embedding.mk (i_inducing) (@i_injective X t t0)

/-
lemma aux1' {α : Type*} {ι : Type*} (t: ι → topological_space α) (i: ι)
   : (⨅ i , t i) ≤ t i :=
begin
  refine infi_le_of_le i _,
  exact le_of_eq (by refl),
end

lemma aux1 {α : Type*} {ι : Type*} {t: ι → topological_space α} {s : set α} {i:ι}
  (h: (t i).is_open s) : (⨅ i , t i).is_open s :=
begin
  refine is_open_implies_is_open_iff.mpr _ s _,
  exact t i,
  apply aux1',
  --refine infi_le_of_le i _,
  --exact le_of_eq (by refl),
  exact h,
end
-/
