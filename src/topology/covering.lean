import topology.connected
import topology.continuous_function.basic

variables {E E' X : Type*} [topological_space E] [topological_space E'] [topological_space X]

def evenly_covered {q : E → X} (hq : continuous q) (U : set X) : Prop :=
∀ e ∈ q ⁻¹' U, let f : connected_component e → X := q ∘ coe in embedding f ∧ set.range f = U -- not sure if this is the best way to state the definition

variables (E E' X)

structure covering_map extends continuous_map E X :=
(surjective : function.surjective to_fun)
(evenly_covered : ∀ x : X, ∃ U ∈ nhds x, evenly_covered continuous_to_fun U)

infixr ` ↠ `:25 := covering_map -- shortcut: type `\rr-` or just type `\rr `

instance : has_coe_to_fun (E ↠ X) (λ _, E → X) := ⟨λ q, q.to_fun⟩

variables {E E' X}

def covering_map.comp
  (p : E ↠ E') (q : E' ↠ X) : E ↠ X :=
{ to_fun := q ∘ p,
  continuous_to_fun := continuous.comp q.continuous_to_fun p.continuous_to_fun, -- seems like there might be a fancy way to get the continuity tactic to do this automatically?
  surjective := function.surjective.comp q.surjective p.surjective,
  evenly_covered := sorry } -- prove separate lemma about composition of evenly covered
