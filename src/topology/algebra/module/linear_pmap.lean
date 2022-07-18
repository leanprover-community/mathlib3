import linear_algebra.linear_pmap
import topology.algebra.module.basic


open_locale topological_space

variables {R E F 𝕜: Type*}

variables [comm_ring R] [add_comm_group E] [add_comm_group F]
variables [module R E] [module R F] [topological_space R]
variables [topological_space E] [topological_add_group E]
variables [topological_space F] [topological_add_group F]

namespace linear_pmap

/-- An operator is closed if its graph is closed. -/
def closed (f : linear_pmap R E F) : Prop :=
is_closed (↑f.graph : set (E × F))

variables [has_continuous_smul R E] [has_continuous_smul R F]

/-- The topological closure of a closed submodule `s` is equal to `s`. -/
lemma _root_.is_closed.topological_closure_eq {s : submodule R E} (hs : is_closed (s : set E)) :
  s.topological_closure = s :=
le_antisymm (s.topological_closure_minimal rfl.le hs) s.submodule_topological_closure

/-- An operator is closable if the closure of the graph is a graph. -/
def closable (f : linear_pmap R E F) : Prop :=
∃ (f' : linear_pmap R E F), f.graph.topological_closure = f'.graph

/-- A closed operator is trivially closable. -/
lemma closed.closable {f : linear_pmap R E F} (hf : f.closed) : f.closable :=
⟨f, hf.topological_closure_eq⟩

lemma closable_iff_tendsto {f : linear_pmap R E F} : f.closable ↔
  ∀ {a : ℕ → f.domain} (ha : filter.tendsto a filter.at_top (𝓝 0))
  (hfa : ∃ y : F, filter.tendsto (function.comp f a) filter.at_top (𝓝 y)),
  filter.tendsto (λ n, f (a n)) filter.at_top (𝓝 0) :=
begin
  split; intro h,
  { rintros a ha ⟨y, hfa⟩,
    have ha' : filter.tendsto (function.comp (continuous_linear_map.subtype_val f.domain) a) filter.at_top (𝓝 (0 : E)) :=
    begin
      refine filter.tendsto.comp _ ha,
      exact continuous_induced_dom.continuous_at,
    end,
    convert hfa,
    cases h with f' h,
    have hf := filter.tendsto.prod_mk ha' hfa,
    simp_rw [function.comp_app, ←nhds_prod_eq] at hf,
    refine (f'.graph_fst_eq_zero_snd _ rfl).symm,
    rw [←h, ←set_like.mem_coe, f.graph.topological_closure_coe],
    refine mem_closure_of_tendsto hf _,
    simp },
  let f'_graph := f.graph.topological_closure,
  -- show that f'_graph is the graph of a `linear_pmap` `f'`:
  sorry,
end

/-- The closure is unique. -/
lemma closable.exists_unique {f g g' : linear_pmap R E F} (hf : f.closable) :
  ∃! (f' : linear_pmap R E F), f.graph.topological_closure = f'.graph :=
begin
  refine exists_unique_of_exists_of_unique hf (λ _ _ hy₁ hy₂, eq_of_eq_graph _),
  rw [←hy₁, ←hy₂],
end

noncomputable
def closure {f : linear_pmap R E F} (hf : f.closable) : linear_pmap R E F :=
hf.some

lemma closable.closure_eq_closure {f : linear_pmap R E F} (hf : f.closable) :
  f.graph.topological_closure = (closure hf).graph :=
hf.some_spec

lemma closable.le_closure {f : linear_pmap R E F} (hf : f.closable) : f ≤ closure hf :=
begin
  refine le_of_le_graph _,
  rw ←hf.closure_eq_closure,
  exact (graph f).submodule_topological_closure,
end

variables (g : linear_pmap R E F) (h : f ≤ g)
#check h.1

lemma closable.mem_domain_closure {f : linear_pmap R E F} (hf : f.closable) {x : (closure hf).domain} :
  ∃ a : ℕ → f.domain, filter.tendsto a filter.at_top (𝓝 (submodule.of_le hf.le_closure.1 x)) ∧
    ∃ (y : F), filter.tendsto (function.comp f a) filter.at_top (𝓝 y) :=
begin
  sorry,
end

end linear_pmap
