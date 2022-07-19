import linear_algebra.linear_pmap
import topology.algebra.module.basic


open_locale topological_space

variables {R E F 𝕜: Type*}

variables [comm_ring R] [add_comm_group E] [add_comm_group F]
variables [module R E] [module R F] [topological_space R]
variables [uniform_space E] [uniform_add_group E]
variables [uniform_space F] [uniform_add_group F]

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

lemma closable_iff_tendsto [t2_space F] {f : linear_pmap R E F} : f.closable ↔
  ∀ {a : ℕ → f.domain} (ha : filter.tendsto a filter.at_top (𝓝 0))
  (hfa : ∃ y : F, filter.tendsto (function.comp f a) filter.at_top (𝓝 y)),
  filter.tendsto (function.comp f a) filter.at_top (𝓝 0)
  :=
begin
  split; intro h,
  { rintros a ha ⟨y, hfa⟩,
    have ha' : filter.tendsto (function.comp (continuous_linear_map.subtype_val f.domain) a)
      filter.at_top (𝓝 (0 : E)) :=
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
  have hf' : ∀ (x : E × F) (hx : x ∈ f'_graph) (hx' : x.fst = 0), x.snd = 0 :=
  begin
    intros x hx hx',
    rw [←set_like.mem_coe] at hx,
    rw [f.graph.topological_closure_coe] at hx,
    rw mem_closure_iff_frequently at hx,
    haveI  : (𝓝 x).is_countably_generated := sorry,
    rcases filter.exists_seq_forall_of_frequently hx with ⟨a, ha, hx⟩,
    simp at hx,
    rcases classical.skolem.mp hx with ⟨a1, ha1⟩,
    unfreezingI { cases x },
    have ha1' : filter.tendsto a1 filter.at_top (𝓝 x_fst) :=
    begin
      sorry,
    end,
    have ha1'' : filter.tendsto (f ∘ a1) filter.at_top (𝓝 x_snd) :=
    begin
      refine filter.tendsto.comp _ ha1',
      sorry,
    end,
    specialize h ha1' ⟨x_snd, ha1''⟩,
    let a2 : ℕ → F := prod.snd ∘ a, --λ n, (a n).snd,
    have ha2 : filter.tendsto a2 filter.at_top (𝓝 x_snd) :=
    begin
      refine filter.tendsto.comp _ ha,
      rw nhds_prod_eq,
      exact filter.tendsto_snd,
    end,
    have ha2' : filter.tendsto a2 filter.at_top (𝓝 0) :=
    begin
      -- slightly harder
      sorry,
    end,
    refine tendsto_nhds_unique' filter.at_top_ne_bot ha2 ha2',
  end,
  use f'_graph.to_linear_pmap hf',
  rw f'_graph.to_linear_pmap_graph_eq,
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

end linear_pmap
