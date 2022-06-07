import topology.separation
import topology.uniform_space.compact_separated

/-noncomputable theory-/


namespace compact_metrizable

/-For all the needs of people who love compact metric spaces,
  but don't quite care about the metric. -/


class compact_metrizable_space (X : Type*) [topological_space X] : Prop :=
(compact : compact_space X)
(t2 : t2_space X)
(second_countable : topological_space.second_countable_topology X)


attribute [instance]
  compact_metrizable_space.compact
  compact_metrizable_space.t2
  compact_metrizable_space.second_countable


instance (X : Type*) [topological_space X] [compact_metrizable_space X] : 
  uniform_space X := uniform_space_of_compact_t2


instance prod.compact_metrizable_space {X : Type*} {Y : Type*} [topological_space X] [topological_space Y]
  [compact_metrizable_space X] [compact_metrizable_space Y] :
  compact_metrizable_space (X × Y) :=
{ compact := by apply_instance,
  t2 := by apply_instance,
  second_countable := by apply_instance }


instance encodable_product.compact_metrizable_space {ι : Type*} [encodable ι] {π : ι → Type*}
  [Π (a : ι), topological_space (π a)] [∀ (i : ι), compact_metrizable_space (π i)] :
  compact_metrizable_space (Π (i : ι), π i) :=
{ compact := by apply_instance,
  t2 := by apply_instance,
  second_countable := by apply_instance }


instance sum.compact_metrizable_space {X : Type*} {Y : Type*} [topological_space X] [topological_space Y]
  [compact_metrizable_space X] [compact_metrizable_space Y] :
  compact_metrizable_space (X ⊕ Y) :=
{ compact := by apply_instance,
  t2 := by apply_instance,
  second_countable := by apply_instance }


instance sigma.compact_metrizable_space {ι : Type*} [fintype ι] [encodable ι] {π : ι → Type*}
  [Π (i : ι), topological_space (π i)] [∀ (i : ι), compact_metrizable_space (π i)] :
  compact_metrizable_space (Σ (i : ι), π i) :=
{ compact := by apply_instance,
  t2 := by apply_instance,
  second_countable := by apply_instance }


/- def subsingleton.compact_metrizable_space {X : Type*} [t : topological_space X] [singleton X] :
  compact_metrizable_space X :=
{ compact := subsingleton.compact_space,
  t2 :=
  begin
    apply t2_space_iff_nhds.2,
    intros x y x_ne_y,
    exfalso,
    exact x_ne_y (subsingleton.elim x y),
  end,
  second_countable :=
  begin
    apply @topological_space.is_topological_basis.second_countable_topology X t {set.univ},
    { have lock := @is_topological_basis_singletons X t subsingleton.discrete_topology,
      have key : {s : set X | ∃ (x : X), s = {x}} = {set.univ} :=
      sorry },
    { exact set.countable_singleton set.univ },
  end }-/


instance comp_met_is_normal {X : Type*} [topological_space X] [compact_metrizable_space X] :
  normal_space X :=
normal_of_compact_t2


instance comp_met_is_regular {X : Type*} [topological_space X] [compact_metrizable_space X] :
  regular_space X :=
normal_space.regular_space


instance comp_met_is_t2_5 {X : Type*} [topological_space X] [compact_metrizable_space X] :
  t2_5_space X :=
regular_space.t2_5_space X


lemma closed_of_comp_met_is_comp_met {X : Type*} [topological_space X] [compact_metrizable_space X]
  {F : set X} (F_closed : is_closed F) :
  compact_metrizable_space F :=
{ compact := is_compact_iff_compact_space.1 F_closed.is_compact,
  t2 := by apply_instance,
  second_countable := by apply_instance }



/- Le lemme d'Urysohn serait bienvenu pour un avoir lemme du type "la topologie est engendrée par une métrique"?
    Sinon, le nom "compact métrisable" est un peu inélégant. -/

/- Ces espaces sont en particulier métrisables, donc uniformes. Peut être intéressant d'instantier une structure
uniforme dessus ? -/


end compact_metrizable
