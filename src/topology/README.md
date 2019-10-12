# Topology

The following "core" modules form a linear chain of imports. A theorem involving concepts defined in several of these files should be found in the last such file in this ordering.

* `basic`
  Topological spaces. Open and closed subsets, interior, closure and frontier (boundary). Neighborhood filters. Limit of a filter. Locally finite families. Continuity and continuity at a point.
* `order`
  The complete lattice structure on topologies on a fixed set. Induced and coinduced topologies.
* `maps`
  Open and closed maps. "Inducing" maps. Embeddings, open embeddings and closed embeddings. Quotient maps.
* `constructions`
  Building new topological spaces from old ones: products, sums, subspaces and quotients.
* `subset_properties`
  Compactness. Clopen subsets, irreducibility and connectedness. Totally disconnected and totally separated sets and spaces.
* `separation`
  Separation axioms T₀ through T₄, also known as Kolmogorov, Tychonoff or Fréchet, Hausdorff, regular, and normal spaces respectively.

The remaining directories and files, in no particular order:

* `algebra`
  Topological spaces with compatible algebraic or ordered structure.
* `category`
  The categories of topological spaces, uniform spaces, etc.
* `instances`
  Specific topological spaces such as the real numbers and the complex numbers.
* `metric_space`
  Metric spaces.
* `sheaves`
  Presheaves on a topological space.
* `uniform_space`
  Uniform spaces.
* `bases`
  Bases for filters and topological spaces. Separable, first countable and second countable spaces.
* `bounded_continuous_function`
  Bounded continuous functions from a topological space to a metric space.
* `compact_open`
  The compact-open topology on the space of continuous maps between two topological spaces.
* `continuous_on`
  Neighborhoods within a subset. Continuity on a subset, and continuity within a subset at a point.
* `dense_embedding`
  Embeddings and other functions with dense image.
* `homeomorph`
  Homeomorphisms between topological spaces.
* `list`
  Topologies on lists and vectors.
* `local_homeomorph`
  Homeomorphisms between open subsets of topological spaces.
* `opens`
  The complete lattice of open subsets of a topological space. The types of closed and nonempty compact subsets.
* `sequences`
  Sequential closure and sequential spaces. Sequentially continuous functions.
* `stone_cech`
  The Stone-Čech compactification of a topological space.
