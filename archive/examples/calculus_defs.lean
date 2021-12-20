import analysis.asymptotics.asymptotics
import topology.instances.ereal

noncomputable theory
open_locale topological_space classical
open filter asymptotics

variables {α E X Y : Type*} [topological_space X] [topological_space Y]
  [normed_group E] [normed_space ℝ E]

def has_jump_discontinuity [linear_order X] (f : X → Y) (a : X) : Prop :=
∃ b c : Y, b ≠ c ∧ tendsto f (𝓝[<] a) (𝓝 b) ∧ tendsto f (𝓝[>] a) (𝓝 c)

def has_removable_discontinuity (f : X → Y) (a : X) : Prop :=
∃ b : Y, tendsto f (𝓝[≠] a) (𝓝 b)

def has_infinite_discontinuity [linear_order X] (f : X → ℝ) (a : X) : Prop :=
tendsto f (𝓝[<] a) at_bot ∨ tendsto f (𝓝[<] a) at_top ∨ tendsto f (𝓝[>] a) at_bot ∨ tendsto f (𝓝[>] a) at_top

/-- $\lim_{x→a}f(x)$ is the limit along the filter `𝓝[≠] a`. -/
def limit_at [nonempty Y] (f : X → Y) (a : X) : Y :=
lim (𝓝[≠] a) f

def elimit_at (f : X → ℝ) (a : X) : ereal :=
lim (𝓝[≠] a) (coe ∘ f)

/-- `f` has asymptote `mx+b` along filter `l` (either `at_bot` or `at_top` if
`f x - x • m - b = o(x)` along `l`. If `m = 0`, then this defines a horizontal asymptote, otherwise
this defines an oblique asymptote. -/
def has_asymptote (f : ℝ → E) (m b : E) (l : filter ℝ) : Prop :=
is_o (λ x, f x - x • m - b) id l
