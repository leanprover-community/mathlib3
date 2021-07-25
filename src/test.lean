import tactic
import analysis.normed_space.dual

@[derive add_comm_group] -- Q : `@[derive [add_comm_group, module 𝕜]]` fails. How to state?
def weak (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E] : Type* := E
