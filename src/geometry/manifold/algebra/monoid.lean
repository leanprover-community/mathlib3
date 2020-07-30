import geometry.manifold.times_cont_mdiff

/-- A Lie (additive) group is a group and a smooth manifold at the same time in which
the addition and negation operations are smooth. -/
class has_smooth_add {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
  (G : Type*) [has_add G] [topological_space G] [has_continuous_add G] [charted_space H G]
 [smooth_manifold_with_corners I G] : Prop :=
(smooth_add : smooth (I.prod I) I (λ p : G×G, p.1 + p.2))

/-- A Lie group is a group and a smooth manifold at the same time in which
the multiplication and inverse operations are smooth. -/
@[to_additive]
class has_smooth_mul {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
  (G : Type*) [has_mul G] [topological_space G] [has_continuous_mul G] [charted_space H G]
  [smooth_manifold_with_corners I G] : Prop :=
(smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2))

section has_smooth_mul

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{H : Type*} [topological_space H]
{E : Type*} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H}
{G : Type*} [has_mul G] [topological_space G] [has_continuous_mul G] [charted_space H G]
[smooth_manifold_with_corners I G] [has_smooth_mul I G]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H' M] [smooth_manifold_with_corners I' M]

@[to_additive]
lemma smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2) :=
has_smooth_mul.smooth_mul

@[to_additive]
lemma smooth.mul {f : M → G} {g : M → G} (hf : smooth I' I f) (hg : smooth I' I g) :
  smooth I' I (f * g) :=
smooth_mul.comp (hf.prod_mk hg)

@[to_additive]
lemma smooth_mul_left {a : G} : smooth I I (λ b : G, a * b) :=
smooth_mul.comp (smooth_const.prod_mk smooth_id)

@[to_additive]
lemma smooth_mul_right {a : G} : smooth I I (λ b : G, b * a) :=
smooth_mul.comp (smooth_id.prod_mk smooth_const)

@[to_additive]
lemma smooth_on.mul {f : M → G} {g : M → G} {s : set M}
  (hf : smooth_on I' I f s) (hg : smooth_on I' I g s) :
  smooth_on I' I (f * g) s :=
(smooth_mul.comp_smooth_on (hf.prod_mk hg) : _)

/- Instance of product -/
@[to_additive]
instance has_smooth_mul.prod {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]  {I : model_with_corners 𝕜 E H}
  {G : Type*} [topological_space G] [charted_space H G] [has_mul G] [has_continuous_mul G]
  [smooth_manifold_with_corners I G] [has_smooth_mul I G] {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {G' : Type*} [topological_space G'] [charted_space H' G']
  [has_mul G'] [has_continuous_mul G'] [smooth_manifold_with_corners I' G'] [has_smooth_mul I' G'] :
  has_smooth_mul (I.prod I') (G×G') :=
{ smooth_mul := ((smooth_fst.comp smooth_fst).smooth.mul (smooth_fst.comp smooth_snd)).prod_mk
  ((smooth_snd.comp smooth_fst).smooth.mul (smooth_snd.comp smooth_snd)), }

end has_smooth_mul

section smooth_monoid_morphism

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']

/-- Morphism of additive Lie groups. -/
structure smooth_add_monoid_morphism (I : model_with_corners 𝕜 E E) (I' : model_with_corners 𝕜 E' E')
(G : Type*) [topological_space G] [charted_space E G] [smooth_manifold_with_corners I G]
[add_monoid G] [has_continuous_add G] [has_smooth_add I G]
(G' : Type*) [topological_space G'] [charted_space E' G'] [smooth_manifold_with_corners I' G']
[add_monoid G'] [has_continuous_add G'] [has_smooth_add I' G'] extends add_monoid_hom G G' :=
  (smooth_to_fun : smooth I I' to_fun)

/-- Morphism of Lie groups. -/
@[to_additive]
structure smooth_monoid_morphism (I : model_with_corners 𝕜 E E) (I' : model_with_corners 𝕜 E' E')
(G : Type*) [topological_space G] [charted_space E G] [smooth_manifold_with_corners I G]
[monoid G] [has_continuous_mul G] [has_smooth_mul I G]
(G' : Type*) [topological_space G'] [charted_space E' G'] [smooth_manifold_with_corners I' G']
[monoid G'] [has_continuous_mul G'] [has_smooth_mul I' G'] extends monoid_hom G G' :=
  (smooth_to_fun : smooth I I' to_fun)

variables {I : model_with_corners 𝕜 E E} {I' : model_with_corners 𝕜 E' E'}
{G : Type*} [topological_space G] [charted_space E G] [smooth_manifold_with_corners I G]
[monoid G] [has_continuous_mul G] [has_smooth_mul I G]
{G' : Type*} [topological_space G'] [charted_space E' G'] [smooth_manifold_with_corners I' G']
[monoid G'] [has_continuous_mul G'] [has_smooth_mul I' G']

@[to_additive]
instance : has_one (smooth_monoid_morphism I I' G G') := ⟨⟨1, smooth_const⟩⟩

@[to_additive]
instance : inhabited (smooth_monoid_morphism I I' G G') := ⟨1⟩

@[to_additive]
instance : has_coe_to_fun (smooth_monoid_morphism I I' G G') := ⟨_, λ a, a.to_fun⟩

end smooth_monoid_morphism

section has_smooth_mul_core

/-- Sometimes one might want to define a Lie additive group `G` without having proved previously
that `G` is a topological additive group. In such case it is possible to use `lie_add_group_core`
that does not require such instance, and then get a Lie group by invoking `to_Lie_add_group`. -/
structure has_smooth_add_core {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
  (G : Type*) [has_add G] [topological_space G] [charted_space H G]
  extends smooth_manifold_with_corners I G : Prop :=
  (smooth_add : smooth (I.prod I) I (λ p : G×G, p.1 + p.2))

/-- Sometimes one might want to define a Lie group `G` without having proved previously that `G` is
a topological group. In such case it is possible to use `lie_group_core` that does not require such
instance, and then get a Lie group by invoking `to_lie_group` defined below. -/
@[to_additive]
structure has_smooth_mul_core {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
  (G : Type*) [has_mul G] [topological_space G] [charted_space H G]
  extends smooth_manifold_with_corners I G : Prop :=
  (smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2))

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E E}
{F : Type*} [normed_group F] [normed_space 𝕜 F] {J : model_with_corners 𝕜 F F}
{G : Type*} [topological_space G] [charted_space E G] [smooth_manifold_with_corners I G] [group G]

namespace has_smooth_mul_core

variables (c : has_smooth_mul_core I G)

@[to_additive]
protected lemma to_has_continuous_mul : has_continuous_mul G :=
{ continuous_mul := c.smooth_mul.continuous, }

@[to_additive]
protected lemma to_lie_group : @has_smooth_mul 𝕜 _ _ _ E _ _ I G _ _ c.to_has_continuous_mul _ _ :=
{ smooth_mul := c.smooth_mul, }

end has_smooth_mul_core

end has_smooth_mul_core
