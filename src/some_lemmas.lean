import group_theory.quotient_group

open_locale classical

variables (G : Type*) [group G] (N : subgroup G) [nN : N.normal]

@[to_additive add_mk_surjective]
lemma mk_surjective : function.surjective (@quotient_group.mk G _ N) :=
by apply quotient.surjective_quotient_mk'
