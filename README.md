# Lean mathlib

![](https://github.com/leanprover-community/mathlib/workflows/continuous%20integration/badge.svg?branch=master)
[![Bors enabled](https://bors.tech/images/badge_small.svg)](https://app.bors.tech/repositories/24316)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://leanprover.zulipchat.com)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/leanprover-community/mathlib)

[Mathlib](https://leanprover-community.github.io) is a user maintained library for the [Lean theorem prover](https://leanprover.github.io).
It contains both programming infrastructure and mathematics,
as well as tactics that use the former and allow to develop the latter.

## Installation

You can find detailed instructions to install Lean, mathlib, and supporting tools on [our website](https://leanprover-community.github.io/get_started.html).

## Experimenting

Got everything installed? Why not start with the [tutorial project](https://leanprover-community.github.io/install/project.html)?

For more pointers, see [Learning Lean](https://leanprover-community.github.io/learn.html).

## Documentation

Besides the installation guides above and [Lean's general
documentation](https://leanprover.github.io/documentation/), the documentation
of mathlib consists of:

- [The mathlib docs](https://leanprover-community.github.io/mathlib_docs): documentation [generated
  automatically](https://github.com/leanprover-community/doc-gen) from the source `.lean` files.
  In addition to the pages generated for each file in the library, the docs also include pages on:
  - [tactics](https://leanprover-community.github.io/mathlib_docs/tactics.html),
  - [commands](https://leanprover-community.github.io/mathlib_docs/commands.html),
  - [hole commands](https://leanprover-community.github.io/mathlib_docs/hole_commands.html), and
  - [attributes](https://leanprover-community.github.io/mathlib_docs/attributes.html).
- A description of [currently covered theories](https://leanprover-community.github.io/theories.html),
  as well as an [overview](https://leanprover-community.github.io/mathlib-overview.html) for mathematicians.
- A couple of [tutorial Lean files](docs/tutorial/)
- Some [extra Lean documentation](https://leanprover-community.github.io/learn.html) not specific to mathlib (see "Miscellaneous topics")
- Documentation for people who would like to [contribute to mathlib](https://leanprover-community.github.io/contribute/index.html)

Much of the discussion surrounding mathlib occurs in a
[Zulip chat room](https://leanprover.zulipchat.com/). Since this
chatroom is only visible to registered users, we provide an
[openly accessible archive](https://leanprover-community.github.io/archive/)
of the public discussions. This is useful for quick reference; for a
better browsing interface, and to participate in the discussions, we strongly
suggest joining the chat. Questions from users at all levels of expertise are
welcomed.

## Maintainers:

* Jeremy Avigad (@avigad): analysis
* Anne Baanen (@Vierkantor): algebra, number theory, tactics
* Reid Barton (@rwbarton): category theory, topology
* Mario Carneiro (@digama0): all
* Bryan Gin-ge Chen (@bryangingechen): documentation, infrastructure
* Johan Commelin (@jcommelin): algebra
* Rémy Degenne (@RemyDegenne): probability, measure theory, analysis
* Floris van Doorn (@fpvandoorn): all
* Gabriel Ebner (@gebner): all
* Sébastien Gouëzel (@sgouezel): topology, calculus
* Markus Himmel (@TwoFX): category theory
* Simon Hudon (@cipher1024): all
* Chris Hughes (@ChrisHughes24): group theory, ring theory, field theory
* Yury G. Kudryashov (@urkud): analysis, topology
* Robert Y. Lewis (@robertylewis): all
* Heather Macbeth (@hrmacbeth): geometry, analysis
* Patrick Massot (@patrickmassot): documentation, topology
* Bhavik Mehta (@b-mehta): category theory, combinatorics
* Scott Morrison (@semorrison): category theory
* Adam Topaz (@adamtopaz): algebra, category theory
* Eric Wieser (@eric-wieser): algebra, infrastructure
