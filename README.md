# Lean mathlib

![](https://github.com/leanprover-community/mathlib/workflows/continuous%20integration/badge.svg?branch=master)

[Mathlib](https://leanprover-community.github.io) is a user maintained library for the [Lean theorem prover](https://leanprover.github.io).
It contains both programming infrastructure and mathematics, as well as tactics that use the former
and allow to develop the later.

## Installation

You can find detailed instructions to install Lean, mathlib, and supporting tools:
* On [Debian-derived Linux](docs/install/debian.md) (Debian, Ubuntu, LMDE...)
* On [other Linux](docs/install/linux.md) distributions
* On [MacOS](docs/install/macos.md)
* On [Windows](docs/install/windows.md)

## Experimenting

Got everything installed? Why not start with the [tutorial project](https://github.com/leanprover-community/mathlib/blob/master/docs/install/project.md#working-on-an-existing-package)?

For more pointers, see [Lean Links](https://leanprover-community.github.io/links/).

## Documentation

Besides the installation guides above and [Lean's general
documentation](https://leanprover.github.io/documentation/), the documentation
of mathlib consists of:

- [The mathlib docs](https://leanprover-community.github.io/mathlib_docs): [documentation generated
  automatically](https://github.com/leanprover-community/doc-gen) from the source `.lean` files.
  In addition to the pages generated for each file in the library, the docs also include pages on:
  - [tactics](https://leanprover-community.github.io/mathlib_docs/tactics.html),
  - [commands](https://leanprover-community.github.io/mathlib_docs/commands.html),
  - [hole commands](https://leanprover-community.github.io/mathlib_docs/hole_commands.html), and
  - [attributes](https://leanprover-community.github.io/mathlib_docs/attributes.html).
- A description of [currently covered theories](docs/theories.md),
  as well as an [overview](docs/mathlib-overview.md) for mathematicians.
- A couple of [tutorials](docs/tutorial/)
- Some [extra Lean documentation](docs/extras.md) not specific to mathlib
- Documentation for people who would like to [contribute to mathlib](docs/contribute/index.md)

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
* Reid Barton (@rwbarton): category theory, topology
* Mario Carneiro (@digama0): all (lead maintainer)
* Bryan Gin-ge Chen (@bryangingechen): documentation, infrastructure
* Johan Commelin (@jcommelin): algebra
* Floris van Doorn (@fpvandoorn): all
* Gabriel Ebner (@gebner): all
* Sébastien Gouëzel (@sgouezel): topology, calculus
* Simon Hudon (@cipher1024): all
* Chris Hughes (@ChrisHughes24): group theory, ring theory, field theory
* Yury G. Kudryashov (@urkud): analysis, topology
* Robert Y. Lewis (@robertylewis): all
* Patrick Massot (@patrickmassot): documentation, topology
* Scott Morrison (@semorrison): category theory
