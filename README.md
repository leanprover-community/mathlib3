# Lean mathlib

[![Build Status](https://travis-ci.org/leanprover-community/mathlib.svg?branch=master)](https://travis-ci.org/leanprover-community/mathlib)
[![Mergify Status][mergify-status]][mergify]
[![Build status](https://ci.appveyor.com/api/projects/status/y0dfsknx5h4iq7pj/branch/master?svg=true)](https://ci.appveyor.com/project/cipher1024/mathlib/branch/master)

[mergify]: https://mergify.io
[mergify-status]: https://gh.mergify.io/badges/leanprover-community/mathlib.png?style=cut

Mathlib is a user maintained library for the [Lean theorem prover](https://leanprover.github.io). 
It contains both programming infrastructure and mathematics, as well as tactics that use the former and allow to develop the later.

## Installation

You can find detailed instructions to install Lean, mathlib, and supporting tools:
* On [Debian-derived Linux](docs/install/debian.md) (Debian, Ubuntu, LMDE...)
* On [other Linux](docs/install/linux.md) distributions
* On [MacOS](docs/install/macos.md)
* On [Windows](docs/install/windows.md)

## Documentation

Besides the installation guides above and [Lean's general
documentation](https://leanprover.github.io/documentation/), the documentation
of mathlib consists of:

- A description of [currently covered theories](docs/theories.md),
  as well as an [overview](docs/mathlib-overview.md) for mathematicians.
- A couple of [tutorials](docs/tutorial/)
- Some [extra Lean documentation](docs/extras.md) not specific to mathlib
- A description of [tactics](docs/tactics.md) introduced in mathlib,
  and available [hole commands](docs/holes.md).
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
* Johan Commelin (@jcommelin): algebra
* Sébastien Gouëzel (@sgouezel): topology, calculus
* Simon Hudon (@cipher1024): all
* Chris Hughes (@ChrisHughes24): group theory, ring theory, field theory
* Robert Y. Lewis (@robertylewis): all
* Patrick Massot (@patrickmassot): documentation, topology
