# A cofixpoint combinator for mixed recursive-corecursive functions

This Agda library provides a cofixpoint combinator which does for productivity
what well-founded recursion does for termination: It allows you to have
arbitrary recursive calls in your corecursive functions if you can prove them
terminating. Functions of this kind are sometimes called mixed
recursive-corecursive, and their naive encoding is usually not obviously
productive, so Agda rejects them. See the examples for some functions that are
relatively easy to implement using this library.

## Tested build configurations

### Version 0.0.2

- Agda 2.5.3; agda-stdlib 0.14

### Version 0.0.1

- Agda 2.5.2; agda-stdlib 0.13
- Agda 2.5.3; agda-stdlib 0.14 (excluding examples!)

## Installation

1. Move this folder to a path of your choice, for example
   `~/.agda/lib/wellfounded-coind`.
2. Add the following entry to your `~/.agda/libraries`:

       ~/.agda/lib/wellfounded-coind/wellfounded-coind.agda-lib

   (Substitute whatever path you chose in step 1.)

It should now be possible to import modules from this library in any of your
Agda projects.

For details, read the
[packaging](http://agda.readthedocs.io/en/latest/tools/package-system.html)
section of Agda's documentation.

## Documentation

There is currently no comprehensive API documentation (sorry!). This repository
contains a copy of my BSc thesis, `paper.pdf`, which describes the library in
some detail, both from a user's and implementor's perspective. Some usage
examples may also be found in `examples/`. Start with `examples/Runs`, which is
the simplest and most complete.

## Versioning contract

The `0.*` series should be treated as unstable, meaning that anything can
change at any time. After that, we'll see; I'm not sure what would be a
sensible versioning policy for dependently typed languages.

## Namespace

This library occupies the `Coinduction.WellFounded.**` module namespace.
