In order to typecheck the examples, make sure that the `wellfounded-coind`
library (defined in `../wellfounded-coind.agda-lib`) is known to the Agda
compiler. There are two simple ways to do so:

1. Add the path to `../wellfounded-coind.agda-lib` to your system-wide
   `libraries` file. The latter is usually located in `~/.agda`.
2. Create a `libraries` file containing the paths to
   `../wellfounded-coind.agda-lib` and the standard library's `.agda-lib` file.
   Then call `agda` with `--library-file libraries`.
