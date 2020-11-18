# WhyRel

WhyRel is a tool for reasoning about relational properties of object-based
programs.  It can and has been used to verify equivalence of ADTs,
noninterference examples, and program transformations.  WhyRel relies on the
[Why3](http://why3.lri.fr) platform to generate and discharge verification
conditions (VCs).  Source files are written in a syntax similar to Java and may
contain programs and biprograms (a novel form of product programs).  WhyRel
translates these to WhyML programs that act on an explicit heap/state model.
The program logic WhyRel implements is based on relational region logic.  VCs
pertinent to this logic are encoded as lemmas and pre- and post-conditions in
specs.

This repository contains the sources for a new version of WhyRel.  The previous
version was used to evaluate a rich set of case studies.  The current version,
_under active development_, is a reimplementation intended to be used for
experimenting with encodings and adding additional features.  It does not yet
implement everything the previous tool did.  Notably, the current version does
not check compatibility (the ACompat condition described in the paper) and does
not permit the use of pure functions in specifications.

## Documentation 

The relational program logic and a high level description of WhyRel can be found
in this research paper: http://arxiv.org/abs/1910.14560
The first version of the paper describes the previous version of WhyRel.

## Installation

The dependencies for WhyRel are:

- Why3 1.3.3
- OCamlbuild 0.14.0 

Please refer to Why3's [installation instructions](http://why3.lri.fr/doc/install.html#installing-why3).
If you install Why3 from source, please make sure to install the API as well.
OCamlbuild is required to build the project.  The sources are expected to
compile using OCaml 4.09.1.

The recommended way of installing dependencies is by using an [opam](https://opam.ocaml.org) switch.

```
opam switch create whyrel 4.09.1
opam install why3.1.3.3 ocamlbuild
```

You may also consider installing the `why-ide` package.

### Compilation

To compile, `cd` to the directory where you cloned this repository (referred to
as `<WHYREL>`) and run

```
make
```

as a test, run

```
<WHYREL>/bin/whyrel -version
```

There is no `install` flag; simply add `<WHYREL>/bin` to your `PATH` if desired.
Run `whyrel -help` to learn about other supported command line flags.


### External provers

Why3 supports a wide range of automated and interactive provers.  In developing
and testing examples for WhyRel, the emphasis has been on using SMT solvers to
discharge VCs.  These include Alt-Ergo, Z3, CVC3, and CVC4.  Please refer to the
Why3 installation documentation for instructions on how to install these, and
other supported provers.


## Usage

At its present state, WhyRel can be used to translate a series of source files
to WhyML modules.  The experimental `-locEq` option can be used to derive the
local equivalence spec for a given method.

To compile a file called `foo.rl` run

```
whyrel foo.rl -o foo.mlw
```

The resulting `foo.mlw` will include WhyML modules for each interface, module,
and bimodule in `foo.rl`, along with an additional module that encodes program
states.  To compile multiple files, simply list them (the order does not matter)

```
whyrel foo1.rl foo2.rl foo3.rl -o foo.mlw
```

Note that only one mlw file will be produced. To verify, using Why3's IDE for
instance, run

```
why3 ide -L <WHYREL>/stdlib foo.mlw
```

It is important to include WhyRel's stdlib by using the `-L` option.


### Known issues

WhyRel relies on Why3's pretty printer.  As of Why3 1.3.3 there is an issue with
how lemmas and axioms are printed.  What should be `lemma bar : P` is instead
printed as `lemma bar = P`.  To fix, simply replace the `=` with `:`.  The sed
file `post-process.sed` in the `util` directory can be used to apply this change
uniformly.

```
sed -f <WHYREL>/util/post-process.sed -i .bak path/to/mlw/file
```

Another issues concerns specs we generate.  A `diverges` clause may have to be
added to the WhyML spec for procedures that contain loops.  WhyRel is concerned
with partial correctness and does not, at this point, emit the `diverges`
clause.  Without this, Why3 will require proving termination; generally done by
including a `variant` clause.

## Examples

See the `examples` directory for a few case studies.  Each example is placed in
a directory that includes source files, WhyML files, and Why3 session files.  To
replay an example, it should be sufficient to run `make && make ide` in the
example's directory.
