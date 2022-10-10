# syMTri - A Tool for Reactive <ins>Sy</ins>nthesis with <ins>M</ins>onitor <ins>Tri</ins>ggers

*This is a prototype and has not yet been tested extensively, nor is the documentation complete.*

### Description

syMTri allows you to combine monitors as symbolic automata (inspired
by [DA](https://link.springer.com/chapter/10.1007/978-3-642-03240-0_13)T[Es](https://github.com/ccol002/larva-rv-tool))
with LTL formulas. There are two
modalities for this combination:

1. The monitor passes control to the LTL formula; or
2. The monitor passes control to a co-safety LTL formula, and at the exact moment the formula is satisfied, control
   passes back to the monitor's initial state.

The second option uses a notion of *tight satisfaction* for LTL formulas, where a finite trace tightly satisfies an LTL
formula if it satisfies the formula but no strict prefix does. For example, the LTL formula X **b** is satisfied by the
trace [a, b], but the the prefix [a] does not satisfy it. Similarly, for X **true** (*next true*), any trace of length 2
tightly satisfies it, but no other prefix of any other length does.

It also includes a separate translation from the monitor language to nuXmv, allowing simulation, model checking and
sanity checking of the monitors.

### Monitor Specification Language

Find examples for the monitor specification language in ./examples.

We are currently doing only high-level syntax checking, but not any type checking or sanity checking
(e.g. we are not checking that integer variables are not assigned real values). However, the translation to nuXmv can be
analysed for these kinds of problems.

### LTL Specification Language (TLSF)

The input expected for the LTL is a [TLSF](https://arxiv.org/pdf/1604.02284.pdf) file, **however ensure that the
GUARANTEES part of the file does not use any definition from the DEFINITION part of the file. This is not yet
supported.**

### Synthesis Requirements

1. [Strix](https://gitlab.lrz.de/i7/strix) is required since it is used for the brunt of the synthesis work (no need to
   install all the extra dependencies of Strix). There are several options to how Strix is installed.

- The default option is that Strix is installed natively and that the command `strix` is available from the `PATH`
  environment variable;
- If you are using Windows or another OS not supported by Strix, you have two options with associated arguments: Access
  it through from a user-provided docker container (e.g. https://hub.docker.com/r/pmallozzi/ltltools,
  or https://github.com/shaunazzopardi/strix-docker/) or a server interface. See the **Running** section below for more
  information about these options.

2. [SyfCo](https://github.com/meyerphi/syfco) is required to be installed by the tool to prepare the input for Strix.
   SyfCo is **required** to be available from the `PATH` environment variable.

3. [nuXmv](https://es-static.fbk.eu/tools/nuxmv/index.php?n=Main.HomePage) is not required, but can be used for analysis
   of the monitors.

### Building

The tool is developed as a Python project using >=Python 3.8, and can be built like any other Python project. Our
preference is to use a venv while developing, then building a single executable using PyInstaller, as follows:

On Windows:

`pyinstaller --onefile --paths ./venv/Lib/site-packages main.py`

On Ubuntu:

`pyinstaller --onefile --paths ./venv/lib/python3.9/site-packages main.py`

### Releases

You can find releases compiled in and for Ubuntu in the [releases page](https://github.com/dSynMa/syMTri/releases/).

### Running

Argument list:

1. `--m <file>`: link to the monitor file;

*For synthesis:*

2. `--l <file>`: link to the tlsf file (**that does not use any propositions from the definition section in the
   guarantee section**);
3. `--rep`: use this if you want the controller to pass back control to the monitor (ensure the LTL guarantees required
   are co-safety, i.e. no **G** operator);
4. `--dot`: use this if you want the output to include a DOT representation of the controller for the combination;
5. `--docker <container-name>`: use this if your Strix implementation is running on a docker container; and
6. `--server <server-location>`: use this if your Strix implementation is running on a virtual machine and exposed
   through a server that exposes an endpoint at `<server-location>/strix` that responds to `GET` requests with
   controllers in KISS format (i.e. strix is called with the `-k` parameter).

*For translation to nuXmv:*

7. `--to_nuxmv`: use this if you want a translation of the monitor into nuxmv input format, for analysis purposes.
   This assumes that each state has outgoing transitions with mutually exclusive guards.
8. `--to_nuxmv_cases`: a variant of the above command that uses case style rather than propositional form. This gives a
   different interpretation of the monitor semantics, where mutually exclusivity of guards is not required, but the
   first
   transition with a guard that matches is taken.

The default output is a monitor with outputs in a format similar to the input monitor.

An example run command is the following:

On Windows (with Strix on docker):

`./syMTri-windows.exe --m "examples/cleaning-robot/monitor.date" --l "examples/cleaning-robot/controller.tlsf" --docker "pmallozzi/ltltools" --rep`

On Ubuntu (with Strix installed natively):

`./syMTri --m "examples/cleaning-robot/monitor.date" --l "examples/cleaning-robot/controller.tlsf" --rep`

The nuXmv commands can be used in tandem, e.g.

`./syMTri-windows.exe --m "examples/cleaning-robot/monitor.date" --to_nuxmv --l "examples/cleaning-robot/controller.tlsf" --docker "pmallozzi/ltltools" --rep`

or on their own, e.g.

`./syMTri-windows.exe --m "examples/cleaning-robot/monitor.date" --to_nuxmv`
