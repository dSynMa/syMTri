# syMTri - A Tool for Reactive <ins>Sy</ins>nthesis with <ins>M</ins>onitor <ins>Tri</ins>ggers

*This is a prototype and has not yet been tested extensively, nor is the documentation complete.*

### Description

syMTri allows you to combine monitors as symbolic automata (inspired by [DATEs]()) with LTL formulas. There are two modalities for this combination: 
1. The monitor passes control to the LTL formula; or
2. The monitor passes control to a co-safety LTL formula, and at the exact moment the formula is satisfied, control passes back to the monitor's initial state.

The second option uses a notion of *tight satisfaction* for LTL formulas, where a finite trace tightly satisfies an LTL formula if it satisfies the formula but no strict prefix does. For example, the LTL formula X **b** is satisfied by the trace [a, b], but the the prefix [a] does not satisfy it. Similarly, for X **true** (*next true*), any trace of length 2 tightly satisfies it, but no other prefix of any other length does.


###  Monitor Specification Language

Find examples for the monitor specification language in ./examples. 

We are currently doing high-level syntax checking, but not any type checking or sanity checking (using variables that have been initialised). We are planning on adding that and a translation to nuXmv to enable simulation and model checking of the monitors.

###  LTL Specification Language (TLSF)

The input expected for the LTL is a [TLSF](https://arxiv.org/pdf/1604.02284.pdf) file, **however ensure that the GUARANTEES part of the file does not use any definition from the DEFINITION part of the file. This is not yet supported.**

### Requirements

1. [Strix](https://gitlab.lrz.de/i7/strix) is required since it is used for the brunt of the synthesis work (no need to install all the extra dependencies of Strix). The tool by default assumes that `strix` is available from the `PATH` environment variable. However, there are options to access it through from a user-provided docker container or server interface (see the **Running** section below). 
2. [SyfCo](https://github.com/meyerphi/syfco) is required to be installed by the tool to prepare the input for Strix. SyfCo is **required** to be available from the `PATH` environment variable.

###  Building

The tool is developed as a Python project using >=Python 3.8, and can be built like any other Python project.

###  Releases

You can find releases compiled in and for Ubuntu in the [releases page]().

###  Running
Argument list:

1. `--m <file>`: link to the monitor file;
2. `--l <file>`: link to the tlsf file (**that does not use any propositions from the definition section in the guarantee section**);
3. `--rep`: use this if you want the controller to pass back control to the monitor (ensure the LTL guarantees required are co-safety, i.e. no **G** operator);
4. `--dot`: use this if you want the output to include a DOT representation of the controller for the combination;
5. `--docker <container-name>`: use this if your Strix implementation is running on a docker container; and
6. `--server <server-location>`: use this if your Strix implementation is running on a virtual machine and exposed through a server that exposes an endpoint at `<server-location>/strix` that responds to `GET` requests with controllers in KISS format (i.e. strix is called with the `-k` parameter).

The default output is a monitor with outputs in a format similar to the input monitor.
