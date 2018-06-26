Explanator: Send in the Explanator—it explains satisfaction/violation of LTL formulas on lasso words

        Bhargav Bhatt and Dmitriy Traytel
    Department of Computer Science, ETH Zurich, Switzerland


This library is distributed under the terms of the GNU Lesser General
Public License version 3. See files LICENSE and COPYING.

Explanator depends on a recent (>= 4.04.0) version of the OCaml compiler.

To install ocaml and some additional libraries use opam - ocaml's
package manager. For example:

    apt-get install opam
    opam switch 4.05.0
    eval $(opam config env)
    opam install safa menhir

then compile Explanator with

    make

to obtain a binary explanator.native file and

    ./explanator.native -fmla examples/ex1.ltl -log examples/ex1.log

to run an example.

    ./explanator.native -?

provides some additional hints about the tool's user interface.