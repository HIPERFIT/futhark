.. role:: ref(emphasis)

.. _futhark(1):

=======
futhark
=======

SYNOPSIS
========

futhark <subcommand> options...

DESCRIPTION
===========

Futhark is a data-parallel functional array language.  Through various
subcommands, the ``futhark`` tool provides facilities for compiling,
developing, or analysing Futhark programs.  Most subcommands are
documented in their own manpage.  For example, ``futhark opencl`` is
documented as :ref:`futhark-opencl(1)`.  The remaining subcommands are
documented in this page.

COMMANDS
========

futhark check [-w] PROGRAM
--------------------------

Check whether a Futhark program type checks.  With ``-w``, no warnings
are printed.

futhark datacmp FILE_A FILE_B
-----------------------------

Check whether the two files contain the same Futhark values.  The
files must be formatted using the general Futhark data format that is
used by all other executable and tools (such as
:ref:`futhark-dataset(1)`).  All discrepancies will be reported.  This
is in contrast to :ref:`futhark-test(1)`, which only reports the first
one.

futhark dataget PROGRAM DATASET
-------------------------------

Find the test dataset whose description contains ``DATASET``
(e.g. ``#1``) and print it in binary representation to standard
output.  This does not work for ``script`` datasets.

futhark dev options... PROGRAM
------------------------------

A Futhark compiler development command, intentionally undocumented and
intended for use in developing the Futhark compiler, not for
programmers writing in Futhark.

futhark hash PROGRAM
--------------------

Print a hexadecimal hash of the program AST, including all non-builtin
imports.  Supposed to be invariant to whitespace changes.

futhark imports PROGRAM
-----------------------

Print all non-builtin imported Futhark files to stdout, one per line.

futhark query PROGRAM LINE COL
------------------------------

Print information about the variable at the given position in the
program.

SEE ALSO
========

:ref:`futhark-opencl(1)`, :ref:`futhark-c(1)`, :ref:`futhark-py(1)`, :ref:`futhark-pyopencl(1)`, :ref:`futhark-wasm(1)`, :ref:`futhark-wasm-multicore(1)`, :ref:`futhark-dataset(1)`, :ref:`futhark-doc(1)`, :ref:`futhark-test(1)`, :ref:`futhark-bench(1)`, :ref:`futhark-run(1)`, :ref:`futhark-repl(1)`, :ref:`futhark-literate(1)`
