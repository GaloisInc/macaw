Overview
========

This repository implements some shared code that can be re-used by multiple
architecture-specific backends to bridge the semantics defined in the semmc
repository [SemMC]_ to macaw [macaw]_.  The semantics in SemMC are defined in
terms of the SimpleBuilder [SB]_ IR from Crucible.  The code in this library
translates those SimpleBuilder-based formulas into a Haskell function that
generates macaw IR expressions (see the ``genExecInstruction`` function in
``Data.Macaw.SemMC.TH``).  This repository contains code shared between all
architectures; the intent is that each architecture will also define
architecture-specific operations that are taken as an input to this library.

Architecture-Specific Backends
==============================

See macaw-ppc as an example for what is required in an architecture-specific
backend.  At a high level, the required steps are:

1. Define an architecture-specific register type
2. Define architecture-specific functions and statements
3. Define a transformation from architecture-specific locations into TH expressions
4. Define a function to translate SimpleBuilder ``NonceApp``s into TH expressions
5. Define a function translate SimpleBuilder ``App``s into TH expressions
6. Define a function to translate *instructions* into TH expressions

Architecture-Specific Register Type
-----------------------------------

Architecture-Specific Functions
-------------------------------

Translating Architecture-Specific Locations
-------------------------------------------

Translating ``NonceApp``
------------------------

This translator is for translating architecture-specific uninterpreted
functions, which are represented using ``NonceApp`` in SimpleBuilder.  These
will be most often translated into architecture-specific functions, but may also
require architecture-specific statements to represent side effects (including
exceptions).  This is also where all floating point operations are translated,
as there are no floating point operations in macaw.

Translating ``App``
-------------------

Very few ``App`` constructors in SimpleBuilder require custom translation.  This
is primarily intended to translate division-type operations into
architecture-specific functions, as there are no division operations defined in
macaw.

Translating Instructions
------------------------

The final specialized matcher is for doing direct translations of instructions
into architecture-specific statements.  This is meant for instructions for which
we cannot express semantics in the SimpleBuilder IR due to special side effects.
Often, trap and system call-type instructions fall into this category.

Note that this function is specified by TH ``Name`` instead of as a value-level
function; this is required, as its type signature refers to an
architecture-specific type, which we cannot mention in this shared library
without incurring undesired dependencies.


.. [SemMC] https://github.com/GaloisInc/semmc
.. [macaw] https://github.com/GaloisInc/macaw
.. [SB] https://github.com/GaloisInc/crucible/blob/master/crucible/src/Lang/Crucible/Solver/SimpleBuilder.hs
