This is the main repository for the Macaw binary analysis framework.
This framework is implemented to offer extensible support for
architectures.

The main algorithm implemented so far is a code discovery procedure
which will discover reachable code in the binary given one or more
entry points such as _start, or the current symbols.

The core libraries are:

* macaw-base -- The core architecture-independent operations and algorithms.
* macaw-symbolic -- A work-in-progress library that provides symbolic simulation of Macaw programs.
* macaw-x86 -- Provides definitions enabling Macaw to be used on X86_64 programs.

The libraries that make up Macaw are released under the BSD license.