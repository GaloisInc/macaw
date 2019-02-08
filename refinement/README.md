Macaw Refinement Libary
========================================

The refinement library provides supplemental functionality for
discovery of elements that macaw-symbolic is not able to discover via
pattern matching.  This library will use crucible symbolic analysis to
attempt to determine elements that could not be identified by
macaw-symbolic.  The identification provided by macaw-symbolic is
incomplete, and so is the identification by this macaw-refinement, but
macaw-refinement attempts to additionally "refine" the analysis to
achieve even more information which can then be provided back to the
macaw analysis.

  * Terminator effects for incomplete blocks.  For example, the target
    IP address by symbolic evaluation (e.g. of jump tables).  If the
    current block does not provide sufficient information to
    symbolically identify the target, previous blocks can be added to
    the analysis (back to the entry block or a loop point).

  * Argument liveness (determining which registers and memory
    locations are used/live by a block allows determination of ABI
    compliance (for transformations) and specific block
    requirements (which currently start with a full register state and
    blank memory).

  * Call graphs.  Determination of targets of call instructions that
    cannot be identified by pattern matching via symbolic evaluation,
    using techniques similar to those for identifying incomplete blocks.
