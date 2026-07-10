import Ascend.Attr

/-!
# Structural rules of the registry

The lattice laws of `rwp`, in their triple form, are registered like any other spec: the
engine has no hard-coded rules. A bind decomposes into the head's `rwp` with the rebound
coupling as the precondition; the abstract bind is synthesized by the same template mechanism
that serves the leaves.
-/

namespace Ascend

attribute [ascend] Ascent.RTriple.bind

end Ascend
