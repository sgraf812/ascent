import Ascend.Attr

/-!
# Structural rules of the registry

The lattice laws of `rwp`, in their triple form, are registered like any other spec: the
engine has no hard-coded rules. A bind decomposes into the head's `rwp` with the rebound
coupling as the precondition; the abstract bind is synthesized by the same template mechanism
that serves the leaves. `tryCatch` is decomposed identically on the exception side, its handlers
synthesized as sub-program holes exactly as bind's continuation.
-/

namespace Ascend

attribute [ascend] Ascent.RTriple.bind
attribute [ascend] Ascent.RTriple.tryCatch
attribute [ascend] Ascent.RTriple.throw

end Ascend
