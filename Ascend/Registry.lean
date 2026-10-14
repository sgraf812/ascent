import Ascend.Attr

/-!
# Structural rules of the registry

The lattice laws of `wrp`, in their triple form, are registered like any other spec: the
engine has no hard-coded rules. A bind decomposes into the head's `wrp` with the rebound
coupling as the precondition; the abstract bind is synthesized by the same template mechanism
that serves the leaves. `tryCatch` is decomposed identically on the exception side, its handlers
synthesized as sub-program holes exactly as bind's continuation.
-/

namespace Ascend

attribute [ascend] Ascent.Refinement.bind
attribute [ascend] Ascent.Refinement.tryCatch
attribute [ascend] Ascent.Refinement.throw

end Ascend
