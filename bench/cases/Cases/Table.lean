import Cases.Setup.Blocks

/-!
# `Table`: a table of cells with jumps

The concrete program runs a table of `n` cells on the toy block machine. Each cell decrements the
register, jumps on the flag that the decrement wrote, and writes the register. The rule `wrp_cells`
asks for one refinement per cell and collects the abstract cells into one abstract table. The
family stresses the table slots of the abstract program and a value that each cell carries from
its decrement to its jump. No `vcgen` case corresponds to this family.
-/

open Std.WP Lean.Order Distillery DistillBench.Blocks

namespace DistillBench.Table

attribute [distill] wrp_bind wrp_pure

noncomputable def cell : BlockM CS Unit := do decC; jnzC 1; setC 5

end DistillBench.Table
