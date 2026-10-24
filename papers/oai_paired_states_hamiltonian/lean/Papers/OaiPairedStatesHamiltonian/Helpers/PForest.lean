module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SelectionAcyclic

/-! Acyclicity of the selected edge set. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


-- @node: lem:p-forest
/-- For [a sphere triangulation](hyp:hT) with [different face colors across every
edge](hyp:hcol) and [no separating triangle](hyp:hsep), if [the distinguished edge lies
on the designated outer face](hyp:he0), then [the selected edge set obtained from the
constructed forest pair and that distinguished edge is a spanning forest](goal). -/
lemma selectedSet_isForest (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (hsep : TreesNoSeparatingTriangle T) (t0 : T.Face)
    (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0) :
    IsSpanningForest T {e | e ∈ selectedSet T hT col hcol t0
      (forestPair T hT col hcol hsep t0).2 e0 he0} := by
  exact selectedSet_isForest_of_pair T hT col hcol t0
    (forestPair T hT col hcol hsep t0).1 (forestPair T hT col hcol hsep t0).2
    (forestPair_isPair T hT col hcol hsep t0)
    (forestPair_qsForest T hT col hcol hsep t0) hsep e0 he0


end OaiPairedStatesHamiltonian
