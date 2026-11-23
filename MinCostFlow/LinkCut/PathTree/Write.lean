module

public import MinCostFlow.LinkCut.Path.Point
public import MinCostFlow.MinRatio.PathTreeContract

/-!
# Point write against the contract's model

`pointWriteSplay` is the node state of `pathTreeWrite`: the program for a point write ends with
the records holding exactly the contract's result.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open MinCostFlow.MinRatio

theorem pathTreeWrite_splay (s : PathTreeState) (x : ℕ) (v : Option PathEdgeValue) :
    (pathTreeWrite s x v).splay = pointWriteSplay s x v := rfl

theorem pathTreeWrite_n (s : PathTreeState) (x : ℕ) (v : Option PathEdgeValue) :
    (pathTreeWrite s x v).n = (lctExpose pathPayload s x).n := rfl

theorem pathTreeWrite_freeHead (s : PathTreeState) (x : ℕ) (v : Option PathEdgeValue) :
    (pathTreeWrite s x v).freeHead = (lctExpose pathPayload s x).freeHead := rfl

end MinCostFlow.LinkCut.Path
