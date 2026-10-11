module
public meta import Batteries
public meta import TreeSearch.Basic
open Batteries

namespace TreeSearch

public meta section

/-- Order heap entries by priority only. -/
private instance : Ord (Float × Nat) where
  compare a b := if a.1 < b.1 then .lt else if b.1 < a.1 then .gt else .eq

variable {m : Type → Type} [Monad m] {σ ε : Type}

def BestFirst.defaultMaxNodes : Nat := 64

def bestFirstSearch (priority : σ → m Float)
    (isTerminal : σ → m Bool) (expand : σ → m (Array (ε × σ))) (start : σ)
    (maxNodes := BestFirst.defaultMaxNodes)
    : m (Option Nat × Array (Node σ (ε × Nat))) := do
  let mut nodes := #[ { data := start } ]
  let mut heap := BinaryHeap.singleton ((0.0, 0) : Float × Nat)

  while heap.size <= maxNodes do
    match heap.max with
    | none => return (none, nodes)
    | some (_, i) =>
      heap := heap.popMax
      let some node := nodes[i]? | unreachable!
      let state := node.data
      if ← isTerminal state then
        return (some i, nodes)

      -- expand successors
      let mut newChildren := #[]
      for (e, s') in ← expand state do
        let i' := nodes.size
        nodes := nodes.push { data := s' }
        newChildren := newChildren.push (e, i')
        heap := heap.insert (← priority s', i')

      nodes := nodes.set! i { node with children := node.children ++ newChildren }
  return (none, nodes)

end

end TreeSearch
