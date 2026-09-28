import VeriQuick.TimeM

open VeriQuick.TimeM

namespace Algorithms.MaxSubarray.Correctness

def Subarray (xs ys : List Int) : Prop :=
  ys ≠ [] ∧ ∃ pre post, xs = pre ++ ys ++ post

def MaxSubarray (xs : List Int) (m : Int) : Prop :=
  (∃ ys, Subarray xs ys ∧ ys.sum = m) ∧
  (∀ ys, Subarray xs ys → ys.sum ≤ m)

def Correct (impl : List Int →  Option Int) : Prop :=
  impl [] = none ∧
  ∀ xs, xs ≠ [] → ∃ m, impl xs = some m ∧ MaxSubarray xs m

end Algorithms.MaxSubarray.Correctness
