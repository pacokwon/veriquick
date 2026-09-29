import VeriQuick.Complexity
import Algorithms.MaxSubarray.Impl

open VeriQuick.TimeM
open VeriQuick.Complexity
open Algorithms.MaxSubarray.Impl

namespace Algorithms.MaxSubarray.Complexity

def Bound (n : Nat) := n + 1

def complexity : Prop :=
  Asymptotic maxSubarray_timed (.some Bound)

theorem maxSubarray_timed_isLinear : complexity := by
  refine ⟨5, 0, by decide, ?_⟩
  intro xs n _
  have := maxSubarray_timed_cost xs
  simp only [n, Size.size, Bound]
  omega

end Algorithms.MaxSubarray.Complexity
