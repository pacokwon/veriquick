import VeriQuick.TimeM
import VeriQuick.Instrumentation

import Algorithms.MaxSubarray.Correctness
open Algorithms.MaxSubarray.Correctness

open VeriQuick.TimeM

namespace Algorithms.MaxSubarray.Impl

def scan (currentSum bestSum : Int) : List Int → Int
  | [] => bestSum
  | hd :: tl =>
    let currentSum' := max hd (currentSum + hd)
    scan currentSum' (max bestSum currentSum') tl

def maxSubarray : List Int → Option Int
  | [] => none
  | hd :: tl => some (scan hd hd tl)

#eval maxSubarray []
#eval maxSubarray [-2, 1, -3, 4, -1, 2, 1, -5, 4]
#eval maxSubarray [2, 3, -1, -20, 5, 10]
#eval maxSubarray [-1, -4]

/-- `ys` is a nonempty suffix of `xs` -/
def Suffix (xs ys : List Int) : Prop :=
  ys ≠ [] ∧ ys <:+ xs

def MaxSuffix (xs : List Int) (m : Int) : Prop :=
  (∃ ys, Suffix xs ys ∧ ys.sum = m) ∧
  (∀ ys, Suffix xs ys → ys.sum ≤ m)

/-- suffix of `lst ++ [x]` is either `[x]` OR suffix of `lst` extended by `x` -/
private theorem suffix_append_singleton {lst ys : List Int} {x : Int}
    (hsuffix : Suffix (lst ++ [x]) ys)
  : ys = [x] ∨ ∃ s, Suffix lst s ∧ ys = s ++ [x] := by
    obtain ⟨hne, ⟨t, ht⟩⟩ := hsuffix
    rcases List.eq_nil_or_concat ys with rfl | ⟨s, y, rfl⟩
    · contradiction
    · rw [List.concat_eq_append, ← List.append_assoc] at ht
      obtain ⟨hlst, hy⟩ := List.append_inj' ht rfl
      injection hy with hy
      subst hy
      by_cases hs : s = []
      · left; simp [hs]
      · right; refine ⟨s, ⟨⟨hs, ⟨t, hlst⟩⟩, by simp⟩⟩

/-- max suffix of `lst ++ [x]` is either `x` OR max suffix of `lst` extended by `x` -/
private theorem maxSuffix_append {lst : List Int} {currentSum : Int} (x : Int)
    (hcur : MaxSuffix lst currentSum) :
    MaxSuffix (lst ++ [x]) (max x (currentSum + x)) := by
  constructor
  · obtain ⟨w, ⟨hw_empty, ⟨pre, hpre⟩⟩, hw_sum⟩ := hcur.left
    by_cases hle : x ≤ (currentSum + x)
    · exact ⟨w ++ [x], ⟨by simp, ⟨pre, by simp [← hpre]⟩⟩, by simp; omega⟩
    · exact ⟨[x], ⟨by simp, ⟨lst, by rfl⟩⟩, by simp; omega⟩
  · intro ys hsuffix
    rcases suffix_append_singleton hsuffix with hsingleton | ⟨s, ⟨hs_suffix, rfl⟩⟩
    · subst hsingleton; simp; omega
    · have : s.sum ≤ currentSum := hcur.right s hs_suffix
      simp; omega

/-- subarray of `lst ++ [x]` is either a subarray of `lst` OR a suffix of `lst ++ [x]` -/
private theorem subarray_append_singleton {lst ys : List Int} {x : Int}
    (hsub : Subarray (lst ++ [x]) ys) :
    Subarray lst ys ∨ Suffix (lst ++ [x]) ys := by
      obtain ⟨hne, ⟨pre, post, hpp⟩⟩ := hsub
      rcases List.eq_nil_or_concat post with rfl | ⟨post, p, rfl⟩
      · right
        exact ⟨hne, pre, by simp [hpp]⟩
      · left
        rw [List.concat_eq_append, ← List.append_assoc] at hpp
        have hlst_pp := List.append_inj_left' hpp (by rfl)
        exact ⟨hne, ⟨pre, post, hlst_pp⟩⟩

/-- max subarray of `lst ++ [x]` is max subarray of `lst` OR max suffix of `lst ++ [x]` -/
private theorem maxSubarray_append {lst : List Int} {currentSum bestSum : Int} (x : Int)
    (hcur : MaxSuffix lst currentSum) (hbest : MaxSubarray lst bestSum) :
    MaxSubarray (lst ++ [x]) (max bestSum (max x (currentSum + x))) := by
      constructor
      · obtain ⟨ys, ⟨⟨hy_ne, pre, post, hpp⟩, rfl⟩⟩ := hbest.left
        obtain ⟨zs, ⟨hz_ne, ⟨t, ht⟩⟩, hz_sum⟩ := (maxSuffix_append x hcur).left
        by_cases hle : ys.sum ≤ max x (currentSum + x)
        · -- suffix wins. use suffix list
          exact ⟨zs, ⟨hz_ne, ⟨t, [], by simp [ht]⟩⟩, by omega⟩
        · -- subarray wins. use subarray list
          exact ⟨ys, ⟨hy_ne, ⟨pre, post ++ [x], by simp [hpp]⟩⟩, by omega⟩
      · intro ys happ_sub
        rcases subarray_append_singleton happ_sub with hsub | happ_sub
        · have : ys.sum ≤ bestSum := hbest.right ys hsub
          omega
        · have := (maxSuffix_append x hcur).right ys happ_sub
          omega

/-- if the invariant holds for processed prefix `lst`, `scan` returns max subarray of `lst ++ xs` -/
private theorem scan_correct (xs : List Int) :
    ∀ (lst : List Int) (currentSum bestSum : Int),
    MaxSuffix lst currentSum → MaxSubarray lst bestSum →
    MaxSubarray (lst ++ xs) (scan currentSum bestSum xs) := by
      induction xs with
      | nil => intro lst _ _ _ hbest; simp [scan]; exact hbest
      | cons hd tl ih =>
        intro lst currentSum bestSum hcur hbest
        have hcur' := maxSuffix_append hd hcur
        have hbest' := maxSubarray_append hd hcur hbest
        have := ih _ _ _ hcur' hbest'
        simpa [scan] using this

/-- `x` is a max suffix of `[x]` -/
private theorem maxSuffix_singleton (x : Int) : MaxSuffix [x] x := by
  constructor
  · exists [x]
    constructor <;> simp [Suffix]
  · intro ys ⟨hne, hsuf⟩
    rcases List.suffix_cons_iff.mp hsuf with rfl | hnil
    · simp
    · rw [List.suffix_nil] at hnil
      contradiction

/-- `x` is a max subarray of `[x]` -/
private theorem maxSubarray_singleton (x : Int) : MaxSubarray [x] x := by
  constructor
  · exists [x]
    constructor
    · exact ⟨by simp, ⟨[], [], by simp⟩⟩
    · simp
  · intro ys ⟨hne, pre, post, hpp⟩
    have hsub : Subarray ([] ++ [x]) ys := ⟨hne, pre, post, by simpa using hpp⟩
    rcases subarray_append_singleton hsub with ⟨_, pre', post', h⟩ | hsuf
    · simp at h
      have := h.2.1
      contradiction
    · exact (maxSuffix_singleton x).right ys (by simpa using hsuf)

theorem maxSubarray_correct : Correct maxSubarray := by
  constructor
  · simp [maxSubarray]
  · intro xs hne
    cases xs with
    | nil => contradiction
    | cons hd tl =>
      refine ⟨scan hd hd tl, rfl, ?_⟩
      have hsuf := maxSuffix_singleton hd
      have hsub := maxSubarray_singleton hd
      exact scan_correct _ _ _ _ hsuf hsub

#instrument scan as scan_timed
#instrument maxSubarray as maxSubarray_timed

#eval scan_timed 0 0 [] -- 0 => 2
#eval scan_timed 0 0 [1] -- 1 => 7 (+5)
#eval scan_timed 1 1 [1, -2] -- 2 => 12 (+5)
#eval scan_timed 1 1 [1, -2, 5] -- 3 => 17 (+5)

#eval maxSubarray_timed [] -- 0 => 3
#eval maxSubarray_timed [0] -- 1 => 5
#eval maxSubarray_timed [0, 1] -- 2 => 10
#eval maxSubarray_timed [1, 1, -2] -- 3 => 15
#eval maxSubarray_timed [1, 1, -2, 5] -- 4 => 20

theorem scan_timed_cost (currentSum bestSum : Int) (xs : List Int) :
    (scan_timed currentSum bestSum xs).cost = 5 * xs.length + 2
  := by
    induction xs generalizing currentSum bestSum with
    | nil => simp [scan_timed]
    | cons hd tl ih =>
      simp only [TimeM.cost] at ih
      simp [scan_timed, ih]
      omega

theorem maxSubarray_timed_cost (xs : List Int) :
    (maxSubarray_timed xs).cost ≤ 5 * xs.length + 3
  := by
    cases xs with
    | nil => simp [maxSubarray_timed]
    | cons hd tl =>
      have h := scan_timed_cost hd hd tl
      simp only [TimeM.cost] at h
      simp [maxSubarray_timed, h]
      omega

end Algorithms.MaxSubarray.Impl
