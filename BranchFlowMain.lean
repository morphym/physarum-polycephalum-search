import TrickyProof.BranchFlow

namespace BranchFlowDemo

/-!
An exact-rational two-branch diagnostic. Branch A is two edges deep and starts
with less policy conductivity than the one-edge branch B. Its transported
information is more useful, so branch-wide reinforcement eventually reverses
the flow ordering.
-/

structure Conductivity where
  aRoot : ℚ
  aDeep : ℚ
  bRoot : ℚ
  deriving Repr, BEq

/-- Conductance of two serial unit-length edges. -/
def flowA (conductivity : Conductivity) : ℚ :=
  1 / (1 / conductivity.aRoot + 1 / conductivity.aDeep)

/-- Conductance of one unit-length edge. -/
def flowB (conductivity : Conductivity) : ℚ :=
  conductivity.bRoot

def retention : ℚ := 3 / 4
def usefulnessA : ℚ := 4
def usefulnessB : ℚ := 1 / 2

/-- Every edge of a branch receives that branch's useful transported flow. -/
def step (conductivity : Conductivity) : Conductivity where
  aRoot := retention * conductivity.aRoot + flowA conductivity * usefulnessA
  aDeep := retention * conductivity.aDeep + flowA conductivity * usefulnessA
  bRoot := retention * conductivity.bRoot + flowB conductivity * usefulnessB

/-- Policy head initially prefers B: A has mass 2/5 and B has mass 3/5. -/
def initial : Conductivity where
  aRoot := 2 / 5
  aDeep := 2 / 5
  bRoot := 3 / 5

def afterOne : Conductivity := step initial
def afterTwo : Conductivity := step afterOne

theorem initial_policy_prefers_b :
    flowA initial = 1 / 5 ∧ flowB initial = 3 / 5 := by
  native_decide

theorem first_useful_observation_credits_both_a_edges :
    afterOne.aRoot = 11 / 10 ∧
      afterOne.aDeep = 11 / 10 ∧
      afterOne.bRoot = 3 / 4 := by
  native_decide

theorem useful_deep_branch_eventually_carries_more_flow :
    flowA afterTwo = 121 / 80 ∧
      flowB afterTwo = 15 / 16 ∧
      flowB afterTwo < flowA afterTwo := by
  native_decide

/-- Cost is integrated traffic times the number of traversed edges. -/
def roundCost (conductivity : Conductivity) : ℚ :=
  2 * flowA conductivity + flowB conductivity

theorem initial_round_cost : roundCost initial = 1 := by
  native_decide

def showRound (round : Nat) (conductivity : Conductivity) : String :=
  s!"round={round}, D={reprStr conductivity}, flow(A)={flowA conductivity}, flow(B)={flowB conductivity}, cost={roundCost conductivity}"

def main : IO Unit := do
  IO.println "Branch-flow diagnostic (exact rationals)"
  IO.println "A is a two-edge branch; B is a one-edge branch."
  IO.println (showRound 0 initial)
  IO.println (showRound 1 afterOne)
  IO.println (showRound 2 afterTwo)
  IO.println "\nThe policy initially favors B, but useful traffic on A reinforces"
  IO.println "both its root and deep edges; by round 2, A carries more flow."

end BranchFlowDemo

def main : IO Unit := BranchFlowDemo.main
