import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace TrickyProof.BranchFlow

open Finset
open scoped BigOperators

/-!
# Branch-wide self-organizing search flow

This file formalizes the algebraic core of a search process in which traffic is
assigned to complete visited branches and useful traffic reinforces every edge
on the branch.  It deliberately does not assume that usefulness is known before
the branch is searched.
-/

variable {Edge Branch : Type*}

/-- Product of local policy probabilities along a branch. -/
def branchPrior (localProbabilities : List ℚ) : ℚ :=
  localProbabilities.prod

@[simp]
theorem branchPrior_nil : branchPrior [] = 1 := rfl

theorem branchPrior_append (initial remaining : List ℚ) :
    branchPrior (initial ++ remaining) =
      branchPrior initial * branchPrior remaining := by
  simp [branchPrior]

/-- Extending a branch by a probability in `[0,1]` cannot increase its prior. -/
theorem branchPrior_extension_le (initial : List ℚ) (probability : ℚ)
    (hinitial : 0 ≤ branchPrior initial)
    (_hprobability_nonnegative : 0 ≤ probability)
    (hprobability_at_most_one : probability ≤ 1) :
    branchPrior (initial ++ [probability]) ≤ branchPrior initial := by
  rw [branchPrior_append]
  simp only [branchPrior, List.prod_singleton]
  exact mul_le_of_le_one_right hinitial hprobability_at_most_one

/--
Initialize an edge's conductivity by the total policy mass of all represented
branches using it, plus a positive exploration floor.
-/
noncomputable def policyConductivity [Fintype Branch] [DecidableEq Edge]
    (path : Branch → Finset Edge) (branchMass : Branch → ℚ)
    (explorationFloor : ℚ) (edge : Edge) : ℚ :=
  explorationFloor +
    ∑ branch, if edge ∈ path branch then branchMass branch else 0

theorem policyConductivity_pos [Fintype Branch] [DecidableEq Edge]
    (path : Branch → Finset Edge) (branchMass : Branch → ℚ)
    (explorationFloor : ℚ)
    (hfloor : 0 < explorationFloor)
    (hmass : ∀ branch, 0 ≤ branchMass branch) (edge : Edge) :
    0 < policyConductivity path branchMass explorationFloor edge := by
  unfold policyConductivity
  have hsum : 0 ≤ ∑ branch, if edge ∈ path branch then branchMass branch else 0 := by
    exact Finset.sum_nonneg fun branch _ => by
      split <;> simp_all
  linarith

/-- Useful traffic deposited at an edge by all current branch flows. -/
noncomputable def depositedTraffic [Fintype Branch] [DecidableEq Edge]
    (path : Branch → Finset Edge) (flow usefulness : Branch → ℚ)
    (edge : Edge) : ℚ :=
  ∑ branch, if edge ∈ path branch then flow branch * usefulness branch else 0

/-- Total branch traffic entering one internal split. -/
noncomputable def incomingFlow (active : Finset Branch) (flow : Branch → ℚ) : ℚ :=
  ∑ branch ∈ active, flow branch

/-- Traffic leaving one internal split through a specified child. -/
noncomputable def childFlow {Child : Type*} [DecidableEq Child]
    (active : Finset Branch) (nextChild : Branch → Child)
    (flow : Branch → ℚ) (child : Child) : ℚ :=
  ∑ branch ∈ active, if nextChild branch = child then flow branch else 0

/--
When each active branch continues through exactly its designated child, the sum
of outgoing child flows equals the incoming branch flow.
-/
theorem branchFlow_conservation_at_split {Child : Type*}
    [Fintype Child] [DecidableEq Child]
    (active : Finset Branch) (nextChild : Branch → Child)
    (flow : Branch → ℚ) :
    (∑ child, childFlow active nextChild flow child) =
      incomingFlow active flow := by
  classical
  unfold childFlow incomingFlow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro branch _
  rw [Finset.sum_eq_single (nextChild branch)]
  · simp
  · intro child _ hne
    have hne' : nextChild branch ≠ child := Ne.symm hne
    simp [hne']
  · simp

/-- One discrete conductivity update. -/
noncomputable def evolve [Fintype Branch] [DecidableEq Edge]
    (path : Branch → Finset Edge) (flow usefulness : Branch → ℚ)
    (retention learningRate : ℚ) (conductivity : Edge → ℚ)
    (edge : Edge) : ℚ :=
  retention * conductivity edge +
    learningRate * depositedTraffic path flow usefulness edge

/-- A single branch event, useful for stating the all-depth credit property. -/
def reinforceBranch [DecidableEq Edge] (path : Finset Edge)
    (retention learningRate flow usefulness : ℚ)
    (conductivity : Edge → ℚ) (edge : Edge) : ℚ :=
  retention * conductivity edge +
    if edge ∈ path then learningRate * flow * usefulness else 0

/-- Every edge on a useful branch receives the same direct reinforcement. -/
theorem reinforceBranch_on_path [DecidableEq Edge] (path : Finset Edge)
    (retention learningRate flow usefulness : ℚ)
    (conductivity : Edge → ℚ) (edge : Edge) (hedge : edge ∈ path) :
    reinforceBranch path retention learningRate flow usefulness conductivity edge -
        retention * conductivity edge =
      learningRate * flow * usefulness := by
  simp [reinforceBranch, hedge]

/-- An edge outside the transported branch receives decay but no direct credit. -/
theorem reinforceBranch_off_path [DecidableEq Edge] (path : Finset Edge)
    (retention learningRate flow usefulness : ℚ)
    (conductivity : Edge → ℚ) (edge : Edge) (hedge : edge ∉ path) :
    reinforceBranch path retention learningRate flow usefulness conductivity edge =
      retention * conductivity edge := by
  simp [reinforceBranch, hedge]

/--
One branch observation credits all of its depths: total direct reinforcement is
branch length times the per-edge reinforcement.
-/
theorem whole_branch_credit [DecidableEq Edge] (path : Finset Edge)
    (retention learningRate flow usefulness : ℚ)
    (conductivity : Edge → ℚ) :
    (∑ edge ∈ path,
        (reinforceBranch path retention learningRate flow usefulness conductivity edge -
          retention * conductivity edge)) =
      (path.card : ℚ) * (learningRate * flow * usefulness) := by
  calc
    (∑ edge ∈ path,
        (reinforceBranch path retention learningRate flow usefulness conductivity edge -
          retention * conductivity edge)) =
        ∑ edge ∈ path, (learningRate * flow * usefulness) := by
          apply Finset.sum_congr rfl
          intro edge hedge
          simp [reinforceBranch, hedge]
    _ = (path.card : ℚ) * (learningRate * flow * usefulness) := by simp

/--
Summing edge deposits equals summing each branch's useful traffic once for every
edge it traverses. This is the finite double-counting identity behind all-depth
credit assignment.
-/
theorem total_depositedTraffic [Fintype Edge] [Fintype Branch]
    [DecidableEq Edge] (path : Branch → Finset Edge)
    (flow usefulness : Branch → ℚ) :
    (∑ edge, depositedTraffic path flow usefulness edge) =
      ∑ branch, (path branch).card * (flow branch * usefulness branch) := by
  classical
  simp only [depositedTraffic]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro branch _
  rw [← Finset.sum_filter]
  simp

/-- Nonnegative traffic and usefulness produce nonnegative deposited traffic. -/
theorem depositedTraffic_nonnegative [Fintype Branch] [DecidableEq Edge]
    (path : Branch → Finset Edge) (flow usefulness : Branch → ℚ)
    (hflow : ∀ branch, 0 ≤ flow branch)
    (husefulness : ∀ branch, 0 ≤ usefulness branch) (edge : Edge) :
    0 ≤ depositedTraffic path flow usefulness edge := by
  unfold depositedTraffic
  exact Finset.sum_nonneg fun branch _ => by
    split
    · exact mul_nonneg (hflow branch) (husefulness branch)
    · simp

/-- Positive initialized conductivities stay positive under positive retention. -/
theorem evolve_positive [Fintype Branch] [DecidableEq Edge]
    (path : Branch → Finset Edge) (flow usefulness : Branch → ℚ)
    (retention learningRate : ℚ) (conductivity : Edge → ℚ)
    (hretention : 0 < retention) (hlearning : 0 ≤ learningRate)
    (hconductivity : ∀ edge, 0 < conductivity edge)
    (hflow : ∀ branch, 0 ≤ flow branch)
    (husefulness : ∀ branch, 0 ≤ usefulness branch) (edge : Edge) :
    0 < evolve path flow usefulness retention learningRate conductivity edge := by
  unfold evolve
  have hbase : 0 < retention * conductivity edge :=
    mul_pos hretention (hconductivity edge)
  have hdeposit : 0 ≤ learningRate * depositedTraffic path flow usefulness edge :=
    mul_nonneg hlearning
      (depositedTraffic_nonnegative path flow usefulness hflow husefulness edge)
  linarith

/-- With no useful traffic, retention below one strictly decays a positive edge. -/
theorem unused_edge_decays (retention conductivity : ℚ)
    (hconductivity : 0 < conductivity)
    (hretention_below_one : retention < 1) :
    retention * conductivity < conductivity := by
  nlinarith

/-- Multiplicative local adaptation used to expose the positive-feedback law. -/
def multiplicativeStep (retention gain conductivity : ℚ) : ℚ :=
  (retention + gain) * conductivity

/--
If one positive edge has a larger useful-flow gain than another, its relative
conductivity increases after one common-retention update. Division is avoided
by expressing the ratio comparison through cross multiplication.
-/
theorem larger_gain_amplifies_relative_conductivity
    (retention gainA gainB conductivityA conductivityB : ℚ)
    (hconductivityA : 0 < conductivityA)
    (hconductivityB : 0 < conductivityB)
    (hgain : gainB < gainA) :
    multiplicativeStep retention gainB conductivityB * conductivityA <
      multiplicativeStep retention gainA conductivityA * conductivityB := by
  unfold multiplicativeStep
  calc
    (retention + gainB) * conductivityB * conductivityA =
        (retention + gainB) * (conductivityA * conductivityB) := by ring
    _ < (retention + gainA) * (conductivityA * conductivityB) :=
      mul_lt_mul_of_pos_right
        (by linarith : retention + gainB < retention + gainA)
        (mul_pos hconductivityA hconductivityB)
    _ = (retention + gainA) * conductivityA * conductivityB := by ring

/-- Cost of one round of branch traffic. -/
noncomputable def roundCost [Fintype Branch]
    (cost flow : Branch → ℚ) : ℚ :=
  ∑ branch, cost branch * flow branch

/-- Accumulated computation is the sum of the costs of all completed rounds. -/
def usedBudget (rounds : List ℚ) : ℚ := rounds.sum

@[simp]
theorem usedBudget_append_round (rounds : List ℚ) (nextRound : ℚ) :
    usedBudget (rounds ++ [nextRound]) = usedBudget rounds + nextRound := by
  simp [usedBudget]

theorem usedBudget_monotone (rounds : List ℚ) (nextRound : ℚ)
    (hnonnegative : 0 ≤ nextRound) :
    usedBudget rounds ≤ usedBudget (rounds ++ [nextRound]) := by
  rw [usedBudget_append_round]
  linarith

end TrickyProof.BranchFlow
