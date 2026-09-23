/-
Axiom audit: prints the axiom dependencies of every theorem in this repository.
Run with `lake env lean AxiomAudit.lean`.

The fifteen library theorems depend only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).  The four executable-diagnostic
theorems additionally depend on a `native_decide` axiom, which trusts the Lean
compiler and evaluator in addition to the kernel.
-/
import TrickyProof.BranchFlow
import BranchFlowMain

#print axioms TrickyProof.BranchFlow.branchPrior_nil
#print axioms TrickyProof.BranchFlow.branchPrior_append
#print axioms TrickyProof.BranchFlow.branchPrior_extension_le
#print axioms TrickyProof.BranchFlow.policyConductivity_pos
#print axioms TrickyProof.BranchFlow.branchFlow_conservation_at_split
#print axioms TrickyProof.BranchFlow.reinforceBranch_on_path
#print axioms TrickyProof.BranchFlow.reinforceBranch_off_path
#print axioms TrickyProof.BranchFlow.whole_branch_credit
#print axioms TrickyProof.BranchFlow.total_depositedTraffic
#print axioms TrickyProof.BranchFlow.depositedTraffic_nonnegative
#print axioms TrickyProof.BranchFlow.evolve_positive
#print axioms TrickyProof.BranchFlow.unused_edge_decays
#print axioms TrickyProof.BranchFlow.larger_gain_amplifies_relative_conductivity
#print axioms TrickyProof.BranchFlow.usedBudget_append_round
#print axioms TrickyProof.BranchFlow.usedBudget_monotone

#print axioms BranchFlowDemo.initial_policy_prefers_b
#print axioms BranchFlowDemo.first_useful_observation_credits_both_a_edges
#print axioms BranchFlowDemo.useful_deep_branch_eventually_carries_more_flow
#print axioms BranchFlowDemo.initial_round_cost
