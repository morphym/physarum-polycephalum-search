/-
Axiom audit: prints the axiom dependencies of every theorem in this repository.
Run with `lake env lean AxiomAudit.lean`.

The thirty-eight library theorems depend only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).  The four executable-diagnostic
theorems additionally depend on a `native_decide` axiom, which trusts the Lean
compiler and evaluator in addition to the kernel.
-/
import TrickyProof.BranchFlow
import TrickyProof.FlowSolver
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

#print axioms TrickyProof.FlowSolver.resistance_sink
#print axioms TrickyProof.FlowSolver.resistance_node
#print axioms TrickyProof.FlowSolver.totalConductance_nil
#print axioms TrickyProof.FlowSolver.totalConductance_cons
#print axioms TrickyProof.FlowSolver.seriesConductance_sink
#print axioms TrickyProof.FlowSolver.resistance_nonneg
#print axioms TrickyProof.FlowSolver.totalConductance_nonneg
#print axioms TrickyProof.FlowSolver.seriesConductance_pos
#print axioms TrickyProof.FlowSolver.totalConductance_pos
#print axioms TrickyProof.FlowSolver.resistance_pos_of_node
#print axioms TrickyProof.FlowSolver.sinkFlows_sink
#print axioms TrickyProof.FlowSolver.sinkFlows_node
#print axioms TrickyProof.FlowSolver.sinkFlowsAux_nil
#print axioms TrickyProof.FlowSolver.sinkFlowsAux_cons
#print axioms TrickyProof.FlowSolver.sinkFlows_sum
#print axioms TrickyProof.FlowSolver.sinkFlowsAux_sum
#print axioms TrickyProof.FlowSolver.series_strictAnti_resistance
#print axioms TrickyProof.FlowSolver.sibling_starvation
#print axioms TrickyProof.FlowSolver.sinkFlows_two_sinks
#print axioms TrickyProof.FlowSolver.subtree_reinforcement_starves_sibling
#print axioms TrickyProof.FlowSolver.shared_balanced
#print axioms TrickyProof.FlowSolver.shared_reinforced
#print axioms TrickyProof.FlowSolver.reinforcing_A_starves_B_and_C

#print axioms BranchFlowDemo.initial_policy_prefers_b
#print axioms BranchFlowDemo.first_useful_observation_credits_both_a_edges
#print axioms BranchFlowDemo.useful_deep_branch_eventually_carries_more_flow
#print axioms BranchFlowDemo.initial_round_cost
