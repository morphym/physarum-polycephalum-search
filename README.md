# Physarum-Inspired Branch-Flow Search

Lean 4 formalization of the algebraic core of branch-flow search, a game-tree
search whose substrate is a conductivity network borrowed from the slime mold
*Physarum polycephalum*.

Traffic is assigned to complete root-to-frontier branches. Useful traffic
reinforces every edge on the branch it travelled, and unused edges decay:

```
D_e^{t+1} = rho * D_e^t + alpha * sum over branches b through e of |q_b| * U_b,   0 < rho < 1
```

A move policy supplies only the initial conductivities. No learned action
decides where the next unit of computation goes.

The paper is [`whitepaper.tex`](whitepaper.tex), built as
[`whitepaper.pdf`](whitepaper.pdf).

## What is proved

Nineteen theorems, in two groups.

Fifteen in `TrickyProof/BranchFlow.lean`, checked by the Lean kernel:

| Theorem | Statement |
| --- | --- |
| `branchPrior_nil` | the empty branch has prior 1 |
| `branchPrior_append` | branch mass factors across concatenation |
| `branchPrior_extension_le` | extending a branch by a probability in `[0,1]` cannot increase its prior |
| `policyConductivity_pos` | a positive exploration floor makes every initialized edge positive |
| `branchFlow_conservation_at_split` | outgoing child traffic sums to incoming branch traffic |
| `reinforceBranch_on_path` | every edge on a transported branch gets the same direct credit |
| `reinforceBranch_off_path` | every edge off it gets decay and nothing else |
| `whole_branch_credit` | total branch credit is branch length times per-edge credit |
| `total_depositedTraffic` | total deposited edge traffic equals the length-weighted sum over branches |
| `depositedTraffic_nonnegative` | nonnegative flow and usefulness give nonnegative deposit |
| `evolve_positive` | positive conductivity stays positive under positive retention |
| `unused_edge_decays` | an unused positive edge strictly decays when retention is below one |
| `larger_gain_amplifies_relative_conductivity` | a larger useful-flow gain strictly increases relative conductivity |
| `usedBudget_append_round` | appending a round adds its cost |
| `usedBudget_monotone` | accumulated budget is monotone under nonnegative round costs |

Four in `BranchFlowMain.lean`, an exact-rational two-branch diagnostic. Branch
A is two edges deep and starts with less policy conductivity than the one-edge
branch B. Its useful traffic reinforces both of its edges, and by round two it
carries more flow:

```
round=0, D={ aRoot := 2/5,    aDeep := 2/5,    bRoot := 3/5   }, flow(A)=1/5,    flow(B)=3/5,   cost=1
round=1, D={ aRoot := 11/10,  aDeep := 11/10,  bRoot := 3/4   }, flow(A)=11/20,  flow(B)=3/4,   cost=37/20
round=2, D={ aRoot := 121/40, aDeep := 121/40, bRoot := 15/16 }, flow(A)=121/80, flow(B)=15/16, cost=317/80
```

These four use `native_decide`, so they trust the Lean compiler in addition to
the kernel. See the trusted base section below.

## What is not proved

No theorem here says the search plays well. There is nothing about playing
strength, nothing about the usefulness function `U_b` beyond it being
nonnegative, nothing about convergence, no flow solver, and no adversarial
backup. Section 9 of the whitepaper lists this in full.

If the coupled flow solve is approximated by sampling one path per round and
incrementing edge counts, the algorithm degenerates toward existing methods.
The theorems here hold in both cases, so they do not distinguish them.

## Trusted computing base

The fifteen library theorems depend on Lean's three standard axioms and nothing
else:

```
propext, Classical.choice, Quot.sound
```

The four diagnostic theorems each carry one additional `native_decide` axiom.
There is no `sorry` and no `admit` in the repository.

Reproduce the audit:

```bash
lake build
lake env lean AxiomAudit.lean
```

## Building

```bash
lake exe cache get     # optional: prebuilt Mathlib oleans
lake build
lake exe branch_flow_demo
```

Toolchain is `leanprover/lean4:v4.33.1` with Mathlib `v4.33.1`.

The whitepaper builds with XeLaTeX or `tectonic`. The mono font needs to cover
`ℚ`, `∑`, `∈` and `→`; the preamble picks DejaVu Sans Mono or Menlo.

```bash
tectonic whitepaper.tex
```

## References

1. T. Nakagaki, H. Yamada, Á. Tóth. Maze-solving by an amoeboid organism. Nature 407, 470 (2000).
2. A. Tero, R. Kobayashi, T. Nakagaki. A mathematical model for adaptive transport network in path finding by true slime mold. Journal of Theoretical Biology 244(4), 553–564 (2007).
3. A. Tero et al. Rules for biologically inspired adaptive network design. Science 327(5964), 439–442 (2010).
