# Physarum-Inspired Branch-Flow Search

Lean 4 formalization of the algebraic core of branch-flow search. It is a
game-tree search that runs on a conductivity network, the same kind of network
the slime mold *Physarum polycephalum* grows while it feeds.

The slime mold has no controller anywhere in it. Tubes carrying a lot of flow
get thicker, tubes carrying little flow thin out and disappear, and what is
left is a good network. Branch-flow search does that to a game tree. The one
change is that reinforcement is gated by how useful the search result turned
out to be, not by flow alone, because a search route can carry heavy traffic
and learn nothing.

Traffic goes to complete root-to-frontier branches. A branch that transports
something useful reinforces every edge it travelled, and unused edges decay:

```
D_e^{t+1} = rho * D_e^t + alpha * sum over branches b through e of |q_b| * U_b,   0 < rho < 1
```

The move policy only sets the starting conductivities. Nothing learned decides
where the next unit of computation goes.

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

Two of these carry most of the weight. `policyConductivity_pos` is what keeps
the policy a prior instead of a constraint, because an edge starting at exactly
zero would carry no flow, so it would get no deposit, so it would stay at zero
and the move would be gone from the search for good. `evolve_positive` says the
update never drives an edge to zero either, so decay suppresses a route rather
than deleting it, and a faded route can come back.

Four more in `BranchFlowMain.lean`. That file is a diagnostic, it runs the
dynamics on the smallest setup that can show the intended behaviour. Branch A
is two edges deep, branch B is one edge, and the policy prefers B, so B starts
with three times the traffic. Then one useful observation on A credits both of
A's edges at once. By round two A carries more flow:

```
round=0, D={ aRoot := 2/5,    aDeep := 2/5,    bRoot := 3/5   }, flow(A)=1/5,    flow(B)=3/5,   cost=1
round=1, D={ aRoot := 11/10,  aDeep := 11/10,  bRoot := 3/4   }, flow(A)=11/20,  flow(B)=3/4,   cost=37/20
round=2, D={ aRoot := 121/40, aDeep := 121/40, bRoot := 15/16 }, flow(A)=121/80, flow(B)=15/16, cost=317/80
```

Everything there is exact rationals, no floating point anywhere. It shows the
mechanism does what it is described as doing, on one configuration, with the
usefulness values picked by hand rather than measured from a game tree. It says
nothing about search quality.

These four use `native_decide`, so they trust the Lean compiler on top of the
kernel.

## What is not proved

No theorem here says the search plays well. There is nothing about playing
strength, nothing about the usefulness function `U_b` past it being
nonnegative, nothing about convergence, no flow solver, and no adversarial
backup. Section 9 of the whitepaper lists all of it.

The `|P_b|` factor in `whole_branch_credit` is worth calling out, because it is
easy to misread. A longer branch soaks up proportionally more total deposit,
and that is just what crediting every edge equally does. It is not evidence
that long branches carry more information. If the length preference is
unwanted, divide `U_b` by `|P_b|` or by measured branch cost.

On the obvious objection, that this is MCTS with different words: if the
coupled flow solve is approximated by sampling one path per round and
incrementing edge counts, the algorithm does degenerate toward existing
methods, and the theorems here hold in both cases, so they do not distinguish
them. The claimed difference is the simultaneous globally coupled flow field,
where changing one conductivity moves traffic everywhere else. That difference
is not proved here to be worth anything. The decisive test is likely the
ablation that drops branch-wide credit for endpoint-only credit. If crediting
the whole branch does not improve regret per unit of cost, the main reason for
the design is gone, and as of now the empirical result remains the best way to
know.

## Trusted computing base

The fifteen library theorems depend on Lean's three standard axioms and nothing
else:

```
propext, Classical.choice, Quot.sound
```

The four diagnostic theorems each carry one extra `native_decide` axiom.
`native_decide` evaluates the proposition with compiled code and asserts the
answer, so the compiler and runtime get trusted too. The only claims affected
are the exact rationals in the table above. Swapping it for kernel-level
`decide` or `norm_num` would remove the dependency and is worth doing.

There is no `sorry` and no `admit` in the repository. CI checks both of those
and re-runs the audit on every push, and it fails if a `native_decide` axiom
shows up outside those four theorems.

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

The whitepaper builds with XeLaTeX or `tectonic`. The mono font has to cover
`ℚ`, `∑`, `∈` and `→`, so the preamble picks DejaVu Sans Mono or Menlo.

```bash
tectonic whitepaper.tex
```

## References

1. T. Nakagaki, H. Yamada, Á. Tóth. Maze-solving by an amoeboid organism. Nature 407, 470 (2000).
2. A. Tero, R. Kobayashi, T. Nakagaki. A mathematical model for adaptive transport network in path finding by true slime mold. Journal of Theoretical Biology 244(4), 553–564 (2007).
3. A. Tero et al. Rules for biologically inspired adaptive network design. Science 327(5964), 439–442 (2010).
