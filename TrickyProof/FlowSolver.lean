import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace TrickyProof.FlowSolver

/-!
# The flow map `q = F(D)` on trees

`TrickyProof.BranchFlow` takes branch flow as a free function.  Nothing there
ties it to the conductivities, so the credit theorems hold for flow assignments
that no conductivity field could produce.  This file supplies the missing map.

On a tree the electrical problem is series-parallel, so `F` has a closed form
and needs no matrix inversion.  Writing `R(v)` for the resistance from `v` to
ground and `s_e` for the conductance of edge `e` in series with the subtree
under it,

    s_e = 1 / (1/D_e + R(head e)),    R(v) = 1 / Σ_{e ∈ out(v)} s_e,

with `R = 0` at a grounded sink.  Current entering a node splits between the
children in proportion to `s_e`.

Two results carry the content.  `sinkFlows_sum` says the injected current is
conserved and all of it arrives at the sinks, which is the conservation law
that `BranchFlow.branchFlow_conservation_at_split` assumes rather than derives.
`sibling_starvation` with `series_strictAnti_resistance` says that reinforcing
one branch strictly reduces a sibling's flow, including when the reinforcement
happens deep inside the subtree.  That is the global coupling which separates
this search from incrementing independent per-edge counters.

Scope: trees only.  On a transposition DAG the edge flow is still determined,
but it no longer decomposes uniquely into branch flows, so `F` would need an
extra convention.
-/

mutual

/-- A rooted tree whose edges carry conductivities.  `sink` is grounded. -/
inductive FlowTree where
  | sink : FlowTree
  | node : Children → FlowTree
  deriving Repr

/-- Outgoing edges of a node: a conductivity paired with the subtree below. -/
inductive Children where
  | nil : Children
  | cons : ℚ → FlowTree → Children → Children
  deriving Repr

end

mutual

/-- Resistance from a node to ground. -/
def resistance : FlowTree → ℚ
  | .sink => 0
  | .node cs => 1 / totalConductance cs

/-- Sum over the outgoing edges of (edge in series with its subtree). -/
def totalConductance : Children → ℚ
  | .nil => 0
  | .cons d t rest => 1 / (1 / d + resistance t) + totalConductance rest

end

/-- Conductance of one edge in series with everything below it. -/
def seriesConductance (d : ℚ) (t : FlowTree) : ℚ := 1 / (1 / d + resistance t)

@[simp] theorem resistance_sink : resistance .sink = 0 := rfl

@[simp] theorem resistance_node (cs : Children) :
    resistance (.node cs) = 1 / totalConductance cs := rfl

@[simp] theorem totalConductance_nil : totalConductance .nil = 0 := rfl

@[simp] theorem totalConductance_cons (d : ℚ) (t : FlowTree) (rest : Children) :
    totalConductance (.cons d t rest)
      = seriesConductance d t + totalConductance rest := rfl

@[simp] theorem seriesConductance_sink (d : ℚ) : seriesConductance d .sink = d := by
  simp [seriesConductance]

/-! ## Positivity -/

mutual

/-- Every conductivity in the tree is positive, and every node has a child. -/
inductive TreePos : FlowTree → Prop where
  | sink : TreePos .sink
  | node {cs : Children} (hne : cs ≠ .nil) (h : ChildrenPos cs) : TreePos (.node cs)

inductive ChildrenPos : Children → Prop where
  | nil : ChildrenPos .nil
  | cons {d : ℚ} {t : FlowTree} {rest : Children}
      (hd : 0 < d) (ht : TreePos t) (hrest : ChildrenPos rest) :
      ChildrenPos (.cons d t rest)

end

mutual

theorem resistance_nonneg : ∀ {t : FlowTree}, TreePos t → 0 ≤ resistance t
  | _, .sink => by simp
  | _, .node _ h => by
      simpa using div_nonneg (by norm_num : (0:ℚ) ≤ 1) (totalConductance_nonneg h)

theorem totalConductance_nonneg :
    ∀ {cs : Children}, ChildrenPos cs → 0 ≤ totalConductance cs
  | _, .nil => by simp
  | _, .cons hd ht hrest => by
      have hden : (0:ℚ) ≤ 1 / _ + resistance _ :=
        add_nonneg (by positivity) (resistance_nonneg ht)
      have hs : 0 ≤ seriesConductance _ _ :=
        div_nonneg (by norm_num : (0:ℚ) ≤ 1) hden
      have := totalConductance_nonneg hrest
      simpa using add_nonneg hs this

end

theorem seriesConductance_pos {d : ℚ} {t : FlowTree} (hd : 0 < d) (ht : TreePos t) :
    0 < seriesConductance d t := by
  have hden : 0 < 1 / d + resistance t := by
    have := resistance_nonneg ht
    have : 0 < 1 / d := by positivity
    linarith [resistance_nonneg ht]
  simpa [seriesConductance] using one_div_pos.mpr hden

theorem totalConductance_pos :
    ∀ {cs : Children}, cs ≠ .nil → ChildrenPos cs → 0 < totalConductance cs
  | .nil, hne, _ => absurd rfl hne
  | .cons _ _ _, _, .cons hd ht hrest => by
      have hs := seriesConductance_pos hd ht
      have := totalConductance_nonneg hrest
      simpa using add_pos_of_pos_of_nonneg hs this

theorem resistance_pos_of_node {cs : Children} (hne : cs ≠ .nil) (h : ChildrenPos cs) :
    0 < resistance (.node cs) := by
  simpa using one_div_pos.mpr (totalConductance_pos hne h)

/-! ## The flow map -/

mutual

/-- Current arriving at each sink, given `q` injected at the root.  This is the
map `F` from conductivities to branch flows: one entry per root-to-sink
branch. -/
def sinkFlows : ℚ → FlowTree → List ℚ
  | q, .sink => [q]
  | q, .node cs => sinkFlowsAux q (totalConductance cs) cs

/-- Splits `q` across `cs` in proportion to each edge's series conductance. -/
def sinkFlowsAux : ℚ → ℚ → Children → List ℚ
  | _, _, .nil => []
  | q, tot, .cons d t rest =>
      sinkFlows (q * seriesConductance d t / tot) t ++ sinkFlowsAux q tot rest

end

@[simp] theorem sinkFlows_sink (q : ℚ) : sinkFlows q .sink = [q] := rfl

@[simp] theorem sinkFlows_node (q : ℚ) (cs : Children) :
    sinkFlows q (.node cs) = sinkFlowsAux q (totalConductance cs) cs := rfl

@[simp] theorem sinkFlowsAux_nil (q tot : ℚ) : sinkFlowsAux q tot .nil = [] := rfl

@[simp] theorem sinkFlowsAux_cons (q tot d : ℚ) (t : FlowTree) (rest : Children) :
    sinkFlowsAux q tot (.cons d t rest)
      = sinkFlows (q * seriesConductance d t / tot) t ++ sinkFlowsAux q tot rest := rfl

mutual

/-- Conservation: all injected current reaches the sinks. -/
theorem sinkFlows_sum :
    ∀ {t : FlowTree}, TreePos t → ∀ q : ℚ, (sinkFlows q t).sum = q
  | _, .sink, q => by simp
  | _, .node (cs := cs) hne h, q => by
      have htot : totalConductance cs ≠ 0 := ne_of_gt (totalConductance_pos hne h)
      rw [sinkFlows_node, sinkFlowsAux_sum h]
      field_simp

/-- Splitting `q` across the children distributes exactly `q * (Σ s_e) / tot`. -/
theorem sinkFlowsAux_sum :
    ∀ {cs : Children}, ChildrenPos cs → ∀ q tot : ℚ,
      (sinkFlowsAux q tot cs).sum = q * totalConductance cs / tot
  | _, .nil, q, tot => by simp
  | _, .cons (d := d) (t := t) (rest := rest) _ ht hrest, q, tot => by
      rw [sinkFlowsAux_cons, List.sum_append, sinkFlows_sum ht,
        sinkFlowsAux_sum hrest, totalConductance_cons]
      ring

end

/-! ## Coupling

Reinforcement anywhere inside one subtree strictly reduces the flow reaching a
sibling.  This is the property that per-edge counter updates do not have.
-/

/-- Lowering the resistance below an edge strictly raises that edge's share.
The reinforced edge need not touch the node where the split happens, so the
effect is nonlocal. -/
theorem series_strictAnti_resistance {d R R' : ℚ} (hd : 0 < d)
    (hR' : 0 ≤ R') (h : R' < R) :
    1 / (1 / d + R) < 1 / (1 / d + R') := by
  have hd' : 0 < 1 / d := by positivity
  have h1 : 0 < 1 / d + R' := by linarith
  have h2 : 0 < 1 / d + R := by linarith
  exact one_div_lt_one_div_of_lt h1 (by linarith)

/-- Raising one branch's series conductance strictly starves its sibling. -/
theorem sibling_starvation {q sA sA' sB : ℚ}
    (hq : 0 < q) (hA : 0 < sA) (hB : 0 < sB) (h : sA < sA') :
    q * sB / (sA' + sB) < q * sB / (sA + sB) := by
  have h1 : 0 < sA + sB := by linarith
  have h2 : 0 < sA' + sB := by linarith
  have hnum : 0 < q * sB := mul_pos hq hB
  exact div_lt_div_of_pos_left hnum h1 (by linarith)

/-- The split at a two-child node, written out. -/
theorem sinkFlows_two_sinks (q dA dB : ℚ) :
    sinkFlows q (.node (.cons dA .sink (.cons dB .sink .nil)))
      = [q * dA / (dA + dB), q * dB / (dA + dB)] := by
  simp [sinkFlows, sinkFlowsAux]

/-- Reinforcement strictly inside a subtree, which lowers that subtree's
resistance from `R` to `R'` without touching its root edge `d`, strictly
reduces a sibling's flow. -/
theorem subtree_reinforcement_starves_sibling
    {q d R R' sB : ℚ} (hq : 0 < q) (hd : 0 < d)
    (hR' : 0 ≤ R') (hRR : R' < R) (hB : 0 < sB) :
    q * sB / (1 / (1 / d + R') + sB) < q * sB / (1 / (1 / d + R) + sB) := by
  have hd' : 0 < 1 / d := by positivity
  have hA : 0 < 1 / (1 / d + R) := one_div_pos.mpr (by linarith)
  exact sibling_starvation hq hA hB (series_strictAnti_resistance hd hR' hRR)

/-! ### A concrete coupled tree

`shared dA dB` is the smallest tree with a shared prefix:

    root --1--> v --dA--> sink        (branch A)
                v --dB--> sink        (branch B)
    root --1--> sink                  (branch C)

Branch C leaves the root by a different edge, so it shares nothing with A
beyond the root itself.  Reinforcing A still takes current away from it.
-/

def shared (dA dB : ℚ) : FlowTree :=
  .node (.cons 1 (.node (.cons dA .sink (.cons dB .sink .nil))) (.cons 1 .sink .nil))

theorem shared_balanced : sinkFlows 1 (shared 1 1) = [1/5, 1/5, 3/5] := by
  norm_num [shared, sinkFlows, sinkFlowsAux, seriesConductance, resistance,
    totalConductance]

theorem shared_reinforced : sinkFlows 1 (shared 9 1) = [3/7, 1/21, 11/21] := by
  norm_num [shared, sinkFlows, sinkFlowsAux, seriesConductance, resistance,
    totalConductance]

/-- Reinforcing branch A starves its sibling B and also branch C, which does
not share the reinforced edge at all.  A per-edge counter update cannot move
C, so this is the behaviour that the coupled flow field adds. -/
theorem reinforcing_A_starves_B_and_C :
    sinkFlows 1 (shared 1 1) = [1/5, 1/5, 3/5] ∧
    sinkFlows 1 (shared 9 1) = [3/7, 1/21, 11/21] ∧
    (1/21 : ℚ) < 1/5 ∧ (11/21 : ℚ) < 3/5 := by
  refine ⟨shared_balanced, shared_reinforced, by norm_num, by norm_num⟩

end TrickyProof.FlowSolver
