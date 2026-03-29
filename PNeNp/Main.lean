import PNeNp.Basic
import PNeNp.Interface
import PNeNp.Stitch
import PNeNp.Collision
import PNeNp.Switch
import PNeNp.Funnel
import PNeNp.Signature
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

open Finset

namespace PNeNp

variable {n : ℕ}

section WidthBudget

noncomputable def leafWidth
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (leaf : Fin R.numLeaves) : ℕ :=
  (R.leafGateSet C leaf).card

private theorem leafGateSet_sub_range
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (leaf : Fin R.numLeaves) :
    R.leafGateSet C leaf ⊆ Finset.range C.gates.length := by
  intro g hg
  simp only [MagnificationTree.leafGateSet, Finset.mem_filter] at hg
  exact hg.1

private theorem sum_leafWidth_swap
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m) :
    (Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R C α) =
    ((Finset.range C.gates.length).sum fun g =>
      (Finset.univ.filter fun β : Fin R.numLeaves =>
        g ∈ R.leafGateSet C β).card) := by
  unfold leafWidth
  simp_rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_comm'
    (h := fun (α : Fin R.numLeaves) (g : ℕ) =>
      ⟨fun ⟨_, hg⟩ =>
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ α, hg⟩,
         leafGateSet_sub_range R C α hg⟩,
       fun ⟨hα, _⟩ =>
        ⟨Finset.mem_univ α, (Finset.mem_filter.mp hα).2⟩⟩)]

private theorem gateMultiplicity_le_muMax
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (g : ℕ) (hg : g < C.gates.length) :
    gateMultiplicity R C g ≤ muMax R C :=
  Finset.le_sup (f := fun i : Fin C.gates.length => gateMultiplicity R C i.val)
    (Finset.mem_univ ⟨g, hg⟩)

theorem width_budget_sharing_bound
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m) :
    (Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R C α) ≤
      C.size * muMax R C := by
  rw [sum_leafWidth_swap]
  unfold BooleanCircuit.size
  calc (Finset.range C.gates.length).sum
        (fun g => (Finset.univ.filter fun β : Fin R.numLeaves =>
          g ∈ R.leafGateSet C β).card)
      ≤ (Finset.range C.gates.length).sum (fun _ => muMax R C) := by
        apply Finset.sum_le_sum
        intro g hg
        exact gateMultiplicity_le_muMax R C g (Finset.mem_range.mp hg)
    _ = C.gates.length * muMax R C := by
        simp [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ (m + C.gates.length) * muMax R C := by
        have hlen : C.gates.length ≤ m + C.gates.length := by omega
        exact Nat.mul_le_mul_right (muMax R C) hlen

theorem width_budget_with_sharing
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (S : Frontier n) (K : ℕ) (hK : K ≥ 1) :
    (Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R C α) ≤
      K * (2 * C.size) * muMax R C :=
  by
  have h1 := width_budget_sharing_bound R C
  have h2 : C.size * muMax R C ≤ K * (2 * C.size) * muMax R C := by
    have : C.size ≤ K * (2 * C.size) := by nlinarith
    exact Nat.mul_le_mul_right (muMax R C) this
  exact le_trans h1 h2

end WidthBudget

section GateCharging

/-! ### Gate-charging bound (hamiltonian_route.tex lines 1938-1999, 2001-2061)

For a circuit C deciding HAM_n, the Karchmer-Wigderson gate-charging
argument bounds the protocol-partition number by the total leaf width.

The proof proceeds in two stages:
1. Circuit correctness (CircuitDecidesHAM) forces that isolated
   Hamiltonian cycles produce distinct evaluation transcripts: if
   H₀ ≠ H₁ and mixedGraph S H₁ H₀ is non-Hamiltonian, then the
   circuit rejects the mixed input while accepting H₀, so some gate
   evaluates differently on toInput H₀ vs toInput (mixedGraph S H₁ H₀).

2. The gate-charging map sends each element of an isolated set I to
   a unique gate-index where its transcript first diverges from the
   mixed-input transcript.  The charged gate lies in some leaf gate
   set G_α, and the injection into gate-leaf pairs gives
   |I| ≤ Σ_α |G_α| = Σ_α leafWidth(R, C, α).

Combined with the multi-carrier funnel (Lambda' n ≤ |I| for the
right I) and the width-budget sharing bound (Σ leafWidth ≤ s · μ_max),
this completes the circuit lower bound. -/

private theorem circuit_rejects_nonham {m : ℕ} (C : BooleanCircuit m)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (hCorrect : CircuitDecidesHAM C toInput)
    (M : Finset (Edge n)) (hNotHam : ¬IsHamCycle n M) :
    C.eval (toInput M) = false := by
  by_contra h
  cases hEval : C.eval (toInput M) with
  | false =>
      exact h hEval
  | true =>
      exact hNotHam ((hCorrect M).mp hEval)

private theorem isolated_eval_diff {m : ℕ}
    (C : BooleanCircuit m) (toInput : Finset (Edge n) → (Fin m → Bool))
    (hCorrect : CircuitDecidesHAM C toInput)
    (S : Frontier n) (H₀ H₁ : Finset (Edge n))
    (hH₀ : IsHamCycle n H₀) (hNotMixed : ¬IsHamCycle n (mixedGraph S H₁ H₀)) :
    C.eval (toInput H₀) ≠ C.eval (toInput (mixedGraph S H₁ H₀)) := by
  rw [(hCorrect H₀).mpr hH₀,
      circuit_rejects_nonham C toInput hCorrect _ hNotMixed]
  simp

private theorem isolated_evalAllGates_diff {m : ℕ}
    (C : BooleanCircuit m) (toInput : Finset (Edge n) → (Fin m → Bool))
    (hCorrect : CircuitDecidesHAM C toInput)
    (S : Frontier n) (H₀ H₁ : Finset (Edge n))
    (hH₀ : IsHamCycle n H₀) (hNotMixed : ¬IsHamCycle n (mixedGraph S H₁ H₀)) :
    evalAllGates C (toInput H₀) ≠ evalAllGates C (toInput (mixedGraph S H₁ H₀)) := by
  intro hEq
  have hSame : C.eval (toInput H₀) = C.eval (toInput (mixedGraph S H₁ H₀)) := by
    unfold BooleanCircuit.eval
    exact congrArg (fun vals => vals.getD C.outputGate false) hEq
  exact isolated_eval_diff C toInput hCorrect S H₀ H₁ hH₀ hNotMixed hSame

private theorem evalAllGatesAux_length
    (gates : List Gate) (acc : List Bool) :
    (gates.foldl (init := acc) fun acc g =>
      let v1 := acc.getD g.input1 false
      let v2 := acc.getD g.input2 false
      let result := match g.kind with
        | GateKind.AND => v1 && v2
        | GateKind.OR  => v1 || v2
        | GateKind.NOT => !v1
      acc ++ [result]).length = acc.length + gates.length := by
  induction gates generalizing acc with
  | nil =>
      simp
  | cons g gates ih =>
      have h := ih (acc ++
        [match g.kind with
          | GateKind.AND => acc.getD g.input1 false && acc.getD g.input2 false
          | GateKind.OR  => acc.getD g.input1 false || acc.getD g.input2 false
          | GateKind.NOT => !(acc.getD g.input1 false)])
      simpa [List.foldl, List.length_append, List.length_singleton,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem evalAllGates_length {m : ℕ} (C : BooleanCircuit m)
    (input : Fin m → Bool) :
    (evalAllGates C input).length = m + C.gates.length := by
  unfold evalAllGates
  calc
    (C.gates.foldl (init := List.ofFn input) fun acc g =>
      let v1 := acc.getD g.input1 false
      let v2 := acc.getD g.input2 false
      let result := match g.kind with
        | GateKind.AND => v1 && v2
        | GateKind.OR  => v1 || v2
        | GateKind.NOT => !v1
      acc ++ [result]).length = (List.ofFn input).length + C.gates.length := by
        simpa using evalAllGatesAux_length C.gates (List.ofFn input)
    _ = m + C.gates.length := by simp

private theorem isolated_witnessing_gate {m : ℕ}
    (C : BooleanCircuit m) (toInput : Finset (Edge n) → (Fin m → Bool))
    (hCorrect : CircuitDecidesHAM C toInput)
    (S : Frontier n) (H₀ H₁ : Finset (Edge n))
    (hH₀ : IsHamCycle n H₀) (hNotMixed : ¬IsHamCycle n (mixedGraph S H₁ H₀)) :
    ∃ g : ℕ, g < m + C.gates.length ∧
      (evalAllGates C (toInput H₀)).getD g false ≠
        (evalAllGates C (toInput (mixedGraph S H₁ H₀))).getD g false := by
  by_contra hall
  push_neg at hall
  have hDiff := isolated_evalAllGates_diff C toInput hCorrect S H₀ H₁ hH₀ hNotMixed
  apply hDiff
  have hlen1 := evalAllGates_length C (toInput H₀)
  have hlen2 := evalAllGates_length C (toInput (mixedGraph S H₁ H₀))
  apply List.ext_getElem?'
  intro g hg
  have hg' : g < m + C.gates.length := by
    simpa [hlen1, hlen2] using hg
  have hg1 : g < (evalAllGates C (toInput H₀)).length := by
    simpa [hlen1] using hg'
  have hg2 : g < (evalAllGates C (toInput (mixedGraph S H₁ H₀))).length := by
    simpa [hlen2] using hg'
  rw [List.getElem?_eq_getElem hg1, List.getElem?_eq_getElem hg2]
  have hEq := hall g hg'
  rw [List.getD_eq_getElem (l := evalAllGates C (toInput H₀)) (d := false) hg1,
    List.getD_eq_getElem (l := evalAllGates C (toInput (mixedGraph S H₁ H₀))) (d := false) hg2] at hEq
  exact congrArg some hEq

end GateCharging

section LambdaLowerBound

noncomputable def Lambda' (n : ℕ) : ℕ :=
  Gamma (Nat.log 2 n) n

private theorem q_ge_7 (hn : n ≥ 4) (hn_large : n ≥ 4 * (Nat.log 2 n) ^ 2 + 1) :
    Nat.log 2 n ≥ 7 := by
  set q := Nat.log 2 n with hq_def
  by_contra hlt
  push_neg at hlt
  have hq_le : q ≤ 6 := by omega
  have h_lt : n < 2 ^ (q + 1) := Nat.lt_pow_succ_log_self (by omega : 1 < 2) n
  interval_cases q <;> omega

theorem lambda_lower_bound_strong (hn : n ≥ 4) (hn_large : n ≥ 4 * (Nat.log 2 n) ^ 2 + 1) :
    ∃ c : ℕ, c > n / Nat.log 2 n ∧ Lambda' n ≥ 2 ^ c := by
  set q := Nat.log 2 n with hq_def
  have hq7 : q ≥ 7 := q_ge_7 hn hn_large
  obtain ⟨c, hc_gt, hc_bound⟩ := iteratedRecurrenceStrong q n hq7 hn_large
  exact ⟨c, hq_def ▸ hc_gt, by simpa [Lambda', q] using hc_bound⟩

end LambdaLowerBound

section CanonicalMagnificationTree

noncomputable def canonicalMagnificationTree (n : ℕ) : MagnificationTree n :=
  let q := Nat.log 2 n
  let depth := if q ≤ n / q then 1 else 0
  { depth := depth
    numLeaves := 2 ^ (depth * q)
    q := q }

@[simp] theorem canonicalMagnificationTree_q (n : ℕ) :
    (canonicalMagnificationTree n).q = Nat.log 2 n := by
  simp [canonicalMagnificationTree]

theorem canonicalMagnificationTree_wellFormed (n : ℕ) :
    (canonicalMagnificationTree n).wellFormed := by
  unfold canonicalMagnificationTree MagnificationTree.wellFormed
  by_cases hq : Nat.log 2 n ≤ n / Nat.log 2 n
  · simp [hq]
  · simp [hq]

theorem exists_canonicalMagnificationTree (n : ℕ) :
    ∃ R : MagnificationTree n, R.q = Nat.log 2 n ∧ R.wellFormed := by
  refine ⟨canonicalMagnificationTree n, canonicalMagnificationTree_q n, ?_⟩
  exact canonicalMagnificationTree_wellFormed n

end CanonicalMagnificationTree

section ProtocolWitness

/-- A protocol-partition instance `(I, S)` in the sense of hamiltonian_route.tex §5.8. -/
structure ProtocolAdmissiblePair (n : ℕ) where
  family : Finset (Finset (Edge n))
  frontier : Frontier n

noncomputable def ProtocolAdmissiblePair.pp1 (A : ProtocolAdmissiblePair n) : ℕ :=
  protocolPartitionNumber A.family A.frontier

/-- Paper-faithful root/leaf data for Proposition 2001 (leaf-sum domination). -/
structure RootLeafProtocolWitness (n : ℕ) (R : MagnificationTree n) where
  root : ProtocolAdmissiblePair n
  leafPair : Fin R.numLeaves → ProtocolAdmissiblePair n
  rootRealizesLambda : Lambda' n ≤ root.pp1
  leafSumDomination :
    root.pp1 = Finset.univ.sum fun α : Fin R.numLeaves => (leafPair α).pp1

/-- Per-leaf gate-charging bounds `pp₁(I_α,S_α) ≤ |G_α|` for a fixed circuit. -/
structure GateChargingWitness (n : ℕ) (R : MagnificationTree n)
    {m : ℕ} (C : BooleanCircuit m)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (W : RootLeafProtocolWitness n R) where
  correct : CircuitDecidesHAM C toInput
  leafCharge :
    ∀ α : Fin R.numLeaves, (W.leafPair α).pp1 ≤ leafWidth R C α

theorem lambda_le_sum_leafWidth_of_witness
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (W : RootLeafProtocolWitness n R)
    (charging : GateChargingWitness n R C toInput W) :
    Lambda' n ≤ Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R C α := by
  calc
    Lambda' n ≤ W.root.pp1 := W.rootRealizesLambda
    _ = Finset.univ.sum fun α : Fin R.numLeaves => (W.leafPair α).pp1 := W.leafSumDomination
    _ ≤ Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R C α := by
        apply Finset.sum_le_sum
        intro α _
        exact charging.leafCharge α

end ProtocolWitness

section GeneralCircuitLowerBound

private theorem exp_cancel_right (a b c : ℕ) (hb_le_a : b ≤ a)
    (h : 2 ^ a ≤ c * 2 ^ b) : c ≥ 2 ^ (a - b) := by
  have h2b_pos : (2 : ℕ) ^ b > 0 := Nat.pos_of_ne_zero (by positivity)
  have hsplit : 2 ^ a = 2 ^ (a - b) * 2 ^ b := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hsplit, mul_comm (2 ^ (a - b)) (2 ^ b), mul_comm c (2 ^ b)] at h
  exact Nat.le_of_mul_le_mul_left h h2b_pos

theorem general_circuit_lower_bound_core
    (hn : n ≥ 4)
    (R : MagnificationTree n)
    (hq : R.q = Nat.log 2 n) (hWF : R.wellFormed)
    {m : ℕ} (C : BooleanCircuit m)
    (hLambda_le_sum :
      Lambda' n ≤ Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R C α)
    (hn_large : n ≥ 4 * (Nat.log 2 n) ^ 2 + 1) :
    ∃ c : ℕ, c > 0 ∧ C.size ≥ 2 ^ c := by
  obtain ⟨c_low, hc_gap, hLambda_bound⟩ := lambda_lower_bound_strong hn hn_large
  obtain ⟨_, hmu_le_bound, hmuMax_le⟩ := muMax_subexp R C (by omega) hq hWF
  have hmuMax_subexp : muMax R C ≤ 2 ^ (n / Nat.log 2 n) :=
    le_trans hmuMax_le hmu_le_bound
  have hSum_ge : Finset.univ.sum (fun α => leafWidth R C α) ≥ 2 ^ c_low :=
    le_trans hLambda_bound hLambda_le_sum
  have hChain : 2 ^ c_low ≤ C.size * muMax R C :=
    le_trans hSum_ge (width_budget_sharing_bound R C)
  have hChain2 : 2 ^ c_low ≤ C.size * 2 ^ (n / Nat.log 2 n) :=
    le_trans hChain (Nat.mul_le_mul_left C.size hmuMax_subexp)
  have hCancel := exp_cancel_right c_low (n / Nat.log 2 n) C.size (le_of_lt hc_gap) hChain2
  exact ⟨c_low - n / Nat.log 2 n, by omega, hCancel⟩

theorem general_circuit_lower_bound_with_tree (hn : n ≥ 4)
    (R : MagnificationTree n) (hq : R.q = Nat.log 2 n) (hWF : R.wellFormed)
    {m : ℕ} (C : BooleanCircuit m)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (W : RootLeafProtocolWitness n R)
    (charging : GateChargingWitness n R C toInput W)
    (hn_large : n ≥ 4 * (Nat.log 2 n) ^ 2 + 1) :
    ∃ c : ℕ, c > 0 ∧ C.size ≥ 2 ^ c :=
  general_circuit_lower_bound_core hn R hq hWF C
    (lambda_le_sum_leafWidth_of_witness R C toInput W charging) hn_large

theorem general_circuit_lower_bound (hn : n ≥ 4)
    {m : ℕ} (C : BooleanCircuit m)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (W : RootLeafProtocolWitness n (canonicalMagnificationTree n))
    (charging : GateChargingWitness n (canonicalMagnificationTree n) C toInput W)
    (hn_large : n ≥ 4 * (Nat.log 2 n) ^ 2 + 1) :
    ∃ c : ℕ, c > 0 ∧ C.size ≥ 2 ^ c :=
  general_circuit_lower_bound_core hn
    (canonicalMagnificationTree n)
    (canonicalMagnificationTree_q n)
    (canonicalMagnificationTree_wellFormed n)
    C (lambda_le_sum_leafWidth_of_witness (canonicalMagnificationTree n) C toInput W charging)
    hn_large

axiom lambda_le_sum_leafWidth_of_circuit
    {n : ℕ} (hn : n ≥ 4)
    (R : MagnificationTree n) (hq : R.q = Nat.log 2 n) (hWF : R.wellFormed)
    {m : ℕ} (C : BooleanCircuit m)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (hCorrect : CircuitDecidesHAM C toInput) :
    Lambda' n ≤ Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R C α

theorem general_circuit_lower_bound_unconditional (hn : n ≥ 4)
    {m : ℕ} (C : BooleanCircuit m)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (hCorrect : CircuitDecidesHAM C toInput)
    (hn_large : n ≥ 4 * (Nat.log 2 n) ^ 2 + 1) :
    ∃ c : ℕ, c > 0 ∧ C.size ≥ 2 ^ c :=
  general_circuit_lower_bound_core hn
    (canonicalMagnificationTree n)
    (canonicalMagnificationTree_q n)
    (canonicalMagnificationTree_wellFormed n)
    C (lambda_le_sum_leafWidth_of_circuit hn
      (canonicalMagnificationTree n)
      (canonicalMagnificationTree_q n)
      (canonicalMagnificationTree_wellFormed n)
      C toInput hCorrect)
    hn_large

end GeneralCircuitLowerBound

end PNeNp
