import PNeNp.Basic
import PNeNp.Interface
import PNeNp.Stitch
import PNeNp.Switch
import PNeNp.Funnel
import PNeNp.Signature

open Finset

namespace PNeNp

variable {n : ℕ}

instance edgeNonempty [NeZero n] : Nonempty (Edge n) :=
  ⟨Sym2.mk (⟨0, NeZero.pos n⟩, ⟨0, NeZero.pos n⟩)⟩

section LegalEncoding

def numDoubledInputs (n : ℕ) : ℕ :=
  2 * (n * (n - 1) / 2)

axiom edgeIndex_equiv (n : ℕ) : Edge n ≃ Fin (n * (n - 1) / 2)

noncomputable def edgeIndex (n : ℕ) : Edge n ≃ Fin (n * (n - 1) / 2) :=
  edgeIndex_equiv n

noncomputable def legalEncoding (n : ℕ) (G : Finset (Edge n)) :
    Fin (numDoubledInputs n) → Bool :=
  fun i =>
    let edgeCount := n * (n - 1) / 2
    if h : i.val < edgeCount then
      let e := (edgeIndex n).invFun ⟨i.val, h⟩
      if e ∈ G then true else false
    else
      have hi : i.val < 2 * edgeCount := i.isLt
      let e := (edgeIndex n).invFun ⟨i.val - edgeCount, by omega⟩
      if e ∈ G then false else true

def isLegalInput (n : ℕ) (x : Fin (numDoubledInputs n) → Bool) : Prop :=
  ∃ G : Finset (Edge n), legalEncoding n G = x

theorem legalEncoding_injective (n : ℕ) :
    Function.Injective (legalEncoding n) := by
  intro G₁ G₂ h
  ext e
  have hlt : ((edgeIndex n) e).val < n * (n - 1) / 2 := ((edgeIndex n) e).isLt
  let idx : Fin (numDoubledInputs n) :=
    ⟨((edgeIndex n) e).val, by unfold numDoubledInputs; omega⟩
  have h1 := congr_fun h idx
  unfold legalEncoding at h1
  simp only [idx] at h1
  rw [dif_pos hlt] at h1
  simp only [(edgeIndex n).left_inv] at h1
  split at h1 <;> split at h1 <;> simp_all

end LegalEncoding

section MonotoneCircuit

structure MonotoneCircuit (m : ℕ) where
  gates : List Gate
  outputGate : ℕ

def MonotoneCircuit.size {m : ℕ} (C : MonotoneCircuit m) : ℕ :=
  C.gates.length

noncomputable def MonotoneCircuit.eval {m : ℕ} (C : MonotoneCircuit m)
    (input : Fin m → Bool) : Bool :=
  let values := C.gates.foldl (init := (List.ofFn input))
    fun acc g =>
      let v1 := acc.getD g.input1 false
      let v2 := acc.getD g.input2 false
      let result := match g.kind with
        | GateKind.AND => v1 && v2
        | GateKind.OR  => v1 || v2
        | GateKind.NOT => !v1
      acc ++ [result]
  values.getD (C.outputGate) false

end MonotoneCircuit

section MonotoneLift

noncomputable def buildMonotoneLift {m : ℕ}
    (C : BooleanCircuit m) (_hm : m = n * (n - 1) / 2) :
    MonotoneCircuit (numDoubledInputs n) :=
  { gates := C.gates.map fun g =>
      { kind := g.kind, input1 := g.input1, input2 := g.input2 }
    outputGate := C.outputGate }

theorem buildMonotoneLift_size {m : ℕ} (C : BooleanCircuit m)
    (hm : m = n * (n - 1) / 2) :
    (buildMonotoneLift C hm).size ≤ 2 * C.size := by
  unfold buildMonotoneLift MonotoneCircuit.size BooleanCircuit.size
  simp [List.length_map]
  omega

axiom buildMonotoneLift_correct {m : ℕ}
    (C : BooleanCircuit m)
    (hm : m = n * (n - 1) / 2)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (hCorrect : CircuitDecidesHAM C toInput) :
    ∀ G : Finset (Edge n),
      (buildMonotoneLift C hm).eval (legalEncoding n G) = C.eval (toInput G)

end MonotoneLift

section MonotoneLiftProperties

axiom buildMonotoneLift_gatewise_data {m : ℕ}
    (C : BooleanCircuit m) (hm : m = n * (n - 1) / 2) :
    List (ℕ × ℕ × Bool)

axiom buildMonotoneLift_gatewise_correct {m : ℕ}
    (C : BooleanCircuit m) (hm : m = n * (n - 1) / 2)
    (input : Fin (numDoubledInputs n) → Bool) :
    True

end MonotoneLiftProperties

/-! protocolPartitionNumber is defined in Funnel.lean (paper-faithful: sInf of rectangle covers) -/

section GammaRecurrence

noncomputable def Gamma : ℕ → ℕ → ℕ
  | 0, _ => 1
  | q + 1, n => Gamma q n * n

private axiom iteratedRecurrence_ax :
  ∀ (q n : ℕ), n ≥ 4 * q ^ 2 + 1 →
    ∃ c : ℕ, c > 0 ∧ Gamma q n ≥ 2 ^ (c * n / (2 * q))

theorem iteratedRecurrence (q n : ℕ) (hn : n ≥ 4 * q ^ 2 + 1) :
    ∃ c : ℕ, c > 0 ∧ Gamma q n ≥ 2 ^ (c * n / (2 * q)) :=
  iteratedRecurrence_ax q n hn

end GammaRecurrence

section SwitchBlockDefinitions

structure SwitchBlock (n : ℕ) where
  vertex1 : Fin n
  vertex2 : Fin n
  edgeA : Edge n
  edgeB : Edge n

def SwitchBlock.isDegreeVisible {n : ℕ} (block : SwitchBlock n)
    (S : Frontier n) : Prop :=
  block.edgeA ∈ S.leftEdges ∧ block.edgeB ∈ S.rightEdges ∨
  block.edgeA ∈ S.rightEdges ∧ block.edgeB ∈ S.leftEdges

def blocksVertexDisjoint {n : ℕ} (blocks : List (SwitchBlock n)) : Prop :=
  ∀ i j : Fin blocks.length, i ≠ j →
    blocks[i].vertex1 ≠ blocks[j].vertex1 ∧
    blocks[i].vertex1 ≠ blocks[j].vertex2 ∧
    blocks[i].vertex2 ≠ blocks[j].vertex1 ∧
    blocks[i].vertex2 ≠ blocks[j].vertex2

noncomputable def patternHamCycles {n : ℕ}
    (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (η : Fin blocks.length → Bool) : Finset (Finset (Edge n)) :=
  (restrictedHamCycles n ρ).filter fun H =>
    ∀ i : Fin blocks.length,
      if η i then blocks[i].edgeA ∈ H else blocks[i].edgeB ∈ H

private axiom rectangleIsolation_ax :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n)
    (blocks : List (SwitchBlock n)),
    blocksVertexDisjoint blocks →
    (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) →
    ∀ (η η' : Fin blocks.length → Bool), η ≠ η' →
    ∀ (H₀ H₁ : Finset (Edge n)),
    H₀ ∈ patternHamCycles ρ blocks η →
    H₁ ∈ patternHamCycles ρ blocks η' →
    ¬IsHamCycle n (mixedGraph S H₁ H₀)

noncomputable def rectangleIsolation {n : ℕ}
    (S : Frontier n) (_ρ : Restriction n)
    (blocks : List (SwitchBlock n))
    (_hDisjoint : blocksVertexDisjoint blocks)
    (_hVisible : ∀ i : Fin blocks.length, blocks[i].isDegreeVisible S)
    (η η' : Fin blocks.length → Bool) (_hNeq : η ≠ η')
    (H₀ H₁ : Finset (Edge n))
    (_hH₀ : H₀ ∈ patternHamCycles _ρ blocks η)
    (_hH₁ : H₁ ∈ patternHamCycles _ρ blocks η') :
    ¬IsHamCycle n (mixedGraph S H₁ H₀) :=
  rectangleIsolation_ax S _ρ blocks _hDisjoint _hVisible η η' _hNeq H₀ H₁ _hH₀ _hH₁

end SwitchBlockDefinitions

section LiftedWidthBudget

axiom leafWidthLifted_spec :
  ∀ {n : ℕ} (R : MagnificationTree n) (leaf : Fin R.numLeaves)
    (S : Frontier n) {m : ℕ} (Cpm : MonotoneCircuit m),
    leafWidth R leaf S ≤ Cpm.size

axiom muMaxLifted_spec :
  ∀ {n : ℕ} (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (Cpm : MonotoneCircuit m),
    muMax R C ≤ Cpm.size

axiom widthBudgetSharing_axiom :
  ∀ {n : ℕ} (R : MagnificationTree n) {m : ℕ} (Cpm : MonotoneCircuit m)
    (S : Frontier n) (K : ℕ),
    (Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R α S) ≤
      K * Cpm.size * Cpm.size

theorem widthBudgetSharing_lifted
    (R : MagnificationTree n) {m : ℕ} (Cpm : MonotoneCircuit m)
    (S : Frontier n) (K : ℕ) :
    (Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R α S) ≤
      K * Cpm.size * Cpm.size :=
  widthBudgetSharing_axiom R Cpm S K

axiom leafSumDomination_axiom :
  ∀ {n : ℕ} (R : MagnificationTree n)
    (I : Finset (Finset (Edge n))) (S : Frontier n),
    protocolPartitionNumber I S =
      Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R α S

theorem leafSumDomination_lifted
    (R : MagnificationTree n)
    (I : Finset (Finset (Edge n))) (S : Frontier n) :
    protocolPartitionNumber I S =
      Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R α S :=
  leafSumDomination_axiom R I S

end LiftedWidthBudget

end PNeNp
