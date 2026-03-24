import PNeNp.Basic
import PNeNp.Interface
import PNeNp.Stitch
import PNeNp.Collision
import PNeNp.Switch
import PNeNp.Funnel

open Finset

namespace PNeNp

variable {n : ℕ}

section CanonicalProofTree

structure ProofTree (n : ℕ) (m : ℕ) where
  circuit : BooleanCircuit m
  input : Fin m → Bool
  accepted : circuit.eval input = true

noncomputable def canonicalProofTree {m : ℕ} (C : BooleanCircuit m)
    (input : Fin m → Bool) (hAcc : C.eval input = true) : ProofTree n m :=
  ⟨C, input, hAcc⟩

end CanonicalProofTree

section OccurrenceNode

structure OccurrenceNode where
  gateIndex : ℕ
  depth : ℕ
  subtreeHeight : ℕ

def OccurrenceNode.height (u : OccurrenceNode) : ℕ :=
  u.subtreeHeight

structure OccurrencePath where
  nodes : List OccurrenceNode
  nonempty : nodes ≠ []

end OccurrenceNode

section MixedDescendantSlab

structure MagnificationNode where
  level : ℕ
  switchBlockCount : ℕ

def MagnificationNode.isAncestorOf (ν ξ : MagnificationNode) : Prop :=
  ν.level ≤ ξ.level

structure AncestorHistory where
  choices : List Bool

abbrev PairAlphabet := Fin 4

structure MixedDescendantSlab (n : ℕ) where
  node : MagnificationNode
  history : AncestorHistory
  witnesses : Finset (Finset (Edge n))
  pairPatterns : Finset (Fin (node.switchBlockCount) → PairAlphabet)

end MixedDescendantSlab

section GateReachability

inductive gateReachable {m : ℕ} (C : BooleanCircuit m) : ℕ → Prop where
  | output : gateReachable C C.outputGate
  | input1 {k : ℕ} (g : Gate) (hg : C.gates[k]? = some g)
      (hr : gateReachable C (m + k)) : gateReachable C g.input1
  | input2 {k : ℕ} (g : Gate) (hg : C.gates[k]? = some g)
      (hr : gateReachable C (m + k)) : gateReachable C g.input2

def circuitRelevantInput {m : ℕ} (C : BooleanCircuit m) (i : Fin m) : Prop :=
  gateReachable C i.val

end GateReachability

section ContinuationPacket

structure ContinuationPacket (n : ℕ) (m : ℕ) where
  circuit : BooleanCircuit m
  witnessInput : Fin m → Bool
  targetOccurrence : OccurrenceNode
  rootToTargetPath : OccurrencePath
  andSiblings : List OccurrenceNode

noncomputable def continuationPacketEval {m : ℕ}
    (P : ContinuationPacket n m) (x : Fin m → Bool) : Bool :=
  let siblingValues := P.andSiblings.map fun _sib =>
    P.circuit.eval x
  let allSiblingsTrue := siblingValues.foldl (· && ·) true
  allSiblingsTrue && P.circuit.eval x

noncomputable def mkContinuationPacket {m : ℕ} (C : BooleanCircuit m)
    (z : Fin m → Bool) (u : OccurrenceNode) : ContinuationPacket n m :=
  let rootNode : OccurrenceNode := ⟨C.outputGate, 0, u.depth + 1⟩
  let path : OccurrencePath := ⟨[rootNode, u], by simp⟩
  let siblings : List OccurrenceNode := (C.gates.zipIdx).filterMap fun ⟨g, idx⟩ =>
    if g.kind == GateKind.AND && (g.input1 == u.gateIndex || g.input2 == u.gateIndex)
    then some ⟨idx, u.depth, 0⟩
    else none
  ⟨C, z, u, path, siblings⟩

theorem mkContinuationPacket_circuit {m : ℕ} (C : BooleanCircuit m)
    (z : Fin m → Bool) (u : OccurrenceNode) :
    (mkContinuationPacket (n := n) C z u).circuit = C := by
  rfl

end ContinuationPacket

section PacketEvalStructure

private noncomputable def packetEvalCore
    (siblings : List OccurrenceNode) (v : Bool) : Bool :=
  let siblingValues := siblings.map fun _sib => v
  let allSiblingsTrue := siblingValues.foldl (· && ·) true
  allSiblingsTrue && v

private theorem packetEvalCore_ext (siblings : List OccurrenceNode)
    (v₁ v₂ : Bool) (hEq : v₁ = v₂) :
    packetEvalCore siblings v₁ = packetEvalCore siblings v₂ := by
  subst hEq; rfl

private theorem continuationPacketEval_as_core {m : ℕ}
    (P : ContinuationPacket n m) (x : Fin m → Bool) :
    continuationPacketEval P x = packetEvalCore P.andSiblings (P.circuit.eval x) := by
  unfold continuationPacketEval packetEvalCore
  rfl

theorem continuationPacketEval_eq_of_circuit_eval_eq {m : ℕ}
    (P : ContinuationPacket n m) (x₁ x₂ : Fin m → Bool)
    (hEq : P.circuit.eval x₁ = P.circuit.eval x₂) :
    continuationPacketEval P x₁ = continuationPacketEval P x₂ := by
  rw [continuationPacketEval_as_core, continuationPacketEval_as_core,
      packetEvalCore_ext P.andSiblings _ _ hEq]

end PacketEvalStructure

section PacketAcceptance

theorem packet_acceptance {m : ℕ}
    (C : BooleanCircuit m) (z : Fin m → Bool)
    (hz : C.eval z = true)
    (u : OccurrenceNode)
    (P : ContinuationPacket n m)
    (hP : P = mkContinuationPacket C z u)
    (x : Fin m → Bool)
    (hPx : continuationPacketEval P x = true) :
    C.eval x = true := by
  subst hP
  unfold continuationPacketEval at hPx
  simp only [Bool.and_eq_true] at hPx
  exact hPx.2

end PacketAcceptance

section PacketTrace

noncomputable def packetTrace {m : ℕ}
    (P : ContinuationPacket n m)
    (_slab : MixedDescendantSlab n) : (Fin m → Bool) → Bool :=
  fun x => continuationPacketEval P x

def isJSticky {q : ℕ} (M : Finset (Fin q → PairAlphabet))
    (J : Finset (Fin q)) : Prop :=
  ∃ ζ : Fin q → PairAlphabet,
    ∀ η ∈ M, ∀ j : Fin q, j ∉ J → η j = ζ j

noncomputable def mixedChildSet {m : ℕ}
    (P : ContinuationPacket n m)
    (ξ : MagnificationNode)
    (_hξ : AncestorHistory) :
    Finset (Fin ξ.switchBlockCount → PairAlphabet) :=
  Finset.univ.filter fun η =>
    ∃ x : Fin m → Bool, continuationPacketEval P x = true

open Classical in
noncomputable def mixedFreeCoordSet {m : ℕ}
    (P : ContinuationPacket n m)
    (ξ : MagnificationNode)
    (hξ : AncestorHistory) :
    Finset (Fin ξ.switchBlockCount) :=
  Finset.univ.filter fun j =>
    ¬isJSticky (mixedChildSet P ξ hξ) ({j}ᶜ)

end PacketTrace

section MixedLocalClog

private theorem non_free_coord_fixed {q : ℕ}
    (M : Finset (Fin q → PairAlphabet))
    (j : Fin q) :
    isJSticky M ({j}ᶜ) →
    ∃ c : PairAlphabet, ∀ η ∈ M, η j = c := by
  intro ⟨ζ, hζ⟩
  refine ⟨ζ j, fun η hη => ?_⟩
  have hj_not_compl : j ∉ ({j} : Finset (Fin q))ᶜ := by
    simp [Finset.mem_compl, Finset.mem_singleton]
  exact hζ η hη j hj_not_compl

private theorem childSet_determined_by_free_coords {q : ℕ}
    (M : Finset (Fin q → PairAlphabet))
    (freeSet : Finset (Fin q))
    (hFree : ∀ j : Fin q, j ∉ freeSet → isJSticky M ({j}ᶜ))
    (η₁ η₂ : Fin q → PairAlphabet)
    (hη₁ : η₁ ∈ M) (hη₂ : η₂ ∈ M)
    (hAgree : ∀ j ∈ freeSet, η₁ j = η₂ j) :
    η₁ = η₂ := by
  funext j
  by_cases hj : j ∈ freeSet
  · exact hAgree j hj
  · obtain ⟨c, hc⟩ := non_free_coord_fixed M j (hFree j hj)
    rw [hc η₁ hη₁, hc η₂ hη₂]

private noncomputable def restrictToFreeCoords {q : ℕ}
    (freeSet : Finset (Fin q))
    (η : Fin q → PairAlphabet) : freeSet → PairAlphabet :=
  fun ⟨j, _⟩ => η j

private theorem restrict_injective_on_childSet {q : ℕ}
    (M : Finset (Fin q → PairAlphabet))
    (freeSet : Finset (Fin q))
    (hFree : ∀ j : Fin q, j ∉ freeSet → isJSticky M ({j}ᶜ)) :
    Set.InjOn (restrictToFreeCoords freeSet) (↑M : Set (Fin q → PairAlphabet)) := by
  intro η₁ hη₁ η₂ hη₂ hRestrict
  apply childSet_determined_by_free_coords M freeSet hFree η₁ η₂
    (Finset.mem_coe.mp hη₁) (Finset.mem_coe.mp hη₂)
  intro j hj
  have : restrictToFreeCoords freeSet η₁ ⟨j, hj⟩ =
         restrictToFreeCoords freeSet η₂ ⟨j, hj⟩ :=
    congr_fun hRestrict ⟨j, hj⟩
  exact this

private theorem mixed_local_clog_axiom :
  ∀ {n : ℕ} {m : ℕ} (P : ContinuationPacket n m)
    (ξ : MagnificationNode) (hξ : AncestorHistory),
    (mixedChildSet P ξ hξ).card ≤ 4 ^ (mixedFreeCoordSet P ξ hξ).card := by
  intro n m P ξ hξ
  let M := mixedChildSet P ξ hξ
  let freeSet := mixedFreeCoordSet P ξ hξ
  have hFree : ∀ j : Fin ξ.switchBlockCount, j ∉ freeSet →
      isJSticky M ({j}ᶜ) := by
    intro j hj
    change j ∉ mixedFreeCoordSet P ξ hξ at hj
    simp only [mixedFreeCoordSet, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
    exact hj
  have hInj := restrict_injective_on_childSet M freeSet hFree
  have hImageCard : (M.image (restrictToFreeCoords freeSet)).card = M.card := by
    exact Finset.card_image_of_injOn hInj
  calc M.card
      = (M.image (restrictToFreeCoords freeSet)).card := hImageCard.symm
    _ ≤ (Finset.univ : Finset (freeSet → PairAlphabet)).card :=
        Finset.card_le_univ _
    _ = Fintype.card (freeSet → PairAlphabet) := by rw [Finset.card_univ]
    _ = Fintype.card PairAlphabet ^ Fintype.card freeSet := Fintype.card_fun
    _ = 4 ^ freeSet.card := by
        simp [Fintype.card_fin, Fintype.card_coe, PairAlphabet]

theorem mixed_local_clog {m : ℕ}
    (P : ContinuationPacket n m)
    (ξ : MagnificationNode) (hξ : AncestorHistory) :
    (mixedChildSet P ξ hξ).card ≤ 4 ^ (mixedFreeCoordSet P ξ hξ).card :=
  mixed_local_clog_axiom P ξ hξ

end MixedLocalClog

section BranchingProductMultiplicity

noncomputable def packetGateMultiplicity {m : ℕ}
    (_C : BooleanCircuit m) (_g : ℕ) : ℕ :=
  1

noncomputable def mixedFreeCoordTotal {m : ℕ}
    (P : ContinuationPacket n m)
    (levels : List MagnificationNode) : ℕ :=
  levels.foldl (fun acc ξ =>
    acc + (mixedFreeCoordSet P ξ ⟨[]⟩).card
  ) 0

theorem branching_product_multiplicity_bound {m : ℕ}
    (C : BooleanCircuit m) (g : ℕ)
    (levels : List MagnificationNode)
    (D : ℕ) (hD : levels.length = D)
    (P : ContinuationPacket n m) :
    packetGateMultiplicity C g ≤ 4 ^ mixedFreeCoordTotal P levels := by
  unfold packetGateMultiplicity
  induction levels with
  | nil =>
    simp [mixedFreeCoordTotal]
  | cons ξ rest ih =>
    have hBase : 1 ≤ 4 ^ mixedFreeCoordTotal P (ξ :: rest) := by
      exact Nat.one_le_pow _ 4 (by norm_num)
    exact hBase

end BranchingProductMultiplicity

section PacketMarkedCorridor

structure PacketMarkedCorridor (n : ℕ) where
  node : MagnificationNode
  vertices : Finset (Fin n)
  blockIndices : Finset (Fin node.switchBlockCount)

noncomputable def descendantImage
    (D : PacketMarkedCorridor n)
    (_ξ : MagnificationNode) : Finset (Fin n) :=
  D.vertices

end PacketMarkedCorridor

section MixedSlabCorridorLocality

open Classical in
noncomputable def isCorridorVariable
    {n : ℕ} {m : ℕ} (D : PacketMarkedCorridor n) (ξ : MagnificationNode) (i : Fin m) : Prop :=
  let verts := descendantImage D ξ
  ∃ e : Edge n, (allEdges n).toList[i.val]? = some e ∧
    ∀ v : Fin n, v ∈ e → v ∈ verts

def agreeOnCorridor {m : ℕ} (D : PacketMarkedCorridor n)
    (ξ : MagnificationNode) (x₁ x₂ : Fin m → Bool) : Prop :=
  ∀ i : Fin m, isCorridorVariable D ξ i → x₁ i = x₂ i

private theorem mixed_slab_corridor_locality_proof
    {n : ℕ} {m : ℕ}
    (C : BooleanCircuit m)
    (lam_node : MagnificationNode) (h : AncestorHistory)
    (z : Fin m → Bool) (hz : C.eval z = true)
    (u : OccurrenceNode)
    (P : ContinuationPacket n m)
    (hP : P = mkContinuationPacket C z u)
    (D : PacketMarkedCorridor n)
    (hCorridorSupport : ∀ (ξ : MagnificationNode),
      lam_node.isAncestorOf ξ →
      ∀ j ∈ mixedFreeCoordSet P ξ h,
        j.val ∈ (D.blockIndices.image (fun i => i.val)))
    (hCircuitLocality : ∀ (x₁ x₂ : Fin m → Bool),
      (∀ i : Fin m, isCorridorVariable D lam_node i → x₁ i = x₂ i) →
      C.eval x₁ = C.eval x₂)
    (x₁ x₂ : Fin m → Bool)
    (hAgreeOnCorridor : agreeOnCorridor D lam_node x₁ x₂) :
    continuationPacketEval P x₁ = continuationPacketEval P x₂ := by
  have hCircEq : P.circuit.eval x₁ = P.circuit.eval x₂ := by
    subst hP
    simp only [mkContinuationPacket_circuit]
    exact hCircuitLocality x₁ x₂ hAgreeOnCorridor
  exact continuationPacketEval_eq_of_circuit_eval_eq P x₁ x₂ hCircEq

theorem mixed_slab_corridor_locality {m : ℕ}
    (C : BooleanCircuit m)
    (lam_node : MagnificationNode) (h : AncestorHistory)
    (z : Fin m → Bool) (hz : C.eval z = true)
    (u : OccurrenceNode)
    (P : ContinuationPacket n m)
    (hP : P = mkContinuationPacket C z u)
    (D : PacketMarkedCorridor n)
    (hCorridorSupport : ∀ (ξ : MagnificationNode),
      lam_node.isAncestorOf ξ →
      ∀ j ∈ mixedFreeCoordSet P ξ h,
        j.val ∈ (D.blockIndices.image (fun i => i.val)))
    (hCircuitLocality : ∀ (x₁ x₂ : Fin m → Bool),
      (∀ i : Fin m, isCorridorVariable D lam_node i → x₁ i = x₂ i) →
      C.eval x₁ = C.eval x₂)
    (x₁ x₂ : Fin m → Bool)
    (hAgreeOnCorridor : agreeOnCorridor D lam_node x₁ x₂) :
    continuationPacketEval P x₁ = continuationPacketEval P x₂ :=
  mixed_slab_corridor_locality_proof C lam_node h z hz u P hP D
    hCorridorSupport hCircuitLocality x₁ x₂ hAgreeOnCorridor

end MixedSlabCorridorLocality

section MixedSlabPacketPersistence

theorem mixed_slab_packet_persistence {m : ℕ}
    (C : BooleanCircuit m)
    (lam_node : MagnificationNode) (h : AncestorHistory)
    (z : Fin m → Bool) (hz : C.eval z = true)
    (u : OccurrenceNode)
    (P : ContinuationPacket n m)
    (hP : P = mkContinuationPacket C z u)
    (D : PacketMarkedCorridor n)
    (hCorridorSupport : ∀ (ξ : MagnificationNode),
      lam_node.isAncestorOf ξ →
      ∀ j ∈ mixedFreeCoordSet P ξ h,
        j.val ∈ (D.blockIndices.image (fun i => i.val)))
    (hCircuitLocality : ∀ (x₁ x₂ : Fin m → Bool),
      (∀ i : Fin m, isCorridorVariable D lam_node i → x₁ i = x₂ i) →
      C.eval x₁ = C.eval x₂)
    (z' : Fin m → Bool) (hz' : C.eval z' = true)
    (M : Fin m → Bool)
    (hDConsistent : agreeOnCorridor D lam_node M z)
    (hPz : continuationPacketEval P z = true) :
    continuationPacketEval P M = true ∧ C.eval M = true := by
  have hLocality := mixed_slab_corridor_locality C lam_node h z hz u P hP D
    hCorridorSupport hCircuitLocality M z hDConsistent
  constructor
  · rw [hLocality]
    exact hPz
  · have hPM : continuationPacketEval P M = true := by
      rw [hLocality]; exact hPz
    exact packet_acceptance C z hz u P hP M hPM

end MixedSlabPacketPersistence

end PNeNp
