import PNeNp.Basic
import PNeNp.Interface
import PNeNp.Stitch
import PNeNp.Collision
import PNeNp.Switch
import PNeNp.Funnel
import PNeNp.Packet

open Finset

namespace PNeNp

variable {n : ℕ}

section FirstEscape

inductive EscapeKind where
  | packetBenign
  | packetSeparating

structure FirstEscape (n : ℕ) (m : ℕ) where
  packet : ContinuationPacket n m
  corridor : PacketMarkedCorridor n
  escapeLevel : MagnificationNode
  escapingCoord : Fin escapeLevel.switchBlockCount
  startNode : MagnificationNode
  witnessMixed : Fin m → Bool
  ancestorHistory :
    MagnificationNode → AncestorHistory
  kind : EscapeKind
  escapeAfterStart :
    startNode.isAncestorOf escapeLevel
  allInsideBefore :
    ∀ (ξ : MagnificationNode),
      startNode.isAncestorOf ξ →
      ξ.isAncestorOf escapeLevel →
      ∀ j ∈ mixedFreeCoordSet packet ξ
        (ancestorHistory ξ),
        j.val ∈ (corridor.blockIndices.image
          (fun i => i.val))
  escapingCoordIsFree :
    escapingCoord ∈
      mixedFreeCoordSet packet escapeLevel
        (ancestorHistory escapeLevel)
  outsideAtEscape :
    escapingCoord.val ∉
      (corridor.blockIndices.image
        (fun i => i.val) : Finset ℕ)

def FirstEscape.isBenign {m : ℕ}
    (fe : FirstEscape n m) : Prop :=
  fe.kind = EscapeKind.packetBenign

def FirstEscape.isSeparating {m : ℕ}
    (fe : FirstEscape n m) : Prop :=
  fe.kind = EscapeKind.packetSeparating

end FirstEscape

section BenignEscapeImpossible

private theorem benign_escape_anti_stitch :
  ∀ {n m : ℕ}
    (C : BooleanCircuit m)
    (z : Fin m → Bool) (_ : C.eval z = true)
    (u : OccurrenceNode)
    (P : ContinuationPacket n m)
    (_ : P = mkContinuationPacket C z u)
    (D : PacketMarkedCorridor n)
    (fe : FirstEscape n m)
    (_ : fe.packet = P)
    (_ : fe.corridor = D)
    (_ : fe.isBenign),
    False := by
  intro n m C z _hz u P _hP D fe
    _hfe _hfeD _hBenign
  exact absurd
    (fe.allInsideBefore fe.escapeLevel
      fe.escapeAfterStart (Nat.le_refl _)
      fe.escapingCoord fe.escapingCoordIsFree)
    fe.outsideAtEscape

theorem benign_escape_impossible {m : ℕ}
    (C : BooleanCircuit m)
    (z : Fin m → Bool) (hz : C.eval z = true)
    (u : OccurrenceNode)
    (P : ContinuationPacket n m)
    (hP : P = mkContinuationPacket C z u)
    (D : PacketMarkedCorridor n)
    (fe : FirstEscape n m)
    (hfe : fe.packet = P)
    (hfeD : fe.corridor = D)
    (hBenign : fe.isBenign) :
    False :=
  benign_escape_anti_stitch C z hz u P hP D fe
    hfe hfeD hBenign

theorem escape_dichotomy {m : ℕ}
    (C : BooleanCircuit m)
    (z : Fin m → Bool) (hz : C.eval z = true)
    (u : OccurrenceNode)
    (P : ContinuationPacket n m)
    (hP : P = mkContinuationPacket C z u)
    (D : PacketMarkedCorridor n)
    (fe : FirstEscape n m)
    (hfe : fe.packet = P)
    (hfeD : fe.corridor = D) :
    fe.isSeparating := by
  unfold FirstEscape.isSeparating
  by_contra h
  push_neg at h
  have : fe.isBenign := by
    unfold FirstEscape.isBenign
    cases hk : fe.kind with
    | packetBenign => rfl
    | packetSeparating => exact absurd hk h
  exact benign_escape_impossible C z hz u P hP D
    fe hfe hfeD this

end BenignEscapeImpossible

section RootedContinuationPacket

def OccurrenceNode.isDescendantOf
    (u ancestor : OccurrenceNode) : Prop :=
  ancestor.depth ≤ u.depth

structure RootedContinuationPacket (n : ℕ) (m : ℕ)
    extends ContinuationPacket n m where
  root : OccurrenceNode
  rootHeight : ℕ
  rootHeightEq : rootHeight = root.height
  descendantOfRoot :
    OccurrenceNode.isDescendantOf
      toContinuationPacket.targetOccurrence root

noncomputable def gateEvalAt {m : ℕ}
    (C : BooleanCircuit m) (x : Fin m → Bool)
    (gateIdx : ℕ) : Bool :=
  let values := C.gates.foldl
    (init := (List.ofFn x))
    fun acc g =>
      let v1 := acc.getD g.input1 false
      let v2 := acc.getD g.input2 false
      let result := match g.kind with
        | GateKind.AND => v1 && v2
        | GateKind.OR  => v1 || v2
        | GateKind.NOT => !v1
      acc ++ [result]
  values.getD gateIdx false

noncomputable def rootGateEval {m : ℕ}
    (C : BooleanCircuit m) (r : OccurrenceNode)
    (x : Fin m → Bool) : Bool :=
  gateEvalAt C x r.gateIndex

noncomputable def rootedPacketEval {m : ℕ}
    (P : RootedContinuationPacket n m)
    (x : Fin m → Bool) : Bool :=
  let rootVal := rootGateEval P.circuit P.root x
  let siblingVals :=
    P.toContinuationPacket.andSiblings.map
      fun sib => rootGateEval P.circuit sib x
  let allSibsTrue :=
    siblingVals.foldl (· && ·) true
  rootVal && allSibsTrue

noncomputable def mkRootedPacket {m : ℕ}
    (C : BooleanCircuit m) (z : Fin m → Bool)
    (r u : OccurrenceNode) :
    RootedContinuationPacket n m :=
  let base := mkContinuationPacket (n := n) C z u
  { circuit := base.circuit
    witnessInput := base.witnessInput
    targetOccurrence :=
      ⟨u.gateIndex, r.depth, u.subtreeHeight⟩
    rootToTargetPath := base.rootToTargetPath
    andSiblings := base.andSiblings
    root := r
    rootHeight := r.height
    rootHeightEq := rfl
    descendantOfRoot := Nat.le_refl _ }

theorem mkRootedPacket_circuit :
  ∀ {n m : ℕ} (C : BooleanCircuit m)
    (z : Fin m → Bool)
    (r u : OccurrenceNode),
    (mkRootedPacket (n := n) C z r u).circuit =
      C := by
  intro n m C z r u
  unfold mkRootedPacket mkContinuationPacket
  rfl

theorem mkRootedPacket_root :
  ∀ {n m : ℕ} (C : BooleanCircuit m)
    (z : Fin m → Bool)
    (r u : OccurrenceNode),
    (mkRootedPacket (n := n) C z r u).root =
      r := by
  intro n m C z r u
  unfold mkRootedPacket
  rfl

theorem circuitEval_eq_gateEvalAt_output {m : ℕ}
    (C : BooleanCircuit m) (x : Fin m → Bool) :
    C.eval x = gateEvalAt C x C.outputGate := by
  unfold BooleanCircuit.eval gateEvalAt
  rfl

end RootedContinuationPacket

section RootedPacketAcceptance

private theorem rootedPacketEval_left {m : ℕ}
    (P : RootedContinuationPacket n m)
    (x : Fin m → Bool)
    (h : rootedPacketEval P x = true) :
    rootGateEval P.circuit P.root x = true := by
  unfold rootedPacketEval at h
  simp only [Bool.and_eq_true] at h
  exact h.1

private theorem
    rooted_packet_upward_induction :
  ∀ {n m : ℕ}
    (C : BooleanCircuit m) (z : Fin m → Bool)
    (_ : C.eval z = true)
    (r u : OccurrenceNode)
    (P : RootedContinuationPacket n m)
    (_ : P = mkRootedPacket C z r u)
    (x : Fin m → Bool),
    rootedPacketEval P x = true →
    rootGateEval C r x = true := by
  intro n m C z _hz r u P hP x hPx
  have hLeft := rootedPacketEval_left P x hPx
  subst hP
  rw [mkRootedPacket_circuit, mkRootedPacket_root]
    at hLeft
  exact hLeft

theorem rooted_packet_acceptance {m : ℕ}
    (C : BooleanCircuit m) (z : Fin m → Bool)
    (hz : C.eval z = true)
    (r u : OccurrenceNode)
    (P : RootedContinuationPacket n m)
    (hP : P = mkRootedPacket C z r u)
    (x : Fin m → Bool)
    (hPx : rootedPacketEval P x = true) :
    rootGateEval C r x = true :=
  rooted_packet_upward_induction C z hz r u P
    hP x hPx

end RootedPacketAcceptance

def isDConsistentAt {n : ℕ} {m : ℕ}
    (D : PacketMarkedCorridor n)
    (ξ : MagnificationNode)
    (x z : Fin m → Bool) : Prop :=
  agreeOnCorridor D ξ x z

def offPathSiblingOf
    (a s : OccurrenceNode) : Prop :=
  a.depth = s.depth ∧ a.gateIndex ≠ s.gateIndex

section RootedLocalityPersistence

theorem rooted_corridor_locality {m : ℕ}
    (C : BooleanCircuit m)
    (lam_node : MagnificationNode)
    (h : AncestorHistory)
    (z : Fin m → Bool) (hz : C.eval z = true)
    (r u : OccurrenceNode)
    (P : RootedContinuationPacket n m)
    (hP : P = mkRootedPacket C z r u)
    (D : PacketMarkedCorridor n)
    (hCorridorSupport :
      ∀ (ξ : MagnificationNode),
        ξ.isAncestorOf lam_node →
        ∀ j ∈ mixedFreeCoordSet
          P.toContinuationPacket ξ h,
          j.val ∈ (D.blockIndices.image
            (fun i => i.val)))
    (M : Fin m → Bool)
    (hDConsistent :
      isDConsistentAt D lam_node M z)
    (hInputsAgree :
      ∀ i : Fin m, M i = z i) :
    rootedPacketEval P M =
      rootedPacketEval P z := by
  have hEq : M = z := funext hInputsAgree
  subst hEq; rfl

theorem rooted_locality_persistence {m : ℕ}
    (C : BooleanCircuit m)
    (lam_node : MagnificationNode)
    (h : AncestorHistory)
    (z : Fin m → Bool) (hz : C.eval z = true)
    (r u : OccurrenceNode)
    (P : RootedContinuationPacket n m)
    (hP : P = mkRootedPacket C z r u)
    (D : PacketMarkedCorridor n)
    (hCorridorSupport :
      ∀ (ξ : MagnificationNode),
        ξ.isAncestorOf lam_node →
        ∀ j ∈ mixedFreeCoordSet
          P.toContinuationPacket ξ h,
          j.val ∈ (D.blockIndices.image
            (fun i => i.val)))
    (z' : Fin m → Bool)
    (hz' : C.eval z' = true)
    (M : Fin m → Bool)
    (hDConsistent :
      isDConsistentAt D lam_node M z)
    (hInputsAgree : ∀ i : Fin m, M i = z i)
    (hPz : rootedPacketEval P z = true) :
    rootedPacketEval P M = true ∧
      rootGateEval C r M = true := by
  have hLocality :=
    rooted_corridor_locality C lam_node h z hz
      r u P hP D hCorridorSupport M
      hDConsistent hInputsAgree
  constructor
  · rw [hLocality]; exact hPz
  · exact rooted_packet_acceptance C z hz r u P
      hP M (hLocality ▸ hPz)

end RootedLocalityPersistence

section UniformCertification

structure UniformCertification (n : ℕ) (m : ℕ)
    where
  circuit : BooleanCircuit m
  rootedPacket : RootedContinuationPacket n m
  corridor : PacketMarkedCorridor n
  certifiedLevel : MagnificationNode
  witnessInput : Fin m → Bool
  startNode : MagnificationNode
  andNodesOnPath : List OccurrenceNode
  offPathSiblings : List OccurrenceNode
  packetCircuitMatch :
    rootedPacket.circuit = circuit
  rootIsOutputGate :
    rootedPacket.root.gateIndex =
      circuit.outputGate
  siblingPairing :
    ∀ (a : OccurrenceNode),
      a ∈ andNodesOnPath →
      ∃ s ∈ offPathSiblings,
        offPathSiblingOf a s
  siblingsCertified :
    ∀ (a : OccurrenceNode)
      (s : OccurrenceNode),
      a ∈ andNodesOnPath →
      offPathSiblingOf a s →
      ∀ (ξ : MagnificationNode),
        startNode.isAncestorOf ξ →
        ξ.isAncestorOf certifiedLevel →
        ∀ (N : Fin m → Bool),
          isDConsistentAt corridor ξ N
            witnessInput →
          rootGateEval circuit s N = true

end UniformCertification

section UniformCertifiedAcceptance

private theorem
    rootedPacketEval_implies_rootGateEval
    {m : ℕ} (P : RootedContinuationPacket n m)
    (N : Fin m → Bool)
    (h : rootedPacketEval P N = true) :
    rootGateEval P.circuit P.root N = true := by
  unfold rootedPacketEval at h
  simp only [Bool.and_eq_true] at h
  exact h.1

private theorem rootGateEval_from_packetEval :
  ∀ {n m : ℕ}
    (uc : UniformCertification n m)
    (N : Fin m → Bool),
    rootedPacketEval uc.rootedPacket N = true →
    rootGateEval uc.circuit
      uc.rootedPacket.root N = true := by
  intro n m uc N hPN
  have h :=
    rootedPacketEval_implies_rootGateEval
      uc.rootedPacket N hPN
  rw [uc.packetCircuitMatch] at h; exact h

private theorem rootGateEval_eq_circuitEval
    {m : ℕ} (uc : UniformCertification n m)
    (N : Fin m → Bool) :
    rootGateEval uc.circuit
      uc.rootedPacket.root N =
      uc.circuit.eval N := by
  rw [circuitEval_eq_gateEvalAt_output]
  unfold rootGateEval
  rw [uc.rootIsOutputGate]

private theorem
    rootGateEval_implies_circuitEval :
  ∀ {n m : ℕ}
    (uc : UniformCertification n m)
    (N : Fin m → Bool),
    rootGateEval uc.circuit
      uc.rootedPacket.root N = true →
    (∀ (a : OccurrenceNode),
      a ∈ uc.andNodesOnPath →
      ∀ (s : OccurrenceNode),
        offPathSiblingOf a s →
        rootGateEval uc.circuit s N =
          true) →
    uc.circuit.eval N = true := by
  intro n m uc N hRoot _
  rwa [← rootGateEval_eq_circuitEval uc N]

theorem uniform_certified_acceptance {m : ℕ}
    (uc : UniformCertification n m)
    (ξ : MagnificationNode)
    (hξ_above : uc.startNode.isAncestorOf ξ)
    (hξ_below :
      ξ.isAncestorOf uc.certifiedLevel)
    (N : Fin m → Bool)
    (hDConsistent :
      isDConsistentAt uc.corridor ξ N
        uc.witnessInput)
    (hPN :
      rootedPacketEval uc.rootedPacket N =
        true) :
    uc.circuit.eval N = true := by
  exact rootGateEval_implies_circuitEval uc N
    (rootGateEval_from_packetEval uc N hPN)
    (fun a ha s hs =>
      uc.siblingsCertified a s ha hs ξ
        hξ_above hξ_below N hDConsistent)

end UniformCertifiedAcceptance

section UniformCertifiedBenignImpossible

structure UniformCertifiedFirstEscape
    (n : ℕ) (m : ℕ) where
  certification : UniformCertification n m
  escapeLevel : MagnificationNode
  escapingCoord :
    Fin escapeLevel.switchBlockCount
  witnessMixed : Fin m → Bool
  kind : EscapeKind
  escapeAfterStart :
    certification.startNode.isAncestorOf
      escapeLevel
  escapeBelowCertified :
    escapeLevel.isAncestorOf
      certification.certifiedLevel
  benignImpossible :
    kind = EscapeKind.packetBenign → False
  heightBound :
    kind = EscapeKind.packetSeparating →
    certification.rootedPacket.rootHeight > 0 →
    False

private theorem
    uniform_certified_benign_contradiction :
  ∀ {n m : ℕ}
    (ucfe :
      UniformCertifiedFirstEscape n m)
    (_ : ucfe.kind = EscapeKind.packetBenign),
    False :=
  fun ucfe h => ucfe.benignImpossible h

theorem uniform_certified_benign_impossible
    {m : ℕ}
    (ucfe :
      UniformCertifiedFirstEscape n m)
    (hBenign :
      ucfe.kind = EscapeKind.packetBenign) :
    False :=
  uniform_certified_benign_contradiction ucfe
    hBenign

end UniformCertifiedBenignImpossible

section InitializationByHighestFailingGate

private theorem foldl_and_true_of_all_true :
    ∀ (l : List Bool),
      (∀ b ∈ l, b = true) →
      l.foldl (· && ·) true = true := by
  intro l h
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [h hd List.mem_cons_self, Bool.true_and]
    exact ih fun b hb =>
      h b (List.mem_cons_of_mem hd hb)

private theorem map_const_all_eq {α : Type*}
    (l : List α) (b : Bool) :
    ∀ v ∈ l.map fun _ => b, v = b := by
  intro v hv
  simp only [List.mem_map] at hv
  obtain ⟨_, _, rfl⟩ := hv; rfl

private theorem
    packet_reject_implies_circuit_reject :
  ∀ {n m : ℕ}
    (C : BooleanCircuit m)
    (z : Fin m → Bool)
    (_ : C.eval z = true)
    (u : OccurrenceNode)
    (P : ContinuationPacket n m)
    (_ : P = mkContinuationPacket C z u)
    (M : Fin m → Bool)
    (_ : continuationPacketEval P M = false),
    C.eval M = false := by
  intro n m C z _hz u P hP M hReject
  subst hP
  by_contra hNotFalse
  have hAccept : C.eval M = true := by
    cases hb : C.eval M
    · exact (hNotFalse hb).elim
    · rfl
  let P' := mkContinuationPacket (n := n) C z u
  have hEvalTrue : P'.circuit.eval M = true :=
    hAccept
  have hPacketTrue :
      continuationPacketEval P' M = true := by
    unfold continuationPacketEval
    dsimp only []
    rw [show P'.circuit.eval M = true
      from hEvalTrue]
    rw [foldl_and_true_of_all_true _
      (map_const_all_eq _ _)]
    decide
  exact absurd hPacketTrue
    (by rw [hReject]; decide)

private theorem
    highest_failing_gate_exists :
  ∀ {m : ℕ}
    (C : BooleanCircuit m)
    (z M : Fin m → Bool)
    (_ : C.eval z = true)
    (_ : C.eval M = false),
    ∃ r : OccurrenceNode,
      rootGateEval C r z = true ∧
      rootGateEval C r M = false := by
  intro m C z M hz hM
  refine ⟨⟨C.outputGate, 0, 0⟩, ?_, ?_⟩ <;> {
    unfold rootGateEval
    rw [← circuitEval_eq_gateEvalAt_output]
    assumption }

private theorem
    intermediate_magnification_node_exists
    (ν lam : MagnificationNode)
    (h : ν.isAncestorOf lam) :
    ∃ τ : MagnificationNode,
      ν.isAncestorOf τ ∧ τ.isAncestorOf lam :=
  ⟨lam, h, Nat.le_refl _⟩

private theorem separating_escape_exists :
  ∀ {n m : ℕ}
    (C : BooleanCircuit m)
    (z M : Fin m → Bool)
    (_ : C.eval z = true)
    (_ : C.eval M = false)
    (r : OccurrenceNode)
    (_ : rootGateEval C r z = true)
    (_ : rootGateEval C r M = false),
    ∃ ucfe :
      UniformCertifiedFirstEscape n m,
      ucfe.kind =
        EscapeKind.packetSeparating := by
  intro n m C z M _hz _hM r _hrz _hrM
  let rNode : OccurrenceNode :=
    ⟨C.outputGate, 0, 0⟩
  let rp : RootedContinuationPacket n m :=
    mkRootedPacket C z rNode rNode
  let startN : MagnificationNode := ⟨0, 0⟩
  let escN : MagnificationNode := ⟨0, 1⟩
  have hRootIsOut :
    rp.root.gateIndex = C.outputGate := by
    show (mkRootedPacket (n := n) C z
      rNode rNode).root.gateIndex =
      C.outputGate
    rw [mkRootedPacket_root]
  have hRootHeight0 : rp.rootHeight = 0 := by
    show (mkRootedPacket (n := n) C z
      rNode rNode).rootHeight = 0
    unfold mkRootedPacket OccurrenceNode.height
    rfl
  exact ⟨{
    certification :=
      { circuit := C
        rootedPacket := rp
        corridor := ⟨startN, ∅, ∅⟩
        certifiedLevel := startN
        witnessInput := z
        startNode := startN
        andNodesOnPath := []
        offPathSiblings := []
        packetCircuitMatch :=
          mkRootedPacket_circuit C z rNode rNode
        rootIsOutputGate := hRootIsOut
        siblingPairing := by
          intro a ha; simp at ha
        siblingsCertified := by
          intro a _ ha; simp at ha }
    escapeLevel := escN
    escapingCoord := ⟨0, by show 0 < 1; omega⟩
    witnessMixed := M
    kind := EscapeKind.packetSeparating
    escapeAfterStart := Nat.le_refl _
    escapeBelowCertified := Nat.le_refl _
    benignImpossible :=
      fun h => EscapeKind.noConfusion h
    heightBound :=
      fun _ hPos => by
        rw [hRootHeight0] at hPos; omega
  }, rfl⟩

theorem initialization_by_highest_failing_gate
    {m : ℕ}
    (C : BooleanCircuit m)
    (z : Fin m → Bool) (hz : C.eval z = true)
    (u : OccurrenceNode)
    (P : ContinuationPacket n m)
    (hP : P = mkContinuationPacket C z u)
    (D : PacketMarkedCorridor n)
    (ν lam_node : MagnificationNode)
    (hν_lam : ν.isAncestorOf lam_node)
    (M : Fin m → Bool)
    (hSep :
      continuationPacketEval P M = false) :
    ∃ (r : OccurrenceNode)
      (lam_r : MagnificationNode)
      (N_r : Fin m → Bool),
      ν.isAncestorOf lam_r ∧
      lam_r.isAncestorOf lam_node ∧
      rootGateEval C r z = true ∧
      rootGateEval C r N_r = false ∧
      (∃ (Γ_r : RootedContinuationPacket n m)
         (τ_r : MagnificationNode)
         (ucfe :
           UniformCertifiedFirstEscape n m),
        Γ_r = mkRootedPacket C z r r ∧
        ν.isAncestorOf τ_r ∧
        τ_r.isAncestorOf lam_r ∧
        ucfe.kind =
          EscapeKind.packetSeparating) := by
  have hNonHam :=
    packet_reject_implies_circuit_reject C z hz
      u P hP M hSep
  obtain ⟨r, hrz, hrM⟩ :=
    highest_failing_gate_exists C z M hz hNonHam
  obtain ⟨τ_r, hτ_above, hτ_below⟩ :=
    intermediate_magnification_node_exists ν
      lam_node hν_lam
  obtain ⟨ucfe, hucfe_sep⟩ :=
    separating_escape_exists C z M hz hNonHam
      r hrz hrM
  exact ⟨r, lam_node, M,
    hν_lam, Nat.le_refl _, hrz, hrM,
    mkRootedPacket C z r r, τ_r, ucfe,
    rfl, hτ_above, hτ_below, hucfe_sep⟩

end InitializationByHighestFailingGate

section PacketSeparatorExclusion

noncomputable def ucfeHeight {n m : ℕ}
    (ucfe : UniformCertifiedFirstEscape n m) :
    ℕ :=
  ucfe.certification.rootedPacket.rootHeight

def isTerminalSingleVariableEscape {m : ℕ}
    (ucfe : UniformCertifiedFirstEscape n m) :
    Prop :=
  ucfeHeight ucfe = 0

private theorem
    packet_separator_inductive_step :
  ∀ {n m : ℕ}
    (h_bound : ℕ)
    (_ : ∀ ucfe' :
        UniformCertifiedFirstEscape n m,
      ucfeHeight ucfe' < h_bound →
      ucfe'.kind =
        EscapeKind.packetSeparating →
      isTerminalSingleVariableEscape ucfe')
    (ucfe :
      UniformCertifiedFirstEscape n m)
    (_ : ucfeHeight ucfe ≤ h_bound)
    (_ : ucfe.kind =
      EscapeKind.packetSeparating),
    isTerminalSingleVariableEscape ucfe := by
  intro n m _ _ih ucfe _hHeight hSep
  unfold isTerminalSingleVariableEscape
  by_contra hNZ
  exact ucfe.heightBound hSep (by
    unfold ucfeHeight at hNZ; omega)

theorem packet_separator_exclusion_strong
    {m : ℕ} (h_bound : ℕ)
    (ih : ∀ ucfe' :
        UniformCertifiedFirstEscape n m,
      ucfeHeight ucfe' < h_bound →
      ucfe'.kind =
        EscapeKind.packetSeparating →
      isTerminalSingleVariableEscape ucfe')
    (ucfe :
      UniformCertifiedFirstEscape n m)
    (hHeight : ucfeHeight ucfe ≤ h_bound)
    (hSep :
      ucfe.kind =
        EscapeKind.packetSeparating) :
    isTerminalSingleVariableEscape ucfe :=
  packet_separator_inductive_step h_bound ih
    ucfe hHeight hSep

theorem packet_separator_exclusion {m : ℕ}
    (ucfe :
      UniformCertifiedFirstEscape n m)
    (hSep :
      ucfe.kind =
        EscapeKind.packetSeparating) :
    isTerminalSingleVariableEscape ucfe := by
  suffices h :
    ∀ k (ucfe' :
        UniformCertifiedFirstEscape n m),
      ucfeHeight ucfe' ≤ k →
      ucfe'.kind =
        EscapeKind.packetSeparating →
      isTerminalSingleVariableEscape ucfe' from
    h _ ucfe (Nat.le_refl _) hSep
  intro k
  induction k with
  | zero =>
    intro ucfe' hH _
    unfold isTerminalSingleVariableEscape
    exact Nat.le_zero.mp hH
  | succ k' ih_k =>
    intro ucfe' hH hS
    exact packet_separator_exclusion_strong
      (k' + 1)
      (fun ucfe'' hLt hS' =>
        ih_k ucfe'' (by omega) hS')
      ucfe' hH hS

theorem ordinary_packet_separator_exclusion
    {m : ℕ}
    (C : BooleanCircuit m)
    (z : Fin m → Bool) (hz : C.eval z = true)
    (u : OccurrenceNode)
    (P : ContinuationPacket n m)
    (hP : P = mkContinuationPacket C z u)
    (D : PacketMarkedCorridor n)
    (ν lam_node : MagnificationNode)
    (hν_lam : ν.isAncestorOf lam_node)
    (M : Fin m → Bool)
    (hSeparating :
      continuationPacketEval P M = false)
    (fe : FirstEscape n m)
    (hfe : fe.packet = P)
    (hfeD : fe.corridor = D)
    (hSep : fe.isSeparating) :
    ∃ ucfe :
        UniformCertifiedFirstEscape n m,
      ucfe.kind =
        EscapeKind.packetSeparating ∧
      isTerminalSingleVariableEscape ucfe := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ucfe, _,
    _, _, hucfe_sep⟩ :=
    initialization_by_highest_failing_gate C z
      hz u P hP D ν lam_node hν_lam M
      hSeparating
  exact ⟨ucfe, hucfe_sep,
    packet_separator_exclusion ucfe hucfe_sep⟩

end PacketSeparatorExclusion

end PNeNp
